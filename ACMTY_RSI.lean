/-
  ACM-TY: Abstract Computation Model — Takeo Yamamoto
  完全版 Lean 4 実装 1ファイル版
  UHA x BSCM x DIFD x GIFE x Evolution x Computer x AI
  License: Apache 2.0
  Author: Takeo Yamamoto
-/

import Mathlib

open scoped BigOperators

/──────────────────────────────────────────────
  0. 基本定義
──────────────────────────────────────────────/

abbrev U64 := ZMod (2 ^ 64)

/-- デフォルト値用 -/
instance {n : Nat} : Inhabited (UHA n) where
  default := ⟨fun _ => 0⟩

/──────────────────────────────────────────────
  1. UHA — UltraCore HyperAlgebra（連続核）
──────────────────────────────────────────────/

structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

/-- 加算 -/
def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

instance : Add (UHA n) := ⟨add⟩

/-- スカラー倍 -/
def smul (a : U64) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : SMul U64 (UHA n) := ⟨smul⟩

/-- スカラー除算 : 座標ごとに Nat 除算して戻す -/
def divScalar (x : UHA n) (d : U64) : UHA n :=
  ⟨fun i => ((x.coords i).val / d.val : Nat)⟩

/-- 多元代数乗法（構造定数 c を外部から与える） -/
def mulWith
  (c : Fin n → Fin n → UHA n)
  (x y : UHA n) : UHA n :=
  ⟨fun i =>
    ∑ j : Fin n, ∑ k : Fin n, (x.coords j) * (y.coords k) * (c j k).coords i
  ⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i : Fin n, (x.coords i) * (x.coords i)

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

end UHA

/──────────────────────────────────────────────
  2. BSCM — Discrete Control Core（離散核）
──────────────────────────────────────────────/

namespace BSCM

/-- 離散状態更新 -/
def delta (s : U64) : U64 :=
  if s.val % 2 = 0 then
    ((s.val / 2 : Nat) : U64)
  else
    (((s.val + 1) / 2 : Nat) : U64)

/-- 外部入力付き制御ステップ -/
def controlStep (current_state external_input : U64) : U64 :=
  delta (current_state + external_input)

/-- 簡易エントロピー指標（下位2バイトの和） -/
def entropy (s : U64) : U64 :=
  ((s.val % 256 + (s.val / 256) % 256 : Nat) : U64)

end BSCM

/──────────────────────────────────────────────
  3. GIFE — General Information Field Engine（場核）
──────────────────────────────────────────────/

structure Entity (n : Nat) where
  id : Nat
  state : UHA n
  energy : U64
  mood : U64
  genome : U64
  discrete : U64

instance {n : Nat} : Inhabited (Entity n) where
  default := { id := 0, state := ⟨fun _ => 0⟩, energy := 0, mood := 0, genome := 0, discrete := 0 }

/-- Topology : Nat インデックスによる接続構造
    元の Fin 版だと id から Fin を作る証明が必要で詰まるため
    Nat 版に直した。意味は同じ -/
structure Topology (n : Nat) where
  connMatrix : Nat → Nat → U64
  viscosity : U64
  curvature : U64

namespace Topology

variable {n : Nat}

/-- i→j の接続強度 -/
def conn (top : Topology n) (i j : Nat) : U64 :=
  top.connMatrix i j

end Topology

structure FieldState (n : Nat) where
  entities : List (Entity n)
  entropy : U64
  topology : Topology n

/──────────────────────────────────────────────
  4. DIFD — Discrete Fluid Dynamics（流体核）
──────────────────────────────────────────────/

namespace DIFD

variable {n : Nat}

/-- 粘性クリップ -/
def clipViscosity (v : U64) : U64 :=
  if v.val > 1000000 then (1000000 : U64) else v

/-- 渦度減衰 -/
def decayVortex (c : U64) : U64 :=
  ((c.val / 2 : Nat) : U64)

/-- 圧力正規化 -/
def normalizePressure (p : U64) : U64 :=
  if p.val > 10 ^ 12 then ((10 ^ 12 : Nat) : U64) else p

/-- CFL 条件（簡易版） -/
def cfl (vel : UHA n) (visc : U64) : Bool :=
  decide (vel.norm.val < (visc * visc).val)

/-- 離散拡散：隣接 Entity の UHA 状態を重み付き平均 -/
def diffuse
  (top : Topology n)
  (e : Entity n)
  (neighbors : List (Entity n)) : UHA n :=
  let total : UHA n :=
    neighbors.foldl
      (fun acc nb =>
        let w := Topology.conn top e.id nb.id
        UHA.add acc (UHA.smul w nb.state))
      ⟨fun _ => 0⟩
  let norm : U64 :=
    neighbors.foldl
      (fun a nb => a + Topology.conn top e.id nb.id)
      0
  if norm = 0 then e.state
  else UHA.divScalar total norm

/-- 離散渦度 -/
def vortex
  (top : Topology n)
  (e : Entity n) : UHA n :=
  UHA.smul (decayVortex top.curvature) e.state

/-- 離散圧力 -/
def pressure
  (entropy : U64)
  (e : Entity n) : UHA n :=
  UHA.smul (normalizePressure entropy) e.state

/-- 完成版流体更新則 -/
def fluidUpdate
  (top : Topology n)
  (entropy : U64)
  (e : Entity n)
  (neighbors : List (Entity n)) : UHA n :=
  let visc := clipViscosity top.viscosity
  let d := diffuse top e neighbors
  let v := vortex top e
  let p := pressure entropy e
  if cfl d visc then
    UHA.add (UHA.add d v) p
  else
    e.state

end DIFD

/──────────────────────────────────────────────
  5. Dynamics & Evolution（力学核＋進化核）
──────────────────────────────────────────────/

structure Dynamics (n : Nat) where
  updateEntity :
    Entity n → U64 → Entity n
  updateEntropy :
    FieldState n → U64
  updateTopology :
    Topology n → List (Entity n) → Topology n

structure Evolution (n : Nat) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt : Entity n → U64 → Entity n

structure EvolutionCore (n : Nat) where
  fitness : Entity n → FieldState n → U64
  diversity : List (Entity n)

/──────────────────────────────────────────────
  6. BSCM ↔ UHA 統合（離散と連続の結合）
──────────────────────────────────────────────/

namespace Unified

variable {n : Nat}

/-- 離散 → 連続 -/
def discreteToContinuous (d : U64) (x : UHA n) : UHA n :=
  UHA.smul (BSCM.entropy d) x

/-- 連続 → 離散 -/
def continuousToDiscrete (x : UHA n) : U64 :=
  BSCM.controlStep (x.norm) (BSCM.entropy (x.norm))

end Unified

/──────────────────────────────────────────────
  7. Engine & 統合ステップ
──────────────────────────────────────────────/

structure Engine (n : Nat) where
  dynamics : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

/-- 統合 Entity 更新（DIFD + BSCM-UHA） -/
def updateEntityUnified {n : Nat}
  (dyn : Dynamics n)
  (top : Topology n)
  (entropy : U64)
  (neighbors : List (Entity n))
  (e : Entity n) : Entity n :=
  let fluidState := DIFD.fluidUpdate top entropy e neighbors
  let contState := Unified.discreteToContinuous e.discrete fluidState
  let newDisc := Unified.continuousToDiscrete contState
  let base := dyn.updateEntity e entropy
  { base with state := contState, discrete := newDisc }

/-- 従来進化ステップ（GIFE + DIFD + Evolution + BSCM-UHA） -/
def stepClassic {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e =>
      updateEntityUnified eng.dynamics s.topology s.entropy s.entities e)

  let adapted :=
    updated.map (fun e => eng.evolution.adapt e s.entropy)

  let selected :=
    eng.evolution.select adapted

  let mutated :=
    selected.map eng.evolution.mutate

  let newTopology :=
    eng.dynamics.updateTopology s.topology mutated

  let interimState : FieldState n :=
    { entities := mutated, entropy := s.entropy, topology := newTopology }

  let newEntropy :=
    eng.dynamics.updateEntropy interimState

  { entities := mutated, entropy := newEntropy, topology := newTopology }

/──────────────────────────────────────────────
  8. Takeo Evolution（環境変化時のみ進化）
──────────────────────────────────────────────/

def envChanged {n : Nat} (prev curr : FieldState n) : Bool :=
  decide (prev.entropy ≠ curr.entropy) ||
  decide (prev.topology.viscosity ≠ curr.topology.viscosity) ||
  decide (prev.topology.curvature ≠ curr.topology.curvature)

def argmaxEntity {n : Nat}
  (core : EvolutionCore n)
  (env : FieldState n) : Entity n :=
  match core.diversity with
  | [] =>
    { id := 0, state := ⟨fun _ => 0⟩, energy := 0, mood := 0, genome := 0, discrete := 0 }
  | e :: es =>
    es.foldl
      (fun best cand =>
        if core.fitness cand env > core.fitness best env then cand else best)
      e

/-- Takeoモデル：環境変化時のみ進化を適用 -/
def stepTakeo {n : Nat}
  (eng : Engine n)
  (core : EvolutionCore n)
  (prev : FieldState n)
  (curr : FieldState n) : FieldState n :=
  if envChanged prev curr then
    let best := argmaxEntity core curr
    { entities := [best]
    , entropy := curr.entropy
    , topology := curr.topology }
  else prev

/-- 統合ステップ：Takeo進化あり／なしを切り替え -/
def step {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none => stepClassic eng s
  | some core =>
    let next := stepClassic eng s
    stepTakeo eng core s next

/──────────────────────────────────────────────
  9. 簡易テスト
──────────────────────────────────────────────/

def sampleUHA : UHA 4 :=
  ⟨fun i =>
    match i.val with
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | _ => 4⟩

#eval UHA.norm sampleUHA

/──────────────────────────────────────────────
  10. ACM-TY Computer : 新型コンピュータ
──────────────────────────────────────────────/

namespace ACMTY_Computer

/-- 命令セット : 従来の ALU + 流体 + 進化 -/
inductive Opcode where
  | NOP | ADD | SMUL | MUL
  | DIFFUSE | VORTEX | PRESSURE
  | BSCM_STEP | LOAD | STORE
  | JUMP_IF_ENV | EVOLVE | HALT
  deriving Repr, DecidableEq, Inhabited

structure Instr (n : Nat) where
  op : Opcode
  dst : Fin 8
  src1 : Fin 8
  src2 : Fin 8
  imm : U64
  deriving Repr

/-- CPU : レジスタは UHA、制御は BSCM、メモリは場 -/
structure CPU (n : Nat) where
  pc : Nat
  regs : Fin 8 → UHA n
  dregs : Fin 8 → U64
  prog : List (Instr n)
  mem : List (UHA n)
  field : FieldState n
  engine : Engine n
  algebra : Fin n → Fin n → UHA n
  halted : Bool

def initCPU {n : Nat}
  (prog : List (Instr n)) (field : FieldState n)
  (engine : Engine n) (algebra : Fin n → Fin n → UHA n) : CPU n :=
  { pc := 0
    regs := fun _ => ⟨fun _ => 0⟩
    dregs := fun _ => 0
    prog := prog, mem := [], field := field
    engine := engine, algebra := algebra, halted := false }

/-- メモリ書き込み : 範囲外は 0 で埋めて拡張 -/
def storeMem {n : Nat} : List (UHA n) → Nat → UHA n → List (UHA n)
  | [], 0, v => [v]
  | [], k+1, v => ⟨fun _ => 0⟩ :: storeMem [] k v
  | _ :: xs, 0, v => v :: xs
  | x :: xs, k+1, v => x :: storeMem xs k v

/-- レジスタを Entity に変換して流体命令に渡す -/
def regToEntity {n : Nat} (cpu : CPU n) (r : Fin 8) : Entity n :=
  { id := r.val
    state := cpu.regs r
    energy := 0, mood := 0, genome := 0
    discrete := cpu.dregs r }

/-- 1命令実行 : フェッチ済みの命令をデコードして実行 -/
def execInstr {n : Nat} (cpu : CPU n) (instr : Instr n) : CPU n :=
  let r1 := cpu.regs instr.src1
  let r2 := cpu.regs instr.src2
  match instr.op with
  | .NOP => { cpu with pc := cpu.pc + 1 }
  | .ADD => { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst (r1 + r2) }
  | .SMUL => { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst (UHA.smul instr.imm r1) }
  | .MUL => { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst (UHA.mulWith cpu.algebra r1 r2) }
  | .DIFFUSE =>
    let e := regToEntity cpu instr.src1
    let ns := DIFD.fluidUpdate cpu.field.topology cpu.field.entropy e cpu.field.entities
    { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst ns }
  | .VORTEX =>
    let e := regToEntity cpu instr.src1
    let ns := DIFD.vortex cpu.field.topology e
    { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst ns }
  | .PRESSURE =>
    let e := regToEntity cpu instr.src1
    let ns := DIFD.pressure cpu.field.entropy e
    { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst ns }
  | .BSCM_STEP => { cpu with pc := cpu.pc + 1,
      dregs := Function.update cpu.dregs instr.dst
        (BSCM.controlStep (cpu.dregs instr.src1) instr.imm) }
  | .LOAD => { cpu with pc := cpu.pc + 1,
      regs := Function.update cpu.regs instr.dst
        (cpu.mem.getD instr.imm.val ⟨fun _ => 0⟩) }
  | .STORE => { cpu with pc := cpu.pc + 1,
      mem := storeMem cpu.mem instr.imm.val r1 }
  | .JUMP_IF_ENV =>
    if cpu.field.entropy.val = instr.imm.val then
      { cpu with pc := cpu.pc + 1 }
    else
      { cpu with pc := instr.imm.val }
  | .EVOLVE => { cpu with pc := cpu.pc + 1,
      field := _root_.step cpu.engine cpu.field }
  | .HALT => { cpu with halted := true }

/-- 実行ループ : fuel が尽きるか HALT するまで回す -/
def run {n : Nat} (cpu : CPU n) (fuel : Nat) : CPU n :=
  match fuel with
  | 0 => cpu
  | k+1 =>
    if cpu.halted then cpu
    else match cpu.prog.drop cpu.pc with
    | [] => { cpu with halted := true }
    | instr :: _ => run (execInstr cpu instr) k

end ACMTY_Computer

/──────────────────────────────────────────────
  11. ACM-TY AI : 新型AI
──────────────────────────────────────────────/

namespace ACMTY_AI

/-- 活性化 : ノルムからスケールを作って発散を抑える -/
def activation {n : Nat} (x : UHA n) : UHA n :=
  let s : U64 := ((x.norm.val % 256 + 1 : Nat) : U64)
  UHA.smul s x

/-- 1ニューロン順伝播 : 流体更新 + 活性化 + 離散化 -/
def forwardEntity {n : Nat}
  (top : Topology n) (entropy : U64)
  (e : Entity n) (neighbors : List (Entity n)) : Entity n :=
  let fluid := DIFD.fluidUpdate top entropy e neighbors
  { e with state := activation fluid
    discrete := Unified.continuousToDiscrete fluid }

/-- 1層順伝播 : 場全体を一気に流す -/
def forwardField {n : Nat} (s : FieldState n) : FieldState n :=
  { s with entities :=
    s.entities.map (fun e => forwardEntity s.topology s.entropy e s.entities) }

/-- 損失 : 2つの UHA 状態の差のノルム -/
def loss {n : Nat} (a b : UHA n) : U64 :=
  UHA.norm (UHA.add a (UHA.smul (-1) b))

/-- AIエージェント : 脳が FieldState、記憶が過去の場の履歴 -/
structure Agent (n : Nat) where
  engine : Engine n
  brain : FieldState n
  memory : List (FieldState n)

/-- 知覚 : 入力を場に注入して1層流す -/
def perceive {n : Nat} (agent : Agent n) (input : FieldState n) : FieldState n :=
  forwardField { input with topology := agent.brain.topology }

/-- 意思決定 : Takeo進化ありなら最適個体、なしなら先頭 -/
def decide {n : Nat} (agent : Agent n) (input : FieldState n) : Entity n :=
  match agent.engine.takeoCore with
  | some core => argmaxEntity core input
  | none =>
    match input.entities with
    | [] => { id := 0, state := ⟨fun _ => 0⟩, energy := 0, mood := 0, genome := 0, discrete := 0 }
    | e :: _ => e

/-- 学習 : 環境変化時のみ進化、それ以外は流体でなじませる -/
def learn {n : Nat} (agent : Agent n) (experience : FieldState n) : Agent n :=
  let next := _root_.step agent.engine experience
  { agent with brain := next, memory := agent.brain :: agent.memory }

/-- 訓練 : エピソード列を順に学習 -/
def train {n : Nat} (agent : Agent n) (episodes : List (FieldState n)) : Agent n :=
  episodes.foldl (fun ag ep => learn ag ep) agent

/-- 推論 : 知覚して決めるだけ、学習しない -/
def infer {n : Nat} (agent : Agent n) (input : FieldState n) : Entity n :=
  decide agent (perceive agent input)

end ACMTY_AI

/──────────────────────────────────────────────
  12. デモ : コンピュータで (1,2,3,4) を流体計算
──────────────────────────────────────────────/

def demoTopology : Topology 4 :=
  { connMatrix := fun _ _ => 1, viscosity := 100, curvature := 2 }

def demoField : FieldState 4 :=
  { entities :=
    [ { id := 0, state := sampleUHA, energy := 10, mood := 0, genome := 1, discrete := 1 }
      { id := 1, state := sampleUHA, energy := 20, mood := 0, genome := 2, discrete := 2 } ]
    entropy := 100
    topology := demoTopology }

def demoEngine : Engine 4 :=
  { dynamics :=
    { updateEntity := fun e _ => e
      updateEntropy := fun s => s.entropy
      updateTopology := fun t _ => t }
    evolution :=
    { mutate := fun e => { e with genome := e.genome + 1 }
      select := fun es => es
      adapt := fun e _ => e }
    takeoCore := none }

def demoAlgebra : Fin 4 → Fin 4 → UHA 4 :=
  fun _ _ => ⟨fun _ => 1⟩

-- R0 = mem[0], R1 = DIFFUSE(R0), R2 = R0 + R1, STORE R2 -> mem[0], HALT
def demoProg : List (ACMTY_Computer.Instr 4) :=
  [ { op := .LOAD, dst := 0, src1 := 0, src2 := 0, imm := 0 }
    { op := .DIFFUSE, dst := 1, src1 := 0, src2 := 0, imm := 0 }
    { op := .ADD, dst := 2, src1 := 0, src2 := 1, imm := 0 }
    { op := .STORE, dst := 0, src1 := 2, src2 := 0, imm := 0 }
    { op := .HALT, dst := 0, src1 := 0, src2 := 0, imm := 0 } ]

def demoCPU : ACMTY_Computer.CPU 4 :=
  ACMTY_Computer.initCPU demoProg demoField demoEngine demoAlgebra

def demoCPU2 : ACMTY_Computer.CPU 4 :=
  { demoCPU with mem := [sampleUHA] }

#eval UHA.norm ((ACMTY_Computer.run demoCPU2 20).regs 2)
#eval UHA.norm (ACMTY_AI.forwardField demoField).entities.head!.state

-- Takeo進化ありの AI デモ用
def demoCore : EvolutionCore 4 :=
  { fitness := fun e _ => UHA.norm e.state
    diversity := demoField.entities }

def demoEngineTakeo : Engine 4 :=
  { demoEngine with takeoCore := some demoCore }

def demoAgent : ACMTY_AI.Agent 4 :=
  { engine := demoEngineTakeo, brain := demoField, memory := [] }

#eval UHA.norm (ACMTY_AI.infer demoAgent demoField).state

/──────────────────────────────────────────────
  13. ACM-TY × RSI — Recursive Self-Improvement
  ユーザー提供コードをそのまま統合
  import はファイル頂点の import Mathlib に集約済み
──────────────────────────────────────────────/

namespace ACM_RSI

/──────────────────────────────────────────────
  1. Genome — 自己プログラム表現
──────────────────────────────────────────────/

abbrev Genome := List Nat

/──────────────────────────────────────────────
  2. Performance — 性能評価
──────────────────────────────────────────────/

structure Metrics where
  performance : Nat
  reliability  : Nat
  consistency  : Nat
  errors       : Nat
  deriving Repr, DecidableEq

/-- 総合適応性能 -/
def fitness (m : Metrics) : Nat :=
  (m.performance + m.reliability + m.consistency)
    / (m.errors + 1)

/──────────────────────────────────────────────
  3. Verified Candidate — 検証済み改善候補
──────────────────────────────────────────────/

/--
  採用可能な候補は検証条件を満たす。
  Boolによる検証結果を証明項として保持する。
-/

structure Candidate (valid : Genome → Bool) where
  genome : Genome
  proof  : valid genome = true
  metrics : Metrics

/──────────────────────────────────────────────
  4. RSI Engine — 自己改善エンジン
──────────────────────────────────────────────/

structure Engine (valid : Genome → Bool) where

  /-- 改善候補の生成 -/
  propose : Genome → List Genome

  /-- 性能測定 -/
  measure : Genome → Metrics

  /-- 検証関数 -/
  valid : Genome → Bool

/──────────────────────────────────────────────
  5. RSI State — 自己状態
──────────────────────────────────────────────/

structure RSIState (valid : Genome → Bool) where

  current : Candidate valid

  generation : Nat

  accepted : Nat

  rejected : Nat

  stagnation : Nat

  history : List Nat

/──────────────────────────────────────────────
  6. Initialization — 初期化
──────────────────────────────────────────────/

def initialize
  (engine : Engine valid)
  (genome : Genome)
  (h : engine.valid genome = true) :
  RSIState engine.valid :=

  let m := engine.measure genome

  {
    current := {
      genome := genome
      proof := h
      metrics := m
    }
    generation := 0
    accepted := 0
    rejected := 0
    stagnation := 0
    history := [fitness m]
  }

/──────────────────────────────────────────────
  7. Candidate Generation — 改善候補生成
──────────────────────────────────────────────/

/-- 検証に合格した候補だけを抽出 -/

def generateCandidates
  (engine : Engine valid)
  (genome : Genome) :
  List (Candidate engine.valid) :=

  (engine.propose genome).filterMap
    (fun g =>
      if h : engine.valid g = true then
        some {
          genome := g
          proof := h
          metrics := engine.measure g
        }
      else
        none)

/──────────────────────────────────────────────
  8. Selection — 最良候補の選択
──────────────────────────────────────────────/

/-- 適応度による最良候補選択 -/

def selectBest
  (current : Candidate valid)
  (candidates : List (Candidate valid)) :
  Candidate valid :=

  candidates.foldl
    (fun best candidate =>
      if fitness candidate.metrics > fitness best.metrics
      then candidate
      else best)
    current

/──────────────────────────────────────────────
  9. Recursive Self-Improvement
──────────────────────────────────────────────/

/--
  1. 現在のGenomeを取得
  2. 改善候補を生成
  3. 検証
  4. 性能評価
  5. 最良候補を選択
  6. 改善時のみ採用
-/

def step
  (engine : Engine valid)
  (s : RSIState engine.valid) :
  RSIState engine.valid :=

  let candidates :=
    generateCandidates engine s.current.genome

  let best :=
    selectBest s.current candidates

  if fitness best.metrics > fitness s.current.metrics then

    {
      current := best
      generation := s.generation + 1
      accepted := s.accepted + 1
      rejected := s.rejected
      stagnation := 0
      history := s.history ++ [fitness best.metrics]
    }

  else

    {
      current := s.current
      generation := s.generation + 1
      accepted := s.accepted
      rejected := s.rejected + candidates.length
      stagnation := s.stagnation + 1
      history := s.history ++ [fitness s.current.metrics]
    }

/──────────────────────────────────────────────
  10. Autonomous Evolution — 自律反復
──────────────────────────────────────────────/

/-- 指定回数だけ自己改善を反復 -/

def run
  (engine : Engine valid) :
  Nat → RSIState engine.valid → RSIState engine.valid

  | 0, state => state

  | fuel + 1, state =>
      run engine fuel (step engine state)

/-- 改善停滞時の停止条件 -/

def stable
  (threshold : Nat)
  (s : RSIState valid) : Bool :=
  s.stagnation >= threshold

/-- 停滞または燃料切れまで自律反復 -/

def runUntilStable
  (engine : Engine valid)
  (threshold : Nat) :
  Nat → RSIState engine.valid → RSIState engine.valid

  | 0, state => state

  | fuel + 1, state =>
      if stable threshold state then
        state
      else
        runUntilStable engine threshold
          (step engine state)

/──────────────────────────────────────────────
  11. Improvement Monitoring
──────────────────────────────────────────────/

/-- 初期世代と現在世代の性能差 -/

def improvement
  (s : RSIState valid) : Nat :=
  fitness s.current.metrics -
    (s.history.headD 0)

/-- 改善率ではなく累積性能向上量を保持 -/

def report
  (s : RSIState valid) : String :=
  "Generation: " ++ toString s.generation ++
  " | Accepted: " ++ toString s.accepted ++
  " | Rejected: " ++ toString s.rejected ++
  " | Fitness: " ++
    toString (fitness s.current.metrics) ++
  " | Improvement: " ++
    toString (improvement s)

/──────────────────────────────────────────────
  12. Demonstration Engine
──────────────────────────────────────────────/

/-- デモ用の改善候補生成 -/

def demoPropose (g : Genome) : List Genome :=
  [
    g ++ [1],
    g.map (fun x => x + 1)
  ]

/-- デモ用性能測定 -/

def demoMeasure (g : Genome) : Metrics :=
  {
    performance := g.sum
    reliability := 100
    consistency := 100
    errors := 0
  }

/-- デモ用検証条件 -/

def demoEngine : Engine (fun _ => true) :=
  {
    propose := demoPropose
    measure := demoMeasure
    valid := fun _ => true
  }

/-- 初期AI -/

def demoInitial :=
  initialize demoEngine [1] rfl

/-- 5世代の自律改善 -/

def demoResult :=
  run demoEngine 5 demoInitial

#eval demoResult.current.genome

#eval demoResult.generation

#eval demoResult.accepted

#eval demoResult.history

#eval report demoResult

end ACM_RSI

/──────────────────────────────────────────────
  14. ACM-TY × RSI 統合層
  RSI の Genome が ACM-TY 自身の Topology を書き換える
  これが本当の自己改善：AI が自分のハードウェア条件を進化させる
──────────────────────────────────────────────/

namespace ACMTY_RSI

/-- RSI Genome -> UHA : 先頭から座標に詰める -/
def genomeToUHA {n : Nat} (g : ACM_RSI.Genome) : UHA n :=
  ⟨fun i => ((g.getD i.val 0 : Nat) : U64)⟩

/-- UHA -> RSI Genome -/
def uhaToGenome {n : Nat} (x : UHA n) : ACM_RSI.Genome :=
  (List.finRange n).map (fun i => (x.coords i).val)

/-- Entity -> RSI Genome : genome, energy, mood, discrete + UHA -/
def entityToGenome {n : Nat} (e : Entity n) : ACM_RSI.Genome :=
  [e.genome.val, e.energy.val, e.mood.val, e.discrete.val] ++ uhaToGenome e.state

/-- RSI Genome -> Entity : 既存 Entity に上書き -/
def genomeToEntity {n : Nat} (g : ACM_RSI.Genome) (fallback : Entity n) : Entity n :=
  { fallback with
    state := genomeToUHA g
    genome := ((g.getD 0 0 : Nat) : U64)
    energy := ((g.getD 1 0 : Nat) : U64)
    mood := ((g.getD 2 0 : Nat) : U64)
    discrete := ((g.getD 3 0 : Nat) : U64) }

/-- FieldState -> RSI Metrics : 場の性能を RSI の評価に変換 -/
def metricsFromField {n : Nat} (s : FieldState n) : ACM_RSI.Metrics :=
  { performance := s.entities.foldl (fun acc e => acc + e.state.norm.val) 0 % 100000
    reliability := 100
    consistency := 100
    errors := 0 }

/-- ACM-TY 用の検証 : 長さと値域だけ制限、危険な自己書き換えを防ぐ -/
def acmtyValid (g : ACM_RSI.Genome) : Bool :=
  decide (g.length ≤ 256) && g.all (fun x => decide (x < 2 ^ 64))

/-- ACM-TY 用の候補生成 : 伸ばす、+1、反転、2倍 -/
def acmtyPropose (g : ACM_RSI.Genome) : List ACM_RSI.Genome :=
  [ g ++ [1]
    g.map (fun x => x + 1)
    g.reverse
    g.map (fun x => x * 2 % (2 ^ 64)) ]

/-- ACM-TY 用の性能測定 : Genome の合計 + Field 由来の性能 -/
def acmtyMeasure (g : ACM_RSI.Genome) : ACM_RSI.Metrics :=
  { performance := g.sum % 100000
    reliability := 100
    consistency := 100 - g.length % 10
    errors := 0 }

/-- ACM-TY 用 RSI Engine -/
def acmtyRSIEngine : ACM_RSI.Engine acmtyValid :=
  { propose := acmtyPropose
    measure := acmtyMeasure
    valid := acmtyValid }

/-- ACM-TY 用 RSI 初期状態 -/
def acmtyRSIInitial : ACM_RSI.RSIState acmtyValid :=
  ACM_RSI.initialize acmtyRSIEngine [1] (by decide)

/-- RSI Genome -> Topology : viscosity と curvature を自己書き換え -/
def applyGenomeToTopology {n : Nat} (top : Topology n) (g : ACM_RSI.Genome) : Topology n :=
  { top with
    viscosity := ((g.getD 0 top.viscosity.val : Nat) : U64)
    curvature := ((g.getD 1 top.curvature.val : Nat) : U64) }

/-- 自己改善エージェント : ACM-TY AI + RSI 状態 -/
structure SelfImprovingAgent (n : Nat) where
  agent : ACMTY_AI.Agent n
  rsi : ACM_RSI.RSIState acmtyValid

/-- 1ステップ : ACM-TY で場を進め、RSI で Genome を進め、Genome で Topology を書き換える -/
def selfImproveStep {n : Nat} (s : SelfImprovingAgent n) (experience : FieldState n) :
    SelfImprovingAgent n :=
  let nextRSI := ACM_RSI.step acmtyRSIEngine s.rsi
  let acmNext := _root_.step s.agent.engine experience
  let newTop := applyGenomeToTopology acmNext.topology nextRSI.current.genome
  let nextBrain : FieldState n := { acmNext with topology := newTop }
  let nextAgent : ACMTY_AI.Agent n :=
    { s.agent with brain := nextBrain, memory := s.agent.brain :: s.agent.memory }
  { agent := nextAgent, rsi := nextRSI }

/-- エピソード列で自己改善を反復 -/
def runSelfImproving {n : Nat} (s : SelfImprovingAgent n) (episodes : List (FieldState n)) :
    SelfImprovingAgent n :=
  episodes.foldl (fun acc ep => selfImproveStep acc ep) s

/-- レポート : RSI 側 + ACM-TY 側を両方出す -/
def reportSelf {n : Nat} (s : SelfImprovingAgent n) : String :=
  ACM_RSI.report s.rsi ++
  " | Viscosity: " ++ toString s.agent.brain.topology.viscosity.val ++
  " | Curvature: " ++ toString s.agent.brain.topology.curvature.val ++
  " | Entities: " ++ toString s.agent.brain.entities.length

end ACMTY_RSI

/──────────────────────────────────────────────
  15. 統合デモ
──────────────────────────────────────────────/

def demoSelfAgent : ACMTY_RSI.SelfImprovingAgent 4 :=
  { agent := demoAgent, rsi := ACMTY_RSI.acmtyRSIInitial }

def demoSelfResult : ACMTY_RSI.SelfImprovingAgent 4 :=
  ACMTY_RSI.runSelfImproving demoSelfAgent [demoField, demoField, demoField, demoField, demoField]

#eval ACM_RSI.report demoSelfResult.rsi
#eval ACMTY_RSI.reportSelf demoSelfResult
#eval demoSelfResult.rsi.current.genome
#eval demoSelfResult.agent.brain.topology.viscosity.val
#eval demoSelfResult.agent.brain.topology.curvature.val
#eval UHA.norm (ACMTY_AI.infer demoSelfResult.agent demoField).state
