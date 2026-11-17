"""RSI (Relative Strength Index) — 相対力指数

J. Welles Wilder Jr. が 1978 年に発表したモメンタム指標 RSI の実装。
依存ライブラリなし（Python 標準のみ）。

定義:
    変化 = 終値[t] - 終値[t-1]
    上昇幅 gain = max(変化, 0), 下落幅 loss = max(-変化, 0)
    RS  = 平均上昇幅 / 平均下落幅
    RSI = 100 - 100 / (1 + RS)

平均の取り方で2方式ある:
    - Wilder 方式（原典）: 平滑化平均（alpha = 1/期間 の指数平滑）
    - Cutler 方式: 単純移動平均

使い方:
    from rsi import rsi
    values = rsi([44.34, 44.09, 44.15, ...], period=14)
    # 先頭 period 個は None（計算に必要な本数が揃うまで）
"""

from __future__ import annotations


def _changes(prices: list[float]) -> tuple[list[float], list[float]]:
    gains: list[float] = []
    losses: list[float] = []
    for prev, cur in zip(prices, prices[1:]):
        diff = cur - prev
        gains.append(diff if diff > 0 else 0.0)
        losses.append(-diff if diff < 0 else 0.0)
    return gains, losses


def _rsi_from_averages(avg_gain: float, avg_loss: float) -> float:
    if avg_loss == 0.0:
        # 下落が一度もない場合は 100、横ばい（両方 0）は中立の 50
        return 100.0 if avg_gain > 0 else 50.0
    if avg_gain == 0.0:
        return 0.0
    rs = avg_gain / avg_loss
    return 100.0 - 100.0 / (1.0 + rs)


def rsi_wilder(prices: list[float], period: int = 14) -> list[float | None]:
    """Wilder 方式（原典）の RSI。戻り値は prices と同じ長さで、
    インデックス period 未満は None。"""
    if period < 1:
        raise ValueError("period must be >= 1")
    n = len(prices)
    result: list[float | None] = [None] * n
    if n <= period:
        return result
    gains, losses = _changes(prices)
    # 最初の平均は period 本の単純平均
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    result[period] = _rsi_from_averages(avg_gain, avg_loss)
    # 以後は Wilder の平滑化: avg = (avg * (period-1) + current) / period
    for i in range(period, n - 1):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        result[i + 1] = _rsi_from_averages(avg_gain, avg_loss)
    return result


def rsi_cutler(prices: list[float], period: int = 14) -> list[float | None]:
    """Cutler 方式（単純移動平均）の RSI。"""
    if period < 1:
        raise ValueError("period must be >= 1")
    n = len(prices)
    result: list[float | None] = [None] * n
    if n <= period:
        return result
    gains, losses = _changes(prices)
    for end in range(period, n):
        window_g = gains[end - period:end]
        window_l = losses[end - period:end]
        result[end] = _rsi_from_averages(
            sum(window_g) / period, sum(window_l) / period
        )
    return result


def rsi(prices: list[float], period: int = 14, method: str = "wilder") -> list[float | None]:
    """RSI を計算する。method は "wilder"（既定）または "cutler"。"""
    if method == "wilder":
        return rsi_wilder(prices, period)
    if method == "cutler":
        return rsi_cutler(prices, period)
    raise ValueError(f"unknown method: {method!r}")


if __name__ == "__main__":
    # Wilder の原典『New Concepts in Technical Trading Systems』に近い
    # 検証用の系列で自己チェックする
    sample = [
        44.34, 44.09, 44.15, 43.61, 44.33, 44.83, 45.10, 45.42,
        45.84, 46.08, 45.89, 46.03, 45.61, 46.28, 46.28, 46.00,
        46.03, 46.41, 46.22, 45.64, 46.21, 46.25, 45.71, 46.45,
        45.78, 45.35, 44.03, 44.18, 44.22, 44.57, 43.42, 42.66,
    ]
    w = rsi_wilder(sample, 14)
    c = rsi_cutler(sample, 14)
    print("index  price   RSI(Wilder)  RSI(Cutler)")
    for i, (p, wv, cv) in enumerate(zip(sample, w, c)):
        ws = f"{wv:8.2f}" if wv is not None else "     ---"
        cs = f"{cv:8.2f}" if cv is not None else "     ---"
        print(f"{i:5d}  {p:6.2f}  {ws}    {cs}")

    # 性質のチェック
    up = [float(i) for i in range(30)]            # 上がり続ける
    down = [float(30 - i) for i in range(30)]     # 下がり続ける
    flat = [10.0] * 30                            # 横ばい
    assert rsi_wilder(up)[-1] == 100.0
    assert rsi_wilder(down)[-1] == 0.0
    assert rsi_wilder(flat)[-1] == 50.0
    assert all(0.0 <= v <= 100.0 for v in w if v is not None)
    assert all(v is None for v in rsi_wilder([1.0, 2.0, 3.0], 14))
    print("self-check: OK")
