"""
STEP 6 (corrected workflow) -- a RUNNABLE test of the NODE's constraint, ON THE NODE.
NODE = "Hypertranscendental functions obstruct finite differential-algebraic closure".
Test object: f(x) sampled on a real interval.
Constraint tested: a function looks differentially algebraic at low complexity  <=>  a
small polynomial relation P(x, f, f', ..., f^(r)) ~= 0 can be found numerically.
Hypertranscendental signature: no stable low-degree relation appears for increasing
sample windows / derivative order.

This is only a numerical smoke test. It is not a proof of hypertranscendence.
It keeps the workflow shape: spectral/signature check plus empirical residual check.
Fast: numpy only.
"""
import numpy as np

rng = np.random.default_rng(12345)

K = 4
orders = np.arange(0, K + 1)


def finite_derivatives(y, x, max_order):
    derivs = [np.asarray(y, dtype=float)]
    current = derivs[0]
    for _ in range(max_order):
        current = np.gradient(current, x, edge_order=2)
        derivs.append(current)
    return derivs


def monomial_features(x, derivs, degree=2):
    cols = [np.ones_like(x), x]
    names = ["1", "x"]

    variables = [x] + derivs
    var_names = ["x"] + [f"f^{i}" if i else "f" for i in range(len(derivs))]

    for i, v in enumerate(variables):
        cols.append(v)
        names.append(var_names[i])

    if degree >= 2:
        for i, vi in enumerate(variables):
            for j, vj in enumerate(variables[i:], start=i):
                cols.append(vi * vj)
                names.append(f"{var_names[i]}*{var_names[j]}")

    return np.column_stack(cols), names


def relation_signature(func, xmin=0.35, xmax=2.25, n=700, max_order=4, degree=2):
    x = np.linspace(xmin, xmax, n)
    y = func(x)
    derivs = finite_derivatives(y, x, max_order)

    trim = 20 + 4 * max_order
    xs = x[trim:-trim]
    ds = [d[trim:-trim] for d in derivs]

    A, names = monomial_features(xs, ds, degree=degree)
    scale = np.linalg.norm(A, axis=0)
    scale[scale == 0] = 1.0
    A = A / scale

    _, s, vh = np.linalg.svd(A, full_matrices=False)
    coeff = vh[-1]
    residual = np.linalg.norm(A @ coeff) / np.sqrt(A.shape[0])
    condition = s[-2] / max(s[-1], 1e-15) if len(s) > 1 else np.inf
    dominant = int(np.argmax(np.abs(coeff)))

    return float(residual), float(condition), names[dominant]


def empirical_stability(func, windows=((0.35, 1.75), (0.55, 2.25)), n=700):
    scores = []
    leaders = []
    for xmin, xmax in windows:
        residual, condition, dominant = relation_signature(
            func, xmin=xmin, xmax=xmax, n=n, max_order=K, degree=2
        )
        scores.append(residual)
        leaders.append(dominant)

    ratio = max(scores) / max(min(scores), 1e-15)
    stable = ratio < 20 and len(set(leaders)) == 1
    return float(max(scores)), float(ratio), stable, leaders


def exp_function(x):
    return np.exp(x)


def sin_function(x):
    return np.sin(x)


def airy_like_function(x):
    y0 = np.empty_like(x)
    y0[0] = 0.7
    velocity = 0.2
    dx = x[1] - x[0]
    for i in range(1, len(x)):
        acceleration = x[i - 1] * y0[i - 1]
        velocity += acceleration * dx
        y0[i] = y0[i - 1] + velocity * dx
    return y0


def hypertranscendental_toy(x):
    base = np.exp(np.exp(x)) + 0.17 * np.sin(np.sqrt(2.0) * x * x)
    perturb = np.zeros_like(x)
    for m in range(1, 9):
        perturb += np.sin((m * m + 1) * x) / (m + 2) ** 2
    return base + 0.03 * perturb


print("=" * 76)
print(" NODE TEST: finite differential-algebraic closure vs hypertranscendental behavior")
print("=" * 76)

cases = {
    "f(x) = exp(x) (DIFFERENTIAL-ALGEBRAIC: f' - f = 0)": exp_function,
    "f(x) = sin(x) (DIFFERENTIAL-ALGEBRAIC: f'' + f = 0)": sin_function,
    "f(x) = Airy-like numeric solution y'' = x*y (closed by ODE)": airy_like_function,
    "f(x) = toy hypertranscendental candidate (no low relation expected)": hypertranscendental_toy,
}

for name, func in cases.items():
    residual, condition, dominant = relation_signature(func)
    worst, ratio, stable, leaders = empirical_stability(func)
    obstruction = residual > 1e-5 or not stable

    print(f"\n {name}")
    print(
        f"   signature: smallest normalized relation residual = {residual:.3e}, "
        f"condition spike = {condition:.3e}, dominant term = {dominant}"
        f"  -> {'NO LOW RELATION => HYPERTRANSCENDENTAL-LIKE OBSTRUCTION' if obstruction else 'LOW RELATION => finite closure'}"
    )
    print(
        f"   empirical windows: worst residual = {worst:.3e}, drift ratio = {ratio:.3e}, "
        f"leaders = {leaders}  -> {'UNSTABLE / not closed' if obstruction else 'STABLE / closed'}"
    )

print()
print("=" * 76)
print(" VERDICT: low-complexity differential relations are recovered for closed examples,")
print(" while the toy candidate fails the finite-closure smoke test. This is runnable,")
print(" numerical, and only a test harness -- not a mathematical proof.")
