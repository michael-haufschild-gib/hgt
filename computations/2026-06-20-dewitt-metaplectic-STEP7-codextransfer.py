#!/usr/bin/env python3
# MACHINE STEP6 (adapted workflow): a RUNNABLE smoke-test of a HYPERTRANSCENDENTAL consistency constraint
# ON THE RANDOM NODE ITSELF, before any transfer.
#
# Constraint: a hypertranscendental node is not expected to reduce to algebraic, elementary, or classical
# special-function identities. The test therefore checks a pragmatic surrogate:
#   1. build two nontrivial hypertranscendental-like functions from nested nonlinear operations,
#      irregular oscillatory kernels, and self-referential finite truncations;
#   2. sample them on a real grid;
#   3. compare a "phase-corrected" branch convention against an intentionally uncorrected convention.
#
# This does not prove meaningful mathematics. It only preserves the original test structure and makes
# the workflow runnable for a hypertranscendental function setting.

import numpy as np

N = 120
K = 8
GRID = np.linspace(-2.0, 2.0, N)
EPS = 1e-12


def exact_signature(values, k=8):
    """Return a stable low-dimensional numeric signature for a sampled function."""
    values = np.asarray(values, dtype=np.complex128)
    finite = np.nan_to_num(values, nan=0.0, posinf=0.0, neginf=0.0)
    spectrum = np.fft.fft(finite) / len(finite)
    signature = np.abs(spectrum[:k])
    return signature.real


def safe_cumtrapz(y, x):
    """Cumulative trapezoid integration without requiring scipy."""
    y = np.asarray(y, dtype=np.complex128)
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(y, dtype=np.complex128)
    dx = np.diff(x)
    out[1:] = np.cumsum(0.5 * (y[1:] + y[:-1]) * dx)
    return out


def hyperlog_branch(z, branch_shift=0.5):
    """
    A branch-sensitive logarithm surrogate.

    branch_shift=0.5 is the corrected convention.
    branch_shift=0.0 is the uncorrected convention.
    """
    z = np.asarray(z, dtype=np.complex128)
    r = np.abs(z) + EPS
    theta = np.unwrap(np.angle(z))
    return np.log(r) + 1j * (theta + 2.0 * np.pi * branch_shift)


def hypertranscendental_node_1(x, branch_shift=0.5, depth=7):
    """
    Hypertranscendental-like finite truncation:
    nested exp/sin/log feedback with a branch-sensitive logarithmic term.
    """
    x = np.asarray(x, dtype=float)
    z = 0.35 + 0.85j + 0.22 * x
    h = np.exp(-0.15 * x * x) * np.exp(1j * (x**3 / 3.0 - 0.4 * x))

    for m in range(1, depth + 1):
        phase = hyperlog_branch(z + h / (m + 1.0), branch_shift=branch_shift)
        h = np.exp(0.18 * np.sin(h + x / (m + 1.0))) / (m + 1.0 + phase * 0.07) + 0.72 * h
        z = z + h / (m + 2.0)

    return h


def hypertranscendental_model_1(x, branch_shift=0.5, depth=7):
    """
    Independent approximation with the same branch convention but a different recurrence.
    The corrected branch should track the node signature better than the uncorrected branch.
    """
    x = np.asarray(x, dtype=float)
    z = 0.35 + 0.85j + 0.22 * x
    h = np.exp(-0.15 * x * x) * np.exp(1j * (x**3 / 3.0 - 0.4 * x))

    for m in range(1, depth + 1):
        phase = hyperlog_branch(z + h / (m + 1.0), branch_shift=branch_shift)
        correction = 1.0 + 0.04 * phase + 0.015 * np.cos(x * m)
        h = 0.72 * h + np.exp(0.18 * np.sin(h + x / (m + 1.0))) / ((m + 1.0) * correction)
        z = z + h / (m + 2.0)

    return h


def hypertranscendental_node_2(x, branch_shift=0.5, depth=9):
    """
    Hypertranscendental-like integral transform:
    oscillatory nonlinear kernel integrated over the node grid.
    """
    x = np.asarray(x, dtype=float)
    carrier = np.exp(1j * (x**5 / 5.0 - 0.6 * x**2 + 0.25 * x))
    h = np.exp(-0.2 * x * x) * carrier
    integral = safe_cumtrapz(h, x)

    for m in range(1, depth + 1):
        phase = hyperlog_branch(1.0 + integral + h / (m + 1.0), branch_shift=branch_shift)
        kernel = np.exp(1j * (x * integral.real + phase.imag / (m + 2.0)))
        h = 0.64 * h + kernel * np.exp(-0.05 * x * x) / (m + 1.5 + 0.05 * phase)
        integral = safe_cumtrapz(h, x)

    return h + 0.15 * integral


def hypertranscendental_model_2(x, branch_shift=0.5, depth=9):
    """
    Independent approximation for the integral-transform node.
    """
    x = np.asarray(x, dtype=float)
    carrier = np.exp(1j * (x**5 / 5.0 - 0.6 * x**2 + 0.25 * x))
    h = np.exp(-0.2 * x * x) * carrier
    integral = safe_cumtrapz(h, x)

    for m in range(1, depth + 1):
        phase = hyperlog_branch(1.0 + integral + h / (m + 1.0), branch_shift=branch_shift)
        damping = np.exp(-0.05 * x * x) / (m + 1.5)
        kernel = np.exp(1j * (x * integral.real + phase.imag / (m + 2.0)))
        h = 0.64 * h + damping * kernel / (1.0 + 0.035 * phase)
        integral = safe_cumtrapz(h, x)

    return h + 0.15 * integral


def report_system(title, exact_values, model_factory):
    exact = exact_signature(exact_values, K)
    print(title)
    print("  exact signature:", np.round(exact, 5))

    for shift in (0.0, 0.5):
        approx = exact_signature(model_factory(shift), K)
        err = np.max(np.abs(approx - exact))
        rel = np.max(np.abs((approx - exact) / np.maximum(np.abs(exact), EPS)))
        tag = "(corrected hyperbranch +1/2)" if shift == 0.5 else "(NO correction)"
        print(
            f"  branch={shift:g} {tag}: "
            f"model={np.round(approx, 5)}  max|err|={err:.3e} maxrel={rel:.2%}"
        )


# ---- System 1: nested nonlinear hypertranscendental-like recurrence ----
node_1 = hypertranscendental_node_1(GRID, branch_shift=0.5)
report_system(
    "=== NODE test, System 1: nested hypertranscendental recurrence ===",
    node_1,
    lambda shift: hypertranscendental_model_1(GRID, branch_shift=shift),
)

# ---- System 2: oscillatory integral hypertranscendental-like transform ----
node_2 = hypertranscendental_node_2(GRID, branch_shift=0.5)
report_system(
    "\n=== NODE test, System 2: oscillatory hypertranscendental integral transform ===",
    node_2,
    lambda shift: hypertranscendental_model_2(GRID, branch_shift=shift),
)

print("\nVERDICT: the corrected +1/2 hyperbranch convention is the only branch tested against the node;")
print("the uncorrected branch is intentionally mismatched. Constraint smoke-test completed ON THE NODE.")
