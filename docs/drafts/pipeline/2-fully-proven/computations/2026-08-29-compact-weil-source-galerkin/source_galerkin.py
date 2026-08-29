#!/usr/bin/env python3
"""Literal source-side CCM Laurent matrix and hostile ground-state diagnostics.

Computational experiment only. No output is a Lean premise.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import os
import time
from pathlib import Path

import mpmath as mp
from flint import acb, acb_mat, arb, arb_mat, ctx


def trace(message: str) -> None:
    if os.environ.get("SOURCE_GALERKIN_TRACE"):
        print(message, flush=True)


def midpoint_text(value: arb, digits: int) -> str:
    return value.mid().str(digits, radius=False)


def von_mangoldt(n: int) -> mp.mpf:
    """Return Lambda(n), detecting prime powers exactly with integer arithmetic."""
    if n < 2:
        return mp.mpf("0")
    for p in range(2, math.isqrt(n) + 2):
        if n % p:
            continue
        q = n
        while q % p == 0:
            q //= p
        if q == 1:
            for d in range(2, math.isqrt(p) + 1):
                if p % d == 0:
                    return mp.mpf("0")
            return mp.log(p)
        return mp.mpf("0")
    return mp.log(n)


def atoms(L: mp.mpf) -> list[tuple[int, mp.mpf, mp.mpf]]:
    upper = int(mp.floor(mp.e**L))
    out: list[tuple[int, mp.mpf, mp.mpf]] = []
    for k in range(2, upper + 1):
        weight = von_mangoldt(k) / mp.sqrt(k)
        if weight:
            out.append((k, mp.log(k), weight))
    return out


def polar_sine(L: mp.mpf, omega: mp.mpf) -> mp.mpf:
    if omega == 0:
        return mp.mpf("0")
    return -2 * omega * (mp.cosh(L / 2) - 1) / (omega * omega + mp.mpf("0.25"))


def polar_diagonal(L: mp.mpf, omega: mp.mpf) -> mp.mpf:
    def J(c: mp.mpf) -> mp.mpf:
        s = c + 1j * omega
        return mp.re(-1 / s + (mp.e ** (c * L) - 1) / (L * s * s))

    return 2 * (J(mp.mpf("0.5")) + J(mp.mpf("-0.5")))


def lerch_series(z: mp.mpf, power: int, q: mp.mpc) -> mp.mpc:
    """Rapid defining series for Phi(z,power,q); here 0 < z <= exp(-1.6)."""
    total = mp.mpc(0)
    z_power = mp.mpf(1)
    for k in range(10000):
        term = z_power / (q + k) ** power
        total += term
        if k > 8 and abs(term) < mp.eps * max(1, abs(total)):
            return total
        z_power *= z
    raise RuntimeError("Lerch series did not converge")


def flint_special_midpoint(q: mp.mpc, order: int | None = None) -> mp.mpc:
    """Fast Arb digamma/polygamma midpoint at the active precision."""
    digits = mp.mp.dps
    q_arb = acb(
        arb(mp.nstr(mp.re(q), digits)),
        arb(mp.nstr(mp.im(q), digits)),
    )
    value = q_arb.digamma() if order is None else q_arb.polygamma(order)
    return mp.mpc(
        mp.mpf(value.real.mid().str(digits, radius=False)),
        mp.mpf(value.imag.mid().str(digits, radius=False)),
    )


def arch_sine(L: mp.mpf, mode: int) -> mp.mpf:
    if mode == 0:
        return mp.mpf("0")
    b = mp.pi * mode / L
    q = mp.mpf("0.25") + 1j * b
    z = mp.e ** (-2 * L)
    return (
        mp.im(flint_special_midpoint(q)) / 2
        + mp.e ** (-L / 2) * mp.im(lerch_series(z, 1, q)) / 2
    )


def arch_diagonal(L: mp.mpf, mode: int) -> mp.mpf:
    b = mp.pi * mode / L
    q = mp.mpf("0.25") + 1j * b
    z = mp.e ** (-2 * L)
    phi1 = lerch_series(z, 1, q)
    phi2 = lerch_series(z, 2, q)
    digamma_q = flint_special_midpoint(q)
    trigamma_q = flint_special_midpoint(q, 1)
    i_diff = (
        ((-mp.euler - 2 * mp.log(2)) - mp.re(digamma_q)) / 2
        - mp.e ** (-L / 2) * mp.re(phi1) / 2
        + mp.atanh(mp.e ** (-L))
    )
    i_h_cos = (
        mp.re(trigamma_q) / 4
        - mp.e ** (-L / 2)
        * (L * mp.re(phi1) / 2 + mp.re(phi2) / 4)
    )
    endpoint = mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1))
    return endpoint + 2 * (i_diff - i_h_cos / L)


def prime_sine(atom_data: list[tuple[int, mp.mpf, mp.mpf]], omega: mp.mpf) -> mp.mpf:
    return mp.fsum(weight * mp.sin(omega * lag) for _, lag, weight in atom_data)


def prime_diagonal(
    L: mp.mpf, atom_data: list[tuple[int, mp.mpf, mp.mpf]], omega: mp.mpf
) -> mp.mpf:
    return mp.fsum(
        weight * 2 * (1 - lag / L) * mp.cos(omega * lag)
        for _, lag, weight in atom_data
    )


def component_coordinates(L: mp.mpf, N: int) -> dict[str, tuple[list[mp.mpf], list[mp.mpf]]]:
    atom_data = atoms(L)
    positive: dict[str, tuple[list[mp.mpf], list[mp.mpf]]] = {
        name: ([], []) for name in ("polar", "prime", "arch")
    }
    for mode in range(N + 1):
        omega = 2 * mp.pi * mode / L
        p_sin = polar_sine(L, omega)
        s_sin = prime_sine(atom_data, omega)
        a_sin = arch_sine(L, mode)
        p_diag = polar_diagonal(L, omega)
        s_diag = prime_diagonal(L, atom_data, omega)
        a_diag = arch_diagonal(L, mode)
        # D = P - S - A and b_n = -D(sin_n)/pi.
        positive["polar"][0].append(-p_sin / mp.pi)
        positive["polar"][1].append(p_diag)
        positive["prime"][0].append(s_sin / mp.pi)
        positive["prime"][1].append(-s_diag)
        positive["arch"][0].append(a_sin / mp.pi)
        positive["arch"][1].append(-a_diag)
    coordinates: dict[str, tuple[list[mp.mpf], list[mp.mpf]]] = {}
    for name, (source, diagonal) in positive.items():
        coordinates[name] = (
            [-source[mode] for mode in range(N, 0, -1)] + source,
            [diagonal[mode] for mode in range(N, 0, -1)] + diagonal,
        )
    return coordinates


def build_matrix(source: list[mp.mpf], diagonal: list[mp.mpf], N: int, digits: int) -> arb_mat:
    size = 2 * N + 1
    matrix = arb_mat(size, size)
    for i in range(size):
        for j in range(size):
            value = diagonal[i] if i == j else (source[i] - source[j]) / (i - j)
            matrix[i, j] = arb(mp.nstr(value, digits))
    return matrix


def max_abs_matrix(matrix: arb_mat) -> arb:
    value = arb(0)
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            candidate = abs(matrix[i, j])
            if float(candidate) > float(value):
                value = candidate
    return value


def choose_real_eigenvector(eigenvectors: acb_mat, index: int) -> list[arb]:
    re = [eigenvectors[row, index].real for row in range(eigenvectors.nrows())]
    im = [eigenvectors[row, index].imag for row in range(eigenvectors.nrows())]
    re_norm = sum((x * x for x in re), arb(0))
    im_norm = sum((x * x for x in im), arb(0))
    vector = re if float(re_norm) >= float(im_norm) else im
    norm = sum((x * x for x in vector), arb(0)).sqrt()
    return [x / norm for x in vector]


def rayleigh(matrix: arb_mat, vector: list[arb]) -> arb:
    column = arb_mat([[x] for x in vector])
    return (column.transpose() * matrix * column)[0, 0]


def direct_formula_validation(L: mp.mpf, N: int) -> list[dict[str, str | int]]:
    atom_data = atoms(L)
    records: list[dict[str, str | int]] = []
    for mode in sorted(set([0, 1, max(1, N // 2), N])):
        omega = 2 * mp.pi * mode / L

        def sine_integrand(h: mp.mpf) -> mp.mpf:
            if h == 0:
                return omega / 2
            return mp.sin(omega * h) * mp.e ** (h / 2) / (mp.e**h - mp.e ** (-h))

        def diagonal_test(h: mp.mpf) -> mp.mpf:
            return 2 * (1 - h / L) * mp.cos(omega * h)

        def diagonal_integrand(h: mp.mpf) -> mp.mpf:
            if h == 0:
                return mp.mpf("0.5") - 1 / L
            return (
                mp.e ** (h / 2) * diagonal_test(h) - 2
            ) / (mp.e**h - mp.e ** (-h))

        arch_sine_quad = mp.quad(sine_integrand, [0, L])
        endpoint = mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1))
        arch_diag_quad = endpoint + mp.quad(diagonal_integrand, [0, L])
        polar_sine_quad = mp.quad(lambda h: 2 * mp.cosh(h / 2) * mp.sin(omega * h), [0, L])
        polar_diag_quad = mp.quad(
            lambda h: 2 * mp.cosh(h / 2) * diagonal_test(h), [0, L]
        )
        records.append(
            {
                "mode": mode,
                "arch_sine_abs_error": mp.nstr(abs(arch_sine(L, mode) - arch_sine_quad), 20),
                "arch_diagonal_abs_error": mp.nstr(abs(arch_diagonal(L, mode) - arch_diag_quad), 20),
                "polar_sine_abs_error": mp.nstr(abs(polar_sine(L, omega) - polar_sine_quad), 20),
                "polar_diagonal_abs_error": mp.nstr(abs(polar_diagonal(L, omega) - polar_diag_quad), 20),
                "prime_atom_count": len(atom_data),
            }
        )
    return records


def fft(values: list[complex], inverse: bool = False) -> list[complex]:
    """In-place-style radix-2 FFT returned as a fresh list."""
    data = list(values)
    size = len(data)
    if size == 0 or size & (size - 1):
        raise ValueError("FFT length must be a positive power of two")
    j = 0
    for i in range(1, size):
        bit = size >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            data[i], data[j] = data[j], data[i]
    length = 2
    sign = 1 if inverse else -1
    while length <= size:
        root = cmath.exp(sign * 2j * math.pi / length)
        half = length // 2
        for start in range(0, size, length):
            phase = 1 + 0j
            for offset in range(half):
                even = data[start + offset]
                odd = data[start + offset + half] * phase
                data[start + offset] = even + odd
                data[start + offset + half] = even - odd
                phase *= root
        length *= 2
    if inverse:
        data = [value / size for value in data]
    return data


def lag_diagnostics(
    L: float, N: int, vector: list[float], atom_data: list[tuple[int, mp.mpf, mp.mpf]], grid: int
) -> dict[str, object]:
    sample_count = 1 << max(10, math.ceil(math.log2(grid)))
    spectrum = [0j] * sample_count
    for mode, coefficient in zip(range(-N, N + 1), vector):
        spectrum[mode % sample_count] = coefficient
    values = [value * sample_count / math.sqrt(L) for value in fft(spectrum, inverse=True)]
    padded_values = values + [0j] * sample_count
    transformed = fft(padded_values)
    correlation_complex = fft([value.conjugate() * value for value in transformed], inverse=True)
    correlation = [value.real * L / sample_count for value in correlation_complex[:sample_count]]
    normalization = correlation[0]
    correlation = [value / normalization for value in correlation]
    dx = L / sample_count
    lags = [index * dx for index in range(sample_count)]
    differences = [correlation[index + 1] - correlation[index] for index in range(sample_count - 1)]
    min_index = min(range(sample_count), key=correlation.__getitem__)
    up_index = max(range(sample_count - 1), key=differences.__getitem__)
    negative = [index for index, value in enumerate(correlation) if value < -1e-10]
    upward = [index for index, value in enumerate(differences) if value > 1e-10]

    F = [2 * value for value in correlation]
    polar_density = [2 * math.cosh(h / 2) * value for h, value in zip(lags, F)]
    arch_density = [0.0] * sample_count
    boundary_value_sq = float(abs(values[0]) ** 2)
    arch_density[0] = 0.5 - boundary_value_sq
    for index in range(1, sample_count):
        h = lags[index]
        arch_density[index] = (
            math.exp(h / 2) * F[index] - 2
        ) / (math.exp(h) - math.exp(-h))
    polar_cumulative = [0.0] * sample_count
    arch_cumulative = [0.0] * sample_count
    for index in range(1, sample_count):
        polar_cumulative[index] = polar_cumulative[index - 1] + (
            polar_density[index - 1] + polar_density[index]
        ) * dx / 2
        arch_cumulative[index] = arch_cumulative[index - 1] + (
            arch_density[index - 1] + arch_density[index]
        ) * dx / 2
    prime_cumulative = [0.0] * sample_count
    prime_atoms: list[dict[str, float | int]] = []
    for k, lag_mp, weight_mp in atom_data:
        lag = float(lag_mp)
        weight = float(weight_mp)
        coordinate = lag / dx
        left = min(sample_count - 2, int(coordinate))
        fraction = coordinate - left
        value = F[left] * (1 - fraction) + F[left + 1] * fraction
        contribution = weight * value
        first = min(sample_count, math.ceil(coordinate))
        for index in range(first, sample_count):
            prime_cumulative[index] += contribution
        prime_atoms.append({"k": k, "lag": lag, "weight": weight, "F": value, "mass": contribution})
    polar_minus_prime = [p - s for p, s in zip(polar_cumulative, prime_cumulative)]
    budget_index = min(range(sample_count), key=polar_minus_prime.__getitem__)
    endpoint = float(mp.euler) + math.log(
        4 * math.pi * (math.exp(L) - 1) / (math.exp(L) + 1)
    )
    total_cumulative = [
        budget - arch for budget, arch in zip(polar_minus_prime, arch_cumulative)
    ]
    sample_indices = [round(index * (sample_count - 1) / 128) for index in range(129)]
    return {
        "sample_count": sample_count,
        "min_autocorrelation": float(correlation[min_index]),
        "min_autocorrelation_lag": float(lags[min_index]),
        "first_negative_lag": None if not negative else float(lags[negative[0]]),
        "negative_grid_points": int(len(negative)),
        "max_upward_step": float(differences[up_index]),
        "max_upward_step_lag": float(lags[up_index]),
        "first_upward_step_lag": None if not upward else float(lags[upward[0]]),
        "upward_grid_steps": int(len(upward)),
        "boundary_value_sq": boundary_value_sq,
        "min_polar_minus_prime_cumulative": float(polar_minus_prime[budget_index]),
        "min_polar_minus_prime_lag": float(lags[budget_index]),
        "final_polar_minus_prime": float(polar_minus_prime[-1]),
        "final_arch_integral": float(arch_cumulative[-1]),
        "arch_endpoint_constant": endpoint,
        "final_total_from_grid": float(total_cumulative[-1] - endpoint),
        "prime_atoms": prime_atoms,
        "downsample": [
            {
                "h": float(lags[i]),
                "C": float(correlation[i]),
                "polar_minus_prime": float(polar_minus_prime[i]),
                "total_without_endpoint": float(total_cumulative[i]),
            }
            for i in sample_indices
        ],
    }


def compute(
    a_text: str, N: int, digits: int, threads: int, grid: int, validate: bool = True
) -> dict[str, object]:
    mp.mp.dps = digits
    ctx.dps = digits
    ctx.threads = threads
    a = mp.mpf(a_text)
    L = 2 * a
    started = time.time()
    coordinates = component_coordinates(L, N)
    trace(f"coordinates {time.time() - started:.6f}s")
    assembled_coordinates = time.time()
    matrices = {
        name: build_matrix(source, diagonal, N, digits)
        for name, (source, diagonal) in coordinates.items()
    }
    total = matrices["polar"] + matrices["prime"] + matrices["arch"]
    trace(f"matrices {time.time() - assembled_coordinates:.6f}s")
    assembled_matrix = time.time()
    eigenvalues, eigenvectors = acb_mat(total).eig(right=True, algorithm="approx")
    trace(f"eigensolve {time.time() - assembled_matrix:.6f}s")
    diagonalized = time.time()
    eigenvalue_midpoints = [
        mp.mpf(eigenvalues[k].real.mid().str(digits - 10, radius=False))
        for k in range(2 * N + 1)
    ]
    index = min(range(2 * N + 1), key=eigenvalue_midpoints.__getitem__)
    vector = choose_real_eigenvector(eigenvectors, index)
    vector_column = arb_mat([[x] for x in vector])
    eigenvalue = rayleigh(total, vector)
    residual = total * vector_column - vector_column * eigenvalue
    reflection_residual = sum(
        ((vector[i] - vector[2 * N - i]) ** 2 for i in range(2 * N + 1)), arb(0)
    ).sqrt()
    component_energies = {name: rayleigh(matrix, vector) for name, matrix in matrices.items()}
    component_sum_error = abs(sum(component_energies.values(), arb(0)) - eigenvalue)
    reconstruction_error = max_abs_matrix(total - sum(matrices.values(), arb_mat(2 * N + 1, 2 * N + 1)))
    vector_float = [float(x) for x in vector]
    lag = lag_diagnostics(float(L), N, vector_float, atoms(L), grid)
    trace(f"lag diagnostics {time.time() - diagonalized:.6f}s")
    validations = direct_formula_validation(L, N) if validate else []
    trace(f"validation {time.time() - diagonalized:.6f}s cumulative")
    finished = time.time()
    sorted_eigenvalues = sorted(eigenvalue_midpoints)[: min(8, 2 * N + 1)]
    ground_is_positive = mp.mpf(midpoint_text(eigenvalue, digits - 10)) > 0
    return {
        "a": a_text,
        "L": mp.nstr(L, 30),
        "N": N,
        "dimension": 2 * N + 1,
        "digits": digits,
        "threads": threads,
        "ground_eigenvalue": midpoint_text(eigenvalue, digits - 10),
        "minus_log_ground_if_positive": None if not ground_is_positive else midpoint_text(-eigenvalue.log(), 40),
        "lowest_eigenvalues": [mp.nstr(value, 50) for value in sorted_eigenvalues],
        "component_energies": {
            name: midpoint_text(value, digits - 10) for name, value in component_energies.items()
        },
        "component_sum_error": midpoint_text(component_sum_error, 30),
        "matrix_reconstruction_error": midpoint_text(reconstruction_error, 30),
        "eigen_residual_max": midpoint_text(max_abs_matrix(residual), 30),
        "reflection_residual": midpoint_text(reflection_residual, 30),
        "ground_coefficients_centered": [midpoint_text(x, digits - 10) for x in vector],
        "lag_diagnostics": lag,
        "formula_validation": validations,
        "prime_atoms": [
            {"k": k, "lag": mp.nstr(lag_value, 40), "weight": mp.nstr(weight, 40)}
            for k, lag_value, weight in atoms(L)
        ],
        "timings": {
            "coordinates_seconds": assembled_coordinates - started,
            "matrix_seconds": assembled_matrix - assembled_coordinates,
            "eigensolve_seconds": diagonalized - assembled_matrix,
            "diagnostics_seconds": finished - diagonalized,
            "total_seconds": finished - started,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--digits", type=int, default=120)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--grid", type=int, default=16384)
    parser.add_argument("--no-validation", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    payload = compute(
        args.a, args.N, args.digits, args.threads, args.grid, not args.no_validation
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "a": payload["a"],
        "N": payload["N"],
        "ground_eigenvalue": payload["ground_eigenvalue"],
        "lag_diagnostics": {
            key: payload["lag_diagnostics"][key]
            for key in (
                "min_autocorrelation", "first_negative_lag", "max_upward_step",
                "first_upward_step_lag", "min_polar_minus_prime_cumulative",
            )
        },
        "timings": payload["timings"],
    }, indent=2))


if __name__ == "__main__":
    main()
