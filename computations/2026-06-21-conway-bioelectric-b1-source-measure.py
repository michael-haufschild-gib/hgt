#!/usr/bin/env python3
"""THE-MACHINE tick: bioelectric/canonical interaction -> B1 source-measure bridge.

NODE:
  Bioelectric cues interact with canonical pathways such as Wnt, BMP, Notch, Hedgehog,
  and FGF rather than replacing them.

Consolidated target:
  14/32 B1 source-measure bridge.

STEP 9 method:
  13. Find a monotone quantity.
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass

import numpy as np


NODE = (
    "Bioelectric cues often interact with canonical pathways such as Wnt, BMP, Notch, "
    "Hedgehog, and FGF rather than replacing them"
)
TARGET = "14/32 B1 source-measure bridge"
METHOD = "13. Find a monotone quantity"

TRANSFER_ATTEMPTS = [
    "bioelectric canonical interaction becomes transport source-measure interaction",
    "voltage cues gate canonical pathways like carriers gate source measure",
    "bioelectric replacement failure becomes B1 carrier replacement failure",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def sigmoid(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-x))


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: bioelectric cues gate canonical pathways instead of replacing them"]
    lines.append(
        "Constraint: a positional outcome can require an interaction term V*W; voltage alone "
        "or canonical morphogen alone gives a wrong boundary."
    )
    x = np.linspace(0.0, 1.0, 220)
    wnt = 1.0 - x
    voltage = np.exp(-((x - 0.62) / 0.18) ** 2)
    target = ((x > 0.48) & (x < 0.73)).astype(float)
    lines.append("coupling canonical_only voltage_only additive interaction boundary_error")
    for coupling in [0.0, 0.5, 1.0, 2.0, 4.0, 7.0]:
        canonical_only = sigmoid(9.0 * (wnt - 0.52))
        voltage_only = sigmoid(9.0 * (voltage - 0.45))
        additive = sigmoid(7.0 * (0.55 * wnt + 0.45 * voltage - 0.55))
        interaction = sigmoid(7.0 * (0.55 * wnt + 0.45 * voltage + coupling * wnt * voltage - 0.88))
        # Boundary error is the symmetric difference of high-expression regions.
        err = float(np.mean((interaction > 0.5) != (target > 0.5)))
        lines.append(
            f"{coupling:8.2f} {np.mean((canonical_only>0.5)!=(target>0.5)):.6f} "
            f"{np.mean((voltage_only>0.5)!=(target>0.5)):.6f} "
            f"{np.mean((additive>0.5)!=(target>0.5)):.6f} {err:.6f}"
        )
    lines.append(
        "NODE verdict: the error is minimized only after the V*W interaction is admitted; "
        "the voltage cue is not a replacement pathway."
    )
    return lines


def contour_charge(field, center: complex, half_w: float = 0.055, half_h: float = 0.55, samples: int = 160) -> complex:
    pts = []
    # Counter-clockwise rectangle in s = sigma + i t.
    for u in np.linspace(-half_w, half_w, samples, endpoint=False):
        pts.append(center + complex(float(u), -half_h))
    for v in np.linspace(-half_h, half_h, samples, endpoint=False):
        pts.append(center + complex(half_w, float(v)))
    for u in np.linspace(half_w, -half_w, samples, endpoint=False):
        pts.append(center + complex(float(u), half_h))
    for v in np.linspace(half_h, -half_h, samples, endpoint=False):
        pts.append(center + complex(-half_w, float(v)))
    pts.append(pts[0])
    integ = 0.0 + 0.0j
    for a, b in zip(pts, pts[1:]):
        mid = 0.5 * (a + b)
        integ += field(mid) * (b - a)
    return integ / (2j * math.pi)


def transport_carrier(field, center: complex, half_w: float = 0.09, half_h: float = 0.65) -> float:
    sigmas = np.linspace(center.real - half_w, center.real + half_w, 33)
    ts = np.linspace(center.imag - half_h, center.imag + half_h, 73)
    vals = np.empty((len(ts), len(sigmas)), dtype=complex)
    for j, t in enumerate(ts):
        for i, sigma in enumerate(sigmas):
            vals[j, i] = field(complex(float(sigma), float(t)))
    logabs = np.log(np.abs(vals) + 1e-12)
    phase = np.unwrap(np.unwrap(np.angle(vals), axis=0), axis=1)
    dlog_dt, dlog_ds = np.gradient(logabs, ts, sigmas)
    dph_dt, dph_ds = np.gradient(phase, ts, sigmas)
    area_density = np.abs(dlog_ds * dph_dt - dlog_dt * dph_ds)
    return float(np.mean(np.log1p(area_density)))


def pole_field(poles: list[complex], residues: list[complex], background: complex = 0.04 + 0.03j):
    def field(s: complex) -> complex:
        out = background
        for rho, res in zip(poles, residues):
            denom = s - rho
            if abs(denom) < 1e-10:
                denom = complex(1e-10, 1e-10)
            out += res / denom
        return out

    return field


def smooth_external_field(external: complex, strength: complex = 1.8 + 0.5j):
    def field(s: complex) -> complex:
        return 0.05 + strength / (s - external)

    return field


@dataclass
class WindowResult:
    name: str
    center: complex
    expected_source: int
    off_seam: int
    charge: float
    carrier: float


def b1_windows() -> list[WindowResult]:
    cases = [
        (
            "seam_source",
            complex(0.50, 25.0),
            pole_field([complex(0.50, 25.0)], [1.0 + 0.0j]),
            1,
            0,
        ),
        (
            "off_source",
            complex(0.62, 25.0),
            pole_field([complex(0.62, 25.0)], [1.0 + 0.0j]),
            1,
            1,
        ),
        (
            "paired_off_sources",
            complex(0.62, 25.0),
            pole_field([complex(0.62, 25.0), complex(0.38, 25.0)], [1.0 + 0.0j, 1.0 + 0.0j]),
            1,
            1,
        ),
        (
            "smooth_nearby_fake",
            complex(0.62, 25.0),
            smooth_external_field(complex(0.74, 25.0)),
            0,
            1,
        ),
        (
            "smooth_seam_fake",
            complex(0.50, 25.0),
            smooth_external_field(complex(0.62, 25.0)),
            0,
            0,
        ),
        (
            "quiet_window",
            complex(0.62, 25.0),
            lambda s: 0.05 + 0.03j + 0.01 * (s - complex(0.62, 25.0)),
            0,
            1,
        ),
    ]
    out = []
    for name, center, field, expected_source, off_seam in cases:
        q = contour_charge(field, center)
        carrier = transport_carrier(field, center)
        out.append(
            WindowResult(
                name=name,
                center=center,
                expected_source=expected_source,
                off_seam=off_seam,
                charge=abs(q),
                carrier=carrier,
            )
        )
    return out


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The NODE interaction formula V*W cannot be applied unchanged. Minimal B1 transfer: "
        "transport carriers are the bioelectric-like cues, source measure/contour charge is the "
        "canonical pathway, and the bridge must test their interaction rather than replacement."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER ATTEMPTS")
    best: tuple[int, int, str] | None = None
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        dist = levenshtein(NODE.lower(), attempt.lower())
        lines.append(f"{i}. distance={dist:3d} {attempt}")
        if best is None or dist < best[0]:
            best = (dist, i, attempt)
    assert best is not None
    lines.append(f"selected={best[1]} {best[2]}")
    lines.append(f"\nSTEP 9 METHOD {METHOD}")
    lines.append(
        "Monotone quantity: false source-carrying transport calls as the source-measure "
        "coupling alpha increases in score = carrier * ((1-alpha) + alpha*min(1,|charge|/0.5))."
    )
    rows = b1_windows()
    lines.append("window beta expected_source off_seam charge carrier")
    for r in rows:
        lines.append(
            f"{r.name:18s} {r.center.real:.2f} {r.expected_source:d} {r.off_seam:d} "
            f"{r.charge:.6f} {r.carrier:.6f}"
        )
    carrier_threshold = 0.24
    score_threshold = 0.24
    lines.append(f"carrier_threshold={carrier_threshold:.2f}; score_threshold={score_threshold:.2f}")
    lines.append("alpha true_source_calls false_source_calls off_seam_source_calls calls")
    for alpha in [0.0, 0.25, 0.50, 0.75, 0.90, 0.95, 1.00]:
        calls = []
        for r in rows:
            gate = min(1.0, r.charge / 0.5)
            score = r.carrier * ((1.0 - alpha) + alpha * gate)
            if score >= score_threshold:
                calls.append(r)
        true_calls = sum(r.expected_source for r in calls)
        false_calls = sum(1 - r.expected_source for r in calls)
        off_calls = sum(r.expected_source and r.off_seam for r in calls)
        names = ",".join(r.name for r in calls) or "-"
        lines.append(f"{alpha:5.2f} {true_calls:17d} {false_calls:18d} {off_calls:21d} {names}")
    lines.append(
        "STEP 10 verdict: transport-only (alpha=0) calls smooth source-free fakes. As source-measure "
        "coupling rises, false calls monotonically disappear while source-carrying defects persist."
    )
    lines.append(
        "STEP 11 metaphor: B1 should not let the carrier replace the source measure. The native "
        "bridge is an interaction gate: source-carrying transport, not transport-looking geometry."
    )
    return lines


def main() -> None:
    for row in node_rows():
        print(row)
    for row in transfer_rows():
        print(row)
    print("\nDEAD_END: B1_SOURCE_MEASURE_INTERACTION_GATE_REDUCES_TO_CONTOUR_CHARGE")
    print(
        "The interaction gate is a useful sanity check, but it kills smooth fakes because the "
        "contour charge is zero. That is the known source-measure/argument-principle gate, not a "
        "new B1 bridge."
    )


if __name__ == "__main__":
    main()
