#!/usr/bin/env python3
"""Structural verifier for exact modular seam discovery output."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> None:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    data = json.loads((root / "results.json").read_text())
    c5 = data["c5_fixed_action_seam"]
    assert c5["c5_jacobian_first_seam_coefficient"]["decomposition_verified"]
    assert not c5["c5_jacobian_first_seam_coefficient"]["shift_191_10"]["positive_coefficients"]
    assert not c5["new_Q_block"]["shift_191_10"]["positive_coefficients"]
    assert c5["reverse_minor"]["shift_191_10"]["positive_coefficients"]
    assert c5["c5_jacobian_first_seam_coefficient"]["bernstein_191_10_to_20"]["positive_coefficients"]
    assert c5["c5_jacobian_first_seam_coefficient"]["bernstein_191_10_to_20"]["reconstruction_verified"]
    s6f = data["s6f_projective_drift_seam"]
    assert s6f["drift_on_seam"] == "0"
    assert s6f["physical_flow_derivative_at_seam"]["shift_191_10"]["positive_coefficients"]
    odd = s6f["physical_flow_odd_derivatives_at_seam"]
    assert set(odd) == {"1", "3", "5"}
    assert odd["1"]["shift_191_10"]["positive_coefficients"]
    assert odd["3"]["shift_191_10"]["negative_coefficients"]
    assert odd["5"]["shift_191_10"]["positive_coefficients"]
    print("verified: exact decompositions, C5 interval certificate, and S6F odd seam-derivative audit")


if __name__ == "__main__":
    main()
