# Order-free degree-zero classification on the small-abscissa stratum

- **ID:** order-free-degree-zero-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** An ordinary Dirichlet series `L(s) = Σ aₙ n^{−s}` absolutely convergent at some
  real `σ₀ < 1/2` and satisfying, on the overlap strip `σ₀ < Re s < 1−σ₀`, a reflection identity
  with finite conductor datum `L(s) = (Σ_{j∈J} c_j Q_j^{1−2s})·L(1−s)`, has coefficients supported
  on `⋃_j div(Q_j²)` and obeying the exact pairing
  `aₘ·m^{−½} = Σ_{j∈J} (if m ∣ Q_j² then c_j·a_{Q_j²/m}·(Q_j²/m)^{−½} else 0)` — with NO order,
  growth, integrality, or multiplicativity hypothesis. In the trivial-datum case (`h = 1`,
  `L(s) = L(1−s)`) the series is constant.
- **Lean:** `OverlapRigidity.lean` (`sine_series_coeffs_zero`, `overlap_rigidity`,
  `overlap_rigidity_lseries_eq_one`), `BohrCoefficientUniqueness.lean` (`char_avg_finsum`,
  `char_avg_tendsto`, `char_series_coeff_zero`, `conductor_datum_finite_support`,
  `conductor_datum_pairing`, `conductor_datum_pairing_coeff`). All
  `[propext, Classical.choice, Quot.sound]`; umbrella build green; lint green. Mechanism:
  fixed-locus evaluation at `s = ½ + iy` turns the datum into pure phases; Cesàro (Bohr)
  mean-value orthogonality of the characters `e^{iy log n}` (Kronecker–Weyl engine
  `Weyl.char_term_time_average_tendsto`) extracts each coefficient; the frequency equation
  `log m + log n = 2 log Q_j ⟺ mn = Q_j²` produces support and pairing simultaneously.
- **Dual gate:** NOVEL — the Kaczorowski–Perelli degree-0 classification carries the Selberg-class
  finite-order axiom as a standing hypothesis; on the small-abscissa stratum the axiom is
  removed outright, and the literature does not pose the gammaless/orderless case ([ABSENT]²
  verdicts on the checks file). × SIGNIFICANT — first machine-checked cell of the C-COC program
  (reflection-cocycle datum rigidity): the `h = 1` cell and every finite-conductor cell close
  unconditionally on `σ₀ < 1/2`, localizing all remaining C-COC content to the `σ_a ≥ 1/2`
  stratum (quiet-crossing / INT-ORDER wall — companion reductions `GammalessStripRigidity.lean`,
  `QuietCrossingRigidity.lean` in progress on card `goldilocks-divisor-rigidity`).

## Log
- 2026-07-09 — proven on paper (fixed-locus Bohr matching), formalized both halves
  (support + pairing), verified axiom-clean; card `goldilocks-divisor-rigidity.md` carries the
  surrounding research program.
