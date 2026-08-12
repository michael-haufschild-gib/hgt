# Steps 40 + 40b: polynomial descent step + nodal single-minor criterion [LEAN-PROVED]

Both modules axiom-clean ([propext, Classical.choice, Quot.sound]), olean-built, wired into
`RHTower.lean` after `XiResolventEffectiveTuranDetection`.

## XiResolventEffectivePolynomialDescent.lean

- `poly_minor_truncation_le_of_offline_level`: effective window at weight `P(u)²` for real `P`
  killing every copy above level ℓ: `N ≤ (2S²b⁴/g + b⁴S²/(ℓ²−ρ₂²))/(Im(u_qh)²·‖P(u_qh)‖⁴)`
  with `b = evalRealPolynomialNormBound P 1`. Pure instantiation of the step-39 window
  (xiPolyMoment IS definitionally the weighted moment — pass hminor by defeq).
- `poly_single_minor_truncation_le_of_offline_level`: same, data = single (0,2,1) minors at the
  N polynomials `X^n·P` (index shift `xiPolyMoment_X_pow_mul` + omega normalizations).
- `level_criticalLine_of_poly_single_minors_window`: finite polynomial jet certificate.

## XiResolventNodalSingleMinorCriterion.lean — the sharpened RH endpoint

- `def nodalPolynomial R = ∏_{r ∈ R} (X − C r)`; `evalRealPolynomial_nodalPolynomial`.
- `riemannHypothesis_iff_forall_nodal_single_minor {X} (hX : 0 ≤ X)`:
  RH ⟺ ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m,
  `0 ≤ (M_p(0)M_p(2) − M_p(1)²).re` for `p = Polynomial.X ^ m * nodalPolynomial R`.
  STRICT sharpening of step 37: test family = monic real-rooted polynomials, roots in [0,1],
  instead of all real polynomials.
- Backward proof = descent clone (strong induction on ncard of higher-modulus copies) noting the
  killing polynomial IS `nodalPolynomial atoms` with atoms = norms (∈ (0,1]) of higher copies
  (real by IH); per level the EVEN machine + index shift consume exactly the nodal single-minor
  data. Forward = a fortiori from `polyTuranMinor_re_nonneg_of_riemannHypothesis` with
  `simpa only [Nat.zero_add]`.

## Audit

Restricting to real-rooted squares would weaken a Hamburger-type positivity condition; the
equivalence survives at the thin family because detection is descent oscillation and the
killing weights are constructed inside the family. Distinct from Laguerre–Pólya/Jensen
hyperbolicity (coefficient-side). [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] provisional.

## Next

(i) rational-node density → countable closed-form criterion (needs node-Lipschitz stability of
the datum — effective constants exist from steps 39/40); (ii) window optimality vs step-38
masking config; (iii) arithmetic supply of first nodal data via two-scale bridge
(`XiResolventPartialLineSupply`). Card: xic-order-one-growth-organ.md steps 39-40b.
