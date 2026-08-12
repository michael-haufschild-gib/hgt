# Step 50: the probe-circle criterion and the Hermitian wall's final form [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiProbeCircleCriterion.lean` (imports
GaussHodgeWeilPositivityCone), wired last in RHTower.lean. Four theorems + two defs, all
[propext, Classical.choice, Quot.sound].

## Theorems

- `xiOnLineProbeProfile γ x = 2x/(γ² + x²)`; `xiBudgetMassAt_eq_online_smear`:
  massAt(c)_q = (profile γ (c−b) + profile γ (c+b))/2 with γ = Re α, b = Im α — pure ring
  identity. THE SMEARING LAW: off-line copies are probe-displaced on-line copies
  (displacement < strip half-width 1/2). Explains: floor ceiling (step 49), finite-probe
  maskability, why sampling can never resolve the line.
- `xiProbeCoordinate c q := ((c:ℂ) − I·conj(α))⁻¹` (pole of the probe response at i·ᾱ);
  denominator re = c − b, im = −γ, nonzero via the 32-floor.
- `xiProbeCoordinate_circle_iff`: Re x = c·normSq x ⟺ Im α = 0 (on-line). (Circle = image of
  critical axis under probe inversion; proof: inv_re, normSq_inv, field_simp.)
- `riemannHypothesis_iff_forall_probeCoordinate_circle (c : ℝ)`: RH ⟺ ∀ q, circle relation.
  Forward via xiSpectralPoint_real_of_rh; backward via exists_spectralSq_im_pos pattern.

## The death and the law

The circle relation is quadratic HERMITIAN: x·x̄ = (x + x̄)/(2c). All prime-side data — the
ray-jet family and every derivative (certified prime sums Σ Λ(n)(log n)ᵏ n^{-s} + Γ-jets) —
are HOLOMORPHIC moments Σ r·xᵏ of the divisor atoms. Testing the circle needs mixed moments
Σ r·xʲ·x̄ˡ — the Σg² vs Σ|g|² holomorphy gap. THE CONSERVED WALL, three independent
manifestations now: (46) supply/certificate polynomial-family disjointness; (49) cone/detector
vacuity (unconditional positivity is spectrally silent); (50) holomorphic/Hermitian moment gap.
Final form of the law: prime-side linear data = holomorphic moments; RH = one Hermitian
quadratic relation on the atoms; no functional of holomorphic moments computes a Hermitian
relation. The unique entry: a Hermitian-valued arithmetic identity — autocorrelated explicit
formulas (Route E "correlations wall": form-factor computable only in the classical
uncertainty range) or a definitizable Krein intertwiner (Gauss lane step-7 verdict).

## Programme status

Steps 36-50: the criterion/effectivity interface is COMPLETE — countable rational-nodal
endpoint, relative/floor unconditionalization, effective windows/masking/delay, mass budget,
tail surrogate, Weil-positivity cone, and the wall mapped with theorem-grade precision from
three directions. Remaining mathematics lives entirely in the bilinear arithmetic input.
Card: xic-order-one-growth-organ.md step 50; Gauss hub step 16.
