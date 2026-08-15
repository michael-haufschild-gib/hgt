import Mathlib

/-!
# The prolate endpoint jet grows: no fixed truncation is cofinal

Four exact mechanisms of the card are formalized.

*The endpoint identity.*  Evaluating the prolate equation at `x = 1` kills the second-derivative
coefficient and leaves `2ψ'(1) = (κ − c²)ψ(1)`, which is `(2)`.

*The scaled logarithmic derivative.*  For the CCM scaling `e(x) = N ψ(x/λ)` the endpoint
logarithmic derivative is `(κ − c²)/(2λ)`, which is `(4)`.

*The critical scale.*  With `c = 2πλ²` this is exactly `−2π²λ³ + κ/(2λ)`, which is `(6)`.

*Failure of a fixed jet order.*  The ratio `(11)` of the second endpoint term to the first at
`y = λ` is at least `πλ² − O(1)`, so it grows polynomially — equation `(12)`.  No fixed jet
truncation can be cofinal.

The prolate Sturm–Liouville theory, the fixed-mode asymptotic `(5)`, the integration-by-parts
expansion `(10)` and the two-scale boundary laws are cited parents and stay outside the Lean
statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The endpoint identity -/

/-- **Equation (2).**  At the regular endpoint the prolate equation degenerates to the exact
first-order relation. -/
theorem prolate_endpoint_identity (psival psid psidd kap c : ℝ)
    (hode : (1 - (1 : ℝ) ^ 2) * psidd - 2 * 1 * psid + (kap - c ^ 2 * (1 : ℝ) ^ 2) * psival = 0) :
    2 * psid = (kap - c ^ 2) * psival := by
  norm_num at hode
  linarith

/-! ## The scaled logarithmic derivative -/

/-- The derivative of the CCM-scaled mode at the endpoint. -/
theorem hasDerivAt_scaledMode {psi : ℝ → ℝ} {d N lam : ℝ} (hlam : lam ≠ 0)
    (hpsi : HasDerivAt psi d 1) :
    HasDerivAt (fun x : ℝ => N * psi (x / lam)) (N * d / lam) lam := by
  have hinner : HasDerivAt (fun x : ℝ => x / lam) (1 / lam) lam := by
    simpa using (hasDerivAt_id lam).div_const lam
  have hval : lam / lam = 1 := div_self hlam
  have hcomp : HasDerivAt (fun x : ℝ => psi (x / lam)) (d * (1 / lam)) lam := by
    have hpsi' : HasDerivAt psi d (lam / lam) := by rwa [hval]
    have h : HasDerivAt (psi ∘ fun x : ℝ => x / lam) (d * (1 / lam)) lam :=
      HasDerivAt.comp lam hpsi' hinner
    exact h
  have hmul := hcomp.const_mul N
  refine hmul.congr_deriv ?_
  field_simp

/-- **Equation (4).**  The endpoint logarithmic derivative of the scaled mode. -/
theorem scaled_logDeriv_eq {psival d N lam kap c : ℝ} (hlam : lam ≠ 0) (hN : N ≠ 0)
    (hval : psival ≠ 0) (hend : 2 * d = (kap - c ^ 2) * psival) :
    (N * d / lam) / (N * psival) = (kap - c ^ 2) / (2 * lam) := by
  have hd : d = (kap - c ^ 2) * psival / 2 := by linarith
  rw [hd]
  field_simp

/-! ## The critical scale -/

/-- **Equation (6).**  In the CCM scaling `c = 2πλ²` the endpoint logarithmic derivative is exactly
`−2π²λ³` plus the eigenvalue remainder. -/
theorem critical_scale_logDeriv {kap lam : ℝ} (hlam : lam ≠ 0) :
    (kap - (2 * Real.pi * lam ^ 2) ^ 2) / (2 * lam)
      = -2 * Real.pi ^ 2 * lam ^ 3 + kap / (2 * lam) := by
  field_simp
  ring

/-! ## Failure of a fixed jet order -/

/-- **Equations (11)–(12).**  The ratio of the second endpoint term to the first at `y = λ` is at
least `πλ² − O(1)`: the nominal `1/y²` term is polynomially larger than the nominal `1/y` term. -/
theorem jet_ratio_ge {lam r C : ℝ} (hlam : 0 < lam) (hr : |r| ≤ C * lam) :
    Real.pi * lam ^ 2 - C / (2 * Real.pi)
      ≤ |(-2 * Real.pi ^ 2 * lam ^ 3 + r)| / (2 * Real.pi * lam) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < 2 * Real.pi * lam := by positivity
  have hlower : 2 * Real.pi ^ 2 * lam ^ 3 - C * lam
      ≤ |(-2 * Real.pi ^ 2 * lam ^ 3 + r)| := by
    have habs : |(-2 * Real.pi ^ 2 * lam ^ 3 + r)|
        ≥ |(-2 * Real.pi ^ 2 * lam ^ 3)| - |r| := by
      have hh := abs_sub_abs_le_abs_sub (-2 * Real.pi ^ 2 * lam ^ 3) (-r)
      rw [abs_neg] at hh
      have hrw : (-2 * Real.pi ^ 2 * lam ^ 3) - (-r) = -2 * Real.pi ^ 2 * lam ^ 3 + r := by ring
      rw [hrw] at hh
      linarith
    have hneg : |(-2 * Real.pi ^ 2 * lam ^ 3)| = 2 * Real.pi ^ 2 * lam ^ 3 := by
      rw [abs_of_nonpos (by nlinarith [pow_pos hlam 3])]
      ring
    rw [hneg] at habs
    linarith
  have hprod : (Real.pi * lam ^ 2 - C / (2 * Real.pi)) * (2 * Real.pi * lam)
      = 2 * Real.pi ^ 2 * lam ^ 3 - C * lam := by
    field_simp
  rw [le_div_iff₀ hden, hprod]
  exact hlower

end GaloisForLFunctions.RHTower

end
