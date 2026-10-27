import GaloisForLFunctions.BiarithmeticGaugeGeometry.PositiveCoupledRigidityAndTheCriticalTransferLaw
import GaloisForLFunctions.BiarithmeticGaugeGeometry.CentralExcessForcesASquareRootPrimeDeficit

/-!
# Strong Multiplicity One Below the Square-Root Deficit

An arithmetic member of `HeightCoupledSystem 2 1 1 γ` is a pair `(F, Λ)` with
`−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`. Its deficit against `ζ_γ` is `d(n) = (b_γ(n) − b(n))⁺`, where
`b_γ(n) = Λ(n)(2 + 2 cos(γ log n))`. A central excess forces `Σ d(n) n^{−s}` to have abscissa at
least `½` (`centralExcess_forces_squareRoot_deficit`). Below that threshold the arithmetic class is
rigid.

* **Strong multiplicity one (`latticeMember_eq_of_subcritical_deficit`).** If `ξ` has no
  off-critical zero at ordinate `γ`, the deficit series has abscissa `< ½`, and the central order
  does not drop, then `b(n) = b_γ(n)` for every `n ≥ 1` and `F = K ζ_γ` with `K ∈ ℝ^×`.
  The surplus is a positive measure and `b(1) − D` is holomorphic on `Re s > σ_E` for some
  `σ_E < ½`, so the critical transfer law applies and `Λ` has the divisor of `Λ_γ`; divisor rigidity
  gives `F = K ζ_γ`, and the coefficients agree by uniqueness of Dirichlet series.
* **Square-root deficit for equal central order (`half_le_deficit_abscissa_of_ne`).** A member with
  the central order of `ζ_γ` whose coefficients differ from `b_γ` has deficit abscissa `≥ ½`.
* **Arithmetic chirality (`latticeMember_eq_or_centralDrop`).** With subcritical deficit, either
  `b = b_γ` or the central order strictly drops (and then every critical jump is bounded by the drop,
  `abs_criticalTransfer_le_centralDrop`).
* **Zero-free ordinates (`latticeMember_eq_of_xi_ne_zero_on_line`).** If `ξ` has no zero on
  `Im s = γ`, every arithmetic member with subcritical deficit has the coefficients of `ζ_γ`; this
  holds unconditionally at `γ = 0`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry

/-- **Strong multiplicity one below the square-root deficit.** If `ξ` has no off-critical zero at
ordinate `γ`, an arithmetic member of `HeightCoupledSystem 2 1 1 γ` whose deficit series has
abscissa `< ½` and whose central order is at least that of `Λ_γ` has the coefficients of `ζ_γ`
and is a nonzero real multiple of it. -/
theorem latticeMember_eq_of_subcritical_deficit {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) < (1 / 2 : ℝ))
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat) :
    (∀ n, n ≠ 0 → b n = heightCoupledVonMangoldt γ n) ∧
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s := by
  obtain ⟨σE, hσEd, hσE⟩ := EReal.lt_iff_exists_real_btwn.mp hdef
  have hσE' : σE < 1 / 2 := by exact_mod_cast hσE
  set D : ℂ → ℂ := LSeries (fun n => (latticeDeficit γ b n : ℂ)) with hDdef
  have hE : DifferentiableOn ℂ (fun s => (b 1 : ℂ) - D s) {s : ℂ | σE < s.re} := fun s hs =>
    ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_trans hσEd
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := latticeMember_primeMass_split (γ := γ) hb habs hL
  obtain ⟨K, hK0, -, hFK⟩ := eq_const_mul_of_orders_eq hHC
    (perturbedDeformation_orders_eq_of_central_le hoff hHC hmass hσE' hE hsplit hcent)
  refine ⟨fun n hn => ?_, K, hK0, hFK⟩
  -- `F = K ζ_γ` makes the two Dirichlet series agree on `Re s > 1`
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLeq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s =
      LSeries (fun n => (heightCoupledVonMangoldt γ n : ℂ)) s := by
    intro s hs
    have hev : F =ᶠ[𝓝 s] fun w => (K : ℂ) * heightCoupledF riemannZeta γ w :=
      Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => hFK w hw
    rw [← hL s hs, ← neg_logDeriv_heightCoupledF_eq_LSeries γ hs, logDeriv_apply, hev.deriv_eq,
      hev.eq_of_nhds, ← logDeriv_apply, logDeriv_const_mul _ _ (by exact_mod_cast hK0)]
  have h1top : (1 : EReal) < ⊤ := by exact_mod_cast EReal.coe_lt_top 1
  have h := LSeries.eq_of_LSeries_eventually_eq (f := fun n => (b n : ℂ))
    (g := fun n => (heightCoupledVonMangoldt γ n : ℂ)) (lt_of_le_of_lt habs h1top)
    (lt_of_le_of_lt (abscissaOfAbsConv_heightCoupledVonMangoldt_le_one γ) h1top)
    (Filter.eventually_atTop.mpr ⟨2, fun x hx => hLeq x (by simp only [Complex.ofReal_re]; linarith)⟩)
    hn
  exact_mod_cast h

/-- **Equal central order forces a square-root deficit.** If `ξ` has no off-critical zero at
ordinate `γ`, an arithmetic member with the central order of `Λ_γ` (or more) whose coefficients
differ from those of `ζ_γ` has deficit abscissa at least `½`. -/
theorem half_le_deficit_abscissa_of_ne {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat)
    (hne : ∃ n, n ≠ 0 ∧ b n ≠ heightCoupledVonMangoldt γ n) :
    ((1 / 2 : ℝ) : EReal) ≤ LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn, hbn⟩ := hne
  exact hbn ((latticeMember_eq_of_subcritical_deficit hoff hHC hb habs hL hlt hcent).1 n hn)

/-- **Arithmetic chirality.** If `ξ` has no off-critical zero at ordinate `γ`, an arithmetic member
with subcritical deficit has the coefficients of `ζ_γ` or strictly lowers the central order. -/
theorem latticeMember_eq_or_centralDrop {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) < (1 / 2 : ℝ)) :
    (∀ n, n ≠ 0 → b n = heightCoupledVonMangoldt γ n) ∨
      (analyticOrderAt Λ (1 / 2)).toNat <
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat := by
  rcases lt_or_ge (analyticOrderAt Λ (1 / 2)).toNat
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat with h | h
  · exact Or.inr h
  · exact Or.inl (latticeMember_eq_of_subcritical_deficit hoff hHC hb habs hL hdef h).1

/-- `Λ_γ(½) ≠ 0` when `ξ` has no zero on the horizontal line `Im s = γ`. -/
theorem centralOrder_heightCoupledΛ_eq_zero {γ : ℝ}
    (hfree : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0) :
    (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat = 0 := by
  have hne : heightCoupledΛ (fun s => 2 * RHTower.xi s) γ ((1 / 2 : ℝ) : ℂ) ≠ 0 := fun h =>
    hfree _ (xi_add_eq_zero_of_heightCoupledΛ_real_zero h)
  have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [hhalf] at hne
  rw [((zeta_mem_heightCoupledSystem γ).entire_Λ.analyticAt _).analyticOrderAt_eq_zero.mpr hne]
  rfl

/-- **Strong multiplicity one at zero-free ordinates.** If `ξ` has no zero on `Im s = γ`, every
arithmetic member of `HeightCoupledSystem 2 1 1 γ` with subcritical deficit has the coefficients of
`ζ_γ` and is a nonzero real multiple of it. -/
theorem latticeMember_eq_of_xi_ne_zero_on_line {γ : ℝ}
    (hfree : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) < (1 / 2 : ℝ)) :
    (∀ n, n ≠ 0 → b n = heightCoupledVonMangoldt γ n) ∧
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s :=
  latticeMember_eq_of_subcritical_deficit (fun x hx => absurd hx (hfree x)) hHC hb habs hL hdef
    (by rw [centralOrder_heightCoupledΛ_eq_zero hfree]; exact Nat.zero_le _)

/-- Strong multiplicity one holds unconditionally at height `0`. -/
theorem latticeMember_eq_of_subcritical_deficit_zero {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 0 F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit 0 b n : ℂ)) < (1 / 2 : ℝ)) :
    (∀ n, n ≠ 0 → b n = heightCoupledVonMangoldt 0 n) ∧
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta 0 s :=
  latticeMember_eq_of_xi_ne_zero_on_line (fun x => by simpa using RHTower.xi_ne_zero_of_real x)
    hHC hb habs hL hdef

end GaloisForLFunctions.BiarithmeticGaugeGeometry
