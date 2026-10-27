import GaloisForLFunctions.BiarithmeticGaugeGeometry.PositiveCoupledRigidityAndTheCriticalTransferLaw
import GaloisForLFunctions.BiarithmeticGaugeGeometry.CentralExcessForcesASquareRootPrimeDeficit

/-!
# Strong Multiplicity One Below the Square-Root Deficit

An arithmetic member of `HeightCoupledSystem 2 1 1 γ` is a pair `(F, Λ)` with
`−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`. Its deficit against `ζ_γ` is `d(n) = (b_γ(n) − b(n))⁺`, where
`b_γ(n) = Λ(n)(2 + 2 cos(γ log n))`. A central excess forces `Σ d(n) n^{−s}` to have abscissa at
least `½` (`centralExcess_forces_squareRoot_deficit`). Below that threshold the arithmetic class is
rigid.

* **The Abel-residue threshold (`latticeMember_eq_of_negligible_deficit`).** If `ξ` has no
  off-critical zero at ordinate `γ`, the deficit series converges on `Re s > ½` with zero Abel
  residue, `(σ − ½) Σ d(n) n^{−σ} → 0`, and the central order does not drop, then `b(n) = b_γ(n)` for
  every `n ≥ 1` and `F = K ζ_γ` with `K ∈ ℝ^×`; in particular when the deficit has abscissa `< ½`
  (`latticeMember_eq_of_subcritical_deficit`). With the deficit–excess law this makes the Abel
  residue of the deficit at `½` the exact invariant: zero residue forbids any change at constant
  central order, and a central excess needs residue at least the excess.
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

/-- A Dirichlet series with nonnegative coefficients is dominated on vertical lines by its value on
the real axis. -/
theorem norm_LSeries_le_re_of_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) {s : ℂ}
    (hs : LSeriesSummable (fun n => (d n : ℂ)) s) :
    ‖LSeries (fun n => (d n : ℂ)) s‖ ≤ (LSeries (fun n => (d n : ℂ)) (s.re : ℂ)).re := by
  have hσ : LSeriesSummable (fun n => (d n : ℂ)) (s.re : ℂ) :=
    (LSeriesSummable_iff_of_re_eq_re (by simp)).mp hs
  have hterm : ∀ n, ‖LSeries.term (fun n => (d n : ℂ)) s n‖ =
      (LSeries.term (fun n => (d n : ℂ)) (s.re : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcp : ((n : ℂ)) ^ ((s.re : ℝ) : ℂ) = (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hnpos.le]; simp
    rw [LSeries.norm_term_eq, if_neg hn, LSeries.term_of_ne_zero hn, hcp, ← Complex.ofReal_div,
      Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd n)]
  calc ‖LSeries (fun n => (d n : ℂ)) s‖ ≤ ∑' n, ‖LSeries.term (fun n => (d n : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ = ∑' n, (LSeries.term (fun n => (d n : ℂ)) (s.re : ℂ) n).re := tsum_congr hterm
    _ = (LSeries (fun n => (d n : ℂ)) (s.re : ℂ)).re := (Complex.re_tsum hσ).symm

/-- A nonnegative Dirichlet series with zero Abel residue at `x₀` on the real axis is Abel-negligible
at every point of the line `Re s = x₀`. -/
theorem tendsto_sub_mul_LSeries_of_residue_zero {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) {x₀ : ℝ}
    (habs : LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ x₀)
    (hres : Tendsto (fun σ : ℝ => (σ - x₀) * (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).re)
      (𝓝[>] x₀) (𝓝 0)) (t : ℝ) :
    Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) *
      LSeries (fun n => (d n : ℂ)) ((σ : ℂ) + (t : ℂ) * I)) (𝓝[>] x₀) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ hres
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : x₀ < σ := hσ
  have hs : LSeriesSummable (fun n => (d n : ℂ)) ((σ : ℂ) + (t : ℂ) * I) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt habs (by simpa using hσ'))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine mul_le_mul_of_nonneg_left ((norm_LSeries_le_re_of_nonneg hd hs).trans (le_of_eq ?_))
    (by linarith)
  simp

/-- A Dirichlet series converging absolutely left of `x₀` has zero Abel residue there. -/
theorem tendsto_residue_zero_of_abscissa_lt {d : ℕ → ℝ} {x₀ : ℝ}
    (habs : LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) < x₀) :
    Tendsto (fun σ : ℝ => (σ - x₀) * (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).re)
      (𝓝[>] x₀) (𝓝 0) := by
  have hc : ContinuousAt (fun σ : ℝ => (σ - x₀) * (LSeries (fun n => (d n : ℂ)) (σ : ℂ)).re)
      x₀ := by
    refine (continuousAt_id.sub continuousAt_const).mul (Complex.continuous_re.continuousAt.comp ?_)
    exact (LSeries_hasDerivAt (by simpa using habs)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have h := hc.tendsto
  simp only [sub_self, zero_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The Abel-residue threshold.** If `ξ` has no off-critical zero at ordinate `γ` and an arithmetic
member of `HeightCoupledSystem 2 1 1 γ` has a deficit series converging absolutely on `Re s > ½` with
zero Abel residue at `½`, `(σ − ½) Σ d(n) n^{−σ} → 0`, and keeps the central order, then it has the
coefficients of `ζ_γ` and is a nonzero real multiple of it. -/
theorem latticeMember_eq_of_negligible_deficit {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) ≤ (1 / 2 : ℝ))
    (hres : Tendsto (fun σ : ℝ => (σ - 1 / 2) *
      (LSeries (fun n => (latticeDeficit γ b n : ℂ)) (σ : ℂ)).re) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0))
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat) :
    (∀ n, n ≠ 0 → b n = heightCoupledVonMangoldt γ n) ∧
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ with hΛγ
  set D : ℂ → ℂ := LSeries (fun n => (latticeDeficit γ b n : ℂ)) with hDdef
  have hE : DifferentiableOn ℂ (fun s => (b 1 : ℂ) - D s) {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    fun s hs => ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_of_le_of_lt hdef
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := latticeMember_primeMass_split (γ := γ) hb habs hL
  obtain ⟨c, -, hord, hanchor, hrel, -⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hmass hE hsplit
  have hc : c ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have hz := (hanchor (by linarith) hgt).1
    have := hoff c (xi_add_eq_zero_of_heightCoupledΛ_real_zero hz)
    linarith
  have hmax : max c (1 / 2 : ℝ) = 1 / 2 := max_eq_right hc
  -- the perturbation `b(1) − D` is Abel-negligible on the critical line
  have hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - (1 / 2 : ℝ) : ℝ) : ℂ) *
      ((b 1 : ℂ) - D ((σ : ℂ) + (t : ℂ) * I))) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro t
    have h1 : Tendsto (fun σ : ℝ => ((σ - 1 / 2 : ℝ) : ℂ) * (b 1 : ℂ)) (𝓝[>] (1 / 2 : ℝ))
        (𝓝 0) := by
      have h : Continuous fun σ : ℝ => ((σ - 1 / 2 : ℝ) : ℂ) * (b 1 : ℂ) := by fun_prop
      have h' := (h.tendsto (1 / 2 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))
      simpa using h'
    have h2 := tendsto_sub_mul_LSeries_of_residue_zero (latticeDeficit_nonneg γ b) hdef hres t
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3.congr fun σ => by simp only [hDdef]; ring
  have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  -- every order agrees: right of `½` by the principle, left by symmetry, on it by transfer
  have hordnat : ∀ w : ℂ, (analyticOrderAt Λ w).toNat = (analyticOrderAt Λγ w).toNat := by
    have hright : ∀ w : ℂ, 1 / 2 < w.re → analyticOrderAt Λ w = analyticOrderAt Λγ w :=
      fun w hw => hord w (by rw [hmax]; exact hw)
    intro w
    rcases lt_trichotomy w.re (1 / 2) with hlt | heq | hgt
    · rw [← hHC.orderAt_one_sub, ← hHC0.orderAt_one_sub, hright (1 - w) (by simp; linarith)]
    · have hwe : w = (((1 / 2 : ℝ)) : ℂ) + (w.im : ℂ) * I := by
        rw [hhalf]; exact Complex.ext (by simp [heq]) (by simp)
      have h := abs_jump_le_of_rel hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top
        hHC0.orderAt_ne_top (x₀ := 1 / 2) (fun z hz => hrel z (by rw [hmax]; exact hz)) hEt w.im
      rw [← hwe, hhalf] at h
      have hc' : ((analyticOrderAt Λγ (1 / 2)).toNat : ℝ) - (analyticOrderAt Λ (1 / 2)).toNat ≤ 0 :=
        by have : ((analyticOrderAt Λγ (1 / 2)).toNat : ℝ) ≤ (analyticOrderAt Λ (1 / 2)).toNat :=
             by exact_mod_cast hcent
           linarith
      have h0 := abs_nonpos_iff.mp (h.trans hc')
      exact_mod_cast (sub_eq_zero.mp h0).symm
    · rw [hright w hgt]
  have hordall : ∀ w : ℂ, analyticOrderAt Λ w = analyticOrderAt Λγ w := fun w => by
    rw [← ENat.coe_toNat (hHC.orderAt_ne_top w), ← ENat.coe_toNat (hHC0.orderAt_ne_top w),
      hordnat w]
  obtain ⟨K, hK0, -, hFK⟩ := eq_const_mul_of_orders_eq hHC hordall
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
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s :=
  latticeMember_eq_of_negligible_deficit hoff hHC hb habs hL hdef.le
    (tendsto_residue_zero_of_abscissa_lt hdef) hcent

/-- **Equal central order forces a positive deficit residue.** If `ξ` has no off-critical zero at
ordinate `γ`, an arithmetic member with the central order of `Λ_γ` (or more), whose deficit series
converges absolutely on `Re s > ½` and whose coefficients differ from those of `ζ_γ`, has a deficit
with nonzero Abel residue at `½`. -/
theorem not_tendsto_deficit_residue_of_ne {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) ≤ (1 / 2 : ℝ))
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat)
    (hne : ∃ n, n ≠ 0 ∧ b n ≠ heightCoupledVonMangoldt γ n) :
    ¬ Tendsto (fun σ : ℝ => (σ - 1 / 2) *
      (LSeries (fun n => (latticeDeficit γ b n : ℂ)) (σ : ℂ)).re) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  intro hres
  obtain ⟨n, hn, hbn⟩ := hne
  exact hbn ((latticeMember_eq_of_negligible_deficit hoff hHC hb habs hL hdef hres hcent).1 n hn)

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
