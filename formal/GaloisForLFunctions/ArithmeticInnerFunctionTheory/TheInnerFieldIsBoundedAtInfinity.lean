import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheLogMeanIsTheInnerMassAtInfinity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet

/-!
# The inner field is bounded at infinity

Selberg's mollified second moment bounds the off-line first moment:
`Σ_{0≤γ≤V, β>½} m_ρ(β−½) ≤ (67/1000) V` for large `V` (`eventually_offLineMoment_le_selberg_upper`).
Zeros come in conjugate pairs with equal multiplicity, so every window `|γ − t| ≤ T` with
`|t| ≤ T` carries depth `O(T)`, uniformly in `t` (`exists_sum_depth_le_linear`). This improves
the unmollified `T log log T` of `exists_sum_depth_le`.

In inner-field form (`exists_innerField_le`, `eventually_innerField_le`):

* `I(½ + x + it)` is bounded on `x ≥ 1`, `|t| ≤ x`;
* for each `t`, `I(½ + x + it) ≤ 27/5` for all large `x`;
* the Abel log-mean `∫ log |ζ(½+iτ)| P_{½+x+it}(τ) dτ` is at most `11/2` for all large `x`.

The inner mass at infinity is the depth density, so the mollifier reaches it in size; that it
tends to `0` (depth density `o(T)`) is the open question B57.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- `ζ` is analytic away from its pole. -/
private theorem analyticAt_zeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton) _ (by simpa using hs)

/-- Conjugate points carry the same order of `ζ`. -/
theorem analyticOrderAt_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta (conj s) = analyticOrderAt riemannZeta s := by
  have hs' : conj s ≠ 1 := fun h => hs (by simpa using congrArg conj h)
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_zeta hs'),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_zeta hs)]
  simp [iteratedDeriv_riemannZeta_conj]

/-- Conjugate zeros have the same multiplicity. -/
theorem zeroMult_conj {s : ℂ} (hs : s ≠ 1) : zeroMult (conj s) = zeroMult s := by
  rw [zeroMult, zeroMult, analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_riemannZeta_conj hs]

/-- A zero right of the line is a zero of `ξ` in the strip, with the same multiplicity. -/
private theorem right_zero_facts {z : ℂ} (hz : riemannZeta z = 0) (hre : 1 / 2 < z.re) :
    xi z = 0 ∧ z.re < 1 ∧ zeroMult z = ((analyticOrderAt xi z).toNat : ℝ) := by
  have hre1 : z.re < 1 := by
    by_contra! h
    exact riemannZeta_ne_zero_of_one_le_re h hz
  have hxi : xi z = 0 := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hz, fun n h => by
    have := congrArg Complex.re h
    simp only [neg_re, mul_re, re_ofNat, add_re, natCast_re, one_re, im_ofNat, add_im, natCast_im,
      one_im, zero_mul, sub_zero] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith⟩
  refine ⟨hxi, hre1, ?_⟩
  rw [zeroMult, analyticOrderNatAt,
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨by linarith, hre1⟩]

/-- A right zero at height in `[0, H]` lies in the census box. -/
private theorem mem_boxFinsetLe_of {z : ℂ} {H : ℝ} (hz : riemannZeta z = 0) (hre : 1 / 2 < z.re)
    (h0 : 0 ≤ z.im) (hH : z.im ≤ H) : z ∈ boxFinsetLe H := by
  obtain ⟨hxi, hre1, -⟩ := right_zero_facts hz hre
  rw [mem_boxFinsetLe]
  exact ⟨hre, hre1, h0, hH, hxi⟩

/-- **Both half-planes against the census.** A finite set of right zeros of height at most `H`
carries depth at most twice the off-line first moment up to `H`. -/
theorem sum_depth_le_two_offLineMoment {H : ℝ} (Z : Finset ZetaRightZero)
    (hZ : ∀ ρ ∈ Z, |(ρ : ℂ).im| ≤ H) :
    ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ 2 * offLineMoment H := by
  classical
  have hbox : ∀ S : Finset ℂ, S ⊆ boxFinsetLe H →
      ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) ≤ offLineMoment H :=
    fun S hS => Finset.sum_le_sum_of_subset_of_nonneg hS fun z hz _ => offLineMoment_term_nonneg hz
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ : ZetaRightZero => 0 ≤ (ρ : ℂ).im)]
  have hup : ∑ ρ ∈ Z.filter (fun ρ : ZetaRightZero => 0 ≤ (ρ : ℂ).im), zeroMult ρ * depth ρ ≤
      offLineMoment H := by
    calc ∑ ρ ∈ Z.filter (fun ρ : ZetaRightZero => 0 ≤ (ρ : ℂ).im), zeroMult ρ * depth ρ
        = ∑ z ∈ (Z.filter (fun ρ : ZetaRightZero => 0 ≤ (ρ : ℂ).im)).image
              (fun ρ : ZetaRightZero => (ρ : ℂ)),
            ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) := by
          rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [(right_zero_facts ρ.2.1 ρ.2.2).2.2, depth]
      _ ≤ offLineMoment H := by
          refine hbox _ fun z hz => ?_
          obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hρZ, hρ0⟩ := Finset.mem_filter.mp hρ
          exact mem_boxFinsetLe_of ρ.2.1 ρ.2.2 hρ0 ((le_abs_self _).trans (hZ ρ hρZ))
  have hdown : ∑ ρ ∈ Z.filter (fun ρ : ZetaRightZero => ¬ 0 ≤ (ρ : ℂ).im), zeroMult ρ * depth ρ ≤
      offLineMoment H := by
    have hzc : ∀ ρ : ZetaRightZero, riemannZeta (conj (ρ : ℂ)) = 0 := fun ρ => by
      rw [riemannZeta_conj, ρ.2.1, map_zero]
    have hrc : ∀ ρ : ZetaRightZero, 1 / 2 < (conj (ρ : ℂ)).re := fun ρ => by
      rw [conj_re]
      exact ρ.2.2
    calc ∑ ρ ∈ Z.filter (fun ρ : ZetaRightZero => ¬ 0 ≤ (ρ : ℂ).im), zeroMult ρ * depth ρ
        = ∑ z ∈ (Z.filter (fun ρ : ZetaRightZero => ¬ 0 ≤ (ρ : ℂ).im)).image
              (fun ρ : ZetaRightZero => conj (ρ : ℂ)),
            ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) := by
          rw [Finset.sum_image (fun a _ b _ h => Subtype.ext ((starRingEnd ℂ).injective h))]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          have hne : (ρ : ℂ) ≠ 1 := fun h => by
            have := ρ.2.1
            rw [h] at this
            exact riemannZeta_one_ne_zero this
          rw [← (right_zero_facts (hzc ρ) (hrc ρ)).2.2, zeroMult_conj hne, depth, conj_re]
      _ ≤ offLineMoment H := by
          refine hbox _ fun z hz => ?_
          obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hρZ, hρ0⟩ := Finset.mem_filter.mp hρ
          have hH := hZ ρ hρZ
          rw [abs_of_neg (not_le.mp hρ0)] at hH
          refine mem_boxFinsetLe_of (hzc ρ) (hrc ρ) ?_ ?_
          · rw [conj_im]
            linarith only [not_le.mp hρ0]
          · rw [conj_im]
            exact hH
  linarith only [hup, hdown]

/-- **Selberg's depth density, uniformly over windows.** There is `C` with
`Σ_{|γ−t|≤T} m_ρ(β−½) ≤ C T` for all `T ≥ 1` and `|t| ≤ T`. -/
theorem exists_sum_depth_le_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T t : ℝ}, 1 ≤ T → |t| ≤ T → ∀ Z : Finset ZetaRightZero,
      (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) → ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ C * T := by
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  refine ⟨268 / 1000 + 134 / 1000 * |V₀|, by positivity, fun {T t} hT ht Z hZ => ?_⟩
  have hH : ∀ ρ ∈ Z, |(ρ : ℂ).im| ≤ 2 * T := fun ρ hρ => by
    have h1 := hZ ρ hρ
    have h2 := abs_sub_abs_le_abs_sub (ρ : ℂ).im t
    linarith only [h1, h2, ht]
  have hM : offLineMoment (2 * T) ≤ 67 / 1000 * (2 * T + |V₀|) := by
    refine (offLineMoment_mono (le_max_left (2 * T) V₀)).trans ?_
    refine (hV₀ _ (le_max_right _ _)).trans ?_
    have : max (2 * T) V₀ ≤ 2 * T + |V₀| :=
      max_le (by linarith only [abs_nonneg V₀]) (by linarith only [le_abs_self V₀, hT])
    linarith only [this]
  have h := sum_depth_le_two_offLineMoment Z hH
  have hV : 0 ≤ |V₀| := abs_nonneg V₀
  nlinarith only [h, hM, hV, hT]

/-- **The inner field is bounded at infinity**, uniformly on `|t| ≤ x`. -/
theorem exists_innerField_le :
    ∃ B : ℝ, ∀ {x t : ℝ}, 1 ≤ x → |t| ≤ x → innerField (centre x t) ≤ B := by
  obtain ⟨C, hC, hD⟩ := exists_sum_depth_le_linear
  exact ⟨40 * C, fun {x t} hx ht => innerField_le_of_depthDensity hx hC fun T hT Z hZ =>
    hD (hx.trans hT) (ht.trans hT) Z hZ⟩

/-- **The inner mass at infinity is at most `27/5`.** For each height `t`, eventually in the
width, `I(½ + x + it) ≤ 27/5`: twice Selberg's `67/1000` per window of the inner-field kernel. -/
theorem eventually_innerField_le (t : ℝ) :
    ∀ᶠ x : ℝ in atTop, innerField (centre x t) ≤ 27 / 5 := by
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  filter_upwards [eventually_ge_atTop (max (max 1 V₀) (134 * |t|))] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxV : V₀ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxt : 134 * |t| ≤ x := (le_max_right _ _).trans hx
  have h := innerField_le_of_depthDensity (t := t) (ε := 135 / 1000) hx1 (by norm_num)
    fun T hT Z hZ => by
      have hH : ∀ ρ ∈ Z, |(ρ : ℂ).im| ≤ T + |t| := fun ρ hρ => by
        have h1 := hZ ρ hρ
        have h2 := abs_sub_abs_le_abs_sub (ρ : ℂ).im t
        linarith only [h1, h2]
      have hM := hV₀ (T + |t|) (by linarith only [hxV, hT, abs_nonneg t])
      have h3 := sum_depth_le_two_offLineMoment Z hH
      linarith only [h3, hM, hxt, hT]
  linarith only [h]

/-- **The Abel log-mean of `ζ` on the line is at most `11/2`** for every height, eventually in the
width. With `I ≥ 0` it lies between `−o(1)` and `27/5 + o(1)`. -/
theorem eventually_poisson_log_le (t : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ *
      halfPlanePoissonKernel (centre x t) τ ≤ 11 / 2 := by
  have hc := (tendsto_log_correction t).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
  have hc' := (tendsto_log_correction t).eventually (lt_mem_nhds (show (-1 / 10 : ℝ) < 0 by norm_num))
  filter_upwards [eventually_innerField_le t, hc, hc'] with x hI h1 h2
  rw [innerField] at hI
  linarith only [hI, h2]

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
