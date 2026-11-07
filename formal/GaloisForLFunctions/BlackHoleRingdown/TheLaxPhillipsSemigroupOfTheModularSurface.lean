import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffDilation
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The Lax–Phillips semigroup of the modular surface

A resonance of `SL₂(ℤ)\ℍ` is a parameter `u` with `Λ(1 + 2u) = 0`, `-½ < Re u < 0`, `Im u > 0`,
i.e. `u = (ρ - 1)/2` for a zero `ρ` of `ζ`. At a resonance the completed Eisenstein series has the
single cusp term `Λ(2u) y^{½-u}`, and its truncation `t_u = Λ¹E*_u` at height `1` is a genuine
`L²(𝒟)` state. The corpus cusp model (`resonant_finite_combination_isometry`) is the outgoing
translation representation: `Σ cᵢ t_{uᵢ} ↦ Σ cᵢ Λ(2uᵢ) y^{-uᵢ-½} 1_{(0,1]}(y)` is isometric into
`L²(ℝ)`.

**The semigroup.** In this representation the Lax–Phillips semigroup is the compressed normalized
dilation `(Z(t)F)(y) = 1_{(0,1]}(y) e^{-t/2} F(e^{-t} y)` (`lpCompress`): the wave group moves the
data up the cusp and the projection cuts it back at height `1`. Each resonant state is an
eigenvector, `Z(t) t_u = e^{ut} t_u` (`lpCompress_cuspCutoff`). On every finite combination

  `‖Σ cᵢ e^{uᵢ t} t_{uᵢ}‖²_{L²(𝒟)} = ∫_0^{e^{-t}} |Σ cᵢ Λ(2uᵢ) y^{-uᵢ-½}|² dy`
  (`integral_norm_sq_resonantFlow`),

so `Z(t)` is a contraction (`resonantFlow_contraction`), hence well defined on the span of the
resonant states, it is a semigroup in `t`, and it exhausts the interaction space,
`‖Z(t)f‖ → 0` (`tendsto_resonantFlow_zero`).

**Damping.** A mode decays as `‖Z(t) t_u‖² = e^{2 Re u · t} ‖t_u‖²` with `2 Re u = Re ρ - 1`. The
Riemann hypothesis holds iff every resonant mode decays at the universal rate `e^{-t/4}`
(`riemannHypothesis_iff_resonant_decay`): the modular form of the graph law "the Krein metric is
Hilbert iff universal damping" (`ArithmeticScatteringHolography.kreinHerm_nonneg_iff`).
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-! ## The compressed dilation -/

/-- The Lax–Phillips semigroup in the cusp model: `(Z(t)F)(y) = 1_{(0,1]}(y) e^{-t/2} F(e^{-t} y)`. -/
def lpCompress (t : ℝ) (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun y => (Real.sqrt (Real.exp (-t)) : ℂ) * F (Real.exp (-t) * y)) y

theorem ofReal_exp_neg_cpow_neg (t : ℝ) (u : ℂ) :
    ((Real.exp (-t) : ℝ) : ℂ) ^ (-u) = Complex.exp (u * t) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos _).ne'),
    ← ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1
  push_cast
  ring

/-- **Resonant states are eigenvectors:** `Z(t) t_u = e^{ut} t_u` for `t ≥ 0`. -/
theorem lpCompress_cuspCutoff (u : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    lpCompress t (cuspCutoff u 1) = fun y => Complex.exp (u * t) * cuspCutoff u 1 y := by
  funext y
  have hr : 0 < Real.exp (-t) := Real.exp_pos _
  have hr1 : 1 ≤ 1 / Real.exp (-t) := by
    rw [le_div_iff₀ hr, one_mul]
    exact Real.exp_le_one_iff.2 (by linarith)
  unfold lpCompress
  by_cases hy : y ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hy, cuspCutoff_dilation u 1 hr y, ofReal_exp_neg_cpow_neg]
    congr 1
    have hy' : y ∈ Ioc (0 : ℝ) (1 / Real.exp (-t)) := ⟨hy.1, hy.2.trans hr1⟩
    simp only [cuspCutoff, if_pos hy, if_pos hy']
  · rw [indicator_of_notMem hy]
    simp only [cuspCutoff, if_neg hy, mul_zero]

/-- The compression is linear on finite combinations. -/
theorem lpCompress_sum {ι : Type*} (S : Finset ι) (u c : ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    lpCompress t (fun y => ∑ i ∈ S, c i * cuspCutoff (u i) 1 y) =
      fun y => ∑ i ∈ S, (c i * Complex.exp (u i * t)) * cuspCutoff (u i) 1 y := by
  funext y
  have h : ∀ i, lpCompress t (cuspCutoff (u i) 1) y =
      Complex.exp (u i * t) * cuspCutoff (u i) 1 y := fun i => by
    rw [lpCompress_cuspCutoff _ ht]
  unfold lpCompress at h ⊢
  by_cases hy : y ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := h i
    rw [indicator_of_mem hy] at hi
    rw [mul_left_comm, hi]
    ring
  · rw [indicator_of_notMem hy]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    simp only [cuspCutoff, if_neg hy, mul_zero]

/-- `‖Z(t)F‖² = ∫_0^{e^{-t}} |F|²`: the compression keeps the part of the data below `e^{-t}`. -/
theorem integral_norm_sq_lpCompress (t : ℝ) (F : ℝ → ℂ) :
    ∫ y, ‖lpCompress t F y‖ ^ 2 = ∫ y in Ioc 0 (Real.exp (-t)), ‖F y‖ ^ 2 := by
  set r := Real.exp (-t) with hrdef
  have hr : 0 < r := Real.exp_pos _
  have hpt : ∀ y, ‖lpCompress t F y‖ ^ 2 =
      r * (Ioc 0 r).indicator (fun x => ‖F x‖ ^ 2) (r * y) := by
    intro y
    have hm : r * y ∈ Ioc 0 r ↔ y ∈ Ioc (0 : ℝ) 1 := by
      simp only [mem_Ioc, mul_pos_iff_of_pos_left hr]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by nlinarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by nlinarith⟩
    unfold lpCompress
    by_cases hy : y ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hy, indicator_of_mem (hm.2 hy), norm_mul, mul_pow, norm_real,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr.le]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hm.1 h))]
      simp
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x =>
    (Ioc 0 r).indicator (fun x => ‖F x‖ ^ 2) x) r, integral_indicator measurableSet_Ioc,
    smul_eq_mul, abs_inv, abs_of_pos hr, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-! ## The semigroup on resonant states -/

section Resonant

variable {ι : Type*} (S : Finset ι) (u c : ι → ℂ)

/-- The cusp model of a finite combination of resonant states. -/
def resonantModel (y : ℝ) : ℂ := ∑ i ∈ S, c i * cuspCutoff (u i) 1 y

theorem memLp_resonantModel (hur : ∀ i ∈ S, (u i).re < 0) :
    MemLp (resonantModel S u c) 2 volume := by
  unfold resonantModel
  exact memLp_finsetSum S (f := fun i y => c i * cuspCutoff (u i) 1 y) fun i hi =>
    (cuspCutoff_memLp (hur i hi) zero_le_one).const_mul _

theorem integrable_norm_sq_resonantModel (hur : ∀ i ∈ S, (u i).re < 0) :
    Integrable fun y => ‖resonantModel S u c y‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (memLp_resonantModel S u c hur).1).1
    (memLp_resonantModel S u c hur)

variable {S u c}

/-- **The Lax–Phillips semigroup on resonant states.** For `t ≥ 0`,
`‖Σ cᵢ e^{uᵢ t} t_{uᵢ}‖²_{L²(𝒟)} = ∫_0^{e^{-t}} |Σ cᵢ Λ(2uᵢ) y^{-uᵢ-½}|² dy`. -/
theorem integral_norm_sq_resonantFlow (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z in fd, ‖∑ i ∈ S, (c i * Complex.exp (u i * t)) * truncatedLineModel (u i) 1 z‖ ^ 2) =
      ∫ y in Ioc 0 (Real.exp (-t)), ‖resonantModel S u c y‖ ^ 2 := by
  rw [resonant_finite_combination_isometry S u (fun _ => 1) _ hu hur hAu (fun _ _ => le_rfl),
    ← integral_norm_sq_lpCompress t (resonantModel S u c),
    show resonantModel S u c = fun y => ∑ i ∈ S, c i * cuspCutoff (u i) 1 y from rfl,
    lpCompress_sum S u c ht]

/-- At `t = 0` the flow is the identity: `‖Σ cᵢ t_{uᵢ}‖² = ∫_0^1 |Σ cᵢ Λ(2uᵢ) y^{-uᵢ-½}|²`. -/
theorem integral_norm_sq_resonant (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0) :
    (∫ z in fd, ‖∑ i ∈ S, c i * truncatedLineModel (u i) 1 z‖ ^ 2) =
      ∫ y in Ioc 0 1, ‖resonantModel S u c y‖ ^ 2 := by
  have h := integral_norm_sq_resonantFlow (c := c) hu hur hAu le_rfl
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero,
    Real.exp_zero] at h
  exact h

/-- **Contraction.** `‖Z(t) f‖ ≤ ‖f‖` on the span of resonant states. -/
theorem resonantFlow_contraction (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z in fd, ‖∑ i ∈ S, (c i * Complex.exp (u i * t)) * truncatedLineModel (u i) 1 z‖ ^ 2) ≤
      ∫ z in fd, ‖∑ i ∈ S, c i * truncatedLineModel (u i) 1 z‖ ^ 2 := by
  rw [integral_norm_sq_resonantFlow hu hur hAu ht, integral_norm_sq_resonant hu hur hAu]
  have hint := (integrable_norm_sq_resonantModel S u c hur).integrableOn (s := Ioc 0 1)
  refine setIntegral_mono_set hint (Eventually.of_forall fun y => by positivity) ?_
  refine Eventually.of_forall fun y hy => ⟨hy.1, hy.2.trans (Real.exp_le_one_iff.2 (by linarith))⟩

/-- The flow is well defined on the span: a vanishing combination stays zero. -/
theorem resonantFlow_eq_zero (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0) {t : ℝ} (ht : 0 ≤ t)
    (h0 : (∫ z in fd, ‖∑ i ∈ S, c i * truncatedLineModel (u i) 1 z‖ ^ 2) = 0) :
    (∫ z in fd, ‖∑ i ∈ S, (c i * Complex.exp (u i * t)) * truncatedLineModel (u i) 1 z‖ ^ 2) =
      0 :=
  le_antisymm (h0 ▸ resonantFlow_contraction hu hur hAu ht)
    (integral_nonneg fun _ => by positivity)

/-- **Exhaustion.** `‖Z(t) f‖ → 0` as `t → ∞`. -/
theorem tendsto_resonantFlow_zero (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0) :
    Tendsto (fun t : ℝ => ∫ z in fd,
      ‖∑ i ∈ S, (c i * Complex.exp (u i * t)) * truncatedLineModel (u i) 1 z‖ ^ 2)
      atTop (𝓝 0) := by
  have hint := integrable_norm_sq_resonantModel S u c hur
  have hlim : Tendsto (fun t : ℝ => ∫ y, (Ioc 0 (Real.exp (-t))).indicator
      (fun y => ‖resonantModel S u c y‖ ^ 2) y) atTop (𝓝 (∫ _y : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖resonantModel S u c y‖ ^ 2) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun t =>
        (hint.indicator measurableSet_Ioc).aestronglyMeasurable
    · refine Eventually.of_forall fun t => Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => by positivity) _)]
      exact indicator_le_self' (fun _ _ => by positivity) y
    · refine Eventually.of_forall fun y => ?_
      rcases le_or_gt y 0 with hy | hy
      · exact tendsto_const_nhds.congr fun t => by
          rw [indicator_of_notMem fun h => absurd h.1 (not_lt.2 hy)]
      · have hev : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < y := by
          have := (Real.tendsto_exp_neg_atTop_nhds_zero).eventually (gt_mem_nhds hy)
          exact this
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with t ht
        rw [indicator_of_notMem fun h => absurd h.2 (not_le.2 ht)]
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [integral_norm_sq_resonantFlow hu hur hAu ht, integral_indicator measurableSet_Ioc]

end Resonant

/-! ## Damping of the modes -/

/-- `‖Z(t) t_u‖² = e^{2 Re u · t} ‖t_u‖²`. -/
theorem integral_norm_sq_mode (u : ℂ) (t : ℝ) :
    (∫ z in fd, ‖Complex.exp (u * t) * truncatedLineModel u 1 z‖ ^ 2) =
      Real.exp (2 * u.re * t) * ∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2 := by
  simp_rw [norm_mul, mul_pow, Complex.norm_exp]
  rw [integral_const_mul, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

/-- A resonant state has positive norm: `‖t_u‖² = |Λ(2u)|²/(-2 Re u)`. -/
theorem integral_norm_sq_resonantState_pos {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) : 0 < ∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2 := by
  have h := integral_norm_sq_resonant (S := {()}) (u := fun _ => u) (c := fun _ => 1)
    (fun _ _ => hu) (fun _ _ => hur) (fun _ _ => hAu)
  simp only [Finset.sum_singleton, one_mul] at h
  rw [h]
  have hB : msB u ≠ 0 := by
    rw [msB, show 2 * u = (1 + 2 * u) - 1 by ring]
    refine reflectedCompletedLambda_sub_one_ne_zero (by simp; linarith) (by simp; linarith [hu.2])
  -- the integrand is `|Λ(2u)|² y^{-2 Re u - 1}` on `(0, 1]`
  have hpos : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ‖resonantModel {()} (fun _ => u) (fun _ => 1) y‖ ^ 2 := by
    intro y hy
    simp only [resonantModel, Finset.sum_singleton, one_mul, cuspCutoff, if_pos hy]
    have : (y : ℂ) ^ (-u - 1 / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      exact fun h => (ofReal_ne_zero.2 hy.1.ne') h.1
    exact pow_pos (norm_pos_iff.2 (mul_ne_zero hB this)) 2
  have hint := (integrable_norm_sq_resonantModel {()} (fun _ => u) (fun _ => 1)
    (fun _ _ => hur)).integrableOn (s := Ioc 0 1)
  refine (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
    hint).2 ?_
  have hsub : Ioc (0 : ℝ) 1 ⊆ Function.support
      (fun y => ‖resonantModel {()} (fun _ => u) (fun _ => 1) y‖ ^ 2) ∩ Ioc 0 1 :=
    fun y hy => ⟨(hpos y hy).ne', hy⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp

/-- **Universal damping is the Riemann hypothesis.** Every resonant mode of the Lax–Phillips
semigroup decays at the universal rate, `‖Z(t) t_u‖² = e^{-t/2} ‖t_u‖²`, iff RH holds. -/
theorem riemannHypothesis_iff_resonant_decay :
    RiemannHypothesis ↔ ∀ u : ℂ, u ∈ eisensteinLineDomain → u.re < 0 → msA u = 0 → ∀ t : ℝ,
      (∫ z in fd, ‖Complex.exp (u * t) * truncatedLineModel u 1 z‖ ^ 2) =
        Real.exp (-(t / 2)) * ∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2 := by
  constructor
  · intro hRH u hu hur hAu t
    -- `ρ = 1 + 2u` is a nontrivial zero, so `Re u = -1/4`
    have him : (1 + 2 * u).im ≠ 0 := by simp; linarith [hu.2]
    have hζ : riemannZeta (1 + 2 * u) = 0 := by
      have h := hAu
      rw [msA, reflectedCompletedLambda] at h
      exact (mul_eq_zero.1 h).resolve_left (by
        intro h0
        obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h0
        exact him (by rw [hn]; simp))
    have htriv : ¬∃ n : ℕ, 1 + 2 * u = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      exact him (by rw [hn]; simp)
    have hne1 : 1 + 2 * u ≠ 1 := fun h => him (by rw [h]; simp)
    have hre := hRH _ hζ htriv hne1
    have hu4 : u.re = -1 / 4 := by simp at hre; linarith
    rw [integral_norm_sq_mode, hu4]
    congr 2
    ring
  · intro h
    by_contra hRH
    obtain ⟨ρ, hρ, hρ1, hρ2⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    -- a zero with the same real part in the upper half plane
    obtain ⟨ρ', hρ', hre', him'⟩ : ∃ ρ' : ℂ, riemannZeta ρ' = 0 ∧ ρ'.re = ρ.re ∧ 0 < ρ'.im := by
      rcases lt_trichotomy ρ.im 0 with hi | hi | hi
      · refine ⟨(starRingEnd ℂ) ρ, by rw [riemannZeta_conj, hρ, map_zero], by simp, ?_⟩
        simp
        linarith
      · exfalso
        have hreal : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
        exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) hρ2 (hreal ▸ hρ)
      · exact ⟨ρ, hρ, rfl, hi⟩
    set u := (ρ' - 1) / 2 with hudef
    have hu : u ∈ eisensteinLineDomain := ⟨by simp [hudef]; linarith, by simp [hudef]; linarith⟩
    have hur : u.re < 0 := by simp [hudef]; linarith
    have hAu : msA u = 0 := by
      rw [msA, show 1 + 2 * u = ρ' by rw [hudef]; ring, reflectedCompletedLambda, hρ', mul_zero]
    have hd := h u hu hur hAu 1
    rw [integral_norm_sq_mode] at hd
    have hpos := integral_norm_sq_resonantState_pos hu hur hAu
    have hexp : Real.exp (2 * u.re * 1) = Real.exp (-(1 / 2)) := mul_right_cancel₀ hpos.ne' hd
    have := Real.exp_injective hexp
    have hre : u.re = (ρ'.re - 1) / 2 := by simp [hudef]
    linarith

end

end GaloisForLFunctions.BlackHoleRingdown
