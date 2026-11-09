import GaloisForLFunctions.ArithmeticPositiveDuality.QuotientMassCannotSkipLogarithmicBands

/-!
# Both quotient signs recur in bounded logarithmic bands

The positive convolution recurrence transfers absolute boundary mass to both
signs. Its geometric forcing tends to zero in high bands, while an annihilator
zero keeps the boundary mass uniformly positive.
-/

noncomputable section
open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The canonical coefficient with its critical exponential weight. -/
def dampedQuotientCoeff (P : MvPolynomial (Fin 2) ℝ≥0) (β : ℝ) (d : Fin 2 →₀ ℕ) : ℝ :=
  annihilatorQuotientCoeff P d * Real.exp (-monomialLog d * β)

/-- Positive critical coefficient mass in a logarithmic band. -/
def quotientPositiveBandMass (P : MvPolynomial (Fin 2) ℝ≥0) (β A B : ℝ) : ℝ :=
  ∑ d ∈ logarithmicBand A B, max (dampedQuotientCoeff P β d) 0

/-- Negative critical coefficient mass in a logarithmic band. -/
def quotientNegativeBandMass (P : MvPolynomial (Fin 2) ℝ≥0) (β A B : ℝ) : ℝ :=
  ∑ d ∈ logarithmicBand A B, max (-dampedQuotientCoeff P β d) 0

theorem quotientBandMass_eq_signs (P : MvPolynomial (Fin 2) ℝ≥0) (β A B : ℝ) :
    quotientBandMass P β A B = quotientPositiveBandMass P β A B +
      quotientNegativeBandMass P β A B := by
  rw [quotientBandMass, quotientPositiveBandMass, quotientNegativeBandMass, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  have he : |annihilatorQuotientCoeff P d| * Real.exp (-monomialLog d * β) =
      |dampedQuotientCoeff P β d| := by
    rw [dampedQuotientCoeff, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [he]
  by_cases h : 0 ≤ dampedQuotientCoeff P β d
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · have hn := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), zero_add]

private theorem weighted_quotient_recurrence (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (β : ℝ) (d : Fin 2 →₀ ℕ) :
    dampedQuotientCoeff P β d +
      (∑ e ∈ P.support.erase 0, if e ≤ d then
        (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) *
          dampedQuotientCoeff P β (d - e) else 0) = Real.exp (-monomialLog d * β) := by
  classical
  have h := congrArg (fun x : ℝ => x * Real.exp (-monomialLog d * β))
    (quotient_recurrence P hP d)
  rw [MvPolynomial.support_map_of_injective P NNReal.coe_injective] at h
  simp only [add_mul, sum_mul, one_mul] at h
  convert h using 1
  congr 1
  apply sum_congr rfl
  intro e _
  split_ifs with he
  · have hfreq := frequency_add e (d - e)
    rw [add_tsub_cancel_of_le he] at hfreq
    unfold dampedQuotientCoeff
    rw [show -monomialLog d * β =
      -monomialLog e * β + -monomialLog (d - e) * β by rw [hfreq]; ring,
      Real.exp_add]
    ring
  · ring

private theorem weighted_recurrence_sign_bounds (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (β : ℝ) (d : Fin 2 →₀ ℕ) :
    max (dampedQuotientCoeff P β d) 0 ≤ Real.exp (-monomialLog d * β) +
      (∑ e ∈ P.support.erase 0, if e ≤ d then
        (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) *
          max (-dampedQuotientCoeff P β (d - e)) 0 else 0) ∧
    max (-dampedQuotientCoeff P β d) 0 ≤
      (∑ e ∈ P.support.erase 0, if e ≤ d then
        (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) *
          max (dampedQuotientCoeff P β (d - e)) 0 else 0) := by
  classical
  let c := fun e => ((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)
  have hc (e) : 0 ≤ c e := mul_nonneg (P.coeff e).coe_nonneg (Real.exp_pos _).le
  have hrec := weighted_quotient_recurrence P hP β d
  have hneg : -(∑ e ∈ P.support.erase 0, if e ≤ d then
      c e * dampedQuotientCoeff P β (d - e) else 0) ≤
      ∑ e ∈ P.support.erase 0, if e ≤ d then
        c e * max (-dampedQuotientCoeff P β (d - e)) 0 else 0 := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro e _
    split_ifs
    · simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (le_max_left (-dampedQuotientCoeff P β (d - e)) 0) (hc e)
    · simp only [neg_zero, le_refl]
  have hpos : (∑ e ∈ P.support.erase 0, if e ≤ d then
      c e * dampedQuotientCoeff P β (d - e) else 0) ≤
      ∑ e ∈ P.support.erase 0, if e ≤ d then
        c e * max (dampedQuotientCoeff P β (d - e)) 0 else 0 := by
    apply sum_le_sum
    intro e _
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hc e)
    · exact le_rfl
  have hsum (f : (Fin 2 →₀ ℕ) → ℝ) (hf : ∀ x, 0 ≤ f x) :
      0 ≤ ∑ e ∈ P.support.erase 0, if e ≤ d then c e * f (d - e) else 0 :=
    sum_nonneg (fun e _ => by
      split_ifs
      · exact mul_nonneg (hc e) (hf _)
      · exact le_rfl)
  constructor
  · apply max_le
    · change _ ≤ Real.exp (-monomialLog d * β) +
        ∑ e ∈ P.support.erase 0, if e ≤ d then
          c e * max (-dampedQuotientCoeff P β (d - e)) 0 else 0
      linarith only [hrec, hneg]
    · exact add_nonneg (Real.exp_pos _).le
        (hsum (fun x => max (-dampedQuotientCoeff P β x) 0) (fun _ => le_max_right _ _))
  · apply max_le
    · change _ ≤ ∑ e ∈ P.support.erase 0, if e ≤ d then
        c e * max (dampedQuotientCoeff P β (d - e)) 0 else 0
      have hg := (Real.exp_pos (-monomialLog d * β)).le
      linarith only [hrec, hpos, hg]
    · exact hsum (fun x => max (dampedQuotientCoeff P β x) 0) (fun _ => le_max_right _ _)

private theorem shifted_band_sum_le (f : (Fin 2 →₀ ℕ) → ℝ) (hf : ∀ d, 0 ≤ f d)
    {B T : ℝ} {e : Fin 2 →₀ ℕ} (heB : monomialLog e ≤ B) :
    (∑ d ∈ logarithmicBand (T - B) T, if e ≤ d then f (d - e) else 0) ≤
      ∑ d ∈ logarithmicBand (T - 2 * B) T, f d := by
  classical
  rw [← sum_filter]
  let S := (logarithmicBand (T - B) T).filter (fun d => e ≤ d)
  have hinj : Set.InjOn (fun d : Fin 2 →₀ ℕ => d - e) (S : Set (Fin 2 →₀ ℕ)) := by
    intro d hd g hg heq
    have hd' := (mem_filter.mp hd).2
    have hg' := (mem_filter.mp hg).2
    change d - e = g - e at heq
    rw [← add_tsub_cancel_of_le hd', ← add_tsub_cancel_of_le hg', heq]
  change (∑ d ∈ S, f (d - e)) ≤ _
  rw [← sum_image hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hd
    obtain ⟨hgBand, heg⟩ := mem_filter.mp hg
    obtain ⟨hlo, hhi⟩ := mem_logarithmicBand.mp hgBand
    have hfreq := frequency_add e (g - e)
    rw [add_tsub_cancel_of_le heg] at hfreq
    have he0 := frequency_nonneg e
    apply mem_logarithmicBand.mpr
    constructor <;> linarith only [hlo, hhi, heB, hfreq, he0]
  · intro d _ _
    exact hf d

private theorem positive_convolution_band_le (P : MvPolynomial (Fin 2) ℝ≥0)
    (β : ℝ) (f : (Fin 2 →₀ ℕ) → ℝ) (hf : ∀ d, 0 ≤ f d) {B : ℝ}
    (hB : ∀ e ∈ P.support, monomialLog e ≤ B) (T : ℝ) :
    (∑ d ∈ logarithmicBand (T - B) T, ∑ e ∈ P.support.erase 0,
      if e ≤ d then (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) * f (d - e) else 0) ≤
      dirichletTailMass P β * ∑ d ∈ logarithmicBand (T - 2 * B) T, f d := by
  classical
  rw [sum_comm]
  calc
    _ = ∑ e ∈ P.support.erase 0, (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) *
        (∑ d ∈ logarithmicBand (T - B) T, if e ≤ d then f (d - e) else 0) := by
      apply sum_congr rfl
      intro e _
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      split_ifs <;> simp only [mul_zero]
    _ ≤ ∑ e ∈ P.support.erase 0, (((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * β)) *
        (∑ d ∈ logarithmicBand (T - 2 * B) T, f d) := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (shifted_band_sum_le f hf (hB e (mem_of_mem_erase he)))
        (mul_nonneg (P.coeff e).coe_nonneg (Real.exp_pos _).le)
    _ = _ := by rw [← sum_mul]; rfl

/-- Positive convolution moves mass of either sign to the opposite sign within
one kernel span. Only the positive part pays the geometric forcing. -/
theorem quotient_sign_band_transfer (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (β : ℝ) {B : ℝ}
    (hB : ∀ e ∈ P.support, monomialLog e ≤ B) (T : ℝ) :
    quotientPositiveBandMass P β (T - B) T ≤
      (∑ d ∈ logarithmicBand (T - B) T, Real.exp (-monomialLog d * β)) +
        dirichletTailMass P β * quotientNegativeBandMass P β (T - 2 * B) T ∧
    quotientNegativeBandMass P β (T - B) T ≤
      dirichletTailMass P β * quotientPositiveBandMass P β (T - 2 * B) T := by
  have hp := sum_le_sum (fun d (_ : d ∈ logarithmicBand (T - B) T) =>
    (weighted_recurrence_sign_bounds P hP β d).1)
  have hn := sum_le_sum (fun d (_ : d ∈ logarithmicBand (T - B) T) =>
    (weighted_recurrence_sign_bounds P hP β d).2)
  rw [sum_add_distrib] at hp
  exact ⟨hp.trans (add_le_add le_rfl
    (positive_convolution_band_le P β (fun d => max (-dampedQuotientCoeff P β d) 0)
      (fun _ => le_max_right _ _) hB T)),
    hn.trans (positive_convolution_band_le P β (fun d => max (dampedQuotientCoeff P β d) 0)
      (fun _ => le_max_right _ _) hB T)⟩

private theorem absolute_band_le_each_sign (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (β : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ e ∈ P.support, monomialLog e ≤ B) (T : ℝ) :
    quotientBandMass P β (T - B) T ≤
      (∑ d ∈ logarithmicBand (T - B) T, Real.exp (-monomialLog d * β)) +
        (dirichletTailMass P β + 1) * quotientNegativeBandMass P β (T - 2 * B) T ∧
    quotientBandMass P β (T - B) T ≤
      (dirichletTailMass P β + 1) * quotientPositiveBandMass P β (T - 2 * B) T := by
  have hsub : logarithmicBand (T - B) T ⊆ logarithmicBand (T - 2 * B) T := by
    intro d hd
    obtain ⟨hlo, hhi⟩ := mem_logarithmicBand.mp hd
    exact mem_logarithmicBand.mpr ⟨by linarith only [hlo, hB0], hhi⟩
  have hp : quotientPositiveBandMass P β (T - B) T ≤
      quotientPositiveBandMass P β (T - 2 * B) T :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_right _ _)
  have hn : quotientNegativeBandMass P β (T - B) T ≤
      quotientNegativeBandMass P β (T - 2 * B) T :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_right _ _)
  obtain ⟨hpn, hnp⟩ := quotient_sign_band_transfer P hP β hB T
  rw [quotientBandMass_eq_signs]
  constructor <;> nlinarith only [hp, hn, hpn, hnp]

private theorem geometric_band_tendsto_zero {β : ℝ} (hβ : 0 < β) {B : ℝ} (hB : 0 ≤ B) :
    Tendsto (fun T : ℝ => ∑ d ∈ logarithmicBand (T - B) T,
      Real.exp (-monomialLog d * β)) atTop (𝓝 0) := by
  have hs : Summable (fun d : Fin 2 →₀ ℕ => Real.exp (-monomialLog d * β)) := by
    simpa only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero] using
      frequency_geometric_norm (s := (β : ℂ)) hβ
  have hlim := hs.hasSum.comp tendsto_frequencyCutoff
  have hshift : Tendsto (fun T : ℝ => T - B) atTop atTop := by
    apply tendsto_atTop.2
    intro u
    filter_upwards [eventually_ge_atTop (u + B)] with T hT
    linarith only [hT]
  have h := hlim.sub (hlim.comp hshift)
  have heq (T : ℝ) : (∑ d ∈ frequencyCutoff T, Real.exp (-monomialLog d * β)) -
      (∑ d ∈ frequencyCutoff (T - B), Real.exp (-monomialLog d * β)) =
      ∑ d ∈ logarithmicBand (T - B) T, Real.exp (-monomialLog d * β) := by
    rw [← sum_sdiff (frequencyCutoff_mono (sub_le_self T hB)), add_sub_cancel_right]
    rfl
  simpa only [Function.comp_def, heq, sub_self] using h

/-- Twice any frequency bound for the annihilator suffices for uniformly
positive mass of both coefficient signs at the critical exponent. -/
theorem quotient_sign_band_mass_eventually_lower
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : dirichletEval ρ P = 0) {B : ℝ} (hB : 0 < B)
    (hfreq : ∀ e ∈ P.support, monomialLog e ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c ≤ quotientPositiveBandMass P ρ.re (T - 2 * B) T ∧
      c ≤ quotientNegativeBandMass P ρ.re (T - 2 * B) T := by
  classical
  obtain ⟨c₀, hc₀, hmass⟩ := quotient_band_mass_eventually_lower P hP hρ hz hfreq
  have hsmall : ∀ᶠ T : ℝ in atTop,
      (∑ d ∈ logarithmicBand (T - B) T, Real.exp (-monomialLog d * ρ.re)) < c₀ / 2 :=
    (geometric_band_tendsto_zero hρ hB.le).eventually (gt_mem_nhds (half_pos hc₀))
  let H := dirichletTailMass P ρ.re + 1
  have hH : 0 < H := add_pos_of_nonneg_of_pos (dirichletTailMass_nonneg P ρ.re) zero_lt_one
  let c := c₀ / (2 * H)
  have hc : 0 < c := div_pos hc₀ (mul_pos (by norm_num) hH)
  refine ⟨c, hc, ?_⟩
  have hev : ∀ᶠ T : ℝ in atTop,
      c ≤ quotientPositiveBandMass P ρ.re (T - 2 * B) T ∧
      c ≤ quotientNegativeBandMass P ρ.re (T - 2 * B) T := by
    filter_upwards [hmass, hsmall] with T hmassT hsmallT
    obtain ⟨hn, hp⟩ := absolute_band_le_each_sign P hP ρ.re hB.le hfreq T
    constructor
    · apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hH)).mpr
      change c₀ ≤ quotientPositiveBandMass P ρ.re (T - 2 * B) T * (2 * H)
      dsimp only [H]
      nlinarith only [hmassT, hp, hc₀]
    · apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hH)).mpr
      change c₀ ≤ quotientNegativeBandMass P ρ.re (T - 2 * B) T * (2 * H)
      dsimp only [H]
      nlinarith only [hmassT, hn, hsmallT]
  exact hev

/-- Both signs have a uniform positive critical mass in every sufficiently
high logarithmic band of one fixed width. -/
theorem quotient_signs_have_bounded_logarithmic_gaps
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : dirichletEval ρ P = 0) :
    ∃ W c T₀ : ℝ, 0 < W ∧ 0 < c ∧ ∀ T : ℝ, T₀ ≤ T →
      c ≤ quotientPositiveBandMass P ρ.re T (T + W) ∧
      c ≤ quotientNegativeBandMass P ρ.re T (T + W) := by
  classical
  let B := 1 + ∑ e ∈ P.support, monomialLog e
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (sum_nonneg (fun e _ => frequency_nonneg e))
  have hfreq (e : Fin 2 →₀ ℕ) (he : e ∈ P.support) : monomialLog e ≤ B := by
    have h := single_le_sum (fun d _ => frequency_nonneg d) he
    dsimp only [B]
    linarith only [h]
  obtain ⟨c, hc, hev⟩ := quotient_sign_band_mass_eventually_lower P hP hρ hz hB hfreq
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨2 * B, c, T₀, mul_pos (by norm_num) hB, hc, fun T hT => ?_⟩
  have h := hT₀ (T + 2 * B) (by linarith only [hT, hB])
  simpa only [add_sub_cancel_right] using h

/-- Every finite actual xi divisor admits arbitrarily accurate positive
annihilation, and every prescribed zero forces bounded-band quotient oscillation. -/
theorem exists_xi_annihilator_with_quotient_band_oscillation
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, dirichletEval (ρ : ℂ) P = 0 ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (fun s => dirichletEval s P) (ρ : ℂ)) ∧
      (∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε) ∧
      ∀ ρ ∈ F, ∃ W c T₀ : ℝ, 0 < W ∧ 0 < c ∧ ∀ T : ℝ, T₀ ≤ T →
        c ≤ quotientPositiveBandMass P (ρ : ℂ).re T (T + W) ∧
        c ≤ quotientNegativeBandMass P (ρ : ℂ).re T (T + W) := by
  obtain ⟨P, hP, hz, hacc⟩ := exists_xi_zero_annihilator_with_multiplicities F m hε
  refine ⟨P, hP, hz, hacc, fun ρ hρ => ?_⟩
  exact quotient_signs_have_bounded_logarithmic_gaps P hP
    (RHTower.xi_zero_re_mem_open_unit ρ.property).1 (hz ρ hρ).1

#print axioms quotient_sign_band_mass_eventually_lower
#print axioms quotient_signs_have_bounded_logarithmic_gaps
#print axioms exists_xi_annihilator_with_quotient_band_oscillation

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
