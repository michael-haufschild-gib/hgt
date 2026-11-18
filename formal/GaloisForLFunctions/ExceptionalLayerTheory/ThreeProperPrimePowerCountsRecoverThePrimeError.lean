import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Recovering the prime error from three counts of proper prime powers

The Costa–Pereira inequalities isolate the square and cube contributions
up to a fifth-root error. At three successive powers of the cutoff the
cube of one row cancels the square of the next. The last remaining
Chebyshev term has exponent eight twenty-sevenths.
-/

noncomputable section
open Filter Topology
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The logarithmic count of proper prime powers after its square and cube main terms. -/
def properPowerDiscrepancy (x : ℝ) : ℝ :=
  Chebyshev.psi x-Chebyshev.theta x-x^(1/2:ℝ)-x^(1/3:ℝ)

private abbrev E (x : ℝ) := Chebyshev.psi x-x
private abbrev L := Real.log 4+4

private theorem zero_le_L : (0:ℝ)≤L := by dsimp only [L]; positivity

private theorem two_rows {x : ℝ} (hx : 0≤x) :
    0≤properPowerDiscrepancy x-(E (x^(1/2:ℝ))+E (x^(1/3:ℝ))) ∧
    properPowerDiscrepancy x-(E (x^(1/2:ℝ))+E (x^(1/3:ℝ)))≤L*x^(1/5:ℝ) := by
  have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx
  have hhi := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  simp only [← one_div] at hlo hhi
  have h₇ := Chebyshev.psi_nonneg (x^(1/7:ℝ))
  have h₅ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx (1/5))
  dsimp only [properPowerDiscrepancy,E,L] at *
  constructor <;> linarith only [hlo,hhi,h₇,h₅]

private theorem rescaled_rows {x : ℝ} (hx : 1≤x) {r : ℝ} (hr : r≤2) :
    |properPowerDiscrepancy (x^r)-(E (x^(r/2))+E (x^(r/3)))|≤L*x^(2/5:ℝ) := by
  have hx0 := zero_le_one.trans hx
  have h := two_rows (Real.rpow_nonneg hx0 r)
  rw [← Real.rpow_mul hx0,← Real.rpow_mul hx0] at h
  simp only [mul_one_div] at h
  rw [abs_of_nonneg h.1]
  apply h.2.trans
  apply mul_le_mul_of_nonneg_left _ zero_le_L
  rw [← Real.rpow_mul hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hr])

/-- Three proper-power counts recover the actual Chebyshev error below
square-root precision, uniformly at every real cutoff. -/
theorem three_properPowerDiscrepancies_recover_psi {x : ℝ} (hx : 1≤x) :
    |properPowerDiscrepancy (x^(2:ℝ))-properPowerDiscrepancy (x^(4/3:ℝ))+
      properPowerDiscrepancy (x^(8/9:ℝ))-(Chebyshev.psi x-x)|≤(4*(Real.log 4+4)+1)*x^(2/5:ℝ) := by
  have h₂ := rescaled_rows hx (r := 2) (by norm_num)
  have h₄ := rescaled_rows hx (r := 4/3) (by norm_num)
  have h₈ := rescaled_rows hx (r := 8/9) (by norm_num)
  norm_num only [show (2:ℝ)/2=1 by norm_num,Real.rpow_one,show (4/3:ℝ)/2=2/3 by norm_num,
    show (4/3:ℝ)/3=4/9 by norm_num,show (8/9:ℝ)/2=4/9 by norm_num,
    show (8/9:ℝ)/3=8/27 by norm_num] at h₂ h₄ h₈
  have hpow := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (8/27:ℝ)≤2/5)
  have hnon := Real.rpow_nonneg (zero_le_one.trans hx) (8/27:ℝ)
  have hu := (Chebyshev.psi_le_const_mul_self hnon).trans (mul_le_mul_of_nonneg_left hpow zero_le_L)
  have hl := Chebyshev.psi_nonneg (x^(8/27:ℝ))
  obtain ⟨l₂,u₂⟩ := abs_le.mp h₂
  obtain ⟨l₄,u₄⟩ := abs_le.mp h₄
  obtain ⟨l₈,u₈⟩ := abs_le.mp h₈
  have hL := mul_nonneg zero_le_L (Real.rpow_nonneg (zero_le_one.trans hx) (2/5:ℝ))
  dsimp only [E] at *
  rw [abs_le]
  constructor <;> linarith only [l₂,u₂,l₄,u₄,l₈,u₈,hpow,hnon,hu,hl,hL]

/-- At every exponent at least two fifths, the power bound on the
Chebyshev error is equivalent to the half-exponent proper-power bound. -/
theorem psi_power_bound_iff_properPowerDiscrepancy {a : ℝ} (ha : 2/5≤a) :
    (∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 1≤x → |Chebyshev.psi x-x|≤C*x^a) ↔
    ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, 1≤x → |properPowerDiscrepancy x|≤K*x^(a/2) := by
  have ha0 : 0≤a := by linarith only [ha]
  constructor
  · rintro ⟨C,hC,he⟩
    refine ⟨2*C+L,by linarith only [hC,zero_le_L],?_⟩
    intro x hx
    have hx0 := zero_le_one.trans hx
    have h (r : ℝ) (hr : 0≤r) (hr' : r≤1/2) : |E (x^r)|≤C*x^(a/2) := by
      apply (he _ (Real.one_le_rpow hx hr)).trans
      rw [← Real.rpow_mul hx0]
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hx
      linarith only [mul_le_mul_of_nonneg_right hr' ha0]
    have h₂ := abs_le.mp (h (1/2) (by norm_num) le_rfl)
    have h₃ := abs_le.mp (h (1/3) (by norm_num) (by norm_num))
    have ht := two_rows hx0
    have h₅ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx
      (by linarith only [ha] : (1/5:ℝ)≤a/2)) zero_le_L
    have hpos := mul_nonneg zero_le_L (Real.rpow_nonneg hx0 (a/2))
    rw [abs_le]
    constructor <;> linarith only [h₂.1,h₂.2,h₃.1,h₃.2,ht.1,ht.2,h₅,hpos]
  · rintro ⟨K,hK,hu⟩
    refine ⟨3*K+4*L+1,by linarith only [hK,zero_le_L],?_⟩
    intro x hx
    have hx0 := zero_le_one.trans hx
    have h (r : ℝ) (hr : 0≤r) (hr' : r≤2) : |properPowerDiscrepancy (x^r)|≤K*x^a := by
      apply (hu _ (Real.one_le_rpow hx hr)).trans
      rw [← Real.rpow_mul hx0]
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.rpow_le_rpow_of_exponent_le hx
      linarith only [mul_le_mul_of_nonneg_right hr' ha0]
    have h₂ := abs_le.mp (h 2 (by norm_num) le_rfl)
    have h₄ := abs_le.mp (h (4/3) (by norm_num) (by norm_num))
    have h₈ := abs_le.mp (h (8/9) (by norm_num) (by norm_num))
    have hR := (three_properPowerDiscrepancies_recover_psi hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ha)
        (by linarith only [zero_le_L] : (0:ℝ)≤4*L+1))
    obtain ⟨hlo,hhi⟩ := abs_le.mp hR
    rw [abs_le]
    constructor <;> linarith only [h₂.1,h₂.2,h₄.1,h₄.2,h₈.1,h₈.2,hlo,hhi]

/-- At the square cutoff the centered proper powers differ from the prime
error by a power strictly below the zero abscissa. -/
theorem properPowerDiscrepancy_square_tracks_prime_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |properPowerDiscrepancy (y^(2:ℝ))-(Chebyshev.psi y-y)| ≤ K*y^(5*zeroReSup/6) := by
  have hhalf := half_le_zeroReSup
  obtain ⟨C,hC,hψ⟩ := exists_abs_chebyshevPsi_sub_le_rpow
    (show zeroReSup < 5*zeroReSup/4 by linarith only [hhalf])
  refine ⟨C+L,add_nonneg hC zero_le_L,?_⟩
  intro y hy
  have hc := hψ (y^(2/3:ℝ)) (Real.one_le_rpow hy (by norm_num))
  rw [← Real.rpow_mul (zero_le_one.trans hy),show (2/3:ℝ)*(5*zeroReSup/4)=5*zeroReSup/6 by ring] at hc
  have ht := rescaled_rows hy (r := 2) le_rfl
  rw [show (2:ℝ)/2=1 by norm_num,Real.rpow_one] at ht
  have hscale := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy
    (show (2:ℝ)/5≤5*zeroReSup/6 by linarith only [hhalf])) zero_le_L
  rw [abs_le] at ht hc ⊢
  dsimp only [E] at ht
  constructor <;> linarith only [ht.1,ht.2,hc.1,hc.2,hscale]

/-- Each sign of the corrected prime-power count reaches every power below
half the zero abscissa at arbitrarily large cutoffs, whether or not that
abscissa is attained by a zero. -/
theorem properPowerDiscrepancy_both_signs_below_abscissa {b : ℝ} (hb : b < zeroReSup/2) :
    (∃ᶠ x : ℝ in atTop, x^b < properPowerDiscrepancy x) ∧
      ∃ᶠ x : ℝ in atTop, properPowerDiscrepancy x < -x^b := by
  let v := max (2*b) (5*zeroReSup/6)
  have hv : v < zeroReSup := max_lt (by linarith only [hb]) (by linarith only [half_le_zeroReSup])
  obtain ⟨a,hva,ha⟩ := exists_between hv
  obtain ⟨K,hK,htrack⟩ := properPowerDiscrepancy_square_tracks_prime_error
  have hbig := (tendsto_rpow_atTop (sub_pos.mpr hva)).eventually_gt_atTop (K+1)
  have htest : ∀ᶠ y : ℝ in atTop, y^(2*b)+|properPowerDiscrepancy (y^(2:ℝ))-E y| < y^a := by
    filter_upwards [eventually_ge_atTop (1:ℝ),hbig] with y hy hlarge
    have hp := zero_lt_one.trans_le hy
    have h₁ := Real.rpow_le_rpow_of_exponent_le hy (le_max_left (2*b) (5*zeroReSup/6))
    have h₂ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy
      (le_max_right (2*b) (5*zeroReSup/6))) hK
    have h₃ := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hp v)
    rw [← Real.rpow_add hp,show v+(a-v)=a by ring] at h₃
    change y^(2*b)≤y^v at h₁
    change K*y^(5*zeroReSup/6)≤K*y^v at h₂
    linarith only [h₁,h₂,h₃,htrack y hy]
  obtain ⟨hplus,hminus⟩ := chebyshevPsi_sub_exponent_law.1 a ha
  constructor
  · apply frequently_atTop.mpr
    intro X
    obtain ⟨y,⟨hy,ht⟩,hX⟩ := ((hplus.and_eventually htest).and_eventually
      (eventually_ge_atTop (max 1 X))).exists
    have h1 : 1≤y := (le_max_left _ _).trans hX
    have hh := neg_abs_le (properPowerDiscrepancy (y^(2:ℝ))-E y)
    refine ⟨y^(2:ℝ),(le_max_right _ _).trans (hX.trans ?_),?_⟩
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1:ℝ)≤2)
    · rw [← Real.rpow_mul (zero_le_one.trans h1)]
      change y^a < E y at hy
      linarith only [hy,ht,hh]
  · apply frequently_atTop.mpr
    intro X
    obtain ⟨y,⟨hy,ht⟩,hX⟩ := ((hminus.and_eventually htest).and_eventually
      (eventually_ge_atTop (max 1 X))).exists
    have h1 : 1≤y := (le_max_left _ _).trans hX
    have hh := le_abs_self (properPowerDiscrepancy (y^(2:ℝ))-E y)
    refine ⟨y^(2:ℝ),(le_max_right _ _).trans (hX.trans ?_),?_⟩
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1:ℝ)≤2)
    · rw [← Real.rpow_mul (zero_le_one.trans h1)]
      change E y < -y^a at hy
      linarith only [hy,ht,hh]

/-- An eventual power bound for either sign bounds the real parts of all
nontrivial zeros. The constant and the sign may be chosen separately at
each exponent. -/
theorem zeroReSup_le_twice_of_properPowerDiscrepancy_one_sided {b K : ℝ}
    (h : (∀ᶠ x : ℝ in atTop, properPowerDiscrepancy x ≤ K*x^b) ∨
      (∀ᶠ x : ℝ in atTop, -K*x^b ≤ properPowerDiscrepancy x)) : zeroReSup ≤ 2*b := by
  by_contra! hbad
  obtain ⟨c,hbc,hc⟩ := exists_between (show b < zeroReSup/2 by linarith only [hbad])
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hbc)).eventually_gt_atTop K
  have hpow : ∀ᶠ x : ℝ in atTop, K*x^b < x^c := by
    filter_upwards [eventually_gt_atTop (0:ℝ),hg] with x hx he
    have hv := mul_lt_mul_of_pos_right he (Real.rpow_pos_of_pos hx b)
    rwa [← Real.rpow_add hx,sub_add_cancel] at hv
  obtain ⟨hplus,hminus⟩ := properPowerDiscrepancy_both_signs_below_abscissa hc
  rcases h with h | h
  · obtain ⟨x,⟨hp,hu⟩,hx⟩ := ((hplus.and_eventually h).and_eventually hpow).exists
    exact (not_lt_of_ge hu) (hx.trans hp)
  · obtain ⟨x,⟨hm,hl⟩,hx⟩ := ((hminus.and_eventually h).and_eventually hpow).exists
    linarith only [hm,hl,hx]

/-- Above half the zero abscissa the same exponent bounds the full
corrected count uniformly on the real half-line. -/
theorem properPowerDiscrepancy_bound_above_abscissa {b : ℝ} (hb : zeroReSup/2 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b := by
  have h := (psi_power_bound_iff_properPowerDiscrepancy (a := 2*b)
    (by linarith only [hb,half_le_zeroReSup])).mp
    (exists_abs_chebyshevPsi_sub_le_rpow (by linarith only [hb] : zeroReSup < 2*b))
  simpa only [show 2*b/2=b by ring] using h

/-- Unconditional exponents for the proper-power count from the sub-seven-eighths strip. -/
theorem properPowerDiscrepancy_from_zero_free_strip {b : ℝ} (hb : 20999/48000 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b := by
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  exact properPowerDiscrepancy_bound_above_abscissa (by linarith only [hΘ,hb])

/-- The corrected proper-power count alone characterizes RH at the quarter exponent. -/
theorem riemannHypothesis_iff_properPowerDiscrepancy_quarter :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/4 < b → b < 1/2 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b := by
  constructor
  · intro hRH b hb _
    have hΘ := zeroReSup_le_of_forall_re_le fun q => (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    exact properPowerDiscrepancy_bound_above_abscissa (by linarith only [hΘ,hb])
  · intro h
    apply riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro z hz hz' hzero
    obtain ⟨q,hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hzero (by linarith only [hz]) hz'
    let e := (z.re-1/2)/2
    have he : 0 < e := by dsimp only [e]; linarith only [hz]
    have he' : e < 1/2 := by dsimp only [e]; linarith only [hz']
    obtain ⟨C,hC,hbound⟩ := (psi_power_bound_iff_properPowerDiscrepancy (a := 1/2+e)
      (by linarith only [he])).mpr (h _ (by linarith only [he]) (by linarith only [he']))
    have ht := re_le_half_add_of_chebyshevError_ge_rpow hC he he' (x₁ := 2) (by norm_num)
      (fun t ht => (abs_le.mp (hbound t (by linarith only [ht]))).1) q
    rw [hq] at ht
    dsimp only [e] at ht
    linarith only [ht,hz]

#print axioms zeroReSup_le_twice_of_properPowerDiscrepancy_one_sided
#print axioms properPowerDiscrepancy_bound_above_abscissa
#print axioms properPowerDiscrepancy_both_signs_below_abscissa
#print axioms properPowerDiscrepancy_square_tracks_prime_error
#print axioms properPowerDiscrepancy_from_zero_free_strip
#print axioms riemannHypothesis_iff_properPowerDiscrepancy_quarter
#print axioms three_properPowerDiscrepancies_recover_psi
#print axioms psi_power_bound_iff_properPowerDiscrepancy
end GaloisForLFunctions.ExceptionalLayerTheory
