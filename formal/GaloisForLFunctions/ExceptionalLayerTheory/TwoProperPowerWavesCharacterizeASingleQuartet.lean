import GaloisForLFunctions.ExceptionalLayerTheory.ThreeProperPrimePowerCountsRecoverThePrimeError
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope

/-!
# The two proper-power waves of a single quartet

At the square cutoff the corrected proper powers read the prime errors at
y and y^(2/3). Subtracting the relation at y^(2/3) leaves a last error at
y^(4/9), already below square-root precision for every linear-growth model.
-/

noncomputable section
open Complex
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory
open ExclusionOfTheCriticalState

private abbrev E (y : ℝ) := Chebyshev.psi y-y
private abbrev B (y : ℝ) := Real.sqrt y*(1+Real.log y)^2
private abbrev T (y : ℝ) := y^(2/3:ℝ)
private abbrev L : ℝ := Real.log 4+4

private theorem B_lower {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ B y := by
  apply le_mul_of_one_le_right (Real.sqrt_nonneg _)
  exact one_le_pow₀ (le_add_of_nonneg_right (Real.log_nonneg hy))

private theorem B_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : B x ≤ B y := by
  have hx0 := zero_lt_one.trans_le hx
  have hl := Real.log_le_log hx0 hxy
  exact mul_le_mul (Real.sqrt_le_sqrt hxy) ((sq_le_sq₀ (by linarith only [Real.log_nonneg hx])
    (by linarith only [Real.log_nonneg (hx.trans hxy)])).mpr (add_le_add_left hl 1))
    (sq_nonneg _) (Real.sqrt_nonneg _)

private theorem T_in_interval {y : ℝ} (hy : 1 ≤ y) : 1 ≤ T y ∧ T y ≤ y :=
  ⟨Real.one_le_rpow hy (by norm_num),by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num : (2/3:ℝ) ≤ 1)⟩

private theorem square_error {y : ℝ} (hy : 1 ≤ y) :
    |properPowerDiscrepancy (y^(2:ℝ))-(E y+E (T y))| ≤ L*B y := by
  have hy0 := zero_le_one.trans hy
  have hx := Real.rpow_nonneg hy0 (2:ℝ)
  have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx
  have hhi := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (y^(2:ℝ))
  have htail := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hy0 (2/5:ℝ))
  have hpos := Chebyshev.psi_nonneg (y^(2/7:ℝ))
  have hn : 0 ≤ L := by dsimp only [L]; positivity
  have hscale : y^(2/5:ℝ) ≤ B y := calc
    y^(2/5:ℝ) ≤ y^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    _ = Real.sqrt y := (Real.sqrt_eq_rpow _).symm
    _ ≤ B y := B_lower hy
  have hbound := mul_le_mul_of_nonneg_left hscale hn
  simp only [← one_div,← Real.rpow_mul hy0,mul_one_div,div_self (by norm_num : (2:ℝ) ≠ 0),
    Real.rpow_one] at hlo hhi
  dsimp only [properPowerDiscrepancy,E,T]
  rw [← Real.rpow_mul hy0,← Real.rpow_mul hy0]
  simp only [mul_one_div,div_self (by norm_num : (2:ℝ) ≠ 0),Real.rpow_one]
  rw [abs_le]
  dsimp only [L] at hbound ⊢
  constructor <;> linarith only [hlo,hhi,htail,hpos,hbound,
    mul_nonneg hn ((Real.sqrt_nonneg _).trans (B_lower hy))]

/-- For every model of at most linear growth, square-root accuracy for
the prime error is equivalent to the same accuracy for the two predicted
waves in the corrected proper-power count at the square cutoff. -/
theorem prime_model_iff_two_properPower_waves {W : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ y : ℝ, 1 ≤ y → |E y-W y| ≤ A*y) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |E y-W y| ≤ C*B y) ↔
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |properPowerDiscrepancy (y^(2:ℝ))-(W y+W (T y))| ≤ K*B y := by
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨L+2*C,by positivity,fun y hy => ?_⟩
    obtain ⟨h₁,h₂⟩ := T_in_interval hy
    have ht := (h _ h₁).trans (mul_le_mul_of_nonneg_left (B_mono h₁ h₂) hC)
    obtain ⟨el,eu⟩ := abs_le.mp (square_error hy)
    obtain ⟨yl,yu⟩ := abs_le.mp (h y hy)
    obtain ⟨tl,tu⟩ := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith only [el,eu,yl,yu,tl,tu]
  · rintro ⟨K,hK,h⟩
    refine ⟨2*(K+L)+A,by positivity,fun y hy => ?_⟩
    have row (t : ℝ) (ht : 1 ≤ t) :
        |(E t-W t)+(E (T t)-W (T t))| ≤ (K+L)*B t := by
      obtain ⟨el,eu⟩ := abs_le.mp (square_error ht)
      obtain ⟨wl,wu⟩ := abs_le.mp (h t ht)
      rw [abs_le]; constructor <;> linarith only [el,eu,wl,wu]
    obtain ⟨h₁,h₂⟩ := T_in_interval hy
    have ht := (row _ h₁).trans (mul_le_mul_of_nonneg_left (B_mono h₁ h₂) (add_nonneg hK hL))
    have hsmall : T (T y) ≤ B y := by
      change (y^(2/3:ℝ))^(2/3:ℝ) ≤ _
      rw [← Real.rpow_mul (zero_le_one.trans hy)]
      apply le_trans _ (B_lower hy)
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    have hlast := (hlin _ (T_in_interval h₁).1).trans (mul_le_mul_of_nonneg_left hsmall hA)
    obtain ⟨rl,ru⟩ := abs_le.mp (row y hy)
    obtain ⟨tl,tu⟩ := abs_le.mp ht
    obtain ⟨ll,lu⟩ := abs_le.mp hlast
    rw [abs_le]
    constructor <;> linarith only [rl,ru,tl,tu,ll,lu]

/-- The prescribed prime wave with its actual divisor multiplicity. -/
def quartetPrimeWaveTerm (ρ : ℂ) (y : ℝ) : ℝ :=
  -(2*(quartetCopyMult ρ:ℝ)*(((y:ℂ)^ρ)/ρ).re)

private theorem wave_linear {ρ : ℂ} (h1 : ρ.re < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, 1 ≤ y → |E y-quartetPrimeWaveTerm ρ y| ≤ A*y := by
  let D := 2*(quartetCopyMult ρ:ℝ)/‖ρ‖
  have hd : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨5+D,by positivity,fun y hy => ?_⟩
  have hp := zero_lt_one.trans_le hy
  have h := (Complex.abs_re_le_norm (((y:ℂ)^ρ)/ρ)).trans_eq (norm_div _ _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp] at h
  have hpow := Real.rpow_le_rpow_of_exponent_le hy h1.le
  rw [Real.rpow_one] at hpow
  have hw : |quartetPrimeWaveTerm ρ y| ≤ D*y := by
    rw [quartetPrimeWaveTerm,abs_neg,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*(quartetCopyMult ρ:ℝ))]
    apply (mul_le_mul_of_nonneg_left (h.trans (div_le_div_of_nonneg_right hpow (norm_nonneg _))) (by positivity)).trans_eq
    dsimp only [D]; ring
  apply (abs_sub _ _).trans
  exact (add_le_add (RiemannGaussian.abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hy) hw).trans_eq (by ring)

/-- The pair of prescribed waves on ordinary prime powers characterizes
the single-quartet stratum. The error at the square cutoff is of order
sqrt(y) times the square of the logarithm. -/
theorem hasSingleOffLineQuartet_iff_two_properPower_waves {ρ : ℂ} (hh : 1/2 < ρ.re)
    (hmem : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    HasSingleOffLineQuartet ρ ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |properPowerDiscrepancy (y^(2:ℝ))-
        (quartetPrimeWaveTerm ρ y+quartetPrimeWaveTerm ρ (y^(2/3:ℝ)))| ≤
        K*(Real.sqrt y*(1+Real.log y)^2) := by
  obtain ⟨A,hA,ha⟩ := wave_linear (ρ := ρ) hmem.2.2
  rw [← prime_model_iff_two_properPower_waves hA ha]
  rw [hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hh hmem]
  constructor
  · rintro ⟨K,h⟩
    let C := 16*A+|K|
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C,hC,fun y hy => ?_⟩
    have hB : 1 ≤ B y := (by simpa using Real.sqrt_le_sqrt hy : 1 ≤ Real.sqrt y).trans (B_lower hy)
    by_cases h16 : 16 ≤ y
    · have he : |E y-quartetPrimeWaveTerm ρ y| ≤ K*(Real.sqrt y*(Real.log y)^2) := by
        simpa only [E,quartetPrimeWaveTerm,sub_neg_eq_add,mul_assoc] using h y h16
      have hb : (Real.log y)^2 ≤ (1+Real.log y)^2 :=
        (sq_le_sq₀ (Real.log_nonneg hy) (by linarith only [Real.log_nonneg hy])).mpr (by linarith)
      have hs := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      have hcoeff : K ≤ C := by dsimp only [C]; linarith only [le_abs_self K,hA]
      apply he.trans
      apply (mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).trans
      exact mul_le_mul_of_nonneg_left hs hC
    · apply (ha y hy).trans
      apply (mul_le_mul_of_nonneg_left (not_le.mp h16).le hA).trans
      dsimp only [C]
      have hl := mul_le_mul_of_nonneg_left hB hC
      dsimp only [C] at hl
      linarith only [hl,abs_nonneg K]
  · rintro ⟨K,hK,h⟩
    refine ⟨4*K,fun y hy => ?_⟩
    have h1 : 1 ≤ y := by linarith only [hy]
    have hlog : 1 ≤ Real.log y := (Real.le_log_iff_exp_le (zero_lt_one.trans_le h1)).mpr
      (Real.exp_one_lt_three.le.trans (by linarith only [hy]))
    have hs := (sq_le_sq₀ (by linarith only [hlog] : 0 ≤ 1+Real.log y)
      (by linarith only [hlog] : 0 ≤ 2*Real.log y)).mpr (by linarith only [hlog] : 1+Real.log y ≤ 2*Real.log y)
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hK (Real.sqrt_nonneg _))
    have he := h y h1
    dsimp only [B,E,quartetPrimeWaveTerm] at he
    rw [sub_neg_eq_add] at he
    linarith only [he,ht]

#print axioms prime_model_iff_two_properPower_waves
#print axioms hasSingleOffLineQuartet_iff_two_properPower_waves
end GaloisForLFunctions.ExceptionalLayerTheory
