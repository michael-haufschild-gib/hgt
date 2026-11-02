import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveFiniteCorrection
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Bounded primitives for reciprocal spline numerators

The reciprocal of `sinh (δ + ix)^8`, for `δ > 0`, has an absolutely convergent
negative-frequency binomial expansion. Integrating each frequency gives a
uniformly bounded primitive for every positive modulation. Reflection gives
a bounded primitive for positive modulations of `(1 - exp(-2δ) exp(2ix))⁻⁸`.
These primitives control translated interval averages by endpoint differences.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def splineShift (j : Fin 9) : ℝ := 8-2*j.val

def splineCoefficient (δ : ℝ) (j : Fin 9) : ℝ :=
  (-1 : ℝ)^j.val*(Nat.choose 8 j.val : ℝ)/256*Real.exp (splineShift j*δ)

def shiftedSplineNumerator (δ t x : ℝ) : ℂ :=
  ∑ j : Fin 9, (splineCoefficient δ j : ℂ)*phase (t+splineShift j) x

def shiftedSplineSlope (δ t x : ℝ) : ℂ :=
  ∑ j : Fin 9, Complex.I*((splineCoefficient δ j*(t+splineShift j) : ℝ) : ℂ)*
    phase (t+splineShift j) x

lemma hasDerivAt_phase (u x : ℝ) :
    HasDerivAt (phase u) (phase u x*((u : ℂ)*Complex.I)) x := by
  have hbase := ((hasDerivAt_id (x : ℂ)).const_mul (u : ℂ)).mul_const Complex.I
  have h := hbase.cexp.comp_ofReal
  unfold phase
  simpa only [id_eq, mul_one, Complex.ofReal_mul] using h

lemma hasDerivAt_shiftedSplineNumerator (δ t x : ℝ) :
    HasDerivAt (shiftedSplineNumerator δ t) (shiftedSplineSlope δ t x) x := by
  have he : shiftedSplineSlope δ t x = ∑ j : Fin 9,
      (splineCoefficient δ j : ℂ)*(phase (t+splineShift j) x*
        (((t+splineShift j : ℝ) : ℂ)*Complex.I)) := by
    apply sum_congr rfl
    intro j _
    push_cast
    ring
  rw [he]
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_phase (t+splineShift j) x).const_mul (splineCoefficient δ j : ℂ)

def splineSlopeBound (δ t : ℝ) : ℝ :=
  ∑ j : Fin 9, |splineCoefficient δ j*(t+splineShift j)|

lemma norm_shiftedSplineSlope_le (δ t x : ℝ) :
    ‖shiftedSplineSlope δ t x‖ ≤ splineSlopeBound δ t := by
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro j _
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, phase_norm, mul_one]

def splineRatio (δ : ℝ) : ℝ := Real.exp (-2*δ)

def splineInvScale (δ : ℝ) : ℝ := 256*Real.exp (-8*δ)

def splineBinomialMass (δ : ℝ) (k : ℕ) : ℝ :=
  ((k+7).choose 7 : ℝ)*splineRatio δ^k

lemma splineRatio_pos (δ : ℝ) : 0 < splineRatio δ := Real.exp_pos _

lemma splineRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : splineRatio δ < 1 := by
  exact (Real.exp_lt_exp.mpr (by linarith : -2*δ < 0)).trans_eq Real.exp_zero

lemma splineInvScale_pos (δ : ℝ) : 0 < splineInvScale δ := by
  dsimp only [splineInvScale]
  positivity

lemma splineBinomialMass_nonneg (δ : ℝ) (k : ℕ) : 0 ≤ splineBinomialMass δ k :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (splineRatio_pos δ).le _)

lemma hasSum_splineBinomialMass {δ : ℝ} (hδ : 0 < δ) :
    HasSum (splineBinomialMass δ) (1/(1-splineRatio δ)^8) := by
  have hn : ‖splineRatio δ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (splineRatio_pos δ)]
    exact splineRatio_lt_one hδ
  exact hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 7 hn

def splineDualTerm (δ s : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  (-Complex.I)*((splineInvScale δ*splineBinomialMass δ k/(s+8+2*k) : ℝ) : ℂ)*
    phase (-(s+8+2*k)) x

def splineDual (δ s x : ℝ) : ℂ := ∑' k : ℕ, splineDualTerm δ s k x

lemma norm_splineDualTerm_le (δ : ℝ) {s : ℝ} (hs : 0 < s+8) (k : ℕ) (x : ℝ) :
    ‖splineDualTerm δ s k x‖ ≤
      (splineInvScale δ/(s+8))*splineBinomialMass δ k := by
  have hden : 0 < s+8+2*(k : ℝ) := by positivity
  have hnum : 0 ≤ splineInvScale δ*splineBinomialMass δ k :=
    mul_nonneg (splineInvScale_pos δ).le (splineBinomialMass_nonneg δ k)
  rw [splineDualTerm, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le),
    phase_norm, mul_one]
  calc
    _ ≤ splineInvScale δ*splineBinomialMass δ k/(s+8) :=
      div_le_div_of_nonneg_left hnum (by linarith only [hs])
        (le_add_of_nonneg_right (by positivity))
    _ = _ := by ring

lemma summable_splineDualTerm {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s+8) (x : ℝ) :
    Summable (fun k => splineDualTerm δ s k x) :=
  Summable.of_norm_bounded
    ((hasSum_splineBinomialMass hδ).summable.mul_left (splineInvScale δ/(s+8)))
    (fun k => norm_splineDualTerm_le δ hs k x)

/-- The negative-frequency primitive is bounded uniformly in the translation. -/
lemma norm_splineDual_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s+8) (x : ℝ) :
    ‖splineDual δ s x‖ ≤ (splineInvScale δ/(s+8))*(1/(1-splineRatio δ)^8) :=
  tsum_of_norm_bounded
    ((hasSum_splineBinomialMass hδ).mul_left (splineInvScale δ/(s+8)))
    (fun k => norm_splineDualTerm_le δ hs k x)

lemma hasDerivAt_splineDualTerm (δ : ℝ) {s : ℝ} (hs : 0 < s+8) (k : ℕ) (x : ℝ) :
    HasDerivAt (splineDualTerm δ s k)
      (-((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*phase (-(s+8+2*k)) x) x := by
  have h := (hasDerivAt_phase (-(s+8+2*(k : ℝ))) x).const_mul
    ((-Complex.I)*((splineInvScale δ*splineBinomialMass δ k/(s+8+2*k) : ℝ) : ℂ))
  have hden : ((s+8+2*(k : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show s+8+2*(k : ℝ) ≠ 0 from (by positivity : 0 < s+8+2*(k : ℝ)).ne')
  have halg (A z v : ℂ) (hz : z ≠ 0) :
      (-Complex.I)*(A/z)*(v*((-z)*Complex.I)) = -A*v := by
    calc
      _ = (A/z)*z*(Complex.I*Complex.I)*v := by ring
      _ = -A*v := by rw [div_mul_cancel₀ _ hz, Complex.I_mul_I]; ring
  have he : (-Complex.I)*((splineInvScale δ*splineBinomialMass δ k/(s+8+2*k) : ℝ) : ℂ)*
      (phase (-(s+8+2*k)) x*((((-(s+8+2*(k : ℝ))) : ℝ) : ℂ)*Complex.I)) =
      -((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*phase (-(s+8+2*k)) x := by
    rw [Complex.ofReal_div, Complex.ofReal_neg]
    exact halg _ _ _ hden
  rw [he] at h
  exact h

lemma hasDerivAt_splineDual_series {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s+8) (x : ℝ) :
    HasDerivAt (splineDual δ s)
      (∑' k : ℕ, -((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*
        phase (-(s+8+2*k)) x) x := by
  apply hasDerivAt_tsum
    ((hasSum_splineBinomialMass hδ).summable.mul_left (splineInvScale δ))
    (fun k y => hasDerivAt_splineDualTerm δ hs k y)
    (fun k y => ?_) (summable_splineDualTerm hδ hs 0) x
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (splineInvScale_pos δ).le (splineBinomialMass_nonneg δ k)),
    phase_norm, mul_one]

def inverseSplineNumerator (δ x : ℝ) : ℂ :=
  (splineInvScale δ : ℂ)*phase (-8) x/(1-(splineRatio δ : ℂ)*phase (-2) x)^8

lemma phase_dual_split (s x : ℝ) (k : ℕ) :
    phase (-(s+8+2*k)) x=phase (-s) x*phase (-8) x*(phase (-2) x)^k := by
  simp only [phase]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma hasSum_splineDual_derivative {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    HasSum (fun k : ℕ => -((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*
      phase (-(s+8+2*k)) x) (-phase (-s) x*inverseSplineNumerator δ x) := by
  have hq : ‖(splineRatio δ : ℂ)*phase (-2) x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (splineRatio_pos δ),
      phase_norm, mul_one]
    exact splineRatio_lt_one hδ
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 7 hq).mul_left
    (-phase (-s) x*(splineInvScale δ : ℂ)*phase (-8) x)
  have he : (fun k : ℕ => -((splineInvScale δ*splineBinomialMass δ k : ℝ) : ℂ)*
      phase (-(s+8+2*k)) x) =
      (fun k : ℕ => (-phase (-s) x*(splineInvScale δ : ℂ)*phase (-8) x)*
        (((k+7).choose 7 : ℂ)*((splineRatio δ : ℂ)*phase (-2) x)^k)) := by
    funext k
    rw [phase_dual_split]
    simp only [splineBinomialMass, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast, mul_pow]
    ring
  rw [he]
  have hv : (-phase (-s) x*(splineInvScale δ : ℂ)*phase (-8) x)*
      (1/(1-(splineRatio δ : ℂ)*phase (-2) x)^8)=
      -phase (-s) x*inverseSplineNumerator δ x := by
    dsimp only [inverseSplineNumerator]
    ring
  rw [hv] at h
  exact h

/-- The bounded negative-frequency series is an exact dual primitive. -/
theorem hasDerivAt_splineDual {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s+8) (x : ℝ) :
    HasDerivAt (splineDual δ s) (-phase (-s) x*inverseSplineNumerator δ x) x := by
  have h := hasDerivAt_splineDual_series hδ hs x
  rw [(hasSum_splineDual_derivative hδ s x).tsum_eq] at h
  exact h

lemma exp_real_phase (a δ x : ℝ) :
    Complex.exp ((a : ℂ)*((δ : ℂ)+(x : ℂ)*Complex.I)) =
      (Real.exp (a*δ) : ℂ)*phase a x := by
  rw [phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma sinh_exp_factor (z : ℂ) :
    Complex.sinh z=Complex.exp z/2*(1-Complex.exp (-2*z)) := by
  have he : Complex.exp z*Complex.exp (-2*z)=Complex.exp (-z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [Complex.sinh]
  calc
    _ = (Complex.exp z-Complex.exp z*Complex.exp (-2*z))/2 := by rw [he]
    _ = _ := by ring

lemma inverseSplineNumerator_eq {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    inverseSplineNumerator δ x=1/Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8 := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hq : ‖(splineRatio δ : ℂ)*phase (-2) x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (splineRatio_pos δ),
      phase_norm, mul_one]
    exact splineRatio_lt_one hδ
  have hden : 1-(splineRatio δ : ℂ)*phase (-2) x ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [← he, norm_one] at hq
    exact (lt_irrefl _ hq)
  have he2 : Complex.exp (-2*z)=(splineRatio δ : ℂ)*phase (-2) x := by
    simpa only [splineRatio, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      exp_real_phase (-2) δ x
  have he8 : Complex.exp (-8*z)=(Real.exp (-8*δ) : ℂ)*phase (-8) x := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_ofNat] using exp_real_phase (-8) δ x
  have hsin : Complex.sinh z ≠ 0 := by
    rw [sinh_exp_factor, he2]
    exact mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _) (by norm_num)) hden
  apply (eq_div_iff (pow_ne_zero 8 hsin)).mpr
  rw [inverseSplineNumerator, sinh_exp_factor, he2, mul_pow, div_pow]
  have hprod : Complex.exp (-8*z)*Complex.exp z^8=1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    norm_num
  calc
    _ = Complex.exp (-8*z)*Complex.exp z^8 := by
      rw [he8]
      simp only [splineInvScale, Complex.ofReal_mul, Complex.ofReal_ofNat]
      field_simp
      ring
    _ = 1 := hprod

/-- Exact reciprocal-spline primitive, with no free coefficient choice. -/
theorem hasDerivAt_splineDual_exact {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (x : ℝ) :
    HasDerivAt (splineDual δ s)
      (-phase (-s) x/Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8) x := by
  simpa only [inverseSplineNumerator_eq hδ, mul_one_div] using
    hasDerivAt_splineDual hδ (by linarith only [hs]) x

def positiveBinomialPrimitive (δ v x : ℝ) : ℂ :=
  (splineInvScale δ : ℂ)⁻¹*splineDual δ (v-8) (-x)

lemma phase_neg_arg (u x : ℝ) : phase u (-x)=phase (-u) x := by
  simp only [phase, mul_neg, neg_mul]

lemma norm_positiveBinomialPrimitive_le {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v)
    (x : ℝ) :
    ‖positiveBinomialPrimitive δ v x‖ ≤ 1/v*(1/(1-splineRatio δ)^8) := by
  have hs : 0 < v-8+8 := by linarith only [hv]
  have hA := splineInvScale_pos δ
  rw [positiveBinomialPrimitive, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hA]
  calc
    _ ≤ (splineInvScale δ)⁻¹*((splineInvScale δ/(v-8+8))*(1/(1-splineRatio δ)^8)) :=
      mul_le_mul_of_nonneg_left (norm_splineDual_le hδ hs (-x)) (inv_nonneg.mpr hA.le)
    _ = _ := by rw [sub_add_cancel]; field_simp

lemma hasDerivAt_positiveBinomialPrimitive {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v)
    (x : ℝ) :
    HasDerivAt (positiveBinomialPrimitive δ v)
      (phase v x/(1-(splineRatio δ : ℂ)*phase 2 x)^8) x := by
  have hs : 0 < v-8+8 := by linarith only [hv]
  have h := ((hasDerivAt_splineDual hδ hs (-x)).scomp x
    (hasDerivAt_id x).neg).const_mul (splineInvScale δ : ℂ)⁻¹
  have he : (splineInvScale δ : ℂ)⁻¹*
      ((-1 : ℝ) • (-phase (-(v-8)) (-x)*inverseSplineNumerator δ (-x))) =
      phase v x/(1-(splineRatio δ : ℂ)*phase 2 x)^8 := by
    simp only [inverseSplineNumerator, phase_neg_arg, neg_neg, neg_smul, one_smul,
      neg_mul, neg_neg]
    have hp : phase (v-8) x*phase 8 x=phase v x := by
      rw [← phase_freq_add, sub_add_cancel]
    have hA : (splineInvScale δ : ℂ) ≠ 0 := by
      exact_mod_cast (splineInvScale_pos δ).ne'
    calc
      _ = (phase (v-8) x*phase 8 x)/(1-(splineRatio δ : ℂ)*phase 2 x)^8 := by
        field_simp
      _ = _ := by rw [hp]
  rw [he] at h
  exact h

#print axioms hasDerivAt_shiftedSplineNumerator
#print axioms norm_splineDual_le
#print axioms hasDerivAt_splineDual_exact
#print axioms hasDerivAt_positiveBinomialPrimitive
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
