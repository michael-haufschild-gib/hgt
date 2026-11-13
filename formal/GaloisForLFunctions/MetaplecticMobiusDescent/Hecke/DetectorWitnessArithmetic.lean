/-
Detector witness arithmetic adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorFourierSeparation
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.GammaZeroDetector

/-!
# Detector witness arithmetic

Free rows and nonzero ideals of the inverse amplification and its injective row map; dyadic
blocks of the finite detector; exponential witness sums and their tails; maxima over detector
family inclusions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
namespace Parameters
open ProbePhysical ProbeHighRowFamily CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

theorem exists_fixed_source (e : ℝ) (he : 0< e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
  obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
    (S₀∪fixedBadPrimes)
    (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (CanonicalRowCompletion.fixedBadPrimes_prime P))
    Finset.subset_union_right
  refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero

theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
    (∀x,0≤ w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W⊆Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
  refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
  have hcl : tsupport w⊆Set.Icc 1 2 :=
    closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hcl hx).1
end Parameters

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => Eisenstein.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, if_neg hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, if_neg hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, if_neg hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end HeckeDetectorWitnessArithmetic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

lemma exponential_cubic_bound (x Y : ℝ) (hx : 0 < x) (hY : 0 < Y) :
    x * Real.exp (-x/Y) ≤ 6*Y^3/x^2 := by
  have he := Real.pow_div_factorial_le_exp (x/Y) (show 0 ≤ x/Y by positivity) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x/Y))).le
  have hex : Real.exp (x/Y)*Real.exp (-(x/Y))=1 := by rw [←Real.exp_add]; simp
  rw [hex] at hh
  have hb : (x/Y)^3*Real.exp (-(x/Y)) ≤ 6 := by nlinarith
  calc
    _ = (Y^3/x^2)*((x/Y)^3*Real.exp (-(x/Y))) := by
      rw [neg_div]
      field_simp
    _ ≤ (Y^3/x^2)*6 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma divisor_count (I : Ideal O) (hI : I ≠ 0) :
    ((idealDivisors I).card : ℝ) ≤ 128*(Ideal.absNorm I : ℝ) := by
  apply EisensteinLatticeCount.finite_ideal_count_real
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  · intro J hJ
    exact ne_zero_of_dvd_ne_zero hI ((mem_idealDivisors hI).mp hJ)
  · intro J hJ
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm ((mem_idealDivisors hI).mp hJ))

theorem cutoffCoefficient_bound (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D : ℝ) (I : Ideal O) :
    ‖cutoffCoefficient V D I‖ ≤ 128*B*(Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [cutoffCoefficient,hI]
  rw [cutoffCoefficient,if_neg hI]
  let e := mulFiberDivisorEquiv I hI
  have he : (∑' p : MulFiber I, (moebius p.val.1 : ℂ)*V ((Ideal.absNorm p.val.1 : ℝ)/D)) =
      ∑' J : {J : Ideal O // J ∈ idealDivisors I},
        (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D) :=
    e.tsum_eq (fun J => (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D))
  rw [he,tsum_fintype]
  calc
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I},
        ‖(moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D)‖ := norm_sum_le _ _
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I}, B := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IdealCoprimeBilinearSieve.moebius_norm_le_one _)).trans (hV _)
    _ = ((idealDivisors I).card : ℝ)*B := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (divisor_count I hI) hB]

lemma norm_weight_two (I : Ideal O) (hI : I ≠ 0) :
    ‖fullIdealWeight 2 I‖ = 1/(Ideal.absNorm I : ℝ)^2 := by
  rw [fullIdealWeight,if_neg hI,Complex.cpow_neg,Complex.cpow_ofNat,
    norm_inv,norm_pow,Complex.norm_natCast]
  simp [one_div]

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,fullIdealWeight,if_neg hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)< Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,fullIdealWeight]
  have hN : (0 : ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

def terminalRemainder (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

lemma exponentialTerm_half (χ : Character) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : Character) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

def terminalTerm (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : Character) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

theorem terminal_sum_finite (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ I ∈ HeckeInverseAmplification.idealsUpTo ⌈2*U⌉₊, terminalTerm χ V T D Y U s I := by
  apply tsum_eq_sum
  intro I hI
  by_cases hI0 : I = 0
  · simp [terminalTerm,exponentialTerm,cutoffCoefficient,hI0]
  have hN : (⌈2*U⌉₊ : ℝ) < Ideal.absNorm I := by
    have hn : ¬Ideal.absNorm I ≤ ⌈2*U⌉₊ := by
      intro hh
      apply hI
      exact HeckeInverseAmplification.mem_idealsUpTo.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0),hh⟩
    exact_mod_cast lt_of_not_ge hn
  have ht : T ((Ideal.absNorm I : ℝ)/U)=0 := by
    apply hTzero
    apply (le_div_iff₀ hU).mpr
    linarith [Nat.le_ceil (2*U)]
  simp only [terminalTerm,ht,mul_zero]

end HeckeDetectorTail

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace HeckeDetectorFinite
open HeckeFamily HeckeInverseAmplification HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss 
local notation "O" => Eisenstein.O

def pairSet (U : ℝ) : Finset (Ideal O × Ideal O) :=
  (idealsUpTo ⌈2*U⌉₊) ×ˢ (idealsUpTo ⌈2*U⌉₊)

lemma pairCoefficient_zero_left (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

theorem pair_fiber (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val) =
      terminalTerm χ V T D Y U s I := by
  have h := weighted_fiber χ V D s I
  unfold terminalTerm exponentialTerm
  rw [←h,←tsum_mul_right,←tsum_mul_right,←tsum_mul_right]
  apply tsum_congr
  intro p
  simp only [pairCoefficient,p.property]

theorem terminal_sum_eq_pair_sum (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p := by
  have hfinite : Function.HasFiniteSupport (pairCoefficient χ V T D Y U s) := by
    apply (pairSet U).finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (pairCoefficient_support χ V T D Y U hU hT s p hn)
  have hsum := (summable_of_hasFiniteSupport hfinite).hasSum.tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun I : Ideal O => ∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val)
    (∑' p, pairCoefficient χ V T D Y U s p) at hsum
  simp_rw [pair_fiber] at hsum
  rw [hsum.tsum_eq]
  exact tsum_eq_sum (pairCoefficient_support χ V T D Y U hU hT s)

def dyadicBlock (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k)

theorem terminal_sum_eq_dyadic (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        ∑ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1), dyadicBlock χ V T D Y U s j k := by
  have hX : (0 : ℝ) < ⌈2*U⌉₊ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (2*U))
  rw [terminal_sum_eq_pair_sum χ V T D Y U hU hT s]
  apply actual_pair_reassembly χ V T hV hVzero D Y U _ _ hX hX s
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1,hp1b⟩ := mem_idealsUpTo.mp h1
  obtain ⟨hp2,hp2b⟩ := mem_idealsUpTo.mp h2
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega),
    Ideal.absNorm_eq_zero_iff.not.mp (by omega),by exact_mod_cast hp1b,by exact_mod_cast hp2b⟩

theorem exists_dyadic_block (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (c : ℝ)
    (hc : c ≤ ‖∑' I : Ideal O, terminalTerm χ V T D Y U s I‖) :
    ∃ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
      ∃ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        c ≤ (((length (⌈2*U⌉₊ : ℝ)+1 : ℕ) : ℝ)^2)*‖dyadicBlock χ V T D Y U s j k‖ := by
  rw [terminal_sum_eq_dyadic χ V T D Y U hU hT hV hVzero s] at hc
  obtain ⟨j,hj,k,hk,hb⟩ := exists_large_pair (length (⌈2*U⌉₊ : ℝ))
    (length (⌈2*U⌉₊ : ℝ)) (dyadicBlock χ V T D Y U s)
  exact ⟨j,hj,k,hk,by simpa only [pow_two] using hc.trans hb⟩

theorem nonzero_block_scale_bounds (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hD : 0 < D) (hU : 0 < U)
    (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (j k : ℕ)
    (hb : dyadicBlock χ V T D Y U s j k ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨p,hp,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hk := (mul_ne_zero_iff.mp hne).2
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  simp only [pairCoefficient,ne_eq,mul_eq_zero,not_or] at hc
  obtain ⟨⟨⟨⟨⟨hmu,hfirst⟩,hweight⟩,hexp⟩,hproduct⟩,hterminal⟩ := hc
  apply pair_scale_bounds V T hV hVzero hT
    (Ideal.absNorm p.1) (Ideal.absNorm p.2) D U (by positivity) (by positivity)
    hD hU j k hj hk hfirst
  · simpa only [map_mul,Nat.cast_mul] using hproduct
  · simpa only [map_mul,Nat.cast_mul] using hterminal

end HeckeDetectorFinite

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Set
namespace HeckeDetectorDyadicBridge
open HeckeFamily HeckeInverseAmplification HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss 
local notation "O" => Eisenstein.O

def fourierSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U⌉₊

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma pairSet_subset_fourier (U : ℝ) (hU : 0≤ U) :
    pairSet U ⊆ fourierSet U ×ˢ fourierSet U := by
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  have hb : ⌈2*U⌉₊ ≤ ⌈16*U⌉₊ := Nat.ceil_mono (by linarith)
  exact Finset.mem_product.mpr
    ⟨mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h1).1,(mem_idealsUpTo.mp h1).2.trans hb⟩,
     mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h2).1,(mem_idealsUpTo.mp h2).2.trans hb⟩⟩

lemma annular_covered (U D : ℝ) (hD : 0< D) (hDU : D≤8*U)
    (W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤ x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : W ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hr : (J.absNorm : ℝ)/D<2 := lt_of_not_ge (fun hn => hw (hW _ hn))
  have hn : (J.absNorm : ℝ)≤16*U := by
    have hh := (div_lt_iff₀ hD).mp hr
    linarith
  exact_mod_cast hn.trans (Nat.le_ceil (16*U))

lemma inverse_annular_covered (U D Dstar : ℝ) (hD : 0< D) (hDU : D≤8*U)
    (V W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤ x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply annular_covered U D hD hDU W hW J hJ
  exact (mul_ne_zero_iff.mp hw).2

lemma scales_le_eight_terminal (U : ℝ) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U) :
    (2 : ℝ)^j≤8*U ∧ (2 : ℝ)^k≤8*U := by
  have hj : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hk : 1≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hk).trans hprod.le
  · exact (le_mul_of_one_le_left (by positivity) hj).trans hprod.le

theorem dyadicBlock_eq_fourier_rectangle (χ : Character) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0< U) (hT : ∀ x : ℝ, 2≤ x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end HeckeDetectorDyadicBridge

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤ U) (hx : 1≤ x) (hxU : x≤8*U^21) :
    0≤ Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0< U := by linarith
  have hU1 : 1< U := by linarith
  have hxp : 0< x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤ U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤ Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤ Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1< U) (hcost : 8≤ U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8< U^r*U^m) :
    r≤ t+ε ∧ t-ε≤ r+m := by
  have hUp : 0< U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤ U) (ht : 1≤ t) (ht' : t≤3/2) :
    2≤ U^t ∧ U^t≤ U^(3/2 : ℝ) := by
  have hU1 : 1≤ U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end HeckeDetectorDyadicGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace HeckeDetectorCoefficientBounds
open HeckeFamily HeckeDetectorFourier HeckeDetectorTail
open HeckeInverseAmplification
local notation "O" => Eisenstein.O

lemma annular_norm_le_two (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖DyadicTransfer.annularCutoff V x‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [hV x,hV (2*x)])

lemma inverseCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact IdealCoprimeBilinearSieve.moebius_norm_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

def expandedSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U^21⌉₊

lemma expandedSet_count (U : ℝ) (hU : 1 ≤ U) :
    ((expandedSet U).card : ℝ) ≤ 4096*U^21 := by
  have hp : 1 ≤ U^21 := one_le_pow₀ hU
  have hc : (1 : ℝ) ≤ ⌈16*U^21⌉₊ := (by linarith : (1 : ℝ) ≤ 16*U^21).trans (Nat.le_ceil _)
  have h := EisensteinLatticeCount.finite_ideal_count_real (expandedSet U) (⌈16*U^21⌉₊ : ℝ) hc
    (fun I hI => Ideal.absNorm_eq_zero_iff.not.mp (by have := (mem_idealsUpTo.mp hI).1; omega))
    (fun I hI => by exact_mod_cast (mem_idealsUpTo.mp hI).2)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16*U^21 by positivity)
  linarith

theorem coefficient_mass (χ : Character) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end HeckeDetectorCoefficientBounds

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorDyadicBridge
local notation "O" => Eisenstein.O

theorem dyadic_frequency_bound (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : Character) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end HeckeDetectorFrequency

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end HeckeDetectorRowSpecialization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

def SixthFree (I : Ideal O) : Prop := ∀ P, (normalizedFactors I).count P<6

theorem ideal_decomposition_unique {I J A B : Ideal O}
    (hI : I≠0) (hJ : J≠0) (hA : A≠0) (hB : B≠0)
    (hIf : SixthFree I) (hJf : SixthFree J) (he : I*A^6=J*B^6) :
    I=J ∧ A=B := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hI (pow_ne_zero _ hA),
    normalizedFactors_mul hJ (pow_ne_zero _ hB),normalizedFactors_pow,normalizedFactors_pow] at hf
  have hc (P : Ideal O) := congrArg (Multiset.count P) hf
  have hcounts (P : Ideal O) :
      (normalizedFactors I).count P=(normalizedFactors J).count P ∧
      (normalizedFactors A).count P=(normalizedFactors B).count P := by
    have hh := hc P
    simp only [Multiset.count_add,Multiset.count_nsmul] at hh
    have hi := hIf P
    have hj := hJf P
    omega
  have hIJ : normalizedFactors I=normalizedFactors J :=
    Multiset.ext.mpr (fun P => (hcounts P).1)
  have hAB : normalizedFactors A=normalizedFactors B :=
    Multiset.ext.mpr (fun P => (hcounts P).2)
  constructor
  · simpa only [Ideal.prod_normalizedFactors_eq_self hI,Ideal.prod_normalizedFactors_eq_self hJ]
      using congrArg Multiset.prod hIJ
  · simpa only [Ideal.prod_normalizedFactors_eq_self hA,Ideal.prod_normalizedFactors_eq_self hB]
      using congrArg Multiset.prod hAB

abbrev FreeRow := {u : O // u≠0 ∧ SixthFree (Ideal.span {u})}
abbrev NonzeroIdeal := CubicEisenstein.NonzeroIdeal

def rowMap (p : FreeRow×NonzeroIdeal) : O :=
  p.1.val*(cubicIdealGenerator p.2.val)^6

theorem rowMap_ne_zero (p : FreeRow×NonzeroIdeal) : rowMap p≠0 :=
  mul_ne_zero p.1.property.1 (pow_ne_zero _ (cubicIdealGenerator_ne_zero
    p.2.val p.2.property))

theorem rowMap_span (p : FreeRow×NonzeroIdeal) :
    Ideal.span {rowMap p}=Ideal.span {p.1.val}*p.2.val^6 := by
  unfold rowMap
  rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,
    span_cubicIdealGenerator]

theorem rowMap_injective : Function.Injective rowMap := by
  intro p q hpq
  have he := congrArg (fun u : O => Ideal.span {u}) hpq
  rw [rowMap_span,rowMap_span] at he
  have hd := ideal_decomposition_unique
    (Ideal.span_singleton_eq_bot.not.mpr p.1.property.1)
    (Ideal.span_singleton_eq_bot.not.mpr q.1.property.1)
    p.2.property q.2.property p.1.property.2 q.1.property.2 he
  have ha : p.2=q.2 := Subtype.ext hd.2
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val*(cubicIdealGenerator p.2.val)^6=
      q.1.val*(cubicIdealGenerator q.2.val)^6 at hpq
    rw [ha] at hpq
    exact mul_right_cancel₀ (pow_ne_zero _ (cubicIdealGenerator_ne_zero
      q.2.val q.2.property)) hpq
  · exact ha

theorem rowMap_norm (p : FreeRow×NonzeroIdeal) :
    (Ideal.span {rowMap p}).absNorm=(Ideal.span {p.1.val}).absNorm*p.2.val.absNorm^6 := by
  rw [rowMap_span,map_mul,map_pow]

end HeckeInverseAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_reciprocal_identity (χ ψ : Character) (P : HeckeIdealSeries.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    {s : ℂ} (hs : 1< s.re) :
    series χ true s=(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s))*series ψ true s := by
  have hL : LFunction ψ s=LFunction χ s*(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s)) := by
    rw [LFunction_eq_series ψ hs,LFunction_eq_series χ hs,hm,
      IdealEuler.series_deletePrimes {P} (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs]
    simp only [Finset.prod_singleton]
    change IdealEuler.series (idealCoeff χ) s *
      (1-idealCoeff χ P.val*fullIdealWeight s P.val)=_
    rw [fullIdealWeight,if_neg P.property.ne_zero]
  have h0 : s≠0 := by intro h; norm_num [h] at hs
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  simp only [series,ite_true,HeckeReciprocal.reciprocal_eq_inv χ h0 h1,
    HeckeReciprocal.reciprocal_eq_inv ψ h0 h1]
  have hχ := LFunction_ne_zero_of_one_lt_re χ hs
  have hψ := LFunction_ne_zero_of_one_lt_re ψ hs
  apply (mul_right_cancel₀ hψ)
  rw [mul_assoc,inv_mul_cancel₀ hψ,mul_one,hL]
  rw [←mul_assoc,inv_mul_cancel₀ hχ,one_mul]

lemma rescaled_power (D N : ℝ) (hD : 0< D) (hN : 0< N) (w : ℂ) :
    (D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w)=
      (N : ℂ)^(-(1/2 : ℂ))*((D/N : ℝ) : ℂ)^(w-(1/2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hD hN).ne')]
  rw [←Complex.ofReal_log hD.le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log (div_pos hD hN).le,Real.log_div hD.ne' hN.ne']
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem prime_column_identity (χ ψ : Character) (P : HeckeIdealSeries.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0< D) :
    polynomial χ true W D σ freq=polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq := by
  let N : ℝ := P.val.absNorm
  have hN : 0< N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc : 1<(2-σ)+σ := by linarith
  have he (t : ℝ) : integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)=
      integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)-
      (idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ)))*
        integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I) := by
    let w : ℂ := (((2-σ : ℝ) : ℂ)+t*I)+shift σ freq
    have hw : 1< w.re := by dsimp [w]; simp
    have hr := prime_reciprocal_identity χ ψ P hm hw
    have hp := rescaled_power D N hD hN w
    unfold integrand
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series χ true w=_
    rw [hr]
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*
      ((1-idealCoeff χ P.val*(N : ℂ)^(-w))*series ψ true w)=_
    calc
      _ = mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series ψ true w-
          idealCoeff χ P.val*mellin W _*((D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w))*series ψ true w := by ring
      _ = _ := by rw [hp]; ring
  have hI := integrand_vertical_integrable ψ true W a b ha hWs hW D (2-σ) σ freq hD hc
  have hJ := integrand_vertical_integrable ψ true W a b ha hWs hW (D/N) (2-σ) σ freq (div_pos hD hN) hc
  rw [polynomial_mellin χ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW (D/(P.val.absNorm : ℝ)) (2-σ) σ freq (div_pos hD hN) hc]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))=_
  simp_rw [he]
  rw [integral_sub hI (hJ.const_mul _),integral_const_mul]
  change _=(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))-
    idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ))*
      ((1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I)))
  ring

end HeckeInverseAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion

theorem row_coeff_zero_unsupported (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : lambda∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬quadraticSupported J) :
    idealCoeff χ J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := cubicIdealGenerator J
  have hn : n≠0 := cubicIdealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := span_cubicIdealGenerator J
  rw [←hs,idealCoeff_span χ hn,heq]
  exact rowTwist_zero_of_not_supported (elementHom η) m f z n hmLam hm2 (fun h => hJ (hs ▸ h))

theorem prime_coprime_iff (P : HeckeIdealSeries.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : Character) (m f z a : O)
    (P : HeckeIdealSeries.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hψ : ∀ n : O, elementCoeff ψ n=rowTwist (elementHom η) m f (z*a^6) n)
    (hmLam : lambda∣m) (hm2 : (2 : O)∣m) :
    idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : quadraticSupported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

end HeckeInverseAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : HeckeIdealSeries.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0< D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤ P.val.absNorm := by
    exact_mod_cast (show 1≤ P.val.absNorm from (HeckeIdealSeries.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)< P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]

theorem finite_amplification (rows : Finset FreeRow) (multipliers : Finset NonzeroIdeal)
    (target : Finset O) (F : FreeRow→ℝ) (E : O→ℝ) (K : ℝ)
    (hK : 0≤ K) (hE : ∀ u, 0≤ E u)
    (hmap : ∀ u∈rows, ∀ A∈multipliers, rowMap (u,A)∈target)
    (hamp : ∀ u∈rows, ∀ A∈multipliers, F u≤ K*E (rowMap (u,A))) :
    (multipliers.card : ℝ)*(∑ u∈rows, F u)≤ K*∑ v∈target, E v := by
  have hs : (multipliers.card : ℝ)*(∑ u∈rows, F u)=
      ∑ p∈rows×ˢmultipliers, F p.1 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ ∑ p∈rows×ˢmultipliers, K*E (rowMap p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
      exact hamp p.1 hu p.2 hA
    _ = K*∑ v∈(rows×ˢmultipliers).image rowMap, E v := by
      rw [Finset.mul_sum,Finset.sum_image]
      exact fun p hp q hq h => rowMap_injective h
    _ ≤ K*∑ v∈target, E v := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
        exact hmap p.1 hu p.2 hA
      · intro v hv hn
        exact hE v

end HeckeInverseAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : lambda∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda^2∣r-1) (hx : f^4*z=(u : O)*lambda^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : lambda∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤ c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp

theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : lambda∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda^2∣r-1) (hx : f^4*z=(u : O)*lambda^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : lambda∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤ c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]

end HeckePrimeNonprincipal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace HeckeDetectorFamilyInclusion
open HeckeFamily HeckeDetectorZeros Complex

theorem maximum_le_of_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ)
    (hinclude : ∀ i,∃ j, ∀ s : ℂ, LFunction (χ i) s=LFunction (ψ j) s) :
    zeroMaximum χ hχ T≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j,hj⟩ := hinclude i
    rw [←hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · rw [←hj s]
      exact hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

theorem maximum_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hχ T≤ zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inl i,fun _ => rfl⟩

theorem maximum_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum ψ hψ T≤ zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inr i,fun _ => rfl⟩

theorem inverse_nonprincipal (χ : Character) (hχ : χ.residue≠1) : χ.inverse.residue≠1 := by
  change χ.residue⁻¹≠1
  simpa only [ne_eq,inv_eq_one] using hχ

theorem maximum_inverse {ι : Type*} [Fintype ι] (χ : ι→Character)
    (hχ : ∀ i,(χ i).residue≠1) (T : ℝ) :
    zeroMaximum (fun i => (χ i).inverse) (fun i => inverse_nonprincipal (χ i) (hχ i)) T=
      zeroMaximum χ hχ T := by
  let ψ := fun i => (χ i).inverse
  have hψ := fun i => inverse_nonprincipal (χ i) (hχ i)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T hm
      rw [LFunction_inverse_conj (χ i) (hχ i),map_eq_zero] at hz
      have hh := zero_re_le_maximum χ hχ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
      have hz' : LFunction (ψ i) (conj s)=0 := by
        rw [LFunction_inverse_conj (χ i) (hχ i),conj_conj,hz,map_zero]
      have hh := zero_re_le_maximum ψ hψ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz'
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

end HeckeDetectorFamilyInclusion

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
