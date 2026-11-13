/-
Gaussian windows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.CalibrationCharacters

/-!
# Gaussian windows

Fixed Gaussian windows, Mellin profiles, joint densities and annuli of the probe; the inverse
Mellin transform of the Gaussian vertical kernel; Gaussian completion of the selected
summands.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical

/-- The inverse Mellin transform of the Gaussian vertical kernel. -/
def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

lemma gaussianMellin_integral (y : ℝ) (hy : 0< y) (σ : ℝ) :
    (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      (Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log (y:ℂ))^2/4) := by
  have hi (v : ℝ) :
      (y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2)=
      Complex.exp ((-1:ℂ)*(v:ℂ)^2+
        (Complex.I*(2*(σ:ℂ)-Complex.log (y:ℂ)))*(v:ℂ)+
        ((σ:ℂ)^2-Complex.log (y:ℂ)*(σ:ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),←Complex.exp_add]
    congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hi]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re<0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma gaussianMellin_inversion (y : ℝ) (hy : 0< y) (σ : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)*
      (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      gaussianMellinProfile y := by
  rw [gaussianMellin_integral y hy σ]
  exact mul_assoc _ _ _ |>.symm

lemma gaussian_completed_norm_power (a b Z : ℝ) (ha : 0< a) (hb : 0< b) (hZ : 0< Z) (t : ℂ) :
    (Z:ℂ)^t*((a:ℂ)^(-t)*(b:ℂ)^(-(3*t)))=((a*b^3/Z:ℝ):ℂ)^(-t) := by
  rw [positive_div_cpow _ _ (mul_pos ha (pow_pos hb 3)).le hZ]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (pow_pos hb 3).le]
  have hp : ((b^3:ℝ):ℂ)^(-t)=(b:ℂ)^((3:ℂ)*(-t)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3:ℝ) (-t)).symm
  rw [hp,Complex.cpow_neg (Z:ℂ),div_inv_eq_mul]
  rw [show (3:ℂ)*(-t)= -(3*t) by ring]
  ring

lemma gaussianMellinProfile_norm (y : ℝ) (hy : 0< y) :
    ‖gaussianMellinProfile y‖=
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(Real.log y)^2/4) := by
  unfold gaussianMellinProfile
  rw [norm_mul,Complex.norm_exp,←Complex.ofReal_log hy.le]
  congr 2
  simp [←Complex.ofReal_pow]

lemma gaussianMellinProfile_power_bound (y : ℝ) (hy : 0< y) (a : ℝ) :
    ‖gaussianMellinProfile y‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (a^2)*y^(-a) := by
  rw [gaussianMellinProfile_norm y hy,Real.rpow_def_of_pos hy]
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log y/2-a)]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss CubicEisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

lemma gaussianCompleted_Vstar (y : ℝ) (hy : 0< y) :
    Vstar gaussianCompletedProfile y=gaussianMellinProfile y := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianCompletedProfile]
  field_simp

lemma gaussian_mellinSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (σ Z : ℝ) (hZ : 0< Z) (I J : Id) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫v : ℝ,mellinSummand S D Ψ σ Z (I,J) v)=
      correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hq : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z :=
    div_pos (mul_pos hi (pow_pos hj 3)) hZ
  have hp (v : ℝ) : mellinSummand S D Ψ σ Z (I,J) v=
      (((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z:ℝ):ℂ)^(-((σ:ℂ)+v*Complex.I))*
      Complex.exp (((σ:ℂ)+v*Complex.I)^2)*
      (completedMask S D I J*completedCorrection I J*
        (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J) := by
    unfold mellinSummand spectralSummand fullIdealWeight
    simp only [if_neg hI,if_neg hJ]
    rw [←gaussian_completed_norm_power _ _ Z hi hj hZ]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_mul_const,←mul_assoc,gaussianMellin_inversion _ hq σ]
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianCompleted_Vstar _ hq]
  ring

lemma gaussian_correctedSummand_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0< Z) :
    Summable (fun p : Id×Id=> correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2) := by
  have hs : Summable (fun p : Id×Id=>∫v : ℝ,‖mellinSummand S D Ψ 2 Z p v‖) := by
    simp only [mellinSummand_integral_norm S D Ψ 2 Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (2:ℂ) (by norm_num)).norm.mul_right _
  have hi : Summable (fun p : Id×Id=>∫v : ℝ,mellinSummand S D Ψ 2 Z p v) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun p=> norm_integral_le_integral_norm _) hs
  have hh := hi.mul_left (((1/(2*Real.pi):ℝ):ℂ))
  simpa only [gaussian_mellinSummand S D Ψ 2 Z hZ] using hh

/-- Mellin inversion identifies the spectral row with the Gaussian completed sum. -/
theorem spectralRow_eq_gaussianCompleted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (σ : ℝ) (hσ : 1<σ) (Z : ℝ) (hZ : 0< Z) :
    verticalIntegral σ (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow S D Ψ t)=
      correctedCompletedT S D Ψ gaussianCompletedProfile Z := by
  rw [verticalIntegral,spectralRow_integral_eq_tsum S D Ψ hΨ σ hσ Z hZ,←tsum_mul_left]
  unfold correctedCompletedT
  apply tsum_congr
  intro p
  exact gaussian_mellinSummand S D Ψ σ Z hZ p.1 p.2

theorem markedPhysicalProbe_eq_gaussian (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (X Y Z : ℝ) (hZ : 0< Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Y:ℂ)⁻¹*∑'s : {I : Id // _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported I},
        if ∀P∈C.excluded,¬P∣s.val then
          let a := primaryIdealGenerator s.val
          let ha := _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_primaryIdealGenerator_ne_zero s.val s.property
          let has := (_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_span_primaryIdealGenerator_iff s.val).mpr s.property
          let q : ℝ := Ideal.absNorm s.val
          W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val/
            (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
          ∑'m : O,C.residueMonoid m*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)*
            W0 (elementNorm m/(elementNorm C.generator*q*X))*
            correctedCompletedT C.excluded D (rowCoefficient η C.Xi a has m)
              gaussianCompletedProfile Z
        else 0 := by
  unfold markedPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    apply tsum_congr
    intro m
    rw [spectralRow_eq_gaussianCompleted _ _ _
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m) 4 (by norm_num) Z hZ]
  · rfl

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
namespace ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤ y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤ y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤ Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤ x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j< K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤ K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤ j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤ x) :
    HasSum (fun j : ℕ=> gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=> gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤ x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤ x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace ProbePhysical
open CompletedGauss

lemma gaussianMellinProfile_real (y : ℝ) (hy : 0< y) :
    gaussianMellinProfile y=
      ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
        (Real.exp (-(Real.log y)^2/4):ℂ) := by
  unfold gaussianMellinProfile
  rw [←Complex.ofReal_log hy.le]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_small (Z : ℝ) (j : ℕ) (y : ℝ) (hy : y≤1/2) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_small y hy,zero_mul,zero_div]
lemma gaussianDyadicProfile_large (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 2≤ y) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_large y hy,zero_mul,zero_div]

lemma gaussianDyadicProfile_compact (Z : ℝ) (j : ℕ) : HasCompactSupport (gaussianDyadicProfile Z j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianDyadicProfile Z j y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianDyadicProfile_small Z j y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianDyadicProfile_large Z j y (le_of_lt (lt_of_not_ge h)))

lemma gaussianDyadicProfile_contDiff (Z : ℝ) (hZ : 0< Z) (j : ℕ) :
    ContDiff ℝ ∞ (gaussianDyadicProfile Z j) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0< y
  · have he : gaussianDyadicProfile Z j =ᶠ[𝓝 y]
        (fun x : ℝ=> gaussianAnnulus x*
          (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
            (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))/(Real.sqrt x:ℂ)) := by
      filter_upwards [eventually_gt_nhds hy] with x hx
      rw [gaussianDyadicProfile,gaussianMellinProfile_real _ (div_pos (mul_pos (by positivity) hx) hZ)]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hq : (2:ℝ)^j*y/Z≠0 := ne_of_gt (div_pos (mul_pos (by positivity) hy) hZ)
    have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have ha := gaussianAnnulus_contDiff.contDiffAt (x:=y)
    have hl : ContDiffAt ℝ ∞ (fun x : ℝ=> Real.log ((2:ℝ)^j*x/Z)) y :=
      (show ContDiffAt ℝ ∞ (fun x : ℝ=>(2:ℝ)^j*x/Z) y by fun_prop).log hq
    have hg : ContDiffAt ℝ ∞ (fun x : ℝ=> Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4)) y :=
      ((hl.pow 2).neg.div_const 4).exp
    have hgC := Complex.ofRealCLM.contDiff.contDiffAt.comp y hg
    have hsR : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy.ne'
    have ht : ContDiffAt ℝ ∞ (fun x : ℝ=> gaussianAnnulus x*
        (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
          (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))) y :=
      ha.mul (contDiffAt_const.mul hgC)
    have hsc : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hsR
    simpa only [div_eq_mul_inv] using ht.mul (hsc.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianDyadicProfile_small Z j x hx.le

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0< y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma annular_reassembly_summable {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤ N p) :
    Summable (fun q : α×ℕ=> gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    · simp only [hp,mul_zero,norm_zero]
      exact hasSum_zero
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _=> norm_nonneg _)).mpr
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤ N p) :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=> fun j : ℕ=> gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq

lemma gaussian_dyadic_correctedSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (hZ : 0< Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z=
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hI : I≠0 := by intro he; subst I; simp [correctedSummand,markedSummand,CompletedGauss.summand] at h
  have hJ : J≠0 := by intro he; subst J; simp [correctedSummand,markedSummand,CompletedGauss.summand] at h
  have hi : 1≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤ Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0< Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z=
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=> gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0< Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)


end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_power_bound (z : ℂ) (hz : z≠0) (a : ℝ) :
    ‖gaussianLog z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (Real.pi^2/4+a^2)*‖z‖^(-a) := by
  have hre : (-(Complex.log z)^2/4).re=
      ((Complex.log z).im^2-(Real.log ‖z‖)^2)/4 := by
    simp [pow_two,Complex.mul_re,Complex.log_re]
  have hp : (Complex.log z).im^2≤ Real.pi^2 := by
    have h1 := Complex.log_im_le_pi z
    have h2 := Complex.neg_pi_lt_log_im z
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤ Real.pi+(Complex.log z).im by linarith)]
  unfold gaussianLog
  rw [norm_mul,Complex.norm_exp,hre,Real.rpow_def_of_pos (norm_pos_iff.mpr hz),
    mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log ‖z‖/2-a)]

lemma iteratedDeriv_restrict_positive (f : ℂ→ℂ)
    (hf : ∀x : ℝ,0< x→ AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) (hx : 0< x) :
    iteratedDeriv n (fun y : ℝ=> f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : Set.EqOn (deriv (fun y : ℝ=> f (y:ℂ))) (fun y : ℝ=> deriv f (y:ℂ)) (Set.Ioi 0) := by
      intro y hy
      exact (hf y hy).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he.iteratedDeriv_of_isOpen isOpen_Ioi n hx]
    exact ih (deriv f) (fun y hy=>(hf y hy).deriv)

lemma gaussianLog_analytic (z : ℂ) (hz : 0< z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0< r) (z : ℂ) (hz : 0< z.re) :
    AnalyticAt ℂ (fun w : ℂ=> gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)

lemma gaussianLog_scaled_disk_bound (a : ℝ) :
    ∃C : ℝ,0< C ∧ ∀r : ℝ,0< r→∀y∈Set.Icc (1/2:ℝ) 2,
      ∀z∈Metric.closedBall (y:ℂ) (1/4),‖gaussianLog ((r:ℂ)*z)‖≤ C*r^(-a) := by
  have hc : ContinuousOn (fun t : ℝ=> t^(-a)) (Set.Icc (1/4:ℝ) (9/4)) := by
    intro t ht
    exact (continuousAt_id.rpow_const (Or.inl (show t≠0 by linarith [ht.1]))).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBpos : 0< B := by
    have hh := hB 1 (by norm_num : (1:ℝ)∈Set.Icc (1/4:ℝ) (9/4))
    norm_num at hh
    linarith
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (Real.pi^2/4+a^2)
  have hcn : 0≤ c := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro r hr y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hyr : ‖(y:ℂ)‖=y := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hy.1])]
  have hu := norm_sub_norm_le z (y:ℂ)
  have hl := norm_sub_norm_le (y:ℂ) z
  rw [hyr] at hu hl
  rw [norm_sub_rev] at hl
  have hzn : ‖z‖∈Set.Icc (1/4:ℝ) (9/4) := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hz0 : z≠0 := norm_pos_iff.mp (by linarith [hzn.1])
  have hrz : (r:ℂ)*z≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz0
  have hb : ‖z‖^(-a)≤ B := (le_abs_self _).trans (hB ‖z‖ hzn)
  have hh := gaussianLog_power_bound ((r:ℂ)*z) hrz a
  have hnorm : ‖(r:ℂ)*z‖=r*‖z‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  rw [hnorm,Real.mul_rpow hr.le (norm_nonneg _)] at hh
  calc
    _ ≤ c*(r^(-a)*‖z‖^(-a)) := hh
    _ ≤ c*(r^(-a)*B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hcn
    _ ≤ (c+1)*B*r^(-a) := by nlinarith [mul_nonneg hBpos.le (Real.rpow_pos_of_pos hr (-a)).le]

lemma gaussianLog_scaled_derivative_bound (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀r : ℝ,0< r→∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (fun x : ℝ=> gaussianMellinProfile (r*x)) y‖≤ C*r^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLog_scaled_disk_bound a
  refine ⟨(n.factorial:ℝ)*B/(1/4:ℝ)^n,by positivity,?_⟩
  intro r hr y hy
  have hf : ∀x : ℝ,0< x→ AnalyticAt ℂ (fun z : ℂ=> gaussianLog ((r:ℂ)*z)) (x:ℂ) :=
    fun x hx=> gaussianLog_scaled_analytic r hr (x:ℂ) hx
  have he : (fun x : ℝ=> gaussianMellinProfile (r*x))=
      (fun x : ℝ=> gaussianLog ((r:ℂ)*(x:ℂ))) := by
    funext x
    rw [←Complex.ofReal_mul,gaussianLog_ofReal]
  rw [he,iteratedDeriv_restrict_positive _ hf n y (by linarith [hy.1])]
  have hd : DiffContOnCl ℂ (fun z : ℂ=> gaussianLog ((r:ℂ)*z)) (Metric.ball (y:ℂ) (1/4)) := by
    apply DifferentiableOn.diffContOnCl_ball (U:={z : ℂ|0< z.re})
      (fun z hz=>(gaussianLog_scaled_analytic r hr z hz).differentiableAt.differentiableWithinAt)
    intro z hz
    have hn : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have ha := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hn
    simp only [Complex.sub_re,Complex.ofReal_re,abs_le] at ha
    change 0< z.re
    linarith [hy.1]
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/4) hd
    (fun z hz=> hbound r hr y hy z (Metric.sphere_subset_closedBall hz))
  exact hh.trans_eq (by ring)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)
lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤ y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0< y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

def gaussianFixedSchwartz : SchwartzMap ℝ ℂ := gaussianFixedWindow_compact.toSchwartzMap gaussianFixedWindow_contDiff

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0< r) (y : ℝ) (hy : 0< y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=> gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=> gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

lemma gaussianDyadicProfile_factor (Z : ℝ) (j : ℕ) :
    gaussianDyadicProfile Z j=(fun y : ℝ=> gaussianFixedWindow y*
      gaussianMellinProfile (((2:ℝ)^j/Z)*y)) := by
  funext y
  unfold gaussianDyadicProfile gaussianFixedWindow
  rw [show (2:ℝ)^j*y/Z=((2:ℝ)^j/Z)*y by ring]
  ring

lemma gaussianDyadicProfile_derivative_outside (Z : ℝ) (j n : ℕ) (y : ℝ)
    (hy : y∉Set.Icc (1/2:ℝ) 2) : iteratedDeriv n (gaussianDyadicProfile Z j) y=0 := by
  have he : gaussianDyadicProfile Z j=ᶠ[𝓝 y](fun _=>0) := by
    simp only [Set.mem_Icc,not_and_or,not_le] at hy
    rcases hy with hy|hy
    · filter_upwards [eventually_lt_nhds hy] with x hx
      exact gaussianDyadicProfile_small Z j x hx.le
    · filter_upwards [eventually_gt_nhds hy] with x hx
      exact gaussianDyadicProfile_large Z j x hx.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianDyadicProfile_derivative_uniform (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,0< Z→∀j : ℕ,∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤ C*(((2:ℝ)^j/Z)^(-a)) := by
  choose B hB hbound using fun i : ℕ=> gaussianLog_scaled_derivative_bound a i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i gaussianFixedSchwartz
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤ A i := by exact apply_nonneg _ _
  have hC : 0≤ C := Finset.sum_nonneg (fun i _=> mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro Z hZ j y hy
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  have hy0 : 0< y := by linarith [hy.1]
  rw [gaussianDyadicProfile_factor,iteratedDeriv_fun_mul
    (gaussianFixedWindow_contDiff.contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    ((gaussianProfile_scaled_smooth _ hr y hy0).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i gaussianFixedWindow y*
        iteratedDeriv (n-i) (fun x : ℝ=> gaussianMellinProfile (((2:ℝ)^j/Z)*x)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*(((2:ℝ)^j/Z)^(-a))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hfixed : ‖iteratedDeriv i gaussianFixedWindow y‖≤ A i := by
        have hh := SchwartzMap.le_seminorm' ℝ 0 i gaussianFixedSchwartz y
        simp only [pow_zero,one_mul] at hh
        exact hh
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfixed (Nat.cast_nonneg _))
        (hbound _ _ hr y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*(((2:ℝ)^j/Z)^(-a)) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*(((2:ℝ)^j/Z)^(-a)) := by nlinarith [Real.rpow_pos_of_pos hr (-a)]

theorem gaussianDyadicSchwartz_seminorm (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,∀hZ : 0< Z,∀j : ℕ,
      SchwartzMap.seminorm ℝ k n (gaussianDyadicSchwartz Z hZ j)≤ C*(((2:ℝ)^j/Z)^(-a)) := by
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicProfile_derivative_uniform a n
  refine ⟨(2:ℝ)^k*B,by positivity,?_⟩
  intro Z hZ j
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  change |y|^k*‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤ _
  by_cases hy : y∈Set.Icc (1/2:ℝ) 2
  · have habs : |y|≤2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
    calc
      _ ≤ (2:ℝ)^k*(B*(((2:ℝ)^j/Z)^(-a))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs k) (hbound Z hZ j y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gaussianDyadicProfile_derivative_outside Z j n y hy,norm_zero,mul_zero]
    positivity

theorem gaussianDyadicSchwartz_finite_seminorm (a : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,∀hZ : 0< Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*(((2:ℝ)^j/Z)^(-a)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    intro Z hZ j
    simp only [Finset.sup_empty,one_mul]
    change 0≤(((2:ℝ)^j/Z)^(-a))
    exact Real.rpow_nonneg (by positivity) _
  | @insert p S hp ih =>
    obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_seminorm a p.1 p.2
    obtain ⟨C,hC,hrest⟩ := ih
    refine ⟨B+C,by positivity,?_⟩
    intro Z hZ j
    rw [Finset.sup_insert,Seminorm.sup_apply]
    apply max_le
    · exact (hbound Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])
    · exact (hrest Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])

theorem gaussianDyadicSchwartz_two_sided (A : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,∀hZ : 0< Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*min (((2:ℝ)^j/Z)^A) (((2:ℝ)^j/Z)^(-A)) := by
  obtain ⟨B,hB,hlo⟩ := gaussianDyadicSchwartz_finite_seminorm (-A) S
  obtain ⟨C,hC,hhi⟩ := gaussianDyadicSchwartz_finite_seminorm A S
  refine ⟨B+C,by positivity,?_⟩
  intro Z hZ j
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤ B+C)]
  apply le_min
  · have hh := hlo Z hZ j
    rw [neg_neg] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) A])
  · exact (hhi Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-A)])

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbePhysical

lemma gaussianDyadicSchwartz_polynomial_decay (N : ℕ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,∀hZ : 0< Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C/(1+(2:ℝ)^j/Z)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianDyadicSchwartz_finite_seminorm 0 S
  obtain ⟨C,hC,hdecay⟩ := gaussianDyadicSchwartz_finite_seminorm (N:ℝ) S
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro Z hZ j
  let r := (2:ℝ)^j/Z
  have hr : 0< r := div_pos (by positivity) hZ
  have hden : 0<(1+r)^N := pow_pos (by linarith) _
  change _≤(B+C)*(2:ℝ)^N/(1+r)^N
  by_cases hr1 : r≤1
  · have hh := hzero Z hZ j
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay Z hZ j
    change _≤ C*r^(-(N:ℝ)) at hh
    rw [Real.rpow_neg hr.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2*r)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hi : 0≤ C*(r^N)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hp hi
    rw [mul_pow] at hm
    have hn : r^N≠0 := ne_of_gt (pow_pos hr _)
    have he : (C*(r^N)⁻¹)*((2:ℝ)^N*r^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianDyadicSchwartz_summed (s : ℝ) (hs : 0< s) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,∀hZ : 0< Z,
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j))≤ C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_polynomial_decay N S
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound Z hZ j) (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j) := by positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace ProbePhysical

def gaussianFlow (R : ℝ) (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-((Real.log R:ℂ)+z)^2/4)
lemma gaussianFlow_analytic (R : ℝ) (z : ℂ) : AnalyticAt ℂ (gaussianFlow R) z := by
  unfold gaussianFlow
  fun_prop
lemma gaussianFlow_real (R : ℝ) (hR : 0< R) (s : ℝ) :
    gaussianFlow R (s:ℂ)=gaussianMellinProfile (R*Real.exp s) := by
  unfold gaussianFlow gaussianMellinProfile
  rw [←Complex.ofReal_log (mul_pos hR (Real.exp_pos _)).le,Real.log_mul hR.ne' (Real.exp_pos _).ne',Real.log_exp,
    Complex.ofReal_add]

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=> f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=> f (y:ℂ))=(fun y : ℝ=> deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤ L) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→∀y : ℝ,|y|≤ L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤ C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤ c := norm_nonneg _
  have hB : 0< B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤ L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤ B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤ L) (n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→∀y : ℝ,|y|≤ L→
      ‖iteratedDeriv n (fun s : ℝ=> gaussianFlow R (s:ℂ)) y‖≤ C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=> gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=> hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace ProbePhysical

lemma gaussianFlow_real_smooth (R : ℝ) : ContDiff ℝ ∞ (fun s : ℝ=> gaussianFlow R (s:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hf : ContDiffAt ℂ ∞ (gaussianFlow R) (s:ℂ) := (gaussianFlow_analytic R _).contDiffAt
  exact (hf.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt

def gaussianLogWindow (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  (hV.mul_right (f':=fun s : ℝ=> gaussianFlow R (s:ℂ))).toSchwartzMap
    (V.smooth'.mul (gaussianFlow_real_smooth R))
@[simp] lemma gaussianLogWindow_apply (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R s : ℝ) : gaussianLogWindow V hV R s=V s*gaussianFlow R (s:ℂ) := rfl

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤ L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤ L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→∀y : ℝ,|y|≤ L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤ C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=> gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤ A i := apply_nonneg _ _
  have hC : 0≤ C := Finset.sum_nonneg (fun i _=> mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=> V s*gaussianFlow R (s:ℂ)) y‖≤ _
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=> gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=> gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤ A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤ L) (hbox : ∀s,V s≠0→|s|≤ L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤ C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤ L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

/-- Uniform derivative bounds control every Fourier moment of the compact log window. -/
theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤ L) (hbox : ∀s,V s≠0→|s|≤ L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤ C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=> gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0< C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=> add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(JointLogSeparation.coefficientMomentBound 0 C+JointLogSeparation.coefficientMomentBound J C)
  have hD : 0≤ D := mul_nonneg (by positivity)
    (add_nonneg (JointLogSeparation.coefficientMomentBound_nonneg _ _ hC.le)
      (JointLogSeparation.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤ J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤ C := by
    have hbi : B (0,i)+B (p,i)≤ C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=> B (0,i)+B (p,i))
        (fun i _=> add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := JointLogSeparation.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤ D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set JointLogSeparation LocalLogFourier
namespace ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0< R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0< R)
    (hactive : (∏i,W i (y i))≠0→ V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*kernelLogPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i y≠0→|y|≤ M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0< R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*kernelLogPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤ C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤ T := Finset.sum_nonneg (fun i _=> mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := JointLogSeparation.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤ T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact JointLogSeparation.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨CanonicalCubeSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set JointLogSeparation CompletedGauss
namespace ProbePhysical

def gaussianSlotWindow {ι : Type*} (W : ι→ℝ→ℂ) : Option ι→ℝ→ℂ
  | none => fun y=> gaussianAnnulus (Real.exp y)
  | some i => fun y=> W i (Real.exp y)
def gaussianSlotSlope {ι : Type*} : Option ι→ℝ
  | none => 1
  | some _ => -1
def gaussianSlotPoint {ι : Type*} (x : ℝ) (q : ι→ℝ) : Option ι→ℝ
  | none => Real.log x
  | some i => Real.log (q i)

lemma gaussianSlot_argument {ι : Type*} [Fintype ι] (x : ℝ) (hx : 0< x) (q : ι→ℝ) (hq : ∀i,0< q i) :
    Real.exp (∑i : Option ι,gaussianSlotSlope i*gaussianSlotPoint x q i)=x/(∏i,q i) := by
  simp only [Fintype.sum_option,gaussianSlotSlope,gaussianSlotPoint,one_mul,neg_one_mul]
  rw [Real.exp_add,Real.exp_sum,Real.exp_log hx]
  simp_rw [Real.exp_neg,Real.exp_log (hq _)]
  rw [Finset.prod_inv_distrib]
  rfl

lemma logPhase_neg_argument (t y : ℝ) : kernelLogPhase t (-y)=kernelLogPhase (-t) y := by
  unfold kernelLogPhase
  congr 1
  push_cast
  ring

lemma gaussianSlot_product {ι : Type*} [Fintype ι] (W : ι→ℝ→ℂ)
    (x : ℝ) (hx : 0< x) (q : ι→ℝ) (hq : ∀i,0< q i) (t : ℝ) :
    (∏i : Option ι,gaussianSlotWindow W i (gaussianSlotPoint x q i)*
      kernelLogPhase t (gaussianSlotSlope i*gaussianSlotPoint x q i))=
      gaussianAnnulus x*kernelLogPhase t (Real.log x)*
        ∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)) := by
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,gaussianSlotSlope,
    one_mul,neg_one_mul,Real.exp_log hx,logPhase_neg_argument]
  simp_rw [Real.exp_log (hq _)]

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0< x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*kernelLogPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

lemma gaussianAnnulus_log_support (y : ℝ) (hy : gaussianAnnulus (Real.exp y)≠0) :
    |y|≤|Real.log (1/2)|+|Real.log 2|+1 := by
  have hlo : (1/2:ℝ)< Real.exp y := by
    by_contra h; exact hy (gaussianAnnulus_small _ (le_of_not_gt h))
  have hhi : Real.exp y<2 := by
    by_contra h; exact hy (gaussianAnnulus_large _ (le_of_not_gt h))
  have hl : Real.log (1/2)≤ y := by simpa using Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo.le
  have hh : y≤ Real.log 2 := by simpa using Real.log_le_log (Real.exp_pos y) hhi.le
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (1/2)); have := abs_nonneg (Real.log 2); linarith
  · have := le_abs_self (Real.log 2); have := abs_nonneg (Real.log (1/2)); linarith

theorem gaussian_selected_slot_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤ M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
        gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
          ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
            (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤ C*R^(-A)) := by
  let M' : Option ι→ℝ := fun o=> match o with
    | none => |Real.log (1/2)|+|Real.log 2|+1
    | some i => M i
  have hM' : ∀o,0≤ M' o := by intro o; cases o with
    | none => dsimp [M']; positivity
    | some i => exact hM i
  have hW : ∀o y,gaussianSlotWindow W o y≠0→|y|≤ M' o := by
    intro o y
    cases o with
    | none => exact gaussianAnnulus_log_support y
    | some i => exact hwindow i y
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_coupled_family (gaussianSlotWindow W) gaussianSlotSlope M' hM' hW
  refine ⟨V,hV,?_,hbound⟩
  intro R hR x hx q hq
  have hh := hsep R hR (gaussianSlotPoint x q)
  rw [gaussianSlot_argument x hx q hq] at hh
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,Real.exp_log hx] at hh
  simp_rw [Real.exp_log (hq _)] at hh
  rw [show R*(x/∏i,q i)=R*x/(∏i,q i) by ring] at hh
  rw [hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [gaussianFixedWindow_Vstar_twist t x hx]
  simp only [gaussianSlotSlope,one_mul,neg_one_mul,logPhase_neg_argument]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace ProbePhysical

def gaussianJointMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : ℝ :=
  ∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤ gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→ gaussianJointMoment V hV J R≤ C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤ L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

lemma gaussianJointMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) :
    ∃C : ℝ,0< C ∧ ∀R : ℝ,0< R→ gaussianJointMoment V hV J R≤ C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianJointMoment_power_bound V hV J 0
  obtain ⟨C,hC,hdecay⟩ := gaussianJointMoment_power_bound V hV J (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤ C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

/-- Polynomial decay makes the dyadic Gaussian moments summable. -/
theorem gaussianJointMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (s : ℝ) (hs : 0< s) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,0< Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤ C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianJointMoment_polynomial_decay V hV J N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianJointMoment_nonneg V hV J _)
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory JointLogSeparation CompletedGauss
namespace ProbePhysical
open ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma correctedSummand_normTwisted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (T t : ℝ) (I J : Id) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource W t) T I J=
      kernelLogPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T))*
        correctedSummand S D Ψ W T I J := by
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
    CompletedHeight.normTwistedSource
  ring

lemma correctedSummand_fixed_finite (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T : ℝ) (hT : 0< T) :
    (Function.support (fun p : Id×Id=> correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2)).Finite := by
  apply (completedIdealT_finite_support Ψ gaussianFixedWindow gaussianFixedWindow_compact T hT).subset
  intro p hp hz
  exact hp (by simp only [correctedSummand,markedSummand,hz,mul_zero])

lemma gaussian_slot_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ) (x : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ=> kernelLogPhase t x*c*
      (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*b t) := by
  have hh : Integrable (fun t : ℝ=> b t*(kernelLogPhase t x*c*
      ∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))) := by
    apply b.integrable.mul_bdd (c:=‖c‖*∏i,‖W i (q i)‖)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul ((kernelLogPhase_continuous_left x).mul_const c)
      apply continuous_finsetProd
      intro i hi
      exact ((kernelLogPhase_continuous_left (Real.log (q i))).comp continuous_neg).const_mul _
    · apply Filter.Eventually.of_forall
      intro t
      simp only [norm_mul,norm_prod,kernelLogPhase_norm,mul_one,one_mul,le_refl]
  simpa only [mul_comm (b _) _] using hh

lemma gaussian_selected_summand {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0< Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0< q i) (I J : Id) :
    (∏i,W i (q i))*correctedSummand S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) I J=
      ∫t : ℝ,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) I J*
        (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hT : (0:ℝ)<2^j := by positivity
  have hN := div_pos (mul_pos hi (pow_pos hj 3)) hT
  have hprod : 0<∏i,q i := Finset.prod_pos (fun i _=> hq i)
  have hh := hsep ((2:ℝ)^j/Z) (div_pos hT hZ) _ hN q hq
  have he : (2:ℝ)^j/Z*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(∏i,q i)=
      (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i) := by ring
  rw [he] at hh
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianDyadicProfile_Vstar _ _ _ hN]
  let c : ℂ := completedCorrection I J*completedMask S D I J*
    (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J
  calc
    _ = c*(gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
      (∏i,W i (q i))*gaussianMellinProfile
        ((2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i))) := by dsimp [c]; ring
    _ = c*∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t)
      ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp [c]
      ring

lemma correctedSummand_gaussian_factor (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianMellinProfile (((2:ℝ)^j/Z)*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j))*
        correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) I J := by
  rw [gaussianDyadicProfile_factor]
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
  ring

lemma gaussian_selected_completed_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (T : ℝ) (hT : 0< T) :
    Integrable (fun t : ℝ=> correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*b t) := by
  let hf := correctedSummand_fixed_finite S D Ψ T hT
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=> by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  simp_rw [hr,Finset.sum_mul]
  apply integrable_finsetSum
  intro p hp
  simp_rw [correctedSummand_normTwisted]
  exact gaussian_slot_integrable W q b _ _

theorem gaussian_selected_completed {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0< Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0< q i) :
    (∏i,W i (q i))*correctedCompletedT S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∫t : ℝ,correctedCompletedT S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  let hf := correctedSummand_fixed_finite S D Ψ ((2:ℝ)^j) (by positivity)
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hl : correctedCompletedT S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=> by rw [correctedSummand_gaussian_factor,hz p hp,mul_zero])
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=> by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  have hi (p : Id×Id) : Integrable (fun t : ℝ=>
      correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2*
        (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simp_rw [correctedSummand_normTwisted]
    exact gaussian_slot_integrable W q _ _ _
  rw [hl,Finset.mul_sum]
  simp_rw [hr,Finset.sum_mul]
  rw [integral_finsetSum _ (fun p _=> hi p)]
  apply Finset.sum_congr rfl
  intro p hp
  exact gaussian_selected_summand W V hV hsep S D Ψ Z hZ j q hq p.1 p.2

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
