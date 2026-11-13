/-
Fourier separation of the detector adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorRowCounts

/-!
# Fourier separation of the detector

Inverse and ratio profiles of the dyadic bridge, phase polynomials and coefficients of the
detector Fourier series; finite pair separation, bounded frequencies and frequency tail orders.
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


namespace HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*kernelLogPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (kernelLogPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*kernelLogPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, kernelLogPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*kernelLogPhase t x*kernelLogPhase t y := by
  rw [JointLogSeparation.schwartz_phase_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [kernelLogPhase_add]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*kernelLogPhase t (x i))*(b j*kernelLogPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*kernelLogPhase t (x i))*(b j*kernelLogPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end HeckeDetectorFourier

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end
end HeckeDetectorFourier

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma normalization (D : ℝ) (hD : 0< D) (s : ℂ) :
    (D : ℂ)^((1/2 : ℂ)-s)*(D : ℂ)^(-(1/2 : ℂ))=(D : ℂ)^(-s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 1
  ring

theorem phase_sum_eq_polynomial (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0< D) (s : ℂ) (t : ℝ) (S : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    (∑ J∈S, coefficient χ inverse J*(J.absNorm : ℂ)^(-s)*
      W ((J.absNorm : ℝ)/D)*kernelLogPhase t (Real.log ((J.absNorm : ℝ)/D))) =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ inverse W D s.re (2*Real.pi*t-s.im) := by
  rw [polynomial_eq_finite χ inverse W D s.re (2*Real.pi*t-s.im) S hcover,
    ← mul_assoc, normalization D hD s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hnorm : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS J hJ))
  have hp := norm_phase (J.absNorm : ℝ) D hnorm hD s t
  simp only [Complex.ofReal_natCast] at hp
  calc
    _ = coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
        ((J.absNorm : ℂ)^(-s)*kernelLogPhase t (Real.log ((J.absNorm : ℝ)/D))) := by ring
    _ = _ := by rw [hp]; ring

def inverseProfile (V W : ℝ→ℂ) (Dstar D : ℝ) (x : ℝ) : ℂ :=
  V (D*x/Dstar)*W x

lemma inverseProfile_at_norm (V W : ℝ→ℂ) (Dstar D x : ℝ) (hD : 0< D) :
    inverseProfile V W Dstar D (x/D)=V (x/Dstar)*W (x/D) := by
  unfold inverseProfile
  congr 2
  field_simp

lemma weighted_eq (χ : Character) (s : ℂ) (J : Ideal O) (hJ : J≠0) :
    IdealEuler.weighted (idealCoeff χ) s J=idealCoeff χ J*(J.absNorm : ℂ)^(-s) := by
  simp only [IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, fullIdealWeight, if_neg hJ]

theorem plain_phase_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (hD : 0< D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (plainCoefficient χ W D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ false W D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ false W D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [plainCoefficient, weighted_eq χ s J (hS J hJ)]
  rfl

theorem inverse_phase_eq (χ : Character) (V W : ℝ→ℂ) (Dstar D : ℝ) (hD : 0< D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (inverseCoefficient χ V W Dstar D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*
        polynomial χ true (inverseProfile V W Dstar D) D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ true (inverseProfile V W Dstar D) D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [inverseCoefficient, weighted_eq χ s J (hS J hJ), inverseProfile_at_norm V W Dstar D _ hD]
  simp only [coefficient, ite_true]
  ring

lemma normalization_norm (D : ℝ) (hD : 0< D) (s : ℂ) :
    ‖(D : ℂ)^((1/2 : ℂ)-s)‖=D^(1/2-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  congr 1
  simp

theorem pair_phase_norm (χ : Character) (V W₁ W₂ : ℝ→ℂ) (Dstar D N : ℝ)
    (hD : 0< D) (hN : 0< N) (s : ℂ) (t : ℝ) (S R : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0) (hR : ∀ J∈R, J≠0)
    (hcoverS : ∀ J : Ideal O, J≠0 → inverseProfile V W₁ Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (hcoverR : ∀ J : Ideal O, J≠0 → W₂ ((J.absNorm : ℝ)/N)≠0 → J∈R) :
    ‖phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
        (fun J => Real.log ((J.absNorm : ℝ)/D)) t‖ *
      ‖phasePolynomial R (plainCoefficient χ W₂ N s)
        (fun J => Real.log ((J.absNorm : ℝ)/N)) t‖ =
      D^(1/2-s.re)*N^(1/2-s.re)*
        (‖polynomial χ true (inverseProfile V W₁ Dstar D) D s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false W₂ N s.re (2*Real.pi*t-s.im)‖) := by
  rw [inverse_phase_eq χ V W₁ Dstar D hD s t S hS hcoverS,
    plain_phase_eq χ W₂ N hN s t R hR hcoverR,
    norm_mul, norm_mul, normalization_norm D hD s, normalization_norm N hN s]
  ring

end HeckeDetectorDyadicBridge

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := JointLogSeparation.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (JointLogSeparation.schwartzDerivativeDecayConstant F K K)
    (JointLogSeparation.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using JointLogSeparation.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const
    (hF.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j)
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end HeckeDetectorProfiles

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  let Ωs : SchwartzMap ℝ ℂ := hΩc.toSchwartzMap hΩ
  have hΩs : (Ωs : ℝ → ℂ) = Ω := rfl
  let CΩ := JointLogSeparation.profileSourceBound Ωs K
  have hCΩ : 0 ≤ CΩ := JointLogSeparation.profileSourceBound_nonneg Ωs K
  have hbΩ (i : ℕ) (hi : i ≤ K) (y : ℝ) :
      ‖iteratedFDeriv ℝ i Ω y‖ ≤ CΩ := by
    have hs : ‖iteratedFDeriv ℝ i Ω y‖ ≤ SchwartzMap.seminorm ℝ 0 i Ωs := by
      simpa only [pow_zero, one_mul, hΩs] using (SchwartzMap.le_seminorm ℝ 0 i Ωs y)
    exact hs.trans ((le_add_of_nonneg_right (apply_nonneg _ _)).trans
      (JointLogSeparation.source_le_profileSourceBound Ωs K i hi))
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end HeckeDetectorProfiles

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(JointLogSeparation.coefficientMomentBound 0 C'+
    JointLogSeparation.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (JointLogSeparation.coefficientMomentBound_nonneg 0 C' hC')
      (JointLogSeparation.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := JointLogSeparation.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := JointLogSeparation.schwartz_fourier_one_plus_integrable g J
  have hiN := JointLogSeparation.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C/R^N := by
  obtain ⟨C,hC,hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J+N)
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
    (hb A B D hA hB hD)

theorem logSource_product_inversion (Ω V T : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B D x y : ℝ) :
    logSourceFun Ω V T A B D (x+y) =
      ∫ t : ℝ, kernelLogPhase t x * kernelLogPhase t y *
        (𝓕 (logSource Ω V T hΩc hΩ hV hT A B D)) t := by
  have hh := JointLogSeparation.schwartz_phase_inversion
    (logSource Ω V T hΩc hΩ hV hT A B D) (x+y)
  change logSourceFun Ω V T A B D (x+y) = _ at hh
  simpa only [kernelLogPhase_add] using hh

end
end HeckeDetectorFourier

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace HeckeDetectorDyadicProfiles
def ratioProfile (V W : ℝ→ℂ) (R x : ℝ) : ℂ := V (R*x)*W x

def logFamily (V W : ℝ→ℂ) (p : ℝ×ℝ) (y : ℝ) : ℂ :=
  Real.exp (-p.2*y) • ratioProfile V W p.1 (Real.exp (-y))

lemma logFamily_smooth (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily V W)) := by
  unfold Function.uncurry logFamily ratioProfile
  have he : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => Real.exp (-p.1.2*p.2)) := by fun_prop
  have hv : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => V (p.1.1*Real.exp (-p.2))) :=
    hV.comp (by fun_prop)
  have hw : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => W (Real.exp (-p.2))) :=
    hW.comp (by fun_prop)
  exact he.smul (hv.mul hw)

lemma ratioProfile_support (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (ratioProfile V W R)⊆Function.support W := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).2

lemma logFamily_support (V W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily V W p)⊆Icc (-Real.log b) (-Real.log a) := by
  exact mellinLogFamily_support (ratioProfile V W p.1) a b ha
    ((ratioProfile_support V W p.1).trans hW) p.2

theorem ratioProfile_mellin_bound (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0< a) (hWs : Function.support W⊆Icc a b)
    (Rmax lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ R∈Icc 0 Rmax, ∀ σ∈Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (ratioProfile V W R) ((σ : ℂ)+t*Complex.I)‖≤ C := by
  obtain ⟨C,hC,hb⟩ := CompactProfileFamily.compact_family_fourier_weighted_bound
    (logFamily V W) (logFamily_smooth V W hV hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support V W a b ha hWs)
    (Icc 0 Rmax ×ˢ Icc lo hi) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro R hR σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (mellinLogFamily (ratioProfile V W R) σ) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j * ((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily V W (R,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow, mul_assoc]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (R,σ) ⟨hR,hσ⟩ _) (by positivity)

lemma inverseProfile_eq_ratio (V W : ℝ→ℂ) (Dstar D : ℝ) :
    HeckeDetectorDyadicBridge.inverseProfile V W Dstar D=ratioProfile V W (D/Dstar) := by
  funext x
  unfold HeckeDetectorDyadicBridge.inverseProfile ratioProfile
  congr 2
  ring

theorem exists_profile_bounds (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (lo hi : ℝ) :
    ∃ C : ℕ→ℝ, (∀ j, 0< C j) ∧
      (∀ j : ℕ, ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin W ((σ : ℂ)+t*Complex.I)‖≤ C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0< Dstar → 0≤ D → D≤4*Dstar →
        ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile V W Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤ C j) := by
  choose Cp hCp hbP using fun j => compact_source_mellin_strip_decay W a b ha hWs hW lo hi j
  choose Ci hCi hbI using fun j => ratioProfile_mellin_bound V W hV hW a b ha hWs 4 lo hi j
  refine ⟨fun j => Cp j+Ci j,fun j => add_pos (hCp j) (hCi j),?_,?_⟩
  · intro j σ hσ t
    exact (hbP j σ hσ t).trans (le_add_of_nonneg_right (hCi j).le)
  · intro j Dstar D hDs hD hratio σ hσ t
    rw [inverseProfile_eq_ratio]
    exact (hbI j (D/Dstar) ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hratio⟩ σ hσ t).trans
      (le_add_of_nonneg_left (hCp j).le)

end HeckeDetectorDyadicProfiles

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
open Set
namespace HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

theorem actual_profile_bounds :
    ∃ C : ℕ→ℝ, (∀ j, 0< C j) ∧
      (∀ j : ℕ, ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin positiveAnnular ((σ : ℂ)+t*Complex.I)‖≤ C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0< Dstar → 0≤ D → D≤4*Dstar →
        ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤ C j) :=
  exists_profile_bounds cutoff positiveAnnular (cutoff.smooth ⊤) positiveAnnular_smooth
    (1/4) (9/4) (by norm_num) positiveAnnular_support (-2) 2

end HeckeDetectorDyadicProfiles

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical ContDiff
open Set
namespace HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

theorem simultaneous_upper (R dmax τ ε e κ η : ℝ)
    (hR : 0≤ R) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    ∃ C : ℝ, 0< C ∧ ∀ Z d : ℝ, 1≤ Z → 0≤ d → d≤ dmax → 2< Z^τ →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤ a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))< a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤ Z^d → 0< Dstar →
        0≤ r → r≤ R → 0≤ m → m≤ R → (Z^d)^r≤4*Dstar →
        51/100≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        ‖polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq‖^2≤ C*(Z^d)^((2*a-1)*r+ε) ∧
        ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq‖^2≤
          C*(Z^d)^((2*a-1)*min m (1-m)+ε) := by
  obtain ⟨Cp,hCp,hplain,hinverse⟩ := actual_profile_bounds
  obtain ⟨n,C,hC,hbound⟩ := source_dyadic_bounds R dmax τ ε e κ η
    hR hdmax hτ hε he he' hκ hκ' hη hbudget Cp (fun k => (hCp k).le)
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight
  have hU : 1≤ Z^d := Real.one_le_rpow hZ hd
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (by linarith) _
  have hstrip : Icc (1-a-6*e-σ) (2-σ)⊆Icc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hInv := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j true
    (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
    (1/4) (9/4) (by norm_num) (inverse_profile_support Dstar ((Z^d)^r))
    (inverse_profile_smooth Dstar ((Z^d)^r)) r σ freq hQ hr hrR hfreq hheight
    (fun x hx t => hinverse 2 Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
    (fun x hx t => hinverse (n+2) Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
  have hPlain := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j false
    positiveAnnular (1/4) (9/4) (by norm_num) positiveAnnular_support positiveAnnular_smooth
    m σ freq hQ hm hmR hfreq hheight
    (fun x hx t => hplain 2 x (hstrip hx) t)
    (fun x hx t => hplain (n+2) x (hstrip hx) t)
  exact ⟨hInv.1,hPlain.2⟩

end HeckeDetectorDyadicActual

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p< dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0< Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0< dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d → A≤ Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ< dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d →
      ∀ i : ℕ, i≤ I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ< dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d →
      ∀ i : ℕ, i≤ I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤ Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤ Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0< dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤ d → d≤ dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤ Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0< Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤ Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end HeckeDetectorDyadicGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeDetectorBudget
open HeckeDetectorPartition

lemma source_length_bound (U : ℝ) (hU : 2 ≤ U) :
    ((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ) ≤ 25*Real.logb 2 U := by
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^21 := one_le_pow₀ (by linarith) (n := 21)
  have hc : (1 : ℝ) ≤ ⌈2*U^21⌉₊ := le_trans (by linarith) (Nat.le_ceil (2*U^21))
  have hcu : (⌈2*U^21⌉₊ : ℝ) ≤ 4*U^21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*U^21 by positivity)
    linarith
  have hl : 1 ≤ Real.logb 2 U := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by norm_num : (0 : ℝ)<2) hU
    simpa using h
  have hb := length_bound (⌈2*U^21⌉₊ : ℝ) hc
  have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by linarith : (0 : ℝ)<⌈2*U^21⌉₊) hcu
  have he : Real.logb 2 (4*U^21) = 2+21*Real.logb 2 U := by
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow]
    have hfour : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow]
      norm_num
    rw [hfour]
    norm_num
  rw [he] at hm
  push_cast
  linarith

lemma source_pair_count_bound (U : ℝ) (hU : 2 ≤ U) :
    (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)^2) ≤ 625*(Real.logb 2 U)^2 := by
  have h := source_length_bound U hU
  have hl : 0 ≤ Real.logb 2 U := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [sq_nonneg (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)-25*Real.logb 2 U)]

end HeckeDetectorBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma frequency_interval_compl (R : ℝ) :
    (Set.Icc (-R) R)ᶜ = {t : ℝ | R < ‖t‖} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, Real.norm_eq_abs,
    ← abs_le, not_le]

private lemma exists_interval_norm_product (f h : ℝ → ℂ) (hf : Continuous f)
    (hh : Integrable h) (hprod : Integrable (fun u => h u * f u))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R, h u * f u‖ ≤ (∫ u : ℝ, ‖h u‖) * ‖f t‖ := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.norm.continuousOn
  refine ⟨t, by simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using ht, ?_⟩
  have hb : Integrable (fun u => ‖h u‖ * ‖f t‖) := hh.norm.mul_const _
  calc
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u * f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u‖ * ‖f t‖ := by
      apply setIntegral_mono_on hprod.norm.integrableOn hb.integrableOn measurableSet_Icc
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax hu) (norm_nonneg _)
    _ ≤ ∫ u : ℝ, ‖h u‖ * ‖f t‖ :=
      setIntegral_le_integral hb (Filter.Eventually.of_forall (by intro u; positivity))
    _ = _ := integral_mul_const _ _

theorem exists_interval_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u‖ ≤
        (∫ u : ℝ, ‖(𝓕 g) u‖)*
          ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  have hf : Continuous (fun u => phasePolynomial S a x u * phasePolynomial T b y u) :=
    (phasePolynomial_continuous S a x).mul (phasePolynomial_continuous T b y)
  have hi : Integrable (fun u => (𝓕 g) u *
      (phasePolynomial S a x u * phasePolynomial T b y u)) := by
    simpa only [mul_assoc] using separated_pair_integrable S T a b x y g
  obtain ⟨t, ht, hb⟩ := exists_interval_norm_product
    (fun u => phasePolynomial S a x u * phasePolynomial T b y u)
    (fun u => (𝓕 g) u) hf (𝓕 g).integrable hi R hR
  exact ⟨t, ht, by simpa only [mul_assoc] using hb⟩

private theorem integral_sub_interval_norm_le (f w : ℝ → ℂ) (E R : ℝ)
    (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ u, ‖f u‖ ≤ E * ‖w u‖) :
    ‖(∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u)‖ ≤
      E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := by
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc hf
  have heq : (∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u) =
      ∫ u : ℝ in {u | R < ‖u‖}, f u := by
    rw [← hsplit, frequency_interval_compl]
    abel
  rw [heq]
  have hm : MeasurableSet {u : ℝ | R < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, E * ‖w u‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun u _ => hbound u)
    _ = _ := integral_const_mul _ _

private theorem separated_pair_norm_le {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (z : ℂ) (u : ℝ) :
    ‖z * phasePolynomial S a x u * phasePolynomial T b y u‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) * ‖z‖ := by
  rw [mul_assoc, norm_mul, norm_mul, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact mul_le_mul (phasePolynomial_norm S a x u) (phasePolynomial_norm T b y u)
    (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem schwartz_tail_le (g : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 g) u‖) ≤
      (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) / R^N := by
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa only [pow_zero, one_mul, Nat.zero_add, mul_comm] using
    schwartz_weighted_tail g 0 N R hR

private theorem separated_pair_tail_of_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (w : ℝ → ℂ) (R M : ℝ) (N : ℕ)
    (hi : Integrable (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u))
    (hw : Integrable w) (hbound : (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) ≤ M / R^N) :
    ‖(∫ u : ℝ, w u * phasePolynomial S a x u * phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        w u * phasePolynomial S a x u * phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) / R^N * M := by
  let E := (∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)
  have hE : 0 ≤ E := mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have htail := integral_sub_interval_norm_le
    (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u)
    w E R hi hw (fun u => separated_pair_norm_le S T a b x y (w u) u)
  calc
    _ ≤ E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := htail
    _ ≤ E * (M / R^N) := mul_le_mul_of_nonneg_left hbound hE
    _ = _ := by rw [div_mul_eq_mul_div, mul_div_assoc]

theorem separated_pair_tail {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ‖(∫ u : ℝ, (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) := by
  exact separated_pair_tail_of_bound S T a b x y (fun u : ℝ => (𝓕 g : SchwartzMap ℝ ℂ) u)
    R (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) N
    (separated_pair_integrable S T a b x y g) (𝓕 g).integrable
    (schwartz_tail_le g R hR N)

theorem exists_bounded_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) +
      (∫ u : ℝ, ‖(𝓕 g) u‖)*
        ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  obtain ⟨t,ht,hb⟩ := exists_interval_frequency S T a b x y g R hR.le
  refine ⟨t,ht,?_⟩
  rw [finite_pair_separation]
  have htail := separated_pair_tail S T a b x y g R hR N
  exact (norm_le_norm_sub_add _ _).trans (add_le_add htail hb)

end
end HeckeDetectorFourier

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Topology
open Filter
namespace HeckeDetectorFrequency

lemma logb_square_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun U : ℝ => (Real.logb 2 U)^2/U^a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have h' := h.const_mul ((Real.log 2)^2)⁻¹
  convert h' using 1
  · ext U
    rw [Real.rpow_two,Real.logb]
    ring
  · ring_nf

theorem exists_frequency_tail_order (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ C : ℝ, ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n) ≤ 1/4 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (43/τ)
  have he : 0 < τ*(n : ℝ)-42 := by
    have hh := (div_lt_iff₀ hτ).mp hn
    nlinarith
  refine ⟨n,?_⟩
  intro C
  have ht := (logb_square_div_rpow_tendsto (τ*(n : ℝ)-42) he).const_mul (625*67108864*C)
  have ht' : Tendsto
      (fun U : ℝ => (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun U : ℝ => (625*67108864*C)*
      ((Real.logb 2 U)^2/U^(τ*(n : ℝ)-42))) atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    rw [Real.rpow_sub hU,Real.rpow_mul_natCast hU.le,
      show (42 : ℝ)=((42 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    field_simp
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht').2 (1/4) (by norm_num))
  exact ⟨U₀,fun U hU hU1 => (hU₀ U hU).le⟩

end HeckeDetectorFrequency

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
