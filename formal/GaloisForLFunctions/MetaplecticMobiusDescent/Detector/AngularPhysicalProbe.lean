import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularFiniteReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PhysicalRows

/-!
# The physical cubic probe with a direct angular source

Angular twisting changes the multiplicative completed-source coefficient. Gaussian
Mellin inversion identifies its spectral definition with the actual corrected completed
sum, preserving the physical scale and the free Fourier frequency.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified CompletedGauss CanonicalRowCompletion
open SchwartzPlanePoisson GaloisForLFunctions.FamilyContinuationTheory
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma angularSourceTwist_norm_le (ℓ : ℕ) (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) :
    ∀n,‖angularSourceTwist ℓ Ψ n‖≤1 := by
  intro n
  rw [angularSourceTwist_apply,norm_mul,norm_pow]
  exact mul_le_one₀ (hΨ n) (by positivity)
    (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one n))

def angularMarkedPhysicalProbe (ℓ : ℕ) (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryIdealGenerator s.val
      let ha := supported_primaryIdealGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (angularSourceTwist ℓ (rowCoefficient η C.Xi a has m)) t)
    else 0

def angularPhysicalProbe (ℓ : ℕ) (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  angularMarkedPhysicalProbe ℓ η C 1 W₀ W₁ X Y Z

/-- Compensation uses the same angular target coefficient as the completed source. -/
def angularCompensatedTuple (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W₀ W₁ : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (angularSourceTwist ℓ (targetMonoid η))
    (fun a=>angularMarkedPhysicalProbe ℓ η C (Ideal.span {a}) W₀ W₁) X Y Z

def angularCompensatedPhysicalProbe (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W₀ W₁ : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (slotWindow : Fin K→ℝ→ℂ) (slotScale : Fin K→ℝ) (X Y Z : ℝ) : ℂ :=
  ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
    (∏i,slotWindow i (elementNorm (p i).val/slotScale i))*
      angularCompensatedTuple ℓ η C W₀ W₁ (fun i=>(p i).val) X Y Z

theorem angularMarkedPhysicalProbe_eq_gaussian (ℓ : ℕ) (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (X Y Z : ℝ) (hZ : 0< Z) :
    angularMarkedPhysicalProbe ℓ η C D W0 W1 X Y Z=
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
            correctedCompletedT C.excluded D (angularSourceTwist ℓ (rowCoefficient η C.Xi a has m))
              gaussianCompletedProfile Z
        else 0 := by
  unfold angularMarkedPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    apply tsum_congr
    intro m
    rw [spectralRow_eq_gaussianCompleted _ _ _
      (angularSourceTwist_norm_le ℓ _
        (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m)) 4 (by norm_num) Z hZ]
  · rfl

theorem angularMarkedPhysicalProbe_eq_rows (ℓ : ℕ) (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) :
    angularMarkedPhysicalProbe ℓ η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (angularSourceTwist ℓ (physicalRowMonoid η C r)) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=> verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (angularSourceTwist ℓ (physicalRowMonoid η C r)) t))
  rw [hf.tsum_prod]
  unfold angularMarkedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [if_pos hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [if_neg hc,zero_mul,mul_zero,tsum_zero]

theorem angularMarkedPhysicalProbe_eq_gaussian_rows (ℓ : ℕ) (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    angularMarkedPhysicalProbe ℓ η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (angularSourceTwist ℓ (physicalRowMonoid η C r)) gaussianCompletedProfile Z := by
  rw [angularMarkedPhysicalProbe_eq_rows ℓ η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (angularSourceTwist_norm_le ℓ _ (physicalRowMonoid_norm η C r)) 4 (by norm_num) Z hZ]

end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
