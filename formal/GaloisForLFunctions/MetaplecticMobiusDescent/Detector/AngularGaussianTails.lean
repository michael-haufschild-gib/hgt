import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.AngularSelectedWeights
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LowPhysicalInverseBounds

/-!
# Gaussian tails of angular physical rows

Bounded angular coefficients preserve the completed-source majorant. Finite physical row
support transfers its remote-dyad decay with the original physical scale mass.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open JointLogSeparation
open GaloisForLFunctions.FamilyContinuationTheory
namespace ProbePhysical
open ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def angularGaussianPhysicalFamilyIntegral (ℓ : ℕ) {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (angularSourceTwist ℓ (physicalRowMonoid η C r))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

lemma angularGaussianPhysicalFamily_integral_eq (ℓ : ℕ) {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    angularGaussianPhysicalFamilyIntegral ℓ η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=> a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=> D p.1) (fun p=> angularSourceTwist ℓ (physicalRowMonoid η C p.2)) W (fun p=> q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=> by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem angularGaussianPhysicalFamily_remote (ℓ : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0< C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→ HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→ Id,∀X Y : α→ℝ,
      (∀k∈F,0< X k)→(∀k∈F,0< Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0< Z→1≤ A→
      Summable (fun j : ℕ=> if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖angularGaussianPhysicalFamilyIntegral ℓ η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖angularGaussianPhysicalFamilyIntegral ℓ η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=> a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=> D p.1) (fun p=> angularSourceTwist ℓ (physicalRowMonoid η C p.2))
    (fun p _=> angularSourceTwist_norm_le ℓ _ (physicalRowMonoid_norm η C p.2)) W (fun p=> q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [angularGaussianPhysicalFamily_integral_eq ℓ η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh
theorem angularGaussianPhysicalFamily_remote_polynomial (ℓ : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1) (hB0 : 0≤ B0) (hB1 : 0≤ B1) :
    ∃K : ℝ,0< K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→ HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤ B0) → (∀x,‖W1 x‖≤ B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→ Id,∀X Y : α→ℝ,
      (∀k∈F,1≤ X k)→(∀k∈F,1≤ Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0< Z→1≤ A→
      Summable (fun j : ℕ=> if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖angularGaussianPhysicalFamilyIntegral ℓ η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤ A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖angularGaussianPhysicalFamilyIntegral ℓ η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := angularGaussianPhysicalFamily_remote ℓ V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=> lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=> lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

lemma angularCompensationSubsetWeight_norm_le (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) :
    ‖angularCompensationSubsetWeight ℓ η W Y p J‖≤‖compensationSubsetWeight η W Y p J‖ := by
  have he : angularCompensationSubsetWeight ℓ η W Y p J=
      star (elemPsiSix (slotProduct p (Finset.univ\J)))^ℓ*compensationSubsetWeight η W Y p J := by
    rw [angularCompensationSubsetWeight,angularCompensationSubsetCoefficient_eq,
      compensationSubsetWeight]
    ring
  rw [he,norm_mul,norm_pow,norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one _))

lemma angular_compensation_scale_mass_bound (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>angularCompensationSubsetWeight ℓ η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  apply le_trans _ (compensation_scale_mass_bound η C ell hell hsum b Z hZ T hT hnorm J W hW)
  unfold gaussianPhysicalScaleMass
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (angularCompensationSubsetWeight_norm_le ℓ η W _ _ J)
      (Finset.prod_nonneg (fun _ _=>norm_nonneg _)))
  unfold lowPhysicalScale elementNorm
  positivity

end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
