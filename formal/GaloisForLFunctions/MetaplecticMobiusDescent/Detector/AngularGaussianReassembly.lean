import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.AngularLowSeparation

/-!
# Gaussian reassembly of the angular compensated probe

Actual angular rows use the same joint Gaussian density and scale moments. Finite row
support justifies summation, and selected-prime weights retain the conjugate angular target.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open JointLogSeparation
namespace ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem angular_physical_selected_gaussian_reassembly (ℓ : ℕ) {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : ι→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→ Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0< X k) (hY : ∀k∈F,0< Y k) (Z : ℝ) (hZ : 0< Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0< q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*angularMarkedPhysicalProbe ℓ η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (angularSourceTwist ℓ (physicalRowMonoid η C r))
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*kernelLogPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=> by rw [hR k hk r hr,zero_mul])
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=> D p.1) (fun p=> angularSourceTwist ℓ (physicalRowMonoid η C p.2))
    (fun p _=> angularSourceTwist_norm_le ℓ _ (physicalRowMonoid_norm η C p.2)) Z hZ (fun p=> q p.1)
    (fun p hp=> hq p.1 (Finset.mem_product.mp hp).1)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (angularSourceTwist ℓ (physicalRowMonoid η C p.2)) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [angularMarkedPhysicalProbe_eq_gaussian_rows ℓ η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (hX k hk) (hY k hk) (mul_pos hZ (Finset.prod_pos (fun i _=> hq k hk i))),hs k hk]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [A]
        ring
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [A]
      ring

lemma angularCompensatedPhysicalProbe_eq_subsets (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→ Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    angularCompensatedPhysicalProbe ℓ η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            angularCompensationSubsetProbe ℓ η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold angularCompensatedPhysicalProbe
  simp_rw [angularCompensatedTuple_eq_subsets ℓ,Finset.mul_sum]
  exact Finset.sum_comm

theorem angular_compensation_subset_common (ℓ : ℕ) {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0< R→∀x : ℝ,0< x→∀q : SelectedSlot J→ℝ,(∀i,0< q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*kernelLogPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→ Fin K→ O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0< P i) (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*angularCompensationSubsetProbe ℓ η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,angularCompensationSubsetWeight ℓ η W P (p k) J*
        angularCompensationRowTest ℓ η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  have hbase : 0< Z*∏i∈Finset.univ\J,P i := mul_pos hZ (Finset.prod_pos (fun i _=> hP i))
  have hh := angular_physical_selected_gaussian_reassembly ℓ
    (fun i : SelectedSlot J=> W i.val) V hV hsep η C W0 W1 hW0 hW1 F
    (fun k=> angularCompensationSubsetWeight ℓ η W P (p k) J)
    (fun k=> Ideal.span {slotProduct (p k) (Finset.univ\J)})
    (fun k=> X/elementNorm (slotProduct (p k) J)) (fun k=> Y/elementNorm (slotProduct (p k) J))
    (fun k hk=> div_pos hX (slotProduct_norm_pos (p k) (hp k hk) J))
    (fun k hk=> div_pos hY (slotProduct_norm_pos (p k) (hp k hk) J))
    (Z*∏i∈Finset.univ\J,P i) hbase
    (fun k (i : SelectedSlot J)=> elementNorm (p k i.val)/P i.val)
    (fun k hk i=> div_pos (physicalElementNorm_pos _ (hp k hk i.val)) (hP i.val))
  calc
    _ = ∑k∈F,angularCompensationSubsetWeight ℓ η W P (p k) J*
      (∏i : SelectedSlot J,W i.val (elementNorm (p k i.val)/P i.val))*
        angularMarkedPhysicalProbe ℓ η C (Ideal.span {slotProduct (p k) (Finset.univ\J)}) W0 W1
          (X/elementNorm (slotProduct (p k) J)) (Y/elementNorm (slotProduct (p k) J))
          ((Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p k i.val)/P i.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussian_compensation_scale P hP (p k) J Z,gaussian_slot_window_split W (fun i=> elementNorm (p k i)/P i) J]
      unfold angularCompensationSubsetProbe angularCompensationSubsetWeight
      ring
    _ = _ := hh
theorem angularCompensatedPhysicalProbe_common_gaussian (ℓ : ℕ) {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤ M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤ M i) :
    ∃V : Finset (Fin K)→ SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0< s→∃B : ℝ,0< B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0< Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤ B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→ HasCompactSupport W1→
        ∀slotPrimes : Fin K→ Finset O,(∀i a,a∈slotPrimes i→ a≠0)→
        ∀P : Fin K→ℝ,(∀i,0< P i)→∀X Y Z : ℝ,0< X→0< Y→0< Z→
          angularCompensatedPhysicalProbe ℓ η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                angularCompensationSubsetWeight ℓ η W P (fun i=>(p i).val) A*
                  angularCompensationRowTest ℓ η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=> W i.val)
      (fun i : SelectedSlot A=> M i.val) (fun i=> hM i.val) (fun i=> hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=> gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0< B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [angularCompensatedPhysicalProbe_eq_subsets ℓ]
    apply Finset.sum_congr rfl
    intro A hA
    exact angular_compensation_subset_common ℓ A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=> fun i=>(p i).val)
      (fun p _ i=> hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
