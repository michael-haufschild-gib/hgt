import GaloisForLFunctions.RHTower.SoninCorrectionResponseRecovery

/-!
# Faithful separation of the complete Sonin time-band source

The actual anticommutator AB+BA recovers each original time-band channel by
a bounded right factor. Actual invertibility follows from the strict
alternating-block bound, not from an added source-admission hypothesis.
The resulting bounded maps identify full complex response summability and
cofinal nuclear admission with those of all four original source channels.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap Filter Topology
open GaloisForLFunctions.HTGeometry
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)
local notation "S1" => SchattenOneOperator SoninL2
local notation "S4" => ((S1 × S1) × (S1 × S1))


private theorem one_sub_reverse_unit {M : Type*} [Ring M] (X Y : M)
    (h : IsUnit (1-Y*X)) : IsUnit (1-X*Y) := by
  let W := Ring.inverse (1-Y*X)
  have hL : (1-Y*X)*W=1 := Ring.mul_inverse_cancel _ h
  have hR : W*(1-Y*X)=1 := Ring.inverse_mul_cancel _ h
  refine ⟨⟨1-X*Y,1+X*W*Y,?_,?_⟩,rfl⟩
  · calc
      _ = 1+X*((1-Y*X)*W-1)*Y := by noncomm_ring
      _ = 1 := by rw [hL]; simp
  · calc
      _ = 1+X*(W*(1-Y*X)-1)*Y := by noncomm_ring
      _ = 1 := by rw [hR]; simp

/-- The literal physical/Fourier product has an invertible one-minus operator. -/
theorem isUnit_one_sub_centralPhysicalFourier (a : ℝ) (ha : 0 < a) :
    IsUnit (1-(centralPhysicalForbidden a).starProjection *
      (centralFourierForbidden a).starProjection) := by
  let A := (centralPhysicalForbidden a).starProjection
  let B := (centralFourierForbidden a).starProjection
  have hB : B*B=B := (centralFourierForbidden a).isIdempotentElem_starProjection
  have h : IsUnit (1-B*(A*B)) := by
    exact isUnit_one_sub_of_norm_lt_one
      (by simpa only [A,B,mul_assoc,soninAlternatingBlock] using
        norm_centralSoninAlternatingBlock_lt_one a ha)
  have h' := one_sub_reverse_unit (A*B) B h
  simpa only [mul_assoc,hB] using h'

/-- The reversed literal product has an invertible one-minus operator as well. -/
theorem isUnit_one_sub_centralFourierPhysical (a : ℝ) (ha : 0 < a) :
    IsUnit (1-(centralFourierForbidden a).starProjection *
      (centralPhysicalForbidden a).starProjection) :=
  one_sub_reverse_unit _ _ (isUnit_one_sub_centralPhysicalFourier a ha)

/-- Fixed bounded right factor recovering the physical-first channel. -/
def soninPhysicalFourierRecoveryFactor (a : ℝ) : Op :=
  (1-(centralPhysicalForbidden a).starProjection) *
    (centralFourierForbidden a).starProjection *
      Ring.inverse (1-(centralPhysicalForbidden a).starProjection *
        (centralFourierForbidden a).starProjection)

/-- Fixed bounded right factor recovering the Fourier-first channel. -/
def soninFourierPhysicalRecoveryFactor (a : ℝ) : Op :=
  (1-(centralFourierForbidden a).starProjection) *
    (centralPhysicalForbidden a).starProjection *
      Ring.inverse (1-(centralFourierForbidden a).starProjection *
        (centralPhysicalForbidden a).starProjection)

private theorem recover_product {M : Type*} [Ring M] (A B : M)
    (hA : A*A=A) (hB : B*B=B) (hU : IsUnit (1-A*B)) :
    (A*B+B*A)*((1-A)*B*Ring.inverse (1-A*B)) = A*B := by
  calc
    _ = ((A*B+B*A)*((1-A)*B))*Ring.inverse (1-A*B) := by noncomm_ring
    _ = (A*B*(1-A*B))*Ring.inverse (1-A*B) := by
      congr 1
      have hAAB : A*(A*B)=A*B := by rw [← mul_assoc,hA]
      noncomm_ring [hA,hB,hAAB]
    _ = _ := by rw [mul_assoc,Ring.mul_inverse_cancel _ hU,mul_one]

/-- No source-side cancellation between the two actual time-band channels
can hide the physical-first block: it is recovered by a bounded right factor. -/
theorem centralPhysicalFourier_eq_anticommutator_rightFactor (a : ℝ) (ha : 0 < a) :
    ((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
      (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection) *
        soninPhysicalFourierRecoveryFactor a =
      (centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection :=
  recover_product _ _ (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isUnit_one_sub_centralPhysicalFourier a ha)

/-- The same unchanged anticommutator also recovers its Fourier-first block. -/
theorem centralFourierPhysical_eq_anticommutator_rightFactor (a : ℝ) (ha : 0 < a) :
    ((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
      (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection) *
        soninFourierPhysicalRecoveryFactor a =
      (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection := by
  simpa only [soninFourierPhysicalRecoveryFactor,add_comm] using
    recover_product _ _ (centralFourierForbidden a).isIdempotentElem_starProjection
      (centralPhysicalForbidden a).isIdempotentElem_starProjection
      (isUnit_one_sub_centralFourierPhysical a ha)

private def rightAction (R : Op) : S1 →L[ℂ] S1 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨T.val ∘L R, memSchattenClass_one_comp_right T.property R⟩
      map_add' := by intro S T; apply SchattenOneOperator.ext; rfl
      map_smul' := by intro c T; apply SchattenOneOperator.ext; rfl }
    ‖R‖ (fun T => by
      change traceNorm SoninL2 (T.val ∘L R) ≤ ‖R‖ * traceNorm SoninL2 T.val
      simpa only [mul_comm] using traceNorm_comp_right_le T.summable R)

/-- Bounded separation of both original source directions into their two time-band channels. -/
def soninTimeBandChannelSplit (a : ℝ) : (S1 × S1) →L[ℂ] S4 :=
  let T := (rightAction (soninPhysicalFourierRecoveryFactor a)).prod
    (rightAction (soninFourierPhysicalRecoveryFactor a))
  T.prodMap T

/-- The original source channels are recombined by ordinary addition. -/
def soninTimeBandChannelMerge : S4 →L[ℂ] (S1 × S1) :=
  let T := ContinuousLinearMap.fst ℂ S1 S1 + ContinuousLinearMap.snd ℂ S1 S1
  T.prodMap T

/-- The four actual time-band channels of the complete complex source pair,
packaged in genuine Schatten-one. The coe identity identifies every channel. -/
def soninNuclearSeparatedTimeBandSourcePair (a : ℝ) (ha : 0 < a) (D : Op) : S4 :=
  soninTimeBandChannelSplit a (soninNuclearTimeBandSourcePair a ha D)

/-- Separation retains DAB, DBA, D*AB and D*BA exactly, for every bounded complex source. -/
theorem soninNuclearSeparatedTimeBandSourcePair_coe (a : ℝ) (ha : 0 < a) (D : Op) :
    let A := (centralPhysicalForbidden a).starProjection
    let B := (centralFourierForbidden a).starProjection
    let S := soninNuclearSeparatedTimeBandSourcePair a ha D
    ((S.1.1.val,S.1.2.val),(S.2.1.val,S.2.2.val)) =
      ((D*(A*B),D*(B*A)),(adjoint D*(A*B),adjoint D*(B*A))) := by
  dsimp only
  have h := soninNuclearTimeBandSourcePair_coe a ha D
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have hf (X : Op) :
      (X*((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection)) *
        soninPhysicalFourierRecoveryFactor a =
      X*((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection) := by
    rw [mul_assoc,centralPhysicalFourier_eq_anticommutator_rightFactor a ha]
  have hg (X : Op) :
      (X*((centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection)) *
        soninFourierPhysicalRecoveryFactor a =
      X*((centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection) := by
    rw [mul_assoc,centralFourierPhysical_eq_anticommutator_rightFactor a ha]
  change (((soninNuclearTimeBandSourcePair a ha D).1.val*soninPhysicalFourierRecoveryFactor a,
    (soninNuclearTimeBandSourcePair a ha D).1.val*soninFourierPhysicalRecoveryFactor a),
    ((soninNuclearTimeBandSourcePair a ha D).2.val*soninPhysicalFourierRecoveryFactor a,
    (soninNuclearTimeBandSourcePair a ha D).2.val*soninFourierPhysicalRecoveryFactor a)) = _
  rw [h1,h2,hf,hg,hf,hg]

/-- Recombination recovers the entire literal unsplit source pair. -/
theorem soninTimeBandChannelMerge_apply (a : ℝ) (ha : 0 < a) (D : Op) :
    soninTimeBandChannelMerge (soninNuclearSeparatedTimeBandSourcePair a ha D) =
      soninNuclearTimeBandSourcePair a ha D := by
  have hs := soninNuclearSeparatedTimeBandSourcePair_coe a ha D
  have ht := soninNuclearTimeBandSourcePair_coe a ha D
  dsimp only at hs ht
  apply Prod.ext <;> apply SchattenOneOperator.ext
  · have h1 := congrArg (fun p : (Op × Op) × (Op × Op) => p.1.1) hs
    have h2 := congrArg (fun p : (Op × Op) × (Op × Op) => p.1.2) hs
    have h3 := congrArg Prod.fst ht
    dsimp only at h1 h2 h3
    change (soninNuclearSeparatedTimeBandSourcePair a ha D).1.1.val +
      (soninNuclearSeparatedTimeBandSourcePair a ha D).1.2.val = _
    rw [h1,h2,h3,mul_add]
  · have h1 := congrArg (fun p : (Op × Op) × (Op × Op) => p.2.1) hs
    have h2 := congrArg (fun p : (Op × Op) × (Op × Op) => p.2.2) hs
    have h3 := congrArg Prod.snd ht
    dsimp only at h1 h2 h3
    change (soninNuclearSeparatedTimeBandSourcePair a ha D).2.1.val +
      (soninNuclearSeparatedTimeBandSourcePair a ha D).2.2.val = _
    rw [h1,h2,h3,mul_add]

/-- Full complex response summability is equivalent to simultaneous admission
of all four original time-band source channels. No cancellation premise is added. -/
theorem summable_soninNuclearResponsePair_iff_separatedTimeBand {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) :
    Summable (fun i => soninNuclearResponsePair a ha (D i)) ↔
      Summable (fun i => soninNuclearSeparatedTimeBandSourcePair a ha (D i)) := by
  rw [summable_soninNuclearResponsePair_iff_timeBand]
  constructor
  · intro h
    exact (soninTimeBandChannelSplit a).summable h
  · intro h
    simpa only [soninTimeBandChannelMerge_apply] using soninTimeBandChannelMerge.summable h

/-- The same faithful separation preserves every cofinal nuclear limit. -/
theorem tendsto_soninNuclearResponsePair_iff_separatedTimeBand {ι : Type*}
    (a : ℝ) (ha : 0 < a) (D : ι → Op) (l : Filter ι) :
    (∃ T : S1 × S1, Tendsto (fun i => soninNuclearResponsePair a ha (D i)) l (nhds T)) ↔
      (∃ T : S4, Tendsto (fun i => soninNuclearSeparatedTimeBandSourcePair a ha (D i)) l (nhds T)) := by
  rw [tendsto_soninNuclearResponsePair_iff_timeBand]
  constructor
  · rintro ⟨T,hT⟩
    exact ⟨soninTimeBandChannelSplit a T,(soninTimeBandChannelSplit a).continuous.continuousAt.tendsto.comp hT⟩
  · rintro ⟨T,hT⟩
    refine ⟨soninTimeBandChannelMerge T,?_⟩
    exact (soninTimeBandChannelMerge.continuous.continuousAt.tendsto.comp hT).congr
      fun i => soninTimeBandChannelMerge_apply a ha (D i)

end RHTower
