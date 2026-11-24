import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HolomorphicLefschetzIntegral
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TangentMatrixOpenRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenCorrespondenceTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothComponents

/-! The fixed-point formula for finite étale correspondences descends
from the integral clopen components of the source and target. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace UpperTheory.Cb
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.T

variable {k : Type} [Field k] {Y : Scheme.{0}} {t : Y ⟶ Spec (CommRingCat.of k)}

private def pointIn (W : Y.Opens) :
    W.toScheme.BaseFieldPointOver k (W.ι ≫ t) → Y.BaseFieldPointOver k t :=
  mapBaseFieldPoint (f := W.ι) rfl

private theorem pointIn_injective (W : Y.Opens) :
    Function.Injective (pointIn (t := t) W) := by
  intro a b h
  apply baseFieldPoint_eq_of_hom_eq
  apply (cancel_mono W.ι).mp
  exact congrArg Scheme.BaseFieldPointOver.hom h

private theorem pointIn_mem (W : Y.Opens) (a : W.toScheme.BaseFieldPointOver k (W.ι ≫ t)) :
    (pointIn W a).hom default ∈ W :=
  (a.hom default).property

open Classical in
private theorem sum_points_clopen {J : Type} [Fintype J] (W : J → Y.Opens)
    (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hc : iSup W = ⊤)
    (S : Finset (Y.BaseFieldPointOver k t)) (w : Y.BaseFieldPointOver k t → k) :
    ∑ j, ∑ y ∈ S.preimage (pointIn (t := t) (W j)) (pointIn_injective _).injOn, w (pointIn (W j) y) =
      ∑ y ∈ S, w y := by
  simp_rw [Finset.sum_preimage', Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨j, ⟨f, hf, -⟩, -⟩ :=
    existsUnique_lift_one_point y.hom default W hd hc
  let z : (W j).toScheme.BaseFieldPointOver k ((W j).ι ≫ t) :=
    ⟨f, by rw [← Category.assoc, hf, y.commutes]⟩
  have hz : pointIn (W j) z = y := baseFieldPoint_eq_of_hom_eq hf
  rw [Finset.sum_eq_single j]
  · exact if_pos ⟨z, hz⟩
  · intro j' _ hne
    apply if_neg
    rintro ⟨z', hz'⟩
    have hx : y.hom default ∈ W j' ⊓ W j :=
      ⟨hz' ▸ pointIn_mem _ _, hz ▸ pointIn_mem _ _⟩
    rw [hd j' j hne] at hx
    exact hx
  · simp

variable [IsAlgClosed k] [CharZero k]
  {Z : Scheme.{0}} {s : Z ⟶ Spec (CommRingCat.of k)} {d : ℕ} [SmoothOfRelativeDimension d s]
  {c₁ c₂ : Y ⟶ Z} {h₁ : c₁ ≫ s = t} {h₂ : c₂ ≫ s = t}

/-- A source component with both legs landing in the same target component
contributes the integral fixed-point sum on its diagonal block. -/
private theorem lefschetz_component {I : Type} [Fintype I] [DecidableEq I]
    (V : I → Z.Opens) (hcl : ∀ i, IsClosed (V i : Set Z))
    (hd : ∀ i j, i ≠ j → V i ⊓ V j = ⊥) (hc : iSup V = ⊤)
    (hp : IsProjOver s) (i j : I) (W : Y.Opens) [IsIntegral W.toScheme]
    [∀ i, IsIntegral (V i).toScheme] [∀ i, IsClosedImmersion (V i).ι]
    {f₁ : W.toScheme ⟶ (V i).toScheme} {f₂ : W.toScheme ⟶ (V j).toScheme}
    [IsFinite f₁] [Etale f₁] [IsFinite f₂] [Etale f₂]
    [IsFinite (W.ι ≫ c₁)] [Etale (W.ι ≫ c₁)]
    (e₁ : f₁ ≫ (V i).ι = W.ι ≫ c₁) (e₂ : f₂ ≫ (V j).ι = W.ι ≫ c₂)
    (S : Finset (Y.BaseFieldPointOver k t))
    (hS : ∀ y, y ∈ S ↔ y.hom ≫ c₁ = y.hom ≫ c₂)
    (M : Y.BaseFieldPointOver k t → Matrix (Fin d) (Fin d) k)
    (hM : ∀ y ∈ S, W1.IsTan d h₁ h₂ y (M y) ∧ (1 - M y).det ≠ 0) (p : ℕ) :
    ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q *
      LinearMap.trace k _ (hodgeTrace (f := W.ι ≫ c₁) (by rw [Category.assoc, h₁]) p q ∘ₗ
        hodgePullback (f := W.ι ≫ c₂) (by rw [Category.assoc, h₂]) p q) =
      ∑ y ∈ S.preimage (pointIn (t := t) W) (pointIn_injective W).injOn,
        (1 + (Polynomial.X : Polynomial k) • (M (pointIn W y)).map Polynomial.C).det.coeff p /
          (1 - M (pointIn W y)).det := by
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  letI (a : I) : SmoothOfRelativeDimension d ((V a).ι ≫ s) := by
    simpa only [Nat.zero_add] using (smoothOfRelativeDimension_comp (n := 0) (m := d) (V a).ι s)
  letI (a : I) : Smooth ((V a).ι ≫ s) := SmoothOfRelativeDimension.smooth d _
  letI (q : ℕ) : FiniteDimensional k (HodgeCohomology s p q) :=
    hodgeCohomology_finite_of_projective s hp p q
  letI (q : ℕ) (a : I) : FiniteDimensional k (HodgeCohomology ((V a).ι ≫ s) p q) :=
    hodgeCohomology_finite_of_projective _ (hp.restrict_clopen (V a) (hcl a)) p q
  have g₁ : f₁ ≫ (V i).ι ≫ s = W.ι ≫ t := by rw [← Category.assoc, e₁, Category.assoc, h₁]
  have g₂ : f₂ ≫ (V j).ι ≫ s = W.ι ≫ t := by rw [← Category.assoc, e₂, Category.assoc, h₂]
  have fixed_iff (y : W.toScheme.BaseFieldPointOver k (W.ι ≫ t)) :
      y ∈ S.preimage (pointIn (t := t) W) (pointIn_injective W).injOn ↔
        (y.hom ≫ f₁) ≫ (V i).ι = (y.hom ≫ f₂) ≫ (V j).ι := by
    rw [Finset.mem_preimage, hS]
    change (y.hom ≫ W.ι) ≫ c₁ = (y.hom ≫ W.ι) ≫ c₂ ↔ _
    simp only [Category.assoc, e₁, e₂]
  by_cases hij : i = j
  · subst j
    have hlocal (y : W.toScheme.BaseFieldPointOver k (W.ι ≫ t)) :
        y ∈ S.preimage (pointIn (t := t) W) (pointIn_injective W).injOn ↔
          y.hom ≫ f₁ = y.hom ≫ f₂ :=
      (fixed_iff y).trans (cancel_mono (V i).ι)
    have hrows (y : W.toScheme.BaseFieldPointOver k (W.ι ≫ t))
        (hy : y ∈ S.preimage (pointIn (t := t) W) (pointIn_injective W).injOn) :
        W1.IsTan d g₁ g₂ y (M (pointIn W y)) ∧ (1 - M (pointIn W y)).det ≠ 0 := by
      have hmem := Finset.mem_preimage.mp hy
      obtain ⟨hT, hD⟩ := hM (pointIn W y) hmem
      exact ⟨hT.restrictOpen (V i) W e₁ e₂ g₁ g₂ y ((hS _).mp hmem), hD⟩
    have key := holomorphic_lefschetz_finiteEtale_integral g₁ g₂ (hp.restrict_clopen _ (hcl i))
      _ hlocal (fun y => M (pointIn W y)) hrows p
    rw [← key.2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hodgeCorrespondence_factor e₁ e₂ (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂])
      g₁ g₂ p q, trace_clopen_diagonal s V hcl hd hc p q i]
  · have hempty : S.preimage (pointIn (t := t) W) (pointIn_injective W).injOn = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h := congrArg (fun f : Spec (CommRingCat.of k) ⟶ Z => f default) ((fixed_iff y).mp hy)
      have hxy : ((y.hom ≫ f₁) ≫ (V i).ι) default ∈ V i ⊓ V j :=
        ⟨(f₁ (y.hom default)).property, h ▸ (f₂ (y.hom default)).property⟩
      rw [hd i j hij] at hxy
      exact hxy
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [hodgeCorrespondence_factor e₁ e₂ (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂])
      g₁ g₂ p q, trace_clopen_off_diagonal s V hcl hd hc p q hij, mul_zero]

include h₁ h₂ in
/-- The alternating Hodge trace of a transverse finite étale correspondence
on a smooth projective scheme is the sum of its local cotangent ratios. -/
theorem lefschetz_fixedPoint_finite_etale_correspondence
    [IsFinite c₁] [Etale c₁] [IsFinite c₂] [Etale c₂]
    (hp : IsProjOver s) (S : Finset (Y.BaseFieldPointOver k t))
    (hS : ∀ y, y ∈ S ↔ y.hom ≫ c₁ = y.hom ≫ c₂)
    (M : Y.BaseFieldPointOver k t → Matrix (Fin d) (Fin d) k)
    (hM : ∀ y ∈ S, W1.IsTan d h₁ h₂ y (M y) ∧ (1 - M y).det ≠ 0) (p : ℕ) :
    (∀ q, FiniteDimensional k (HodgeCohomology s p q)) ∧
      ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q *
        LinearMap.trace k _ (hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q) =
      ∑ y ∈ S, (1 + (Polynomial.X : Polynomial k) • (M y).map Polynomial.C).det.coeff p /
        (1 - M y).det := by
  classical
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  letI : SmoothOfRelativeDimension d t := by
    rw [← h₁]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d c₁ s
  letI : Smooth t := SmoothOfRelativeDimension.smooth d t
  letI : CompactSpace Z := hp.compactSpace
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c₁
  obtain ⟨I, hI, V, hvd, hvc, hVi⟩ := exists_integral_clopen_decomposition_of_smooth Z s
  obtain ⟨J, hJ, W, hwd, hwc, hWi⟩ := exists_integral_clopen_decomposition_of_smooth Y t
  letI : Fintype I := hI
  letI : Fintype J := hJ
  letI (i : I) : IsIntegral (V i).toScheme := hVi i
  letI (m : J) : IsIntegral (W m).toScheme := hWi m
  have hVcl (i : I) := isClosed_of_disjoint_open_cover V hvd hvc i
  have hWcl (m : J) := isClosed_of_disjoint_open_cover W hwd hwc m
  letI (i : I) : IsClosedImmersion (V i).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hVcl i)
  letI (m : J) : IsClosedImmersion (W m).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hWcl m)
  letI (m : J) : IsFinite ((W m).ι ≫ c₁) := inferInstance
  letI (m : J) : Etale ((W m).ι ≫ c₁) := inferInstance
  choose i₁ hi₁ using fun m => exists_le_preimage_component c₁ (W m) V hVcl hvc
  choose i₂ hi₂ using fun m => exists_le_preimage_component c₂ (W m) V hVcl hvc
  let f₁ (m : J) := c₁.resLE (V (i₁ m)) (W m) (hi₁ m)
  let f₂ (m : J) := c₂.resLE (V (i₂ m)) (W m) (hi₂ m)
  letI (m : J) : IsFinite (f₁ m) := finite_resLE_of_clopen c₁ _ _ (hWcl m) (hi₁ m)
  letI (m : J) : IsFinite (f₂ m) := finite_resLE_of_clopen c₂ _ _ (hWcl m) (hi₂ m)
  letI (m : J) : Etale (f₁ m) := by dsimp [f₁, Scheme.Hom.resLE]; infer_instance
  letI (m : J) : Etale (f₂ m) := by dsimp [f₂, Scheme.Hom.resLE]; infer_instance
  have e₁ (m : J) : f₁ m ≫ (V (i₁ m)).ι = (W m).ι ≫ c₁ := c₁.resLE_comp_ι (hi₁ m)
  have e₂ (m : J) : f₂ m ≫ (V (i₂ m)).ι = (W m).ι ≫ c₂ := c₂.resLE_comp_ι (hi₂ m)
  let a₁ (m : J) : ((W m).ι ≫ c₁) ≫ s = (W m).ι ≫ t := by rw [Category.assoc, h₁]
  let a₂ (m : J) : ((W m).ι ≫ c₂) ≫ s = (W m).ι ≫ t := by rw [Category.assoc, h₂]
  have htotal (q : ℕ) : hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q =
      ∑ m, hodgeTrace (a₁ m) p q ∘ₗ hodgePullback (a₂ m) p q := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.comp_apply, hodgeTrace_eq_sum_clopen h₁ W hwd hwc, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.comp_apply, hodgePullback_comp h₂ rfl (a₂ m)]
  refine ⟨fun q => hodgeCohomology_finite_of_projective s hp p q, ?_⟩
  simp_rw [htotal, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [fun m => lefschetz_component (h₁ := h₁) (h₂ := h₂) V hVcl hvd hvc hp
    (i₁ m) (i₂ m) (W m) (e₁ m) (e₂ m) S hS M hM p]
  exact sum_points_clopen W hwd hwc S _

end GlobalTheory.T
