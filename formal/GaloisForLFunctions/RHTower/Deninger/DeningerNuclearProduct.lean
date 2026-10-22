import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSpaceInvariance

/-!
# Products of nuclear spaces are nuclear

A linear map bounded from one seminorm to another induces a bounded map of the associated normed
spaces; the comparison map of two seminorms on one space is the case of the identity.  For a
product, the coordinate projections and the coordinate inclusions are such maps.

The product topology is presented by the seminorms that add finitely many coordinate seminorms.
The comparison map of two such seminorms decomposes as the finite sum, over the coordinates
involved, of the coordinate comparison maps conjugated by the projection and the inclusion.  A
finite sum of nuclear maps is nuclear, so a product of nuclear spaces is nuclear.

* `deningerSeminormInduced` : the map of normed spaces induced by a bounded linear map.
* `DeningerIsNuclear.sum` : a finite sum of nuclear maps is nuclear.
* `deningerPiSeminorm`, `deningerPiFamily` : the product presentation.
* `deningerIsNuclearSpace_pi` : a product of nuclear spaces is nuclear.
-/

namespace RHTower

section Induced

variable {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup E'] [Module 𝕜 E']

theorem deningerSeminormKer_comap {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) :
    deningerSeminormKer q ≤ Submodule.comap f (deningerSeminormKer p) := by
  intro x hx
  have hqx : q x = 0 := hx
  show p (f x) = 0
  refine le_antisymm ?_ (apply_nonneg p _)
  have := h x
  rwa [hqx, mul_zero] at this

/-- **The map of normed spaces induced by a bounded linear map.**  A linear map taking the second
seminorm to a multiple of the first induces a bounded map of the associated normed spaces. -/
noncomputable def deningerSeminormInduced {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) :
    DeningerSeminormSpace q →L[𝕜] DeningerSeminormSpace p :=
  LinearMap.mkContinuous
    (Submodule.mapQ (deningerSeminormKer q) (deningerSeminormKer p) f
      (deningerSeminormKer_comap f h))
    C (by
      rintro ⟨a⟩
      show p (f a) ≤ C * q a
      exact h a)

@[simp]
theorem deningerSeminormInduced_mk {p : Seminorm 𝕜 E'} {q : Seminorm 𝕜 E} {C : ℝ}
    (f : E →ₗ[𝕜] E') (h : ∀ x, p (f x) ≤ C * q x) (x : E) :
    deningerSeminormInduced f h (deningerSeminormMk q x) = deningerSeminormMk p (f x) := rfl

end Induced

section FinsetSum

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A finite sum of nuclear maps is nuclear.** -/
theorem DeningerIsNuclear.sum {ι : Type*} (s : Finset ι) {T : ι → X →L[𝕜] Y}
    (h : ∀ i ∈ s, DeningerIsNuclear (T i)) : DeningerIsNuclear (∑ i ∈ s, T i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using deningerIsNuclear_zero
  | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end FinsetSum

section ProductSeminorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type} [DecidableEq ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

theorem deningerSeminormFinsetSum_apply {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (s : Finset ι) (f : ι → Seminorm 𝕜 E) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- **The product seminorm** attached to a finite set of coordinates: the sum of the chosen
coordinate seminorms. -/
def deningerPiSeminorm (s : Finset ι) (p : ∀ i, Seminorm 𝕜 (F i)) :
    Seminorm 𝕜 (∀ i, F i) :=
  ∑ i ∈ s, (p i).comp (LinearMap.proj i)

theorem deningerPiSeminorm_apply (s : Finset ι) (p : ∀ i, Seminorm 𝕜 (F i)) (x : ∀ i, F i) :
    deningerPiSeminorm s p x = ∑ i ∈ s, p i (x i) := by
  rw [deningerPiSeminorm, deningerSeminormFinsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => Seminorm.comp_apply _ _ _

/-- Every chosen coordinate seminorm is dominated by the product seminorm. -/
theorem deningerPiSeminorm_proj_le {s : Finset ι} {p : ∀ i, Seminorm 𝕜 (F i)} {i : ι}
    (hi : i ∈ s) (x : ∀ j, F j) : p i (x i) ≤ deningerPiSeminorm s p x := by
  rw [deningerPiSeminorm_apply]
  exact Finset.single_le_sum (fun j _ => apply_nonneg (p j) (x j)) hi

theorem deningerPiSeminorm_single_eq_of_mem {s : Finset ι}
    {p : ∀ i, Seminorm 𝕜 (F i)} {i : ι}
    (hi : i ∈ s) (v : F i) :
    deningerPiSeminorm s p (LinearMap.single 𝕜 F i v) = p i v := by
  classical
  rw [deningerPiSeminorm_apply]
  rw [Finset.sum_eq_single_of_mem i hi (fun j _ hj => by
    show p j (Pi.single i v j) = 0
    rw [Pi.single_eq_of_ne hj, map_zero])]
  show p i (Pi.single i v i) = p i v
  rw [Pi.single_eq_same]

/-- The product seminorm of a coordinate vector is at most its coordinate seminorm. -/
theorem deningerPiSeminorm_single_le (s : Finset ι) (p : ∀ i, Seminorm 𝕜 (F i)) (i : ι)
    (v : F i) : deningerPiSeminorm s p (LinearMap.single 𝕜 F i v) ≤ p i v := by
  classical
  by_cases hi : i ∈ s
  · exact le_of_eq (deningerPiSeminorm_single_eq_of_mem hi v)
  · rw [deningerPiSeminorm_apply]
    refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (apply_nonneg (p i) v)
    intro j hj
    have hne : i ≠ j := fun hEq => hi (hEq ▸ hj)
    show p j (Pi.single i v j) = 0
    rw [Pi.single_eq_of_ne (Ne.symm hne), map_zero]

/-- **The product presentation** of a product of locally convex spaces. -/
def deningerPiFamily {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i)) :
    SeminormFamily 𝕜 (∀ i, F i) (Finset ι × (∀ i, κ i)) :=
  fun sk => deningerPiSeminorm (𝕜 := 𝕜) (F := F) sk.1 fun i => P i (sk.2 i)

end ProductSeminorm

section ProductNuclear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type} [DecidableEq ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- **A product of nuclear spaces is nuclear.**  The comparison map of two product seminorms is
the finite sum, over the coordinates involved, of the coordinate comparison maps conjugated by the
coordinate projection and the coordinate inclusion. -/
theorem deningerIsNuclearSpace_pi {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (hP : ∀ i, DeningerIsNuclearSpace (P i)) :
    DeningerIsNuclearSpace (deningerPiFamily P) := by
  classical
  rintro ⟨s, k⟩
  choose k' C hle hnuc using fun i => hP i (k i)
  set p : ∀ i, Seminorm 𝕜 (F i) := fun i => P i (k i) with hp
  set p' : ∀ i, Seminorm 𝕜 (F i) := fun i => P i (k' i) with hp'
  set Pfam : Seminorm 𝕜 (∀ i, F i) := deningerPiSeminorm s p with hPfam
  set Q : Seminorm 𝕜 (∀ i, F i) := deningerPiSeminorm s p' with hQ
  set D : ℝ := ∑ i ∈ s, |C i| with hD
  have hDnonneg : 0 ≤ D := Finset.sum_nonneg fun i _ => abs_nonneg (C i)
  -- the domination of the two product seminorms
  have hdom : ∀ x, Pfam x ≤ D * Q x := by
    intro x
    rw [hPfam, deningerPiSeminorm_apply]
    have hterm : ∀ i ∈ s, p i (x i) ≤ |C i| * Q x := by
      intro i hi
      calc p i (x i) ≤ |C i| * p' i (x i) := deningerSeminorm_le_abs (hle i) (x i)
        _ ≤ |C i| * Q x := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (C i))
            exact deningerPiSeminorm_proj_le hi x
    calc ∑ i ∈ s, p i (x i) ≤ ∑ i ∈ s, |C i| * Q x := Finset.sum_le_sum hterm
      _ = D * Q x := by rw [hD, Finset.sum_mul]
  refine ⟨(s, k'), D, hdom, ?_⟩
  -- the coordinate projections and inclusions
  have hproj : ∀ i ∈ s, ∀ x : ∀ j, F j, p' i (x i) ≤ 1 * Q x := by
    intro i hi x
    rw [one_mul]
    exact deningerPiSeminorm_proj_le hi x
  have hincl : ∀ i : ι, ∀ v : F i,
      Pfam (LinearMap.single 𝕜 F i v) ≤ 1 * p i v := by
    intro i v
    rw [one_mul]
    exact deningerPiSeminorm_single_le s p i v
  -- the decomposition of the comparison map
  set G : ι → (DeningerSeminormSpace Q →L[𝕜] DeningerSeminormSpace Pfam) := fun i =>
    if hi : i ∈ s then
      (deningerSeminormInduced (LinearMap.single 𝕜 F i) (hincl i)).comp
        ((deningerSeminormComparison (hle i)).comp
          (deningerSeminormInduced (LinearMap.proj (R := 𝕜) (φ := F) i) (hproj i hi)))
    else 0 with hG
  have hGnuc : ∀ i ∈ s, DeningerIsNuclear (G i) := by
    intro i hi
    rw [hG]
    simp only [dif_pos hi]
    exact ((hnuc i).compR _).compL _
  have hsum : DeningerIsNuclear (∑ i ∈ s, G i) := DeningerIsNuclear.sum s hGnuc
  refine hsum.of_eq ?_
  refine deningerSeminormComparison_ext _ _ fun x => ?_
  have hcoord : ∀ i ∈ s, G i (deningerSeminormMk Q x)
      = deningerSeminormMk Pfam (LinearMap.single 𝕜 F i (x i)) := by
    intro i hi
    rw [hG]
    simp only [dif_pos hi, ContinuousLinearMap.comp_apply, deningerSeminormInduced_mk,
      deningerSeminormComparison_mk]
    rfl
  have hker : x - ∑ i ∈ s, LinearMap.single 𝕜 F i (x i) ∈ deningerSeminormKer Pfam := by
    show Pfam (x - ∑ i ∈ s, LinearMap.single 𝕜 F i (x i)) = 0
    rw [hPfam, deningerPiSeminorm_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hval : (∑ i ∈ s, LinearMap.single 𝕜 F i (x i)) j = x j := by
      rw [Finset.sum_apply]
      refine (Finset.sum_eq_single_of_mem j hj ?_).trans ?_
      · intro b _ hb
        exact Pi.single_eq_of_ne (Ne.symm hb) (x b)
      · exact Pi.single_eq_same j (x j)
    have hzero : (x - ∑ i ∈ s, LinearMap.single 𝕜 F i (x i)) j = 0 := by
      show x j - (∑ i ∈ s, LinearMap.single 𝕜 F i (x i)) j = 0
      rw [hval, sub_self]
    rw [hzero, map_zero]
  calc deningerSeminormComparison hdom (deningerSeminormMk Q x)
      = deningerSeminormMk Pfam x := rfl
    _ = deningerSeminormMk Pfam (∑ i ∈ s, LinearMap.single 𝕜 F i (x i)) :=
        (Submodule.Quotient.eq _).mpr hker
    _ = ∑ i ∈ s, deningerSeminormMk Pfam (LinearMap.single 𝕜 F i (x i)) :=
        map_sum (deningerSeminormMk Pfam) _ _
    _ = ∑ i ∈ s, G i (deningerSeminormMk Q x) := (Finset.sum_congr rfl hcoord).symm
    _ = (∑ i ∈ s, G i) (deningerSeminormMk Q x) := (_root_.sum_apply _ _ _).symm

end ProductNuclear

end RHTower

