import GaloisForLFunctions.RHTower.ProjectivePrimeWeylModel
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The finite tensor aperture of projective clocks

Over a finite aperture `ι` of primes, the local projective clocks `EuclideanSpace ℂ (X i)` assemble
into the tensor product `⨂[ℂ] i, EuclideanSpace ℂ (X i)`.  The point/complement polarizations
assemble with them, as the span of the elementary tensors of their members.

Two facts are proved here.

* A tensor lies in `⨂ᵢ E_{a i}` exactly when its product coordinate function is, in each slot
  separately, constant off the marked point of that slot.  The nontrivial direction is a finite
  expansion: the `2^{|ι|}` tensors of marked-point and complement indicators are themselves
  elementary tensors of polarization members, and their coordinate functions are the indicators of
  the level sets of the marked-point pattern.

* Two such tensor polarizations with everywhere-distinct marked points meet exactly in the line of
  the uniform source tensor, provided every local clock has at least three points.  The mechanism is
  a one-slot exchange through a third point, which is invisible to both polarizations at once, so
  the coordinate function of a common tensor cannot depend on any slot at all.
-/

open Complex Finset
open scoped TensorProduct
open Module

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-! ## Product coordinates on the aperture tensor product -/

/-- The product coordinate basis of the aperture tensor product, indexed by choices of one point in
each local clock. -/
def apertureBasis (X : ι → Type*) [∀ i, Fintype (X i)] :
    Basis (∀ i, X i) ℂ (⨂[ℂ] i, EuclideanSpace ℂ (X i)) :=
  Basis.piTensorProduct (fun i => PiLp.basisFun 2 ℂ (X i))

/-- The coordinate of an aperture tensor at a choice of one point in each local clock. -/
def apertureCoord (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) : ℂ :=
  (apertureBasis X).repr t ξ

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem apertureCoord_tprod (v : ∀ i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) :
    apertureCoord (⨂ₜ[ℂ] i, v i) ξ = ∏ i, v i (ξ i) := by
  rw [apertureCoord, apertureBasis, Basis.piTensorProduct_repr_tprod_apply]
  rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
@[simp]
theorem apertureCoord_add (s t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) :
    apertureCoord (s + t) ξ = apertureCoord s ξ + apertureCoord t ξ := by
  simp [apertureCoord]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
@[simp]
theorem apertureCoord_zero (ξ : ∀ i, X i) :
    apertureCoord (0 : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) ξ = 0 := by
  simp [apertureCoord]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
@[simp]
theorem apertureCoord_smul (c : ℂ) (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) :
    apertureCoord (c • t) ξ = c * apertureCoord t ξ := by
  simp [apertureCoord]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem apertureCoord_sum {κ : Type*} (s : Finset κ)
    (f : κ → ⨂[ℂ] i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) :
    apertureCoord (∑ k ∈ s, f k) ξ = ∑ k ∈ s, apertureCoord (f k) ξ := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, apertureCoord_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, apertureCoord_add, ih]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
/-- Aperture tensors are determined by their product coordinates. -/
theorem apertureTensor_ext {s t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)}
    (h : ∀ ξ, apertureCoord s ξ = apertureCoord t ξ) : s = t := by
  refine (apertureBasis X).repr.injective ?_
  ext ξ
  exact h ξ

/-! ## Slot-by-slot exchange -/

omit [(i : ι) → DecidableEq (X i)] in
/-- **The exchange walk.**  A coordinate function that is invariant under changing a single slot,
whenever the two values in that slot are related by `R`, is invariant under changing every slot at
once. -/
theorem apertureCoord_congr_of_step {t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)}
    {R : ∀ i, X i → X i → Prop}
    (hstep : ∀ (i : ι) (ξ η : ∀ j, X j), (∀ j, j ≠ i → ξ j = η j) → R i (ξ i) (η i) →
      apertureCoord t ξ = apertureCoord t η)
    {ξ η : ∀ j, X j} (hR : ∀ i, R i (ξ i) (η i)) :
    apertureCoord t ξ = apertureCoord t η := by
  classical
  set hyb : Finset ι → (∀ j, X j) := fun D j => if j ∈ D then η j else ξ j with hhyb
  have key : ∀ D : Finset ι, apertureCoord t (hyb D) = apertureCoord t ξ := by
    intro D
    induction D using Finset.induction with
    | empty => simp [hhyb]
    | insert i D hi ih =>
        refine Eq.trans ?_ ih
        have hagree : ∀ j, j ≠ i → hyb D j = hyb (insert i D) j := by
          intro j hj
          simp [hhyb, Finset.mem_insert, hj]
        have hxi : hyb D i = ξ i := by simp [hhyb, hi]
        have hyi : hyb (insert i D) i = η i := by simp [hhyb]
        refine (hstep i (hyb D) (hyb (insert i D)) hagree ?_).symm
        rw [hxi, hyi]
        exact hR i
  have huniv : hyb Finset.univ = η := by
    funext j
    simp [hhyb]
  rw [← key Finset.univ, huniv]

/-! ## The tensor of a family of polarizations -/

/-- The tensor product of a family of local subspaces: the span of the elementary tensors of their
members. -/
def tensorSubspace (A : ∀ i, Submodule ℂ (EuclideanSpace ℂ (X i))) :
    Submodule ℂ (⨂[ℂ] i, EuclideanSpace ℂ (X i)) :=
  Submodule.span ℂ
    {t | ∃ v : ∀ i, EuclideanSpace ℂ (X i), (∀ i, v i ∈ A i) ∧ t = ⨂ₜ[ℂ] i, v i}

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (X i)] [(i : ι) → DecidableEq (X i)] in
theorem tprod_mem_tensorSubspace {A : ∀ i, Submodule ℂ (EuclideanSpace ℂ (X i))}
    {v : ∀ i, EuclideanSpace ℂ (X i)} (hv : ∀ i, v i ∈ A i) :
    (⨂ₜ[ℂ] i, v i) ∈ tensorSubspace A :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- The aperture tensors whose coordinate function is, in every slot separately, constant off the
marked point of that slot. -/
def apertureSlotPolarization (a : ∀ i, X i) :
    Submodule ℂ (⨂[ℂ] i, EuclideanSpace ℂ (X i)) where
  carrier := {t | ∀ (i : ι) (ξ η : ∀ j, X j), (∀ j, j ≠ i → ξ j = η j) →
    ξ i ≠ a i → η i ≠ a i → apertureCoord t ξ = apertureCoord t η}
  add_mem' hs ht := by
    intro i ξ η hag hξ hη
    rw [apertureCoord_add, apertureCoord_add, hs i ξ η hag hξ hη, ht i ξ η hag hξ hη]
  zero_mem' := by
    intro i ξ η _ _ _
    rw [apertureCoord_zero, apertureCoord_zero]
  smul_mem' c t ht := by
    intro i ξ η hag hξ hη
    rw [apertureCoord_smul, apertureCoord_smul, ht i ξ η hag hξ hη]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem mem_apertureSlotPolarization_iff (a : ∀ i, X i)
    (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) :
    t ∈ apertureSlotPolarization a ↔ ∀ (i : ι) (ξ η : ∀ j, X j), (∀ j, j ≠ i → ξ j = η j) →
      ξ i ≠ a i → η i ≠ a i → apertureCoord t ξ = apertureCoord t η := Iff.rfl

/-- The set of slots at which a point choice hits the marked point. -/
def apertureLevel (a ξ : ∀ i, X i) : Finset ι := Finset.univ.filter fun i => ξ i = a i

omit [DecidableEq ι] [(i : ι) → Fintype (X i)] in
theorem mem_apertureLevel_iff (a ξ : ∀ i, X i) (i : ι) :
    i ∈ apertureLevel a ξ ↔ ξ i = a i := by
  simp [apertureLevel]

omit [(i : ι) → DecidableEq (X i)] in
/-- A tensor in the slot polarization has a coordinate function depending only on the level set of
the marked-point pattern. -/
theorem apertureCoord_eq_of_level {a : ∀ i, X i} {t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)}
    (ht : t ∈ apertureSlotPolarization a) {ξ η : ∀ j, X j}
    (hlev : ∀ i, (ξ i = a i ↔ η i = a i)) :
    apertureCoord t ξ = apertureCoord t η := by
  refine apertureCoord_congr_of_step
    (R := fun i x y => (x = a i ∧ y = a i) ∨ (x ≠ a i ∧ y ≠ a i)) ?_ ?_
  · rintro i ξ' η' hag (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have : ξ' = η' := by
        funext j
        rcases eq_or_ne j i with hj | hj
        · subst hj; rw [h1, h2]
        · exact hag j hj
      rw [this]
    · exact ht i ξ' η' hag h1 h2
  · intro i
    rcases eq_or_ne (ξ i) (a i) with h | h
    · exact Or.inl ⟨h, (hlev i).mp h⟩
    · exact Or.inr ⟨h, fun hc => h ((hlev i).mpr hc)⟩

/-! ## The level-set indicator tensors -/

/-- The elementary tensor factor that is the marked-point indicator on the slots of `S` and the
complement indicator elsewhere. -/
def apertureIndicator (a : ∀ i, X i) (S : Finset ι) (i : ι) : EuclideanSpace ℂ (X i) :=
  if i ∈ S then projTwoValue (a i) 1 0 else projTwoValue (a i) 0 1

omit [Fintype ι] [(i : ι) → Fintype (X i)] in
theorem apertureIndicator_mem (a : ∀ i, X i) (S : Finset ι) (i : ι) :
    apertureIndicator a S i ∈ projPolarization (a i) := by
  rw [apertureIndicator]
  split <;> exact projTwoValue_mem_projPolarization _ _ _

omit [Fintype ι] [(i : ι) → Fintype (X i)] in
theorem apertureIndicator_apply (a : ∀ i, X i) (S : Finset ι) (i : ι) (x : X i) :
    apertureIndicator a S i x = if (i ∈ S ↔ x = a i) then 1 else 0 := by
  rw [apertureIndicator]
  by_cases hi : i ∈ S <;> by_cases hx : x = a i <;> simp [hi, hx]

/-- The coordinate function of an indicator tensor is the indicator of one level set. -/
theorem apertureCoord_indicator (a : ∀ i, X i) (S : Finset ι) (ξ : ∀ i, X i) :
    apertureCoord (⨂ₜ[ℂ] i, apertureIndicator a S i) ξ
      = if S = apertureLevel a ξ then 1 else 0 := by
  classical
  rw [apertureCoord_tprod]
  by_cases hS : S = apertureLevel a ξ
  · rw [if_pos hS]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [apertureIndicator_apply, if_pos]
    rw [hS, mem_apertureLevel_iff]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ apertureLevel a ξ) := by
      by_contra hcon
      exact hS (Finset.ext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [apertureIndicator_apply, if_neg]
    rw [mem_apertureLevel_iff] at hi
    exact hi

/-! ## The tensor polarization is exactly the slot polarization -/

omit [DecidableEq ι] in
theorem tensorSubspace_projPolarization_le (a : ∀ i, X i) :
    tensorSubspace (fun i => projPolarization (a i)) ≤ apertureSlotPolarization a := by
  rw [tensorSubspace, Submodule.span_le]
  rintro t ⟨v, hv, rfl⟩
  intro i ξ η hag hξ hη
  rw [apertureCoord_tprod, apertureCoord_tprod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases eq_or_ne j i with hj | hj
  · subst hj
    obtain ⟨β, hβ⟩ := (mem_projPolarization_iff (a j) (v j)).mp (hv j)
    rw [hβ (ξ j) hξ, hβ (η j) hη]
  · rw [hag j hj]

theorem le_tensorSubspace_projPolarization (h2 : ∀ i, 2 ≤ Fintype.card (X i)) (a : ∀ i, X i) :
    apertureSlotPolarization a ≤ tensorSubspace (fun i => projPolarization (a i)) := by
  classical
  have hother : ∀ i, ∃ y : X i, y ≠ a i := by
    intro i
    exact Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le (by norm_num) (h2 i)) (a i)
  choose other hother using hother
  intro t ht
  -- a point choice realizing an arbitrary level set
  set rep : Finset ι → (∀ i, X i) := fun S i => if i ∈ S then a i else other i with hrep
  have hlevel_rep : ∀ (S : Finset ι) (i : ι), (rep S i = a i ↔ i ∈ S) := by
    intro S i
    by_cases hi : i ∈ S <;> simp [hrep, hi, hother i]
  have hdecomp : t = ∑ S : Finset ι,
      apertureCoord t (rep S) • (⨂ₜ[ℂ] i, apertureIndicator a S i) := by
    refine apertureTensor_ext fun ξ => ?_
    rw [apertureCoord_sum]
    have hterm : ∀ S ∈ (Finset.univ : Finset (Finset ι)),
        apertureCoord (apertureCoord t (rep S) • (⨂ₜ[ℂ] i, apertureIndicator a S i)) ξ
          = if S = apertureLevel a ξ then apertureCoord t (rep S) else 0 := by
      intro S _
      rw [apertureCoord_smul, apertureCoord_indicator]
      split <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ (apertureLevel a ξ)
      (fun S => apertureCoord t (rep S)), if_pos (Finset.mem_univ _)]
    refine apertureCoord_eq_of_level ht fun i => ?_
    rw [hlevel_rep, mem_apertureLevel_iff]
  rw [hdecomp]
  refine Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ ?_
  exact tprod_mem_tensorSubspace (fun i => apertureIndicator_mem a S i)

/-- The tensor product of the point/complement polarizations is exactly the slot-wise polarization
condition on product coordinates. -/
theorem tensorSubspace_projPolarization (h2 : ∀ i, 2 ≤ Fintype.card (X i)) (a : ∀ i, X i) :
    tensorSubspace (fun i => projPolarization (a i)) = apertureSlotPolarization a :=
  le_antisymm (tensorSubspace_projPolarization_le a) (le_tensorSubspace_projPolarization h2 a)

/-! ## The uniform source tensor -/

/-- The tensor of the uniform local source vectors. -/
def apertureUniform (X : ι → Type*) [∀ i, Fintype (X i)] : ⨂[ℂ] i, EuclideanSpace ℂ (X i) :=
  ⨂ₜ[ℂ] i, projUniform (X i)

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
/-- The uniform aperture tensor has a constant, nonzero coordinate function. -/
theorem apertureCoord_apertureUniform (ξ : ∀ i, X i) :
    apertureCoord (apertureUniform X) ξ
      = ∏ i, ((1 / Real.sqrt (Fintype.card (X i)) : ℝ) : ℂ) := by
  rw [apertureUniform, apertureCoord_tprod]
  exact Finset.prod_congr rfl fun i _ => by rw [projUniform, projConst_apply]

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem apertureCoord_apertureUniform_ne_zero (h2 : ∀ i, 2 ≤ Fintype.card (X i)) (ξ : ∀ i, X i) :
    apertureCoord (apertureUniform X) ξ ≠ 0 := by
  rw [apertureCoord_apertureUniform]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  have hcard : (0 : ℝ) < (Fintype.card (X i) : ℝ) := by
    have hc : (0 : ℕ) < Fintype.card (X i) := lt_of_lt_of_le (by norm_num) (h2 i)
    exact_mod_cast hc
  have hs : (0 : ℝ) < Real.sqrt (Fintype.card (X i)) := Real.sqrt_pos.mpr hcard
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact div_ne_zero one_ne_zero (ne_of_gt hs)

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem apertureUniform_mem_slot (a : ∀ i, X i) :
    apertureUniform X ∈ apertureSlotPolarization a := by
  intro i ξ η _ _ _
  rw [apertureCoord_apertureUniform, apertureCoord_apertureUniform]

/-! ## The aperture intersection theorem -/

/-- **Equation (21).**  Two aperture tensor polarizations with everywhere-distinct marked points
meet exactly in the uniform source line. -/
theorem apertureSlotPolarization_inf (h3 : ∀ i, 3 ≤ Fintype.card (X i))
    {a b : ∀ i, X i} (hab : ∀ i, a i ≠ b i) :
    apertureSlotPolarization a ⊓ apertureSlotPolarization b
      = Submodule.span ℂ {apertureUniform X} := by
  classical
  have h2 : ∀ i, 2 ≤ Fintype.card (X i) := fun i => le_trans (by norm_num) (h3 i)
  refine le_antisymm ?_ ?_
  · rintro t ⟨hta, htb⟩
    -- a third point in every slot, invisible to both polarizations
    have hthird : ∀ i, ∃ c : X i, c ≠ a i ∧ c ≠ b i := by
      intro i
      by_contra hcon
      have hall : ∀ x : X i, x = a i ∨ x = b i := by
        intro x
        by_cases hxa : x = a i
        · exact Or.inl hxa
        · by_cases hxb : x = b i
          · exact Or.inr hxb
          · exact absurd ⟨x, hxa, hxb⟩ hcon
      have hsub : (Finset.univ : Finset (X i)) ⊆ {a i, b i} := by
        intro x _
        rcases hall x with hx | hx <;> simp [hx]
      have hcardle := Finset.card_le_card hsub
      rw [Finset.card_univ] at hcardle
      have hle : ({a i, b i} : Finset (X i)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      have := h3 i
      omega
    choose third hthirda hthirdb using hthird
    -- one slot may be changed freely
    have hfree : ∀ (i : ι) (ξ η : ∀ j, X j), (∀ j, j ≠ i → ξ j = η j) →
        apertureCoord t ξ = apertureCoord t η := by
      intro i ξ η hag
      have hstep : ∀ ζ : ∀ j, X j,
          apertureCoord t ζ = apertureCoord t (Function.update ζ i (third i)) := by
        intro ζ
        have hag' : ∀ j, j ≠ i → ζ j = Function.update ζ i (third i) j := by
          intro j hj
          rw [Function.update_of_ne hj]
        have hupd : Function.update ζ i (third i) i = third i := Function.update_self _ _ _
        rcases eq_or_ne (ζ i) (a i) with hz | hz
        · refine htb i ζ _ hag' ?_ ?_
          · rw [hz]; exact fun hc => hab i hc
          · rw [hupd]; exact hthirdb i
        · refine hta i ζ _ hag' hz ?_
          rw [hupd]; exact hthirda i
      have hsame : Function.update ξ i (third i) = Function.update η i (third i) := by
        funext j
        rcases eq_or_ne j i with hj | hj
        · subst hj; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, hag j hj]
      rw [hstep ξ, hstep η, hsame]
    -- hence the coordinate function is constant
    have hconst : ∀ ξ η : ∀ j, X j, apertureCoord t ξ = apertureCoord t η := by
      intro ξ η
      exact apertureCoord_congr_of_step (R := fun _ _ _ => True)
        (fun i ξ' η' hag _ => hfree i ξ' η' hag) (fun _ => trivial)
    obtain ⟨ξ0⟩ : Nonempty (∀ i, X i) := by
      refine ⟨fun i => a i⟩
    set κ := apertureCoord t ξ0 with hκ
    set m := apertureCoord (apertureUniform X) ξ0 with hm
    have hmne : m ≠ 0 := apertureCoord_apertureUniform_ne_zero h2 ξ0
    have hval : t = (κ / m) • apertureUniform X := by
      refine apertureTensor_ext fun ξ => ?_
      rw [apertureCoord_smul, hconst ξ ξ0, ← hκ]
      have : apertureCoord (apertureUniform X) ξ = m := by
        rw [hm, apertureCoord_apertureUniform, apertureCoord_apertureUniform]
      rw [this, div_mul_cancel₀ _ hmne]
    rw [hval]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨apertureUniform_mem_slot a, apertureUniform_mem_slot b⟩

/-- **Equation (21).**  The only finite product line simultaneously carried by two complete
point/complement polarizations of the aperture is the uniform source line. -/
theorem tensorSubspace_projPolarization_inf (h3 : ∀ i, 3 ≤ Fintype.card (X i))
    {a b : ∀ i, X i} (hab : ∀ i, a i ≠ b i) :
    tensorSubspace (fun i => projPolarization (a i))
        ⊓ tensorSubspace (fun i => projPolarization (b i))
      = Submodule.span ℂ {apertureUniform X} := by
  have h2 : ∀ i, 2 ≤ Fintype.card (X i) := fun i => le_trans (by norm_num) (h3 i)
  rw [tensorSubspace_projPolarization h2 a, tensorSubspace_projPolarization h2 b]
  exact apertureSlotPolarization_inf h3 hab

/-! ## The aperture Hilbert norm -/

omit [(i : ι) → DecidableEq (X i)] in
/-- The product coordinate model of the aperture tensor product as a Euclidean space.  It sends the
product coordinate basis to the standard orthonormal basis, so the norm it induces is the Hilbert
tensor norm. -/
def apertureModel (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[ℂ] i, EuclideanSpace ℂ (X i)) ≃ₗ[ℂ] EuclideanSpace ℂ (∀ i, X i) :=
  (apertureBasis X).equivFun.trans (WithLp.linearEquiv 2 ℂ ((∀ i, X i) → ℂ)).symm

omit [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem apertureModel_apply (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) (ξ : ∀ i, X i) :
    apertureModel X t ξ = apertureCoord t ξ := rfl

/-- The Hilbert norm of an aperture tensor. -/
def apertureNorm (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) : ℝ := ‖apertureModel X t‖

omit [(i : ι) → DecidableEq (X i)] in
theorem apertureNorm_nonneg (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) : 0 ≤ apertureNorm t :=
  norm_nonneg _

omit [(i : ι) → DecidableEq (X i)] in
theorem apertureNorm_eq (t : ⨂[ℂ] i, EuclideanSpace ℂ (X i)) :
    apertureNorm t = Real.sqrt (∑ ξ : (∀ i, X i), ‖apertureCoord t ξ‖ ^ 2) := by
  rw [apertureNorm, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun ξ _ => by rw [apertureModel_apply])

omit [(i : ι) → DecidableEq (X i)] in
/-- **The aperture norm is the Hilbert tensor norm.**  On elementary tensors it is the product of
the local norms. -/
theorem apertureNorm_tprod (v : ∀ i, EuclideanSpace ℂ (X i)) :
    apertureNorm (⨂ₜ[ℂ] i, v i) = ∏ i, ‖v i‖ := by
  have hlocal : ∀ i, ∑ x : X i, ‖v i x‖ ^ 2 = ‖v i‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hcoord : ∀ ξ : (∀ i, X i),
      ‖apertureCoord (⨂ₜ[ℂ] i, v i) ξ‖ ^ 2 = ∏ i, ‖v i (ξ i)‖ ^ 2 := by
    intro ξ
    rw [apertureCoord_tprod, norm_prod, ← Finset.prod_pow]
  rw [apertureNorm_eq, Finset.sum_congr rfl fun ξ _ => hcoord ξ]
  have hswap : ∑ ξ : (∀ i, X i), ∏ i, ‖v i (ξ i)‖ ^ 2 = ∏ i, ∑ x : X i, ‖v i x‖ ^ 2 := by
    rw [Finset.prod_univ_sum]
    exact (Finset.sum_congr (by rw [Fintype.piFinset_univ]) fun _ _ => rfl).symm
  rw [hswap, Finset.prod_congr rfl fun i _ => hlocal i, Finset.prod_pow,
    Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg (v i))]

/-! ## Aperture operators -/

/-- The aperture compression: the tensor of the local point/complement orthogonal projections. -/
def apertureCompress (a : ∀ i, X i) :
    (⨂[ℂ] i, EuclideanSpace ℂ (X i)) →ₗ[ℂ] ⨂[ℂ] i, EuclideanSpace ℂ (X i) :=
  PiTensorProduct.map fun i => ((projPolarization (a i)).starProjection : _ →L[ℂ] _).toLinearMap

omit [Fintype ι] [DecidableEq ι] in
theorem apertureCompress_tprod (a : ∀ i, X i) (v : ∀ i, EuclideanSpace ℂ (X i)) :
    apertureCompress a (⨂ₜ[ℂ] i, v i)
      = ⨂ₜ[ℂ] i, (projPolarization (a i)).starProjection (v i) :=
  PiTensorProduct.map_tprod _ v

/-- The aperture reflection: the tensor of the local point-permutation unitaries. -/
def aperturePermute (σ : ∀ i, Equiv.Perm (X i)) :
    (⨂[ℂ] i, EuclideanSpace ℂ (X i)) →ₗ[ℂ] ⨂[ℂ] i, EuclideanSpace ℂ (X i) :=
  PiTensorProduct.map fun i => (projPermute (σ i)).toLinearEquiv.toLinearMap

omit [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (X i)] in
theorem aperturePermute_tprod (σ : ∀ i, Equiv.Perm (X i)) (v : ∀ i, EuclideanSpace ℂ (X i)) :
    aperturePermute σ (⨂ₜ[ℂ] i, v i) = ⨂ₜ[ℂ] i, projPermute (σ i) (v i) :=
  PiTensorProduct.map_tprod _ v

/-- The aperture natural-cone state with marked points `a` and local weights `z`. -/
def apertureNatural (a : ∀ i, X i) (z : ι → ℝ) : ⨂[ℂ] i, EuclideanSpace ℂ (X i) :=
  ⨂ₜ[ℂ] i, projNatural (a i) (z i)

/-! ## The aperture Weyl compression coefficient -/

/-- **Equation (15).**  Reflecting the aperture natural-cone state and compressing it back through
the producer polarizations costs exactly the product of the local Hellinger weights. -/
theorem apertureNorm_compress_permute_natural (h2 : ∀ i, 2 ≤ Fintype.card (X i))
    (a : ∀ i, X i) {σ : ∀ i, Equiv.Perm (X i)} (hσ : ∀ i, a i ≠ σ i (a i)) (z : ι → ℝ) :
    apertureNorm (apertureCompress a (aperturePermute σ (apertureNatural a z)))
      = ∏ i, Real.sqrt (1 - projLeakageValue (X i) (z i)) := by
  have hstate : aperturePermute σ (apertureNatural a z)
      = ⨂ₜ[ℂ] i, projNatural (σ i (a i)) (z i) := by
    rw [apertureNatural, aperturePermute_tprod]
    exact congrArg _ (funext fun i => projPermute_projNatural (σ i) (a i) (z i))
  rw [hstate, apertureCompress_tprod, apertureNorm_tprod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hproj : (projPolarization (a i)).starProjection (projNatural (σ i (a i)) (z i))
      = projCompress (a i) (projNatural (σ i (a i)) (z i)) :=
    starProjection_projPolarization (h2 i) (a i) _
  have hsq := projWeylCompressionNorm (h2 i) (hσ i) (z i)
  rw [hproj, ← Real.sqrt_sq (norm_nonneg (projCompress (a i) (projNatural (σ i (a i)) (z i)))),
    hsq]

/-! ## The prime aperture -/

section PrimeAperture

variable {J : Type*} [Fintype J] [DecidableEq J] (q : J → ℕ) [∀ i, Fact (q i).Prime]

/-- **Equation (21).**  Over a finite aperture of primes, the tensor product of the Euler producer
polarizations and the tensor product of the Weyl reporter polarizations meet exactly in the line of
the uniform projective source tensor. -/
theorem tensorSubspace_weylProducer_inf_weylReporter :
    tensorSubspace (fun i => weylProducer (q i)) ⊓ tensorSubspace (fun i => weylReporter (q i))
      = Submodule.span ℂ {apertureUniform (fun i => Option (ZMod (q i)))} := by
  have h3 : ∀ i, 3 ≤ Fintype.card (Option (ZMod (q i))) := fun i => three_le_card_optionZMod (q i)
  have hne : ∀ i, (none : Option (ZMod (q i))) ≠ some 0 := fun i => by simp
  exact tensorSubspace_projPolarization_inf (X := fun i => Option (ZMod (q i))) h3 hne

end PrimeAperture

end

end RHTower
