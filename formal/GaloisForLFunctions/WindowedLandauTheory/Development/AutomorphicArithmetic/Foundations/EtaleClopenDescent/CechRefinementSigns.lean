import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Refinement maps for alternating Čech complexes. A noninjective list of
images contributes zero, and an injective list is oriented by its permutation. -/

noncomputable section

open GlobalTheory GlobalTheory.CechDR GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.PD

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

/-- The sign of the permutation that orders the image of a finite subset. -/
def sortSign (τ : κ → ι) (s : Finset κ) : ℤ :=
  ∏ a ∈ s, ∏ b ∈ s, if a < b ∧ τ b < τ a then -1 else 1

variable {k M N : Type} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

open Classical in
/-- Pullback along a refinement, with the sign for reordering its indices. -/
def pullC (τ : κ → ι) (φ : M →ₗ[k] N) : (Finset ι → M) →ₗ[k] (Finset κ → N) where
  toFun c s := if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0
  map_add' a b := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_add]
  map_smul' r a := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_comm (sortSign τ s) r]

end GlobalTheory.PD

namespace GlobalTheory.PD


variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E E' : Type}
  [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

open Classical in
theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_inj (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) {s : Finset κ}
    (h : Set.InjOn τ s) : pullC τ φ c s = sortSign τ s • φ (c (s.image τ)) := by
  rw [pullC_apply, if_pos h]

theorem pullC_ninj (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) {s : Finset κ}
    (h : ¬ Set.InjOn τ s) : pullC τ φ c s = 0 := by
  rw [pullC_apply, if_neg h]

private theorem cubeSign_eq_prod' {α : Type} [LinearOrder α] (t : Finset α) (i : α) :
    cubeSign t i = ∏ y ∈ t, if y < i then (-1 : ℤ) else 1 := by
  change (-1 : ℤ) ^ (t.filter (· < i)).card = _
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private theorem sortSign_eq_sortSign_erase_mul {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) :
    sortSign τ s = sortSign τ (s.erase j) * ((∏ y ∈ s, if j < y ∧ τ y < τ j then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < j ∧ τ j < τ y then (-1 : ℤ) else 1) := by
  rw [sortSign.eq_1, sortSign.eq_1, ← Finset.mul_prod_erase s _ hj]
  have h1 : ∀ a ∈ s.erase j, (∏ b ∈ s, if a < b ∧ τ b < τ a then (-1 : ℤ) else 1) =
      (if a < j ∧ τ j < τ a then -1 else 1) * ∏ b ∈ s.erase j, if a < b ∧ τ b < τ a then -1 else 1 :=
    fun a _ => (Finset.mul_prod_erase s _ hj).symm
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  have h2 : (∏ a ∈ s.erase j, if a < j ∧ τ j < τ a then (-1 : ℤ) else 1) =
      ∏ a ∈ s, if a < j ∧ τ j < τ a then -1 else 1 := by
    rw [← Finset.mul_prod_erase s _ hj]
    simp
  rw [h2]
  ring

private theorem sortSign_mul_cubeSign_image {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) (hinj : Set.InjOn τ s) :
    sortSign τ s * cubeSign (s.image τ) (τ j) = cubeSign s j * sortSign τ (s.erase j) := by
  rw [sortSign_eq_sortSign_erase_mul τ hj, cubeSign_eq_prod', cubeSign_eq_prod',
    Finset.prod_image (fun x hx y hy h => hinj hx hy h)]
  have key : ∀ y ∈ s, ((if j < y ∧ τ y < τ j then (-1 : ℤ) else 1) *
      (if y < j ∧ τ j < τ y then -1 else 1)) * (if τ y < τ j then -1 else 1) =
      if y < j then -1 else 1 := by
    intro y hy
    by_cases hyj : y = j
    · subst hyj
      simp
    have hne : τ y ≠ τ j := fun e => hyj (hinj hy hj e)
    split_ifs <;> simp_all <;> order
  rw [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finset.prod_congr rfl key]
  ring

private theorem prod_mul_prod_eq_one_of_sq_one {β : Type} {s : Finset β} (f : β → ℤ) (hf : ∀ y, f y * f y = 1) :
    (∏ y ∈ s, f y) * ∏ y ∈ s, f y = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun y _ => hf y

private theorem cubeSign_mul_sortSign_erase_eq_neg_of_collide {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (he : τ a = τ b)
    (hinj : Set.InjOn τ (s.erase b)) :
    cubeSign s a * sortSign τ (s.erase a) = -(cubeSign s b * sortSign τ (s.erase b)) := by
  have sq : ∀ (P : β → Prop) [DecidablePred P],
      (∏ y ∈ s, if P y then (-1 : ℤ) else 1) * (∏ y ∈ s, if P y then (-1 : ℤ) else 1) = 1 :=
    fun P _ => prod_mul_prod_eq_one_of_sq_one _ fun y => by split_ifs <;> norm_num
  have key : cubeSign s b * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < b ∧ τ b < τ y then (-1 : ℤ) else 1) =
      -(cubeSign s a * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < a ∧ τ a < τ y then (-1 : ℤ) else 1)) := by
    rw [cubeSign_eq_prod', cubeSign_eq_prod', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have pt : ∀ y ∈ s, (if y < b then (-1 : ℤ) else 1) * ((if b < y ∧ τ y < τ b then -1 else 1) *
        (if y < b ∧ τ b < τ y then -1 else 1)) =
        (if y = a then -1 else 1) * ((if y < a then (-1 : ℤ) else 1) *
        ((if a < y ∧ τ y < τ a then -1 else 1) * (if y < a ∧ τ a < τ y then -1 else 1))) := by
      intro y hy
      by_cases hya : y = a
      · subst hya
        simp [hab, he]
      by_cases hyb : y = b
      · subst hyb
        simp [hya, he, lt_asymm hab]
      have hne : τ y ≠ τ a := fun e =>
        hya (hinj (Finset.mem_erase.2 ⟨hyb, hy⟩) (Finset.mem_erase.2 ⟨hab.ne, ha⟩) e)
      rw [← he]
      rcases lt_or_gt_of_ne hne with h3 | h3 <;> rcases lt_or_gt_of_ne hya with h1 | h1 <;>
        rcases lt_or_gt_of_ne hyb with h2 | h2
      all_goals first
        | (exfalso; order)
        | simp [h1, h2, h3, hya, hyb, lt_asymm h1, lt_asymm h2, lt_asymm h3]
    rw [Finset.prod_congr rfl pt, Finset.prod_mul_distrib, Finset.prod_ite_eq' s a, if_pos ha]
    ring
  have eA := sortSign_eq_sortSign_erase_mul τ ha
  have eB := sortSign_eq_sortSign_erase_mul τ hb
  have s1 := sq (fun y => a < y ∧ τ y < τ a)
  have s2 := sq (fun y => y < a ∧ τ a < τ y)
  have s3 := sq (fun y => b < y ∧ τ y < τ b)
  have s4 := sq (fun y => y < b ∧ τ b < τ y)
  linear_combination (-(cubeSign s a) * sortSign τ (s.erase a)) * s1
    + (-(cubeSign s a) * sortSign τ (s.erase a) * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      (∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1))) * s2
    + (-(cubeSign s a) * ((∏ y ∈ s, if a < y ∧ τ y < τ a then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < a ∧ τ a < τ y then (-1 : ℤ) else 1)) * eA
    + (-(cubeSign s b) * sortSign τ (s.erase b)) * s3
    + (-(cubeSign s b) * sortSign τ (s.erase b) * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      (∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1))) * s4
    + (-(cubeSign s b) * ((∏ y ∈ s, if b < y ∧ τ y < τ b then (-1 : ℤ) else 1) *
      ∏ y ∈ s, if y < b ∧ τ b < τ y then (-1 : ℤ) else 1)) * eB
    + sortSign τ s * key

private theorem injOn_erase_of_injOn_erase_of_eq {α β : Type} [LinearOrder β] (τ : β → α) {s : Finset β} {a b : β}
    (ha : a ∈ s) (hab : a ≠ b) (he : τ a = τ b) (h : Set.InjOn τ ↑(s.erase b)) :
    Set.InjOn τ ↑(s.erase a) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_erase] at hx hy
  by_cases hxb : x = b
  · by_cases hyb : y = b
    · rw [hxb, hyb]
    · subst hxb
      exact absurd (h (Finset.mem_erase.2 ⟨hyb, hy.2⟩) (Finset.mem_erase.2 ⟨hab, ha⟩)
        (hxy.symm.trans he.symm)) hy.1
  · by_cases hyb : y = b
    · subst hyb
      exact absurd (h (Finset.mem_erase.2 ⟨hxb, hx.2⟩) (Finset.mem_erase.2 ⟨hab, ha⟩)
        (hxy.trans he.symm)) hx.1
    · exact h (Finset.mem_erase.2 ⟨hxb, hx.2⟩) (Finset.mem_erase.2 ⟨hyb, hy.2⟩) hxy

private theorem image_erase_eq_erase_image_of_injOn {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {j : β} (hj : j ∈ s) (hinj : Set.InjOn τ s) :
    (s.image τ).erase (τ j) = (s.erase j).image τ := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨fun e => hx (by rw [e]), hy⟩, rfl⟩
  · rintro ⟨y, ⟨hyj, hy⟩, rfl⟩
    exact ⟨fun e => hyj (hinj hy hj e), y, hy, rfl⟩

private theorem image_erase_eq_of_eq_apply {α β : Type} [LinearOrder α] [LinearOrder β] (τ : β → α) {s : Finset β}
    {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (he : τ a = τ b) :
    (s.erase a).image τ = (s.erase b).image τ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hya, hy⟩, rfl⟩
    by_cases hyb : y = b
    · exact ⟨a, ⟨hab, ha⟩, by rw [hyb, he]⟩
    · exact ⟨y, ⟨hyb, hy⟩, rfl⟩
  · rintro ⟨y, ⟨hyb, hy⟩, rfl⟩
    by_cases hya : y = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hya, he]⟩
    · exact ⟨y, ⟨hya, hy⟩, rfl⟩

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (deltaL k ι E c) = deltaL k κ E' (pullC τ φ c) := by
  funext s
  rw [pullC_apply]
  simp only [deltaL_apply]
  split_ifs with hinj
  · rw [map_sum, Finset.smul_sum, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hinj' : Set.InjOn τ ↑(s.erase j) := hinj.mono (Finset.coe_subset.2 (Finset.erase_subset j s))
    rw [pullC_inj τ φ c hinj', map_zsmul, smul_smul, smul_smul, sortSign_mul_cubeSign_image τ hj hinj,
      image_erase_eq_erase_image_of_injOn τ hj hinj]
  · have hcol : ∃ a ∈ s, ∃ b ∈ s, a < b ∧ τ a = τ b := by
      by_contra hno
      push Not at hno
      apply hinj
      intro x hx y hy hxy
      rcases lt_trichotomy x y with h | h | h
      · exact absurd hxy (hno x hx y hy h)
      · exact h
      · exact absurd hxy.symm (hno y hy x hx h)
    obtain ⟨a, ha, b, hb, hab, he⟩ := hcol
    rw [Finset.sum_eq_add_of_mem a b ha hb hab.ne ?_]
    · by_cases hia : Set.InjOn τ ↑(s.erase a)
      · have hib : Set.InjOn τ ↑(s.erase b) := injOn_erase_of_injOn_erase_of_eq τ hb hab.ne' he.symm hia
        rw [pullC_inj τ φ c hia, pullC_inj τ φ c hib, smul_smul, smul_smul,
          image_erase_eq_of_eq_apply τ ha hb hab.ne he, cubeSign_mul_sortSign_erase_eq_neg_of_collide τ ha hb hab he hib, neg_smul,
          neg_add_cancel]
      · have hib : ¬ Set.InjOn τ ↑(s.erase b) := fun h => hia (injOn_erase_of_injOn_erase_of_eq τ ha hab.ne he h)
        rw [pullC_ninj τ φ c hia, pullC_ninj τ φ c hib, smul_zero, smul_zero, add_zero]
    · intro j hj hjab
      rw [pullC_ninj τ φ c, smul_zero]
      intro h
      exact hab.ne (h (Finset.mem_erase.2 ⟨hjab.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hjab.2.symm, hb⟩) he)


end GlobalTheory.PD

