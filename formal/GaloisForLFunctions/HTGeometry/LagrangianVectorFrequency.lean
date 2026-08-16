import GaloisForLFunctions.HTGeometry.PauliSymplecticTransitivity

/-!
# How often a fixed label lies in a Lagrangian

A Lagrangian of the binary symplectic label space is a self-commuting subgroup of full size.  A
form-preserving additive bijection permutes the Lagrangians, so by transitivity on nonzero labels
every nonzero label lies in the same number of them.  Counting incidences between labels and
Lagrangians in two ways then gives the exact frequency: a fixed nonzero label lies in one Lagrangian
out of `2^n + 1`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- A Lagrangian: a self-commuting subgroup of the label space of full size. -/
def IsLagr (V : Finset (PauliSymp n)) : Prop :=
  (0 : PauliSymp n) ∈ V ∧ (∀ u ∈ V, ∀ v ∈ V, u + v ∈ V) ∧
    (∀ u ∈ V, ∀ v ∈ V, symForm u v = 0) ∧ V.card = 2 ^ n

instance : DecidablePred (IsLagr (n := n)) := fun _ =>
  @instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance inferInstance))

/-- The Lagrangians of the `n`-qubit label space. -/
def lagrangians (n : ℕ) : Finset (Finset (PauliSymp n)) :=
  Finset.univ.filter IsLagr

theorem mem_lagrangians {V : Finset (PauliSymp n)} : V ∈ lagrangians n ↔ IsLagr V := by
  rw [lagrangians, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

section Action

variable {T : PauliSymp n ≃ PauliSymp n}

theorem symplectic_map_zero (hadd : ∀ x y, T (x + y) = T x + T y) : T 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have h2 : T 0 - T 0 = T 0 + T 0 - T 0 := by rw [← h]
  rw [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

theorem isLagr_image (hadd : ∀ x y, T (x + y) = T x + T y)
    (hform : ∀ x y, symForm (T x) (T y) = symForm x y)
    {V : Finset (PauliSymp n)} (hV : IsLagr V) : IsLagr (V.image T) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← symplectic_map_zero hadd]
    exact Finset.mem_image_of_mem _ hV.1
  · intro u hu v hv
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [← hadd]
    exact Finset.mem_image_of_mem _ (hV.2.1 a ha b hb)
  · intro u hu v hv
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [hform]
    exact hV.2.2.1 a ha b hb
  · rw [Finset.card_image_of_injective _ T.injective]
    exact hV.2.2.2

theorem symm_map_add (hadd : ∀ x y, T (x + y) = T x + T y) (a b : PauliSymp n) :
    T.symm (a + b) = T.symm a + T.symm b := by
  refine T.injective ?_
  rw [Equiv.apply_symm_apply, hadd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem symm_map_form (hform : ∀ x y, symForm (T x) (T y) = symForm x y) (a b : PauliSymp n) :
    symForm (T.symm a) (T.symm b) = symForm a b := by
  have h := hform (T.symm a) (T.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

/-- **A symplectic bijection matches the Lagrangians through a fixed label.** -/
theorem card_filter_mem_eq (hadd : ∀ x y, T (x + y) = T x + T y)
    (hform : ∀ x y, symForm (T x) (T y) = symForm x y) (u : PauliSymp n) :
    ((lagrangians n).filter fun V => u ∈ V).card =
      ((lagrangians n).filter fun V => T u ∈ V).card := by
  classical
  have himg : ((lagrangians n).filter fun V => u ∈ V).image (fun V => V.image T) =
      (lagrangians n).filter fun V => T u ∈ V := by
    ext W
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨V, hV, rfl⟩
      refine ⟨mem_lagrangians.mpr (isLagr_image hadd hform (mem_lagrangians.mp hV.1)),
        Finset.mem_image_of_mem _ hV.2⟩
    · rintro ⟨hW, huW⟩
      refine ⟨W.image T.symm, ⟨mem_lagrangians.mpr
          (isLagr_image (symm_map_add hadd) (symm_map_form hform) (mem_lagrangians.mp hW)), ?_⟩,
        ?_⟩
      · have := Finset.mem_image_of_mem (⇑T.symm) huW
        rwa [Equiv.symm_apply_apply] at this
      · rw [Finset.image_image]
        refine (Finset.image_congr ?_).trans Finset.image_id
        intro x _
        exact Equiv.apply_symm_apply T x
  rw [← himg, Finset.card_image_of_injective _ (Finset.image_injective T.injective)]

end Action

/-- **Every nonzero label lies in the same number of Lagrangians.** -/
theorem card_filter_mem_eq_of_ne_zero {u v : PauliSymp n} (hu : u ≠ 0) (hv : v ≠ 0) :
    ((lagrangians n).filter fun V => u ∈ V).card =
      ((lagrangians n).filter fun V => v ∈ V).card := by
  obtain ⟨T, hadd, hform, hTu⟩ := exists_symplectic_equiv_map hu hv
  rw [card_filter_mem_eq hadd hform u, hTu]

section Counting

theorem card_pauliSymp : Fintype.card (PauliSymp n) = 4 ^ n := by
  simp [PauliSymp]

/-- **Incidence double count.** -/
theorem sum_card_filter_mem :
    (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0,
        ((lagrangians n).filter fun V => v ∈ V).card) =
      (lagrangians n).card * (2 ^ n - 1) := by
  classical
  have h1 : ∀ v : PauliSymp n, ((lagrangians n).filter fun V => v ∈ V).card
      = ∑ V ∈ lagrangians n, (if v ∈ V then 1 else 0) := by
    intro v
    rw [Finset.sum_boole]
    simp
  have h2 : ∀ V : Finset (PauliSymp n),
      ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ V).card
      = ∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, (if v ∈ V then 1 else 0) := by
    intro V
    rw [Finset.sum_boole]
    simp
  have hswap : (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0,
      ((lagrangians n).filter fun V => v ∈ V).card) =
      ∑ V ∈ lagrangians n,
        ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ V).card := by
    simp only [h1, h2]
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ V ∈ lagrangians n,
      ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ V).card =
        2 ^ n - 1 := by
    intro V hV
    have hL := mem_lagrangians.mp hV
    have hset : ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ V) =
        V.erase 0 := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hset, Finset.card_erase_of_mem hL.1, hL.2.2.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

/-- **The exact Lagrangian frequency of a nonzero label.** -/
theorem card_filter_mem_mul_succ {v : PauliSymp n} (hv : v ≠ 0) :
    ((lagrangians n).filter fun V => v ∈ V).card * (2 ^ n + 1) = (lagrangians n).card := by
  classical
  set c : ℕ := ((lagrangians n).filter fun V => v ∈ V).card with hc
  have hnpos : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    subst hn0
    exact hv (funext fun i => absurd i.2 (by omega))
  have hnz : (Finset.univ.filter fun w : PauliSymp n => w ≠ 0).card = 4 ^ n - 1 := by
    have hcompl : (Finset.univ.filter fun w : PauliSymp n => w ≠ 0) =
        (Finset.univ : Finset (PauliSymp n)).erase 0 := by
      ext w
      simp [Finset.mem_erase]
    rw [hcompl, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_pauliSymp]
  have hall : ∀ w ∈ Finset.univ.filter fun w : PauliSymp n => w ≠ 0,
      ((lagrangians n).filter fun V => w ∈ V).card = c := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact card_filter_mem_eq_of_ne_zero hw.2 hv
  have hconst : (∑ w ∈ Finset.univ.filter fun w : PauliSymp n => w ≠ 0,
      ((lagrangians n).filter fun V => w ∈ V).card) = (4 ^ n - 1) * c := by
    rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, hnz]
  have hdouble := sum_card_filter_mem (n := n)
  rw [hconst] at hdouble
  have hfact : (4 : ℕ) ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega⟩
    rw [h4, hm]
    have hl : (m + 1) * (m + 1) - 1 = m * m + 2 * m := by
      have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      omega
    have hr : ((m + 1) - 1) * ((m + 1) + 1) = m * m + 2 * m := by
      have h1 : (m + 1) - 1 = m := by omega
      rw [h1]
      ring
    rw [hl, hr]
  rw [hfact] at hdouble
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  have hcancel : c * (2 ^ n + 1) = (lagrangians n).card := by
    have hle : (2 ^ n - 1) * ((2 ^ n + 1) * c) = (2 ^ n - 1) * (lagrangians n).card := by
      calc (2 ^ n - 1) * ((2 ^ n + 1) * c) = (2 ^ n - 1) * (2 ^ n + 1) * c := by ring
        _ = (lagrangians n).card * (2 ^ n - 1) := hdouble
        _ = (2 ^ n - 1) * (lagrangians n).card := by ring
    have hres := Nat.eq_of_mul_eq_mul_left hpos hle
    rw [mul_comm]
    exact hres
  exact hcancel

end Counting

end GaloisForLFunctions.HTGeometry
