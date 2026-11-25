import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.RegularStalkFunctions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.LinearCombination

/-! Affine gluing and reconstruction of a generating algebra from principal opens. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

def van (B : Subring (Fn Z)) (W : Z.Opens) : Ideal B where
  carrier := {b | ∀ z ∈ W, b.1 z = 0}
  add_mem' := fun {a b} ha hb z hz => by
    show a.1 z + b.1 z = 0
    rw [ha z hz, hb z hz, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c a ha z hz => by
    show c.1 z * a.1 z = 0
    rw [ha z hz, mul_zero]

/-- Generation and affineness descend from a principal open cover. -/
theorem local_global {W : Z.Opens} (B : Subring (Fn Z)) (hB : B ≤ Reg W) {T : Type} (w : T → B)
    (hw : van B W ⊔ Ideal.span (Set.range w) = ⊤) (O : T → Z.Opens) (hO : ∀ t, IsLoc (O t) W (w t).1)
    (haff : ∀ t, IsAffineOpen (O t)) (hgen : ∀ t, Gen (O t) (insert (inv (w t).1) B)) :
    IsAffineOpen W ∧ Gen W B := by
  choose r hr using fun b : B => hB b.2
  let ρ : B →+* Γ(Z, W) :=
    { toFun := r
      map_one' := sec_ext fun z hz => by rw [hr, map_one]; rfl
      map_mul' := fun a b => sec_ext fun z hz => by rw [map_mul, hr, hr, hr]; rfl
      map_zero' := sec_ext fun z hz => by rw [hr, map_zero]; rfl
      map_add' := fun a b => sec_ext fun z hz => by rw [map_add, hr, hr, hr]; rfl }
  have hW : IsAffineOpen W := by
    refine isAffineOpen_of_isAffineOpen_basicOpen W (Set.range fun t => ρ (w t)) ?_ ?_
    · have := congrArg (Ideal.map ρ) hw
      rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
        (Ideal.map_eq_bot_iff_le_ker ρ).2 (fun b hb => sec_ext fun z hz => (hr b z hz).trans
          ((hb z hz).trans (map_zero _).symm)), bot_sup_eq] at this
      exact this
    · rintro _ ⟨t, rfl⟩
      have := haff t
      rwa [(hO t).eq_basicOpen (hr (w t))] at this
  refine ⟨hW, fun F hF => ?_⟩
  let J : Ideal B :=
    { carrier := {b | ∃ b' : B, ∀ z ∈ W, b.1 z * F z = b'.1 z}
      add_mem' := fun {a b} ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' + b', fun z hz => by
        show (a.1 z + b.1 z) * F z = a'.1 z + b'.1 z
        rw [add_mul, ha z hz, hb z hz]⟩
      zero_mem' := ⟨0, fun z _ => zero_mul _⟩
      smul_mem' := fun c a ⟨a', ha⟩ => ⟨c * a', fun z hz => by
        show (c.1 z * a.1 z) * F z = c.1 z * a'.1 z
        rw [mul_assoc, ha z hz]⟩ }
  have hJ : J.radical = ⊤ := by
    rw [eq_top_iff, ← hw, sup_le_iff, Ideal.span_le]
    refine ⟨fun b hb => Ideal.le_radical ⟨0, fun z hz => by rw [hb z hz, zero_mul]; rfl⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨b, hb, e⟩ := hgen t F (reg_mono (hO t).le hF)
    obtain ⟨n, b', e'⟩ : ∃ n : ℕ, ∃ b' : B, ∀ z ∈ O t, (w t).1 z ^ n * b z = b'.1 z := by
      clear e
      induction hb using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact ⟨1, 1, fun z hz => by rw [pow_one]; exact Ring.mul_inverse_cancel _ ((hO t).unit hz)⟩
        · exact ⟨0, ⟨x, hx⟩, fun z hz => by rw [pow_zero, one_mul]⟩
      | zero => exact ⟨0, 0, fun _ _ => mul_zero _⟩
      | one => exact ⟨0, 1, fun _ _ => by rw [pow_zero, one_mul]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨n, a, e⟩ := hx
        obtain ⟨m, b, e'⟩ := hy
        refine ⟨n + m, w t ^ m * a + w t ^ n * b, fun z hz => ?_⟩
        show (w t).1 z ^ (n + m) * (x z + y z) = (w t).1 z ^ m * a.1 z + (w t).1 z ^ n * b.1 z
        rw [← e z hz, ← e' z hz]; ring
      | neg x _ hx =>
        obtain ⟨n, a, e⟩ := hx
        refine ⟨n, -a, fun z hz => ?_⟩
        show (w t).1 z ^ n * (-x z) = -a.1 z
        rw [← e z hz]; ring
      | mul x y _ _ hx hy =>
        obtain ⟨n, a, e⟩ := hx
        obtain ⟨m, b, e'⟩ := hy
        refine ⟨n + m, a * b, fun z hz => ?_⟩
        show (w t).1 z ^ (n + m) * (x z * y z) = a.1 z * b.1 z
        rw [← e z hz, ← e' z hz]; ring
    obtain ⟨m, hm⟩ := kill hW.isCompact (hO t) (hB (w t).2)
      (sub_mem (mul_mem (pow_mem (hB (w t).2) n) hF) (hB b'.2)) (fun z hz => by
        show (w t).1 z ^ n * F z - b'.1 z = 0
        rw [e z hz, e' z hz, sub_self])
    refine ⟨m + n, w t ^ m * b', fun z hz => ?_⟩
    have := hm z hz
    show (w t).1 z ^ (m + n) * F z = (w t).1 z ^ m * b'.1 z
    change (w t).1 z ^ m * ((w t).1 z ^ n * F z - b'.1 z) = 0 at this
    linear_combination this
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at hJ
  obtain ⟨b, hb⟩ := hJ
  exact ⟨b.1, Subring.subset_closure b.2, fun z hz => (one_mul _).symm.trans (hb z hz)⟩

/-- A determinant-trick relation with constant term one annihilates powers of the generators. -/
theorem exists_one_add_kill {B : Type} [CommRing B] {T : Type} [Finite T] (u : T → B) (K : Ideal B)
    (h : ∀ t, ∃ e : ℕ, u t ^ e ∈ K ⊔ Ideal.span (Set.range u) ^ (e + 1)) :
    ∃ c, c - 1 ∈ Ideal.span (Set.range u) ∧ ∃ d : ℕ, ∀ t, c * u t ^ d ∈ K := by
  classical
  set I := Ideal.span (Set.range u) with hI
  have step : ∀ J ≤ I, ∀ J' ≤ I, ∀ d k m : ℕ, J ^ d ≤ K ⊔ I ^ (d + 1) → d ≤ k → J ^ k * J' ^ m ≤ K ⊔ I ^ (k + m + 1) := by
    intro J hJ J' hJ' d k m hd hk
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk
    calc J ^ (d + c) * J' ^ m = J ^ d * (J ^ c * J' ^ m) := by ring
      _ ≤ (K ⊔ I ^ (d + 1)) * (I ^ c * I ^ m) :=
        Ideal.mul_mono hd (Ideal.mul_mono (Ideal.pow_right_mono hJ _) (Ideal.pow_right_mono hJ' _))
      _ ≤ _ := by
        rw [Ideal.sup_mul]
        exact sup_le_sup Ideal.mul_le_right (le_of_eq (by ring))
  have key : ∀ s : Finset T, ∃ d : ℕ, Ideal.span (u '' s) ^ d ≤ K ⊔ I ^ (d + 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert t s _ ih =>
      obtain ⟨d, hd⟩ := ih
      obtain ⟨e, he⟩ := h t
      have h₁ : Ideal.span {u t} ≤ I := Ideal.span_mono (by simp)
      have h₂ : Ideal.span (u '' s) ≤ I := Ideal.span_mono (Set.image_subset_range _ _)
      refine ⟨e + d, ?_⟩
      rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, ← Ideal.add_eq_sup, add_pow,
        Ideal.sum_eq_sup, Finset.sup_le_iff]
      intro k hk
      have hk' : k ≤ e + d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      refine Ideal.mul_le_right.trans ?_
      by_cases hke : e ≤ k
      · have := step _ h₁ _ h₂ e k (e + d - k) (by
          rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]; exact he) hke
        rwa [Nat.add_sub_cancel' hk'] at this
      · have := step _ h₂ _ h₁ d (e + d - k) k hd (by omega)
        rwa [Nat.sub_add_cancel hk', mul_comm] at this
  have := Fintype.ofFinite T
  obtain ⟨d, hd⟩ := key Finset.univ
  rw [Finset.coe_univ, Set.image_univ, ← hI] at hd
  obtain ⟨c, hc, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := I) (N := K) (N' := I ^ d)
    (P := I ^ d) (Submodule.FG.pow (Submodule.fg_span (Set.finite_range u)) d) le_rfl (by
      rw [Ideal.smul_eq_mul, ← pow_succ']; exact hd)
  exact ⟨c, hc, d, fun t => hle (Submodule.smul_mem_pointwise_smul _ c _
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self t)) d))⟩

end GlobalTheory.AmpleLocal
