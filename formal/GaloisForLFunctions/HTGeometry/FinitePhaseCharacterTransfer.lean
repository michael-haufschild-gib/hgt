import GaloisForLFunctions.HTGeometry.MultilinearEvaluationUniformity
import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# Transfer of character means from continuous phases to cubic eighth-root phases

A degree-at-most-`m` multilinear phase seed assigns to each Boolean point the eighth root of unity
determined by the value of the polynomial there.  A character of the phase vector whose frequency
has small support and small entries has mean zero unless the frequency vanishes, exactly as on the
continuous phase torus: the support is small enough for the evaluation vector to be uniform, and the
entries are small enough that a nonzero integer frequency stays nonzero modulo eight.  Consequently
every character combination has the same mean in the finite and the continuous phase model.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Evaluation

/-- The value at a Boolean point of the multilinear polynomial with the given coefficients. -/
def boolEval {R : Type*} [CommRing R] {m : ℕ} (c : MonLe ι m → R) (a : ι → Bool) : R :=
  ∑ S, (if ∀ i ∈ S.1, a i = true then (1 : R) else 0) * c S

theorem mulVec_evalMatrix_eq_boolEval {R : Type*} [CommRing R] {k m : ℕ}
    (x : Fin k → (ι → Bool)) (c : MonLe ι m → R) (j : Fin k) :
    (reedMullerEvalMatrix R m x *ᵥ c) j = boolEval c (x j) := rfl

end Evaluation

section Character

theorem addChar_map_finsetSum {A R : Type*} [AddCommGroup A] [CommMonoid R] (ψ : AddChar A R)
    {κ : Type*} (s : Finset κ) (f : κ → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

/-- The eighth-root phase character of a frequency vector on Boolean points. -/
def charFinite {m : ℕ} (n : (ι → Bool) → ℤ) (c : MonLe ι m → ZMod 8) : ℂ :=
  ZMod.stdAddChar (∑ a, ((n a : ℤ) : ZMod 8) * boolEval c a)

theorem charFinite_zero {m : ℕ} (c : MonLe ι m → ZMod 8) :
    charFinite (0 : (ι → Bool) → ℤ) c = 1 := by
  rw [charFinite]
  simp

/-- **Mean of an eighth-root phase character.**  A frequency with small support and entries that
are nonzero modulo eight has mean zero unless it vanishes. -/
theorem sum_charFinite {m : ℕ} (n : (ι → Bool) → ℤ)
    (hsupp : (Finset.univ.filter fun a : ι → Bool => n a ≠ 0).card < 2 ^ (m + 1))
    (hbound : ∀ a, ((n a : ℤ) : ZMod 8) = 0 → n a = 0) :
    (∑ c : MonLe ι m → ZMod 8, charFinite n c) =
      (Fintype.card (MonLe ι m → ZMod 8) : ℂ) * (if n = 0 then 1 else 0) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp [charFinite_zero]
  · rw [if_neg hn, mul_zero]
    set s : Finset (ι → Bool) := Finset.univ.filter fun a : ι → Bool => n a ≠ 0 with hs
    set k : ℕ := s.card with hkdef
    set x : Fin k → (ι → Bool) := fun i => ((s.equivFin.symm i : {a // a ∈ s}) : ι → Bool) with hx
    have hxinj : Function.Injective x := by
      intro i j hij
      exact s.equivFin.symm.injective (Subtype.ext hij)
    have hxmem : ∀ i, x i ∈ s := fun i => (s.equivFin.symm i).2
    have hred : ∀ c : MonLe ι m → ZMod 8,
        (∑ a, ((n a : ℤ) : ZMod 8) * boolEval c a) =
          ∑ i : Fin k, ((n (x i) : ℤ) : ZMod 8) *
            (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c) i := by
      intro c
      have h1 : (∑ i : Fin k, ((n (x i) : ℤ) : ZMod 8) * boolEval c (x i)) =
          ∑ b : {a // a ∈ s}, ((n (b : ι → Bool) : ℤ) : ZMod 8) * boolEval c (b : ι → Bool) :=
        Equiv.sum_comp (s.equivFin.symm)
          (fun b : {a // a ∈ s} => ((n (b : ι → Bool) : ℤ) : ZMod 8) * boolEval c (b : ι → Bool))
      have h2 : (∑ b : {a // a ∈ s}, ((n (b : ι → Bool) : ℤ) : ZMod 8) *
          boolEval c (b : ι → Bool)) =
          ∑ a ∈ s, ((n a : ℤ) : ZMod 8) * boolEval c a :=
        Finset.sum_coe_sort s (fun a : ι → Bool => ((n a : ℤ) : ZMod 8) * boolEval c a)
      have h3 : (∑ a ∈ s, ((n a : ℤ) : ZMod 8) * boolEval c a) =
          ∑ a, ((n a : ℤ) : ZMod 8) * boolEval c a := by
        refine Finset.sum_subset (Finset.subset_univ s) fun a _ ha => ?_
        have hna : n a = 0 := by
          by_contra hcon
          exact ha (by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcon⟩)
        rw [hna]
        simp
      simp only [mulVec_evalMatrix_eq_boolEval]
      rw [h1, h2, h3]
    set F : (Fin k → ZMod 8) → ℂ :=
      fun w => ZMod.stdAddChar (∑ i : Fin k, ((n (x i) : ℤ) : ZMod 8) * w i) with hF
    have hchar : ∀ c : MonLe ι m → ZMod 8,
        charFinite n c = F (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c) := by
      intro c
      rw [charFinite, hF, hred c]
    have hk : k < 2 ^ (m + 1) := hsupp
    have hsum := sum_comp_mulVec_evalMatrix hk x hxinj F
    have hzero : (∑ w : Fin k → ZMod 8, F w) = 0 := by
      have hprod : ∀ w : Fin k → ZMod 8,
          F w = ∏ i : Fin k, ZMod.stdAddChar (((n (x i) : ℤ) : ZMod 8) * w i) := by
        intro w
        rw [hF]
        exact addChar_map_finsetSum _ _ _
      have hne : s.Nonempty := by
        obtain ⟨a, ha⟩ : ∃ a : ι → Bool, n a ≠ 0 := by
          by_contra hcon
          exact hn (funext fun a => not_not.mp fun h => hcon ⟨a, h⟩)
        exact ⟨a, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩⟩
      have hkpos : 0 < k := Finset.card_pos.mpr hne
      have hpi : (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (ZMod 8))) =
          Finset.univ := by
        ext w
        simp
      have hfact : (∏ i : Fin k, ∑ b : ZMod 8,
            ZMod.stdAddChar (((n (x i) : ℤ) : ZMod 8) * b)) =
          ∑ w : Fin k → ZMod 8, ∏ i : Fin k,
            ZMod.stdAddChar (((n (x i) : ℤ) : ZMod 8) * w i) := by
        rw [Finset.prod_univ_sum, hpi]
      simp only [hprod]
      rw [← hfact]
      refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hkpos⟩ : Fin k)) ?_
      have hcne : ((n (x ⟨0, hkpos⟩) : ℤ) : ZMod 8) ≠ 0 := by
        intro hcon
        have := hbound _ hcon
        have hmem := hxmem ⟨0, hkpos⟩
        rw [hs, Finset.mem_filter] at hmem
        exact hmem.2 this
      have hshift := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod 8) ℂ))
        ((n (x ⟨0, hkpos⟩) : ℤ) : ZMod 8) (ZMod.isPrimitive_stdAddChar 8)
      rw [if_neg hcne, Nat.cast_zero] at hshift
      rw [← hshift]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_comm]
    calc (∑ c : MonLe ι m → ZMod 8, charFinite n c)
        = ∑ c : MonLe ι m → ZMod 8, F (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c) :=
          Finset.sum_congr rfl fun c _ => hchar c
      _ = _ • ∑ w : Fin k → ZMod 8, F w := hsum
      _ = 0 := by rw [hzero, smul_zero]

end Character

section Transfer

variable {κ : Type*}

/-- A finite character combination in the eighth-root phase model. -/
def trigFinite {m : ℕ} (P : Finset κ) (ν : κ → ((ι → Bool) → ℤ)) (a : κ → ℂ)
    (c : MonLe ι m → ZMod 8) : ℂ :=
  ∑ p ∈ P, a p * charFinite (ν p) c

/-- **The finite phase model has the same character means as the continuous one.** -/
theorem sum_trigFinite {m : ℕ} (P : Finset κ) (ν : κ → ((ι → Bool) → ℤ)) (a : κ → ℂ)
    (hsupp : ∀ p ∈ P,
      (Finset.univ.filter fun b : ι → Bool => ν p b ≠ 0).card < 2 ^ (m + 1))
    (hbound : ∀ p ∈ P, ∀ b, ((ν p b : ℤ) : ZMod 8) = 0 → ν p b = 0) :
    (∑ c : MonLe ι m → ZMod 8, trigFinite P ν a c) =
      (Fintype.card (MonLe ι m → ZMod 8) : ℂ) * ∑ p ∈ P with ν p = 0, a p := by
  classical
  simp only [trigFinite]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.mul_sum, sum_charFinite (ν p) (hsupp p hp) (hbound p hp)]
  by_cases h : ν p = 0
  · rw [if_pos h, if_pos h, mul_one]
    ring
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- **Equality of the finite and continuous means of a character combination.** -/
theorem average_trigFinite_eq_integral_box_trigLift {m : ℕ} (P : Finset κ)
    (ν : κ → ((ι → Bool) → ℤ)) (a : κ → ℂ)
    (hsupp : ∀ p ∈ P,
      (Finset.univ.filter fun b : ι → Bool => ν p b ≠ 0).card < 2 ^ (m + 1))
    (hbound : ∀ p ∈ P, ∀ b, ((ν p b : ℤ) : ZMod 8) = 0 → ν p b = 0) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℂ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, trigFinite P ν a c =
      ∫ y in torusBox (ι → Bool), trigLift P ν a y := by
  classical
  rw [sum_trigFinite P ν a hsupp hbound, integral_box_trigLift]
  have hcard : (Fintype.card (MonLe ι m → ZMod 8) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (MonLe ι m → ZMod 8) ≠ 0)
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Transfer

end GaloisForLFunctions.HTGeometry
