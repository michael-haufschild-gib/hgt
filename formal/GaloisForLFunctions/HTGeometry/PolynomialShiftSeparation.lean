import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite

/-!
# Separating a finite family of polynomials by a single shift

In characteristic zero a polynomial of positive degree has no nonzero period: if `h(X + d) = h`
then `d = 0`, because otherwise `h` would take the value `h(0)` at every multiple of `d`.  Hence
`c ↦ h(X − c)` is injective.

Consequently, for two polynomials of positive degree and two distinct scalars `a ≠ b`, the equation
`h₁(X − a·t) = h₂(X − b·t)` has at most one solution `t`: both sides determine
`h₁ = h₂(X − (b − a)t)`, and the shift is unique.  A finite family therefore has only finitely many
bad values of `t`, so over an infinite field one shift separates the whole family at once.

This is what makes a product of local algebras monogenic: the minimal polynomials of the shifted
generators become pairwise coprime.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {κ : Type*} [Field κ] [CharZero κ]

/-- **A polynomial of positive degree has no nonzero period.** -/
theorem eq_zero_of_comp_add_C_eq_self {h : κ[X]} (hdeg : 0 < h.natDegree) {d : κ}
    (hcomp : h.comp (X + C d) = h) : d = 0 := by
  by_contra hd
  have hstep : ∀ x : κ, h.eval (x + d) = h.eval x := by
    intro x
    have hx := congrArg (fun p : κ[X] => Polynomial.eval x p) hcomp
    simpa [Polynomial.eval_comp] using hx
  have hn : ∀ n : ℕ, h.eval ((n : κ) * d) = h.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hcast : ((n + 1 : ℕ) : κ) * d = (n : κ) * d + d := by push_cast; ring
        rw [hcast, hstep, ih]
  set p : κ[X] := h - C (h.eval 0) with hpdef
  have hroots : {x : κ | p.IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (f := fun n : ℕ => (n : κ) * d) ?_)
    · rintro x ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hpdef, Polynomial.eval_sub,
        Polynomial.eval_C]
      rw [hn n, sub_self]
    · intro a b hab
      simp only at hab
      have hc : (a : κ) = (b : κ) := mul_right_cancel₀ hd hab
      exact_mod_cast hc
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hroots
  have hconst : h = C (h.eval 0) := by
    rw [hpdef] at hp0
    exact sub_eq_zero.mp hp0
  rw [hconst, Polynomial.natDegree_C] at hdeg
  exact absurd hdeg (lt_irrefl 0)

/-- **Shifting a polynomial of positive degree is injective in the shift.** -/
theorem comp_sub_C_injective {h : κ[X]} (hdeg : 0 < h.natDegree) :
    Function.Injective (fun c : κ => h.comp (X - C c)) := by
  intro c c' hcc
  simp only at hcc
  have hcomp : h.comp (X + C (c - c')) = h := by
    have h1 := congrArg (fun p : κ[X] => p.comp (X + C c)) hcc
    simp only [Polynomial.comp_assoc] at h1
    have h2 : (X - C c).comp (X + C c) = (X : κ[X]) := by
      simp
    have h3 : (X - C c').comp (X + C c) = X + C (c - c') := by
      simp [Polynomial.sub_comp, C_sub]
      ring
    rw [h2, h3, Polynomial.comp_X] at h1
    exact h1.symm
  have hz := eq_zero_of_comp_add_C_eq_self hdeg hcomp
  exact sub_eq_zero.mp hz

theorem comp_sub_C_injective' {h : κ[X]} (hdeg : 0 < h.natDegree) {c c' : κ}
    (hcc : h.comp (X - C c) = h.comp (X - C c')) : c = c' :=
  comp_sub_C_injective hdeg hcc

/-- For two polynomials of positive degree and two distinct multipliers, the shifted equation has
at most one solution. -/
theorem shift_bad_subsingleton {h₁ h₂ : κ[X]} (hdeg : 0 < h₂.natDegree) {a b : κ} (hab : a ≠ b) :
    {t : κ | h₁.comp (X - C (a * t)) = h₂.comp (X - C (b * t))}.Subsingleton := by
  intro t ht t' ht'
  simp only [Set.mem_setOf_eq] at ht ht'
  have key : ∀ s : κ, h₁.comp (X - C (a * s)) = h₂.comp (X - C (b * s)) →
      h₁ = h₂.comp (X - C ((b - a) * s)) := by
    intro s hs
    have h1 := congrArg (fun p : κ[X] => p.comp (X + C (a * s))) hs
    simp only [Polynomial.comp_assoc] at h1
    have h2 : (X - C (a * s)).comp (X + C (a * s)) = (X : κ[X]) := by simp
    have h3 : (X - C (b * s)).comp (X + C (a * s)) = X - C ((b - a) * s) := by
      simp [Polynomial.sub_comp, C_sub, C_mul]
      ring
    rw [h2, h3, Polynomial.comp_X] at h1
    exact h1
  have e1 := key t ht
  have e2 := key t' ht'
  have : (b - a) * t = (b - a) * t' :=
    comp_sub_C_injective' hdeg (by rw [← e1, ← e2])
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  exact mul_left_cancel₀ hba this

/-- **One shift separates a finite family.** -/
theorem exists_shift_separating {ι : Type*} [Finite ι] (h : ι → κ[X])
    (hdeg : ∀ i, 0 < (h i).natDegree) (n : ι → κ) (hn : Function.Injective n) :
    ∃ t : κ, ∀ i j, i ≠ j →
      (h i).comp (X - C (n i * t)) ≠ (h j).comp (X - C (n j * t)) := by
  classical
  set Bad : Set κ := ⋃ (p : ι × ι),
    {t : κ | p.1 ≠ p.2 ∧ (h p.1).comp (X - C (n p.1 * t)) = (h p.2).comp (X - C (n p.2 * t))}
    with hBad
  have hfin : Bad.Finite := by
    rw [hBad]
    refine Set.finite_iUnion fun p => ?_
    by_cases hp : p.1 = p.2
    · refine Set.Finite.subset (Set.finite_empty) ?_
      rintro t ⟨hne, -⟩
      exact absurd hp hne
    · refine Set.Subsingleton.finite ?_
      intro t ht t' ht'
      exact shift_bad_subsingleton (hdeg p.2) (fun hc => hp (hn hc)) ht.2 ht'.2
  obtain ⟨t, ht⟩ := (hfin.infinite_compl).nonempty
  refine ⟨t, fun i j hij hc => ht ?_⟩
  rw [hBad]
  exact Set.mem_iUnion.mpr ⟨(i, j), hij, hc⟩

end GaloisForLFunctions.HTGeometry
