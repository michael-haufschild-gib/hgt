import Mathlib
import GaloisForLFunctions.ZeroConfigurationGeometry.IntegralConfigurationsRepel

/-!
# Distinct roots of integer polynomials repel

Collide or repel for every monic integer polynomial, with no separability assumption. If
`f ∈ ℤ[X]` is monic of degree `n` and all its complex roots lie in `|z| ≤ R` (`2R ≥ 1`), any two
distinct roots satisfy

`1 ≤ |α − β| (2R)^{(n−1)² + (n−2)}`.

Mechanism. A root `α` is an algebraic integer whose integral minimal polynomial divides `f`
(`minpoly_dvd_of_mem_roots`) and is separable over `ℂ` (`separable_map_minpoly`). For distinct
roots `α, β` the polynomial `g = minpoly α` (if the minimal polynomials agree) or
`g = minpoly α · minpoly β` (if not) is monic, separable, has `α, β` among its roots, has all its
roots among those of `f`, and degree at most `n` (`exists_separable_integral_factor`); the
separable case `ZeroConfigurationGeometry.one_le_norm_sub_mul_pow` (derivative product = resultant
`∈ ℤ \ {0}`) applies to `g`.

A multiple root is a collision; everything else is held apart at a distance depending only on the
degree and the disc. This is the discreteness half of the function-field mechanism in its complete
form.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The complex image of an integer polynomial. -/
abbrev toC (f : ℤ[X]) : ℂ[X] := f.map (Int.castRingHom ℂ)

theorem toC_ne_zero {f : ℤ[X]} (hf : f.Monic) : toC f ≠ 0 := (hf.map _).ne_zero

theorem natDegree_toC (f : ℤ[X]) : (toC f).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (RingHom.injective_int _) f

theorem aeval_eq_eval_toC (f : ℤ[X]) (z : ℂ) : aeval z f = (toC f).eval z := by
  rw [aeval_def, eval_map, algebraMap_int_eq]

theorem mem_roots_toC_iff {f : ℤ[X]} (hf : f.Monic) {z : ℂ} :
    z ∈ (toC f).roots ↔ aeval z f = 0 := by
  rw [mem_roots (toC_ne_zero hf), IsRoot, aeval_eq_eval_toC]

/-- A complex root of a monic integer polynomial is an algebraic integer. -/
theorem isIntegral_of_mem_roots {f : ℤ[X]} (hf : f.Monic) {α : ℂ} (hα : α ∈ (toC f).roots) :
    IsIntegral ℤ α :=
  ⟨f, hf, by rw [← aeval_def]; exact (mem_roots_toC_iff hf).mp hα⟩

/-- The integral minimal polynomial of a root divides the polynomial. -/
theorem minpoly_dvd_of_mem_roots {f : ℤ[X]} (hf : f.Monic) {α : ℂ} (hα : α ∈ (toC f).roots) :
    minpoly ℤ α ∣ f :=
  minpoly.isIntegrallyClosed_dvd (isIntegral_of_mem_roots hf hα) ((mem_roots_toC_iff hf).mp hα)

/-- The integral minimal polynomial of an algebraic integer is separable over `ℂ`. -/
theorem separable_map_minpoly {α : ℂ} (hint : IsIntegral ℤ α) : (toC (minpoly ℤ α)).Separable := by
  have hsep : (minpoly ℚ α).Separable := (minpoly.irreducible hint.tower_top).separable
  have h := hsep.map (f := algebraMap ℚ ℂ)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, map_map] at h
  rwa [RingHom.ext_int ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) (Int.castRingHom ℂ)] at h

theorem mem_roots_toC_minpoly {α : ℂ} (hint : IsIntegral ℤ α) : α ∈ (toC (minpoly ℤ α)).roots :=
  (mem_roots_toC_iff (minpoly.monic hint)).mpr (minpoly.aeval ℤ α)

/-- An irreducible monic integer polynomial is the minimal polynomial of each of its roots. -/
theorem eq_minpoly_of_irreducible {A : ℤ[X]} (hA : Irreducible A) (hAm : A.Monic) {z : ℂ}
    (hz : z ∈ (toC A).roots) : A = minpoly ℤ z := by
  have hint := isIntegral_of_mem_roots hAm hz
  have hdvd : minpoly ℤ z ∣ A := minpoly_dvd_of_mem_roots hAm hz
  have hnu : ¬ IsUnit (minpoly ℤ z) := (minpoly.irreducible hint).not_isUnit
  obtain ⟨u, hu⟩ := hdvd
  rcases hA.isUnit_or_isUnit hu with h | h
  · exact absurd h hnu
  · exact (eq_of_monic_of_associated (minpoly.monic hint) hAm
      (associated_mul_unit_right _ _ h).symm.symm |>.trans hu.symm).symm

/-- Roots of a divisor are roots of the polynomial. -/
theorem roots_toC_le_of_dvd {g f : ℤ[X]} (hf : f.Monic) (hgf : g ∣ f) :
    (toC g).roots ≤ (toC f).roots :=
  roots.le_of_dvd (toC_ne_zero hf) (Polynomial.map_dvd _ hgf)

/-- **A separable integral factor through two distinct roots.** For distinct roots `α, β` of a
monic `f ∈ ℤ[X]` there is a monic `g ∈ ℤ[X]`, separable over `ℂ`, with `α, β` among its roots,
all its roots among those of `f`, and `deg g ≤ deg f`. -/
theorem exists_separable_integral_factor {f : ℤ[X]} (hf : f.Monic) {α β : ℂ}
    (hα : α ∈ (toC f).roots) (hβ : β ∈ (toC f).roots) :
    ∃ g : ℤ[X], g.Monic ∧ (toC g).Separable ∧ α ∈ (toC g).roots ∧ β ∈ (toC g).roots ∧
      (toC g).roots ≤ (toC f).roots := by
  classical
  have hiα := isIntegral_of_mem_roots hf hα
  have hiβ := isIntegral_of_mem_roots hf hβ
  set A := minpoly ℤ α with hAdef
  set B := minpoly ℤ β with hBdef
  have hAm : A.Monic := minpoly.monic hiα
  have hBm : B.Monic := minpoly.monic hiβ
  have hAf : (toC A).roots ≤ (toC f).roots := roots_toC_le_of_dvd hf (minpoly_dvd_of_mem_roots hf hα)
  have hBf : (toC B).roots ≤ (toC f).roots := roots_toC_le_of_dvd hf (minpoly_dvd_of_mem_roots hf hβ)
  by_cases hAB : A = B
  · refine ⟨A, hAm, separable_map_minpoly hiα, mem_roots_toC_minpoly hiα, ?_, hAf⟩
    rw [hAB]; exact mem_roots_toC_minpoly hiβ
  · have hsA := separable_map_minpoly hiα
    have hsB := separable_map_minpoly hiβ
    have hne : toC A * toC B ≠ 0 := mul_ne_zero (toC_ne_zero hAm) (toC_ne_zero hBm)
    have hroots : (toC (A * B)).roots = (toC A).roots + (toC B).roots := by
      rw [toC, Polynomial.map_mul, roots_mul hne]
    have hdisj : Disjoint (toC A).roots (toC B).roots := by
      rw [Multiset.disjoint_left]
      intro z hzA hzB
      exact hAB ((eq_minpoly_of_irreducible (minpoly.irreducible hiα) hAm hzA).trans
        (eq_minpoly_of_irreducible (minpoly.irreducible hiβ) hBm hzB).symm)
    have hnd : ((toC A).roots + (toC B).roots).Nodup :=
      Multiset.nodup_add.mpr ⟨nodup_roots hsA, nodup_roots hsB, hdisj⟩
    refine ⟨A * B, hAm.mul hBm, ?_, ?_, ?_, ?_⟩
    · have h0 : toC (A * B) ≠ 0 := by rw [toC, Polynomial.map_mul]; exact hne
      exact (nodup_roots_iff_of_splits h0 (IsAlgClosed.splits _)).mp (hroots ▸ hnd)
    · rw [hroots]; exact Multiset.mem_add.mpr (Or.inl (mem_roots_toC_minpoly hiα))
    · rw [hroots]; exact Multiset.mem_add.mpr (Or.inr (mem_roots_toC_minpoly hiβ))
    · rw [hroots, Multiset.le_iff_subset hnd]
      intro z hz
      rcases Multiset.mem_add.mp hz with h | h
      · exact Multiset.mem_of_le hAf h
      · exact Multiset.mem_of_le hBf h

/-- The degree of a polynomial is the number of its complex roots. -/
theorem card_roots_toC {f : ℤ[X]} : Multiset.card (toC f).roots = f.natDegree := by
  rw [← splits_iff_card_roots.mp (IsAlgClosed.splits (toC f)), natDegree_toC]

/-- **Distinct roots of integer polynomials repel.** Two distinct complex roots of a monic
`f ∈ ℤ[X]` of degree `n` with all roots in `|z| ≤ R`, `2R ≥ 1`, satisfy
`1 ≤ |α − β| (2R)^{(n−1)² + (n−2)}`. No separability is assumed. -/
theorem one_le_norm_sub_mul_pow_of_ne {f : ℤ[X]} (hf : f.Monic) {R : ℝ} (hR1 : 1 ≤ 2 * R)
    (hR : ∀ z ∈ (toC f).roots, ‖z‖ ≤ R) {α β : ℂ} (hα : α ∈ (toC f).roots)
    (hβ : β ∈ (toC f).roots) (hne : α ≠ β) :
    1 ≤ ‖α - β‖ * (2 * R) ^ ((f.natDegree - 1) ^ 2 + (f.natDegree - 2)) := by
  obtain ⟨g, hgm, hgs, hαg, hβg, hgf⟩ := exists_separable_integral_factor hf hα hβ
  have hdeg : g.natDegree ≤ f.natDegree := by
    rw [← card_roots_toC, ← card_roots_toC (f := f)]; exact Multiset.card_le_card hgf
  have h := ZeroConfigurationGeometry.one_le_norm_sub_mul_pow hgm hgs
    (fun z hz => hR z (Multiset.mem_of_le hgf hz)) hαg hβg hne
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 ?_) (norm_nonneg _))
  have h1 : g.natDegree - 1 ≤ f.natDegree - 1 := Nat.sub_le_sub_right hdeg 1
  have h2 : g.natDegree - 2 ≤ f.natDegree - 2 := Nat.sub_le_sub_right hdeg 2
  exact Nat.add_le_add (Nat.pow_le_pow_left h1 2) h2

/-- **Collide or repel, complete form.** Two complex roots of a monic integer polynomial of
degree `n` with all roots in `|z| ≤ R`, `2R ≥ 1`, coincide or are at distance at least
`(2R)^{−((n−1)² + n − 2)}`. -/
theorem collide_or_repel_of_monic {f : ℤ[X]} (hf : f.Monic) {R : ℝ} (hR1 : 1 ≤ 2 * R)
    (hR : ∀ z ∈ (toC f).roots, ‖z‖ ≤ R) {α β : ℂ} (hα : α ∈ (toC f).roots)
    (hβ : β ∈ (toC f).roots) :
    α = β ∨ ((2 * R) ^ ((f.natDegree - 1) ^ 2 + (f.natDegree - 2)))⁻¹ ≤ ‖α - β‖ := by
  by_cases hne : α = β
  · exact Or.inl hne
  · refine Or.inr ?_
    have hpos : 0 < (2 * R) ^ ((f.natDegree - 1) ^ 2 + (f.natDegree - 2)) :=
      pow_pos (by linarith) _
    rw [inv_le_iff_one_le_mul₀ hpos, mul_comm]
    exact one_le_norm_sub_mul_pow_of_ne hf hR1 hR hα hβ hne

end GaloisForLFunctions.ArithmeticDiscreteness
