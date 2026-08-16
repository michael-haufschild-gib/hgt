import GaloisForLFunctions.HTGeometry.GermDivisionIndependence

/-!
# Divisibility by a distinguished polynomial is polynomial divisibility

Evaluating a polynomial over the parameter germ ring at the distinguished coordinate embeds
`ℂ{z'}[X]` into `ℂ{z}`.  The Weierstrass free-module structure says this embedding is injective in
degrees below the degree of a distinguished polynomial `W`, and — much more usefully — that
divisibility by `W` in the germ ring is exactly divisibility by `W` in the polynomial ring.

The proof is polynomial division by the monic `W` followed by the germ-level independence: the
remainder has degree below `deg W`, and a remainder that is a germ multiple of `W` must vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {n : ℕ}

/-- Evaluating a polynomial over the parameter germ ring at the distinguished coordinate. -/
noncomputable def germEval (n : ℕ) :
    Polynomial (AnalyticGerm (0 : Fin n → ℂ)) →+* AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
  Polynomial.eval₂RingHom (germTail n) (germCoord n)

@[simp]
theorem germEval_C (a : AnalyticGerm (0 : Fin n → ℂ)) :
    germEval n (Polynomial.C a) = germTail n a := by
  simp [germEval]

@[simp]
theorem germEval_X : germEval n Polynomial.X = germCoord n := by
  simp [germEval]

/-- A distinguished polynomial, as an element of the polynomial ring over the parameter germs. -/
noncomputable def distPoly (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    Polynomial (AnalyticGerm (0 : Fin n → ℂ)) :=
  Polynomial.X ^ d + lowDegreePoly α d

theorem distPoly_monic (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    (distPoly d α).Monic :=
  monic_X_pow_add (degree_lowDegreePoly_lt α d)

theorem degree_distPoly (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    (distPoly d α).degree = (d : ℕ) := by
  have h : (lowDegreePoly α d).degree < (Polynomial.X ^ d : Polynomial (AnalyticGerm (0 : Fin n → ℂ))).degree := by
    rw [degree_X_pow]
    exact degree_lowDegreePoly_lt α d
  rw [distPoly, degree_add_eq_left_of_degree_lt h, degree_X_pow]

theorem natDegree_distPoly (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    (distPoly d α).natDegree = d :=
  natDegree_eq_of_degree_eq_some (degree_distPoly d α)

/-- The evaluation of a polynomial of low degree is the corresponding germ combination. -/
theorem germEval_eq_of_degree_lt {d : ℕ} {P : Polynomial (AnalyticGerm (0 : Fin n → ℂ))}
    (hdeg : P.degree < (d : ℕ)) :
    germEval n P = ∑ j ∈ Finset.range d, germTail n (P.coeff j) * germCoord n ^ j := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [germEval]
  have hnat : P.natDegree < d := (natDegree_lt_iff_degree_lt hP).mpr hdeg
  show Polynomial.eval₂ (germTail n) (germCoord n) P = _
  exact Polynomial.eval₂_eq_sum_range' (germTail n) hnat (germCoord n)

theorem germEval_lowDegreePoly (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    germEval n (lowDegreePoly α d)
      = ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j := by
  rw [germEval_eq_of_degree_lt (degree_lowDegreePoly_lt α d)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [lowDegreePoly_coeff, if_pos (Finset.mem_range.mp hj)]

theorem germEval_distPoly (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) :
    germEval n (distPoly d α)
      = germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j := by
  rw [distPoly, map_add, map_pow, germEval_X, germEval_lowDegreePoly]

/-- The independence property of a distinguished polynomial, as a predicate. -/
def GermIndependent (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) : Prop :=
  ∀ (q : AnalyticGerm (0 : Fin (n + 1) → ℂ)) (β : ℕ → AnalyticGerm (0 : Fin n → ℂ)),
    q * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
        + ∑ j ∈ Finset.range d, germTail n (β j) * germCoord n ^ j = 0 →
      q = 0 ∧ ∀ j, j < d → β j = 0

/-- **Evaluation is injective in low degrees.** -/
theorem eq_zero_of_germEval_eq_zero {d : ℕ} {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hind : GermIndependent d α) {P : Polynomial (AnalyticGerm (0 : Fin n → ℂ))}
    (hdeg : P.degree < (d : ℕ)) (h : germEval n P = 0) : P = 0 := by
  have hrel : (0 : AnalyticGerm (0 : Fin (n + 1) → ℂ))
      * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
      + ∑ j ∈ Finset.range d, germTail n (P.coeff j) * germCoord n ^ j = 0 := by
    rw [zero_mul, zero_add, ← germEval_eq_of_degree_lt hdeg]
    exact h
  have hcoeff := (hind 0 (fun j => P.coeff j) hrel).2
  refine Polynomial.ext fun m => ?_
  rw [coeff_zero]
  by_cases hm : m < d
  · exact hcoeff m hm
  · exact (degree_lt_iff_coeff_zero P d).mp hdeg m (by omega)

/-- **Divisibility by a distinguished polynomial descends to the polynomial ring.** -/
theorem dvd_germEval_iff {d : ℕ} {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hind : GermIndependent d α) (G : Polynomial (AnalyticGerm (0 : Fin n → ℂ))) :
    germEval n (distPoly d α) ∣ germEval n G ↔ distPoly d α ∣ G := by
  constructor
  · rintro ⟨h, hh⟩
    have hmonic := distPoly_monic d α
    have hdiv : G %ₘ distPoly d α + distPoly d α * (G /ₘ distPoly d α) = G :=
      modByMonic_add_div G (distPoly d α)
    have hdegrem : (G %ₘ distPoly d α).degree < (d : ℕ) := by
      have := degree_modByMonic_lt G hmonic
      rwa [degree_distPoly] at this
    have hEval : germEval n (G %ₘ distPoly d α)
        = (h - germEval n (G /ₘ distPoly d α)) * germEval n (distPoly d α) := by
      have := congrArg (germEval n) hdiv
      rw [map_add, map_mul] at this
      rw [hh] at this
      linear_combination this
    have hrel : (-(h - germEval n (G /ₘ distPoly d α)))
        * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
        + ∑ j ∈ Finset.range d, germTail n ((G %ₘ distPoly d α).coeff j) * germCoord n ^ j = 0 := by
      rw [← germEval_eq_of_degree_lt hdegrem, hEval, ← germEval_distPoly d α]
      ring
    have hrem : G %ₘ distPoly d α = 0 := by
      refine Polynomial.ext fun m => ?_
      rw [coeff_zero]
      by_cases hm : m < d
      · exact (hind _ _ hrel).2 m hm
      · exact (degree_lt_iff_coeff_zero _ d).mp hdegrem m (by omega)
    refine ⟨G /ₘ distPoly d α, ?_⟩
    calc G = G %ₘ distPoly d α + distPoly d α * (G /ₘ distPoly d α) := hdiv.symm
      _ = distPoly d α * (G /ₘ distPoly d α) := by rw [hrem, zero_add]
  · rintro ⟨h, rfl⟩
    exact ⟨germEval n h, by rw [map_mul]⟩

end GaloisForLFunctions.HTGeometry
