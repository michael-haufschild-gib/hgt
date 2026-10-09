import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Exact homogeneous components under positive-degree substitution

Substitution by forms of one positive degree separates the input homogeneous
components. This supplies the component recovery needed to apply the paper's
Rees coefficient-kernel theorem to families with polynomial relations.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {K σ ι : Type*} [CommRing K]

/-- Substitution by degree-`q` forms sends input component `n` to output component `q*n`. -/
theorem paperHomogeneousSubstitution_component
    (g : ι → MvPolynomial σ K) (q : ℕ) (hq : 0 < q)
    (hg : ∀ i, (g i).IsHomogeneous q) (p : MvPolynomial ι K) (n : ℕ) :
    MvPolynomial.homogeneousComponent (q * n) (MvPolynomial.aeval g p) =
      MvPolynomial.aeval g (MvPolynomial.homogeneousComponent n p) := by
  classical
  have he : MvPolynomial.aeval g p =
      ∑ j ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.aeval g (MvPolynomial.homogeneousComponent j p) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [he, map_sum]
  have hc (j : ℕ) : q * n = q * j ↔ n = j := by
    constructor
    · exact Nat.eq_of_mul_eq_mul_left hq
    · rintro rfl
      rfl
  calc
    _ = ∑ j ∈ Finset.range (p.totalDegree + 1),
        if n = j then MvPolynomial.aeval g (MvPolynomial.homogeneousComponent j p) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.homogeneousComponent_isHomogeneous j p).aeval g hg), hc]
    _ = if n ∈ Finset.range (p.totalDegree + 1)
        then MvPolynomial.aeval g (MvPolynomial.homogeneousComponent n p) else 0 :=
      Finset.sum_ite_eq _ _ _
    _ = _ := by
      split_ifs with hn
      · rfl
      · rw [MvPolynomial.homogeneousComponent_eq_zero n p (by simpa using hn), map_zero]

/-- Ordinary polynomial relations are exactly the homogeneous-component relations. -/
theorem paperHomogeneousSubstitution_eq_zero_iff
    (g : ι → MvPolynomial σ K) (q : ℕ) (hq : 0 < q)
    (hg : ∀ i, (g i).IsHomogeneous q) (p : MvPolynomial ι K) :
    MvPolynomial.aeval g p = 0 ↔
      ∀ n, MvPolynomial.aeval g (MvPolynomial.homogeneousComponent n p) = 0 := by
  constructor
  · intro h n
    rw [← paperHomogeneousSubstitution_component g q hq hg p n, h, map_zero]
  · intro h
    calc
      MvPolynomial.aeval g p = MvPolynomial.aeval g
          (∑ n ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent n p) := by
        rw [MvPolynomial.sum_homogeneousComponent]
      _ = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero (fun n _ => h n)

end

end GaloisForLFunctions.HTGeometry
