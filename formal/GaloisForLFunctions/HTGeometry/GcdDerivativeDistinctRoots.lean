import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The derivative gcd measures multiplicity

Over an algebraically closed field of characteristic zero the greatest common divisor of a nonzero
polynomial and its derivative has root multiplicity one less than the polynomial at every point.
Summing over the divisor gives

`deg gcd (W, W') + #{distinct roots of W} = deg W`,

so the complementary degree is exactly the distinct-root census.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]

/-- Root multiplicity of the derivative gcd is one less than that of the polynomial. -/
theorem rootMultiplicity_gcd_derivative (W : K[X]) (hW : W ≠ 0) (a : K) :
    rootMultiplicity a (EuclideanDomain.gcd W (derivative W)) = rootMultiplicity a W - 1 := by
  classical
  set g := EuclideanDomain.gcd W (derivative W) with hg
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, EuclideanDomain.gcd_eq_zero_iff] at h
    exact hW h.1
  set m := rootMultiplicity a W with hm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `a` is not a root of `W`, hence not a root of `g`
    have hnot : ¬ W.IsRoot a := by
      intro hroot
      have := (rootMultiplicity_pos hW).2 hroot
      omega
    have : ¬ g.IsRoot a := by
      intro hroot
      exact hnot (((dvd_iff_isRoot).2 hroot).trans (EuclideanDomain.gcd_dvd_left _ _)
        |> fun hdvd => (dvd_iff_isRoot).1 hdvd)
    have : rootMultiplicity a g = 0 := by
      by_contra hne
      exact this ((rootMultiplicity_pos hg0).1 (Nat.pos_of_ne_zero hne))
    omega
  · have hroot : W.IsRoot a := (rootMultiplicity_pos hW).1 hmpos
    have hderiv : rootMultiplicity a (derivative W) = m - 1 :=
      derivative_rootMultiplicity_of_root hroot
    have hle : rootMultiplicity a g ≤ m - 1 := by
      rcases eq_or_ne (derivative W) 0 with hd | hd
      · have : m = 1 := by
          have hdeg : W.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hd
          have := card_roots' W
          have hle' : rootMultiplicity a W ≤ W.natDegree := rootMultiplicity_le_natDegree W a
          omega
        omega
      · have := (le_rootMultiplicity_iff hd).2
          (((pow_rootMultiplicity_dvd (derivative W) a)).mp' rfl)
        exact le_trans (rootMultiplicity_le_rootMultiplicity_of_dvd hd
          (EuclideanDomain.gcd_dvd_right W (derivative W))) (by omega)
    have hge : m - 1 ≤ rootMultiplicity a g := by
      have hdvdW : (X - C a) ^ (m - 1) ∣ W :=
        dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1)) (pow_rootMultiplicity_dvd W a)
      have hdvdD : (X - C a) ^ (m - 1) ∣ derivative W := by
        rcases eq_or_ne (derivative W) 0 with hd | hd
        · simp [hd]
        · rw [← hderiv]; exact pow_rootMultiplicity_dvd _ _
      have hdvdg : (X - C a) ^ (m - 1) ∣ g :=
        EuclideanDomain.dvd_gcd hdvdW hdvdD
      exact (le_rootMultiplicity_iff hg0).2 hdvdg
    omega

end GaloisForLFunctions.HTGeometry
