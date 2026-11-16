import GaloisForLFunctions.HTGeometry.SignedPairingExpansion
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Homogeneity and higher jets of Pfaffian contractions

Each perfect matching uses half as many contractions as there are letters.
The signed pairing expansion therefore scales homogeneously and commutes
with coefficient maps. Along a polynomial ray, all Hasse jets are explicit;
odd words vanish before any antisymmetry assumption is needed.
-/

open scoped BigOperators
open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Exterior
variable {α K L : Type*} [CommRing K] [CommRing L]

/-- Scaling every contraction extracts one scalar per pair. -/
theorem pfaffianPairing_scale (a : K) (c : α → α → K) (l : List α) :
    pfaffianPairing K (fun i j => a * c i j) l =
      a ^ (l.length / 2) * pfaffianPairing K c l := by
  cases l with
  | nil => simp
  | cons u t =>
    cases t with
    | nil => simp [pfaffianPairing]
    | cons v s =>
      rw [pfaffianPairing, pfaffianPairing, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pfaffianPairing_scale a c ((v :: s).eraseIdx k)]
      have hlen : ((v :: s).eraseIdx k).length = s.length := by
        rw [List.length_eraseIdx_of_lt k.isLt]
        simp
      rw [hlen]
      have hpow : (u :: v :: s).length / 2 = s.length / 2 + 1 := by simp; omega
      rw [hpow, pow_succ]
      ring
termination_by l.length
decreasing_by
  have h := List.length_eraseIdx_le (v :: s) (k : ℕ)
  simp only [List.length_cons] at h ⊢
  omega

/-- The signed pairing expansion commutes with every coefficient homomorphism. -/
theorem pfaffianPairing_map (f : K →+* L) (c : α → α → K) (l : List α) :
    pfaffianPairing L (fun i j => f (c i j)) l = f (pfaffianPairing K c l) := by
  cases l with
  | nil => simp
  | cons u t =>
    rw [pfaffianPairing, pfaffianPairing, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pfaffianPairing_map f c (t.eraseIdx k)]
    simp only [map_mul, map_pow, map_neg, map_one]
termination_by l.length
decreasing_by
  have h := List.length_eraseIdx_le t (k : ℕ)
  simp only [List.length_cons] at h ⊢
  omega

private theorem pfaffianPairing_odd_aux (c : α → α → K) (N : ℕ) :
    ∀ l : List α, l.length ≤ N → l.length % 2 = 1 → pfaffianPairing K c l = 0 := by
  induction N with
  | zero =>
    intro l hlen hodd
    have : l.length = 0 := by omega
    omega
  | succ N ih =>
    intro l hlen hodd
    cases l with
    | nil => simp at hodd
    | cons u t =>
      rw [pfaffianPairing]
      apply Finset.sum_eq_zero
      intro k _
      have hle : (t.eraseIdx k).length ≤ N := by
        have he := List.length_eraseIdx_le t (k : ℕ)
        simp only [List.length_cons] at hlen
        omega
      have ho : (t.eraseIdx k).length % 2 = 1 := by
        rw [List.length_eraseIdx_of_lt k.isLt]
        simp only [List.length_cons] at hodd
        have := k.isLt
        omega
      rw [ih _ hle ho]
      simp

/-- An odd word has no perfect matching. -/
theorem pfaffianPairing_odd_word (n : ℕ) (c : α → α → K) (v : Fin (2 * n + 1) → α) :
    pfaffianPairing K c (List.ofFn v) = 0 :=
  pfaffianPairing_odd_aux c _ _ le_rfl (by simp)

/-- The Pfaffian on a scalar polynomial ray is a single homogeneous monomial. -/
theorem pfaffianPairing_polynomial_ray (c : α → α → K) (l : List α) :
    pfaffianPairing K[X] (fun i j => Polynomial.X * Polynomial.C (c i j)) l =
      Polynomial.C (pfaffianPairing K c l) * Polynomial.X ^ (l.length / 2) := by
  rw [pfaffianPairing_scale, pfaffianPairing_map]
  exact mul_comm _ _

/-- Every radial Hasse jet has the binomial coefficient dictated by the pairing degree. -/
theorem pfaffianPairing_ray_hasse (c : α → α → K) (l : List α) (j : ℕ) :
    hasseDeriv j (pfaffianPairing K[X] (fun i k => X * C (c i k)) l) =
      C (((l.length / 2).choose j : ℕ) : K) * C (pfaffianPairing K c l) *
        X ^ (l.length / 2 - j) := by
  rw [pfaffianPairing_polynomial_ray, C_mul_X_pow_eq_monomial,
    hasseDeriv_monomial, ← C_mul_X_pow_eq_monomial, map_mul]

#print axioms pfaffianPairing_scale
#print axioms pfaffianPairing_map
#print axioms pfaffianPairing_odd_word
#print axioms pfaffianPairing_polynomial_ray
#print axioms pfaffianPairing_ray_hasse

end GaloisForLFunctions.RepresentationLifting.Exterior
