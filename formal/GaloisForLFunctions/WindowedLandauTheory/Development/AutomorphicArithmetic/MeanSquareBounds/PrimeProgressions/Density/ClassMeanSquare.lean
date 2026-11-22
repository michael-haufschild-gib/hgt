import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve

/-! Character Parseval and the maximum multiplicity in each residue class. -/

open Finset

namespace QH.PrimeProgressions

/-- The character second moment is bounded by the energy in the residue fibers. -/
theorem character_square_le_fibers (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) * ‖a n‖ ^ 2 := by
  classical
  let F (b : ZMod q) : Finset ℕ := S.filter (fun n : ℕ => (n : ZMod q) = b)
  let g (b : ZMod q) := ∑ n ∈ F b, a n
  have hmaps : ∀ n ∈ S, (n : ZMod q) ∈ (univ : Finset (ZMod q)) := fun _ _ => mem_univ _
  have hexpand (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ S, a n * χ (n : ZMod q)) = ∑ b : ZMod q, χ b * g b := by
    symm
    calc
      _ = ∑ b : ZMod q, ∑ n ∈ F b, a n * χ (n : ZMod q) := by
        refine sum_congr rfl fun b _ => ?_
        dsimp only [g]
        rw [mul_sum]
        refine sum_congr rfl fun n hn => ?_
        have hb : (n : ZMod q) = b := (mem_filter.mp hn).2
        rw [hb, mul_comm]
      _ = _ := sum_fiberwise_of_maps_to hmaps _
  simp_rw [hexpand]
  rw [RHTower.sum_dirichletChar_normSq]
  have hcs (b : ZMod q) :
      ‖g b‖ ^ 2 ≤ ((F b).card : ℝ) * ∑ n ∈ F b, ‖a n‖ ^ 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (F b) a) 2).trans ?_
    have h := sum_mul_sq_le_sq_mul_sq (F b) (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    simpa only [mul_one, one_mul, one_pow, sum_const, nsmul_eq_mul, mul_comm] using h
  refine (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _))
    (Nat.cast_nonneg q.totient)).trans ?_
  refine (mul_le_mul_of_nonneg_left (sum_le_sum fun b _ => hcs b)
    (Nat.cast_nonneg q.totient)).trans_eq ?_
  rw [mul_sum]
  calc
    _ = ∑ b : ZMod q, ∑ n ∈ F b,
        (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) * ‖a n‖ ^ 2 := by
      refine sum_congr rfl fun b _ => ?_
      rw [← mul_assoc, mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hb : (n : ZMod q) = b := (mem_filter.mp hn).2
      have hF : F b = S.filter (fun m => m ≡ n [MOD q]) := by
        simp only [F, ← hb, ZMod.natCast_eq_natCast_iff]
      rw [hF]
    _ = _ := sum_fiberwise_of_maps_to hmaps _

end QH.PrimeProgressions
