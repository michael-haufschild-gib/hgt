import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletGreen
import GaloisForLFunctions.SelbergClass.Primon.KestenGreenConditioning

/-!
# Exact entrywise Dirichlet factors and convergence

The Dirichlet Green entry is the infinite entry times
`(1-q^(2(N-max(i,j)+1)))/(1-q^(2N+3))`. Every entry is strictly positive
and converges to the infinite Green entry as the terminal boundary
recedes. The same denominator controls the rank-one correction.
-/

open _root_.RHTower Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

private theorem denominator_pos (p : Nat.Primes) (n : ℕ) :
    0 < 1 - primeReciprocal p ^ (2 * n + 3) :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega))

/-- The terminal determinant factor is an exact quotient of geometric gaps. -/
theorem one_add_reciprocal_kestenGreenEntry_diagonal (p : Nat.Primes) (n : ℕ) :
    1 + primeReciprocal p * kestenGreenEntry p n n =
      (1 - primeReciprocal p ^ (2 * n + 3)) / (1 - primeReciprocal p ^ 2) := by
  rw [kestenGreenEntry_diagonal, show 2 * n + 3 = (2 * n + 1) + 2 by omega, pow_add]
  field_simp [(gap_pos p).ne']
  ring

/-- The scalar rank-one truncation coefficient has a closed geometric form. -/
theorem kestenDirichletCorrection_eq (p : Nat.Primes) (n : ℕ) :
    kestenDirichletCorrection p n = primeReciprocal p * (1 - primeReciprocal p ^ 2) /
      (1 - primeReciprocal p ^ (2 * n + 3)) := by
  have h : (primeReciprocal p)⁻¹ + kestenGreenEntry p n n =
      (1 - primeReciprocal p ^ (2 * n + 3)) / (primeReciprocal p * (1 - primeReciprocal p ^ 2)) := by
    rw [kestenGreenEntry_diagonal, show 2 * n + 3 = (2 * n + 1) + 2 by omega, pow_add]
    field_simp [(primeReciprocal_pos p).ne', (gap_pos p).ne']
    ring
  rw [kestenDirichletCorrection, h, inv_div]

private theorem propagate_right (p : Nat.Primes) (i j n : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    kestenGreenEntry p i n = primeReciprocal p ^ (n - j) * kestenGreenEntry p i j := by
  have hi := kestenGreenEntry_propagation p i (n - i)
  have hj := kestenGreenEntry_propagation p i (j - i)
  rw [Nat.add_sub_of_le (hij.trans hjn)] at hi
  rw [Nat.add_sub_of_le hij] at hj
  rw [hi, hj, ← mul_assoc, ← pow_add]
  congr 2
  omega

private theorem entry_factor_ordered (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) (hij : i.val ≤ j.val) :
    kestenDirichletGreen p n i j = kestenGreenEntry p i j *
      (1 - primeReciprocal p ^ (2 * (n - j.val + 1))) / (1 - primeReciprocal p ^ (2 * n + 3)) := by
  have hjn : j.val ≤ n := by omega
  have hp : primeReciprocal p ^ (2 * (n - j.val + 1)) * primeReciprocal p ^ (2 * j.val + 1) =
      primeReciprocal p ^ (2 * n + 3) := by
    rw [← pow_add]
    congr 1
    omega
  have hs : primeReciprocal p ^ (2 * (n - j.val + 1)) =
      primeReciprocal p ^ 2 * (primeReciprocal p ^ (n - j.val)) ^ 2 := by
    rw [show 2 * (n - j.val + 1) = 2 + (n - j.val) * 2 by omega, pow_add, pow_mul]
  rw [kestenDirichletGreen_entry, kestenDirichletCorrection_eq,
    propagate_right p i j n hij hjn, propagate_right p j j n le_rfl hjn,
    kestenGreenEntry_diagonal]
  field_simp [(gap_pos p).ne', (denominator_pos p n).ne']
  rw [← hp, hs]
  ring

/-- Every finite Dirichlet entry is the infinite entry times an exact boundary attenuation factor. -/
theorem kestenDirichletGreen_entry_factor (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    kestenDirichletGreen p n i j = kestenGreenEntry p i j *
      (1 - primeReciprocal p ^ (2 * (n - max i.val j.val + 1))) /
        (1 - primeReciprocal p ^ (2 * n + 3)) := by
  rcases le_total i.val j.val with hij | hji
  · rw [max_eq_right hij]
    exact entry_factor_ordered p n i j hij
  · rw [max_eq_left hji, kestenDirichletGreen_entry_symm,
      kestenGreenEntry_symm p i j]
    exact entry_factor_ordered p n j i hji

/-- Every Dirichlet Green entry is strictly positive. -/
theorem kestenDirichletGreen_entry_pos (p : Nat.Primes) (n : ℕ) (i j : Fin (n + 1)) :
    0 < kestenDirichletGreen p n i j := by
  rw [kestenDirichletGreen_entry_factor]
  exact div_pos (mul_pos (kestenGreenEntry_pos p i j)
    (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega))))
      (denominator_pos p n)

/-- Moving the terminal boundary to infinity recovers every fixed infinite Green entry. -/
theorem tendsto_kestenDirichletGreen_fixedEntry (p : Nat.Primes) (i j : ℕ) :
    Tendsto (fun N : ℕ => kestenDirichletGreen p (i + j + N)
      ⟨i, by omega⟩ ⟨j, by omega⟩) atTop (𝓝 (kestenGreenEntry p i j)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (primeReciprocal p))
    (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide : (2 : ℕ) ≠ 0))
  have he (N : ℕ) : kestenDirichletGreen p (i + j + N) ⟨i, by omega⟩ ⟨j, by omega⟩ =
      kestenGreenEntry p i j *
        (1 - primeReciprocal p ^ (2 * (min i j + 1)) * (primeReciprocal p ^ 2) ^ N) /
        (1 - primeReciprocal p ^ (2 * (i + j) + 3) * (primeReciprocal p ^ 2) ^ N) := by
    rw [kestenDirichletGreen_entry_factor]
    have hn : i + j + N - max i j = min i j + N := by omega
    simp only [hn]
    rw [show 2 * (min i j + N + 1) = 2 * (min i j + 1) + 2 * N by omega,
      show 2 * (i + j + N) + 3 = (2 * (i + j) + 3) + 2 * N by omega,
      pow_add, pow_add, pow_mul (primeReciprocal p) 2 N]
  have h := ((tendsto_const_nhds (x := kestenGreenEntry p i j)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (primeReciprocal p ^ (2 * (min i j + 1)))))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (primeReciprocal p ^ (2 * (i + j) + 3))))
        (by norm_num)
  simpa only [mul_zero, sub_zero, mul_one, div_one] using h.congr (fun N => (he N).symm)

end
end GaloisForLFunctions.SelbergClass.Primon
