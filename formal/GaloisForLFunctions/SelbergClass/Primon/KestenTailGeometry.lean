import GaloisForLFunctions.SelbergClass.Primon.KestenCharacterJets

/-!
# Stationary geometry of character tails

Normalized likelihood tails have a geometric Gram kernel in their depth.
Their backward differences are orthonormal characters, giving the exact
Markov factorization and a depth-independent finite Gram determinant.
-/

open _root_.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A normalized tail is orthogonal to every earlier even character. -/
theorem inner_kestenNormalizedTail_earlier (p : Nat.Primes) (N n : ℕ) (h : n < N) :
    inner ℝ (kestenNormalizedTail p N) (spectralCharacterVector (2 * n)) = 0 := by
  rw [kestenNormalizedTail, inner_smul_left, inner_characterResidual_evenCharacter,
    if_pos h, mul_zero]

/-- The later coefficients of a normalized tail form a geometric progression. -/
theorem inner_kestenNormalizedTail_later (p : Nat.Primes) (N k : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (spectralCharacterVector (2 * (N + k))) =
      primeReciprocal p ^ k := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [kestenNormalizedTail, inner_smul_left, inner_characterResidual_evenCharacter,
    if_neg (by omega), pow_add]
  simp only [conj_trivial, primeReciprocal]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp, one_pow, one_mul]

/-- Cross-prime tails at different depths have an exact geometric Gram kernel. -/
theorem inner_kestenNormalizedTail_add (p q : Nat.Primes) (N k : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (kestenNormalizedTail q (N + k)) =
      primeReciprocal p ^ k / (1 - primeReciprocal p * primeReciprocal q) := by
  induction k generalizing N with
  | zero => simpa using inner_kestenNormalizedTail_sameDepth p q N
  | succ k ih =>
      have hz : inner ℝ (spectralCharacterVector (2 * N))
          (kestenNormalizedTail q (N + (k + 1))) = 0 := by
        rw [real_inner_comm, inner_kestenNormalizedTail_earlier q _ N (by omega)]
      rw [kestenNormalizedTail_step p N, inner_add_left, hz, zero_add, inner_smul_left]
      have he : N + (k + 1) = (N + 1) + k := by omega
      rw [he, ih]
      simp only [conj_trivial, primeReciprocal, pow_succ]
      ring

/-- At one prime, depth translation preserves all pairwise inner products. -/
theorem inner_kestenNormalizedTail (p : Nat.Primes) (N M : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (kestenNormalizedTail p M) =
      primeReciprocal p ^ Nat.dist N M / (1 - primeReciprocal p ^ 2) := by
  rcases le_total N M with h | h
  · have hg := inner_kestenNormalizedTail_add p p N (M - N)
    rw [Nat.add_sub_of_le h] at hg
    simpa only [Nat.dist_eq_sub_of_le h, pow_two] using hg
  · rw [real_inner_comm (kestenNormalizedTail p M) (kestenNormalizedTail p N)]
    have hg := inner_kestenNormalizedTail_add p p M (N - M)
    rw [Nat.add_sub_of_le h] at hg
    simpa only [Nat.dist_eq_sub_of_le_right h, pow_two] using hg

/-- Three ordered depths satisfy the exact scalar Markov factorization. -/
theorem kestenNormalizedTail_markov (p : Nat.Primes) (N j k : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (kestenNormalizedTail p (N + j + k)) *
        ‖kestenNormalizedTail p (N + j)‖ ^ 2 =
      inner ℝ (kestenNormalizedTail p N) (kestenNormalizedTail p (N + j)) *
        inner ℝ (kestenNormalizedTail p (N + j)) (kestenNormalizedTail p (N + j + k)) := by
  rw [show N + j + k = N + (j + k) by omega,
    inner_kestenNormalizedTail_add, norm_sq_kestenNormalizedTail,
    inner_kestenNormalizedTail_add]
  rw [show N + (j + k) = (N + j) + k by omega, inner_kestenNormalizedTail_add, pow_add]
  ring

/-- The backward innovations are exactly the orthonormal even characters. -/
theorem kestenNormalizedTail_innovation (p : Nat.Primes) (N : ℕ) :
    kestenNormalizedTail p N - primeReciprocal p • kestenNormalizedTail p (N + 1) =
      spectralCharacterVector (2 * N) := by
  rw [kestenNormalizedTail_step p N]
  exact add_sub_cancel_right _ _

/-- Gram matrix of consecutive normalized tails, starting at any depth. -/
def kestenDepthGram (p : Nat.Primes) (N n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (kestenNormalizedTail p (N + i)) (kestenNormalizedTail p (N + j))

/-- The finite Gram matrix depends only on depth differences. -/
theorem kestenDepthGram_apply (p : Nat.Primes) (N n : ℕ) (i j : Fin n) :
    kestenDepthGram p N n i j =
      primeReciprocal p ^ Nat.dist i.val j.val / (1 - primeReciprocal p ^ 2) := by
  rw [kestenDepthGram, inner_kestenNormalizedTail, Nat.dist_add_add_left]

/-- Shifting every depth leaves a consecutive Gram matrix unchanged. -/
theorem kestenDepthGram_stationary (p : Nat.Primes) (N M n : ℕ) :
    kestenDepthGram p N n = kestenDepthGram p M n := by
  ext i j
  rw [kestenDepthGram_apply, kestenDepthGram_apply]


/-- Removing the first backward innovation leaves the next depth Gram determinant. -/
private theorem det_kestenDepthGram_succ (p : Nat.Primes) (N n : ℕ) :
    (kestenDepthGram p N (n + 2)).det = (kestenDepthGram p (N + 1) (n + 1)).det := by
  let G := kestenDepthGram p N (n + 2)
  let H := G.updateRow 0 (G 0 + (-primeReciprocal p) • G (0 : Fin (n + 1)).succ)
  have hd : H.det = G.det :=
    Matrix.det_updateRow_add_smul_self G (Fin.succ_ne_zero _).symm _
  have hr (j : Fin (n + 2)) : H 0 j = if j = 0 then 1 else 0 := by
    change (G 0 + (-primeReciprocal p) • G (0 : Fin (n + 1)).succ) j = _
    simp only [G, kestenDepthGram, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_zero, Fin.val_succ, Nat.add_zero, zero_add, neg_mul, ← sub_eq_add_neg]
    have he := congrArg (fun z => inner ℝ z (kestenNormalizedTail p (N + j)))
      (kestenNormalizedTail_innovation p N)
    simp only [inner_sub_left, inner_smul_left, conj_trivial] at he
    rw [he]
    induction j using Fin.cases with
    | zero =>
        simp only [Fin.val_zero, Nat.add_zero, ite_true]
        rw [real_inner_comm, inner_kestenNormalizedTail_leading]
    | succ j =>
        rw [if_neg (Fin.succ_ne_zero j), real_inner_comm,
          inner_kestenNormalizedTail_earlier p _ N (by simp only [Fin.val_succ]; omega)]
  have hm : H.submatrix Fin.succ (0 : Fin (n + 2)).succAbove =
      kestenDepthGram p (N + 1) (n + 1) := by
    ext i j
    simp only [H, Matrix.submatrix_apply, Fin.zero_succAbove,
      Matrix.updateRow_apply, Fin.succ_ne_zero, if_false, G, kestenDepthGram, Fin.val_succ]
    congr 1 <;> congr 1 <;> omega
  rw [← hd, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [hr, ite_true, Fin.succ_ne_zero, if_false, Fin.val_zero, pow_zero,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  exact congrArg Matrix.det hm

/-- Every nonempty consecutive depth Gram determinant is the same positive resolvent. -/
theorem det_kestenDepthGram (p : Nat.Primes) (N n : ℕ) :
    (kestenDepthGram p N (n + 1)).det = 1 / (1 - primeReciprocal p ^ 2) := by
  induction n generalizing N with
  | zero =>
      rw [Matrix.det_fin_one, kestenDepthGram_apply]
      simp only [Fin.val_zero, Nat.dist_self, pow_zero]
  | succ n ih => rw [det_kestenDepthGram_succ, ih]

end
end GaloisForLFunctions.SelbergClass.Primon

