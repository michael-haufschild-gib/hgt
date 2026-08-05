import GaloisForLFunctions.RHTower.Sieve.KthDerivativeTest

/-!
# The logarithmic phase and its dyadic block bound

`n^{-it} = e(g_t(n))` for the phase `g_t(x) = -(t/2π)·log x`, whose `k`-th derivative is
`±(t/2π)(k−1)!·x^{-k}` — constant sign, pinned within the ratio `2^k` on a dyadic block
`[N, 2N]`.  Feeding the chain to the `k`-th derivative test bounds every block of the
Dirichlet series `∑ n^{-it}` by

  `256·( L·(4^k λ)^{1/(2^k−2)} + L^{1−4/2^k}·λ^{−2/2^k} ),  λ = (t/2π)(k−1)!/(2N)^k`,

for any `k ≥ 2` with `λ ≤ 1`.  Odd `k` is the conjugate phase: negating the chain flips
the sign of the top derivative and conjugates every term, so norms are unchanged.
-/

namespace RHTower.Sieve

open Real

/-- The phase of `n^{-it}`: `g_t(x) = -(t/2π)·log x`. -/
noncomputable def logPhase (t : ℝ) : ℝ → ℝ := fun x => -(t / (2 * Real.pi)) * Real.log x

/-- The derivative chain of the logarithmic phase:
`g_t^{(i)}(x) = (t/2π)·(-1)^i·(i-1)!·x^{-i}` for `i ≥ 1`. -/
noncomputable def logPhaseChain (t : ℝ) : ℕ → ℝ → ℝ
  | 0 => logPhase t
  | (i + 1) => fun x =>
      t / (2 * Real.pi) * (-1) ^ (i + 1) * (Nat.factorial i : ℝ) * (x ^ (i + 1))⁻¹

/-- The chain is an honest derivative chain on `(0, ∞)`. -/
theorem logPhaseChain_hasDerivAt (t : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logPhaseChain t i) (logPhaseChain t (i + 1) x) x := by
  cases i with
  | zero =>
    have h := (Real.hasDerivAt_log (ne_of_gt hx)).const_mul (-(t / (2 * Real.pi)))
    have hval : logPhaseChain t 1 x = -(t / (2 * Real.pi)) * x⁻¹ := by
      simp only [logPhaseChain]
      norm_num
    rw [show (0 + 1 : ℕ) = 1 from rfl, hval]
    exact h
  | succ i =>
    have hx' : x ≠ 0 := ne_of_gt hx
    have hpow : HasDerivAt (fun y : ℝ => y ^ (i + 1)) (((i : ℝ) + 1) * x ^ i) x := by
      have := hasDerivAt_pow (i + 1) x
      simpa using this
    have hne : x ^ (i + 1) ≠ 0 := pow_ne_zero _ hx'
    have h := (hpow.inv hne).const_mul
      (t / (2 * Real.pi) * (-1) ^ (i + 1) * (Nat.factorial i : ℝ))
    have hval : logPhaseChain t (i + 1 + 1) x
        = t / (2 * Real.pi) * (-1) ^ (i + 1) * (Nat.factorial i : ℝ)
          * (-(((i : ℝ) + 1) * x ^ i) / (x ^ (i + 1)) ^ 2) := by
      simp only [logPhaseChain]
      have hfact : (Nat.factorial (i + 1) : ℝ) = ((i : ℝ) + 1) * (Nat.factorial i : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfact]
      field_simp
      ring
    rw [hval]
    exact h

/-- The sign-corrected chain member is the positive quantity `(t/2π)·j!·x^{-(j+1)}`. -/
theorem neg_one_pow_mul_logPhaseChain (t : ℝ) (j : ℕ) (x : ℝ) :
    (-1) ^ (j + 1) * logPhaseChain t (j + 1) x
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (x ^ (j + 1))⁻¹ := by
  simp only [logPhaseChain]
  have hsq : ((-1 : ℝ)) ^ (j + 1) * ((-1 : ℝ)) ^ (j + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j + 1, rfl⟩
  linear_combination
    (t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (x ^ (j + 1))⁻¹) * hsq

/-- On a positive interval `[A, B]` the sign-corrected top derivative is pinned between
`(t/2π)·j!·B^{-(j+1)}` and `(t/2π)·j!·A^{-(j+1)}`. -/
theorem logPhaseChain_signed_bounds (t : ℝ) (ht : 0 < t) (j : ℕ)
    {A B x : ℝ} (hA : 0 < A) (hx : x ∈ Set.Icc A B) :
    t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (B ^ (j + 1))⁻¹
      ≤ (-1) ^ (j + 1) * logPhaseChain t (j + 1) x
    ∧ (-1) ^ (j + 1) * logPhaseChain t (j + 1) x
      ≤ t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (A ^ (j + 1))⁻¹ := by
  rw [neg_one_pow_mul_logPhaseChain]
  have hxpos : 0 < x := lt_of_lt_of_le hA hx.1
  have hC : 0 ≤ t / (2 * Real.pi) * (Nat.factorial j : ℝ) := by
    have hπ := Real.pi_pos
    exact mul_nonneg (div_nonneg ht.le (by positivity)) (Nat.cast_nonneg _)
  have hpow1 : x ^ (j + 1) ≤ B ^ (j + 1) := pow_le_pow_left₀ hxpos.le hx.2 _
  have hpow2 : A ^ (j + 1) ≤ x ^ (j + 1) := pow_le_pow_left₀ hA.le hx.1 _
  have hxpow : 0 < x ^ (j + 1) := pow_pos hxpos _
  have hApow : 0 < A ^ (j + 1) := pow_pos hA _
  exact ⟨mul_le_mul_of_nonneg_left (inv_anti₀ hxpow hpow1) hC,
    mul_le_mul_of_nonneg_left (inv_anti₀ hApow hpow2) hC⟩

/-- Negating the phase conjugates every term: the norms of the sums agree. -/
theorem norm_phase_sum_neg (g : ℝ → ℝ) (x₀ : ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L,
        Complex.exp (((2 * Real.pi * -(g (x₀ + n)) : ℝ) : ℂ) * Complex.I)‖
      = ‖∑ n ∈ Finset.range L,
          Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ := by
  have hterm : ∀ n : ℕ,
      Complex.exp (((2 * Real.pi * -(g (x₀ + n)) : ℝ) : ℂ) * Complex.I)
        = (starRingEnd ℂ)
            (Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)) := by
    intro n
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun n _ => hterm n, ← map_sum]
  exact RCLike.norm_conj _

/-- `n^{-it}` is the phase `e(g_t(n))`. -/
theorem natCast_cpow_neg_I_mul (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * logPhase t (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hcast : (n : ℂ) = (((n : ℝ) : ℂ)) := by norm_cast
  rw [hcast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1
  simp only [logPhase]
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **The dyadic block bound for `∑ n^{-it}`.**  For any `k ≥ 2` whose block derivative
size `λ = (t/2π)(k−1)!/(2N)^k` is at most one, a run of `L` consecutive Dirichlet phases
starting at `N` and staying inside `[N, 2N]` obeys the `k`-th derivative test with
ratio `2^k`. -/
theorem dirichlet_block_bound (t : ℝ) (ht : 0 < t) (k N L : ℕ) (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlam1 ⊢
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial j : ℝ) / (2 * (N : ℝ)) ^ (j + 1)
    with hlamdef
  have hπ := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hN1)
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    have h1 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
    have h2 : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have h3 : (0 : ℝ) < (2 * (N : ℝ)) ^ (j + 1) := by positivity
    exact div_pos (mul_pos h1 h2) h3
  have hgrow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    calc (1 : ℝ) = 2 ^ 0 := by norm_num
      _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ one_le_two (Nat.zero_le _)
  -- the two endpoint identities for the derivative window
  have hlam_eq : lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * ((2 * (N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef, div_eq_mul_inv]
  have hupper_eq : (2 : ℝ) ^ (j + 1) * lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (((N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef]
    field_simp [mul_pow]
    ring
  -- the sample span sits inside the dyadic window
  have hspan_mem : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      0 < x ∧ x ∈ Set.Icc ((N : ℝ)) (2 * (N : ℝ)) := by
    intro x hx
    have hL1 : ((L - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : L - 1 ≤ N := by omega
      exact_mod_cast this
    exact ⟨by linarith [hx.1], hx.1, by linarith [hx.2]⟩
  -- rewrite the Dirichlet terms as phases
  have hphase : ∀ i ∈ Finset.range L, ((N + i : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + i) : ℝ) : ℂ) * Complex.I) := by
    intro i _
    have harg : ((N + i : ℕ) : ℝ) = (N : ℝ) + (i : ℝ) := by push_cast; ring
    rw [natCast_cpow_neg_I_mul t (N + i) (by omega), harg]
  rw [Finset.sum_congr rfl hphase]
  -- write `4^k` as the ratio squared, matching the derivative test's conclusion
  rw [show (4 : ℝ) ^ (j + 1) = ((2 : ℝ) ^ (j + 1)) ^ 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
  rcases Nat.even_or_odd (j + 1) with hev | hodd
  · -- even order: the chain itself has positive top derivative
    have hone : ((-1 : ℝ)) ^ (j + 1) = 1 := Even.neg_one_pow hev
    have hchain : ∀ i < j + 1, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        HasDerivAt (logPhaseChain t i) (logPhaseChain t (i + 1) x) x :=
      fun i _ x hx => logPhaseChain_hasDerivAt t i (hspan_mem x hx).1
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        lam ≤ logPhaseChain t (j + 1) x := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hone, one_mul] at hb
      rw [hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        logPhaseChain t (j + 1) x ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hone, one_mul] at hb
      rw [hupper_eq]
      exact hb
    have hDk := kth_derivative_test (j + 1) hk (logPhaseChain t) (N : ℝ) L hL
      hlam0 hlam1 hgrow1 hchain hlo hhi
    exact hDk
  · -- odd order: run the test on the negated chain and conjugate back
    have hneg : ((-1 : ℝ)) ^ (j + 1) = -1 := Odd.neg_one_pow hodd
    have hchain : ∀ i < j + 1, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        HasDerivAt (fun y => -(logPhaseChain t i y)) (-(logPhaseChain t (i + 1) x)) x :=
      fun i _ x hx => (logPhaseChain_hasDerivAt t i (hspan_mem x hx).1).neg
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        lam ≤ -(logPhaseChain t (j + 1) x) := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hneg, neg_one_mul] at hb
      rw [hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        -(logPhaseChain t (j + 1) x) ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hneg, neg_one_mul] at hb
      rw [hupper_eq]
      exact hb
    have hDk := kth_derivative_test (j + 1) hk (fun i y => -(logPhaseChain t i y))
      (N : ℝ) L hL hlam0 hlam1 hgrow1 hchain hlo hhi
    rw [← norm_phase_sum_neg (logPhase t) (N : ℝ) L]
    exact hDk

end RHTower.Sieve
