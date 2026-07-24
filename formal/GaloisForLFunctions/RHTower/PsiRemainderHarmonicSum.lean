import GaloisForLFunctions.RHTower.PsiRemainderSignChange

/-!
# The uniform harmonic-weighted remainder sum

`|∑_{n ≤ N} R(n)·(1/n − 1/(n+1))| ≤ 20` for `R = ψ − id`:

the discrete form of the classical `∫ R(t)/t² dt = O(1)`.  The `ψ` part
Abel-summs to `∑ Λ(k)/k − ψ(N)/(N+1)` and Mertens pins `∑ Λ(k)/k` to
`log N` within `7`; the linear part is the harmonic tail
`∑ 1/(n+1) = H_{N+1} − 1`, pinned to `log(N+1) + γ − 1` within `1`.  The
logarithms cancel, leaving a bounded quantity.  On any multiplicative
window this forces the remainder to visit small relative values — the
sign-change reservoir of the Erdős–Selberg contraction.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The reciprocal telescope on `[k, N]`:
`∑_{n=k}^{N} (1/n − 1/(n+1)) = 1/k − 1/(N+1)`. -/
theorem sum_reciprocal_telescope {k N : ℕ} (_hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ n ∈ Finset.Icc k N, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = 1 / (k : ℝ) - 1 / ((N : ℝ) + 1) := by
  have hIcc : Finset.Icc k N = Finset.Ico k (N + 1) :=
    (Finset.Ico_add_one_right_eq_Icc k N).symm
  rw [hIcc]
  have h3 := Finset.sum_Ico_eq_sub
    (fun n => 1 / (((n + 1 : ℕ)) : ℝ) - 1 / ((n : ℕ) : ℝ))
    (show k ≤ N + 1 by omega)
  have h1 := Finset.sum_range_sub (fun n => 1 / ((n : ℕ) : ℝ)) (N + 1)
  have h2 := Finset.sum_range_sub (fun n => 1 / ((n : ℕ) : ℝ)) k
  have hneg : ∑ n ∈ Finset.Ico k (N + 1),
      (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = -∑ n ∈ Finset.Ico k (N + 1),
          (1 / (((n + 1 : ℕ)) : ℝ) - 1 / ((n : ℕ) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hneg, h3, h1, h2]
  push_cast
  norm_num

/-- Abel summation of the `ψ` part:
`∑_{n ≤ N} ψ(n)(1/n − 1/(n+1)) = ∑_{k ≤ N} Λ(k)/k − ψ(N)/(N+1)`. -/
theorem sum_chebyshevPsi_harmonic_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, chebyshevPsi n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = (∑ k ∈ Finset.Icc 1 N, vonMangoldt k / k)
        - chebyshevPsi N * (1 / ((N : ℝ) + 1)) := by
  have hexp : ∀ n ∈ Finset.Icc 1 N,
      chebyshevPsi n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        = ∑ k ∈ Finset.Icc 1 n,
            vonMangoldt k * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    intro n _
    rw [show chebyshevPsi n = ∑ k ∈ Finset.Icc 1 n, vonMangoldt k from rfl,
      Finset.sum_mul]
  rw [Finset.sum_congr rfl hexp, Finset.sum_sigma']
  have hbij : ∑ x ∈ (Finset.Icc 1 N).sigma (fun n => Finset.Icc 1 n),
      vonMangoldt x.2 * (1 / (x.1 : ℝ) - 1 / ((x.1 : ℝ) + 1))
      = ∑ y ∈ (Finset.Icc 1 N).sigma (fun k => Finset.Icc k N),
          vonMangoldt y.1 * (1 / (y.2 : ℝ) - 1 / ((y.2 : ℝ) + 1)) := by
    apply Finset.sum_nbij' (i := fun x => ⟨x.2, x.1⟩)
      (j := fun y => ⟨y.2, y.1⟩)
    · rintro ⟨n, k⟩ hx
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hx
      dsimp only at hx
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
      dsimp only
      omega
    · rintro ⟨k, n⟩ hy
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hy
      dsimp only at hy
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
      dsimp only
      omega
    · rintro ⟨n, k⟩ _
      rfl
    · rintro ⟨k, n⟩ _
      rfl
    · rintro ⟨n, k⟩ _
      rfl
  rw [hbij, Finset.sum_sigma]
  have hinner : ∀ k ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc k N,
        vonMangoldt k * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        = vonMangoldt k / k - vonMangoldt k * (1 / ((N : ℝ) + 1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← Finset.mul_sum, sum_reciprocal_telescope hk.1 hk.2]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    field_simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, ← Finset.sum_mul,
    show (∑ k ∈ Finset.Icc 1 N, vonMangoldt k) = chebyshevPsi N from rfl]

/-- **Uniform harmonic-weighted remainder bound**:
`|∑_{n ≤ N} R(n)(1/n − 1/(n+1))| ≤ 20`. -/
theorem abs_sum_psiRemainder_harmonic_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N,
        psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))| ≤ 20 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- split ψ − id
  have hsplit : ∑ n ∈ Finset.Icc 1 N,
      psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = (∑ n ∈ Finset.Icc 1 N,
          chebyshevPsi n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        - ∑ n ∈ Finset.Icc 1 N,
            (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [psiRemainder]
    ring
  -- linear part is the harmonic tail
  have hlin : ∑ n ∈ Finset.Icc 1 N,
      (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      = ∑ n ∈ Finset.Icc 1 N, 1 / ((n : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    field_simp
    ring
  have hharm : ∑ n ∈ Finset.Icc 1 N, 1 / ((n : ℝ) + 1)
      = (∑ i ∈ Finset.Icc 1 (N + 1), ((i : ℝ))⁻¹) - 1 := by
    have hins : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext x
      simp [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have hre : ∑ i ∈ Finset.Icc 2 (N + 1), ((i : ℝ))⁻¹
        = ∑ n ∈ Finset.Icc 1 N, 1 / ((n : ℝ) + 1) := by
      apply Finset.sum_nbij' (i := fun i => i - 1) (j := fun n => n + 1)
      · intro i hi
        rw [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        omega
      · intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Icc]
        omega
      · intro i hi
        rw [Finset.mem_Icc] at hi
        omega
      · intro n _
        omega
      · intro i hi
        rw [Finset.mem_Icc] at hi
        have hc : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          ring
        rw [hc, one_div]
    rw [hre]
    norm_num
  -- assemble
  rw [hsplit, sum_chebyshevPsi_harmonic_eq N hN, hlin, hharm]
  have hM := abs_le.1 (Mertens.mertens_first N hN)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have hH := abs_le.1 (abs_sum_inv_sub_log_sub_mascheroni_le (N + 1) (by omega))
  have hHN1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hH
  have hlogstep : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 := by
    have h1 := log_succ_sub_log_le hN
    have h2 : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]
      exact_mod_cast hN
    linarith
  have hlogmono : 0 ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
    have := Real.log_le_log hN0 (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
    linarith
  have hψfrac : 0 ≤ chebyshevPsi N * (1 / ((N : ℝ) + 1))
      ∧ chebyshevPsi N * (1 / ((N : ℝ) + 1)) ≤ 7 := by
    constructor
    · have hψ0 : 0 ≤ chebyshevPsi N :=
        Finset.sum_nonneg fun m _ => vonMangoldt_nonneg
      positivity
    · rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith [chebyshevPsi_le_seven N]
  have hγu : Real.eulerMascheroniConstant ≤ 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds.le
  have hγl : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  rw [abs_le]
  constructor
  · nlinarith [hM.1, hH.2, hψfrac.1, hψfrac.2, hlogstep, hlogmono, hHN1]
  · nlinarith [hM.2, hH.1, hψfrac.1, hψfrac.2, hlogstep, hlogmono, hHN1]

end RHTower
