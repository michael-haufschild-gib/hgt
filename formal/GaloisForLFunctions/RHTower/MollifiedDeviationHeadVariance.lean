import GaloisForLFunctions.RHTower.Sieve.BarbanVehovWeight
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow
import GaloisForLFunctions.RHTower.PrimeHigherMertens
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The head of the mollified deviation `ζΨ − 1` and its variance law

For the linear (Levinson–Conrey) mollifier `Ψ_M(s) = ∑_{m ≤ M} μ(m) (log(M/m)/log M) m^{-s}`, the
Dirichlet coefficients of the product `ζ·Ψ_M` are `[k = 1] + Λ(k)/log M` for every `1 ≤ k ≤ M`
(Barban–Vehov / Möbius inversion, already owned by the corpus).  Hence the deviation `W_M = ζΨ_M − 1`
splits as a *head*

```text
H_M(s) = (1/log M) ∑_{1 < k ≤ M} Λ(k) k^{-s} = −(1/log M) · (ζ'/ζ)_{≤ M}(s)
```

— the truncated logarithmic derivative, normalized by `log M` — plus a tail supported on `k > M`.

The head is a genuine Dirichlet polynomial on the critical line.  Its coefficient energy is
`∑_{k ≤ M} Λ(k)²/k / (log M)²`, and by the higher-order Mertens theorem this tends to `1/2`,
independently of the mollifier length exponent.  The corpus's Dirichlet mean value theorem then gives
the *head variance law*: on every window of length at least `M²`, the mean square of the head tends
to `1/2` as `M → ∞`.  (Conrey's mollified mean value `E|ζΨ|² → 1 + 1/θ`, not in Lean, says the
whole deviation has variance `1/θ`; so the head accounts for exactly half a unit and the tail plus
cross term for `1/θ − 1/2`.)

No zero, ordinate, or RH premise enters any statement.
-/

open ArithmeticFunction Finset Filter Topology

namespace RHTower

noncomputable section

/-! ## Head identification -/

/-- Dirichlet coefficients of the linear mollifier `Ψ_M`. -/
def linearMollifierDirichletCoeff (M m : ℕ) : ℝ :=
  Sieve.barbanVehovWeight M m / Real.log M

/-- Dirichlet coefficients of the mollified product `ζ·Ψ_M`: convolution of the mollifier with `1`. -/
def mollifiedProductDirichletCoeff (M k : ℕ) : ℝ :=
  ∑ m ∈ k.divisors, linearMollifierDirichletCoeff M m

theorem mollifiedProductDirichletCoeff_eq (M k : ℕ) :
    mollifiedProductDirichletCoeff M k = Sieve.barbanVehovCoeff M k / Real.log M := by
  unfold mollifiedProductDirichletCoeff linearMollifierDirichletCoeff Sieve.barbanVehovCoeff
  rw [Finset.sum_div]

/-- **Head identification.**  For `1 ≤ k ≤ M` the mollified product `ζΨ_M` has Dirichlet
coefficient `[k = 1] + Λ(k)/log M`: the deviation `ζΨ_M − 1` starts with the truncated
logarithmic derivative of `ζ`, normalized by `log M`. -/
theorem mollifiedProductDirichletCoeff_eq_vonMangoldt {M k : ℕ} (hM : 1 < M) (hk : 1 ≤ k)
    (hkM : k ≤ M) :
    mollifiedProductDirichletCoeff M k =
      (if k = 1 then 1 else 0) + Λ k / Real.log M := by
  rw [mollifiedProductDirichletCoeff_eq]
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rcases eq_or_lt_of_le hk with h1 | h1
  · subst h1
    rw [Sieve.barbanVehovCoeff_one (by omega), if_pos rfl, vonMangoldt_apply_one, zero_div,
      add_zero, div_self hlog]
  · rw [Sieve.barbanVehovCoeff_eq_vonMangoldt h1 hkM, if_neg (by omega)]
    ring

/-! ## The head as a critical-line Dirichlet polynomial -/

/-- Critical-line coefficients of the head `H_M(1/2 + it) = (1/log M) ∑_{k ≤ M} Λ(k) k^{-1/2-it}`,
indexed by `n ↦ k = n + 1`. -/
def mollifiedDeviationHeadCoeff (M : ℕ) : Fin M → ℂ :=
  fun n => ((Λ ((n : ℕ) + 1) / (Real.log M * Real.sqrt (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ)

/-- The head coefficient energy is the Chebyshev square-weight sum over `(log M)²`. -/
theorem sum_normSq_mollifiedDeviationHeadCoeff (M : ℕ) :
    ∑ n : Fin M, ‖mollifiedDeviationHeadCoeff M n‖ ^ (2 : ℕ) =
      (∑ k ∈ Icc 1 M, Λ k ^ (2 : ℕ) / (k : ℝ)) / (Real.log M) ^ (2 : ℕ) := by
  have hIcc : Icc 1 M = Ico 1 (M + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range, Finset.sum_div, Nat.add_sub_cancel]
  calc ∑ n : Fin M, ‖mollifiedDeviationHeadCoeff M n‖ ^ (2 : ℕ)
      = ∑ n ∈ range M,
          ‖((Λ (n + 1) / (Real.log M * Real.sqrt ((n : ℝ) + 1)) : ℝ) : ℂ)‖ ^ (2 : ℕ) :=
        Fin.sum_univ_eq_sum_range
          (fun n : ℕ => ‖((Λ (n + 1) / (Real.log M * Real.sqrt ((n : ℝ) + 1)) : ℝ) : ℂ)‖ ^ (2 : ℕ)) M
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_comm 1 n]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : Real.sqrt ((n : ℝ) + 1) ^ (2 : ℕ) = (n : ℝ) + 1 := Real.sq_sqrt hn.le
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, div_pow, mul_pow, hsq, div_div, mul_comm (Real.log (M : ℝ) ^ (2 : ℕ))]

/-! ## The Chebyshev square-weight sum is asymptotically `(log N)²/2` -/

/-- Pointwise split of `Λ(k)²` into the prime part and the prime-power part. -/
theorem vonMangoldt_sq_split (k : ℕ) :
    Λ k ^ (2 : ℕ) = (if k.Prime then (Real.log k) ^ (2 : ℕ) else 0) + Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) := by
  unfold Mertens.notPrimeVonMangoldt
  by_cases hp : k.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp [hp]

theorem sum_vonMangoldt_sq_div_eq_primeLogPowSum_add (N : ℕ) :
    ∑ k ∈ Icc 1 N, Λ k ^ (2 : ℕ) / (k : ℝ) =
      primeLogPowSum 2 (N : ℝ) + ∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) / (k : ℝ) := by
  rw [primeLogPowSum, Nat.floor_natCast]
  have h0 : ∑ n ∈ Icc 0 N, primeLogPowWeight 2 n = ∑ n ∈ Icc 1 N, primeLogPowWeight 2 n := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [primeLogPowWeight]
    · have hsplit : Icc 0 N = insert 0 (Icc 1 N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp)]
      simp [primeLogPowWeight]
  rw [h0, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [vonMangoldt_sq_split, primeLogPowWeight]
  by_cases hp : k.Prime
  · simp [hp, add_div]
  · simp [hp]

/-- The prime-power part of the square-weight sum is `O(log N)`. -/
theorem sum_notPrimeVonMangoldt_sq_div_le (N : ℕ) :
    ∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (8 + Mertens.mertensTail) := by
  have hN0 : ∀ k ∈ Icc 1 N, (1 : ℝ) ≤ k := fun k hk => by
    exact_mod_cast (Finset.mem_Icc.mp hk).1
  calc ∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) / (k : ℝ)
      ≤ ∑ k ∈ Icc 1 N, Real.log N * (Mertens.notPrimeVonMangoldt k / (k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : (1 : ℝ) ≤ k := hN0 k hk
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
        have hnn : 0 ≤ Mertens.notPrimeVonMangoldt k := by
          unfold Mertens.notPrimeVonMangoldt
          split_ifs
          · exact le_rfl
          · exact vonMangoldt_nonneg
        have hle : Mertens.notPrimeVonMangoldt k ≤ Real.log N := by
          unfold Mertens.notPrimeVonMangoldt
          split_ifs
          · exact Real.log_nonneg (by linarith)
          · exact le_trans vonMangoldt_le_log (Real.log_le_log (by linarith) hkN)
        have hkpos : (0 : ℝ) < k := by linarith
        rw [sq, ← mul_div_assoc, div_le_div_iff_of_pos_right hkpos]
        exact mul_le_mul_of_nonneg_right hle hnn
    _ = Real.log N * ∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k / (k : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Real.log N * (8 + Mertens.mertensTail) := by
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN
          simp
        · exact mul_le_mul_of_nonneg_left (Mertens.tail_bounded N)
            (Real.log_nonneg (by exact_mod_cast hN))

/-- **The Chebyshev square-weight law.**  `∑_{k ≤ N} Λ(k)²/k / (log N)² → 1/2`. -/
theorem tendsto_sum_vonMangoldt_sq_div_div_log_sq :
    Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, Λ k ^ (2 : ℕ) / (k : ℝ)) / (Real.log N) ^ (2 : ℕ))
      atTop (𝓝 (1 / 2)) := by
  -- Mertens: primeLogPowSum 2 N − (log N)²/2 → C
  have hM : Tendsto (fun N : ℕ => primeLogPowSum 2 (N : ℝ) - (Real.log N) ^ (2 : ℕ) / 2)
      atTop (𝓝 (mertensLogPowConstantFull 1)) := by
    have h := (tendsto_primeLogPowSum_sub 1).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.congr' ?_
    filter_upwards with N
    simp only [Function.comp]
    norm_num
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogsq : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (2 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp hlog
  -- the Mertens remainder over (log N)² tends to 0
  have h1 : Tendsto (fun N : ℕ =>
      (primeLogPowSum 2 (N : ℝ) - (Real.log N) ^ (2 : ℕ) / 2) / (Real.log N) ^ (2 : ℕ)) atTop (𝓝 0) :=
    hM.div_atTop hlogsq
  -- the prime-power remainder over (log N)² tends to 0
  have h2 : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) / (k : ℝ)) / (Real.log N) ^ (2 : ℕ))
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun N : ℕ => (8 + Mertens.mertensTail) / Real.log (N : ℝ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
    refine squeeze_zero' ?_ ?_ hconst
    · filter_upwards with N
      apply div_nonneg
      · exact Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      · positivity
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      rw [div_le_div_iff₀ (by positivity) hlogpos]
      have := sum_notPrimeVonMangoldt_sq_div_le N
      calc (∑ k ∈ Icc 1 N, Mertens.notPrimeVonMangoldt k ^ (2 : ℕ) / (k : ℝ)) * Real.log (N : ℝ)
          ≤ (Real.log N * (8 + Mertens.mertensTail)) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right this hlogpos.le
        _ = (8 + Mertens.mertensTail) * (Real.log (N : ℝ)) ^ (2 : ℕ) := by ring
  -- assemble
  have hsum := (h1.add h2).add_const (1 / 2 : ℝ)
  simp only [zero_add, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [sum_vonMangoldt_sq_div_eq_primeLogPowSum_add]
  field_simp
  ring

/-! ## The head variance law -/

/-- Mean square of the head on a window, with the corpus's explicit Dirichlet mean value error. -/
theorem mollifiedDeviationHead_meanSquare_window (M : ℕ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ))
        - (T₂ - T₁) * ((∑ k ∈ Icc 1 M, Λ k ^ (2 : ℕ) / (k : ℝ)) / (Real.log M) ^ (2 : ℕ))|
      ≤ 8 * (M : ℝ) * (1 + Real.log M) *
          ((∑ k ∈ Icc 1 M, Λ k ^ (2 : ℕ) / (k : ℝ)) / (Real.log M) ^ (2 : ℕ)) := by
  have h := Sieve.dirichlet_meanValue_window M (mollifiedDeviationHeadCoeff M) T₁ T₂
  rwa [sum_normSq_mollifiedDeviationHeadCoeff] at h

/-- **Head variance law.**  On every window of length at least `M²`, the mean square of the head
`(1/log M) ∑_{k ≤ M} Λ(k) k^{-1/2-it}` is within `ε` of `1/2` once `M` is large. -/
theorem exists_mollifiedDeviationHead_meanSquare_close {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ T₁ T₂ : ℝ, (M : ℝ) ^ (2 : ℕ) ≤ T₂ - T₁ →
      |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ)) / (T₂ - T₁)
          - 1 / 2| < ε := by
  -- the coefficient energy is eventually within ε/2 of 1/2, and 8(1+log M)/M is eventually small
  have hS := tendsto_sum_vonMangoldt_sq_div_div_log_sq
  have hS' := (Metric.tendsto_atTop.mp hS) (ε / 2) (by positivity)
  obtain ⟨M₁, hM₁⟩ := hS'
  have hlogM : Tendsto (fun M : ℕ => 8 * (1 + Real.log (M : ℝ)) / (M : ℝ)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h' : Tendsto (fun M : ℕ => Real.log (M : ℝ) ^ (1 : ℕ) / (1 * (M : ℝ) + 0)) atTop (𝓝 0) :=
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hinv : Tendsto (fun M : ℕ => 8 / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    have := (hinv.add (h'.const_mul 8))
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    field_simp
  have hlog' := (Metric.tendsto_atTop.mp hlogM) (ε / (4 * (1 + ε))) (by positivity)
  obtain ⟨M₂, hM₂⟩ := hlog'
  refine ⟨max (max M₁ M₂) 2, ?_⟩
  intro M hM T₁ T₂ hT
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hM)
  have hM2 : M₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM)
  have hM2' : (2 : ℕ) ≤ M := le_trans (le_max_right _ _) hM
  have hM0 : 0 < M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
  have hlen : (0 : ℝ) < T₂ - T₁ := lt_of_lt_of_le (by positivity) hT
  set S : ℝ := (∑ k ∈ Icc 1 M, Λ k ^ (2 : ℕ) / (k : ℝ)) / (Real.log M) ^ (2 : ℕ) with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    apply div_nonneg
    · exact Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · positivity
  have hSclose : |S - 1 / 2| < ε / 2 := by
    have := hM₁ M hM1
    rwa [Real.dist_eq] at this
  have hS1 : S ≤ 1 + ε := by
    have := abs_lt.mp hSclose
    linarith [this.2]
  have hlogclose : |8 * (1 + Real.log (M : ℝ)) / (M : ℝ) - 0| < ε / (4 * (1 + ε)) := by
    have := hM₂ M hM2
    rwa [Real.dist_eq] at this
  rw [sub_zero, abs_of_nonneg (by positivity)] at hlogclose
  have hwin := mollifiedDeviationHead_meanSquare_window M T₁ T₂
  -- divide the window bound by the window length
  have hdiv : |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ))
      / (T₂ - T₁) - S| ≤ 8 * (M : ℝ) * (1 + Real.log M) * S / (T₂ - T₁) := by
    have : (∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ))
        / (T₂ - T₁) - S
        = ((∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ))
            - (T₂ - T₁) * S) / (T₂ - T₁) := by
      field_simp
    rw [this, abs_div, abs_of_pos hlen]
    exact div_le_div_of_nonneg_right hwin hlen.le
  have hsmall : 8 * (M : ℝ) * (1 + Real.log M) * S / (T₂ - T₁) ≤ ε / 4 := by
    have hlogM0 : 0 ≤ 1 + Real.log (M : ℝ) := by
      have := Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hM2') : (1:ℝ) ≤ M)
      linarith
    calc 8 * (M : ℝ) * (1 + Real.log M) * S / (T₂ - T₁)
        ≤ 8 * (M : ℝ) * (1 + Real.log M) * (1 + ε) / (M : ℝ) ^ (2 : ℕ) := by
          apply div_le_div₀ (by positivity) ?_ (by positivity) hT
          exact mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = (8 * (1 + Real.log (M : ℝ)) / (M : ℝ)) * (1 + ε) := by
          field_simp
      _ ≤ (ε / (4 * (1 + ε))) * (1 + ε) :=
          mul_le_mul_of_nonneg_right hlogclose.le (by positivity)
      _ = ε / 4 := by
          field_simp
  calc |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ)) / (T₂ - T₁)
        - 1 / 2|
      ≤ |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ (2 : ℕ)) / (T₂ - T₁)
          - S| + |S - 1 / 2| := abs_sub_le _ _ _
    _ ≤ ε / 4 + |S - 1 / 2| := by linarith [le_trans hdiv hsmall]
    _ < ε / 4 + ε / 2 := by linarith
    _ ≤ ε := by linarith

end

end RHTower
