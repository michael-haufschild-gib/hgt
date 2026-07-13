import GaloisForLFunctions.SuperexponentialGrowth

/-!
# Quantitative balanced valuation gap for superlacunary magnitudes

For a superlacunary sequence `b` (`b (n+1)/b n → ∞`), every non-balanced index tuple
`t : Fin r → ℕ` with fixed sum `∑ tᵢ = r·M` carries an exponent sum strictly and *quantitatively*
above the balanced value `r·b M`:

`∑ᵢ b (tᵢ) ≥ (r+1)·b M + (r-1)·m₀`,

where `m₀` is a global lower bound for `b`.  The mechanism is not Schur convexity but a one-term
domination: not-all-equal at fixed sum forces some entry `> M`, whose value `b(tₘₐₓ) ≥ b(M+1)` (past
the eventual-monotonicity threshold) already exceeds `(r+1)·b M` because the ratio diverges; the
remaining `r-1` entries cost at least `(r-1)·m₀`.  This is the analytic gap that feeds the
Archimedean bend for full-support magnitude hypertranscendence.
-/

open Filter Finset

namespace GaloisForLFunctions

/-- A superlacunary (eventually positive) `b` has a global lower bound: only finitely many indices
precede the positivity threshold. -/
theorem exists_global_lower_bound {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n) :
    ∃ m₀ : ℝ, ∀ n, m₀ ≤ b n := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hpos
  classical
  refine ⟨min 0 ((Finset.range (N₀ + 1)).inf' (by simp) b), fun n => ?_⟩
  rcases Nat.lt_or_ge n N₀ with h | h
  · exact le_trans (min_le_right _ _) (Finset.inf'_le b (Finset.mem_range.mpr (by omega)))
  · exact le_trans (min_le_left _ _) (le_of_lt (hN₀ n h))

/-- A tuple summing to `r·M` that is not constantly `M` has an entry strictly above `M`
(the maximum exceeds the mean unless the tuple is balanced). -/
theorem exists_index_gt_of_sum_eq {r : ℕ} (t : Fin r → ℕ) (M : ℕ)
    (hsum : (∑ i, t i) = r * M) (hne : ∃ i, t i ≠ M) : ∃ i, M < t i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  obtain ⟨i₀, hi₀⟩ := hne
  have : (∑ i, t i) < ∑ _i : Fin r, M :=
    Finset.sum_lt_sum (fun i _ => h i) ⟨i₀, Finset.mem_univ i₀, lt_of_le_of_ne (h i₀) hi₀⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- Past a threshold, `b` is nondecreasing: increments are positive because `b (n+1) ≥ 2·b n > b n`
once the ratio is at least `2`. -/
theorem exists_eventually_monotone {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ Nm : ℕ, ∀ p q, Nm ≤ p → p ≤ q → b p ≤ b q := by
  have h2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ b (n + 1) / b n := hratio.eventually_ge_atTop 2
  obtain ⟨Nm, hNm⟩ := Filter.eventually_atTop.mp (hpos.and h2)
  refine ⟨Nm, fun p q hp hpq => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.le.dest hpq
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : b (p + d) ≤ b (p + d + 1) := by
      obtain ⟨hbq, hr⟩ := hNm (p + d) (by omega); rw [le_div_iff₀ hbq] at hr; linarith
    calc b p ≤ b (p + d) := ih (by omega)
      _ ≤ b (p + d + 1) := hstep

/-- **Quantitative balanced valuation gap.**  For a superlacunary `b`, every non-balanced tuple
`t : Fin r → ℕ` with `∑ tᵢ = r·M` (past the threshold) has exponent sum at least
`(r+1)·b M + (r-1)·m₀`, `m₀` a global lower bound.  Keep only the strictly-super-mean entry
(`b(tₘₐₓ) ≥ b(M+1) ≥ (r+1)·b M` by monotonicity and diverging ratio) and bound the other `r-1`
entries below by `m₀`. -/
theorem tuple_valuation_gap_lower {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) {r : ℕ} (hr : 0 < r) :
    ∃ (N : ℕ) (m₀ : ℝ), (∀ n, m₀ ≤ b n) ∧ ∀ M, N ≤ M → ∀ t : Fin r → ℕ,
      (∑ i, t i) = r * M → (∃ i, t i ≠ M) →
      ((r : ℝ) + 1) * b M + ((r : ℝ) - 1) * m₀ ≤ ∑ i, b (t i) := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_global_lower_bound hpos
  obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
  have hrr : ∀ᶠ n in atTop, ((r : ℝ) + 1) ≤ b (n + 1) / b n := hratio.eventually_ge_atTop _
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp (hpos.and hrr)
  refine ⟨max Nm Nr, m₀, hm₀, fun M hM t hsum hne => ?_⟩
  obtain ⟨imax, himax⟩ := exists_index_gt_of_sum_eq t M hsum hne
  have hsplit : b (t imax) + ∑ i ∈ Finset.univ.erase imax, b (t i) = ∑ i, b (t i) :=
    Finset.add_sum_erase Finset.univ (fun i => b (t i)) (Finset.mem_univ imax)
  have hrest : ((r : ℝ) - 1) * m₀ ≤ ∑ i ∈ Finset.univ.erase imax, b (t i) := by
    have hcard : (Finset.univ.erase imax).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ imax), Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_nsmul_le_sum (Finset.univ.erase imax) (fun i => b (t i)) m₀
      (fun i _ => hm₀ (t i))
    rw [hcard, nsmul_eq_mul] at hle
    have hcast : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by
      have : 1 ≤ r := hr; push_cast [Nat.cast_sub this]; ring
    rwa [hcast] at hle
  have hmax : ((r : ℝ) + 1) * b M ≤ b (t imax) := by
    have hMr : Nr ≤ M := le_trans (le_max_right _ _) hM
    obtain ⟨hbM, hratM⟩ := hNr M hMr
    have h1 : ((r : ℝ) + 1) * b M ≤ b (M + 1) := by rw [le_div_iff₀ hbM] at hratM; linarith
    have hNmM : Nm ≤ M := le_trans (le_max_left _ _) hM
    have h2 : b (M + 1) ≤ b (t imax) := hmono (M + 1) (t imax) (by omega) (by omega)
    linarith
  linarith [hsplit, hrest, hmax]

/-- **Valuation gap from a super-mean entry.**  The same lower bound `(r+1)·b M + (r-1)·m₀` holds for
*any* tuple with some entry `> M` — no fixed-sum hypothesis.  This covers both the same-sum
non-balanced tuples (`∑ = r·M`, not all `M`) and the larger-sum tuples (`∑ > r·M`) arising from
higher-order differential monomials. -/
theorem tuple_valuation_gap_lower_gt {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) {r : ℕ} (hr : 0 < r) :
    ∃ (N : ℕ) (m₀ : ℝ), (∀ n, m₀ ≤ b n) ∧ ∀ M, N ≤ M → ∀ t : Fin r → ℕ,
      (∃ i, M < t i) → ((r : ℝ) + 1) * b M + ((r : ℝ) - 1) * m₀ ≤ ∑ i, b (t i) := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_global_lower_bound hpos
  obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
  have hrr : ∀ᶠ n in atTop, ((r : ℝ) + 1) ≤ b (n + 1) / b n := hratio.eventually_ge_atTop _
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp (hpos.and hrr)
  refine ⟨max Nm Nr, m₀, hm₀, fun M hM t hex => ?_⟩
  obtain ⟨imax, himax⟩ := hex
  have hsplit : b (t imax) + ∑ i ∈ Finset.univ.erase imax, b (t i) = ∑ i, b (t i) :=
    Finset.add_sum_erase Finset.univ (fun i => b (t i)) (Finset.mem_univ imax)
  have hrest : ((r : ℝ) - 1) * m₀ ≤ ∑ i ∈ Finset.univ.erase imax, b (t i) := by
    have hcard : (Finset.univ.erase imax).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ imax), Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_nsmul_le_sum (Finset.univ.erase imax) (fun i => b (t i)) m₀
      (fun i _ => hm₀ (t i))
    rw [hcard, nsmul_eq_mul] at hle
    have hcast : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by
      have : 1 ≤ r := hr; push_cast [Nat.cast_sub this]; ring
    rwa [hcast] at hle
  have hmax : ((r : ℝ) + 1) * b M ≤ b (t imax) := by
    have hMr : Nr ≤ M := le_trans (le_max_right _ _) hM
    obtain ⟨hbM, hratM⟩ := hNr M hMr
    have h1 : ((r : ℝ) + 1) * b M ≤ b (M + 1) := by rw [le_div_iff₀ hbM] at hratM; linarith
    have hNmM : Nm ≤ M := le_trans (le_max_left _ _) hM
    have h2 : b (M + 1) ≤ b (t imax) := hmono (M + 1) (t imax) (by omega) (by omega)
    linarith
  linarith [hsplit, hrest, hmax]

/-- **Threshold gap.**  The super-mean valuation bound with an arbitrary ratio threshold `K` in place
of `r+1`.  For the mixed-degree combine, applying it with a single `K` (e.g. the top degree `+1`) for
every arity `r` makes a lower-degree differential monomial dominated by the leading one despite having
fewer factors: a single entry `> M` already forces exponent `≥ b (M+1) ≥ K·b M`. -/
theorem tuple_valuation_gap_threshold {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (K : ℝ) {r : ℕ} :
    ∃ (N : ℕ) (m₀ : ℝ), (∀ n, m₀ ≤ b n) ∧ ∀ M, N ≤ M → ∀ t : Fin r → ℕ,
      (∃ i, M < t i) → K * b M + ((r : ℝ) - 1) * m₀ ≤ ∑ i, b (t i) := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_global_lower_bound hpos
  obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
  have hrr : ∀ᶠ n in atTop, K ≤ b (n + 1) / b n := hratio.eventually_ge_atTop _
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp (hpos.and hrr)
  refine ⟨max Nm Nr, m₀, hm₀, fun M hM t hex => ?_⟩
  obtain ⟨imax, himax⟩ := hex
  have hsplit : b (t imax) + ∑ i ∈ Finset.univ.erase imax, b (t i) = ∑ i, b (t i) :=
    Finset.add_sum_erase Finset.univ (fun i => b (t i)) (Finset.mem_univ imax)
  have hrest : ((r : ℝ) - 1) * m₀ ≤ ∑ i ∈ Finset.univ.erase imax, b (t i) := by
    have hcard : (Finset.univ.erase imax).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ imax), Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_nsmul_le_sum (Finset.univ.erase imax) (fun i => b (t i)) m₀
      (fun i _ => hm₀ (t i))
    rw [hcard, nsmul_eq_mul] at hle
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0; exact imax.elim0
    · have hcast : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by push_cast [Nat.cast_sub hrpos]; ring
      rwa [hcast] at hle
  have hmax : K * b M ≤ b (t imax) := by
    have hMr : Nr ≤ M := le_trans (le_max_right _ _) hM
    obtain ⟨hbM, hratM⟩ := hNr M hMr
    have h1 : K * b M ≤ b (M + 1) := by rw [le_div_iff₀ hbM] at hratM; linarith
    have hNmM : Nm ≤ M := le_trans (le_max_left _ _) hM
    have h2 : b (M + 1) ≤ b (t imax) := hmono (M + 1) (t imax) (by omega) (by omega)
    linarith
  linarith [hsplit, hrest, hmax]

/-- **Superlacunary magnitudes dominate any logarithm.**  Since `b n / n → ∞`, for every slope `A`
and offset `K` eventually `A·log(M+2) + K ≤ b M`.  This clears the `2·log B` coefficient-count term
in the Archimedean bend against the balanced valuation gap. -/
theorem exists_dominates_log {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (A K : ℝ) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → A * Real.log ((M : ℝ) + 2) + K ≤ b M := by
  have htend := tendsto_div_natCast_atTop_of_ratio_tendsto_atTop hpos hratio
  set D : ℝ := 2 * (|A| + |K|) + 1 with hD
  obtain ⟨Nt, hNt⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop D)
  refine ⟨max Nt 1, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hM1r : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hbM : D * (M : ℝ) ≤ b M := by
    have hge := hNt M (le_trans (le_max_left _ _) hM)
    rw [le_div_iff₀ hMpos] at hge; exact hge
  have hlog : Real.log ((M : ℝ) + 2) ≤ (M : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (M : ℝ) + 2 by positivity); linarith
  have hlognn : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hA : A * Real.log ((M : ℝ) + 2) ≤ |A| * ((M : ℝ) + 1) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self A) hlognn)
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg A))
  have hAbound : |A| * ((M : ℝ) + 1) ≤ 2 * |A| * (M : ℝ) := by nlinarith [abs_nonneg A, hM1r]
  have hKbound : K ≤ 2 * |K| * (M : ℝ) :=
    le_trans (le_abs_self K)
      (by nlinarith [mul_nonneg (abs_nonneg K) (show (0 : ℝ) ≤ 2 * (M : ℝ) - 1 by linarith)])
  have hDM : 2 * |A| * (M : ℝ) + 2 * |K| * (M : ℝ) ≤ D * (M : ℝ) := by rw [hD]; nlinarith [hMpos]
  linarith [hbM, hA, hAbound, hKbound, hDM]

/-- **Higher-jet magnitude ratio vanishes.**  For superlacunary `b`, the falling-factorial-
weighted magnitude of a higher-order jet coefficient, normalised by the lowest order, tends to
zero: `(N+j)^j · exp(-b (N+jmin)) → 0`.  The polynomial falling-factorial growth is beaten by the
superlacunary decay (`b (N+jmin) ≥ (j+1)·log(N+jmin+2)` eventually).  This is the domination that
makes the derivative jets `Fᵍ` linearly independent for a superlacunary-magnitude series. -/
theorem jet_ratio_tendsto_zero {b : ℕ → ℝ} (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (jmin j : ℕ) :
    Tendsto (fun N => (((N + j) ^ j : ℕ) : ℝ) * Real.exp (- b (N + jmin))) atTop (nhds 0) := by
  obtain ⟨Nd, hNd⟩ := exists_dominates_log hpos hratio ((j : ℝ) + 1) 0
  have hbound : ∀ᶠ N in atTop, (((N + j) ^ j : ℕ) : ℝ) * Real.exp (- b (N + jmin))
      ≤ (2 : ℝ) ^ j / N := by
    refine Filter.eventually_atTop.mpr ⟨max (max Nd j) 1, fun N hN => ?_⟩
    have hNd' : Nd ≤ N + jmin := by
      have : Nd ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN; omega
    have hNj : j ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hg := hNd (N + jmin) hNd'
    rw [add_zero] at hg
    -- (N+j)^j = exp(j*log(N+j))
    have hNjpos : (0 : ℝ) < (N : ℝ) + j := by positivity
    have hpow : (((N + j) ^ j : ℕ) : ℝ) = Real.exp ((j : ℝ) * Real.log ((N : ℝ) + j)) := by
      rw [Real.exp_nat_mul, Real.exp_log hNjpos]; push_cast; ring
    rw [hpow, ← Real.exp_add]
    have hexp_le : (j : ℝ) * Real.log ((N : ℝ) + j) + (- b (N + jmin))
        ≤ (j : ℝ) * Real.log 2 - Real.log N := by
      have hlogNj : Real.log ((N : ℝ) + j) ≤ Real.log 2 + Real.log N := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        apply Real.log_le_log hNjpos
        have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNj
        nlinarith [hNr, hjN]
      have hxge : Real.log ↑N ≤ Real.log ((N : ℝ) + ↑jmin + 2) :=
        Real.log_le_log (by linarith [hNr])
          (by have := Nat.cast_nonneg jmin (α := ℝ); linarith)
      have hgcast : ((j : ℝ) + 1) * Real.log ((N : ℝ) + ↑jmin + 2) ≤ b (N + jmin) := by
        convert hg using 3; push_cast; ring
      nlinarith [hlogNj, hxge, hgcast, mul_le_mul_of_nonneg_left hlogNj (by positivity : (0:ℝ) ≤ (j:ℝ))]
    calc Real.exp ((j : ℝ) * Real.log ((N : ℝ) + j) + (- b (N + jmin)))
        ≤ Real.exp ((j : ℝ) * Real.log 2 - Real.log N) := Real.exp_le_exp.mpr hexp_le
      _ = (2 : ℝ) ^ j / N := by
          rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2),
            Real.exp_log (by linarith)]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N => by positivity)) hbound ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat ((2 : ℝ) ^ j))

end GaloisForLFunctions
