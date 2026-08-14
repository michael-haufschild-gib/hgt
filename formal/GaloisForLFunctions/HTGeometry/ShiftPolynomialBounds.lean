import GaloisForLFunctions.HTGeometry.FormalEulerOperator

/-!
# Size of the shift polynomials of a linear operator with convergent coefficients

Two estimates drive the growth of a formal solution.

*Above*: if every coefficient `B_j` of the operator is a convergent power series, its `μ`-th
coefficient decays geometrically in `μ`, so the shift polynomial `Φ_μ` is bounded by
`C ρ^μ (1+k)^m` at every integer argument `k` — geometric in the shift, polynomial of the operator
order in the argument.

*Below*: the shift polynomial at shift zero is bounded **below** by a multiple of `(1+n)^{deg Φ_0}`
for all large `n`, because a nonzero polynomial is dominated by its leading term.  Dividing by it is
what turns the coefficient convolution into a recursion.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-! ### A nonzero polynomial is bounded below by its leading power -/

/-- **A nonzero complex polynomial is bounded below along the natural numbers by a multiple of the
power of its degree.** -/
theorem exists_lower_bound_eval_natCast (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * ((n : ℝ) + 1) ^ P.natDegree ≤ ‖P.eval ((n : ℕ) : ℂ)‖ := by
  classical
  set d : ℕ := P.natDegree with hd
  set a : ℂ := P.coeff d with ha
  have ha0 : a ≠ 0 := by
    rw [ha, hd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hapos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
  set S : ℝ := ∑ i ∈ Finset.range d, ‖P.coeff i‖ with hS
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  -- the tail is dominated by the top power for large arguments
  have hsplit : ∀ n : ℕ, P.eval ((n : ℕ) : ℂ)
      = (∑ i ∈ Finset.range d, P.coeff i * ((n : ℕ) : ℂ) ^ i) + a * ((n : ℕ) : ℂ) ^ d := by
    intro n
    rw [Polynomial.eval_eq_sum_range, ← hd, Finset.sum_range_succ]
  have htail : ∀ n : ℕ, 1 ≤ n →
      ‖∑ i ∈ Finset.range d, P.coeff i * ((n : ℕ) : ℂ) ^ i‖ ≤ S * (n : ℝ) ^ (d - 1) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine le_trans (norm_sum_le _ _) ?_
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hid : i ≤ d - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hnorm : ‖P.coeff i * ((n : ℕ) : ℂ) ^ i‖ = ‖P.coeff i‖ * (n : ℝ) ^ i := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hid) (norm_nonneg _)
  refine ⟨‖a‖ / 2 ^ (d + 1), by positivity, max 1 ⌈2 * S / ‖a‖⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnS : 2 * S / ‖a‖ ≤ (n : ℝ) := by
    have h1 : (⌈2 * S / ‖a‖⌉₊ : ℕ) ≤ n := le_trans (le_max_right _ _) hn
    have h2 : (2 * S / ‖a‖) ≤ (⌈2 * S / ‖a‖⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈2 * S / ‖a‖⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hSa : 2 * S ≤ ‖a‖ * (n : ℝ) := by
    rw [div_le_iff₀ hapos] at hnS
    linarith
  -- the lower bound on the top power
  have hlow : ‖a‖ / 2 * (n : ℝ) ^ d ≤ ‖P.eval ((n : ℕ) : ℂ)‖ := by
    have htop : ‖a * ((n : ℕ) : ℂ) ^ d‖ = ‖a‖ * (n : ℝ) ^ d := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hsub : ‖a * ((n : ℕ) : ℂ) ^ d‖ - ‖∑ i ∈ Finset.range d, P.coeff i * ((n : ℕ) : ℂ) ^ i‖
        ≤ ‖P.eval ((n : ℕ) : ℂ)‖ := by
      rw [hsplit n]
      have hrev := norm_sub_le
        ((∑ i ∈ Finset.range d, P.coeff i * ((n : ℕ) : ℂ) ^ i) + a * ((n : ℕ) : ℂ) ^ d)
        (∑ i ∈ Finset.range d, P.coeff i * ((n : ℕ) : ℂ) ^ i)
      simp only [add_sub_cancel_left] at hrev
      linarith
    rw [htop] at hsub
    have htail' := htail n hn1
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [hd0] at hsub htail' ⊢
      simp only [Finset.range_zero, Finset.sum_empty, norm_zero, pow_zero] at hsub ⊢
      linarith
    · have hpow : (n : ℝ) ^ d = (n : ℝ) * (n : ℝ) ^ (d - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (d - 1) := by positivity
      nlinarith [hsub, htail', hpow, hpos, hSa]
  refine le_trans ?_ hlow
  have hstep : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d := by
    refine pow_le_pow_left₀ (by positivity) (by linarith) d
  calc ‖a‖ / 2 ^ (d + 1) * ((n : ℝ) + 1) ^ d
      ≤ ‖a‖ / 2 ^ (d + 1) * (2 * (n : ℝ)) ^ d := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ‖a‖ / 2 * (n : ℝ) ^ d := by
        rw [mul_pow, pow_succ]
        field_simp

/-! ### The shift polynomials of a convergent operator -/

/-- **The shift polynomials decay geometrically in the shift and grow at most polynomially in the
argument.** -/
theorem exists_bound_shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ (μ k : ℕ),
      ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * ((k : ℝ) + 1) ^ m := by
  classical
  choose C A hC hA hbound using hB
  set Cmax : ℝ := ∑ j : Fin (m + 1), C j with hCmax
  set ρ : ℝ := (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty A with hρ
  have hρpos : 0 < ρ := by
    obtain ⟨j⟩ : Nonempty (Fin (m + 1)) := ⟨⟨0, Nat.succ_pos m⟩⟩
    exact lt_of_lt_of_le (hA j) (Finset.le_sup' A (Finset.mem_univ j))
  have hAle : ∀ j, A j ≤ ρ := fun j => Finset.le_sup' A (Finset.mem_univ j)
  have hCmax0 : (0 : ℝ) ≤ Cmax := Finset.sum_nonneg fun j _ => le_of_lt (hC j)
  have hCpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * (Cmax + 1) := by
    have h1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith [hCmax0]
  refine ⟨((m + 1 : ℕ) : ℝ) * (Cmax + 1), ρ, hCpos, hρpos, fun μ k => ?_⟩
  have hterm : ∀ j : Fin (m + 1),
      ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖
        ≤ C j * ρ ^ μ * ((k : ℝ) + 1) ^ m := by
    intro j
    have h1 : ‖PowerSeries.coeff μ (B j)‖ ≤ C j * A j ^ μ := by
      have := hbound j μ
      simpa using this
    have h2 : ‖((k : ℕ) : ℂ) ^ (j : ℕ)‖ ≤ ((k : ℝ) + 1) ^ m := by
      rw [norm_pow, Complex.norm_natCast]
      calc (k : ℝ) ^ (j : ℕ) ≤ ((k : ℝ) + 1) ^ (j : ℕ) :=
            pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) _
        _ ≤ ((k : ℝ) + 1) ^ m := by
            refine pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) ?_
            exact Nat.lt_succ_iff.mp j.isLt
    have hAρ : A j ^ μ ≤ ρ ^ μ := pow_le_pow_left₀ (le_of_lt (hA j)) (hAle j) μ
    calc ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖
        = ‖PowerSeries.coeff μ (B j)‖ * ‖((k : ℕ) : ℂ) ^ (j : ℕ)‖ := norm_mul _ _
      _ ≤ (C j * A j ^ μ) * ((k : ℝ) + 1) ^ m :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg (le_of_lt (hC j)) (le_of_lt (pow_pos (hA j) μ)))
      _ ≤ (C j * ρ ^ μ) * ((k : ℝ) + 1) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hAρ (le_of_lt (hC j))
      _ = C j * ρ ^ μ * ((k : ℝ) + 1) ^ m := by ring
  calc ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖
      = ‖∑ j : Fin (m + 1), PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖ := by
        rw [eval_shiftPolynomial]
    _ ≤ ∑ j : Fin (m + 1), ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin (m + 1), (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ m := by
        refine Finset.sum_le_sum fun j _ => le_trans (hterm j) ?_
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        have hCj : C j ≤ Cmax := by
          rw [hCmax]
          exact Finset.single_le_sum (f := fun j : Fin (m + 1) => C j)
            (fun i _ => le_of_lt (hC i)) (Finset.mem_univ j)
        linarith
    _ = ((m + 1 : ℕ) : ℝ) * ((Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ m) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (((m + 1 : ℕ) : ℝ) * (Cmax + 1)) * ρ ^ μ * ((k : ℝ) + 1) ^ m := by ring

/-! ### The Newton-polygon form of the bound -/

/-- **The shift polynomials obey the Newton bound.**  If every coefficient of the operator that is
present at shift `μ` has index at most `d + r μ`, then the shift polynomial at that shift grows no
faster than `(k+1)^{d + r μ}`. -/
theorem exists_bound_shiftPolynomial_newton {m d : ℕ} {r : ℝ}
    (B : Fin (m + 1) → PowerSeries ℂ) (hB : ∀ j, IsGevreySeries 0 (B j))
    (hdeg : ∀ (μ : ℕ) (j : Fin (m + 1)), 1 ≤ μ → PowerSeries.coeff μ (B j) ≠ 0 →
      ((j : ℕ) : ℝ) ≤ (d : ℝ) + r * μ) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ (μ k : ℕ), 1 ≤ μ →
      ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖
        ≤ C * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by
  classical
  choose C A hC hA hbound using hB
  set Cmax : ℝ := ∑ j : Fin (m + 1), C j with hCmax
  set ρ : ℝ := (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty A with hρ
  have hρpos : 0 < ρ := by
    obtain ⟨j⟩ : Nonempty (Fin (m + 1)) := ⟨⟨0, Nat.succ_pos m⟩⟩
    exact lt_of_lt_of_le (hA j) (Finset.le_sup' A (Finset.mem_univ j))
  have hAle : ∀ j, A j ≤ ρ := fun j => Finset.le_sup' A (Finset.mem_univ j)
  have hCmax0 : (0 : ℝ) ≤ Cmax := Finset.sum_nonneg fun j _ => le_of_lt (hC j)
  have hCpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * (Cmax + 1) := by
    have h1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith [hCmax0]
  refine ⟨((m + 1 : ℕ) : ℝ) * (Cmax + 1), ρ, hCpos, hρpos, fun μ k hμ => ?_⟩
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hterm : ∀ j : Fin (m + 1),
      ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖
        ≤ C j * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by
    intro j
    by_cases hz : PowerSeries.coeff μ (B j) = 0
    · rw [hz]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt (hC j)) (le_of_lt (pow_pos hρpos μ)))
        (le_of_lt (Real.rpow_pos_of_pos (by linarith) _))
    · have h1 : ‖PowerSeries.coeff μ (B j)‖ ≤ C j * A j ^ μ := by
        have := hbound j μ
        simpa using this
      have hjle : ((j : ℕ) : ℝ) ≤ (d : ℝ) + r * μ := hdeg μ j hμ hz
      have h2 : ‖((k : ℕ) : ℂ) ^ (j : ℕ)‖ ≤ ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by
        rw [norm_pow, Complex.norm_natCast]
        calc (k : ℝ) ^ (j : ℕ) ≤ ((k : ℝ) + 1) ^ (j : ℕ) :=
              pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) _
          _ = ((k : ℝ) + 1) ^ (((j : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
          _ ≤ ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) :=
              Real.rpow_le_rpow_of_exponent_le hk1 hjle
      have hAρ : A j ^ μ ≤ ρ ^ μ := pow_le_pow_left₀ (le_of_lt (hA j)) (hAle j) μ
      calc ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖
          = ‖PowerSeries.coeff μ (B j)‖ * ‖((k : ℕ) : ℂ) ^ (j : ℕ)‖ := norm_mul _ _
        _ ≤ (C j * A j ^ μ) * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) :=
            mul_le_mul h1 h2 (norm_nonneg _)
              (mul_nonneg (le_of_lt (hC j)) (le_of_lt (pow_pos (hA j) μ)))
        _ ≤ (C j * ρ ^ μ) * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hAρ (le_of_lt (hC j))
        _ = C j * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by ring
  calc ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖
      = ‖∑ j : Fin (m + 1), PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖ := by
        rw [eval_shiftPolynomial]
    _ ≤ ∑ j : Fin (m + 1), ‖PowerSeries.coeff μ (B j) * ((k : ℕ) : ℂ) ^ (j : ℕ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin (m + 1), (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by
        refine Finset.sum_le_sum fun j _ => le_trans (hterm j) ?_
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        have hCj : C j ≤ Cmax := by
          rw [hCmax]
          exact Finset.single_le_sum (f := fun j : Fin (m + 1) => C j)
            (fun i _ => le_of_lt (hC i)) (Finset.mem_univ j)
        linarith
    _ = ((m + 1 : ℕ) : ℝ) * ((Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (((m + 1 : ℕ) : ℝ) * (Cmax + 1)) * ρ ^ μ * ((k : ℝ) + 1) ^ ((d : ℝ) + r * μ) := by ring

end GaloisForLFunctions.HTGeometry
