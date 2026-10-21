import GaloisForLFunctions.BezoutValuationIncidence.ExactTypeIILossOfTheReceiverGram

/-!
# The exact rank-two cross-scale law of the receiver Gram

For rows `c, c'` the receiver's bilinear form is `B(c, c') = Σ_M V_c(M) V_{c'}(M)/(M(M+1))`, with
`V_c(M) = R(c) - Σ_n c(n) (M mod n)/n`. Split the small-scale row into mean and fluctuation and the
large-scale row into ramp and steps:

`V_c = m(c) + F_c`,  `m(c) = R(c) - Σ_n c(n) (n-1)/(2n)`,  `F_c(M) = -Σ_n (c(n)/n) ((M mod n) - (n-1)/2)`,

`V_{c'}(M) = R(c') - M H(c') + Σ_n c'(n) ⌊M/n⌋`,  `H(c') = Σ_n c'(n)/n`.

The interval sums of `F_c` are at most `K_c = Σ_n |c(n)| n/2`, so `β(c) = Σ_{M ≥ 1} F_c(M)/(M+1)`
converges (Dirichlet), and Abel summation of `F_c` against the steps `1[jn ≤ M]` gives the exact
rank-two law

`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ 2 K_c Σ_n |c'(n)|/n²`.

Across scales the receiver Gram is the rank-two form `-m(c) R(c') - β(c) H(c')` up to a remainder
`O(K_c ‖c'‖_{1/n²})`: for `c` on `(P, 2P]` and `c'` on `(Q, 2Q]` the remainder is
`‖c‖₁ ‖c'‖₁ P/Q²` against the rank-two size `‖c‖₁ ‖c'‖₁ (log Q)/Q`.

For two single moduli `e < q` this is a sign law: with `D_e = (e-1)/2 - log e`,

`e q B(δ_e, δ_q) = D_e log q - e β(δ_e) + O(e²/q)`,

and `D_e < 0` exactly for `e ∈ {2, 3}`. The far-scale coupling of the moduli `2` and `3` to every
large modulus is negative and grows like `-(log q)`, while every modulus `e ≥ 4` couples positively.
-/

open Finset ArithmeticFunction RHTower Filter Topology GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Mean, fluctuation, ramp and steps of a row -/

/-- The long-run mean of the receiver value of a row. -/
def rowMean (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  vonMangoldtReadout N c - ∑ n ∈ Icc 1 N, c n * ((n : ℝ) - 1) / (2 * n)

/-- The fast fluctuation of the receiver value of a row. -/
def rowFluct (N : ℕ) (c : ℕ → ℝ) (M : ℕ) : ℝ :=
  -∑ n ∈ Icc 1 N, c n / n * centeredResidue n M

/-- The interval-sum bound `K_c = Σ_n |c(n)| n/2` of the fluctuation. -/
def rowFluctBound (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 N, |c n| * n / 2

theorem rowValue_eq_mean_add_fluct (N M : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPrefixDiscrepancy N M c = rowMean N c + rowFluct N c M := by
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue, rowMean, rowFluct]
  unfold centeredResidue
  rw [← sum_neg_distrib]
  have h : ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n =
      ∑ n ∈ Icc 1 N, c n * ((n : ℝ) - 1) / (2 * n) +
        ∑ n ∈ Icc 1 N, c n / n * (((M % n : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [h, sum_neg_distrib]
  ring

theorem abs_sum_Ico_rowFluct_le (N : ℕ) (c : ℕ → ℝ) (A L : ℕ) :
    |∑ M ∈ Ico A (A + L), rowFluct N c M| ≤ rowFluctBound N c := by
  unfold rowFluct rowFluctBound
  rw [sum_neg_distrib, abs_neg, sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn1 : 0 < n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [← mul_sum, abs_mul, abs_div, abs_of_pos hn0]
  calc |c n| / n * |∑ M ∈ Ico A (A + L), centeredResidue n M|
      ≤ |c n| / n * ((n : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sum_Ico_centeredResidue_le n hn1 A L) (by positivity)
    _ = |c n| * n / 2 := by field_simp

theorem rowFluctBound_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ rowFluctBound N c :=
  sum_nonneg fun _ _ => by positivity

/-- The slow factor: `V_{c'}(M) = R(c') - M H(c') + Σ_n c'(n) ⌊M/n⌋`. -/
theorem rowValue_eq_ramp_add_steps (N M : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPrefixDiscrepancy N M c = vonMangoldtReadout N c -
      M * finiteHarmonicSum N c + ∑ n ∈ Icc 1 N, c n * ((M / n : ℕ) : ℝ) := by
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue, finiteHarmonicSum, mul_sum]
  have h : ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n =
      ∑ n ∈ Icc 1 N, (M : ℝ) * (c n / n) - ∑ n ∈ Icc 1 N, c n * ((M / n : ℕ) : ℝ) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div M n)
    push_cast at this
    have hmod : ((M % n : ℕ) : ℝ) = M - n * (M / n : ℕ) := by linarith
    rw [hmod]
    field_simp
  rw [h]
  ring

/-! ## §2. The Dirichlet constant `β(c)` -/

theorem cauchySeq_rowFluct_harmonic (N : ℕ) (c : ℕ → ℝ) :
    CauchySeq fun H : ℕ => ∑ M ∈ Ico 1 H, rowFluct N c M / ((M : ℝ) + 1) := by
  have hK := rowFluctBound_nonneg N c
  have htail : ∀ A H, A ≤ H → |∑ M ∈ Ico A H, rowFluct N c M / ((M : ℝ) + 1)| ≤
      rowFluctBound N c * (1 / ((A : ℝ) + 1)) := by
    intro A H _
    have := abs_sum_Ico_mul_antitone_le (x := rowFluct N c) (w := fun M : ℕ => 1 / ((M : ℝ) + 1))
      hK (fun M => by positivity)
      (fun i j hij => one_div_le_one_div_of_le (by positivity)
        (by have : (i : ℝ) ≤ j := by exact_mod_cast hij
            linarith)) (abs_sum_Ico_rowFluct_le N c) A H
    calc |∑ M ∈ Ico A H, rowFluct N c M / ((M : ℝ) + 1)|
        = |∑ M ∈ Ico A H, 1 / ((M : ℝ) + 1) * rowFluct N c M| := by
          congr 1; exact sum_congr rfl fun _ _ => by ring
      _ ≤ _ := this
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨A, hA⟩ := exists_nat_gt (rowFluctBound N c / ε)
  refine ⟨A + 1, fun H hH => ?_⟩
  rw [Real.dist_eq, ← sum_Ico_consecutive _ (by omega : 1 ≤ A + 1) hH, add_sub_cancel_left]
  refine lt_of_le_of_lt (htail (A + 1) H hH) ?_
  have hA1 : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [mul_one_div, div_lt_iff₀ hA1]
  rw [div_lt_iff₀ hε] at hA
  push_cast
  nlinarith

/-- `β(c) = Σ_{M ≥ 1} F_c(M)/(M+1)`, a conditionally convergent series. -/
def rowBeta (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  limUnder atTop fun H : ℕ => ∑ M ∈ Ico 1 H, rowFluct N c M / ((M : ℝ) + 1)

theorem tendsto_rowBeta (N : ℕ) (c : ℕ → ℝ) :
    Tendsto (fun H : ℕ => ∑ M ∈ Ico 1 H, rowFluct N c M / ((M : ℝ) + 1)) atTop
      (𝓝 (rowBeta N c)) :=
  (cauchySeq_rowFluct_harmonic N c).tendsto_limUnder

/-! ## §3. The rank-two law -/

/-- The receiver's bilinear form `B(c, c') = Σ_M V_c(M) V_{c'}(M)/(M(M+1))`. -/
def rowBilinear (N : ℕ) (c c' : ℕ → ℝ) : ℝ :=
  ∑' M : ℕ, sieveEnergyCenteredPrefixDiscrepancy N M c *
    sieveEnergyCenteredPrefixDiscrepancy N M c' / (pronicSeq M : ℝ)

theorem abs_rowValue_le (N M : ℕ) (c : ℕ → ℝ) :
    |sieveEnergyCenteredPrefixDiscrepancy N M c| ≤
      |vonMangoldtReadout N c| + ∑ n ∈ Icc 1 N, |c n| := by
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue]
  exact (abs_sub _ _).trans (add_le_add le_rfl (abs_residueSum_le_l1 N M c))

theorem hasSum_rowBilinear (N : ℕ) (c c' : ℕ → ℝ) :
    HasSum (fun M : ℕ => sieveEnergyCenteredPrefixDiscrepancy N M c *
      sieveEnergyCenteredPrefixDiscrepancy N M c' / (pronicSeq M : ℝ)) (rowBilinear N c c') := by
  refine (summable_div_pronicSeq_of_bounded (B := (|vonMangoldtReadout N c| +
    ∑ n ∈ Icc 1 N, |c n|) * (|vonMangoldtReadout N c'| + ∑ n ∈ Icc 1 N, |c' n|))
    fun M => ?_).hasSum
  rw [abs_mul]
  exact mul_le_mul (abs_rowValue_le N M c) (abs_rowValue_le N M c') (abs_nonneg _)
    (by positivity)

/-- The step sum `Σ_n c'(n) Σ_{M < H} F_c(M) ⌊M/n⌋/(M(M+1))` converges to
`B(c, c') + m(c) R(c') + β(c) H(c')`. -/
theorem tendsto_rowStepSum (N : ℕ) (c c' : ℕ → ℝ) :
    Tendsto (fun H : ℕ => ∑ n ∈ Icc 1 N, c' n *
      ∑ M ∈ range H, rowFluct N c M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)) atTop
      (𝓝 (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c')) := by
  set m := rowMean N c
  set R' := vonMangoldtReadout N c'
  set H' := finiteHarmonicSum N c'
  set V := fun M => sieveEnergyCenteredPrefixDiscrepancy N M c
  set V' := fun M => sieveEnergyCenteredPrefixDiscrepancy N M c'
  set F := rowFluct N c
  set X : ℕ → ℝ := fun H => ∑ M ∈ range H, V M * V' M / (pronicSeq M : ℝ) -
    m * ∑ M ∈ range H, V' M / (pronicSeq M : ℝ) -
    R' * (∑ M ∈ range H, V M / (pronicSeq M : ℝ) - m * ∑ M ∈ range H, 1 / (pronicSeq M : ℝ)) +
    H' * ∑ M ∈ Ico 1 H, F M / ((M : ℝ) + 1) with hX
  have hlim : Tendsto X atTop (𝓝 (rowBilinear N c c' + m * R' + rowBeta N c * H')) := by
    have h1 := (hasSum_rowBilinear N c c').tendsto_sum_nat
    have h2 := (hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq N c').tendsto_sum_nat
    have h3 := (hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq N c).tendsto_sum_nat
    have h4 := hasSum_one_div_pronicSeq_nat.tendsto_sum_nat
    have h5 := tendsto_rowBeta N c
    have := ((h1.sub (h2.const_mul m)).sub ((h3.sub (h4.const_mul m)).const_mul R')).add
      (h5.const_mul H')
    convert this using 2
    ring
  refine hlim.congr fun H => ?_
  have hpt : ∀ M, V M * V' M / (pronicSeq M : ℝ) - m * (V' M / (pronicSeq M : ℝ)) -
      R' * (V M / (pronicSeq M : ℝ) - m * (1 / (pronicSeq M : ℝ))) =
      -H' * ((M : ℝ) * F M / (pronicSeq M : ℝ)) +
        ∑ n ∈ Icc 1 N, c' n * (F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)) := by
    intro M
    have hva : V M = m + F M := rowValue_eq_mean_add_fluct N M c
    have hvb : V' M - R' = -(M : ℝ) * H' + ∑ n ∈ Icc 1 N, c' n * ((M / n : ℕ) : ℝ) := by
      have := rowValue_eq_ramp_add_steps N M c'
      simp only [V', R', H']
      linarith
    have e1 : V M * V' M / (pronicSeq M : ℝ) - m * (V' M / (pronicSeq M : ℝ)) -
        R' * (V M / (pronicSeq M : ℝ) - m * (1 / (pronicSeq M : ℝ))) =
        F M * (V' M - R') / (pronicSeq M : ℝ) := by
      rw [hva]; ring
    rw [e1, hvb, mul_add, add_div, mul_sum, sum_div]
    congr 1
    · ring
    · exact sum_congr rfl fun _ _ => by ring
  have hcomb : X H = ∑ M ∈ range H, (V M * V' M / (pronicSeq M : ℝ) -
      m * (V' M / (pronicSeq M : ℝ)) -
        R' * (V M / (pronicSeq M : ℝ) - m * (1 / (pronicSeq M : ℝ)))) +
      H' * ∑ M ∈ Ico 1 H, F M / ((M : ℝ) + 1) := by
    simp only [hX, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
  have hshift : ∑ M ∈ range H, (M : ℝ) * F M / (pronicSeq M : ℝ) =
      ∑ M ∈ Ico 1 H, F M / ((M : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos H with h0 | hH
    · subst h0; simp
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hH]
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, zero_add]
    refine sum_congr rfl fun M hM => ?_
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (mem_Ico.mp hM).1
    rw [cast_pronicSeq_eq]
    field_simp
  rw [hcomb, sum_congr rfl fun M _ => hpt M, sum_add_distrib, ← mul_sum, hshift, sum_comm]
  simp only [← mul_sum]
  ring

/-- **Exact rank-two cross-scale law of the receiver Gram.**
`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ 2 K_c Σ_n |c'(n)|/n²`. -/
theorem abs_rowBilinear_add_mean_add_beta_le (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      2 * rowFluctBound N c * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
  set K := rowFluctBound N c
  have hK : 0 ≤ K := rowFluctBound_nonneg N c
  have hF : ∀ A L, |∑ M ∈ Ico A (A + L), rowFluct N c M| ≤ K := abs_sum_Ico_rowFluct_le N c
  clear_value K
  set F := rowFluct N c
  refine le_of_tendsto (tendsto_rowStepSum N c c').abs (Eventually.of_forall fun H => ?_)
  -- every step `1[jn ≤ M]` costs `K w(jn)`
  have hstep : ∀ n ∈ Icc 1 N, |∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)| ≤
      2 * K / (n : ℝ) ^ 2 := by
    intro n hn
    have hn1 : 0 < n := (mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hexp : ∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ) =
        ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, pronicWeightAntitone M * F M := by
      rw [sum_congr rfl fun M hM => by
        rw [cast_div_eq_sum_steps hn1 (mem_range.mp hM), mul_sum, sum_div], sum_comm]
      refine sum_congr rfl fun j hj => ?_
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      simp_rw [mul_ite, mul_one, mul_zero, ite_div, zero_div]
      rw [← sum_filter]
      have hset : (range H).filter (fun M => j * n ≤ M) = Ico (j * n) H := by
        ext M; simp only [mem_filter, mem_range, mem_Ico]; tauto
      rw [hset]
      refine sum_congr rfl fun M hM => ?_
      have hjn : 1 ≤ M := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) (mem_Ico.mp hM).1
      rw [pronicWeightAntitone_of_pos hjn, cast_pronicSeq_eq]
      ring
    rw [hexp]
    have hj : ∀ j ∈ Icc 1 H, |∑ M ∈ Ico (j * n) H, pronicWeightAntitone M * F M| ≤
        K * (2 / ((n : ℝ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)))) := by
      intro j hj
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      refine (abs_sum_Ico_mul_antitone_le hK (fun M => by unfold pronicWeightAntitone; positivity)
        pronicWeightAntitone_antitone hF _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [pronicWeightAntitone_of_pos hjn]
      have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hjn' : (n : ℝ) ≤ j * n + 2 := by nlinarith
      have hpos : (0 : ℝ) ≤ (j : ℝ) * n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hjn' hpos]
    calc |∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, pronicWeightAntitone M * F M|
        ≤ ∑ j ∈ Icc 1 H, K * (2 / ((n : ℝ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)))) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj)
      _ = 2 * K / (n : ℝ) ^ 2 * ∑ j ∈ Ico 1 (H + 1), 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
          rw [show Icc 1 H = Ico 1 (H + 1) from rfl, mul_sum]
          refine sum_congr rfl fun j hj => ?_
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
          field_simp
      _ ≤ 2 * K / (n : ℝ) ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [sum_Ico_pronic_mass (by norm_num) (by omega)]
          have : (0 : ℝ) ≤ 1 / ((H + 1 : ℕ) : ℝ) := by positivity
          push_cast at this ⊢
          linarith
      _ = 2 * K / (n : ℝ) ^ 2 := mul_one _
  calc |∑ n ∈ Icc 1 N, c' n * ∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)|
      ≤ ∑ n ∈ Icc 1 N, |c' n| * (2 * K / (n : ℝ) ^ 2) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hstep n hn) (abs_nonneg _))
    _ = 2 * K * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-! ## §4. Single moduli: the sign law -/

/-- The unit row at the modulus `e`. -/
def unitRow (e : ℕ) (n : ℕ) : ℝ := if n = e then 1 else 0

theorem sum_Icc_unitRow_mul {N e : ℕ} (he : e ∈ Icc 1 N) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, unitRow e n * f n = f e := by
  rw [sum_eq_single e (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd he h)]
  simp [unitRow]

theorem rowMean_unitRow {N e : ℕ} (he : e ∈ Icc 1 N) :
    rowMean N (unitRow e) = Real.log e / e - ((e : ℝ) - 1) / (2 * e) := by
  rw [rowMean, vonMangoldtReadout_eq_log_harmonic]
  have h1 := sum_Icc_unitRow_mul he (fun n => Real.log n / n)
  have h2 := sum_Icc_unitRow_mul he (fun n => ((n : ℝ) - 1) / (2 * n))
  simp only [mul_div_assoc'] at h1 h2
  rw [h1, h2]

theorem vonMangoldtReadout_unitRow {N e : ℕ} (he : e ∈ Icc 1 N) :
    vonMangoldtReadout N (unitRow e) = Real.log e / e := by
  rw [vonMangoldtReadout_eq_log_harmonic]
  have h := sum_Icc_unitRow_mul he (fun n => Real.log n / n)
  simp only [mul_div_assoc'] at h
  exact h

theorem finiteHarmonicSum_unitRow {N e : ℕ} (he : e ∈ Icc 1 N) :
    finiteHarmonicSum N (unitRow e) = 1 / e := by
  rw [finiteHarmonicSum]
  have h := sum_Icc_unitRow_mul he (fun n => 1 / (n : ℝ))
  simp only [mul_one_div] at h
  exact h

theorem rowFluctBound_unitRow {N e : ℕ} (he : e ∈ Icc 1 N) :
    rowFluctBound N (unitRow e) = (e : ℝ) / 2 := by
  rw [rowFluctBound]
  rw [sum_eq_single e (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd he h)]
  simp [unitRow]

theorem sum_abs_unitRow_div_sq {N e : ℕ} (he : e ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, |unitRow e n| / (n : ℝ) ^ 2 = 1 / (e : ℝ) ^ 2 := by
  rw [sum_eq_single e (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd he h)]
  simp [unitRow]

theorem sum_Ico_one_div_succ_eq_harmonic_sub_one {e : ℕ} (he1 : 1 ≤ e) :
    ∑ M ∈ Ico 1 e, 1 / ((M : ℝ) + 1) = (harmonic e : ℝ) - 1 := by
  induction e, he1 using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [sum_Ico_succ_top hk, ih, harmonic_succ]
    push_cast
    ring

/-- The fluctuation of a unit row is `((e-1)/2 - (M mod e))/e`. -/
theorem rowFluct_unitRow {N e : ℕ} (he : e ∈ Icc 1 N) (M : ℕ) :
    rowFluct N (unitRow e) M = -centeredResidue e M / e := by
  rw [rowFluct]
  rw [sum_eq_single e (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd he h)]
  simp [unitRow, neg_div]
  ring

/-- **The Dirichlet constant of a unit row.**
`|e β(δ_e) - ((e+1)/2 (H_e - 1) - (e - 1))| ≤ e/2`, with `H_e` the harmonic number. -/
theorem abs_mul_rowBeta_unitRow_sub_le {N e : ℕ} (he : e ∈ Icc 1 N) :
    |(e : ℝ) * rowBeta N (unitRow e) -
        (((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1))| ≤ (e : ℝ) / 2 := by
  have he1 : 1 ≤ e := (mem_Icc.mp he).1
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  -- the head `1 ≤ M < e` is explicit
  have hhead : ∑ M ∈ Ico 1 e, -centeredResidue e M / ((M : ℝ) + 1) =
      ((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1) := by
    have hpt : ∀ M ∈ Ico 1 e, -centeredResidue e M / ((M : ℝ) + 1) =
        ((e : ℝ) + 1) / 2 * (1 / ((M : ℝ) + 1)) - 1 := by
      intro M hM
      rw [centeredResidue, Nat.mod_eq_of_lt (mem_Ico.mp hM).2]
      field_simp
      ring
    rw [sum_congr rfl hpt, sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul,
      mul_one]
    rw [sum_Ico_one_div_succ_eq_harmonic_sub_one he1, Nat.cast_sub he1, Nat.cast_one]
  -- the tail `M ≥ e` is an Abel sum of centered residues
  have htail : ∀ H, e ≤ H → |∑ M ∈ Ico e H, -centeredResidue e M / ((M : ℝ) + 1)| ≤ (e : ℝ) / 2 := by
    intro H _
    have := abs_sum_Ico_mul_antitone_le (x := fun M => -centeredResidue e M)
      (w := fun M : ℕ => 1 / ((M : ℝ) + 1)) (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2 / 2)
      (fun M => by positivity)
      (fun i j hij => one_div_le_one_div_of_le (by positivity)
        (by have : (i : ℝ) ≤ j := by exact_mod_cast hij
            linarith))
      (fun A L => by rw [sum_neg_distrib, abs_neg]; exact abs_sum_Ico_centeredResidue_le e he1 A L)
      e H
    calc |∑ M ∈ Ico e H, -centeredResidue e M / ((M : ℝ) + 1)|
        = |∑ M ∈ Ico e H, 1 / ((M : ℝ) + 1) * -centeredResidue e M| := by
          congr 1; exact sum_congr rfl fun _ _ => by ring
      _ ≤ (e : ℝ) ^ 2 / 2 * (1 / ((e : ℝ) + 1)) := this
      _ ≤ (e : ℝ) / 2 := by
          rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- pass to the limit
  have hlim := (tendsto_rowBeta N (unitRow e)).const_mul (e : ℝ)
  have hlim' : Tendsto (fun H : ℕ => ∑ M ∈ Ico 1 H, -centeredResidue e M / ((M : ℝ) + 1))
      atTop (𝓝 ((e : ℝ) * rowBeta N (unitRow e))) := by
    refine hlim.congr fun H => ?_
    rw [mul_sum]
    exact sum_congr rfl fun M _ => by rw [rowFluct_unitRow he]; field_simp
  refine le_of_tendsto (((hlim'.sub_const _)).abs)
    (eventually_atTop.mpr ⟨e, fun H hH => ?_⟩)
  rw [← sum_Ico_consecutive _ he1 hH, hhead, add_sub_cancel_left]
  exact htail H hH

/-- **Sign law of the receiver Gram across scales.** For `1 ≤ e ≤ q ≤ N`, with
`D_e = (e-1)/2 - log e`,

`|e q B(δ_e, δ_q) - (D_e log q - (e+1)/2 (H_e - 1) + (e - 1))| ≤ e/2 + e²/q`. -/
theorem abs_unitRow_bilinear_sub_le {N e q : ℕ} (he : e ∈ Icc 1 N) (hq : q ∈ Icc 1 N) :
    |(e : ℝ) * q * rowBilinear N (unitRow e) (unitRow q) -
        ((((e : ℝ) - 1) / 2 - Real.log e) * Real.log q -
          (((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1)))| ≤
      (e : ℝ) / 2 + (e : ℝ) ^ 2 / q := by
  have heR : (0 : ℝ) < e := by exact_mod_cast (mem_Icc.mp he).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
  have hmain := abs_rowBilinear_add_mean_add_beta_le N (unitRow e) (unitRow q)
  rw [rowMean_unitRow he, vonMangoldtReadout_unitRow hq, finiteHarmonicSum_unitRow hq,
    rowFluctBound_unitRow he, sum_abs_unitRow_div_sq hq] at hmain
  have hβ := abs_mul_rowBeta_unitRow_sub_le (N := N) he
  set B := rowBilinear N (unitRow e) (unitRow q)
  set β := rowBeta N (unitRow e)
  -- scale the rank-two law by `e q`
  have hscaled : |(e : ℝ) * q * B - ((((e : ℝ) - 1) / 2 - Real.log e) * Real.log q -
      (e : ℝ) * β)| ≤ (e : ℝ) ^ 2 / q := by
    have hT : (e : ℝ) * q * B - ((((e : ℝ) - 1) / 2 - Real.log e) * Real.log q - (e : ℝ) * β) =
        ((e : ℝ) * q) * (B + (Real.log e / e - ((e : ℝ) - 1) / (2 * e)) * (Real.log q / q) +
          β * (1 / q)) := by
      field_simp
      ring
    rw [hT, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (e : ℝ) * q)]
    calc (e : ℝ) * q * |B + (Real.log e / e - ((e : ℝ) - 1) / (2 * e)) * (Real.log q / q) +
          β * (1 / q)| ≤ (e : ℝ) * q * (2 * ((e : ℝ) / 2) * (1 / (q : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = (e : ℝ) ^ 2 / q := by field_simp
  calc _ = |((e : ℝ) * q * B - ((((e : ℝ) - 1) / 2 - Real.log e) * Real.log q - (e : ℝ) * β)) -
        ((e : ℝ) * β - (((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1)))| := by
        congr 1; ring
    _ ≤ (e : ℝ) ^ 2 / q + (e : ℝ) / 2 := (abs_sub _ _).trans (add_le_add hscaled hβ)
    _ = (e : ℝ) / 2 + (e : ℝ) ^ 2 / q := add_comm _ _

/-- `D_e = (e-1)/2 - log e` is negative exactly at `e = 2, 3` among `e ≥ 2`. -/
theorem farCoupling_neg_iff {e : ℕ} (he : 2 ≤ e) :
    ((e : ℝ) - 1) / 2 - Real.log e < 0 ↔ e = 2 ∨ e = 3 := by
  constructor
  · intro h
    by_contra hne
    have he4 : 4 ≤ e := by omega
    -- `x ↦ (x-1)/2 - log x` is increasing for `x ≥ 2`, and positive at `4`
    have h4 : Real.log 4 < 3 / 2 := by
      have := Real.exp_one_gt_d9
      have h43 : (4 : ℝ) < Real.exp (3 / 2) := by
        have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
          rw [← Real.exp_add]; norm_num
        rw [this]
        have h12 : (1 : ℝ) + 1 / 2 ≤ Real.exp (1 / 2) := by
          have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
        nlinarith
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      exact h43
    have heR : (4 : ℝ) ≤ e := by exact_mod_cast he4
    have hlog : Real.log e - Real.log 4 ≤ ((e : ℝ) - 4) / 4 := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < e / 4 by positivity)
      linarith
    linarith
  · rintro (rfl | rfl)
    · have : (1 : ℝ) / 2 < Real.log 2 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      push_cast; linarith
    · have : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      push_cast; linarith

/-- **Eventual sign of the far-scale coupling.** For every modulus `e ≥ 2`, the coupling
`B(δ_e, δ_q)` of the receiver Gram has, for all large `q`, the sign of `D_e = (e-1)/2 - log e`:
negative for `e = 2, 3` and positive for `e ≥ 4`. -/
theorem eventually_sign_unitRow_bilinear {e : ℕ} (he : 2 ≤ e) :
    ∃ Q₀ : ℕ, ∀ q N : ℕ, Q₀ ≤ q → q ≤ N → e ≤ N →
      (0 < rowBilinear N (unitRow e) (unitRow q) ↔ 0 < ((e : ℝ) - 1) / 2 - Real.log e) ∧
      (rowBilinear N (unitRow e) (unitRow q) < 0 ↔ ((e : ℝ) - 1) / 2 - Real.log e < 0) := by
  set D := ((e : ℝ) - 1) / 2 - Real.log e with hD
  set C := |((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1)| + (e : ℝ) / 2 +
    (e : ℝ) ^ 2 + 1 with hC
  have hD0 : D ≠ 0 := by
    intro h0
    rcases (lt_trichotomy D 0) with hlt | heq | hgt
    · exact absurd h0 hlt.ne
    · -- `D_e = 0` is impossible: it would force `e = 2, 3` by the sign law, where `D < 0`
      have h1 : ¬ (D < 0) := by rw [heq]; exact lt_irrefl 0
      by_cases h23 : e = 2 ∨ e = 3
      · exact h1 ((farCoupling_neg_iff he).mpr h23)
      · -- for `e ≥ 4`, `D_e ≥ 3/2 - log 4 > 0`
        have he4 : 4 ≤ e := by omega
        have h4 : Real.log 4 < 3 / 2 := by
          have h43 : (4 : ℝ) < Real.exp (3 / 2) := by
            have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
              rw [← Real.exp_add]; norm_num
            rw [this]
            have h12 : (1 : ℝ) + 1 / 2 ≤ Real.exp (1 / 2) := by
              have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
            have := Real.exp_one_gt_d9
            nlinarith
          rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
          exact h43
        have heR : (4 : ℝ) ≤ e := by exact_mod_cast he4
        have hlog : Real.log e - Real.log 4 ≤ ((e : ℝ) - 4) / 4 := by
          rw [← Real.log_div (by positivity) (by norm_num)]
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < e / 4 by positivity)
          linarith
        have : 0 < D := by rw [hD]; linarith
        exact absurd heq this.ne'
    · exact absurd h0 hgt.ne'
  have hDabs : 0 < |D| := abs_pos.mpr hD0
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_gt (Real.exp (C / |D|))
  refine ⟨Q₀ + 1, fun q N hq hqN heN => ?_⟩
  have hq1 : 1 ≤ q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have heI : e ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, heN⟩
  have hqI : q ∈ Icc 1 N := mem_Icc.mpr ⟨hq1, hqN⟩
  have hbound := abs_unitRow_bilinear_sub_le heI hqI
  have hlogq : C / |D| < Real.log q := by
    rw [Real.lt_log_iff_exp_lt hqR]
    exact lt_of_lt_of_le hQ₀ (by exact_mod_cast (by omega : Q₀ ≤ q))
  have hmain : C < |D| * Real.log q := by
    rwa [div_lt_iff₀' hDabs] at hlogq
  have he2 : (e : ℝ) ^ 2 / q ≤ (e : ℝ) ^ 2 := div_le_self (by positivity) (by exact_mod_cast hq1)
  have hepos : (0 : ℝ) < (e : ℝ) * q := by positivity
  set B := rowBilinear N (unitRow e) (unitRow q)
  set E := ((e : ℝ) + 1) / 2 * ((harmonic e : ℝ) - 1) - ((e : ℝ) - 1)
  have hE := le_abs_self E
  have hE' := neg_abs_le E
  have hlo := (abs_le.mp hbound).1
  have hhi := (abs_le.mp hbound).2
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · rw [abs_of_neg hneg] at hmain
    have hB : B < 0 := by
      have : (e : ℝ) * q * B < 0 := by nlinarith
      exact neg_of_mul_neg_right (by linarith) hepos.le
    exact ⟨⟨fun h => absurd h (not_lt.mpr hB.le), fun h => absurd hneg (not_lt.mpr h.le)⟩,
      ⟨fun _ => hneg, fun _ => hB⟩⟩
  · rw [abs_of_pos hpos] at hmain
    have hB : 0 < B := by
      have : 0 < (e : ℝ) * q * B := by nlinarith
      exact pos_of_mul_pos_right this hepos.le
    exact ⟨⟨fun _ => hpos, fun _ => hB⟩,
      ⟨fun h => absurd hB (not_lt.mpr h.le), fun h => absurd h (not_lt.mpr hpos.le)⟩⟩

/-! ## §5. The prime kernel -/

theorem rowValue_unitRow_prime {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (M : ℕ) :
    sieveEnergyCenteredPrefixDiscrepancy N M (unitRow p) =
      pmRamanujanEnergyCenteredPrimitive p M / p := by
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue, vonMangoldtReadout_unitRow hpI]
  have h := sum_Icc_unitRow_mul hpI (fun n => ((M % n : ℕ) : ℝ) / n)
  simp only [mul_div_assoc'] at h
  rw [h, pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime hp,
    vonMangoldt_apply_prime hp]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

/-- The receiver's unit rows at primes are the Vasyunin prime kernel:
`p q B(δ_p, δ_q) = 𝒢^{ec}(p, q)`. -/
theorem mul_rowBilinear_unitRow_prime {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpN : p ≤ N)
    (hqN : q ≤ N) :
    (p : ℝ) * q * rowBilinear N (unitRow p) (unitRow q) = pmRamanujanEnergyCenteredGram p q := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [rowBilinear, pmRamanujanEnergyCenteredGram, ← tsum_mul_left]
  refine tsum_congr fun M => ?_
  rw [rowValue_unitRow_prime hp hpN, rowValue_unitRow_prime hq hqN, cast_pronicSeq_eq]
  field_simp

/-- **Far-scale law of the prime kernel.** For primes `p, q`,
`|𝒢^{ec}(p,q) - (D_p log q - (p+1)/2 (H_p - 1) + (p - 1))| ≤ p/2 + p²/q`. In particular
`𝒢^{ec}(p, q) = (p/2) log(q/p) + O(p)` for `q ≥ p²`. -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_farScale_le {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) :
    |pmRamanujanEnergyCenteredGram p q -
        ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
          (((p : ℝ) + 1) / 2 * ((harmonic p : ℝ) - 1) - ((p : ℝ) - 1)))| ≤
      (p : ℝ) / 2 + (p : ℝ) ^ 2 / q := by
  have h := abs_unitRow_bilinear_sub_le (N := max p q) (e := p) (q := q)
    (mem_Icc.mpr ⟨hp.one_lt.le, le_max_left _ _⟩) (mem_Icc.mpr ⟨hq.one_lt.le, le_max_right _ _⟩)
  rwa [mul_rowBilinear_unitRow_prime hp hq (le_max_left _ _) (le_max_right _ _)] at h

end

end GaloisForLFunctions.BezoutValuationIncidence
