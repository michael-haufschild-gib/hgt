import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Uniform cofinal arithmetic cancellation for the literal Möbius source

Let `s_N(k)=sum_{d<=N,d|k} mu(d)` and let `L_N(M)` be its finite-prefix discrepancy.
For every positive epsilon there is K such that, simultaneously for all N,M>=K,
`|L_N(M)| <= epsilon*M` and `|sum_{k<=M} s_N(k)| <= epsilon*M`.
The two scales grow independently; no receiver budget or full-period average is used.

The finite arithmetic estimate behind this limit is
`|sum_{k<=M} s_N(k)| <= 1 + 2*B*mertensSup((B+1)*N)` for `1<=M<=(B+1)*N`.
Complementary quotient compression rewrites the prefix as one minus B truncated
Möbius windows. The corpus's unconditional Mertens and harmonic Möbius limits make
this bound sublinear for each fixed B. For larger horizons the direct discrepancy
bound `|L_N(M)| <= N` takes over. Below the cutoff, full Möbius inversion gives the
exact source prefix one.

This is signed first-moment cancellation. It asserts neither a square-root rate nor
an upper bound for critical unsigned energy or the interior martingale. The analytic
inputs are proved corpus theorems, not assumptions of the exported results.
-/

open Finset Filter
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology


namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Exact finite quotient-window decomposition of the literal Möbius source prefix. -/
theorem sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows {N B M : ℕ}
    (hM : 1 ≤ M) (hhi : M ≤ (B + 1) * N) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) =
      1 - ∑ q ∈ Finset.Icc 1 B, ∑ d ∈ Finset.Ioc N (M / q), moebiusReal d := by
  classical
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 M) :
      sieveSeq N moebiusReal k = (if k = 1 then 1 else 0) -
        ∑ q ∈ Finset.Icc 1 B,
          if q ∣ k ∧ N < k / q then moebiusReal (k / q) else 0 := by
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk1,
      sum_divisors_moebiusReal_eq_ite_one hk1,
      complementaryQuotientTail_eq_sum_Icc_of_le_mul (hkM.trans hhi), Finset.sum_filter]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hunit : (∑ k ∈ Finset.Icc 1 M, (if k = 1 then (1 : ℝ) else 0)) = 1 := by
    simp [hM]
  rw [hunit, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hfilter :
      (∑ k ∈ Finset.Icc 1 M,
        if q ∣ k ∧ N < k / q then moebiusReal (k / q) else 0) =
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => q ∣ k),
        if N < k / q then moebiusReal (k / q) else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hqk : q ∣ k <;> simp [hqk]
  rw [hfilter, sum_Icc_filter_dvd_eq_sum_Icc_div hqpos]
  have hquot (j : ℕ) : q * j / q = j := Nat.mul_div_cancel_left j hqpos
  simp_rw [hquot]
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- A finite arithmetic majorant uniform over an entire linear horizon window. -/
theorem abs_sum_sieveSeq_moebiusReal_le_mertensSup {N B M : ℕ}
    (hM : 1 ≤ M) (hhi : M ≤ (B + 1) * N) :
    |∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k| ≤
      1 + 2 * B * mertensSup ((B + 1) * N) := by
  classical
  rw [sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows hM hhi]
  have hwindow (q : ℕ) (hq : q ∈ Finset.Icc 1 B) :
      |∑ d ∈ Finset.Ioc N (M / q), moebiusReal d| ≤ 2 * mertensSup ((B + 1) * N) := by
    by_cases hNQ : N ≤ M / q
    · have heq : Finset.Ioc N (M / q) = Finset.Ico (N + 1) (M / q + 1) := by
        ext d
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      rw [heq, Finset.sum_Ico_eq_sub _ (by omega : N + 1 ≤ M / q + 1)]
      change |mertensM (M / q) - mertensM N| ≤ _
      have h0 := abs_mertensM_le_mertensSup (show N ≤ (B + 1) * N by nlinarith)
      have h1 := abs_mertensM_le_mertensSup ((Nat.div_le_self M q).trans hhi)
      exact (abs_sub _ _).trans (by linarith)
    · have hempty : Finset.Ioc N (M / q) = ∅ := by
        ext d
        constructor
        · intro hd
          have hd' := Finset.mem_Ioc.mp hd
          omega
        · intro hd
          simp at hd
      rw [hempty, Finset.sum_empty, abs_zero]
      exact mul_nonneg (by norm_num) (mertensSup_nonneg _)
  calc
    _ ≤ |(1 : ℝ)| + |∑ q ∈ Finset.Icc 1 B, ∑ d ∈ Finset.Ioc N (M / q), moebiusReal d| := abs_sub _ _
    _ ≤ 1 + ∑ q ∈ Finset.Icc 1 B, |∑ d ∈ Finset.Ioc N (M / q), moebiusReal d| := by
      rw [abs_one]
      exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _q ∈ Finset.Icc 1 B, 2 * mertensSup ((B + 1) * N) :=
      add_le_add le_rfl (Finset.sum_le_sum hwindow)
    _ = _ := by simp; ring

/-- The finite quotient-window majorant is sublinear as the cutoff grows, for every fixed band count. -/
theorem tendsto_moebius_prefix_linear_window_majorant (B : ℕ) :
    Tendsto (fun N : ℕ => (1 + 2 * B * mertensSup ((B + 1) * N)) / (N : ℝ))
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun N : ℕ => (B + 1) * N) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => by dsimp only [id_eq]; nlinarith) tendsto_id
  have hratio : Tendsto (fun N : ℕ => mertensSup ((B + 1) * N) / (N : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_mertensSup_div.comp hscale).mul_const ((B : ℝ) + 1)
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hb : (B : ℝ) + 1 ≠ 0 := by positivity
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add
    (hratio.const_mul (2 * (B : ℝ)))
  simp only [mul_zero, zero_add] at h
  exact h.congr (fun N => by ring)

/-- The unconditional harmonic Möbius prime-number theorem in BVI source coordinates. -/
theorem tendsto_finiteHarmonicSum_moebiusReal_zero :
    Tendsto (fun N : ℕ => finiteHarmonicSum N moebiusReal) atTop (𝓝 0) := by
  have h := (Asymptotics.isLittleO_one_iff ℝ).mp mu_pnt_alt
  have hN : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  refine (h.comp hN).congr fun N => ?_
  simp only [Function.comp_apply, Nat.floor_natCast]
  unfold finiteHarmonicSum
  change (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ) / n) =
    ∑ n ∈ Finset.Ico 1 (N + 1), moebiusReal n / n
  rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1)]
  simp [moebiusReal]

/-- The direct fractional-part bound is uniform over all observation horizons. -/
theorem abs_sievePrefixDiscrepancy_moebiusReal_le_cutoff (N M : ℕ) :
    |sievePrefixDiscrepancy N M moebiusReal| ≤ (N : ℝ) := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, abs_neg]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, |moebiusReal d| := abs_sievedFractSum_le_sum_abs _ _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      unfold moebiusReal
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = _ := by simp

/-- Signed discrepancy is sublinear uniformly over every horizon above the growing cutoff. -/
theorem eventually_uniform_moebiusPrefixDiscrepancy_sublinear :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N ≤ M →
      |sievePrefixDiscrepancy N M moebiusReal| ≤ ε * M := by
  intro ε hε
  obtain ⟨B, hB⟩ := exists_nat_gt (2 / ε)
  have hcoeff : 1 ≤ ε * ((B : ℝ) + 1) := by
    have h := (div_lt_iff₀ hε).mp hB
    nlinarith
  have hsmall := (tendsto_moebius_prefix_linear_window_majorant B).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hharm := tendsto_finiteHarmonicSum_moebiusReal_zero.abs.eventually
    (eventually_lt_nhds (show |(0 : ℝ)| < ε / 2 by simpa using half_pos hε))
  filter_upwards [hsmall, hharm, eventually_ge_atTop (1 : ℕ)] with N hs hh hN
  intro M hNM
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  by_cases hnear : M ≤ (B + 1) * N
  · have hprefix := abs_sum_sieveSeq_moebiusReal_le_mertensSup (by omega : 1 ≤ M) hnear
    have hpsmall : |∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k| ≤ ε / 2 * N :=
      hprefix.trans ((div_lt_iff₀ hn).mp hs).le
    have heq : sievePrefixDiscrepancy N M moebiusReal =
        (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) -
          (M : ℝ) * finiteHarmonicSum N moebiusReal := by
      rw [sievePrefixDiscrepancy_eq_sum_sub_drift]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact (sieveSeq_eq_sievedDivisorSum N moebiusReal (Finset.mem_Icc.mp hk).1).symm
    rw [heq]
    have hprod : |(M : ℝ) * finiteHarmonicSum N moebiusReal| ≤ (M : ℝ) * (ε / 2) := by
      rw [abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left hh.le hm
    have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have hbound := (abs_sub
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k)
      ((M : ℝ) * finiteHarmonicSum N moebiusReal)).trans (add_le_add hpsmall hprod)
    nlinarith [mul_le_mul_of_nonneg_left hNMreal (half_pos hε).le]
  · have hfar : ((B : ℝ) + 1) * N < M := by exact_mod_cast (lt_of_not_ge hnear)
    have hNbound := mul_le_mul_of_nonneg_right hcoeff hn.le
    have hMbound := mul_le_mul_of_nonneg_left hfar.le hε.le
    exact (abs_sievePrefixDiscrepancy_moebiusReal_le_cutoff N M).trans (by nlinarith)

private theorem moebiusPrefixDiscrepancy_eq_sum_sub_drift (N M : ℕ) :
    sievePrefixDiscrepancy N M moebiusReal =
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) -
        (M : ℝ) * finiteHarmonicSum N moebiusReal := by
  rw [sievePrefixDiscrepancy_eq_sum_sub_drift]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (sieveSeq_eq_sievedDivisorSum N moebiusReal (Finset.mem_Icc.mp hk).1).symm

/-- Unconditional signed discrepancy cancellation under unrestricted joint cofinal growth of cutoff and horizon. -/
theorem cofinal_moebiusPrefixDiscrepancy_sublinear :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N M : ℕ, K ≤ N → K ≤ M →
      |sievePrefixDiscrepancy N M moebiusReal| ≤ ε * M := by
  intro ε hε
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp
    (eventually_uniform_moebiusPrefixDiscrepancy_sublinear ε hε)
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.mp
    (tendsto_finiteHarmonicSum_moebiusReal_zero.abs.eventually
      (eventually_lt_nhds (show |(0 : ℝ)| < ε / 2 by simpa using half_pos hε)))
  obtain ⟨K2, hK2⟩ := exists_nat_gt (2 / ε)
  refine ⟨max K0 (max K1 (K2 + 1)), ?_⟩
  intro N M hN hM
  by_cases hNM : N ≤ M
  · exact hK0 N (by omega) M hNM
  · have hMN : M ≤ N := by omega
    have hm1 : 1 ≤ M := by omega
    have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hh : |finiteHarmonicSum N moebiusReal| ≤ ε / 2 := (hK1 N (by omega)).le
    have h2 : (2 : ℝ) ≤ ε * M := by
      have hbound := (div_lt_iff₀ hε).mp hK2
      have hKM : (K2 : ℝ) ≤ M := by exact_mod_cast (show K2 ≤ M by omega)
      nlinarith [mul_le_mul_of_nonneg_left hKM hε.le]
    rw [moebiusPrefixDiscrepancy_eq_sum_sub_drift,
      sum_sieveSeq_moebiusReal_eq_one_of_le hm1 hMN]
    have hp : |(M : ℝ) * finiteHarmonicSum N moebiusReal| ≤ (M : ℝ) * (ε / 2) := by
      rw [abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left hh hm
    have ht := abs_sub (1 : ℝ) ((M : ℝ) * finiteHarmonicSum N moebiusReal)
    rw [abs_one] at ht
    linarith

/-- The literal Möbius divisor-source prefix has vanishing normalized mean under unrestricted joint cofinal growth. -/
theorem cofinal_moebius_source_prefix_sublinear :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N M : ℕ, K ≤ N → K ≤ M →
      |∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k| ≤ ε * M := by
  intro ε hε
  obtain ⟨K0, hK0⟩ := cofinal_moebiusPrefixDiscrepancy_sublinear (ε / 2) (half_pos hε)
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.mp
    (tendsto_finiteHarmonicSum_moebiusReal_zero.abs.eventually
      (eventually_lt_nhds (show |(0 : ℝ)| < ε / 2 by simpa using half_pos hε)))
  refine ⟨max K0 K1, ?_⟩
  intro N M hN hM
  have hd := hK0 N M (by omega) (by omega)
  have hh : |finiteHarmonicSum N moebiusReal| ≤ ε / 2 := (hK1 N (by omega)).le
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have heq : (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) =
      sievePrefixDiscrepancy N M moebiusReal + (M : ℝ) * finiteHarmonicSum N moebiusReal := by
    rw [moebiusPrefixDiscrepancy_eq_sum_sub_drift]
    ring
  rw [heq]
  have hp : |(M : ℝ) * finiteHarmonicSum N moebiusReal| ≤ (M : ℝ) * (ε / 2) := by
    rw [abs_mul, abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left hh hm
  have ht := abs_add_le (sievePrefixDiscrepancy N M moebiusReal)
    ((M : ℝ) * finiteHarmonicSum N moebiusReal)
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
