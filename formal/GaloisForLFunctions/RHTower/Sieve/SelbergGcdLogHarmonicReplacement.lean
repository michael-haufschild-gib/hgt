import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPrincipalCollapse
import GaloisForLFunctions.RHTower.Sieve.SelbergDilatedLogMonomialAsymptotic

/-!
# Harmonic replacement for the gcd-logarithmic principal model

The logarithmically weighted rectangular model
`∑_{d ≤ N/max(a,b)} (log d / d)·K_{q+1}(N/(ad))·K_{r+1}(N/(bd))`
is replaced by its harmonic main term
`∑_{d} (log d / d)·(q+1)(r+1)·log(N/(ad))^q·log(N/(bd))^r`
with an error `o((log N)^{q+r+2})`.

The pointwise input is isolated first: the product of two Möbius log-power kernels is within a
prescribed *relative* error of its leading term as soon as both cutoffs are large.  That lemma is
independent of the weight, so it also reproves the unweighted replacement.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- **Relative closeness of a product of two Möbius log-power kernels to its leading term.** -/
theorem exists_kernelProduct_close (q r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ Y Z : ℝ, K ≤ Y → K ≤ Z →
      |moebiusLogPowerKernelReal (q + 1) Y * moebiusLogPowerKernelReal (r + 1) Z -
          ((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
            (Real.log Y ^ q * Real.log Z ^ r)| ≤
        δ * (Real.log Y ^ q * Real.log Z ^ r) := by
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  set cq : ℝ := ((q + 1 : ℕ) : ℝ) with hcq
  set cr : ℝ := ((r + 1 : ℕ) : ℝ) with hcr
  have hcqpos : 0 < cq := by rw [hcq]; positivity
  have hden : 0 < DB + cq := by positivity
  set η : ℝ := δ / (DB + cq) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hAnear : ∀ᶠ Y : ℝ in atTop,
      |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q - cq| < η :=
    (tendsto_moebiusLogPowerKernelReal_div_log_pow q).eventually
      (Metric.ball_mem_nhds cq hηpos)
  rw [eventually_atTop] at hAnear
  obtain ⟨KA, hKA⟩ := hAnear
  have hBnear : ∀ᶠ Z : ℝ in atTop,
      |moebiusLogPowerKernelReal (r + 1) Z / Real.log Z ^ r - cr| < η :=
    (tendsto_moebiusLogPowerKernelReal_div_log_pow r).eventually
      (Metric.ball_mem_nhds cr hηpos)
  rw [eventually_atTop] at hBnear
  obtain ⟨KB, hKB⟩ := hBnear
  refine ⟨max (max KA KB) 2, le_max_right _ _, ?_⟩
  intro Y Z hY hZ
  have hKAY : KA ≤ Y := le_trans (le_trans (le_max_left KA KB) (le_max_left _ _)) hY
  have hKBZ : KB ≤ Z := le_trans (le_trans (le_max_right KA KB) (le_max_left _ _)) hZ
  have hY2 : (2 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hZ2 : (2 : ℝ) ≤ Z := le_trans (le_max_right _ _) hZ
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hYone : (1 : ℝ) ≤ Y := by linarith
  have hZone : (1 : ℝ) ≤ Z := by linarith
  have hA : |moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q| ≤
      η * Real.log Y ^ q := by
    have hpos : (0 : ℝ) < Real.log Y ^ q := pow_pos hlogY q
    have h := (hKA Y hKAY).le
    have heq : moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q =
        (moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q - cq) *
          Real.log Y ^ q := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right h hpos.le
  have hB : |moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r| ≤
      η * Real.log Z ^ r := by
    have hpos : (0 : ℝ) < Real.log Z ^ r := pow_pos hlogZ r
    have h := (hKB Z hKBZ).le
    have heq : moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r =
        (moebiusLogPowerKernelReal (r + 1) Z / Real.log Z ^ r - cr) *
          Real.log Z ^ r := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right h hpos.le
  have hBglobal : |moebiusLogPowerKernelReal (r + 1) Z| ≤ DB * Real.log Z ^ r :=
    hDBbound Z hZone
  have hsplit :
      moebiusLogPowerKernelReal (q + 1) Y * moebiusLogPowerKernelReal (r + 1) Z -
          cq * cr * (Real.log Y ^ q * Real.log Z ^ r) =
        (moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q) *
            moebiusLogPowerKernelReal (r + 1) Z +
          (cq * Real.log Y ^ q) *
            (moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r) := by
    ring
  rw [hsplit]
  have hterm1 : |(moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q) *
      moebiusLogPowerKernelReal (r + 1) Z| ≤
      (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) := by
    rw [abs_mul]
    exact mul_le_mul hA hBglobal (abs_nonneg _)
      (mul_nonneg hηpos.le (pow_nonneg hlogY.le q))
  have hterm2 : |(cq * Real.log Y ^ q) *
      (moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r)| ≤
      (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ cq * Real.log Y ^ q)]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hfinal : (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) +
      (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) ≤
      δ * (Real.log Y ^ q * Real.log Z ^ r) := by
    have hcollect : (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) +
        (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) =
        (η * (DB + cq)) * (Real.log Y ^ q * Real.log Z ^ r) := by ring
    rw [hcollect]
    have hηval : η * (DB + cq) = δ := by
      rw [hη]
      field_simp
    rw [hηval]
  exact le_trans (le_trans (abs_add_le _ _) (add_le_add hterm1 hterm2)) hfinal

/-- Single-sum form of the replacement error. -/
theorem selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonicMain
    (q r a b N : ℕ) :
    selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N -
        selbergGcdLogHarmonicMain q r a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b),
        Real.log (d : ℝ) *
          (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            ((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) / (d : ℝ) := by
  rw [selbergGcdLogPrincipalScaledLogPowerModel, selbergGcdLogHarmonicMain,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- **Harmonic replacement for the gcd-logarithmic principal model.** -/
theorem tendsto_selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      (selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N -
        selbergGcdLogHarmonicMain q r a b N) /
          Real.log N ^ (q + r + 2)) atTop (𝓝 0) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow q
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  set cq : ℝ := ((q + 1 : ℕ) : ℝ) with hcqdef
  set cr : ℝ := ((r + 1 : ℕ) : ℝ) with hcrdef
  have hcq : 0 ≤ cq := by rw [hcqdef]; positivity
  have hcr : 0 ≤ cr := by rw [hcrdef]; positivity
  set B : ℝ := DA * DB + cq * cr with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  set c : ℕ := max a b with hcdef
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK2, hKclose⟩ := exists_kernelProduct_close q r (δ := ε / 8) (by positivity)
  have hKpos : (0 : ℝ) < K := by linarith
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have hfull : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic (N / c) : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  rw [eventually_atTop] at hfull
  obtain ⟨Nfull, hNfull⟩ := hfull
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * B * K / ε < Real.log N :=
    hlogTop.eventually_gt_atTop (4 * B * K / ε)
  rw [eventually_atTop] at hlarge
  obtain ⟨Nlarge, hNlarge⟩ := hlarge
  refine ⟨max (max Nfull Nlarge) 2, ?_⟩
  intro N hN
  have hNfull' : Nfull ≤ N := (le_max_left Nfull Nlarge).trans
    ((le_max_left (max Nfull Nlarge) 2).trans hN)
  have hNlarge' : Nlarge ≤ N := (le_max_right Nfull Nlarge).trans
    ((le_max_left (max Nfull Nlarge) 2).trans hN)
  have hN2 : 2 ≤ N := (le_max_right (max Nfull Nlarge) 2).trans hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hratioTwo : (harmonic (N / c) : ℝ) / Real.log N < 2 := by
    have hfullN := hNfull N hNfull'
    rw [Real.dist_eq] at hfullN
    have hself : (harmonic (N / c) : ℝ) / Real.log N - 1 ≤
        |(harmonic (N / c) : ℝ) / Real.log N - 1| := le_abs_self _
    linarith
  have hharm : (harmonic (N / c) : ℝ) ≤ 2 * Real.log N := by
    have := (div_lt_iff₀ hlogpos).mp hratioTwo
    linarith
  have hbigLog : 4 * B * K / ε < Real.log N := hNlarge N hNlarge'
  have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
      |Real.log (d : ℝ) *
          (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            cq * cr *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) / (d : ℝ)| ≤
        (ε / 8) * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) +
          B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdN : d ≤ N := le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_le
      (Finset.mem_Icc.mp hd).2)) (Nat.div_le_self N c)
    have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
    have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hdpos)
    have hlogdN : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) hdNR
    have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((a * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument ha (le_max_left a b) hd
    have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((b * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument hb (le_max_right a b) hd
    have hYAle : (N : ℝ) / ((a * d : ℕ) : ℝ) ≤ (N : ℝ) :=
      selbergScaledArgument_le_natCast ha hdpos
    have hYBle : (N : ℝ) / ((b * d : ℕ) : ℝ) ≤ (N : ℝ) :=
      selbergScaledArgument_le_natCast hb hdpos
    have hLA0 : 0 ≤ Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) := Real.log_nonneg hYAone
    have hLB0 : 0 ≤ Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) := Real.log_nonneg hYBone
    have hLAle : Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ≤ Real.log N :=
      Real.log_le_log (by positivity) hYAle
    have hLBle : Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ≤ Real.log N :=
      Real.log_le_log (by positivity) hYBle
    have hprodle : Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
        Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r ≤ Real.log N ^ (q + r) := by
      calc
        _ ≤ Real.log N ^ q * Real.log N ^ r :=
          mul_le_mul (pow_le_pow_left₀ hLA0 hLAle q)
            (pow_le_pow_left₀ hLB0 hLBle r) (pow_nonneg hLB0 r)
            (pow_nonneg hlogpos.le q)
        _ = Real.log N ^ (q + r) := (pow_add _ _ _).symm
    have hsecond_nonneg : 0 ≤ B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ)) := by
      positivity
    by_cases hcase : K ≤ (N : ℝ) / ((a * d : ℕ) : ℝ) ∧ K ≤ (N : ℝ) / ((b * d : ℕ) : ℝ)
    · have hclose := hKclose _ _ hcase.1 hcase.2
      have hmain : |Real.log (d : ℝ) *
            (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) / (d : ℝ)| ≤
          (ε / 8) * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) := by
        rw [abs_div, abs_of_pos hdR, abs_mul, abs_of_nonneg hlogd0]
        rw [div_le_iff₀ hdR]
        have hstep : Real.log (d : ℝ) *
            |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)| ≤
            Real.log N * ((ε / 8) * Real.log N ^ (q + r)) := by
          refine mul_le_mul hlogdN (hclose.trans ?_) (abs_nonneg _) hlogpos.le
          exact mul_le_mul_of_nonneg_left hprodle (by positivity)
        calc
          Real.log (d : ℝ) *
              |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                  moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
                cq * cr *
                  (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                    Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)|
              ≤ Real.log N * ((ε / 8) * Real.log N ^ (q + r)) := hstep
          _ = (ε / 8) * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) * (d : ℝ) := by
                rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
                field_simp
      linarith [hmain, hsecond_nonneg]
    · have hsmall : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
        rcases not_and_or.mp hcase with hA | hB'
        · have hlt : (N : ℝ) / ((a * d : ℕ) : ℝ) < K := lt_of_not_ge hA
          have had : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos ha hdpos
          have hNlt : (N : ℝ) < K * ((a * d : ℕ) : ℝ) := by
            rw [div_lt_iff₀ had] at hlt
            linarith
          have haR : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_left a b
          have hcast : ((a * d : ℕ) : ℝ) = (a : ℝ) * (d : ℝ) := by push_cast; ring
          rw [hcast] at hNlt
          rw [div_le_div_iff₀ hdR hNR]
          have hmul : K * ((a : ℝ) * (d : ℝ)) ≤ K * ((c : ℝ) * (d : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haR hdR.le) hKpos.le
          linarith [hmul]
        · have hlt : (N : ℝ) / ((b * d : ℕ) : ℝ) < K := lt_of_not_ge hB'
          have hbd : (0 : ℝ) < ((b * d : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos hb hdpos
          have hNlt : (N : ℝ) < K * ((b * d : ℕ) : ℝ) := by
            rw [div_lt_iff₀ hbd] at hlt
            linarith
          have hbR : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_right a b
          have hcast : ((b * d : ℕ) : ℝ) = (b : ℝ) * (d : ℝ) := by push_cast; ring
          rw [hcast] at hNlt
          rw [div_le_div_iff₀ hdR hNR]
          have hmul : K * ((b : ℝ) * (d : ℝ)) ≤ K * ((c : ℝ) * (d : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbR hdR.le) hKpos.le
          linarith [hmul]
      have hglobal : |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            cq * cr *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)| ≤
          B * Real.log N ^ (q + r) := by
        have hQA := hDAbound _ hYAone
        have hQB := hDBbound _ hYBone
        have hprod : |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))| ≤
            DA * DB * Real.log N ^ (q + r) := by
          rw [abs_mul]
          calc
            _ ≤ (DA * Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q) *
                (DB * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r) :=
              mul_le_mul hQA hQB (abs_nonneg _) (by positivity)
            _ = DA * DB * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r) := by ring
            _ ≤ DA * DB * Real.log N ^ (q + r) :=
              mul_le_mul_of_nonneg_left hprodle (by positivity)
        have hlead : |cq * cr *
            (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
              Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)| ≤
            cq * cr * Real.log N ^ (q + r) := by
          rw [abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left hprodle (by positivity)
        calc
          _ ≤ |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))| +
              |cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)| := abs_sub _ _
          _ ≤ DA * DB * Real.log N ^ (q + r) + cq * cr * Real.log N ^ (q + r) :=
            add_le_add hprod hlead
          _ = B * Real.log N ^ (q + r) := by rw [hBdef]; ring
      have hfirst_nonneg : 0 ≤ (ε / 8) * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) := by
        positivity
      have hmain : |Real.log (d : ℝ) *
            (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) / (d : ℝ)| ≤
          B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ)) := by
        rw [abs_div, abs_of_pos hdR, abs_mul, abs_of_nonneg hlogd0]
        rw [div_le_iff₀ hdR]
        have hstep : Real.log (d : ℝ) *
            |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)| ≤
            Real.log N * (B * Real.log N ^ (q + r)) :=
          mul_le_mul hlogdN hglobal (abs_nonneg _) hlogpos.le
        have hfac : Real.log N * (B * Real.log N ^ (q + r)) =
            B * Real.log N ^ (q + r + 1) := by
          rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
          ring
        rw [hfac] at hstep
        have hmul : B * Real.log N ^ (q + r + 1) ≤
            B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ)) * (d : ℝ) := by
          have h1 : (1 : ℝ) ≤ (K * (c : ℝ) / (N : ℝ)) * (d : ℝ) := by
            have hmulled := mul_le_mul_of_nonneg_right hsmall hdR.le
            rw [one_div, inv_mul_cancel₀ hdR.ne'] at hmulled
            exact hmulled
          have hnn : 0 ≤ B * Real.log N ^ (q + r + 1) := by positivity
          calc
            B * Real.log N ^ (q + r + 1)
                = B * Real.log N ^ (q + r + 1) * 1 := by ring
            _ ≤ B * Real.log N ^ (q + r + 1) *
                ((K * (c : ℝ) / (N : ℝ)) * (d : ℝ)) :=
                  mul_le_mul_of_nonneg_left h1 hnn
            _ = B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ)) * (d : ℝ) := by
                  ring
        linarith [hstep, hmul]
      linarith [hmain, hfirst_nonneg]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (pow_pos hlogpos (q + r + 2))]
  rw [div_lt_iff₀ (pow_pos hlogpos (q + r + 2))]
  have hsum := selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonicMain q r a b N
  rw [hsum, ← hcdef]
  calc
    |∑ d ∈ Finset.Icc 1 (N / c),
        Real.log (d : ℝ) *
          (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            cq * cr *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) / (d : ℝ)|
        ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            ((ε / 8) * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) +
              B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ))) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (ε / 8) * Real.log N ^ (q + r + 1) * (harmonic (N / c) : ℝ) +
          ((N / c : ℕ) : ℝ) *
            (B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ))) := by
      have hcard : (((Finset.Icc 1 (N / c)).card : ℕ) : ℝ) = ((N / c : ℕ) : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_Icc_one_div_eq_harmonic,
        Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (ε / 8) * Real.log N ^ (q + r + 1) * (2 * Real.log N) +
          B * K * Real.log N ^ (q + r + 1) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left hharm (by positivity)
      · have hdivle : ((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ)) ≤ 1 := by
          have h1 : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) / (c : ℝ) := by
            rw [le_div_iff₀ hcR]
            exact_mod_cast Nat.div_mul_le_self N c
          calc
            ((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ))
                ≤ ((N : ℝ) / (c : ℝ)) * ((c : ℝ) / (N : ℝ)) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = 1 := by field_simp
        have hrewrite : ((N / c : ℕ) : ℝ) *
            (B * Real.log N ^ (q + r + 1) * (K * (c : ℝ) / (N : ℝ))) =
            (B * K * Real.log N ^ (q + r + 1)) *
              (((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ))) := by
          ring
        rw [hrewrite]
        have hnn : 0 ≤ B * K * Real.log N ^ (q + r + 1) := by positivity
        calc
          (B * K * Real.log N ^ (q + r + 1)) *
              (((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ)))
              ≤ (B * K * Real.log N ^ (q + r + 1)) * 1 :=
                mul_le_mul_of_nonneg_left hdivle hnn
          _ = B * K * Real.log N ^ (q + r + 1) := mul_one _
    _ < ε * Real.log N ^ (q + r + 2) := by
      have hpow : Real.log N ^ (q + r + 2) =
          Real.log N ^ (q + r + 1) * Real.log N := by
        rw [show q + r + 2 = (q + r + 1) + 1 by omega, pow_succ]
      rw [hpow]
      have hBK : B * K < (ε / 4) * Real.log N := by
        rcases eq_or_lt_of_le hB with hB0 | hBpos
        · rw [← hB0]
          have : (0 : ℝ) < (ε / 4) * Real.log N := by positivity
          simpa using this
        · rw [div_lt_iff₀ hε] at hbigLog
          linarith [hbigLog]
      have hposPow : (0 : ℝ) < Real.log N ^ (q + r + 1) := pow_pos hlogpos _
      have h1 : B * K * Real.log N ^ (q + r + 1) <
          ((ε / 4) * Real.log N) * Real.log N ^ (q + r + 1) :=
        mul_lt_mul_of_pos_right hBK hposPow
      have hX : (0 : ℝ) < ε * (Real.log N ^ (q + r + 1) * Real.log N) := by
        positivity
      linarith [h1, hX]

/-- **The gcd-logarithmic principal model at every pair of logarithmic powers.** -/
theorem tendsto_selbergGcdLogPrincipalScaledLogPowerModel_div_log_pow
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N /
        Real.log N ^ (q + r + 2))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)))) := by
  have herr :=
    tendsto_selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero q r ha hb
  have hmain := tendsto_selbergGcdLogHarmonicMain_div_log_pow q r ha hb
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards with N
  ring

end

end RHTower.Sieve
