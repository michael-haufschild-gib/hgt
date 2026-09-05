import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogHarmonicReplacement
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowGeneralMoment
import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogHarmonicModels

/-!
# Principal Selberg coefficients with arbitrary gcd-logarithmic power

The origin-based Barban--Vehov short energy contains the three weights
`log (m,n)^a`, `a = 1,2,3`.  The existing principal collapse treats only
`a = 1`.  This file builds the exponent-uniform coefficient

`diag(log(d)^a / d) * (mu/d tensor mu/d)`

and collapses every rectangular logarithmic moment to one diagonal sum.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Reciprocal diagonal coefficient weighted by an arbitrary logarithmic power. -/
def selbergDiagonalLogPowerReciprocalCoeff (a m n : ℕ) : ℝ :=
  if m = n then Real.log (m : ℝ) ^ a / (m : ℝ) else 0

@[simp] theorem selbergDiagonalLogPowerReciprocalCoeff_one (a : ℕ) :
    selbergDiagonalLogPowerReciprocalCoeff a 1 1 = if a = 0 then 1 else 0 := by
  cases a <;> simp [selbergDiagonalLogPowerReciprocalCoeff]

theorem selbergDiagonalLogPowerReciprocalCoeff_one_eq
    (m n : ℕ) :
    selbergDiagonalLogPowerReciprocalCoeff 1 m n =
      selbergDiagonalLogReciprocalCoeff m n := by
  rw [selbergDiagonalLogPowerReciprocalCoeff,
    selbergDiagonalLogReciprocalCoeff]
  split_ifs <;> ring

/-- A rectangular double sum against the logarithmic-power diagonal collapses to its diagonal. -/
theorem selbergDiagonalLogPowerReciprocalCoeff_double_sum_mul_eq
    (a : ℕ) {X Y : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogPowerReciprocalCoeff a d e * F d e) =
      ∑ d ∈ Finset.Icc 1 (min X Y),
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * F d d := by
  have hinner : ∀ d ∈ Finset.Icc 1 X,
      (∑ e ∈ Finset.Icc 1 Y,
        selbergDiagonalLogPowerReciprocalCoeff a d e * F d e) =
      if d ∈ Finset.Icc 1 Y then
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * F d d else 0 := by
    intro d hd
    by_cases hdY : d ∈ Finset.Icc 1 Y
    · rw [if_pos hdY, Finset.sum_eq_single_of_mem d hdY]
      · rw [selbergDiagonalLogPowerReciprocalCoeff, if_pos rfl]
      · intro e he hed
        rw [selbergDiagonalLogPowerReciprocalCoeff,
          if_neg (Ne.symm hed), zero_mul]
    · rw [if_neg hdY]
      apply Finset.sum_eq_zero
      intro e he
      rw [selbergDiagonalLogPowerReciprocalCoeff]
      split_ifs with hde
      · subst e
        exact (hdY he).elim
      · ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Product-kernel specialization of the logarithmic-power diagonal collapse. -/
theorem selbergDiagonalLogPowerReciprocalCoeff_double_sum_eq
    (a : ℕ) {X Y : ℕ} (h k : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogPowerReciprocalCoeff a d e * (h d * k e)) =
      ∑ d ∈ Finset.Icc 1 (min X Y),
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * (h d * k d) := by
  simpa using selbergDiagonalLogPowerReciprocalCoeff_double_sum_mul_eq
    a (X := X) (Y := Y) (fun d e => h d * k e)

/-- Principal Euler coefficient carrying `log(gcd)^a`. -/
def selbergGcdLogPowerPrincipalCoeff (a : ℕ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution
    (selbergDiagonalLogPowerReciprocalCoeff a)
    selbergMoebiusReciprocalPair

theorem selbergGcdLogPowerPrincipalCoeff_one_eq :
    selbergGcdLogPowerPrincipalCoeff 1 = selbergGcdLogPrincipalCoeff := by
  unfold selbergGcdLogPowerPrincipalCoeff selbergGcdLogPrincipalCoeff
  rw [show selbergDiagonalLogPowerReciprocalCoeff 1 =
      selbergDiagonalLogReciprocalCoeff by
    funext m n
    exact selbergDiagonalLogPowerReciprocalCoeff_one_eq m n]

/-- Rectangular model after collapsing the principal `log(gcd)^a` coefficient. -/
def selbergGcdLogPowerPrincipalScaledModel
    (a i j A B N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max A B),
    Real.log (d : ℝ) ^ a *
      (moebiusLogPowerKernelReal i ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
        moebiusLogPowerKernelReal j ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
      (d : ℝ)

/-- The principal `log(gcd)^a` coefficient collapses to one weighted harmonic model. -/
theorem selbergGcdLogPowerPrincipalCoeff_weighted_logPower_eq_scaledModel
    (a i j A B N : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (∑ r ∈ Finset.Icc 1 (N / A), ∑ s ∈ Finset.Icc 1 (N / B),
      selbergGcdLogPowerPrincipalCoeff a r s *
        (Real.log ((N : ℝ) / ((A * r : ℕ) : ℝ)) ^ i *
          Real.log ((N : ℝ) / ((B * s : ℕ) : ℝ)) ^ j)) =
      selbergGcdLogPowerPrincipalScaledModel a i j A B N := by
  rw [selbergGcdLogPowerPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / A), ∀ e ∈ Finset.Icc 1 (N / B),
      (∑ r ∈ Finset.Icc 1 (N / A / d),
        ∑ s ∈ Finset.Icc 1 (N / B / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((A * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((B * (e * s) : ℕ) : ℝ)) ^ j)) =
        moebiusLogPowerKernelReal i ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
          moebiusLogPowerKernelReal j ((N : ℝ) / ((B * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / A / d),
        ∑ s ∈ Finset.Icc 1 (N / B / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((A * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((B * (e * s) : ℕ) : ℝ)) ^ j)) =
          (∑ r ∈ Finset.Icc 1 (N / A / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((A * d) * r : ℕ) : ℝ)) ^ i) *
          (∑ s ∈ Finset.Icc 1 (N / B / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((B * e) * s : ℕ) : ℝ)) ^ j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [selbergMoebiusReciprocalPair]
        simp only [Nat.mul_assoc]
        ring
      _ = _ := by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
          ← moebiusLogPowerKernelReal_nat_ratio i N (A * d)
            (Nat.mul_pos hA (Finset.mem_Icc.mp hd).1),
          ← moebiusLogPowerKernelReal_nat_ratio j N (B * e)
            (Nat.mul_pos hB (Finset.mem_Icc.mp he).1)]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalLogPowerReciprocalCoeff_double_sum_eq,
    min_natDiv_eq_natDiv_max N A B hA hB,
    selbergGcdLogPowerPrincipalScaledModel]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The `(1,1)` principal model with `log(gcd)^a` differs from its harmonic moment only by a
lower-order term. -/
theorem tendsto_selbergGcdLogPowerPrincipalScaledModel_one_one_sub_harmonic_div_log_pow_zero
    (a : ℕ) {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      (selbergGcdLogPowerPrincipalScaledModel a 1 1 A B N -
        harmonicLogWindowMoment a 0 (N / max A B)) /
          Real.log N ^ (a + 1)) atTop (𝓝 0) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  set C : ℝ := DA * DB + 1 with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  set c : ℕ := max A B with hcdef
  have hc : 0 < c := lt_of_lt_of_le hA (le_max_left A B)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK2, hKclose⟩ :=
    exists_kernelProduct_close 0 0 (δ := ε / 8) (by positivity)
  have hKpos : (0 : ℝ) < K := by linarith
  have hmoment := tendsto_harmonicLogWindowMoment_natDiv_div_log_pow a hc
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist (harmonicLogWindowMoment a 0 (N / c) / Real.log N ^ (a + 1))
        (1 / ((a : ℝ) + 1)) < 1 :=
    hmoment.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  rw [eventually_atTop] at hnear
  obtain ⟨Nmoment, hNmoment⟩ := hnear
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * C * K / ε < Real.log N :=
    hlogTop.eventually_gt_atTop (4 * C * K / ε)
  rw [eventually_atTop] at hlarge
  obtain ⟨Nlarge, hNlarge⟩ := hlarge
  refine ⟨max (max Nmoment Nlarge) 2, ?_⟩
  intro N hN
  have hNmoment' : Nmoment ≤ N := (le_max_left Nmoment Nlarge).trans
    ((le_max_left (max Nmoment Nlarge) 2).trans hN)
  have hNlarge' : Nlarge ≤ N := (le_max_right Nmoment Nlarge).trans
    ((le_max_left (max Nmoment Nlarge) 2).trans hN)
  have hN2 : 2 ≤ N := (le_max_right (max Nmoment Nlarge) 2).trans hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hmomentTwo :
      harmonicLogWindowMoment a 0 (N / c) / Real.log N ^ (a + 1) < 2 := by
    have hdist := hNmoment N hNmoment'
    rw [Real.dist_eq] at hdist
    have hconst : (1 / ((a : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le a)
    have hself :
        harmonicLogWindowMoment a 0 (N / c) / Real.log N ^ (a + 1) -
            (1 / ((a : ℝ) + 1)) ≤
          |harmonicLogWindowMoment a 0 (N / c) / Real.log N ^ (a + 1) -
            (1 / ((a : ℝ) + 1))| := le_abs_self _
    linarith
  have hmomentBound : harmonicLogWindowMoment a 0 (N / c) ≤
      2 * Real.log N ^ (a + 1) := by
    have := (div_lt_iff₀ (pow_pos hlogpos (a + 1))).mp hmomentTwo
    linarith
  have hbigLog : 4 * C * K / ε < Real.log N := hNlarge N hNlarge'
  have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
      |Real.log (d : ℝ) ^ a *
          (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1) /
            (d : ℝ)| ≤
        (ε / 8) * (Real.log (d : ℝ) ^ a / (d : ℝ)) +
          C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdN : d ≤ N := le_trans (Finset.mem_Icc.mp hd).2 (Nat.div_le_self N c)
    have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
    have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hdpos)
    have hlogdN : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) hdNR
    have hlogpow : Real.log (d : ℝ) ^ a ≤ Real.log N ^ a :=
      pow_le_pow_left₀ hlogd0 hlogdN a
    have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument hA (le_max_left A B) hd
    have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((B * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument hB (le_max_right A B) hd
    have hsecond_nonneg :
        0 ≤ C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ)) := by positivity
    by_cases hcase :
        K ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) ∧
          K ≤ (N : ℝ) / ((B * d : ℕ) : ℝ)
    · have hclose := hKclose _ _ hcase.1 hcase.2
      norm_num at hclose
      have hmain :
          |Real.log (d : ℝ) ^ a *
              (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                  moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1) /
                (d : ℝ)| ≤
            (ε / 8) * (Real.log (d : ℝ) ^ a / (d : ℝ)) := by
        rw [abs_div, abs_of_pos hdR, abs_mul,
          abs_of_nonneg (pow_nonneg hlogd0 a)]
        push_cast at hclose ⊢
        calc
          Real.log (d : ℝ) ^ a *
                |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A : ℝ) * (d : ℝ))) *
                    moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B : ℝ) * (d : ℝ))) - 1| /
              (d : ℝ)
              ≤ (Real.log (d : ℝ) ^ a * (ε / 8)) / (d : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hclose (pow_nonneg hlogd0 a)) hdR.le
          _ = (ε / 8) * (Real.log (d : ℝ) ^ a / (d : ℝ)) := by ring
      linarith
    · have hsmall : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
        rcases not_and_or.mp hcase with hAcase | hBcase
        · have hlt : (N : ℝ) / ((A * d : ℕ) : ℝ) < K := lt_of_not_ge hAcase
          have hAd : (0 : ℝ) < ((A * d : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos hA hdpos
          have hNlt : (N : ℝ) < K * ((A * d : ℕ) : ℝ) := by
            rw [div_lt_iff₀ hAd] at hlt
            linarith
          have hAc : (A : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_left A B
          have hcast : ((A * d : ℕ) : ℝ) = (A : ℝ) * (d : ℝ) := by
            push_cast
            ring
          rw [hcast] at hNlt
          rw [div_le_div_iff₀ hdR hNR]
          nlinarith [hdR, hNR, hKpos.le]
        · have hlt : (N : ℝ) / ((B * d : ℕ) : ℝ) < K := lt_of_not_ge hBcase
          have hBd : (0 : ℝ) < ((B * d : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos hB hdpos
          have hNlt : (N : ℝ) < K * ((B * d : ℕ) : ℝ) := by
            rw [div_lt_iff₀ hBd] at hlt
            linarith
          have hBc : (B : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_right A B
          have hcast : ((B * d : ℕ) : ℝ) = (B : ℝ) * (d : ℝ) := by
            push_cast
            ring
          rw [hcast] at hNlt
          rw [div_le_div_iff₀ hdR hNR]
          nlinarith [hdR, hNR, hKpos.le]
      have hglobal :
          |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1| ≤ C := by
        have hKA := hDAbound _ hYAone
        have hKB := hDBbound _ hYBone
        simp only [pow_zero, mul_one] at hKA hKB
        have hprod :
            |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))| ≤
              DA * DB := by
          rw [abs_mul]
          nlinarith [abs_nonneg
            (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ))),
            abs_nonneg
              (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)))]
        rw [hCdef]
        calc
          |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1| ≤
              |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))| +
                |(1 : ℝ)| := abs_sub _ _
          _ ≤ DA * DB + 1 := by simpa [abs_mul] using hprod
      have hfirst_nonneg : 0 ≤ (ε / 8) *
          (Real.log (d : ℝ) ^ a / (d : ℝ)) := by positivity
      have hmain :
          |Real.log (d : ℝ) ^ a *
              (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                  moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1) /
                (d : ℝ)| ≤
            C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ)) := by
        rw [abs_div, abs_of_pos hdR, abs_mul,
          abs_of_nonneg (pow_nonneg hlogd0 a)]
        have hnum := mul_le_mul hlogpow hglobal (abs_nonneg _)
          (pow_nonneg hlogpos.le a)
        have hdiv := div_le_div_of_nonneg_right hnum hdR.le
        calc
          Real.log (d : ℝ) ^ a *
                |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                    moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1| /
              (d : ℝ)
              ≤ C * Real.log N ^ a / (d : ℝ) := by
                simpa [mul_comm] using hdiv
          _ ≤ C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ)) := by
                have hfac : 0 ≤ C * Real.log N ^ a := by positivity
                rw [div_eq_mul_one_div]
                exact mul_le_mul_of_nonneg_left hsmall hfac
      linarith
  rw [Real.dist_eq, sub_zero, abs_div,
    abs_of_pos (pow_pos hlogpos (a + 1))]
  rw [div_lt_iff₀ (pow_pos hlogpos (a + 1))]
  have hsum :
      selbergGcdLogPowerPrincipalScaledModel a 1 1 A B N -
          harmonicLogWindowMoment a 0 (N / c) =
        ∑ d ∈ Finset.Icc 1 (N / c),
          Real.log (d : ℝ) ^ a *
            (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1) /
              (d : ℝ) := by
    rw [selbergGcdLogPowerPrincipalScaledModel,
      harmonicLogWindowMoment_zero_eq_sum_Icc, ← hcdef,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsum]
  calc
    |∑ d ∈ Finset.Icc 1 (N / c),
        Real.log (d : ℝ) ^ a *
          (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) - 1) /
            (d : ℝ)|
        ≤ ∑ d ∈ Finset.Icc 1 (N / c),
          ((ε / 8) * (Real.log (d : ℝ) ^ a / (d : ℝ)) +
            C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ))) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (ε / 8) * harmonicLogWindowMoment a 0 (N / c) +
          ((N / c : ℕ) : ℝ) *
            (C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ))) := by
      have hcard : (((Finset.Icc 1 (N / c)).card : ℕ) : ℝ) = ((N / c : ℕ) : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← harmonicLogWindowMoment_zero_eq_sum_Icc,
        Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (ε / 8) * (2 * Real.log N ^ (a + 1)) +
          C * K * Real.log N ^ a := by
      refine add_le_add (mul_le_mul_of_nonneg_left hmomentBound (by positivity)) ?_
      have hdivle : ((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ)) ≤ 1 := by
        have h1 : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) / (c : ℝ) := by
          rw [le_div_iff₀ hcR]
          exact_mod_cast Nat.div_mul_le_self N c
        calc
          ((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ))
              ≤ ((N : ℝ) / (c : ℝ)) * ((c : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 := by field_simp
      have hrewrite : ((N / c : ℕ) : ℝ) *
          (C * Real.log N ^ a * (K * (c : ℝ) / (N : ℝ))) =
          (C * K * Real.log N ^ a) *
            (((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ))) := by ring
      rw [hrewrite]
      exact (mul_le_mul_of_nonneg_left hdivle (by positivity)).trans_eq (mul_one _)
    _ < ε * Real.log N ^ (a + 1) := by
      have hpow : Real.log N ^ (a + 1) = Real.log N ^ a * Real.log N := by
        rw [pow_succ]
      rw [hpow]
      have hCK : C * K < (ε / 4) * Real.log N := by
        rw [div_lt_iff₀ hε] at hbigLog
        nlinarith
      have hposPow : (0 : ℝ) < Real.log N ^ a := pow_pos hlogpos a
      have htail : C * K * Real.log N ^ a <
          ((ε / 4) * Real.log N) * Real.log N ^ a :=
        mul_lt_mul_of_pos_right hCK hposPow
      nlinarith [mul_pos hε (mul_pos hposPow hlogpos)]

/-- **Every principal `log(gcd)^a` moment needed by the origin-based short energy.** -/
theorem tendsto_selbergGcdLogPowerPrincipalScaledModel_one_one_div_log_pow
    (a : ℕ) {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      selbergGcdLogPowerPrincipalScaledModel a 1 1 A B N /
        Real.log N ^ (a + 1)) atTop (𝓝 (1 / ((a : ℝ) + 1))) := by
  have herr :=
    tendsto_selbergGcdLogPowerPrincipalScaledModel_one_one_sub_harmonic_div_log_pow_zero
      a hA hB
  have hmain := tendsto_harmonicLogWindowMoment_natDiv_div_log_pow a
    (lt_of_lt_of_le hA (le_max_left A B))
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  ring

/-- Harmonic model for the only higher complementary-log moment needed by the short-energy
assembly: `log(gcd)^2 log(N/m)^2 log(N/n)`. -/
def selbergGcdLogSquareTwoOneHarmonicMain (A B N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max A B),
    2 * Real.log (d : ℝ) ^ 2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) / (d : ℝ)

private theorem log_natCast_div_mul_eq_sub_sub
    {N A d : ℕ} (hN : 0 < N) (hA : 0 < A) (hd : 0 < d) :
    Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) =
      Real.log N - Real.log A - Real.log d := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_mul, Real.log_div hNR (mul_ne_zero hAR hdR), Real.log_mul hAR hdR]
  ring

theorem selbergGcdLogSquareTwoOneHarmonicMain_eq
    {A B N : ℕ} (hN : 0 < N) (hA : 0 < A) :
    selbergGcdLogSquareTwoOneHarmonicMain A B N =
      2 * ((Real.log N - Real.log A) * harmonicLogWindowMoment 2 0 (N / max A B) -
        harmonicLogWindowMoment 3 0 (N / max A B)) := by
  rw [selbergGcdLogSquareTwoOneHarmonicMain,
    harmonicLogWindowMoment_zero_eq_sum_Icc, harmonicLogWindowMoment_zero_eq_sum_Icc]
  calc
    (∑ d ∈ Finset.Icc 1 (N / max A B),
        2 * Real.log (d : ℝ) ^ 2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) /
          (d : ℝ)) =
      ∑ d ∈ Finset.Icc 1 (N / max A B),
        2 * ((Real.log N - Real.log A) * (Real.log (d : ℝ) ^ 2 / (d : ℝ)) -
          Real.log (d : ℝ) ^ 3 / (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        rw [log_natCast_div_mul_eq_sub_sub hN hA hdpos]
        ring
    _ = 2 * ((Real.log N - Real.log A) *
          (∑ d ∈ Finset.Icc 1 (N / max A B), Real.log (d : ℝ) ^ 2 / (d : ℝ)) -
        ∑ d ∈ Finset.Icc 1 (N / max A B), Real.log (d : ℝ) ^ 3 / (d : ℝ)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]

private theorem tendsto_log_nat_sub_const_div_log (c : ℝ) :
    Tendsto (fun N : ℕ => (Real.log N - c) / Real.log N) atTop (nhds 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => c / Real.log N) atTop (nhds 0) :=
    hlog.const_div_atTop c
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hc
  have h' : Tendsto (fun N : ℕ => 1 - c / Real.log N) atTop (nhds 1) := by
    simpa only [sub_zero] using h
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlogN]

/-- The harmonic model has the beta-integral coefficient `1/6`. -/
theorem tendsto_selbergGcdLogSquareTwoOneHarmonicMain_div_log_four
    {A B : ℕ} (hA : 0 < A) (_hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      selbergGcdLogSquareTwoOneHarmonicMain A B N / Real.log N ^ 4)
      atTop (nhds (1 / 6 : ℝ)) := by
  let c := max A B
  have hc : 0 < c := lt_of_lt_of_le hA (le_max_left A B)
  have h2 := tendsto_harmonicLogWindowMoment_natDiv_div_log_pow 2 hc
  have h3 := tendsto_harmonicLogWindowMoment_natDiv_div_log_pow 3 hc
  norm_num at h2 h3
  have hratio := tendsto_log_nat_sub_const_div_log (Real.log A)
  have hprod := hratio.mul h2
  have hcomb := (hprod.sub h3).const_mul (2 : ℝ)
  norm_num at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergGcdLogSquareTwoOneHarmonicMain_eq (by omega) hA]
  dsimp only [c] at *
  field_simp [hlog]

/-- Uniform fourth-order envelope for the corresponding principal model. -/
theorem exists_abs_selbergGcdLogPowerPrincipalScaledModel_two_two_one_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ A B : ℕ, 0 < A → 0 < B →
      |selbergGcdLogPowerPrincipalScaledModel 2 2 1 A B N| ≤
        M * Real.log N ^ 4 := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 1
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  refine ⟨2 * DA * DB, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN A B hA hB
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hratioTwo : (harmonic N : ℝ) / Real.log N < 2 := by
    rw [Real.dist_eq] at hnearN
    have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
        |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
    linarith
  have hharm : (harmonic N : ℝ) ≤ 2 * Real.log N := by
    have := (div_lt_iff₀ hlogpos).mp hratioTwo
    linarith
  rw [selbergGcdLogPowerPrincipalScaledModel]
  calc
    |∑ d ∈ Finset.Icc 1 (N / max A B),
        Real.log (d : ℝ) ^ 2 *
          (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
          (d : ℝ)| ≤
      ∑ d ∈ Finset.Icc 1 (N / max A B),
        |Real.log (d : ℝ) ^ 2 *
          (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
          (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / max A B),
        DA * DB * Real.log N ^ 3 * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hdN : d ≤ N :=
        (Finset.mem_Icc.mp hd).2.trans (Nat.div_le_self N (max A B))
      have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      have hlogd0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hdpos)
      have hlogdN : Real.log (d : ℝ) ≤ Real.log N :=
        Real.log_le_log (by positivity) hdNR
      have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument hA (le_max_left A B) hd
      have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((B * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument hB (le_max_right A B) hd
      have hYAle : (N : ℝ) / ((A * d : ℕ) : ℝ) ≤ (N : ℝ) :=
        selbergScaledArgument_le_natCast hA hdpos
      have hLA0 : 0 ≤ Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) :=
        Real.log_nonneg hYAone
      have hLAle : Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) ≤ Real.log N :=
        Real.log_le_log (by positivity) hYAle
      have hKA := hDAbound _ hYAone
      have hKB := hDBbound _ hYBone
      simp only [pow_zero, mul_one] at hKB
      rw [abs_div, abs_of_pos hdR, abs_mul,
        abs_of_nonneg (sq_nonneg _), abs_mul]
      rw [div_le_iff₀ hdR]
      have hlogSq : Real.log (d : ℝ) ^ 2 ≤ Real.log N ^ 2 :=
        pow_le_pow_left₀ hlogd0 hlogdN 2
      have hKA' : |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ))| ≤
          DA * Real.log N := by
        have hKA0 : |moebiusLogPowerKernelReal 2
            ((N : ℝ) / ((A * d : ℕ) : ℝ))| ≤
            DA * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) := by
          simpa only [pow_one] using hKA
        exact hKA0.trans (mul_le_mul_of_nonneg_left hLAle hDA)
      have hcore := mul_le_mul
        (mul_le_mul hlogSq hKA' (abs_nonneg _) (sq_nonneg _)) hKB
        (abs_nonneg _) (by positivity : 0 ≤ Real.log N ^ 2 * (DA * Real.log N))
      calc
        Real.log (d : ℝ) ^ 2 *
            (|moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ))| *
              |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))|) ≤
            Real.log N ^ 2 * (DA * Real.log N) * DB := by
              calc
                _ = (Real.log (d : ℝ) ^ 2 *
                    |moebiusLogPowerKernelReal 2
                      ((N : ℝ) / ((A * d : ℕ) : ℝ))|) *
                    |moebiusLogPowerKernelReal 1
                      ((N : ℝ) / ((B * d : ℕ) : ℝ))| := by ring
                _ ≤ _ := by simpa only [Nat.zero_add, Nat.one_add] using hcore
        _ = DA * DB * Real.log N ^ 3 * (1 / (d : ℝ)) * (d : ℝ) := by
          field_simp
    _ = DA * DB * Real.log N ^ 3 * (harmonic (N / max A B) : ℝ) := by
      rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
    _ ≤ DA * DB * Real.log N ^ 3 * (harmonic N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (RHTower.harmonic_cast_mono (Nat.div_le_self N (max A B))) (by positivity)
    _ ≤ DA * DB * Real.log N ^ 3 * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = 2 * DA * DB * Real.log N ^ 4 := by ring

/-- Exact single-sum error after replacing the two Möbius kernels by their leading product. -/
theorem selbergGcdLogPowerPrincipalScaledModel_two_two_one_sub_harmonicMain
    (A B N : ℕ) :
    selbergGcdLogPowerPrincipalScaledModel 2 2 1 A B N -
        selbergGcdLogSquareTwoOneHarmonicMain A B N =
      ∑ d ∈ Finset.Icc 1 (N / max A B),
        Real.log (d : ℝ) ^ 2 *
          (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))) / (d : ℝ) := by
  rw [selbergGcdLogPowerPrincipalScaledModel, selbergGcdLogSquareTwoOneHarmonicMain,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Harmonic replacement for `log(gcd)^2 log(N/m)^2 log(N/n)`. -/
theorem tendsto_selbergGcdLogPowerPrincipalScaledModel_two_two_one_sub_harmonic_div_log_four_zero
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      (selbergGcdLogPowerPrincipalScaledModel 2 2 1 A B N -
        selbergGcdLogSquareTwoOneHarmonicMain A B N) / Real.log N ^ 4)
      atTop (nhds 0) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 1
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  set C : ℝ := DA * DB + 2 with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  set c : ℕ := max A B with hcdef
  have hc : 0 < c := lt_of_lt_of_le hA (le_max_left A B)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK2, hKclose⟩ := exists_kernelProduct_close 1 0 (δ := ε / 8) (by positivity)
  have hKpos : (0 : ℝ) < K := by linarith
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  rw [eventually_atTop] at hnear
  obtain ⟨Nh, hNh⟩ := hnear
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * C * K / ε < Real.log N :=
    hlogTop.eventually_gt_atTop (4 * C * K / ε)
  rw [eventually_atTop] at hlarge
  obtain ⟨Nl, hNl⟩ := hlarge
  refine ⟨max (max Nh Nl) 2, ?_⟩
  intro N hN
  have hNhN : Nh ≤ N := (le_max_left Nh Nl).trans
    ((le_max_left (max Nh Nl) 2).trans hN)
  have hNlN : Nl ≤ N := (le_max_right Nh Nl).trans
    ((le_max_left (max Nh Nl) 2).trans hN)
  have hN2 : 2 ≤ N := (le_max_right (max Nh Nl) 2).trans hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hharm : (harmonic N : ℝ) ≤ 2 * Real.log N := by
    have hdist := hNh N hNhN
    rw [Real.dist_eq] at hdist
    have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
        |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
    have hlt : (harmonic N : ℝ) / Real.log N < 2 := by linarith
    exact (div_lt_iff₀ hlogpos).mp hlt |>.le
  have hbigLog : 4 * C * K / ε < Real.log N := hNl N hNlN
  have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
      |Real.log (d : ℝ) ^ 2 *
          (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))) / (d : ℝ)| ≤
        (ε / 8) * Real.log N ^ 3 * (1 / (d : ℝ)) +
          C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2.trans (Nat.div_le_self N c)
    have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
    have hlogd0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hdpos)
    have hlogdN : Real.log (d : ℝ) ≤ Real.log N :=
      Real.log_le_log (by positivity) hdNR
    have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument hA (le_max_left A B) (by simpa [c, hcdef] using hd)
    have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((B * d : ℕ) : ℝ) :=
      one_le_selbergScaledArgument hB (le_max_right A B) (by simpa [c, hcdef] using hd)
    have hYAle : (N : ℝ) / ((A * d : ℕ) : ℝ) ≤ (N : ℝ) :=
      selbergScaledArgument_le_natCast hA hdpos
    have hYBle : (N : ℝ) / ((B * d : ℕ) : ℝ) ≤ (N : ℝ) :=
      selbergScaledArgument_le_natCast hB hdpos
    have hLA0 : 0 ≤ Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) := Real.log_nonneg hYAone
    have hLAle : Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) ≤ Real.log N :=
      Real.log_le_log (by positivity) hYAle
    have hLB0 : 0 ≤ Real.log ((N : ℝ) / ((B * d : ℕ) : ℝ)) := Real.log_nonneg hYBone
    have hLBle : Real.log ((N : ℝ) / ((B * d : ℕ) : ℝ)) ≤ Real.log N :=
      Real.log_le_log (by positivity) hYBle
    have hlogSq : Real.log (d : ℝ) ^ 2 ≤ Real.log N ^ 2 :=
      pow_le_pow_left₀ hlogd0 hlogdN 2
    have hsecond : 0 ≤ C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ)) := by positivity
    by_cases hgood : K ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) ∧
        K ≤ (N : ℝ) / ((B * d : ℕ) : ℝ)
    · have hclose := hKclose _ _ hgood.1 hgood.2
      norm_num [pow_zero] at hclose
      have hLAle' :
          Real.log ((N : ℝ) / ((A : ℝ) * (d : ℝ))) ≤ Real.log N := by
        simpa only [Nat.cast_mul] using hLAle
      have hclose' :
          |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
              2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))| ≤
            (ε / 8) * Real.log N := by
        have hclose'' :=
          hclose.trans (mul_le_mul_of_nonneg_left hLAle' (by positivity : 0 ≤ ε / 8))
        simpa only [Nat.cast_mul] using hclose''
      have hmain : |Real.log (d : ℝ) ^ 2 *
            (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
              2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))) / (d : ℝ)| ≤
          (ε / 8) * Real.log N ^ 3 * (1 / (d : ℝ)) := by
        rw [abs_div, abs_of_pos hdR, abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hmul := mul_le_mul hlogSq hclose' (abs_nonneg _) (sq_nonneg (Real.log N))
        calc
          Real.log (d : ℝ) ^ 2 *
                |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                    moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
                  2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))| / (d : ℝ) ≤
              (Real.log N ^ 2 * ((ε / 8) * Real.log N)) / (d : ℝ) :=
                div_le_div_of_nonneg_right hmul hdR.le
          _ = (ε / 8) * Real.log N ^ 3 * (1 / (d : ℝ)) := by ring
      linarith
    · have hsmall : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
        rcases not_and_or.mp hgood with hbad | hbad
        · have hlt := lt_of_not_ge hbad
          have hAd : (0 : ℝ) < ((A * d : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hA hdpos
          have hNlt : (N : ℝ) < K * ((A * d : ℕ) : ℝ) :=
            (div_lt_iff₀ hAd).mp hlt
          rw [div_le_div_iff₀ hdR hNR]
          push_cast at hNlt
          have hAc : (A : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_left A B
          nlinarith [hKpos.le]
        · have hlt := lt_of_not_ge hbad
          have hBd : (0 : ℝ) < ((B * d : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hB hdpos
          have hNlt : (N : ℝ) < K * ((B * d : ℕ) : ℝ) :=
            (div_lt_iff₀ hBd).mp hlt
          rw [div_le_div_iff₀ hdR hNR]
          push_cast at hNlt
          have hBc : (B : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_right A B
          nlinarith [hKpos.le]
      have hKA := hDAbound _ hYAone
      have hKB := hDBbound _ hYBone
      simp only [pow_one] at hKA
      simp only [pow_zero, mul_one] at hKB
      have hdiff : |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))| ≤ C * Real.log N := by
        rw [hCdef]
        calc
          _ ≤ |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ))| *
                |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))| +
              2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) := by
                calc
                  _ ≤ |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                        moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))| +
                      |2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))| := abs_sub _ _
                  _ = _ := by
                    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hLA0)]
          _ ≤ (DA * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))) * DB +
              2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ)) := by
                gcongr
          _ ≤ (DA * Real.log N) * DB + 2 * Real.log N := by gcongr
          _ = (DA * DB + 2) * Real.log N := by ring
      rw [abs_div, abs_of_pos hdR, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hprod := mul_le_mul hlogSq hdiff (abs_nonneg _) (sq_nonneg (Real.log N))
      calc
        Real.log (d : ℝ) ^ 2 *
              |moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
                  moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
                2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))| / (d : ℝ) ≤
            C * Real.log N ^ 3 * (1 / (d : ℝ)) := by
              have := div_le_div_of_nonneg_right hprod hdR.le
              calc
                _ ≤ (Real.log N ^ 2 * (C * Real.log N)) / (d : ℝ) := this
                _ = _ := by ring
        _ ≤ C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ ≤ (ε / 8) * Real.log N ^ 3 * (1 / (d : ℝ)) +
            C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ)) :=
          le_add_of_nonneg_left (by positivity)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (pow_pos hlogpos 4),
    div_lt_iff₀ (pow_pos hlogpos 4)]
  rw [selbergGcdLogPowerPrincipalScaledModel_two_two_one_sub_harmonicMain, ← hcdef]
  calc
    |∑ d ∈ Finset.Icc 1 (N / c),
        Real.log (d : ℝ) ^ 2 *
          (moebiusLogPowerKernelReal 2 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((A * d : ℕ) : ℝ))) / (d : ℝ)| ≤
      ∑ d ∈ Finset.Icc 1 (N / c),
        ((ε / 8) * Real.log N ^ 3 * (1 / (d : ℝ)) +
          C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ))) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (ε / 8) * Real.log N ^ 3 * (harmonic (N / c) : ℝ) +
        ((N / c : ℕ) : ℝ) *
          (C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_Icc_one_div_eq_harmonic,
        Finset.sum_const, nsmul_eq_mul]
      rw [Nat.card_Icc]
      norm_num
    _ ≤ (ε / 4) * Real.log N ^ 4 + C * K * Real.log N ^ 3 := by
      refine add_le_add ?_ ?_
      · calc
          (ε / 8) * Real.log N ^ 3 * (harmonic (N / c) : ℝ) ≤
              (ε / 8) * Real.log N ^ 3 * (harmonic N : ℝ) :=
            mul_le_mul_of_nonneg_left
              (RHTower.harmonic_cast_mono (Nat.div_le_self N c)) (by positivity)
          _ ≤ (ε / 8) * Real.log N ^ 3 * (2 * Real.log N) :=
            mul_le_mul_of_nonneg_left hharm (by positivity)
          _ = (ε / 4) * Real.log N ^ 4 := by ring
      · have hdivle : ((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ)) ≤ 1 := by
          have hq : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) / (c : ℝ) := by
            rw [le_div_iff₀ hcR]
            exact_mod_cast Nat.div_mul_le_self N c
          calc
            _ ≤ ((N : ℝ) / (c : ℝ)) * ((c : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_right hq (by positivity)
            _ = 1 := by field_simp
        have hm := mul_le_mul_of_nonneg_left hdivle
          (show 0 ≤ C * K * Real.log N ^ 3 by positivity)
        calc
          ((N / c : ℕ) : ℝ) *
              (C * Real.log N ^ 3 * (K * (c : ℝ) / (N : ℝ))) =
              (C * K * Real.log N ^ 3) *
                (((N / c : ℕ) : ℝ) * ((c : ℝ) / (N : ℝ))) := by ring
          _ ≤ C * K * Real.log N ^ 3 := by simpa using hm
    _ < ε * Real.log N ^ 4 := by
      have hCK : C * K < (ε / 4) * Real.log N := by
        rw [div_lt_iff₀ hε] at hbigLog
        nlinarith
      have htail := mul_lt_mul_of_pos_right hCK (pow_pos hlogpos 3)
      calc
        (ε / 4) * Real.log N ^ 4 + C * K * Real.log N ^ 3 <
            (ε / 4) * Real.log N ^ 4 +
              (ε / 4) * Real.log N * Real.log N ^ 3 := by
          have hadd := add_lt_add_left htail ((ε / 4) * Real.log N ^ 4)
          linarith only [hadd]
        _ = (ε / 2) * Real.log N ^ 4 := by ring
        _ < ε * Real.log N ^ 4 := by
          have hpow : 0 < Real.log N ^ 4 := pow_pos hlogpos 4
          nlinarith

/-- The principal `(2,1)` square-gcd-log model has leading coefficient `1/6`. -/
theorem tendsto_selbergGcdLogPowerPrincipalScaledModel_two_two_one_div_log_four
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      selbergGcdLogPowerPrincipalScaledModel 2 2 1 A B N / Real.log N ^ 4)
      atTop (nhds (1 / 6 : ℝ)) := by
  have herr :=
    tendsto_selbergGcdLogPowerPrincipalScaledModel_two_two_one_sub_harmonic_div_log_four_zero
      hA hB
  have hmain := tendsto_selbergGcdLogSquareTwoOneHarmonicMain_div_log_four hA hB
  have h := herr.add hmain
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]
  ring

end

end RHTower.Sieve
