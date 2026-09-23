import GaloisForLFunctions.RHTower.Sieve.PrimeLeakageEstimates
import GaloisForLFunctions.RHTower.Sieve.PrimeProfileTransferLimit

/-!
# The two leakage remainders vanish

Reading each prime `p ≤ N` at its exponent `t_p = log p / log N` and driving the projective clock
with a bounded weight profile `f`, two remainders separate the exact leakage product from the
prime-profile sum:

* `Σ_{p ≤ N} ( L_p(f(t_p)) − (e^{f(t_p)} − 1)²/p )`, the deviation of the exact leakage from its
  leading prime-density term;
* `Σ_{p ≤ N} ( log (1 − L_p(f(t_p))) + L_p(f(t_p)) )`, the quadratic defect of the logarithm.

Both vanish.  Each term is `O(p⁻²)` uniformly in the scale — the first by the leakage expansion, the
second because the uniform bound `L_p ≤ θ < 1` holds for *every* prime — and each tends to zero for
a fixed prime, because `log p / log N → 0` and `f` vanishes at the origin.  Dominated vanishing of
prime sums over a growing range then applies verbatim.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-! ## The exponent coordinate of a fixed prime dies -/

theorem tendsto_exponentCoord (p : ℕ) :
    Tendsto (fun N : ℕ => Real.log p / Real.log N) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds tendsto_log_natCast_atTop'

/-! ## Uniform bounds from a bounded weight -/

theorem sq_exp_sub_one_le {z F : ℝ} (hz : |z| ≤ F) :
    (Real.exp z - 1) ^ (2 : ℕ) ≤ (Real.exp F - 1) ^ (2 : ℕ) := by
  have hFnn : 0 ≤ F := le_trans (abs_nonneg z) hz
  have hzF : z ≤ F := le_trans (le_abs_self z) hz
  have hFz : -F ≤ z := neg_le_of_abs_le hz
  have hup : Real.exp z ≤ Real.exp F := Real.exp_le_exp.mpr hzF
  have hlow : Real.exp (-F) ≤ Real.exp z := Real.exp_le_exp.mpr hFz
  have hone : (1 : ℝ) ≤ Real.exp F := Real.one_le_exp hFnn
  have hprod : Real.exp F * Real.exp (-F) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsum : (2 : ℝ) ≤ Real.exp F + Real.exp (-F) := by
    nlinarith [sq_nonneg (Real.exp F - 1), Real.exp_pos F, Real.exp_pos (-F), hprod]
  have habs : |Real.exp z - 1| ≤ Real.exp F - 1 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hnn : (0 : ℝ) ≤ Real.exp F - 1 := by linarith
  calc (Real.exp z - 1) ^ (2 : ℕ) = |Real.exp z - 1| ^ (2 : ℕ) := (sq_abs _).symm
    _ ≤ (Real.exp F - 1) ^ (2 : ℕ) := by gcongr

theorem exp_sq_le {z F : ℝ} (hz : |z| ≤ F) : Real.exp z ^ (2 : ℕ) ≤ Real.exp F ^ (2 : ℕ) := by
  have hzF : z ≤ F := le_trans (le_abs_self z) hz
  have hup : Real.exp z ≤ Real.exp F := Real.exp_le_exp.mpr hzF
  nlinarith [Real.exp_pos z, hup]

/-! ## The leakage expansion remainder -/

/-- The summand of the leakage-expansion remainder, cut off below the first prime. -/
def leakageExpansionTerm (f : ℝ → ℝ) (N p : ℕ) : ℝ :=
  if 2 ≤ p then
    primeLeakage p (f (Real.log p / Real.log N))
      - (Real.exp (f (Real.log p / Real.log N)) - 1) ^ (2 : ℕ) / (p : ℝ)
  else 0

theorem abs_leakageExpansionTerm_le {f : ℝ → ℝ} {F : ℝ} (hfb : ∀ t, |f t| ≤ F) (N p : ℕ) :
    |leakageExpansionTerm f N p|
      ≤ ((Real.exp F - 1) ^ (2 : ℕ) * (1 + Real.exp F ^ (2 : ℕ))) / (p : ℝ) ^ (2 : ℕ) := by
  rw [leakageExpansionTerm]
  split_ifs with hp
  · set z : ℝ := f (Real.log p / Real.log N) with hz
    have hzF := hfb (Real.log p / Real.log N)
    have hbase := abs_primeLeakage_sub_div_le hp z
    refine le_trans hbase ?_
    have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 : (Real.exp z - 1) ^ (2 : ℕ) ≤ (Real.exp F - 1) ^ (2 : ℕ) := sq_exp_sub_one_le hzF
    have h2 : Real.exp z ^ (2 : ℕ) ≤ Real.exp F ^ (2 : ℕ) := exp_sq_le hzF
    have hnn1 : (0 : ℝ) ≤ (Real.exp z - 1) ^ (2 : ℕ) := sq_nonneg _
    have hnn2 : (0 : ℝ) ≤ 1 + Real.exp z ^ (2 : ℕ) := by positivity
    nlinarith [hnn1, hnn2, h1, h2, sq_nonneg (Real.exp F - 1)]
  · have hnn : (0 : ℝ) ≤ ((Real.exp F - 1) ^ (2 : ℕ) * (1 + Real.exp F ^ (2 : ℕ))) / (p : ℝ) ^ (2 : ℕ) := by
      positivity
    simpa using hnn

theorem tendsto_leakageExpansionTerm {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) (p : ℕ) :
    Tendsto (fun N : ℕ => leakageExpansionTerm f N p) atTop (𝓝 0) := by
  by_cases hp : 2 ≤ p
  · have hcoord := tendsto_exponentCoord p
    have hfz : Tendsto (fun N : ℕ => f (Real.log p / Real.log N)) atTop (𝓝 0) := by
      have := (hf.tendsto 0).comp hcoord
      rwa [hf0] at this
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hleak : Tendsto (fun N : ℕ => primeLeakage p (f (Real.log p / Real.log N))) atTop
        (𝓝 0) := by
      have hcont : Continuous (fun z : ℝ => primeLeakage p z) := by
        unfold primeLeakage
        have hden : ∀ z : ℝ, (p : ℝ) + Real.exp z ^ (2 : ℕ) ≠ 0 := by
          intro z
          have : (0 : ℝ) < (p : ℝ) + Real.exp z ^ (2 : ℕ) := by positivity
          exact ne_of_gt this
        fun_prop (disch := exact hden _)
      have hcomp := (hcont.tendsto 0).comp hfz
      simp only [Function.comp_def] at hcomp
      rwa [primeLeakage_zero] at hcomp
    have hprof : Tendsto (fun N : ℕ =>
        (Real.exp (f (Real.log p / Real.log N)) - 1) ^ (2 : ℕ) / (p : ℝ)) atTop (𝓝 0) := by
      have hcont : Continuous (fun z : ℝ => (Real.exp z - 1) ^ (2 : ℕ) / (p : ℝ)) := by fun_prop
      have hcomp := (hcont.tendsto 0).comp hfz
      simp only [Function.comp_def] at hcomp
      simpa using hcomp
    have hsub := hleak.sub hprof
    rw [sub_zero] at hsub
    refine hsub.congr ?_
    intro N
    rw [leakageExpansionTerm, if_pos hp]
  · simp only [leakageExpansionTerm, if_neg hp]
    exact tendsto_const_nhds

/-- **Equation (17).**  The exact leakage differs from its leading prime-density term by a sum that
vanishes at all-prime aperture. -/
theorem tendsto_sum_leakageExpansion {f : ℝ → ℝ} {F : ℝ} (hf : Continuous f) (hf0 : f 0 = 0)
    (hfb : ∀ t, |f t| ≤ F) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N, leakageExpansionTerm f N p) atTop (𝓝 0) := by
  refine tendsto_sum_primesLE_of_dominated
    (b := fun p => ((Real.exp F - 1) ^ (2 : ℕ) * (1 + Real.exp F ^ (2 : ℕ))) / (p : ℝ) ^ (2 : ℕ)) ?_ ?_ ?_ ?_
  · exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _ |>.congr
      (fun p => by rw [mul_one_div])
  · intro p
    positivity
  · intro N p
    exact abs_leakageExpansionTerm_le hfb N p
  · intro p
    exact tendsto_leakageExpansionTerm hf hf0 p

/-! ## The logarithmic defect -/

/-- The summand of the logarithmic defect, cut off below the first prime. -/
def leakageLogDefectTerm (f : ℝ → ℝ) (N p : ℕ) : ℝ :=
  if 2 ≤ p then
    Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))
      + primeLeakage p (f (Real.log p / Real.log N))
  else 0

theorem abs_leakageLogDefectTerm_le {f : ℝ → ℝ} {F : ℝ} (hfb : ∀ t, |f t| ≤ F) (N p : ℕ) :
    |leakageLogDefectTerm f N p|
      ≤ ((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) /
          ((1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) * (p : ℝ) ^ (2 : ℕ)) := by
  have hθ := theta_lt_one F
  have hgap : (0 : ℝ) < 1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ)) := by linarith
  rw [leakageLogDefectTerm]
  split_ifs with hp
  · set z : ℝ := f (Real.log p / Real.log N) with hz
    have hzF := hfb (Real.log p / Real.log N)
    have hzle : z ≤ F := le_trans (le_abs_self z) hzF
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hL0 := primeLeakage_nonneg hp z
    have hLθ := primeLeakage_le_theta hp hzle
    have hbase := abs_log_one_sub_add_le hL0 hθ hLθ
    refine le_trans hbase ?_
    have hLdiv : primeLeakage p z ≤ (Real.exp F - 1) ^ (2 : ℕ) / (p : ℝ) := by
      refine le_trans (primeLeakage_le_div hp z) ?_
      exact div_le_div_of_nonneg_right (sq_exp_sub_one_le hzF) (by linarith)
    have hsq : primeLeakage p z ^ (2 : ℕ) ≤ ((Real.exp F - 1) ^ (2 : ℕ) / (p : ℝ)) ^ (2 : ℕ) := by
      have hd0 : (0 : ℝ) ≤ (Real.exp F - 1) ^ (2 : ℕ) / (p : ℝ) := le_trans hL0 hLdiv
      nlinarith [hL0, hLdiv, hd0]
    rw [div_le_div_iff₀ hgap (by positivity)]
    have hexp : ((Real.exp F - 1) ^ (2 : ℕ) / (p : ℝ)) ^ (2 : ℕ)
        = ((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) / (p : ℝ) ^ (2 : ℕ) := by
      rw [div_pow]
    rw [hexp] at hsq
    have hp2 : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
    calc primeLeakage p z ^ (2 : ℕ) * ((1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) * (p : ℝ) ^ (2 : ℕ))
        ≤ (((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) / (p : ℝ) ^ (2 : ℕ)) *
            ((1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) * (p : ℝ) ^ (2 : ℕ)) := by
          gcongr
      _ = ((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) *
            (1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) := by
          field_simp
  · have hnn : (0 : ℝ) ≤ ((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) /
        ((1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) * (p : ℝ) ^ (2 : ℕ)) := by
      positivity
    simpa using hnn

theorem tendsto_leakageLogDefectTerm {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) (p : ℕ) :
    Tendsto (fun N : ℕ => leakageLogDefectTerm f N p) atTop (𝓝 0) := by
  by_cases hp : 2 ≤ p
  · have hcoord := tendsto_exponentCoord p
    have hfz : Tendsto (fun N : ℕ => f (Real.log p / Real.log N)) atTop (𝓝 0) := by
      have := (hf.tendsto 0).comp hcoord
      rwa [hf0] at this
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hcont : Continuous (fun z : ℝ => primeLeakage p z) := by
      unfold primeLeakage
      have hden : ∀ z : ℝ, (p : ℝ) + Real.exp z ^ (2 : ℕ) ≠ 0 := by
        intro z
        have : (0 : ℝ) < (p : ℝ) + Real.exp z ^ (2 : ℕ) := by positivity
        exact ne_of_gt this
      fun_prop (disch := exact hden _)
    have hleak : Tendsto (fun N : ℕ => primeLeakage p (f (Real.log p / Real.log N))) atTop
        (𝓝 0) := by
      have hcomp := (hcont.tendsto 0).comp hfz
      simp only [Function.comp_def] at hcomp
      rwa [primeLeakage_zero] at hcomp
    have hlog : Tendsto (fun N : ℕ =>
        Real.log (1 - primeLeakage p (f (Real.log p / Real.log N)))) atTop (𝓝 0) := by
      have hone : Tendsto (fun N : ℕ =>
          1 - primeLeakage p (f (Real.log p / Real.log N))) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hleak
        simpa using this
      have hcomp := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone
      simp only [Function.comp_def] at hcomp
      simpa using hcomp
    have hadd := hlog.add hleak
    rw [add_zero] at hadd
    refine hadd.congr ?_
    intro N
    rw [leakageLogDefectTerm, if_pos hp]
  · simp only [leakageLogDefectTerm, if_neg hp]
    exact tendsto_const_nhds

/-- **Equation (19).**  The quadratic defect of the logarithm vanishes at all-prime aperture. -/
theorem tendsto_sum_leakageLogDefect {f : ℝ → ℝ} {F : ℝ} (hf : Continuous f) (hf0 : f 0 = 0)
    (hfb : ∀ t, |f t| ≤ F) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N, leakageLogDefectTerm f N p) atTop (𝓝 0) := by
  have hθ := theta_lt_one F
  have hgap : (0 : ℝ) < 1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ)) := by linarith
  refine tendsto_sum_primesLE_of_dominated
    (b := fun p => ((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) /
      ((1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))) * (p : ℝ) ^ (2 : ℕ))) ?_ ?_ ?_ ?_
  · have hbase := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left
      (((Real.exp F - 1) ^ (2 : ℕ)) ^ (2 : ℕ) / (1 - (Real.exp F ^ (2 : ℕ) + 1) / (2 + Real.exp F ^ (2 : ℕ))))
    refine hbase.congr ?_
    intro p
    field_simp
  · intro p
    positivity
  · intro N p
    exact abs_leakageLogDefectTerm_le hfb N p
  · intro p
    exact tendsto_leakageLogDefectTerm hf hf0 p

end

end RHTower.Sieve
