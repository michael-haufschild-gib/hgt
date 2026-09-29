import GaloisForLFunctions.RHTower.ThetaMovingShellFourierJet
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Complete omitted theta-tail jets at a moving square cutoff

Every later shell is retained. A summable Gaussian majorant makes all shells
after the first omitted one vanish in the joint normalized limit.
-/

open Real Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

def thetaMovingTailJetTerm (N j k : ℕ) (lambda : ℝ) : ℂ :=
  ((Real.exp (-Real.pi * (thetaMovingShellScale (N+j) - thetaMovingShellScale N)) *
    (thetaMovingShellScale (N+j) / thetaMovingShellScale N) *
      (thetaMovingShellScale N / thetaMovingShellScale (N+j))^k : ℝ) : ℂ) *
        thetaMovingShellGammaJet (N+j) k
          (lambda * thetaMovingShellScale N / thetaMovingShellScale (N+j))

def thetaMovingTailJet (N k : ℕ) (lambda : ℝ) : ℂ :=
  ∑' j : ℕ, thetaMovingTailJetTerm N j k lambda

/-- The complete literal omitted source, with no shells discarded. -/
def thetaShellTailFrequencyJet (N k : ℕ) (b : ℝ) : ℂ :=
  ∑' j : ℕ, thetaShellFrequencyJet (N+j) k b

theorem thetaMovingTailJetTerm_eq_normalized_shell (N j k : ℕ) (lambda : ℝ) :
    thetaMovingTailJetTerm N j k lambda =
      ((Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
        thetaMovingShellScale N^k : ℝ) : ℂ) *
          thetaShellFrequencyJet (N+j) k (lambda * thetaMovingShellScale N) := by
  have ha := (thetaMovingShellScale_pos N).ne'
  have hb := (thetaMovingShellScale_pos (N+j)).ne'
  unfold thetaMovingTailJetTerm
  rw [thetaMovingShellGammaJet_eq_normalized_shell]
  rw [div_mul_cancel₀ _ hb]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  have he : Real.exp (-Real.pi * (thetaMovingShellScale (N+j)-thetaMovingShellScale N)) *
      Real.exp (Real.pi * thetaMovingShellScale (N+j)) =
        Real.exp (Real.pi * thetaMovingShellScale N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  simp only [div_pow]
  field_simp [ha, hb]

theorem thetaMovingTailJet_eq_normalized_shell_tsum (N k : ℕ) (lambda : ℝ) :
    thetaMovingTailJet N k lambda =
      ((Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
        thetaMovingShellScale N^k : ℝ) : ℂ) *
          thetaShellTailFrequencyJet N k (lambda * thetaMovingShellScale N) := by
  simp only [thetaMovingTailJet, thetaShellTailFrequencyJet,
    thetaMovingTailJetTerm_eq_normalized_shell, tsum_mul_left]

theorem thetaMovingShellScale_add_sub (N j : ℕ) :
    thetaMovingShellScale (N+j) - thetaMovingShellScale N =
      2 * ((N : ℝ)+1) * (j : ℝ) + (j : ℝ)^2 := by
  unfold thetaMovingShellScale
  push_cast
  ring

theorem thetaMovingShellScale_le_add (N j : ℕ) :
    thetaMovingShellScale N ≤ thetaMovingShellScale (N+j) := by
  rw [← sub_nonneg, thetaMovingShellScale_add_sub]
  positivity

theorem thetaMovingShellScale_add_le_mul (N j : ℕ) :
    thetaMovingShellScale (N+j) ≤ thetaMovingShellScale N * ((j : ℝ)+1)^2 := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hlin : (N : ℝ)+(j : ℝ)+1 ≤ ((N : ℝ)+1)*((j : ℝ)+1) := by
    nlinarith [mul_nonneg hN hj]
  unfold thetaMovingShellScale
  push_cast
  nlinarith [sq_nonneg (((N : ℝ)+1)*((j : ℝ)+1)-((N : ℝ)+(j : ℝ)+1))]

theorem thetaMovingTailJetTerm_zero (N k : ℕ) (lambda : ℝ) :
    thetaMovingTailJetTerm N 0 k lambda = thetaMovingShellGammaJet N k lambda := by
  have ha := (thetaMovingShellScale_pos N).ne'
  simp [thetaMovingTailJetTerm, ha]

theorem norm_thetaMovingTailJetTerm_le (N j k : ℕ) (lambda : ℝ) :
    ‖thetaMovingTailJetTerm N j k lambda‖ ≤
      thetaMovingShellJetBound k * ((j : ℝ)+1)^2 *
        Real.exp (-Real.pi * (thetaMovingShellScale (N+j) - thetaMovingShellScale N)) := by
  have ha := thetaMovingShellScale_pos N
  have hb := thetaMovingShellScale_pos (N+j)
  have hc := thetaMovingShellJetBound_nonneg k
  have hratio : thetaMovingShellScale N / thetaMovingShellScale (N+j) ≤ 1 :=
    (div_le_one hb).mpr (thetaMovingShellScale_le_add N j)
  have hpow : (thetaMovingShellScale N / thetaMovingShellScale (N+j))^k ≤ 1 := by
    simpa using pow_le_pow_left₀ (by positivity :
      0 ≤ thetaMovingShellScale N / thetaMovingShellScale (N+j)) hratio k
  have hratio2 : thetaMovingShellScale (N+j) / thetaMovingShellScale N ≤ ((j : ℝ)+1)^2 :=
    (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using thetaMovingShellScale_add_le_mul N j)
  have hn := norm_thetaMovingShellGammaJet_le (N+j) k
    (lambda * thetaMovingShellScale N / thetaMovingShellScale (N+j))
  unfold thetaMovingTailJetTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.exp (-Real.pi * (thetaMovingShellScale (N+j) - thetaMovingShellScale N)) *
        (thetaMovingShellScale (N+j) / thetaMovingShellScale N)) * thetaMovingShellJetBound k := by
      have hp := mul_le_mul hpow hn (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
      have ht := mul_le_mul_of_nonneg_left hp (by positivity :
        0 ≤ Real.exp (-Real.pi * (thetaMovingShellScale (N+j) - thetaMovingShellScale N)) *
          (thetaMovingShellScale (N+j) / thetaMovingShellScale N))
      simpa only [one_mul, mul_assoc] using ht
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left hratio2
        (Real.exp_pos (-Real.pi * (thetaMovingShellScale (N+j)-thetaMovingShellScale N))).le
      have := mul_le_mul_of_nonneg_right ht hc
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this

theorem norm_thetaMovingTailJetTerm_le_gaussian (N j k : ℕ) (lambda : ℝ) :
    ‖thetaMovingTailJetTerm N j k lambda‖ ≤
      thetaMovingShellJetBound k * ((j : ℝ)+1)^2 * Real.exp (-Real.pi*(j : ℝ)^2) := by
  apply (norm_thetaMovingTailJetTerm_le N j k lambda).trans
  have hdelta : (j : ℝ)^2 ≤ thetaMovingShellScale (N+j) - thetaMovingShellScale N := by
    rw [thetaMovingShellScale_add_sub]
    have : 0 ≤ 2*((N : ℝ)+1)*(j : ℝ) := by positivity
    linarith
  have hc := thetaMovingShellJetBound_nonneg k
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos]

private theorem summable_tailMajorant (k : ℕ) :
    Summable (fun j : ℕ => thetaMovingShellJetBound k * ((j : ℝ)+1)^2 *
      Real.exp (-Real.pi*(j : ℝ)^2)) := by
  have h0 := summable_pow_mul_exp_neg_nat_sq 0 Real.pi_pos
  have h2 := summable_pow_mul_exp_neg_nat_sq 2 Real.pi_pos
  have hsum : Summable (fun j : ℕ => (2+2*(j : ℝ)^2) * Real.exp (-Real.pi*(j : ℝ)^2)) := by
    apply ((h0.mul_left 2).add (h2.mul_left 2)).congr
    intro j
    simp only [pow_zero, one_mul]
    ring
  have hsmall : Summable (fun j : ℕ => ((j : ℝ)+1)^2 * Real.exp (-Real.pi*(j : ℝ)^2)) := by
    apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hsum
    gcongr
    nlinarith [sq_nonneg ((j : ℝ)-1)]
  simpa only [mul_assoc] using hsmall.mul_left (thetaMovingShellJetBound k)

theorem summable_thetaMovingTailJetTerm (N k : ℕ) (lambda : ℝ) :
    Summable (fun j : ℕ => thetaMovingTailJetTerm N j k lambda) := by
  exact (summable_tailMajorant k).of_norm_bounded
    (fun j => norm_thetaMovingTailJetTerm_le_gaussian N j k lambda)

private theorem tendsto_later_tailTerm_zero {j : ℕ} (hj : 0 < j) (k : ℕ) (lambda : ℝ) :
    Tendsto (fun N => thetaMovingTailJetTerm N j k lambda) atTop (𝓝 0) := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hlin : Tendsto (fun N : ℕ => 2*((N : ℝ)+1)*(j : ℝ)) atTop atTop := by
    exact ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      (by positivity : (0 : ℝ) < 2)).atTop_mul_const hjR
  have hdelta : Tendsto (fun N => thetaMovingShellScale (N+j)-thetaMovingShellScale N)
      atTop atTop := by
    simpa only [thetaMovingShellScale_add_sub] using hlin.atTop_add tendsto_const_nhds
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hdelta.const_mul_atTop Real.pi_pos)
  have hbound := hexp.const_mul (thetaMovingShellJetBound k * ((j : ℝ)+1)^2)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using hbound)
  exact Eventually.of_forall (fun N => by
    simpa only [neg_mul] using norm_thetaMovingTailJetTerm_le N j k lambda)

/-- Complete tail: all later shells disappear, retaining the first omitted shell's jet. -/
theorem tendsto_thetaMovingTailJet (k : ℕ) (lambda : ℝ) :
    Tendsto (fun N => thetaMovingTailJet N k lambda) atTop
      (𝓝 (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
        ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1)))) := by
  let Z : ℂ := ((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
    ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1))
  have hpoint (j : ℕ) : Tendsto (fun N => thetaMovingTailJetTerm N j k lambda) atTop
      (𝓝 (if j = 0 then Z else 0)) := by
    cases j with
    | zero => simpa only [thetaMovingTailJetTerm_zero, ↓reduceIte, Z] using
        tendsto_thetaMovingShellGammaJet k lambda
    | succ j => simpa only [Nat.succ_ne_zero, if_false] using
        tendsto_later_tailTerm_zero (Nat.succ_pos j) k lambda
  have hlim := tendsto_tsum_of_dominated_convergence (summable_tailMajorant k) hpoint
    (Eventually.of_forall (fun N j => norm_thetaMovingTailJetTerm_le_gaussian N j k lambda))
  simpa only [thetaMovingTailJet, tsum_ite_eq, Z] using hlim

/-- Unconditional joint cutoff/height limit for every fixed literal tail jet. -/
theorem tendsto_normalized_thetaShellTailFrequencyJet (k : ℕ) (lambda : ℝ) :
    Tendsto (fun N =>
      ((Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
        thetaMovingShellScale N^k : ℝ) : ℂ) *
          thetaShellTailFrequencyJet N k (lambda * thetaMovingShellScale N)) atTop
      (𝓝 (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
        ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1)))) := by
  simpa only [thetaMovingTailJet_eq_normalized_shell_tsum] using
    tendsto_thetaMovingTailJet k lambda

end
end RHTower
