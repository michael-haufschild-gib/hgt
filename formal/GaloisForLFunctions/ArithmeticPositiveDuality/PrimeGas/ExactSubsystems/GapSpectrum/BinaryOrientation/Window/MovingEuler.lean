import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Finite Euler products along a moving inverse temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Set Topology

private theorem smooth_sum (N : ℕ) {w : ℂ} (hw : 1 < w.re) :
    (∏ p ∈ N.primesLE, (1-(p:ℂ)^(-w))⁻¹) =
      ∑' n : ℕ, if n ∈ (N+1).smoothNumbers then (n:ℂ)^(-w) else 0 := by
  classical
  let f := (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hw)).toMonoidHom
  have hs : Summable f := (summable_riemannZetaSummand hw).of_norm
  have he := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hs (N+1)
  rw [tsum_subtype] at he
  refine he.trans (tsum_congr fun n => ?_)
  by_cases hn : n ∈ (N+1).smoothNumbers
  · rw [Set.indicator_of_mem hn,if_pos hn]
    rfl
  · rw [Set.indicator_of_notMem hn,if_neg hn]

/-- A moving cutoff and a moving inverse temperature may approach their limits together
anywhere in the trace half-plane. -/
theorem moving_euler_product {w : ℂ} (hw : 1 < w.re) {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesLE, (1-(p:ℂ)^(-z N))⁻¹) atTop (𝓝 (riemannZeta w)) := by
  classical
  obtain ⟨b,hb,hbw⟩ := exists_between hw
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hz
  have hgood : ∀ᶠ N in atTop, b < (z N).re := hre.eventually_const_lt hbw
  let f := fun (N n : ℕ) => if n ∈ (N+1).smoothNumbers then (n:ℂ)^(-z N) else 0
  have hlim (n : ℕ) : Tendsto (fun N => f N n) atTop (𝓝 ((n:ℂ)^(-w))) := by
    rcases eq_or_ne n 0 with rfl | hn
    · have hw0 := Complex.ne_zero_of_one_lt_re hw
      have hn (N : ℕ) : 0 ∉ (N+1).smoothNumbers := fun he => Nat.ne_zero_of_mem_smoothNumbers he rfl
      simp [f,hw0,hn]
    · have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
      have ht : Tendsto (fun N => (n:ℂ)^(-z N)) atTop (𝓝 ((n:ℂ)^(-w))) := by
        simp only [Complex.cpow_def_of_ne_zero hn']
        exact (Complex.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul hz.neg)
      apply ht.congr'
      filter_upwards [eventually_ge_atTop n] with N hN
      exact (if_pos (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn) (Nat.lt_succ_of_le hN))).symm
  have hbound : ∀ᶠ N in atTop, ∀ n, ‖f N n‖ ≤ (n:ℝ)^(-b) := by
    filter_upwards [hgood] with N hN n
    by_cases hm : n ∈ (N+1).smoothNumbers
    · have hn := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hm)
      rw [show f N n = (n:ℂ)^(-z N) from if_pos hm,← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (neg_le_neg hN.le)
    · rw [show f N n = 0 from if_neg hm,norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have H := tendsto_tsum_of_dominated_convergence
    (Real.summable_nat_rpow.mpr (by linarith only [hb] : -b < -1)) hlim hbound
  change Tendsto (fun N => ∑' n, f N n) atTop (𝓝 (∑' n : ℕ, (n:ℂ)^(-w))) at H
  have hsum : (∑' n : ℕ, (n:ℂ)^(-w)) = riemannZeta w := tsum_riemannZetaSummand hw
  rw [hsum] at H
  apply H.congr'
  filter_upwards [hgood] with N hN
  exact (smooth_sum N (hb.trans hN)).symm

#print axioms moving_euler_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
