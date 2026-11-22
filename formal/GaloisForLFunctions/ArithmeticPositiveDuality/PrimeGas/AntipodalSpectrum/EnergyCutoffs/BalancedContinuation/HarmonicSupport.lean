import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Vanishing tails of contracting finite differences

When every column of a forward difference array tends to zero down the
rows, an identically zero tail propagates backwards one column at a time.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

open Filter
open scoped Topology

/-- A rotated unit phase in a positive sector admits one strict contraction for the whole sector. -/
theorem unit_sector_contract {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : ‖z‖ = 1) (hr : c ≤ z.re) :
    ‖1-(c:ℂ)*z‖ ≤ Real.sqrt (1-c^2) := by
  have hu : z.re*z.re+z.im*z.im = 1 := by
    rw [← Complex.normSq_apply,Complex.normSq_eq_norm_sq,hz,one_pow]
  have h : ‖1-(c:ℂ)*z‖^2 ≤ 1-c^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,zero_sub]
    nlinarith only [congrArg (c^2*·) hu,mul_le_mul_of_nonneg_left hr hc.le]
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt h)

/-- Iterating the insertion 1−a u on normalized harmonic coefficients. -/
noncomputable def iterateMoments (a : ℂ) (R : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0,k => R k
  | m+1,k => iterateMoments a R m k-a*iterateMoments a R m (k+1)

theorem unbounded_of_decaying_columns (a : ℂ) (R : ℕ → ℂ)
    (hlim : ∀ k, Tendsto (fun m => ‖iterateMoments a R m k‖) atTop (𝓝 0)) :
    R 0 ≠ 0 → ∀ K, ∃ k ≥ K, R k ≠ 0 := by
  intro h₀ K
  by_contra! htail
  apply h₀
  revert htail
  induction K with
  | zero => exact fun h => h 0 le_rfl
  | succ K ih =>
    intro h
    have hall (m : ℕ) : ∀ k ≥ K+1, iterateMoments a R m k = 0 := by
      induction m with
      | zero => exact h
      | succ m hm =>
        intro k hk
        rw [iterateMoments,hm k hk,hm (k+1) (by omega),mul_zero,sub_zero]
    have hconst (m : ℕ) : iterateMoments a R m K = R K := by
      induction m with
      | zero => rfl
      | succ m hm => rw [iterateMoments,hm,hall m (K+1) le_rfl,mul_zero,sub_zero]
    have hv : Tendsto (fun _ : ℕ => ‖R K‖) atTop (𝓝 0) := by simpa only [hconst] using hlim K
    have hK : R K = 0 := norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hv)
    exact ih fun k hk => (eq_or_lt_of_le hk).elim (fun he => he ▸ hK) (fun hl => h k hl)

#print axioms unbounded_of_decaying_columns
#print axioms unit_sector_contract

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
