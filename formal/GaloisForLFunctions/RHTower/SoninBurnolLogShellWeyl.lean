import GaloisForLFunctions.RHTower.SchattenApproximation
import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel

/-!
# The dilation commutator of the logarithmic shell channel

A position channel deserves the name *logarithm* only if conjugating it by the dilation by `r`
shifts it by the constant `log r`.  For the step channel on the geometric shell tower this holds
exactly, not approximately: the dilation carries each layer to the next, and the channel's value
jumps by exactly `log r` between consecutive layers.

Two edge terms survive, one at each end of the finite tower: the base layer contributes `log a`,
and the top layer has no successor inside the tower.  Between them, on the interior band, the
conjugated channel is the original channel minus the scalar `log r`.  This is the archimedean
generator relation `[log t, dilation] = log r · dilation` in exact finite form.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

theorem logShellRadius_succ (a r : ℝ) (k : ℕ) :
    logShellRadius a r (k + 1) = r * logShellRadius a r k := by
  unfold logShellRadius
  rw [pow_succ]
  ring

theorem log_logShellRadius_succ {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    Real.log (logShellRadius a r (k + 1)) =
      Real.log (logShellRadius a r k) + Real.log r := by
  rw [logShellRadius_succ, Real.log_mul (zero_lt_one.trans hr).ne'
    (logShellRadius_pos ha hr k).ne']
  ring

theorem logShellRadius_strictMono {a r : ℝ} (ha : 0 < a) (hr : 1 < r) {j k : ℕ}
    (hjk : j < k) : logShellRadius a r j < logShellRadius a r k :=
  lt_of_lt_of_le (logShellRadius_lt_succ ha hr j)
    (logShellRadius_mono ha hr (Nat.succ_le_of_lt hjk))

/-- The logarithmic shell channel translated one layer outward. -/
def shiftedLogShellChannel (a r : ℝ) (n : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ k ∈ Finset.range n,
    ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
        evenIndicatorCutoff (logShellRadius a r (k + 1)))

/-- **Exact dilation intertwining.**  Dilating by `r` carries the logarithmic shell channel to its
one-layer translate. -/
theorem evenDilationCLM_mul_evenLogShellChannel
    (a r : ℝ) (hr : 1 < r) (n : ℕ) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
        evenLogShellChannel a r n =
      shiftedLogShellChannel a r n *
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) := by
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  set U := evenDilationCLM r⁻¹ (inv_pos.mpr hrpos) with hU
  have hmove : ∀ C : ℝ, U * evenIndicatorCutoff C =
      evenIndicatorCutoff (r * C) * U := by
    intro C
    have h := evenDilationCLM_mul_evenIndicatorCutoff C r⁻¹ (inv_pos.mpr hrpos)
    rw [inv_inv] at h
    exact h
  unfold evenLogShellChannel shiftedLogShellChannel
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_even, smul_mul_even, mul_sub, sub_mul, hmove, hmove,
    ← logShellRadius_succ a r (k + 1), ← logShellRadius_succ a r k]

/-- The translated channel is the next channel with its two edge layers removed: the base layer
carries `log a`, and the interior band carries the constant `log r`. -/
theorem shiftedLogShellChannel_eq_sub_edges
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) :
    shiftedLogShellChannel a r n =
      evenLogShellChannel a r (n + 1) -
        ((Real.log a : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r 1) -
            evenIndicatorCutoff (logShellRadius a r 0)) -
        ((Real.log r : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r (n + 1)) -
            evenIndicatorCutoff (logShellRadius a r 1)) := by
  classical
  have hbase : Real.log (logShellRadius a r 0) = Real.log a := by
    simp [logShellRadius]
  have hpeel : evenLogShellChannel a r (n + 1) =
      (∑ k ∈ Finset.range n,
        ((Real.log (logShellRadius a r (k + 1)) : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
            evenIndicatorCutoff (logShellRadius a r (k + 1)))) +
        ((Real.log (logShellRadius a r 0) : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r 1) -
            evenIndicatorCutoff (logShellRadius a r 0)) := by
    unfold evenLogShellChannel
    exact Finset.sum_range_succ' _ n
  have hterm : ∀ k ∈ Finset.range n,
      ((Real.log (logShellRadius a r (k + 1)) : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
            evenIndicatorCutoff (logShellRadius a r (k + 1))) =
        ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
            (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
              evenIndicatorCutoff (logShellRadius a r (k + 1))) +
          ((Real.log r : ℝ) : ℂ) •
            (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
              evenIndicatorCutoff (logShellRadius a r (k + 1))) := by
    intro k _
    have hcoeff : ((Real.log (logShellRadius a r (k + 1)) : ℝ) : ℂ) =
        ((Real.log (logShellRadius a r k) : ℝ) : ℂ) + ((Real.log r : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, log_logShellRadius_succ ha hr k]
    rw [hcoeff]
    ext y
    simp [add_smul]
  have hsplit :
      (∑ k ∈ Finset.range n,
        ((Real.log (logShellRadius a r (k + 1)) : ℝ) : ℂ) •
          (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
            evenIndicatorCutoff (logShellRadius a r (k + 1)))) =
        shiftedLogShellChannel a r n +
          ((Real.log r : ℝ) : ℂ) •
            (∑ k ∈ Finset.range n,
              (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
                evenIndicatorCutoff (logShellRadius a r (k + 1)))) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.smul_sum]
    rfl
  have htel :
      (∑ k ∈ Finset.range n,
        (evenIndicatorCutoff (logShellRadius a r (k + 2)) -
          evenIndicatorCutoff (logShellRadius a r (k + 1)))) =
        evenIndicatorCutoff (logShellRadius a r (n + 1)) -
          evenIndicatorCutoff (logShellRadius a r 1) := by
    exact Finset.sum_range_sub
      (fun k => evenIndicatorCutoff (logShellRadius a r (k + 1))) n
  rw [hpeel, hsplit, htel, hbase]
  abel

/-- **Logarithmic Weyl relation.**  Conjugating the shell channel by the dilation by `r` returns
the next channel minus the base-layer term `log a` and minus the constant `log r` on the interior
band.  Up to the two edges of the finite tower, dilation shifts the channel by exactly `log r`:
the channel is a logarithm of the position, not merely a bounded operator with logarithmic
values. -/
theorem evenDilationCLM_mul_evenLogShellChannel_eq_shift
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
        evenLogShellChannel a r n =
      (evenLogShellChannel a r (n + 1) -
          ((Real.log a : ℝ) : ℂ) •
            (evenIndicatorCutoff (logShellRadius a r 1) -
              evenIndicatorCutoff (logShellRadius a r 0)) -
          ((Real.log r : ℝ) : ℂ) •
            (evenIndicatorCutoff (logShellRadius a r (n + 1)) -
              evenIndicatorCutoff (logShellRadius a r 1))) *
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) := by
  rw [evenDilationCLM_mul_evenLogShellChannel a r hr n,
    shiftedLogShellChannel_eq_sub_edges a r ha hr n]

/-- **Unit-base Weyl relation.**  At base aperture one the lower edge term disappears: dilation
conjugation subtracts exactly the constant `log r` on the interior band. -/
theorem evenDilationCLM_mul_evenLogShellChannel_one
    (r : ℝ) (hr : 1 < r) (n : ℕ) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
        evenLogShellChannel 1 r n =
      (evenLogShellChannel 1 r (n + 1) -
          ((Real.log r : ℝ) : ℂ) •
            (evenIndicatorCutoff (logShellRadius 1 r (n + 1)) -
              evenIndicatorCutoff (logShellRadius 1 r 1))) *
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) := by
  have h := evenDilationCLM_mul_evenLogShellChannel_eq_shift 1 r zero_lt_one hr n
  have hz : ((0 : ℂ)) • (evenIndicatorCutoff (logShellRadius 1 r 1) -
      evenIndicatorCutoff (logShellRadius 1 r 0)) = 0 := by
    ext y
    simp
  rw [Real.log_one, Complex.ofReal_zero, hz, sub_zero] at h
  exact h

end RHTower

namespace RHTower

open ContinuousLinearMap

/-! ## The dilation defect is not trace class -/

/-- Scaling by a nonzero constant cannot make a noncompact operator compact. -/
theorem not_isCompactOperator_smul {T : evenSubspace →L[ℂ] evenSubspace} {c : ℂ}
    (hc : c ≠ 0) (hT : ¬ IsCompactOperator T) : ¬ IsCompactOperator (c • T) := by
  intro hcpt
  apply hT
  have hinv : c⁻¹ • (c • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [← hinv]
  exact hcpt.smul c⁻¹

/-- **The archimedean defect is not a trace-class correction.**  The interior-band term produced by
one dilation step of the conductor is a nonzero multiple of a nondegenerate shell projection, hence
noncompact.  The scalar `log r` that dilation extracts from the conductor therefore sits on an
infinite-rank band: it cannot be read by the ordinary trace, and the archimedean finite part
requires the aperture-regularized reading rather than a trace-class counterterm. -/
theorem not_isCompactOperator_conductorDilationDefect
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) (hn : 0 < n) :
    ¬ IsCompactOperator (((Real.log r : ℝ) : ℂ) •
      (evenIndicatorCutoff (logShellRadius a r (n + 1)) -
        evenIndicatorCutoff (logShellRadius a r 1))) := by
  have hlogr : (0 : ℝ) < Real.log r := Real.log_pos hr
  have hc : ((Real.log r : ℝ) : ℂ) ≠ 0 := by
    simpa using hlogr.ne'
  refine not_isCompactOperator_smul hc ?_
  refine not_isCompactOperator_evenIndicatorShellDiff
    (logShellRadius a r 1) (logShellRadius a r (n + 1))
    (logShellRadius_pos ha hr 1) ?_
  exact logShellRadius_strictMono ha hr (Nat.succ_lt_succ hn)

/-- The dilation defect of the conductor is not Schatten-1. -/
theorem not_memSchattenClass_one_conductorDilationDefect
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) (hn : 0 < n) :
    ¬ MemSchattenClass 1 (((Real.log r : ℝ) : ℂ) •
      (evenIndicatorCutoff (logShellRadius a r (n + 1)) -
        evenIndicatorCutoff (logShellRadius a r 1))) := by
  intro hS
  exact not_isCompactOperator_conductorDilationDefect a r ha hr n hn
    (hS.isCompactOperator one_pos)

end RHTower
