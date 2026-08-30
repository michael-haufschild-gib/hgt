import GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice

/-!
# Complete-source tail / Sonin phase work

The complete-resolution source exposes a signed tail orientation while the
cofinal Sonin construction exposes the two complex Hardy orientations.  This
module pairs those two *source-selected* odd quantities before either is
discarded.  The resulting current is reflection-even and has a literal
nonnegative closed form.  It is strictly positive precisely at an off-line
Xi-divisor copy.

The result closes one cross-route interface:

* `ORIENT`: the two reflected Sonin phases remain separate until the pairing;
* `COF + LAND`: one finite Sonin diagonal converges to the paired current;
* `COMP`: that same complete-source tail fixes every retained prime Bockstein
  parameter.

It does not assert the missing global bound or vanishing of this work.  Such
a statement remains RH-strength, so this file records the unconditional
source law rather than silently assuming its endpoint.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The even source work formed by pairing complete-resolution tail orientation
with the cofinal Sonin odd phase. -/
def sourceTailSoninPhaseWork (q : XiZeroCopy) : ℂ :=
  (I * ((Real.log 2 : ℝ) : ℂ) / 8) *
    (sourceZeroHorizontalTailLog q : ℂ) *
      xiZeroSoninCriticalPhaseOddFisherProfile q

/-- The source tail is the exact complete-resolution realization of the
horizontal rate used by the Sonin phase and every prime Bockstein. -/
theorem sourceZeroHorizontalTailLog_eq_neg_log_two_half_mul_rate
    (q : XiZeroCopy) :
    sourceZeroHorizontalTailLog q =
      -(Real.log 2 / 2) * primeDepthBVWoldXiCenteredRate q.1 := by
  rw [(completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog 0 q).2,
    primeDepthBVWoldXiCenteredRate]
  ring

/-- Exact closed form of the paired source current. -/
theorem sourceTailSoninPhaseWork_closedForm
    (q : XiZeroCopy) :
    sourceTailSoninPhaseWork q =
      ((Real.log 2 ^ 2 / 4 * primeDepthBVWoldXiCenteredRate q.1 ^ 2 *
        (1 - primeDepthBVWoldXiCenteredRate q.1 ^ 2) /
          (1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [sourceTailSoninPhaseWork,
    xiZeroSoninCriticalPhaseOddFisherProfile,
    sourceZeroHorizontalTailLog_eq_neg_log_two_half_mul_rate,
    soninCriticalPhaseOddFisherProfile]
  push_cast
  have hden : (1 + (primeDepthBVWoldXiCenteredRate q.1 : ℂ) ^ 2) ≠ 0 := by
    have hpos : 0 < 1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2 := by positivity
    exact_mod_cast hpos.ne'
  field_simp [hden]
  ring_nf
  simp [I_sq]
  ring

/-- Pairing the two odd source observables produces nonnegative even work
before target-side scalarization. -/
theorem sourceTailSoninPhaseWork_re_nonneg
    (q : XiZeroCopy) :
    0 ≤ (sourceTailSoninPhaseWork q).re := by
  rw [sourceTailSoninPhaseWork_closedForm]
  simp only [ofReal_re]
  have hstrip := sourceHorizontalXiCenteredRate_abs_lt_one q
  have hsq : primeDepthBVWoldXiCenteredRate q.1 ^ 2 < 1 := by
    have habsSq : |primeDepthBVWoldXiCenteredRate q.1| ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg _) zero_le_one).2 hstrip
    calc
      primeDepthBVWoldXiCenteredRate q.1 ^ 2 =
          |primeDepthBVWoldXiCenteredRate q.1| ^ 2 := (sq_abs _).symm
      _ < (1 : ℝ) ^ 2 := habsSq
      _ = 1 := by norm_num
  have hfac : 0 ≤ 1 - primeDepthBVWoldXiCenteredRate q.1 ^ 2 := by
    linarith
  have hden : 0 < (1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2) ^ 2 := by
    positivity
  exact div_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (sq_nonneg _)) hfac) hden.le

/-- The source work is strictly positive exactly at off-line Xi copies. -/
theorem sourceTailSoninPhaseWork_re_pos_iff
    (q : XiZeroCopy) :
    0 < (sourceTailSoninPhaseWork q).re ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [sourceTailSoninPhaseWork_closedForm]
  simp only [ofReal_re]
  let t := primeDepthBVWoldXiCenteredRate q.1
  have hstrip : |t| < 1 := by
    exact sourceHorizontalXiCenteredRate_abs_lt_one q
  have hfac : 0 < 1 - t ^ 2 := by
    have habsSq : |t| ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg _) zero_le_one).2 hstrip
    have hsq : t ^ 2 < 1 := by
      calc
        t ^ 2 = |t| ^ 2 := (sq_abs _).symm
        _ < (1 : ℝ) ^ 2 := habsSq
        _ = 1 := by norm_num
    linarith
  have hden : 0 < (1 + t ^ 2) ^ 2 := by positivity
  have hpos : 0 < Real.log 2 ^ 2 / 4 * t ^ 2 * (1 - t ^ 2) /
      (1 + t ^ 2) ^ 2 ↔ t ≠ 0 := by
    constructor
    · intro h ht
      simp [ht] at h
    · intro ht
      exact div_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_ne_zero ht)) hfac) hden
  simpa [t] using hpos.trans (not_congr (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1))

/-- The paired source work is reflection-even: both orientations have already
been retained, rather than recovered by target-side continuation. -/
theorem sourceTailSoninPhaseWork_reflection
    (q : XiZeroCopy) :
    sourceTailSoninPhaseWork (xiZeroCopyLineConjEquiv q) =
      sourceTailSoninPhaseWork q := by
  rw [sourceTailSoninPhaseWork,
    sourceTailSoninPhaseWork,
    sourceZeroHorizontalTailLog_reflection 0 q,
    xiZeroSoninCriticalPhaseOddFisherProfile,
    xiZeroSoninCriticalPhaseOddFisherProfile]
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) = _
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate]
  simp only [Complex.ofReal_neg]
  unfold soninCriticalPhaseOddFisherProfile
  ring_nf
  simp [I_sq]
  ring

/-- One cofinal finite Sonin schedule lands the two-orientation score on the
complete-source tail current, while the same tail fixes every literal
prime-Bockstein coefficient. -/
theorem exists_sourceTailSoninPhaseWork_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (q : XiZeroCopy) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      Tendsto (fun j =>
        (I * ((Real.log 2 : ℝ) : ℂ) / 8) *
          (sourceZeroHorizontalTailLog q : ℂ) *
          soninCofinalCriticalPhaseOddFisherScore a c d r hc hcd hr
            (primeDepthBVWoldXiCenteredRate q.1) j (Nseq j))
        atTop (nhds (sourceTailSoninPhaseWork q)) ∧
      (∀ p : Nat.Primes,
        sourceZeroHorizontalPrimeCarrier q p =
          primeGammaCofinalBocksteinCoefficient
            (-2 * sourceZeroHorizontalTailLog q / Real.log 2) p) := by
  obtain ⟨Nseq, hcofinal, hlimit, _hzero⟩ :=
    exists_xiZeroSoninCofinalCriticalPhaseOddFisherScore_diagonal
      a c d r ha hc hcd hda hr harc q
  refine ⟨Nseq, hcofinal, ?_, ?_⟩
  · have hconst : Tendsto (fun _ : ℕ =>
        (I * ((Real.log 2 : ℝ) : ℂ) / 8) *
          (sourceZeroHorizontalTailLog q : ℂ)) atTop
        (nhds ((I * ((Real.log 2 : ℝ) : ℂ) / 8) *
          (sourceZeroHorizontalTailLog q : ℂ))) := tendsto_const_nhds
    have hmul := hconst.mul hlimit
    simpa only [sourceTailSoninPhaseWork] using hmul
  · intro p
    exact sourceZeroHorizontalPrimeCarrier_eq_sourceTailBockstein 0 q p

end RHTower
