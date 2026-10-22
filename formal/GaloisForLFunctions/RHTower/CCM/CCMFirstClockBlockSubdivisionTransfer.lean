import GaloisForLFunctions.RHTower.CCM.CCMFirstClockHalfWaveReflection

/-!
# Ax+b block-subdivision realization of the CCM first clock

Multiplication by a positive integer sends one additive successor edge to a consecutive block of
fine successor edges.  Exact telescoping makes every multiplicative coboundary a joint eigenvector
of the normalized block averages.  The literal finite von Mangoldt sine clock is therefore the
imaginary part of one source-defined block-transfer coordinate.

This module is unconditional.  It constructs the non-diagonal source carrier needed by the direct
first-clock attack; it does not assert the remaining dissipativity inequality.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Additive successor coboundary of a scalar sequence. -/
def successorEdge (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  F (n + 1) - F n

/-- Sum a fine-edge sequence over the `q` consecutive edges above the coarse edge `n`. -/
def blockSubdivisionSum (q : ℕ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q, u (q * n + a)

/-- Critical square-root normalization of the block-subdivision sum. -/
def criticalBlockSubdivisionAverage (q : ℕ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((q : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * blockSubdivisionSum q u n

/-- Exact path subdivision: the fine successor edges telescope to the two coarse endpoints. -/
theorem blockSubdivisionSum_successorEdge
    (F : ℕ → ℂ) (q n : ℕ) :
    blockSubdivisionSum q (successorEdge F) n =
      F (q * (n + 1)) - F (q * n) := by
  simp only [blockSubdivisionSum, successorEdge]
  have htel := Finset.sum_range_sub (fun a : ℕ => F (q * n + a)) q
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htel

/-- Multiplicativity turns exact additive subdivision into a joint eigenvector law. -/
theorem criticalBlockSubdivisionAverage_successorEdge_of_multiplicative
    (F : ℕ → ℂ) (q n : ℕ)
    (hmul : ∀ a b : ℕ, F (a * b) = F a * F b) :
    criticalBlockSubdivisionAverage q (successorEdge F) n =
      (((q : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * F q * successorEdge F n := by
  rw [criticalBlockSubdivisionAverage, blockSubdivisionSum_successorEdge,
    hmul q (n + 1), hmul q n, successorEdge]
  ring_nf

/-- Multiplicative oscillatory phase, with the zero endpoint filled by zero. -/
def ccmBlockClockPhase (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else Complex.exp ((t * Real.log n : ℝ) * Complex.I)

theorem ccmBlockClockPhase_zero (t : ℝ) :
    ccmBlockClockPhase t 0 = 0 := by
  simp [ccmBlockClockPhase]

theorem ccmBlockClockPhase_of_pos
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ccmBlockClockPhase t n =
      Complex.exp ((t * Real.log n : ℝ) * Complex.I) := by
  simp [ccmBlockClockPhase, hn.ne']

/-- The distinguished additive-edge clock is a genuine multiplicative character away from its
zero endpoint. -/
theorem ccmBlockClockPhase_mul (t : ℝ) (a b : ℕ) :
    ccmBlockClockPhase t (a * b) =
      ccmBlockClockPhase t a * ccmBlockClockPhase t b := by
  by_cases ha : a = 0
  · simp [ha, ccmBlockClockPhase]
  by_cases hb : b = 0
  · simp [hb, ccmBlockClockPhase]
  have haPos : 0 < a := Nat.pos_of_ne_zero ha
  have hbPos : 0 < b := Nat.pos_of_ne_zero hb
  rw [ccmBlockClockPhase_of_pos t (Nat.mul_pos haPos hbPos),
    ccmBlockClockPhase_of_pos t haPos,
    ccmBlockClockPhase_of_pos t hbPos]
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), mul_add]
  push_cast
  rw [add_mul, Complex.exp_add]

/-- Full joint-eigenvector law for the physical logarithmic clock on every coarse edge. -/
theorem criticalBlockSubdivisionAverage_clockPhase
    (t : ℝ) (q n : ℕ) :
    criticalBlockSubdivisionAverage q
        (successorEdge (ccmBlockClockPhase t)) n =
      (((q : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        ccmBlockClockPhase t q *
          successorEdge (ccmBlockClockPhase t) n := by
  exact criticalBlockSubdivisionAverage_successorEdge_of_multiplicative
    (ccmBlockClockPhase t) q n (ccmBlockClockPhase_mul t)

/-- At the initial coarse edge, the normalized subdivision coordinate is the exact critical
Mellin character `q^(-1/2) exp(i t log q)`. -/
theorem criticalBlockSubdivisionAverage_clockPhase_zero
    (t : ℝ) {q : ℕ} (hq : 0 < q) :
    criticalBlockSubdivisionAverage q
        (successorEdge (ccmBlockClockPhase t)) 0 =
      (((q : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((t * Real.log q : ℝ) * Complex.I) := by
  rw [criticalBlockSubdivisionAverage, blockSubdivisionSum_successorEdge]
  simp [ccmBlockClockPhase_zero, ccmBlockClockPhase_of_pos t hq]

/-- Finite hard-aperture von Mangoldt transfer on the common block-subdivision carrier. -/
def ccmFirstClockPrimeBlockTransfer (L t : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    (ArithmeticFunction.vonMangoldt q : ℂ) *
      criticalBlockSubdivisionAverage q
        (successorEdge (ccmBlockClockPhase t)) 0

/-- The imaginary part of the block transfer is literally the published finite prime sine mass. -/
theorem ccmFirstClockPrimeBlockTransfer_im (L t : ℝ) :
    (ccmFirstClockPrimeBlockTransfer L t).im =
      ccmFirstClockPrimeSineMass L t := by
  rw [ccmFirstClockPrimeBlockTransfer, ccmFirstClockPrimeSineMass]
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := by
    exact lt_of_lt_of_le (by omega : 0 < 2) (Finset.mem_Icc.mp hq).1
  rw [criticalBlockSubdivisionAverage_clockPhase_zero t hqpos]
  rw [criticalMellinAtomWeight]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- Literal CCM source connector on the ax+b edge-subdivision carrier. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_budget_add_blockTransfer
    {L t : ℝ} (hL : 0 < L) (hperiod : t * L = 2 * Real.pi) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) t =
      ccmFirstClockContinuousHalfWaveBudget L t +
        (ccmFirstClockPrimeBlockTransfer L t).im := by
  rw [ccmFirstClockPrimeBlockTransfer_im]
  exact pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime hL hperiod

/-! ### The exact infinite Gamma carrier inside the block algebra -/

/-- Overlap of the two normalized initial block seeds.  Written as an intersection sum, this is
literally the scalar product of the vectors which are constant on `range m` and `range n`. -/
def criticalBlockSeedGram (m n : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range m ∩ Finset.range n,
    ((m : ℝ) ^ (-1 / 2 : ℝ)) * ((n : ℝ) ^ (-1 / 2 : ℝ))

theorem criticalBlockSeedGram_eq (m n : ℕ) :
    criticalBlockSeedGram m n =
      (min m n : ℝ) * ((m : ℝ) ^ (-1 / 2 : ℝ)) *
        ((n : ℝ) ^ (-1 / 2 : ℝ)) := by
  simp [criticalBlockSeedGram, Finset.sum_const, mul_assoc]

theorem criticalBlockSeedGram_comm (m n : ℕ) :
    criticalBlockSeedGram m n = criticalBlockSeedGram n m := by
  rw [criticalBlockSeedGram_eq, criticalBlockSeedGram_eq, min_comm]
  ring

/-- The normalized aligned-block overlap is the Ornstein--Uhlenbeck kernel in logarithmic scale. -/
theorem criticalBlockSeedGram_eq_exp_logGap_of_le
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    criticalBlockSeedGram m n =
      Real.exp (-|Real.log m - Real.log n| / 2) := by
  have hmR : 0 < (m : ℝ) := by positivity
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hlog : Real.log m ≤ Real.log n :=
    Real.strictMonoOn_log.monotoneOn hmR hnR hmnR
  rw [criticalBlockSeedGram_eq, min_eq_left hmnR,
    Real.rpow_def_of_pos hmR, Real.rpow_def_of_pos hnR,
    abs_of_nonpos (sub_nonpos.mpr hlog)]
  rw [show (m : ℝ) = Real.exp (Real.log m) by rw [Real.exp_log hmR],
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Real.log_exp]
  ring

theorem criticalBlockSeedGram_eq_exp_logGap
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalBlockSeedGram m n =
      Real.exp (-|Real.log m - Real.log n| / 2) := by
  rcases le_total m n with hmn | hnm
  · exact criticalBlockSeedGram_eq_exp_logGap_of_le hm hmn
  · rw [criticalBlockSeedGram_comm]
    rw [criticalBlockSeedGram_eq_exp_logGap_of_le hn hnm]
    congr 2
    rw [abs_sub_comm]

/-- Infinite direct sum of the tensor degrees `1,5,9,...` of one block-overlap coordinate. -/
def oddBlockFockRadialSum (r : ℝ) : ℝ :=
  ∑' j : ℕ, r ^ (4 * j + 1)

/-- Closed resolvent of the complete odd block-Fock ladder. -/
theorem oddBlockFockRadialSum_eq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    oddBlockFockRadialSum r = r / (1 - r ^ 4) := by
  rw [oddBlockFockRadialSum]
  have hpow0 : 0 ≤ r ^ 4 := pow_nonneg hr0 4
  have hpow1 : r ^ 4 < 1 :=
    pow_lt_one₀ hr0 hr1 (by omega)
  calc
    (∑' j : ℕ, r ^ (4 * j + 1)) =
        ∑' j : ℕ, r * (r ^ 4) ^ j := by
          apply tsum_congr
          intro j
          rw [pow_add, pow_mul]
          ring
    _ = r * ∑' j : ℕ, (r ^ 4) ^ j := by
          rw [tsum_mul_left]
    _ = r * (1 - r ^ 4)⁻¹ := by
          rw [tsum_geometric_of_lt_one hpow0 hpow1]
    _ = r / (1 - r ^ 4) := by rw [div_eq_mul_inv]

/-- The CCM archimedean density is exactly the complete odd block-Fock resolvent. -/
theorem oddBlockFockRadialSum_exp_eq_archimedeanDensity
    {h : ℝ} (hh : 0 < h) :
    oddBlockFockRadialSum (Real.exp (-h / 2)) =
      ccmPublishedArchimedeanDensity h := by
  have hr0 : 0 ≤ Real.exp (-h / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  rw [oddBlockFockRadialSum_eq hr0 hr1,
    ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hh]
  congr 2
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Remove the degree-one block sector from the complete `1 mod 4` Fock ladder. -/
def oddBlockFockTail (r : ℝ) : ℝ :=
  oddBlockFockRadialSum r - r

/-- The degree-one radial coordinate is exactly the defect between the full odd ladder and its
four-grade tail. -/
theorem oddBlockFockRadialSum_sub_tail (r : ℝ) :
    oddBlockFockRadialSum r - oddBlockFockTail r = r := by
  rw [oddBlockFockTail]
  ring

/-- Exact Gamma--polar grade fracture: polar completion cancels the degree-one decaying block
sector, leaving degrees `5,9,13,...` and one reversed growing boundary sector. -/
theorem continuousSourceDensity_eq_oddBlockFockTail_sub_polar
    {h : ℝ} (hh : 0 < h) :
    ccmFirstClockContinuousSourceDensity h =
      oddBlockFockTail (Real.exp (-h / 2)) -
        Real.exp (h / 2) := by
  rw [oddBlockFockTail, ccmFirstClockContinuousSourceDensity,
    oddBlockFockRadialSum_exp_eq_archimedeanDensity hh,
    Real.cosh_eq]
  ring_nf

/-- The reflected continuous budget consists exactly of the decreasing higher odd block-Fock
tail plus the reflected growing polar boundary. -/
theorem continuousReflectionGap_eq_blockFockTail_add_polarReflection
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    ccmFirstClockContinuousReflectionGap L h =
      (oddBlockFockTail (Real.exp (-h / 2)) -
        oddBlockFockTail (Real.exp (-(h + L / 2) / 2))) +
      (Real.exp ((h + L / 2) / 2) - Real.exp (h / 2)) := by
  rw [ccmFirstClockContinuousReflectionGap,
    continuousSourceDensity_eq_oddBlockFockTail_sub_polar hh,
    continuousSourceDensity_eq_oddBlockFockTail_sub_polar
      (by linarith : 0 < h + L / 2)]
  ring

/-- **Von Mangoldt block-Fock defect law.**  Every positive integer atom's critical Mellin radial
weight is its von Mangoldt mass times the universal degree-one defect of the Gamma block ladder. -/
theorem criticalMellinAtomWeight_eq_vonMangoldt_mul_oddBlockFockDefect
    (q : ℕ) :
    criticalMellinAtomWeight q =
      ArithmeticFunction.vonMangoldt q *
        (oddBlockFockRadialSum ((q : ℝ) ^ (-1 / 2 : ℝ)) -
          oddBlockFockTail ((q : ℝ) ^ (-1 / 2 : ℝ))) := by
  rw [criticalMellinAtomWeight, oddBlockFockRadialSum_sub_tail]
  ring

/-- The literal prime clock is the phase-weighted relative defect trace of the complete Gamma
block ladder against its four-grade tail. -/
theorem ccmFirstClockPrimeSineMass_eq_oddBlockFockDefectTrace
    (L ξ : ℝ) :
    ccmFirstClockPrimeSineMass L ξ =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ArithmeticFunction.vonMangoldt q *
          (oddBlockFockRadialSum ((q : ℝ) ^ (-1 / 2 : ℝ)) -
            oddBlockFockTail ((q : ℝ) ^ (-1 / 2 : ℝ))) *
          Real.sin (ξ * Real.log q) := by
  rw [ccmFirstClockPrimeSineMass]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [criticalMellinAtomWeight_eq_vonMangoldt_mul_oddBlockFockDefect]

/-- Exact published-source connector in the block-Fock relative-defect coordinates. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_budget_add_oddBlockFockDefectTrace
    {L ξ : ℝ} (hL : 0 < L) (hperiod : ξ * L = 2 * Real.pi) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) ξ =
      ccmFirstClockContinuousHalfWaveBudget L ξ +
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          ArithmeticFunction.vonMangoldt q *
            (oddBlockFockRadialSum ((q : ℝ) ^ (-1 / 2 : ℝ)) -
              oddBlockFockTail ((q : ℝ) ^ (-1 / 2 : ℝ))) *
            Real.sin (ξ * Real.log q) := by
  rw [← ccmFirstClockPrimeSineMass_eq_oddBlockFockDefectTrace]
  exact pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime hL hperiod

/-! ### Exact LCM meet of aligned block channels -/

/-- Adjacency characterization of sequences constant on every aligned block of length `q`.
The only adjacency at which a jump is permitted is a `q`-block boundary. -/
def IsAlignedBlockConstant {𝕂 : Type*} (q : ℕ) (u : ℕ → 𝕂) : Prop :=
  ∀ k : ℕ, ¬q ∣ k + 1 → u (k + 1) = u k

/-- Unnormalized aligned block replication; its range is unchanged by the critical nonzero
scalar normalization used by the Hilbert isometry `V_q=A_q^*`. -/
def alignedBlockReplication {𝕂 : Type*} (q : ℕ) (v : ℕ → 𝕂) (k : ℕ) : 𝕂 :=
  v (k / q)

theorem isAlignedBlockConstant_alignedBlockReplication
    {𝕂 : Type*} (q : ℕ) (v : ℕ → 𝕂) :
    IsAlignedBlockConstant q (alignedBlockReplication q v) := by
  intro k hk
  rw [alignedBlockReplication, alignedBlockReplication,
    Nat.succ_div_of_not_dvd hk]

/-- Exact range characterization of aligned block replication. -/
theorem isAlignedBlockConstant_iff_exists_alignedBlockReplication
    {𝕂 : Type*} {q : ℕ} (hq : 0 < q) (u : ℕ → 𝕂) :
    IsAlignedBlockConstant q u ↔
      ∃ v : ℕ → 𝕂, u = alignedBlockReplication q v := by
  constructor
  · intro h
    refine ⟨fun n => u (q * n), funext fun k => ?_⟩
    rw [alignedBlockReplication]
    have hwithin (n a : ℕ) (ha : a < q) :
        u (q * n + a) = u (q * n) := by
      induction a with
      | zero => simp
      | succ a ih =>
          have ha' : a < q := by omega
          have hnot : ¬q ∣ q * n + a + 1 := by
            intro hd
            have hsmall : q ∣ a + 1 :=
              (Nat.dvd_add_iff_right (Nat.dvd_mul_right q n)).mpr (by
                simpa [Nat.add_assoc] using hd)
            exact (Nat.not_dvd_of_pos_of_lt (by omega) ha) hsmall
          rw [show q * n + (a + 1) = (q * n + a) + 1 by omega,
            h (q * n + a) hnot, ih ha']
    have hmod : k % q < q := Nat.mod_lt k hq
    have hkdecomp : q * (k / q) + k % q = k :=
      Nat.div_add_mod k q
    calc
      u k = u (q * (k / q) + k % q) := congrArg u hkdecomp.symm
      _ = u (q * (k / q)) := hwithin (k / q) (k % q) hmod
  · rintro ⟨v, rfl⟩
    exact isAlignedBlockConstant_alignedBlockReplication q v

/-- **LCM block-meet law.**  Simultaneous `m`- and `n`-block constancy is exactly constancy on
aligned blocks of length `lcm m n`.  Thus the noncommuting block channels retain the causal LCM
ridge erased by scalar prime-face convolution. -/
theorem isAlignedBlockConstant_lcm_iff
    {𝕂 : Type*} (m n : ℕ) (u : ℕ → 𝕂) :
    IsAlignedBlockConstant (Nat.lcm m n) u ↔
      IsAlignedBlockConstant m u ∧ IsAlignedBlockConstant n u := by
  constructor
  · intro h
    constructor
    · intro k hmk
      apply h k
      intro hlcm
      exact hmk ((Nat.dvd_lcm_left m n).trans hlcm)
    · intro k hnk
      apply h k
      intro hlcm
      exact hnk ((Nat.dvd_lcm_right m n).trans hlcm)
  · rintro ⟨hm, hn⟩ k hlcm
    by_cases hmk : m ∣ k + 1
    · apply hn k
      intro hnk
      exact hlcm (Nat.lcm_dvd hmk hnk)
    · exact hm k hmk

/-- The literal range of the `lcm` block-replication channel is the intersection of the two
literal block-replication ranges. -/
theorem alignedBlockReplication_range_lcm_iff_inter
    {𝕂 : Type*} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (u : ℕ → 𝕂) :
    (∃ v : ℕ → 𝕂, u = alignedBlockReplication (Nat.lcm m n) v) ↔
      (∃ v : ℕ → 𝕂, u = alignedBlockReplication m v) ∧
      (∃ v : ℕ → 𝕂, u = alignedBlockReplication n v) := by
  have hlcm : 0 < Nat.lcm m n :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hm.ne' hn.ne')
  rw [← isAlignedBlockConstant_iff_exists_alignedBlockReplication hlcm,
    ← isAlignedBlockConstant_iff_exists_alignedBlockReplication hm,
    ← isAlignedBlockConstant_iff_exists_alignedBlockReplication hn,
    isAlignedBlockConstant_lcm_iff]

/-- Cofinal aligned block constancy has only the constant channel.  In particular, after passing
to `ℓ²(ℕ)`, the unrenormalized meet of all future block ranges is zero. -/
theorem isAlignedBlockConstant_all_ge_two_iff_constant
    {𝕂 : Type*} (u : ℕ → 𝕂) :
    (∀ q : ℕ, 2 ≤ q → IsAlignedBlockConstant q u) ↔
      ∀ k : ℕ, u k = u 0 := by
  constructor
  · intro h
    have hadj (k : ℕ) : u (k + 1) = u k := by
      apply h (k + 2) (by omega) k
      intro hdvd
      have hle : k + 2 ≤ k + 1 :=
        Nat.le_of_dvd (by omega : 0 < k + 1) hdvd
      omega
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [hadj k, ih]
  · intro h q _hq k _hboundary
    rw [h (k + 1), h k]

/-- Literal range form of the cofinal collapse: the common range of every future block
replication is exactly the constant channel. -/
theorem alignedBlockReplication_range_all_ge_two_iff_constant
    {𝕂 : Type*} (u : ℕ → 𝕂) :
    (∀ q : ℕ, 2 ≤ q →
      ∃ v : ℕ → 𝕂, u = alignedBlockReplication q v) ↔
      ∀ k : ℕ, u k = u 0 := by
  constructor
  · intro h
    apply (isAlignedBlockConstant_all_ge_two_iff_constant u).1
    intro q hq
    exact (isAlignedBlockConstant_iff_exists_alignedBlockReplication
      (lt_of_lt_of_le (by omega : 0 < 2) hq) u).2 (h q hq)
  · intro h q hq
    apply (isAlignedBlockConstant_iff_exists_alignedBlockReplication
      (lt_of_lt_of_le (by omega : 0 < 2) hq) u).1
    exact (isAlignedBlockConstant_all_ge_two_iff_constant u).2 h q hq

/-- **Block--Gamma sewing law.**  At every two distinct positive block scales, the complete
odd tensor ladder of their normalized seed overlap is literally the published CCM Gamma density
at their logarithmic separation. -/
theorem oddBlockFock_of_seedGram_eq_archimedeanDensity
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hlog : Real.log m ≠ Real.log n) :
    oddBlockFockRadialSum (criticalBlockSeedGram m n) =
      ccmPublishedArchimedeanDensity |Real.log m - Real.log n| := by
  rw [criticalBlockSeedGram_eq_exp_logGap hm hn]
  exact oddBlockFockRadialSum_exp_eq_archimedeanDensity
    (abs_pos.mpr (sub_ne_zero.mpr hlog))

end

end RHTower
