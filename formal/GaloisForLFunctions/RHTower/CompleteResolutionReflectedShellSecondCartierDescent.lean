import GaloisForLFunctions.RHTower.CompleteResolutionSecondCartierNormalOrder

/-!
# Reflected complete-shell descent to the literal second-Cartier endpoint

The complete Möbius resolution contains more than its singular normal reader.  Before taking the
normal limit, every prime has two independent prime-peeled adjacent shell transfers: one at `s`
and one at the functional-equation mate `1 - star s`.  This file retains both transfers as a
three-coordinate Krein jet.

The two transfers converge to `p^(1/2-s)` and its reciprocal-star.  Consequently the finite source
jet converges, coefficient for coefficient, to the literal second-Cartier polarized orbit.  This
constructs the missing pre-divisor representation without a finite measure, Toeplitz admission,
or scalar short.

The resulting order theorem is sharp.  A uniform cofinal energy budget for the finite shell jets
is equivalent to moderation of the literal endpoint.  On an actual strict-right Xi fibre the
finite source jets exhibit two-stage radial escape, while the exact support-fibre multiplicity sum
is unchanged.  Thus the remaining producer is no longer an unspecified decay estimate: it is a
completed Euler--Gamma budget for this explicit reflected-shell jet.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Non-scalar source jet retaining forward and reflected prime-peeled shell transports
independently before the cofinal normal limit. -/
def completeResolutionPrimePeeledReflectedSecondCartierJet
    (p : Nat.Primes) (K n : ℕ) (s c : ℂ) :
    SourceHorizontalSecondCartierKreinJet :=
  let a := normalizedPrimePeeledShellAdjacentTransfer p K s
  let b := normalizedPrimePeeledShellAdjacentTransfer p K (1 - star s)
  (a ^ n, c * b ^ n, c * b ^ n)

/-- Functional-equation reflection turns the limiting prime-normal character into the
reciprocal-star character. -/
theorem primePeeledNormalCharacter_reflection (p : Nat.Primes) (s : ℂ) :
    (p.1 : ℂ) ^ ((1 / 2 : ℂ) - (1 - star s)) =
      (star ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)))⁻¹ := by
  rw [star_natCast_cpow_commonTest p.1 _ p.2.ne_zero]
  rw [← Complex.cpow_neg]
  congr 1
  simp
  ring

/-- The reflected finite-shell transfer converges to the reciprocal-star orientation. -/
theorem tendsto_normalizedPrimePeeledShellAdjacentTransfer_reflection
    (p : Nat.Primes) {s : ℂ} (hs : s.re < 1) :
    Tendsto
      (fun K : ℕ => normalizedPrimePeeledShellAdjacentTransfer p K (1 - star s))
      atTop
      (nhds ((star ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)))⁻¹)) := by
  have hreflect : 0 < (1 - star s).re := by
    simp only [sub_re, one_re]
    rw [show (star s).re = s.re by simp]
    linarith
  rw [← primePeeledNormalCharacter_reflection]
  exact tendsto_normalizedPrimePeeledShellAdjacentTransfer p hreflect

/-- **Pre-divisor reflected-shell descent.** For every fixed orbit depth, the exact two-orientation
source jet converges to the literal second-Cartier polarized orbit with the coefficient `c`
unchanged. -/
theorem tendsto_completeResolutionPrimePeeledReflectedSecondCartierJet
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionPrimePeeledReflectedSecondCartierJet p K n s c)
      atTop
      (nhds (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
        ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c n)) := by
  have ha := tendsto_normalizedPrimePeeledShellAdjacentTransfer p hs0
  have hb := tendsto_normalizedPrimePeeledShellAdjacentTransfer_reflection p hs1
  have han := ha.pow n
  have hbn := hb.pow n
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have hcb := hc.mul hbn
  have hprod := han.prodMk (hcb.prodMk hcb)
  let lam : ℂ := (p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)
  have horbit :
      sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n =
        (lam ^ n, c * (star lam)⁻¹ ^ n, c * (star lam)⁻¹ ^ n) := by
    ext <;>
      simp [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit,
        sourceHorizontalSecondCartierKreinJetTransfer,
        sourceHorizontalSecondCartierKreinPolarizedGhost,
        sourceHorizontalSecondCartierKreinUnit,
        sourceHorizontalSecondCartierKreinGhost,
        sourceHorizontalSecondCartierKreinSourceTransfer] <;>
      ring
  rw [horbit]
  simpa [completeResolutionPrimePeeledReflectedSecondCartierJet, lam, nhds_prod_eq]
    using hprod

/-- Positive radial energy is continuous on the non-scalar Krein jet. -/
theorem continuous_sourceHorizontalSecondCartierKreinPositiveOrbitEnergy :
    Continuous sourceHorizontalSecondCartierKreinPositiveOrbitEnergy := by
  unfold sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
  fun_prop

/-- Radial energy of finite reflected-shell jets converges to the exact literal orbit energy. -/
theorem tendsto_completeResolutionPrimePeeledReflectedSecondCartierEnergy
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    Tendsto
      (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionPrimePeeledReflectedSecondCartierJet p K n s c))
      atTop
      (nhds (sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
          ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c n))) := by
  exact continuous_sourceHorizontalSecondCartierKreinPositiveOrbitEnergy.continuousAt.tendsto.comp
    (tendsto_completeResolutionPrimePeeledReflectedSecondCartierJet p hs0 hs1 n)

/-- Actual Xi specialization of the finite reflected-shell jet at prime two.  The physical
conormal coefficient is inserted before the cofinal shell limit. -/
def completeResolutionActualXiReflectedShellSecondCartierJet
    (K n : ℕ) (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    SourceHorizontalSecondCartierKreinJet :=
  completeResolutionPrimePeeledReflectedSecondCartierJet
    (default : Nat.Primes) K n (q.1.1 : ℂ)
      (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- **Coefficient-faithful actual landing.** At every fixed orbit depth, finite completed-source
energy converges to the already-constructed literal prime-two endpoint energy. -/
theorem tendsto_completeResolutionActualXiReflectedShellSecondCartierEnergy
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N n : ℕ) :
    Tendsto
      (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionActualXiReflectedShellSecondCartierJet K n x u q r N))
      atTop
      (nhds
        (‖bilateralEigenFamily
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
              (default : Nat.Primes)) (-(n : ℤ))‖ ^ (2 : ℕ) +
          4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
            (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost)
              (n : ℤ)‖ ^ (2 : ℕ))) := by
  have hs := xi_divisor_support_re_mem_open_unit q.1.1
  have h := tendsto_completeResolutionPrimePeeledReflectedSecondCartierEnergy
    (default : Nat.Primes) hs.1 hs.2 n
    (c := sourceHorizontalActualXiSecondCartierKreinScale x u q r N)
  have hlam :
      (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) := by
    simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
      bilateralHalfDensityCharacter]
  rw [hlam,
    sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy]
    at h
  exact h

/-- Concrete pre-divisor producer signature.  One constant bounds every orbit depth after passing
far enough into the exact completed-source shells; the shell threshold may depend on orbit depth,
but the energy constant may not. -/
def CompleteResolutionPrimePeeledReflectedSecondCartierCofinalBudget
    (p : Nat.Primes) (s c : ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ᶠ K : ℕ in atTop,
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (completeResolutionPrimePeeledReflectedSecondCartierJet p K n s c) ≤ C

/-- **Exact order descent.** A completed-source cofinal budget is equivalent to moderation of the
literal second-Cartier orbit.  This is unconditional and pre-divisor; it neither assumes nor hides
a post-selected finite measure. -/
theorem completeResolutionPrimePeeledReflectedSecondCartierCofinalBudget_iff
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    CompleteResolutionPrimePeeledReflectedSecondCartierCofinalBudget p s c ↔
      SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
        ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    exact le_of_tendsto
      (tendsto_completeResolutionPrimePeeledReflectedSecondCartierEnergy p hs0 hs1 n)
      (hC n)
  · rintro ⟨C, hC⟩
    refine ⟨C + 1, fun n => ?_⟩
    have hlim := tendsto_completeResolutionPrimePeeledReflectedSecondCartierEnergy
      p (c := c) hs0 hs1 n
    obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.1 hlim) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop K₀] with K hK
    have hnear := hK₀ K hK
    rw [Real.dist_eq] at hnear
    have hbound := hC n
    linarith [(abs_lt.mp hnear).2]

/-- Actual Xi instance of the pre-divisor cofinal source budget. -/
def CompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) : Prop :=
  CompleteResolutionPrimePeeledReflectedSecondCartierCofinalBudget
    (default : Nat.Primes) (q.1.1 : ℂ)
      (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- On an actual Xi fibre, the new source budget is exactly moderation of the literal non-spectral
endpoint, with the physical coefficient unchanged. -/
theorem completeResolutionActualXiReflectedShellSecondCartierCofinalBudget_iff_endpointModerate
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    CompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget x u q r N ↔
      bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
          (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost) := by
  have hs := xi_divisor_support_re_mem_open_unit q.1.1
  rw [CompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget,
    completeResolutionPrimePeeledReflectedSecondCartierCofinalBudget_iff
      (default : Nat.Primes) hs.1 hs.2]
  have hlam :
      (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) := by
    simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
      bilateralHalfDensityCharacter]
  rw [hlam]
  exact sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate
    q hkappa hr N hjet (default : Nat.Primes)

/-- A hypothetical strict-right Xi fibre already forces escape at finite source-shell stages: for
every requested energy, some physical orbit depth eventually exceeds it throughout the cofinal
shell tail. -/
theorem completeResolutionActualXiReflectedShellSecondCartier_twoStageEscape
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (B : ℝ) :
    ∃ n : ℕ, ∀ᶠ K : ℕ in atTop,
      B < sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionActualXiReflectedShellSecondCartierJet K n x u q r N) := by
  have hendpoint :=
    tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop
      q hkappa hr N hjet (default : Nat.Primes)
  obtain ⟨n, hn⟩ := (hendpoint.eventually_gt_atTop (B + 1)).exists
  rw [sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy]
    at hn
  have hlim :=
    tendsto_completeResolutionActualXiReflectedShellSecondCartierEnergy x u q r N n
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.1 hlim) 1 zero_lt_one
  refine ⟨n, ?_⟩
  filter_upwards [eventually_ge_atTop K₀] with K hK
  have hnear := hK₀ K hK
  rw [Real.dist_eq] at hnear
  linarith [(abs_lt.mp hnear).1]

/-- Universal actual-fibre cofinal budget. -/
def EveryCompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget
    (x u r : ℝ) (N : ℕ) : Prop :=
  ∀ q : XiRightZeroCopy,
    CompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget x u q r N

/-- Global classification of the explicit pre-divisor budget.  Proving it from an independent
completed Euler--Gamma order law is sufficient for RH, and no weaker post-selected admission is
being substituted. -/
theorem everyCompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget_iff_rh
    {x u r : ℝ}
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0) (N : ℕ)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    EveryCompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget x u r N ↔
      RiemannHypothesis := by
  rw [← everySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded_iff_rh
    hkappa hr N hjet (default : Nat.Primes)]
  constructor
  · intro h q
    have hs := xi_divisor_support_re_mem_open_unit q.1.1
    have hq :=
      (completeResolutionPrimePeeledReflectedSecondCartierCofinalBudget_iff
        (default : Nat.Primes) hs.1 hs.2).1 (h q)
    have hlam :
        (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
            (default : Nat.Primes) := by
      simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
        bilateralHalfDensityCharacter]
    rwa [hlam] at hq
  · intro h q
    have hs := xi_divisor_support_re_mem_open_unit q.1.1
    apply
      (completeResolutionPrimePeeledReflectedSecondCartierCofinalBudget_iff
        (default : Nat.Primes) hs.1 hs.2).2
    have hq := h q
    have hlam :
        (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
            (default : Nat.Primes) := by
      simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
        bilateralHalfDensityCharacter]
    rwa [hlam]

/-- **Coefficient-and-multiplicity capstone.** Finite completed-source energies converge to the
literal endpoint, every strict-right fibre escapes already at finite source stages, the cofinal
budget fails there, and the analytic support-fibre multiplicity remains the exact scalar sum of
the same physical Krein ghost. -/
theorem completeResolutionActualXiReflectedShellSecondCartier_capstone
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    (∀ n : ℕ,
      Tendsto
        (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
          (completeResolutionActualXiReflectedShellSecondCartierJet K n x u q r N))
        atTop
        (nhds
          (‖bilateralEigenFamily
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
                (default : Nat.Primes)) (-(n : ℤ))‖ ^ (2 : ℕ) +
            4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
              (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost)
                (n : ℤ)‖ ^ (2 : ℕ)))) ∧
      (∀ B : ℝ, ∃ n : ℕ, ∀ᶠ K : ℕ in atTop,
        B < sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
          (completeResolutionActualXiReflectedShellSecondCartierJet K n x u q r N)) ∧
      ¬ CompleteResolutionActualXiReflectedShellSecondCartierCofinalBudget x u q r N ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  refine ⟨tendsto_completeResolutionActualXiReflectedShellSecondCartierEnergy x u q r N,
    ?_, ?_,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum x u q r N⟩
  · exact completeResolutionActualXiReflectedShellSecondCartier_twoStageEscape
      x u q r N hkappa hr hjet
  · rw [completeResolutionActualXiReflectedShellSecondCartierCofinalBudget_iff_endpointModerate
      x u q r N hkappa hr hjet]
    exact not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
      q hkappa hr N hjet (default : Nat.Primes)

/-! ## Genuine consecutive-shell source evolution

The preceding frozen-shell power is a pointwise normal model, not completed source evolution.
Here orbit depth is the product of actual adjacent transfers at shells `K, ..., K+n-1`; no
transfer is repeated by an external clock.
-/

/-- Consecutive completed-source transport through `n` actual prime-peeled shell boundaries. -/
def completeResolutionPrimePeeledCumulativeShellTransfer
    (p : Nat.Primes) (K n : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n,
    normalizedPrimePeeledShellAdjacentTransfer p (K + j) s

@[simp] theorem completeResolutionPrimePeeledCumulativeShellTransfer_zero
    (p : Nat.Primes) (K : ℕ) (s : ℂ) :
    completeResolutionPrimePeeledCumulativeShellTransfer p K 0 s = 1 := by
  simp [completeResolutionPrimePeeledCumulativeShellTransfer]

/-- Successor depth is the next literal shell boundary, not a repeated frozen multiplier. -/
theorem completeResolutionPrimePeeledCumulativeShellTransfer_succ
    (p : Nat.Primes) (K n : ℕ) (s : ℂ) :
    completeResolutionPrimePeeledCumulativeShellTransfer p K (n + 1) s =
      completeResolutionPrimePeeledCumulativeShellTransfer p K n s *
        normalizedPrimePeeledShellAdjacentTransfer p (K + n) s := by
  simp [completeResolutionPrimePeeledCumulativeShellTransfer,
    Finset.prod_range_succ]

/-- Exact source telescoping law.  When the traversed shell residuals are nonzero, the genuine
consecutive transport is the half-density power times the terminal-to-initial residual ratio. -/
theorem completeResolutionPrimePeeledCumulativeShellTransfer_eq_residualRatio
    (p : Nat.Primes) (K n : ℕ) (s : ℂ)
    (hnz : ∀ j : ℕ, j ≤ n → primePeeledShellResidual p (K + j) s ≠ 0) :
    completeResolutionPrimePeeledCumulativeShellTransfer p K n s =
      ((p.1 : ℂ) ^ (1 / 2 : ℂ)) ^ n *
        primePeeledShellResidual p (K + n) s /
          primePeeledShellResidual p K s := by
  induction n with
  | zero =>
      rw [completeResolutionPrimePeeledCumulativeShellTransfer_zero]
      simp only [pow_zero, one_mul, Nat.add_zero]
      exact (div_self (hnz 0 (by omega))).symm
  | succ n ih =>
      have hnz' : ∀ j : ℕ, j ≤ n →
          primePeeledShellResidual p (K + j) s ≠ 0 :=
        fun j hj => hnz j (by omega)
      have hRn : primePeeledShellResidual p (K + n) s ≠ 0 := hnz n (by omega)
      have hR0 : primePeeledShellResidual p K s ≠ 0 := by
        simpa using hnz 0 (by omega)
      rw [completeResolutionPrimePeeledCumulativeShellTransfer_succ, ih hnz']
      rw [normalizedPrimePeeledShellAdjacentTransfer,
        primePeeledShellAdjacentTransfer]
      rw [pow_succ]
      field_simp [hRn, hR0]
      ring_nf

/-- A fixed finite run of consecutive shell boundaries converges to the corresponding power of
the prime-normal character. -/
theorem tendsto_completeResolutionPrimePeeledCumulativeShellTransfer
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionPrimePeeledCumulativeShellTransfer p K n s)
      atTop
      (nhds (((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hshift :=
        (tendsto_normalizedPrimePeeledShellAdjacentTransfer p hs).comp
          (tendsto_add_atTop_nat n)
      rw [show n + 1 = Nat.succ n by omega]
      simp_rw [completeResolutionPrimePeeledCumulativeShellTransfer_succ]
      simpa [pow_succ, Nat.add_comm] using ih.mul hshift

/-- Reflected consecutive evolution converges to the reciprocal-star endpoint leg. -/
theorem tendsto_completeResolutionPrimePeeledCumulativeShellTransfer_reflection
    (p : Nat.Primes) {s : ℂ} (hs : s.re < 1) (n : ℕ) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionPrimePeeledCumulativeShellTransfer p K n (1 - star s))
      atTop
      (nhds (((star ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)))⁻¹) ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hshift :=
        (tendsto_normalizedPrimePeeledShellAdjacentTransfer_reflection p hs).comp
          (tendsto_add_atTop_nat n)
      rw [show n + 1 = Nat.succ n by omega]
      simp_rw [completeResolutionPrimePeeledCumulativeShellTransfer_succ]
      simpa [pow_succ, Nat.add_comm] using ih.mul hshift

/-- Non-scalar two-orientation jet from one genuine consecutive completed-source run. -/
def completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
    (p : Nat.Primes) (K n : ℕ) (s c : ℂ) :
    SourceHorizontalSecondCartierKreinJet :=
  let a := completeResolutionPrimePeeledCumulativeShellTransfer p K n s
  let b := completeResolutionPrimePeeledCumulativeShellTransfer p K n (1 - star s)
  (a, c * b, c * b)

/-- **Source-natural pre-divisor descent.** Every fixed-length consecutive source run lands on the
literal coefficient-faithful second-Cartier orbit. -/
theorem tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet p K n s c)
      atTop
      (nhds (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
        ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c n)) := by
  have ha := tendsto_completeResolutionPrimePeeledCumulativeShellTransfer p hs0 n
  have hb :=
    tendsto_completeResolutionPrimePeeledCumulativeShellTransfer_reflection p hs1 n
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have hcb := hc.mul hb
  have hprod := ha.prodMk (hcb.prodMk hcb)
  let lam : ℂ := (p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)
  have horbit :
      sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n =
        (lam ^ n, c * (star lam)⁻¹ ^ n, c * (star lam)⁻¹ ^ n) := by
    ext <;>
      simp [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit,
        sourceHorizontalSecondCartierKreinJetTransfer,
        sourceHorizontalSecondCartierKreinPolarizedGhost,
        sourceHorizontalSecondCartierKreinUnit,
        sourceHorizontalSecondCartierKreinGhost,
        sourceHorizontalSecondCartierKreinSourceTransfer] <;>
      ring
  rw [horbit]
  simpa [completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet,
    lam, nhds_prod_eq] using hprod

/-- Positive energy of genuine source evolution converges to literal endpoint energy. -/
theorem tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierEnergy
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    Tendsto
      (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
          p K n s c))
      atTop
      (nhds (sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
          ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c n))) := by
  exact continuous_sourceHorizontalSecondCartierKreinPositiveOrbitEnergy.continuousAt.tendsto.comp
    (tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
      p hs0 hs1 n)

/-- Source-natural order signature: one constant controls every consecutive orbit length
cofinally in the starting shell. -/
def CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget
    (p : Nat.Primes) (s c : ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ᶠ K : ℕ in atTop,
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
        p K n s c) ≤ C

/-- Uniform completed-source order on genuine consecutive shell runs is exactly moderation of the
literal endpoint. -/
theorem completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
    (p : Nat.Primes) {s c : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget p s c ↔
      SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
        ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - s)) c := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    exact le_of_tendsto
      (tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierEnergy
        p hs0 hs1 n)
      (hC n)
  · rintro ⟨C, hC⟩
    refine ⟨C + 1, fun n => ?_⟩
    have hlim :=
      tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierEnergy
        p (c := c) hs0 hs1 n
    obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.1 hlim) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop K₀] with K hK
    have hnear := hK₀ K hK
    rw [Real.dist_eq] at hnear
    have hbound := hC n
    linarith [(abs_lt.mp hnear).2]

/-- Actual Xi specialization of genuine consecutive completed-source evolution. -/
def completeResolutionActualXiCumulativeReflectedSecondCartierJet
    (K n : ℕ) (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    SourceHorizontalSecondCartierKreinJet :=
  completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
    (default : Nat.Primes) K n (q.1.1 : ℂ)
      (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- Coefficient-faithful actual Xi landing for genuine source evolution. -/
theorem tendsto_completeResolutionActualXiCumulativeReflectedSecondCartierEnergy
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N n : ℕ) :
    Tendsto
      (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionActualXiCumulativeReflectedSecondCartierJet
          K n x u q r N))
      atTop
      (nhds
        (‖bilateralEigenFamily
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
              (default : Nat.Primes)) (-(n : ℤ))‖ ^ (2 : ℕ) +
          4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
            (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost)
              (n : ℤ)‖ ^ (2 : ℕ))) := by
  have hs := xi_divisor_support_re_mem_open_unit q.1.1
  have h := tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierEnergy
    (default : Nat.Primes) hs.1 hs.2 n
    (c := sourceHorizontalActualXiSecondCartierKreinScale x u q r N)
  have hlam :
      (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) := by
    simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
      bilateralHalfDensityCharacter]
  rw [hlam,
    sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy]
    at h
  exact h

/-- Actual Xi instance of the genuine consecutive-shell source budget. -/
def CompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) : Prop :=
  CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget
    (default : Nat.Primes) (q.1.1 : ℂ)
      (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- Actual genuine-source order is exactly literal endpoint moderation. -/
theorem completeResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget_iff_endpointModerate
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    CompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget x u q r N ↔
      bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
          (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost) := by
  have hs := xi_divisor_support_re_mem_open_unit q.1.1
  rw [CompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget,
    completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
      (default : Nat.Primes) hs.1 hs.2]
  have hlam :
      (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) := by
    simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
      bilateralHalfDensityCharacter]
  rw [hlam]
  exact sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate
    q hkappa hr N hjet (default : Nat.Primes)

/-- Strict-right escape already occurs along genuine finite consecutive source runs. -/
theorem completeResolutionActualXiCumulativeReflectedSecondCartier_twoStageEscape
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (B : ℝ) :
    ∃ n : ℕ, ∀ᶠ K : ℕ in atTop,
      B < sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (completeResolutionActualXiCumulativeReflectedSecondCartierJet
          K n x u q r N) := by
  have hendpoint :=
    tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop
      q hkappa hr N hjet (default : Nat.Primes)
  obtain ⟨n, hn⟩ := (hendpoint.eventually_gt_atTop (B + 1)).exists
  rw [sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy]
    at hn
  have hlim :=
    tendsto_completeResolutionActualXiCumulativeReflectedSecondCartierEnergy x u q r N n
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.1 hlim) 1 zero_lt_one
  refine ⟨n, ?_⟩
  filter_upwards [eventually_ge_atTop K₀] with K hK
  have hnear := hK₀ K hK
  rw [Real.dist_eq] at hnear
  linarith [(abs_lt.mp hnear).1]

/-- Universal actual-fibre budget for genuine completed-source evolution. -/
def EveryCompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget
    (x u r : ℝ) (N : ℕ) : Prop :=
  ∀ q : XiRightZeroCopy,
    CompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget x u q r N

/-- Global classification: uniform order of genuine consecutive source runs is exactly RH. -/
theorem everyCompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget_iff_rh
    {x u r : ℝ}
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0) (N : ℕ)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    EveryCompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget x u r N ↔
      RiemannHypothesis := by
  rw [← everySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded_iff_rh
    hkappa hr N hjet (default : Nat.Primes)]
  constructor
  · intro h q
    have hs := xi_divisor_support_re_mem_open_unit q.1.1
    have hq :=
      (completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
        (default : Nat.Primes) hs.1 hs.2).1 (h q)
    have hlam :
        (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
            (default : Nat.Primes) := by
      simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
        bilateralHalfDensityCharacter]
    rwa [hlam] at hq
  · intro h q
    have hs := xi_divisor_support_re_mem_open_unit q.1.1
    apply
      (completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
        (default : Nat.Primes) hs.1 hs.2).2
    have hq := h q
    have hlam :
        (((default : Nat.Primes).1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1.1 : ℂ))) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
            (default : Nat.Primes) := by
      simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
        bilateralHalfDensityCharacter]
    rwa [hlam]

/-- **Genuine-source capstone.** Consecutive completed shells preserve both orientations, physical
coefficient, and analytic multiplicity; strict-right copies escape and cannot satisfy one uniform
source-order budget. -/
theorem completeResolutionActualXiCumulativeReflectedSecondCartier_capstone
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    (∀ n : ℕ,
      Tendsto
        (fun K : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
          (completeResolutionActualXiCumulativeReflectedSecondCartierJet
            K n x u q r N))
        atTop
        (nhds
          (‖bilateralEigenFamily
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
                (default : Nat.Primes)) (-(n : ℤ))‖ ^ (2 : ℕ) +
            4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
              (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost)
                (n : ℤ)‖ ^ (2 : ℕ)))) ∧
      (∀ B : ℝ, ∃ n : ℕ, ∀ᶠ K : ℕ in atTop,
        B < sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
          (completeResolutionActualXiCumulativeReflectedSecondCartierJet
            K n x u q r N)) ∧
      ¬ CompleteResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget
        x u q r N ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  refine ⟨
    tendsto_completeResolutionActualXiCumulativeReflectedSecondCartierEnergy x u q r N,
    ?_, ?_,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum x u q r N⟩
  · exact completeResolutionActualXiCumulativeReflectedSecondCartier_twoStageEscape
      x u q r N hkappa hr hjet
  · rw [
      completeResolutionActualXiCumulativeReflectedSecondCartierCofinalBudget_iff_endpointModerate
        x u q r N hkappa hr hjet]
    exact not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
      q hkappa hr N hjet (default : Nat.Primes)

end

end RHTower
