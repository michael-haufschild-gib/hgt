import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualLaplaceRenormalization

/-!
# Source-horizontal neutral jet of the Route-T residual

The signed Gamma Bockstein is differentiated at neutral horizontal grade.  After one explicit
uniformly positive primewise gauge, its jet is exactly the depth-one Wold coefficient.  The
ordered logarithmic prime gap is likewise the neutral jet of the relative central holonomy of two
consecutive primes.  Their reflection-odd difference therefore has neutral jet equal to the full
Route-T residual increment.

The construction is pre-divisor.  Specializing its grade to an `XiZeroCopy` retains the divisor
multiplicity label and line-conjugate reflection.  No cofinal limit/derivative interchange or RH
statement is asserted.
-/

namespace RHTower

noncomputable section

/-- Uniform positive gauge transporting the neutral Gamma-Bockstein jet to the depth-one Wold
coefficient. -/
def sourceHorizontalWoldNeutralJetGauge (p : Nat.Primes) : ℝ :=
  (1 - 1 / (p : ℝ)) ^ 3 * ((p : ℝ) + 1) ^ 2 /
    (2 * (p : ℝ) ^ 2)

/-- The signed Gamma Bockstein has the prime-log generator as its first neutral jet. -/
theorem hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero
    (p : Nat.Primes) :
    HasDerivAt (fun t : ℝ => primeGammaCofinalBocksteinCoefficient t p)
      (-2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)) 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpos : HasDerivAt (fun t : ℝ => (p : ℝ) ^ t) (Real.log (p : ℝ)) 0 := by
    apply ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_rpow hp).congr_deriv
    simp
  have hneg : HasDerivAt (fun t : ℝ => (p : ℝ) ^ (-t)) (-Real.log (p : ℝ)) 0 := by
    have h := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg.const_rpow hp)
    convert h using 1 <;> simp
  have hraw :=
    (hneg.mul_const (primeActivationOccupancyFisherDensity p)).sub
      (hpos.mul_const (primeActivationOccupancyFisherDensity p))
  have hderiv :
      -Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p -
          Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p =
        -2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by
    ring
  rw [← hderiv]
  simpa [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist] using! hraw

/-- Exact coefficient-faithful bridge: the Wold coefficient is the negative neutral Bockstein
jet through one explicit primewise gauge. -/
theorem sourceHorizontalWoldNeutralJetGauge_mul_bocksteinJet
    (p : Nat.Primes) :
    sourceHorizontalWoldNeutralJetGauge p *
        (2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)) =
      woldCoeff 1 p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [sourceHorizontalWoldNeutralJetGauge,
    primeActivationOccupancyFisherDensity_eq, woldCoeff]
  simp only [pow_one]
  field_simp [hp]

/-- The bridge gauge is uniformly separated from zero and infinity.  Hence the R-to-T neutral
transport is boundedly coefficient-faithful, not compact smoothing. -/
theorem sourceHorizontalWoldNeutralJetGauge_bounds (p : Nat.Primes) :
    1 / 16 ≤ sourceHorizontalWoldNeutralJetGauge p ∧
      sourceHorizontalWoldNeutralJetGauge p ≤ 9 / 8 := by
  let P : ℝ := p
  have hP2 : 2 ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hP0 : 0 < P := by linarith
  have hfac := woldFactor_mem p
  have hratioLower : 1 ≤ (P + 1) ^ 2 / P ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hP0)]
    nlinarith
  have hratioUpper : (P + 1) ^ 2 / P ^ 2 ≤ 9 / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hP0)]
    nlinarith [sq_nonneg (P - 2)]
  change 1 / 16 ≤ (1 - 1 / P) ^ 3 * (P + 1) ^ 2 / (2 * P ^ 2) ∧
    (1 - 1 / P) ^ 3 * (P + 1) ^ 2 / (2 * P ^ 2) ≤ 9 / 8
  have hrewrite :
      (1 - 1 / P) ^ 3 * (P + 1) ^ 2 / (2 * P ^ 2) =
        (1 - 1 / P) ^ 3 * ((P + 1) ^ 2 / P ^ 2) / 2 := by
    field_simp [hP0.ne']
  rw [hrewrite]
  constructor
  · nlinarith [mul_le_mul hfac.1 hratioLower (by norm_num : 0 ≤ (1 : ℝ))
      (by linarith : 0 ≤ (1 - 1 / P) ^ 3)]
  · nlinarith [mul_le_mul hfac.2 hratioUpper
      (by positivity : 0 ≤ (P + 1) ^ 2 / P ^ 2)
      (by linarith : 0 ≤ (1 : ℝ))]

/-- Gauged Bockstein deformation whose neutral jet is the literal Wold coefficient. -/
def sourceHorizontalWoldPrimeDeformation (p : Nat.Primes) (t : ℝ) : ℝ :=
  -sourceHorizontalWoldNeutralJetGauge p *
    primeGammaCofinalBocksteinCoefficient t p

theorem hasDerivAt_sourceHorizontalWoldPrimeDeformation_zero
    (p : Nat.Primes) :
    HasDerivAt (sourceHorizontalWoldPrimeDeformation p) (woldCoeff 1 p) 0 := by
  have h := (hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero p).const_mul
    (-sourceHorizontalWoldNeutralJetGauge p)
  have hderiv :
      -sourceHorizontalWoldNeutralJetGauge p *
          (-2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)) =
        woldCoeff 1 p := by
    rw [← sourceHorizontalWoldNeutralJetGauge_mul_bocksteinJet]
    ring
  rw [← hderiv]
  simpa only [sourceHorizontalWoldPrimeDeformation] using! h

@[simp] theorem sourceHorizontalWoldPrimeDeformation_neg
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalWoldPrimeDeformation p (-t) =
      -sourceHorizontalWoldPrimeDeformation p t := by
  rw [sourceHorizontalWoldPrimeDeformation,
    sourceHorizontalWoldPrimeDeformation,
    primeGammaCofinalBocksteinCoefficient_neg]
  ring

/-- Reflection-odd relative holonomy of two consecutive ordered prime labels. -/
def sourceHorizontalAdjacentPrimeHolonomyDeformation (N : ℕ) (t : ℝ) : ℝ :=
  (((nthPrimeSubtype (N + 1) : ℝ) / (nthPrimeSubtype N : ℝ)) ^ t -
      ((nthPrimeSubtype (N + 1) : ℝ) / (nthPrimeSubtype N : ℝ)) ^ (-t)) / 2

@[simp] theorem sourceHorizontalAdjacentPrimeHolonomyDeformation_neg
    (N : ℕ) (t : ℝ) :
    sourceHorizontalAdjacentPrimeHolonomyDeformation N (-t) =
      -sourceHorizontalAdjacentPrimeHolonomyDeformation N t := by
  simp [sourceHorizontalAdjacentPrimeHolonomyDeformation]
  ring

/-- The adjacent-prime log mesh is exactly the neutral jet of relative holonomy. -/
theorem hasDerivAt_sourceHorizontalAdjacentPrimeHolonomyDeformation_zero
    (N : ℕ) :
    HasDerivAt (sourceHorizontalAdjacentPrimeHolonomyDeformation N)
      (xiMassNthPrimeLogHeight (N + 1) - xiMassNthPrimeLogHeight N) 0 := by
  let r : ℝ := (nthPrimeSubtype (N + 1) : ℝ) / (nthPrimeSubtype N : ℝ)
  have hpnext : 0 < (nthPrimeSubtype (N + 1) : ℝ) := by
    exact_mod_cast (nthPrimeSubtype (N + 1)).2.pos
  have hp : 0 < (nthPrimeSubtype N : ℝ) := by
    exact_mod_cast (nthPrimeSubtype N).2.pos
  have hr : 0 < r := by exact div_pos hpnext hp
  have hpos : HasDerivAt (fun t : ℝ => r ^ t) (Real.log r) 0 := by
    apply ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_rpow hr).congr_deriv
    simp
  have hneg : HasDerivAt (fun t : ℝ => r ^ (-t)) (-Real.log r) 0 := by
    have h := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg.const_rpow hr)
    convert h using 1 <;> simp
  have h := (hpos.sub hneg).div_const 2
  have hlog :
      (Real.log r - -Real.log r) / 2 =
        xiMassNthPrimeLogHeight (N + 1) - xiMassNthPrimeLogHeight N := by
    rw [xiMassNthPrimeLogHeight, xiMassNthPrimeLogHeight]
    dsimp only [r]
    rw [Real.log_div hpnext.ne' hp.ne']
    ring
  rw [← hlog]
  simpa only [sourceHorizontalAdjacentPrimeHolonomyDeformation, r,
    Pi.sub_apply] using! h

/-- Full reflection-odd source deformation for one Route-T residual increment. -/
def sourceHorizontalWoldResidualIncrementDeformation (N : ℕ) (t : ℝ) : ℝ :=
  sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype (N + 1)) t -
    sourceHorizontalAdjacentPrimeHolonomyDeformation N t

@[simp] theorem sourceHorizontalWoldResidualIncrementDeformation_neg
    (N : ℕ) (t : ℝ) :
    sourceHorizontalWoldResidualIncrementDeformation N (-t) =
      -sourceHorizontalWoldResidualIncrementDeformation N t := by
  rw [sourceHorizontalWoldResidualIncrementDeformation,
    sourceHorizontalWoldResidualIncrementDeformation,
    sourceHorizontalWoldPrimeDeformation_neg,
    sourceHorizontalAdjacentPrimeHolonomyDeformation_neg]
  ring

/-- **Frankenstein neutral-jet law.**  The complete Route-T residual increment, including its
ordered logarithmic mesh cocycle, is the first neutral jet of the source-horizontal deformation. -/
theorem hasDerivAt_sourceHorizontalWoldResidualIncrementDeformation_zero
    (N : ℕ) :
    HasDerivAt (sourceHorizontalWoldResidualIncrementDeformation N)
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) 0 := by
  have h :=
    (hasDerivAt_sourceHorizontalWoldPrimeDeformation_zero
      (nthPrimeSubtype (N + 1))).sub
      (hasDerivAt_sourceHorizontalAdjacentPrimeHolonomyDeformation_zero N)
  rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]
  exact h

/-- Multiplicity-exact Xi specialization of the pre-divisor deformation. -/
def sourceZeroHorizontalWoldResidualIncrementDeformation
    (q : XiZeroCopy) (N : ℕ) (u : ℝ) : ℝ :=
  sourceHorizontalWoldResidualIncrementDeformation N
    (u * primeDepthBVWoldXiCenteredRate q.1)

/-- The copy-labelled path retains both Xi reflection orientations by literal negation. -/
@[simp] theorem sourceZeroHorizontalWoldResidualIncrementDeformation_reflection
    (q : XiZeroCopy) (N : ℕ) (u : ℝ) :
    sourceZeroHorizontalWoldResidualIncrementDeformation
        (xiZeroCopyLineConjEquiv q) N u =
      -sourceZeroHorizontalWoldResidualIncrementDeformation q N u := by
  rw [sourceZeroHorizontalWoldResidualIncrementDeformation,
    sourceZeroHorizontalWoldResidualIncrementDeformation]
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate]
  simpa only [mul_neg] using
    sourceHorizontalWoldResidualIncrementDeformation_neg N
      (u * primeDepthBVWoldXiCenteredRate q.1)

/-- The neutral jet on each multiplicity-labelled Xi path is centered rate times the exact
Route-T residual increment. -/
theorem hasDerivAt_sourceZeroHorizontalWoldResidualIncrementDeformation_zero
    (q : XiZeroCopy) (N : ℕ) :
    HasDerivAt (sourceZeroHorizontalWoldResidualIncrementDeformation q N)
      (primeDepthBVWoldXiCenteredRate q.1 *
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N)) 0 := by
  have hinner : HasDerivAt
      (fun u : ℝ => u * primeDepthBVWoldXiCenteredRate q.1)
      (primeDepthBVWoldXiCenteredRate q.1) 0 := by
    simpa [mul_comm] using
      (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const
        (primeDepthBVWoldXiCenteredRate q.1)
  have houter : HasDerivAt (sourceHorizontalWoldResidualIncrementDeformation N)
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N)
      (0 * primeDepthBVWoldXiCenteredRate q.1) := by
    simpa using hasDerivAt_sourceHorizontalWoldResidualIncrementDeformation_zero N
  have hcomp := houter.scomp 0 hinner
  simpa [Function.comp, sourceZeroHorizontalWoldResidualIncrementDeformation,
    mul_comm] using! hcomp

end

end RHTower
