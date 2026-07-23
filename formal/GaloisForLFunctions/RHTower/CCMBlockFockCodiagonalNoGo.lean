import GaloisForLFunctions.RHTower.CCMFirstClockBlockSubdivisionTransfer
import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation

/-!
# The CCM block--Fock codiagonal has maximally multivalued closure

The odd block--Fock vector at a prime `p` has radial parameter `r = p⁻¹ᐟ²` and coordinates

`r^(2j+1/2) = p⁻¹ᐟ⁴ (p⁻¹)^j`.

It is therefore a nonzero scalar multiple of the reciprocal-prime Hardy coherent kernel already
carrying the arithmetic Gamma--valuation Schur system.  Removing degree one and shifting the
remaining grades `5,9,13,...` back by four multiplies this kernel by `p⁻¹`.  Its infinitesimal
logarithmic clock is consequently the order-one arithmetic-Schur trace clock, again with the same
nonzero scalar rescaling in both source and response columns.

The rescaling cannot repair the graph.  The exact block--Fock source/tail-clock graph is dense in
the whole product Hilbert space.  Hence every closed relation containing it contains every
vertical response, and no closed single-valued (even nonlinear) codiagonal can extend it.

This is unconditional.  It closes the singular block--Fock/LCM codiagonal proposed by the direct
CCM first-clock attack; it does not assert RH or exclude source transports outside this carrier.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Critical block radius `p⁻¹ᐟ²`, written without a fractional-power branch. -/
def ccmPrimeBlockRadius (p : Nat.Primes) : ℝ :=
  Real.sqrt (primeReciprocal p)

/-- Degree-one amplitude `p⁻¹ᐟ⁴` of the odd block--Fock vector. -/
def ccmPrimeOddBlockScale (p : Nat.Primes) : ℝ :=
  Real.sqrt (ccmPrimeBlockRadius p)

theorem ccmPrimeBlockRadius_pos (p : Nat.Primes) :
    0 < ccmPrimeBlockRadius p := by
  exact Real.sqrt_pos.2 (primeReciprocal_pos p)

theorem ccmPrimeBlockRadius_lt_one (p : Nat.Primes) :
    ccmPrimeBlockRadius p < 1 := by
  rw [ccmPrimeBlockRadius, Real.sqrt_lt' zero_lt_one]
  simpa using primeReciprocal_lt_one p

theorem ccmPrimeBlockRadius_sq (p : Nat.Primes) :
    ccmPrimeBlockRadius p ^ 2 = primeReciprocal p := by
  rw [ccmPrimeBlockRadius, Real.sq_sqrt (primeReciprocal_pos p).le]

theorem ccmPrimeOddBlockScale_pos (p : Nat.Primes) :
    0 < ccmPrimeOddBlockScale p := by
  exact Real.sqrt_pos.2 (ccmPrimeBlockRadius_pos p)

theorem ccmPrimeOddBlockScale_sq (p : Nat.Primes) :
    ccmPrimeOddBlockScale p ^ 2 = ccmPrimeBlockRadius p := by
  rw [ccmPrimeOddBlockScale, Real.sq_sqrt (ccmPrimeBlockRadius_pos p).le]

/-- Complete odd block--Fock vector `p⁻¹ᐟ⁴ (1,p⁻¹,p⁻²,...)`. -/
def ccmPrimeOddBlockFockVector (p : Nat.Primes) : PrimeHardy :=
  ccmPrimeOddBlockScale p • primeHardyKernel p

/-- Higher-grade tail after deleting degree one and shifting grades down by four. -/
def ccmPrimeOddBlockFockShiftedTail (p : Nat.Primes) : PrimeHardy :=
  ccmPrimeOddBlockScale p •
    (primeReciprocal p • primeHardyKernel p)

@[simp] theorem ccmPrimeOddBlockFockVector_apply
    (p : Nat.Primes) (j : ℕ) :
    ccmPrimeOddBlockFockVector p j =
      ccmPrimeOddBlockScale p * primeReciprocal p ^ j := by
  simp [ccmPrimeOddBlockFockVector, primeHardyKernel]

@[simp] theorem ccmPrimeOddBlockFockShiftedTail_apply
    (p : Nat.Primes) (j : ℕ) :
    ccmPrimeOddBlockFockShiftedTail p j =
      ccmPrimeOddBlockScale p * primeReciprocal p ^ (j + 1) := by
  change ccmPrimeOddBlockScale p *
      (primeReciprocal p * primeReciprocal p ^ j) =
    ccmPrimeOddBlockScale p * primeReciprocal p ^ (j + 1)
  rw [pow_succ]
  ring

/-- The Hilbert energy of the concrete prime vector is exactly the complete odd block--Fock
resolvent used by the CCM Gamma density. -/
theorem inner_ccmPrimeOddBlockFockVector_self
    (p : Nat.Primes) :
    inner ℝ (ccmPrimeOddBlockFockVector p)
        (ccmPrimeOddBlockFockVector p) =
      oddBlockFockRadialSum (ccmPrimeBlockRadius p) := by
  have hr0 : 0 ≤ ccmPrimeBlockRadius p :=
    (ccmPrimeBlockRadius_pos p).le
  have hr1 : ccmPrimeBlockRadius p < 1 :=
    ccmPrimeBlockRadius_lt_one p
  rw [oddBlockFockRadialSum_eq hr0 hr1]
  rw [ccmPrimeOddBlockFockVector, inner_smul_left, inner_smul_right,
    inner_primeHardyKernel]
  simp only [starRingEnd_apply, star_trivial]
  rw [← mul_assoc, ← pow_two, ccmPrimeOddBlockScale_sq]
  rw [← ccmPrimeBlockRadius_sq]
  ring

/-- The shifted higher-grade vector has exactly the odd block--Fock tail energy. -/
theorem inner_ccmPrimeOddBlockFockShiftedTail_self
    (p : Nat.Primes) :
    inner ℝ (ccmPrimeOddBlockFockShiftedTail p)
        (ccmPrimeOddBlockFockShiftedTail p) =
      oddBlockFockTail (ccmPrimeBlockRadius p) := by
  have hr0 : 0 ≤ ccmPrimeBlockRadius p :=
    (ccmPrimeBlockRadius_pos p).le
  have hr1 : ccmPrimeBlockRadius p < 1 :=
    ccmPrimeBlockRadius_lt_one p
  have hden : 1 - ccmPrimeBlockRadius p ^ 4 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr
      (pow_lt_one₀ hr0 hr1 (by omega)))
  rw [oddBlockFockTail, oddBlockFockRadialSum_eq hr0 hr1]
  rw [ccmPrimeOddBlockFockShiftedTail]
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [inner_primeHardyKernel]
  ring_nf
  rw [ccmPrimeOddBlockScale_sq]
  rw [← ccmPrimeBlockRadius_sq]
  field_simp [hden]
  ring

/-- Concrete Hilbert-space form of the universal block-shift defect: deleting degree one removes
exactly the critical radius `p⁻¹ᐟ²`. -/
theorem ccmPrimeOddBlockFock_energy_sub_shiftedTail
    (p : Nat.Primes) :
    inner ℝ (ccmPrimeOddBlockFockVector p)
        (ccmPrimeOddBlockFockVector p) -
      inner ℝ (ccmPrimeOddBlockFockShiftedTail p)
        (ccmPrimeOddBlockFockShiftedTail p) =
      ccmPrimeBlockRadius p := by
  rw [inner_ccmPrimeOddBlockFockVector_self,
    inner_ccmPrimeOddBlockFockShiftedTail_self,
    oddBlockFockRadialSum_sub_tail]

/-- Actual-prime block--Fock source column. -/
def ccmPrimeOddBlockFockSourceMap :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] PrimeHardy :=
  Finsupp.lsum ℝ (fun p =>
    LinearMap.toSpanSingleton ℝ _ (ccmPrimeOddBlockFockVector p))

/-- Infinitesimal log-clock on the shifted `5,9,13,...` block--Fock tail. -/
def ccmPrimeOddBlockFockTailClock :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] PrimeHardy :=
  Finsupp.lsum ℝ (fun p =>
    LinearMap.toSpanSingleton ℝ _
      (Real.log (p.1 : ℝ) • ccmPrimeOddBlockFockShiftedTail p))

@[simp] theorem ccmPrimeOddBlockFockSourceMap_single
    (p : Nat.Primes) (c : ℝ) :
    ccmPrimeOddBlockFockSourceMap (Finsupp.single p c) =
      c • ccmPrimeOddBlockFockVector p := by
  simp [ccmPrimeOddBlockFockSourceMap]

@[simp] theorem ccmPrimeOddBlockFockTailClock_single
    (p : Nat.Primes) (c : ℝ) :
    ccmPrimeOddBlockFockTailClock (Finsupp.single p c) =
      c • (Real.log (p.1 : ℝ) •
        ccmPrimeOddBlockFockShiftedTail p) := by
  simp [ccmPrimeOddBlockFockTailClock]

/-- **Block--Fock codiagonal saturation law.**  The exact actual-prime source and shifted-tail
log-clock graph is dense in the entire product Hilbert space.  The `p⁻¹ᐟ⁴` Fock normalization is
an invertible diagonal rescaling and therefore cannot change the order-one arithmetic-Schur graph
closure. -/
theorem ccmPrimeOddBlockFockTailClock_graphClosure_eq_top :
    (realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
      ccmPrimeOddBlockFockTailClock).topologicalClosure = ⊤ := by
  apply realLinearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y h
  apply primeTailLogRelation_eq_zero 1
  intro p
  have hp := h (Finsupp.single p 1)
  simp only [ccmPrimeOddBlockFockSourceMap_single,
    ccmPrimeOddBlockFockTailClock_single, one_smul,
    ccmPrimeOddBlockFockVector, ccmPrimeOddBlockFockShiftedTail,
    inner_smul_left] at hp
  have hfactor :
      ccmPrimeOddBlockScale p *
        (inner ℝ (primeHardyKernel p) x +
          (Real.log (p.1 : ℝ) * primeReciprocal p ^ 1) *
            inner ℝ (primeHardyKernel p) y) = 0 := by
    rw [pow_one]
    calc
      ccmPrimeOddBlockScale p *
          (inner ℝ (primeHardyKernel p) x +
            (Real.log (p.1 : ℝ) * primeReciprocal p) *
              inner ℝ (primeHardyKernel p) y) =
        ccmPrimeOddBlockScale p * inner ℝ (primeHardyKernel p) x +
          Real.log (p.1 : ℝ) *
            (ccmPrimeOddBlockScale p *
              (primeReciprocal p * inner ℝ (primeHardyKernel p) y)) := by ring
      _ = 0 := hp
  exact (mul_eq_zero.mp hfactor).resolve_left
    (ccmPrimeOddBlockScale_pos p).ne'

/-- Every closed linear relation extending the literal block--Fock source/tail clock contains
every vertical response. -/
theorem ccmPrimeOddBlockFock_closedRelationExtension_contains_vertical
    (G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)))
    (hGclosed : IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))))
    (hgraph :
      realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
        ccmPrimeOddBlockFockTailClock ≤ G)
    (y : PrimeHardy) :
    WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G := by
  have hclosure :
      ((realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
        ccmPrimeOddBlockFockTailClock).topologicalClosure :
          Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => hgraph hw) hGclosed
  apply hclosure
  rw [ccmPrimeOddBlockFockTailClock_graphClosure_eq_top]
  trivial

/-- No closed single-valued linear codiagonal can retain the exact block--Fock source/tail clock. -/
theorem ccmPrimeOddBlockFock_no_closed_singleValuedRelationExtension :
    ¬ ∃ G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) ∧
      realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
        ccmPrimeOddBlockFockTailClock ≤ G ∧
      ∀ y : PrimeHardy,
        WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G → y = 0 := by
  rintro ⟨G, hGclosed, hgraph, hsingle⟩
  have hvertical :=
    ccmPrimeOddBlockFock_closedRelationExtension_contains_vertical
      G hGclosed hgraph (lp.single 2 1 1)
  exact primeHardy_basisOne_ne_zero (hsingle _ hvertical)

/-- Strong set-theoretic form: even a nonlinear closed relation containing the exact algebraic
block--Fock graph cannot be single-valued. -/
theorem ccmPrimeOddBlockFock_no_closed_singleValuedRelation :
    ¬ ∃ G : Set (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed G ∧
      (realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
          ccmPrimeOddBlockFockTailClock :
        Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G ∧
      ∀ x y z : PrimeHardy,
        WithLp.toLp 2 (x, y) ∈ G →
        WithLp.toLp 2 (x, z) ∈ G →
        y = z := by
  rintro ⟨G, hGclosed, hgraph, hsingle⟩
  have hclosure :
      ((realLinearGraphSubmodule ccmPrimeOddBlockFockSourceMap
        ccmPrimeOddBlockFockTailClock).topologicalClosure :
          Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hgraph hGclosed
  have hzero :
      WithLp.toLp 2 ((0 : PrimeHardy), (0 : PrimeHardy)) ∈ G := by
    apply hclosure
    rw [ccmPrimeOddBlockFockTailClock_graphClosure_eq_top]
    trivial
  have hone :
      WithLp.toLp 2 ((0 : PrimeHardy), (lp.single 2 1 1 : PrimeHardy)) ∈ G := by
    apply hclosure
    rw [ccmPrimeOddBlockFockTailClock_graphClosure_eq_top]
    trivial
  exact primeHardy_basisOne_ne_zero
    (hsingle 0 0 (lp.single 2 1 1) hzero hone).symm

end

end RHTower
