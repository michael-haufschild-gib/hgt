import GaloisForLFunctions.HTGeometry.L2DependentOperatorFamilyCrossDisjointness
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection

/-!
# JAS phase-twisted cross-sector superselection

Arbitrary countable families of prime-phase-twisted Poisson sectors cannot evade reflected
source-linear superselection off the critical wall. Every left phase sector is mutually singular
to every reflected right phase sector, and pairwise disjointness survives the dependent Hilbert
`ell²` sum where every coordinate has a different `L²` measure.

The critical positive survivor is sharp: two twisted critical sectors share a measure class exactly
when their relative phase cocycle has summable `p⁻¹`-weighted square defect. Divergent relative
phase defect produces mutually singular sectors.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Phase twists do not alter the radial square-summability threshold. -/
theorem summable_normSq_twistedPrimePoissonParameter_zero_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    Summable (fun p : Nat.Primes =>
      ‖((twistedPrimePoissonParameter sigma t hsigma chi p :
          CirclePoissonParameter) : ℂ) - 0‖ ^ 2) ↔
      1 / 2 < sigma := by
  rw [show (fun p : Nat.Primes =>
      ‖((twistedPrimePoissonParameter sigma t hsigma chi p :
          CirclePoissonParameter) : ℂ) - 0‖ ^ 2) =
      fun p : Nat.Primes =>
        ‖((primePoissonParameter sigma t hsigma p :
          CirclePoissonParameter) : ℂ) - 0‖ ^ 2 by
    funext p
    rw [sub_zero, sub_zero, coe_twistedPrimePoissonParameter,
      coe_primePoissonParameter, norm_mul, Circle.norm_coe, one_mul]]
  exact summable_normSq_primePoissonParameter_zero_iff sigma t hsigma

/-- Every twist lies in the Haar class exactly to the right of the wall. -/
theorem twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    ((twistedPrimePoissonMeasure sigma t hsigma chi ≪ torusHaar Nat.Primes) ∧
        torusHaar Nat.Primes ≪ twistedPrimePoissonMeasure sigma t hsigma chi) ↔
      1 / 2 < sigma := by
  rw [← torusPoissonMeasure_zero_eq_torusHaar Nat.Primes]
  rw [twistedPrimePoissonMeasure,
    torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
      (twistedPrimePoissonParameter sigma t hsigma chi)
      (fun _ : Nat.Primes => (0 : CirclePoissonParameter))
      (tendsto_twistedPrimePoissonParameter_natEquivPrimes_zero sigma t hsigma chi)
      tendsto_const_nhds]
  exact summable_normSq_twistedPrimePoissonParameter_zero_iff sigma t hsigma chi

/-- Every twist on or left of the wall is singular to Haar. -/
theorem twistedPrimePoissonMeasure_mutuallySingular_torusHaar_of_le_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hwall : sigma ≤ 1 / 2)
    (chi : Nat.Primes → Circle) :
    (twistedPrimePoissonMeasure sigma t hsigma chi).MutuallySingular
      (torusHaar Nat.Primes) := by
  rw [← torusPoissonMeasure_zero_eq_torusHaar Nat.Primes]
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  intro hsum
  have hright :=
    (summable_normSq_twistedPrimePoissonParameter_zero_iff sigma t hsigma chi).mp hsum
  exact (not_lt_of_ge hwall) hright

/-- Arbitrary left/right phase twists remain mutually singular off the reflected wall. -/
theorem twistedPrimePoissonMeasure_reflection_mutuallySingular_of_ne_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2)
    (chi psi : Nat.Primes → Circle) :
    (twistedPrimePoissonMeasure sigma t hsigma chi).MutuallySingular
      (twistedPrimePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1) psi) := by
  rcases lt_or_gt_of_ne hwall with hleft | hright
  · rcases twistedPrimePoissonMeasure_mutuallySingular_torusHaar_of_le_half
      sigma t hsigma hleft.le chi with ⟨s, hs, hmus, hhaar⟩
    have htarget :=
      (twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
        (1 - sigma) t (sub_pos.mpr hsigma1) psi).mpr (by linarith)
    exact ⟨s, hs, hmus, htarget.1 hhaar⟩
  · rcases twistedPrimePoissonMeasure_mutuallySingular_torusHaar_of_le_half
      (1 - sigma) t (sub_pos.mpr hsigma1) (by linarith) psi with
        ⟨s, hs, htarget, hhaar⟩
    have hsource :=
      (twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
        sigma t hsigma chi).mpr hright
    exact (show
      (twistedPrimePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1) psi).MutuallySingular
        (twistedPrimePoissonMeasure sigma t hsigma chi) from
      ⟨s, hs, htarget, hsource.1 hhaar⟩).symm

/-- Exact local displacement between two prime-phase twists. -/
theorem normSq_twistedPrimePoissonParameter_sub_twisted_eq
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi psi : Nat.Primes → Circle) (p : Nat.Primes) :
    ‖((twistedPrimePoissonParameter sigma t hsigma chi p :
        CirclePoissonParameter) : ℂ) -
      ((twistedPrimePoissonParameter sigma t hsigma psi p :
        CirclePoissonParameter) : ℂ)‖ ^ 2 =
      (p : ℝ) ^ (-2 * sigma) * ‖(chi p : ℂ) - (psi p : ℂ)‖ ^ 2 := by
  simp only [coe_twistedPrimePoissonParameter]
  rw [show (chi p : ℂ) * primePoissonParameterValue sigma t p -
      (psi p : ℂ) * primePoissonParameterValue sigma t p =
      ((chi p : ℂ) - (psi p : ℂ)) * primePoissonParameterValue sigma t p by ring,
    norm_mul, mul_pow, norm_primePoissonParameterValue]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hradial : Real.exp (-sigma * Real.log (p : ℝ)) ^ 2 =
      (p : ℝ) ^ (-2 * sigma) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [hradial]
  ring

/-- Exact two-twist Kakutani equivalence criterion. -/
theorem twistedPrimePoissonMeasure_pair_mutuallyAbsolutelyContinuous_iff
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi psi : Nat.Primes → Circle) :
    ((twistedPrimePoissonMeasure sigma t hsigma chi ≪
          twistedPrimePoissonMeasure sigma t hsigma psi) ∧
        twistedPrimePoissonMeasure sigma t hsigma psi ≪
          twistedPrimePoissonMeasure sigma t hsigma chi) ↔
      Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-2 * sigma) *
          ‖(chi p : ℂ) - (psi p : ℂ)‖ ^ 2) := by
  unfold twistedPrimePoissonMeasure
  rw [torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (twistedPrimePoissonParameter sigma t hsigma chi)
    (twistedPrimePoissonParameter sigma t hsigma psi)
    (tendsto_twistedPrimePoissonParameter_natEquivPrimes_zero sigma t hsigma chi)
    (tendsto_twistedPrimePoissonParameter_natEquivPrimes_zero sigma t hsigma psi)]
  apply summable_congr
  exact normSq_twistedPrimePoissonParameter_sub_twisted_eq
    sigma t hsigma chi psi

/-- Divergent relative phase defect gives mutually singular twisted sectors. -/
theorem twistedPrimePoissonMeasure_pair_mutuallySingular_of_not_summable
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi psi : Nat.Primes → Circle)
    (hdiv : ¬ Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-2 * sigma) *
        ‖(chi p : ℂ) - (psi p : ℂ)‖ ^ 2)) :
    (twistedPrimePoissonMeasure sigma t hsigma chi).MutuallySingular
      (twistedPrimePoissonMeasure sigma t hsigma psi) := by
  unfold twistedPrimePoissonMeasure
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  intro hsum
  apply hdiv
  exact hsum.congr fun p =>
    normSq_twistedPrimePoissonParameter_sub_twisted_eq
      sigma t hsigma chi psi p

/-- Sharp critical survivor: relative phase cocycles are admissible exactly in weighted `ell²`. -/
theorem twistedPrimePoissonMeasure_half_pair_mutuallyAbsolutelyContinuous_iff
    (t : ℝ) (chi psi : Nat.Primes → Circle) :
    ((twistedPrimePoissonMeasure (1 / 2) t (by norm_num) chi ≪
          twistedPrimePoissonMeasure (1 / 2) t (by norm_num) psi) ∧
        twistedPrimePoissonMeasure (1 / 2) t (by norm_num) psi ≪
          twistedPrimePoissonMeasure (1 / 2) t (by norm_num) chi) ↔
      Summable (fun p : Nat.Primes =>
        ‖(chi p : ℂ) - (psi p : ℂ)‖ ^ 2 / (p : ℝ)) := by
  rw [twistedPrimePoissonMeasure_pair_mutuallyAbsolutelyContinuous_iff]
  apply summable_congr
  intro p
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [show (-2 : ℝ) * (1 / 2) = -1 by ring, Real.rpow_neg_one]
  field_simp

/-- `L²` fibre of one phase-history channel. -/
abbrev TwistedPrimePoissonSectorL2
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi : ℕ → Nat.Primes → Circle) (n : ℕ) : Type :=
  Lp ℂ 2 (twistedPrimePoissonMeasure sigma t hsigma (chi n))

/-- Countable dependent sum of phase-history prime-Poisson multiplication representations. -/
def twistedPrimePoissonCrossSumMul
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi : ℕ → Nat.Primes → Circle) (f : C(PrimeTorus, ℂ)) :
    L2DependentSum ℕ (TwistedPrimePoissonSectorL2 sigma t hsigma chi) →L[ℂ]
      L2DependentSum ℕ (TwistedPrimePoissonSectorL2 sigma t hsigma chi) :=
  l2DependentDiagonal
    (fun n => continuousL2Mul
      (twistedPrimePoissonMeasure sigma t hsigma (chi n)) f)
    ‖f‖ (norm_nonneg f)
    (fun n => norm_continuousL2Mul_le
      (twistedPrimePoissonMeasure sigma t hsigma (chi n)) f)

/-- The countable phase-sector family remains star closed. -/
theorem adjoint_twistedPrimePoissonCrossSumMul
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (chi : ℕ → Nat.Primes → Circle) (f : C(PrimeTorus, ℂ)) :
    (twistedPrimePoissonCrossSumMul sigma t hsigma chi f).adjoint =
      twistedPrimePoissonCrossSumMul sigma t hsigma chi (star f) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  change inner ℂ
      (continuousL2Mul
        (twistedPrimePoissonMeasure sigma t hsigma (chi n)) (star f) (x n))
      (y n) =
    inner ℂ (x n)
      (continuousL2Mul
        (twistedPrimePoissonMeasure sigma t hsigma (chi n)) f (y n))
  rw [← adjoint_continuousL2Mul, ContinuousLinearMap.adjoint_inner_left]

/-- All countable phase-history channels remain jointly disjoint off wall. -/
theorem twistedPrimePoissonCrossSumMul_operatorFamiliesDisjoint_of_ne_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2)
    (chi psi : ℕ → Nat.Primes → Circle) :
    OperatorFamiliesDisjoint
      (twistedPrimePoissonCrossSumMul sigma t hsigma chi)
      (twistedPrimePoissonCrossSumMul
        (1 - sigma) t (sub_pos.mpr hsigma1) psi) := by
  unfold twistedPrimePoissonCrossSumMul
  exact operatorFamiliesDisjoint_l2DependentCrossSum
      (fun n f => continuousL2Mul
        (twistedPrimePoissonMeasure sigma t hsigma (chi n)) f)
      (fun m f => continuousL2Mul
        (twistedPrimePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1) (psi m)) f)
      (fun f : C(PrimeTorus, ℂ) => ‖f‖)
      (fun f => norm_nonneg f)
      (fun f n => norm_continuousL2Mul_le
        (twistedPrimePoissonMeasure sigma t hsigma (chi n)) f)
      (fun f m => norm_continuousL2Mul_le
        (twistedPrimePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1) (psi m)) f)
      (fun n m => continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular
        (twistedPrimePoissonMeasure_reflection_mutuallySingular_of_ne_half
          sigma t hsigma hsigma1 hwall (chi n) (psi m)))

/-- A nonzero closed source-linear sewing between arbitrary countable phase-history sums forces the
critical wall. Countable phase relabelling cannot be an off-wall JAS escape. -/
theorem twistedPrimePoissonCrossSumMul_nonzeroClosedSourceLinearSewing_forces_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (chi psi : ℕ → Nat.Primes → Circle) :
    NonzeroClosedSourceLinearSewing
      (twistedPrimePoissonCrossSumMul sigma t hsigma chi)
      (twistedPrimePoissonCrossSumMul
        (1 - sigma) t (sub_pos.mpr hsigma1) psi) →
      sigma = 1 / 2 := by
  intro hsew
  by_contra hwall
  rcases hsew with ⟨R, hclosed, hdense, hsingle, hinv, z, hz, hout⟩
  have hdisj := twistedPrimePoissonCrossSumMul_operatorFamiliesDisjoint_of_ne_half
    sigma t hsigma hsigma1 hwall chi psi
  have hinvAdj : ∀ f : C(PrimeTorus, ℂ), ∀ w, w ∈ R →
      hilbertBlockDiagonal
        (twistedPrimePoissonCrossSumMul sigma t hsigma chi f).adjoint
        (twistedPrimePoissonCrossSumMul
          (1 - sigma) t (sub_pos.mpr hsigma1) psi f).adjoint w ∈ R := by
    intro f w hw
    rw [adjoint_twistedPrimePoissonCrossSumMul,
      adjoint_twistedPrimePoissonCrossSumMul]
    exact hinv (star f) w hw
  exact hout ((closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint
    _ _ hdisj R hclosed hdense hsingle hinv hinvAdj z).mp hz)

end


end GaloisForLFunctions.HTGeometry
