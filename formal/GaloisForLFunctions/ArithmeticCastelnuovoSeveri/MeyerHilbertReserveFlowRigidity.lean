import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FaithfulHilbertSchmidtSourceReserves
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerCriticalTopAlgebra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FlowInvariantMeyerMajorantsForceCriticality

/-!
# The exact flow-invariance locus of the faithful Meyer reserve

Boundedness and invariance of the faithful source/sharp Hilbert–Schmidt reserve
have the same locus: critical highest jets. Invariance on every source is exactly
simple criticality and hence the Riemann–Roch condition for this reserve cone.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Arithmetic sharp reverses the existing centered source flow. -/
theorem meyerSourceSharp_centeredFlow (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (deningerMeyerStrongLogCenteredFlow c g) =
      deningerMeyerStrongLogCenteredFlow (-c) (deningerMeyerSourceSharp g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  dsimp only
  rw [deningerMeyerSourceSharp_mellin, meyerCenteredSourceFlow_mellin,
    meyerCenteredSourceFlow_mellin, deningerMeyerSourceSharp_mellin]
  have hh : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have he : conj ((c : ℂ) * (conj (1 - s) - 1 / 2)) =
      ((-c : ℝ) : ℂ) * (s - 1 / 2) := by
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj,
      Complex.ofReal_neg, hh]
    ring
  change conj (Complex.exp ((c : ℂ) * (conj (1 - s) - 1 / 2)) *
      deningerMeyerStrongLogMellin g (conj (1 - s))) = _
  rw [map_mul, ← Complex.exp_conj, he]

private theorem hsNormSq_centeredFlow_of_top (g : DeningerMeyerStrongLogTarget)
    (hg : MeyerCriticalTopJets g) (c : ℝ) :
    hsNormSq (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)) =
      hsNormSq (deningerMeyerHilbertConvolution g) := by
  have he := congrArg (fun r : ℝ => r ^ 2)
    (meyerHilbertOrbitIsometric_of_criticalTopJets hg c)
  have h1 := Real.sq_sqrt (hsNormSq_nonneg
    (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)))
  have h2 := Real.sq_sqrt (hsNormSq_nonneg (deningerMeyerHilbertConvolution g))
  exact h1.symm.trans (he.trans h2)

/-- The faithful reserve is constant on every bounded centered orbit. -/
theorem meyerHilbertReserve_centeredFlow_of_criticalTopJets
    (g : DeningerMeyerStrongLogTarget) (hg : MeyerCriticalTopJets g) (c : ℝ) :
    meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) =
      meyerHilbertReserve (0, 0, g) := by
  unfold meyerHilbertReserve
  dsimp only
  rw [meyerSourceSharp_centeredFlow, hsNormSq_centeredFlow_of_top g hg,
    hsNormSq_centeredFlow_of_top (deningerMeyerSourceSharp g) (meyerCriticalTopJets_sharp hg)]

/-- A bound for the faithful reserve bounds the entire convolution orbit. -/
theorem meyerHilbertOrbitBounded_of_reserve_bounded (g : DeningerMeyerStrongLogTarget)
    (h : ∃ C : ℝ, ∀ c : ℝ,
      meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) ≤ C) :
    MeyerHilbertOrbitBounded g := by
  obtain ⟨C, hC⟩ := h
  have hCn : 0 ≤ C := (meyerHilbertReserve_nonneg _).trans (hC 0)
  refine ⟨Real.sqrt (2 * C), fun c => ?_⟩
  have hb := hC c
  have hother := hsNormSq_nonneg
    (deningerMeyerHilbertConvolution
      (deningerMeyerSourceSharp (deningerMeyerStrongLogCenteredFlow c g)))
  change (hsNormSq (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)) +
    hsNormSq (deningerMeyerHilbertConvolution
      (deningerMeyerSourceSharp (deningerMeyerStrongLogCenteredFlow c g)))) / 2 ≤ C at hb
  have hroot := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCn)
  have hn := Real.sq_sqrt (hsNormSq_nonneg
    (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)))
  change hsNorm (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)) ^ 2 = _ at hn
  nlinarith only [hb, hother, hroot, hn, Real.sqrt_nonneg (2 * C),
    hsNorm_nonneg (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g))]

/-- Local reserve invariance is exactly the critical highest-jet condition. -/
theorem meyerHilbertReserve_invariant_iff_criticalTopJets (g : DeningerMeyerStrongLogTarget) :
    (∀ c : ℝ, meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) =
      meyerHilbertReserve (0, 0, g)) ↔ MeyerCriticalTopJets g := by
  constructor
  · intro h
    apply (meyerHilbertOrbitBounded_iff_criticalTopJets g).mp
    exact meyerHilbertOrbitBounded_of_reserve_bounded g
      ⟨meyerHilbertReserve (0, 0, g), fun c => (h c).le⟩
  · exact meyerHilbertReserve_centeredFlow_of_criticalTopJets g

/-- Finite boundedness of the reserve already forces its exact invariance. -/
theorem meyerHilbertReserve_bounded_iff_criticalTopJets (g : DeningerMeyerStrongLogTarget) :
    (∃ C : ℝ, ∀ c : ℝ,
      meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) ≤ C) ↔
      MeyerCriticalTopJets g := by
  constructor
  · intro h
    exact (meyerHilbertOrbitBounded_iff_criticalTopJets g).mp
      (meyerHilbertOrbitBounded_of_reserve_bounded g h)
  · intro h
    exact ⟨meyerHilbertReserve (0, 0, g),
      fun c => (meyerHilbertReserve_centeredFlow_of_criticalTopJets g h c).le⟩

/-- The faithful reserve is globally invariant exactly when all Xi points are simple and critical. -/
theorem all_meyerHilbertReserves_invariant_iff :
    (∀ (g : DeningerMeyerStrongLogTarget) (c : ℝ),
      meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) =
        meyerHilbertReserve (0, 0, g)) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  rw [← all_meyerHilbertOrbits_bounded_iff]
  constructor
  · intro h g
    exact (meyerHilbertOrbitBounded_iff_criticalTopJets g).mpr
      ((meyerHilbertReserve_invariant_iff_criticalTopJets g).mp (h g))
  · intro h g
    exact (meyerHilbertReserve_invariant_iff_criticalTopJets g).mpr
      ((meyerHilbertOrbitBounded_iff_criticalTopJets g).mp (h g))

/-- For this faithful cone, the RR obligation is precisely global reserve invariance. -/
theorem meyerHilbertSourceCone_riemannRoch_iff_reserve_invariant :
    meyerScalingSurface.RiemannRochAxiom meyerHilbertSourceCone ↔
      ∀ (g : DeningerMeyerStrongLogTarget) (c : ℝ),
        meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g) =
          meyerHilbertReserve (0, 0, g) :=
  meyerHilbertSourceCone_riemannRoch_iff.trans all_meyerHilbertReserves_invariant_iff.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSourceSharp_centeredFlow
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_centeredFlow_of_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertOrbitBounded_of_reserve_bounded
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_invariant_iff_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_bounded_iff_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.all_meyerHilbertReserves_invariant_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_riemannRoch_iff_reserve_invariant
