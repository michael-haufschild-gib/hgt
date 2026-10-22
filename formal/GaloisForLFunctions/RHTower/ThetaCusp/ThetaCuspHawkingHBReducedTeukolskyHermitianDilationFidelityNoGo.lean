import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingReducedSecondOrderChiralTeukolskyGradeIncidence
import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction

/-!
# Hermitian dilation cannot faithfully erase reduced Teukolsky angular leakage

The exact reduced second-order chiral Teukolsky source admits an unconditional conservative
completion.  Put its same-grade coefficient `c(q)` into the rank-one modal kernel

`K(q) = c(q) e_00`

and take the standard chiral dilation `D(K) = [[0,K],[Kᴴ,0]]`.  The result is Hilbert--Schmidt,
self-adjoint, finitely supported over the same modal cell, and coefficient-faithful in its positive
chiral block.  Thus abstract Hermiticity, modal locality, Hilbert--Schmidt regularity, and exact
source-block recovery cannot forbid the angular leakage already forced at tilted Xi fibres.

There is a sharp obstruction to turning this completion into an RH proof.  Hermitian dilation
replaces the holomorphic square trace by positive Gram energy.  For the actual Teukolsky source,
equality of the original and dilated Hilbert--Carleman determinants holds exactly when the source
vanishes, hence exactly on the critical line.  Globally, determinant fidelity on every Xi fibre is
equivalent to RH.  Every fibre also carries the quantitative second-jet mismatch floor

`‖c(q)‖² / 2`.

This kills multi-sector Hermitianization as a non-circular producer for HB and its shared FZZ-P,
PW-B, and RBH Ward endpoint.  A surviving angular law must use genuine differential/elliptic
domain or boundary geometry to forbid doubled chirality; the abstract conservative properties
proved here are insufficient.

`[NEW] [HB ROUTE KILL] [TEUKOLSKY] [HERMITIAN DILATION] [DETERMINANT FIDELITY]
[QUADRATIC JET] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

/-- Exact reduced same-grade Teukolsky coefficient placed in the chiral source kernel. -/
def d4HBReducedTeukolskyHermitianDilationSourceCoefficient
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) : ℂ :=
  d4ThetaReducedSecondOrderChiralTeukolskyGradeSource amplitude mixed anti q
    (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q))

/-- Rank-one modal kernel carrying the exact reduced source coefficient. -/
def d4HBReducedTeukolskyHermitianDilationSourceKernel
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) : ℕ × ℕ → ℂ :=
  diagKernel 0
    (d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q)

/-- The source occupies one modal cell. -/
def d4HBReducedTeukolskyHermitianDilationSourceSupport : Finset ℕ := {0}

/-- Chiral doubling changes only the chirality label of the occupied modal cell. -/
def d4HBReducedTeukolskyHermitianDilationSupport : Finset (ℕ ⊕ ℕ) :=
  d4HBReducedTeukolskyHermitianDilationSourceSupport.disjSum
    d4HBReducedTeukolskyHermitianDilationSourceSupport

/-- The exact rank-one Teukolsky source kernel is Hilbert--Schmidt. -/
theorem d4HBReducedTeukolskyHermitianDilationSourceKernel_isHS
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    IsHS (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) := by
  exact isHS_diagKernel 0 _

/-- The source kernel has support in its single declared modal cell. -/
theorem d4HBReducedTeukolskyHermitianDilationSourceKernel_support
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    ∀ p, p ∉ d4HBReducedTeukolskyHermitianDilationSourceSupport ×ˢ
          d4HBReducedTeukolskyHermitianDilationSourceSupport →
      d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q p = 0 := by
  intro p hp
  simp only [d4HBReducedTeukolskyHermitianDilationSourceKernel, diagKernel]
  rw [if_neg]
  intro h
  apply hp
  subst p
  simp [d4HBReducedTeukolskyHermitianDilationSourceSupport]

/-- Hermitian dilation preserves modal support and only doubles its chirality label. -/
theorem d4HBReducedTeukolskyHermitianDilation_support
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    ∀ p, p ∉ d4HBReducedTeukolskyHermitianDilationSupport ×ˢ
          d4HBReducedTeukolskyHermitianDilationSupport →
      sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) p = 0 := by
  exact sourceHermitianDilationKernel_support
    (d4HBReducedTeukolskyHermitianDilationSourceKernel_support amplitude mixed anti q)

/-- The doubled reduced-source carrier is self-adjoint on every Xi fibre. -/
theorem d4HBReducedTeukolskyHermitianDilation_isSelfAdjoint
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    hsAdjoint (sourceHermitianDilationKernel
        (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
      sourceHermitianDilationKernel
        (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) := by
  exact hsAdjoint_sourceHermitianDilationKernel _

/-- Exact coefficient faithfulness: the positive-to-negative chiral entry is the physical reduced
Teukolsky source coefficient, with no scalar gauge. -/
theorem d4HBReducedTeukolskyHermitianDilation_sourceBlock
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    sourceHermitianDilationKernel
        (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)
        (Sum.inl 0, Sum.inr 0) =
      d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q := by
  simp [sourceHermitianDilationKernel,
    d4HBReducedTeukolskyHermitianDilationSourceKernel, diagKernel]

/-- The dilated determinant equals the original source determinant exactly when the physical source
coefficient vanishes. -/
theorem d4HBReducedTeukolskyHermitianDilation_det_eq_iff_source_eq_zero
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    entireDet2 (sourceHermitianDilationKernel
        (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
        entireDet2
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) ↔
      d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q = 0 := by
  rw [entireDet2_sourceHermitianDilationKernel_eq_iff
    (d4HBReducedTeukolskyHermitianDilationSourceKernel_isHS amplitude mixed anti q)]
  constructor
  · intro h
    have h00 := congrFun h (0, 0)
    simpa [d4HBReducedTeukolskyHermitianDilationSourceKernel, diagKernel] using h00
  · intro h
    funext p
    simp [d4HBReducedTeukolskyHermitianDilationSourceKernel, diagKernel, h]

/-- For a nonzero Einstein seed, determinant fidelity of the Hermitian completion occurs exactly on
the critical line. -/
theorem d4HBReducedTeukolskyHermitianDilation_det_eq_iff_re_eq_half
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ) (q : XiZeroCopy) :
    entireDet2 (sourceHermitianDilationKernel
        (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
        entireDet2
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4HBReducedTeukolskyHermitianDilation_det_eq_iff_source_eq_zero]
  have h := not_congr
    (d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
      ha mixed anti 0 q)
  simpa [d4HBReducedTeukolskyHermitianDilationSourceCoefficient] using h

/-- Quantitative survivor: Hermitianization pays at least half the exact source energy in the
quadratic determinant jet. -/
theorem d4HBReducedTeukolskyHermitianDilation_quadraticJetGap
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    ‖d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q‖ ^ (2 : ℕ) / 2 ≤
      ‖taylorCoeff
          (entireDet2 (sourceHermitianDilationKernel
            (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q))) 2 -
        taylorCoeff
          (entireDet2
            (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) 2‖ := by
  have h := half_hsNormSq_le_norm_taylorCoeff_dilation_sub
    (d4HBReducedTeukolskyHermitianDilationSourceKernel_isHS amplitude mixed anti q)
  simpa [d4HBReducedTeukolskyHermitianDilationSourceKernel,
    hsNormSq_diagKernel] using h

/-- Universal determinant fidelity of the self-adjoint reduced-source completion is RH itself. -/
theorem forall_d4HBReducedTeukolskyHermitianDilation_det_eq_iff_rh
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ) :
    (∀ q : XiZeroCopy,
      entireDet2 (sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
        entireDet2
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) ↔
      RiemannHypothesis := by
  rw [← forall_d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_zero_iff_rh
    ha 0 mixed anti]
  constructor
  · intro h q
    exact (d4HBReducedTeukolskyHermitianDilation_det_eq_iff_source_eq_zero
      amplitude mixed anti q).1 (h q)
  · intro h q
    exact (d4HBReducedTeukolskyHermitianDilation_det_eq_iff_source_eq_zero
      amplitude mixed anti q).2 (h q)

/-- Closed route class: self-adjoint, local, Hilbert--Schmidt chiral dilation absorbs the angular
source unconditionally, but preserving its holomorphic determinant is exactly RH. -/
def D4HBReducedTeukolskyHermitianDilationFidelityRouteKilled : Prop :=
  ∀ amplitude : ℂ, amplitude ≠ 0 → ∀ mixed anti : ℂ,
    (∀ q : XiZeroCopy,
      IsHS (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) ∧
      hsAdjoint (sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
        sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) ∧
      sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)
          (Sum.inl 0, Sum.inr 0) =
        d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q ∧
      (∀ p, p ∉ d4HBReducedTeukolskyHermitianDilationSupport ×ˢ
            d4HBReducedTeukolskyHermitianDilationSupport →
        sourceHermitianDilationKernel
            (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) p = 0) ∧
      (entireDet2 (sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
          entireDet2
            (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q) ↔
        (q.1 : ℂ).re = 1 / 2) ∧
      ‖d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q‖ ^ (2 : ℕ) / 2 ≤
        ‖taylorCoeff
            (entireDet2 (sourceHermitianDilationKernel
              (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q))) 2 -
          taylorCoeff
            (entireDet2
              (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) 2‖) ∧
    ((∀ q : XiZeroCopy,
      entireDet2 (sourceHermitianDilationKernel
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) =
        entireDet2
          (d4HBReducedTeukolskyHermitianDilationSourceKernel amplitude mixed anti q)) ↔
      RiemannHypothesis)

/-- Premise-free certificate killing multi-sector Hermitianization as the missing angular-leakage
producer for the HB/FZZ-P/PW-B/RBH endpoint. -/
theorem d4HBReducedTeukolskyHermitianDilationFidelityRouteKilled :
    D4HBReducedTeukolskyHermitianDilationFidelityRouteKilled := by
  intro amplitude ha mixed anti
  constructor
  · intro q
    exact ⟨d4HBReducedTeukolskyHermitianDilationSourceKernel_isHS amplitude mixed anti q,
      d4HBReducedTeukolskyHermitianDilation_isSelfAdjoint amplitude mixed anti q,
      d4HBReducedTeukolskyHermitianDilation_sourceBlock amplitude mixed anti q,
      d4HBReducedTeukolskyHermitianDilation_support amplitude mixed anti q,
      d4HBReducedTeukolskyHermitianDilation_det_eq_iff_re_eq_half ha mixed anti q,
      d4HBReducedTeukolskyHermitianDilation_quadraticJetGap amplitude mixed anti q⟩
  · exact forall_d4HBReducedTeukolskyHermitianDilation_det_eq_iff_rh ha mixed anti

end

end RHTower
