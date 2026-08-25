import GaloisForLFunctions.HTGeometry.ReflectionTransverseProvenanceWeightSelection
import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHodge
import GaloisForLFunctions.RHTower.XiNodalDefectSuperselection
import GaloisForLFunctions.RHTower.XiWeilSameFiberAtomIsotropy

/-!
# Stratified formation and dagger coherence on the Xi divisor

There are two different involutions on a multiplicity-exact Xi atom.

* Functional-equation reflection sends `rho` to `1 - rho`.  It is fixed-point-free on every
  Xi zero copy, including copies over critical-line zeros.
* Hermitian line conjugation sends `rho` to `1 - conj rho`.  It fixes a copy exactly when its
  support lies on the critical line.

Conflating these involutions makes a formation-weight proposal inconsistent: a nonzero integral
atom can never be invariant under a nontrivial formation action built from functional-equation
reflection.  The Hermitian action has the intended behavior.  It preserves the full integer
multiplicity exactly when the local mixed grade--phase curvature vanishes, equivalently when the
source-level second-order descent anomaly is coherent.

This is a falsifiable structural bridge, not an RH proof.  The global Hermitian formation law is
proved below to have exactly RH strength; an independent arithmetic construction of that law
remains necessary.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Formation action on one source atom using Hermitian line conjugation
`rho |-> 1 - conj rho`. -/
def xiHermitianFormationAtom
    (scale : ℕ) (q : XiZeroCopy) (multiplicity : ℤ) : XiZeroCopy →₀ ℤ :=
  reflectionProvenanceWeightAction xiZeroCopyLineConjEquiv scale
    (Finsupp.single q multiplicity)

/-- Wrong-involution control: the same formation construction using bare functional-equation
reflection `rho |-> 1 - rho`. -/
def xiFunctionalEquationFormationAtom
    (scale : ℕ) (q : XiZeroCopy) (multiplicity : ℤ) : XiZeroCopy →₀ ℤ :=
  reflectionProvenanceWeightAction xiZeroCopyReflectEquiv scale
    (Finsupp.single q multiplicity)

/-- A nontrivial Hermitian formation fixes a nonzero integral atom exactly on the critical line.
The coefficient is not reduced or rationalized. -/
theorem xiHermitianFormationAtom_eq_self_iff_re_eq_half
    (q : XiZeroCopy) (multiplicity : ℤ) (hm : multiplicity ≠ 0)
    {scale : ℕ} (hscale : 2 ≤ scale) :
    xiHermitianFormationAtom scale q multiplicity =
        Finsupp.single q multiplicity ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hinvariant
    have hfixed : xiZeroCopyLineConjEquiv q = q :=
      support_fixed_of_provenanceWeightInvariant
        xiZeroCopyLineConjEquiv (Finsupp.single q multiplicity)
        hscale (by simpa [xiHermitianFormationAtom] using hinvariant)
        q (by simp [hm])
    exact (xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half q).mp hfixed
  · intro hline
    have hfixed : xiZeroCopyLineConjEquiv q = q :=
      (xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half q).mpr hline
    simpa [xiHermitianFormationAtom] using
      (reflectionProvenanceWeightAction_single_of_fixed
        xiZeroCopyLineConjEquiv multiplicity scale hfixed)

/-- Falsifier for the unstratified proposal: bare functional-equation reflection has no fixed Xi
copy, so no nonzero atom is invariant under any nontrivial formation scale. -/
theorem xiFunctionalEquationFormationAtom_ne_self
    (q : XiZeroCopy) (multiplicity : ℤ) (hm : multiplicity ≠ 0)
    {scale : ℕ} (hscale : 2 ≤ scale) :
    xiFunctionalEquationFormationAtom scale q multiplicity ≠
      Finsupp.single q multiplicity := by
  intro hinvariant
  have hfixed : xiZeroCopyReflectEquiv q = q :=
    support_fixed_of_provenanceWeightInvariant
      xiZeroCopyReflectEquiv (Finsupp.single q multiplicity)
      hscale (by simpa [xiFunctionalEquationFormationAtom] using hinvariant)
      q (by simp [hm])
  exact xiZeroCopyReflectEquiv_ne q hfixed

/-- The corrected formation criterion is exactly local derived coherence: the first-order source
anomaly may remain nonzero, while its covariant second boundary vanishes. -/
theorem xiHermitianFormationAtom_eq_self_iff_secondOrderCoherent
    (q : XiZeroCopy) (multiplicity : ℤ) (hm : multiplicity ≠ 0)
    {scale : ℕ} (hscale : 2 ≤ scale) :
    xiHermitianFormationAtom scale q multiplicity =
        Finsupp.single q multiplicity ↔
      XiNodalArithmeticSecondOrderCoherent q := by
  calc
    xiHermitianFormationAtom scale q multiplicity =
          Finsupp.single q multiplicity ↔
        (q.1 : ℂ).re = 1 / 2 :=
      xiHermitianFormationAtom_eq_self_iff_re_eq_half
        q multiplicity hm hscale
    _ ↔ XiNodalDefectSuperselected q :=
      (xiNodalDefectSuperselected_iff_re_eq_half q).symm
    _ ↔ XiNodalDefectMasterEquation q :=
      (xiNodalDefectMasterEquation_iff_superselected q).symm
    _ ↔ XiNodalArithmeticSecondOrderCoherent q :=
      (xiNodalArithmeticSecondOrderCoherent_iff q).symm

/-- Equivalent source-jet form: Hermitian formation invariance kills precisely the mixed
grade--phase jet, not the multiplicity coefficient. -/
theorem xiHermitianFormationAtom_eq_self_iff_mixedSourceJet_eq_zero
    (q : XiZeroCopy) (multiplicity : ℤ) (hm : multiplicity ≠ 0)
    {scale : ℕ} (hscale : 2 ≤ scale) :
    xiHermitianFormationAtom scale q multiplicity =
        Finsupp.single q multiplicity ↔
      xiReflectedPhaseNeutralMixedJet q = 0 := by
  calc
    xiHermitianFormationAtom scale q multiplicity =
          Finsupp.single q multiplicity ↔
        (q.1 : ℂ).re = 1 / 2 :=
      xiHermitianFormationAtom_eq_self_iff_re_eq_half
        q multiplicity hm hscale
    _ ↔ XiNodalDefectSuperselected q :=
      (xiNodalDefectSuperselected_iff_re_eq_half q).symm
    _ ↔ xiReflectedPhaseNeutralMixedJet q = 0 :=
      xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q

/-- Global source law at one nontrivial formation scale.  Unit coefficients are enough because
the local theorem preserves arbitrary nonzero integer multiplicity. -/
def XiHermitianFormationCoherence (scale : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    xiHermitianFormationAtom scale q 1 = Finsupp.single q 1

/-- Global Hermitian formation coherence is the same statement as universal second-order nodal
coherence. -/
theorem xiHermitianFormationCoherence_iff_nodalSecondOrderCoherence
    {scale : ℕ} (hscale : 2 ≤ scale) :
    XiHermitianFormationCoherence scale ↔
      XiNodalArithmeticSecondOrderCoherence := by
  unfold XiHermitianFormationCoherence XiNodalArithmeticSecondOrderCoherence
  apply forall_congr'
  intro q
  exact xiHermitianFormationAtom_eq_self_iff_secondOrderCoherent
    q 1 one_ne_zero hscale

/-- Exact-strength audit: this synthesis identifies the correct kind of source law, but does not
produce it.  Proving global Hermitian formation coherence independently is equivalent to RH. -/
theorem xiHermitianFormationCoherence_iff_riemannHypothesis
    {scale : ℕ} (hscale : 2 ≤ scale) :
    XiHermitianFormationCoherence scale ↔ RiemannHypothesis := by
  rw [xiHermitianFormationCoherence_iff_nodalSecondOrderCoherence hscale,
    xiNodalArithmeticSecondOrderCoherence_iff_riemannHypothesis]

end

end RHTower
