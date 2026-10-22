import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGCompletedEisensteinOpticalIncidence

/-!
# Completed-Eisenstein continuum excludes QNM-only HB completion

The completed angular EKG vertex is not merely bright at one continuum energy.  For every Xi
divisor copy and every external energy, its squared continuum density has strictly positive total
mass.  Continuity upgrades the existing bright-point theorem to positive Lebesgue support, while
integrability makes the total mass finite.

Consequently the continuum-completed optical energy is strictly larger than every finite
QNM/Maass energy sum.  No fixed finite QNM sector can therefore be the complete nonlinear EKG
response on the Xi divisor.  This kills QNM-only realizations of the remaining HB Green producer;
a survivor must retain genuine continuum/direct-arc response before attempting FE--Schwarz Ward
extinction.

`[NEW] [HB ROUTE KILL] [CONTINUUM MASS] [QNM INCOMPLETENESS] [LEAN-PROVED]`
-/

open Complex Real MeasureTheory
open scoped FourierTransform SchwartzMap Interval

namespace RHTower

noncomputable section

/-- Integrated completed-Eisenstein continuum mass at one Xi divisor and external energy. -/
def thetaCuspHawkingCompletedEisensteinContinuumMass
    (q : XiZeroCopy) (t : ℝ) : ℝ :=
  ∫ r : ℝ, thetaCuspHawkingCompletedEisensteinContinuumDensity q t r

/-- Every Xi divisor has strictly positive total completed-Eisenstein continuum mass. -/
theorem thetaCuspHawkingCompletedEisensteinContinuumMass_pos
    (q : XiZeroCopy) (t : ℝ) :
    0 < thetaCuspHawkingCompletedEisensteinContinuumMass q t := by
  rw [thetaCuspHawkingCompletedEisensteinContinuumMass,
    integral_pos_iff_support_of_nonneg
      (thetaCuspHawkingCompletedEisensteinContinuumDensity_nonneg q t)
      (integrable_thetaCuspHawkingCompletedEisensteinContinuumDensity q t)]
  obtain ⟨r, hr⟩ :=
    exists_thetaCuspHawkingCompletedEisensteinContinuumDensity_pos q t
  have hrmem : r ∈ Function.support
      (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) := by
    exact ne_of_gt hr
  have hopen : IsOpen (Function.support
      (thetaCuspHawkingCompletedEisensteinContinuumDensity q t)) := by
    convert
      (continuous_thetaCuspHawkingCompletedEisensteinContinuumDensity q t).isOpen_preimage
        ({0}ᶜ) isOpen_ne using 1
    ext x
    simp [Function.support]
  have hrsupport : r ∈ (volume : Measure ℝ).support := by
    rw [Measure.support_eq_univ]
    trivial
  exact (Measure.mem_support_iff_forall r).mp hrsupport
    (Function.support (thetaCuspHawkingCompletedEisensteinContinuumDensity q t))
    (hopen.mem_nhds hrmem)

/-- Finite discrete energy completed by the integrated physical continuum channel. -/
def thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t : ℝ) : ℝ :=
  thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude +
    2 * Real.pi * thetaCuspHawkingCompletedEisensteinContinuumMass q t

/-- The exact continuum correction is its positive integrated spectral mass. -/
theorem thetaCuspHawkingEKGIntegratedContinuumOpticalGap_eq
    {ι : Type*} (modes : Finset ι) (amplitude : ι → ℂ)
    (q : XiZeroCopy) (t : ℝ) :
    thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy
          modes amplitude q t -
        thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude =
      2 * Real.pi * thetaCuspHawkingCompletedEisensteinContinuumMass q t := by
  rw [thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy]
  ring

/-- Every continuum-completed EKG response strictly exceeds its finite discrete sector. -/
theorem thetaCuspHawkingEKGDiscreteOpticalEnergy_lt_discretePlusIntegratedContinuum
    {ι : Type*} (modes : Finset ι) (amplitude : ι → ℂ)
    (q : XiZeroCopy) (t : ℝ) :
    thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude <
      thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy
        modes amplitude q t := by
  rw [thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy]
  have hmass := thetaCuspHawkingCompletedEisensteinContinuumMass_pos q t
  nlinarith [Real.pi_pos]

/-- QNM-only completeness would erase the completed continuum sector. -/
def ThetaCuspHawkingEKGFiniteQNMOnlyComplete {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t : ℝ) : Prop :=
  thetaCuspHawkingEKGDiscretePlusIntegratedContinuumOpticalEnergy
      modes amplitude q t =
    thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude

/-- No finite QNM/Maass sector is complete even at one Xi divisor and external energy. -/
theorem not_thetaCuspHawkingEKGFiniteQNMOnlyComplete
    {ι : Type*} (modes : Finset ι) (amplitude : ι → ℂ)
    (q : XiZeroCopy) (t : ℝ) :
    ¬ ThetaCuspHawkingEKGFiniteQNMOnlyComplete modes amplitude q t := by
  intro h
  have hlt :=
    thetaCuspHawkingEKGDiscreteOpticalEnergy_lt_discretePlusIntegratedContinuum
      modes amplitude q t
  exact (ne_of_gt hlt) h

/-- A fixed finite QNM sector is claimed to complete every Xi-divisor response. -/
def ThetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) : Prop :=
  ∀ q : XiZeroCopy, ∀ t : ℝ,
    ThetaCuspHawkingEKGFiniteQNMOnlyComplete modes amplitude q t

/-- **[HB QNM-ONLY ROUTE KILL].** No fixed finite QNM/Maass sector is the complete nonlinear EKG
optical response on the Xi divisor. -/
theorem not_thetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete
    {ι : Type*} (modes : Finset ι) (amplitude : ι → ℂ) :
    ¬ ThetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete modes amplitude := by
  intro hcomplete
  obtain ⟨q⟩ := nonempty_xiZeroCopy
  exact not_thetaCuspHawkingEKGFiniteQNMOnlyComplete modes amplitude q 0
    (hcomplete q 0)

end

end RHTower
