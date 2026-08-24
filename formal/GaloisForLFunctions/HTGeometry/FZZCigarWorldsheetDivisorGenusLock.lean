import GaloisForLFunctions.HTGeometry.FZZCigarTorusReplicaNeutrality

/-!
# FZZ cigar worldsheet divisor/genus lock

The arbitrary-genus path-integral proof of FZZ duality contains a topological
constraint absent from abstract KMS or scattering models.  After integrating
out the cigar first-order field `γ`, its partner `β` is a meromorphic
one-differential.  With `N` poles from asymptotic string vertex operators, its
divisor has `N + 2g - 2` zeros on a closed genus-`g` worldsheet.  If `S` zeros
coalesce into the spectrally flowed identity, the remaining number `M` of
degenerate Liouville/FZZ insertions obeys

`M + S - N = 2g - 2`.

This file records four exact consequences.

* Adding one handle creates two residual horizon defects.
* Adding one asymptotic radiation vertex creates one residual horizon defect.
* Genus one is precisely charge neutral; the sphere carries the familiar
  two-unit background deficit.
* A fugacity coupled only to this conserved divisor charge factors out of
  every fixed-genus sector.  It therefore cannot produce nonzero Lee--Yang or
  RH-bearing zeros.  Any such zero set must come from a generating function
  over genuine radiation multiplicity, twists, or moduli, not from relabeling
  the fixed topological charge.

The last point is a route-specific no-go with a positive survivor: the next
object to construct is the full multiplicity-generating cigar scattering
amplitude, in which every emitted/asymptotic quantum is paired with an extra
horizon insertion.

Physics source:

* Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*,
  arXiv:0805.3931, especially equations (4.6)--(4.12).  Their `β` product has
  `M = N + 2g - 2 - S` residual zeros, expressed by prime forms.
* Kazakov--Kostov--Kutasov, *A Matrix Model for the Two Dimensional Black
  Hole*, hep-th/0101011, sections 4.4--4.5.  Its exact Toda times `t_n` are
  indexed by integer vortex winding `n`.
* Halder--Jafferis, arXiv:2402.00932, equations (3.29)--(3.33).  Their area
  operator instead differentiates a genuinely fractional winding `1 - δ`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace FZZCigar

/-- Signed Euler exponent of a connected closed genus-`g` string worldsheet.
It is both minus the Euler characteristic and the usual closed-string loop
exponent. -/
def worldsheetLoopExponent (genus : ℕ) : ℤ :=
  2 * (genus : ℤ) - 2

/-- Signed divisor charge of the FZZ first-order differential: residual
simple zeros plus the spectrally-flowed zero, minus asymptotic poles. -/
def fzzDivisorCharge (residualZeros spectralFlowZeros radiationPoles : ℕ) : ℤ :=
  (residualZeros : ℤ) + (spectralFlowZeros : ℤ) - (radiationPoles : ℤ)

/-- Expected signed number of residual FZZ zeros before imposing
nonnegativity.  The integer presentation avoids truncated natural
subtraction in low-point sphere sectors. -/
def fzzResidualZeroIndex
    (genus radiationPoles spectralFlowZeros : ℕ) : ℤ :=
  (radiationPoles : ℤ) + 2 * (genus : ℤ) - 2 - (spectralFlowZeros : ℤ)

/-- Source-faithful FZZ divisor constraint on a closed worldsheet. -/
def FZZDivisorRealization
    (genus residualZeros spectralFlowZeros radiationPoles : ℕ) : Prop :=
  fzzDivisorCharge residualZeros spectralFlowZeros radiationPoles =
    worldsheetLoopExponent genus

/-- Realizing the residual index is equivalent to the FZZ divisor/genus
constraint. -/
theorem fzzDivisorRealization_iff_residualZeroIndex
    (genus residualZeros spectralFlowZeros radiationPoles : ℕ) :
    FZZDivisorRealization genus residualZeros spectralFlowZeros radiationPoles ↔
      (residualZeros : ℤ) =
        fzzResidualZeroIndex genus radiationPoles spectralFlowZeros := by
  simp only [FZZDivisorRealization, fzzDivisorCharge, worldsheetLoopExponent,
    fzzResidualZeroIndex]
  constructor <;> intro h <;> omega

/-- Each added worldsheet handle forces exactly two additional residual FZZ
zeros at fixed external radiation and spectral flow. -/
theorem fzzResidualZeroIndex_add_handle
    (genus radiationPoles spectralFlowZeros : ℕ) :
    fzzResidualZeroIndex (genus + 1) radiationPoles spectralFlowZeros =
      fzzResidualZeroIndex genus radiationPoles spectralFlowZeros + 2 := by
  simp only [fzzResidualZeroIndex, Nat.cast_add, Nat.cast_one]
  ring

/-- Each additional asymptotic string/radiation pole forces exactly one
additional residual degenerate FZZ insertion at fixed topology. -/
theorem fzzResidualZeroIndex_add_radiation
    (genus radiationPoles spectralFlowZeros extra : ℕ) :
    fzzResidualZeroIndex genus (radiationPoles + extra) spectralFlowZeros =
      fzzResidualZeroIndex genus radiationPoles spectralFlowZeros + extra := by
  simp only [fzzResidualZeroIndex, Nat.cast_add]
  ring

/-- Coalescing `extra` more zeros into the spectrally flowed identity removes
the same signed number from the residual FZZ insertion count. -/
theorem fzzResidualZeroIndex_add_spectralFlow
    (genus radiationPoles spectralFlowZeros extra : ℕ) :
    fzzResidualZeroIndex genus radiationPoles (spectralFlowZeros + extra) =
      fzzResidualZeroIndex genus radiationPoles spectralFlowZeros - extra := by
  simp only [fzzResidualZeroIndex, Nat.cast_add]
  ring

/-- Realized-sector form of the radiation/horizon pairing law: at fixed
topology and spectral flow, `extra` new asymptotic radiation insertions force
exactly `extra` new residual horizon insertions. -/
theorem fzzDivisorRealization_radiation_defect_pairing
    {genus residualZeros spectralFlowZeros radiationPoles
      residualZeros' extra : ℕ}
    (h : FZZDivisorRealization genus residualZeros spectralFlowZeros radiationPoles)
    (h' : FZZDivisorRealization genus residualZeros' spectralFlowZeros
      (radiationPoles + extra)) :
    residualZeros' = residualZeros + extra := by
  have hindex :=
    (fzzDivisorRealization_iff_residualZeroIndex genus residualZeros
      spectralFlowZeros radiationPoles).mp h
  have hindex' :=
    (fzzDivisorRealization_iff_residualZeroIndex genus residualZeros'
      spectralFlowZeros (radiationPoles + extra)).mp h'
  rw [fzzResidualZeroIndex_add_radiation] at hindex'
  exact_mod_cast (show (residualZeros' : ℤ) = residualZeros + extra by omega)

/-- Realized-sector form of handle pair creation: increasing genus by one at
fixed radiation data forces exactly two new residual FZZ horizon defects. -/
theorem fzzDivisorRealization_handle_pair_creation
    {genus residualZeros spectralFlowZeros radiationPoles residualZeros' : ℕ}
    (h : FZZDivisorRealization genus residualZeros spectralFlowZeros radiationPoles)
    (h' : FZZDivisorRealization (genus + 1) residualZeros'
      spectralFlowZeros radiationPoles) :
    residualZeros' = residualZeros + 2 := by
  have hindex :=
    (fzzDivisorRealization_iff_residualZeroIndex genus residualZeros
      spectralFlowZeros radiationPoles).mp h
  have hindex' :=
    (fzzDivisorRealization_iff_residualZeroIndex (genus + 1) residualZeros'
      spectralFlowZeros radiationPoles).mp h'
  rw [fzzResidualZeroIndex_add_handle] at hindex'
  exact_mod_cast (show (residualZeros' : ℤ) = residualZeros + 2 by omega)

/-- On a torus, the residual and spectrally-flowed zeros exactly neutralize
the asymptotic radiation poles. -/
theorem fzzDivisorRealization_genus_one_iff_neutral
    (residualZeros spectralFlowZeros radiationPoles : ℕ) :
    FZZDivisorRealization 1 residualZeros spectralFlowZeros radiationPoles ↔
      residualZeros + spectralFlowZeros = radiationPoles := by
  change
    ((residualZeros : ℤ) + (spectralFlowZeros : ℤ) - (radiationPoles : ℤ) = 0) ↔
      residualZeros + spectralFlowZeros = radiationPoles
  constructor
  · intro h
    exact_mod_cast (show (residualZeros : ℤ) + spectralFlowZeros = radiationPoles by omega)
  · intro h
    have h' : (residualZeros : ℤ) + spectralFlowZeros = radiationPoles := by
      exact_mod_cast h
    omega

/-- On the sphere, two additional asymptotic poles are required to compensate
the curvature/background-charge deficit. -/
theorem fzzDivisorRealization_genus_zero_iff_background_deficit
    (residualZeros spectralFlowZeros radiationPoles : ℕ) :
    FZZDivisorRealization 0 residualZeros spectralFlowZeros radiationPoles ↔
      residualZeros + spectralFlowZeros + 2 = radiationPoles := by
  change
    ((residualZeros : ℤ) + (spectralFlowZeros : ℤ) - (radiationPoles : ℤ) = -2) ↔
      residualZeros + spectralFlowZeros + 2 = radiationPoles
  constructor
  · intro h
    exact_mod_cast
      (show (residualZeros : ℤ) + spectralFlowZeros + 2 = radiationPoles by omega)
  · intro h
    have h' : (residualZeros : ℤ) + spectralFlowZeros + 2 = radiationPoles := by
      exact_mod_cast h
    omega

/-- Every realized FZZ sector has divisor charge equal to its closed-string
loop exponent. -/
theorem fzzDivisorCharge_eq_worldsheetLoopExponent
    {genus residualZeros spectralFlowZeros radiationPoles : ℕ}
    (h : FZZDivisorRealization genus residualZeros spectralFlowZeros radiationPoles) :
    fzzDivisorCharge residualZeros spectralFlowZeros radiationPoles =
      worldsheetLoopExponent genus :=
  h

section FugacityNoGo

variable {ι : Type*}

/-- A fugacity coupled to FZZ divisor charge is only a topological monomial on
every realized sector. -/
theorem fzzChargeFugacity_eq_topologicalMonomial
    (z : ℂ) {genus residualZeros spectralFlowZeros radiationPoles : ℕ}
    (h : FZZDivisorRealization genus residualZeros spectralFlowZeros radiationPoles) :
    z ^ fzzDivisorCharge residualZeros spectralFlowZeros radiationPoles =
      z ^ worldsheetLoopExponent genus := by
  rw [h]

/-- Fixed-genus sector sum factors into one topological fugacity monomial and
the unweighted amplitude.  Consequently divisor-charge fugacity cannot
resolve different horizon/radiation configurations at fixed topology. -/
theorem sum_fzzChargeFugacity_eq_topologicalFactor
    (sectors : Finset ι) (z : ℂ) (genus : ℕ)
    (residualZeros spectralFlowZeros radiationPoles : ι → ℕ)
    (amplitude : ι → ℂ)
    (hrealized : ∀ i ∈ sectors,
      FZZDivisorRealization genus (residualZeros i)
        (spectralFlowZeros i) (radiationPoles i)) :
    ∑ i ∈ sectors,
        z ^ fzzDivisorCharge (residualZeros i) (spectralFlowZeros i)
          (radiationPoles i) * amplitude i =
      z ^ worldsheetLoopExponent genus * ∑ i ∈ sectors, amplitude i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fzzChargeFugacity_eq_topologicalMonomial z (hrealized i hi)]

/-- Away from zero fugacity, a fixed-genus realized sector sum vanishes iff
its unweighted amplitude already vanishes.  Thus no nonzero Lee--Yang locus,
and hence no RH-bearing zero set, can be generated by the conserved FZZ
divisor charge alone. -/
theorem sum_fzzChargeFugacity_eq_zero_iff
    (sectors : Finset ι) {z : ℂ} (hz : z ≠ 0) (genus : ℕ)
    (residualZeros spectralFlowZeros radiationPoles : ι → ℕ)
    (amplitude : ι → ℂ)
    (hrealized : ∀ i ∈ sectors,
      FZZDivisorRealization genus (residualZeros i)
        (spectralFlowZeros i) (radiationPoles i)) :
    (∑ i ∈ sectors,
        z ^ fzzDivisorCharge (residualZeros i) (spectralFlowZeros i)
          (radiationPoles i) * amplitude i = 0) ↔
      ∑ i ∈ sectors, amplitude i = 0 := by
  rw [sum_fzzChargeFugacity_eq_topologicalFactor sectors z genus residualZeros
    spectralFlowZeros radiationPoles amplitude hrealized]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hz)
  · intro h
    rw [h, mul_zero]

end FugacityNoGo

section IntegerWindingNoGo

/-- A continuous attempt to obtain replica backreaction by merely relabeling
integer Toda winding sectors is locally constant and has zero derivative.

This separates two mathematically different operations which must not be
conflated: the exact black-hole matrix model varies integer-indexed source
couplings `t_n`, whereas the Halder--Jafferis area operator varies the charge
of the winding vertex itself through `1 - δ`.  A nonzero replica-area tangent
therefore requires a new off-shell deformation of the kernel/OPE; it cannot
come from a continuous map into the old integer label set. -/
theorem integerWindingTodaRelabel_hasDerivAt_zero
    (amplitude : ℤ → ℂ) (windingLabel : ℝ → ℤ)
    (hcontinuous : ContinuousAt windingLabel 0) :
    HasDerivAt (fun δ : ℝ => amplitude (windingLabel δ)) 0 0 := by
  have hlabel : windingLabel =ᶠ[nhds 0] fun _ => windingLabel 0 := by
    have hsingleton : {windingLabel 0} ∈ nhds (windingLabel 0) := by
      rw [nhds_discrete]
      exact Set.mem_singleton _
    filter_upwards [hcontinuous hsingleton] with δ hδ
    exact Set.mem_singleton_iff.mp hδ
  have hamplitude :
      (fun δ : ℝ => amplitude (windingLabel δ)) =ᶠ[nhds 0]
        fun _ => amplitude (windingLabel 0) :=
    hlabel.fun_comp amplitude
  exact (hasDerivAt_const (x := (0 : ℝ)) (c := amplitude (windingLabel 0))).congr_of_eventuallyEq
    hamplitude

end IntegerWindingNoGo

end FZZCigar

end GaloisForLFunctions.HTGeometry
