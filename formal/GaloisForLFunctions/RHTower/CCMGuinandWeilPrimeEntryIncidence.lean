import GaloisForLFunctions.RHTower.CCMGuinandWeilCompletedCenteredSourceMatrix

/-!
# Four-unit prime-entry source--codiagonal incidence

As aperture grows, a prime-power atom enters the finite Guinand--Weil horizon at
`a = log(k)/2`.  Both its odd source coordinate and weighted-cosine diagonal coordinate vanish at
that wall, so the finite packet has no value jump.  Their aperture tangents do not vanish.

This file computes those tangents exactly.  The diagonal tangent is mode-independent and carries
the coefficient `-4 * criticalMellinAtomWeight k / log k`; the odd tangent is its Fourier mode
multiple.  Thus each arithmetic entry event has an exact four-unit source--codiagonal incidence.
The theorem concerns the source germ before finite packet quotienting and does not assert a global
smooth aperture path across the one-sided atom-inclusion wall.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Aperture at which index `k` first reaches the moving logarithmic horizon. -/
def ccmGuinandWeilPrimeEntryAperture (k : ℕ) : ℝ :=
  Real.log k / 2

/-- Unclamped affine horizon coordinate of index `k` as aperture varies. -/
def ccmGuinandWeilPrimeEntryHorizon (k : ℕ) (a : ℝ) : ℝ :=
  1 - (Real.log k / 2) / a

/-- Every nontrivial index enters exactly at horizon coordinate zero. -/
theorem ccmGuinandWeilPrimeEntryHorizon_at_entry {k : ℕ} (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryHorizon k (ccmGuinandWeilPrimeEntryAperture k) = 0 := by
  have hlog : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hk)).ne'
  simp [ccmGuinandWeilPrimeEntryHorizon, ccmGuinandWeilPrimeEntryAperture, hlog]

/-- The entering atom moves into the horizon with speed `2 / log k`. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_entry
    {k : ℕ} (hk : 1 < k) :
    HasDerivAt (ccmGuinandWeilPrimeEntryHorizon k) (2 / Real.log k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  have ha0 : ccmGuinandWeilPrimeEntryAperture k ≠ 0 := by
    rw [ccmGuinandWeilPrimeEntryAperture]
    positivity
  have hquot :=
    (hasDerivAt_const (x := ccmGuinandWeilPrimeEntryAperture k)
      (c := Real.log k / 2)).div
      (hasDerivAt_id (x := ccmGuinandWeilPrimeEntryAperture k)) ha0
  have hraw :=
    (hasDerivAt_const (x := ccmGuinandWeilPrimeEntryAperture k) (c := (1 : ℝ))).sub hquot
  have hraw' : HasDerivAt
      (fun a : ℝ => 1 - (Real.log k / 2) / a)
      (2 / Real.log k) (ccmGuinandWeilPrimeEntryAperture k) := by
    apply hraw.congr_deriv
    simp only [ccmGuinandWeilPrimeEntryAperture, id_eq, zero_mul, zero_sub]
    field_simp [hlog.ne']
  exact hraw'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun a => by rfl)

/-- Single-atom contribution to the odd source reporter as a function of horizon coordinate. -/
def ccmGuinandWeilPrimeEntryOddProfile (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  -criticalMellinAtomWeight k *
      Real.sin (2 * Real.pi * omega * (mode : ℝ)) / Real.pi

/-- Single-atom contribution to the diagonal reporter as a function of horizon coordinate. -/
def ccmGuinandWeilPrimeEntryDiagonalProfile (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  -2 * criticalMellinAtomWeight k * omega *
    Real.cos (2 * Real.pi * omega * (mode : ℝ))

/-- Odd source profile pulled back along the moving aperture horizon. -/
def ccmGuinandWeilPrimeEntryOddGerm (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryOddProfile k mode (ccmGuinandWeilPrimeEntryHorizon k a)

/-- Diagonal profile pulled back along the moving aperture horizon. -/
def ccmGuinandWeilPrimeEntryDiagonalGerm (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalProfile k mode (ccmGuinandWeilPrimeEntryHorizon k a)

/-- The odd profile is exactly the normalized single-atom term in the continuous source. -/
theorem ccmGuinandWeilPrimeEntryOddProfile_eq_sourceAtom
    (k : ℕ) (mode : ℤ) (omega : CCMGuinandWeilHorizon) :
    ccmGuinandWeilPrimeEntryOddProfile k mode omega.1 =
      (-criticalMellinAtomWeight k *
        ccmGuinandWeilSineCoordinate mode omega) / Real.pi := by
  rfl

/-- The diagonal profile is exactly the single-atom weighted-cosine reporter term. -/
theorem ccmGuinandWeilPrimeEntryDiagonalProfile_eq_sourceAtom
    (k : ℕ) (mode : ℤ) (omega : CCMGuinandWeilHorizon) :
    ccmGuinandWeilPrimeEntryDiagonalProfile k mode omega.1 =
      2 * (-criticalMellinAtomWeight k *
        ccmGuinandWeilWeightedCosineCoordinate mode omega) := by
  rw [ccmGuinandWeilPrimeEntryDiagonalProfile]
  change -2 * criticalMellinAtomWeight k * omega.1 *
      Real.cos (2 * Real.pi * omega.1 * (mode : ℝ)) =
    2 * (-criticalMellinAtomWeight k *
      (omega.1 * Real.cos (2 * Real.pi * omega.1 * (mode : ℝ))))
  ring

/-- An entering prime atom creates no odd-source value jump. -/
theorem ccmGuinandWeilPrimeEntryOddGerm_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddGerm k mode (ccmGuinandWeilPrimeEntryAperture k) = 0 := by
  rw [ccmGuinandWeilPrimeEntryOddGerm, ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryOddProfile]
  simp

/-- An entering prime atom creates no diagonal value jump. -/
theorem ccmGuinandWeilPrimeEntryDiagonalGerm_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalGerm k mode (ccmGuinandWeilPrimeEntryAperture k) = 0 := by
  rw [ccmGuinandWeilPrimeEntryDiagonalGerm, ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryDiagonalProfile]
  simp

/-- Odd single-atom reporter has horizon derivative `-2 n w_k` at entry. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddProfile_zero
    (k : ℕ) (mode : ℤ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddProfile k mode)
      (-2 * (mode : ℝ) * criticalMellinAtomWeight k) 0 := by
  have hphase : HasDerivAt
      (fun omega : ℝ => 2 * Real.pi * omega * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) 0 := by
    have hraw := ((hasDerivAt_id (x := (0 : ℝ))).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun omega : ℝ => 2 * Real.pi * id omega * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) 0 := hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun omega => by rfl)
  have hsin : HasDerivAt
      (fun omega : ℝ => Real.sin (2 * Real.pi * omega * (mode : ℝ)))
      (2 * Real.pi * (mode : ℝ)) 0 := by
    have hraw :=
      (Real.hasDerivAt_sin (2 * Real.pi * 0 * (mode : ℝ))).comp 0 hphase
    have hraw' : HasDerivAt
        (Real.sin ∘ fun omega : ℝ => 2 * Real.pi * omega * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) 0 := hraw.congr_deriv (by simp)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun omega => by rfl)
  have hscaled := (hsin.const_mul (-criticalMellinAtomWeight k)).div_const Real.pi
  have hscaled' : HasDerivAt
      (fun omega : ℝ => -criticalMellinAtomWeight k *
        Real.sin (2 * Real.pi * omega * (mode : ℝ)) / Real.pi)
      (-2 * (mode : ℝ) * criticalMellinAtomWeight k) 0 :=
    hscaled.congr_deriv (by
      field_simp [Real.pi_ne_zero])
  exact hscaled'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun omega => by
      rw [ccmGuinandWeilPrimeEntryOddProfile])

/-- Diagonal single-atom reporter has mode-independent horizon derivative `-2 w_k` at entry. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfile_zero
    (k : ℕ) (mode : ℤ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalProfile k mode)
      (-2 * criticalMellinAtomWeight k) 0 := by
  have hphase : HasDerivAt
      (fun omega : ℝ => 2 * Real.pi * omega * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) 0 := by
    have hraw := ((hasDerivAt_id (x := (0 : ℝ))).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun omega : ℝ => 2 * Real.pi * id omega * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) 0 := hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun omega => by rfl)
  have hcos : HasDerivAt
      (fun omega : ℝ => Real.cos (2 * Real.pi * omega * (mode : ℝ))) 0 0 := by
    have hraw :=
      (Real.hasDerivAt_cos (2 * Real.pi * 0 * (mode : ℝ))).comp 0 hphase
    have hraw' : HasDerivAt
        (Real.cos ∘ fun omega : ℝ => 2 * Real.pi * omega * (mode : ℝ)) 0 0 :=
      hraw.congr_deriv (by simp)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun omega => by rfl)
  have hmul := (hasDerivAt_id (x := (0 : ℝ))).mul hcos
  have hscaled := hmul.const_mul (-2 * criticalMellinAtomWeight k)
  have hscaled' : HasDerivAt
      (fun omega : ℝ => -2 * criticalMellinAtomWeight k *
        (omega * Real.cos (2 * Real.pi * omega * (mode : ℝ))))
      (-2 * criticalMellinAtomWeight k) 0 :=
    hscaled.congr_deriv (by simp)
  exact hscaled'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun omega => by
      rw [ccmGuinandWeilPrimeEntryDiagonalProfile]
      ring)

/-- Aperture derivative of the entering odd source carries exact four-unit coefficient. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddGerm k mode)
      (-4 * (mode : ℝ) * criticalMellinAtomWeight k / Real.log k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  have houter : HasDerivAt (ccmGuinandWeilPrimeEntryOddProfile k mode)
      (-2 * (mode : ℝ) * criticalMellinAtomWeight k)
      (ccmGuinandWeilPrimeEntryHorizon k (ccmGuinandWeilPrimeEntryAperture k)) := by
    rw [ccmGuinandWeilPrimeEntryHorizon_at_entry hk]
    exact hasDerivAt_ccmGuinandWeilPrimeEntryOddProfile_zero k mode
  have hcomp := houter.comp
    (ccmGuinandWeilPrimeEntryAperture k) (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_entry hk)
  have hcomp' : HasDerivAt
      (ccmGuinandWeilPrimeEntryOddProfile k mode ∘ ccmGuinandWeilPrimeEntryHorizon k)
      (-4 * (mode : ℝ) * criticalMellinAtomWeight k / Real.log k)
      (ccmGuinandWeilPrimeEntryAperture k) := hcomp.congr_deriv (by ring)
  exact hcomp'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun a => by
      rw [ccmGuinandWeilPrimeEntryOddGerm]
      rfl)

/-- Aperture derivative of the entering diagonal is mode-independent with exact coefficient four. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalGerm k mode)
      (-4 * criticalMellinAtomWeight k / Real.log k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  have houter : HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalProfile k mode)
      (-2 * criticalMellinAtomWeight k)
      (ccmGuinandWeilPrimeEntryHorizon k (ccmGuinandWeilPrimeEntryAperture k)) := by
    rw [ccmGuinandWeilPrimeEntryHorizon_at_entry hk]
    exact hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfile_zero k mode
  have hcomp := houter.comp
    (ccmGuinandWeilPrimeEntryAperture k) (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_entry hk)
  have hcomp' : HasDerivAt
      (ccmGuinandWeilPrimeEntryDiagonalProfile k mode ∘ ccmGuinandWeilPrimeEntryHorizon k)
      (-4 * criticalMellinAtomWeight k / Real.log k)
      (ccmGuinandWeilPrimeEntryAperture k) := hcomp.congr_deriv (by ring)
  exact hcomp'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun a => by
      rw [ccmGuinandWeilPrimeEntryDiagonalGerm]
      rfl)

/-- **Four-unit event incidence.** At every prime-entry wall, odd-source tangent equals Fourier
mode times diagonal tangent. -/
theorem ccmGuinandWeilPrimeEntry_fourUnit_source_codiagonal_incidence
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    deriv (ccmGuinandWeilPrimeEntryOddGerm k mode) (ccmGuinandWeilPrimeEntryAperture k) =
      (mode : ℝ) *
        deriv (ccmGuinandWeilPrimeEntryDiagonalGerm k mode)
          (ccmGuinandWeilPrimeEntryAperture k) := by
  rw [(hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_entry hk mode).deriv,
    (hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_entry hk mode).deriv]
  ring

end RHTower
