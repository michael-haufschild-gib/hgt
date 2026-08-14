import GaloisForLFunctions.RHTower.ProlateCCMArcsineWeakLimit
import GaloisForLFunctions.RHTower.ProlateDunsterBesselOffDiagonal
import GaloisForLFunctions.RHTower.ProlateRadialNormalization

/-!
# Canonical radial families attached to fixed signed prolate modes

The radial normalization theorem supplies an exact endpoint-normalized solution separately at
every live aperture.  Limit theorems need a single family of such solutions.  This module makes
that family by classical choice, records its eventual exact specification, and instantiates the
Dunster weak-limit and full-ray off-diagonal theorems.

No asymptotic property is hidden in the choice.  The remaining analytic input is isolated exactly
as convergence of the chosen radial separation ratio to zero.
-/

noncomputable section

open Filter MeasureTheory Set

namespace RHTower

/-- Exact bandwidth associated with physical aperture `a`. -/
def signedModeRadialBandwidth (a : ℝ) : ℝ := 2 * Real.pi * a ^ 2

theorem tendsto_signedModeRadialBandwidth_atTop :
    Tendsto signedModeRadialBandwidth atTop atTop := by
  have hsq : Tendsto (fun a : ℝ => a ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  change Tendsto (fun a : ℝ => 2 * Real.pi * a ^ 2) atTop atTop
  exact hsq.const_mul_atTop (by positivity : 0 < 2 * Real.pi)

/-- Data selected from the endpoint-normalized radial existence theorem. -/
structure SignedModeRadialData where
  Phi : ℝ → ℝ
  R : ℝ → ℝ
  chi : ℝ
  s : ℝ

/-- Full exact specification of radial data for signed mode `n` at aperture `a`. -/
def SignedModeRadialData.IsExact (a : ℝ) (n : ℕ) (D : SignedModeRadialData) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D.Phi ∧ D.Phi ≠ 0 ∧ Function.Even D.Phi ∧
    D.Phi 1 ≠ 0 ∧ D.R = prolateEndpointNormalize D.Phi ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D.R ∧ Function.Even D.R ∧ D.R 1 = 1 ∧
    (∀ x : ℝ, bandTransform (signedModeRadialBandwidth a) D.Phi x =
      evenProlateSignedValue a n ^ 2 * D.Phi x) ∧
    (∀ x : ℝ, prolateSLAction (signedModeRadialBandwidth a) D.R x = D.chi * D.R x) ∧
    D.s = radialSeparationRatio (signedModeRadialBandwidth a) D.chi ∧ 0 ≤ D.s ∧
    2 * deriv D.R 1 = D.s * signedModeRadialBandwidth a ^ 2 -
      signedModeRadialBandwidth a ^ 2 ∧
    (∀ x : ℝ, (x ^ 2 - 1) * deriv (deriv D.R) x + 2 * x * deriv D.R x -
      (D.s * signedModeRadialBandwidth a ^ 2 -
        signedModeRadialBandwidth a ^ 2 * x ^ 2) * D.R x = 0)

theorem exists_signedModeRadialData_isExact
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ D : SignedModeRadialData, D.IsExact a n := by
  obtain ⟨Phi, R, chi, s, hPhi, hPhi0, hPhiEven, hPhi1, hRdef, hR, hREven,
      hR1, hband, heig, hs, hs0, hend, hode⟩ :=
    exists_endpointNormalized_radialProlate_of_signedMode ha n hvalue
  exact ⟨⟨Phi, R, chi, s⟩, hPhi, hPhi0, hPhiEven, hPhi1, hRdef, hR, hREven,
    hR1, by simpa [signedModeRadialBandwidth] using hband,
    by simpa [signedModeRadialBandwidth] using heig,
    by simpa [signedModeRadialBandwidth] using hs, hs0,
    by simpa [signedModeRadialBandwidth] using hend,
    by simpa [signedModeRadialBandwidth] using hode⟩

/-- Canonical endpoint-normalized radial data for signed mode `n`.  Outside the live-aperture
region it is assigned a harmless zero tuple; every theorem below uses its eventual exactness. -/
noncomputable def signedModeRadialData (a : ℝ) (n : ℕ) : SignedModeRadialData :=
  if h : 0 < a ∧ evenProlateSignedValue a n ≠ 0 then
    Classical.choose (exists_signedModeRadialData_isExact h.1 n h.2)
  else
    ⟨0, 0, 0, 0⟩

theorem signedModeRadialData_isExact
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    (signedModeRadialData a n).IsExact a n := by
  rw [signedModeRadialData, dif_pos ⟨ha, hvalue⟩]
  exact Classical.choose_spec (exists_signedModeRadialData_isExact ha n hvalue)

/-- Every fixed signed greedy index has exact canonical radial data at all sufficiently large
apertures. -/
theorem eventually_signedModeRadialData_isExact (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).IsExact a n := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_evenProlateSignedValue_ne_zero n] with a ha hvalue
  exact signedModeRadialData_isExact ha n hvalue

theorem eventually_signedModeRadialData_s_nonneg (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, 0 ≤ (signedModeRadialData a n).s := by
  filter_upwards [eventually_signedModeRadialData_isExact n] with a h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hs0, _⟩
  exact hs0

theorem eventually_signedModeRadialData_R_one (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).R 1 = 1 := by
  filter_upwards [eventually_signedModeRadialData_isExact n] with a h
  rcases h with ⟨_, _, _, _, _, _, _, hR1, _⟩
  exact hR1

theorem eventually_signedModeRadialData_hasDerivAt (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ t,
      HasDerivAt (signedModeRadialData a n).R
        (deriv (signedModeRadialData a n).R t) t := by
  filter_upwards [eventually_signedModeRadialData_isExact n] with a h
  rcases h with ⟨_, _, _, _, _, hRsm, _⟩
  intro t
  exact ((contDiff_infty_iff_deriv.mp hRsm).1 t).hasDerivAt

theorem eventually_signedModeRadialData_hasSecondDerivAt (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ t,
      HasDerivAt (deriv (signedModeRadialData a n).R)
        (deriv (deriv (signedModeRadialData a n).R) t) t := by
  filter_upwards [eventually_signedModeRadialData_isExact n] with a h
  rcases h with ⟨_, _, _, _, _, hRsm, _⟩
  intro t
  exact ((contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp hRsm).2).1 t).hasDerivAt

theorem eventually_signedModeRadialData_ode (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ t,
      (t ^ 2 - 1) * deriv (deriv (signedModeRadialData a n).R) t +
          2 * t * deriv (signedModeRadialData a n).R t -
        ((signedModeRadialData a n).s * signedModeRadialBandwidth a ^ 2 -
          signedModeRadialBandwidth a ^ 2 * t ^ 2) *
          (signedModeRadialData a n).R t = 0 := by
  filter_upwards [eventually_signedModeRadialData_isExact n] with a h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hode⟩
  exact hode

/-- Canonical fixed-mode radial density obeys the exact CCM arcsine tail law once the remaining
separation asymptotic is proved. -/
theorem tendsto_integral_Ioi_signedModeRadialDensity
    (n : ℕ)
    (hs : Tendsto (fun a : ℝ => (signedModeRadialData a n).s) atTop (nhds 0))
    {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
      GaloisForLFunctions.RHTower.radialProlateDensity
        (signedModeRadialBandwidth a) (signedModeRadialData a n).R x)
      atTop
      (nhds ((∫ x in Ioi b, _root_.RHTower.radialLeakageDensity x) / Real.pi)) := by
  let D : ℝ → SignedModeRadialData := fun a => signedModeRadialData a n
  let DR : ℝ → ℝ → ℝ := fun a => deriv (D a).R
  let DDR : ℝ → ℝ → ℝ := fun a => deriv (deriv (D a).R)
  exact GaloisForLFunctions.RHTower.tendsto_integral_Ioi_radialProlateDensity_to_ccmLeakage
    (R := fun a => (D a).R) (DR := DR) (DDR := DDR)
    tendsto_signedModeRadialBandwidth_atTop hs
    (eventually_signedModeRadialData_s_nonneg n)
    (by simpa [D] using eventually_signedModeRadialData_R_one n)
    (by simpa [D, DR] using eventually_signedModeRadialData_hasDerivAt n)
    (by simpa [D, DR, DDR] using eventually_signedModeRadialData_hasSecondDerivAt n)
    (by simpa [D, DR, DDR] using eventually_signedModeRadialData_ode n) hb

/-- Canonical fixed-mode first-row radial Gram overlaps vanish on the full exterior ray once the
remaining separation asymptotic is proved. -/
theorem tendsto_integral_Ioi_signedModeFirstRowRadialProduct
    (n : ℕ)
    (hs : Tendsto (fun a : ℝ => (signedModeRadialData a n).s) atTop (nhds 0))
    {k : ℝ} (hk : 1 < k) :
    Tendsto (fun a : ℝ => ∫ x in Ioi (1 : ℝ),
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) atTop (nhds 0) := by
  let D : ℝ → SignedModeRadialData := fun a => signedModeRadialData a n
  let DR : ℝ → ℝ → ℝ := fun a => deriv (D a).R
  let DDR : ℝ → ℝ → ℝ := fun a => deriv (deriv (D a).R)
  exact GaloisForLFunctions.RHTower.tendsto_integral_Ioi_firstRowRadialProduct_fixedRatio
    (R := fun a => (D a).R) (DR := DR) (DDR := DDR)
    tendsto_signedModeRadialBandwidth_atTop hs
    (eventually_signedModeRadialData_s_nonneg n)
    (by simpa [D] using eventually_signedModeRadialData_R_one n)
    (by simpa [D, DR] using eventually_signedModeRadialData_hasDerivAt n)
    (by simpa [D, DR, DDR] using eventually_signedModeRadialData_hasSecondDerivAt n)
    (by simpa [D, DR, DDR] using eventually_signedModeRadialData_ode n) hk

end RHTower

end

