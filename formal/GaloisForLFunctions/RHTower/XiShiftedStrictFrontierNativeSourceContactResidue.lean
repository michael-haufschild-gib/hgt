import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactSourceWallResidue

/-!
# Native adaptive-source residue at every strict-frontier contact

The parity-complete first-contact producer and the arbitrary-order newborn admission norm contain
the same first Padé defect.  Dividing them cancels its magnitude exactly.  The resulting signed
native-source/admission residue is universal: it depends only on admission degree, contact order,
and parity.

This is a source-first statement.  Even contact uses the diagonal adaptive mixed completed source;
odd contact uses the nondegenerate completed null-flag source.  No bilinear surrogate, orientation
map, or fixed reporter is introduced.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Scalar power-series coefficient is the corresponding iterated derivative divided by
factorial.  Stated multiplication-first to avoid division in source identities. -/
theorem iteratedDeriv_eq_factorial_mul_coeff_of_hasFPowerSeriesAt
    {f : ℝ → ℝ} {coeff : ℕ → ℝ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ coeff) 0)
    (d : ℕ) :
    iteratedDeriv d f 0 = d.factorial * coeff d := by
  have hcanonical := hf.analyticAt.hasFPowerSeriesAt
  have heq := hf.eq_formalMultilinearSeries hcanonical
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff d) heq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  rw [hcoeff]
  field_simp

/-- First live Padé defect is exactly first live shifted-Hankel determinant jet. -/
theorem iteratedDeriv_det_xiShiftedMomentHankelMatrix_add_at_firstPadeContact
    {y : ℝ} (hy : 0 < y) {n d : ℕ}
    (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    iteratedDeriv d
        (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det) 0 =
      d.factorial * (xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) := by
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)
  let coeff : ℕ → ℝ := fun j => PowerSeries.coeff j A.det
  let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det
  have hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ coeff) 0 := by
    simpa only [f, coeff, A, xiShiftedHankelDetFPowerSeries] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 1))
  have hjet := iteratedDeriv_eq_factorial_mul_coeff_of_hasFPowerSeriesAt hf d
  have hcoeff : coeff d =
      (xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) := by
    dsimp only [coeff, A]
    exact coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
      c hhead hc hlast hd hzero
  rw [hcoeff] at hjet
  change iteratedDeriv d
      (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det) 0 = _ at hjet
  calc
    iteratedDeriv d
        (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det) 0 =
      d.factorial * ((xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d))) := hjet
    _ = d.factorial * (xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) := by ring

/-- Literal parity-selected native source at a finite first contact.  Admission chooses `P` before
source formation; contact parity chooses the completed source algebra. -/
noncomputable def xiShiftedAdaptiveMixedCompletedFirstContactSourceValue
    (w : ℝ) (n d : ℕ) (c : Fin (n + 1) → ℝ) : ℝ :=
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  if d % 2 = 0 then
    xiShiftedAdaptiveMixedCompletedArithmeticSource w (P * X ^ (d / 2 - 1))
  else
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource
      w (n + d / 2) (P * X ^ (d / 2)) (P * X ^ (d / 2))

/-- Forced multiplier relating native source to first Padé defect. -/
def xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier
    (n d : ℕ) : ℝ :=
  if d % 2 = 0 then ((2 * n + d : ℕ) : ℝ) else 2

/-- The parity-selected native source is exactly the first Padé defect times its forced positive
multiplier. -/
theorem xiShiftedAdaptiveMixedCompletedFirstContactSourceValue_eq_multiplier_mul_defect
    {w : ℝ} {n d : ℕ} {c : Fin (n + 1) → ℝ}
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw w n d c) :
    xiShiftedAdaptiveMixedCompletedFirstContactSourceValue w n d c =
      xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier n d *
        xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d) := by
  dsimp only [XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw] at hsource
  rcases hsource with heven | hodd
  · obtain ⟨r, _hr, hd, hvalue, _hpos⟩ := heven
    have hmod : d % 2 = 0 := by omega
    have hhalf : d / 2 = r := by omega
    simp only [xiShiftedAdaptiveMixedCompletedFirstContactSourceValue,
      xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier, hmod, ↓reduceIte,
      hhalf, hvalue]
  · obtain ⟨r, hd, hvalue, _hpos⟩ := hodd
    have hmod : d % 2 ≠ 0 := by omega
    have hhalf : d / 2 = r := by omega
    simp only [xiShiftedAdaptiveMixedCompletedFirstContactSourceValue,
      xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier, hmod, ↓reduceIte,
      hhalf, hvalue]

/-- Right-chamber contact orientation makes the parity-selected native source strictly positive
after inserting the intrinsic contact sign. -/
theorem xiShiftedAdaptiveMixedCompletedFirstContactSourceValue_signed_pos
    {w : ℝ} {n d : ℕ} {c : Fin (n + 1) → ℝ}
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw w n d c) :
    0 < (-1 : ℝ) ^ d *
      xiShiftedAdaptiveMixedCompletedFirstContactSourceValue w n d c := by
  dsimp only [XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw] at hsource
  rcases hsource with heven | hodd
  · obtain ⟨r, _hr, hd, _hvalue, hpos⟩ := heven
    have hmod : d % 2 = 0 := by omega
    have hhalf : d / 2 = r := by omega
    simpa only [xiShiftedAdaptiveMixedCompletedFirstContactSourceValue, hmod, ↓reduceIte,
      hhalf] using hpos
  · obtain ⟨r, hd, _hvalue, hpos⟩ := hodd
    have hmod : d % 2 ≠ 0 := by omega
    have hhalf : d / 2 = r := by omega
    simpa only [xiShiftedAdaptiveMixedCompletedFirstContactSourceValue, hmod, ↓reduceIte,
      hhalf] using hpos

/-- **Defect cancellation.**  Native signed source and newborn-norm contact coefficient contain
the same first defect.  Their division-free ratio is purely combinatorial. -/
theorem choose_mul_signed_xiShiftedAdaptiveMixedCompletedFirstContactSourceValue
    {w : ℝ} {n d : ℕ} {c : Fin (n + 1) → ℝ}
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw w n d c) :
    (Nat.choose (2 * n + d) d : ℝ) *
        ((-1 : ℝ) ^ d *
          xiShiftedAdaptiveMixedCompletedFirstContactSourceValue w n d c) =
      xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier n d *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect (w ^ 2) c (2 * n + d)) := by
  rw [xiShiftedAdaptiveMixedCompletedFirstContactSourceValue_eq_multiplier_mul_defect
    hsource]
  ring

/-- Native source selected by the first contact at canonical strict frontier `n`. -/
noncomputable def xiShiftedStrictFrontierNativeContactSourceValue
    (n d : ℕ) : ℝ :=
  xiShiftedAdaptiveMixedCompletedFirstContactSourceValue
    (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
    (xiShiftedStrictFrontierNullVector n)

/-- Signed native source divided by moving newborn norm, scaled by intrinsic contact order. -/
noncomputable def xiShiftedStrictFrontierScaledNativeContactSourceResidue
    (n d : ℕ) (u : ℝ) : ℝ :=
  u ^ d * ((-1 : ℝ) ^ d * xiShiftedStrictFrontierNativeContactSourceValue n d) /
    xiShiftedCanonicalAdmissionNorm
      (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2)

/-- Universal residue left after native arithmetic source and newborn admission coefficient cancel
their common first Padé defect. -/
noncomputable def xiShiftedStrictFrontierNativeContactUniversalResidue
    (n d : ℕ) : ℝ :=
  xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d /
    (Nat.choose (2 * (n + 2) + d) d : ℝ)

/-- **Exact native arithmetic contact residue.**  The scaled signed native completed source divided
by moving newborn norm tends to a positive universal combinatorial value.  First-defect magnitude
cancels exactly. -/
theorem tendsto_xiShiftedStrictFrontierScaledNativeContactSourceResidue
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    Tendsto (xiShiftedStrictFrontierScaledNativeContactSourceResidue n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierNativeContactUniversalResidue n d)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  let S := (-1 : ℝ) ^ d * xiShiftedStrictFrontierNativeContactSourceValue n d
  let q : ℝ := Nat.choose (2 * (n + 2) + d) d
  let M := xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d
  let C := xiShiftedStrictFrontierAdmissionNormContactCoefficient n d
  have hqNat : 0 < Nat.choose (2 * (n + 2) + d) d := Nat.choose_pos (by omega)
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hC : 0 < C := by
    simpa only [C] using xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos hsigned
  have hbalance : q * S = M * C := by
    have hraw :=
      choose_mul_signed_xiShiftedAdaptiveMixedCompletedFirstContactSourceValue hsource
    have hy0 : 0 ≤ y := by
      obtain ⟨v, hv⟩ := hne
      have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
      exact le_of_lt (lt_of_le_of_lt (hv.1.trans hvle) hstrict)
    rw [Real.sq_sqrt hy0] at hraw
    simpa only [q, S, M, C, y, xiShiftedStrictFrontierNativeContactSourceValue,
      xiShiftedStrictFrontierAdmissionNormContactCoefficient,
      xiShiftedStrictFrontierPadeDefect, xiShiftedStrictFrontierNullVector] using hraw
  have hN : Tendsto (fun u : ℝ => N (y + u) / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [N, y, C, xiShiftedStrictFrontierAdmissionNormContactCoefficient] using
      tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
        hne hstrict hd hzero
  have hInv : Tendsto (fun u : ℝ => (N (y + u) / u ^ d)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 C⁻¹) := hN.inv₀ hC.ne'
  have hlimit : S * C⁻¹ = M / q := by
    field_simp [hC.ne', hq.ne']
    nlinarith [hbalance]
  have hprod : Tendsto (fun u : ℝ => S * (N (y + u) / u ^ d)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (M / q)) := by
    have ht : Tendsto (fun u : ℝ => S * (N (y + u) / u ^ d)⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 (S * C⁻¹)) := tendsto_const_nhds.mul hInv
    simpa only [hlimit] using ht
  have hNpos := eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier
    hne hstrict
  apply hprod.congr'
  filter_upwards [hNpos, self_mem_nhdsWithin] with u hNu hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hNu0 : N (y + u) ≠ 0 := by simpa only [N, y] using ne_of_gt hNu
  dsimp only [xiShiftedStrictFrontierScaledNativeContactSourceResidue,
    xiShiftedStrictFrontierNativeContactUniversalResidue, S, N, y, M, q]
  field_simp

/-- Universal native contact residue is strictly positive. -/
theorem xiShiftedStrictFrontierNativeContactUniversalResidue_pos
    {n d : ℕ} (hd : 0 < d) :
    0 < xiShiftedStrictFrontierNativeContactUniversalResidue n d := by
  have hqNat : 0 < Nat.choose (2 * (n + 2) + d) d := Nat.choose_pos (by omega)
  have hq : 0 < (Nat.choose (2 * (n + 2) + d) d : ℝ) := by exact_mod_cast hqNat
  rw [xiShiftedStrictFrontierNativeContactUniversalResidue]
  apply div_pos _ hq
  rw [xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier]
  split_ifs
  · positivity
  · norm_num

/-- Simple odd contact and first even contact carry the same harmonic source/admission price. -/
theorem xiShiftedStrictFrontierNativeContactUniversalResidue_one
    (n : ℕ) :
    xiShiftedStrictFrontierNativeContactUniversalResidue n 1 =
      2 / ((2 * (n + 2) + 1 : ℕ) : ℝ) := by
  simp [xiShiftedStrictFrontierNativeContactUniversalResidue,
    xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier]

/-- First even contact has exactly the simple-contact price `2/(2m+1)`, with `m=n+2`. -/
theorem xiShiftedStrictFrontierNativeContactUniversalResidue_two
    (n : ℕ) :
    xiShiftedStrictFrontierNativeContactUniversalResidue n 2 =
      2 / ((2 * (n + 2) + 1 : ℕ) : ℝ) := by
  rw [xiShiftedStrictFrontierNativeContactUniversalResidue,
    xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier]
  simp only [Nat.reduceMod, ↓reduceIte]
  have hchoose : Nat.choose (2 * (n + 2) + 2) 2 = (n + 3) * (2 * n + 5) := by
    have hN : 2 * (n + 2) + 2 = 2 * (n + 3) := by omega
    have hNm1 : 2 * (n + 3) - 1 = 2 * n + 5 := by omega
    rw [Nat.choose_two_right]
    calc
      (2 * (n + 2) + 2) * (2 * (n + 2) + 2 - 1) / 2 =
          (2 * (n + 3)) * (2 * n + 5) / 2 := by rw [hN, hNm1]
      _ = ((n + 3) * (2 * n + 5)) * 2 / 2 := by congr 1; ring
      _ = (n + 3) * (2 * n + 5) := Nat.mul_div_left _ (by decide)
  rw [hchoose]
  have hn3 : (0 : ℝ) < n + 3 := by positivity
  push_cast
  field_simp
  ring

/-- Admission/contact counterweight forced by exact newborn-norm coefficient. -/
noncomputable def xiShiftedStrictFrontierNativeContactAdmissionWeight
    (n d : ℕ) : ℝ :=
  (Nat.choose (2 * (n + 2) + d) d : ℝ) /
    xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d

/-- **Universal unit charge.**  Exact admission weight converts parity-native arithmetic residue
to one, for every finite positive contact order. -/
theorem xiShiftedStrictFrontierNativeContactAdmissionWeight_mul_residue_eq_one
    (n : ℕ) {d : ℕ} (hd : 0 < d) :
    xiShiftedStrictFrontierNativeContactAdmissionWeight n d *
      xiShiftedStrictFrontierNativeContactUniversalResidue n d = 1 := by
  have hqNat : 0 < Nat.choose (2 * (n + 2) + d) d := Nat.choose_pos (by omega)
  have hq : (Nat.choose (2 * (n + 2) + d) d : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hqNat)
  have hM : xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d ≠ 0 := by
    rw [xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier]
    split_ifs
    · positivity
    · norm_num
  rw [xiShiftedStrictFrontierNativeContactAdmissionWeight,
    xiShiftedStrictFrontierNativeContactUniversalResidue]
  field_simp

/-- Every actual strict-frontier native contact has unit residue after its forced
admission/contact normalization. -/
theorem tendsto_xiShiftedStrictFrontierNativeContactUnitCharge
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    Tendsto
      (fun u => xiShiftedStrictFrontierNativeContactAdmissionWeight n d *
        xiShiftedStrictFrontierScaledNativeContactSourceResidue n d u)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : Tendsto
      (fun _u : ℝ => xiShiftedStrictFrontierNativeContactAdmissionWeight n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierNativeContactAdmissionWeight n d)) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_xiShiftedStrictFrontierScaledNativeContactSourceResidue
      hne hstrict hd hzero hsigned hsource)
  simpa only [xiShiftedStrictFrontierNativeContactAdmissionWeight_mul_residue_eq_one n hd]
    using h

/-- **Native source is exact first newborn-determinant jet.**  At canonical strict frontier, the
parity-selected adaptive completed source is not only asymptotic residue data.  After forced
integer scaling it equals the first live iterated derivative of newborn Hankel determinant,
weighted by positive head determinant.  This is division-free and source-first. -/
theorem multiplier_mul_iteratedDeriv_strictFrontierNewbornDet_eq_nativeSource
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d *
        iteratedDeriv d
          (fun u : ℝ => (xiShiftedMomentHankelMatrix
            (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 3)).det) 0 =
      d.factorial *
        (xiShiftedMomentHankelMatrix
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2)).det *
        (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        ((-1 : ℝ) ^ d * xiShiftedStrictFrontierNativeContactSourceValue n d) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) (m + 1)
  let coeff : ℕ → ℝ := fun j => PowerSeries.coeff j A.det
  let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (m + 1)).det
  let q : ℝ := Nat.choose (2 * m + d) d
  let M := xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier m d
  let S := (-1 : ℝ) ^ d * xiShiftedStrictFrontierNativeContactSourceValue n d
  let C := (-1 : ℝ) ^ d * q * xiShiftedStrictFrontierPadeDefect n (2 * m + d)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef := by
    simpa only [y, m] using hface.1
  have hflat : xiShiftedMomentHankelMatrix y (m + 1) *ᵥ c = 0 := by
    have h := xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
    simpa only [y, m, c, xiShiftedStrictFrontierNullVector, Nat.add_assoc] using h
  have hlast : c (Fin.last m) ≠ 0 := by
    simp [c, xiShiftedStrictFrontierNullVector, m]
  have hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ coeff) 0 := by
    simpa only [f, coeff, A, xiShiftedHankelDetFPowerSeries] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (m + 1))
  have hjet : iteratedDeriv d f 0 = d.factorial * coeff d :=
    iteratedDeriv_eq_factorial_mul_coeff_of_hasFPowerSeriesAt hf d
  have hcoeff : coeff d =
      (xiShiftedMomentHankelMatrix y m).det * C := by
    dsimp only [coeff, A, C, q]
    have hzero' : ∀ k < 2 * m + d,
        xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
      intro k hk
      simpa only [m, c, y, xiShiftedStrictFrontierPadeDefect,
        xiShiftedStrictFrontierNullVector] using hzero k hk
    simpa only [m, c, y, xiShiftedStrictFrontierPadeDefect,
      xiShiftedStrictFrontierNullVector] using
      (coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
        c hhead hflat hlast hd hzero')
  have hbalance : q * S = M * C := by
    have hraw :=
      choose_mul_signed_xiShiftedAdaptiveMixedCompletedFirstContactSourceValue hsource
    have hy0 : 0 ≤ y := le_of_lt hy
    rw [Real.sq_sqrt hy0] at hraw
    simpa only [q, S, M, C, m, c, y,
      xiShiftedStrictFrontierNativeContactSourceValue,
      xiShiftedStrictFrontierPadeDefect, xiShiftedStrictFrontierNullVector] using hraw
  rw [hcoeff] at hjet
  change M * iteratedDeriv d f 0 = d.factorial *
    (xiShiftedMomentHankelMatrix y m).det * q * S
  rw [hjet]
  calc
    M * (d.factorial * ((xiShiftedMomentHankelMatrix y m).det * C)) =
        d.factorial * (xiShiftedMomentHankelMatrix y m).det * (M * C) := by ring
    _ = d.factorial * (xiShiftedMomentHankelMatrix y m).det * (q * S) := by
      rw [hbalance]
    _ = d.factorial * (xiShiftedMomentHankelMatrix y m).det * q * S := by ring

/-- Source-first contact orientation makes the first live newborn determinant jet strictly
positive, independent of parity. -/
theorem iteratedDeriv_strictFrontierNewbornDet_pos_of_nativeSource
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsource : XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)) :
    0 < iteratedDeriv d
      (fun u : ℝ => (xiShiftedMomentHankelMatrix
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 3)).det) 0 := by
  have heq := multiplier_mul_iteratedDeriv_strictFrontierNewbornDet_eq_nativeSource
    hne hstrict hd hzero hsource
  have hS := xiShiftedAdaptiveMixedCompletedFirstContactSourceValue_signed_pos hsource
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  have hdet : 0 < (xiShiftedMomentHankelMatrix
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2)).det := hface.1.det_pos
  have hqNat : 0 < Nat.choose (2 * (n + 2) + d) d := Nat.choose_pos (by omega)
  have hq : 0 < (Nat.choose (2 * (n + 2) + d) d : ℝ) := by
    exact_mod_cast hqNat
  have hfact : 0 < (d.factorial : ℝ) := by positivity
  have hM : 0 < xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d := by
    rw [xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier]
    split_ifs
    · positivity
    · norm_num
  have hprod : 0 < xiShiftedAdaptiveMixedCompletedFirstContactSourceMultiplier (n + 2) d *
      iteratedDeriv d
        (fun u : ℝ => (xiShiftedMomentHankelMatrix
          (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 3)).det) 0 := by
    rw [heq]
    exact mul_pos (mul_pos (mul_pos hfact hdet) hq) hS
  exact pos_of_mul_pos_right hprod hM.le

/-- Every lower newborn determinant jet vanishes before first native arithmetic contact. -/
theorem iteratedDeriv_strictFrontierNewbornDet_eq_zero_of_lt_contact
    {n d j : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hjd : j < d) :
    iteratedDeriv j
      (fun u : ℝ => (xiShiftedMomentHankelMatrix
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 3)).det) 0 = 0 := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let c := xiShiftedStrictFrontierNullVector n
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y m).PosDef := by
    simpa only [y, m] using hface.1
  have hflat : xiShiftedMomentHankelMatrix y (m + 1) *ᵥ c = 0 := by
    have h := xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
    simpa only [y, m, c, xiShiftedStrictFrontierNullVector, Nat.add_assoc] using h
  have hlast : c (Fin.last m) ≠ 0 := by
    simp [c, xiShiftedStrictFrontierNullVector, m]
  by_cases hj0 : j = 0
  · subst j
    simp only [iteratedDeriv_zero, add_zero]
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hflat
      (i := Fin.last m)
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hlast
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hzero' : ∀ k < 2 * m + j,
        xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
      intro k hk
      simpa only [m, c, y, xiShiftedStrictFrontierPadeDefect,
        xiShiftedStrictFrontierNullVector] using hzero k (by omega)
    have hjet := iteratedDeriv_det_xiShiftedMomentHankelMatrix_add_at_firstPadeContact
      hy c hhead hflat hlast hjpos hzero'
    have hdefect : xiShiftedHankelBoundaryPadeDefect y c (2 * m + j) = 0 := by
      simpa only [m, c, y, xiShiftedStrictFrontierPadeDefect,
        xiShiftedStrictFrontierNullVector] using hzero (2 * (n + 2) + j) (by omega)
    rw [hdefect, mul_zero, mul_zero] at hjet
    simpa only [m, y] using hjet

end

end RHTower
