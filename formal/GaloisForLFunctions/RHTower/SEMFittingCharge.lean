/-
# The integral Fitting charge of an actual symmetric-EM hole

The symmetrized Euler-Maclaurin annulus supply produces `SEMSplitData` unconditionally,
and its finite hole count is exactly the vanishing order of `xi` at the centre.  The
integral divisor-jet lattice already carries an explicit `ZMod n` charge.  This module
joins those two theorem islands.

To a genuine split with hole list `zs`, attach an algebraic standard integral unipotent defect
with parameter `-zs.length`.  Its Fitting class is the constant jet of `zs.length`, so
the integral jet charge reads precisely the hole count modulo `n`.  Thus every RH
ladder rung is equivalent to vanishing of one concrete integral Fitting charge of every
actual symmetric-EM split.

The attached matrix is a canonical algebraic model of the count; this module does not identify it
with a defect produced by the analytic gluing construction.  Nor does it assume or assert that the
charge vanishes.  The missing theorem is therefore a realization-and-annihilation law for an actual
arithmetic/analytic seam, rather than merely a vanishing statement about the attached matrix.
-/
import GaloisForLFunctions.RHTower.SymmetrizedEMCarrier
import GaloisForLFunctions.RHTower.IntegralJetCharge
import GaloisForLFunctions.RHTower.FittingDeckChargeBarrier

namespace RHTower

open Polynomial

noncomputable section

/-- An algebraic integral unipotent defect canonically labelled by the hole count of an actual
symmetrized Euler-Maclaurin split.  No analytic-seam realization is asserted here. -/
def semHoleDefectZ {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (_h : SEMSplitData ρ r₀ R N zs u) : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  seamDefZ (-(zs.length : ℤ))

/-- The attached algebraic defect is independent of the annulus, truncation, factorization, and
hole-list representative at a fixed centre.  Count rigidity makes the model an invariant of the
central ξ-germ, despite being constructed from finite-member data. -/
theorem semHoleDefectZ_rigid {ρ : ℂ}
    {r₀ R r₀' R' : ℝ} {N N' : ℕ} {zs zs' : List ℂ} {u u' : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) (h' : SEMSplitData ρ r₀' R' N' zs' u') :
    semHoleDefectZ h = semHoleDefectZ h' := by
  have hlen : zs.length = zs'.length := by
    rw [← semSplitData_count_eq h, ← semSplitData_count_eq h']
  simp only [semHoleDefectZ, hlen]

/-- Intrinsically, the attached defect is the integral unipotent defect labelled by the finite
analytic order of the ξ-germ at the centre. -/
theorem semHoleDefectZ_eq_xiOrder {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u) :
    semHoleDefectZ h = seamDefZ (-((analyticOrderAt xi ρ).toNat : ℤ)) := by
  rw [semHoleDefectZ, semSplitData_count_eq h]

/-- The Fitting class of the SEM hole defect is the constant integral jet of its hole count. -/
theorem semHoleDefectZ_fittingClass {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u) (m : ℕ) :
    fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h) =
      jetClass ℤ m (C (zs.length : ℤ)) := by
  rw [semHoleDefectZ, fittingClass_seamDefZ]
  congr 1
  simp

/-- The integral Fitting charge reads exactly the finite member's hole count modulo `n`. -/
theorem integralJetCharge_semHoleDefectZ {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u)
    {m n : ℕ} (hm : 1 ≤ m) :
    integralJetCharge m n hm
        (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h)) =
      (zs.length : ZMod n) := by
  rw [semHoleDefectZ_fittingClass, integralJetCharge_jetClass, coeffZeroRingHomZ_C]
  norm_cast

/-- Charge vanishing is exactly divisibility of the symmetric member's hole count. -/
theorem integralJetCharge_semHoleDefectZ_eq_zero_iff {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u)
    {m n : ℕ} (hm : 1 ≤ m) :
    integralJetCharge m n hm
        (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h)) = 0 ↔
      n ∣ zs.length := by
  rw [integralJetCharge_semHoleDefectZ h hm, ZMod.natCast_eq_zero_iff]

/-- For an actual SEM split, the integral Fitting charge is the central ξ-order modulo `n`. -/
theorem integralJetCharge_semHoleDefectZ_eq_xiOrder {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u)
    {m n : ℕ} (hm : 1 ≤ m) :
    integralJetCharge m n hm
        (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h)) =
      ((analyticOrderAt xi ρ).toNat : ZMod n) := by
  rw [integralJetCharge_semHoleDefectZ h hm, semSplitData_count_eq h]

/-- Level `k` of the RH ladder is exactly vanishing of the depth-one integral Fitting charge
modulo `2^k` for every actual symmetric-EM split at every hypothetical right-half zero. -/
theorem rhLadder_iff_semHoleFittingCharge_zero (k : ℕ) :
    RHLadder k ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          integralJetCharge 1 (2 ^ k) (by omega)
              (fittingBoundaryClass 1 (standardPresZ 1) (semHoleDefectZ h)) = 0 := by
  rw [rhLadder_iff_toNat_dvd]
  constructor
  · intro hlad ρ hρ hzero r₀ R N zs u h
    rw [integralJetCharge_semHoleDefectZ_eq_zero_iff h (by omega)]
    rw [← semSplitData_count_eq h]
    exact hlad ρ hρ hzero
  · intro h ρ hρ hzero
    have h0 : 0 < ρ.re := lt_trans (by norm_num) (mem_rightHalf.mp hρ)
    obtain ⟨r₀, R, N, zs, u, hdata⟩ :=
      semSplitData_exists ρ h0 (xi_zero_re_lt_one hzero)
    have hcharge := h ρ hρ hzero r₀ R N zs u hdata
    have hdvd := (integralJetCharge_semHoleDefectZ_eq_zero_iff hdata (by omega)).mp hcharge
    rwa [← semSplitData_count_eq hdata] at hdvd

/-- RH is exactly all-level annihilation of the concrete integral Fitting charges attached to
the unconditional symmetric-EM split supply. -/
theorem riemannHypothesis_iff_all_semHoleFittingCharges_zero :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          integralJetCharge 1 (2 ^ k) (by omega)
              (fittingBoundaryClass 1 (standardPresZ 1) (semHoleDefectZ h)) = 0 := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' rhLadder_iff_semHoleFittingCharge_zero

/-! ### The additive base-change barrier -/

/-- Base change sends an arbitrary integral constant jet to the corresponding rational one. -/
theorem baseChangeZQ_constJet_int (m : ℕ) (t : ℤ) :
    baseChangeZQ m (jetClass ℤ m (C t)) = jetClass ℚ m (C (t : ℚ)) := by
  rw [jetClass, baseChangeZQ, Ideal.Quotient.lift_mk, jetClass]
  simp

/-- Every additive finite charge on the rational jet algebra kills the base-changed SEM hole
class.  The analytic/divisible coefficient channel therefore cannot read the integral charge. -/
theorem rat_additive_charge_baseChange_semHole_eq_zero {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u)
    {m n : ℕ} [NeZero n] (φ : LocalDivisorJet ℚ m →+ ZMod n) :
    φ (baseChangeZQ m
      (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h))) = 0 := by
  rw [semHoleDefectZ_fittingClass, baseChangeZQ_constJet_int]
  exact addHom_rat_zmod_eq_zero (φ.comp (constJetHom m)) (zs.length : ℚ)

/-- If the SEM hole count is nonzero modulo `n`, its integral Fitting charge cannot factor through
the rational jet algebra.  Thus the remaining annihilation law must preserve integral arithmetic
before scalar extension or use a non-additive channel; analytic additive naturality is impossible. -/
theorem semHole_integral_charge_not_factor_through_rat_of_not_dvd
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m n : ℕ} (hm : 1 ≤ m)
    [NeZero n] (hnot : ¬n ∣ zs.length) :
    ¬ ∃ φ : LocalDivisorJet ℚ m →+ ZMod n,
      φ (baseChangeZQ m
          (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h))) =
        integralJetCharge m n hm
          (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h)) := by
  rintro ⟨φ, hφ⟩
  have hrat := rat_additive_charge_baseChange_semHole_eq_zero h φ
  have hint : integralJetCharge m n hm
      (fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h)) ≠ 0 := by
    intro hz
    exact hnot ((integralJetCharge_semHoleDefectZ_eq_zero_iff h hm).mp hz)
  exact hint (hφ ▸ hrat)

/-! ### The non-additive determinant target -/

/-- Adding the SEM hole defect to the sheared integral presentation changes its determinant from
`X^m` to `X^m + zs.length`.  The integral Fitting charge is the constant determinant defect. -/
theorem det_standardPresZ_add_semHoleDefectZ {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u) (m : ℕ) :
    (standardPresZ m + semHoleDefectZ h).det =
      (X : Polynomial ℤ) ^ m + C (zs.length : ℤ) := by
  rw [standardPresZ, semHoleDefectZ, seamDefZ, Matrix.det_fin_two]
  simp [Matrix.add_apply]

/-- For positive jet depth, determinant preservation modulo the pinned divisor `X^m` is equivalent
to the absence of every SEM hole zero.  This is the exact non-additive conservation law that would
annihilate all integral charges; it remains to derive it from arithmetic rather than assume it. -/
theorem X_pow_dvd_det_standardPresZ_add_semHoleDefectZ_iff {ρ : ℂ}
    {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m : ℕ} (hm : 1 ≤ m) :
    (X : Polynomial ℤ) ^ m ∣ (standardPresZ m + semHoleDefectZ h).det ↔
      zs.length = 0 := by
  rw [det_standardPresZ_add_semHoleDefectZ]
  constructor
  · rintro ⟨q, hq⟩
    have hm0 : m ≠ 0 := by omega
    have heval := congrArg (Polynomial.eval 0) hq
    have hlenZ : (zs.length : ℤ) = 0 := by
      simpa [hm0] using heval
    exact_mod_cast hlenZ
  · intro hzero
    rw [hzero]
    simp

/-- Failure of one ladder rung is exactly the existence of an actual symmetric-EM split carrying
a nonzero integral Fitting charge at that dyadic level.  The obstruction is therefore a concrete
finite member and integral seam, not an abstract hypothetical divisor count. -/
theorem not_rhLadder_iff_exists_semHoleFittingCharge_ne_zero (k : ℕ) :
    ¬RHLadder k ↔
      ∃ ρ ∈ rightHalf, xi ρ = 0 ∧
        ∃ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          integralJetCharge 1 (2 ^ k) (by omega)
              (fittingBoundaryClass 1 (standardPresZ 1) (semHoleDefectZ h)) ≠ 0 := by
  classical
  rw [rhLadder_iff_toNat_dvd]
  constructor
  · push Not
    rintro ⟨ρ, hρ, hzero, hnotdvd⟩
    have h0 : 0 < ρ.re := lt_trans (by norm_num) (mem_rightHalf.mp hρ)
    obtain ⟨r₀, R, N, zs, u, hdata⟩ :=
      semSplitData_exists ρ h0 (xi_zero_re_lt_one hzero)
    refine ⟨ρ, hρ, hzero, r₀, R, N, zs, u, hdata, ?_⟩
    intro hcharge
    have hdvd := (integralJetCharge_semHoleDefectZ_eq_zero_iff hdata (by omega)).mp hcharge
    exact hnotdvd (by rwa [← semSplitData_count_eq hdata] at hdvd)
  · rintro ⟨ρ, hρ, hzero, r₀, R, N, zs, u, hdata, hcharge⟩ hlad
    have hdvd := hlad ρ hρ hzero
    have hz : integralJetCharge 1 (2 ^ k) (by omega)
        (fittingBoundaryClass 1 (standardPresZ 1) (semHoleDefectZ hdata)) = 0 :=
      (integralJetCharge_semHoleDefectZ_eq_zero_iff hdata (by omega)).mpr
        (by rwa [← semSplitData_count_eq hdata])
    exact hcharge hz

/-- Failure of RH is exactly a nonzero integral Fitting charge on one unconditional
symmetrized-EM split at one dyadic level. -/
theorem not_riemannHypothesis_iff_exists_semHoleFittingCharge_ne_zero :
    ¬RiemannHypothesis ↔
      ∃ k : ℕ, ∃ ρ ∈ rightHalf, xi ρ = 0 ∧
        ∃ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          integralJetCharge 1 (2 ^ k) (by omega)
              (fittingBoundaryClass 1 (standardPresZ 1) (semHoleDefectZ h)) ≠ 0 := by
  classical
  rw [rh_iff_forall_ladder]
  push Not
  exact exists_congr fun k => not_rhLadder_iff_exists_semHoleFittingCharge_ne_zero k

end

end RHTower
