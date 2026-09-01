import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinFundamentalSymmetry
import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightGreen
import GaloisForLFunctions.RHTower.GammaValuationSchurKotheVectorNoGoDualSurvivor

/-!
# Tame trivialization of source-horizontal rigged Krein fibres

The Bockstein weights vary with the horizontal spectral coordinate, but away from the critical
wall that variation is a tame diagonal change of coordinates on the fixed Deninger height--Köthe
source.  Within either open half-strip the change is an exact congruence of the full rigged Witt
pairing; across the wall it is an anti-congruence.

Consequently every producer depending only on the pointwise topological Krein-isomorphism class
is constant within a half-strip and cannot force the critical wall.  Fixed source coordinates and
cross-fibre relative data are the sharp survivors.
-/

open Complex
namespace RHTower
noncomputable section

open PreDivisorReflectionDefectStabilization

def riggedPrimeAxisIndex (m : DeningerPrimeLattice) : Nat.Primes :=
  Function.invFun preDivisorRiggedPrimeAxis m

theorem riggedPrimeAxisIndex_axis (p : Nat.Primes) :
    riggedPrimeAxisIndex (preDivisorRiggedPrimeAxis p) = p := by
  exact Function.leftInverse_invFun preDivisorRiggedPrimeAxis_injective p

def riggedPrimeWeightScale (s t : ℂ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (preDivisorRiggedPrimeWeight s p) /
    Real.sqrt (preDivisorRiggedPrimeWeight t p)

def riggedPrimeFibreMultiplier (s t : ℂ) (m : DeningerPrimeLattice) : ℂ :=
  if preDivisorRiggedPrimeAxis (riggedPrimeAxisIndex m) = m then
    (riggedPrimeWeightScale s t (riggedPrimeAxisIndex m) : ℂ)
  else 1

@[simp] theorem riggedPrimeFibreMultiplier_axis (s t : ℂ) (p : Nat.Primes) :
    riggedPrimeFibreMultiplier s t (preDivisorRiggedPrimeAxis p) =
      (riggedPrimeWeightScale s t p : ℂ) := by
  rw [riggedPrimeFibreMultiplier, riggedPrimeAxisIndex_axis]
  simp

theorem riggedPrimeWeightScale_pos
    (s t : ℂ) (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (p : Nat.Primes) :
    0 < riggedPrimeWeightScale s t p := by
  rw [riggedPrimeWeightScale]
  exact div_pos
    (Real.sqrt_pos.2 (preDivisorRiggedPrimeWeight_pos_of_offWall s hs p))
    (Real.sqrt_pos.2 (preDivisorRiggedPrimeWeight_pos_of_offWall t ht p))

theorem sqrt_weight_mul_riggedPrimeWeightScale
    (s t : ℂ) (ht : t.re ≠ 1 / 2) (p : Nat.Primes) :
    Real.sqrt (preDivisorRiggedPrimeWeight t p) *
        riggedPrimeWeightScale s t p =
      Real.sqrt (preDivisorRiggedPrimeWeight s p) := by
  rw [riggedPrimeWeightScale]
  field_simp [ne_of_gt (Real.sqrt_pos.2
    (preDivisorRiggedPrimeWeight_pos_of_offWall t ht p))]

theorem riggedPrimeWeightScale_mul_reverse
    (s t : ℂ) (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (p : Nat.Primes) :
    riggedPrimeWeightScale s t p * riggedPrimeWeightScale t s p = 1 := by
  rw [riggedPrimeWeightScale, riggedPrimeWeightScale]
  field_simp [ne_of_gt (Real.sqrt_pos.2
      (preDivisorRiggedPrimeWeight_pos_of_offWall s hs p)),
    ne_of_gt (Real.sqrt_pos.2
      (preDivisorRiggedPrimeWeight_pos_of_offWall t ht p))]

theorem weight_mul_riggedPrimeWeightScale_sq
    (s t : ℂ) (ht : t.re ≠ 1 / 2) (p : Nat.Primes) :
    preDivisorRiggedPrimeWeight t p * riggedPrimeWeightScale s t p ^ 2 =
      preDivisorRiggedPrimeWeight s p := by
  have hws : 0 ≤ preDivisorRiggedPrimeWeight s p := abs_nonneg _
  have hwt : 0 ≤ preDivisorRiggedPrimeWeight t p := abs_nonneg _
  rw [riggedPrimeWeightScale, div_pow,
    Real.sq_sqrt hws, Real.sq_sqrt hwt]
  field_simp [ne_of_gt (preDivisorRiggedPrimeWeight_pos_of_offWall t ht p)]

theorem riggedPrimeFibreMultiplier_mul_reverse
    (s t : ℂ) (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (m : DeningerPrimeLattice) :
    riggedPrimeFibreMultiplier s t m * riggedPrimeFibreMultiplier t s m = 1 := by
  rw [riggedPrimeFibreMultiplier, riggedPrimeFibreMultiplier]
  by_cases h : preDivisorRiggedPrimeAxis (riggedPrimeAxisIndex m) = m
  · rw [if_pos h, if_pos h]
    exact_mod_cast riggedPrimeWeightScale_mul_reverse s t hs ht (riggedPrimeAxisIndex m)
  · rw [if_neg h, if_neg h, one_mul]

def riggedPrimeWeightLowerConstant (s : ℂ) : ℝ :=
  (1 / 4 : ℝ) *
    (1 - (2 : ℝ) ^ (-2 * |preDivisorCenteredRate s|))

theorem riggedPrimeWeightLowerConstant_pos
    (s : ℂ) (hs : s.re ≠ 1 / 2) :
    0 < riggedPrimeWeightLowerConstant s := by
  have hrate : preDivisorCenteredRate s ≠ 0 := by
    intro h
    rw [preDivisorCenteredRate] at h
    apply hs
    linarith
  have habs : 0 < |preDivisorCenteredRate s| := abs_pos.mpr hrate
  have hpow : (2 : ℝ) ^ (-2 * |preDivisorCenteredRate s|) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  rw [riggedPrimeWeightLowerConstant]
  positivity

theorem riggedPrimeWeightLowerConstant_mul_inv_prime_le
    (s : ℂ) (p : Nat.Primes) :
    riggedPrimeWeightLowerConstant s * ((p : ℝ)⁻¹) ≤
      preDivisorRiggedPrimeWeight s p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hexp : (-1 : ℝ) ≤ |preDivisorCenteredRate s| - 1 := by
    linarith [abs_nonneg (preDivisorCenteredRate s)]
  have hpow : ((p : ℝ)⁻¹) ≤
      (p : ℝ) ^ (|preDivisorCenteredRate s| - 1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1 hexp
  have hc : 0 ≤ riggedPrimeWeightLowerConstant s := by
    rw [riggedPrimeWeightLowerConstant]
    have hpowle : (2 : ℝ) ^ (-2 * |preDivisorCenteredRate s|) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by nlinarith [abs_nonneg (preDivisorCenteredRate s)])
    nlinarith
  calc
    riggedPrimeWeightLowerConstant s * ((p : ℝ)⁻¹) ≤
        riggedPrimeWeightLowerConstant s *
          (p : ℝ) ^ (|preDivisorCenteredRate s| - 1) :=
      mul_le_mul_of_nonneg_left hpow hc
    _ ≤ preDivisorRiggedPrimeWeight s p := by
      simpa [riggedPrimeWeightLowerConstant, preDivisorRiggedPrimeWeight,
        preDivisorPrimeCarrier, primeGammaCofinalBocksteinMagnitude,
        primeGammaCofinalBocksteinCoefficient] using
          (primeGammaCofinalBocksteinMagnitude_bounds
            (preDivisorCenteredRate s) p).1

theorem riggedPrimeWeightScale_le_const_mul_prime
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (p : Nat.Primes) :
    riggedPrimeWeightScale s t p ≤
      (riggedPrimeWeightLowerConstant t)⁻¹ * (p : ℝ) := by
  let c := riggedPrimeWeightLowerConstant t
  have hc : 0 < c := riggedPrimeWeightLowerConstant_pos t ht
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hwt : c * (p : ℝ)⁻¹ ≤ preDivisorRiggedPrimeWeight t p :=
    riggedPrimeWeightLowerConstant_mul_inv_prime_le t p
  have hwtpos : 0 < preDivisorRiggedPrimeWeight t p :=
    preDivisorRiggedPrimeWeight_pos_of_offWall t ht p
  have hws : preDivisorRiggedPrimeWeight s p ≤ 1 :=
    (preDivisorRiggedPrimeWeight_mem_unit hsStrip p).2
  have hscale0 : 0 ≤ riggedPrimeWeightScale s t p :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htarget0 : 0 ≤ c⁻¹ * (p : ℝ) := mul_nonneg (inv_nonneg.mpr hc.le) hp.le
  apply (sq_le_sq₀ hscale0 htarget0).mp
  have hws0 : 0 ≤ preDivisorRiggedPrimeWeight s p := abs_nonneg _
  have hwt0 : 0 ≤ preDivisorRiggedPrimeWeight t p := abs_nonneg _
  rw [riggedPrimeWeightScale, div_pow,
    Real.sq_sqrt hws0, Real.sq_sqrt hwt0]
  have hratio : preDivisorRiggedPrimeWeight s p /
      preDivisorRiggedPrimeWeight t p ≤ c⁻¹ * (p : ℝ) := by
    rw [div_le_iff₀ hwtpos]
    calc
      preDivisorRiggedPrimeWeight s p ≤ 1 := hws
      _ ≤ (c⁻¹ * (p : ℝ)) * preDivisorRiggedPrimeWeight t p := by
        have hmul := mul_le_mul_of_nonneg_left hwt (inv_nonneg.mpr hc.le)
        field_simp [hc.ne'] at hmul ⊢
        nlinarith
  have hone : 1 ≤ c⁻¹ * (p : ℝ) := by
    have hc_le_one : c ≤ 1 := by
      dsimp [c]
      rw [riggedPrimeWeightLowerConstant]
      have hpow0 : 0 ≤ (2 : ℝ) ^ (-2 * |preDivisorCenteredRate t|) := by positivity
      nlinarith
    have hinv : 1 ≤ c⁻¹ := by
      have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
      have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
      nlinarith
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c⁻¹ * (p : ℝ) :=
        mul_le_mul hinv hp1 (by norm_num) (inv_nonneg.mpr hc.le)
  calc
    preDivisorRiggedPrimeWeight s p / preDivisorRiggedPrimeWeight t p ≤
        c⁻¹ * (p : ℝ) := hratio
    _ ≤ (c⁻¹ * (p : ℝ)) ^ 2 := by nlinarith

def riggedPrimeFibreMultiplierConstant (t : ℂ) : ℝ :=
  1 + (riggedPrimeWeightLowerConstant t)⁻¹

theorem riggedPrimeFibreMultiplierConstant_pos
    (t : ℂ) (ht : t.re ≠ 1 / 2) :
    0 < riggedPrimeFibreMultiplierConstant t := by
  have hc := riggedPrimeWeightLowerConstant_pos t ht
  rw [riggedPrimeFibreMultiplierConstant]
  positivity

theorem norm_riggedPrimeFibreMultiplier_le
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (m : DeningerPrimeLattice) :
    ‖riggedPrimeFibreMultiplier s t m‖ ≤
      riggedPrimeFibreMultiplierConstant t * deningerHeight m ^ 1 := by
  let c := riggedPrimeWeightLowerConstant t
  have hc : 0 < c := riggedPrimeWeightLowerConstant_pos t ht
  have hC : 1 ≤ riggedPrimeFibreMultiplierConstant t := by
    rw [riggedPrimeFibreMultiplierConstant]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
  by_cases haxis : preDivisorRiggedPrimeAxis (riggedPrimeAxisIndex m) = m
  · rw [riggedPrimeFibreMultiplier, if_pos haxis, Complex.norm_real]
    have hscale0 : 0 ≤ riggedPrimeWeightScale s t (riggedPrimeAxisIndex m) :=
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hscale0]
    have hscale := riggedPrimeWeightScale_le_const_mul_prime s t hsStrip ht
      (riggedPrimeAxisIndex m)
    have hheight : deningerHeight m = ((riggedPrimeAxisIndex m : Nat.Primes) : ℝ) := by
      calc
        deningerHeight m =
            deningerHeight (preDivisorRiggedPrimeAxis (riggedPrimeAxisIndex m)) :=
          congrArg deningerHeight haxis.symm
        _ = ((riggedPrimeAxisIndex m : Nat.Primes) : ℝ) := by
          change deningerHeight
            (gammaSewnMobiusApertureStokesPrimePowerAxis
              (riggedPrimeAxisIndex m, 0)) = _
          rw [deningerHeight_gammaValuationAxis]
          norm_num
    rw [hheight, pow_one]
    calc
      riggedPrimeWeightScale s t (riggedPrimeAxisIndex m) ≤
          c⁻¹ * ((riggedPrimeAxisIndex m : Nat.Primes) : ℝ) := hscale
      _ ≤ riggedPrimeFibreMultiplierConstant t *
          ((riggedPrimeAxisIndex m : Nat.Primes) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _
          (by exact_mod_cast (riggedPrimeAxisIndex m).2.pos.le)
        rw [riggedPrimeFibreMultiplierConstant]
        exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
  · rw [riggedPrimeFibreMultiplier, if_neg haxis, norm_one, pow_one]
    apply le_trans hC
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_deningerHeight m)
      (riggedPrimeFibreMultiplierConstant_pos t ht).le

private theorem deningerHeightMulConst_mem
    {φ : DeningerPrimeLattice → ℂ} {C : ℝ} {j : ℕ}
    (_hC : 0 ≤ C)
    (hφ : ∀ m, ‖φ m‖ ≤ C * deningerHeight m ^ j)
    (a : DeningerHeightKothe) :
    (fun m => φ m * (a : DeningerPrimeLattice → ℂ) m) ∈
      DeningerHeightKothe := by
  intro k
  have hsum := (a.2 (k + j)).mul_left C
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (deningerHeight_pos m).le _) (norm_nonneg _))
    (fun m => ?_) hsum
  show deningerHeight m ^ k * ‖φ m * (a : DeningerPrimeLattice → ℂ) m‖ ≤
      C * (deningerHeightKotheData.w (k + j) m *
        ‖(a : DeningerPrimeLattice → ℂ) m‖)
  rw [deningerHeightKotheData_w, norm_mul, pow_add]
  have hk : 0 ≤ deningerHeight m ^ k := pow_nonneg (deningerHeight_pos m).le _
  have ha : 0 ≤ ‖(a : DeningerPrimeLattice → ℂ) m‖ := norm_nonneg _
  calc
    deningerHeight m ^ k *
        (‖φ m‖ * ‖(a : DeningerPrimeLattice → ℂ) m‖) ≤
      deningerHeight m ^ k *
        ((C * deningerHeight m ^ j) *
          ‖(a : DeningerPrimeLattice → ℂ) m‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hφ m) ha) hk
    _ = C * ((deningerHeight m ^ k * deningerHeight m ^ j) *
        ‖(a : DeningerPrimeLattice → ℂ) m‖) := by ring

def deningerHeightMulConst
    (φ : DeningerPrimeLattice → ℂ) (C : ℝ) (j : ℕ)
    (hC : 0 ≤ C)
    (hφ : ∀ m, ‖φ m‖ ≤ C * deningerHeight m ^ j) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe where
  toFun a := ⟨fun m => φ m * (a : DeningerPrimeLattice → ℂ) m,
    deningerHeightMulConst_mem hC hφ a⟩
  map_add' a b := by
    ext m
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c a := by
    ext m
    change φ m * (c * (a : DeningerPrimeLattice → ℂ) m) =
      c * (φ m * (a : DeningerPrimeLattice → ℂ) m)
    ring

@[simp] theorem deningerHeightMulConst_coe
    {φ : DeningerPrimeLattice → ℂ} {C : ℝ} {j : ℕ}
    (hC : 0 ≤ C)
    (hφ : ∀ m, ‖φ m‖ ≤ C * deningerHeight m ^ j)
    (a : DeningerHeightKothe) (m : DeningerPrimeLattice) :
    ((deningerHeightMulConst φ C j hC hφ a : DeningerHeightKothe) :
      DeningerPrimeLattice → ℂ) m =
      φ m * (a : DeningerPrimeLattice → ℂ) m := rfl

theorem deningerHeightSeminorm_mulConst_le
    {φ : DeningerPrimeLattice → ℂ} {C : ℝ} {j : ℕ}
    (hC : 0 ≤ C)
    (hφ : ∀ m, ‖φ m‖ ≤ C * deningerHeight m ^ j)
    (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHeightMulConst φ C j hC hφ a) ≤
      C * deningerHeightSeminorm (k + j) a := by
  rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
  have hsum := (a.2 (k + j)).mul_left C
  calc
    ∑' m, deningerHeight m ^ k *
        ‖((deningerHeightMulConst φ C j hC hφ a : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) m‖ ≤
      ∑' m, C * (deningerHeight m ^ (k + j) *
        ‖(a : DeningerPrimeLattice → ℂ) m‖) := by
          refine Summable.tsum_le_tsum (fun m => ?_)
            ((deningerHeightMulConst φ C j hC hφ a).2 k) hsum
          rw [deningerHeightMulConst_coe, norm_mul, pow_add]
          have hk : 0 ≤ deningerHeight m ^ k :=
            pow_nonneg (deningerHeight_pos m).le _
          have ha : 0 ≤ ‖(a : DeningerPrimeLattice → ℂ) m‖ := norm_nonneg _
          calc
            deningerHeight m ^ k * (‖φ m‖ *
                ‖(a : DeningerPrimeLattice → ℂ) m‖) ≤
              deningerHeight m ^ k * ((C * deningerHeight m ^ j) *
                ‖(a : DeningerPrimeLattice → ℂ) m‖) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (hφ m) ha) hk
            _ = C * ((deningerHeight m ^ k * deningerHeight m ^ j) *
                ‖(a : DeningerPrimeLattice → ℂ) m‖) := by ring
    _ = C * ∑' m, deningerHeight m ^ (k + j) *
        ‖(a : DeningerPrimeLattice → ℂ) m‖ := by rw [tsum_mul_left]

def riggedPrimeFibreTransport
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMulConst (riggedPrimeFibreMultiplier s t)
    (riggedPrimeFibreMultiplierConstant t) 1
    (riggedPrimeFibreMultiplierConstant_pos t ht).le
    (norm_riggedPrimeFibreMultiplier_le s t hsStrip ht)

@[simp] theorem riggedPrimeFibreTransport_coe
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (a : DeningerHeightKothe)
    (m : DeningerPrimeLattice) :
    ((riggedPrimeFibreTransport s t hsStrip ht a : DeningerHeightKothe) :
      DeningerPrimeLattice → ℂ) m =
      riggedPrimeFibreMultiplier s t m *
        (a : DeningerPrimeLattice → ℂ) m := rfl

theorem deningerHeightSeminorm_riggedPrimeFibreTransport_le
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (riggedPrimeFibreTransport s t hsStrip ht a) ≤
      riggedPrimeFibreMultiplierConstant t *
        deningerHeightSeminorm (k + 1) a := by
  exact deningerHeightSeminorm_mulConst_le
    (riggedPrimeFibreMultiplierConstant_pos t ht).le
    (norm_riggedPrimeFibreMultiplier_le s t hsStrip ht) k a

theorem riggedPrimeFibreTransport_reverse
    (s t : ℂ)
    (hsStrip : 0 < s.re ∧ s.re < 1)
    (htStrip : 0 < t.re ∧ t.re < 1)
    (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (a : DeningerHeightKothe) :
    riggedPrimeFibreTransport t s htStrip hs
        (riggedPrimeFibreTransport s t hsStrip ht a) = a := by
  ext m
  rw [riggedPrimeFibreTransport_coe, riggedPrimeFibreTransport_coe]
  rw [← mul_assoc, mul_comm (riggedPrimeFibreMultiplier t s m),
    riggedPrimeFibreMultiplier_mul_reverse s t hs ht m, one_mul]

def riggedPrimeFibreTransportEquiv
    (s t : ℂ)
    (hsStrip : 0 < s.re ∧ s.re < 1)
    (htStrip : 0 < t.re ∧ t.re < 1)
    (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2) :
    DeningerHeightKothe ≃ₗ[ℂ] DeningerHeightKothe :=
  LinearEquiv.ofLinear
    (riggedPrimeFibreTransport s t hsStrip ht)
    (riggedPrimeFibreTransport t s htStrip hs)
    (by
      apply LinearMap.ext
      intro a
      simpa [LinearMap.comp_apply] using
        riggedPrimeFibreTransport_reverse t s htStrip hsStrip ht hs a)
    (by
      apply LinearMap.ext
      intro a
      simpa [LinearMap.comp_apply] using
        riggedPrimeFibreTransport_reverse s t hsStrip htStrip hs ht a)

@[simp] theorem riggedPrimeFibreTransportEquiv_apply
    (s t : ℂ)
    (hsStrip : 0 < s.re ∧ s.re < 1)
    (htStrip : 0 < t.re ∧ t.re < 1)
    (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (a : DeningerHeightKothe) :
    riggedPrimeFibreTransportEquiv s t hsStrip htStrip hs ht a =
      riggedPrimeFibreTransport s t hsStrip ht a := rfl

theorem preDivisorRiggedPrimeLinear_transport
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeLinear t
        (riggedPrimeFibreTransport s t hsStrip ht a) =
      preDivisorRiggedPrimeLinear s a := by
  rw [preDivisorRiggedPrimeLinear, preDivisorRiggedPrimeLinear]
  apply tsum_congr
  intro p
  rw [preDivisorRiggedPrimeLinearTerm,
    preDivisorRiggedPrimeLinearTerm,
    riggedPrimeFibreTransport_coe,
    riggedPrimeFibreMultiplier_axis]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    Real.sqrt (preDivisorRiggedPrimeWeight t p) *
        (riggedPrimeWeightScale s t p *
          ((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re) =
      (Real.sqrt (preDivisorRiggedPrimeWeight t p) *
        riggedPrimeWeightScale s t p) *
          ((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re := by ring
    _ = _ := by rw [sqrt_weight_mul_riggedPrimeWeightScale s t ht p]

theorem preDivisorRiggedPrimeDiagonal_transport
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeDiagonal t
        (riggedPrimeFibreTransport s t hsStrip ht a)
        (riggedPrimeFibreTransport s t hsStrip ht b) =
      preDivisorRiggedPrimeDiagonal s a b := by
  rw [preDivisorRiggedPrimeDiagonal, preDivisorRiggedPrimeDiagonal]
  apply tsum_congr
  intro p
  rw [preDivisorRiggedPrimeDiagonalTerm,
    preDivisorRiggedPrimeDiagonalTerm,
    riggedPrimeFibreTransport_coe,
    riggedPrimeFibreTransport_coe,
    riggedPrimeFibreMultiplier_axis]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hscale := weight_mul_riggedPrimeWeightScale_sq s t ht p
  ring_nf at hscale ⊢
  rw [hscale]
  ring

theorem preDivisorRiggedPrimeWittPairing_transport
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2)
    (horient : preDivisorOrientation t = preDivisorOrientation s)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing t
        (riggedPrimeFibreTransport s t hsStrip ht a)
        (riggedPrimeFibreTransport s t hsStrip ht b) =
      preDivisorRiggedPrimeWittPairing s a b := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_transport,
    preDivisorRiggedPrimeLinear_transport,
    preDivisorRiggedPrimeLinear_transport,
    horient]

theorem preDivisorRiggedPrimeWittPairing_transport_anti
    (s t : ℂ) (hsStrip : 0 < s.re ∧ s.re < 1)
    (ht : t.re ≠ 1 / 2)
    (horient : preDivisorOrientation t = -preDivisorOrientation s)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing t
        (riggedPrimeFibreTransport s t hsStrip ht a)
        (riggedPrimeFibreTransport s t hsStrip ht b) =
      -preDivisorRiggedPrimeWittPairing s a b := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_transport,
    preDivisorRiggedPrimeLinear_transport,
    preDivisorRiggedPrimeLinear_transport,
    horient]
  ring

def SameOpenCriticalChamber (s t : ℂ) : Prop :=
  (s.re < 1 / 2 ∧ t.re < 1 / 2) ∨
    (1 / 2 < s.re ∧ 1 / 2 < t.re)

theorem preDivisorOrientation_eq_of_sameOpenCriticalChamber
    (s t : ℂ) (hchamber : SameOpenCriticalChamber s t) :
    preDivisorOrientation t = preDivisorOrientation s := by
  rcases hchamber with hleft | hright
  · rw [preDivisorOrientation_eq_one_of_left s hleft.1,
      preDivisorOrientation_eq_one_of_left t hleft.2]
  · rw [preDivisorOrientation_eq_neg_one_of_right s hright.1,
      preDivisorOrientation_eq_neg_one_of_right t hright.2]

theorem ne_half_of_sameOpenCriticalChamber_left
    {s t : ℂ} (hchamber : SameOpenCriticalChamber s t) :
    s.re ≠ 1 / 2 := by
  rcases hchamber with hleft | hright <;> linarith

theorem ne_half_of_sameOpenCriticalChamber_right
    {s t : ℂ} (hchamber : SameOpenCriticalChamber s t) :
    t.re ≠ 1 / 2 := by
  rcases hchamber with hleft | hright <;> linarith

@[simp] theorem riggedPrimeFibreTransportEquiv_symm_apply
    (s t : ℂ)
    (hsStrip : 0 < s.re ∧ s.re < 1)
    (htStrip : 0 < t.re ∧ t.re < 1)
    (hs : s.re ≠ 1 / 2) (ht : t.re ≠ 1 / 2)
    (a : DeningerHeightKothe) :
    (riggedPrimeFibreTransportEquiv s t hsStrip htStrip hs ht).symm a =
      riggedPrimeFibreTransport t s htStrip hs a := rfl

/--
The pointwise rigged-Krein geometry producer class is killed when every pair of fibres in one
open half-strip is related by an exact tame congruence which also transports the distinguished
reservoir functional and positive diagonal.  Both directions lose at most one height seminorm.
-/
def SourceHorizontalRiggedPointwiseKreinGeometryRouteKilled : Prop :=
  ∀ s t : ℂ,
    (0 < s.re ∧ s.re < 1) →
    (0 < t.re ∧ t.re < 1) →
    SameOpenCriticalChamber s t →
    ∃ E : DeningerHeightKothe ≃ₗ[ℂ] DeningerHeightKothe,
      (∀ a, preDivisorRiggedPrimeLinear t (E a) =
        preDivisorRiggedPrimeLinear s a) ∧
      (∀ a b, preDivisorRiggedPrimeDiagonal t (E a) (E b) =
        preDivisorRiggedPrimeDiagonal s a b) ∧
      (∀ a b, preDivisorRiggedPrimeWittPairing t (E a) (E b) =
        preDivisorRiggedPrimeWittPairing s a b) ∧
      (∀ k a, deningerHeightSeminorm k (E a) ≤
        riggedPrimeFibreMultiplierConstant t *
          deningerHeightSeminorm (k + 1) a) ∧
      (∀ k a, deningerHeightSeminorm k (E.symm a) ≤
        riggedPrimeFibreMultiplierConstant s *
          deningerHeightSeminorm (k + 1) a)

/--
**CCM-FU pointwise rigged-fibre no-go.**  All off-wall source fibres in either connected
half-strip have exactly the same tame topological Krein geometry.  Thus no invariant of one
unmarked fibre can distinguish a hypothetical off-wall Xi zero from another point in its chamber;
any surviving Ward producer must retain fixed source coordinates or cross-fibre relative data.
-/
theorem sourceHorizontalRiggedPointwiseKreinGeometryRouteKilled :
    SourceHorizontalRiggedPointwiseKreinGeometryRouteKilled := by
  intro s t hsStrip htStrip hchamber
  have hs : s.re ≠ 1 / 2 :=
    ne_half_of_sameOpenCriticalChamber_left hchamber
  have ht : t.re ≠ 1 / 2 :=
    ne_half_of_sameOpenCriticalChamber_right hchamber
  let E := riggedPrimeFibreTransportEquiv s t hsStrip htStrip hs ht
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact preDivisorRiggedPrimeLinear_transport s t hsStrip ht a
  · intro a b
    exact preDivisorRiggedPrimeDiagonal_transport s t hsStrip ht a b
  · intro a b
    exact preDivisorRiggedPrimeWittPairing_transport s t hsStrip ht
      (preDivisorOrientation_eq_of_sameOpenCriticalChamber s t hchamber) a b
  · intro k a
    exact deningerHeightSeminorm_riggedPrimeFibreTransport_le
      s t hsStrip ht k a
  · intro k a
    exact deningerHeightSeminorm_riggedPrimeFibreTransport_le
      t s htStrip hs k a

end
end RHTower

