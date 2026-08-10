import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightKothe

/-!
# Green inverse and Hodge structure on the prime-log height source

A coefficient multiplier whose modulus is bounded by `H(m)^j` acts continuously on the source
with a loss of exactly `j` seminorm steps.  Because the height controls the prime-log frequency
in both directions,

`H(m)⁻¹ ≤ |ℓ(m)| ≤ H(m)`  for `m ≠ 0`,

the frequency and its inverse are both multipliers of growth one.  So the gapless generator
`D` has a continuous Green inverse after a single height step, and the sequence

`0 → ℂ·δ₀ → 𝒦_H → 𝒦_H⁰ → 0`

is split strict exact.  The modulus, its inverse, the odd Hodge sign, the Hardy projectors, and
the coefficientwise Poisson semigroup are multipliers of growth one or zero, and satisfy the
expected relations on the sector of vanishing total character.

* `deningerHeightMul` : the multiplier calculus and its seminorm loss.
* `deningerGenerator`, `deningerGreen` : `D` and `D⁻¹`, with `D ∘ D⁻¹ = id` on `𝒦_H⁰`.
* `deningerModulus`, `deningerModulusGreen`, `deningerHodgeSign`, `deningerHardyPlus`,
  `deningerHardyMinus`, `deningerPoisson` : `A`, `G`, `W`, `Π₊`, `Π₋`, `P_r`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Multiplier calculus -/

private theorem deningerHeightMul_mem {φ : DeningerLattice → ℂ} {j : ℕ}
    (hφ : ∀ m, ‖φ m‖ ≤ deningerHeight m ^ j) (a : DeningerHeightKothe) :
    (fun m => φ m * (a : DeningerLattice → ℂ) m) ∈ DeningerHeightKothe := by
  intro k
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (deningerHeight_pos m).le _) (norm_nonneg _))
    (fun m => ?_) (a.2 (k + j))
  show deningerHeight m ^ k * ‖φ m * (a : DeningerLattice → ℂ) m‖
      ≤ deningerHeightKotheData.w (k + j) m * ‖(a : DeningerLattice → ℂ) m‖
  rw [deningerHeightKotheData_w, norm_mul, pow_add]
  have hnn : (0 : ℝ) ≤ deningerHeight m ^ k := pow_nonneg (deningerHeight_pos m).le _
  have hstep : deningerHeight m ^ k * (‖φ m‖ * ‖(a : DeningerLattice → ℂ) m‖)
      ≤ deningerHeight m ^ k * (deningerHeight m ^ j * ‖(a : DeningerLattice → ℂ) m‖) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hφ m) (norm_nonneg _)) hnn
  calc deningerHeight m ^ k * (‖φ m‖ * ‖(a : DeningerLattice → ℂ) m‖)
      ≤ deningerHeight m ^ k * (deningerHeight m ^ j * ‖(a : DeningerLattice → ℂ) m‖) := hstep
    _ = deningerHeight m ^ k * deningerHeight m ^ j * ‖(a : DeningerLattice → ℂ) m‖ := by ring

/-- **Multiplier calculus.**  Coefficientwise multiplication by a multiplier bounded by `H^j`. -/
def deningerHeightMul (φ : DeningerLattice → ℂ) (j : ℕ)
    (hφ : ∀ m, ‖φ m‖ ≤ deningerHeight m ^ j) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe where
  toFun a := ⟨fun m => φ m * (a : DeningerLattice → ℂ) m, deningerHeightMul_mem hφ a⟩
  map_add' a b := by
    ext m
    show φ m * ((a + b : DeningerHeightKothe) : DeningerLattice → ℂ) m
        = ((⟨fun m => φ m * (a : DeningerLattice → ℂ) m, deningerHeightMul_mem hφ a⟩ +
            ⟨fun m => φ m * (b : DeningerLattice → ℂ) m, deningerHeightMul_mem hφ b⟩ :
              DeningerHeightKothe) : DeningerLattice → ℂ) m
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c a := by
    ext m
    show φ m * ((c • a : DeningerHeightKothe) : DeningerLattice → ℂ) m
        = ((c • (⟨fun m => φ m * (a : DeningerLattice → ℂ) m,
            deningerHeightMul_mem hφ a⟩ : DeningerHeightKothe)) : DeningerLattice → ℂ) m
    show φ m * (c * (a : DeningerLattice → ℂ) m)
        = c * (φ m * (a : DeningerLattice → ℂ) m)
    ring

@[simp]
theorem deningerHeightMul_coe {φ : DeningerLattice → ℂ} {j : ℕ}
    (hφ : ∀ m, ‖φ m‖ ≤ deningerHeight m ^ j) (a : DeningerHeightKothe)
    (m : DeningerLattice) :
    ((deningerHeightMul φ j hφ a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = φ m * (a : DeningerLattice → ℂ) m := rfl

/-- **A multiplier of growth `j` costs exactly `j` seminorm steps.** -/
theorem deningerHeightSeminorm_mul_le {φ : DeningerLattice → ℂ} {j : ℕ}
    (hφ : ∀ m, ‖φ m‖ ≤ deningerHeight m ^ j) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHeightMul φ j hφ a)
      ≤ deningerHeightSeminorm (k + j) a := by
  rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
  refine Summable.tsum_le_tsum (fun m => ?_)
    ((deningerHeightMul φ j hφ a).2 k) (a.2 (k + j))
  show deningerHeight m ^ k * ‖φ m * (a : DeningerLattice → ℂ) m‖
      ≤ deningerHeight (m) ^ (k + j) * ‖(a : DeningerLattice → ℂ) m‖
  rw [norm_mul, pow_add]
  have hnn : (0 : ℝ) ≤ deningerHeight m ^ k := pow_nonneg (deningerHeight_pos m).le _
  calc deningerHeight m ^ k * (‖φ m‖ * ‖(a : DeningerLattice → ℂ) m‖)
      ≤ deningerHeight m ^ k * (deningerHeight m ^ j * ‖(a : DeningerLattice → ℂ) m‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hφ m) (norm_nonneg _)) hnn
    _ = deningerHeight m ^ k * deningerHeight m ^ j * ‖(a : DeningerLattice → ℂ) m‖ := by ring

/-! ## The multipliers -/

/-- The sign of the prime-log frequency. -/
def deningerSign (m : DeningerLattice) : ℝ :=
  if 0 < deningerFreq m then 1 else if deningerFreq m < 0 then -1 else 0

theorem deningerSign_of_pos {m : DeningerLattice} (h : 0 < deningerFreq m) :
    deningerSign m = 1 := by
  rw [deningerSign, if_pos h]

theorem deningerSign_of_neg {m : DeningerLattice} (h : deningerFreq m < 0) :
    deningerSign m = -1 := by
  have hnot : ¬ (0 : ℝ) < deningerFreq m := by linarith
  rw [deningerSign, if_neg hnot, if_pos h]

theorem deningerSign_of_zero {m : DeningerLattice} (h : deningerFreq m = 0) :
    deningerSign m = 0 := by
  have hnot1 : ¬ (0 : ℝ) < deningerFreq m := by rw [h]; exact lt_irrefl 0
  have hnot2 : ¬ deningerFreq m < 0 := by rw [h]; exact lt_irrefl 0
  rw [deningerSign, if_neg hnot1, if_neg hnot2]

theorem abs_deningerSign_le_one (m : DeningerLattice) : |deningerSign m| ≤ 1 := by
  rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
  · rw [deningerSign_of_neg h]; norm_num
  · rw [deningerSign_of_zero h]; norm_num
  · rw [deningerSign_of_pos h]; norm_num

theorem deningerSign_mul_self {m : DeningerLattice} (h : deningerFreq m ≠ 0) :
    deningerSign m * deningerSign m = 1 := by
  rcases lt_trichotomy (deningerFreq m) 0 with hlt | heq | hgt
  · rw [deningerSign_of_neg hlt]; norm_num
  · exact absurd heq h
  · rw [deningerSign_of_pos hgt]; norm_num

theorem deningerFreq_multiplier_bound (m : DeningerLattice) :
    ‖((deningerFreq m : ℂ))‖ ≤ deningerHeight m ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
  exact abs_deningerFreq_le_height m

theorem deningerGreen_multiplier_bound (m : DeningerLattice) :
    ‖(((deningerFreq m)⁻¹ : ℝ) : ℂ)‖ ≤ deningerHeight m ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
  by_cases hm : m = 0
  · subst hm
    have h0 : deningerFreq (0 : DeningerLattice) = 0 := deningerFreq_zero
    rw [h0, inv_zero, abs_zero]
    exact le_of_lt (deningerHeight_pos 0)
  · have hle := deningerHeight_inv_le_abs_freq hm
    have hfpos : 0 < |deningerFreq m| := abs_pos.mpr (deningerFreq_ne_zero hm)
    rw [abs_inv, inv_le_comm₀ hfpos (deningerHeight_pos m)]
    exact hle

theorem deningerModulus_multiplier_bound (m : DeningerLattice) :
    ‖((|deningerFreq m| : ℝ) : ℂ)‖ ≤ deningerHeight m ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one, abs_abs]
  exact abs_deningerFreq_le_height m

theorem deningerModulusGreen_multiplier_bound (m : DeningerLattice) :
    ‖(((|deningerFreq m|)⁻¹ : ℝ) : ℂ)‖ ≤ deningerHeight m ^ 1 := by
  have h := deningerGreen_multiplier_bound m
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs, ← abs_inv]
  exact h

theorem deningerHodgeSign_multiplier_bound (m : DeningerLattice) :
    ‖(Complex.I * ((deningerSign m : ℝ) : ℂ))‖ ≤ deningerHeight m ^ 0 := by
  rw [pow_zero, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact abs_deningerSign_le_one m

theorem deningerHardyPlus_multiplier_bound (m : DeningerLattice) :
    ‖(if 0 < deningerFreq m then (1 : ℂ) else 0)‖ ≤ deningerHeight m ^ 0 := by
  rw [pow_zero]
  by_cases h : 0 < deningerFreq m <;> simp [h]

theorem deningerHardyMinus_multiplier_bound (m : DeningerLattice) :
    ‖(if deningerFreq m < 0 then (1 : ℂ) else 0)‖ ≤ deningerHeight m ^ 0 := by
  rw [pow_zero]
  by_cases h : deningerFreq m < 0 <;> simp [h]

theorem deningerPoisson_multiplier_bound (r : ℝ) (hr : 0 ≤ r) (m : DeningerLattice) :
    ‖((Real.exp (-(r * |deningerFreq m|)) : ℝ) : ℂ)‖ ≤ deningerHeight m ^ 0 := by
  rw [pow_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.mpr ?_
  have hnn : 0 ≤ r * |deningerFreq m| := mul_nonneg hr (abs_nonneg _)
  linarith

/-- **The signed prime-log generator** `(Da)_m = ℓ(m) a_m`. -/
def deningerGenerator : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => ((deningerFreq m : ℝ) : ℂ)) 1 deningerFreq_multiplier_bound

/-- **The Green inverse** `(D⁻¹a)_m = ℓ(m)⁻¹ a_m`, zero at the trivial character. -/
def deningerGreen : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => (((deningerFreq m)⁻¹ : ℝ) : ℂ)) 1
    deningerGreen_multiplier_bound

/-- **The modulus** `(Aa)_m = |ℓ(m)| a_m`. -/
def deningerModulus : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => ((|deningerFreq m| : ℝ) : ℂ)) 1
    deningerModulus_multiplier_bound

/-- **The positive Green operator** `(Ga)_m = |ℓ(m)|⁻¹ a_m`. -/
def deningerModulusGreen : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => (((|deningerFreq m|)⁻¹ : ℝ) : ℂ)) 1
    deningerModulusGreen_multiplier_bound

/-- **The odd Hodge sign** `(Wa)_m = i·sgn(ℓ(m)) a_m`. -/
def deningerHodgeSign : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => Complex.I * ((deningerSign m : ℝ) : ℂ)) 0
    deningerHodgeSign_multiplier_bound

/-- **The positive Hardy projector** `(Π₊a)_m = 1_{ℓ(m)>0} a_m`. -/
def deningerHardyPlus : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => if 0 < deningerFreq m then (1 : ℂ) else 0) 0
    deningerHardyPlus_multiplier_bound

/-- **The negative Hardy projector** `(Π₋a)_m = 1_{ℓ(m)<0} a_m`. -/
def deningerHardyMinus : DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => if deningerFreq m < 0 then (1 : ℂ) else 0) 0
    deningerHardyMinus_multiplier_bound

/-- **The coefficientwise Poisson extension** `(P_r a)_m = e^{-r|ℓ(m)|} a_m`. -/
def deningerPoisson (r : ℝ) (hr : 0 ≤ r) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  deningerHeightMul (fun m => ((Real.exp (-(r * |deningerFreq m|)) : ℝ) : ℂ)) 0
    (deningerPoisson_multiplier_bound r hr)

/-! ## The seminorm estimates -/

theorem deningerHeightSeminorm_generator_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerGenerator a) ≤ deningerHeightSeminorm (k + 1) a :=
  deningerHeightSeminorm_mul_le deningerFreq_multiplier_bound k a

theorem deningerHeightSeminorm_green_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerGreen a) ≤ deningerHeightSeminorm (k + 1) a :=
  deningerHeightSeminorm_mul_le deningerGreen_multiplier_bound k a

theorem deningerHeightSeminorm_modulus_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerModulus a) ≤ deningerHeightSeminorm (k + 1) a :=
  deningerHeightSeminorm_mul_le deningerModulus_multiplier_bound k a

theorem deningerHeightSeminorm_modulusGreen_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerModulusGreen a) ≤ deningerHeightSeminorm (k + 1) a :=
  deningerHeightSeminorm_mul_le deningerModulusGreen_multiplier_bound k a

theorem deningerHeightSeminorm_hodgeSign_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHodgeSign a) ≤ deningerHeightSeminorm k a := by
  have h := deningerHeightSeminorm_mul_le deningerHodgeSign_multiplier_bound k a
  rw [Nat.add_zero] at h
  exact h

theorem deningerHeightSeminorm_hardyPlus_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHardyPlus a) ≤ deningerHeightSeminorm k a := by
  have h := deningerHeightSeminorm_mul_le deningerHardyPlus_multiplier_bound k a
  rw [Nat.add_zero] at h
  exact h

theorem deningerHeightSeminorm_hardyMinus_le (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerHardyMinus a) ≤ deningerHeightSeminorm k a := by
  have h := deningerHeightSeminorm_mul_le deningerHardyMinus_multiplier_bound k a
  rw [Nat.add_zero] at h
  exact h

theorem deningerHeightSeminorm_poisson_le (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerPoisson r hr a) ≤ deningerHeightSeminorm k a := by
  have h := deningerHeightSeminorm_mul_le (deningerPoisson_multiplier_bound r hr) k a
  rw [Nat.add_zero] at h
  exact h

/-! ## The strict exact sequence -/

theorem deningerGenerator_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerGenerator a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = ((deningerFreq m : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m := rfl

theorem deningerGreen_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerGreen a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = (((deningerFreq m)⁻¹ : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m := rfl

/-- The generator lands in the sector of vanishing total character. -/
theorem deningerGenerator_mem_zero (a : DeningerHeightKothe) :
    deningerGenerator a ∈ deningerHeightKotheZero := by
  rw [deningerHeightKotheZero_mem_iff, deningerGenerator_coe]
  simp

/-- **The generator is left inverse to the Green inverse on the zero-character sector.** -/
theorem deningerGenerator_green (a : DeningerHeightKothe)
    (ha : a ∈ deningerHeightKotheZero) :
    deningerGenerator (deningerGreen a) = a := by
  have ha0 : (a : DeningerLattice → ℂ) 0 = 0 := ha
  ext m
  rw [deningerGenerator_coe, deningerGreen_coe]
  by_cases hm : m = 0
  · subst hm
    rw [ha0]
    ring
  · have hne : deningerFreq m ≠ 0 := deningerFreq_ne_zero hm
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hne]
    simp

/-- **The kernel of the generator is the line of the trivial character.** -/
theorem deningerGenerator_eq_zero_iff (a : DeningerHeightKothe) :
    deningerGenerator a = 0 ↔ ∀ m : DeningerLattice, m ≠ 0 →
      (a : DeningerLattice → ℂ) m = 0 := by
  constructor
  · intro h m hm
    have hcoord := congrArg (fun x : DeningerHeightKothe => (x : DeningerLattice → ℂ) m) h
    rw [deningerGenerator_coe] at hcoord
    have hzero : ((deningerFreq m : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m = 0 := by
      simpa using hcoord
    have hne : ((deningerFreq m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast deningerFreq_ne_zero hm
    exact (mul_eq_zero.mp hzero).resolve_left hne
  · intro h
    ext m
    rw [deningerGenerator_coe]
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [h m hm]
      simp

/-- **The kernel of the generator is the line spanned by the trivial character.** -/
theorem deningerGenerator_ker_eq_span_delta :
    LinearMap.ker deningerGenerator
      = Submodule.span ℂ {deningerKotheDelta deningerHeightKotheData (0 : DeningerLattice)} := by
  classical
  apply le_antisymm
  · intro a ha
    have hzero := (deningerGenerator_eq_zero_iff a).mp ha
    have hrep : a = (a : DeningerLattice → ℂ) 0 •
        deningerKotheDelta deningerHeightKotheData (0 : DeningerLattice) := by
      ext m
      show (a : DeningerLattice → ℂ) m
          = (((a : DeningerLattice → ℂ) 0 •
              deningerKotheDelta deningerHeightKotheData (0 : DeningerLattice) :
                DeningerHeightKothe) : DeningerLattice → ℂ) m
      rw [Submodule.coe_smul, Pi.smul_apply, deningerKotheDelta_coe, smul_eq_mul]
      by_cases hm : m = 0
      · subst hm
        simp
      · rw [hzero m hm, Pi.single_eq_of_ne hm, mul_zero]
    rw [hrep]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show deningerGenerator (deningerKotheDelta deningerHeightKotheData
      (0 : DeningerLattice)) = 0
    ext m
    rw [deningerGenerator_coe]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hdelta : ((deningerKotheDelta deningerHeightKotheData (0 : DeningerLattice) :
          DeningerHeightKothe) : DeningerLattice → ℂ) m = 0 := by
        rw [deningerKotheDelta_coe]
        exact Pi.single_eq_of_ne hm 1
      rw [hdelta]
      simp

/-- **The generator is onto the zero-character sector**, with the Green inverse as an explicit
continuous splitting. -/
theorem deningerGenerator_surjective_onto_zero (b : DeningerHeightKothe)
    (hb : b ∈ deningerHeightKotheZero) :
    ∃ a : DeningerHeightKothe, deningerGenerator a = b :=
  ⟨deningerGreen b, deningerGenerator_green b hb⟩

/-! ## The Hodge relations on the zero-character sector -/

theorem deningerHodgeSign_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerHodgeSign a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = Complex.I * ((deningerSign m : ℝ) : ℂ) *
        (a : DeningerLattice → ℂ) m := rfl

theorem deningerHardyPlus_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerHardyPlus a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = (if 0 < deningerFreq m then (1 : ℂ) else 0) *
        (a : DeningerLattice → ℂ) m := rfl

theorem deningerHardyMinus_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerHardyMinus a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = (if deningerFreq m < 0 then (1 : ℂ) else 0) *
        (a : DeningerLattice → ℂ) m := rfl

/-- `W² = -1` on the zero-character sector. -/
theorem deningerHodgeSign_sq (a : DeningerHeightKothe)
    (ha : a ∈ deningerHeightKotheZero) :
    deningerHodgeSign (deningerHodgeSign a) = -a := by
  have ha0 : (a : DeningerLattice → ℂ) 0 = 0 := ha
  ext m
  rw [deningerHodgeSign_coe, deningerHodgeSign_coe]
  show Complex.I * ((deningerSign m : ℝ) : ℂ) *
      (Complex.I * ((deningerSign m : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m)
      = ((-a : DeningerHeightKothe) : DeningerLattice → ℂ) m
  rw [Submodule.coe_neg, Pi.neg_apply]
  by_cases hm : m = 0
  · subst hm
    rw [ha0]
    ring
  · have hpos : deningerFreq m ≠ 0 := deningerFreq_ne_zero hm
    have hsq : ((deningerSign m : ℝ) : ℂ) *
        ((deningerSign m : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, deningerSign_mul_self hpos]
      norm_num
    calc Complex.I * ((deningerSign m : ℝ) : ℂ) *
          (Complex.I * ((deningerSign m : ℝ) : ℂ) *
            (a : DeningerLattice → ℂ) m)
        = (Complex.I * Complex.I) *
            (((deningerSign m : ℝ) : ℂ) *
              ((deningerSign m : ℝ) : ℂ)) *
            (a : DeningerLattice → ℂ) m := by ring
      _ = -(a : DeningerLattice → ℂ) m := by
          rw [Complex.I_mul_I, hsq]; ring

/-- The Hardy projectors are idempotent. -/
theorem deningerHardyPlus_idem (a : DeningerHeightKothe) :
    deningerHardyPlus (deningerHardyPlus a) = deningerHardyPlus a := by
  ext m
  simp only [deningerHardyPlus_coe]
  by_cases h : 0 < deningerFreq m <;> simp [h]

theorem deningerHardyMinus_idem (a : DeningerHeightKothe) :
    deningerHardyMinus (deningerHardyMinus a) = deningerHardyMinus a := by
  ext m
  simp only [deningerHardyMinus_coe]
  by_cases h : deningerFreq m < 0 <;> simp [h]

/-- The Hardy projectors are orthogonal. -/
theorem deningerHardy_mul_eq_zero (a : DeningerHeightKothe) :
    deningerHardyPlus (deningerHardyMinus a) = 0 := by
  ext m
  rw [deningerHardyPlus_coe, deningerHardyMinus_coe]
  by_cases h : 0 < deningerFreq m
  · have hnot : ¬ deningerFreq m < 0 := by linarith
    simp [h, hnot]
  · simp [h]

/-- The Hardy projectors sum to the identity on the zero-character sector. -/
theorem deningerHardy_add_eq_id (a : DeningerHeightKothe)
    (ha : a ∈ deningerHeightKotheZero) :
    deningerHardyPlus a + deningerHardyMinus a = a := by
  have ha0 : (a : DeningerLattice → ℂ) 0 = 0 := ha
  ext m
  show ((deningerHardyPlus a + deningerHardyMinus a : DeningerHeightKothe) :
      DeningerLattice → ℂ) m = (a : DeningerLattice → ℂ) m
  rw [Submodule.coe_add, Pi.add_apply, deningerHardyPlus_coe, deningerHardyMinus_coe]
  by_cases hm : m = 0
  · subst hm
    rw [ha0]
    simp
  · have hne : deningerFreq m ≠ 0 := deningerFreq_ne_zero hm
    rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
    · have hnot : ¬ (0 : ℝ) < deningerFreq m := by linarith
      simp [h, hnot]
    · exact absurd h hne
    · have hnot : ¬ deningerFreq m < 0 := by linarith
      simp [h, hnot]

/-- The odd Hodge sign is the difference of the Hardy projectors. -/
theorem deningerHodgeSign_eq_hardy_sub (a : DeningerHeightKothe) :
    deningerHodgeSign a
      = Complex.I • (deningerHardyPlus a - deningerHardyMinus a) := by
  ext m
  rw [deningerHodgeSign_coe]
  show Complex.I * ((deningerSign m : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m
      = ((Complex.I • (deningerHardyPlus a - deningerHardyMinus a) :
          DeningerHeightKothe) : DeningerLattice → ℂ) m
  rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply,
    deningerHardyPlus_coe, deningerHardyMinus_coe]
  rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
  · have hnot : ¬ (0 : ℝ) < deningerFreq m := by linarith
    rw [deningerSign_of_neg h]
    simp [h, hnot]
  · have hnot1 : ¬ (0 : ℝ) < deningerFreq m := by rw [h]; exact lt_irrefl 0
    have hnot2 : ¬ deningerFreq m < 0 := by rw [h]; exact lt_irrefl 0
    rw [deningerSign_of_zero h]
    simp [hnot1, hnot2]
  · have hnot : ¬ deningerFreq m < 0 := by linarith
    rw [deningerSign_of_pos h]
    simp [h, hnot]

/-! ## The Poisson semigroup -/

theorem deningerPoisson_coe (r : ℝ) (hr : 0 ≤ r) (a : DeningerHeightKothe)
    (m : DeningerLattice) :
    ((deningerPoisson r hr a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = ((Real.exp (-(r * |deningerFreq m|)) : ℝ) : ℂ) *
        (a : DeningerLattice → ℂ) m := rfl

theorem deningerModulus_coe (a : DeningerHeightKothe) (m : DeningerLattice) :
    ((deningerModulus a : DeningerHeightKothe) : DeningerLattice → ℂ) m
      = ((|deningerFreq m| : ℝ) : ℂ) * (a : DeningerLattice → ℂ) m := rfl

theorem deningerPoisson_zero (a : DeningerHeightKothe) :
    deningerPoisson 0 le_rfl a = a := by
  ext m
  rw [deningerPoisson_coe]
  simp

theorem deningerPoisson_add (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (a : DeningerHeightKothe) :
    deningerPoisson (r + t) (by linarith) a
      = deningerPoisson r hr (deningerPoisson t ht a) := by
  ext m
  rw [deningerPoisson_coe, deningerPoisson_coe, deningerPoisson_coe]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf

/-- **The modulus is the outward Dirichlet-to-Neumann operator of the Poisson family.**  The
coefficientwise derivative of `P_r` is `-A P_r`. -/
theorem deningerPoisson_hasDerivAt (a : DeningerHeightKothe) (m : DeningerLattice)
    (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => ((Real.exp (-(t * |deningerFreq m|)) : ℝ) : ℂ) *
        (a : DeningerLattice → ℂ) m)
      (-(((|deningerFreq m| : ℝ) : ℂ) *
        (((Real.exp (-(r * |deningerFreq m|)) : ℝ) : ℂ) *
          (a : DeningerLattice → ℂ) m))) r := by
  have hbase : HasDerivAt (fun t : ℝ => -(t * |deningerFreq m|)) (-|deningerFreq m|) r :=
    (hasDerivAt_mul_const (|deningerFreq m|)).neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t * |deningerFreq m|)))
      (Real.exp (-(r * |deningerFreq m|)) * (-|deningerFreq m|)) r := hbase.exp
  have hcomplex := (hexp.ofReal_comp).mul_const ((a : DeningerLattice → ℂ) m)
  have heq : ((Real.exp (-(r * |deningerFreq m|)) * (-|deningerFreq m|) : ℝ) : ℂ) *
      (a : DeningerLattice → ℂ) m
      = -(((|deningerFreq m| : ℝ) : ℂ) *
        (((Real.exp (-(r * |deningerFreq m|)) : ℝ) : ℂ) *
          (a : DeningerLattice → ℂ) m)) := by
    push_cast
    ring
  rw [← heq]
  exact hcomplex

end

end RHTower
