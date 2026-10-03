import GaloisForLFunctions.HTGeometry.WordConvolutionBanachAlgebra
import GaloisForLFunctions.HTGeometry.PositiveInvolutionIsIdentity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.CStarAlgebra.Unitary.Maps

/-!
# Self-adjoint Dyson word reversal and twisted reflection

Let `H` be a complex Hilbert space, `A` a finite alphabet, `L = L*` and `K_a = K_a*`.  In the word
algebra `𝔅 = ℓ¹(A*; End H)` put `B = L ⊗ δ_∅ + ∑_a K_a ⊗ δ_a` and `F_t = e^{-tB} = ∑_w U_w(t) ⊗ δ_w`.

* The word adjoint `(T ⊗ δ_w)^* = T^* ⊗ δ_{rev w}` is an isometric conjugate-linear
  anti-involution; `B^* = B`, `F_t^* = F_t`, and `U_w(t)^* = U_{rev w}(t)`.
* If `J` is a unitary involution and `σ` an involutive letter permutation with `JLJ* = L` and
  `JK_aJ* = K_{σ a}`, the relabelling `𝒞(T ⊗ δ_w) = JTJ* ⊗ δ_{σ w}` is an involutive automorphism
  commuting with `*`; the twisted reversal `ρ = 𝒞 ∘ *` is an anti-involution; both fix `B` and
  `F_t`, so `JU_w(t)J* = U_{σ w}(t)` and `JU_w(t)^*J* = U_{σ(rev w)}(t)`.
* On the units fixed by any anti-involution, `X ▷ Y = XY⁻¹X` is a reflection fusion, and an
  ordinary product of fixed elements is fixed exactly when they commute.
* The constant term of `F_t` is `e^{-tL}`; the normalized response `Z_t = (e^{tL} ⊗ δ_∅)F_t` has
  constant term one, and `Z_t^* = Z_t` exactly when `e^{tL} ⊗ δ_∅` commutes with `F_t`.
* For fixed `X = e^A`, `Y = e^C` with `A, C` in the first filtration step, `XY` leaves the fixed
  locus through `[A, C]` modulo filtration degree three, and the anti-fixed part of the truncated
  logarithm of `XY` is `½[A, C]`.
* If `B ≠ 0` then `F_t ≠ 1` for every real `t ≠ 0`, although `F_t` is fixed by both reversals:
  the two reversals share the nonzero fixed line `ℝB`.
-/

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## Reflection fusion on the fixed units of an anti-involution -/

section ReflectionFusion

variable {M : Type*} [Monoid M]

/-- Reflection fusion `X ▷ Y = X Y⁻¹ X` of units. -/
def reflectionFusion (X Y : Mˣ) : Mˣ := X * Y⁻¹ * X

/-- **(DSR.16)** `X ▷ X = X`. -/
theorem reflectionFusion_self (X : Mˣ) : reflectionFusion X X = X := by
  simp [reflectionFusion]

/-- **(DSR.16)** `X ▷ (X ▷ Y) = Y`. -/
theorem reflectionFusion_reflectionFusion (X Y : Mˣ) :
    reflectionFusion X (reflectionFusion X Y) = Y := by
  simp only [reflectionFusion]; group

/-- **(DSR.17)** `X ▷ (Y ▷ Z) = (X ▷ Y) ▷ (X ▷ Z)`. -/
theorem reflectionFusion_left_distrib (X Y Z : Mˣ) :
    reflectionFusion X (reflectionFusion Y Z) =
      reflectionFusion (reflectionFusion X Y) (reflectionFusion X Z) := by
  simp only [reflectionFusion]; group

variable {α : M → M} (hmul : ∀ x y, α (x * y) = α y * α x) (hinv : ∀ x, α (α x) = x)
include hmul hinv

theorem antiInvolution_one : α 1 = 1 := by
  have h := hmul 1 (α 1)
  rw [one_mul, hinv, one_mul] at h
  exact h.symm

theorem antiInvolution_inv_of_fixed {X : Mˣ} (hX : α X = X) : α ↑X⁻¹ = ↑X⁻¹ := by
  have h1 : α ↑X⁻¹ * ↑X = 1 := by
    rw [← hX, ← hmul, Units.mul_inv, antiInvolution_one hmul hinv]
  calc α ↑X⁻¹ = α ↑X⁻¹ * (↑X * ↑X⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (α ↑X⁻¹ * ↑X) * ↑X⁻¹ := by rw [mul_assoc]
    _ = ↑X⁻¹ := by rw [h1, one_mul]

/-- **Theorem 4.1 (DSR.15)** The fixed units are closed under reflection fusion. -/
theorem antiInvolution_reflectionFusion {X Y : Mˣ} (hX : α X = X) (hY : α Y = Y) :
    α ↑(reflectionFusion X Y) = ↑(reflectionFusion X Y) := by
  simp only [reflectionFusion, Units.val_mul]
  rw [hmul, hmul, hX, antiInvolution_inv_of_fixed hmul hinv hY, mul_assoc]

omit hinv in
/-- **(DSR.18)** An ordinary product of fixed elements is reversed. -/
theorem antiInvolution_mul_of_fixed {X Y : M} (hX : α X = X) (hY : α Y = Y) :
    α (X * Y) = Y * X := by
  rw [hmul, hX, hY]

omit hinv in
/-- **(DSR.18)** An ordinary product of fixed elements is fixed exactly when they commute. -/
theorem antiInvolution_mul_fixed_iff {X Y : M} (hX : α X = X) (hY : α Y = Y) :
    α (X * Y) = X * Y ↔ X * Y = Y * X := by
  rw [antiInvolution_mul_of_fixed hmul hX hY]
  exact eq_comm

end ReflectionFusion

/-! ## Unitary conjugation -/

section UnitaryConj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugation `T ↦ J T J*` by a unitary. -/
def unitaryConj (J : unitary (H →L[ℂ] H)) : (H →L[ℂ] H) →+* (H →L[ℂ] H) where
  toFun T := (J : H →L[ℂ] H) * T * star (J : H →L[ℂ] H)
  map_one' := by rw [mul_one, Unitary.mul_star_self_of_mem J.2]
  map_mul' T R := by
    have h : star (J : H →L[ℂ] H) * J = 1 := Unitary.star_mul_self_of_mem J.2
    calc (J : H →L[ℂ] H) * (T * R) * star (J : H →L[ℂ] H)
        = J * T * (star (J : H →L[ℂ] H) * J) * R * star (J : H →L[ℂ] H) := by
          rw [h, mul_one]; noncomm_ring
      _ = _ := by noncomm_ring
  map_zero' := by simp
  map_add' T R := by simp [mul_add, add_mul]

theorem unitaryConj_apply (J : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    unitaryConj J T = (J : H →L[ℂ] H) * T * star (J : H →L[ℂ] H) := rfl

theorem norm_unitaryConj (J : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) : ‖unitaryConj J T‖ = ‖T‖ := by
  rw [unitaryConj_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]

theorem unitaryConj_star (J : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    unitaryConj J (star T) = star (unitaryConj J T) := by
  simp only [unitaryConj_apply, star_mul, star_star, mul_assoc]

theorem unitaryConj_smul (J : unitary (H →L[ℂ] H)) (c : ℂ) (T : H →L[ℂ] H) :
    unitaryConj J (c • T) = c • unitaryConj J T := by
  simp only [unitaryConj_apply, mul_smul_comm, smul_mul_assoc]

theorem unitaryConj_unitaryConj {J : unitary (H →L[ℂ] H)} (hJ : (J : H →L[ℂ] H) * J = 1)
    (T : H →L[ℂ] H) : unitaryConj J (unitaryConj J T) = T := by
  have hs : star (J : H →L[ℂ] H) * star (J : H →L[ℂ] H) = 1 := by
    rw [← star_mul, hJ, star_one]
  simp only [unitaryConj_apply]
  calc (J : H →L[ℂ] H) * ((J : H →L[ℂ] H) * T * star (J : H →L[ℂ] H)) * star (J : H →L[ℂ] H)
      = ((J : H →L[ℂ] H) * J) * T * (star (J : H →L[ℂ] H) * star (J : H →L[ℂ] H)) := by
        noncomm_ring
    _ = T := by rw [hJ, hs, one_mul, mul_one]

end UnitaryConj

/-! ## Exponentials of self-adjoint operators -/

section SelfAdjointExp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance selfAdjointExpRatAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

theorem star_exp_smul_of_isSelfAdjoint {L : H →L[ℂ] H} (hL : IsSelfAdjoint L) (r : ℝ) :
    star (NormedSpace.exp ((r : ℂ) • L)) = NormedSpace.exp ((r : ℂ) • L) := by
  rw [NormedSpace.star_exp, star_smul, hL.star_eq, Complex.star_def, Complex.conj_ofReal]

theorem exp_smul_mul_exp_smul (L : H →L[ℂ] H) (r : ℝ) :
    NormedSpace.exp ((r : ℂ) • L) * NormedSpace.exp ((r : ℂ) • L) =
      NormedSpace.exp (((2 * r : ℝ) : ℂ) • L) := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
  congr 2
  push_cast; ring

theorem isPositive_exp_smul {L : H →L[ℂ] H} (hL : IsSelfAdjoint L) (r : ℝ) :
    (NormedSpace.exp ((r : ℂ) • L)).IsPositive := by
  set N := NormedSpace.exp (((r / 2 : ℝ) : ℂ) • L)
  have hN : ContinuousLinearMap.adjoint N = N := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact star_exp_smul_of_isSelfAdjoint hL _
  have h : NormedSpace.exp ((r : ℂ) • L) = ContinuousLinearMap.adjoint N ∘L N := by
    rw [hN, ← ContinuousLinearMap.mul_def, exp_smul_mul_exp_smul]
    congr 3; ring
  rw [h]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self N

/-- A self-adjoint generator whose exponential at a nonzero real time is the identity vanishes. -/
theorem eq_zero_of_exp_smul_eq_one {L : H →L[ℂ] H} (hL : IsSelfAdjoint L) {s : ℝ} (hs : s ≠ 0)
    (h : NormedSpace.exp ((s : ℂ) • L) = 1) : L = 0 := by
  have hk : ∀ k : ℕ, NormedSpace.exp (((s / 2 ^ k : ℝ) : ℂ) • L) = 1 := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      refine eq_one_of_isPositive_of_mul_self_eq_one (isPositive_exp_smul hL _) ?_
      rw [exp_smul_mul_exp_smul]
      convert ih using 4
      field_simp
      ring
  have hd := HasDerivAt.tendsto_slope_zero (hasDerivAt_exp_smul_const (𝕂 := ℝ) L (0 : ℝ))
  have hr : Tendsto (fun k : ℕ => s / 2 ^ k) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
        (by norm_num)).const_mul s
      rw [mul_zero] at this
      refine this.congr fun k => ?_
      rw [inv_pow, div_eq_mul_inv]
    · exact div_ne_zero hs (pow_ne_zero _ two_ne_zero)
  have hc := hd.comp hr
  have hzero : (fun k : ℕ => (s / 2 ^ k)⁻¹ •
      (NormedSpace.exp ((0 + s / 2 ^ k) • L) - NormedSpace.exp ((0 : ℝ) • L))) = fun _ => 0 := by
    funext k
    rw [zero_add, zero_smul, NormedSpace.exp_zero,
      show (s / 2 ^ k) • L = ((s / 2 ^ k : ℝ) : ℂ) • L from (Complex.coe_smul _ _).symm, hk k,
      sub_self, smul_zero]
  have hlim : Tendsto (fun _ : ℕ => (0 : H →L[ℂ] H)) atTop
      (𝓝 (NormedSpace.exp ((0 : ℝ) • L) * L)) := by
    rw [← hzero]; exact hc
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  rwa [zero_smul, NormedSpace.exp_zero, one_mul] at this

end SelfAdjointExp

/-! ## The self-adjoint Dyson source -/

variable (A : Type*) [Fintype A] [DecidableEq A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **(DSR.1)** A self-adjoint source `L = L*`, `K_a = K_a*` over a finite alphabet. -/
structure SelfAdjointDysonSource where
  /-- The base generator. -/
  L : H →L[ℂ] H
  /-- The letter interventions. -/
  K : A → H →L[ℂ] H
  isSelfAdjoint_L : IsSelfAdjoint L
  isSelfAdjoint_K : ∀ a, IsSelfAdjoint (K a)

namespace SelfAdjointDysonSource

variable {A H}
variable (S : SelfAdjointDysonSource A H)

local instance dysonRatAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _

/-- **(DSR.3)** The source generator `B = L ⊗ δ_∅ + ∑_a K_a ⊗ δ_a`. -/
def generator : WordL1 A (H →L[ℂ] H) :=
  WordL1.single [] S.L + ∑ a, WordL1.single [a] (S.K a)

/-- **(DSR.3)** The source response `F_t = e^{-tB}`. -/
def response (t : ℝ) : WordL1 A (H →L[ℂ] H) := NormedSpace.exp ((-(t : ℂ)) • S.generator)

/-- **(DSR.3)** The word coefficients `U_w(t)`. -/
def coeff (w : List A) (t : ℝ) : H →L[ℂ] H := S.response t w

/-- **(DSR.3)** `F_t = ∑_w U_w(t) ⊗ δ_w`, convergent in `ℓ¹`. -/
theorem hasSum_response (t : ℝ) :
    HasSum (fun w => WordL1.single w (S.coeff w t)) (S.response t) :=
  WordL1.hasSum_single _

theorem generator_apply_nil : S.generator [] = S.L := by
  rw [generator, WordL1.add_apply, WordL1.sum_apply, WordL1.single_apply_self]
  simp [WordL1.single_apply]

theorem generator_apply_singleton (a : A) : S.generator [a] = S.K a := by
  rw [generator, WordL1.add_apply, WordL1.sum_apply, Finset.sum_eq_single a]
  · simp [WordL1.single_apply]
  · intro b _ hb
    rw [WordL1.single_apply, if_neg (by simpa [eq_comm] using hb)]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ### Theorem 2.1: Dyson adjoint reversal -/

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 2.1 (DSR.5)** The word adjoint is an isometric conjugate-linear anti-involution. -/
theorem wordAdjoint_laws (X Y : WordL1 A (H →L[ℂ] H)) (c : ℂ) :
    star (X * Y) = star Y * star X ∧ star (star X) = X ∧ ‖star X‖ = ‖X‖ ∧
      star (c • X) = conj c • star X :=
  ⟨star_mul X Y, star_star X, norm_star X, star_smul c X⟩

/-- **(DSR.6)** `B^* = B`. -/
theorem star_generator : star S.generator = S.generator := by
  simp only [generator, star_add, star_sum, WordL1.star_single, List.reverse_nil,
    List.reverse_singleton, S.isSelfAdjoint_L.star_eq, (S.isSelfAdjoint_K _).star_eq]

/-- **(DSR.6)** `F_t^* = F_t`. -/
theorem star_response (t : ℝ) : star (S.response t) = S.response t := by
  rw [response, NormedSpace.star_exp, star_smul, star_generator, star_neg, Complex.star_def,
    Complex.conj_ofReal]

/-- **(DSR.7)** Schedule reversal: `U_w(t)^* = U_{rev w}(t)`. -/
theorem star_coeff (w : List A) (t : ℝ) : star (S.coeff w t) = S.coeff w.reverse t := by
  have h := congrArg (fun X : WordL1 A (H →L[ℂ] H) => X w.reverse) (S.star_response t)
  simp only [WordL1.star_apply, List.reverse_reverse] at h
  exact h

/-! ### Theorem 3.1: twisted functional-equation reversal -/

/-- **(DSR.8)** Functional relabelling data: an involutive letter permutation and a unitary
involution covariant with the source. -/
structure FunctionalRelabelling where
  σ : A ≃ A
  σ_involutive : ∀ a, σ (σ a) = a
  J : unitary (H →L[ℂ] H)
  J_mul_self : (J : H →L[ℂ] H) * J = 1
  conj_L : unitaryConj J S.L = S.L
  conj_K : ∀ a, unitaryConj J (S.K a) = S.K (σ a)

namespace FunctionalRelabelling

variable {S}
variable (R : FunctionalRelabelling S)

/-- **(DSR.9)** The covariance automorphism `𝒞(T ⊗ δ_w) = JTJ* ⊗ δ_{σ w}`. -/
def covariance : WordL1 A (H →L[ℂ] H) →+* WordL1 A (H →L[ℂ] H) :=
  WordL1.relabel R.σ (unitaryConj R.J) (norm_unitaryConj R.J)

/-- **(DSR.10)** The twisted reversal `ρ = 𝒞 ∘ *`. -/
def twistedReversal (X : WordL1 A (H →L[ℂ] H)) : WordL1 A (H →L[ℂ] H) := R.covariance (star X)

omit [Fintype A] in
theorem covariance_single (w : List A) (T : H →L[ℂ] H) :
    R.covariance (WordL1.single w T) = WordL1.single (w.map R.σ) (unitaryConj R.J T) :=
  WordL1.relabel_single _ _ _ w T

omit [Fintype A] [DecidableEq A] in
theorem covariance_smul (c : ℂ) (X : WordL1 A (H →L[ℂ] H)) :
    R.covariance (c • X) = c • R.covariance X :=
  WordL1.relabel_smul _ _ _ (unitaryConj_smul R.J) c X

omit [Fintype A] [DecidableEq A] in
theorem continuous_covariance : Continuous R.covariance := WordL1.continuous_relabel _ _ _

omit [Fintype A] [DecidableEq A] in
theorem map_symm_map_symm (w : List A) : (w.map R.σ.symm).map R.σ.symm = w := by
  have h : ∀ a, R.σ.symm (R.σ.symm a) = a := fun a => by
    rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, R.σ_involutive]
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun a _ => h a

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 3.1** `𝒞` and `*` commute. -/
theorem covariance_star (X : WordL1 A (H →L[ℂ] H)) :
    R.covariance (star X) = star (R.covariance X) := by
  ext w
  simp only [covariance, WordL1.relabel_apply, WordL1.star_apply, List.map_reverse,
    unitaryConj_star]

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 3.1** `𝒞² = id`. -/
theorem covariance_covariance (X : WordL1 A (H →L[ℂ] H)) : R.covariance (R.covariance X) = X := by
  ext w
  simp only [covariance, WordL1.relabel_apply, R.map_symm_map_symm,
    unitaryConj_unitaryConj R.J_mul_self]

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 3.1** `𝒞` is an involutive, hence bijective, ring automorphism. -/
theorem covariance_involutive : Function.Involutive R.covariance := R.covariance_covariance

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 3.1** `ρ² = id`. -/
theorem twistedReversal_twistedReversal (X : WordL1 A (H →L[ℂ] H)) :
    R.twistedReversal (R.twistedReversal X) = X := by
  simp only [twistedReversal]
  rw [← R.covariance_star, star_star, R.covariance_covariance]

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 3.1** `ρ` is an anti-automorphism. -/
theorem twistedReversal_mul (X Y : WordL1 A (H →L[ℂ] H)) :
    R.twistedReversal (X * Y) = R.twistedReversal Y * R.twistedReversal X := by
  simp only [twistedReversal, star_mul, map_mul]

/-- **(DSR.11)** `𝒞(B) = B`. -/
theorem covariance_generator : R.covariance S.generator = S.generator := by
  simp only [generator, map_add, map_sum, covariance_single, List.map_nil, List.map_singleton,
    R.conj_L, R.conj_K]
  congr 1
  exact Equiv.sum_comp R.σ (fun a => WordL1.single [a] (S.K a))

/-- **(DSR.11)** `ρ(B) = B`. -/
theorem twistedReversal_generator : R.twistedReversal S.generator = S.generator := by
  rw [twistedReversal, S.star_generator, R.covariance_generator]

/-- **(DSR.11)** `𝒞(F_t) = F_t`. -/
theorem covariance_response (t : ℝ) : R.covariance (S.response t) = S.response t := by
  rw [response, NormedSpace.map_exp _ R.continuous_covariance, R.covariance_smul,
    R.covariance_generator]

/-- **(DSR.11)** `ρ(F_t) = F_t`. -/
theorem twistedReversal_response (t : ℝ) : R.twistedReversal (S.response t) = S.response t := by
  rw [twistedReversal, S.star_response, R.covariance_response]

/-- **(DSR.12)** `J U_w(t) J* = U_{σ w}(t)`. -/
theorem conj_coeff (w : List A) (t : ℝ) :
    unitaryConj R.J (S.coeff w t) = S.coeff (w.map R.σ) t := by
  have h := congrArg (fun X : WordL1 A (H →L[ℂ] H) => X (w.map R.σ)) (R.covariance_response t)
  simp only [covariance, WordL1.relabel_apply, List.map_map, Equiv.symm_comp_self,
    List.map_id] at h
  exact h

/-- **(DSR.13)** `J U_w(t)^* J* = U_{σ(rev w)}(t)`. -/
theorem conj_star_coeff (w : List A) (t : ℝ) :
    unitaryConj R.J (star (S.coeff w t)) = S.coeff (w.reverse.map R.σ) t := by
  have h := congrArg (fun X : WordL1 A (H →L[ℂ] H) => X (w.reverse.map R.σ))
    (R.twistedReversal_response t)
  simp only [twistedReversal, covariance, WordL1.relabel_apply, WordL1.star_apply, List.map_map,
    Equiv.symm_comp_self, List.map_id, List.reverse_reverse] at h
  exact h

/-! ### Theorem 4.1: fixed Dyson units carry reflection fusion -/

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 4.1** The units fixed by `ρ` are closed under reflection fusion. -/
theorem twistedReversal_reflectionFusion {X Y : (WordL1 A (H →L[ℂ] H))ˣ}
    (hX : R.twistedReversal X = X) (hY : R.twistedReversal Y = Y) :
    R.twistedReversal ↑(reflectionFusion X Y) = ↑(reflectionFusion X Y) :=
  antiInvolution_reflectionFusion R.twistedReversal_mul R.twistedReversal_twistedReversal hX hY

omit [Fintype A] [DecidableEq A] in
/-- **(DSR.18)** for `ρ`. -/
theorem twistedReversal_mul_fixed_iff {X Y : WordL1 A (H →L[ℂ] H)}
    (hX : R.twistedReversal X = X) (hY : R.twistedReversal Y = Y) :
    R.twistedReversal (X * Y) = X * Y ↔ X * Y = Y * X :=
  antiInvolution_mul_fixed_iff R.twistedReversal_mul hX hY

/-- **Theorem 4.1** Every `F_t` is a unit fixed by both `*` and `ρ`. -/
theorem response_mem_fixedUnits (t : ℝ) :
    IsUnit (S.response t) ∧ star (S.response t) = S.response t ∧
      R.twistedReversal (S.response t) = S.response t :=
  ⟨NormedSpace.isUnit_exp _, S.star_response t, R.twistedReversal_response t⟩

/-- **(DSR.21)** The common fixed tangent of `*` and `ρ` contains the source line `ℝB`. -/
theorem fixed_sourceLine (r : ℝ) :
    star ((r : ℂ) • S.generator) = (r : ℂ) • S.generator ∧
      R.twistedReversal ((r : ℂ) • S.generator) = (r : ℂ) • S.generator := by
  have h1 : star ((r : ℂ) • S.generator) = (r : ℂ) • S.generator := by
    rw [star_smul, S.star_generator, Complex.star_def, Complex.conj_ofReal]
  refine ⟨h1, ?_⟩
  rw [twistedReversal, h1, R.covariance_smul, R.covariance_generator]

end FunctionalRelabelling

omit [Fintype A] [DecidableEq A] in
/-- **Theorem 4.1** The units fixed by the word adjoint are closed under reflection fusion. -/
theorem star_reflectionFusion {X Y : (WordL1 A (H →L[ℂ] H))ˣ}
    (hX : star (X : WordL1 A (H →L[ℂ] H)) = X) (hY : star (Y : WordL1 A (H →L[ℂ] H)) = Y) :
    star (↑(reflectionFusion X Y) : WordL1 A (H →L[ℂ] H)) = ↑(reflectionFusion X Y) :=
  antiInvolution_reflectionFusion star_mul star_star hX hY

omit [Fintype A] [DecidableEq A] in
/-- **(DSR.18)** for the word adjoint. -/
theorem star_mul_fixed_iff {X Y : WordL1 A (H →L[ℂ] H)} (hX : star X = X) (hY : star Y = Y) :
    star (X * Y) = X * Y ↔ X * Y = Y * X :=
  antiInvolution_mul_fixed_iff star_mul hX hY

/-! ### Section 5: constant term and interaction normalization -/

/-- The constant term of `F_t` is `S_t = e^{-tL}`. -/
theorem constantTerm_response (t : ℝ) :
    WordL1.constantTerm (S.response t) = NormedSpace.exp ((-(t : ℂ)) • S.L) := by
  rw [response, NormedSpace.map_exp _ WordL1.continuous_constantTerm]
  congr 1
  change ((-(t : ℂ)) • S.generator) [] = _
  rw [WordL1.smul_apply, S.generator_apply_nil]

/-- **(DSR.19)** The interaction-normalized response `Z_t = (S_t⁻¹ ⊗ δ_∅) F_t`. -/
def normalizedResponse (t : ℝ) : WordL1 A (H →L[ℂ] H) :=
  WordL1.single [] (NormedSpace.exp ((t : ℂ) • S.L)) * S.response t

/-- **(DSR.19)** `Z_t` has constant term one. -/
theorem constantTerm_normalizedResponse (t : ℝ) :
    WordL1.constantTerm (S.normalizedResponse t) = 1 := by
  rw [normalizedResponse, map_mul, constantTerm_response]
  change WordL1.single [] (NormedSpace.exp ((t : ℂ) • S.L)) [] * _ = 1
  rw [WordL1.single_apply_self, ← NormedSpace.exp_add_of_commute ((Commute.refl S.L).smul_left _
    |>.smul_right _), ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

/-- **(DSR.19)** `Z_t ∈ 1 + 𝔅_{≥1}`. -/
theorem normalizedResponse_sub_one_mem (t : ℝ) :
    S.normalizedResponse t - 1 ∈ WordL1.filtration ℂ 1 := by
  intro w hw
  have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
  subst hw0
  rw [WordL1.sub_apply, ← WordL1.constantTerm_apply, S.constantTerm_normalizedResponse,
    WordL1.one_apply, wordUnit_nil, sub_self]

/-- The word-filtration logarithm of `Z_t` converges coefficientwise: `(Z_t - 1)^k` vanishes on
every word of length `< k`. -/
theorem pow_normalizedResponse_sub_one_apply (t : ℝ) (k : ℕ) {w : List A} (hw : w.length < k) :
    ((S.normalizedResponse t - 1) ^ k) w = 0 :=
  WordL1.pow_mem_filtration (S.normalizedResponse_sub_one_mem t) k w hw

/-- **Section 5** The normalization preserves `*` exactly when `S_t⁻¹ ⊗ δ_∅` commutes with
`F_t`. -/
theorem star_normalizedResponse_iff (t : ℝ) :
    star (S.normalizedResponse t) = S.normalizedResponse t ↔
      Commute (WordL1.single [] (NormedSpace.exp ((t : ℂ) • S.L))) (S.response t) := by
  have hP : star (WordL1.single ([] : List A) (NormedSpace.exp ((t : ℂ) • S.L))) =
      WordL1.single [] (NormedSpace.exp ((t : ℂ) • S.L)) := by
    rw [WordL1.star_single, List.reverse_nil, star_exp_smul_of_isSelfAdjoint S.isSelfAdjoint_L]
  rw [normalizedResponse, star_mul, S.star_response, hP]
  exact eq_comm

/-! ### Theorem 6.1: exact joint-selection no-go -/

/-- **Theorem 6.1 (DSR.22)** If `B ≠ 0` then `F_t ≠ 1` for every real `t ≠ 0`. -/
theorem response_ne_one (hB : S.generator ≠ 0) {t : ℝ} (ht : t ≠ 0) : S.response t ≠ 1 := by
  intro hF
  by_cases hL : S.L = 0
  · have hB1 : S.generator ∈ WordL1.filtration ℂ 1 := by
      intro w hw
      have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
      subst hw0
      rw [S.generator_apply_nil, hL]
    have htr := WordL1.exp_sub_sum_mem_filtration
      (Submodule.smul_mem _ (-(t : ℂ)) hB1) 2
    have hK : ∀ a, S.K a = 0 := by
      intro a
      have h := htr [a] (by simp)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
        inv_one, one_smul, pow_zero, pow_one, zero_add, Nat.succ_eq_add_one, mul_one] at h
      change (S.response t - (1 + (-(t : ℂ)) • S.generator)) [a] = 0 at h
      rw [hF, WordL1.sub_apply, WordL1.add_apply, WordL1.smul_apply, S.generator_apply_singleton,
        WordL1.one_apply, wordUnit_of_ne_nil (List.cons_ne_nil a []), zero_add, zero_sub,
        neg_eq_zero, smul_eq_zero] at h
      rcases h with h | h
      · exact absurd (neg_eq_zero.1 h) (Complex.ofReal_ne_zero.2 ht)
      · exact h
    apply hB
    rw [generator, hL, WordL1.single_zero, zero_add]
    exact Finset.sum_eq_zero fun a _ => by rw [hK a, WordL1.single_zero]
  · apply hL
    have h := S.constantTerm_response t
    rw [hF, map_one] at h
    refine eq_zero_of_exp_smul_eq_one S.isSelfAdjoint_L (s := -t) (neg_ne_zero.2 ht) ?_
    rw [Complex.ofReal_neg]
    exact h.symm

end SelfAdjointDysonSource

/-! ## Filtered first escape from the fixed locus -/

section Escape

variable {A : Type*} {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

theorem exp_sub_one_sub_mem_filtration_two {X : WordL1 A E} (hX : X ∈ WordL1.filtration ℂ 1) :
    NormedSpace.exp X - 1 - X ∈ WordL1.filtration ℂ 2 := by
  have h := WordL1.exp_sub_sum_mem_filtration hX 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, inv_one,
    one_smul, pow_zero, pow_one, zero_add, Nat.succ_eq_add_one, mul_one] at h
  rwa [sub_sub] at *

omit [CompleteSpace E] in
theorem mem_filtration_three_of_mul {X Y : WordL1 A E} {i j : ℕ} (hij : 3 ≤ i + j)
    (hX : X ∈ WordL1.filtration ℂ i) (hY : Y ∈ WordL1.filtration ℂ j) :
    X * Y ∈ WordL1.filtration ℂ 3 :=
  WordL1.filtration_antitone hij (WordL1.mul_mem_filtration hX hY)

/-- **(DSR.20)** For fixed `X = e^A`, `Y = e^C` of an anti-multiplicative `α` with `A, C ∈ 𝔅_{≥1}`,
`XY - α(XY) ≡ [A, C]` modulo `𝔅_{≥3}`. -/
theorem fixed_mul_escape {α : WordL1 A E → WordL1 A E}
    (hmul : ∀ x y, α (x * y) = α y * α x) {Aa C : WordL1 A E}
    (hA : Aa ∈ WordL1.filtration ℂ 1) (hC : C ∈ WordL1.filtration ℂ 1)
    (hX : α (NormedSpace.exp Aa) = NormedSpace.exp Aa)
    (hY : α (NormedSpace.exp C) = NormedSpace.exp C) :
    NormedSpace.exp Aa * NormedSpace.exp C - α (NormedSpace.exp Aa * NormedSpace.exp C) -
      (Aa * C - C * Aa) ∈ WordL1.filtration ℂ 3 := by
  rw [hmul, hX, hY]
  set P := NormedSpace.exp Aa - 1 - Aa with hP
  set Q := NormedSpace.exp C - 1 - C with hQ
  have hP2 : P ∈ WordL1.filtration ℂ 2 := exp_sub_one_sub_mem_filtration_two hA
  have hQ2 : Q ∈ WordL1.filtration ℂ 2 := exp_sub_one_sub_mem_filtration_two hC
  have hXe : NormedSpace.exp Aa = 1 + Aa + P := by rw [hP]; abel
  have hYe : NormedSpace.exp C = 1 + C + Q := by rw [hQ]; abel
  have key : NormedSpace.exp Aa * NormedSpace.exp C - NormedSpace.exp C * NormedSpace.exp Aa -
      (Aa * C - C * Aa) = (Aa * Q - Q * Aa) + (P * C - C * P) + (P * Q - Q * P) := by
    rw [hXe, hYe]; noncomm_ring
  rw [key]
  refine add_mem (add_mem (sub_mem ?_ ?_) (sub_mem ?_ ?_)) (sub_mem ?_ ?_)
  · exact mem_filtration_three_of_mul (by norm_num) hA hQ2
  · exact mem_filtration_three_of_mul (by norm_num) hQ2 hA
  · exact mem_filtration_three_of_mul (by norm_num) hP2 hC
  · exact mem_filtration_three_of_mul (by norm_num) hC hP2
  · exact mem_filtration_three_of_mul (by norm_num) hP2 hQ2
  · exact mem_filtration_three_of_mul (by norm_num) hQ2 hP2

/-- Second-order truncated logarithm `ℓ(Z) = (Z - 1) - ½(Z - 1)²`. -/
def truncatedLog (Z : WordL1 A E) : WordL1 A E := (Z - 1) - (2 : ℂ)⁻¹ • (Z - 1) ^ 2

/-- **(DSR.20)** The anti-fixed part of the truncated logarithm of `XY` is `½[A, C]` modulo
`𝔅_{≥3}`. -/
theorem truncatedLog_antiFixed {α : WordL1 A E → WordL1 A E}
    (hmul : ∀ x y, α (x * y) = α y * α x) {Aa C : WordL1 A E}
    (hA : Aa ∈ WordL1.filtration ℂ 1) (hC : C ∈ WordL1.filtration ℂ 1)
    (hX : α (NormedSpace.exp Aa) = NormedSpace.exp Aa)
    (hY : α (NormedSpace.exp C) = NormedSpace.exp C) :
    (2 : ℂ)⁻¹ • (truncatedLog (NormedSpace.exp Aa * NormedSpace.exp C) -
        truncatedLog (α (NormedSpace.exp Aa * NormedSpace.exp C))) -
      (2 : ℂ)⁻¹ • (Aa * C - C * Aa) ∈ WordL1.filtration ℂ 3 := by
  have hesc := fixed_mul_escape hmul hA hC hX hY
  rw [hmul, hX, hY] at hesc ⊢
  set X := NormedSpace.exp Aa
  set Y := NormedSpace.exp C
  have hX1 : X - 1 ∈ WordL1.filtration ℂ 1 := by
    have h := exp_sub_one_sub_mem_filtration_two hA
    have : X - 1 = (X - 1 - Aa) + Aa := by abel
    rw [this]
    exact add_mem (WordL1.filtration_antitone (by norm_num) h) hA
  have hY1 : Y - 1 ∈ WordL1.filtration ℂ 1 := by
    have h := exp_sub_one_sub_mem_filtration_two hC
    have : Y - 1 = (Y - 1 - C) + C := by abel
    rw [this]
    exact add_mem (WordL1.filtration_antitone (by norm_num) h) hC
  have hall : ∀ Z : WordL1 A E, Z ∈ WordL1.filtration ℂ 0 := fun Z w hw =>
    absurd hw (Nat.not_lt_zero _)
  have hU : X * Y - 1 ∈ WordL1.filtration ℂ 1 := by
    have : X * Y - 1 = (X - 1) * Y + (Y - 1) := by noncomm_ring
    rw [this]
    exact add_mem (by simpa using WordL1.mul_mem_filtration hX1 (hall Y)) hY1
  have hV : Y * X - 1 ∈ WordL1.filtration ℂ 1 := by
    have : Y * X - 1 = (Y - 1) * X + (X - 1) := by noncomm_ring
    rw [this]
    exact add_mem (by simpa using WordL1.mul_mem_filtration hY1 (hall X)) hX1
  have hcomm : Aa * C - C * Aa ∈ WordL1.filtration ℂ 2 :=
    sub_mem (WordL1.mul_mem_filtration hA hC) (WordL1.mul_mem_filtration hC hA)
  have hD : X * Y - Y * X ∈ WordL1.filtration ℂ 2 := by
    have : X * Y - Y * X = (X * Y - Y * X - (Aa * C - C * Aa)) + (Aa * C - C * Aa) := by abel
    rw [this]
    exact add_mem (WordL1.filtration_antitone (by norm_num) hesc) hcomm
  have hsq : (X * Y - 1) ^ 2 - (Y * X - 1) ^ 2 ∈ WordL1.filtration ℂ 3 := by
    have : (X * Y - 1) ^ 2 - (Y * X - 1) ^ 2 =
        (X * Y - 1) * (X * Y - Y * X) + (X * Y - Y * X) * (Y * X - 1) := by noncomm_ring
    rw [this]
    exact add_mem (mem_filtration_three_of_mul (by norm_num) hU hD)
      (mem_filtration_three_of_mul (by norm_num) hD hV)
  have key : (2 : ℂ)⁻¹ • (truncatedLog (X * Y) - truncatedLog (Y * X)) -
      (2 : ℂ)⁻¹ • (Aa * C - C * Aa) =
      (2 : ℂ)⁻¹ • (X * Y - Y * X - (Aa * C - C * Aa)) -
        ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((X * Y - 1) ^ 2 - (Y * X - 1) ^ 2) := by
    simp only [truncatedLog, smul_sub, mul_smul]
    abel
  rw [key]
  exact sub_mem (Submodule.smul_mem _ _ hesc) (Submodule.smul_mem _ _ hsq)

end Escape

end GaloisForLFunctions.HTGeometry
