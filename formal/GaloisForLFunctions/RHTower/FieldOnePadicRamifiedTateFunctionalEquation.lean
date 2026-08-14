import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierPlancherel
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Ramified finite-place Tate functional equation on literal `ℚ_p`

This file formalizes the arbitrary-conductor angular theorem used at each
finite place in Connes--Marcolli equation (2.258), with Tate's normalization.
For every primitive Dirichlet character of exact conductor `p^n`, it proves:

* the Haar-integral discrete Fourier equation on `ℤ_p / p^nℤ_p`;
* the previously missing square-norm law `|τ(χ)|² = p^n` from Parseval;
* unit modulus of the normalized Gauss phase `τ(χ) / √(p^n)`;
* construction of the corresponding character packet as a literal
  compactly supported locally constant function on `ℚ_p`;
* dual-conductor support of its literal p-adic Fourier transform; and
* the pointwise inverse-character/Gauss-phase formula on the entire dual
  denominator stage.

Primitive characters are the mathematical objects parametrized by the
typed subtype `FieldOnePadicPrimitiveAngularCharacter`; no theorem takes a
primitivity premise. No Fourier functional equation or unitarity statement
is assumed.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

/-- A finite-place angular character at its exact conductor `p^n`. -/
abbrev FieldOnePadicPrimitiveAngularCharacter (n : ℕ) :=
  {χ : DirichletCharacter ℂ (p ^ n) // χ.IsPrimitive}

/-- Pullback of an exact-conductor finite character to the actual unit ball. -/
def fieldOnePadicPrimitiveAngularLift (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) : ℤ_[p] → ℂ :=
  fun u => χ.1 (PadicInt.toZModPow n u)

theorem continuous_fieldOnePadicPrimitiveAngularLift (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Continuous (fieldOnePadicPrimitiveAngularLift p n χ) := by
  exact (continuous_of_discreteTopology : Continuous (χ.1 : ZMod (p ^ n) → ℂ)).comp
    (fieldOnePadicInt_toZModPow_continuous p n)

theorem integrable_fieldOnePadicPrimitiveAngularLift (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Integrable (fieldOnePadicPrimitiveAngularLift p n χ)
      (fieldOnePadicIntNormalizedHaar p) := by
  exact (continuous_fieldOnePadicPrimitiveAngularLift p n χ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fieldOnePadicPrimitiveAngularLift_period (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (x z : ℤ_[p]) :
    fieldOnePadicPrimitiveAngularLift p n χ
        (x + (p : ℤ_[p]) ^ n * z) =
      fieldOnePadicPrimitiveAngularLift p n χ x := by
  unfold fieldOnePadicPrimitiveAngularLift
  congr 1
  rw [map_add, map_mul, map_pow, map_natCast]
  have hp : ((p : ZMod (p ^ n)) ^ n) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp, zero_mul, add_zero]

/-- Exact finite-conductor local Fourier functional equation on `ℤ_p`.
The Haar Fourier coefficient of a primitive angular character is its inverse
character multiplied by the probability-normalized Gauss sum. -/
theorem fieldOnePadicPrimitiveAngular_fourierIntegral
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (k : ZMod (p ^ n)) :
    fieldOnePadicIntCyclicFourierIntegral p n
        (fieldOnePadicPrimitiveAngularLift p n χ) k =
      (((p ^ n : ℕ) : ℂ)⁻¹ * χ.1⁻¹ (-k)) *
        gaussSum χ.1 ZMod.stdAddChar := by
  rw [fieldOnePadicIntCyclicFourierIntegral_eq p n
    (fieldOnePadicPrimitiveAngularLift p n χ)
    (integrable_fieldOnePadicPrimitiveAngularLift p n χ)
    (fieldOnePadicPrimitiveAngularLift_period p n χ)]
  unfold fieldOnePadicIntCyclicFourier
  have hsamples :
      (fun r : ZMod (p ^ n) =>
          fieldOnePadicPrimitiveAngularLift p n χ
            (fieldOnePadicIntResidueRep p n r)) = χ.1 := by
    funext r
    unfold fieldOnePadicPrimitiveAngularLift
    rw [fieldOnePadicIntResidueRep_spec]
  rw [hsamples, χ.2.fourierTransform_eq_inv_mul_gaussSum]
  ring

/-- The Gauss sum at an exact prime-power conductor has the expected square
norm.  This is the finite-place unitarity normalization in Tate's local
functional equation. -/
theorem normSq_gaussSum_fieldOnePadicPrimitiveAngularCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Complex.normSq (gaussSum χ.1 ZMod.stdAddChar) = (p ^ n : ℝ) := by
  let N := p ^ n
  let C : ℝ := ∑ a : ZMod N, Complex.normSq (χ.1 a)
  have hCpos : 0 < C := by
    have hone : Complex.normSq (χ.1 (1 : ZMod N)) = 1 := by
      simp [Complex.normSq_eq_norm_sq]
    have hle : Complex.normSq (χ.1 (1 : ZMod N)) ≤ C := by
      exact Finset.single_le_sum
        (fun a _ => Complex.normSq_nonneg (χ.1 a)) (Finset.mem_univ _)
    linarith
  have hinvNorm (a : ZMod N) :
      Complex.normSq (χ.1⁻¹ a) = Complex.normSq (χ.1 a) := by
    by_cases ha : IsUnit a
    · rw [← ha.unit_spec]
      simp only [Complex.normSq_eq_norm_sq]
      rw [DirichletCharacter.unit_norm_eq_one,
        DirichletCharacter.unit_norm_eq_one]
    · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]
  have hinvSum :
      ∑ k : ZMod N, Complex.normSq (χ.1⁻¹ (-k)) = C := by
    calc
      _ = ∑ k : ZMod N, Complex.normSq (χ.1⁻¹ k) := by
        exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun k => by simp)
      _ = C := by
        simp only [C]
        exact Finset.sum_congr rfl (fun k _ => hinvNorm k)
  have hparse := fieldOneFiniteCyclicFourier_parseval N χ.1
  simp_rw [χ.2.fourierTransform_eq_inv_mul_gaussSum,
    Complex.normSq_mul] at hparse
  rw [← Finset.sum_mul, hinvSum] at hparse
  change C * Complex.normSq (gaussSum χ.1 ZMod.stdAddChar) =
      (N : ℝ) * C at hparse
  apply mul_left_cancel₀ hCpos.ne'
  calc
    C * Complex.normSq (gaussSum χ.1 ZMod.stdAddChar) =
        (N : ℝ) * C := hparse
    _ = C * (N : ℝ) := mul_comm _ _
    _ = C * (p : ℝ) ^ n := by simp only [N, Nat.cast_pow]

theorem norm_gaussSum_fieldOnePadicPrimitiveAngularCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    ‖gaussSum χ.1 ZMod.stdAddChar‖ = Real.sqrt ((p : ℝ) ^ n) := by
  have hsquare : ‖gaussSum χ.1 ZMod.stdAddChar‖ ^ 2 = (p : ℝ) ^ n := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_gaussSum_fieldOnePadicPrimitiveAngularCharacter p n χ
  have hrootSquare : (Real.sqrt ((p : ℝ) ^ n)) ^ 2 = (p : ℝ) ^ n := by
    exact Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (gaussSum χ.1 ZMod.stdAddChar),
    Real.sqrt_nonneg ((p : ℝ) ^ n)]

/-- Probability-normalized primitive Gauss phase. -/
def fieldOnePadicPrimitiveGaussPhase
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) : ℂ :=
  (Real.sqrt ((p : ℝ) ^ n) : ℂ)⁻¹ * gaussSum χ.1 ZMod.stdAddChar

theorem norm_fieldOnePadicPrimitiveGaussPhase
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    ‖fieldOnePadicPrimitiveGaussPhase p n χ‖ = 1 := by
  rw [fieldOnePadicPrimitiveGaussPhase, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    norm_gaussSum_fieldOnePadicPrimitiveAngularCharacter]
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (pow_pos hpR n)).ne'

/-- Unitary form of the finite local Tate equation: after the square-root
Haar normalization, additive Fourier transform exchanges a primitive
angular character with its inverse and multiplies by a unit phase. -/
theorem fieldOnePadicPrimitiveAngular_unitaryFourierIntegral
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (k : ZMod (p ^ n)) :
    (Real.sqrt ((p : ℝ) ^ n) : ℂ) *
        fieldOnePadicIntCyclicFourierIntegral p n
          (fieldOnePadicPrimitiveAngularLift p n χ) k =
      χ.1⁻¹ (-k) * fieldOnePadicPrimitiveGaussPhase p n χ := by
  rw [fieldOnePadicPrimitiveAngular_fourierIntegral p n χ k]
  unfold fieldOnePadicPrimitiveGaussPhase
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpow : 0 < (p : ℝ) ^ n := pow_pos hpR n
  have hsqrtSquare :
      ((Real.sqrt ((p : ℝ) ^ n) : ℂ) ^ 2) = ((p ^ n : ℕ) : ℂ) := by
    norm_cast
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hN : (((p ^ n : ℕ) : ℂ)⁻¹) =
      ((Real.sqrt ((p : ℝ) ^ n) : ℂ)⁻¹) ^ 2 := by
    rw [← hsqrtSquare, inv_pow]
  rw [hN]
  have hsqrt0 : (Real.sqrt ((p : ℝ) ^ n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpow).ne'
  field_simp

/-! ## Literal `ℚ_p` character packet -/

def fieldOnePadicUnitBall : Set ℚ_[p] :=
  Set.range ((↑) : ℤ_[p] → ℚ_[p])

theorem fieldOnePadicUnitBall_isClopen :
    IsClopen (fieldOnePadicUnitBall p) := by
  constructor
  · have hball : fieldOnePadicUnitBall p =
        Metric.closedBall (0 : ℚ_[p]) 1 := by
      ext x
      simp [fieldOnePadicUnitBall, Metric.mem_closedBall,
        dist_eq_norm_sub]
    rw [hball]
    exact (isCompact_closedBall (0 : ℚ_[p]) 1).isClosed
  · exact PadicInt.isOpenEmbedding_coe.isOpen_range

noncomputable def fieldOnePadicUnitBallHomeomorph :
    ℤ_[p] ≃ₜ fieldOnePadicUnitBall p :=
  PadicInt.isOpenEmbedding_coe.isEmbedding.toHomeomorph

def fieldOnePadicPrimitiveAngularLiftLocallyConstant
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    LocallyConstant ℤ_[p] ℂ where
  toFun := fieldOnePadicPrimitiveAngularLift p n χ
  isLocallyConstant :=
    ((IsLocallyConstant.iff_continuous
      (PadicInt.toZModPow (p := p) n)).2
        (fieldOnePadicInt_toZModPow_continuous p n)).comp χ.1

noncomputable def fieldOnePadicPrimitiveAngularOnUnitBall
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    LocallyConstant (fieldOnePadicUnitBall p) ℂ :=
  LocallyConstant.comap
    ⟨(fieldOnePadicUnitBallHomeomorph p).symm,
      (fieldOnePadicUnitBallHomeomorph p).symm.continuous⟩
    (fieldOnePadicPrimitiveAngularLiftLocallyConstant p n χ)

noncomputable def fieldOnePadicPrimitiveAngularPacketLC
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    LocallyConstant ℚ_[p] ℂ := by
  classical
  exact LocallyConstant.piecewise
    (fieldOnePadicUnitBall_isClopen p).isClosed
    (fieldOnePadicUnitBall_isClopen p).compl.isClosed
    (Set.union_compl_self (fieldOnePadicUnitBall p))
    (fieldOnePadicPrimitiveAngularOnUnitBall p n χ)
    (LocallyConstant.const ↥((fieldOnePadicUnitBall p)ᶜ) (0 : ℂ))
    (fun x hx => (hx.2 hx.1).elim)

theorem fieldOnePadicPrimitiveAngularPacketLC_coe
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]) :
    fieldOnePadicPrimitiveAngularPacketLC p n χ (u : ℚ_[p]) =
      fieldOnePadicPrimitiveAngularLift p n χ u := by
  classical
  have hu : (u : ℚ_[p]) ∈ fieldOnePadicUnitBall p :=
    ⟨u, rfl⟩
  rw [fieldOnePadicPrimitiveAngularPacketLC,
    LocallyConstant.piecewise_apply_left _ _ _ _ _ _ _ hu]
  change fieldOnePadicPrimitiveAngularLift p n χ
      ((fieldOnePadicUnitBallHomeomorph p).symm
        ⟨(u : ℚ_[p]), hu⟩) = _
  rw [show ⟨(u : ℚ_[p]), hu⟩ =
      fieldOnePadicUnitBallHomeomorph p u by
    apply Subtype.ext
    rfl]
  simp

theorem fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    {x : ℚ_[p]} (hx : x ∉ fieldOnePadicUnitBall p) :
    fieldOnePadicPrimitiveAngularPacketLC p n χ x = 0 := by
  classical
  rw [fieldOnePadicPrimitiveAngularPacketLC,
    LocallyConstant.piecewise_apply_right _ _ _ _ _ _ _
      (Set.mem_compl hx)]
  rfl

theorem fieldOnePadicPrimitiveAngularPacketLC_hasCompactSupport
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    HasCompactSupport
      (fieldOnePadicPrimitiveAngularPacketLC p n χ : ℚ_[p] → ℂ) := by
  have hcompact : IsCompact (fieldOnePadicUnitBall p) := by
    have hball : fieldOnePadicUnitBall p =
        Metric.closedBall (0 : ℚ_[p]) 1 := by
      ext x
      simp [fieldOnePadicUnitBall, Metric.mem_closedBall,
        dist_eq_norm_sub]
    rw [hball]
    exact isCompact_closedBall (0 : ℚ_[p]) 1
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro x hx
  by_contra hout
  exact hx (fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem
    p n χ hout)

noncomputable def fieldOnePadicPrimitiveAngularPacket
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ⟨fieldOnePadicPrimitiveAngularPacketLC p n χ,
    fieldOnePadicPrimitiveAngularPacketLC_hasCompactSupport p n χ⟩

theorem fieldOnePadicPrimitiveAngularPacket_support
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    tsupport
        ((fieldOnePadicPrimitiveAngularPacket p n χ).1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p 0 := by
  have hclosed : IsClosed (fieldOnePadicUnitBall p) :=
    (fieldOnePadicUnitBall_isClopen p).isClosed
  have hsupport : Function.support
      (fieldOnePadicPrimitiveAngularPacketLC p n χ : ℚ_[p] → ℂ) ⊆
      fieldOnePadicUnitBall p := by
    intro x hx
    by_contra hout
    exact hx (fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem
      p n χ hout)
  have htop : tsupport
      (fieldOnePadicPrimitiveAngularPacketLC p n χ : ℚ_[p] → ℂ) ⊆
      fieldOnePadicUnitBall p :=
    closure_minimal hsupport hclosed
  intro x hx
  have hxU := htop hx
  rcases hxU with ⟨u, rfl⟩
  change ‖(p : ℚ_[p]) ^ 0 * (u : ℚ_[p])‖ ≤ 1
  simpa using u.property

theorem fieldOnePadicPrimitiveAngularPacket_period
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (x : ℚ_[p]) (z : ℤ_[p]) :
    (fieldOnePadicPrimitiveAngularPacket p n χ).1
        (x + (p : ℚ_[p]) ^ n * (z : ℚ_[p])) =
      (fieldOnePadicPrimitiveAngularPacket p n χ).1 x := by
  by_cases hx : x ∈ fieldOnePadicUnitBall p
  · obtain ⟨u : ℤ_[p], rfl⟩ := hx
    have hsum :
        (u : ℚ_[p]) + (p : ℚ_[p]) ^ n * (z : ℚ_[p]) =
          ((u + (p : ℤ_[p]) ^ n * z : ℤ_[p]) : ℚ_[p]) := by
      simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast]
    rw [hsum]
    change fieldOnePadicPrimitiveAngularPacketLC p n χ
        ((u + (p : ℤ_[p]) ^ n * z : ℤ_[p]) : ℚ_[p]) =
      fieldOnePadicPrimitiveAngularPacketLC p n χ (u : ℚ_[p])
    rw [
      fieldOnePadicPrimitiveAngularPacketLC_coe p n χ,
      fieldOnePadicPrimitiveAngularPacketLC_coe p n χ]
    exact fieldOnePadicPrimitiveAngularLift_period p n χ u z
  · have hsumout :
        x + (p : ℚ_[p]) ^ n * (z : ℚ_[p]) ∉
          fieldOnePadicUnitBall p := by
      intro hsum
      obtain ⟨u : ℤ_[p], hu⟩ := hsum
      apply hx
      refine ⟨u - (p : ℤ_[p]) ^ n * z, ?_⟩
      simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast]
      rw [hu]
      ring
    change fieldOnePadicPrimitiveAngularPacketLC p n χ
        (x + (p : ℚ_[p]) ^ n * (z : ℚ_[p])) =
      fieldOnePadicPrimitiveAngularPacketLC p n χ x
    rw [fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem
        p n χ hsumout,
      fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem p n χ hx]

/-- The literal Fourier transform is supported in the exact conductor's dual
denominator stage. -/
theorem fieldOnePadicPrimitiveAngularPacket_fourier_support
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Function.support (fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveAngularPacket p n χ)) ⊆
      fieldOnePadicDenominatorStage p n := by
  intro y hy
  by_contra hout
  exact hy (fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
    p n (fieldOnePadicPrimitiveAngularPacket p n χ)
    (fieldOnePadicPrimitiveAngularPacket_period p n χ) hout)

/-- Literal `ℚ_p` Fourier transform of the exact-conductor angular packet,
evaluated on its entire dual denominator stage. -/
theorem fieldOnePadicPrimitiveAngularPacket_fourier_invPow
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (v : ℤ_[p]) :
    fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveAngularPacket p n χ)
        (fieldOnePadicInvPowIntCoeAddMonoidHom p n v) =
      (((p ^ n : ℕ) : ℂ)⁻¹ *
        χ.1⁻¹ (-(PadicInt.toZModPow n v))) *
          gaussSum χ.1 ZMod.stdAddChar := by
  rw [fieldOnePadicBruhatFourier_invPow_coeff p 0 n
    (fieldOnePadicPrimitiveAngularPacket p n χ)
    (fieldOnePadicPrimitiveAngularPacket_support p n χ) v]
  simp only [pow_zero, one_mul]
  have hscaled : fieldOnePadicBruhatScaled p 0
      (fieldOnePadicPrimitiveAngularPacket p n χ) =
      fieldOnePadicPrimitiveAngularLift p n χ := by
    funext u
    change fieldOnePadicPrimitiveAngularPacketLC p n χ
      ((fieldOnePadicPrimeInvPowUnit p 0 : ℚ_[p]) * (u : ℚ_[p])) = _
    simp only [fieldOnePadicPrimeInvPowUnit, pow_zero, Units.val_one,
      one_mul]
    exact fieldOnePadicPrimitiveAngularPacketLC_coe p n χ u
  rw [hscaled,
    show 0 + n = n by omega]
  rw [fieldOnePadicPrimitiveAngular_fourierIntegral p n χ]

theorem fieldOnePadicPrimitiveAngularPacket_unitaryFourier_invPow
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (v : ℤ_[p]) :
    (Real.sqrt ((p : ℝ) ^ n) : ℂ) *
      fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveAngularPacket p n χ)
        (fieldOnePadicInvPowIntCoeAddMonoidHom p n v) =
      χ.1⁻¹ (-(PadicInt.toZModPow n v)) *
        fieldOnePadicPrimitiveGaussPhase p n χ := by
  rw [fieldOnePadicPrimitiveAngularPacket_fourier_invPow p n χ v]
  unfold fieldOnePadicPrimitiveGaussPhase
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpow : 0 < (p : ℝ) ^ n := pow_pos hpR n
  have hsqrtSquare :
      ((Real.sqrt ((p : ℝ) ^ n) : ℂ) ^ 2) = ((p ^ n : ℕ) : ℂ) := by
    norm_cast
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← hsqrtSquare, ← inv_pow]
  have hsqrt0 : (Real.sqrt ((p : ℝ) ^ n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpow).ne'
  field_simp

end
end GaloisForLFunctions.RHTower
