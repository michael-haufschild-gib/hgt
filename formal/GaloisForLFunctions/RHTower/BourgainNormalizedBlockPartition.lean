/-
# Exact block partition for the normalized four-curve

Bourgain's Section 1 bootstrap repeatedly partitions an arithmetic sample
interval into consecutive blocks.  This module proves the exact finite-sum
identity for the generic normalized four-curve, the corresponding
coefficient `ℓ²` partition, and phase-translation invariance.
-/
import GaloisForLFunctions.RHTower.BourgainGenericPairedTripleFourierIdentity

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Restriction of a length-`K*H` coefficient vector to block `i`. -/
def bourgainGenericCurveBlockCoefficients
    (K H : ℕ) (c : Fin (K * H) → ℂ)
    (i : Fin K) : Fin H → ℂ :=
  fun m => c (finProdFinEquiv (i, m))

/-- Starting parameter of block `i`. -/
def bourgainGenericCurveBlockBase
    (H : ℕ) (D a : ℝ) (i : ℕ) : ℝ :=
  a + (H : ℝ) * i / D

/-- A length-`K*H` exact curve sum is exactly the sum of its `K`
consecutive length-`H` blocks. -/
theorem bourgainGenericFourCurveExactLocalSum_mul_eq_sum_blocks
    (K H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin (K * H) → ℂ) (x : BourgainPhaseSpace) :
    bourgainGenericFourCurveExactLocalSum
        (K * H) φ₃ φ₄ D a c x =
      ∑ i : Fin K,
        bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D
          (bourgainGenericCurveBlockBase H D a i.1)
          (bourgainGenericCurveBlockCoefficients K H c i) x := by
  unfold bourgainGenericFourCurveExactLocalSum
  rw [← (finProdFinEquiv : Fin K × Fin H ≃ Fin (K * H)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro m
  unfold bourgainGenericCurveBlockCoefficients
    bourgainGenericCurveBlockBase
  congr 2
  congr 1
  unfold bourgainIndex
  rw [finProdFinEquiv_apply_val]
  push_cast
  ring_nf

/-- Exact `ℓ²` mass partition across consecutive blocks. -/
theorem sum_sum_norm_sq_bourgainGenericCurveBlockCoefficients
    (K H : ℕ) (c : Fin (K * H) → ℂ) :
    (∑ i : Fin K,
      ∑ m : Fin H,
        ‖bourgainGenericCurveBlockCoefficients K H c i m‖ ^
          (2 : ℕ)) =
      ∑ n : Fin (K * H), ‖c n‖ ^ (2 : ℕ) := by
  rw [← (finProdFinEquiv : Fin K × Fin H ≃ Fin (K * H)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- Cubing the total coefficient mass costs exactly the elementary
`K²` block factor. -/
theorem sum_norm_sq_bourgainGenericCurveBlockCoefficients_pow_three
    (K H : ℕ) (c : Fin (K * H) → ℂ) :
    (∑ n : Fin (K * H), ‖c n‖ ^ (2 : ℕ)) ^ (3 : ℕ) ≤
      (K : ℝ) ^ (2 : ℕ) *
        ∑ i : Fin K,
          (∑ m : Fin H,
            ‖bourgainGenericCurveBlockCoefficients K H c i m‖ ^
              (2 : ℕ)) ^ (3 : ℕ) := by
  let mass : Fin K → ℝ := fun i =>
    ∑ m : Fin H,
      ‖bourgainGenericCurveBlockCoefficients K H c i m‖ ^ (2 : ℕ)
  have hmass (i : Fin K) : 0 ≤ mass i := by
    dsimp [mass]
    positivity
  have hpower :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin K)))
      (f := mass) (fun i hi => hmass i) 2
  have hpartition :
      (∑ i : Fin K, mass i) =
        ∑ n : Fin (K * H), ‖c n‖ ^ (2 : ℕ) := by
    exact
      sum_sum_norm_sq_bourgainGenericCurveBlockCoefficients K H c
  simpa only [hpartition, Finset.card_univ, Fintype.card_fin, mass]
    using hpower

/-- Product form of the cubic block-mass inequality for the two separated
curve pieces. -/
theorem mul_sum_norm_sq_pow_three_le_blockMass
    (K H : ℕ) (c₁ c₂ : Fin (K * H) → ℂ) :
    (∑ n : Fin (K * H), ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
        (∑ n : Fin (K * H), ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) ≤
      (K : ℝ) ^ (4 : ℕ) *
        (∑ i : Fin K,
          (∑ m : Fin H,
            ‖bourgainGenericCurveBlockCoefficients K H c₁ i m‖ ^
              (2 : ℕ)) ^ (3 : ℕ)) *
        (∑ i : Fin K,
          (∑ m : Fin H,
            ‖bourgainGenericCurveBlockCoefficients K H c₂ i m‖ ^
              (2 : ℕ)) ^ (3 : ℕ)) := by
  have h₁ :=
    sum_norm_sq_bourgainGenericCurveBlockCoefficients_pow_three K H c₁
  have h₂ :=
    sum_norm_sq_bourgainGenericCurveBlockCoefficients_pow_three K H c₂
  have hc₂0 :
      0 ≤ (∑ n : Fin (K * H), ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
    positivity
  have hblock₁0 :
      0 ≤ (K : ℝ) ^ (2 : ℕ) *
        ∑ i : Fin K,
          (∑ m : Fin H,
            ‖bourgainGenericCurveBlockCoefficients K H c₁ i m‖ ^
              (2 : ℕ)) ^ (3 : ℕ) := by
    positivity
  calc
    (∑ n : Fin (K * H), ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin (K * H), ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) ≤
        ((K : ℝ) ^ (2 : ℕ) *
          ∑ i : Fin K,
            (∑ m : Fin H,
              ‖bourgainGenericCurveBlockCoefficients K H c₁ i m‖ ^
                (2 : ℕ)) ^ (3 : ℕ)) *
        ((K : ℝ) ^ (2 : ℕ) *
          ∑ i : Fin K,
            (∑ m : Fin H,
              ‖bourgainGenericCurveBlockCoefficients K H c₂ i m‖ ^
                (2 : ℕ)) ^ (3 : ℕ)) :=
      mul_le_mul h₁ h₂ hc₂0 hblock₁0
    _ = _ := by ring

/-- Translate generic exact-curve coefficients by a unit phase. -/
def bourgainGenericExactLocalTranslateCoefficients
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) (y : BourgainPhaseSpace) :
    Fin H → ℂ :=
  fun n =>
    c n * bourgainUnitCharacter
      (bourgainDot y
        (bourgainGenericFourCurve φ₃ φ₄
          (a + (bourgainIndex n : ℝ) / D)))

@[simp] theorem norm_bourgainGenericExactLocalTranslateCoefficients
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) (y : BourgainPhaseSpace) (n : Fin H) :
    ‖bourgainGenericExactLocalTranslateCoefficients
        H φ₃ φ₄ D a c y n‖ = ‖c n‖ := by
  rw [bourgainGenericExactLocalTranslateCoefficients, norm_mul,
    norm_bourgainUnitCharacter, mul_one]

/-- Linearity of the phase pairing in its physical variable. -/
theorem bourgainDot_add
    (x y v : BourgainPhaseSpace) :
    bourgainDot (x + y) v =
      bourgainDot x v + bourgainDot y v := by
  unfold bourgainDot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Translation in physical phase space is exactly coefficient twisting. -/
theorem bourgainGenericFourCurveExactLocalSum_add
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) (x y : BourgainPhaseSpace) :
    bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D a c (x + y) =
      bourgainGenericFourCurveExactLocalSum H φ₃ φ₄ D a
        (bourgainGenericExactLocalTranslateCoefficients
          H φ₃ φ₄ D a c y) x := by
  unfold bourgainGenericFourCurveExactLocalSum
    bourgainGenericExactLocalTranslateCoefficients
  apply Fintype.sum_congr
  intro n
  rw [bourgainDot_add, bourgainUnitCharacter_add]
  ring

/-- Twisting preserves the full coefficient `ℓ²` mass. -/
theorem sum_norm_sq_bourgainGenericExactLocalTranslateCoefficients
    (H : ℕ) (φ₃ φ₄ : ℝ → ℝ) (D a : ℝ)
    (c : Fin H → ℂ) (y : BourgainPhaseSpace) :
    (∑ n : Fin H,
      ‖bourgainGenericExactLocalTranslateCoefficients
        H φ₃ φ₄ D a c y n‖ ^ (2 : ℕ)) =
      ∑ n : Fin H, ‖c n‖ ^ (2 : ℕ) := by
  apply Fintype.sum_congr
  intro n
  rw [norm_bourgainGenericExactLocalTranslateCoefficients]

end

end RHTower
