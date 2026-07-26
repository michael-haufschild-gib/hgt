/-
# Exact block localization for Bourgain's `A₆` curve

A consecutive block of normalized square-root-curve samples is exactly the
local sum used by the osculating-cell estimates.  No Taylor approximation
enters this identification.
-/
import GaloisForLFunctions.RHTower.BourgainA6PhysicalBox
import GaloisForLFunctions.RHTower.BourgainAnisotropicCellGrid

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Weighted block of samples
`(q+m)/N ↦ ((q+m)/N,((q+m)/N)²,((q+m)/N)^(3/2),
((q+m)/N)^(1/2))`. -/
def bourgainA6PhysicalBlockSum
    (N M q : ℕ) (c : Fin M → ℂ)
    (x : BourgainPhaseSpace) : ℂ :=
  ∑ m : Fin M,
    c m * bourgainUnitCharacter
      (bourgainSquareRootCurvePhase x
        (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)))

/-- A physical block is literally an exact local sum based at
`sqrt(q/N)`, with denominator `N`. -/
theorem bourgainA6PhysicalBlockSum_eq_exactLocalSum
    (N M q : ℕ) (c : Fin M → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainA6PhysicalBlockSum N M q c x =
      bourgainSquareRootExactLocalSum M (N : ℝ)
        (Real.sqrt ((q : ℝ) / (N : ℝ))) c x := by
  unfold bourgainA6PhysicalBlockSum bourgainSquareRootExactLocalSum
  apply Fintype.sum_congr
  intro m
  congr 2
  congr 1
  rw [Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ) / (N : ℝ))]
  push_cast
  ring

/-- Exact partition of a normalized `A₆` curve sum at scale `K*M` into
`K` consecutive blocks of length `M`. -/
theorem bourgainA6NormalizedCurveSum_mul_eq_sum_blocks
    (K M : ℕ) (x : BourgainPhaseSpace) :
    bourgainA6NormalizedCurveSum (K * M) x =
      ∑ i : Fin K,
        bourgainA6PhysicalBlockSum (K * M) M (M * i.1)
          (fun _ => 1) x := by
  unfold bourgainA6NormalizedCurveSum
  rw [← (finProdFinEquiv : Fin K × Fin M ≃ Fin (K * M)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  unfold bourgainA6PhysicalBlockSum
  apply Fintype.sum_congr
  intro m
  rw [one_mul]
  congr 2
  congr 1
  unfold bourgainIndex
  norm_cast
  rw [finProdFinEquiv_apply_val]
  simp only
  omega

/-- Block partition with every block rewritten as the exact local sum used by
the osculating-cell theorem. -/
theorem bourgainA6NormalizedCurveSum_mul_eq_sum_exactLocal
    (K M : ℕ) (x : BourgainPhaseSpace) :
    bourgainA6NormalizedCurveSum (K * M) x =
      ∑ i : Fin K,
        bourgainSquareRootExactLocalSum M (K * M : ℕ)
          (Real.sqrt (((M * i.1 : ℕ) : ℝ) / ((K * M : ℕ) : ℝ)))
          (fun _ => 1) x := by
  rw [bourgainA6NormalizedCurveSum_mul_eq_sum_blocks]
  apply Fintype.sum_congr
  intro i
  exact bourgainA6PhysicalBlockSum_eq_exactLocalSum
    (K * M) M (M * i.1) (fun _ => 1) x

/-- The base parameter of a nonempty block is positive. -/
theorem sqrt_natCast_div_pos
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    0 < Real.sqrt ((q : ℝ) / (N : ℝ)) := by
  apply Real.sqrt_pos.2
  positivity

/-- Ordered positive block starts give ordered square-root base
parameters. -/
theorem sqrt_natCast_div_lt
    {N q₁ q₂ : ℕ} (hN : 0 < N) (hq : q₁ < q₂) :
    Real.sqrt ((q₁ : ℝ) / (N : ℝ)) <
      Real.sqrt ((q₂ : ℝ) / (N : ℝ)) := by
  apply Real.sqrt_lt_sqrt (by positivity)
  exact div_lt_div_of_pos_right (by exact_mod_cast hq) (by positivity)

/-- Exact osculating-cell integral estimate specialized to two normalized
`A₆` blocks.  This is the local analytic input before physical-domain
covering and the Bourgain--Guth scale recurrence. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_translatedCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hq₁ : 0 < q₁) → (hq : q₁ < q₂) →
      ∀ (c₁ c₂ : Fin M → ℂ) (y : BourgainPhaseSpace),
      let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
      let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
      let hscale : (M : ℝ) / (N : ℝ) ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hM.ne')
          (Nat.cast_ne_zero.mpr hN.ne')
      let R : ℝ :=
        ‖((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            (sqrt_natCast_div_pos hN hq₁)
            (sqrt_natCast_div_lt hN hq)).symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
          (‖((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm :
              BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
            ((M : ℝ) ^ (2 : ℕ) / 2))
      let J : ENNReal :=
        ENNReal.ofReal
          |((((M : ℝ) / (N : ℝ)) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹|
      let B : ℝ :=
        ((M : ℝ) ^ (3 : ℕ) *
          (C * (M : ℝ) ^ (ε / 2) *
            (∑ n : Fin M, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) *
        ((M : ℝ) ^ (3 : ℕ) *
          (C * (M : ℝ) ^ (ε / 2) *
            (∑ n : Fin M, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)))
      (∫⁻ z in bourgainTranslatedOsculatingFundamentalCell
          M ((M : ℝ) / (N : ℝ)) a b y,
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ c₁ z‖ ^ (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ c₂ z‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (J * ENNReal.ofReal B +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  R a b ((M : ℝ) / (N : ℝ)) c₁ c₂) *
              (J * ENNReal.ofReal ((M : ℝ) ^ (6 : ℕ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_translatedFundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hq₁ hq c₁ c₂ y
  simpa only [bourgainA6PhysicalBlockSum_eq_exactLocalSum] using
    hbound M hM
      (show (0 : ℝ) < N by exact_mod_cast hN)
      (sqrt_natCast_div_pos hN hq₁)
      (sqrt_natCast_div_lt hN hq)
      c₁ c₂ y

end

end RHTower
