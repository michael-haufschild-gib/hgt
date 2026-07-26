/-
# Exact local moment transfer for Bourgain's square-root curve

The quadratic planar estimate is stable under the cubic Taylor remainder.
This module keeps the loss explicit: a factor `1024` from two sixth powers
and a finite cube-volume error term.  No suppressed multiplier is assumed.
-/
import GaloisForLFunctions.RHTower.BourgainPhaseOperatorBounds

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem mul_pow_six_le_perturbed
    {x y a b e f : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (hx : x ≤ a + e) (hy : y ≤ b + f) :
    x ^ (6 : ℕ) * y ^ (6 : ℕ) ≤
      1024 *
        (a ^ (6 : ℕ) * b ^ (6 : ℕ) +
          a ^ (6 : ℕ) * f ^ (6 : ℕ) +
          e ^ (6 : ℕ) * b ^ (6 : ℕ) +
          e ^ (6 : ℕ) * f ^ (6 : ℕ)) := by
  have hxpow :
      x ^ (6 : ℕ) ≤
        32 * (a ^ (6 : ℕ) + e ^ (6 : ℕ)) := by
    calc
      x ^ (6 : ℕ) ≤ (a + e) ^ (6 : ℕ) :=
        pow_le_pow_left₀ hx0 hx 6
      _ ≤ 2 ^ (6 - 1) * (a ^ (6 : ℕ) + e ^ (6 : ℕ)) :=
        add_pow_le ha0 he0 6
      _ = _ := by norm_num
  have hypow :
      y ^ (6 : ℕ) ≤
        32 * (b ^ (6 : ℕ) + f ^ (6 : ℕ)) := by
    calc
      y ^ (6 : ℕ) ≤ (b + f) ^ (6 : ℕ) :=
        pow_le_pow_left₀ hy0 hy 6
      _ ≤ 2 ^ (6 - 1) * (b ^ (6 : ℕ) + f ^ (6 : ℕ)) :=
        add_pow_le hb0 hf0 6
      _ = _ := by norm_num
  calc
    x ^ (6 : ℕ) * y ^ (6 : ℕ) ≤
        (32 * (a ^ (6 : ℕ) + e ^ (6 : ℕ))) *
          (32 * (b ^ (6 : ℕ) + f ^ (6 : ℕ))) := by
      exact mul_le_mul hxpow hypow (pow_nonneg hy0 6)
        (mul_nonneg (by norm_num) (add_nonneg
          (pow_nonneg ha0 6) (pow_nonneg he0 6)))
    _ = _ := by ring

theorem norm_bourgainSquareRootQuadraticLocalSum_le_l1
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    ‖bourgainSquareRootQuadraticLocalSum H D a c x‖ ≤
      ∑ n : Fin H, ‖c n‖ := by
  unfold bourgainSquareRootQuadraticLocalSum
  calc
    ‖∑ n : Fin H,
        c n * bourgainUnitCharacter
          (bourgainSquareRootQuadraticLocalPhase a x
            ((bourgainIndex n : ℝ) / D))‖ ≤
        ∑ n : Fin H,
          ‖c n * bourgainUnitCharacter
            (bourgainSquareRootQuadraticLocalPhase a x
              ((bourgainIndex n : ℝ) / D))‖ :=
      norm_sum_le _ _
    _ = ∑ n : Fin H, ‖c n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_bourgainUnitCharacter, mul_one]

/-- Uniform Taylor error on the physical frequency cube `‖x‖ ≤ N`. -/
def bourgainSquareRootLocalTaylorError
    (N a δ : ℝ) {H : ℕ} (c : Fin H → ℂ) : ℝ :=
  (2 * Real.pi *
    ((N * bourgainSquareRootThirdDerivativeBound a) *
      δ ^ (3 : ℕ) / 2)) *
    ∑ n : Fin H, ‖c n‖

theorem bourgainSquareRootLocalTaylorError_nonneg
    {N a δ : ℝ} (hN : 0 ≤ N) (ha : 0 < a) (hδ : 0 ≤ δ)
    {H : ℕ} (c : Fin H → ℂ) :
    0 ≤ bourgainSquareRootLocalTaylorError N a δ c := by
  unfold bourgainSquareRootLocalTaylorError
  unfold bourgainSquareRootThirdDerivativeBound
  positivity

theorem norm_bourgainSquareRootExactLocalSum_le_quadratic_uniform
    (H : ℕ) {D a δ N : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace)
    (hx : ‖x‖ ≤ N)
    (hsample :
      ∀ n : Fin H,
        a ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (a ^ 2) (a ^ 2 + δ)) :
    ‖bourgainSquareRootExactLocalSum H D a c x‖ ≤
      ‖bourgainSquareRootQuadraticLocalSum H D a c x‖ +
        bourgainSquareRootLocalTaylorError N a δ c := by
  refine
    (norm_bourgainSquareRootExactLocalSum_le_quadratic_explicit
      H ha hδ c x hsample).trans ?_
  apply add_le_add le_rfl
  unfold bourgainSquareRootLocalTaylorError
  have hbound : 0 ≤ bourgainSquareRootThirdDerivativeBound a := by
    unfold bourgainSquareRootThirdDerivativeBound
    positivity
  gcongr

/-- The three error terms left after expanding the product of two perturbed
sixth powers. -/
def bourgainSquareRootBilinearTaylorError
    (N a b δ : ℝ) {H : ℕ} (c₁ c₂ : Fin H → ℂ) : ℝ :=
  let S₁ := ∑ n : Fin H, ‖c₁ n‖
  let S₂ := ∑ n : Fin H, ‖c₂ n‖
  let E₁ := bourgainSquareRootLocalTaylorError N a δ c₁
  let E₂ := bourgainSquareRootLocalTaylorError N b δ c₂
  S₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) +
    E₁ ^ (6 : ℕ) * S₂ ^ (6 : ℕ) +
    E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ)

theorem bourgainSquareRootBilinearTaylorError_nonneg
    {N a b δ : ℝ} (hN : 0 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 ≤ δ)
    {H : ℕ} (c₁ c₂ : Fin H → ℂ) :
    0 ≤ bourgainSquareRootBilinearTaylorError N a b δ c₁ c₂ := by
  unfold bourgainSquareRootBilinearTaylorError
  have hE₁ :=
    bourgainSquareRootLocalTaylorError_nonneg hN ha hδ c₁
  have hE₂ :=
    bourgainSquareRootLocalTaylorError_nonneg hN hb hδ c₂
  positivity

theorem exactLocalSum_bilinearIntegrand_le_quadratic_add_error
    (H : ℕ) {D a b δ N : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hN : 0 ≤ N)
    (c₁ c₂ : Fin H → ℂ) (x : BourgainPhaseSpace)
    (hx : ‖x‖ ≤ N)
    (hsamplea :
      ∀ n : Fin H,
        a ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (a ^ 2) (a ^ 2 + δ))
    (hsampleb :
      ∀ n : Fin H,
        b ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (b ^ 2) (b ^ 2 + δ)) :
    ‖bourgainSquareRootExactLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainSquareRootExactLocalSum H D b c₂ x‖ ^ (6 : ℕ) ≤
      1024 *
        (‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^ (6 : ℕ) +
          bourgainSquareRootBilinearTaylorError N a b δ c₁ c₂) := by
  let A := ‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖
  let B := ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖
  let E₁ := bourgainSquareRootLocalTaylorError N a δ c₁
  let E₂ := bourgainSquareRootLocalTaylorError N b δ c₂
  let S₁ := ∑ n : Fin H, ‖c₁ n‖
  let S₂ := ∑ n : Fin H, ‖c₂ n‖
  have hE₁ : 0 ≤ E₁ :=
    bourgainSquareRootLocalTaylorError_nonneg hN ha hδ.le c₁
  have hE₂ : 0 ≤ E₂ :=
    bourgainSquareRootLocalTaylorError_nonneg hN hb hδ.le c₂
  have hA : A ≤ S₁ :=
    norm_bourgainSquareRootQuadraticLocalSum_le_l1 H D a c₁ x
  have hB : B ≤ S₂ :=
    norm_bourgainSquareRootQuadraticLocalSum_le_l1 H D b c₂ x
  have hbase :=
    mul_pow_six_le_perturbed
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hE₁ hE₂
      (norm_bourgainSquareRootExactLocalSum_le_quadratic_uniform
        H ha hδ c₁ x hx hsamplea)
      (norm_bourgainSquareRootExactLocalSum_le_quadratic_uniform
        H hb hδ c₂ x hx hsampleb)
  calc
    ‖bourgainSquareRootExactLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainSquareRootExactLocalSum H D b c₂ x‖ ^ (6 : ℕ) ≤
      1024 *
        (A ^ (6 : ℕ) * B ^ (6 : ℕ) +
          A ^ (6 : ℕ) * E₂ ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * B ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ)) := hbase
    _ ≤ 1024 *
        (A ^ (6 : ℕ) * B ^ (6 : ℕ) +
          S₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * S₂ ^ (6 : ℕ) +
          E₁ ^ (6 : ℕ) * E₂ ^ (6 : ℕ)) := by
      gcongr
    _ = _ := by
      simp [A, B, E₁, E₂, S₁, S₂,
        bourgainSquareRootBilinearTaylorError]
      ring

/-- Exact local square-root sums inherit the quadratic bilinear estimate,
with the full Taylor-remainder contribution displayed as a cube-volume
term. -/
theorem setLIntegral_bourgainSquareRootExactLocalSum_bilinear_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N D δ : ℝ},
        (ha₀ : 0 < a₀) → (ha₀b₀ : a₀ < b₀) →
        (hN : 0 ≤ N) → (hD : D ≠ 0) → (hδ : 0 < δ) →
      ∀ (H : ℕ), (hH : 0 < H) → ∀ (c₁ c₂ : Fin H → ℂ),
      (∀ n : Fin H,
        a₀ ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (a₀ ^ 2) (a₀ ^ 2 + δ)) →
      (∀ n : Fin H,
        b₀ ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (b₀ ^ 2) (b₀ ^ 2 + δ)) →
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD) :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        (‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            (a := a₀) (b := b₀) ha₀ ha₀b₀ :
            (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N) ≤
          (H : ℝ) ^ (2 : ℕ) / 2 →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
              |(3 * (b₀ - a₀) ^ (4 : ℕ) /
                (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
            ENNReal.ofReal |(((H : ℝ) / D) ^ (6 : ℕ))⁻¹| *
            ENNReal.ofReal
              ((H : ℝ) ^ (8 : ℕ) *
                (C * (H : ℝ) ^ ε *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  N a₀ b₀ δ c₁ c₂) *
              ENNReal.ofReal ((2 * N) ^ (4 : ℕ))) := by
  obtain ⟨C, hC, hquad⟩ :=
    setLIntegral_bourgainSquareRootQuadraticLocalSum_bilinear_subpower hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N D δ ha₀ ha₀b₀ hN hD hδ H hH c₁ c₂
    hsamplea hsampleb hfit
  let Q : (Fin 4 → ℝ) → ℝ := fun x =>
    ‖bourgainSquareRootQuadraticLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
      ‖bourgainSquareRootQuadraticLocalSum H D b₀ c₂ x‖ ^ (6 : ℕ)
  let K : ℝ :=
    bourgainSquareRootBilinearTaylorError N a₀ b₀ δ c₁ c₂
  have hb₀ : 0 < b₀ := ha₀.trans ha₀b₀
  have hK : 0 ≤ K :=
    bourgainSquareRootBilinearTaylorError_nonneg
      hN ha₀ hb₀ hδ.le c₁ c₂
  have hQ0 (x : Fin 4 → ℝ) : 0 ≤ Q x := by
    unfold Q
    positivity
  have hQmeas : Measurable fun x => ENNReal.ofReal (Q x) := by
    let P : (Fin 4 → ℝ) → ENNReal := fun y =>
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂ y)
    have hP : Measurable P :=
      measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
        H c₁ c₂
    have hscale : (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD
    have hcomp : Measurable fun x =>
        P (bourgainParabolaPhaseScale ((H : ℝ) / D)
          (bourgainSquareRootPhaseCoordinates a₀ b₀ x)) := by
      apply hP.comp
      have heq :
          (fun x =>
            bourgainParabolaPhaseScale ((H : ℝ) / D)
              (bourgainSquareRootPhaseCoordinates a₀ b₀ x)) =
            fun x =>
              bourgainParabolaPhaseScaleContinuousLinearEquiv hscale
                (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
                  ha₀ ha₀b₀ x) := by
        funext x
        rw [bourgainParabolaPhaseScaleContinuousLinearEquiv_apply,
          bourgainSquareRootPhaseCoordinateContinuousLinearEquiv_apply]
      rw [heq]
      exact
        ((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).continuous.comp
          (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            ha₀ ha₀b₀).continuous).measurable
    convert hcomp using 1
    funext x
    unfold P Q
    rw [quadraticLocalSum_bilinearIntegrand_eq H hH hD]
  have hquadBound :=
    hquad ha₀ ha₀b₀ hD H hH c₁ c₂ hfit
  have hpoint (x : Fin 4 → ℝ) (hx : ‖x‖ ≤ N) :
      ‖bourgainSquareRootExactLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainSquareRootExactLocalSum H D b₀ c₂ x‖ ^ (6 : ℕ) ≤
        1024 * (Q x + K) := by
    exact exactLocalSum_bilinearIntegrand_le_quadratic_add_error
      H ha₀ hb₀ hδ hN c₁ c₂ x hx hsamplea hsampleb
  have hRhsMeas : Measurable fun x =>
      ENNReal.ofReal (1024 * (Q x + K)) := by
    have heq : (fun x =>
        ENNReal.ofReal (1024 * (Q x + K))) =
        fun x => (1024 : ENNReal) *
          (ENNReal.ofReal (Q x) + ENNReal.ofReal K) := by
      funext x
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1024 by norm_num),
        ENNReal.ofReal_add (hQ0 x) hK]
      norm_num
    rw [heq]
    fun_prop
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) ≤
        ∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
          ENNReal.ofReal (1024 * (Q x + K)) := by
      apply setLIntegral_mono hRhsMeas
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hpoint x hx)
    _ = (1024 : ENNReal) *
        ((∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
            ENNReal.ofReal (Q x)) +
          ENNReal.ofReal K *
            ENNReal.ofReal ((2 * N) ^ (4 : ℕ))) := by
      have hformula :
          (fun x : Fin 4 → ℝ =>
            ENNReal.ofReal (1024 * (Q x + K))) =
          fun x => (1024 : ENNReal) *
            (ENNReal.ofReal (Q x) + ENNReal.ofReal K) := by
        funext x
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1024 by norm_num),
          ENNReal.ofReal_add (hQ0 x) hK]
        norm_num
      have hsummeas : Measurable fun x =>
          ENNReal.ofReal (Q x) + ENNReal.ofReal K :=
        hQmeas.add measurable_const
      rw [hformula, lintegral_const_mul _ hsummeas,
        lintegral_add_left hQmeas, setLIntegral_const,
        volume_fin_four_normCube hN]
    _ ≤ _ := by
      gcongr

theorem bourgainSquareRootLocalSample_mem
    {H : ℕ} {D a : ℝ} (hD : 0 < D)
    (n : Fin H) :
    a ^ 2 + (bourgainIndex n : ℝ) / D ∈
      Set.Icc (a ^ 2) (a ^ 2 + (H : ℝ) / D) := by
  have hn0 : 0 ≤ (bourgainIndex n : ℝ) := by positivity
  have hnH : (bourgainIndex n : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast bourgainIndex_le n
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn0 hD.le)
  · exact add_le_add_right
      ((div_le_div_iff_of_pos_right hD).2 hnH) _

/-- Application-range version of the exact local estimate.  Sample
containment and both operator-norm fit conditions are discharged by
`H ≤ D` and the concrete physical-cube condition `12N ≤ H²`. -/
theorem setLIntegral_bourgainSquareRootExactLocalSum_bilinear_application
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N D : ℝ},
        (ha₀ : 1 / 2 ≤ a₀) → (ha₀b₀ : a₀ < b₀) →
        (hb₀ : b₀ ≤ 1) → (hN : 0 ≤ N) → (hD : 0 < D) →
      ∀ (H : ℕ), (hH : 0 < H) →
      (hHD : (H : ℝ) ≤ D) → ∀ (c₁ c₂ : Fin H → ℂ),
      12 * N ≤ (H : ℝ) ^ (2 : ℕ) →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
              |(3 * (b₀ - a₀) ^ (4 : ℕ) /
                (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
            ENNReal.ofReal |(((H : ℝ) / D) ^ (6 : ℕ))⁻¹| *
            ENNReal.ofReal
              ((H : ℝ) ^ (8 : ℕ) *
                (C * (H : ℝ) ^ ε *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  N a₀ b₀ ((H : ℝ) / D) c₁ c₂) *
              ENNReal.ofReal ((2 * N) ^ (4 : ℕ))) := by
  obtain ⟨C, hC, hlocal⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_bilinear_subpower hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N D ha₀ ha₀b₀ hb₀ hN hD H hH hHD c₁ c₂ hphysical
  have ha₀pos : 0 < a₀ := lt_of_lt_of_le (by norm_num) ha₀
  have hscale0 : 0 ≤ (H : ℝ) / D := by positivity
  have hscale1 : (H : ℝ) / D ≤ 1 :=
    (div_le_one hD).2 hHD
  have hscale : (H : ℝ) / D ≠ 0 := by positivity
  have hopScale :=
    opNorm_bourgainParabolaPhaseScale_le_one
      hscale hscale0 hscale1
  have hopPhase :=
    opNorm_bourgainSquareRootPhaseCoordinates_le_six
      ha₀ ha₀b₀ hb₀
  have hfit :
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        (‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            ha₀pos ha₀b₀ :
            (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N) ≤
          (H : ℝ) ^ (2 : ℕ) / 2 := by
    calc
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        (‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            ha₀pos ha₀b₀ :
            (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N) ≤
          1 * (6 * N) := by
        apply mul_le_mul hopScale
        · exact mul_le_mul_of_nonneg_right hopPhase hN
        · positivity
        · norm_num
      _ ≤ (H : ℝ) ^ (2 : ℕ) / 2 := by
        norm_num
        linarith
  exact hlocal ha₀pos ha₀b₀ hN hD.ne'
    (div_pos (Nat.cast_pos.mpr hH) hD)
    H hH c₁ c₂
    (bourgainSquareRootLocalSample_mem hD)
    (bourgainSquareRootLocalSample_mem hD)
    hfit

end

end RHTower
