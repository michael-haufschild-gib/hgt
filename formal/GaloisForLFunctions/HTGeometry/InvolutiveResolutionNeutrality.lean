import GaloisForLFunctions.HTGeometry.ResolutionAmplification

/-!
# Involutive transport is resolution-neutral

Let `τ : X → X` be a continuous involution of a metric space.  The symmetrized distance
`d_τ(x, y) = d(x, y) + d(τ x, τ y)` is a metric inducing the same topology, and `τ` is an isometry
of `d_τ` because `τ² = id`.

For every isometric equivalence `τ`, pulling effects back along `τ` is a bijection of `[0,
1]`-valued
effects that preserves Lipschitz constants and integral contrasts.  Hence pushforward by `τ`
preserves the whole Lipschitz resolution-price curve,

`R_{(τ_* μ₀, τ_* μ₁)}(r) = R_{(μ₀, μ₁)}(r)`,

transporting a kernel along `τ` preserves its resolution amplification, and exact formations are
transported to exact formations of the pushed laws.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Isometric transport -/

section Isometric

variable {X : Type*} [MetricSpace X]

theorem lipNorm_comp_isometryEquiv (τ : X ≃ᵢ X) (g : X → ℝ) : lipNorm (g ∘ τ) = lipNorm g := by
  have key : ∀ (σ : X ≃ᵢ X) (g : X → ℝ), lipNorm (g ∘ σ) ≤ lipNorm g := by
    intro σ g
    refine le_iInf₂ fun K hK => ?_
    simpa using lipNorm_le (hK.comp σ.isometry.lipschitz)
  refine le_antisymm (key τ g) ?_
  have h := key τ.symm (g ∘ τ)
  have hg : (g ∘ τ) ∘ τ.symm = g := by
    funext x
    simp
  rwa [hg] at h

variable [MeasurableSpace X] [BorelSpace X]

theorem hahnEffectCurrent_map_isometryEquiv (P Q : Measure X) (τ : X ≃ᵢ X) (e : X → ℝ) :
    hahnEffectCurrent (P.map τ) (Q.map τ) e = hahnEffectCurrent P Q (e ∘ τ) := by
  have hP := integral_map_equiv τ.toHomeomorph.toMeasurableEquiv (μ := P) e
  have hQ := integral_map_equiv τ.toHomeomorph.toMeasurableEquiv (μ := Q) e
  simp only [Homeomorph.toMeasurableEquiv_coe, IsometryEquiv.coe_toHomeomorph] at hP hQ
  rw [hahnEffectCurrent, hahnEffectCurrent, hP, hQ]
  rfl

theorem lipschitzResolutionPrice_map_le (P Q : Measure X) (τ : X ≃ᵢ X) (r : ℝ) :
    lipschitzResolutionPrice (P.map τ) (Q.map τ) r ≤ lipschitzResolutionPrice P Q r := by
  refine le_iInf fun e => le_iInf fun he => le_iInf fun hr => ?_
  have h1 : ∀ x, (e ∘ τ.symm) x ∈ Icc (0 : ℝ) 1 := fun x => he _
  have h2 : r ≤ hahnEffectCurrent (P.map τ) (Q.map τ) (e ∘ τ.symm) := by
    rw [hahnEffectCurrent_map_isometryEquiv]
    have he' : (e ∘ τ.symm) ∘ τ = e := by
      funext x
      simp
    rwa [he']
  exact (lipschitzResolutionPrice_le _ _ h1 h2).trans (le_of_eq (lipNorm_comp_isometryEquiv _ _))

theorem map_map_isometryEquiv_symm (P : Measure X) (τ : X ≃ᵢ X) : (P.map τ).map τ.symm = P := by
  rw [Measure.map_map τ.symm.continuous.measurable τ.continuous.measurable]
  have : (τ.symm ∘ τ : X → X) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

/-- **(RP.24).**  Pushforward by an isometric equivalence preserves the whole price curve. -/
theorem lipschitzResolutionPrice_map_isometryEquiv (P Q : Measure X) (τ : X ≃ᵢ X) (r : ℝ) :
    lipschitzResolutionPrice (P.map τ) (Q.map τ) r = lipschitzResolutionPrice P Q r := by
  refine le_antisymm (lipschitzResolutionPrice_map_le P Q τ r) ?_
  have h := lipschitzResolutionPrice_map_le (P.map τ) (Q.map τ) τ.symm r
  rwa [map_map_isometryEquiv_symm, map_map_isometryEquiv_symm] at h

variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]

omit [MetricSpace X] [BorelSpace X] [MetricSpace Z] in
theorem kernelPullback_comap (K : Kernel X Z) {g : X → X} (hg : Measurable g) (f : Z → ℝ) :
    kernelPullback (K.comap g hg) f = kernelPullback K f ∘ g := by
  funext x
  rfl

/-- Transporting a kernel along an isometric equivalence preserves its amplification. -/
theorem resolutionAmplification_comap_isometryEquiv (K : Kernel X Z) (τ : X ≃ᵢ X) :
    resolutionAmplification (K.comap τ τ.continuous.measurable) = resolutionAmplification K := by
  unfold resolutionAmplification
  simp_rw [kernelPullback_comap, lipNorm_comp_isometryEquiv]

end Isometric

/-! ## The symmetrized metric -/

section Symmetrized

variable {X : Type*} [MetricSpace X]

/-- `d_τ(x, y) = d(x, y) + d(τ x, τ y)`. -/
def symmetrizedDist (τ : X → X) (x y : X) : ℝ := dist x y + dist (τ x) (τ y)

/-- `X` carrying the symmetrized metric `d_τ`. -/
def SymmetrizedSpace (X : Type*) (_τ : X → X) : Type _ := X

namespace SymmetrizedSpace

variable {τ : X → X}

instance [MeasurableSpace X] : MeasurableSpace (SymmetrizedSpace X τ) :=
  inferInstanceAs (MeasurableSpace X)

/-- **(RP.23).**  For continuous `τ`, `d_τ` is a metric inducing the topology of `X`. -/
instance instMetricSpace [Fact (Continuous τ)] : MetricSpace (SymmetrizedSpace X τ) :=
  @MetricSpace.ofDistTopology X _ (symmetrizedDist τ)
    (fun x => by simp [symmetrizedDist])
    (fun x y => by simp [symmetrizedDist, dist_comm])
    (fun x y z => by
      unfold symmetrizedDist
      linarith [dist_triangle x y z, dist_triangle (τ x) (τ y) (τ z)])
    (fun s => by
      rw [Metric.isOpen_iff]
      constructor
      · rintro h x hx
        obtain ⟨ε, hε, hball⟩ := h x hx
        refine ⟨ε, hε, fun y hy => hball ?_⟩
        rw [Metric.mem_ball, dist_comm]
        unfold symmetrizedDist at hy
        linarith [dist_nonneg (x := τ x) (y := τ y)]
      · rintro h x hx
        obtain ⟨ε, hε, hs⟩ := h x hx
        obtain ⟨δ, hδ, hδε⟩ :=
          Metric.continuous_iff.mp (Fact.out : Continuous τ) x (ε / 2) (half_pos hε)
        refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun y hy => hs y ?_⟩
        rw [Metric.mem_ball] at hy
        have h1 : dist y x < δ := hy.trans_le (min_le_left _ _)
        have h2 : dist y x < ε / 2 := hy.trans_le (min_le_right _ _)
        have h3 := hδε y h1
        unfold symmetrizedDist
        rw [dist_comm x y, dist_comm (τ x) (τ y)]
        linarith)
    (fun x y h => by
      unfold symmetrizedDist at h
      exact dist_eq_zero.mp
        (le_antisymm (by linarith [dist_nonneg (x := τ x) (y := τ y)]) dist_nonneg))

/-- The involution acting on `(X, d_τ)`. -/
def symmetrizedMap (τ : X → X) : SymmetrizedSpace X τ → SymmetrizedSpace X τ := τ

variable [Fact (Continuous τ)]

theorem dist_eq (x y : SymmetrizedSpace X τ) : dist x y = symmetrizedDist τ x y := rfl

/-- `d_τ` is compatible: it induces the original topology. -/
theorem topology_eq :
    (inferInstance : TopologicalSpace (SymmetrizedSpace X τ))
      = (inferInstance : TopologicalSpace X) := rfl

instance [MeasurableSpace X] [BorelSpace X] : BorelSpace (SymmetrizedSpace X τ) :=
  ⟨BorelSpace.measurable_eq (α := X)⟩

/-- An involution is an isometry of its symmetrized metric. -/
theorem isometry_of_involutive (hτ : Function.Involutive τ) : Isometry (symmetrizedMap τ) :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq, dist_eq, symmetrizedDist, symmetrizedDist]
    unfold symmetrizedMap
    rw [hτ x, hτ y, add_comm]

/-- The involution as an isometric equivalence of `(X, d_τ)`. -/
def involutionIsometryEquiv (hτ : Function.Involutive τ) :
    SymmetrizedSpace X τ ≃ᵢ SymmetrizedSpace X τ where
  toFun := symmetrizedMap τ
  invFun := symmetrizedMap τ
  left_inv := hτ
  right_inv := hτ
  isometry_toFun := isometry_of_involutive hτ

theorem coe_involutionIsometryEquiv (hτ : Function.Involutive τ) :
    (involutionIsometryEquiv hτ : SymmetrizedSpace X τ → SymmetrizedSpace X τ)
      = symmetrizedMap τ := rfl

theorem symm_involutionIsometryEquiv (hτ : Function.Involutive τ) :
    ((involutionIsometryEquiv hτ).symm : SymmetrizedSpace X τ → SymmetrizedSpace X τ)
      = symmetrizedMap τ := rfl

variable [MeasurableSpace X] [BorelSpace X]

theorem measurable_involution (hτ : Function.Involutive τ) : Measurable (symmetrizedMap τ) :=
  (involutionIsometryEquiv hτ).continuous.measurable

/-- **Theorem 7.1 (RP.24).**  Pushforward by the involution preserves the price curve of `d_τ`. -/
theorem lipschitzResolutionPrice_map_involution (hτ : Function.Involutive τ)
    (P Q : Measure (SymmetrizedSpace X τ)) (r : ℝ) :
    lipschitzResolutionPrice (P.map (symmetrizedMap τ)) (Q.map (symmetrizedMap τ)) r
      = lipschitzResolutionPrice P Q r :=
  lipschitzResolutionPrice_map_isometryEquiv P Q (involutionIsometryEquiv hτ) r

/-- **Theorem 7.1.**  Transporting a kernel along the involution preserves its amplification. -/
theorem resolutionAmplification_comap_involution {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    (hτ : Function.Involutive τ) (K : Kernel (SymmetrizedSpace X τ) Z) :
    resolutionAmplification (K.comap (symmetrizedMap τ) (measurable_involution hτ))
      = resolutionAmplification K :=
  resolutionAmplification_comap_isometryEquiv K (involutionIsometryEquiv hτ)

/-- **Theorem 7.1.**  The transported kernel forms the same target law exactly from the pushed
source law. -/
theorem isExactFormation_map_involution {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (hτ : Function.Involutive τ) (μ : Measure (SymmetrizedSpace X τ))
    {d : ℕ} (K : Kernel (SymmetrizedSpace X τ) (Fin d → Y)) (p : Measure Y)
    (hK : IsExactFormation μ K p) :
    IsExactFormation (μ.map (symmetrizedMap τ)) (K.comap (symmetrizedMap τ)
      (measurable_involution hτ)) p :=
  isExactFormation_homeomorph μ (involutionIsometryEquiv hτ).toHomeomorph K p hK

end SymmetrizedSpace

end Symmetrized

end GaloisForLFunctions.HTGeometry
