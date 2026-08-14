import GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCoreRigidity

/-!
# Triple-reporter fusion mechanics

Three jointly recoverable reporter organs generate a proper strictly convex
total energy. Their midpoint dissipation is exactly additive, nonlinear
no-loss selects one source law, and selection propagates to every fourth
continuous affine reporter.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter Topology

variable {E F₁ F₂ F₃ F₄ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [NormedAddCommGroup F₄] [NormedSpace ℝ F₄]

/-- Product of three linear reporter organs. -/
def tripleFusionReporter (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂)
    (R₃ : E →L[ℝ] F₃) : E →L[ℝ] F₁ × (F₂ × F₃) :=
  R₁.prod (R₂.prod R₃)

/-- Additive energy fused from three reporter organs. -/
def tripleFusionEnergy (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂)
    (R₃ : E →L[ℝ] F₃) (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ)
    (W₃ : F₃ → ℝ) (z : E) : ℝ :=
  W₁ (R₁ z) + W₂ (R₂ z) + W₃ (R₃ z)

/-- Jensen dissipation at the midpoint of two laws. -/
noncomputable def midpointDissipation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : V → ℝ) (a b : V) : ℝ :=
  (2 : ℝ)⁻¹ * W a + (2 : ℝ)⁻¹ * W b -
    W ((2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b)

/-- The fused midpoint dissipation is exactly the sum of the three organ
dissipations. -/
theorem tripleFusion_midpointDissipation_conservation
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ) (a b : E) :
    midpointDissipation (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃) a b =
      midpointDissipation W₁ (R₁ a) (R₁ b) +
      midpointDissipation W₂ (R₂ a) (R₂ b) +
      midpointDissipation W₃ (R₃ a) (R₃ b) := by
  simp only [midpointDissipation, tripleFusionEnergy, map_add, map_smul]
  ring

/-- A common decoder makes the triple reporter jointly injective. -/
theorem tripleFusionReporter_injective_of_recovery
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z) :
    Function.Injective (tripleFusionReporter R₁ R₂ R₃) := by
  intro a b hab
  rw [← hQR a, ← hQR b, hab]

/-- Joint reporter formation reconstructs the complete source law core. -/
theorem tripleFusionReporter_commonRecovery_asymptoticLawCore
    {x : ℕ → E} {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hx : ∀ n, x n ∈ K)
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z) :
    let R := tripleFusionReporter R₁ R₂ R₃
    R '' asymptoticLawCore x = asymptoticLawCore (R ∘ x) ∧
      Q '' asymptoticLawCore (R ∘ x) = asymptoticLawCore x := by
  dsimp
  exact commonRecovery_asymptoticLawCore hK hKconv hx
    (tripleFusionReporter R₁ R₂ R₃).toContinuousAffineMap
    Q.toContinuousAffineMap hQR

/-- Continuity of the fused energy is inherited from the three reporter
energies. -/
theorem continuous_tripleFusionEnergy
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ)
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₃ : Continuous W₃) :
    Continuous (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃) := by
  exact ((hW₁.comp R₁.continuous).add (hW₂.comp R₂.continuous)).add
    (hW₃.comp R₃.continuous)

/-- Strict convexity is generated jointly: no individual reporter need be
injective, because the common decoder makes the triple reporter injective. -/
theorem strictConvexOn_tripleFusionEnergy_of_commonRecovery
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ)
    (hW₁ : StrictConvexOn ℝ Set.univ W₁)
    (hW₂ : StrictConvexOn ℝ Set.univ W₂)
    (hW₃ : StrictConvexOn ℝ Set.univ W₃) :
    StrictConvexOn ℝ Set.univ
      (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃) := by
  constructor
  · exact (convex_univ : Convex ℝ (Set.univ : Set E))
  · intro a ha b hb hab α β hα hβ hsum
    have h₁le := hW₁.convexOn.2 (Set.mem_univ (R₁ a)) (Set.mem_univ (R₁ b))
      hα.le hβ.le hsum
    have h₂le := hW₂.convexOn.2 (Set.mem_univ (R₂ a)) (Set.mem_univ (R₂ b))
      hα.le hβ.le hsum
    have h₃le := hW₃.convexOn.2 (Set.mem_univ (R₃ a)) (Set.mem_univ (R₃ b))
      hα.le hβ.le hsum
    have hstrict :
        W₁ (α • R₁ a + β • R₁ b) + W₂ (α • R₂ a + β • R₂ b) +
            W₃ (α • R₃ a + β • R₃ b) <
          α • W₁ (R₁ a) + β • W₁ (R₁ b) +
            (α • W₂ (R₂ a) + β • W₂ (R₂ b)) +
            (α • W₃ (R₃ a) + β • W₃ (R₃ b)) := by
      by_cases h₁ne : R₁ a ≠ R₁ b
      · have h₁lt := hW₁.2 (Set.mem_univ (R₁ a)) (Set.mem_univ (R₁ b)) h₁ne hα hβ hsum
        linarith
      · have h₁eq : R₁ a = R₁ b := not_ne_iff.mp h₁ne
        by_cases h₂ne : R₂ a ≠ R₂ b
        · have h₂lt := hW₂.2 (Set.mem_univ (R₂ a)) (Set.mem_univ (R₂ b)) h₂ne hα hβ hsum
          linarith
        · have h₂eq : R₂ a = R₂ b := not_ne_iff.mp h₂ne
          have h₃ne : R₃ a ≠ R₃ b := by
            intro h₃eq
            apply hab
            apply tripleFusionReporter_injective_of_recovery R₁ R₂ R₃ Q hQR
            simp [tripleFusionReporter, h₁eq, h₂eq, h₃eq]
          have h₃lt := hW₃.2 (Set.mem_univ (R₃ a)) (Set.mem_univ (R₃ b)) h₃ne hα hβ hsum
          linarith
    dsimp only [tripleFusionEnergy]
    simp only [map_add, map_smul, smul_eq_mul]
    norm_num [smul_eq_mul] at hstrict
    linarith

/-- Compact sublevels fuse through common recovery. Nonnegativity prevents
cross-organ cancellation: bounded total energy bounds every component, and
the decoder pulls the compact product of component sublevels back over the
source sublevel. -/
theorem isCompact_sublevel_tripleFusionEnergy_of_commonRecovery
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ)
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₃ : Continuous W₃)
    (hW₁nonneg : ∀ u, 0 ≤ W₁ u) (hW₂nonneg : ∀ u, 0 ≤ W₂ u)
    (hW₃nonneg : ∀ u, 0 ≤ W₃ u)
    (hW₁proper : ∀ r : ℝ, IsCompact {u : F₁ | W₁ u ≤ r})
    (hW₂proper : ∀ r : ℝ, IsCompact {u : F₂ | W₂ u ≤ r})
    (hW₃proper : ∀ r : ℝ, IsCompact {u : F₃ | W₃ u ≤ r})
    (c : ℝ) :
    IsCompact {z : E | tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ z ≤ c} := by
  let K₁ : Set F₁ := {u : F₁ | W₁ u ≤ c}
  let K₂ : Set F₂ := {u : F₂ | W₂ u ≤ c}
  let K₃ : Set F₃ := {u : F₃ | W₃ u ≤ c}
  let KP : Set (F₁ × (F₂ × F₃)) := K₁ ×ˢ (K₂ ×ˢ K₃)
  have hKP : IsCompact KP := by
    exact (hW₁proper c).prod ((hW₂proper c).prod (hW₃proper c))
  have hQKP : IsCompact (Q '' KP) := hKP.image Q.continuous
  refine hQKP.of_isClosed_subset
    (isClosed_Iic.preimage
      (continuous_tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ hW₁ hW₂ hW₃)) ?_
  intro z hz
  have hzsum : W₁ (R₁ z) + W₂ (R₂ z) + W₃ (R₃ z) ≤ c := hz
  have h₁c : W₁ (R₁ z) ≤ c := by
    linarith [hW₂nonneg (R₂ z), hW₃nonneg (R₃ z)]
  have h₂c : W₂ (R₂ z) ≤ c := by
    linarith [hW₁nonneg (R₁ z), hW₃nonneg (R₃ z)]
  have h₃c : W₃ (R₃ z) ≤ c := by
    linarith [hW₁nonneg (R₁ z), hW₂nonneg (R₂ z)]
  refine ⟨tripleFusionReporter R₁ R₂ R₃ z, ?_, hQR z⟩
  exact ⟨h₁c, h₂c, h₃c⟩

/-- **Three-organ fusion selection.** Joint recovery, nonnegative component
properness, strict component convexity, convergent fused energy, and nonlinear
no-loss force one source law. No compact source carrier is assumed. -/
theorem tripleFusion_noLoss_selects_singleton_asymptoticLawCore
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ)
    (hW₁cont : Continuous W₁) (hW₂cont : Continuous W₂)
    (hW₃cont : Continuous W₃)
    (hW₁strict : StrictConvexOn ℝ Set.univ W₁)
    (hW₂strict : StrictConvexOn ℝ Set.univ W₂)
    (hW₃strict : StrictConvexOn ℝ Set.univ W₃)
    (hW₁nonneg : ∀ u, 0 ≤ W₁ u) (hW₂nonneg : ∀ u, 0 ≤ W₂ u)
    (hW₃nonneg : ∀ u, 0 ≤ W₃ u)
    (hW₁proper : ∀ r : ℝ, IsCompact {u : F₁ | W₁ u ≤ r})
    (hW₂proper : ∀ r : ℝ, IsCompact {u : F₂ | W₂ u ≤ r})
    (hW₃proper : ∀ r : ℝ, IsCompact {u : F₃ | W₃ u ≤ r})
    {x : ℕ → E} {c : ℝ}
    (hWx : Tendsto (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ ∘ x)
      atTop (𝓝 c))
    (hNoLoss :
      tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ '' asymptoticLawCore x ⊆
        asymptoticLawCore
          (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ ∘ x)) :
    ∃ a, asymptoticLawCore x = {a} := by
  apply properStrictConvex_asymptoticLawCore_singleton_of_noLoss
    (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃)
  · exact strictConvexOn_tripleFusionEnergy_of_commonRecovery
      R₁ R₂ R₃ Q hQR W₁ W₂ W₃ hW₁strict hW₂strict hW₃strict
  · intro r
    exact isCompact_sublevel_tripleFusionEnergy_of_commonRecovery
      R₁ R₂ R₃ Q hQR W₁ W₂ W₃ hW₁cont hW₂cont hW₃cont
      hW₁nonneg hW₂nonneg hW₃nonneg hW₁proper hW₂proper hW₃proper r
  · exact hWx
  · exact hNoLoss

/-- **Fourth-organ prediction.** Once three jointly recoverable reporter
energies select the source core, every fourth continuous affine reporter has a
singleton formed core. This conclusion needs no energy or properness on the
fourth organ. -/
theorem tripleFusion_selection_propagates_to_fourthReporter
    (R₁ : E →L[ℝ] F₁) (R₂ : E →L[ℝ] F₂) (R₃ : E →L[ℝ] F₃)
    (Q : (F₁ × (F₂ × F₃)) →L[ℝ] E)
    (hQR : ∀ z, Q (tripleFusionReporter R₁ R₂ R₃ z) = z)
    (W₁ : F₁ → ℝ) (W₂ : F₂ → ℝ) (W₃ : F₃ → ℝ)
    (hW₁cont : Continuous W₁) (hW₂cont : Continuous W₂)
    (hW₃cont : Continuous W₃)
    (hW₁strict : StrictConvexOn ℝ Set.univ W₁)
    (hW₂strict : StrictConvexOn ℝ Set.univ W₂)
    (hW₃strict : StrictConvexOn ℝ Set.univ W₃)
    (hW₁nonneg : ∀ u, 0 ≤ W₁ u) (hW₂nonneg : ∀ u, 0 ≤ W₂ u)
    (hW₃nonneg : ∀ u, 0 ≤ W₃ u)
    (hW₁proper : ∀ r : ℝ, IsCompact {u : F₁ | W₁ u ≤ r})
    (hW₂proper : ∀ r : ℝ, IsCompact {u : F₂ | W₂ u ≤ r})
    (hW₃proper : ∀ r : ℝ, IsCompact {u : F₃ | W₃ u ≤ r})
    {x : ℕ → E} {c : ℝ}
    (hWx : Tendsto (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ ∘ x)
      atTop (𝓝 c))
    (hNoLoss :
      tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ '' asymptoticLawCore x ⊆
        asymptoticLawCore
          (tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃ ∘ x))
    (T : E →ᴬ[ℝ] F₄) :
    ∃ a, asymptoticLawCore x = {a} ∧
      asymptoticLawCore (T ∘ x) = {T a} := by
  obtain ⟨a, ha⟩ := tripleFusion_noLoss_selects_singleton_asymptoticLawCore
    R₁ R₂ R₃ Q hQR W₁ W₂ W₃ hW₁cont hW₂cont hW₃cont
    hW₁strict hW₂strict hW₃strict hW₁nonneg hW₂nonneg hW₃nonneg
    hW₁proper hW₂proper hW₃proper hWx hNoLoss
  let W := tripleFusionEnergy R₁ R₂ R₃ W₁ W₂ W₃
  obtain ⟨C, hC⟩ := hWx.bddAbove_range
  let K : Set E := {z : E | W z ≤ C}
  have hxK : ∀ n, x n ∈ K := by
    intro n
    exact hC ⟨n, rfl⟩
  have hK : IsCompact K := by
    exact isCompact_sublevel_tripleFusionEnergy_of_commonRecovery
      R₁ R₂ R₃ Q hQR W₁ W₂ W₃ hW₁cont hW₂cont hW₃cont
      hW₁nonneg hW₂nonneg hW₃nonneg hW₁proper hW₂proper hW₃proper C
  have hWstrict : StrictConvexOn ℝ Set.univ W :=
    strictConvexOn_tripleFusionEnergy_of_commonRecovery
      R₁ R₂ R₃ Q hQR W₁ W₂ W₃ hW₁strict hW₂strict hW₃strict
  have hKconv : Convex ℝ K := by
    simpa [K] using hWstrict.convexOn.convex_le C
  have hformed := continuousAffine_image_asymptoticLawCore hK hKconv hxK T
  refine ⟨a, ha, ?_⟩
  rw [ha] at hformed
  simpa using hformed.symm

end GaloisForLFunctions.HTGeometry
