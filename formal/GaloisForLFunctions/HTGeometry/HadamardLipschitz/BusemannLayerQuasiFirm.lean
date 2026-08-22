/-
# Busemann layers are quasi-α-firmly nonexpansive (Theorem 2.5 in the Busemann setting)

The one-parameter family `T_τ(x) = exp_x(-τ grad V(x))` of Busemann gradient-descent steps has
geodesic orbits in `τ`, so the averaging identity `x #_α T_τ(x) = T_{ατ}(x)` holds exactly.
Combining it with Theorem 2.4 gives quasi-α-firm nonexpansiveness for every `α ∈ [τ/τ̄, 1)`,
where `τ̄ = 2/(λ² M₂)` is the step-size ceiling of Theorem 4.1.

Feeding that into Theorem 2.2 yields `busemannStep_tendsto_iterate`: on a proper Hadamard
space the Picard iterates of a Busemann layer converge to one of its fixed points.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.BusemannLayer
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.QuasiFirm
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.FixedPointIteration

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

variable {X : Type*} [MetricSpace X] [NPCSpace X]

/-- The Busemann gradient-descent step of size `τ` for the potential `V = φ(λ b + β)`. -/
def busemannStep (F : BusemannFlow X) (dφ : ℝ → ℝ) (lam β τ : ℝ) (x : X) : X :=
  F.flow (τ * (lam * dφ (lam * F.fn x + β))) x

omit [NPCSpace X] in
theorem busemannStep_eq_layer (F : BusemannFlow X) (dφ : ℝ → ℝ) (lam β τ : ℝ) (x : X) :
    busemannStep F dφ lam β τ x = layer F (fun r => τ * lam * dφ (lam * r + β)) x := by
  simp [busemannStep, layer, mul_assoc]

/-- The orbits of the step family are the Busemann flow lines, so geodesic averaging simply
rescales the step size. -/
theorem gd_busemannStep (F : BusemannFlow X) (dφ : ℝ → ℝ) {lam β : ℝ} (hlam : 0 ≤ lam)
    (hnonneg : ∀ s, 0 ≤ dφ s) {α τ : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hτ : 0 ≤ τ) (x : X) :
    NPCSpace.gd x (busemannStep F dφ lam β τ x) α = busemannStep F dφ lam β (α * τ) x := by
  have hk : 0 ≤ τ * (lam * dφ (lam * F.fn x + β)) :=
    mul_nonneg hτ (mul_nonneg hlam (hnonneg _))
  rw [busemannStep, busemannStep, F.gd_flow hk hα₀ hα₁ x]
  congr 1
  ring

/-- **Theorem 2.5 for Busemann layers.**  With `τ̄ = 2/(λ² M₂)`, the step `T_τ` is
quasi-α-firmly nonexpansive at any of its fixed points, for every `α ∈ [τ/τ̄, 1)`. -/
theorem busemannStep_quasiFirmAt (F : BusemannFlow X) (dφ : ℝ → ℝ) {lam β M₂ : ℝ}
    (hlam : 0 < lam) (hM₂ : 0 < M₂) (hnonneg : ∀ s, 0 ≤ dφ s) (hmono : Monotone dφ)
    (hlip : ∀ u v : ℝ, |dφ u - dφ v| ≤ M₂ * |u - v|) (p : X) (hp : dφ (lam * F.fn p + β) = 0)
    {τ α : ℝ} (hτ0 : 0 < τ) (hα : τ / (2 / (lam ^ 2 * M₂)) ≤ α) (hα1 : α < 1) :
    QuasiFirmAt (busemannStep F dφ lam β τ) p ((1 - α) / α) := by
  have hτbar : 0 < 2 / (lam ^ 2 * M₂) := by positivity
  refine quasiFirmAt_of_geodesicFamily (busemannStep F dφ lam β)
    (fun α' τ' hα₀' hα₁' hτ' x => gd_busemannStep F dφ hlam.le hnonneg hα₀' hα₁' hτ' x)
    hτbar ?_ p ?_ hτ0 hα hα1
  · intro τ' hτ'0 hτ'bar x y
    rw [busemannStep_eq_layer, busemannStep_eq_layer]
    refine activation_layer_nonexpansive F dφ τ' lam β M₂ hτ'0 hlam.le hnonneg hmono hlip ?_ x y
    have h : τ' * (lam ^ 2 * M₂) ≤ 2 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2 * M₂)).mp hτ'bar
      linarith
    linarith [h]
  · intro τ' _
    rw [busemannStep, hp, mul_zero, mul_zero, F.flow_zero]

/-- **Theorem 2.2 for Busemann layers.**  On a proper Hadamard space the iterates of a
Busemann gradient-descent layer converge to a fixed point. -/
theorem busemannStep_tendsto_iterate [ProperSpace X] (F : BusemannFlow X) (dφ : ℝ → ℝ)
    {lam β M₂ : ℝ} (hlam : 0 < lam) (hM₂ : 0 < M₂) (hnonneg : ∀ s, 0 ≤ dφ s)
    (hmono : Monotone dφ) (hlip : ∀ u v : ℝ, |dφ u - dφ v| ≤ M₂ * |u - v|) (p : X)
    (hp : dφ (lam * F.fn p + β) = 0) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ * (lam ^ 2 * M₂) < 2)
    (x₀ : X) :
    ∃ q : X, busemannStep F dφ lam β τ q = q ∧
      Filter.Tendsto (fun n => (busemannStep F dφ lam β τ)^[n] x₀) Filter.atTop (nhds q) := by
  have hτbar : 0 < 2 / (lam ^ 2 * M₂) := by positivity
  have hlt : τ / (2 / (lam ^ 2 * M₂)) < 1 := by
    rw [div_lt_one hτbar, lt_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2 * M₂)]
    linarith
  set α : ℝ := (τ / (2 / (lam ^ 2 * M₂)) + 1) / 2 with hαdef
  have hαpos : 0 < α := by
    have : 0 < τ / (2 / (lam ^ 2 * M₂)) := by positivity
    rw [hαdef]; linarith
  have hαle : τ / (2 / (lam ^ 2 * M₂)) ≤ α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hqf := busemannStep_quasiFirmAt F dφ hlam hM₂ hnonneg hmono hlip p hp hτ0 hαle hα1
  have hne : ∀ x y : X, dist (busemannStep F dφ lam β τ x) (busemannStep F dφ lam β τ y)
      ≤ dist x y := by
    intro x y
    rw [busemannStep_eq_layer, busemannStep_eq_layer]
    refine activation_layer_nonexpansive F dφ τ lam β M₂ hτ0.le hlam.le hnonneg hmono hlip ?_ x y
    linarith
  have hfix : busemannStep F dφ lam β τ p = p := by
    rw [busemannStep, hp, mul_zero, mul_zero, F.flow_zero]
  exact tendsto_iterate_of_quasiFirmAt _ hne p hfix
    (quasiFirmCoeff α hαpos hα1) hqf x₀

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
