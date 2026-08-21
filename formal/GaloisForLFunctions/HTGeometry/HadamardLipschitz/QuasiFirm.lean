/-
# Quasi-α-firmly nonexpansive maps on NPC spaces

Definition 2.1 of the source: `T` is *quasi-α-firmly nonexpansive* when, for every fixed
point `p`,
```
d(Tx, p)^2 ≤ d(x,p)^2 - ((1-α)/α) d(Tx, x)^2 .
```
It is convenient to carry the coefficient `ξ = (1-α)/α` directly; `quasiFirmCoeff` translates.

Results proved here:

* `quasiFirmAt_gd` — **Theorem 2.4**: the geodesic average `T_α(x) = x #_α N(x)` of a
  nonexpansive `N` is quasi-α-firmly nonexpansive, with `Fix T_α = Fix N`
  (`gd_fixedPoint_iff`);
* `quasiFirmAt_comp` — **Proposition 2.3**: quasi-firmness is stable under composition, with
  `1/ξ = 1/ξ₁ + 1/ξ₂` (equivalently `α = (ξ₁+ξ₂)/(ξ₁ξ₂+ξ₁+ξ₂)`, `alpha_comp_eq`);
* `quasiFirmAt_of_geodesicFamily` — **Theorem 2.5**: a nonexpansive family of gradient steps
  along geodesics is quasi-α-firmly nonexpansive for every `α ∈ [τ/τ̄, 1)`.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.NPCSpace

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

variable {X : Type*} [MetricSpace X]

/-- Quasi-firmness of `T` at the point `p`, with coefficient `ξ`. Definition 2.1 is the case
`ξ = (1-α)/α`, required at every fixed point of `T`. -/
def QuasiFirmAt (T : X → X) (p : X) (ξ : ℝ) : Prop :=
  ∀ x : X, dist (T x) p ^ 2 ≤ dist x p ^ 2 - ξ * dist (T x) x ^ 2

/-- Definition 2.1: `T` is quasi-α-firmly nonexpansive. -/
structure QuasiFirmlyNonexpansive (T : X → X) (α : ℝ) : Prop where
  /-- The averaging parameter is a proportion. -/
  alpha_pos : 0 < α
  /-- The averaging parameter is a proportion. -/
  alpha_lt_one : α < 1
  /-- `T` has a fixed point. -/
  exists_fixed : ∃ p, T p = p
  /-- The defining inequality, at every fixed point. -/
  firm : ∀ p, T p = p → QuasiFirmAt T p ((1 - α) / α)

/-- The dictionary between the averaging parameter `α ∈ (0,1)` and the coefficient
`ξ = (1-α)/α ∈ (0, ∞)`. -/
theorem quasiFirmCoeff (α : ℝ) (h0 : 0 < α) (h1 : α < 1) : 0 < (1 - α) / α :=
  div_pos (by linarith) h0

/-- Inverse dictionary: `α = 1/(1+ξ)`. -/
theorem alpha_of_coeff (ξ : ℝ) (hξ : 0 < ξ) : (1 - 1 / (1 + ξ)) / (1 / (1 + ξ)) = ξ := by
  have h : (1 : ℝ) + ξ ≠ 0 := by linarith
  field_simp
  ring

variable [NPCSpace X]

/-- **Theorem 2.4.**  If `N` is nonexpansive and fixes `p`, the geodesic average
`T_α(x) = x #_α N(x)` satisfies the quasi-α-firm inequality at `p`. -/
theorem quasiFirmAt_gd (N : X → X) (hN : ∀ x y, dist (N x) (N y) ≤ dist x y) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : X) (hp : N p = p) :
    QuasiFirmAt (fun x => NPCSpace.gd x (N x) α) p ((1 - α) / α) := by
  intro x
  have hnpc := NPCSpace.dist_gd_sq_le x (N x) p α hα0.le hα1.le
  have hNp : dist (N x) p ≤ dist x p := by
    have := hN x p; rwa [hp] at this
  have hleft : dist x (NPCSpace.gd x (N x) α) = α * dist x (N x) :=
    NPCSpace.dist_gd_left x (N x) α hα0.le hα1.le
  have hsym : dist (NPCSpace.gd x (N x) α) x = α * dist x (N x) := by
    rw [dist_comm]; exact hleft
  have hxN : dist x (N x) = dist (NPCSpace.gd x (N x) α) x / α := by
    rw [hsym]; field_simp
  simp only
  rw [hxN] at hnpc
  have hnn : 0 ≤ dist (N x) p := dist_nonneg
  have hnn2 : 0 ≤ dist x p := dist_nonneg
  have hsq : dist (N x) p ^ 2 ≤ dist x p ^ 2 := by nlinarith
  have hcoef : α * (1 - α) * (dist (NPCSpace.gd x (N x) α) x / α) ^ 2
      = (1 - α) / α * dist (NPCSpace.gd x (N x) α) x ^ 2 := by
    field_simp
  rw [hcoef] at hnpc
  nlinarith [hnpc, hsq]

/-- The fixed points of the geodesic average are those of `N` (Theorem 2.4, second half). -/
theorem gd_fixedPoint_iff (N : X → X) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (x : X) :
    NPCSpace.gd x (N x) α = x ↔ N x = x := by
  constructor
  · intro h
    have hleft : dist x (NPCSpace.gd x (N x) α) = α * dist x (N x) :=
      NPCSpace.dist_gd_left x (N x) α hα0.le hα1.le
    rw [h, dist_self] at hleft
    have : dist x (N x) = 0 := by
      rcases mul_eq_zero.mp hleft.symm with h' | h'
      · exact absurd h' (ne_of_gt hα0)
      · exact h'
    exact (dist_eq_zero.mp this).symm
  · intro h
    rw [h]
    have hleft : dist x (NPCSpace.gd x x α) = α * dist x x :=
      NPCSpace.dist_gd_left x x α hα0.le hα1.le
    rw [dist_self, mul_zero] at hleft
    exact (dist_eq_zero.mp hleft).symm

omit [NPCSpace X] in
/-- **Proposition 2.3.**  Quasi-firmness at a common fixed point is stable under composition,
with harmonic addition of the coefficients. -/
theorem quasiFirmAt_comp {T₁ T₂ : X → X} {p : X} {ξ₁ ξ₂ : ℝ} (h₁ : 0 < ξ₁) (h₂ : 0 < ξ₂)
    (hT₁ : QuasiFirmAt T₁ p ξ₁) (hT₂ : QuasiFirmAt T₂ p ξ₂) :
    QuasiFirmAt (T₂ ∘ T₁) p (ξ₁ * ξ₂ / (ξ₁ + ξ₂)) := by
  intro x
  have e₁ := hT₁ x
  have e₂ := hT₂ (T₁ x)
  set A := dist (T₁ x) x with hA
  set B := dist (T₂ (T₁ x)) (T₁ x) with hB
  have hAnn : 0 ≤ A := dist_nonneg
  have hBnn : 0 ≤ B := dist_nonneg
  have htri : dist (T₂ (T₁ x)) x ≤ B + A := dist_triangle _ _ _
  have hCnn : 0 ≤ dist (T₂ (T₁ x)) x := dist_nonneg
  have hCsq : dist (T₂ (T₁ x)) x ^ 2 ≤ (B + A) ^ 2 := by nlinarith
  have hcs : ξ₁ * ξ₂ / (ξ₁ + ξ₂) * (B + A) ^ 2 ≤ ξ₁ * A ^ 2 + ξ₂ * B ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (ξ₁ * A - ξ₂ * B)]
  have hpos : 0 < ξ₁ * ξ₂ / (ξ₁ + ξ₂) := by positivity
  simp only [Function.comp_apply]
  nlinarith [e₁, e₂, hCsq, hcs, hpos]

/-- The composed averaging parameter of Proposition 2.3. -/
theorem alpha_comp_eq (ξ₁ ξ₂ : ℝ) (h₁ : 0 < ξ₁) (h₂ : 0 < ξ₂) :
    1 / (1 + ξ₁ * ξ₂ / (ξ₁ + ξ₂)) = (ξ₁ + ξ₂) / (ξ₁ * ξ₂ + ξ₁ + ξ₂) := by
  have hs : ξ₁ + ξ₂ ≠ 0 := by positivity
  have hd : ξ₁ * ξ₂ + ξ₁ + ξ₂ ≠ 0 := by positivity
  field_simp
  ring

/-- **Theorem 2.5.**  Let `T τ` be a family of gradient steps whose orbits `τ ↦ T τ x` are
geodesics issuing from `x`, nonexpansive for `τ ∈ [0, τ̄]` and fixing `p`.  Then `T τ` is
quasi-α-firmly nonexpansive for every `α ∈ [τ/τ̄, 1)`. -/
theorem quasiFirmAt_of_geodesicFamily (T : ℝ → X → X)
    (hgd : ∀ α τ : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ τ → ∀ x, NPCSpace.gd x (T τ x) α = T (α * τ) x)
    {τbar : ℝ} (hτbar : 0 < τbar)
    (hne : ∀ τ : ℝ, 0 ≤ τ → τ ≤ τbar → ∀ x y, dist (T τ x) (T τ y) ≤ dist x y)
    (p : X) (hp : ∀ τ : ℝ, 0 ≤ τ → T τ p = p)
    {τ α : ℝ} (hτ0 : 0 < τ) (hα : τ / τbar ≤ α) (hα1 : α < 1) :
    QuasiFirmAt (T τ) p ((1 - α) / α) := by
  have hα0 : 0 < α := lt_of_lt_of_le (div_pos hτ0 hτbar) hα
  have hτ' : 0 < τ / α := div_pos hτ0 hα0
  have hτ'le : τ / α ≤ τbar := by
    rw [div_le_iff₀ hα0]
    have := (div_le_iff₀ hτbar).mp hα
    nlinarith
  have hkey := quasiFirmAt_gd (T (τ / α)) (hne (τ / α) hτ'.le hτ'le) hα0 hα1 p (hp _ hτ'.le)
  have hrw : (fun x => NPCSpace.gd x (T (τ / α) x) α) = T τ := by
    funext x
    rw [hgd α (τ / α) hα0.le hα1.le hτ'.le x]
    congr 1
    field_simp
  rwa [hrw] at hkey

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
