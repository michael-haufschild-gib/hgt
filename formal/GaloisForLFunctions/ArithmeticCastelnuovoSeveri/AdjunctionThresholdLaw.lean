import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurfaceHodgeIndex
import Mathlib.Analysis.Real.Sqrt

/-!
# The adjunction threshold law

Weil's proof of the Riemann hypothesis for a curve `C/𝔽_q` uses four classes of `C × C`: the
fibres `H, V`, the diagonal `Δ` and the Frobenius graph `Γ`, with

    Γ·H = 1,  Γ·V = q,  Δ·H = Δ·V = 1,  Δ² = 2 − 2g,  Γ·Δ = N,  Γ² = s,

where `N = #C(𝔽_q)` (Lefschetz) and `s = q(2 − 2g)` (adjunction). This file decides exactly which
values of `(q, g, N, s)` occur on a polar surface with the Hodge index property
(`realizable_iff`):

    realizable  ⟺  0 ≤ 2q − s,  0 ≤ g,  (q + 1 − N)² ≤ (2q − s)·2g.

The three numbers are the defect Gram matrix of `(Γ, Δ)`: `δ(Γ) = 2q − s`, `δ(Δ) = 2g`,
`δ(Γ, Δ) = q + 1 − N`. Consequences:

* **Hasse–Weil** (`realizable_adjunction_iff`): with the adjunction value `s = q(2 − 2g)` the data
  are realizable iff `g ≥ 0` and `|q + 1 − N| ≤ 2g√q`.
* **Adjunction carries the whole bound** (`realizable_of_free_selfIntersection`): for `g > 0` and
  *every* `N` some self-intersection `s` is compatible with Hodge index. Pairing, fibres, diagonal
  and Lefschetz number give no bound on `N` without the value of `Γ²`.
* **Only the lower bound is used** (`sq_le_of_hodgeIndex_of_selfIntersection_ge`): an adjunction
  inequality `Γ² ≥ q(2 − 2g) − ε` gives `(q + 1 − N)² ≤ 2g(2gq + ε)`. Weil's proof needs an upper
  bound on the self-defect `δ(Γ)`, never its exact value.
* **Genus zero is rigid** (`realizable_genusZero_iff`): `g = 0` forces `N = q + 1` — the
  `𝔽_q[T]` calibration, where the defect form vanishes on `⟨Γ, Δ⟩` and the continuation budget is
  zero.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open PolarSurface

/-- The Weil configuration `(q, g, N, s)` is **realizable**: some polar surface with the Hodge
index property carries classes `Γ, Δ` with these intersection numbers. -/
def WeilRealizable (q g N s : ℝ) : Prop :=
  ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (S : PolarSurface E) (Γ Δ : E),
    S.HodgeIndex ∧ S.pair Γ S.H = 1 ∧ S.pair Γ S.V = q ∧ S.pair Δ S.H = 1 ∧ S.pair Δ S.V = 1 ∧
      S.pair Δ Δ = 2 - 2 * g ∧ S.pair Γ Γ = s ∧ S.pair Γ Δ = N

/-- A `2 × 2` positive semidefinite quadratic form is nonnegative. -/
theorem quad_nonneg_of_psd {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb0 : b = 0 := by rw [← ha0, zero_mul] at hb; nlinarith [sq_nonneg b]
    rw [← ha0, hb0]; nlinarith [sq_nonneg y]
  · have hkey : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y]
    nlinarith [hkey, ha0]

/-- The model surface `ℝ⁴ = ⟨H, V⟩ ⊕ ⟨X, Y⟩`: hyperbolic on the pole plane, minus the defect
Gram `[[a, b], [b, c]]` on the primitive plane. -/
def modelPair (a b c : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => x 0 * y 1 + x 1 * y 0 - (a * x 2 * y 2 + b * (x 2 * y 3 + x 3 * y 2) + c * x 3 * y 3))
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun r x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun r x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- The model polar surface with defect Gram `[[a, b], [b, c]]`. -/
def modelSurface (a b c : ℝ) : PolarSurface (Fin 4 → ℝ) where
  pair := modelPair a b c
  pair_comm x y := by simp only [modelPair, LinearMap.mk₂_apply]; ring
  H := ![1, 0, 0, 0]
  V := ![0, 1, 0, 0]
  pair_H_H := by simp [modelPair]
  pair_V_V := by simp [modelPair]
  pair_H_V := by simp [modelPair]

theorem modelSurface_pair (a b c : ℝ) (x y : Fin 4 → ℝ) :
    (modelSurface a b c).pair x y
      = x 0 * y 1 + x 1 * y 0 - (a * x 2 * y 2 + b * (x 2 * y 3 + x 3 * y 2) + c * x 3 * y 3) :=
  rfl

theorem modelSurface_H (a b c : ℝ) : (modelSurface a b c).H = ![1, 0, 0, 0] := rfl

theorem modelSurface_V (a b c : ℝ) : (modelSurface a b c).V = ![0, 1, 0, 0] := rfl

theorem modelSurface_hodgeIndex {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) :
    (modelSurface a b c).HodgeIndex := by
  intro x hH hV
  rw [modelSurface_H, modelSurface_pair] at hH
  rw [modelSurface_V, modelSurface_pair] at hV
  simp at hH hV
  rw [modelSurface_pair, hH, hV]
  have := quad_nonneg_of_psd ha hc hb (x 2) (x 3)
  nlinarith [this]

/-- **The adjunction threshold law.** A Weil configuration is realizable on a polar surface with
the Hodge index property iff its defect Gram matrix is positive semidefinite. -/
theorem realizable_iff (q g N s : ℝ) :
    WeilRealizable q g N s ↔ 0 ≤ 2 * q - s ∧ 0 ≤ g ∧ (q + 1 - N) ^ 2 ≤ (2 * q - s) * (2 * g) := by
  constructor
  · rintro ⟨E, _, _, S, Γ, Δ, hS, hΓH, hΓV, hΔH, hΔV, hΔΔ, hΓΓ, hΓΔ⟩
    have hdef := (S.castelnuovoSeveri_iff_defect_nonneg.mp (S.hodgeIndex_iff_castelnuovoSeveri.mp hS))
    have hΓ : S.defect Γ Γ = 2 * q - s := by rw [defect_self, hΓH, hΓV, hΓΓ]; ring
    have hΔ : S.defect Δ Δ = 2 * g := by rw [defect_self, hΔH, hΔV, hΔΔ]; ring
    have hΓΔ' : S.defect Γ Δ = q + 1 - N := by
      simp only [defect, polar, hΓH, hΓV, hΔH, hΔV, hΓΔ]; ring
    have hcs := S.defect_sq_le_of_hodgeIndex hS Γ Δ
    rw [hΓ, hΔ, hΓΔ'] at hcs
    refine ⟨hΓ ▸ hdef Γ, ?_, hcs⟩
    have := hdef Δ
    rw [hΔ] at this
    linarith
  · rintro ⟨ha, hg, hb⟩
    refine ⟨Fin 4 → ℝ, inferInstance, inferInstance,
      modelSurface (2 * q - s) (q + 1 - N) (2 * g), ![q, 1, 1, 0], ![1, 1, 0, 1],
      modelSurface_hodgeIndex ha (by linarith) (by nlinarith [hb]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [modelSurface_H, modelSurface_V, modelSurface_pair] <;> simp <;> ring

/-- **Hasse–Weil from Hodge index and adjunction.** With the adjunction value `Γ² = q(2 − 2g)`,
`q > 0`, the configuration is realizable iff `g ≥ 0` and `(q + 1 − N)² ≤ 4 g² q`. -/
theorem realizable_adjunction_iff {q : ℝ} (hq : 0 < q) (g N : ℝ) :
    WeilRealizable q g N (q * (2 - 2 * g)) ↔ 0 ≤ g ∧ (q + 1 - N) ^ 2 ≤ 4 * g ^ 2 * q := by
  rw [realizable_iff]
  have h1 : 2 * q - q * (2 - 2 * g) = 2 * g * q := by ring
  rw [h1]
  constructor
  · rintro ⟨_, hg, hb⟩
    exact ⟨hg, by nlinarith [hb]⟩
  · rintro ⟨hg, hb⟩
    exact ⟨by positivity, hg, by nlinarith [hb]⟩

/-- **Weil's bound in abstract form**: on any polar surface with the Hodge index property, classes
with the Weil intersection numbers satisfy `|q + 1 − N| ≤ 2g√q`. -/
theorem abs_le_of_hodgeIndex {E : Type} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)
    (hS : S.HodgeIndex) {Γ Δ : E} {q g N : ℝ} (hq : 0 < q)
    (hΓH : S.pair Γ S.H = 1) (hΓV : S.pair Γ S.V = q) (hΔH : S.pair Δ S.H = 1)
    (hΔV : S.pair Δ S.V = 1) (hΔΔ : S.pair Δ Δ = 2 - 2 * g) (hΓΓ : S.pair Γ Γ = q * (2 - 2 * g))
    (hΓΔ : S.pair Γ Δ = N) : |q + 1 - N| ≤ 2 * g * Real.sqrt q := by
  have hr : WeilRealizable q g N (q * (2 - 2 * g)) :=
    ⟨E, inferInstance, inferInstance, S, Γ, Δ, hS, hΓH, hΓV, hΔH, hΔV, hΔΔ, hΓΓ, hΓΔ⟩
  obtain ⟨hg, hb⟩ := (realizable_adjunction_iff hq g N).mp hr
  have hsq : (2 * g * Real.sqrt q) ^ 2 = 4 * g ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq.le]; ring
  have hnn : 0 ≤ 2 * g * Real.sqrt q := by positivity
  rw [← hsq] at hb
  exact abs_le_of_sq_le_sq hb hnn

/-- **The adjunction carries the whole bound.** For `g > 0` and every value `N` of the Lefschetz
number there is a self-intersection `s` making the configuration realizable: without `Γ²` the
Hodge index theorem bounds nothing. -/
theorem realizable_of_free_selfIntersection {g : ℝ} (hg : 0 < g) (q N : ℝ) :
    WeilRealizable q g N (2 * q - (q + 1 - N) ^ 2 / (2 * g)) := by
  rw [realizable_iff]
  have h : 2 * q - (2 * q - (q + 1 - N) ^ 2 / (2 * g)) = (q + 1 - N) ^ 2 / (2 * g) := by ring
  rw [h, div_mul_cancel₀ _ (by positivity : (2 * g) ≠ 0)]
  exact ⟨by positivity, hg.le, le_rfl⟩

/-- **Only the lower adjunction bound is used.** If `Γ² ≥ q(2 − 2g) − ε` on a realizable
configuration then `(q + 1 − N)² ≤ 2g(2gq + ε)`. -/
theorem sq_le_of_realizable_of_selfIntersection_ge {q g N s ε : ℝ} (hr : WeilRealizable q g N s)
    (hs : q * (2 - 2 * g) - ε ≤ s) : (q + 1 - N) ^ 2 ≤ 2 * g * (2 * g * q + ε) := by
  obtain ⟨_, hg, hb⟩ := (realizable_iff q g N s).mp hr
  have : (2 * q - s) * (2 * g) ≤ (2 * g * q + ε) * (2 * g) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith [hb, this]

/-- **Genus zero is rigid.** A realizable configuration of genus `0` has `N = q + 1`. -/
theorem realizable_genusZero_iff (q N s : ℝ) :
    WeilRealizable q 0 N s ↔ s ≤ 2 * q ∧ N = q + 1 := by
  rw [realizable_iff]
  constructor
  · rintro ⟨ha, -, hb⟩
    refine ⟨by linarith, ?_⟩
    have : (q + 1 - N) ^ 2 = 0 := le_antisymm (by simpa using hb) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rintro ⟨hs, hN⟩
    refine ⟨by linarith, le_rfl, ?_⟩
    rw [hN]; simp

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
