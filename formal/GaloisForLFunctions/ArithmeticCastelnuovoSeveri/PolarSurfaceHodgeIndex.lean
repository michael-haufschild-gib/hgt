import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.TFAE

/-!
# The Hodge index theorem of a polar surface

A **polar surface** is a real vector space of cycles with a symmetric intersection pairing and two
isotropic classes `H, V` with `H · V = 1`. On `C × C` these are the two fibre classes; on the
scaling surface of `ℤ` they are the pole directions `e^{u/2}, e^{−u/2}`, whose pairing with a test
is the value of its transform at `∓ i/2`.

Every cycle splits orthogonally into its **polar part** `(x · V) H + (x · H) V` and its
**primitive part** `x° = x − (x · V) H − (x · H) V`, and

    x · y = (x · H)(y · V) + (x · V)(y · H) + x° · y°.

The **Castelnuovo–Severi defect** `δ(x, y) = (x · H)(y · V) + (x · V)(y · H) − x · y` is therefore
`−x° · y°`: it only sees the primitive part. Four statements are equivalent
(`hodgeIndex_tfae`):

* **Hodge index**: the pairing is negative semidefinite on the primitive classes;
* **Castelnuovo–Severi**: `x² ≤ 2 (x · H)(x · V)` for every cycle;
* **positivity of the defect**: `δ(x, x) ≥ 0` for every cycle — this is Weil positivity once the
  cycles are tests and the pairing is the explicit formula;
* **ample form**: the pairing is negative semidefinite on the orthogonal complement of the ample
  class `H + V`, `(H + V)² = 2`.

Under Hodge index the defect is a positive semidefinite symmetric form, so it obeys
Cauchy–Schwarz, `δ(x, y)² ≤ δ(x, x) δ(y, y)` (`defect_sq_le_of_hodgeIndex`): this is the one
inequality Weil's proof uses. Hodge index is also the statement that the pairing has a single
positive square: no plane of cycles is positive definite (`hodgeIndex_iff_no_positive_plane`).
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A **polar surface**: cycles with a symmetric real intersection pairing and two isotropic
classes `H, V` with `H · V = 1` (the fibre classes, or the pole plane `e^{±u/2}`). -/
structure PolarSurface (E : Type*) [AddCommGroup E] [Module ℝ E] where
  /-- The intersection pairing. -/
  pair : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  pair_comm : ∀ x y, pair x y = pair y x
  /-- The first fibre class (pole direction). -/
  H : E
  /-- The second fibre class (pole direction). -/
  V : E
  pair_H_H : pair H H = 0
  pair_V_V : pair V V = 0
  pair_H_V : pair H V = 1

namespace PolarSurface

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

theorem pair_V_H : S.pair S.V S.H = 1 := by rw [S.pair_comm, S.pair_H_V]

/-- The polar (Lorentz) part of the pairing: `(x · H)(y · V) + (x · V)(y · H)`. -/
def polar (x y : E) : ℝ := S.pair x S.H * S.pair y S.V + S.pair x S.V * S.pair y S.H

/-- The **Castelnuovo–Severi defect** `δ(x, y) = (x · H)(y · V) + (x · V)(y · H) − x · y`. -/
def defect (x y : E) : ℝ := S.polar x y - S.pair x y

/-- The primitive part `x° = x − (x · V) H − (x · H) V`. -/
def prim (x : E) : E := x - S.pair x S.V • S.H - S.pair x S.H • S.V

theorem defect_comm (x y : E) : S.defect x y = S.defect y x := by
  simp only [defect, polar, S.pair_comm x y]; ring

theorem defect_self (x : E) : S.defect x x = 2 * S.pair x S.H * S.pair x S.V - S.pair x x := by
  simp only [defect, polar]; ring

theorem pair_prim_H (x : E) : S.pair (S.prim x) S.H = 0 := by
  simp only [prim, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    S.pair_H_H, S.pair_V_H]
  ring

theorem pair_prim_V (x : E) : S.pair (S.prim x) S.V = 0 := by
  simp only [prim, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    S.pair_H_V, S.pair_V_V]
  ring

theorem pair_prim_right (x y : E) :
    S.pair x (S.prim y) = S.pair x y - S.pair y S.V * S.pair x S.H - S.pair y S.H * S.pair x S.V :=
  by simp only [prim, map_sub, map_smul, smul_eq_mul]

/-- The primitive pairing is minus the defect. -/
theorem pair_prim_prim (x y : E) : S.pair (S.prim x) (S.prim y) = -S.defect x y := by
  simp only [prim, defect, polar, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H, S.pair_comm S.H y,
    S.pair_comm S.V y]
  ring

/-- **Orthogonal decomposition.** `x · y = (x · H)(y · V) + (x · V)(y · H) + x° · y°`. -/
theorem pair_eq_polar_add_prim (x y : E) :
    S.pair x y = S.polar x y + S.pair (S.prim x) (S.prim y) := by
  rw [pair_prim_prim, defect]; ring

/-- The defect only sees the primitive part. -/
theorem defect_prim (x y : E) : S.defect (S.prim x) (S.prim y) = S.defect x y := by
  simp only [defect, polar, pair_prim_H, pair_prim_V, pair_prim_prim, zero_mul, add_zero]
  ring

/-- **Hodge index**: the pairing is negative semidefinite on primitive classes. -/
def HodgeIndex : Prop := ∀ x, S.pair x S.H = 0 → S.pair x S.V = 0 → S.pair x x ≤ 0

/-- **Castelnuovo–Severi inequality**: `x² ≤ 2 (x · H)(x · V)` for every cycle. -/
def CastelnuovoSeveri : Prop := ∀ x, S.pair x x ≤ 2 * S.pair x S.H * S.pair x S.V

/-- The ample class `H + V`, with `(H + V)² = 2`. -/
def ample : E := S.H + S.V

theorem pair_ample_ample : S.pair S.ample S.ample = 2 := by
  simp only [ample, map_add, LinearMap.add_apply, S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H]
  norm_num

theorem pair_ample (x : E) : S.pair x S.ample = S.pair x S.H + S.pair x S.V := by
  simp only [ample, map_add]

/-- **Hodge index for the ample class**: negative semidefinite on `(H + V)^⊥`. -/
def AmpleHodgeIndex : Prop := ∀ x, S.pair x S.ample = 0 → S.pair x x ≤ 0

theorem castelnuovoSeveri_iff_defect_nonneg :
    S.CastelnuovoSeveri ↔ ∀ x, 0 ≤ S.defect x x := by
  refine forall_congr' fun x => ?_
  rw [defect_self]
  constructor <;> intro h <;> linarith

theorem hodgeIndex_iff_castelnuovoSeveri : S.HodgeIndex ↔ S.CastelnuovoSeveri := by
  rw [castelnuovoSeveri_iff_defect_nonneg]
  constructor
  · intro h x
    have := h (S.prim x) (S.pair_prim_H x) (S.pair_prim_V x)
    rw [pair_prim_prim] at this
    linarith
  · intro h x hH hV
    have := h x
    rw [defect_self, hH, hV] at this
    linarith

theorem ampleHodgeIndex_iff_castelnuovoSeveri : S.AmpleHodgeIndex ↔ S.CastelnuovoSeveri := by
  constructor
  · intro h
    rw [← hodgeIndex_iff_castelnuovoSeveri]
    intro x hH hV
    exact h x (by rw [pair_ample, hH, hV, add_zero])
  · intro h x hx
    rw [pair_ample] at hx
    have hV : S.pair x S.V = -S.pair x S.H := by linarith
    have := h x
    rw [hV] at this
    nlinarith [sq_nonneg (S.pair x S.H)]

/-- The four forms of the Hodge index theorem. -/
theorem hodgeIndex_tfae :
    List.TFAE [S.HodgeIndex, S.CastelnuovoSeveri, ∀ x, 0 ≤ S.defect x x, S.AmpleHodgeIndex] := by
  tfae_have 1 ↔ 2 := S.hodgeIndex_iff_castelnuovoSeveri
  tfae_have 2 ↔ 3 := S.castelnuovoSeveri_iff_defect_nonneg
  tfae_have 4 ↔ 2 := S.ampleHodgeIndex_iff_castelnuovoSeveri
  tfae_finish

theorem defect_add_left (x y z : E) : S.defect (x + y) z = S.defect x z + S.defect y z := by
  simp only [defect, polar, map_add, LinearMap.add_apply]; ring

theorem defect_smul_left (c : ℝ) (x y : E) : S.defect (c • x) y = c * S.defect x y := by
  simp only [defect, polar, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/-- **Cauchy–Schwarz for the defect.** Under Hodge index, `δ(x, y)² ≤ δ(x, x) δ(y, y)`. This is
the single inequality of Weil's proof: applied to `x = Γ`, `y = Δ` it is the Hasse–Weil bound. -/
theorem defect_sq_le_of_hodgeIndex (h : S.HodgeIndex) (x y : E) :
    S.defect x y ^ 2 ≤ S.defect x x * S.defect y y := by
  have hpos := (S.castelnuovoSeveri_iff_defect_nonneg.mp (S.hodgeIndex_iff_castelnuovoSeveri.mp h))
  have hq : ∀ t : ℝ, 0 ≤ S.defect y y * (t * t) + 2 * S.defect x y * t + S.defect x x := by
    intro t
    have h1 := hpos (x + t • y)
    have h2 : S.defect (x + t • y) (x + t • y)
        = S.defect y y * (t * t) + 2 * S.defect x y * t + S.defect x x := by
      simp only [defect, polar, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, S.pair_comm y x]
      ring
    rwa [h2] at h1
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **One positive square.** Hodge index holds iff no plane of cycles is positive definite: for
every two cycles the Gram matrix `[[x², x·y], [x·y, y²]]` fails `x² > 0`, `(x·y)² < x² y²`. -/
theorem hodgeIndex_iff_no_positive_plane :
    S.HodgeIndex ↔ ∀ x y, ¬ (0 < S.pair x x ∧ S.pair x y ^ 2 < S.pair x x * S.pair y y) := by
  constructor
  · intro h x y ⟨hx, hxy⟩
    have hamp := (S.ampleHodgeIndex_iff_castelnuovoSeveri.mpr
      (S.hodgeIndex_iff_castelnuovoSeveri.mp h))
    set cx := S.pair x S.ample
    set cy := S.pair y S.ample
    by_cases hc : cx = 0 ∧ cy = 0
    · have := hamp x hc.1
      linarith
    · -- the combination `cy x − cx y` is orthogonal to the ample class
      have hz := hamp (cy • x - cx • y) (by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        ring)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_comm y x] at hz
      have hne : cx ≠ 0 ∨ cy ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hc hcon
      -- the Gram form is positive definite, contradicting `hz`
      have hy : 0 < S.pair y y := by
        by_contra hy
        push Not at hy
        nlinarith [sq_nonneg (S.pair x y)]
      have hquad : 0 < S.pair x x * (cy * cy) - 2 * S.pair x y * (cx * cy)
          + S.pair y y * (cx * cx) := by
        rcases hne with h1 | h1
        · have hcx : 0 < cx ^ 2 := by positivity
          nlinarith [sq_nonneg (S.pair x x * cy - S.pair x y * cx), sq_nonneg cy]
        · have hcy : 0 < cy ^ 2 := by positivity
          nlinarith [sq_nonneg (S.pair y y * cx - S.pair x y * cy), sq_nonneg cx]
      nlinarith [hz, hquad]
  · intro h x hH hV
    by_contra hx
    push Not at hx
    apply h x S.ample
    refine ⟨hx, ?_⟩
    rw [pair_ample, hH, hV, pair_ample_ample]
    nlinarith

end PolarSurface

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
