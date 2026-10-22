import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Tactic

/-!
# Bar-cochain skeleton for Deninger's arithmetic power transfers

The arithmetic power correspondences form a multiplicative monoid.  Once their framed transfers
act on a coefficient group, the source differential is the inhomogeneous bar coboundary.  This
module records its first three terms and proves the two nilpotence identities needed for the
good degree-two truncation.

No zeta zero, spectral coordinate, positivity statement, or RH hypothesis occurs here.
-/

namespace RHTower

section PowerBar

variable {M V : Type*}
variable [Monoid M] [AddCommGroup V] [DistribMulAction M V]

/-- Degree-zero to degree-one inhomogeneous bar coboundary. -/
def deningerPowerBarD0 (v : V) (n : M) : V :=
  n • v - v

/-- Degree-one to degree-two inhomogeneous bar coboundary. -/
def deningerPowerBarD1 (φ : M → V) (m n : M) : V :=
  m • φ n - φ (m * n) + φ m

/-- Degree-two to degree-three inhomogeneous bar coboundary. -/
def deningerPowerBarD2 (ψ : M → M → V) (l m n : M) : V :=
  l • ψ m n - ψ (l * m) n + ψ l (m * n) - ψ l m

/-- Transfer composition makes the first two bar coboundaries compose to zero. -/
theorem deningerPowerBarD1_comp_D0 (v : V) :
    deningerPowerBarD1 (M := M) (deningerPowerBarD0 (M := M) v) = 0 := by
  funext m n
  simp [deningerPowerBarD0, deningerPowerBarD1, smul_sub, mul_smul]

/-- Associativity makes the second and third bar coboundaries compose to zero. -/
theorem deningerPowerBarD2_comp_D1 (φ : M → V) :
    deningerPowerBarD2 (M := M) (deningerPowerBarD1 (M := M) φ) = 0 := by
  funext l m n
  simp [deningerPowerBarD1, deningerPowerBarD2, smul_sub, smul_add,
    mul_smul, mul_assoc]
  abel

/-- Genuine degree-two cocycles used by the good truncation. -/
def DeningerPowerBarCocycle2 :=
  {ψ : M → M → V // deningerPowerBarD2 (M := M) ψ = 0}

/-- The degree-one coboundary lands in genuine degree-two cocycles. -/
def deningerPowerBarD1Cocycle (φ : M → V) :
  DeningerPowerBarCocycle2 (M := M) (V := V) :=
  ⟨deningerPowerBarD1 (M := M) φ, deningerPowerBarD2_comp_D1 φ⟩

/-- The total valuation weight of a bar tuple, for an additive weight on the power monoid. -/
def DeningerPowerWeight (v : M → ℕ) : Prop := ∀ m n : M, v (m * n) = v m + v n

/-- **Inner faces preserve weight.**  Composing two adjacent entries leaves the total valuation
weight unchanged, by additivity of valuations. -/
theorem deningerPowerWeight_inner_face {v : M → ℕ} (hv : DeningerPowerWeight v) (l m n : M) :
    v (l * m) + v n = v l + v m + v n := by
  rw [hv l m]

theorem deningerPowerWeight_inner_face' {v : M → ℕ} (hv : DeningerPowerWeight v) (l m n : M) :
    v l + v (m * n) = v l + v m + v n := by
  rw [hv m n, add_assoc]

omit [Monoid M] in
/-- **Outer faces decrease weight.**  Dropping an entry removes a nonnegative summand. -/
theorem deningerPowerWeight_outer_face_left (v : M → ℕ) (l m n : M) :
    v m + v n ≤ v l + v m + v n := by
  omega

omit [Monoid M] in
theorem deningerPowerWeight_outer_face_right (v : M → ℕ) (l m n : M) :
    v l + v m ≤ v l + v m + v n := by
  omega

/-- **The weight cutoff is stable under every face.**  A bar triple of weight at most `N` has all
four faces of weight at most `N`, so the finite-weight restriction of the bar skeleton is a
subcomplex. -/
theorem deningerPowerWeight_faces_le {v : M → ℕ} (hv : DeningerPowerWeight v) (N : ℕ)
    (l m n : M) (h : v l + v m + v n ≤ N) :
    v (l * m) + v n ≤ N ∧ v l + v (m * n) ≤ N ∧ v m + v n ≤ N ∧ v l + v m ≤ N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [deningerPowerWeight_inner_face hv]; exact h
  · rw [deningerPowerWeight_inner_face' hv]; exact h
  · exact le_trans (deningerPowerWeight_outer_face_left v l m n) h
  · exact le_trans (deningerPowerWeight_outer_face_right v l m n) h

end PowerBar

end RHTower
