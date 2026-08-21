import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Rayleigh quotients split along a symmetric involution

Let `J` be a linear involution of an inner product space which is symmetric for the inner product
(equivalently, a self-adjoint unitary: a parity operator).  It splits every vector orthogonally into
its even and odd parts, and if a quadratic functional `Q` splits additively along that
decomposition, then the greatest lower bound of the Rayleigh quotient `Q(v)/‖v‖²` over all nonzero
vectors is the minimum of the two parity-restricted greatest lower bounds:

`λ = min(λ⁺, λ⁻)`.

The lower bound is the two-term estimate `Q(v) = Q(v⁺) + Q(v⁻) ≥ λ⁺‖v⁺‖² + λ⁻‖v⁻‖² ≥ λ‖v‖²`; the
converse is immediate because the parity vectors are themselves competitors.

This is the abstract content of the parity decomposition of a localized Weil form, where `J` is
`u ↦ u(-·)`, `Q` is the localized quadratic form, and the additive splitting of `Q` is the
vanishing of the even–odd cross term.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The even part of `v` for the involution `J`. -/
def parityEven (J : V →ₗ[ℂ] V) (v : V) : V := (2 : ℂ)⁻¹ • (v + J v)

/-- The odd part of `v` for the involution `J`. -/
def parityOdd (J : V →ₗ[ℂ] V) (v : V) : V := (2 : ℂ)⁻¹ • (v - J v)

theorem parityEven_add_parityOdd (J : V →ₗ[ℂ] V) (v : V) :
    parityEven J v + parityOdd J v = v := by
  rw [parityEven, parityOdd, ← smul_add]
  rw [show v + J v + (v - J v) = (2 : ℂ) • v from by
    rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

theorem parityEven_mem (J : V →ₗ[ℂ] V) (hJJ : ∀ v, J (J v) = v) (v : V) :
    J (parityEven J v) = parityEven J v := by
  rw [parityEven, map_smul, map_add, hJJ]
  rw [show J v + v = v + J v from by abel]

theorem parityOdd_mem (J : V →ₗ[ℂ] V) (hJJ : ∀ v, J (J v) = v) (v : V) :
    J (parityOdd J v) = -parityOdd J v := by
  rw [parityOdd, map_smul, map_sub, hJJ, ← smul_neg]
  congr 1
  abel

theorem inner_parityEven_parityOdd (J : V →ₗ[ℂ] V) (hJJ : ∀ v, J (J v) = v)
    (hJsym : ∀ x y : V, ⟪J x, y⟫_ℂ = ⟪x, J y⟫_ℂ) (v : V) :
    ⟪parityEven J v, parityOdd J v⟫_ℂ = 0 := by
  have hJJinner : ⟪J v, J v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [hJsym, hJJ]
  have hcross : ⟪J v, v⟫_ℂ = ⟪v, J v⟫_ℂ := hJsym v v
  rw [parityEven, parityOdd, inner_smul_left, inner_smul_right, inner_sub_right,
    inner_add_left, inner_add_left, hJJinner, hcross]
  ring

theorem norm_sq_parity_split (J : V →ₗ[ℂ] V) (hJJ : ∀ v, J (J v) = v)
    (hJsym : ∀ x y : V, ⟪J x, y⟫_ℂ = ⟪x, J y⟫_ℂ) (v : V) :
    ‖v‖ ^ 2 = ‖parityEven J v‖ ^ 2 + ‖parityOdd J v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := ℂ) (parityEven J v) (parityOdd J v) (inner_parityEven_parityOdd J hJJ hJsym v)
  rw [parityEven_add_parityOdd] at h
  simpa [sq] using h

/-- The Rayleigh quotient values of `Q` over the nonzero vectors of a set. -/
def rayleighSetOn (Q : V → ℝ) (S : Set V) : Set ℝ :=
  {r | ∃ v ∈ S, v ≠ 0 ∧ r = Q v / ‖v‖ ^ 2}

theorem parity_form_zero {Q : V → ℝ} {J : V →ₗ[ℂ] V}
    (hsplit : ∀ v, Q v = Q (parityEven J v) + Q (parityOdd J v)) :
    Q 0 = 0 := by
  have h := hsplit 0
  rw [parityEven, parityOdd] at h
  simp at h
  linarith

/-- **Parity lower bound.**  If `Q` splits additively along the parity decomposition and is bounded
below by `lp` (resp. `lm`) on the even (resp. odd) subspace, then it is bounded below by
`min lp lm` everywhere. -/
theorem parity_rayleigh_lower_bound {Q : V → ℝ} {J : V →ₗ[ℂ] V} {lp lm : ℝ}
    (hJJ : ∀ v, J (J v) = v) (hJsym : ∀ x y : V, ⟪J x, y⟫_ℂ = ⟪x, J y⟫_ℂ)
    (hsplit : ∀ v, Q v = Q (parityEven J v) + Q (parityOdd J v))
    (hlp : ∀ w : V, J w = w → lp * ‖w‖ ^ 2 ≤ Q w)
    (hlm : ∀ w : V, J w = -w → lm * ‖w‖ ^ 2 ≤ Q w)
    (v : V) :
    min lp lm * ‖v‖ ^ 2 ≤ Q v := by
  have hp := hlp (parityEven J v) (parityEven_mem J hJJ v)
  have hm := hlm (parityOdd J v) (parityOdd_mem J hJJ v)
  have hminp : min lp lm * ‖parityEven J v‖ ^ 2 ≤ lp * ‖parityEven J v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
  have hminm : min lp lm * ‖parityOdd J v‖ ^ 2 ≤ lm * ‖parityOdd J v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
  rw [hsplit v, norm_sq_parity_split J hJJ hJsym v, mul_add]
  linarith

/-- **Suzuki's parity identity for the ground energy.**  The greatest lower bound of the Rayleigh
quotient over all nonzero vectors is the minimum of the two parity-restricted greatest lower
bounds. -/
theorem isGLB_rayleigh_min_parity {Q : V → ℝ} {J : V →ₗ[ℂ] V} {lp lm : ℝ}
    (hJJ : ∀ v, J (J v) = v) (hJsym : ∀ x y : V, ⟪J x, y⟫_ℂ = ⟪x, J y⟫_ℂ)
    (hsplit : ∀ v, Q v = Q (parityEven J v) + Q (parityOdd J v))
    (hp : IsGLB (rayleighSetOn Q {w : V | J w = w}) lp)
    (hm : IsGLB (rayleighSetOn Q {w : V | J w = -w}) lm) :
    IsGLB (rayleighSetOn Q Set.univ) (min lp lm) := by
  have hQzero : Q 0 = 0 := parity_form_zero hsplit
  have hlp : ∀ w : V, J w = w → lp * ‖w‖ ^ 2 ≤ Q w := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hQzero]
    · have hmem : Q w / ‖w‖ ^ 2 ∈ rayleighSetOn Q {w : V | J w = w} := ⟨w, hw, hw0, rfl⟩
      have hle := hp.1 hmem
      have hpos : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
      rw [le_div_iff₀ hpos] at hle
      linarith
  have hlm : ∀ w : V, J w = -w → lm * ‖w‖ ^ 2 ≤ Q w := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hQzero]
    · have hmem : Q w / ‖w‖ ^ 2 ∈ rayleighSetOn Q {w : V | J w = -w} := ⟨w, hw, hw0, rfl⟩
      have hle := hm.1 hmem
      have hpos : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
      rw [le_div_iff₀ hpos] at hle
      linarith
  constructor
  · rintro r ⟨v, -, hv0, rfl⟩
    have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    exact parity_rayleigh_lower_bound hJJ hJsym hsplit hlp hlm v
  · intro b hb
    have hbp : b ≤ lp := by
      refine hp.2 ?_
      rintro r ⟨v, hv, hv0, rfl⟩
      exact hb ⟨v, Set.mem_univ v, hv0, rfl⟩
    have hbm : b ≤ lm := by
      refine hm.2 ?_
      rintro r ⟨v, hv, hv0, rfl⟩
      exact hb ⟨v, Set.mem_univ v, hv0, rfl⟩
    exact le_min hbp hbm

end GaloisForLFunctions.HTGeometry
