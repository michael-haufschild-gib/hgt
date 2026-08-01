import GaloisForLFunctions.RHTower.SuzukiFullFrequencyNeumannHolonomy

/-!
# Homogeneous projective-resolvent Plücker lift for Suzuki source sewing

Suzuki's normalized triangle response is projective: numerator and characteristic denominator
are two linear observations of the same shifted resolvent source.  Consequently, its finite-shift
motion is not the coordinatewise affine defect of a scalar resolvent.

This module proves the exact replacement.  If

`u_alpha = (A - alpha)⁻¹ e`, `u_beta = (A - beta)⁻¹ e`, and
`v = (A - alpha)⁻¹ (A - beta)⁻¹ e`,

then every boundary projective minor satisfies

`[N,D](u_beta,u_alpha) = (beta-alpha) [N,D](v,A v)`.

An affine comparison numerator `L(u_lambda)-lambda*K(u_lambda)` becomes a fixed linear
observation after adding one homogeneous coordinate.  Its projective chord has the exact split

`Euler--Gamma spectral-pair blade - Neumann homogeneous blade`.

Thus one-mode linear Krein debt is not the source invariant: the Euler--Gamma quotient is blind
on invariant spectral lines, while genuine motion lives on spectral pairs and is governed by
their Plücker orientations.  This is the algebraic target for a source-level
Christoffel--Darboux/Green identity.  No RH assumption, positivity premise, Xi-divisor input, or
numerical computation occurs here.
-/

open Complex

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Alternating projective minor of two linear boundary observations.  This is the scalar
evaluation of `N ∧ D` on the ordered blade `x ∧ y`. -/
def suzukiProjectiveResolventMinor
    (N D : V →ₗ[ℂ] ℂ) (x y : V) : ℂ :=
  N x * D y - N y * D x

@[simp] theorem suzukiProjectiveResolventMinor_self
    (N D : V →ₗ[ℂ] ℂ) (x : V) :
    suzukiProjectiveResolventMinor N D x x = 0 := by
  simp [suzukiProjectiveResolventMinor]

theorem suzukiProjectiveResolventMinor_swap
    (N D : V →ₗ[ℂ] ℂ) (x y : V) :
    suzukiProjectiveResolventMinor N D y x =
      -suzukiProjectiveResolventMinor N D x y := by
  simp only [suzukiProjectiveResolventMinor]
  ring

/-- **Projective resolvent-chord identity.**  The two endpoint states lie on the affine line
through `A v` in direction `v`; their projective minor is the spectral shift times the fixed
Plücker blade `v ∧ A v`. -/
theorem suzukiProjectiveResolventMinor_chord
    (A : V →ₗ[ℂ] V) (N D : V →ₗ[ℂ] ℂ)
    (alpha beta : ℂ) (uAlpha uBeta v : V)
    (hBeta : uBeta = A v - alpha • v)
    (hAlpha : uAlpha = A v - beta • v) :
    suzukiProjectiveResolventMinor N D uBeta uAlpha =
      (beta - alpha) * suzukiProjectiveResolventMinor N D v (A v) := by
  rw [hBeta, hAlpha]
  simp only [suzukiProjectiveResolventMinor, map_sub, map_smul, smul_eq_mul]
  ring

/-- Resolvent instantiation of the projective chord identity.  The hypotheses are exactly the two
right-inverse equations and commutation of the two resolvents on the source vector. -/
theorem suzukiProjectiveResolventMinor_twoResolvents
    (A RAlpha RBeta : V →ₗ[ℂ] V) (N D : V →ₗ[ℂ] ℂ)
    (alpha beta : ℂ) (e : V)
    (hAlphaInv : ∀ x, A (RAlpha x) - alpha • RAlpha x = x)
    (hBetaInv : ∀ x, A (RBeta x) - beta • RBeta x = x)
    (hcomm : RAlpha (RBeta e) = RBeta (RAlpha e)) :
    suzukiProjectiveResolventMinor N D (RBeta e) (RAlpha e) =
      (beta - alpha) *
        suzukiProjectiveResolventMinor N D
          (RAlpha (RBeta e)) (A (RAlpha (RBeta e))) := by
  apply suzukiProjectiveResolventMinor_chord A N D alpha beta
  · exact (hAlphaInv (RBeta e)).symm
  · rw [hcomm]
    exact (hBetaInv (RAlpha e)).symm

/-- Projective motion of a quotient is its division-free minor divided by the two endpoint
denominators. -/
theorem suzukiProjectiveResponse_sub_eq_minor
    {nAlpha nBeta dAlpha dBeta : ℂ}
    (hAlpha : dAlpha ≠ 0) (hBeta : dBeta ≠ 0) :
    nBeta / dBeta - nAlpha / dAlpha =
      (nBeta * dAlpha - nAlpha * dBeta) / (dBeta * dAlpha) := by
  field_simp [hAlpha, hBeta]

/-! ## Homogenization of the affine Neumann channel -/

/-- Shifted numerator with a comparison channel affine in the form shift. -/
def suzukiShiftedAffineSourceNumerator
    (L K : V →ₗ[ℂ] ℂ) (lambda : ℂ) (u : V) : ℂ :=
  L u - lambda * K u

/-- The resolvent equation absorbs the shift-dependent comparison channel into a fixed boundary
functional plus one constant homogeneous coordinate. -/
theorem suzukiShiftedAffineSourceNumerator_eq_homogeneous
    (A : V →ₗ[ℂ] V) (L K : V →ₗ[ℂ] ℂ)
    (e u : V) (lambda : ℂ)
    (hres : A u - lambda • u = e) :
    suzukiShiftedAffineSourceNumerator L K lambda u =
      (L u - K (A u)) + K e := by
  simp only [suzukiShiftedAffineSourceNumerator]
  rw [← hres]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Homogeneous Plücker-chord identity.**  Adding constant homogeneous numerator coordinate
`c` joins the affine comparison channel to the Euler--Gamma pair blade. -/
theorem suzukiHomogeneousProjectiveResolventChord
    (A : V →ₗ[ℂ] V) (B D : V →ₗ[ℂ] ℂ)
    (alpha beta c : ℂ) (uAlpha uBeta v : V)
    (hBeta : uBeta = A v - alpha • v)
    (hAlpha : uAlpha = A v - beta • v) :
    (B uBeta + c) * D uAlpha - (B uAlpha + c) * D uBeta =
      (beta - alpha) *
        (B v * D (A v) - B (A v) * D v - c * D v) := by
  rw [hBeta, hAlpha]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Full source capstone.**  A numerator `L-lambda*K` on a resolvent orbit has one exact
homogeneous projective blade.  The first alternating term is the Euler--Gamma spectral-pair
sector; the term containing `K e` is the affine Neumann/homogeneous sector. -/
theorem suzukiShiftedAffineSourceProjectiveChord_twoResolvents
    (A RAlpha RBeta : V →ₗ[ℂ] V) (L K D : V →ₗ[ℂ] ℂ)
    (alpha beta : ℂ) (e : V)
    (hAlphaInv : ∀ x, A (RAlpha x) - alpha • RAlpha x = x)
    (hBetaInv : ∀ x, A (RBeta x) - beta • RBeta x = x)
    (hcomm : RAlpha (RBeta e) = RBeta (RAlpha e)) :
    suzukiShiftedAffineSourceNumerator L K beta (RBeta e) * D (RAlpha e) -
        suzukiShiftedAffineSourceNumerator L K alpha (RAlpha e) * D (RBeta e) =
      (beta - alpha) *
        ((L (RAlpha (RBeta e)) - K (A (RAlpha (RBeta e)))) *
            D (A (RAlpha (RBeta e))) -
          (L (A (RAlpha (RBeta e))) -
              K (A (A (RAlpha (RBeta e)))) + K e) *
            D (RAlpha (RBeta e))) := by
  let B : V →ₗ[ℂ] ℂ := L - K.comp A
  have hBetaState : RBeta e = A (RAlpha (RBeta e)) - alpha • RAlpha (RBeta e) :=
    (hAlphaInv (RBeta e)).symm
  have hAlphaState : RAlpha e = A (RAlpha (RBeta e)) - beta • RAlpha (RBeta e) := by
    rw [hcomm]
    exact (hBetaInv (RAlpha e)).symm
  have hNumBeta :
      suzukiShiftedAffineSourceNumerator L K beta (RBeta e) = B (RBeta e) + K e := by
    rw [suzukiShiftedAffineSourceNumerator_eq_homogeneous
      A L K e (RBeta e) beta (hBetaInv e)]
    rfl
  have hNumAlpha :
      suzukiShiftedAffineSourceNumerator L K alpha (RAlpha e) = B (RAlpha e) + K e := by
    rw [suzukiShiftedAffineSourceNumerator_eq_homogeneous
      A L K e (RAlpha e) alpha (hAlphaInv e)]
    rfl
  rw [hNumBeta, hNumAlpha]
  rw [suzukiHomogeneousProjectiveResolventChord A B D alpha beta (K e)
    (RAlpha e) (RBeta e) (RAlpha (RBeta e)) hBetaState hAlphaState]
  simp only [B, LinearMap.sub_apply, LinearMap.comp_apply]
  ring

/-! ## Spectral-pair orientation and rank-one blindness -/

/-- On a single invariant spectral line the Euler--Gamma projective blade vanishes identically,
regardless of the sign of the eigenvalue. -/
theorem suzukiProjectiveResolventMinor_eigenvector_eq_zero
    (A : V →ₗ[ℂ] V) (N D : V →ₗ[ℂ] ℂ)
    (t : ℂ) (v : V) (hA : A v = t • v) :
    suzukiProjectiveResolventMinor N D v (A v) = 0 := by
  rw [hA]
  simp only [suzukiProjectiveResolventMinor, map_smul, smul_eq_mul]
  ring

/-- Exact two-mode expansion of the Euler--Gamma projective blade.  Its sign carrier is the
source Plücker minor, multiplied by the spectral gap. -/
theorem suzukiTwoModeProjectiveResolventMinor_eq
    (t0 t1 v0 v1 b0 b1 d0 d1 : ℂ) :
    (b0 * v0 + b1 * v1) * (d0 * t0 * v0 + d1 * t1 * v1) -
        (b0 * t0 * v0 + b1 * t1 * v1) * (d0 * v0 + d1 * v1) =
      (t1 - t0) * v0 * v1 * (b0 * d1 - b1 * d0) := by
  ring

/-- **Sharp two-mode orientation law.**  For ordered spectral nodes and a positive filtered
source product, projective shift growth is nonnegative exactly when the source boundary minor has
positive Plücker orientation.  Individual node signs do not appear. -/
theorem suzukiTwoModeProjectiveResolventMinor_nonneg_iff_orientation
    {t0 t1 v0 v1 b0 b1 d0 d1 : ℝ}
    (ht : t0 < t1) (hv : 0 < v0 * v1) :
    0 ≤
        (b0 * v0 + b1 * v1) * (d0 * t0 * v0 + d1 * t1 * v1) -
          (b0 * t0 * v0 + b1 * t1 * v1) * (d0 * v0 + d1 * v1) ↔
      0 ≤ b0 * d1 - b1 * d0 := by
  have hfactor : 0 < (t1 - t0) * (v0 * v1) :=
    mul_pos (sub_pos.mpr ht) hv
  rw [show
      (b0 * v0 + b1 * v1) * (d0 * t0 * v0 + d1 * t1 * v1) -
          (b0 * t0 * v0 + b1 * t1 * v1) * (d0 * v0 + d1 * v1) =
        ((t1 - t0) * (v0 * v1)) * (b0 * d1 - b1 * d0) by ring]
  exact mul_nonneg_iff_of_pos_left hfactor

/-! ## Connector to the existing full-frequency Neumann holonomy -/

/-- Suzuki's centered Neumann numerator is literally the scalar projective minor of the two
central-jet/characteristic boundary columns. -/
theorem suzukiCenteredProjectiveShiftNumerator_eq_projectiveMinor
    (centralJetAlpha centralJetBeta : ℂ) (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiCenteredProjectiveShiftNumerator
        centralJetAlpha centralJetBeta WAlpha WBeta z =
      centralJetAlpha * WBeta z - centralJetBeta * WAlpha z := by
  rfl

end

/-! ## The finite diagonal expansion

`(10)` is the two-mode case.  Summing it over all coordinate pairs gives `(11)`: the chord of a
diagonal model expands as a double sum whose summand carries the spectral gap `t_j - t_i` against a
source Plücker minor.  The expansion is bilinear algebra — the resolvent denominators enter only
through the coefficients `v`. -/

/-- **`(11)`, the diagonal expansion.**  The chord of a diagonal model is the double sum of the
spectral gap against the source coefficients. -/
theorem suzukiDiagonalProjectiveChord_expansion {n : Type*} [Fintype n] (t v b d : n → ℝ) :
    (∑ i, b i * v i) * (∑ j, d j * (t j * v j))
        - (∑ i, b i * (t i * v i)) * (∑ j, d j * v j)
      = ∑ i, ∑ j, v i * v j * b i * d j * (t j - t i) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Rank-one blindness at the diagonal.**  Every diagonal term of the expansion vanishes, so a
single mode contributes nothing: the chord sees only genuine spectral pairs. -/
theorem suzukiDiagonalProjectiveChord_diagonal_eq_zero {n : Type*} (t v b d : n → ℝ) (i : n) :
    v i * v i * b i * d i * (t i - t i) = 0 := by
  ring

/-- **The blade separates from the source.**  Symmetrizing the expansion pairs the blade coordinate
`(t_j - t_i) v_i v_j`, which involves only the spectral data, against the source's own two-by-two
minor `b_i d_j - b_j d_i`.  This is `(4)`'s claim in coordinates: the chord's dependence on the
source enters only through source minors, the blade being fixed. -/
theorem suzukiDiagonalProjectiveChord_symmetrized {n : Type*} [Fintype n] (t v b d : n → ℝ) :
    2 * (∑ i, ∑ j, v i * v j * b i * d j * (t j - t i))
      = ∑ i, ∑ j, (t j - t i) * (v i * v j) * (b i * d j - b j * d i) := by
  have hswap : (∑ i, ∑ j, v i * v j * b i * d j * (t j - t i))
      = ∑ i, ∑ j, v j * v i * b j * d i * (t i - t j) := Finset.sum_comm
  rw [two_mul]
  nth_rewrite 2 [hswap]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end RHTower
