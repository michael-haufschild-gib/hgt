import Mathlib

/-!
# The staircase assembly inequality

The certificate for the constrained restricted Weil form replaces the multiplier `m_S` by a
staircase `Σ_b c_b 1_{B_b} + c_∞ 1_{rest}` with band projections `P_b`, splits a test `x = y + z`
into a finite-dimensional low part `y` and a high part `z` orthogonal to it, and uses three inputs:

* the low block is bounded below, `q(y) ≥ a ‖y‖²` (the certified finite eigenvalue);
* the high part has little mass in the finite bands, `Σ_b ‖P_b z‖² ≤ M ‖z‖²` (Taylor localisation);
* the band constants are bounded, `|c_b − c_∞| ≤ D`.

Then, writing `q(v, w)` for the staircase bilinear form,

```
  q(x) ≥ a ‖y‖² − 2 D √M ‖y‖ ‖z‖ + (c_∞ − (c_∞ − c_min)⁺ M) ‖z‖²,
```

and if `κ ≤ a`, `κ ≤ c_∞ − (c_∞ − c_min)⁺ M` and `D² M ≤ (a − κ)(c − κ)` then `q(x) ≥ κ ‖x‖²`.
This file proves that assembly in an abstract real inner product space, for any finite family of
mutually orthogonal self-adjoint idempotents.  Nothing here is specific to the Weil form; it is the
linear-algebra skeleton of the certificate, so that the only unformalised input is the finite
numerical block.
-/

open Finset
open scoped RealInnerProductSpace

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite family of mutually orthogonal self-adjoint idempotents (band projections). -/
structure BandProjections (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) where
  P : Fin n → E →ₗ[ℝ] E
  self_adjoint : ∀ b (v w : E), ⟪P b v, w⟫ = ⟪v, P b w⟫
  idem : ∀ b (v : E), P b (P b v) = P b v
  orth : ∀ b c, b ≠ c → ∀ v : E, P b (P c v) = 0

namespace BandProjections

variable {n : ℕ} (B : BandProjections E n)

theorem inner_P_P (b : Fin n) (v w : E) : ⟪B.P b v, B.P b w⟫ = ⟪v, B.P b w⟫ := by
  rw [B.self_adjoint, B.idem]

theorem inner_P_P_ne {b c : Fin n} (hbc : b ≠ c) (v w : E) : ⟪B.P b v, B.P c w⟫ = 0 := by
  rw [B.self_adjoint, B.orth b c hbc, inner_zero_right]

theorem inner_P_self_nonneg (b : Fin n) (v : E) : 0 ≤ ⟪v, B.P b v⟫ := by
  rw [← B.inner_P_P]; exact real_inner_self_nonneg

/-- `‖Σ_b P_b v‖² = Σ_b ⟪v, P_b v⟫`. -/
theorem norm_sum_P_sq (v : E) : ‖∑ b, B.P b v‖ ^ (2 : ℕ) = ∑ b, ⟪v, B.P b v⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine sum_congr rfl (fun b _ => ?_)
  rw [inner_sum, sum_eq_single b]
  · exact B.inner_P_P b v v
  · intro c _ hcb
    exact B.inner_P_P_ne (Ne.symm hcb) v v
  · intro h; exact absurd (mem_univ b) h

/-- Bessel: `Σ_b ⟪v, P_b v⟫ ≤ ‖v‖²`. -/
theorem sum_inner_P_le (v : E) : ∑ b, ⟪v, B.P b v⟫ ≤ ‖v‖ ^ (2 : ℕ) := by
  have h0 : 0 ≤ ‖v - ∑ b, B.P b v‖ ^ (2 : ℕ) := by positivity
  have hexp : ‖v - ∑ b, B.P b v‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℕ) - ∑ b, ⟪v, B.P b v⟫ := by
    rw [norm_sub_sq_real, B.norm_sum_P_sq, inner_sum]
    ring
  linarith

/-- The staircase bilinear form `q(v, w) = Σ_b c_b ⟪v, P_b w⟫ + c_∞ (⟪v, w⟫ − Σ_b ⟪v, P_b w⟫)`. -/
noncomputable def staircaseForm (c : Fin n → ℝ) (cinf : ℝ) (v w : E) : ℝ :=
  ∑ b, c b * ⟪v, B.P b w⟫ + cinf * (⟪v, w⟫ - ∑ b, ⟪v, B.P b w⟫)

theorem staircaseForm_symm (c : Fin n → ℝ) (cinf : ℝ) (v w : E) :
    B.staircaseForm c cinf v w = B.staircaseForm c cinf w v := by
  unfold staircaseForm
  have h : ∀ b, ⟪v, B.P b w⟫ = ⟪w, B.P b v⟫ := fun b => by
    rw [← B.self_adjoint, real_inner_comm]
  simp only [h, real_inner_comm v w]

theorem staircaseForm_add_left (c : Fin n → ℝ) (cinf : ℝ) (v v' w : E) :
    B.staircaseForm c cinf (v + v') w = B.staircaseForm c cinf v w + B.staircaseForm c cinf v' w := by
  unfold staircaseForm
  simp only [inner_add_left, mul_add, sum_add_distrib]
  ring

theorem staircaseForm_add_right (c : Fin n → ℝ) (cinf : ℝ) (v w w' : E) :
    B.staircaseForm c cinf v (w + w') = B.staircaseForm c cinf v w + B.staircaseForm c cinf v w' := by
  rw [B.staircaseForm_symm, B.staircaseForm_add_left, B.staircaseForm_symm c cinf w,
    B.staircaseForm_symm c cinf w']

/-- Expansion of the form on a sum. -/
theorem staircaseForm_add_add (c : Fin n → ℝ) (cinf : ℝ) (y z : E) :
    B.staircaseForm c cinf (y + z) (y + z) =
      B.staircaseForm c cinf y y + 2 * B.staircaseForm c cinf y z + B.staircaseForm c cinf z z := by
  rw [B.staircaseForm_add_left, B.staircaseForm_add_right, B.staircaseForm_add_right,
    B.staircaseForm_symm c cinf z y]
  ring

/-- **High block.**  If `Σ_b ⟪z, P_b z⟫ ≤ M ‖z‖²`, then
`q(z, z) ≥ (c_∞ − (c_∞ − c_min)⁺ M) ‖z‖²` where `c_min ≤ c_b` for all `b`. -/
theorem staircaseForm_self_ge_high (c : Fin n → ℝ) (cinf cmin M : ℝ) (hc : ∀ b, cmin ≤ c b)
    (z : E) (hM : ∑ b, ⟪z, B.P b z⟫ ≤ M * ‖z‖ ^ (2 : ℕ)) :
    (cinf - max (cinf - cmin) 0 * M) * ‖z‖ ^ (2 : ℕ) ≤ B.staircaseForm c cinf z z := by
  unfold staircaseForm
  rw [real_inner_self_eq_norm_sq]
  have hsum : ∑ b, (cinf - c b) * ⟪z, B.P b z⟫ ≤ max (cinf - cmin) 0 * ∑ b, ⟪z, B.P b z⟫ := by
    rw [mul_sum]
    refine sum_le_sum (fun b _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (B.inner_P_self_nonneg b z)
    exact le_trans (by linarith [hc b]) (le_max_left _ _)
  have hS0 : 0 ≤ ∑ b, ⟪z, B.P b z⟫ := sum_nonneg (fun b _ => B.inner_P_self_nonneg b z)
  have h2 : max (cinf - cmin) 0 * ∑ b, ⟪z, B.P b z⟫ ≤ max (cinf - cmin) 0 * (M * ‖z‖ ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hM (le_max_right _ _)
  have hid : ∑ b, c b * ⟪z, B.P b z⟫ + cinf * (‖z‖ ^ (2 : ℕ) - ∑ b, ⟪z, B.P b z⟫) =
      cinf * ‖z‖ ^ (2 : ℕ) - ∑ b, (cinf - c b) * ⟪z, B.P b z⟫ := by
    simp only [sub_mul, sum_sub_distrib, mul_sub, Finset.mul_sum]
    ring
  rw [hid]
  nlinarith

/-- **Cross term.**  For `⟪y, z⟫ = 0`, `|c_b − c_∞| ≤ D` and `Σ_b ⟪z, P_b z⟫ ≤ M ‖z‖²`,
`|q(y, z)| ≤ D √M ‖y‖ ‖z‖`. -/
theorem abs_staircaseForm_le_cross (c : Fin n → ℝ) (cinf D M : ℝ) (hD : ∀ b, |c b - cinf| ≤ D)
    (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (y z : E) (hyz : ⟪y, z⟫ = 0)
    (hM : ∑ b, ⟪z, B.P b z⟫ ≤ M * ‖z‖ ^ (2 : ℕ)) :
    |B.staircaseForm c cinf y z| ≤ D * Real.sqrt M * ‖y‖ * ‖z‖ := by
  have hid : B.staircaseForm c cinf y z = ∑ b, (c b - cinf) * ⟪B.P b y, B.P b z⟫ := by
    unfold staircaseForm
    rw [hyz]
    simp only [B.inner_P_P, sub_mul, sum_sub_distrib, zero_sub, mul_neg, Finset.mul_sum]
    ring
  rw [hid]
  calc |∑ b, (c b - cinf) * ⟪B.P b y, B.P b z⟫|
      ≤ ∑ b, |(c b - cinf) * ⟪B.P b y, B.P b z⟫| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, D * (‖B.P b y‖ * ‖B.P b z‖) := by
        refine sum_le_sum (fun b _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hD b) (abs_real_inner_le_norm _ _) (abs_nonneg _) hD0
    _ = D * ∑ b, ‖B.P b y‖ * ‖B.P b z‖ := by rw [mul_sum]
    _ ≤ D * (Real.sqrt (∑ b, ‖B.P b y‖ ^ (2 : ℕ)) * Real.sqrt (∑ b, ‖B.P b z‖ ^ (2 : ℕ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ D * (‖y‖ * (Real.sqrt M * ‖z‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0
        have hy : Real.sqrt (∑ b, ‖B.P b y‖ ^ (2 : ℕ)) ≤ ‖y‖ := by
          rw [Real.sqrt_le_left (norm_nonneg _)]
          calc ∑ b, ‖B.P b y‖ ^ (2 : ℕ) = ∑ b, ⟪y, B.P b y⟫ := by
                refine sum_congr rfl (fun b _ => ?_)
                rw [← real_inner_self_eq_norm_sq, B.inner_P_P]
            _ ≤ ‖y‖ ^ (2 : ℕ) := B.sum_inner_P_le y
        have hz : Real.sqrt (∑ b, ‖B.P b z‖ ^ (2 : ℕ)) ≤ Real.sqrt M * ‖z‖ := by
          rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_mul hM0]
          refine Real.sqrt_le_sqrt ?_
          calc ∑ b, ‖B.P b z‖ ^ (2 : ℕ) = ∑ b, ⟪z, B.P b z⟫ := by
                refine sum_congr rfl (fun b _ => ?_)
                rw [← real_inner_self_eq_norm_sq, B.inner_P_P]
            _ ≤ M * ‖z‖ ^ (2 : ℕ) := hM
        exact mul_le_mul hy hz (Real.sqrt_nonneg _) (norm_nonneg _)
    _ = D * Real.sqrt M * ‖y‖ * ‖z‖ := by ring

/-- The scalar `2 × 2` certificate: if `κ ≤ a`, `κ ≤ r` and `β² ≤ (a − κ)(r − κ)` then
`a Y² − 2 β Y Z + r Z² ≥ κ (Y² + Z²)`. -/
theorem two_by_two_certificate {a r β κ Y Z : ℝ} (hκa : κ ≤ a) (hκr : κ ≤ r)
    (hdet : β ^ (2 : ℕ) ≤ (a - κ) * (r - κ)) :
    κ * (Y ^ (2 : ℕ) + Z ^ (2 : ℕ)) ≤ a * Y ^ (2 : ℕ) - 2 * β * Y * Z + r * Z ^ (2 : ℕ) := by
  set p : ℝ := a - κ with hp
  set q : ℝ := r - κ with hq
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  suffices h : 0 ≤ p * Y ^ (2 : ℕ) - 2 * β * Y * Z + q * Z ^ (2 : ℕ) by
    have : a * Y ^ (2 : ℕ) - 2 * β * Y * Z + r * Z ^ (2 : ℕ) - κ * (Y ^ (2 : ℕ) + Z ^ (2 : ℕ)) =
        p * Y ^ (2 : ℕ) - 2 * β * Y * Z + q * Z ^ (2 : ℕ) := by rw [hp, hq]; ring
    linarith
  rcases eq_or_lt_of_le hp0 with hp0' | hppos
  · have hβ : β = 0 := by
      have : β ^ (2 : ℕ) ≤ 0 := by rw [← hp0'] at hdet; linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    rw [← hp0', hβ]
    nlinarith [sq_nonneg Z]
  · have key : p * (p * Y ^ (2 : ℕ) - 2 * β * Y * Z + q * Z ^ (2 : ℕ)) =
        (p * Y - β * Z) ^ (2 : ℕ) + (p * q - β ^ (2 : ℕ)) * Z ^ (2 : ℕ) := by ring
    have hnn : 0 ≤ p * (p * Y ^ (2 : ℕ) - 2 * β * Y * Z + q * Z ^ (2 : ℕ)) := by
      rw [key]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    exact (mul_nonneg_iff_of_pos_left hppos).1 hnn

/-- **Staircase assembly.**  With a low block bound `q(y) ≥ a ‖y‖²`, the high-mass bound
`Σ_b ⟪z, P_b z⟫ ≤ M ‖z‖²`, band constants `c_min ≤ c_b`, `|c_b − c_∞| ≤ D`, and the `2 × 2`
certificate conditions, the staircase form satisfies `q(y + z) ≥ κ ‖y + z‖²`. -/
theorem staircaseForm_ge_of_certificate (c : Fin n → ℝ) (cinf cmin D M a κ : ℝ)
    (hc : ∀ b, cmin ≤ c b) (hD : ∀ b, |c b - cinf| ≤ D) (hD0 : 0 ≤ D) (hM0 : 0 ≤ M)
    (y z : E) (hyz : ⟪y, z⟫ = 0) (hM : ∑ b, ⟪z, B.P b z⟫ ≤ M * ‖z‖ ^ (2 : ℕ))
    (hlow : a * ‖y‖ ^ (2 : ℕ) ≤ B.staircaseForm c cinf y y)
    (hκa : κ ≤ a) (hκr : κ ≤ cinf - max (cinf - cmin) 0 * M)
    (hdet : (D * Real.sqrt M) ^ (2 : ℕ) ≤ (a - κ) * (cinf - max (cinf - cmin) 0 * M - κ)) :
    κ * ‖y + z‖ ^ (2 : ℕ) ≤ B.staircaseForm c cinf (y + z) (y + z) := by
  rw [B.staircaseForm_add_add, norm_add_sq_real, hyz, mul_zero, add_zero]
  have hhigh := B.staircaseForm_self_ge_high c cinf cmin M hc z hM
  have hcross := B.abs_staircaseForm_le_cross c cinf D M hD hD0 hM0 y z hyz hM
  have hcross' : -(D * Real.sqrt M * ‖y‖ * ‖z‖) ≤ B.staircaseForm c cinf y z :=
    (abs_le.1 hcross).1
  have h22 := two_by_two_certificate (Y := ‖y‖) (Z := ‖z‖) hκa hκr hdet
  nlinarith

end BandProjections

end RHTower
