import Mathlib

/-!
# One-sided transfer along positive dilation kernels

A producer outputs a one-sided bound for one observable; the landing theorems need it for another.
This module is the transfer tool between observables related by a positive dilation kernel
`K f (x) = Σ_j a_j f(λ_j x)`, `a_j ≥ 0`, `λ_j > 0`, with gain `ρ(s) = Σ_j a_j λ_j^s` on the power
`x^s` (`dilationGain`).

* `le_rpow_of_le_add_dilate`: if `f ≤ g + K f`, `g ≤ A x^s` with `ρ(s) < 1`, and `f ≤ B x^v` at one
  exponent with `ρ(v) < 1`, then `f ≤ A / (1 − ρ(s)) · x^s`. The a priori exponent leaves no trace.
* `le_rpow_of_le_add_dilate_of_isLittleO`: the a priori bound may sit at a neutral exponent
  (`ρ(u) ≤ 1`) if it holds there with every `ε > 0` up to a contracting power.
* `transfer_constant_attained`: `f = A / (1 − ρ(s)) · x^s`, `g = A x^s` is a case of equality, so the
  constant is exact.
* `rpow_eq_sum_dilate_of_gain_eq_one`: a power with `ρ(u) = 1` satisfies `f = K f`; at a neutral
  exponent no bound on `g` controls `f`.
* `dilationGain_lt_one_of_barycentric`: for probability weights with barycentre `Σ a_j λ_j = 1` and
  two distinct scales, `ρ(s) < 1` for every `0 < s < 1`, by strict concavity of `x^s`. The neutral
  exponents are `0` and `1` (`dilationGain_zero`, `dilationGain_one`).

The halving kernel (`λ = ½`, `ρ(s) = 2^(−s)`) and the midpoint kernel (`λ = ⅔, 4/3` with weights
`½, ½`) are the two instances used by the landing theorems of the corpus.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

variable {ι : Type*}

/-- The gain on `x^s` of the dilation kernel `K f (x) = Σ_j a_j f(λ_j x)`. -/
def dilationGain (t : Finset ι) (a lam : ι → ℝ) (s : ℝ) : ℝ := ∑ j ∈ t, a j * lam j ^ s

theorem dilationGain_nonneg {t : Finset ι} {a lam : ι → ℝ} (ha : ∀ j ∈ t, 0 ≤ a j)
    (hl : ∀ j ∈ t, 0 < lam j) (s : ℝ) : 0 ≤ dilationGain t a lam s :=
  Finset.sum_nonneg fun j hj => mul_nonneg (ha j hj) (Real.rpow_nonneg (hl j hj).le s)

theorem dilationGain_zero (t : Finset ι) (a lam : ι → ℝ) :
    dilationGain t a lam 0 = ∑ j ∈ t, a j := by
  simp only [dilationGain, Real.rpow_zero, mul_one]

theorem dilationGain_one (t : Finset ι) (a lam : ι → ℝ) :
    dilationGain t a lam 1 = ∑ j ∈ t, a j * lam j := by
  simp only [dilationGain, Real.rpow_one]

/-- The kernel multiplies the power `x^s` by its gain. -/
theorem sum_mul_rpow_dilate {t : Finset ι} (a : ι → ℝ) {lam : ι → ℝ} (hl : ∀ j ∈ t, 0 < lam j)
    (s : ℝ) {x : ℝ} (hx : 0 < x) :
    ∑ j ∈ t, a j * (lam j * x) ^ s = dilationGain t a lam s * x ^ s := by
  rw [dilationGain, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j hj => by
    rw [Real.mul_rpow (hl j hj).le hx.le, mul_assoc]

/-- Iterating the kernel inequality multiplies each power by its gain; the target power sums to
the geometric series and the contracting a priori power disappears. -/
private theorem transfer_core {t : Finset ι} {a lam : ι → ℝ} (ha : ∀ j ∈ t, 0 ≤ a j)
    (hl : ∀ j ∈ t, 0 < lam j) {f g : ℝ → ℝ} {s u v A B ε ρs ρu ρv : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hρs : ρs < 1) (hρu0 : 0 ≤ ρu) (hρu : ρu ≤ 1) (hρv0 : 0 ≤ ρv) (hρv : ρv < 1)
    (es : ∀ x : ℝ, 0 < x → ∑ j ∈ t, a j * (lam j * x) ^ s = ρs * x ^ s)
    (eu : ∀ x : ℝ, 0 < x → ∑ j ∈ t, a j * (lam j * x) ^ u = ρu * x ^ u)
    (ev : ∀ x : ℝ, 0 < x → ∑ j ∈ t, a j * (lam j * x) ^ v = ρv * x ^ v)
    (hfg : ∀ x : ℝ, 0 < x → f x ≤ g x + ∑ j ∈ t, a j * f (lam j * x))
    (hg : ∀ x : ℝ, 0 < x → g x ≤ A * x ^ s)
    (hf : ∀ x : ℝ, 0 < x → f x ≤ ε * x ^ u + B * x ^ v) :
    ∀ x : ℝ, 0 < x → f x ≤ A / (1 - ρs) * x ^ s + ε * x ^ u := by
  have h1ρ : 0 < 1 - ρs := sub_pos.mpr hρs
  have hL : 0 ≤ A / (1 - ρs) := div_nonneg hA h1ρ.le
  have hL1 : A / (1 - ρs) * (1 - ρs) = A := div_mul_cancel₀ A h1ρ.ne'
  have habs : A / (1 - ρs) * ρs + A = A / (1 - ρs) := by linarith
  have iter : ∀ k : ℕ, ∀ x : ℝ, 0 < x →
      f x ≤ A / (1 - ρs) * x ^ s + ε * ρu ^ k * x ^ u + B * ρv ^ k * x ^ v := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have h0 := mul_nonneg hL (Real.rpow_nonneg hx.le s)
      have h1 := hf x hx
      simp only [pow_zero, mul_one]
      linarith
    | succ k ih =>
      intro x hx
      have hsum : ∑ j ∈ t, a j * f (lam j * x) ≤
          ∑ j ∈ t, a j * (A / (1 - ρs) * (lam j * x) ^ s + ε * ρu ^ k * (lam j * x) ^ u +
            B * ρv ^ k * (lam j * x) ^ v) :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (ih _ (mul_pos (hl j hj) hx)) (ha j hj)
      have hexp : ∑ j ∈ t, a j * (A / (1 - ρs) * (lam j * x) ^ s + ε * ρu ^ k * (lam j * x) ^ u +
            B * ρv ^ k * (lam j * x) ^ v) =
          A / (1 - ρs) * (ρs * x ^ s) + ε * ρu ^ k * (ρu * x ^ u) +
            B * ρv ^ k * (ρv * x ^ v) := by
        rw [← es x hx, ← eu x hx, ← ev x hx, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      calc f x ≤ g x + ∑ j ∈ t, a j * f (lam j * x) := hfg x hx
        _ ≤ A * x ^ s + (A / (1 - ρs) * (ρs * x ^ s) + ε * ρu ^ k * (ρu * x ^ u) +
              B * ρv ^ k * (ρv * x ^ v)) := add_le_add (hg x hx) (hsum.trans hexp.le)
        _ = (A / (1 - ρs) * ρs + A) * x ^ s + ε * ρu ^ (k + 1) * x ^ u +
              B * ρv ^ (k + 1) * x ^ v := by
          rw [pow_succ, pow_succ]
          ring
        _ = A / (1 - ρs) * x ^ s + ε * ρu ^ (k + 1) * x ^ u + B * ρv ^ (k + 1) * x ^ v := by
          rw [habs]
  intro x hx
  have bound : ∀ k : ℕ, f x ≤ A / (1 - ρs) * x ^ s + ε * x ^ u + B * x ^ v * ρv ^ k := by
    intro k
    have h1 := iter k x hx
    have h2 : ε * ρu ^ k * x ^ u ≤ ε * x ^ u := by
      have h := mul_le_of_le_one_right (mul_nonneg hε (Real.rpow_nonneg hx.le u))
        (pow_le_one₀ (n := k) hρu0 hρu)
      calc ε * ρu ^ k * x ^ u = ε * x ^ u * ρu ^ k := by ring
        _ ≤ ε * x ^ u := h
    have h3 : B * ρv ^ k * x ^ v = B * x ^ v * ρv ^ k := by ring
    linarith
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρv0 hρv).const_mul (B * x ^ v)).const_add
    (A / (1 - ρs) * x ^ s + ε * x ^ u)
  have hout := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := f x)) hlim bound
  simpa only [mul_zero, add_zero] using hout

/-- **One-sided transfer with a neutral remainder.** If `f ≤ g + K f`, `g ≤ A x^s` with
`ρ(s) < 1`, and `f ≤ ε x^u + B x^v` with `ρ(u) ≤ 1`, `ρ(v) < 1`, then
`f ≤ A / (1 − ρ(s)) · x^s + ε x^u`. -/
theorem le_of_le_add_dilate {t : Finset ι} {a lam : ι → ℝ} (ha : ∀ j ∈ t, 0 ≤ a j)
    (hl : ∀ j ∈ t, 0 < lam j) {f g : ℝ → ℝ} {s u v A B ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hs : dilationGain t a lam s < 1) (hu : dilationGain t a lam u ≤ 1)
    (hv : dilationGain t a lam v < 1)
    (hfg : ∀ x : ℝ, 0 < x → f x ≤ g x + ∑ j ∈ t, a j * f (lam j * x))
    (hg : ∀ x : ℝ, 0 < x → g x ≤ A * x ^ s)
    (hf : ∀ x : ℝ, 0 < x → f x ≤ ε * x ^ u + B * x ^ v) :
    ∀ x : ℝ, 0 < x → f x ≤ A / (1 - dilationGain t a lam s) * x ^ s + ε * x ^ u :=
  transfer_core ha hl hA hε hs (dilationGain_nonneg ha hl u) hu (dilationGain_nonneg ha hl v) hv
    (fun _ hx => sum_mul_rpow_dilate a hl s hx) (fun _ hx => sum_mul_rpow_dilate a hl u hx)
    (fun _ hx => sum_mul_rpow_dilate a hl v hx) hfg hg hf

/-- **One-sided transfer.** If `f ≤ g + K f`, `g ≤ A x^s` with `ρ(s) < 1`, and `f ≤ B x^v` at
one exponent with `ρ(v) < 1`, then `f ≤ A / (1 − ρ(s)) · x^s`. -/
theorem le_rpow_of_le_add_dilate {t : Finset ι} {a lam : ι → ℝ} (ha : ∀ j ∈ t, 0 ≤ a j)
    (hl : ∀ j ∈ t, 0 < lam j) {f g : ℝ → ℝ} {s v A B : ℝ} (hA : 0 ≤ A)
    (hs : dilationGain t a lam s < 1) (hv : dilationGain t a lam v < 1)
    (hfg : ∀ x : ℝ, 0 < x → f x ≤ g x + ∑ j ∈ t, a j * f (lam j * x))
    (hg : ∀ x : ℝ, 0 < x → g x ≤ A * x ^ s) (hf : ∀ x : ℝ, 0 < x → f x ≤ B * x ^ v) :
    ∀ x : ℝ, 0 < x → f x ≤ A / (1 - dilationGain t a lam s) * x ^ s := by
  intro x hx
  have h := le_of_le_add_dilate ha hl (u := v) (ε := 0) hA le_rfl hs hv.le hv hfg hg
    (fun y hy => by simpa only [zero_mul, zero_add] using hf y hy) x hx
  simpa only [zero_mul, add_zero] using h

/-- **One-sided transfer from a bound at a neutral exponent.** The a priori bound may sit at an
exponent with `ρ(u) ≤ 1`, provided it holds with every `ε > 0` up to a contracting power. -/
theorem le_rpow_of_le_add_dilate_of_isLittleO {t : Finset ι} {a lam : ι → ℝ}
    (ha : ∀ j ∈ t, 0 ≤ a j) (hl : ∀ j ∈ t, 0 < lam j) {f g : ℝ → ℝ} {s u A : ℝ} (hA : 0 ≤ A)
    (hs : dilationGain t a lam s < 1) (hu : dilationGain t a lam u ≤ 1)
    (hfg : ∀ x : ℝ, 0 < x → f x ≤ g x + ∑ j ∈ t, a j * f (lam j * x))
    (hg : ∀ x : ℝ, 0 < x → g x ≤ A * x ^ s)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ B v : ℝ, dilationGain t a lam v < 1 ∧
      ∀ x : ℝ, 0 < x → f x ≤ ε * x ^ u + B * x ^ v) :
    ∀ x : ℝ, 0 < x → f x ≤ A / (1 - dilationGain t a lam s) * x ^ s := by
  intro x hx
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hxu : 0 < x ^ u := Real.rpow_pos_of_pos hx u
  obtain ⟨B, v, hv, hbound⟩ := hf (δ / x ^ u) (div_pos hδ hxu)
  have h := le_of_le_add_dilate ha hl hA (div_pos hδ hxu).le hs hu hv hfg hg hbound x hx
  rwa [div_mul_cancel₀ _ hxu.ne'] at h

/-- **The constant is exact.** `f = A / (1 − ρ(s)) · x^s` and `g = A x^s` satisfy `f = g + K f`. -/
theorem transfer_constant_attained {t : Finset ι} (a : ι → ℝ) {lam : ι → ℝ}
    (hl : ∀ j ∈ t, 0 < lam j) {s A : ℝ} (hs : dilationGain t a lam s ≠ 1) {x : ℝ} (hx : 0 < x) :
    A / (1 - dilationGain t a lam s) * x ^ s =
      A * x ^ s + ∑ j ∈ t, a j * (A / (1 - dilationGain t a lam s) * (lam j * x) ^ s) := by
  have hne : 1 - dilationGain t a lam s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hL1 := div_mul_cancel₀ A hne
  have e : ∑ j ∈ t, a j * (A / (1 - dilationGain t a lam s) * (lam j * x) ^ s) =
      A / (1 - dilationGain t a lam s) * (dilationGain t a lam s * x ^ s) := by
    rw [← sum_mul_rpow_dilate a hl s hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : A / (1 - dilationGain t a lam s) * x ^ s =
      A / (1 - dilationGain t a lam s) * (1 - dilationGain t a lam s) * x ^ s +
        A / (1 - dilationGain t a lam s) * (dilationGain t a lam s * x ^ s) := by ring
  rw [e, e2, hL1]

/-- **Neutral exponents carry no transfer.** A power with `ρ(u) = 1` satisfies `f = K f`, so no
bound on `g = f − K f` controls its multiples. -/
theorem rpow_eq_sum_dilate_of_gain_eq_one {t : Finset ι} (a : ι → ℝ) {lam : ι → ℝ}
    (hl : ∀ j ∈ t, 0 < lam j) {u : ℝ} (hu : dilationGain t a lam u = 1) {x : ℝ} (hx : 0 < x) :
    x ^ u = ∑ j ∈ t, a j * (lam j * x) ^ u := by
  rw [sum_mul_rpow_dilate a hl u hx, hu, one_mul]

/-- **Barycentric stencils contract every power strictly between `0` and `1`.** For probability
weights `a_j` on scales `λ_j` with barycentre `Σ a_j λ_j = 1` and two distinct scales, the gain
`Σ a_j λ_j^s` is `< 1` for `0 < s < 1`, by strict concavity of `x ↦ x^s`. -/
theorem dilationGain_lt_one_of_barycentric {t : Finset ι} {a lam : ι → ℝ}
    (ha : ∀ j ∈ t, 0 < a j) (hl : ∀ j ∈ t, 0 < lam j) (h0 : ∑ j ∈ t, a j = 1)
    (h1 : ∑ j ∈ t, a j * lam j = 1) (hne : ∃ j ∈ t, ∃ k ∈ t, lam j ≠ lam k) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : dilationGain t a lam s < 1 := by
  have h := (Real.strictConcaveOn_rpow hs0 hs1).lt_map_sum ha h0
    (fun j hj => Set.mem_Ici.mpr (hl j hj).le) hne
  simp only [smul_eq_mul] at h
  rw [h1, Real.one_rpow] at h
  exact h

end GaloisForLFunctions.ArithmeticProducerTheory
