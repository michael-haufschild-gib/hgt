import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.ZetaValues

/-!
# The Montgomery–Vaughan Hilbert inequality

For real points `λ_1, …, λ_R` with `|λ_r − λ_s| ≥ δ > 0` (`r ≠ s`) and complex weights `z_r`,

`|Σ_{r ≠ s} z_r z̄_s / (λ_r − λ_s)| ≤ (π/δ) Σ |z_r|²`.

The constant has no logarithm: the row sums `Σ_s 1/|λ_r − λ_s|` diverge logarithmically, so the
bound needs the cancellation in the kernel. Proof (Montgomery–Vaughan): the matrix
`i/(λ_r − λ_s)` is Hermitian, so it suffices to bound its eigenvalues. On an eigenvector the
partial-fraction identity `K_{rs}K_{rt} = K_{st}(K_{rs} − K_{rt})` turns `‖Kv‖²` into
`Σ_s κ_s|v_s|² + 2Σ_{s,t} v_s v̄_t K_{st}²` plus terms that cancel, where `κ_s = Σ_r K_{rs}²`; and
`κ_s ≤ 2Σ_{k ≥ 1} (kδ)^{-2} = π²/(3δ²)`. Hence `μ² ≤ 3·π²/(3δ²)`.
-/

open Finset Matrix Real
open scoped ComplexConjugate

namespace GaloisForLFunctions.HilbertInequality

/-- A Hermitian matrix whose eigenvalues lie in `[-c, c]` has quadratic form bounded by `c‖x‖²`. -/
theorem norm_star_dotProduct_mulVec_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, |hA.eigenvalues i| ≤ c)
    (x : n → ℂ) : ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ c * ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  set y := star U *ᵥ x with hy
  have hsy : star y = star x ᵥ* U := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hAx : A *ᵥ x = U *ᵥ (D *ᵥ y) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hy, mulVec_mulVec, mulVec_mulVec]
  have hquad : star x ⬝ᵥ (A *ᵥ x) = ∑ i, (hA.eigenvalues i : ℂ) * (‖y i‖ ^ 2 : ℝ) := by
    rw [hAx, dotProduct_mulVec, ← hsy, hD, dotProduct]
    refine sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal, Complex.ofReal_pow, ← Complex.mul_conj', Function.comp_apply,
      Pi.star_apply, RCLike.star_def,
      show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl]
    ring
  have hnorm : ∑ i, ‖y i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    have h1 : ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
      rw [Complex.ofReal_sum, dotProduct]
      refine sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_pow, ← Complex.mul_conj', Pi.star_apply, RCLike.star_def, mul_comm]
    have h2 : ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) = star x ⬝ᵥ x := by
      rw [Complex.ofReal_sum, dotProduct]
      refine sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_pow, ← Complex.mul_conj', Pi.star_apply, RCLike.star_def, mul_comm]
    have h3 : star y ⬝ᵥ y = star x ⬝ᵥ x := by
      rw [hsy, ← dotProduct_mulVec, hy, mulVec_mulVec, hUU, one_mulVec]
    exact_mod_cast h1.trans (h3.trans h2.symm)
  rw [hquad, ← hnorm]
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖y i‖)]
  exact mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)


/-! ### The kernel row sum -/

/-- Positive numbers that are pairwise `δ`-separated and at least `δ` have `Σ 1/d² ≤ π²/(6δ²)`:
`d ↦ ⌊d/δ⌋` is injective with values `≥ 1`, and `d ≥ ⌊d/δ⌋ δ`. -/
theorem sum_one_div_sq_le_of_separated {ι : Type*} (S : Finset ι) (d : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hd : ∀ r ∈ S, δ ≤ d r)
    (hsep : ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' → δ ≤ |d r - d r'|) :
    ∑ r ∈ S, 1 / d r ^ 2 ≤ π ^ 2 / 6 / δ ^ 2 := by
  classical
  set h : ι → ℕ := fun r => ⌊d r / δ⌋₊ with hh
  have hq (r : ι) (hr : r ∈ S) : 1 ≤ d r / δ := (one_le_div hδ).mpr (hd r hr)
  have hh1 (r : ι) (hr : r ∈ S) : 1 ≤ h r := Nat.le_floor (by exact_mod_cast hq r hr)
  have hhle (r : ι) (hr : r ∈ S) : (h r : ℝ) * δ ≤ d r := by
    have := Nat.floor_le (zero_le_one.trans (hq r hr))
    rwa [le_div_iff₀ hδ] at this
  have hinj : Set.InjOn h S := by
    intro r hr r' hr' hrr
    by_contra hne
    have h1 := Nat.floor_le (zero_le_one.trans (hq r hr))
    have h2 := Nat.lt_floor_add_one (d r / δ)
    have h3 := Nat.floor_le (zero_le_one.trans (hq r' hr'))
    have h4 := Nat.lt_floor_add_one (d r' / δ)
    simp only [hh] at hrr
    rw [hrr] at h1 h2
    have hlt : |d r / δ - d r' / δ| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hlt
    exact absurd (hsep r (by simpa using hr) r' (by simpa using hr') hne) (not_le.mpr hlt)
  have hterm (r : ι) (hr : r ∈ S) : 1 / d r ^ 2 ≤ 1 / (h r : ℝ) ^ 2 / δ ^ 2 := by
    have hpos : 0 < (h r : ℝ) * δ := mul_pos (by exact_mod_cast hh1 r hr) hδ
    rw [div_div, ← mul_pow]
    exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le (hhle r hr) 2)
  calc ∑ r ∈ S, 1 / d r ^ 2 ≤ ∑ r ∈ S, 1 / (h r : ℝ) ^ 2 / δ ^ 2 := sum_le_sum hterm
    _ = (∑ k ∈ S.image h, 1 / (k : ℝ) ^ 2) / δ ^ 2 := by
        rw [sum_image hinj, sum_div]
    _ ≤ π ^ 2 / 6 / δ ^ 2 := by
        gcongr
        rw [← hasSum_zeta_two.tsum_eq]
        exact hasSum_zeta_two.summable.sum_le_tsum _ (fun _ _ => by positivity)

variable {ι : Type*}

/-- The Hilbert kernel `1/(λ_r − λ_s)`; it vanishes on the diagonal (`1/0 = 0`). -/
noncomputable def hilbertDifferenceKernel (l : ι → ℝ) (r s : ι) : ℝ := 1 / (l r - l s)

theorem hilbertDifferenceKernel_self (l : ι → ℝ) (r : ι) : hilbertDifferenceKernel l r r = 0 := by
  simp [hilbertDifferenceKernel]

theorem hilbertDifferenceKernel_swap (l : ι → ℝ) (r s : ι) : hilbertDifferenceKernel l s r = -hilbertDifferenceKernel l r s := by
  simp only [hilbertDifferenceKernel, one_div, ← inv_neg, neg_sub]

/-- **Row sum of the squared kernel.** For `δ`-separated points,
`Σ_r 1/(λ_r − λ_s)² ≤ π²/(3δ²)`: at most one point per gap `[kδ, (k+1)δ)` on each side. -/
theorem sum_hilbertDifferenceKernel_sq_le [Fintype ι] (l : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |l r - l s|) (s : ι) :
    ∑ r, hilbertDifferenceKernel l r s ^ 2 ≤ π ^ 2 / 3 / δ ^ 2 := by
  set P := univ.filter fun r => l s < l r
  set M := univ.filter fun r => l r < l s
  have hsplit : ∑ r, hilbertDifferenceKernel l r s ^ 2 =
      ∑ r ∈ P, 1 / (l r - l s) ^ 2 + ∑ r ∈ M, 1 / (l s - l r) ^ 2 := by
    rw [← sum_filter_add_sum_filter_not univ (fun r => l s < l r)]
    congr 1
    · exact sum_congr rfl fun r _ => by rw [hilbertDifferenceKernel, div_pow, one_pow]
    · rw [← sum_filter_add_sum_filter_not _ (fun r => l r < l s)]
      simp only [filter_filter]
      have hz : ∑ r ∈ univ.filter (fun r => ¬l s < l r ∧ ¬l r < l s), hilbertDifferenceKernel l r s ^ 2
          = 0 := by
        refine sum_eq_zero fun r hr => ?_
        obtain ⟨h1, h2⟩ := (mem_filter.mp hr).2
        rw [hilbertDifferenceKernel, show l r = l s by linarith, sub_self, div_zero, zero_pow two_ne_zero]
      have hfM : univ.filter (fun r => ¬l s < l r ∧ l r < l s) = M := by
        ext r
        simp only [mem_filter, mem_univ, true_and, M]
        exact ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩
      rw [hz, add_zero, hfM]
      refine sum_congr rfl fun r _ => ?_
      rw [hilbertDifferenceKernel, div_pow, one_pow, ← neg_sub, neg_sq]
  have hP := sum_one_div_sq_le_of_separated P (fun r => l r - l s) hδ
    (fun r hr => by
      have hlt := (mem_filter.mp hr).2
      have := hsep r s (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)
      rwa [abs_of_pos (sub_pos.mpr hlt)] at this)
    (fun r _ r' _ hne => by simpa using hsep r r' hne)
  have hM := sum_one_div_sq_le_of_separated M (fun r => l s - l r) hδ
    (fun r hr => by
      have hlt := (mem_filter.mp hr).2
      have := hsep r s (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)
      rwa [abs_of_neg (sub_neg.mpr hlt), neg_sub] at this)
    (fun r _ r' _ hne => by
      have := hsep r' r (Ne.symm hne)
      simpa [abs_sub_comm] using this)
  rw [hsplit, show π ^ 2 / 3 / δ ^ 2 = π ^ 2 / 6 / δ ^ 2 + π ^ 2 / 6 / δ ^ 2 by ring]
  exact add_le_add hP hM


/-! ### The eigenvector identity -/

theorem hilbertDifferenceKernel_mul [DecidableEq ι] (l : ι → ℝ) (hinj : Function.Injective l) {r s t : ι} (hst : s ≠ t) :
    hilbertDifferenceKernel l r s * hilbertDifferenceKernel l r t =
      hilbertDifferenceKernel l s t * (hilbertDifferenceKernel l r s - hilbertDifferenceKernel l r t) +
        ((if r = s then hilbertDifferenceKernel l s t ^ 2 else 0) +
          if r = t then hilbertDifferenceKernel l s t ^ 2 else 0) := by
  by_cases hrs : r = s
  · subst hrs
    simp [hilbertDifferenceKernel_self, hst]
    ring
  by_cases hrt : r = t
  · subst hrt
    simp [hilbertDifferenceKernel_self, hrs, hilbertDifferenceKernel_swap l r s]
    ring
  have h1 : l r - l s ≠ 0 := sub_ne_zero.mpr (hinj.ne hrs)
  have h2 : l r - l t ≠ 0 := sub_ne_zero.mpr (hinj.ne hrt)
  have h3 : l s - l t ≠ 0 := sub_ne_zero.mpr (hinj.ne hst)
  simp only [hrs, hrt, if_false, add_zero, hilbertDifferenceKernel]
  field_simp
  ring

variable [Fintype ι] [DecidableEq ι]

/-- **Partial fractions in the column sums.** With `σ_s = Σ_r K_{rs}` and `κ_s = Σ_r K_{rs}²`,
`Σ_r K_{rs} K_{rt} = K_{st}(σ_s − σ_t) + 2K_{st}² + [s = t] κ_s`. -/
theorem sum_hilbertDifferenceKernel_mul (l : ι → ℝ) (hinj : Function.Injective l) (s t : ι) :
    ∑ r, hilbertDifferenceKernel l r s * hilbertDifferenceKernel l r t =
      hilbertDifferenceKernel l s t * ((∑ r, hilbertDifferenceKernel l r s) - ∑ r, hilbertDifferenceKernel l r t) +
        2 * hilbertDifferenceKernel l s t ^ 2 + if s = t then ∑ r, hilbertDifferenceKernel l r s ^ 2 else 0 := by
  by_cases hst : s = t
  · subst hst
    simp [hilbertDifferenceKernel_self, sq]
  rw [sum_congr rfl fun r _ => hilbertDifferenceKernel_mul l hinj hst, sum_add_distrib, sum_add_distrib,
    ← mul_sum, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  simp only [mem_univ, if_true, hst, if_false]
  ring

/-- **Montgomery–Vaughan eigenvalue bound.** If `Σ_s K_{rs} v_s = −iμ v_r` for all `r`
(an eigenvector of the Hermitian matrix `iK`), then `μ² ‖v‖² ≤ (π/δ)² ‖v‖²`. The `σ`-terms of the
partial-fraction identity cancel on an eigenvector; the rest is three copies of `Σ κ_s|v_s|²`. -/
theorem sq_mul_sum_norm_sq_le_of_eigen (l : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |l r - l s|) (v : ι → ℂ) (μ : ℝ)
    (hv : ∀ r, ∑ s, (hilbertDifferenceKernel l r s : ℂ) * v s = -(Complex.I * μ) * v r) :
    μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ (π / δ) ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
  set K := hilbertDifferenceKernel l with hK
  have hinj : Function.Injective l := fun r s h => by
    by_contra hne
    have := hsep r s hne
    rw [h, sub_self, abs_zero] at this
    linarith
  set σ : ι → ℝ := fun s => ∑ r, K r s with hσ
  set κ : ι → ℝ := fun s => ∑ r, K r s ^ 2 with hκ
  set w : ι → ℂ := fun r => ∑ s, (K r s : ℂ) * v s with hw
  -- `‖w‖² = μ²‖v‖²` from the eigen-equation
  have hww : ∑ r, ‖w r‖ ^ 2 = μ ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    simp only [hw, hv r, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
  -- the quadratic expansion of `Σ_r |w_r|²`
  have hexp : ((∑ r, ‖w r‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, v s * conj (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    have h1 : ∀ r, ((‖w r‖ ^ 2 : ℝ) : ℂ) =
        ∑ s, ∑ t, v s * conj (v t) * ((K r s * K r t : ℝ) : ℂ) := by
      intro r
      rw [Complex.ofReal_pow, ← Complex.mul_conj', hw, map_sum, sum_mul_sum]
      refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [sum_congr rfl fun r _ => h1 r, sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [Complex.ofReal_sum, mul_sum]
  -- the `σ`-part vanishes on an eigenvector
  have hcross : ∑ s, ∑ t, v s * conj (v t) * ((K s t * (σ s - σ t) : ℝ) : ℂ) = 0 := by
    have hcol : ∀ t, ∑ s, (K s t : ℂ) * v s = -w t := by
      intro t
      rw [hw, ← sum_neg_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [hK, hilbertDifferenceKernel_swap l t s, Complex.ofReal_neg]
      ring
    have e1 : ∑ s, ∑ t, v s * conj (v t) * ((K s t * σ s : ℝ) : ℂ) =
        ∑ s, (σ s : ℂ) * (v s * conj (w s)) := by
      refine sum_congr rfl fun s _ => ?_
      rw [hw, map_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun t _ => ?_
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    have e2 : ∑ s, ∑ t, v s * conj (v t) * ((K s t * σ t : ℝ) : ℂ) =
        ∑ t, (σ t : ℂ) * (conj (v t) * -w t) := by
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [← hcol t, mul_sum, mul_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [Complex.ofReal_mul]
      ring
    have e3 : ∀ s, v s * conj (w s) + conj (v s) * w s = 0 := by
      intro s
      simp only [hw, hv s, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hsplit : ∑ s, ∑ t, v s * conj (v t) * ((K s t * (σ s - σ t) : ℝ) : ℂ) =
        ∑ s, ∑ t, v s * conj (v t) * ((K s t * σ s : ℝ) : ℂ) -
          ∑ s, ∑ t, v s * conj (v t) * ((K s t * σ t : ℝ) : ℂ) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      push_cast
      ring
    rw [hsplit, e1, e2, ← sum_sub_distrib]
    refine sum_eq_zero fun s _ => ?_
    linear_combination (σ s : ℂ) * e3 s
  -- what remains: the `2K²` cross term and the diagonal `Σ κ_s |v_s|²`
  have hsum : ((∑ r, ‖w r‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, v s * conj (v t) * ((2 * K s t ^ 2 : ℝ) : ℂ) +
        ((∑ s, ‖v s‖ ^ 2 * κ s : ℝ) : ℂ) := by
    rw [hexp]
    have h1 : ∀ s t, v s * conj (v t) * ((∑ r, K r s * K r t : ℝ) : ℂ) =
        v s * conj (v t) * ((K s t * (σ s - σ t) : ℝ) : ℂ) +
          v s * conj (v t) * ((2 * K s t ^ 2 : ℝ) : ℂ) +
            if s = t then ((‖v s‖ ^ 2 * κ s : ℝ) : ℂ) else 0 := by
      intro s t
      simp only [hσ, hκ, hK]
      rw [sum_hilbertDifferenceKernel_mul l hinj s t]
      split_ifs with hst
      · subst hst
        rw [hilbertDifferenceKernel_self]
        push_cast
        rw [← Complex.mul_conj']
        ring
      · push_cast
        ring
    simp_rw [h1, sum_add_distrib, sum_ite_eq, mem_univ, if_true, hcross, zero_add,
      Complex.ofReal_sum]
  have hB : ‖∑ s, ∑ t, v s * conj (v t) * ((2 * K s t ^ 2 : ℝ) : ℂ)‖ ≤
      2 * ∑ s, ‖v s‖ ^ 2 * κ s := by
    have hrow : ∀ s, ∑ t, K s t ^ 2 = κ s := fun s =>
      sum_congr rfl fun t _ => by rw [hK, hilbertDifferenceKernel_swap l s t, neg_sq]
    calc ‖∑ s, ∑ t, v s * conj (v t) * ((2 * K s t ^ 2 : ℝ) : ℂ)‖
        ≤ ∑ s, ∑ t, (‖v s‖ ^ 2 + ‖v t‖ ^ 2) * K s t ^ 2 := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => (norm_sum_le _ _).trans
            (sum_le_sum fun t _ => ?_))
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
          nlinarith [sq_nonneg (‖v s‖ - ‖v t‖), sq_nonneg (K s t)]
      _ = 2 * ∑ s, ‖v s‖ ^ 2 * κ s := by
          simp_rw [add_mul, sum_add_distrib]
          rw [sum_comm (f := fun s t => ‖v t‖ ^ 2 * K s t ^ 2)]
          simp_rw [← mul_sum, hrow]
          ring
  have hkap : ∑ s, ‖v s‖ ^ 2 * κ s ≤ π ^ 2 / 3 / δ ^ 2 * ∑ s, ‖v s‖ ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun s _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (sum_hilbertDifferenceKernel_sq_le l hδ hsep s) (sq_nonneg _)
  have hreal : ∑ r, ‖w r‖ ^ 2 ≤ 3 * ∑ s, ‖v s‖ ^ 2 * κ s := by
    have h := congrArg (‖·‖) hsum
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)] at h
    have hC : |∑ s, ‖v s‖ ^ 2 * κ s| = ∑ s, ‖v s‖ ^ 2 * κ s :=
      abs_of_nonneg (sum_nonneg fun s _ => mul_nonneg (sq_nonneg _)
        (sum_nonneg fun _ _ => sq_nonneg _))
    have := norm_add_le (∑ s, ∑ t, v s * conj (v t) * ((2 * K s t ^ 2 : ℝ) : ℂ))
      ((∑ s, ‖v s‖ ^ 2 * κ s : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, hC, ← h] at this
    linarith
  rw [← hww, div_pow]
  calc ∑ r, ‖w r‖ ^ 2 ≤ 3 * (π ^ 2 / 3 / δ ^ 2 * ∑ s, ‖v s‖ ^ 2) := hreal.trans (by linarith)
    _ = π ^ 2 / δ ^ 2 * ∑ r, ‖v r‖ ^ 2 := by ring


/-! ### The inequality -/

/-- **The Montgomery–Vaughan Hilbert inequality.** For real points with pairwise distances at
least `δ > 0` and complex weights,
`|Σ_{r ≠ s} z_r z̄_s /(λ_r − λ_s)| ≤ (π/δ) Σ |z_r|²` (the diagonal term vanishes as `1/0 = 0`).
The matrix `i/(λ_r − λ_s)` is Hermitian and every eigenvalue has modulus at most `π/δ`. -/
theorem norm_sum_mul_conj_hilbertDifferenceKernel_le (l : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |l r - l s|) (z : ι → ℂ) :
    ‖∑ r, ∑ s, z r * conj (z s) * (hilbertDifferenceKernel l r s : ℂ)‖ ≤ π / δ * ∑ r, ‖z r‖ ^ 2 := by
  set H : Matrix ι ι ℂ := fun r s => Complex.I * (hilbertDifferenceKernel l r s : ℂ) with hHdef
  have hH : H.IsHermitian := by
    ext r s
    simp only [hHdef, conjTranspose_apply, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, hilbertDifferenceKernel_swap l s r, Complex.ofReal_neg]
    ring
  have heig : ∀ i, |hH.eigenvalues i| ≤ π / δ := by
    intro i
    set v : ι → ℂ := ⇑(hH.eigenvectorBasis i) with hv
    have hmul := hH.mulVec_eigenvectorBasis i
    have hev : ∀ r, ∑ s, (hilbertDifferenceKernel l r s : ℂ) * v s =
        -(Complex.I * (hH.eigenvalues i : ℝ)) * v r := by
      intro r
      have h : (H *ᵥ v) r = (hH.eigenvalues i • v) r := congrFun hmul r
      rw [Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
        show (H *ᵥ v) r = ∑ s, Complex.I * (hilbertDifferenceKernel l r s : ℂ) * v s from rfl,
        show (RCLike.ofReal (hH.eigenvalues i) : ℂ) = (hH.eigenvalues i : ℂ) from rfl] at h
      have h' : ∑ s, (hilbertDifferenceKernel l r s : ℂ) * v s =
          -Complex.I * ∑ s, Complex.I * (hilbertDifferenceKernel l r s : ℂ) * v s := by
        rw [mul_sum]
        refine sum_congr rfl fun s _ => ?_
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [h', h]
      ring
    have hb := sq_mul_sum_norm_sq_le_of_eigen l hδ hsep v _ hev
    have hone : ∑ r, ‖v r‖ ^ 2 = 1 := by
      have h1 := hH.eigenvectorBasis.orthonormal.1 i
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
      simpa [hv] using h1
    rw [hone, mul_one, mul_one] at hb
    exact abs_le_of_sq_le_sq' hb (div_pos Real.pi_pos hδ).le |>.elim
      (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  have hq := norm_star_dotProduct_mulVec_le hH heig z
  have hrel : star z ⬝ᵥ (H *ᵥ z) =
      -Complex.I * ∑ r, ∑ s, z r * conj (z s) * (hilbertDifferenceKernel l r s : ℂ) := by
    simp only [dotProduct, mulVec, hHdef, Pi.star_apply, RCLike.star_def]
    simp_rw [mul_sum]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [hilbertDifferenceKernel_swap l s r, Complex.ofReal_neg]
    ring
  rw [hrel, norm_mul, norm_neg, Complex.norm_I, one_mul] at hq
  exact hq

end GaloisForLFunctions.HilbertInequality
