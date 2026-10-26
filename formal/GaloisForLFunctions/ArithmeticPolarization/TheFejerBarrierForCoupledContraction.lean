import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# The Fejér barrier for coupled contraction

A positive completion of a charged weight is a harmonic lift `Π_k F(s ± ikγ)^{b_k}`; its coupled
contractions are governed by Post–Widder positivity of polar sums (ACP `polarScaleWeight`). This
module isolates the law behind every real-anchor statement and proves that no harmonic lift ever
removes the whole lifted divisor of a deepest quartet.

* **The leading-line law** (`leadingSum_nonneg_of_periodic`). For a conjugation-symmetric polar
  configuration with positive-definite vertical sections, the trigonometric sum
  `T(t) = Σ_{Re z = σ_max} c(z) cos(Im z · t)` of its rightmost line is nonnegative wherever it is
  periodic: the scale weight is `e^{σ_max t}(T(t) + o(1))`, and periodicity returns every value of
  `T` at arbitrarily large `t`. The real-anchor laws of ACP are Fourier inequalities of this
  positivity: averaging `T(θ)(1 ± cos θ) ≥ 0` over a period gives `|w₁| ≤ 2w₀`.
* **Harmonic lifts** (`harmonicLift_leading`). The deepest quartet `½ + a ± iγ` of multiplicity `m`,
  lifted by `Π_k F(s ± ikγ)^{b_k}`, puts on the line `Re s = ½ + a` the trigonometric sum
  `2m cos(γt) P(γt)`, `P(θ) = Σ_k b_k cos kθ`.
* **The barrier** (`exists_cos_mul_neg`, `not_removes_lifted_divisor`). For every nonnegative cosine
  polynomial `P ≢ 0`, `cos θ · P(θ) < 0` somewhere; hence no positive multiplier has the whole lifted
  deepest-line divisor as its leading line. A harmonic coupling contracts at most part of each
  lifted quartet, whatever its coefficients.
-/

open Complex Finset Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry

/-! ### 1. The leading-line law -/

/-- The **leading-line sum** `T(t) = Σ_{z ∈ S, Re z = σ} c(z) cos(Im z · t)`. -/
def leadingSum (S : Finset ℂ) (c : ℂ → ℝ) (σ : ℝ) (t : ℝ) : ℝ :=
  ∑ z ∈ S.filter (fun z => z.re = σ), c z * Real.cos (z.im * t)

/-- The off-leading remainder `R(t) = Σ_{Re z ≠ σ} c(z) e^{(Re z − σ)t} cos(Im z · t)`. -/
def offLeadingSum (S : Finset ℂ) (c : ℂ → ℝ) (σ : ℝ) (t : ℝ) : ℝ :=
  ∑ z ∈ S.filter (fun z => z.re ≠ σ), c z * Real.exp ((z.re - σ) * t) * Real.cos (z.im * t)

/-- The scale weight splits as `e^{σ t} (T(t) + R(t))`. -/
theorem polarScaleWeight_eq_leading (S : Finset ℂ) (c : ℂ → ℝ) (σ t : ℝ) :
    polarScaleWeight S c t = Real.exp (σ * t) * (leadingSum S c σ t + offLeadingSum S c σ t) := by
  rw [polarScaleWeight, ← Finset.sum_filter_add_sum_filter_not S (fun z => z.re = σ), leadingSum,
    offLeadingSum, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun z hz => ?_
    rw [(Finset.mem_filter.mp hz).2]; ring
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [show Real.exp (z.re * t) = Real.exp (σ * t) * Real.exp ((z.re - σ) * t) by
      rw [← Real.exp_add]; ring_nf]
    ring

/-- The remainder vanishes at infinity when no weighted point lies right of the leading line. -/
theorem tendsto_offLeadingSum {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ) :
    Tendsto (offLeadingSum S c σ) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ z ∈ S.filter (fun z => z.re ≠ σ), (0 : ℝ) by simp]
  refine tendsto_finsetSum _ fun z hz => ?_
  have hne := (Finset.mem_filter.mp hz).2
  by_cases hc : c z = 0
  · simp [hc]
  have hlt : z.re - σ < 0 := by
    have := hmax z (Finset.mem_filter.mp hz).1 hc
    exact sub_neg.mpr (lt_of_le_of_ne this hne)
  have hexp : Tendsto (fun t => Real.exp ((z.re - σ) * t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hlt)
    simpa [Function.comp_def, mul_comm] using this
  have hb : Tendsto (fun t => |c z| * Real.exp ((z.re - σ) * t)) atTop (𝓝 0) := by
    simpa using hexp.const_mul |c z|
  refine squeeze_zero_norm (fun t => ?_) hb
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (z.im * t)
  have h0 : 0 ≤ |c z| * Real.exp ((z.re - σ) * t) := by positivity
  nlinarith [abs_nonneg (c z), Real.exp_pos ((z.re - σ) * t)]

/-- **The leading-line law.** For a conjugation-symmetric polar configuration with
positive-definite vertical sections and no weighted point right of `σ_max`, the leading-line sum
is nonnegative at every point where it is `τ`-periodic. -/
theorem leadingSum_nonneg_of_periodic {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σmax τ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax) (hτ : 0 < τ)
    (hper : ∀ t, leadingSum S c σmax (t + τ) = leadingSum S c σmax t) (t : ℝ) :
    0 ≤ leadingSum S c σmax t := by
  by_contra hneg
  rw [not_le] at hneg
  have hiter : ∀ n : ℕ, leadingSum S c σmax (t + n * τ) = leadingSum S c σmax t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hper, ih]
  have hseq : Tendsto (fun n : ℕ => t + n * τ) atTop atTop :=
    tendsto_atTop_add_const_left _ t (tendsto_natCast_atTop_atTop.atTop_mul_const hτ)
  have hR := (tendsto_offLeadingSum hmax).comp hseq
  have hev1 : ∀ᶠ n : ℕ in atTop, offLeadingSum S c σmax (t + n * τ) <
      -leadingSum S c σmax t :=
    hR.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, 0 < t + n * τ := hseq.eventually (eventually_gt_atTop 0)
  obtain ⟨n, h1, h2⟩ := (hev1.and hev2).exists
  have hw := posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re hpd h2
  rw [polarScaleWeight_eq_leading, hiter n] at hw
  have : leadingSum S c σmax t + offLeadingSum S c σmax (t + n * τ) < 0 := by linarith
  have := mul_neg_of_pos_of_neg (Real.exp_pos (σmax * (t + n * τ))) this
  linarith

/-! ### 2. Harmonic lifts and the barrier -/

/-- The cosine polynomial `P(θ) = Σ_{k<N} b_k cos kθ` of a harmonic coupling. -/
def cosPoly (b : ℕ → ℝ) (N : ℕ) (θ : ℝ) : ℝ := ∑ k ∈ range N, b k * Real.cos (k * θ)

/-- **The leading line of a harmonic lift.** Lifting the deepest quartet `½ + a ± iγ` by shifts
`±kγ` with weights `m b_k` puts the trigonometric sum `2m cos(γt) P(γt)` on the deepest line. -/
theorem harmonicLift_leading (m γ t : ℝ) (b : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range N, m * b k * (Real.cos ((γ - k * γ) * t) + Real.cos ((-γ - k * γ) * t)) =
      2 * m * Real.cos (γ * t) * cosPoly b N (γ * t) := by
  rw [cosPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (γ - k * γ) * t = γ * t - k * (γ * t) by ring,
    show (-γ - k * γ) * t = -(γ * t + k * (γ * t)) by ring, Real.cos_neg, Real.cos_sub,
    Real.cos_add]
  ring

/-- A cosine polynomial is a polynomial in `cos θ` (Chebyshev). -/
theorem cosPoly_eq_eval (b : ℕ → ℝ) (N : ℕ) (θ : ℝ) :
    cosPoly b N θ =
      (∑ k ∈ range N, Polynomial.C (b k) * Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) := by
  rw [cosPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
  push_cast; ring

/-- **The barrier inequality.** If a cosine polynomial is nonnegative and not identically zero,
`cos θ · P(θ) < 0` for some `θ`. -/
theorem exists_cos_mul_neg {b : ℕ → ℝ} {N : ℕ} (hP : ∀ θ, 0 ≤ cosPoly b N θ)
    (hne : ∃ θ₀, cosPoly b N θ₀ ≠ 0) : ∃ θ, Real.cos θ * cosPoly b N θ < 0 := by
  classical
  set Q := ∑ k ∈ range N, Polynomial.C (b k) * Polynomial.Chebyshev.T ℝ (k : ℤ)
  have hQ : Q ≠ 0 := by
    rintro hQ0
    obtain ⟨θ₀, h⟩ := hne
    apply h
    rw [cosPoly_eq_eval]
    change Q.eval _ = 0
    rw [hQ0, Polynomial.eval_zero]
  -- a point of `(−1, 0)` that is not a root of `Q`
  have hinf : (Set.Ioo (-1 : ℝ) 0).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨x, hx, hxr⟩ := hinf.exists_notMem_finset Q.roots.toFinset
  have hQx : Q.eval x ≠ 0 := by
    intro h0
    exact hxr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr h0))
  refine ⟨Real.arccos x, ?_⟩
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have hval : cosPoly b N (Real.arccos x) = Q.eval x := by rw [cosPoly_eq_eval, hcos]
  have hpos : 0 < cosPoly b N (Real.arccos x) :=
    lt_of_le_of_ne (hP _) (fun h => hQx (by rw [← hval, h]))
  rw [hcos]
  exact mul_neg_of_neg_of_pos hx.2 hpos

/-- **The Fejér barrier for coupled contraction.** No conjugation-symmetric polar configuration
with positive-definite vertical sections has as its leading line the lifted divisor of a deepest
quartet of multiplicity `m > 0` under a harmonic coupling with nonnegative cosine polynomial
`P ≢ 0`: the leading-line sum would be `2m cos(γt) P(γt)`, which is negative somewhere. -/
theorem not_removes_lifted_divisor {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σmax γ m : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax) (hγ : γ ≠ 0) (hm : 0 < m)
    {b : ℕ → ℝ} {N : ℕ} (hP : ∀ θ, 0 ≤ cosPoly b N θ) (hne : ∃ θ₀, cosPoly b N θ₀ ≠ 0)
    (hlead : ∀ t, leadingSum S c σmax t = 2 * m * Real.cos (γ * t) * cosPoly b N (γ * t)) :
    False := by
  obtain ⟨θ, hθ⟩ := exists_cos_mul_neg hP hne
  have hτ : 0 < 2 * π / |γ| := div_pos Real.two_pi_pos (abs_pos.mpr hγ)
  have hper : ∀ t, leadingSum S c σmax (t + 2 * π / |γ|) = leadingSum S c σmax t := by
    intro t
    have hshift : γ * (t + 2 * π / |γ|) = γ * t + (if 0 ≤ γ then 1 else -1) * (2 * π) := by
      split_ifs with h
      · rw [abs_of_nonneg h]; field_simp
      · rw [abs_of_neg (lt_of_not_ge h)]; field_simp
    have hcp : ∀ (x : ℝ) (e : ℤ), cosPoly b N (x + e * (2 * π)) = cosPoly b N x := by
      intro x e
      rw [cosPoly, cosPoly]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k : ℝ) * (x + e * (2 * π)) = k * x + ((k * e : ℤ) : ℝ) * (2 * π) by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
    rw [hlead, hlead, hshift]
    split_ifs
    · have := hcp (γ * t) 1
      simp only [Int.cast_one, one_mul] at this
      rw [one_mul, this, Real.cos_add_two_pi]
    · have := hcp (γ * t) (-1)
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at this
      rw [neg_one_mul, this, show γ * t + -(2 * π) = γ * t - 2 * π by ring, Real.cos_sub_two_pi]
  have hnn := leadingSum_nonneg_of_periodic hS_conj hc_conj hS_re hpd hmax hτ hper (θ / γ)
  rw [hlead, show γ * (θ / γ) = θ by field_simp] at hnn
  have : 2 * m * (Real.cos θ * cosPoly b N θ) < 0 := mul_neg_of_pos_of_neg (by linarith) hθ
  linarith

end GaloisForLFunctions.ArithmeticPolarization
