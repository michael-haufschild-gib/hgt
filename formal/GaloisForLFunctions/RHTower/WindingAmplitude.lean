/-
Vertical bound for the imaginary part of digamma, and the winding amplitude face.

The digamma recurrence turns `Im ψ(σ+it)` into the limit of the positive partial sums
`Σ t/((σ+n)²+t²)`, each bounded by the banked arctan comparison; the far-field anchor
`Im ψ(σ+it+N) → 0` follows from the Gauss-limit shift bound because `ψ(N+1)` is real.  Hence
`0 ≤ Im ψ(σ+it) ≤ 1/t + π/2`.  Consequently the winding amplitude of the archimedean envelope
obeys `|Im w(u)| ≤ 3/u + π/4`: the modulus-variation face of the resonance-moment cancellation
is an explicit function of the height alone.
-/
import GaloisForLFunctions.RHTower.WindingFloor

open Complex Filter Metric

namespace RHTower

/-- Imaginary part of the half point. -/
theorem im_div_two (z : ℂ) : (z / 2).im = z.im / 2 := by
  rw [Complex.div_im]
  simp
  ring

/-- The shifted vertical summand in closed form: the imaginary mirror of `re_inv_shift`. -/
theorem im_inv_shift (σ t : ℝ) (n : ℕ) :
    (((σ : ℂ) + (t : ℂ) * Complex.I + n)⁻¹).im
      = -(t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ))) := by
  have hz : (σ : ℂ) + (t : ℂ) * Complex.I + n
      = ((σ + n : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hz, Complex.inv_im, Complex.normSq_add_mul_I]
  simp [neg_div]

/-- `ψ(N+1)` is real. -/
theorem im_digamma_natCast_add_one (N : ℕ) :
    (Complex.digamma ((N : ℂ) + 1)).im = 0 := by
  rw [digamma_natCast_add_one, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
    neg_zero, zero_add, Complex.im_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) from by push_cast; ring, one_div,
    Complex.inv_im]
  simp

/-- Far-field anchor for the imaginary part: `Im ψ(σ+it+N) → 0`, because the digamma shift
bound compares `ψ(σ+it+N)` to the real value `ψ(N+1)` with error `O(1/N)`. -/
theorem im_digamma_vertical_anchor_tendsto (σ t : ℝ) :
    Tendsto (fun N : ℕ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (N : ℂ))).im)
      atTop (nhds 0) := by
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hw
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖w - 1‖))
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-σ + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * ‖w - 1‖)]
    with N hN1 hσN hthr
  have hwre : w.re = σ := by
    rw [hw]
    simp
  have hwN : 0 < (w + (N : ℂ)).re := by
    rw [Complex.add_re, hwre, Complex.natCast_re]
    linarith
  have hb := digamma_shift_diff_bound hN1 hwN hthr
  calc ‖(Complex.digamma (w + (N : ℂ))).im‖
      = |(Complex.digamma (w + (N : ℂ)) - Complex.digamma ((N : ℂ) + 1)).im| := by
        rw [Complex.sub_im, im_digamma_natCast_add_one, sub_zero, Real.norm_eq_abs]
    _ ≤ ‖Complex.digamma (w + (N : ℂ)) - Complex.digamma ((N : ℂ) + 1)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ 2 * ‖w - 1‖ / (N : ℝ) := hb

/-- **Vertical bound for `Im ψ`.**  For `σ ≥ 0`, `t > 0`:
`0 ≤ Im ψ(σ+it) ≤ 1/t + π/2`.  The recurrence writes `Im ψ(σ+it)` as the limit of the
positive partial sums `Σ t/((σ+n)²+t²)`, uniformly bounded by the arctan comparison. -/
theorem im_digamma_vertical_bound {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    0 ≤ (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ∧
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ≤ 1 / t + Real.pi / 2 := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hz : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hc
    have him := congrArg Complex.im hc
    rw [hz_def] at him
    simp at him
    linarith
  have hS_eq : ∀ N : ℕ, (Complex.digamma z).im - (Complex.digamma (z + (N : ℂ))).im =
      ∑ n ∈ Finset.range N, t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    intro N
    rw [digamma_apply_add_nat z hz N, Complex.add_im, Complex.im_sum]
    rw [show ∑ n ∈ Finset.range N, ((z + (n : ℂ))⁻¹).im =
      ∑ n ∈ Finset.range N, -(t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ))) from
      Finset.sum_congr rfl fun n _ => by rw [hz_def]; exact im_inv_shift σ t n]
    rw [Finset.sum_neg_distrib]
    ring
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ)))
      atTop (nhds ((Complex.digamma z).im)) := by
    have h1 : Tendsto (fun N : ℕ =>
        (Complex.digamma z).im - (Complex.digamma (z + (N : ℂ))).im)
        atTop (nhds ((Complex.digamma z).im - 0)) :=
      tendsto_const_nhds.sub (im_digamma_vertical_anchor_tendsto σ t)
    rw [sub_zero] at h1
    exact h1.congr hS_eq
  have hS_nonneg : ∀ N : ℕ, 0 ≤ ∑ n ∈ Finset.range N, t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    intro N
    refine Finset.sum_nonneg fun n _ => ?_
    have hd : 0 < (σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ) := by positivity
    positivity
  have hS_le : ∀ N : ℕ, (∑ n ∈ Finset.range N, t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ))) ≤
      1 / t + Real.pi / 2 := by
    intro N
    have h1 : (∑ n ∈ Finset.range N, t / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ))) =
        t * ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h1]
    have h2 := sum_inv_sq_add_le hσ ht N
    have h3 : t * (∑ n ∈ Finset.range N, 1 / ((σ + n) ^ (2 : ℕ) + t ^ (2 : ℕ))) ≤
        t * (1 / t ^ (2 : ℕ) + Real.pi / (2 * t)) :=
      mul_le_mul_of_nonneg_left h2 ht.le
    have h4 : t * (1 / t ^ (2 : ℕ) + Real.pi / (2 * t)) = 1 / t + Real.pi / 2 := by
      field_simp
    linarith
  exact ⟨ge_of_tendsto' htend hS_nonneg, le_of_tendsto' htend hS_le⟩

/-- **Explicit winding-amplitude bound.**  The modulus-variation datum of the archimedean
envelope satisfies `|Im w(u)| ≤ 3/u + π/4` at every positive height: the rational part
contributes at most `2/u` and the digamma part at most `(2/u + π/2)/2`. -/
theorem archWinding_im_abs_le {u : ℝ} (hu : 0 < u) :
    |(archWinding u).im| ≤ 3 / u + Real.pi / 4 := by
  have h1 : 2 * linePt u - 1 = ((2 * u : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have h2 : linePt u * (linePt u - 1) = ((-(1 / 4 + u ^ (2 : ℕ)) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    linear_combination ((u : ℂ)) ^ (2 : ℕ) * Complex.I_sq
  have h3 : ((2 * u : ℝ) : ℂ) * Complex.I / ((-(1 / 4 + u ^ (2 : ℕ)) : ℝ) : ℂ) =
      ((2 * u / (-(1 / 4 + u ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, div_mul_eq_mul_div]
  have hpolyim : ((2 * linePt u - 1) / (linePt u * (linePt u - 1))).im =
      -(2 * u / (1 / 4 + u ^ (2 : ℕ))) := by
    rw [h1, h2, h3, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [div_neg]
    ring
  have him_eq : (archWinding u).im = -(2 * u / (1 / 4 + u ^ (2 : ℕ))) +
      (Complex.digamma ((linePt u) / 2)).im / 2 := by
    rw [archWinding_eq u, Complex.add_im, hpolyim, Complex.sub_im, im_div_two,
      im_div_two, Complex.ofReal_im]
    ring
  have harg : (linePt u) / 2 = ((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have hψ := im_digamma_vertical_bound (σ := 1 / 4) (t := u / 2) (by norm_num) (by positivity)
  rw [← harg] at hψ
  have hrat_le : 2 * u / (1 / 4 + u ^ (2 : ℕ)) ≤ 2 / u := by
    rw [div_le_div_iff₀ (by positivity) hu]
    nlinarith
  have hrat_nonneg : 0 ≤ 2 * u / (1 / 4 + u ^ (2 : ℕ)) := by positivity
  have hhalf : 1 / (u / 2) = 2 / u := one_div_div u 2
  rw [him_eq]
  calc |(-(2 * u / (1 / 4 + u ^ (2 : ℕ))) + (Complex.digamma ((linePt u) / 2)).im / 2)|
      ≤ |(-(2 * u / (1 / 4 + u ^ (2 : ℕ))))| + |(Complex.digamma ((linePt u) / 2)).im / 2| :=
        abs_add_le _ _
    _ = 2 * u / (1 / 4 + u ^ (2 : ℕ)) + (Complex.digamma ((linePt u) / 2)).im / 2 := by
        rw [abs_neg, abs_of_nonneg hrat_nonneg, abs_div,
          abs_of_nonneg hψ.1, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2 / u + (1 / (u / 2) + Real.pi / 2) / 2 := by
        have := hψ.2
        gcongr
    _ = 3 / u + Real.pi / 4 := by
        rw [hhalf]
        ring

end RHTower
