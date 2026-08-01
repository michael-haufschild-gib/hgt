import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The diagonal anti-Pick identity

For a finite node family with positive weights, the shift-variable ratio `q = N / D` of two Cauchy
transforms has an exact imaginary-part identity: after symmetrizing the double sum, every summand
carries the factor `(r_j - r_k)(t_j - t_k)`, which is nonnegative exactly when the ratio family is
monotone in the node.

The identity is algebra, not analysis.  Its two ingredients are the imaginary part of a single
mixed term — which carries the antisymmetric factor `t_k - t_j` — and the symmetrization of a double
sum over a finite index set.
-/

namespace RHTower

open Finset

/-- Symmetrizing a double sum over one finite index set. -/
theorem sum_sum_add_swap {ι : Type*} (s : Finset ι) (f : ι → ι → ℝ) :
    ∑ j ∈ s, ∑ k ∈ s, (f j k + f k j) = 2 * ∑ j ∈ s, ∑ k ∈ s, f j k := by
  have hswap : ∑ j ∈ s, ∑ k ∈ s, f k j = ∑ j ∈ s, ∑ k ∈ s, f j k :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- **The mixed term's imaginary part.**  The imaginary part of a product of a Cauchy factor with
the conjugate of another carries the antisymmetric node difference. -/
theorem im_cauchy_mul_conj {t s : ℝ} {z : ℂ}
    (ht : ((t : ℂ) - z) ≠ 0) (hs : ((s : ℂ) - z) ≠ 0) :
    ((1 / ((t : ℂ) - z)) * (starRingEnd ℂ) (1 / ((s : ℂ) - z))).im
      = z.im * (s - t) / (Complex.normSq ((t : ℂ) - z) * Complex.normSq ((s : ℂ) - z)) := by
  have hnt : Complex.normSq ((t : ℂ) - z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr ht)
  have hns : Complex.normSq ((s : ℂ) - z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hs)
  rw [map_div₀, map_one, div_mul_div_comm, one_mul, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  field_simp
  ring

/-- **`(1)`, the diagonal anti-Pick identity.**  Symmetrized, the imaginary part of the ratio's
numerator against the conjugate denominator is a double sum whose every summand carries
`(r_j - r_k)(t_j - t_k)` with a leading minus sign. -/
theorem im_antiPick_sum {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) (z : ℂ) :
    ∑ j ∈ s, ∑ k ∈ s,
        w j * r j * w k *
          (z.im * (t k - t j) /
            (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z)))
      = -(z.im / 2) * ∑ j ∈ s, ∑ k ∈ s,
          w j * w k * (r j - r k) * (t j - t k) /
            (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z)) := by
  classical
  set F : ι → ι → ℝ := fun j k =>
    w j * r j * w k *
      (z.im * (t k - t j) /
        (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z))) with hF
  have hsym := sum_sum_add_swap s F
  have hterm : ∀ j ∈ s, ∀ k ∈ s, F j k + F k j
      = -z.im * (w j * w k * (r j - r k) * (t j - t k) /
          (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z))) := by
    intro j _ k _
    simp only [hF]
    field_simp
    ring
  have hrw : ∑ j ∈ s, ∑ k ∈ s, (F j k + F k j)
      = ∑ j ∈ s, ∑ k ∈ s, -z.im * (w j * w k * (r j - r k) * (t j - t k) /
          (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z))) :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hterm j hj k hk
  rw [hrw] at hsym
  have hconst : ∑ j ∈ s, ∑ k ∈ s,
      -z.im * (w j * w k * (r j - r k) * (t j - t k) /
        (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z)))
      = -z.im * ∑ j ∈ s, ∑ k ∈ s,
        w j * w k * (r j - r k) * (t j - t k) /
          (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hconst] at hsym
  linarith [hsym]

/-! ## The denominator never vanishes

The ratio `q = N / D` is well posed above the real axis because `D` is a positive combination of
Cauchy kernels, each of which has positive imaginary part there.  This is the setup fact the whole
argument rests on. -/

/-- A single Cauchy term's imaginary part above the real axis. -/
theorem im_cauchyTerm (w t : ℝ) (z : ℂ) :
    ((w : ℂ) / ((t : ℂ) - z)).im = w * z.im / Complex.normSq ((t : ℂ) - z) := by
  rw [Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring

theorem sub_ofReal_ne_zero_of_im_ne_zero {t : ℝ} {z : ℂ} (hz : z.im ≠ 0) : ((t : ℂ) - z) ≠ 0 := by
  intro hc
  have him : ((t : ℂ) - z).im = 0 := by rw [hc]; simp
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_eq_zero] at him
  exact hz him

theorem sub_ofReal_ne_zero_of_im_pos {t : ℝ} {z : ℂ} (hz : 0 < z.im) : ((t : ℂ) - z) ≠ 0 :=
  sub_ofReal_ne_zero_of_im_ne_zero (ne_of_gt hz)

/-- **The denominator is Herglotz.**  A positive combination of Cauchy kernels has strictly positive
imaginary part above the real axis. -/
theorem im_cauchySum_pos {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    0 < (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z)).im := by
  rw [Complex.im_sum]
  refine Finset.sum_pos (fun j hj => ?_) hne
  rw [im_cauchyTerm]
  exact div_pos (mul_pos (hw j hj) hz)
    (Complex.normSq_pos.mpr (sub_ofReal_ne_zero_of_im_pos hz))

/-- **Hence it never vanishes**, so the shift ratio is well posed above the real axis. -/
theorem cauchySum_ne_zero {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z)) ≠ 0 := by
  intro hc
  have := im_cauchySum_pos s w t hz hw hne
  rw [hc] at this
  simp at this

/-- Below the real axis the same combination has strictly negative imaginary part. -/
theorem im_cauchySum_neg {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {z : ℂ} (hz : z.im < 0)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z)).im < 0 := by
  rw [Complex.im_sum]
  refine Finset.sum_neg (fun j hj => ?_) hne
  rw [im_cauchyTerm]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hw j hj) hz)
    (Complex.normSq_pos.mpr (sub_ofReal_ne_zero_of_im_ne_zero (ne_of_lt hz)))

/-- **`D` has no nonreal zeros.**  Off the real axis the imaginary part of a positive combination of
Cauchy kernels has the sign of `Im z`, so it cannot vanish.  This is the half of the zero-structure
claim behind `(3)` that needs no node ordering. -/
theorem cauchySum_ne_zero_of_im_ne_zero {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z)) ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · intro hc
    have := im_cauchySum_neg s w t hneg hw hne
    rw [hc] at this
    simp at this
  · exact cauchySum_ne_zero s w t hpos hw hne

/-! ## Strict monotonicity off the nodes

On the real axis away from the nodes, a positive Cauchy combination has derivative
`sum w_j/(t_j - x)^2 > 0`.  So it is strictly increasing on every interval free of nodes, which is
the *uniqueness* half of "one real zero between consecutive nodes": a strictly monotone function
takes each value at most once. -/

/-- The real derivative of a single Cauchy term off its node. -/
theorem hasDerivAt_cauchyTermReal (w t x : ℝ) (h : t - x ≠ 0) :
    HasDerivAt (fun y : ℝ => w / (t - y)) (w / (t - x) ^ 2) x := by
  have hsub : HasDerivAt (fun y : ℝ => t - y) (-1) x := by
    simpa using HasDerivAt.const_sub t (hasDerivAt_id x)
  have hdiv := (hasDerivAt_const x w).div hsub h
  have hval : (0 * (t - x) - w * -1) / (t - x) ^ 2 = w / (t - x) ^ 2 := by ring
  rwa [hval] at hdiv

/-- The real derivative of the full combination off every node. -/
theorem hasDerivAt_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) :
    HasDerivAt (fun y : ℝ => ∑ j ∈ s, w j / (t j - y))
      (∑ j ∈ s, w j / (t j - x) ^ 2) x := by
  have h2 := HasDerivAt.sum fun j hj => hasDerivAt_cauchyTermReal (w j) (t j) x (h j hj)
  have hfun : (∑ i ∈ s, fun y : ℝ => w i / (t i - y))
      = fun y : ℝ => ∑ j ∈ s, w j / (t j - y) := by
    funext y
    simp [Finset.sum_apply]
  rwa [hfun] at h2

/-- **The derivative is strictly positive off the nodes.** -/
theorem deriv_cauchySumReal_pos {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    0 < ∑ j ∈ s, w j / (t j - x) ^ 2 := by
  refine Finset.sum_pos (fun j hj => ?_) hne
  have hne' := h j hj
  exact div_pos (hw j hj) (by positivity)

/-- **Uniqueness of the zero on a node-free interval.**  Strict monotonicity forces at most one
zero, which is the "one" of `(3)`'s interlacing claim; existence is the sign change at the two
node endpoints. -/
theorem injOn_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {S : Set ℝ}
    (hS : Convex ℝ S) (hnode : ∀ x ∈ S, ∀ j ∈ s, t j - x ≠ 0)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    Set.InjOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S := by
  have hcont : ContinuousOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S := fun x hx =>
    ((hasDerivAt_cauchySumReal s w t x (hnode x hx)).continuousAt).continuousWithinAt
  refine (StrictMonoOn.injOn ?_)
  refine strictMonoOn_of_deriv_pos hS hcont fun x hx => ?_
  have hxS : x ∈ S := interior_subset hx
  rw [(hasDerivAt_cauchySumReal s w t x (hnode x hxS)).deriv]
  exact deriv_cauchySumReal_pos s w t x (hnode x hxS) hw hne

/-- Continuity on a node-free set. -/
theorem continuousOn_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {S : Set ℝ}
    (hnode : ∀ x ∈ S, ∀ j ∈ s, t j - x ≠ 0) :
    ContinuousOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S := fun x hx =>
  ((hasDerivAt_cauchySumReal s w t x (hnode x hx)).continuousAt).continuousWithinAt

/-- **Existence of the zero from a sign change.**  On a node-free interval whose endpoints carry
opposite signs, the combination vanishes somewhere inside.  This is the intermediate-value half of
the interlacing; the analytic input is the sign change itself, which comes from the one-sided
blow-up at the two bounding nodes. -/
theorem exists_zero_of_sign_change {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hnode : ∀ x ∈ Set.Icc a b, ∀ j ∈ s, t j - x ≠ 0)
    (hA : (∑ j ∈ s, w j / (t j - a)) < 0) (hB : 0 < ∑ j ∈ s, w j / (t j - b)) :
    ∃ c ∈ Set.Ioo a b, (∑ j ∈ s, w j / (t j - c)) = 0 := by
  have hcont := continuousOn_cauchySumReal s w t hnode
  have hmem : (0 : ℝ) ∈ Set.Ioo (∑ j ∈ s, w j / (t j - a)) (∑ j ∈ s, w j / (t j - b)) :=
    ⟨hA, hB⟩
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Ioo hab hcont hmem
  exact ⟨c, hc, hcv⟩

/-- **`(3)`'s interlacing.**  On a node-free interval with a sign change there is exactly one zero:
existence by the intermediate value theorem, uniqueness by strict monotonicity. -/
theorem existsUnique_zero_of_sign_change {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hnode : ∀ x ∈ Set.Icc a b, ∀ j ∈ s, t j - x ≠ 0)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty)
    (hA : (∑ j ∈ s, w j / (t j - a)) < 0) (hB : 0 < ∑ j ∈ s, w j / (t j - b)) :
    ∃! c : ℝ, c ∈ Set.Ioo a b ∧ (∑ j ∈ s, w j / (t j - c)) = 0 := by
  obtain ⟨c, hc, hcv⟩ := exists_zero_of_sign_change s w t hab hnode hA hB
  refine ⟨c, ⟨hc, hcv⟩, fun d hd => ?_⟩
  have hsub : Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self
  have hinj := injOn_cauchySumReal s w t (convex_Ioo a b)
    (fun x hx => hnode x (hsub hx)) hw hne
  exact hinj hd.1 hc (hd.2.trans hcv.symm)

/-! ## The one-sided blow-up

Approaching a node from the right, its own term runs to `-infinity`; from the left, to `+infinity`.
Everything else stays continuous there, so the combination inherits the blow-up.  This is the
analytic input that produces the sign change the interlacing consumes. -/

/-- A Cauchy term runs to `-infinity` approaching its node from the right. -/
theorem tendsto_cauchyTerm_atBot {w t : ℝ} (hw : 0 < w) :
    Filter.Tendsto (fun x : ℝ => w / (t - x)) (nhdsWithin t (Set.Ioi t)) Filter.atBot := by
  have hsub : Filter.Tendsto (fun x : ℝ => t - x) (nhdsWithin t (Set.Ioi t))
      (nhdsWithin 0 (Set.Iio 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Filter.Tendsto (fun x : ℝ => t - x) (nhds t) (nhds (t - t)) :=
        (continuous_const.sub continuous_id).tendsto t
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hinv := tendsto_inv_nhdsLT_zero.comp hsub
  have := hinv.const_mul_atBot hw
  simpa [div_eq_mul_inv] using this

/-- A Cauchy term runs to `+infinity` approaching its node from the left. -/
theorem tendsto_cauchyTerm_atTop {w t : ℝ} (hw : 0 < w) :
    Filter.Tendsto (fun x : ℝ => w / (t - x)) (nhdsWithin t (Set.Iio t)) Filter.atTop := by
  have hsub : Filter.Tendsto (fun x : ℝ => t - x) (nhdsWithin t (Set.Iio t))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Filter.Tendsto (fun x : ℝ => t - x) (nhds t) (nhds (t - t)) :=
        (continuous_const.sub continuous_id).tendsto t
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hinv := tendsto_inv_nhdsGT_zero.comp hsub
  have := hinv.const_mul_atTop hw
  simpa [div_eq_mul_inv] using this

/-! ## The constant term of `(3)`

The partial-fraction form `q = ell - sum nu_k/(sigma_k - z)` names `ell` as the weighted mean of the
ratios.  What singles that value out is that subtracting it makes the numerator a Cauchy transform
of **zero total weight** — so `q - ell` decays one order faster and no further constant survives. -/

/-- The weighted mean of the ratios, the constant term of `(3)`. -/
noncomputable def suzukiShiftEll {ι : Type*} (s : Finset ι) (w r : ι → ℝ) : ℝ :=
  (∑ j ∈ s, w j * r j) / (∑ j ∈ s, w j)

/-- **`ell` is exactly the value that zeroes the total weight.** -/
theorem sum_weight_sub_ell_eq_zero {ι : Type*} (s : Finset ι) (w r : ι → ℝ)
    (hmass : (∑ j ∈ s, w j) ≠ 0) :
    ∑ j ∈ s, w j * (r j - suzukiShiftEll s w r) = 0 := by
  have hexp : ∑ j ∈ s, w j * (r j - suzukiShiftEll s w r)
      = (∑ j ∈ s, w j * r j) - suzukiShiftEll s w r * ∑ j ∈ s, w j := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, suzukiShiftEll, div_mul_cancel₀ _ hmass, sub_self]

/-- Subtracting the constant term combines the two Cauchy transforms into one. -/
theorem numerator_sub_ell_mul {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) (ell : ℝ) (z : ℂ) :
    (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z))
        - (ell : ℂ) * ∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z)
      = ∑ j ∈ s, ((w j * (r j - ell) : ℝ) : ℂ) / ((t j : ℂ) - z) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **The constant term is the value at infinity.**  Above the real axis, `q - ell` is the Cauchy
transform of the zero-total-weight family `w_j (r_j - ell)`, divided by `D`.  That the numerator's
weights sum to zero is what makes `ell` the right constant. -/
theorem ratio_sub_ell_eq {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) (ell : ℝ) :
    (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z))
          / (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z)) - (ell : ℂ)
      = (∑ j ∈ s, ((w j * (r j - ell) : ℝ) : ℂ) / ((t j : ℂ) - z))
          / (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z)) := by
  have hD := cauchySum_ne_zero s w t hz hw hne
  rw [div_sub' hD, ← numerator_sub_ell_mul s w r t ell z]
  ring

/-! ## Residue extraction

At a simple zero of the denominator the ratio has a simple pole, and its residue is
`N(sigma)/D'(sigma)`.  No contour is needed to see this: the residue is the limit of
`(z - sigma) q(z)`, and dividing by `z - sigma` turns the denominator into its own difference
quotient at `sigma`, which converges to `D'(sigma)` because `D(sigma) = 0`. -/

/-- **The residue at a simple zero of the denominator.**  `lim (z - sigma) N(z)/D(z)` is
`N(sigma)/D'(sigma)`.  This is the extraction step of `(3)`: it names the coefficient `nu_k` of the
pole at `sigma_k`. -/
theorem tendsto_residue_of_simple_zero {D N : ℂ → ℂ} {σ D' : ℂ}
    (hD : HasDerivAt D D' σ) (hD0 : D σ = 0) (hD'ne : D' ≠ 0) (hN : ContinuousAt N σ) :
    Filter.Tendsto (fun z => (z - σ) * (N z / D z)) (nhdsWithin σ {σ}ᶜ)
      (nhds (N σ / D')) := by
  have hslope : Filter.Tendsto (slope D σ) (nhdsWithin σ ({σ}ᶜ)) (nhds D') :=
    hasDerivAt_iff_tendsto_slope.mp hD
  have hNlim : Filter.Tendsto N (nhdsWithin σ ({σ}ᶜ)) (nhds (N σ)) :=
    Filter.Tendsto.mono_left hN nhdsWithin_le_nhds
  have hdiv := hNlim.div hslope hD'ne
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzne : z - σ ≠ 0 := sub_ne_zero.mpr hz
  rw [slope_def_field, hD0, sub_zero, div_div_eq_mul_div, div_div_eq_mul_div]
  ring

/-! ## From the identity to the sign

Monotone likelihood is exactly nonnegativity of every product `(r_j - r_k)(t_j - t_k)`.  With
nonnegative weights the symmetrized sum is then nonnegative, and the leading minus sign of `(1)`
turns that into the anti-Herglotz sign `(2)`. -/

/-- Under monotone likelihood and nonnegative weights the symmetrized double sum is nonnegative. -/
theorem antiPick_sum_nonneg {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) (z : ℂ)
    (hw : ∀ j ∈ s, 0 ≤ w j)
    (hmono : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ (r j - r k) * (t j - t k)) :
    0 ≤ ∑ j ∈ s, ∑ k ∈ s,
        w j * w k * (r j - r k) * (t j - t k) /
          (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z)) := by
  refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
  refine div_nonneg ?_ (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  have hnum : 0 ≤ (r j - r k) * (t j - t k) := hmono j hj k hk
  have hprod : w j * w k * (r j - r k) * (t j - t k)
      = (w j * w k) * ((r j - r k) * (t j - t k)) := by ring
  rw [hprod]
  exact mul_nonneg (mul_nonneg (hw j hj) (hw k hk)) hnum

/-- **`(2)`, summed form.**  Above the real axis the symmetrized imaginary-part sum is nonpositive. -/
theorem im_antiPick_nonpos {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j ∈ s, 0 ≤ w j)
    (hmono : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ (r j - r k) * (t j - t k)) :
    ∑ j ∈ s, ∑ k ∈ s,
        w j * r j * w k *
          (z.im * (t k - t j) /
            (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z))) ≤ 0 := by
  rw [im_antiPick_sum s w r t z]
  have hS := antiPick_sum_nonneg s w r t z hw hmono
  nlinarith [hS, hz]

/-- The imaginary part of a ratio is the imaginary part against the conjugate, scaled. -/
theorem im_div_eq_im_mul_conj (N D : ℂ) :
    (N / D).im = (N * (starRingEnd ℂ) D).im / Complex.normSq D := by
  rw [Complex.div_im, Complex.mul_im]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

/-- **`(2)`.**  A ratio whose numerator against the conjugate denominator has nonpositive imaginary
part is anti-Herglotz. -/
theorem im_ratio_nonpos_of_im_mul_conj_nonpos {N D : ℂ}
    (h : (N * (starRingEnd ℂ) D).im ≤ 0) : (N / D).im ≤ 0 := by
  rw [im_div_eq_im_mul_conj]
  exact div_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg _)

/-! ## The residue sign of `(3)`

The partial-fraction form `q = ell - sum nu_k/(sigma_k - z)` carries one piece of content beyond its
algebra: the coefficients are nonnegative.  That sign is forced pointwise, by evaluating a single
pole term on the vertical line above its own pole — no global theory is needed to see it. -/

/-- The imaginary part of a pole term directly above its pole. -/
theorem im_poleTerm (ν σ y : ℝ) :
    (-(ν : ℂ) / ((σ : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I))).im = -ν / y := by
  have hσ : ((σ : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I)) = -((y : ℂ) * Complex.I) := by ring
  rw [hσ, Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  by_cases hy : y = 0
  · simp [hy]
  · field_simp
    ring

/-- **`(3)`, the residue sign.**  A pole term is anti-Herglotz on the line above its pole exactly
when its coefficient is nonnegative.  This is the content `nu_k >= 0` of the partial-fraction
form. -/
theorem poleCoeff_nonneg_iff_im_nonpos {ν σ : ℝ} :
    (∀ y : ℝ, 0 < y →
      (-(ν : ℂ) / ((σ : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I))).im ≤ 0) ↔ 0 ≤ ν := by
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [im_poleTerm] at h1
    simpa using h1
  · intro hν y hy
    rw [im_poleTerm]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hy.le

end RHTower
