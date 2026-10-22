import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import GaloisForLFunctions.HTGeometry.LinearPartialFractions

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
`sum w_j/(t_j - x)^(2 : ℕ) > 0`.  So it is strictly increasing on every interval free of nodes, which is
the *uniqueness* half of "one real zero between consecutive nodes": a strictly monotone function
takes each value at most once. -/

/-- The real derivative of a single Cauchy term off its node. -/
theorem hasDerivAt_cauchyTermReal (w t x : ℝ) (h : t - x ≠ 0) :
    HasDerivAt (fun y : ℝ => w / (t - y)) (w / (t - x) ^ (2 : ℕ)) x := by
  have hsub : HasDerivAt (fun y : ℝ => t - y) (-1) x := by
    simpa using HasDerivAt.const_sub t (hasDerivAt_id x)
  have hdiv := (hasDerivAt_const x w).div hsub h
  have hval : (0 * (t - x) - w * -1) / (t - x) ^ (2 : ℕ) = w / (t - x) ^ (2 : ℕ) := by ring
  rwa [hval] at hdiv

/-- The real derivative of the full combination off every node. -/
theorem hasDerivAt_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) :
    HasDerivAt (fun y : ℝ => ∑ j ∈ s, w j / (t j - y))
      (∑ j ∈ s, w j / (t j - x) ^ (2 : ℕ)) x := by
  have h2 := HasDerivAt.sum fun j hj => hasDerivAt_cauchyTermReal (w j) (t j) x (h j hj)
  have hfun : (∑ i ∈ s, fun y : ℝ => w i / (t i - y))
      = fun y : ℝ => ∑ j ∈ s, w j / (t j - y) := by
    funext y
    simp [Finset.sum_apply]
  rwa [hfun] at h2

/-- **The derivative is strictly positive off the nodes.** -/
theorem deriv_cauchySumReal_pos {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    0 < ∑ j ∈ s, w j / (t j - x) ^ (2 : ℕ) := by
  refine Finset.sum_pos (fun j hj => ?_) hne
  have hne' := h j hj
  exact div_pos (hw j hj) (by positivity)

/-- **Uniqueness of the zero on a node-free interval.**  Strict monotonicity forces at most one
zero, which is the "one" of `(3)`'s interlacing claim; existence is the sign change at the two
node endpoints. -/
theorem strictMonoOn_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {S : Set ℝ}
    (hS : Convex ℝ S) (hnode : ∀ x ∈ S, ∀ j ∈ s, t j - x ≠ 0)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    StrictMonoOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S := by
  have hcont : ContinuousOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S := fun x hx =>
    ((hasDerivAt_cauchySumReal s w t x (hnode x hx)).continuousAt).continuousWithinAt
  refine strictMonoOn_of_deriv_pos hS hcont fun x hx => ?_
  have hxS : x ∈ S := interior_subset hx
  rw [(hasDerivAt_cauchySumReal s w t x (hnode x hxS)).deriv]
  exact deriv_cauchySumReal_pos s w t x (hnode x hxS) hw hne

theorem injOn_cauchySumReal {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {S : Set ℝ}
    (hS : Convex ℝ S) (hnode : ∀ x ∈ S, ∀ j ∈ s, t j - x ≠ 0)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    Set.InjOn (fun y : ℝ => ∑ j ∈ s, w j / (t j - y)) S :=
  (strictMonoOn_cauchySumReal s w t hS hnode hw hne).injOn

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

/-! ## The gap zero

Between two consecutive nodes the combination blows down at the left node, blows up at the right
node, and is strictly increasing in between.  So it has exactly one zero there.  This is what turns
the node list into a root list: one root per gap, each in its own interval, hence all distinct. -/

open Filter Set in
/-- **The combination blows down at a node from the right.**  Its own term runs to `-infinity` and
every other term stays continuous there, so the sum inherits the blow-up. -/
theorem tendsto_cauchySumReal_atBot {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {i : ι} (hi : i ∈ s) (hw : 0 < w i) (hnode : ∀ j ∈ s.erase i, t j ≠ t i) :
    Tendsto (fun x : ℝ => ∑ j ∈ s, w j / (t j - x)) (nhdsWithin (t i) (Ioi (t i))) atBot := by
  have hsplit : (fun x : ℝ => ∑ j ∈ s, w j / (t j - x))
      = fun x : ℝ => w i / (t i - x) + ∑ j ∈ s.erase i, w j / (t j - x) := by
    funext x
    exact (Finset.add_sum_erase s (fun j => w j / (t j - x)) hi).symm
  rw [hsplit]
  have hrest : Tendsto (fun x : ℝ => ∑ j ∈ s.erase i, w j / (t j - x))
      (nhdsWithin (t i) (Ioi (t i))) (nhds (∑ j ∈ s.erase i, w j / (t j - t i))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hne : t j - t i ≠ 0 := sub_ne_zero_of_ne (hnode j hj)
    exact (tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) hne).mono_left
      nhdsWithin_le_nhds
  exact Tendsto.atBot_add (tendsto_cauchyTerm_atBot hw) hrest

open Filter Set in
/-- **The combination blows up at a node from the left.** -/
theorem tendsto_cauchySumReal_atTop {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {i : ι} (hi : i ∈ s) (hw : 0 < w i) (hnode : ∀ j ∈ s.erase i, t j ≠ t i) :
    Tendsto (fun x : ℝ => ∑ j ∈ s, w j / (t j - x)) (nhdsWithin (t i) (Iio (t i))) atTop := by
  have hsplit : (fun x : ℝ => ∑ j ∈ s, w j / (t j - x))
      = fun x : ℝ => w i / (t i - x) + ∑ j ∈ s.erase i, w j / (t j - x) := by
    funext x
    exact (Finset.add_sum_erase s (fun j => w j / (t j - x)) hi).symm
  rw [hsplit]
  have hrest : Tendsto (fun x : ℝ => ∑ j ∈ s.erase i, w j / (t j - x))
      (nhdsWithin (t i) (Iio (t i))) (nhds (∑ j ∈ s.erase i, w j / (t j - t i))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hne : t j - t i ≠ 0 := sub_ne_zero_of_ne (hnode j hj)
    exact (tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) hne).mono_left
      nhdsWithin_le_nhds
  exact Tendsto.atTop_add (tendsto_cauchyTerm_atTop hw) hrest

open Filter Set in
/-- Just to the right of a node the combination is negative. -/
theorem exists_mem_Ioo_cauchySumReal_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {i : ι} {b : ℝ} (hi : i ∈ s) (hw : 0 < w i) (hnode : ∀ j ∈ s.erase i, t j ≠ t i)
    (hb : t i < b) :
    ∃ a ∈ Ioo (t i) b, (∑ j ∈ s, w j / (t j - a)) < 0 := by
  have h1 : ∀ᶠ x in nhdsWithin (t i) (Ioi (t i)), (∑ j ∈ s, w j / (t j - x)) < 0 :=
    (tendsto_cauchySumReal_atBot s w t hi hw hnode).eventually (eventually_lt_atBot 0)
  have h2 : ∀ᶠ x in nhdsWithin (t i) (Ioi (t i)), x ∈ Ioo (t i) b :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT hb)
  obtain ⟨a, ha1, ha2⟩ := (h1.and h2).exists
  exact ⟨a, ha2, ha1⟩

open Filter Set in
/-- Just to the left of a node the combination is positive. -/
theorem exists_mem_Ioo_cauchySumReal_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {i : ι} {a : ℝ} (hi : i ∈ s) (hw : 0 < w i) (hnode : ∀ j ∈ s.erase i, t j ≠ t i)
    (ha : a < t i) :
    ∃ b ∈ Ioo a (t i), 0 < ∑ j ∈ s, w j / (t j - b) := by
  have h1 : ∀ᶠ x in nhdsWithin (t i) (Iio (t i)), 0 < ∑ j ∈ s, w j / (t j - x) :=
    (tendsto_cauchySumReal_atTop s w t hi hw hnode).eventually (eventually_gt_atTop 0)
  have h2 : ∀ᶠ x in nhdsWithin (t i) (Iio (t i)), x ∈ Ioo a (t i) :=
    eventually_mem_set.mpr (Ioo_mem_nhdsLT ha)
  obtain ⟨b, hb1, hb2⟩ := (h1.and h2).exists
  exact ⟨b, hb2, hb1⟩

open Set in
/-- **Exactly one zero in each node gap.**  If no node lies strictly between `t i` and `t k`, the
combination has a unique zero there: the blow-ups at the two ends give the sign change, and strict
monotonicity gives uniqueness. -/
theorem existsUnique_zero_in_gap {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {i k : ι} (hi : i ∈ s) (hk : k ∈ s) (hw : ∀ j ∈ s, 0 < w j) (hti : Set.InjOn t ↑s)
    (hlt : t i < t k) (hgap : ∀ j ∈ s, t j ∉ Ioo (t i) (t k)) :
    ∃! c : ℝ, c ∈ Ioo (t i) (t k) ∧ (∑ j ∈ s, w j / (t j - c)) = 0 := by
  have hne : s.Nonempty := ⟨i, hi⟩
  have hfree : ∀ x ∈ Ioo (t i) (t k), ∀ j ∈ s, t j - x ≠ 0 := by
    intro x hx j hj hc
    exact hgap j hj (sub_eq_zero.mp hc ▸ hx)
  have hmono := strictMonoOn_cauchySumReal s w t (convex_Ioo (t i) (t k)) hfree hw hne
  have hnodei : ∀ j ∈ s.erase i, t j ≠ t i := fun j hj heq =>
    Finset.ne_of_mem_erase hj (hti (Finset.mem_of_mem_erase hj) hi heq)
  have hnodek : ∀ j ∈ s.erase k, t j ≠ t k := fun j hj heq =>
    Finset.ne_of_mem_erase hj (hti (Finset.mem_of_mem_erase hj) hk heq)
  obtain ⟨a, hamem, haneg⟩ :=
    exists_mem_Ioo_cauchySumReal_neg s w t hi (hw i hi) hnodei hlt
  obtain ⟨b, hbmem, hbpos⟩ :=
    exists_mem_Ioo_cauchySumReal_pos s w t hk (hw k hk) hnodek hlt
  have hab : a < b := by
    rcases lt_trichotomy a b with h | h | h
    · exact h
    · rw [h] at haneg; linarith
    · have := hmono hbmem hamem h; simp only at this; linarith
  have hsub : Icc a b ⊆ Ioo (t i) (t k) := Icc_subset_Ioo hamem.1 hbmem.2
  obtain ⟨c, hcmem, hczero⟩ :=
    exists_zero_of_sign_change s w t hab.le (fun x hx => hfree x (hsub hx)) haneg hbpos
  refine ⟨c, ⟨Ioo_subset_Ioo hamem.1.le hbmem.2.le hcmem, hczero⟩, fun d hd => ?_⟩
  exact hmono.injOn hd.1 (Ioo_subset_Ioo hamem.1.le hbmem.2.le hcmem) (hd.2.trans hczero.symm)

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
  show N z / slope D σ z = (z - σ) * (N z / D z)
  rw [slope_def_field, hD0, sub_zero, div_div_eq_mul_div]
  ring

/-- A pole term's own residue is its coefficient, exactly and without a limit. -/
theorem residue_poleTerm (ν σ : ℂ) {z : ℂ} (hz : z ≠ σ) :
    (z - σ) * (-ν / (σ - z)) = ν := by
  have hzne : z - σ ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- **The coefficients of `(3)` are forced.**  If the ratio decomposes as a pole term at `sigma`
plus something continuous there, then that pole's coefficient must be the residue
`N(sigma)/D'(sigma)`.  So the decomposition, if it exists, has exactly the coefficients the
extraction names — and by `poleCoeff_nonneg_iff_im_nonpos` they are nonnegative. -/
theorem poleCoeff_eq_residue {D N rest : ℂ → ℂ} {σ D' ν : ℂ}
    (hD : HasDerivAt D D' σ) (hD0 : D σ = 0) (hD'ne : D' ≠ 0) (hN : ContinuousAt N σ)
    (hrest : ContinuousAt rest σ)
    (hdecomp : ∀ z, z ≠ σ → N z / D z = -ν / (σ - z) + rest z) :
    ν = N σ / D' := by
  have hres := tendsto_residue_of_simple_zero hD hD0 hD'ne hN
  have hsub : Filter.Tendsto (fun z : ℂ => z - σ) (nhdsWithin σ ({σ}ᶜ)) (nhds 0) := by
    have h : Filter.Tendsto (fun z : ℂ => z - σ) (nhds σ) (nhds (σ - σ)) :=
      (continuous_id.sub continuous_const).tendsto σ
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hrestlim : Filter.Tendsto rest (nhdsWithin σ ({σ}ᶜ)) (nhds (rest σ)) :=
    Filter.Tendsto.mono_left hrest nhdsWithin_le_nhds
  have hprod : Filter.Tendsto (fun z : ℂ => ν + (z - σ) * rest z)
      (nhdsWithin σ ({σ}ᶜ)) (nhds (ν + 0 * rest σ)) :=
    tendsto_const_nhds.add (hsub.mul hrestlim)
  have hcongr : Filter.Tendsto (fun z : ℂ => (z - σ) * (N z / D z))
      (nhdsWithin σ ({σ}ᶜ)) (nhds (ν + 0 * rest σ)) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hdecomp z hz, mul_add, residue_poleTerm ν σ hz]
  have := tendsto_nhds_unique hcongr hres
  simpa using this

/-! ## Clearing the denominators

Multiplying a Cauchy combination by the node product turns it into a polynomial expression: each
term loses its own factor and keeps the rest.  Doing this to numerator and denominator alike
exhibits the shift ratio as a ratio of polynomial values, which is what connects it to the
partial-fraction theorem over linear factors. -/

/-- **The clearing identity.**  The node product times a Cauchy combination is the sum of the
weights against the complementary products. -/
theorem prod_mul_cauchySum {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ) (z : ℂ)
    (h : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) :
    (∏ j ∈ s, ((t j : ℂ) - z)) * (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z))
      = ∑ j ∈ s, (w j : ℂ) * ∏ k ∈ s.erase j, ((t k : ℂ) - z) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne := h j hj
  rw [← Finset.mul_prod_erase s (fun k => ((t k : ℂ) - z)) hj]
  field_simp

theorem prod_node_ne_zero {ι : Type*} (s : Finset ι) (t : ι → ℝ) (z : ℂ)
    (h : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) : (∏ j ∈ s, ((t j : ℂ) - z)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr h

/-- **The shift ratio is a ratio of polynomial values.**  Clearing the node product from numerator
and denominator leaves two polynomial expressions of one lower degree. -/
theorem cauchyRatio_eq_polyRatio {ι : Type*} [DecidableEq ι] (s : Finset ι) (w r t : ι → ℝ)
    (z : ℂ) (h : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) :
    (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z))
        / (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z))
      = (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) * ∏ k ∈ s.erase j, ((t k : ℂ) - z))
        / (∑ j ∈ s, ((w j : ℝ) : ℂ) * ∏ k ∈ s.erase j, ((t k : ℂ) - z)) := by
  have hP := prod_node_ne_zero s t z h
  rw [← prod_mul_cauchySum s (fun j => w j * r j) t z h, ← prod_mul_cauchySum s w t z h,
    mul_div_mul_left _ _ hP]

/-! ## The cleared denominator is a polynomial of one lower degree

The clearing identity's right-hand side is the evaluation of an honest polynomial — the weights
against the complementary node products.  Its degree is at most one below the node count, which is
the input the factorization bridge needs: a polynomial of that degree with that many distinct real
roots is exactly a constant times the product of the corresponding linear factors. -/

open Polynomial in
/-- The cleared Cauchy combination, as a polynomial. -/
noncomputable def cauchyClearedPoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ) :
    ℝ[X] :=
  ∑ j ∈ s, C (w j) * ∏ k ∈ s.erase j, (C (t k) - X)

open Polynomial in
/-- Its complex values are the cleared combination. -/
theorem aeval_cauchyClearedPoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ) (z : ℂ) :
    aeval z (cauchyClearedPoly s w t)
      = ∑ j ∈ s, (w j : ℂ) * ∏ k ∈ s.erase j, ((t k : ℂ) - z) := by
  simp [cauchyClearedPoly]

open Polynomial in
/-- Its degree is at most one below the node count. -/
theorem natDegree_cauchyClearedPoly_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ) :
    (cauchyClearedPoly s w t).natDegree ≤ s.card - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hterm : ∀ k ∈ s.erase j, (C (t k) - X : ℝ[X]).natDegree = 1 := fun k _ => by
    rw [show (C (t k) - X : ℝ[X]) = -(X - C (t k)) by ring, natDegree_neg, natDegree_X_sub_C]
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.card_erase_of_mem hj]

open Polynomial in
/-- **The clearing identity in polynomial form.**  The node product times a Cauchy combination is
the value of a polynomial of degree at most one below the node count. -/
theorem prod_mul_cauchySum_eq_aeval {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    (z : ℂ) (h : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) :
    (∏ j ∈ s, ((t j : ℂ) - z)) * (∑ j ∈ s, (w j : ℂ) / ((t j : ℂ) - z))
      = aeval z (cauchyClearedPoly s w t) := by
  rw [aeval_cauchyClearedPoly, prod_mul_cauchySum s w t z h]

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

/-! ## Theorem A

The double sum of `(1)` is not a formal device: it *is* the imaginary part of the numerator against
the conjugate denominator.  With that identity the two halves compose — monotone likelihood makes
the double sum nonpositive, and a ratio whose numerator against the conjugate denominator has
nonpositive imaginary part is anti-Herglotz. -/

/-- **The double sum is the numerator against the conjugate denominator.**  Expanding the product of
the two Cauchy sums and taking imaginary parts termwise gives exactly the symmetrized sum of `(1)`.
This is the identity that joins `(1)` to the ratio. -/
theorem im_numerator_mul_conj_denominator {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    ((∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z)) *
        (starRingEnd ℂ) (∑ k ∈ s, ((w k : ℝ) : ℂ) / ((t k : ℂ) - z))).im
      = ∑ j ∈ s, ∑ k ∈ s,
          w j * r j * w k *
            (z.im * (t k - t j) /
              (Complex.normSq ((t j : ℂ) - z) * Complex.normSq ((t k : ℂ) - z))) := by
  rw [map_sum, Finset.sum_mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hj : ((t j : ℂ) - z) ≠ 0 := sub_ofReal_ne_zero_of_im_ne_zero hz
  have hk : ((t k : ℂ) - z) ≠ 0 := sub_ofReal_ne_zero_of_im_ne_zero hz
  have hrw : ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z) *
        (starRingEnd ℂ) (((w k : ℝ) : ℂ) / ((t k : ℂ) - z))
      = ((w j * r j * w k : ℝ) : ℂ) *
          ((1 / ((t j : ℂ) - z)) * (starRingEnd ℂ) (1 / ((t k : ℂ) - z))) := by
    rw [map_div₀, map_div₀, Complex.conj_ofReal, map_one]
    push_cast
    ring
  rw [hrw, Complex.im_ofReal_mul, im_cauchy_mul_conj hj hk]

/-- **Theorem A.**  A ratio of Cauchy transforms with nonnegative weights and monotone responses is
anti-Herglotz above the real axis.  The whole content is `(1)`: the symmetrized double sum carries
`(r_j - r_k)(t_j - t_k)` behind a minus sign, so monotone likelihood makes it nonpositive, and it is
the imaginary part of the numerator against the conjugate denominator. -/
theorem im_shiftRatio_nonpos {ι : Type*} (s : Finset ι) (w r t : ι → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j ∈ s, 0 ≤ w j)
    (hmono : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ (r j - r k) * (t j - t k)) :
    ((∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z)) /
        (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z))).im ≤ 0 := by
  refine im_ratio_nonpos_of_im_mul_conj_nonpos ?_
  rw [im_numerator_mul_conj_denominator s w r t (ne_of_gt hz)]
  exact im_antiPick_nonpos s w r t hz hw hmono

/-- **Constant responses give the constant ratio.**  If every response is the same, the numerator is
that constant times the denominator, so the ratio is constant and its Stieltjes measure vanishes. -/
theorem shiftRatio_eq_const_of_response_const {ι : Type*} (s : Finset ι) (w t : ι → ℝ) {r : ι → ℝ}
    {c : ℝ} (hr : ∀ j ∈ s, r j = c) (z : ℂ)
    (hD : (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z)) ≠ 0) :
    (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z)) /
        (∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z)) = (c : ℂ) := by
  have hnum : (∑ j ∈ s, ((w j * r j : ℝ) : ℂ) / ((t j : ℂ) - z))
      = (c : ℂ) * ∑ j ∈ s, ((w j : ℝ) : ℂ) / ((t j : ℂ) - z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hr j hj]
    push_cast
    ring
  rw [hnum, mul_div_assoc, div_self hD, mul_one]

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

/-! ## The root list and the factorization

A zero of the combination is a root of the cleared polynomial, since the node product does not
vanish there.  With the nodes in increasing order there is one such zero in each of the `n` gaps, and
they are distinct because they lie in disjoint intervals.  That is exactly `n` distinct roots of a
polynomial of degree at most `n`, so the factorization bridge applies and the shift ratio decomposes
with one simple pole per gap. -/

open Polynomial in
/-- The cleared polynomial's real values. -/
theorem eval_cauchyClearedPoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ) (x : ℝ) :
    (cauchyClearedPoly s w t).eval x = ∑ j ∈ s, w j * ∏ k ∈ s.erase j, (t k - x) := by
  simp [cauchyClearedPoly, Polynomial.eval_finsetSum, Polynomial.eval_prod]

open Polynomial in
/-- The real clearing identity. -/
theorem prod_mul_cauchySumReal_eq_eval {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    (x : ℝ) (h : ∀ j ∈ s, t j - x ≠ 0) :
    (∏ j ∈ s, (t j - x)) * (∑ j ∈ s, w j / (t j - x)) = (cauchyClearedPoly s w t).eval x := by
  rw [eval_cauchyClearedPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne := h j hj
  rw [← Finset.mul_prod_erase s (fun k => t k - x) hj]
  field_simp

open Polynomial in
/-- **A zero of the combination is a root of the cleared polynomial**, since the node product does
not vanish off the nodes. -/
theorem isRoot_cauchyClearedPoly {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    {x : ℝ} (h : ∀ j ∈ s, t j - x ≠ 0) (hx : (∑ j ∈ s, w j / (t j - x)) = 0) :
    (cauchyClearedPoly s w t).IsRoot x := by
  rw [Polynomial.IsRoot, ← prod_mul_cauchySumReal_eq_eval s w t x h, hx, mul_zero]

open Polynomial in
/-- The cleared polynomial is nonzero: below every node all its terms are positive. -/
theorem cauchyClearedPoly_ne_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) : cauchyClearedPoly s w t ≠ 0 := by
  set m := s.inf' hne t with hm
  have hpos : ∀ j ∈ s, 0 < t j - (m - 1) := fun j hj => by
    have hle : m ≤ t j := Finset.inf'_le t hj
    linarith
  intro hzero
  have hev : (cauchyClearedPoly s w t).eval (m - 1) = 0 := by rw [hzero]; simp
  rw [← prod_mul_cauchySumReal_eq_eval s w t _ fun j hj => ne_of_gt (hpos j hj)] at hev
  have h1 : 0 < ∏ j ∈ s, (t j - (m - 1)) := Finset.prod_pos fun j hj => hpos j hj
  have h2 : 0 < ∑ j ∈ s, w j / (t j - (m - 1)) :=
    Finset.sum_pos (fun j hj => div_pos (hw j hj) (hpos j hj)) hne
  exact absurd hev (ne_of_gt (mul_pos h1 h2))

open Polynomial Set in
/-- **The root list.**  For strictly increasing nodes with positive weights there is one zero of the
combination in each of the `n` gaps; being in disjoint intervals they are distinct, and each is a
root of the cleared polynomial. -/
theorem exists_injective_gapRoots {n : ℕ} (w t : Fin (n + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (ht : StrictMono t) :
    ∃ σ : Fin n → ℝ, (∀ i, σ i ∈ Ioo (t i.castSucc) (t i.succ)) ∧ Function.Injective σ ∧
      ∀ i, (cauchyClearedPoly Finset.univ w t).IsRoot (σ i) := by
  have hnone : ∀ (i : Fin n) (j : Fin (n + 1)), t j ∉ Ioo (t i.castSucc) (t i.succ) := by
    intro i j hj
    have h1 : i.castSucc < j := ht.lt_iff_lt.mp hj.1
    have h2 : j < i.succ := ht.lt_iff_lt.mp hj.2
    rw [Fin.lt_def] at h1 h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    omega
  have hgap : ∀ i : Fin n, ∃ c ∈ Ioo (t i.castSucc) (t i.succ),
      (∑ j : Fin (n + 1), w j / (t j - c)) = 0 := by
    intro i
    obtain ⟨c, hc, -⟩ := existsUnique_zero_in_gap Finset.univ w t (Finset.mem_univ i.castSucc)
      (Finset.mem_univ i.succ) (fun j _ => hw j) (fun a _ b _ h => ht.injective h)
      (ht (Fin.castSucc_lt_succ (i := i))) fun j _ => hnone i j
    exact ⟨c, hc.1, hc.2⟩
  choose σ hmem hzero using hgap
  have hstrict : ∀ i j : Fin n, i < j → σ i < σ j := by
    intro i j hij
    have h3 : t i.succ ≤ t j.castSucc := by
      refine ht.monotone ?_
      rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    have h1 := (hmem i).2
    have h2 := (hmem j).1
    linarith
  refine ⟨σ, hmem, ?_, fun i => ?_⟩
  · intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (ne_of_lt (hstrict i j h))
    · exact h
    · exact absurd hij (ne_of_gt (hstrict j i h))
  · refine isRoot_cauchyClearedPoly _ w t (fun j _ hc => ?_) (hzero i)
    exact hnone i j (by rw [sub_eq_zero.mp hc]; exact hmem i)

open Polynomial Set in
/-- **`(3)`'s factorization.**  The cleared denominator is a constant times the product of the linear
factors at its `n` interlacing zeros, one in each node gap. -/
theorem exists_factorization_cauchyClearedPoly {n : ℕ} (w t : Fin (n + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (ht : StrictMono t) :
    ∃ (c : ℝ) (σ : Fin n → ℝ), Function.Injective σ ∧
      (∀ i, σ i ∈ Ioo (t i.castSucc) (t i.succ)) ∧
      cauchyClearedPoly Finset.univ w t = C c * ∏ i, (X - C (σ i)) := by
  obtain ⟨σ, hmem, hinj, hroot⟩ := exists_injective_gapRoots w t hw ht
  have hdeg : (cauchyClearedPoly (Finset.univ : Finset (Fin (n + 1))) w t).natDegree
      ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using natDegree_cauchyClearedPoly_le (Finset.univ : Finset (Fin (n + 1))) w t
  obtain ⟨c, hc⟩ :=
    GaloisForLFunctions.HTGeometry.eq_C_mul_prod_X_sub_C hinj (fun i _ => hroot i) hdeg
  exact ⟨c, σ, hinj, hmem, hc⟩

open Polynomial Set in
/-- **`(3)`, existence.**  The cleared shift ratio decomposes as a polynomial part plus one simple
pole in each node gap, with scalar residues. -/
theorem exists_partialFractions_shiftRatio {n : ℕ} (w r t : Fin (n + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (ht : StrictMono t) :
    ∃ (σ : Fin n → ℝ) (q : ℝ[X]) (ν : Fin n → ℝ), Function.Injective σ ∧
      (∀ i, σ i ∈ Ioo (t i.castSucc) (t i.succ)) ∧
      ((cauchyClearedPoly Finset.univ (fun j => w j * r j) t : ℝ[X]) : RatFunc ℝ)
            / ((cauchyClearedPoly Finset.univ w t : ℝ[X]) : RatFunc ℝ)
          = ((q : ℝ[X]) : RatFunc ℝ)
            + ∑ i, ((C (ν i) : ℝ[X]) : RatFunc ℝ) / ((X - C (σ i) : ℝ[X]) : RatFunc ℝ) := by
  obtain ⟨σ, hmem, hinj, hroot⟩ := exists_injective_gapRoots w t hw ht
  have hdeg : (cauchyClearedPoly (Finset.univ : Finset (Fin (n + 1))) w t).natDegree
      ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using natDegree_cauchyClearedPoly_le (Finset.univ : Finset (Fin (n + 1))) w t
  obtain ⟨q, ν, hq⟩ :=
    GaloisForLFunctions.HTGeometry.div_eq_add_sum_const_of_isRoot
      (cauchyClearedPoly Finset.univ (fun j => w j * r j) t) hinj (fun i _ => hroot i) hdeg
      (cauchyClearedPoly_ne_zero Finset.univ w t (fun j _ => hw j) Finset.univ_nonempty)
  exact ⟨σ, q, ν, hinj, hmem, hq⟩

end RHTower
