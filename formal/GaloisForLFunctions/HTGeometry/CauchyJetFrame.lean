import GaloisForLFunctions.HTGeometry.CayleyMomentFrame
import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# All-order regular Cauchy jets of finite measures

For a finite real Borel measure, the resolvent transform is holomorphic off the real support.
This module proves the all-order formula

`iteratedDeriv n (resolventTransform μ) a = n! ∫ x, resolvent a x ^ (n+1) ∂μ`

at every regular complex node. At `a = -i` this is exactly the reciprocal-moment formula used to
identify finite Cayley frames with finite Cauchy jets in the cofinal Cholesky selection law.
-/

open MeasureTheory Measure Metric Complex spectrum
open scoped Topology ComplexOrder ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The integral of the `r`-th resolvent power. -/
def resolventPowerTransform (μ : Measure ℝ) (r : ℕ) (a : ℂ) : ℂ :=
  ∫ x, resolvent a x ^ r ∂μ

/-- Every resolvent power is integrable at a point outside the real support of a finite measure. -/
theorem integrable_resolvent_pow
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a : ℂ}
    (ha : a ∉ algebraMap ℝ ℂ '' μ.support) (r : ℕ) :
    Integrable (fun x : ℝ => resolvent a x ^ r) μ := by
  by_cases hsupport : μ.support.Nonempty
  · have hdist : 0 < infDist a (algebraMap ℝ ℂ '' μ.support) := by
      refine (IsClosed.notMem_iff_infDist_pos ?_ (hsupport.image _)).mp ha
      refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
      exact (algebraMap_isometry ℝ ℂ).isClosedEmbedding
    apply Integrable.of_bound (by fun_prop)
      ((infDist a (algebraMap ℝ ℂ '' μ.support))⁻¹ ^ r)
    filter_upwards [support_mem_ae] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_resolvent_le_inv_infDist_support ha hx) r
  · have hs : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp hsupport
    rw [support_eq_empty_iff.mp hs]
    simp

/-- Differentiation raises the resolvent power by one and multiplies it by the old power. -/
theorem hasDerivAt_resolventPowerTransform
    {μ : Measure ℝ} [IsFiniteMeasure μ] (r : ℕ) (hr : 1 ≤ r)
    (a : ℂ) (ha : a ∉ algebraMap ℝ ℂ '' μ.support) :
    HasDerivAt (resolventPowerTransform μ r)
      ((r : ℂ) * resolventPowerTransform μ (r + 1) a) a := by
  by_cases! hsupport : μ.support.Nonempty
  swap
  · rw [support_eq_empty_iff.mp hsupport]
    have hz : resolventPowerTransform (0 : Measure ℝ) r = fun _ => 0 := by
      funext z
      simp [resolventPowerTransform]
    rw [hz]
    simpa [resolventPowerTransform] using hasDerivAt_const a (0 : ℂ)
  have hdist : 0 < infDist a (algebraMap ℝ ℂ '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (hsupport.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry ℝ ℂ).isClosedEmbedding
  let s : Set ℂ := ball a ((infDist a (algebraMap ℝ ℂ '' μ.support)) / 2)
  have hs_a : s ∈ 𝓝 a := ball_mem_nhds _ (by positivity)
  have hs_μ : s ⊆ (algebraMap ℝ ℂ '' μ.support)ᶜ := by
    unfold s
    grw [ball_subset_ball, ball_infDist_subset_compl]
    grind
  have hmeas : ∀ᶠ w in nhds a,
      AEStronglyMeasurable (fun x : ℝ => resolvent w x ^ r) μ := by
    filter_upwards with w
    exact (measurable_resolvent (a := w)).aestronglyMeasurable.pow r
  have hbound : ∀ᵐ x ∂μ, ∀ w ∈ s,
      ‖(r : ℂ) * resolvent w x ^ (r + 1)‖ ≤
        (r : ℝ) * ((infDist a (algebraMap ℝ ℂ '' μ.support)) / 2)⁻¹ ^ (r + 1) := by
    filter_upwards [support_mem_ae] with x hx w hw
    rw [norm_mul, Complex.norm_natCast, norm_pow]
    gcongr
    grw [resolvent, Ring.inverse_eq_inv, norm_inv]
    gcongr
    calc infDist a (algebraMap ℝ ℂ '' μ.support) / 2
      _ ≤ infDist a (algebraMap ℝ ℂ '' μ.support)
        - infDist a (algebraMap ℝ ℂ '' μ.support) / 2 := by grind
      _ ≤ ‖(algebraMap ℝ ℂ) x - a‖ - ‖a - w‖ := by
        gcongr
        · grw [infDist_le_dist_of_mem (y := (algebraMap ℝ ℂ) x) (by simp [hx]), dist_comm,
            dist_eq_norm]
        · apply le_of_lt
          simpa [s, ← dist_eq_norm, dist_comm w a] using hw
      _ ≤ ‖(algebraMap ℝ ℂ) x - w‖ := by grw [norm_sub_le_norm_add]; grind
  have hderiv : ∀ᵐ x ∂μ, ∀ w ∈ s,
      HasDerivAt (fun w : ℂ => resolvent w x ^ r)
        ((r : ℂ) * resolvent w x ^ (r + 1)) w := by
    filter_upwards [support_mem_ae] with x hx w hw
    have hbase : HasDerivAt (fun w : ℂ => resolvent w x) (resolvent w x ^ 2) w := by
      apply hasDerivAt_resolvent_const_right
      replace hw := hs_μ hw
      contrapose! hw
      rw [Set.notMem_compl_iff]
      use x, hx
      simpa [resolventSet, sub_eq_zero] using hw
    have halg :
        (r : ℂ) * resolvent w x ^ (r + 1) =
          (r : ℂ) * resolvent w x ^ (r - 1) * resolvent w x ^ 2 := by
      calc
        (r : ℂ) * resolvent w x ^ (r + 1) =
            (r : ℂ) * (resolvent w x ^ (r - 1) * resolvent w x ^ 2) := by
          congr 1
          rw [← pow_add]
          congr 1
          omega
        _ = (r : ℂ) * resolvent w x ^ (r - 1) * resolvent w x ^ 2 := by ring
    rw [halg]
    exact hbase.pow r
  have hraw := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_a hmeas
    (integrable_resolvent_pow ha r) (by fun_prop) hbound (by fun_prop) hderiv
  rw [resolventPowerTransform]
  convert hraw.2 using 1
  rw [integral_const_mul]

/-- The normalized all-order Cauchy-jet function. -/
def cauchyJetFunction (μ : Measure ℝ) (n : ℕ) (a : ℂ) : ℂ :=
  (n.factorial : ℂ) * resolventPowerTransform μ (n + 1) a

/-- Successive normalized Cauchy-jet functions are exact derivatives of one another. -/
theorem hasDerivAt_cauchyJetFunction
    {μ : Measure ℝ} [IsFiniteMeasure μ] (n : ℕ)
    (a : ℂ) (ha : a ∉ algebraMap ℝ ℂ '' μ.support) :
    HasDerivAt (cauchyJetFunction μ n) (cauchyJetFunction μ (n + 1) a) a := by
  have h := HasDerivAt.const_mul (n.factorial : ℂ)
    (hasDerivAt_resolventPowerTransform (μ := μ) (n + 1) (by omega) a ha)
  unfold cauchyJetFunction
  convert h using 1
  simp [Nat.factorial_succ]
  ring

/-- The all-order derivative formula for the resolvent transform of a finite real measure. -/
theorem iteratedDeriv_resolventTransform
    {μ : Measure ℝ} [IsFiniteMeasure μ] (n : ℕ)
    (a : ℂ) (ha : a ∉ algebraMap ℝ ℂ '' μ.support) :
    iteratedDeriv n (resolventTransform μ) a = cauchyJetFunction μ n a := by
  induction n generalizing a with
  | zero =>
      simp [cauchyJetFunction, resolventPowerTransform, resolventTransform_apply]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hclosed : IsClosed (algebraMap ℝ ℂ '' μ.support) := by
        refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
        exact (algebraMap_isometry ℝ ℂ).isClosedEmbedding
      have hlocal : iteratedDeriv n (resolventTransform μ) =ᶠ[𝓝 a]
          cauchyJetFunction μ n := by
        filter_upwards [hclosed.isOpen_compl.mem_nhds ha] with z hz
        exact ih z hz
      rw [hlocal.deriv_eq]
      exact (hasDerivAt_cauchyJetFunction n a ha).deriv

/-- Cauchy jets of a real measure at conjugate nonreal nodes are complex conjugates. -/
theorem iteratedDeriv_resolventTransform_conj
    {μ : Measure ℝ} [IsFiniteMeasure μ] (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    iteratedDeriv n (resolventTransform μ) (star z) =
      star (iteratedDeriv n (resolventTransform μ) z) := by
  have hzsupport : z ∉ algebraMap ℝ ℂ '' μ.support := by
    rintro ⟨x, _hx, hxz⟩
    have him := congrArg Complex.im hxz
    simp at him
    exact hz him.symm
  have hstarsupport : star z ∉ algebraMap ℝ ℂ '' μ.support := by
    rintro ⟨x, _hx, hxz⟩
    have him := congrArg Complex.im hxz
    simp at him
    exact hz him
  rw [iteratedDeriv_resolventTransform n (star z) hstarsupport,
    iteratedDeriv_resolventTransform n z hzsupport]
  unfold cauchyJetFunction resolventPowerTransform
  rw [star_mul, star_natCast]
  rw [mul_comm (star (∫ (x : ℝ), resolvent z x ^ (n + 1) ∂μ))]
  congr 1
  change (∫ (x : ℝ), resolvent (star z) x ^ (n + 1) ∂μ) =
    conj (∫ (x : ℝ), resolvent z x ^ (n + 1) ∂μ)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_pow]
  congr 1
  simp [resolvent]

/-- At `-i`, resolvent powers are the reciprocal moments from the Cayley frame module. -/
theorem resolventPowerTransform_neg_I_eq_reciprocalMoment
    (μ : Measure ℝ) (r : ℕ) :
    resolventPowerTransform μ r (-I) = reciprocalMoment μ r := by
  simp only [resolventPowerTransform, reciprocalMoment, resolvent]
  congr 1
  funext x
  congr 1
  simp

/-- The regular node `-i` never belongs to the complex image of a real support. -/
theorem neg_I_notMem_real_support_image (μ : Measure ℝ) :
    -I ∉ algebraMap ℝ ℂ '' μ.support := by
  rintro ⟨x, hx, h⟩
  have := congrArg Complex.im h
  norm_num at this

/-- Exact manuscript formula: the `n`-th Cauchy derivative at `-i` is `n!` times reciprocal
moment `n+1`. -/
theorem iteratedDeriv_resolventTransform_neg_I
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    iteratedDeriv n (resolventTransform μ) (-I) =
      (n.factorial : ℂ) * reciprocalMoment μ (n + 1) := by
  rw [iteratedDeriv_resolventTransform n (-I) (neg_I_notMem_real_support_image μ)]
  exact congrArg ((n.factorial : ℂ) * ·)
    (resolventPowerTransform_neg_I_eq_reciprocalMoment μ (n + 1))

/-- A probability measure has zeroth reciprocal moment one. -/
theorem reciprocalMoment_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    reciprocalMoment μ 0 = 1 := by
  simp [reciprocalMoment]

/-- For probability measures, equality of reciprocal moments through level `N` is exactly equality
of regular Cauchy derivatives of orders strictly below `N`. -/
theorem reciprocalMoment_prefix_iff_cauchyJet_prefix
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    (∀ r ≤ N, reciprocalMoment μ r = reciprocalMoment ν r) ↔
      ∀ n < N,
        iteratedDeriv n (resolventTransform μ) (-I) =
          iteratedDeriv n (resolventTransform ν) (-I) := by
  constructor
  · intro h n hn
    rw [iteratedDeriv_resolventTransform_neg_I,
      iteratedDeriv_resolventTransform_neg_I,
      h (n + 1) (by omega)]
  · intro h r hr
    cases r with
    | zero => rw [reciprocalMoment_zero μ, reciprocalMoment_zero ν]
    | succ n =>
        have hj := h n (by omega)
        rw [iteratedDeriv_resolventTransform_neg_I,
          iteratedDeriv_resolventTransform_neg_I] at hj
        apply mul_left_cancel₀ (a := (n.factorial : ℂ))
        · exact_mod_cast Nat.factorial_ne_zero n
        · exact hj

/-- Exact finite frame/jet equivalence for normalized measures: the Cayley moments through level
`N` agree if and only if the Cauchy jets at `-i` agree through order `N-1`. -/
theorem cayleyMoment_prefix_iff_cauchyJet_prefix
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    (∀ k ≤ N, cayleyMoment μ k = cayleyMoment ν k) ↔
      ∀ n < N,
        iteratedDeriv n (resolventTransform μ) (-I) =
          iteratedDeriv n (resolventTransform ν) (-I) := by
  rw [cayleyMoment_prefix_iff_reciprocalMoment_prefix,
    reciprocalMoment_prefix_iff_cauchyJet_prefix]

/-- The same finite frame/jet equivalence at the upper regular node `i`.  For real measures this
is equivalent to the conventional `-i` statement by conjugation. -/
theorem cayleyMoment_prefix_iff_cauchyJet_pos_I_prefix
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    (∀ k ≤ N, cayleyMoment μ k = cayleyMoment ν k) ↔
      ∀ n < N,
        iteratedDeriv n (resolventTransform μ) I =
          iteratedDeriv n (resolventTransform ν) I := by
  rw [cayleyMoment_prefix_iff_cauchyJet_prefix]
  constructor
  · intro h n hn
    have hμ := iteratedDeriv_resolventTransform_conj (μ := μ) n (-I) (by simp)
    have hν := iteratedDeriv_resolventTransform_conj (μ := ν) n (-I) (by simp)
    simpa using hμ.trans ((congrArg star (h n hn)).trans hν.symm)
  · intro h n hn
    have hμ := iteratedDeriv_resolventTransform_conj (μ := μ) n I (by simp)
    have hν := iteratedDeriv_resolventTransform_conj (μ := ν) n I (by simp)
    simpa using hμ.trans ((congrArg star (h n hn)).trans hν.symm)

/-- Equality of Cayley Toeplitz Gram sections is exactly equality of the corresponding finite
regular Cauchy jets. -/
theorem circleToeplitzGram_eq_iff_cauchyJet_prefix
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    circleToeplitzGram N (cayleyMomentZ μ) =
        circleToeplitzGram N (cayleyMomentZ ν) ↔
      ∀ n < N,
        iteratedDeriv n (resolventTransform μ) (-I) =
          iteratedDeriv n (resolventTransform ν) (-I) := by
  rw [circleToeplitzGram_cayleyMomentZ_eq_iff,
    cayleyMoment_prefix_iff_cauchyJet_prefix]

/-- A common inverse-Cholesky frame through level `N` forces equality of the regular Cauchy jets
through order `N-1`. -/
theorem cauchyJet_eq_of_same_inverseCholeskyFrame
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hμ : IsInverseCholeskyFrame C
      (circleToeplitzGram N (cayleyMomentZ μ)))
    (hν : IsInverseCholeskyFrame C
      (circleToeplitzGram N (cayleyMomentZ ν))) :
    ∀ n < N,
      iteratedDeriv n (resolventTransform μ) (-I) =
        iteratedDeriv n (resolventTransform ν) (-I) := by
  rw [← circleToeplitzGram_eq_iff_cauchyJet_prefix]
  exact gram_eq_of_same_inverseCholesky C _ _ hμ hν

/-- Exact canonical finite-frame/jet equivalence. For positive-definite Cayley Gram sections, the
normalized lower-triangular inverse-Cholesky frames agree exactly when the regular Cauchy jets at
`-i` agree through order `N-1`. -/
theorem gramSchmidtInverseFrame_eq_iff_cauchyJet_prefix
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ)
    (hμ : (circleToeplitzGram N (cayleyMomentZ μ)).PosDef)
    (hν : (circleToeplitzGram N (cayleyMomentZ ν)).PosDef) :
    gramSchmidtInverseFrame (circleToeplitzGram N (cayleyMomentZ μ)) hμ =
        gramSchmidtInverseFrame (circleToeplitzGram N (cayleyMomentZ ν)) hν ↔
      ∀ n < N,
        iteratedDeriv n (resolventTransform μ) (-I) =
          iteratedDeriv n (resolventTransform ν) (-I) := by
  rw [gramSchmidtInverseFrame_eq_iff_gram_eq,
    circleToeplitzGram_eq_iff_cauchyJet_prefix]

end

end GaloisForLFunctions.HTGeometry
