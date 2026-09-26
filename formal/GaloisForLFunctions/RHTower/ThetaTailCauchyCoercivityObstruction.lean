import GaloisForLFunctions.RHTower.ThetaTailAnalyticLocality
import GaloisForLFunctions.RHTower.ThetaTailCauchyAsymptotic

/-!
# The complete theta tail has no positive uniform Cauchy reserve

For every real tail and every c > 0, some finite real Gram packet makes
K_Phi - c C_Phi negative, where
C_Phi(x,y) = Phi(x) Phi(y) / (exp(2x) + exp(2y)).
This is an obstruction to strict relative coercivity, not a negative packet for
K_Phi itself and not a decision of RH.

The exact reflected diagonal asymptotic first excludes a rank-one reference
feature. An augmented analytic L2 realization transports this obstruction to
every tail. The Cauchy Schur complement then supplies the stated reserve test.
-/

noncomputable section
namespace RHTower.ThetaTailCoercivityAudit
open Set Filter Topology

theorem diagonal_source_ratio_atTop :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel r r / thetaCuspFullSource r^2)
      atTop (𝓝 0) := by
  have hf : Tendsto (fun r : ℝ => Real.exp (-2*r)*r) atTop (𝓝 0) := by
    simpa [Real.rpow_one, mul_comm, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) 2 (by norm_num)
  have h := (ThetaTailCauchy.kernel_normalized_limit 0 0).mul hf
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  simp only [zero_add, ThetaTailCauchy.normalizer]
  field_simp [hr.ne', (Real.exp_pos (-2*r)).ne',
    (HedenmalmThetaSource.thetaCuspFullSource_pos r).ne']

theorem diagonal_source_ratio_atBot :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel r r / thetaCuspFullSource r^2)
      atBot (𝓝 0) := by
  have h := diagonal_source_ratio_atTop.comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, thetaTailFirstMomentKernel_neg_neg,
    thetaCuspFullSource_neg] using h

/-- Exact incoming diagonal scale, retaining the complete reflected source. -/
theorem reflected_diagonal_normalized_limit :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel (-r) (-r) /
      (r*Real.exp (-2*r)*thetaCuspFullSource (-r)^2))
      atTop (𝓝 (1/(2*Real.pi))) := by
  simpa [ThetaTailCauchy.normalizer, thetaTailFirstMomentKernel_neg_neg,
    thetaCuspFullSource_neg, pow_two, mul_comm, mul_left_comm, mul_assoc,
    show (1:ℝ)+1=2 by norm_num] using
      ThetaTailCauchy.kernel_normalized_limit 0 0

def rankOneFeature (z : ℂ) : ℂ :=
  thetaCuspStripSource z / (Complex.exp (2*z)+1)

def realFeature (x : ℝ) : ℝ :=
  thetaCuspFullSource x / (Real.exp (2*x)+1)

theorem rankOneFeature_ofReal (x : ℝ) : rankOneFeature (x:ℂ) = (realFeature x:ℂ) := by
  simp [rankOneFeature, realFeature, thetaCuspStripSource_ofReal, Complex.ofReal_exp]

theorem exp_two_add_one_ne_zero {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    Complex.exp (2*z)+1 ≠ 0 := by
  change |z.im| < Real.pi/4 at hz
  have hcos : 0 < Real.cos (2*z.im) :=
    Real.cos_pos_of_mem_Ioo (by constructor <;> linarith [le_abs_self z.im, neg_le_abs z.im])
  have hre : 0 < (Complex.exp (2*z)+1).re := by
    simpa [Complex.exp_re] using
      add_pos (mul_pos (Real.exp_pos (2*z.re)) hcos) (show (0:ℝ)<1 by norm_num)
  intro he
  rw [he, Complex.zero_re] at hre
  exact (lt_irrefl 0) hre

theorem rankOneFeature_analytic : AnalyticOnNhd ℂ rankOneFeature thetaCuspStrip := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_thetaCuspStrip
  apply differentiableOn_thetaCuspStripSource.div
  · fun_prop
  · intro z hz
    exact exp_two_add_one_ne_zero hz

theorem diagonal_feature_ratio_atBot :
    Tendsto (fun r : ℝ => thetaTailFirstMomentKernel r r / realFeature r^2)
      atBot (𝓝 0) := by
  have he : Tendsto (fun r : ℝ => Real.exp (2*r)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0:ℝ)<2))
  have h := diagonal_source_ratio_atBot.mul ((he.add_const 1).pow 2)
  simp only [zero_add, one_pow, zero_mul] at h
  convert h using 1
  funext r
  unfold realFeature
  field_simp [(HedenmalmThetaSource.thetaCuspFullSource_pos r).ne',
    (show Real.exp (2*r)+1 ≠ 0 by positivity)]

theorem exists_negative_rankOne_diagonal {c : ℝ} (hc : 0<c) :
    ∃ x : ℝ, thetaTailFirstMomentKernel x x-c*realFeature x^2 < 0 := by
  have h := diagonal_feature_ratio_atBot.eventually (eventually_lt_nhds hc)
  obtain ⟨x, hx⟩ := h.exists
  have hf : 0 < realFeature x := by
    exact div_pos (HedenmalmThetaSource.thetaCuspFullSource_pos x) (by positivity)
  have hn := (div_lt_iff₀ (pow_pos hf 2)).mp hx
  exact ⟨x, by linarith⟩

end RHTower.ThetaTailCoercivityAudit

noncomputable section
namespace RHTower.ThetaTailCoercivityAudit
open DominatedL2Sections Set Filter Topology
open scoped InnerProductSpace

abbrev Augmented := SourceAugmented

def augmentedSection (z : ℂ) : Augmented :=
  WithLp.toLp 2 (completeThetaSource.section z, rankOneFeature z)

def augmentedForm (c : ℝ) : Augmented →L[ℂ] Augmented :=
  scalarDifferenceForm c

theorem augmentedForm_apply (c : ℝ) (v : Augmented) :
    augmentedForm c v = WithLp.toLp 2 (differenceForm v.fst, -(2*c:ℂ)*v.snd) := rfl

theorem augmentedForm_hermitian (c : ℝ) (v w : Augmented) :
    inner ℂ v (augmentedForm c w) = inner ℂ (augmentedForm c v) w :=
  scalarDifferenceForm_hermitian c v w

theorem augmentedSection_analytic_inner (v : Augmented) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (augmentedSection z)) thetaCuspStrip := by
  have h := (completeThetaSource.analytic_inner v.fst).add
    (rankOneFeature_analytic.mul (analyticOnNhd_const (v := star v.snd)))
  apply AnalyticOnNhd.congr isOpen_thetaCuspStrip h
  intro z _
  change inner ℂ v.fst (completeThetaSource.section z)+rankOneFeature z*star v.snd = _
  rw [WithLp.prod_inner_apply]
  rfl

def rankOneRealization (c : ℝ) :=
  compressedClosedSpanRealization thetaCuspStrip augmentedSection (augmentedForm c)
    isPreconnected_thetaCuspStrip isOpen_thetaCuspStrip augmentedSection_analytic_inner
    (augmentedForm_hermitian c)

private theorem real_mem_strip (x : ℝ) : (x:ℂ) ∈ thetaCuspStrip := by
  simp only [thetaCuspStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
  positivity

def rankOneKernel (c x y : ℝ) : ℝ :=
  thetaTailFirstMomentKernel x y-c*realFeature x*realFeature y

theorem rankOneRealization_kernel_real (c x y : ℝ) :
    (rankOneRealization c).kernel (x:ℂ) (y:ℂ) = ((2*rankOneKernel c x y:ℝ):ℂ) := by
  rw [show (rankOneRealization c).kernel (x:ℂ) (y:ℂ) =
      inner ℂ (augmentedSection (y:ℂ)) (augmentedForm c (augmentedSection (x:ℂ))) from
    compressedClosedSpanRealization_kernel_eq thetaCuspStrip augmentedSection (augmentedForm c)
      isPreconnected_thetaCuspStrip isOpen_thetaCuspStrip augmentedSection_analytic_inner
      (augmentedForm_hermitian c) (real_mem_strip x) (real_mem_strip y)]
  rw [augmentedForm_apply, WithLp.prod_inner_apply]
  change inner ℂ (completeThetaSource.section (y:ℂ))
    (differenceForm (completeThetaSource.section (x:ℂ)))+
    inner ℂ (rankOneFeature (y:ℂ)) (-(2*c:ℂ)*rankOneFeature (x:ℂ)) = _
  rw [← completeThetaSource.realization_kernel (real_mem_strip x) (real_mem_strip y),
    completeThetaSource_realization_kernel, rankOneFeature_ofReal, rankOneFeature_ofReal]
  simp only [RCLike.inner_apply, Complex.conj_ofReal]
  unfold rankOneKernel
  push_cast
  ring

def rankOneTailSamples (c a : ℝ) :
    (rankOneRealization c).toAnalyticTotalSectionFamily.AccumulationSet where
  nodes := (completeThetaSource.tailAccumulationSet a).nodes
  nodes_subset := (completeThetaSource.tailAccumulationSet a).nodes_subset
  point := (completeThetaSource.tailAccumulationSet a).point
  point_mem_domain := (completeThetaSource.tailAccumulationSet a).point_mem_domain
  frequently_nodes := (completeThetaSource.tailAccumulationSet a).frequently_nodes

theorem negative_rankOne_tail_packet {c : ℝ} (hc : 0<c) (a : ℝ) :
    ∃ (S : Finset (Complex.ofReal '' Ioi a)) (b : (Complex.ofReal '' Ioi a) → ℝ),
      ∑ i ∈ S, ∑ j ∈ S, b i*b j*rankOneKernel c i.val.re j.val.re < 0 := by
  obtain ⟨x, hx⟩ := exists_negative_rankOne_diagonal hc
  have hdiag : (inner ℂ ((rankOneRealization c).kernelSection (x:ℂ))
      ((rankOneRealization c).form ((rankOneRealization c).kernelSection (x:ℂ)))).re < 0 := by
    change ((rankOneRealization c).kernel (x:ℂ) (x:ℂ)).re < 0
    rw [rankOneRealization_kernel_real]
    simp only [Complex.ofReal_re, rankOneKernel]
    nlinarith
  obtain ⟨d, hd⟩ := (rankOneRealization c).exists_negative_packet_on_accumulationSet
    (rankOneTailSamples c a) hdiag
  have hk (z w : Complex.ofReal '' Ioi a) :
      (rankOneRealization c).kernel z w = ((2*rankOneKernel c z.val.re w.val.re:ℝ):ℂ) := by
    obtain ⟨r, hr, he⟩ := z.property
    obtain ⟨s, hs, hf⟩ := w.property
    rw [← he, ← hf, Complex.ofReal_re, Complex.ofReal_re]
    exact rankOneRealization_kernel_real c r s
  change (∑ i ∈ d.support, ∑ j ∈ d.support,
    star (d j)*d i*(rankOneRealization c).kernel i j).re < 0 at hd
  simp_rw [hk] at hd
  obtain ⟨b, hb⟩ := real_packet_of_negative_complex_packet d.support
    (fun i j => rankOneKernel c i.val.re j.val.re) d hd
  exact ⟨d.support, b, hb⟩

end RHTower.ThetaTailCoercivityAudit

noncomputable section
namespace RHTower.ThetaTailCoercivityAudit
open Set Filter Topology

/-- Projection onto the extra Cauchy node 1 gives an exact rank-one lower bound. -/
theorem cauchy_rankOne_lower_bound {n : ℕ} {u : Fin n → ℝ}
    (hu : ∀ i, 0<u i) (d : Fin n → ℝ) :
    2*(∑ i, d i/(u i+1))^2 ≤ ∑ i, ∑ j, d i*d j/(u i+u j) := by
  let S := ∑ i, d i/(u i+1)
  let U : Fin (n+1) → ℝ := Fin.cons 1 u
  let D : Fin (n+1) → ℝ := Fin.cons (-2*S) d
  have hU : ∀ i, 0<U i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · norm_num [U]
    · exact hu j
  have hp := (GaloisForLFunctions.RHTower.posSemidef_cauchyMatrix hU).dotProduct_mulVec_nonneg D
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    GaloisForLFunctions.RHTower.kernelMatrix_apply, Finset.mul_sum] at hp
  have heq : (∑ i, ∑ j, D i*(GaloisForLFunctions.RHTower.cauchyKernel (U i) (U j)*D j)) =
      ∑ i, ∑ j, D i*D j/(U i+U j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold GaloisForLFunctions.RHTower.cauchyKernel
    ring
  rw [heq] at hp
  simp only [D, U, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hp
  rw [Finset.sum_add_distrib] at hp
  have hleft : (∑ j, (-2*S)*d j/(1+u j)) = -2*S*S := by
    rw [show (∑ j, (-2*S)*d j/(1+u j)) = (-2*S)*(∑ j, d j/(u j+1)) by
      rw [Finset.mul_sum Finset.univ (fun j => d j/(u j+1)) (-2*S)]
      apply Finset.sum_congr rfl
      intro j _
      rw [add_comm (1:ℝ)]
      ring]
  have hright : (∑ i, d i*(-2*S)/(u i+1)) = -2*S*S := by
    rw [show (∑ i, d i*(-2*S)/(u i+1)) = (-2*S)*(∑ i, d i/(u i+1)) by
      rw [Finset.mul_sum Finset.univ (fun j => d j/(u j+1)) (-2*S)]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [hleft, hright] at hp
  dsimp [S] at hp ⊢
  nlinarith

end RHTower.ThetaTailCoercivityAudit

noncomputable section
namespace RHTower.ThetaTailCoercivityAudit
open Set Filter Topology

private theorem enumerate_negative_packet {a : ℝ} (K : ℝ → ℝ → ℝ)
    (S : Finset (Complex.ofReal '' Ioi a)) (b : (Complex.ofReal '' Ioi a) → ℝ)
    (hb : ∑ i ∈ S, ∑ j ∈ S, b i*b j*K i.val.re j.val.re < 0) :
    ∃ (n : ℕ) (t d : Fin n → ℝ), (∀ i, a<t i) ∧
      (∑ i, ∑ j, d i*d j*K (t i) (t j)) < 0 := by
  classical
  let e := S.equivFin.symm
  let t : Fin S.card → ℝ := fun i => (e i).val.val.re
  let c : Fin S.card → ℝ := fun i => b (e i).val
  refine ⟨S.card, t, c, ?_, ?_⟩
  · intro i
    obtain ⟨r, hr, he⟩ := (e i).val.property
    change a < (e i).val.val.re
    rw [← he, Complex.ofReal_re]
    exact hr
  · have hi (z : Complex.ofReal '' Ioi a) :
        (∑ j, b z*c j*K z.val.re (t j)) =
          ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      dsimp [c, t, e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun w : S => b z*b w.val*K z.val.re w.val.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun w => b z*b w*K z.val.re w.val.re)]
    have he : (∑ i, ∑ j, c i*c j*K (t i) (t j)) =
        ∑ z ∈ S, ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      change (∑ i, ∑ j, b (e i).val*c j*K (e i).val.val.re (t j)) = _
      simp_rw [hi]
      dsimp [e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun z : S => ∑ w ∈ S, b z.val*b w*K z.val.val.re w.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun z => ∑ w ∈ S, b z*b w*K z.val.re w.val.re)]
    exact he ▸ hb

theorem exists_finite_negative_rankOne_tail {c : ℝ} (hc : 0<c) (a : ℝ) :
    ∃ (n : ℕ) (x b : Fin n → ℝ), (∀ i, a<x i) ∧
      (∑ i, ∑ j, b i*b j*rankOneKernel c (x i) (x j)) < 0 := by
  obtain ⟨S, b, hb⟩ := negative_rankOne_tail_packet hc a
  exact enumerate_negative_packet (rankOneKernel c) S b hb

def sourceCauchyKernel (x y : ℝ) : ℝ :=
  thetaCuspFullSource x*thetaCuspFullSource y/(Real.exp (2*x)+Real.exp (2*y))

theorem sourceCauchy_rankOne_lower_bound {n : ℕ} (x b : Fin n → ℝ) :
    2*(∑ i, b i*realFeature (x i))^2 ≤
      ∑ i, ∑ j, b i*b j*sourceCauchyKernel (x i) (x j) := by
  have h := cauchy_rankOne_lower_bound (fun i => Real.exp_pos (2*x i))
    (fun i => b i*thetaCuspFullSource (x i))
  have hs : (∑ i, b i*thetaCuspFullSource (x i)/(Real.exp (2*x i)+1)) =
      ∑ i, b i*realFeature (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold realFeature
    ring
  have hq : (∑ i, ∑ j, (b i*thetaCuspFullSource (x i))*(b j*thetaCuspFullSource (x j))/
      (Real.exp (2*x i)+Real.exp (2*x j))) =
      ∑ i, ∑ j, b i*b j*sourceCauchyKernel (x i) (x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold sourceCauchyKernel
    ring
  rwa [hs, hq] at h

/-- No strictly positive Cauchy-energy reserve survives at all ranks on any real tail. -/
theorem exists_finite_negative_cauchy_reserve {c : ℝ} (hc : 0<c) (a : ℝ) :
    ∃ (n : ℕ) (x b : Fin n → ℝ), (∀ i, a<x i) ∧
      (∑ i, ∑ j, b i*b j*(thetaTailFirstMomentKernel (x i) (x j)-
        c*sourceCauchyKernel (x i) (x j))) < 0 := by
  obtain ⟨n, x, b, hx, hb⟩ := exists_finite_negative_rankOne_tail (c := 2*c) (mul_pos (by norm_num) hc) a
  have hlo := sourceCauchy_rankOne_lower_bound x b
  have hid : (∑ i, ∑ j, b i*b j*rankOneKernel (2*c) (x i) (x j)) =
      (∑ i, ∑ j, b i*b j*thetaTailFirstMomentKernel (x i) (x j))-
        2*c*(∑ i, b i*realFeature (x i))^2 := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold rankOneKernel
    ring
  rw [hid] at hb
  refine ⟨n, x, b, hx, ?_⟩
  have ht : (∑ i, ∑ j, b i*b j*(thetaTailFirstMomentKernel (x i) (x j)-
      c*sourceCauchyKernel (x i) (x j))) =
      (∑ i, ∑ j, b i*b j*thetaTailFirstMomentKernel (x i) (x j))-
        c*(∑ i, ∑ j, b i*b j*sourceCauchyKernel (x i) (x j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ht]
  nlinarith [mul_le_mul_of_nonneg_left hlo hc.le]

end RHTower.ThetaTailCoercivityAudit
