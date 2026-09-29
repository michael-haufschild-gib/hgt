import GaloisForLFunctions.RHTower.ThetaEndpointHarmonicCompleteness

/-!
# The exact defect index of the theta endpoint

Let `M` be the total multiplicity of the zeros of `F = XiC` in the open first quadrant (one
representative per symmetry quartet).  The closure of `span({1} ∪ V)` in `L¹_even(μ)` has codimension

`codim = 2M`  (`∞` if there are infinitely many off-line quartets).

For finitely many quartets the bounded annihilators are exactly the even `g` with
`(k g)^(z) P(z) = F(z) e(z²)`, `e` real of degree at most `2M` with `e(0) = 0`: the defect annihilators
`g_i` with `e = X^{i+1}`, `i < 2M`, are independent on `L¹_even(μ)` and cut out the closure, since every
bounded even annihilator agrees `μ`-a.e. with a combination of them (the difference has a transform
vanishing on the unit disc, hence identically).  Infinitely many quartets give, for every `n`, `n`
independent annihilators from `n` distinct quartets.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Defect annihilators -/

/-- **Defect annihilators.**  For a duplicate-free list `l` of first-quadrant zeros and
`n ≤ |L|`, there are continuous even bounded `g_i` annihilating `span({1} ∪ V)`, independent as
functions, with `(k g_i)^(z) P_L(z) = F(z) z^{2(i+1)}`. -/
theorem exists_defect_annihilators {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    (hnd : l.Nodup) {n : ℕ} (hn : n ≤ (quadrantListOf l).length) :
    ∃ g : Fin n → ℝ → ℝ, (∀ i, Continuous (g i)) ∧ (∀ i x, g i (-x) = g i x) ∧
      (∃ C, ∀ i x, |g i x| ≤ C) ∧
      (∀ i, ∀ s ∈ thetaJetOneSpan, ∫ x, g i x * s x ∂thetaSourceMeasure = 0) ∧
      (∀ i z, sourceTransform (fun x => ((thetaCuspFullSource x * g i x : ℝ) : ℂ)) z *
        listDivisor (quadrantListOf l) z = XiC z * z ^ (2 * ((i : ℕ) + 1))) ∧
      ∀ c : Fin n → ℝ, (∀ x, ∑ i, c i * g i x = 0) → c = 0 := by
  obtain ⟨v, hvc, hve, ⟨C, hvC⟩, hvT⟩ := exists_defect_sources hl hnd hn
  have hk := fun x => thetaCuspFullSource_pos x
  set g : Fin n → ℝ → ℝ := fun i x => v i x / thetaCuspFullSource x
  have hkg : ∀ i x, thetaCuspFullSource x * g i x = v i x := fun i x => by
    simp only [g]; rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (hk x).ne'
  have hgc : ∀ i, Continuous (g i) := fun i =>
    (hvc i).div contDiff_thetaCuspFullSource.continuous fun x => (hk x).ne'
  have hgb : ∀ i x, |g i x| ≤ C := fun i x => by
    simp only [g, abs_div, abs_of_pos (hk x)]
    rw [div_le_iff₀ (hk x)]; exact hvC i x
  have hge : ∀ i x, g i (-x) = g i x := fun i x => by
    simp only [g]; rw [hve i x, thetaCuspFullSource_neg]
  have hT : ∀ i z, sourceTransform (fun x => ((thetaCuspFullSource x * g i x : ℝ) : ℂ)) z *
      listDivisor (quadrantListOf l) z = XiC z * z ^ (2 * ((i : ℕ) + 1)) := fun i z => by
    simp only [hkg]; exact hvT i z
  refine ⟨g, hgc, hge, ⟨C, hgb⟩, fun i => ?_, hT, fun c hc => ?_⟩
  · have hwms := measurableMomentSource_of_le
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hvc i).aestronglyMeasurable)
      fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hvC i x
    refine (annihilates_thetaJetOneSpan_iff (hgc i).measurable (hge i) (hgb i)).2 ⟨?_, ?_⟩
    · simp only [hkg]
      exact integral_eq_zero_of_mul_eq (by omega) (hvT i)
    · have hV : (sourceTransform fun x => ((thetaCuspFullSource x * g i x : ℝ) : ℂ)) =
          sourceTransform fun x => (v i x : ℂ) := by simp only [hkg]
      rw [hV]
      exact keepsRealZeros_of_mul_eq hwms.differentiable_sourceTransform
        (by fun_prop : Differentiable ℂ fun z : ℂ => z ^ (2 * ((i : ℕ) + 1))) hl (hvT i)
  · refine defect_sources_independent hvc hvC hvT c fun x => ?_
    have h := hc x
    have : ∑ i, c i * v i x = thetaCuspFullSource x * ∑ i, c i * g i x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hkg i x]; ring
    rw [this, h, mul_zero]

/-- The pairing functionals of bounded continuous functions. -/
def boundedPairing {g : ℝ → ℝ} (hgc : Continuous g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    StrongDual ℝ ThetaL1 :=
  GaloisForLFunctions.HTGeometry.linftyPairing g hgc.stronglyMeasurable C (ae_of_all _ hgb)

theorem boundedPairing_apply {g : ℝ → ℝ} (hgc : Continuous g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C)
    (f : ThetaL1) : boundedPairing hgc hgb f = ∫ x, g x * f x ∂thetaSourceMeasure :=
  GaloisForLFunctions.HTGeometry.linftyPairing_apply _ _ _ _ f

/-- A continuous function with `∫ G² dμ = 0` vanishes identically. -/
theorem eq_zero_of_integral_mul_self_eq_zero {G : ℝ → ℝ} (hGc : Continuous G) {C : ℝ}
    (hGb : ∀ x, |G x| ≤ C) (h : ∫ x, G x * G x ∂thetaSourceMeasure = 0) : ∀ x, G x = 0 := by
  have hint : Integrable (fun x => G x * G x) thetaSourceMeasure :=
    (integrable_const (C * C)).mono' (hGc.mul hGc).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hGb x) (hGb x) (abs_nonneg _) ((abs_nonneg _).trans (hGb x)))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (G x)) hint).1 h
  have hae' : (fun x => G x * G x) =ᵐ[volume] 0 := ae_thetaSourceMeasure_iff.1 hae
  have hcont : (fun x => G x * G x) = 0 :=
    (hGc.mul hGc).ae_eq_iff_eq volume continuous_const |>.1 hae'
  intro x
  exact mul_self_eq_zero.1 (congrFun hcont x)

/-- Function-level independence of bounded continuous even functions gives independence of their
pairings on `L¹_even(μ)`. -/
theorem pairing_independent {n : ℕ} {g : Fin n → ℝ → ℝ} (hgc : ∀ i, Continuous (g i))
    (hge : ∀ i x, g i (-x) = g i x) {C : ℝ} (hgb : ∀ i x, |g i x| ≤ C)
    (hind : ∀ c : Fin n → ℝ, (∀ x, ∑ i, c i * g i x = 0) → c = 0) (c : Fin n → ℝ)
    (h : ∀ w ∈ thetaEvenL1, ∑ i, c i * boundedPairing (hgc i) (hgb i) w = 0) : c = 0 := by
  set G : ℝ → ℝ := fun x => ∑ i, c i * g i x
  have hGc : Continuous G := continuous_finsetSum _ fun i _ => continuous_const.mul (hgc i)
  set B := ∑ i, |c i| * C
  have hGb : ∀ x, |G x| ≤ B := fun x => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hgb i x) (abs_nonneg _))
  have hGe : ∀ x, G (-x) = G x := fun x => by simp only [G, hge]
  have hGL := toLp_of_bounded hGc hGb
  have h1 := h _ (toLp_mem_thetaEvenL1 hGL hGe)
  simp only [boundedPairing_apply, integral_mul_toLp] at h1
  have h2 : ∑ i, c i * ∫ x, g i x * G x ∂thetaSourceMeasure = ∫ x, G x * G x ∂thetaSourceMeasure := by
    have hint : ∀ i ∈ Finset.univ, Integrable (fun x => c i * (g i x * G x)) thetaSourceMeasure :=
      fun i _ => ((integrable_const (C * B)).mono' ((hgc i).mul hGc).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
          exact mul_le_mul (hgb i x) (hGb x) (abs_nonneg _) ((abs_nonneg _).trans (hgb i x)))).const_mul _
    have hs : ∑ i, c i * ∫ x, g i x * G x ∂thetaSourceMeasure =
        ∑ i, ∫ x, c i * (g i x * G x) ∂thetaSourceMeasure :=
      Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    rw [hs, ← integral_finsetSum _ hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [G, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2] at h1
  exact hind c (eq_zero_of_integral_mul_self_eq_zero hGc hGb h1)

/-! ## The exact defect index -/

/-- The first-quadrant multiplicity `M`: the zeros of `F` in `Re > 0, Im > 0` with multiplicity. -/
def xiQuadrantMult (hfin : xiQuadrantZeros.Finite) : ℕ := ∑ α ∈ hfin.toFinset, xiZeroMult α

theorem length_xiOffLineList (hfin : xiQuadrantZeros.Finite) :
    (xiOffLineList hfin).length = 2 * xiQuadrantMult hfin := by
  rw [xiOffLineList, length_quadrantListOf, Finset.sum_map_toList, xiQuadrantMult, Finset.mul_sum]

theorem sourceTransform_ofReal_sub {A B : ℝ → ℝ} (hA : AEStronglyMeasurable A) {CA : ℝ}
    (hAC : ∀ x, |A x| ≤ CA * thetaCuspFullSource x) (hB : AEStronglyMeasurable B) {CB : ℝ}
    (hBC : ∀ x, |B x| ≤ CB * thetaCuspFullSource x) (z : ℂ) :
    sourceTransform (fun x => ((A x - B x : ℝ) : ℂ)) z =
      sourceTransform (fun x => (A x : ℂ)) z - sourceTransform (fun x => (B x : ℂ)) z := by
  have hmA := measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hA)
    fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hAC x
  have hmB := measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hB)
    fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hBC x
  unfold sourceTransform
  rw [← integral_sub (hmA.integrable_cexp z) (hmB.integrable_cexp z)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  push_cast
  ring

theorem eval_map_eq_sum_of_coeff_zero (e : Polynomial ℝ) {N : ℕ} (hN : e.natDegree ≤ N)
    (h0 : e.coeff 0 = 0) (w : ℂ) :
    (e.map (algebraMap ℝ ℂ)).eval w = ∑ i ∈ Finset.range N, (e.coeff (i + 1) : ℂ) * w ^ (i + 1) := by
  rw [Polynomial.eval_eq_sum_range' (Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_of_le hN)) w,
    Finset.sum_range_succ']
  simp only [Polynomial.coeff_map, h0, map_zero, zero_mul, add_zero, Complex.coe_algebraMap]

/-- **Every bounded annihilator is a combination of the defect annihilators.**  In the finite case,
a bounded even `f'` annihilating `span({1} ∪ V)` agrees `μ`-a.e. with `Σ a_i g_i`. -/
theorem ae_eq_sum_defect_annihilators (hfin : xiQuadrantZeros.Finite)
    {g : Fin (2 * xiQuadrantMult hfin) → ℝ → ℝ} (hgc : ∀ i, Continuous (g i)) {C : ℝ}
    (hgb : ∀ i x, |g i x| ≤ C)
    (hgT : ∀ i z, sourceTransform (fun x => ((thetaCuspFullSource x * g i x : ℝ) : ℂ)) z *
      xiOffLineDivisor hfin z = XiC z * z ^ (2 * ((i : ℕ) + 1)))
    {f' : ℝ → ℝ} (hf'm : Measurable f') (hf'e : ∀ x, f' (-x) = f' x) {Cf : ℝ}
    (hf'b : ∀ x, |f' x| ≤ Cf)
    (hS : ∀ s ∈ thetaJetOneSpan, ∫ x, f' x * s x ∂thetaSourceMeasure = 0) :
    ∃ a : Fin (2 * xiQuadrantMult hfin) → ℝ,
      ∀ᵐ x ∂thetaSourceMeasure, f' x = ∑ i, a i * g i x := by
  obtain ⟨hmean, hkeep⟩ := (annihilates_thetaJetOneSpan_iff hf'm hf'e hf'b).1 hS
  have hvm : AEStronglyMeasurable (fun x => thetaCuspFullSource x * f' x) :=
    (contDiff_thetaCuspFullSource.continuous.measurable.mul hf'm).aestronglyMeasurable
  obtain ⟨e, he, heT⟩ := exists_realPolynomial_of_keepsRealZeros hfin hvm (source_of_bounded hf'b)
    (fun x => by simp only [thetaCuspFullSource_neg, hf'e]) hkeep
  rw [length_xiOffLineList] at he
  have he0 : e.coeff 0 = 0 := by
    have h := heT 0
    rw [xiOffLineDivisor, listDivisor_zero, mul_one, sourceTransform_zero_ofReal, hmean,
      Complex.ofReal_zero] at h
    have h2 : (e.map (algebraMap ℝ ℂ)).eval ((0 : ℂ) ^ 2) = 0 :=
      (mul_eq_zero.1 h.symm).resolve_left (XiC_ne_zero_of_norm_le_one (by simp))
    rw [zero_pow two_ne_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h2
    simpa [Complex.coe_algebraMap] using h2
  set a : Fin (2 * xiQuadrantMult hfin) → ℝ := fun i => e.coeff ((i : ℕ) + 1)
  refine ⟨a, ?_⟩
  have hk := fun x => thetaCuspFullSource_pos x
  have hkc := contDiff_thetaCuspFullSource.continuous
  set B : ℝ → ℝ := fun x => ∑ i, a i * (thetaCuspFullSource x * g i x)
  have hBc : Continuous B := continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (hkc.mul (hgc i)) :
      Continuous fun x => a i * (thetaCuspFullSource x * g i x))
  have hBm : AEStronglyMeasurable B := hBc.aestronglyMeasurable
  set CB := ∑ i, |a i| * C
  have hBC : ∀ x, |B x| ≤ CB * thetaCuspFullSource x := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_mul, abs_of_pos (hk x)]
    calc |a i| * (thetaCuspFullSource x * |g i x|) ≤ |a i| * (thetaCuspFullSource x * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgb i x) (hk x).le) (abs_nonneg _)
      _ = |a i| * C * thetaCuspFullSource x := by ring
  set D : ℝ → ℝ := fun x => thetaCuspFullSource x * f' x - B x
  have hST : ∀ z, sourceTransform (fun x => (D x : ℂ)) z =
      sourceTransform (fun x => ((thetaCuspFullSource x * f' x : ℝ) : ℂ)) z -
        ∑ i, (a i : ℂ) * sourceTransform (fun x => ((thetaCuspFullSource x * g i x : ℝ) : ℂ)) z :=
    fun z => by
      rw [sourceTransform_ofReal_sub hvm (source_of_bounded hf'b) hBm hBC]
      congr 1
      exact sourceTransform_finset_sum_ofReal (v := fun i x => thetaCuspFullSource x * g i x)
        Finset.univ (fun i _ => (hkc.mul (hgc i)).aestronglyMeasurable)
        (fun i _ => source_of_bounded (hgb i)) a z
  have hP0 : ∀ z : ℂ, ‖z‖ ≤ 1 → xiOffLineDivisor hfin z ≠ 0 := fun z hz =>
    listDivisor_quadrantListOf_ne_zero_of_norm_le_one
      (fun α hα => mem_xiOffLineList_toList hfin hα) hz
  have hSTP : ∀ z, sourceTransform (fun x => (D x : ℂ)) z * xiOffLineDivisor hfin z = 0 := by
    intro z
    rw [hST, sub_mul, heT, Finset.sum_mul]
    have hterm : ∀ i : Fin (2 * xiQuadrantMult hfin), (a i : ℂ) * sourceTransform (fun x => ((thetaCuspFullSource x *
        g i x : ℝ) : ℂ)) z * xiOffLineDivisor hfin z = XiC z * ((a i : ℂ) * (z ^ 2) ^ ((i : ℕ) + 1)) :=
      fun i => by rw [mul_assoc, hgT i z, ← pow_mul]; ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
      eval_map_eq_sum_of_coeff_zero e he he0, ← Fin.sum_univ_eq_sum_range
        (fun i => (e.coeff (i + 1) : ℂ) * (z ^ 2) ^ (i + 1)) (2 * xiQuadrantMult hfin)]
    simp only [a]
    ring
  have hdisc : ∀ z : ℂ, ‖z‖ ≤ 1 → sourceTransform (fun x => (D x : ℂ)) z = 0 := fun z hz =>
    (mul_eq_zero.1 (hSTP z)).resolve_right (hP0 z hz)
  have hDms : MeasurableMomentSource fun x => (D x : ℂ) := by
    refine measurableMomentSource_of_le
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hvm.sub hBm)) (C := Cf + CB) fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    have h1 := source_of_bounded hf'b x
    have h2 := hBC x
    nlinarith
  have hall : ∀ z, sourceTransform (fun x => (D x : ℂ)) z = 0 := by
    have hA : AnalyticOnNhd ℂ (sourceTransform fun x => (D x : ℂ)) univ :=
      fun z _ => hDms.differentiable_sourceTransform.analyticAt z
    have hev : (sourceTransform fun x => (D x : ℂ)) =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
      exact hdisc z (by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le)
    intro z
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0) hev
      (mem_univ z)
  have hD0 := ae_eq_zero_of_sourceTransform_eq_zero ((hDms.moment 0).mono'
    hDms.aestronglyMeasurable (Eventually.of_forall fun x => by simp)) hall
  refine ae_thetaSourceMeasure_iff.2 (hD0.mono fun x hx => ?_)
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero, D, B, sub_eq_zero] at hx
  have : thetaCuspFullSource x * f' x = thetaCuspFullSource x * ∑ i, a i * g i x := by
    rw [hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact mul_left_cancel₀ (hk x).ne' this

/-- **The exact defect index (1), finite case.**  With finitely many first-quadrant zeros of total
multiplicity `M`, the closure of `span({1} ∪ V)` has codimension exactly `2M` in `L¹_even(μ)`. -/
theorem finrank_thetaEndpointDefect (hfin : xiQuadrantZeros.Finite) :
    Module.finrank ℝ (thetaEvenL1 ⧸ thetaJetOneSpan.topologicalClosure.comap thetaEvenL1.subtype) =
      2 * xiQuadrantMult hfin := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  have hlen : 2 * xiQuadrantMult hfin ≤ (quadrantListOf hfin.toFinset.toList).length := by
    rw [← xiOffLineList, length_xiOffLineList]
  obtain ⟨g, hgc, hge, ⟨C, hgb⟩, hgann, hgT, hgind⟩ :=
    exists_defect_annihilators hl (nodup_xiOffLine_toList hfin) hlen
  refine GaloisForLFunctions.HTGeometry.finrank_quotient_eq_of_functionals
    (fun i => boundedPairing (hgc i) (hgb i))
    (fun i s hs => by rw [boundedPairing_apply]; exact hgann i s hs)
    (pairing_independent hgc hge hgb hgind) (fun w hw hzero => ?_)
  rw [GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty]
  intro f hfm ⟨Cf, hfC⟩ hS
  obtain ⟨f', hf'm, hf'e, hf'b, hrep⟩ := exists_even_representative hfm hfC
  have hS' : ∀ s ∈ thetaJetOneSpan, ∫ x, f' x * s x ∂thetaSourceMeasure = 0 := fun s hs => by
    rw [← hrep s (thetaJetOneSpan_le_thetaEvenL1 hs)]; exact hS s hs
  obtain ⟨a, ha⟩ := ae_eq_sum_defect_annihilators hfin hgc hgb hgT hf'm hf'e hf'b hS'
  have hint : ∀ i ∈ Finset.univ, Integrable (fun x => a i * (g i x * w x)) thetaSourceMeasure :=
    fun i _ => (integrable_bounded_mul_thetaL1 (hgc i).measurable (hgb i) w).const_mul _
  have hcomb : ∫ x, f' x * w x ∂thetaSourceMeasure =
      ∫ x, ∑ i, a i * (g i x * w x) ∂thetaSourceMeasure :=
    integral_congr_ae (ha.mono fun x hx => by
      simp only [hx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring)
  rw [hrep w hw, hcomb, integral_finsetSum _ hint]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, ← boundedPairing_apply (hgc i) (hgb i), hzero i, mul_zero]

/-- **Infinite defect.**  Infinitely many first-quadrant zeros give infinite codimension. -/
theorem not_finiteDimensional_thetaEndpointDefect (hinf : xiQuadrantZeros.Infinite) :
    ¬ FiniteDimensional ℝ
      (thetaEvenL1 ⧸ thetaJetOneSpan.topologicalClosure.comap thetaEvenL1.subtype) := by
  refine GaloisForLFunctions.HTGeometry.not_finiteDimensional_quotient_of_functionals fun n => ?_
  obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq n
  have hl : ∀ α ∈ t.toList, α ∈ xiQuadrantZeros := fun α hα => ht (Finset.mem_toList.1 hα)
  have hlen : n ≤ (quadrantListOf t.toList).length := by
    rw [length_quadrantListOf, Finset.sum_map_toList, ← hcard, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun α hα => ?_
    have := one_le_xiZeroMult (ht hα).2.2
    omega
  obtain ⟨g, hgc, hge, ⟨C, hgb⟩, hgann, -, hgind⟩ :=
    exists_defect_annihilators hl (Finset.nodup_toList t) hlen
  exact ⟨fun i => boundedPairing (hgc i) (hgb i),
    fun i s hs => by rw [boundedPairing_apply]; exact hgann i s hs,
    pairing_independent hgc hge hgb hgind⟩

/-- **The defect index (1)** in one statement: finitely many first-quadrant zeros give codimension
`2M`, infinitely many give infinite codimension; in particular RH is the zero-defect case. -/
theorem thetaEndpointDefect_eq :
    (∀ hfin : xiQuadrantZeros.Finite, Module.finrank ℝ
      (thetaEvenL1 ⧸ thetaJetOneSpan.topologicalClosure.comap thetaEvenL1.subtype) =
        2 * xiQuadrantMult hfin) ∧
    (xiQuadrantZeros.Infinite → ¬ FiniteDimensional ℝ
      (thetaEvenL1 ⧸ thetaJetOneSpan.topologicalClosure.comap thetaEvenL1.subtype)) :=
  ⟨finrank_thetaEndpointDefect, not_finiteDimensional_thetaEndpointDefect⟩

end

end RHTower
