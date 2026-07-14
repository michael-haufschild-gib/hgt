import GaloisForLFunctions.HTGeometry.SzegoUpperBound

/-!
# Riesz completeness forces singular Szegő collapse

For a singular circle measure, the Riesz-brothers conclusion already makes the analytic
monomials dense in `L²`.  Multiplication by the circle coordinate is a surjective isometry, so a
preimage of the constant function can be approximated by an analytic polynomial.  Shifting the
approximation gives a positive-frequency polynomial close to one.  Reversing its coefficients
produces a monic Gram competitor with the same pointwise modulus, forcing the infimum of the
monic OPUC norms to vanish.

Consequently the separate first-Szegő-limit hypothesis in the purely singular carrier trichotomy
is redundant: the exact Riesz-brothers density conclusion implies the zero determinant-ratio
limit and every downstream frame-escape conclusion.  This is a classical bridge between the two
interfaces, not a new Szegő theorem for general measures.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InnerProductSpace Filter Topology Set
open scoped ENNReal InnerProductSpace NNReal Topology ComplexConjugate

noncomputable section

private theorem circleZMulLp_surjective_aux
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    Function.Surjective (circleZMulLp mu) := by
  intro f
  have hgmem : MemLp (fun z : Circle => conj (z : ℂ) * f z) 2 mu := by
    have hconj : AEStronglyMeasurable (fun z : Circle => conj (z : ℂ)) mu := by
      have hcont : Continuous (fun z : Circle => conj (z : ℂ)) :=
        Complex.continuous_conj.comp continuous_subtype_val
      exact hcont.aestronglyMeasurable
    have hmeas : AEStronglyMeasurable (fun z : Circle => conj (z : ℂ) * f z) mu :=
      hconj.mul (Lp.aestronglyMeasurable f)
    refine ⟨hmeas, ?_⟩
    have heq : eLpNorm (fun z : Circle => conj (z : ℂ) * f z) 2 mu =
        eLpNorm (⇑f) 2 mu :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (fun z => by
        rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]))
    rw [heq]
    exact (Lp.memLp f).2
  let g : Lp ℂ 2 mu := MemLp.toLp (fun z : Circle => conj (z : ℂ) * f z) hgmem
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [circleZMulLp_coeFn_ae mu g, hgmem.coeFn_toLp] with z hz hg
  rw [hz, hg]
  change (z : ℂ) * (conj (z : ℂ) * f z) = f z
  rw [← mul_assoc, Complex.mul_conj]
  have hnormSq : Complex.normSq (z : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  rw [hnormSq]
  norm_num

private theorem exists_finsupp_sum_eq_of_mem_span_range_aux
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (v : ℕ → E) {x : E} (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    ∃ d : ℕ →₀ ℂ, d.sum (fun n c => c • v n) = x := by
  refine Submodule.span_induction (p := fun x _ =>
    ∃ d : ℕ →₀ ℂ, d.sum (fun n c => c • v n) = x) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨n, rfl⟩ := hy
    refine ⟨Finsupp.single n 1, ?_⟩
    simp
  · exact ⟨0, by simp⟩
  · intro x y hx hy hdx hdy
    obtain ⟨dx, rfl⟩ := hdx
    obtain ⟨dy, rfl⟩ := hdy
    refine ⟨dx + dy, ?_⟩
    rw [Finsupp.sum_add_index]
    · simp
    · intro a ha b₁ b₂
      exact add_smul b₁ b₂ (v a)
  · intro a x hx hdx
    obtain ⟨d, rfl⟩ := hdx
    refine ⟨a • d, ?_⟩
    rw [Finsupp.sum_smul_index]
    · change (∑ i ∈ d.support, (a * d i) • v i) =
        a • ∑ i ∈ d.support, d i • v i
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_smul]
    · intro i
      exact zero_smul ℂ (v i)

private theorem revPoly_reverseCoefficients_aux
    {N : ℕ} (d : Fin N → ℂ) (z : ℂ) :
    let c : ℕ → ℂ := fun i => if h : i < N then conj (d (Fin.rev ⟨i, h⟩)) else 0
    revPoly c N z = 1 - ∑ j : Fin N, d j * z ^ (j.1 + 1) := by
  dsimp only
  rw [revPoly, ← Fin.sum_univ_eq_sum_range]
  congr 1
  calc
    (∑ i : Fin N,
        conj (if h : (i : ℕ) < N then conj (d (Fin.rev ⟨i, h⟩)) else 0) *
          z ^ (N - (i : ℕ))) =
      ∑ i : Fin N, d (Fin.rev i) * z ^ ((Fin.rev i).1 + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dif_pos i.2, map_star]
        simp only [starRingEnd_apply, star_star]
        congr 2
        rw [Fin.val_rev]
        omega
    _ = ∑ j : Fin N, d j * z ^ (j.1 + 1) :=
      Fin.revPerm.sum_comp (fun j : Fin N => d j * z ^ (j.1 + 1))

private theorem exists_revPoly_integral_lt_of_analyticMonomialSpan_dense_aux
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hdense : (analyticMonomialSpan mu).topologicalClosure = ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K c, (∫ z : Circle, ‖revPoly c (K + 1) (z : ℂ)‖ ^ 2 ∂mu) < ε := by
  obtain ⟨g, hg⟩ := circleZMulLp_surjective_aux mu (circleMonomialLp mu 0)
  have hgcl : g ∈ closure (analyticMonomialSpan mu : Set (Lp ℂ 2 mu)) := by
    change g ∈ (analyticMonomialSpan mu).topologicalClosure
    rw [hdense]
    exact Submodule.mem_top
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨x, hxspan, hgx⟩ :=
    (Metric.mem_closure_iff.mp hgcl) (Real.sqrt ε) hsqrt
  obtain ⟨d, hd⟩ := exists_finsupp_sum_eq_of_mem_span_range_aux
    (circleMonomialLp mu) (by simpa [analyticMonomialSpan] using hxspan)
  let K : ℕ := d.support.sup id
  let N : ℕ := K + 1
  have hsupp : d.support ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup hn)
  have hsumRange :
      ∑ n ∈ d.support, d n • circleMonomialLp mu n =
        ∑ n ∈ Finset.range N, d n • circleMonomialLp mu n := by
    symm
    apply Finset.sum_subset hsupp
    intro n hnRange hnSupp
    rw [Finsupp.not_mem_support_iff.mp hnSupp, zero_smul]
  have hd' : ∑ n ∈ d.support, d n • circleMonomialLp mu n = x := by
    simpa only [Finsupp.sum] using hd
  have hdx : ∑ i : Fin N, d (i : ℕ) • circleMonomialLp mu (i : ℕ) = x := by
    rw [Fin.sum_univ_eq_sum_range, ← hsumRange, hd']
  let c : ℕ → ℂ := fun i =>
    if h : i < N then conj (d ((Fin.rev ⟨i, h⟩ : Fin N) : ℕ)) else 0
  have hxpoly : ⇑x =ᵐ[mu]
      fun z : Circle => ∑ n ∈ Finset.range N, d n * (z : ℂ) ^ n := by
    rw [← hdx, Fin.sum_univ_eq_sum_range]
    exact coeFn_sum_smul_circleMonomialLp mu (Finset.range N) d
  let f : Lp ℂ 2 mu := circleMonomialLp mu 0 - circleZMulLp mu x
  have hfpoly : ⇑f =ᵐ[mu] fun z : Circle => revPoly c N (z : ℂ) := by
    filter_upwards [Lp.coeFn_sub (circleMonomialLp mu 0) (circleZMulLp mu x),
      circleMonomialLp_coeFn_ae mu 0, circleZMulLp_coeFn_ae mu x, hxpoly] with
        z hsub hzero hshift hx
    rw [hsub, Pi.sub_apply, hzero, hshift, hx]
    simp only [pow_zero]
    rw [revPoly_reverseCoefficients_aux (fun i : Fin N => d (i : ℕ))]
    congr 1
    rw [Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_succ]
    ring
  have hintegral :
      (∫ z : Circle, ‖revPoly c N (z : ℂ)‖ ^ 2 ∂mu) = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hfpoly] with z hz
    rw [hz]
  have hnorm : ‖f‖ = dist g x := by
    calc
      ‖f‖ = ‖circleZMulLp mu g - circleZMulLp mu x‖ := by rw [f, hg]
      _ = ‖circleZMulLp mu (g - x)‖ := by
        rw [show circleZMulLp mu (g - x) =
          circleZMulLp mu g - circleZMulLp mu x from
            (circleZMulLpHom mu).map_sub g x]
      _ = ‖g - x‖ := circleZMulLp_norm mu (g - x)
      _ = dist g x := by rw [dist_eq_norm]
  refine ⟨K, c, ?_⟩
  change (∫ z : Circle, ‖revPoly c N (z : ℂ)‖ ^ 2 ∂mu) < ε
  rw [hintegral, hnorm]
  nlinarith [Real.sq_sqrt hε.le, dist_nonneg g x]

/-- Density of analytic monomials forces the infimum of the squared monic OPUC norms to be zero.
The proof constructs the required reversed-polynomial competitors explicitly. -/
theorem ciInf_normSq_gramSchmidt_eq_zero_of_analyticMonomialSpan_dense
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hdense : (analyticMonomialSpan mu).topologicalClosure = ⊤) :
    (⨅ N, ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2) = 0 := by
  have hbdd : BddBelow
      (Set.range (fun N => ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨N, rfl⟩; positivity⟩
  apply le_antisymm
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨K, c, hc⟩ :=
      exists_revPoly_integral_lt_of_analyticMonomialSpan_dense_aux mu hdense hε
    calc
      (⨅ N, ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2)
          ≤ ‖gramSchmidt ℂ (circleMonomialLp mu) (K + 1)‖ ^ 2 := ciInf_le hbdd K
      _ ≤ ∫ z : Circle, ‖revPoly c (K + 1) (z : ℂ)‖ ^ 2 ∂mu :=
        normSq_gramSchmidt_le_integral_revPoly mu (K + 1) c
      _ ≤ 0 + ε := by linarith
  · exact le_ciInf (fun N => sq_nonneg _)

/-- For a singular measure, analytic-polynomial completeness alone supplies the exact first
Szegő-limit conclusion: both the Gram infimum and the geometric mean are zero. -/
theorem hasSzegoFirstLimitConclusion_of_analyticMonomialSpan_dense_of_mutuallySingular
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hdense : (analyticMonomialSpan mu).topologicalClosure = ⊤) :
    HasSzegoFirstLimitConclusion (circleMeasureGramTower mu) mu circleLebesgue := by
  apply hasSzegoFirstLimitConclusion_of_ciInf_eq mu hmu circleLebesgue
  rw [ciInf_normSq_gramSchmidt_eq_zero_of_analyticMonomialSpan_dense mu hdense,
    szegoGeometricMean_rnDeriv_eq_zero_of_mutuallySingular mu circleLebesgue hsing]

/-- **Pure-singular carrier trichotomy from one classical circle input.**  The exact
Riesz-brothers density conclusion supplies graph saturation and analytic completeness; the latter
forces the singular Szegő limit internally.  No separate first-Szegő-limit hypothesis remains. -/
theorem pureSingularCarrier_trichotomy_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    (linearGraphSubmodule finsuppCoefficientL2
        (polynomialSynthesisL2 mu)).topologicalClosure = ⊤ ∧
      (analyticMonomialSpan mu).topologicalClosure = ⊤ ∧
      Tendsto (fun N => leastEigenvalue (circleMeasureGramTower mu N)
        (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N)) atTop (𝓝 0) ∧
      Tendsto (normalizedFrameDetRoot (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop ∧
      Tendsto (euclideanFrameOpNorm (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop := by
  have hgraph := pureSingular_graph_and_completeness_of_rieszBrothers mu hsing hriesz
  have hszego :=
    hasSzegoFirstLimitConclusion_of_analyticMonomialSpan_dense_of_mutuallySingular
      mu hmu hsing hgraph.2
  exact pureSingularCarrier_trichotomy_of_classical_inputs
    mu hmu hsing hriesz hszego

end

end GaloisForLFunctions.HTGeometry
