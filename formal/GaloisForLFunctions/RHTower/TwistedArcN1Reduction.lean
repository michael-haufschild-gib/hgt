import GaloisForLFunctions.RHTower.TwistedArcGenerator

/-!
# Decay-class (N1) line witnesses from a twisted minimum principle on the modular arc

The twisted arc vectors `g_u` (`TwistedArcGenerator`) are even, satisfy `g_u(1/x) = |x| g_u(x)`,
have zero mean, log profile `O(e^{−3|v|/2})`, and strictly positive cosine transform of the log
profile.  Their integer moments are

`M_n(u) = ∫ g_u(x) cos(2π(n+2) x) dx`   (`twArcMoment n u`, frequency `arcFreq (n+1)`).

**Twisted minimum principle** (`TwistedArcMinimumPrinciple`): no finite combination
`Σ_{n<N} a_n M_n` is strictly positive on the whole arc `u ∈ [−½, ½]`.

**Theorem** (`exists_decayClass_fullLineWitness_of_twistedArcMinimumPrinciple`).  Under the twisted
minimum principle there is an even `h` with `h(1/x) = |x| h(x)`, `∫ h = 0`, log profile
`O(e^{−3|v|/2})`, strictly positive definite log profile, and `∫ h′(x) sin(2πm x) dx = 0` for every
integer `m ≥ 2`: a decay-class line witness blind at every integer `m ≥ 2`.

Proof.  By the separation theorem the twisted minimum principle puts `0` in the closed convex hull of
the first `N` moment vectors for every `N`; Prokhorov compactness of `ProbabilityMeasure [−½, ½]`
gives one probability measure `μ` annihilating every `M_n`.  Then `h = ∫ g_u dμ(u)` inherits every
property of the generators: symmetry pointwise, zero mean and the moments by Fubini, and positive
definiteness because a probability average of strictly positive continuous functions is positive.
-/

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ### Joint continuity -/

theorem continuous_arcQuadTerm_param (j : ℕ) :
    Continuous fun p : ℝ × ArcParam => arcQuadTerm (p.2 : ℝ) j p.1 := by
  have hQ : Continuous fun p : ℝ × ArcParam => arcQuad (p.2 : ℝ) p.1 := by
    unfold arcQuad; fun_prop
  have hpos : ∀ p : ℝ × ArcParam, arcQuad (p.2 : ℝ) p.1 ≠ 0 := fun p =>
    (arcQuad_pos (abs_arcParam_lt p.2) p.1).ne'
  unfold arcQuadTerm
  exact Continuous.div (hQ.rpow_const fun p => Or.inl (hpos p)) (hQ.pow j)
    fun p => pow_ne_zero _ (hpos p)

theorem continuous_arcQuadTerm_param_neg (j : ℕ) :
    Continuous fun p : ℝ × ArcParam => arcQuadTerm (-(p.2 : ℝ)) j p.1 := by
  have h := (continuous_arcQuadTerm_param j).comp
    (continuous_fst.prodMk (continuous_arcNeg.comp continuous_snd))
  exact h

theorem continuous_twArcVector_param : Continuous fun p : ℝ × ArcParam => twArcVector p.2 p.1 := by
  have h1 := continuous_arcQuadTerm_param 1
  have h2 := continuous_arcQuadTerm_param 2
  have h3 := continuous_arcQuadTerm_param 3
  have h4 := continuous_arcQuadTerm_param 4
  have g1 := continuous_arcQuadTerm_param_neg 1
  have g2 := continuous_arcQuadTerm_param_neg 2
  have g3 := continuous_arcQuadTerm_param_neg 3
  have g4 := continuous_arcQuadTerm_param_neg 4
  have hy : Continuous fun p : ℝ × ArcParam => Real.sqrt (modularArcHeight p.2) := by
    unfold modularArcHeight; fun_prop
  unfold twArcVector twPointVec
  fun_prop

theorem continuous_twArcDeriv_param : Continuous fun p : ℝ × ArcParam => twArcDeriv p.2 p.1 := by
  have h1 := continuous_arcQuadTerm_param 1
  have h2 := continuous_arcQuadTerm_param 2
  have h3 := continuous_arcQuadTerm_param 3
  have h4 := continuous_arcQuadTerm_param 4
  have h5 := continuous_arcQuadTerm_param 5
  have g1 := continuous_arcQuadTerm_param_neg 1
  have g2 := continuous_arcQuadTerm_param_neg 2
  have g3 := continuous_arcQuadTerm_param_neg 3
  have g4 := continuous_arcQuadTerm_param_neg 4
  have g5 := continuous_arcQuadTerm_param_neg 5
  have hy : Continuous fun p : ℝ × ArcParam => Real.sqrt (modularArcHeight p.2) := by
    unfold modularArcHeight; fun_prop
  unfold twArcDeriv twPointDeriv
  fun_prop

/-! ### The moments -/

/-- `M_n(u) = ∫ g_u(x) cos(2π(n+2)x) dx`. -/
def twArcMoment (n : ℕ) (u : ArcParam) : ℝ :=
  ∫ x, twArcVector u x * Real.cos (arcFreq (n + 1) * x)

theorem abs_twArcVector_mul_cos_le (ω : ℝ) (u : ArcParam) (x : ℝ) :
    |twArcVector u x * Real.cos (ω * x)| ≤ 9000 * (1 + x ^ 2)⁻¹ := by
  rw [abs_mul]
  exact (mul_le_mul (abs_twArcVector_le u x) (Real.abs_cos_le_one _) (abs_nonneg _)
    (by positivity)).trans (by rw [mul_one])

theorem continuous_twArcMoment (n : ℕ) : Continuous (twArcMoment n) := by
  unfold twArcMoment
  refine continuous_of_dominated (bound := fun x => 9000 * (1 + x ^ 2)⁻¹) (fun u => ?_)
    (fun u => Eventually.of_forall fun x => ?_) (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall fun x => ?_)
  · exact ((continuous_twArcVector u).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_twArcVector_mul_cos_le _ u x
  · exact (continuous_twArcVector_param.comp (continuous_const.prodMk continuous_id)).mul
      continuous_const

/-- The moment `M_n` as a bounded continuous function on the compact arc. -/
def twArcMomentBCF (n : ℕ) : ArcParam →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨twArcMoment n, continuous_twArcMoment n⟩

/-- **The twisted minimum principle**: no finite combination of the twisted moments is strictly
positive on the whole arc. -/
def TwistedArcMinimumPrinciple : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ), ¬ ∀ u : ArcParam, 0 < ∑ i, a i * twArcMoment i u

/-! ### Separation and Prokhorov -/

/-- A continuous linear functional on `ℝ^N` is a weighted sum of coordinates. -/
theorem strongDual_apply_eq_sum {N : ℕ} (f : StrongDual ℝ (Fin N → ℝ)) (x : Fin N → ℝ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ (f.toLinearMap) x
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j; simp [Pi.single_apply, eq_comm]

/-- **Finite stage**: the first `N` twisted moments of some probability measure are `δ`-small. -/
theorem exists_probabilityMeasure_twArc_small (hM : TwistedArcMinimumPrinciple) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ μ : ProbabilityMeasure ArcParam, ∀ n < N,
      |∫ u, twArcMomentBCF n u ∂(μ : Measure ArcParam)| ≤ δ := by
  set Φ : ArcParam → (Fin N → ℝ) := fun u i => twArcMoment i u with hΦ
  set C := closure (convexHull ℝ (range Φ)) with hC
  by_cases h0 : (0 : Fin N → ℝ) ∈ C
  · obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp h0 δ hδ
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hp
    choose u hu using hz
    set μ₀ : Measure ArcParam := ∑ i, (ENNReal.ofReal (w i)) • Measure.dirac (u i) with hμ₀
    have hprob : IsProbabilityMeasure μ₀ := by
      constructor
      rw [hμ₀, Measure.coe_finsetSum, Finset.sum_apply]
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
    refine ⟨⟨μ₀, hprob⟩, fun n hn => ?_⟩
    have hpn : ‖p‖ < δ := by simpa [dist_comm] using hdist
    have hp1 : p ⟨n, hn⟩ = ∑ i, w i * twArcMomentBCF n (u i) := by
      rw [← hsum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hu i]
      rfl
    have hb : |p ⟨n, hn⟩| ≤ ‖p‖ :=
      (norm_le_pi_norm p ⟨n, hn⟩).trans_eq' (Real.norm_eq_abs _).symm
    change |∫ x, twArcMomentBCF n x ∂μ₀| ≤ δ
    rw [hμ₀, integral_sum_dirac w hw0 u, ← hp1]
    linarith
  · exfalso
    obtain ⟨f, s, hf0, hfC⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (range Φ)).closure isClosed_closure h0
    rw [map_zero] at hf0
    have hpos : ∀ u : ArcParam, s < f (Φ u) := fun u =>
      hfC _ (subset_closure (subset_convexHull ℝ _ (mem_range_self u)))
    refine hM N (fun i => f (Pi.single i 1)) fun u => ?_
    have := hf0.trans (hpos u)
    rw [strongDual_apply_eq_sum] at this
    simpa [hΦ, mul_comm] using this

/-- **A probability measure on the arc annihilating every twisted moment.** -/
theorem exists_probabilityMeasure_twArc_annihilating (hM : TwistedArcMinimumPrinciple) :
    ∃ μ : ProbabilityMeasure ArcParam, ∀ n : ℕ,
      ∫ u, twArcMoment n u ∂(μ : Measure ArcParam) = 0 := by
  set T : ℕ → Set (ProbabilityMeasure ArcParam) := fun k =>
    {μ | ∀ n < k, |∫ u, twArcMomentBCF n u ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)} with hT
  have hclosed : ∀ k, IsClosed (T k) := by
    intro k
    have hc : ∀ g : ArcParam →ᵇ ℝ, Continuous fun μ : ProbabilityMeasure ArcParam =>
        |∫ u, g u ∂(μ : Measure ArcParam)| := fun g =>
      continuous_abs.comp (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g)
    have : T k = ⋂ n ∈ Finset.range k, {μ : ProbabilityMeasure ArcParam |
        |∫ u, twArcMomentBCF n u ∂(μ : Measure ArcParam)| ≤ 1 / ((k : ℝ) + 1)} := by
      ext μ
      simp [hT, Finset.mem_range]
    rw [this]
    exact isClosed_biInter fun n _ => isClosed_le (hc _) continuous_const
  have hmono : ∀ k, T (k + 1) ⊆ T k := by
    intro k μ hμ n hn
    have h := hμ n (by omega)
    have hle : 1 / ((↑(k + 1) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith
    exact h.trans hle
  have hne : ∀ k, (T k).Nonempty := fun k =>
    exists_probabilityMeasure_twArc_small hM k (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne
    ((hclosed 0).isCompact) hclosed
  rw [mem_iInter] at hμ
  refine ⟨μ, fun n => ?_⟩
  by_contra hne0
  have hpos : 0 < |∫ u, twArcMomentBCF n u ∂(μ : Measure ArcParam)| := abs_pos.mpr hne0
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  have := hμ (k + n + 1) n (by omega)
  have hle : 1 / ((↑(k + n + 1) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  linarith

/-! ### The averaged witness -/

/-- A function with `|f(x)| ≤ C/(1 + x²)` and `f(1/x) = |x| f(x)` has log profile `≤ C e^{−3|v|/2}`. -/
theorem abs_exp_half_mul_le_of_inv {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C * (1 + x ^ 2)⁻¹)
    (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) (v : ℝ) :
    |Real.exp (v / 2) * f (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2)) := by
  have key : ∀ w, 0 ≤ w → |Real.exp (w / 2) * f (Real.exp w)| ≤ C * Real.exp (-(3 * w / 2)) := by
    intro w hw
    have hC0 : 0 ≤ C := by
      have := (abs_nonneg _).trans (hC 0); nlinarith [inv_pos.mpr (by positivity : (0 : ℝ) < 1 + 0 ^ 2)]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := hC (Real.exp w)
    have h2 : (1 + Real.exp w ^ 2)⁻¹ ≤ Real.exp (-(2 * w)) := by
      rw [Real.exp_neg, ← Real.exp_nat_mul]
      apply inv_anti₀ (Real.exp_pos _)
      push_cast; rw [mul_comm]; linarith
    calc Real.exp (w / 2) * |f (Real.exp w)| ≤ Real.exp (w / 2) * (C * Real.exp (-(2 * w))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hC0))
            (Real.exp_pos _).le
      _ = C * (Real.exp (w / 2) * Real.exp (-(2 * w))) := by ring
      _ = C * Real.exp (-(3 * w / 2)) := by rw [← Real.exp_add]; congr 2; ring
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]; exact key v hv
  · have e : f (Real.exp v) = Real.exp (-v) * f (Real.exp (-v)) := by
      have := hinv (Real.exp (-v)) (Real.exp_pos _).ne'
      rw [one_div, ← Real.exp_neg, neg_neg, abs_of_pos (Real.exp_pos _)] at this
      exact this
    have e2 : Real.exp (v / 2) * f (Real.exp v) = Real.exp (-v / 2) * f (Real.exp (-v)) := by
      rw [e, ← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e2, abs_of_nonpos hv]
    have := key (-v) (by linarith)
    convert this using 3

theorem abs_exp_half_mul_twArcVector_le (u : ArcParam) (v : ℝ) :
    |Real.exp (v / 2) * twArcVector u (Real.exp v)| ≤ 9000 * Real.exp (-(3 * |v| / 2)) :=
  abs_exp_half_mul_le_of_inv (abs_twArcVector_le u) (fun _ hx => twArcVector_inv u hx) v

/-- The averaged witness `h = ∫ g_u dμ(u)`. -/
def twWitness (μ : Measure ArcParam) (x : ℝ) : ℝ := ∫ u, twArcVector u x ∂μ

/-- Its derivative `∫ g_u′ dμ(u)`. -/
def twWitnessDeriv (μ : Measure ArcParam) (x : ℝ) : ℝ := ∫ u, twArcDeriv u x ∂μ

theorem continuous_twArcVector_at (x : ℝ) : Continuous fun u : ArcParam => twArcVector u x :=
  continuous_twArcVector_param.comp (continuous_const.prodMk continuous_id)

theorem continuous_twArcDeriv_at (x : ℝ) : Continuous fun u : ArcParam => twArcDeriv u x :=
  continuous_twArcDeriv_param.comp (continuous_const.prodMk continuous_id)

theorem hasDerivAt_twWitness (μ : Measure ArcParam) [IsFiniteMeasure μ] (x : ℝ) :
    HasDerivAt (twWitness μ) (twWitnessDeriv μ x) x := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (x : ℝ) (u : ArcParam) => twArcVector u x)
    (F' := fun x u => twArcDeriv u x) (x₀ := x) (bound := fun _ => 260000)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' => (continuous_twArcVector_at x').aestronglyMeasurable)
    (integrable_of_continuous_arc (continuous_twArcVector_at x))
    (continuous_twArcDeriv_at x).aestronglyMeasurable
    (Eventually.of_forall fun u x' _ => by
      rw [Real.norm_eq_abs]
      calc |twArcDeriv u x'| ≤ 260000 * (1 + x' ^ 2)⁻¹ := abs_twArcDeriv_le u x'
        _ ≤ 260000 * 1 := by
            gcongr; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x'])
        _ = 260000 := mul_one _)
    (integrable_const _)
    (Eventually.of_forall fun u x' _ => hasDerivAt_twArcVector u x')
  exact key.2

theorem abs_twWitness_le (μ : ProbabilityMeasure ArcParam) (x : ℝ) :
    |twWitness μ x| ≤ 9000 * (1 + x ^ 2)⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure ArcParam))
    (f := fun u => twArcVector u x) (C := 9000 * (1 + x ^ 2)⁻¹)
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact abs_twArcVector_le u x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem abs_twWitnessDeriv_le (μ : ProbabilityMeasure ArcParam) (x : ℝ) :
    |twWitnessDeriv μ x| ≤ 260000 * (1 + x ^ 2)⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure ArcParam))
    (f := fun u => twArcDeriv u x) (C := 260000 * (1 + x ^ 2)⁻¹)
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact abs_twArcDeriv_le u x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem continuous_twWitness (μ : ProbabilityMeasure ArcParam) : Continuous (twWitness μ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_twWitness (μ : Measure ArcParam) x).continuousAt

theorem continuous_twWitnessDeriv (μ : ProbabilityMeasure ArcParam) :
    Continuous (twWitnessDeriv μ) := by
  unfold twWitnessDeriv
  refine continuous_of_dominated (bound := fun _ => 260000) (fun x => ?_)
    (fun x => Eventually.of_forall fun u => ?_) (integrable_const _)
    (Eventually.of_forall fun u => ?_)
  · exact (continuous_twArcDeriv_at x).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    calc |twArcDeriv u x| ≤ 260000 * (1 + x ^ 2)⁻¹ := abs_twArcDeriv_le u x
      _ ≤ 260000 * 1 := by
          gcongr; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      _ = 260000 := mul_one _
  · exact continuous_twArcDeriv u

/-- Product integrability of a kernel dominated by `C (1 + x²)⁻¹`. -/
theorem integrable_prod_of_le {μ : Measure ArcParam} [IsFiniteMeasure μ] {F : ℝ → ArcParam → ℝ}
    (hF : Continuous fun p : ℝ × ArcParam => F p.1 p.2) {C : ℝ}
    (hC : ∀ x u, |F x u| ≤ C * (1 + x ^ 2)⁻¹) :
    Integrable (Function.uncurry F) ((volume : Measure ℝ).prod μ) := by
  have hI : Integrable (fun z : ℝ × ArcParam => (C * (1 + z.1 ^ 2)⁻¹) * (1 : ℝ))
      ((volume : Measure ℝ).prod μ) :=
    (integrable_inv_one_add_sq.const_mul C).mul_prod (integrable_const (1 : ℝ))
  refine hI.mono' hF.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, mul_one]
  exact hC z.1 z.2

theorem twWitness_neg (μ : Measure ArcParam) (x : ℝ) : twWitness μ (-x) = twWitness μ x := by
  unfold twWitness; simp_rw [twArcVector_neg]

theorem twWitness_inv (μ : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    twWitness μ (1 / x) = |x| * twWitness μ x := by
  unfold twWitness; simp_rw [twArcVector_inv _ hx]; rw [integral_const_mul]

theorem integral_twWitness_eq_zero (μ : ProbabilityMeasure ArcParam) :
    ∫ x, twWitness μ x = 0 := by
  unfold twWitness
  rw [integral_integral_swap (integrable_prod_of_le (F := fun x u => twArcVector u x)
    continuous_twArcVector_param (fun x u => abs_twArcVector_le u x))]
  simp_rw [integral_twArcVector_eq_zero, integral_zero]

theorem integral_twWitnessDeriv_mul_sin (μ : ProbabilityMeasure ArcParam) (ω : ℝ) :
    ∫ x, twWitnessDeriv μ x * Real.sin (ω * x) =
      -(ω * ∫ u, (∫ x, twArcVector u x * Real.cos (ω * x)) ∂(μ : Measure ArcParam)) := by
  unfold twWitnessDeriv
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap (integrable_prod_of_le
    (F := fun x u => twArcDeriv u x * Real.sin (ω * x)) (C := 260000)
    (continuous_twArcDeriv_param.mul (by fun_prop))
    (fun x u => by
      rw [abs_mul]
      exact (mul_le_mul (abs_twArcDeriv_le u x) (Real.abs_sin_le_one _) (abs_nonneg _)
        (by positivity)).trans (by rw [mul_one])))]
  simp_rw [integral_twArcDeriv_mul_sin]
  rw [integral_neg, integral_const_mul]

theorem integral_cos_mul_twWitnessProfile_pos (μ : ProbabilityMeasure ArcParam) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twWitness μ (Real.exp v)) := by
  have hb : Integrable fun v : ℝ => 9000 * Real.exp (-(3 / 2 * |v|)) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 9000
  have hbound : ∀ u : ArcParam, ∀ v : ℝ,
      |Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v))| ≤
        9000 * Real.exp (-(3 / 2 * |v|)) := fun u v => by
    rw [abs_mul]
    refine (mul_le_mul (Real.abs_cos_le_one _) (abs_exp_half_mul_twArcVector_le u v)
      (abs_nonneg _) zero_le_one).trans ?_
    rw [one_mul]; apply le_of_eq; congr 2; ring
  have hcont : Continuous fun p : ℝ × ArcParam =>
      Real.cos (τ * p.1) * (Real.exp (p.1 / 2) * twArcVector p.2 (Real.exp p.1)) := by
    have := continuous_twArcVector_param.comp
      ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd)
    exact (by fun_prop : Continuous fun p : ℝ × ArcParam => Real.cos (τ * p.1)).mul
      ((by fun_prop : Continuous fun p : ℝ × ArcParam => Real.exp (p.1 / 2)).mul this)
  have hprod : Integrable (Function.uncurry fun v (u : ArcParam) =>
      Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v)))
      ((volume : Measure ℝ).prod (μ : Measure ArcParam)) := by
    have hI : Integrable (fun z : ℝ × ArcParam => (9000 * Real.exp (-(3 / 2 * |z.1|))) * (1 : ℝ))
        ((volume : Measure ℝ).prod (μ : Measure ArcParam)) := hb.mul_prod (integrable_const _)
    refine hI.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, mul_one]
    exact hbound z.2 z.1
  have e : ∀ v, Real.cos (τ * v) * (Real.exp (v / 2) * twWitness μ (Real.exp v)) =
      ∫ u, Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v))
        ∂(μ : Measure ArcParam) := fun v => by
    unfold twWitness
    rw [integral_const_mul, integral_const_mul]
  simp_rw [e]
  rw [integral_integral_swap hprod]
  set P : ArcParam → ℝ := fun u =>
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v)) with hP
  have hPpos : ∀ u, 0 < P u := fun u => integral_cos_mul_twArcProfile_pos u τ
  have hPc : Continuous P := by
    refine continuous_of_dominated (bound := fun v => 9000 * Real.exp (-(3 / 2 * |v|)))
      (fun u => ?_) (fun u => Eventually.of_forall fun v => ?_) hb
      (Eventually.of_forall fun v => ?_)
    · exact (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hbound u v
    · exact hcont.comp (continuous_const.prodMk continuous_id)
  rw [integral_pos_iff_support_of_nonneg (fun u => (hPpos u).le)
    (integrable_of_continuous_arc hPc)]
  have hsupp : Function.support P = univ :=
    eq_univ_of_forall fun u => (hPpos u).ne'
  rw [hsupp, measure_univ]
  exact one_pos

/-- **Decay-class (N1) line witnesses from the twisted minimum principle on the modular arc.** -/
theorem exists_decayClass_fullLineWitness_of_twistedArcMinimumPrinciple
    (hM : TwistedArcMinimumPrinciple) :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating hM
  refine ⟨twWitness μ, twWitnessDeriv μ, hasDerivAt_twWitness (μ : Measure ArcParam),
    integrable_of_le_inv_one_add_sq (continuous_twWitness μ) (abs_twWitness_le μ),
    integrable_of_le_inv_one_add_sq (continuous_twWitnessDeriv μ) (abs_twWitnessDeriv_le μ),
    twWitness_neg _, fun x hx => twWitness_inv _ hx, integral_twWitness_eq_zero μ,
    ⟨9000, abs_exp_half_mul_le_of_inv (abs_twWitness_le μ) (fun _ hx => twWitness_inv _ hx)⟩,
    fun n => ?_, integral_cos_mul_twWitnessProfile_pos μ⟩
  rw [integral_twWitnessDeriv_mul_sin]
  have := hμ n
  unfold twArcMoment at this
  rw [this, mul_zero, neg_zero]

end

end RHTower
