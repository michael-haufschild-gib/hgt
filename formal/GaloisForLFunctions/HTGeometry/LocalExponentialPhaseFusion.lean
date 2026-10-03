import GaloisForLFunctions.HTGeometry.LocalExponentialSignConeConverse

/-!
# Rational-phase closure and phase/Hankel/source fusion

* **Fourier uniqueness.**  A square-integrable density on a finite measure whose Fourier transform
  vanishes is zero: its Jordan parts are finite measures with equal characteristic functions.
* **Lemma 4.1.**  The rational phases `x ↦ e^{-iqx}`, `q ∈ ℚ`, span a dense subspace of `L²(μ;ℂ)` for
  every finite measure: a density orthogonal to them has a continuous Fourier transform vanishing on
  `ℚ`, hence everywhere.
* **Theorem 4.2 (LEF.15).**  For a bounded Hermitian matrix density, positivity almost everywhere,
  positivity of every block Hankel section and positivity of the phase test on every finite
  rational phase packet are equivalent.
* The half-line window **(LEF.2)** implies the bilateral window **(LEF.1)**.
-/

namespace HTGeometry

open MeasureTheory Complex Filter Topology
open scoped Matrix ComplexOrder InnerProductSpace

/-! ## The half-line window -/

/-- **(LEF.2) ⇒ (LEF.1)** On a finite measure supported in `[b, ∞)`, one positive exponential moment
gives the bilateral window: `e^{a|x|} ≤ e^{ax} + e^{-ab}` on the support. -/
theorem integrable_exp_abs_of_halfLine {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ᵐ x ∂μ, b ≤ x) (hexp : Integrable (fun x => Real.exp (a * x)) μ) :
    Integrable (fun x => Real.exp (a * |x|)) μ := by
  refine (hexp.add (integrable_const (Real.exp (-(a * b))))).mono' (by fun_prop) ?_
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  show Real.exp (a * |x|) ≤ Real.exp (a * x) + Real.exp (-(a * b))
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0]
    linarith [Real.exp_pos (-(a * b))]
  · rw [abs_of_nonpos h0]
    have : Real.exp (a * -x) ≤ Real.exp (-(a * b)) := Real.exp_le_exp.2 (by nlinarith)
    linarith [Real.exp_pos (a * x)]

/-- **Theorem 2.1 under (LEF.2).**  On a finite measure supported in `[b, ∞)` with one positive
exponential moment, the polynomials are dense in `L²(μ;ℂ)`. -/
theorem dense_polySubmodule_of_halfLine {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ᵐ x ∂μ, b ≤ x) (hexp : Integrable (fun x => Real.exp (a * x)) μ) :
    Dense ((polySubmodule ha (integrable_exp_abs_of_halfLine ha hsupp hexp) :
      Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  dense_polySubmodule ha _

/-! ## Fourier uniqueness for square-integrable densities -/

section Fourier

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- A real square-integrable density with vanishing Fourier transform vanishes almost everywhere. -/
theorem ae_eq_zero_of_forall_fourier_eq_zero {f : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hF : ∀ t : ℝ, ∫ x, Complex.exp (t * x * I) * (f x : ℂ) ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hfm : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hpm : AEMeasurable (posWeight f) μ := hfm.real_toNNReal
  have hnm : AEMeasurable (negWeight f) μ := hfm.neg.real_toNNReal
  set νp : Measure ℝ := μ.withDensity (fun x => ((posWeight f x : NNReal) : ENNReal)) with hνp
  set νn : Measure ℝ := μ.withDensity (fun x => ((negWeight f x : NNReal) : ENNReal)) with hνn
  haveI hfinp : IsFiniteMeasure νp := isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hfint)
  haveI hfinn : IsFiniteMeasure νn :=
    isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hfint.neg)
  have hpint : Integrable (fun x => ((posWeight f x : NNReal) : ℝ)) μ := by
    refine hfint.abs.mono' hpm.coe_nnreal_real.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (posWeight f x).coe_nonneg, coe_posWeight]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnint : Integrable (fun x => ((negWeight f x : NNReal) : ℝ)) μ := by
    refine hfint.abs.mono' hnm.coe_nnreal_real.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (negWeight f x).coe_nonneg, coe_negWeight]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hexpint : ∀ t : ℝ, ∀ {w : ℝ → ℝ}, Integrable w μ →
      Integrable (fun x : ℝ => Complex.exp (t * x * I) * (w x : ℂ)) μ := fun t w hw => by
    refine (hw.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hchar : ∀ t : ℝ, charFun νp t = charFun νn t := by
    intro t
    rw [charFun_apply_real, charFun_apply_real, hνp, hνn, integral_withDensity_eq_integral_smul₀ hpm,
      integral_withDensity_eq_integral_smul₀ hnm, ← sub_eq_zero]
    have h1 : (fun x : ℝ => (posWeight f x : NNReal) • Complex.exp (t * x * I)) =
        fun x : ℝ => Complex.exp (t * x * I) * ((posWeight f x : NNReal) : ℝ) := by
      funext x
      rw [NNReal.smul_def, Complex.real_smul, mul_comm]
    have h2 : (fun x : ℝ => (negWeight f x : NNReal) • Complex.exp (t * x * I)) =
        fun x : ℝ => Complex.exp (t * x * I) * ((negWeight f x : NNReal) : ℝ) := by
      funext x
      rw [NNReal.smul_def, Complex.real_smul, mul_comm]
    rw [h1, h2, ← integral_sub (hexpint t hpint) (hexpint t hnint), ← hF t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_sub, ← Complex.ofReal_sub, coe_posWeight_sub_coe_negWeight]
  have hEq : νp = νn := Measure.ext_of_charFun (funext hchar)
  have hdens : (fun x => ((posWeight f x : NNReal) : ENNReal))
      =ᵐ[μ] fun x => ((negWeight f x : NNReal) : ENNReal) :=
    (withDensity_eq_iff hpm.coe_nnreal_ennreal hnm.coe_nnreal_ennreal
      (lintegral_toNNReal_ne_top hfint)).mp hEq
  filter_upwards [hdens] with x hx
  have hxr : ((posWeight f x : NNReal) : ℝ) = ((negWeight f x : NNReal) : ℝ) := by
    exact_mod_cast congrArg ENNReal.toNNReal hx
  have := coe_posWeight_sub_coe_negWeight f x
  rw [hxr, sub_self] at this
  simpa using this.symm

/-- A complex square-integrable density with vanishing Fourier transform vanishes almost
everywhere: the transforms of `Re f` and `Im f` are combinations of the transform of `f` at `±t`. -/
theorem ae_eq_zero_of_forall_complex_fourier_eq_zero {f : ℝ → ℂ} (hf : MemLp f 2 μ)
    (hF : ∀ t : ℝ, ∫ x, Complex.exp (t * x * I) * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hfint : Integrable f μ := hf.integrable (by norm_num)
  have hfc : Integrable (fun x => starRingEnd ℂ (f x)) μ :=
    hfint.mono (Complex.continuous_conj.comp_aestronglyMeasurable hfint.1)
      (Eventually.of_forall fun x => by rw [Complex.norm_conj])
  have hint : ∀ t : ℝ, Integrable (fun x : ℝ => Complex.exp (t * x * I) * f x) μ := fun t => by
    refine hfint.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hconj : ∀ t : ℝ, ∫ x, Complex.exp (t * x * I) * starRingEnd ℂ (f x) ∂μ = 0 := fun t => by
    have h := congrArg (starRingEnd ℂ) (hF (-t))
    rw [← integral_conj, map_zero] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have hre : ∀ t : ℝ, ∫ x, Complex.exp (t * x * I) * ((f x).re : ℂ) ∂μ = 0 := fun t => by
    have h : (fun x : ℝ => Complex.exp (t * x * I) * ((f x).re : ℂ)) =
        fun x : ℝ => (1 / 2 : ℂ) * (Complex.exp (t * x * I) * f x + Complex.exp (t * x * I) * starRingEnd ℂ (f x)) := by
      funext x
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
    have hc : Integrable (fun x : ℝ => Complex.exp (t * x * I) * starRingEnd ℂ (f x)) μ := by
      refine hfc.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Complex.norm_exp]
      simp
    rw [h, integral_const_mul, integral_add (hint t) hc, hF t, hconj t, add_zero, mul_zero]
  have him : ∀ t : ℝ, ∫ x, Complex.exp (t * x * I) * ((f x).im : ℂ) ∂μ = 0 := fun t => by
    have h : (fun x : ℝ => Complex.exp (t * x * I) * ((f x).im : ℂ)) =
        fun x : ℝ => (1 / (2 * I)) * (Complex.exp (t * x * I) * f x - Complex.exp (t * x * I) * starRingEnd ℂ (f x)) := by
      funext x
      rw [← mul_sub, Complex.sub_conj]
      field_simp
      push_cast
      ring
    have hc : Integrable (fun x : ℝ => Complex.exp (t * x * I) * starRingEnd ℂ (f x)) μ := by
      refine hfc.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Complex.norm_exp]
      simp
    rw [h, integral_const_mul, integral_sub (hint t) hc, hF t, hconj t, sub_zero, mul_zero]
  have hrez := ae_eq_zero_of_forall_fourier_eq_zero hf.re hre
  have himz := ae_eq_zero_of_forall_fourier_eq_zero hf.im him
  filter_upwards [hrez, himz] with x hx hy
  exact Complex.ext hx hy

end Fourier

/-! ## Lemma 4.1: rational phases are dense -/

section PhaseDensity

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The phase `x ↦ e^{-iqx}`. -/
noncomputable def phaseFn (q : ℝ) (x : ℝ) : ℂ := Complex.exp (-((q : ℂ) * x * I))

theorem norm_phaseFn (q x : ℝ) : ‖phaseFn q x‖ = 1 := by
  rw [phaseFn, Complex.norm_exp]
  simp

theorem continuous_phaseFn (q : ℝ) : Continuous (phaseFn q) := by
  unfold phaseFn
  fun_prop

theorem conj_phaseFn (q x : ℝ) : starRingEnd ℂ (phaseFn q x) = Complex.exp ((q : ℂ) * x * I) := by
  rw [phaseFn, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem memLp_phaseFn (q : ℝ) : MemLp (phaseFn q) 2 μ :=
  MemLp.of_bound (continuous_phaseFn q).aestronglyMeasurable 1
    (Eventually.of_forall fun x => (norm_phaseFn q x).le)

/-- The rational phase `e^{-iqx}`, `q ∈ ℚ`, as an element of `L²(μ;ℂ)`. -/
noncomputable def phaseLp (q : ℚ) : Lp ℂ 2 μ := (memLp_phaseFn (μ := μ) q).toLp _

theorem coeFn_phaseLp (q : ℚ) : (phaseLp (μ := μ) q : ℝ → ℂ) =ᵐ[μ] phaseFn q :=
  MemLp.coeFn_toLp _

/-- The span of the rational phases in `L²(μ;ℂ)`. -/
noncomputable def phaseSubmodule : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ (Set.range (phaseLp (μ := μ)))

omit [IsFiniteMeasure μ] in
theorem continuous_fourierDensity {f : ℝ → ℂ} (hf : Integrable f μ) :
    Continuous fun t : ℝ => ∫ x, Complex.exp (t * x * I) * f x ∂μ := by
  refine continuous_of_dominated (bound := fun x => ‖f x‖) (fun t => ?_) (fun t => ?_) hf.norm ?_
  · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * I)).aestronglyMeasurable.mul hf.1
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  · exact Eventually.of_forall fun x => by fun_prop

/-- **Lemma 4.1 in Hilbert form.**  The rational phases have trivial orthogonal complement in
`L²(μ;ℂ)` for every finite measure. -/
theorem phaseSubmodule_orthogonal : (phaseSubmodule (μ := μ))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf => ?_
  have hfint : Integrable (f : ℝ → ℂ) μ := (Lp.memLp f).integrable (by norm_num)
  have hrat : ∀ q : ℚ, ∫ x, Complex.exp ((q : ℝ) * x * I) * (f : ℝ → ℂ) x ∂μ = 0 := by
    intro q
    have h := (Submodule.mem_orthogonal _ f).mp hf (phaseLp q) (Submodule.subset_span ⟨q, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_phaseLp (μ := μ) q] with x hx
    rw [hx, RCLike.inner_apply, conj_phaseFn]
    ring
  have hzero : (fun t : ℝ => ∫ x, Complex.exp (t * x * I) * (f : ℝ → ℂ) x ∂μ) = fun _ => 0 :=
    Continuous.ext_on Rat.denseRange_cast (continuous_fourierDensity hfint) continuous_const
      (by rintro _ ⟨q, rfl⟩; exact hrat q)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_complex_fourier_eq_zero (Lp.memLp f) fun t => congrFun hzero t)

/-- **Lemma 4.1.**  The rational phases are dense in `L²(μ;ℂ)`. -/
theorem dense_phaseSubmodule :
    Dense ((phaseSubmodule (μ := μ) : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr phaseSubmodule_orthogonal)

/-- Every element of the phase span is almost everywhere a finite rational trigonometric
polynomial. -/
theorem exists_phase_of_mem_phaseSubmodule {f : Lp ℂ 2 μ} (hf : f ∈ phaseSubmodule (μ := μ)) :
    ∃ (r : ℕ) (q : Fin r → ℚ) (c : Fin r → ℂ),
      (f : ℝ → ℂ) =ᵐ[μ] fun x => ∑ j, c j * phaseFn (q j) x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨q, rfl⟩ := hg
      refine ⟨1, fun _ => q, fun _ => 1, ?_⟩
      filter_upwards [coeFn_phaseLp (μ := μ) q] with x hx
      rw [hx]
      simp
  | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
      rw [hx]
      simp
  | add g h _ _ ihg ihh =>
      obtain ⟨r₁, q₁, c₁, h₁⟩ := ihg
      obtain ⟨r₂, q₂, c₂, h₂⟩ := ihh
      refine ⟨r₁ + r₂, Fin.append q₁ q₂, Fin.append c₁ c₂, ?_⟩
      filter_upwards [Lp.coeFn_add g h, h₁, h₂] with x hx hp hq
      rw [hx, Pi.add_apply, hp, hq, Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  | smul a g _ ih =>
      obtain ⟨r, q, c, hc⟩ := ih
      refine ⟨r, q, fun j => a * c j, ?_⟩
      filter_upwards [Lp.coeFn_smul a g, hc] with x hx hp
      rw [hx, Pi.smul_apply, hp, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

end PhaseDensity

/-! ## The phase endgame -/

section PhaseEndgame

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ} {C : ℝ}

/-- A bounded real weight whose weighted quadratic functional is nonnegative on all of `L²(μ;ℂ)` is
nonnegative almost everywhere: test at the indicator of `{g < 0}`. -/
theorem ae_nonneg_of_forall_weightedSq_nonneg (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C) (h : ∀ f : Lp ℂ 2 μ, 0 ≤ weightedSq μ g f) : 0 ≤ᵐ[μ] g := by
  classical
  set g' : ℝ → ℝ := hg.mk g with hg'def
  have hg'meas : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hgg' : g =ᵐ[μ] g' := hg.ae_eq_mk
  set E : Set ℝ := {x : ℝ | g' x < 0} with hEdef
  have hE : MeasurableSet E := hg'meas.measurable measurableSet_Iio
  have hμE : μ E ≠ ⊤ := (measure_lt_top μ E).ne
  have hgint : Integrable g μ := by
    refine Integrable.mono (integrable_const C) hg ?_
    filter_upwards [hbdd] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
    exact hx
  set fE : Lp ℂ 2 μ := indicatorConstLp 2 hE hμE (1 : ℂ) with hfE
  have hval : weightedSq μ g fE = ∫ x : ℝ in E, g x ∂μ := by
    rw [weightedSq, ← integral_indicator hE]
    refine integral_congr_ae ?_
    have hind := indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := hE) (hμs := hμE) (c := (1 : ℂ))
    filter_upwards [hind] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [hxE]
  have hge : 0 ≤ ∫ x : ℝ in E, g x ∂μ := by
    rw [← hval]
    exact h fE
  have hneg : ∀ᵐ x ∂(μ.restrict E), g x < 0 := by
    rw [ae_restrict_iff' hE]
    filter_upwards [hgg'] with x hx hxE
    rw [hx]
    exact hxE
  have hle : ∫ x : ℝ in E, g x ∂μ ≤ 0 := integral_nonpos_of_ae (hneg.mono fun x hx => hx.le)
  have hzero : ∫ x : ℝ in E, (-g x) ∂μ = 0 := by
    rw [integral_neg, le_antisymm hle hge, neg_zero]
  have hnonneg : 0 ≤ᵐ[μ.restrict E] fun x => -g x := hneg.mono fun x hx => by
    show (0 : ℝ) ≤ -g x
    linarith
  have haezero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hgint.restrict.neg).mp hzero
  have hcontra : ∀ᵐ _x ∂(μ.restrict E), False := by
    filter_upwards [haezero, hneg] with x h1 h2
    have : -g x = 0 := h1
    linarith
  have hEzero : μ E = 0 := by
    have hbot : μ.restrict E = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      have := (Filter.eventually_false_iff_eq_bot (f := ae (μ.restrict E))).mp hcontra
      simpa [MeasureTheory.ae_eq_bot] using this
    rwa [Measure.restrict_eq_zero] at hbot
  have hnot : ∀ᵐ x ∂μ, x ∉ E := by
    rw [MeasureTheory.ae_iff]
    simpa using hEzero
  filter_upwards [hgg', hnot] with x h1 h2
  show (0 : ℝ) ≤ g x
  rw [h1]
  exact not_lt.mp h2

/-- **The phase endgame.**  A bounded real density pairing nonnegatively with the squared modulus of
every rational trigonometric polynomial is nonnegative almost everywhere. -/
theorem ae_nonneg_of_forall_sq_phase_integral_nonneg (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hbdd : ∀ᵐ x ∂μ, |g x| ≤ C)
    (hpos : ∀ (r : ℕ) (q : Fin r → ℚ) (c : Fin r → ℂ),
      0 ≤ ∫ x, ‖∑ j, c j * phaseFn (q j) x‖ ^ 2 * g x ∂μ) : 0 ≤ᵐ[μ] g := by
  refine ae_nonneg_of_forall_weightedSq_nonneg hC hg hbdd fun f => ?_
  have hclosed : IsClosed {u : Lp ℂ 2 μ | 0 ≤ weightedSq μ g u} :=
    isClosed_le continuous_const (continuous_weightedSq hC hg hbdd)
  have hsub : ((phaseSubmodule (μ := μ) : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ))
      ⊆ {u : Lp ℂ 2 μ | 0 ≤ weightedSq μ g u} := by
    intro u hu
    obtain ⟨r, q, c, hrep⟩ := exists_phase_of_mem_phaseSubmodule hu
    show 0 ≤ weightedSq μ g u
    rw [weightedSq, integral_congr_ae (by filter_upwards [hrep] with x hx; rw [hx])]
    exact hpos r q c
  have huniv := hclosed.closure_subset_iff.mpr hsub
  rw [dense_phaseSubmodule.closure_eq] at huniv
  exact huniv (Set.mem_univ f)

end PhaseEndgame

/-! ## Theorem 4.2: phase/Hankel/source fusion -/

section PhaseFusion

variable {d : ℕ} {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- **(LEF.14)** A finite vector-valued rational phase packet `p(x) = Σ_j e^{-i q_j x} v_j`. -/
noncomputable def phasePacket {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) (x : ℝ) : Fin d → ℂ :=
  fun k => ∑ j, phaseFn (q j) x * v j k

/-- The phase test `Q_J(p) = ∫ p(x)* J(x) p(x) dμ`. -/
noncomputable def phaseForm (μ : Measure ℝ) (J : ℝ → Matrix (Fin d) (Fin d) ℂ) {r : ℕ}
    (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) : ℂ :=
  ∫ x, matQuad (J x) (phasePacket q v x) ∂μ

omit [IsFiniteMeasure μ] in
theorem norm_matQuad_le {M : Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hM : ∀ k l, ‖M k l‖ ≤ C)
    (w : Fin d → ℂ) : ‖matQuad M w‖ ≤ C * (∑ k, ‖w k‖) ^ (2 : ℕ) := by
  calc ‖matQuad M w‖ = ‖∑ k, ∑ l, (starRingEnd ℂ) (w k) * M k l * w l‖ := rfl
    _ ≤ ∑ k, ∑ l, ‖(starRingEnd ℂ) (w k) * M k l * w l‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k, ∑ l, ‖w k‖ * C * ‖w l‖ := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM k l) (norm_nonneg _))
          (norm_nonneg _)
    _ = C * (∑ k, ‖w k‖) ^ (2 : ℕ) := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring

omit [IsFiniteMeasure μ] in
theorem norm_phasePacket_le {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) (x : ℝ) (k : Fin d) :
    ‖phasePacket q v x k‖ ≤ ∑ j, ‖v j k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_phaseFn, one_mul]

theorem integrable_matQuad_phasePacket {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ) (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) :
    Integrable (fun x => matQuad (J x) (phasePacket q v x)) μ := by
  have hcont : ∀ k, Continuous fun x => phasePacket q v x k := fun k => by
    unfold phasePacket
    exact continuous_finsetSum _ fun j _ => (continuous_phaseFn (q j)).mul continuous_const
  have hm : AEStronglyMeasurable (fun x => matQuad (J x) (phasePacket q v x)) μ := by
    have h1 : AEStronglyMeasurable (∑ k : Fin d, ∑ l : Fin d, fun x =>
        (starRingEnd ℂ) (phasePacket q v x k) * J x k l * phasePacket q v x l) μ :=
      Finset.aestronglyMeasurable_sum _ fun k _ => Finset.aestronglyMeasurable_sum _ fun l _ =>
        ((Complex.continuous_conj.comp (hcont k)).aestronglyMeasurable.mul (hmeas k l)).mul
          (hcont l).aestronglyMeasurable
    have h2 : (∑ k : Fin d, ∑ l : Fin d, fun x =>
        (starRingEnd ℂ) (phasePacket q v x k) * J x k l * phasePacket q v x l)
        = fun x => matQuad (J x) (phasePacket q v x) := by
      funext x
      simp only [matQuad, Finset.sum_apply]
    rwa [h2] at h1
  refine (integrable_const (|C| * (∑ k, ∑ j, ‖v j k‖) ^ (2 : ℕ))).mono' hm ?_
  filter_upwards [hbdd] with x hx
  calc ‖matQuad (J x) (phasePacket q v x)‖ ≤ C * (∑ k, ‖phasePacket q v x k‖) ^ (2 : ℕ) :=
        norm_matQuad_le hx _
    _ ≤ |C| * (∑ k, ‖phasePacket q v x k‖) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (∑ k, ∑ j, ‖v j k‖) ^ (2 : ℕ) := by
        gcongr with k
        exact norm_phasePacket_le q v x k

theorem re_phaseForm_eq_integral {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ) (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) :
    (phaseForm μ J q v).re = ∫ x, (matQuad (J x) (phasePacket q v x)).re ∂μ := by
  rw [phaseForm]
  exact (integral_re (integrable_matQuad_phasePacket hmeas hbdd q v)).symm

/-- **Theorem 4.2, source ⇒ phase.** -/
theorem re_phaseForm_nonneg_of_ae_posSemidef {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ) (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hpos : ∀ᵐ x ∂μ, (J x).PosSemidef) {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) :
    0 ≤ (phaseForm μ J q v).re := by
  rw [re_phaseForm_eq_integral hmeas hbdd]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hpos] with x hx
  rw [matQuad_eq_dotProduct]
  exact hx.re_dotProduct_nonneg _

omit [IsFiniteMeasure μ] in
/-- Positivity of every direction density gives positivity of a Hermitian density. -/
theorem ae_posSemidef_of_forall_directionDensity_nonneg {J : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian) (h : ∀ u, 0 ≤ᵐ[μ] directionDensity J u) :
    ∀ᵐ x ∂μ, (J x).PosSemidef := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Fin d → ℂ)
  have hall : ∀ᵐ x ∂μ, ∀ u ∈ D, 0 ≤ directionDensity J u x := by
    rw [ae_ball_iff hDcount]
    exact fun u _ => h u
  filter_upwards [hall, hherm] with x hx hxherm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hxherm fun u => ?_
  have hcont : Continuous fun u : Fin d → ℂ => (matQuad (J x) u).re := by
    simp only [matQuad]
    fun_prop
  have hclosed : IsClosed {u : Fin d → ℂ | 0 ≤ (matQuad (J x) u).re} := isClosed_le continuous_const hcont
  have hre : 0 ≤ (matQuad (J x) u).re := by
    have := hDdense.closure_eq ▸ (hclosed.closure_subset_iff.mpr fun u hu => hx u hu)
    exact this (Set.mem_univ u)
  have him : (matQuad (J x) u).im = 0 := by
    have hconj : (starRingEnd ℂ) (matQuad (J x) u) = matQuad (J x) u := by
      simp only [matQuad, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have h1 : (starRingEnd ℂ) (J x l k) = J x k l := by
        have h2 := congrFun (congrFun hxherm k) l
        simpa [Matrix.conjTranspose_apply, Complex.star_def] using h2
      rw [h1]
      ring
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  rw [← matQuad_eq_dotProduct]
  exact Complex.le_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

/-- **Theorem 4.2, phase ⇒ source.**  Positivity of the phase test on every rational phase packet
forces a positive semidefinite density, for every finite measure. -/
theorem ae_posSemidef_of_forall_phaseForm_nonneg {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C) (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian)
    (hF : ∀ (r : ℕ) (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ), 0 ≤ (phaseForm μ J q v).re) :
    ∀ᵐ x ∂μ, (J x).PosSemidef := by
  refine ae_posSemidef_of_forall_directionDensity_nonneg hherm fun u => ?_
  refine ae_nonneg_of_forall_sq_phase_integral_nonneg (C := C * (∑ k, ‖u k‖) ^ (2 : ℕ)) (by positivity)
    (aestronglyMeasurable_directionDensity hmeas u) (hbdd.mono fun x hx => abs_directionDensity_le hx u)
    fun r q c => ?_
  have h := hF r q (fun j k => c j * u k)
  rw [re_phaseForm_eq_integral hmeas hbdd] at h
  refine h.trans_eq (integral_congr_ae (Eventually.of_forall fun x => ?_))
  have hp : phasePacket q (fun j k => c j * u k) x = fun k => (∑ j, c j * phaseFn (q j) x) * u k := by
    funext k
    simp only [phasePacket, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hp, matQuad_smul_vector, conj_mul_self, directionDensity]
  rw [Complex.re_ofReal_mul]

/-- **Theorem 4.2 (LEF.15) Phase/Hankel/source fusion.**  Under one exponential window, positivity
almost everywhere, positivity of every block Hankel section and positivity of the phase test on
every rational phase packet are equivalent. -/
theorem phase_hankel_source_fusion {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ) {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C) (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian) :
    ((∀ᵐ x ∂μ, (J x).PosSemidef) ↔
      ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (blockHankel μ J N) v).re) ∧
    ((∀ᵐ x ∂μ, (J x).PosSemidef) ↔
      ∀ (r : ℕ) (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ), 0 ≤ (phaseForm μ J q v).re) :=
  ⟨ae_posSemidef_iff_forall_blockHankel_nonneg ha hexp hC hmeas hbdd hherm,
    ⟨fun hpos _ q v => re_phaseForm_nonneg_of_ae_posSemidef hmeas hbdd hpos q v,
      ae_posSemidef_of_forall_phaseForm_nonneg hC hmeas hbdd hherm⟩⟩

end PhaseFusion

/-! ## Theorem 5.1: compensation-gauge conservation -/

section Gauge

variable {d : ℕ} {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- **(LEF.16)** The compensated density `J_c = cW - H`. -/
noncomputable def compensated (W H : ℝ → Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (x : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((c : ℂ)) • W x - H x

/-- **(LEF.17)** The source feasible set `{c ≥ 0 : J_c ⪰ 0 a.e.}`. -/
def feasibleSource (μ : Measure ℝ) (W H : ℝ → Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ᵐ x ∂μ, (compensated W H c x).PosSemidef}

/-- **(LEF.17)** The Hankel feasible set. -/
def feasibleHankel (μ : Measure ℝ) (W H : ℝ → Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ (N : ℕ) (v : Fin N × Fin d → ℂ),
    0 ≤ (matQuad (blockHankel μ (compensated W H c) N) v).re}

/-- **(LEF.17)** The phase feasible set. -/
def feasiblePhase (μ : Measure ℝ) (W H : ℝ → Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ (r : ℕ) (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ),
    0 ≤ (phaseForm μ (compensated W H c) q v).re}

/-- **(LEF.19)** The extended sharp gauge `inf S ∈ [0, ∞]` (`∞` for the empty set). -/
noncomputable def sharpGauge (S : Set ℝ) : ENNReal := ⨅ c ∈ S, ENNReal.ofReal c

/-- **Theorem 5.1 (LEF.18)–(LEF.19) Conservation.**  For bounded measurable Hermitian fields `W, H`
the source, Hankel and phase feasible sets coincide, and so do their sharp gauges. -/
theorem feasible_conservation {a : ℝ} (ha : 0 < a) (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {W H : ℝ → Matrix (Fin d) (Fin d) ℂ} {CW CH : ℝ} (hCW : 0 ≤ CW) (hCH : 0 ≤ CH)
    (hWm : ∀ k l, AEStronglyMeasurable (fun x => W x k l) μ)
    (hHm : ∀ k l, AEStronglyMeasurable (fun x => H x k l) μ)
    (hWb : ∀ᵐ x ∂μ, ∀ k l, ‖W x k l‖ ≤ CW) (hHb : ∀ᵐ x ∂μ, ∀ k l, ‖H x k l‖ ≤ CH)
    (hWh : ∀ᵐ x ∂μ, (W x).IsHermitian) (hHh : ∀ᵐ x ∂μ, (H x).IsHermitian) :
    (feasibleSource μ W H = feasibleHankel μ W H ∧ feasibleSource μ W H = feasiblePhase μ W H) ∧
    (sharpGauge (feasibleSource μ W H) = sharpGauge (feasibleHankel μ W H) ∧
      sharpGauge (feasibleSource μ W H) = sharpGauge (feasiblePhase μ W H)) := by
  have hfus : ∀ c : ℝ, 0 ≤ c → _ := fun c hc => phase_hankel_source_fusion (J := compensated W H c)
    (C := c * CW + CH) ha hexp (by positivity)
    (fun k l => ((hWm k l).const_mul (c : ℂ)).sub (hHm k l))
    (by
      filter_upwards [hWb, hHb] with x hx hy k l
      simp only [compensated, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      calc ‖(c : ℂ) * W x k l - H x k l‖ ≤ ‖(c : ℂ) * W x k l‖ + ‖H x k l‖ := norm_sub_le _ _
        _ ≤ c * CW + CH := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
            gcongr
            · exact hx k l
            · exact hy k l)
    (by
      filter_upwards [hWh, hHh] with x hx hy
      unfold compensated
      have hcW : ((c : ℂ) • W x).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul, hx.eq, Complex.star_def, Complex.conj_ofReal]
      exact hcW.sub hy)
  have h1 : feasibleSource μ W H = feasibleHankel μ W H := Set.ext fun c =>
    ⟨fun ⟨hc, h⟩ => ⟨hc, ((hfus c hc).1).1 h⟩, fun ⟨hc, h⟩ => ⟨hc, ((hfus c hc).1).2 h⟩⟩
  have h2 : feasibleSource μ W H = feasiblePhase μ W H := Set.ext fun c =>
    ⟨fun ⟨hc, h⟩ => ⟨hc, ((hfus c hc).2).1 h⟩, fun ⟨hc, h⟩ => ⟨hc, ((hfus c hc).2).2 h⟩⟩
  exact ⟨⟨h1, h2⟩, ⟨by rw [h1], by rw [h2]⟩⟩

omit [IsFiniteMeasure μ] in
/-- With `W ⪰ 0` the source feasible set is an up-set, so the sharp gauge is the threshold of the
compensation law. -/
theorem feasibleSource_mono {W H : ℝ → Matrix (Fin d) (Fin d) ℂ} (hWpos : ∀ᵐ x ∂μ, (W x).PosSemidef)
    {c c' : ℝ} (hc : c ∈ feasibleSource μ W H) (hcc' : c ≤ c') : c' ∈ feasibleSource μ W H := by
  refine ⟨hc.1.trans hcc', ?_⟩
  filter_upwards [hc.2, hWpos] with x hx hw
  have hsplit : compensated W H c' x = compensated W H c x + (((c' - c : ℝ) : ℂ)) • W x := by
    simp only [compensated]
    push_cast
    rw [sub_smul]
    abel
  rw [hsplit]
  exact hx.add (hw.smul (by exact_mod_cast sub_nonneg.2 hcc'))

end Gauge

end HTGeometry
