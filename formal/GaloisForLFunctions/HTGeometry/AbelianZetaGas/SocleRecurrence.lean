import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleExchangeWork

/-!
# Recurrent socle phase and open logarithmic lift

On `H = L²(P_{σ,τ})` the socle phase `U_t f = e^{-itQ} f` acts on the vacuum `Ω = 1`.  Because the
law is atomic, the phase orbit `t ↦ U_t Ω` is norm-precompact: a finite head of atoms carries almost
all probability, and on that head the phases range over a compact torus.  An isometric orbit with
precompact range returns: there are arbitrarily large times `t_n` with `U_{t_n} Ω → Ω`.  Along the
same times the marked logarithmic lift `t_n Q Ω` escapes, `‖t_n Q Ω‖₂ = t_n √(E Q²) → ∞`, and the
vacuum correlation is the imaginary chart of the response, `⟨Ω, U_t Ω⟩ = C_{σ,τ}(it)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

/-- The socle phase `e^{-itQ(A)}`. -/
def socPhase (t : ℝ) (A : AbelianZetaGroupClass) : ℂ :=
  Complex.exp (-(((t * socleLog A : ℝ)) : ℂ) * I)

theorem norm_socPhase (t : ℝ) (A : AbelianZetaGroupClass) : ‖socPhase t A‖ = 1 := by
  rw [socPhase, show -(((t * socleLog A : ℝ)) : ℂ) * I = ((-(t * socleLog A) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

namespace GasChamber

variable (c : GasChamber)

theorem memLp_socPhase (t : ℝ) : MemLp (socPhase t) 2 c.law :=
  MemLp.of_bound measurable_from_top.aestronglyMeasurable 1
    (Eventually.of_forall fun A => (norm_socPhase t A).le)

/-- `(AZC.19)`  The phase orbit `U_t Ω` in `L²(P_{σ,τ})`. -/
def phaseOrbit (t : ℝ) : Lp ℂ 2 c.law := (c.memLp_socPhase t).toLp (socPhase t)

/-- The vacuum `Ω = 1 = U_0 Ω`. -/
def vacuum : Lp ℂ 2 c.law := c.phaseOrbit 0

theorem socPhase_zero : socPhase 0 = fun _ => 1 := by
  funext A
  simp [socPhase]

theorem norm_toLp_eq {f : AbelianZetaGroupClass → ℂ} (hf : MemLp f 2 c.law) :
    ‖hf.toLp f‖ = Real.sqrt (∫ A, ‖f A‖ ^ 2 ∂c.law) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num

theorem norm_phaseOrbit_sub (a b : ℝ) :
    ‖c.phaseOrbit a - c.phaseOrbit b‖ =
      Real.sqrt (∫ A, ‖socPhase a A - socPhase b A‖ ^ 2 ∂c.law) := by
  rw [phaseOrbit, phaseOrbit, ← MemLp.toLp_sub, norm_toLp_eq]
  rfl

/-- The phase orbit is isometric: `‖U_a Ω - U_b Ω‖ = ‖U_{a-b} Ω - Ω‖`. -/
theorem norm_phaseOrbit_sub_eq (a b : ℝ) :
    ‖c.phaseOrbit a - c.phaseOrbit b‖ = ‖c.phaseOrbit (a - b) - c.vacuum‖ := by
  rw [vacuum, norm_phaseOrbit_sub, norm_phaseOrbit_sub]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  simp only
  congr 1
  have h : socPhase a A - socPhase b A = socPhase b A * (socPhase (a - b) A - socPhase 0 A) := by
    simp only [socPhase, mul_sub, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring_nf
  rw [h, norm_mul, norm_socPhase, one_mul]

/-- A probability law on the countable class space is carried, up to `η`, by a finite head. -/
theorem exists_finset_measureReal_compl_lt {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset AbelianZetaGroupClass, c.law.real ((F : Set AbelianZetaGroupClass)ᶜ) < η := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat AbelianZetaGroupClass
  set s : ℕ → Set AbelianZetaGroupClass := fun n =>
    (((Finset.range n).image e : Finset AbelianZetaGroupClass) : Set AbelianZetaGroupClass)ᶜ
  have hanti : Antitone s := fun m n hmn A hA => by
    simp only [s, mem_compl_iff, Finset.mem_coe, Finset.mem_image, Finset.mem_range,
      not_exists, not_and] at hA ⊢
    exact fun k hk => hA k (lt_of_lt_of_le hk hmn)
  have hinter : (⋂ n, s n) = ∅ := by
    ext A
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, rfl⟩ := he A
    refine ⟨k + 1, ?_⟩
    simp only [s, mem_compl_iff, Finset.mem_coe, Finset.mem_image, Finset.mem_range, not_not]
    exact ⟨k, Nat.lt_succ_self k, rfl⟩
  have hlim := tendsto_measure_iInter_atTop (μ := c.law) (s := s)
    (fun n => (MeasurableSpace.measurableSet_top).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))).exists
  refine ⟨(Finset.range n).image e, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_lt_of_lt_ofReal hn

/-- `(AZC.20)`  **Norm-precompactness.**  The phase orbit `t ↦ U_t Ω` has totally bounded range. -/
theorem totallyBounded_range_phaseOrbit : TotallyBounded (range c.phaseOrbit) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨F, hF⟩ := c.exists_finset_measureReal_compl_lt (η := ε ^ 2 / 8) (by positivity)
  set g : ℝ → (F → ℂ) := fun t A => socPhase t A with hgdef
  have hcomp : IsCompact (univ.pi fun _ : F => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hsub : range g ⊆ univ.pi fun _ : F => Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨t, rfl⟩ A _
    simp only [hgdef, Metric.mem_closedBall, dist_zero_right]
    exact (norm_socPhase t A).le
  have htb := (hcomp.totallyBounded.subset hsub)
  obtain ⟨T, hTsub, hTfin, hTcov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 2)
    (by positivity)
  choose rep hrep using fun y : T => hTsub y.2
  haveI : Finite T := hTfin
  refine ⟨range fun y : T => c.phaseOrbit (rep y), finite_range _, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.mp (hTcov ⟨t, rfl⟩)
  refine mem_iUnion₂.mpr ⟨c.phaseOrbit (rep ⟨y, hyT⟩), ⟨⟨y, hyT⟩, rfl⟩, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_phaseOrbit_sub]
  have hclose : ∀ A ∈ (F : Set AbelianZetaGroupClass),
      ‖socPhase t A - socPhase (rep ⟨y, hyT⟩) A‖ < ε / 2 := by
    intro A hA
    have hball : dist (g t) y < ε / 2 := hy
    have hrepy : g (rep ⟨y, hyT⟩) = y := hrep ⟨y, hyT⟩
    rw [← hrepy] at hball
    have := (dist_pi_lt_iff (by positivity)).mp hball ⟨A, hA⟩
    rw [dist_eq_norm] at this
    exact this
  set d : AbelianZetaGroupClass → ℝ := fun A =>
    ‖socPhase t A - socPhase (rep ⟨y, hyT⟩) A‖ ^ 2 with hddef
  have hd2 : ∀ A, d A ≤ 4 := fun A => by
    have h1 := norm_sub_le (socPhase t A) (socPhase (rep ⟨y, hyT⟩) A)
    rw [norm_socPhase, norm_socPhase] at h1
    have h0 : 0 ≤ ‖socPhase t A - socPhase (rep ⟨y, hyT⟩) A‖ := norm_nonneg _
    simp only [hddef]
    nlinarith
  have hdi : Integrable d c.law := (integrable_const (4 : ℝ)).mono'
    measurable_from_top.aestronglyMeasurable (Eventually.of_forall fun A => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hd2 A)
  have hFm : MeasurableSet (F : Set AbelianZetaGroupClass) := MeasurableSpace.measurableSet_top
  have hint : ∫ A, d A ∂c.law < ε ^ 2 := by
    rw [← integral_add_compl hFm hdi]
    have h1 : ∫ A in (F : Set AbelianZetaGroupClass), d A ∂c.law ≤ (ε / 2) ^ 2 := by
      calc ∫ A in (F : Set AbelianZetaGroupClass), d A ∂c.law
          ≤ ∫ A in (F : Set AbelianZetaGroupClass), (ε / 2) ^ 2 ∂c.law :=
            setIntegral_mono_on hdi.integrableOn (integrableOn_const (measure_ne_top _ _)) hFm
              fun A hA => pow_le_pow_left₀ (norm_nonneg _) (hclose A hA).le 2
        _ = c.law.real (F : Set AbelianZetaGroupClass) * (ε / 2) ^ 2 := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ 1 * (ε / 2) ^ 2 := mul_le_mul_of_nonneg_right measureReal_le_one (by positivity)
        _ = (ε / 2) ^ 2 := one_mul _
    have h2 : ∫ A in (F : Set AbelianZetaGroupClass)ᶜ, d A ∂c.law ≤
        4 * c.law.real ((F : Set AbelianZetaGroupClass)ᶜ) := by
      calc ∫ A in (F : Set AbelianZetaGroupClass)ᶜ, d A ∂c.law
          ≤ ∫ A in (F : Set AbelianZetaGroupClass)ᶜ, (4 : ℝ) ∂c.law :=
            setIntegral_mono_on hdi.integrableOn (integrableOn_const (measure_ne_top _ _))
              hFm.compl fun A _ => hd2 A
        _ = 4 * c.law.real ((F : Set AbelianZetaGroupClass)ᶜ) := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
    nlinarith
  calc Real.sqrt (∫ A, d A ∂c.law) < Real.sqrt (ε ^ 2) :=
        Real.sqrt_lt_sqrt (integral_nonneg fun A => by positivity) hint
    _ = ε := Real.sqrt_sq hε.le

/-- **Return lemma.**  For every `ε > 0` and every bound `K`, some time `t ≥ K` brings the orbit
within `ε` of the vacuum. -/
theorem exists_return (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, (K : ℝ) ≤ t ∧ ‖c.phaseOrbit t - c.vacuum‖ < ε := by
  classical
  obtain ⟨T, hTsub, hTfin, hTcov⟩ := Metric.finite_approx_of_totallyBounded
    c.totallyBounded_range_phaseOrbit (ε / 2) (by positivity)
  haveI : Finite T := hTfin
  have hcov : ∀ k : ℕ, ∃ y : T,
      c.phaseOrbit (((K + 1) * k : ℕ) : ℝ) ∈ Metric.ball (y : Lp ℂ 2 c.law) (ε / 2) := by
    intro k
    obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.mp (hTcov ⟨_, rfl⟩)
    exact ⟨⟨y, hyT⟩, hy⟩
  choose f hf using hcov
  obtain ⟨k, l, hkl, hfkl⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hkl with h | h
  · refine ⟨((((K + 1) * l : ℕ) : ℝ) - (((K + 1) * k : ℕ) : ℝ)), ?_, ?_⟩
    · have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
      push_cast
      nlinarith
    · rw [← norm_phaseOrbit_sub_eq]
      have h1 := hf l
      have h2 := hf k
      rw [hfkl] at h2
      rw [Metric.mem_ball, dist_eq_norm] at h1 h2
      calc ‖c.phaseOrbit (((K + 1) * l : ℕ) : ℝ) - c.phaseOrbit (((K + 1) * k : ℕ) : ℝ)‖
          ≤ ‖c.phaseOrbit (((K + 1) * l : ℕ) : ℝ) - (f l : Lp ℂ 2 c.law)‖ +
              ‖(f l : Lp ℂ 2 c.law) - c.phaseOrbit (((K + 1) * k : ℕ) : ℝ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := by
            rw [norm_sub_rev (f l : Lp ℂ 2 c.law)]
            exact add_lt_add h1 h2
        _ = ε := add_halves ε
  · refine ⟨((((K + 1) * k : ℕ) : ℝ) - (((K + 1) * l : ℕ) : ℝ)), ?_, ?_⟩
    · have hkl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
      push_cast
      nlinarith
    · rw [← norm_phaseOrbit_sub_eq]
      have h1 := hf k
      have h2 := hf l
      rw [← hfkl] at h2
      rw [Metric.mem_ball, dist_eq_norm] at h1 h2
      calc ‖c.phaseOrbit (((K + 1) * k : ℕ) : ℝ) - c.phaseOrbit (((K + 1) * l : ℕ) : ℝ)‖
          ≤ ‖c.phaseOrbit (((K + 1) * k : ℕ) : ℝ) - (f k : Lp ℂ 2 c.law)‖ +
              ‖(f k : Lp ℂ 2 c.law) - c.phaseOrbit (((K + 1) * l : ℕ) : ℝ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := by
            rw [norm_sub_rev (f k : Lp ℂ 2 c.law)]
            exact add_lt_add h1 h2
        _ = ε := add_halves ε

/-- `(AZC.20)`  **Recurrence.**  There are times `t_n → ∞` with `U_{t_n} Ω → Ω`. -/
theorem exists_recurrent_times :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun n => c.phaseOrbit (t n)) atTop (𝓝 c.vacuum) := by
  have h := fun n : ℕ => c.exists_return n (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose t ht1 ht2 using h
  refine ⟨t, tendsto_atTop_mono ht1 tendsto_natCast_atTop_atTop, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (ht2 n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## The open logarithmic lift and the vacuum correlation -/

theorem memLp_socleLog : MemLp socleLog 2 c.law := by
  have h := memLp_tilted_mul (c.mem_interior_integrableExpSet (t := 0)
    (by linarith [c.firstDepth])) 2
  rw [show (fun A : AbelianZetaGroupClass => (0 : ℝ) * -socleLog A) = 0 by funext A; simp,
    tilted_zero] at h
  have h' := h.neg
  convert h' using 1
  all_goals first
    | (funext A; simp)
    | norm_num

theorem memLp_lift (t : ℝ) :
    MemLp (fun A => ((t * socleLog A : ℝ) : ℂ)) 2 c.law :=
  ((c.memLp_socleLog.const_mul t).ofReal).congr_norm measurable_from_top.aestronglyMeasurable
    (Eventually.of_forall fun _ => rfl)

/-- `(AZC.21)`  The marked logarithmic lift `t Q Ω` in `L²(P_{σ,τ})`. -/
def logLift (t : ℝ) : Lp ℂ 2 c.law := (c.memLp_lift t).toLp _

theorem socleSecondMoment_pos : 0 < ∫ A, socleLog A ^ 2 ∂c.law := by
  have hi : Integrable (fun A => socleLog A ^ 2) c.law := c.memLp_socleLog.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun A => sq_nonneg _) hi]
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  apply c.not_ae_const_socleLog
  refine ⟨0, ?_⟩
  rw [ae_iff]
  refine measure_mono_null (fun A hA => ?_) hzero
  simp only [mem_setOf_eq] at hA
  simp only [Function.mem_support]
  exact pow_ne_zero 2 hA

/-- `(AZC.21)`  `‖t Q Ω‖₂ = |t| √(E Q²)`. -/
theorem norm_logLift (t : ℝ) :
    ‖c.logLift t‖ = |t| * Real.sqrt (∫ A, socleLog A ^ 2 ∂c.law) := by
  rw [logLift, norm_toLp_eq]
  have h : ∀ A, ‖((t * socleLog A : ℝ) : ℂ)‖ ^ 2 = t ^ 2 * socleLog A ^ 2 := fun A => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [h]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

/-- **Theorem 8.1.**  The phase orbit is norm-precompact and recurrent along times `t_n → ∞`,
while the marked logarithmic lift escapes: `‖t_n Q Ω‖₂ = t_n √(E Q²) → ∞`. -/
theorem recurrent_phase_open_lift :
    TotallyBounded (range c.phaseOrbit) ∧
      ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        Tendsto (fun n => c.phaseOrbit (t n)) atTop (𝓝 c.vacuum) ∧
        Tendsto (fun n => ‖c.logLift (t n)‖) atTop atTop := by
  obtain ⟨t, ht, hrec⟩ := c.exists_recurrent_times
  refine ⟨c.totallyBounded_range_phaseOrbit, t, ht, hrec, ?_⟩
  simp_rw [norm_logLift]
  have hpos : 0 < Real.sqrt (∫ A, socleLog A ^ 2 ∂c.law) :=
    Real.sqrt_pos.mpr c.socleSecondMoment_pos
  exact (tendsto_abs_atTop_atTop.comp ht).atTop_mul_const hpos

/-- `(AZC.22)`  The vacuum correlation is the imaginary chart of the response:
`⟨Ω, U_t Ω⟩ = C_{σ,τ}(it)`. -/
theorem inner_vacuum_phaseOrbit (t : ℝ) :
    inner ℂ c.vacuum (c.phaseOrbit t) = socleResponse c.sigma c.tau ((t : ℂ) * I) := by
  rw [L2.inner_def, ← c.integral_law_cexp_socle (z := (t : ℂ) * I) (by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im]
    linarith [c.firstDepth])]
  refine integral_congr_ae ?_
  filter_upwards [(c.memLp_socPhase 0).coeFn_toLp, (c.memLp_socPhase t).coeFn_toLp] with A h0 ht
  rw [vacuum, phaseOrbit, phaseOrbit] at *
  rw [h0, ht, socPhase_zero, RCLike.inner_apply, map_one, mul_one, socPhase]
  congr 1
  push_cast
  ring

end GasChamber

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
