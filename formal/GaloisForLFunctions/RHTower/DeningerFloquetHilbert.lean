import GaloisForLFunctions.RHTower.DeningerFloquetAtomicMeasure
import GaloisForLFunctions.RHTower.DeningerFloquetGaussianAtom
import GaloisForLFunctions.HTGeometry.FiniteRegularityWienerFamily

/-!
# The Floquet completion is `L²` of the arithmetic lattice measure

The Mellin sampling map `h ↦ 𝓕(e^{t/2}h)` sends a source cochain to a square-integrable function
for the arithmetic lattice measure, its `L²` norm is exactly the half-density Floquet energy, and
its range spans a dense subspace: the Gaussian atoms concentrate at a single node, and a function
orthogonal to all of them vanishes at every node, hence almost everywhere.

Together these say that the Hilbert completion of the source for the Floquet energy is
`L²(μ_Fl)`, with the sampling map as the completion map.

* `deningerFloquetSample_memLp` : the sample is square integrable.
* `deningerFloquetSample_integral_normSq` : **the sampling map is isometric for `E_Fl`.**
* `deningerFloquetLp` : the sampling map into `L²(μ_Fl)`.
* `deningerFloquetLp_span_topologicalClosure` : **its range spans a dense subspace.**
-/

namespace RHTower

open MeasureTheory Set Filter Topology Complex SchwartzMap
open scoped ENNReal FourierTransform InnerProductSpace ContDiff

noncomputable section

/-! ## The sample is square integrable -/

theorem deningerFloquetSample_continuous (h : DeningerExpSchwartz) :
    Continuous (deningerFloquetSample h) :=
  GaloisForLFunctions.HTGeometry.continuous_fourier_of_integrable
    (SchwartzMap.integrable ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))

theorem deningerFloquetSample_normSq_continuous (h : DeningerExpSchwartz) :
    Continuous fun ξ => ‖deningerFloquetSample h ξ‖ ^ 2 :=
  ((deningerFloquetSample_continuous h).norm).pow 2

theorem deningerFloquetSample_integrable_sq (h : DeningerExpSchwartz) :
    Integrable (fun ξ => ‖deningerFloquetSample h ξ‖ ^ 2) deningerFloquetMeasure := by
  refine ⟨(deningerFloquetSample_normSq_continuous h).aestronglyMeasurable, ?_⟩
  have hfun : ∀ ξ : ℝ, ‖(‖deningerFloquetSample h ξ‖ ^ 2 : ℝ)‖ₑ
      = ENNReal.ofReal (‖deningerFloquetSample h ξ‖ ^ 2) := fun ξ =>
    Real.enorm_eq_ofReal (by positivity)
  show ∫⁻ ξ, ‖(‖deningerFloquetSample h ξ‖ ^ 2 : ℝ)‖ₑ ∂deningerFloquetMeasure < ⊤
  simp_rw [hfun]
  rw [lintegral_deningerFloquetSample_normSq]
  exact ENNReal.ofReal_lt_top

theorem deningerFloquetSample_memLp (h : DeningerExpSchwartz) :
    MemLp (deningerFloquetSample h) 2 deningerFloquetMeasure :=
  (memLp_two_iff_integrable_sq_norm
    (deningerFloquetSample_continuous h).aestronglyMeasurable).2
    (deningerFloquetSample_integrable_sq h)

/-- **The sampling map is isometric for the half-density Floquet energy.** -/
theorem deningerFloquetSample_integral_normSq (h : DeningerExpSchwartz) :
    ∫ ξ, ‖deningerFloquetSample h ξ‖ ^ 2 ∂deningerFloquetMeasure
      = deningerHalfDensityFloquetEnergy h := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ξ => by positivity)
    (deningerFloquetSample_normSq_continuous h).aestronglyMeasurable,
    lintegral_deningerFloquetSample_normSq,
    ENNReal.toReal_ofReal (deningerHalfDensityFloquetEnergy_nonneg h)]

/-- The Mellin sampling map into `L²(μ_Fl)`. -/
def deningerFloquetLp (h : DeningerExpSchwartz) : Lp ℂ 2 deningerFloquetMeasure :=
  (deningerFloquetSample_memLp h).toLp _

theorem deningerFloquetLp_coeFn (h : DeningerExpSchwartz) :
    (deningerFloquetLp h : ℝ → ℂ) =ᵐ[deningerFloquetMeasure] deningerFloquetSample h :=
  (deningerFloquetSample_memLp h).coeFn_toLp

/-! ## Gaussian concentration in `L²` -/

/-- The width schedule `σ_n = 1/(n+1)`. -/
def deningerAtomWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem deningerAtomWidth_pos (n : ℕ) : 0 < deningerAtomWidth n := by
  rw [deningerAtomWidth]
  positivity

/-- The Gaussian sample at width `σ_n`. -/
theorem deningerFloquetSample_atomWidth (ξ₀ : ℝ) (n : ℕ) (ξ : ℝ) :
    deningerFloquetSample (deningerFloquetAtom ξ₀ (deningerAtomWidth n)
        (deningerAtomWidth_pos n)) ξ
      = ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) := by
  rw [deningerFloquetSample_atom]
  congr 2
  rw [deningerAtomWidth]
  field_simp

theorem deningerAtomGauss_le (ξ₀ ξ : ℝ) (n : ℕ) :
    Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1)))
      ≤ Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * (((0 : ℕ) : ℝ) + 1))) := by
  refine Real.exp_le_exp.2 ?_
  have hnn : (0 : ℝ) ≤ Real.pi * (ξ - ξ₀) ^ 2 := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  push_cast
  nlinarith

theorem deningerAtomGauss_tendsto (ξ₀ ξ : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1)))) atTop
      (𝓝 (Set.indicator ({ξ₀} : Set ℝ) (fun _ => (1 : ℝ)) ξ)) := by
  by_cases hξ : ξ = ξ₀
  · subst hξ
    have hfun : (fun n : ℕ => Real.exp (-(Real.pi * (ξ - ξ) ^ 2 * ((n : ℝ) + 1))))
        = fun _ : ℕ => (1 : ℝ) := by
      funext n
      norm_num
    rw [hfun, Set.indicator_of_mem (Set.mem_singleton _)]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem (by simpa using hξ)]
    have hne : ξ - ξ₀ ≠ 0 := sub_ne_zero.2 hξ
    have hsq : 0 < (ξ - ξ₀) ^ 2 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
    have hpos : 0 < Real.pi * (ξ - ξ₀) ^ 2 := by positivity
    have hlin : Tendsto (fun n : ℕ => Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1)) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop hpos ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hlin)

/-! ## Density of the range -/

/-- **A function orthogonal to every Mellin sample vanishes.** -/
theorem deningerFloquetLp_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range deningerFloquetLp))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
  have hzero : ∀ h : DeningerExpSchwartz, ⟪deningerFloquetLp h, a⟫_ℂ = 0 := fun h =>
    ha _ (Submodule.subset_span ⟨h, rfl⟩)
  have hA : MemLp (a : ℝ → ℂ) 2 deningerFloquetMeasure := Lp.memLp a
  have hint : ∀ (ξ₀ : ℝ) (n : ℕ),
      ∫ ξ, ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * (a : ℝ → ℂ) ξ
        ∂deningerFloquetMeasure = 0 := by
    intro ξ₀ n
    have hz := hzero (deningerFloquetAtom ξ₀ (deningerAtomWidth n) (deningerAtomWidth_pos n))
    rw [L2.inner_def] at hz
    rw [← hz]
    refine integral_congr_ae ?_
    filter_upwards [deningerFloquetLp_coeFn
      (deningerFloquetAtom ξ₀ (deningerAtomWidth n) (deningerAtomWidth_pos n))] with ξ hξ
    rw [RCLike.inner_apply, hξ, deningerFloquetSample_atomWidth, Complex.conj_ofReal]
    ring
  have hpt : ∀ ξ₀ : ℝ, (deningerFloquetMeasure).real {ξ₀} • (a : ℝ → ℂ) ξ₀ = 0 := by
    intro ξ₀
    have hbound : Integrable
        (fun ξ => ‖deningerFloquetSample (deningerFloquetAtom ξ₀ (deningerAtomWidth 0)
            (deningerAtomWidth_pos 0)) ξ‖ * ‖(a : ℝ → ℂ) ξ‖) deningerFloquetMeasure :=
      MemLp.integrable_mul
        (deningerFloquetSample_memLp
          (deningerFloquetAtom ξ₀ (deningerAtomWidth 0) (deningerAtomWidth_pos 0))).norm hA.norm
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun ξ => ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ)
          * (a : ℝ → ℂ) ξ) deningerFloquetMeasure := by
      intro n
      refine AEStronglyMeasurable.mul ?_ (Lp.aestronglyMeasurable a)
      refine Complex.continuous_ofReal.comp_aestronglyMeasurable ?_
      exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have hdom : ∀ n : ℕ, ∀ᵐ ξ ∂deningerFloquetMeasure,
        ‖((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * (a : ℝ → ℂ) ξ‖
          ≤ ‖deningerFloquetSample (deningerFloquetAtom ξ₀ (deningerAtomWidth 0)
              (deningerAtomWidth_pos 0)) ξ‖ * ‖(a : ℝ → ℂ) ξ‖ := by
      intro n
      refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, deningerFloquetSample_atomWidth]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact deningerAtomGauss_le ξ₀ ξ n
    have hlim : ∀ᵐ ξ ∂deningerFloquetMeasure, Tendsto
        (fun n : ℕ => ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ)
          * (a : ℝ → ℂ) ξ) atTop
        (𝓝 (Set.indicator ({ξ₀} : Set ℝ) (a : ℝ → ℂ) ξ)) := by
      refine Filter.Eventually.of_forall fun ξ => ?_
      have hg : Tendsto (fun n : ℕ =>
          ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ)) atTop
          (𝓝 (((Set.indicator ({ξ₀} : Set ℝ) (fun _ => (1 : ℝ)) ξ : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp (deningerAtomGauss_tendsto ξ₀ ξ)
      have hval : (((Set.indicator ({ξ₀} : Set ℝ) (fun _ => (1 : ℝ)) ξ : ℝ)) : ℂ)
            * (a : ℝ → ℂ) ξ = Set.indicator ({ξ₀} : Set ℝ) (a : ℝ → ℂ) ξ := by
        by_cases hx : ξ = ξ₀
        · subst hx
          rw [Set.indicator_of_mem (Set.mem_singleton _),
            Set.indicator_of_mem (Set.mem_singleton _)]
          simp
        · rw [Set.indicator_of_notMem (by simpa using hx),
            Set.indicator_of_notMem (by simpa using hx)]
          simp
      rw [← hval]
      exact hg.mul tendsto_const_nhds
    have hconv := tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hlim
    have hzero' : (fun n : ℕ => ∫ ξ,
        ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * (a : ℝ → ℂ) ξ
          ∂deningerFloquetMeasure) = fun _ : ℕ => (0 : ℂ) := funext fun n => hint ξ₀ n
    rw [hzero'] at hconv
    have hval : ∫ ξ, Set.indicator ({ξ₀} : Set ℝ) (a : ℝ → ℂ) ξ ∂deningerFloquetMeasure = 0 :=
      tendsto_nhds_unique hconv tendsto_const_nhds
    rwa [integral_indicator (measurableSet_singleton _), integral_singleton] at hval
  have hnode : ∀ ξ₀ ∈ deningerFloquetSupport, (a : ℝ → ℂ) ξ₀ = 0 := by
    intro ξ₀ hξ₀
    have hpos := deningerFloquetMeasure_singleton_pos hξ₀
    have hlt := deningerFloquetMeasure_singleton_lt_top ξ₀
    have hne : (deningerFloquetMeasure).real {ξ₀} ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hlt.ne⟩
    rcases smul_eq_zero.1 (hpt ξ₀) with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hae : (a : ℝ → ℂ) =ᵐ[deningerFloquetMeasure] 0 :=
    deningerFloquetMeasure_ae_eq_zero hnode
  exact Lp.ext_iff.2 (hae.trans (Lp.coeFn_zero ℂ 2 deningerFloquetMeasure).symm)

/-- **The Mellin samples span a dense subspace of `L²(μ_Fl)`.**  With the isometry, this is the
statement that the Hilbert completion of the source for the half-density Floquet energy is `L²` of
the arithmetic lattice measure. -/
theorem deningerFloquetLp_span_topologicalClosure :
    (Submodule.span ℂ (Set.range deningerFloquetLp)).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.2 deningerFloquetLp_orthogonal_eq_bot

end

end RHTower
