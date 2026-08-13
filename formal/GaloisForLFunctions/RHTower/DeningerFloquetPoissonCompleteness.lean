import GaloisForLFunctions.RHTower.DeningerFloquetPoissonClosure

/-!
# Completeness of the Poisson boundaries away from the resonant nodes

Scaling the explicit Poisson test function by `e^{-c}` multiplies its critical-line Mellin sample by
`e^{c/2}e^{-2πicξ}`, so a vector orthogonal to every Poisson boundary has vanishing Fourier
coefficient, at every frequency, against the fixed weight `ζ·M`.  Averaging those relations against
a Gaussian in the scaling parameter produces a Gaussian concentrating at a single node, and the
node is an atom, so the vector vanishes there whenever `ζ` does not.

* `deningerGaussianCharacter_integral` : the Gaussian character integral.
* `deningerFloquetBoundary_orthogonal_inf_eq_bot` : **the completeness computation.**
* `deningerFloquetBoundary_topologicalClosure` : **`(27)`, the closed Poisson-boundary space.**
* `deningerFloquetBoundary_closure_orthogonal` : **`(28)`, the exact Floquet Hilbert quotient.**
-/

namespace RHTower

open MeasureTheory Complex Set Filter Topology SchwartzMap
open GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace FourierTransform

noncomputable section

/-- **The Gaussian character integral.** -/
theorem deningerGaussianCharacter_integral {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    (∫ v : ℝ, Complex.exp (-(Real.pi : ℂ) * (ε : ℂ) * (v : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * (Complex.I * (y : ℂ)) * (v : ℂ)))
      = ((Real.sqrt ε : ℝ) : ℂ)⁻¹
        * Complex.exp (-(Real.pi : ℂ) / (ε : ℂ) * (y : ℂ) ^ 2) := by
  have hb : 0 < ((ε : ℂ)).re := by simpa using hε
  have h := congrFun (fourier_gaussian_pi' (b := (ε : ℂ)) hb (Complex.I * (y : ℂ))) 0
  have hzero : 𝓕 (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (ε : ℂ) * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * (Complex.I * (y : ℂ)) * (x : ℂ))) 0
      = ∫ v : ℝ, Complex.exp (-(Real.pi : ℂ) * (ε : ℂ) * (v : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * (Complex.I * (y : ℂ)) * (v : ℂ)) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp
  rw [hzero] at h
  rw [h]
  have hsqrt : ((ε : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt ε : ℝ) : ℂ) := by
    have h1 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
    rw [h1, ← Complex.ofReal_cpow hε.le, ← Real.sqrt_eq_rpow]
  have hsq : (((0 : ℝ) : ℂ) + Complex.I * (Complex.I * (y : ℂ))) ^ 2 = ((y : ℂ)) ^ 2 := by
    have hI : Complex.I * (Complex.I * (y : ℂ)) = -(y : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    rw [hI]
    push_cast
    ring
  rw [hsqrt, hsq, one_div]

/-! ## The completeness computation -/

/-- **No nonzero vector is orthogonal both to a family of scaled Poisson boundaries with
nowhere-vanishing Mellin profile and to every resonant node.** -/
theorem deningerFloquetFlow_orthogonal_inf_eq_bot (f₀ : DeningerMeyerCap)
    (hf₀ : ∀ ξ : ℝ,
      mellin (((f₀ : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) ≠ 0)
    {K : Submodule ℂ (Lp ℂ 2 deningerFloquetMeasure)}
    (hK : ∀ c : ℝ,
      deningerFloquetLp (deningerPoissonSource (deningerMeyerCapFlow c f₀)) ∈ K) :
    Kᗮ ⊓ deningerFloquetResonanceSpanᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
  obtain ⟨haK, haW⟩ := ha
  set A : ℝ → ℂ := (a : ℝ → ℂ) with hAdef
  set Q : ℝ → ℂ := deningerFloquetSample (deningerPoissonSource f₀) with hQdef
  set w : ℝ → ℂ := fun ξ => (starRingEnd ℂ) (Q ξ) * A ξ with hwdef
  have hQmem : MemLp Q 2 deningerFloquetMeasure :=
    deningerFloquetSample_memLp (deningerPoissonSource f₀)
  have hAmem : MemLp A 2 deningerFloquetMeasure := Lp.memLp a
  have hwmeas : AEStronglyMeasurable w deningerFloquetMeasure :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hQmem.1).mul hAmem.1
  have hwint : Integrable w deningerFloquetMeasure := by
    refine Integrable.mono' (MemLp.integrable_mul hQmem.norm hAmem.norm) hwmeas
      (Filter.Eventually.of_forall fun ξ => ?_)
    show ‖(starRingEnd ℂ) (Q ξ) * A ξ‖ ≤ ‖Q ξ‖ * ‖A ξ‖
    rw [norm_mul, RCLike.norm_conj]
  -- the character relations
  have hchar : ∀ c : ℝ, ∫ ξ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ : ℂ))
      * w ξ ∂deningerFloquetMeasure = 0 := by
    intro c
    have hmemK : deningerFloquetLp
        (deningerPoissonSource (deningerMeyerCapFlow c f₀)) ∈ K := hK c
    have hz := (Submodule.mem_orthogonal _ _).1 haK _ hmemK
    rw [L2.inner_def] at hz
    have hz' : ∫ ξ, Complex.exp ((c : ℂ) / 2)
        * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ : ℂ)) * w ξ)
        ∂deningerFloquetMeasure = 0 := by
      rw [← hz]
      refine integral_congr_ae ?_
      filter_upwards [deningerFloquetLp_coeFn
        (deningerPoissonSource (deningerMeyerCapFlow c f₀))] with ξ hξ
      rw [RCLike.inner_apply, hξ, deningerFloquetSample_capFlow]
      have hQval : riemannZeta (deningerCriticalLine ξ)
          * mellin (((f₀ : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
            (deningerCriticalLine ξ) = Q ξ :=
        (deningerFloquetSample_poissonSource f₀ ξ).symm
      rw [hQval]
      have hcs : (starRingEnd ℂ) ((c : ℂ) * deningerCriticalLine ξ)
          = (c : ℂ) / 2 + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ : ℂ) := by
        rw [deningerCriticalLine]
        simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_I,
          Complex.conj_ofReal]
        ring
      have hconj : (starRingEnd ℂ) (Complex.exp ((c : ℂ) * deningerCriticalLine ξ))
          = Complex.exp ((c : ℂ) / 2)
            * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ : ℂ)) := by
        rw [← Complex.exp_conj, hcs, Complex.exp_add]
      rw [map_mul, hconj, hwdef]
      ring
    rw [integral_const_mul] at hz'
    exact (mul_eq_zero.1 hz').resolve_left (Complex.exp_ne_zero _)
  -- the Gaussian average
  have hgauss : ∀ (ξ₀ : ℝ) (n : ℕ),
      ∫ ξ, ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ
        ∂deningerFloquetMeasure = 0 := by
    intro ξ₀ n
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hεdef
    have hε : 0 < ε := by
      rw [hεdef]
      positivity
    set F : ℝ → ℝ → ℂ := fun c ξ => Complex.exp (-(Real.pi : ℂ) * (ε : ℂ) * (c : ℂ) ^ 2
      + 2 * (Real.pi : ℂ) * (Complex.I * ((ξ : ℂ) - (ξ₀ : ℂ))) * (c : ℂ)) * w ξ with hFdef
    have hnorm : ∀ c ξ : ℝ, ‖F c ξ‖ = Real.exp (-(Real.pi * ε * c ^ 2)) * ‖w ξ‖ := by
      intro c ξ
      have hz : (-(Real.pi : ℂ) * (ε : ℂ) * (c : ℂ) ^ 2
          + 2 * (Real.pi : ℂ) * (Complex.I * ((ξ : ℂ) - (ξ₀ : ℂ))) * (c : ℂ))
          = ((-(Real.pi * ε * c ^ 2) : ℝ) : ℂ)
            + ((2 * Real.pi * (ξ - ξ₀) * c : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hre2 : (((-(Real.pi * ε * c ^ 2) : ℝ) : ℂ)
          + ((2 * Real.pi * (ξ - ξ₀) * c : ℝ) : ℂ) * Complex.I).re
          = -(Real.pi * ε * c ^ 2) := by
        rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [hFdef, norm_mul, Complex.norm_exp, hz, hre2]
    have hgaussInt : Integrable (fun c : ℝ => Real.exp (-(Real.pi * ε * c ^ 2))) volume := by
      have h := integrable_exp_neg_mul_sq (b := Real.pi * ε) (by positivity)
      refine h.congr (Filter.Eventually.of_forall fun c => ?_)
      ring_nf
    have hbound : Integrable (fun z : ℝ × ℝ => Real.exp (-(Real.pi * ε * z.1 ^ 2)) * ‖w z.2‖)
        (volume.prod deningerFloquetMeasure) := hgaussInt.mul_prod hwint.norm
    have hFmeas : AEStronglyMeasurable (Function.uncurry F)
        (volume.prod deningerFloquetMeasure) := by
      refine AEStronglyMeasurable.mul ?_ hwmeas.comp_snd
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have hFint : Integrable (Function.uncurry F) (volume.prod deningerFloquetMeasure) := by
      refine Integrable.mono' hbound hFmeas (Filter.Eventually.of_forall fun z => ?_)
      exact le_of_eq (hnorm z.1 z.2)
    have hswap := integral_integral_swap hFint
    have hleft : ∀ c : ℝ, ∫ ξ, F c ξ ∂deningerFloquetMeasure = 0 := by
      intro c
      have hsplit : ∀ ξ : ℝ, F c ξ
          = Complex.exp (-(Real.pi : ℂ) * (ε : ℂ) * (c : ℂ) ^ 2
              - 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ₀ : ℂ))
            * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (ξ : ℂ)) * w ξ) := by
        intro ξ
        rw [hFdef, ← mul_assoc, ← Complex.exp_add]
        ring_nf
      rw [funext hsplit, integral_const_mul, hchar c, mul_zero]
    rw [funext hleft, integral_zero] at hswap
    have hright : ∀ ξ : ℝ, ∫ c : ℝ, F c ξ
        = ((Real.sqrt ε : ℝ) : ℂ)⁻¹
          * Complex.exp (-(Real.pi : ℂ) / (ε : ℂ) * ((ξ : ℂ) - (ξ₀ : ℂ)) ^ 2) * w ξ := by
      intro ξ
      have hy := deningerGaussianCharacter_integral hε (ξ - ξ₀)
      have hcast : (((ξ - ξ₀ : ℝ)) : ℂ) = (ξ : ℂ) - (ξ₀ : ℂ) := by push_cast; ring
      rw [hcast] at hy
      rw [hFdef, MeasureTheory.integral_mul_const, ← hy]
    rw [funext hright] at hswap
    -- pull out the constant and identify the Gaussian
    have hεne : ((Real.sqrt ε : ℝ) : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hε).ne')
    have hcollect : ∫ ξ, ((Real.sqrt ε : ℝ) : ℂ)⁻¹
        * Complex.exp (-(Real.pi : ℂ) / (ε : ℂ) * ((ξ : ℂ) - (ξ₀ : ℂ)) ^ 2) * w ξ
        ∂deningerFloquetMeasure
        = ((Real.sqrt ε : ℝ) : ℂ)⁻¹ * ∫ ξ,
          ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ
          ∂deningerFloquetMeasure := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show ((Real.sqrt ε : ℝ) : ℂ)⁻¹
          * Complex.exp (-(Real.pi : ℂ) / (ε : ℂ) * ((ξ : ℂ) - (ξ₀ : ℂ)) ^ 2) * w ξ
        = ((Real.sqrt ε : ℝ) : ℂ)⁻¹
          * (((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ)
      rw [mul_assoc]
      congr 2
      rw [Complex.ofReal_exp]
      congr 1
      rw [hεdef]
      push_cast
      field_simp
    rw [hcollect] at hswap
    exact (mul_eq_zero.1 hswap.symm).resolve_left hεne
  -- concentration at a single node
  have hpt : ∀ ξ₀ : ℝ, (deningerFloquetMeasure.real {ξ₀} : ℝ) • w ξ₀ = 0 := by
    intro ξ₀
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun ξ => ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ)
        deningerFloquetMeasure := by
      intro n
      refine AEStronglyMeasurable.mul ?_ hwmeas
      refine Complex.continuous_ofReal.comp_aestronglyMeasurable ?_
      exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have hdom : ∀ n : ℕ, ∀ᵐ ξ ∂deningerFloquetMeasure,
        ‖((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ‖ ≤ ‖w ξ‖ := by
      intro n
      refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      refine Real.exp_le_one_iff.2 ?_
      have hnn : (0 : ℝ) ≤ Real.pi * (ξ - ξ₀) ^ 2 := by positivity
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hlim : ∀ᵐ ξ ∂deningerFloquetMeasure, Tendsto
        (fun n : ℕ => ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * w ξ)
        atTop (𝓝 (Set.indicator ({ξ₀} : Set ℝ) w ξ)) := by
      refine Filter.Eventually.of_forall fun ξ => ?_
      have hg : Tendsto (fun n : ℕ =>
          ((Real.exp (-(Real.pi * (ξ - ξ₀) ^ 2 * ((n : ℝ) + 1))) : ℝ) : ℂ)) atTop
          (𝓝 (((Set.indicator ({ξ₀} : Set ℝ) (fun _ => (1 : ℝ)) ξ : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp (deningerAtomGauss_tendsto ξ₀ ξ)
      have hval : (((Set.indicator ({ξ₀} : Set ℝ) (fun _ => (1 : ℝ)) ξ : ℝ)) : ℂ) * w ξ
          = Set.indicator ({ξ₀} : Set ℝ) w ξ := by
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
    have hconv := tendsto_integral_of_dominated_convergence _ hmeas hwint.norm hdom hlim
    rw [funext (hgauss ξ₀)] at hconv
    have hval : ∫ ξ, Set.indicator ({ξ₀} : Set ℝ) w ξ ∂deningerFloquetMeasure = 0 :=
      tendsto_nhds_unique hconv tendsto_const_nhds
    rwa [integral_indicator (measurableSet_singleton _), integral_singleton] at hval
  -- vanishing at every node
  have hnode : ∀ ξ₀ ∈ deningerFloquetSupport, A ξ₀ = 0 := by
    intro ξ₀ hξ₀
    have hne : (deningerFloquetMeasure.real {ξ₀} : ℝ) ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨(deningerFloquetMeasure_singleton_pos hξ₀).ne',
        (deningerFloquetMeasure_singleton_lt_top ξ₀).ne⟩
    by_cases hζ : riemannZeta (deningerCriticalLine ξ₀) = 0
    · have hres : ξ₀ ∈ deningerFloquetResonance := ⟨hξ₀, hζ⟩
      have hz := (Submodule.mem_orthogonal _ _).1 haW _
        (Submodule.subset_span ⟨ξ₀, hres, rfl⟩)
      rw [inner_deningerFloquetAtomLp_self] at hz
      exact (smul_eq_zero.1 hz).resolve_left hne
    · have hw0 : w ξ₀ = 0 := (smul_eq_zero.1 (hpt ξ₀)).resolve_left hne
      have hQ0 : (starRingEnd ℂ) (Q ξ₀) ≠ 0 := by
        have hQne : Q ξ₀ ≠ 0 := by
          rw [hQdef, deningerFloquetSample_poissonSource]
          exact mul_ne_zero hζ (hf₀ ξ₀)
        simpa using hQne
      exact (mul_eq_zero.1 hw0).resolve_left hQ0
  have hae : A =ᵐ[deningerFloquetMeasure] 0 := deningerFloquetMeasure_ae_eq_zero hnode
  exact Lp.ext_iff.2 (hae.trans (Lp.coeFn_zero ℂ 2 deningerFloquetMeasure).symm)

/-- **No nonzero vector is orthogonal both to every Poisson boundary and to every resonant
node.** -/
theorem deningerFloquetBoundary_orthogonal_inf_eq_bot :
    deningerFloquetBoundaryᗮ ⊓ deningerFloquetResonanceSpanᗮ = ⊥ :=
  deningerFloquetFlow_orthogonal_inf_eq_bot meyerPoissonTestSource
    (fun ξ => deningerFloquetProfile_ne_zero ξ)
    (fun _ => Submodule.subset_span ⟨_, rfl⟩)

/-- **The closed Poisson-boundary space is the annihilator of the resonant nodes.** -/
theorem deningerFloquetBoundary_topologicalClosure :
    deningerFloquetBoundary.topologicalClosure = deningerFloquetResonanceSpanᗮ :=
  submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot deningerFloquetBoundary_le
    (Submodule.isClosed_orthogonal _) deningerFloquetBoundary_orthogonal_inf_eq_bot

/-- **The exact Floquet Hilbert quotient.**  The orthogonal complement of the closed Poisson
boundary is the closed span of the resonant node indicators. -/
theorem deningerFloquetBoundary_closure_orthogonal :
    (deningerFloquetBoundary.topologicalClosure)ᗮ
      = deningerFloquetResonanceSpan.topologicalClosure := by
  rw [deningerFloquetBoundary_topologicalClosure,
    Submodule.orthogonal_orthogonal_eq_closure]

end

end RHTower
