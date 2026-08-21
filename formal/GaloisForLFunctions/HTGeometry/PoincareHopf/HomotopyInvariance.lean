import GaloisForLFunctions.HTGeometry.PoincareHopf.HomotopyDerivative

/-!
# Homotopy invariance of the degree integral along an affine path

If `‖f + t (g - f)‖ > ρ` on the boundary of a bounded open set `Ω` for every `t ∈ [0,1]`, and the
weight `φ` vanishes outside the ball of radius `ρ`, then `f` and `g` have the same degree integral.

The parameter derivative of the integrand is the cofactor pairing of the Jacobian of a field that
vanishes near `∂Ω`, so each slice integrates to zero by the vanishing lemma; the fundamental theorem
of calculus in `t` and Fubini assemble the slices into the difference of the two degree integrals.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f g : (Fin n → ℝ) → (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
  {Ω : Set (Fin n → ℝ)} {ρ : ℝ}

theorem continuous_matrix_det {X : Type*} [TopologicalSpace X]
    {N : X → Matrix (Fin n) (Fin n) ℝ} (hN : ∀ a b, Continuous fun p => N p a b) :
    Continuous fun p => (N p).det := by
  simp only [Matrix.det_apply']
  exact continuous_finsetSum _ fun σ _ =>
    continuous_const.mul (continuous_finsetProd _ fun k _ => hN (σ k) k)

theorem continuous_cofSum {X : Type*} [TopologicalSpace X]
    {N : X → Matrix (Fin n) (Fin n) ℝ} (hN : ∀ a b, Continuous fun p => N p a b) (i j : Fin n) :
    Continuous fun p => cofSum (N p) i j := by
  simp only [cofSum]
  exact continuous_finsetSum _ fun σ _ =>
    continuous_const.mul (continuous_finsetProd _ fun k _ => hN (σ k) k)

theorem contDiff_homField (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (t : ℝ) : ContDiff ℝ 1 (homField f g φ t) :=
  ContDiff.smul (hφ.comp ((contDiff_linPath hf hg t).of_le (by norm_num)))
    ((hg.sub hf).of_le (by norm_num))

theorem homField_eventuallyEq_zero (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hφsupp : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → φ w = 0) {t : ℝ} {x : Fin n → ℝ}
    (hx : ρ < ‖linPath f g t x‖) : homField f g φ t =ᶠ[nhds x] 0 := by
  have hcont : Continuous fun z => ‖linPath f g t z‖ :=
    ((contDiff_linPath hf hg t).continuous).norm
  have hopen : IsOpen {z : Fin n → ℝ | ρ < ‖linPath f g t z‖} := isOpen_lt continuous_const hcont
  filter_upwards [hopen.mem_nhds hx] with z hz
  have : φ (linPath f g t z) = 0 := hφsupp _ (le_of_lt hz)
  simp [homField, this]

/-- Each slice of the parameter family integrates to zero. -/
theorem integral_homDeriv_eq_zero (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hφ : ContDiff ℝ 1 φ) (hφsupp : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → φ w = 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {t : ℝ}
    (hfront : ∀ x ∈ frontier Ω, ρ < ‖linPath f g t x‖) :
    ∫ x in Ω, homDeriv f g φ t x = 0 := by
  have hzero := integral_cofSum_mul_jac_eq_zero (u := linPath f g t) (G := homField f g φ t)
    (contDiff_linPath hf hg t) (contDiff_homField hf hg hφ t) hΩ hΩb
    (fun x hx => homField_eventuallyEq_zero hf hg hφsupp (hfront x hx))
  rw [← hzero]
  exact setIntegral_congr_fun hΩ.measurableSet
    (fun x _ => homDeriv_eq_cofPairing hf hg hφ t x)

theorem continuous_uncurry_homDeriv (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hφ : ContDiff ℝ 1 φ) :
    Continuous (Function.uncurry fun (x : Fin n → ℝ) (t : ℝ) => homDeriv f g φ t x) := by
  have hjf : ∀ a b : Fin n, Continuous fun x : Fin n → ℝ => jac f x a b :=
    fun a b => (contDiff_jacEntry hf a b).continuous
  have hjg : ∀ a b : Fin n, Continuous fun x : Fin n → ℝ => jac g x a b :=
    fun a b => (contDiff_jacEntry hg a b).continuous
  have hM : ∀ a b : Fin n,
      Continuous fun p : (Fin n → ℝ) × ℝ => jac (linPath f g p.2) p.1 a b := by
    intro a b
    have heq : (fun p : (Fin n → ℝ) × ℝ => jac (linPath f g p.2) p.1 a b)
        = fun p : (Fin n → ℝ) × ℝ =>
            jac f p.1 a b + p.2 * (jac g p.1 a b - jac f p.1 a b) := by
      funext p
      exact jac_linPath hf hg p.2 p.1 a b
    rw [heq]
    exact ((hjf a b).comp continuous_fst).add
      (continuous_snd.mul (((hjg a b).comp continuous_fst).sub ((hjf a b).comp continuous_fst)))
  have hpath : Continuous fun p : (Fin n → ℝ) × ℝ => linPath f g p.2 p.1 := by
    have : (fun p : (Fin n → ℝ) × ℝ => linPath f g p.2 p.1)
        = fun p : (Fin n → ℝ) × ℝ => f p.1 + p.2 • (g p.1 - f p.1) := rfl
    rw [this]
    exact (hf.continuous.comp continuous_fst).add
      (continuous_snd.smul ((hg.continuous.comp continuous_fst).sub
        (hf.continuous.comp continuous_fst)))
  have hfdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hA : Continuous fun p : (Fin n → ℝ) × ℝ => g p.1 - f p.1 :=
    (hg.continuous.comp continuous_fst).sub (hf.continuous.comp continuous_fst)
  have hterm1 : Continuous fun p : (Fin n → ℝ) × ℝ =>
      (fderiv ℝ φ (linPath f g p.2 p.1)) (g p.1 - f p.1) * (jac (linPath f g p.2) p.1).det :=
    ((hfdφ.comp hpath).clm_apply hA).mul (continuous_matrix_det hM)
  have hterm2 : Continuous fun p : (Fin n → ℝ) × ℝ =>
      φ (linPath f g p.2 p.1) *
        ∑ i, ∑ j, cofSum (jac (linPath f g p.2) p.1) i j * (jac g p.1 i j - jac f p.1 i j) := by
    refine (hφ.continuous.comp hpath).mul ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_cofSum hM i j).mul
      (((hjg i j).comp continuous_fst).sub ((hjf i j).comp continuous_fst))
  exact hterm1.add hterm2

/-- **Homotopy invariance of the degree integral along an affine path.** -/
theorem degIntegral_linPath_eq (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (hφsupp : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → φ w = 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfront : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier Ω, ρ < ‖linPath f g t x‖) :
    degIntegral g Ω φ = degIntegral f Ω φ := by
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  set D : (Fin n → ℝ) → ℝ → ℝ := fun x t => homDeriv f g φ t x with hD
  have hDcont : Continuous (Function.uncurry D) := continuous_uncurry_homDeriv hf hg hφ
  have hslice : ∀ t ∈ Ioc (0 : ℝ) 1, (∫ x in Ω, D x t) = 0 := fun t ht =>
    integral_homDeriv_eq_zero hf hg hφ hφsupp hΩ hΩb (hfront t ⟨ht.1.le, ht.2⟩)
  have hFTC : ∀ x, (∫ t in Ioc (0 : ℝ) 1, D x t)
      = φ (g x) * (jac g x).det - φ (f x) * (jac f x).det := by
    intro x
    have hsc : Continuous fun t : ℝ => D x t := by
      have hpair : Continuous fun t : ℝ => ((x : Fin n → ℝ), t) :=
        continuous_const.prodMk continuous_id
      simpa [Function.comp_def] using hDcont.comp hpair
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => φ (linPath f g s x) * (jac (linPath f g s) x).det) (D x s) s :=
      fun s _ => hasDerivAt_homIntegrand hf hg hφ s x
    have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hsc.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at hsub
    rw [hsub, linPath_zero, linPath_one]
  have hint : Integrable (Function.uncurry D)
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hK : IsCompact ((closure Ω) ×ˢ (Icc (0 : ℝ) 1)) :=
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDcont.continuousOn
    rw [Measure.prod_restrict]
    haveI : IsFiniteMeasure ((volume.prod volume).restrict (Ω ×ˢ Ioc (0 : ℝ) 1)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top hΩb.measure_lt_top measure_Ioc_lt_top
    refine Integrable.mono' (g := fun _ => C) (integrable_const C)
      hDcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (hΩm.prod measurableSet_Ioc)] with p hp
    exact hC p ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩
  have hI1 : IntegrableOn (fun x => φ (g x) * (jac g x).det) Ω :=
    integrableOn_of_continuous ((hφ.continuous.comp hg.continuous).mul (continuous_det_jac hg))
      hΩm hΩb
  have hI2 : IntegrableOn (fun x => φ (f x) * (jac f x).det) Ω :=
    integrableOn_of_continuous ((hφ.continuous.comp hf.continuous).mul (continuous_det_jac hf))
      hΩm hΩb
  have hdiff : degIntegral g Ω φ - degIntegral f Ω φ
      = ∫ x in Ω, (φ (g x) * (jac g x).det - φ (f x) * (jac f x).det) := by
    rw [degIntegral, degIntegral, ← MeasureTheory.integral_sub hI1 hI2]
  have hswap : (∫ x in Ω, ∫ t in Ioc (0 : ℝ) 1, D x t)
      = ∫ t in Ioc (0 : ℝ) 1, ∫ x in Ω, D x t := MeasureTheory.integral_integral_swap hint
  have hzero : (∫ t in Ioc (0 : ℝ) 1, ∫ x in Ω, D x t) = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hslice]
    simp
  have hfinal : degIntegral g Ω φ - degIntegral f Ω φ = 0 := by
    rw [hdiff, ← MeasureTheory.setIntegral_congr_fun hΩm (fun x (_ : x ∈ Ω) => hFTC x),
      hswap, hzero]
  linarith [hfinal]

end GaloisForLFunctions.HTGeometry.PoincareHopf
