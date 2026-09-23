import GaloisForLFunctions.RHTower.ThetaWienerHopfInjectivity

/-!
# The retarded half-line transgression is injective on `L²` of the half line

An exponential weight converts a square-integrable half-line datum into an integrable one, and it
converts the kernel by the opposite weight, so the transgression identity is preserved up to the
scalar `exp(-εx)`.  Injectivity on integrable data therefore upgrades to injectivity on `L²(ℝ₊)`
for every kernel with a one-sided exponential margin — which the theta kernel has.

* `RHTower.halfLineConvMinus_weighted`;
* `RHTower.eq_zero_of_halfLineConvMinus_eq_zero_memLp_two`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform Topology

namespace RHTower

/-- The exponential weight applied to a datum. -/
def expWeight (eps : ℝ) (f : ℝ → ℂ) (L : ℝ) : ℂ := f L * ((Real.exp (-(eps * L)) : ℝ) : ℂ)

theorem expWeight_apply (eps : ℝ) (f : ℝ → ℂ) (L : ℝ) :
    expWeight eps f L = f L * ((Real.exp (-(eps * L)) : ℝ) : ℂ) := rfl

/-- **The weighted transgression identity.**  Weighting the kernel and the datum by opposite
exponentials multiplies the transgression by a nonvanishing scalar. -/
theorem halfLineConvMinus_weighted (eps : ℝ) (k g : ℝ → ℂ) (x : ℝ) :
    halfLineConvMinus (expWeight eps k) (expWeight eps g) x
      = ((Real.exp (-(eps * x)) : ℝ) : ℂ) * halfLineConvMinus k g x := by
  rw [halfLineConvMinus, halfLineConvMinus, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (.of_forall fun L => ?_)
  show expWeight eps k (x - L) * expWeight eps g L
    = ((Real.exp (-(eps * x)) : ℝ) : ℂ) * (k (x - L) * g L)
  rw [expWeight_apply, expWeight_apply]
  have hexp : ((Real.exp (-(eps * (x - L))) : ℝ) : ℂ) * ((Real.exp (-(eps * L)) : ℝ) : ℂ)
      = ((Real.exp (-(eps * x)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc (k (x - L) * ((Real.exp (-(eps * (x - L))) : ℝ) : ℂ))
        * (g L * ((Real.exp (-(eps * L)) : ℝ) : ℂ))
      = (k (x - L) * g L)
        * (((Real.exp (-(eps * (x - L))) : ℝ) : ℂ) * ((Real.exp (-(eps * L)) : ℝ) : ℂ)) := by ring
    _ = ((Real.exp (-(eps * x)) : ℝ) : ℂ) * (k (x - L) * g L) := by rw [hexp]; ring

theorem memLp_two_expWeightKernel {eps : ℝ} (heps : 0 < eps) :
    MemLp (fun L : ℝ => ((Real.exp (-(eps * L)) : ℝ) : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable (fun L : ℝ => ((Real.exp (-(eps * L)) : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  have hsq : ∀ L : ℝ, ‖((Real.exp (-(eps * L)) : ℝ) : ℂ)‖ ^ (2 : ℕ) = Real.exp (-(2 * eps) * L) := by
    intro L
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hint : IntegrableOn (fun L : ℝ => Real.exp (-(2 * eps) * L)) (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro L _
  exact (hsq L).symm

/-- Weighting a square-integrable half-line datum by a decaying exponential makes it integrable. -/
theorem integrable_expWeight_of_memLp_two {eps : ℝ} (heps : 0 < eps) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ))))
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) :
    Integrable (expWeight eps g) := by
  have hmul : Integrable (g * fun L : ℝ => ((Real.exp (-(eps * L)) : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    hg.integrable_mul (memLp_two_expWeightKernel heps)
  have hon : IntegrableOn (expWeight eps g) (Ioi (0 : ℝ)) := hmul
  refine (integrableOn_univ (μ := (volume : Measure ℝ))).mp ?_
  have hsplit : (Set.univ : Set ℝ) = Iic 0 ∪ Ioi 0 := by
    ext L
    simp
  rw [hsplit]
  refine IntegrableOn.union ?_ hon
  have hzero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Iic (0 : ℝ)) := integrableOn_zero
  refine hzero.congr_fun ?_ measurableSet_Iic
  intro L hL
  rw [expWeight_apply, hsupp L hL, zero_mul]

/-- **Injectivity of the retarded transgression on `L²(ℝ₊)`.**  If the kernel has an exponential
margin `ε` on the left and the weighted symbol is nonzero almost everywhere, then no nonzero
square-integrable half-line datum is annihilated. -/
theorem eq_zero_of_halfLineConvMinus_eq_zero_memLp_two {eps : ℝ} (heps : 0 < eps) {k : ℝ → ℂ}
    (hk : Integrable (expWeight eps k)) (hKne : ∀ᵐ ξ : ℝ, 𝓕 (expWeight eps k) ξ ≠ 0)
    {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ))))
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) (h : ∀ x : ℝ, halfLineConvMinus k g x = 0) :
    g =ᵐ[volume] 0 := by
  have hgw : Integrable (expWeight eps g) := integrable_expWeight_of_memLp_two heps hg hsupp
  have hsuppw : ∀ L : ℝ, L ≤ 0 → expWeight eps g L = 0 := by
    intro L hL
    rw [expWeight_apply, hsupp L hL, zero_mul]
  have hzero : ∀ x : ℝ, halfLineConvMinus (expWeight eps k) (expWeight eps g) x = 0 := by
    intro x
    rw [halfLineConvMinus_weighted, h x, mul_zero]
  have hgwzero := eq_zero_of_halfLineConvMinus_eq_zero hk hKne hgw hsuppw hzero
  filter_upwards [hgwzero] with L hL
  have hval : g L * ((Real.exp (-(eps * L)) : ℝ) : ℂ) = 0 := hL
  have hne : ((Real.exp (-(eps * L)) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.exp_pos _).ne'
  exact (mul_eq_zero.mp hval).resolve_right hne

/-- The entire-symbol form of `L²` injectivity. -/
theorem eq_zero_of_halfLineConvMinus_eq_zero_memLp_two_of_entire {eps : ℝ} (heps : 0 < eps)
    {k : ℝ → ℂ} (hk : Integrable (expWeight eps k))
    {K : ℂ → ℂ} (hKanalytic : AnalyticOnNhd ℂ K Set.univ) (hKne : ∃ z, K z ≠ 0)
    (hKsymbol : ∀ ξ : ℝ, 𝓕 (expWeight eps k) ξ = K (ξ : ℂ))
    {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ))))
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) (h : ∀ x : ℝ, halfLineConvMinus k g x = 0) :
    g =ᵐ[volume] 0 := by
  refine eq_zero_of_halfLineConvMinus_eq_zero_memLp_two heps hk ?_ hg hsupp h
  have hnull := HTGeometry.volume_real_setOf_eq_zero_eq_zero hKanalytic hKne
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro ξ hξ
  simp only [Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [← hKsymbol ξ]
  exact hξ

/-- **The boundary wall.**  Under an exponential kernel margin, two half-line data with integrable
exponential weights and the same transgression coincide.  In particular a square-integrable datum
and a merely bounded one cannot have the same transgression unless they agree. -/
theorem eq_of_halfLineConvMinus_eq_weighted {eps : ℝ} {k : ℝ → ℂ}
    (hk : Integrable (expWeight eps k)) (hKne : ∀ᵐ ξ : ℝ, 𝓕 (expWeight eps k) ξ ≠ 0)
    {g₁ g₂ : ℝ → ℂ} (hg₁ : Integrable (expWeight eps g₁)) (hg₂ : Integrable (expWeight eps g₂))
    (hs₁ : ∀ L : ℝ, L ≤ 0 → g₁ L = 0) (hs₂ : ∀ L : ℝ, L ≤ 0 → g₂ L = 0)
    (h : ∀ x : ℝ, halfLineConvMinus k g₁ x = halfLineConvMinus k g₂ x) :
    g₁ =ᵐ[volume] g₂ := by
  have hw₁ : ∀ L : ℝ, L ≤ 0 → expWeight eps g₁ L = 0 := by
    intro L hL
    rw [expWeight_apply, hs₁ L hL, zero_mul]
  have hw₂ : ∀ L : ℝ, L ≤ 0 → expWeight eps g₂ L = 0 := by
    intro L hL
    rw [expWeight_apply, hs₂ L hL, zero_mul]
  have hconv : ∀ x : ℝ, halfLineConvMinus (expWeight eps k) (expWeight eps g₁) x
      = halfLineConvMinus (expWeight eps k) (expWeight eps g₂) x := by
    intro x
    rw [halfLineConvMinus_weighted, halfLineConvMinus_weighted, h x]
  have hwe := eq_of_halfLineConvMinus_eq hk hKne hg₁ hg₂ hw₁ hw₂ hconv
  filter_upwards [hwe] with L hL
  have hval : g₁ L * ((Real.exp (-(eps * L)) : ℝ) : ℂ)
      = g₂ L * ((Real.exp (-(eps * L)) : ℝ) : ℂ) := hL
  have hne : ((Real.exp (-(eps * L)) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.exp_pos _).ne'
  exact mul_right_cancel₀ hne hval

/-- A bounded half-line datum has integrable exponential weight. -/
theorem integrable_expWeight_of_bounded {eps : ℝ} (heps : 0 < eps) {g : ℝ → ℂ} {C : ℝ}
    (hmeas : Measurable g) (hbdd : ∀ L : ℝ, ‖g L‖ ≤ C)
    (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0) :
    Integrable (expWeight eps g) := by
  have hmeasw : Measurable (expWeight eps g) := by
    have : Measurable fun L : ℝ => ((Real.exp (-(eps * L)) : ℝ) : ℂ) := by fun_prop
    exact hmeas.mul this
  have hon : IntegrableOn (expWeight eps g) (Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun L : ℝ => C * Real.exp (-eps * L)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 heps).const_mul C
    refine MeasureTheory.Integrable.mono hdom hmeasw.aestronglyMeasurable ?_
    filter_upwards with L
    rw [expWeight_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg (g 0)) (hbdd 0)
    have hexp : Real.exp (-(eps * L)) = Real.exp (-eps * L) := by
      congr 1
      ring
    rw [hexp, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hbdd L) (Real.exp_pos _).le
  refine (integrableOn_univ (μ := (volume : Measure ℝ))).mp ?_
  have hsplit : (Set.univ : Set ℝ) = Iic 0 ∪ Ioi 0 := by
    ext L
    simp
  rw [hsplit]
  refine IntegrableOn.union ?_ hon
  have hzero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Iic (0 : ℝ)) := integrableOn_zero
  refine hzero.congr_fun ?_ measurableSet_Iic
  intro L hL
  rw [expWeight_apply, hsupp L hL, zero_mul]

theorem halfLineConvMinus_zeroExtend (k f : ℝ → ℂ) (x : ℝ) :
    halfLineConvMinus k (zeroExtend f) x = halfLineConvMinus k f x := by
  rw [halfLineConvMinus, halfLineConvMinus]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun L hL => ?_)
  rw [zeroExtend, Set.indicator_of_mem hL]

/-- **The exact `L²` wall of Theorem 4.**  On the critical line the canonical input is the unique
half-line datum with its transgression, and it is not square-integrable: no square-integrable datum
reproduces the reflection-fold primitive. -/
theorem not_exists_memLp_two_of_halfLineConvMinus_eq_canonical {eps : ℝ} (heps : 0 < eps)
    {k : ℝ → ℂ} (hk : Integrable (expWeight eps k))
    (hKne : ∀ᵐ ξ : ℝ, 𝓕 (expWeight eps k) ξ ≠ 0)
    {lam : ℂ} (hlam : lam.re = 0) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) (hsupp : ∀ L : ℝ, L ≤ 0 → g L = 0)
    (h : ∀ x : ℝ, halfLineConvMinus k g x = halfLineConvMinus k (canonicalHalfLineInput lam) x) :
    False := by
  set f : ℝ → ℂ := zeroExtend (canonicalHalfLineInput lam) with hf
  have hfsupp : ∀ L : ℝ, L ≤ 0 → f L = 0 := by
    intro L hL
    rw [hf, zeroExtend, Set.indicator_of_notMem (by simpa using hL)]
  have hfmeas : Measurable f := by
    refine Measurable.indicator ?_ measurableSet_Ioi
    have : Continuous (canonicalHalfLineInput lam) := by
      unfold canonicalHalfLineInput
      fun_prop
    exact this.measurable
  have hfbdd : ∀ L : ℝ, ‖f L‖ ≤ 1 := by
    intro L
    by_cases hL : L ∈ Ioi (0 : ℝ)
    · rw [hf, zeroExtend, Set.indicator_of_mem hL, norm_canonicalHalfLineInput_eq_one hlam]
    · rw [hf, zeroExtend, Set.indicator_of_notMem hL, norm_zero]
      norm_num
  have hfint : Integrable (expWeight eps f) :=
    integrable_expWeight_of_bounded heps hfmeas hfbdd hfsupp
  have hgint : Integrable (expWeight eps g) :=
    integrable_expWeight_of_memLp_two heps hg hsupp
  have hconv : ∀ x : ℝ, halfLineConvMinus k g x = halfLineConvMinus k f x := by
    intro x
    rw [hf, halfLineConvMinus_zeroExtend]
    exact h x
  have hae := eq_of_halfLineConvMinus_eq_weighted hk hKne hgint hfint hsupp hfsupp hconv
  have hfLp : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := by
    refine hg.ae_eq ?_
    exact ae_restrict_of_ae hae
  have hsq : IntegrableOn (fun L : ℝ => ‖canonicalHalfLineInput lam L‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
      hfmeas.aestronglyMeasurable
    have hI : IntegrableOn (fun L : ℝ => ‖f L‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).1 hfLp
    refine hI.congr_fun ?_ measurableSet_Ioi
    intro L hL
    show ‖f L‖ ^ (2 : ℕ) = ‖canonicalHalfLineInput lam L‖ ^ (2 : ℕ)
    rw [hf, zeroExtend, Set.indicator_of_mem hL]
  exact not_integrableOn_norm_sq_canonicalHalfLineInput (le_of_eq hlam) hsq

/-! ### Nonnegativity of the half-line Neumann and Dirichlet forms -/

/-- **Green's identity on the half line.**  For a compactly supported `C²` datum satisfying either
the Neumann or the Dirichlet boundary condition, the quadratic form of `-∂_L²` is the Dirichlet
energy, hence nonnegative and real. -/
theorem integral_neg_secondDeriv_mul_conj (y y' y'' : ℝ → ℂ)
    (hy : ∀ L : ℝ, HasDerivAt y (y' L) L) (hy' : ∀ L : ℝ, HasDerivAt y' (y'' L) L)
    (hbdry : y' 0 * (starRingEnd ℂ) (y 0) = 0)
    (hint₁ : IntegrableOn (fun L : ℝ => y'' L * (starRingEnd ℂ) (y L)) (Ioi (0 : ℝ)))
    (hint₂ : IntegrableOn (fun L : ℝ => y' L * (starRingEnd ℂ) (y' L)) (Ioi (0 : ℝ)))
    (hlim : Filter.Tendsto (fun L : ℝ => y' L * (starRingEnd ℂ) (y L)) Filter.atTop (nhds 0)) :
    (∫ L in Ioi (0 : ℝ), -(y'' L) * (starRingEnd ℂ) (y L))
      = ∫ L in Ioi (0 : ℝ), ((‖y' L‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hFderiv : ∀ L : ℝ, HasDerivAt (fun L : ℝ => y' L * (starRingEnd ℂ) (y L))
      (y'' L * (starRingEnd ℂ) (y L) + y' L * (starRingEnd ℂ) (y' L)) L := by
    intro L
    have hconj : HasDerivAt (fun L : ℝ => (starRingEnd ℂ) (y L)) ((starRingEnd ℂ) (y' L)) L :=
      (hy L).star
    exact (hy' L).mul hconj
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun L : ℝ => y' L * (starRingEnd ℂ) (y L))
    (f' := fun L : ℝ => y'' L * (starRingEnd ℂ) (y L) + y' L * (starRingEnd ℂ) (y' L))
    (a := (0 : ℝ)) ((hFderiv 0).continuousAt.continuousWithinAt)
    (fun L _ => hFderiv L) (hint₁.add hint₂) hlim
  rw [MeasureTheory.integral_add hint₁ hint₂, hbdry] at hmain
  have hsq : ∀ L : ℝ, y' L * (starRingEnd ℂ) (y' L) = ((‖y' L‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro L
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  have hneg : (∫ L in Ioi (0 : ℝ), -(y'' L) * (starRingEnd ℂ) (y L))
      = -∫ L in Ioi (0 : ℝ), y'' L * (starRingEnd ℂ) (y L) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun L _ => ?_)
    ring
  rw [hneg]
  simp only [hsq] at hmain ⊢
  linear_combination -hmain

end RHTower
