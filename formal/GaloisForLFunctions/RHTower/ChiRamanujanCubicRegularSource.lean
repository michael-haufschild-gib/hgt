import GaloisForLFunctions.RHTower.ChiRamanujanWeightedCubicContractions
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
/-!
# Pole-removed complete BAG cubic source

The complete weighted prime-coordinate trace has a smooth source through the critical
plane. Its exact connected decomposition retains both finite-part kernels, the mixed
principal-value kernel and the intersection kernel. No physical prime-source transfer or
critical distributional limit is asserted by this module.
-/

noncomputable section
open scoped BigOperators Topology ContDiff
namespace RHTower.BAGTrace

def residuePair (σ α : ℂ) : ℂ := zetaResidueFactor (σ+α)*zetaResidueFactor (σ-α)

def regularCubicSource (σ α β : ℂ) : ℂ :=
  residuePair σ α * residuePair σ β * cubicEulerCorrection σ α β / residuePair σ (α-β)

def regularAxisSource (σ α : ℂ) : ℂ := residuePair σ α * axisEulerCorrection σ α

theorem zetaResidueFactor_ne_zero_closed {s : ℂ} (hs : 1 ≤ s.re) :
    zetaResidueFactor s ≠ 0 := by
  by_cases h1 : s=1
  · simp [h1]
  · rw [zetaResidueFactor_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

theorem residuePair_ne_zero_closed {σ α : ℂ} (hσ : 1 ≤ σ.re) (hα : α.re=0) :
    residuePair σ α ≠ 0 := by
  apply mul_ne_zero <;> apply zetaResidueFactor_ne_zero_closed <;> simpa [hα] using hσ

theorem residuePair_neg (σ α : ℂ) : residuePair σ (-α) = residuePair σ α := by
  simp only [residuePair, sub_neg_eq_add, ← sub_eq_add_neg]
  exact mul_comm _ _

theorem regularCubicSource_zero_left {σ β : ℂ} (hσ : 1 ≤ σ.re) (hβ : β.re=0) :
    regularCubicSource σ 0 β = residuePair σ 0 := by
  simp only [regularCubicSource, cubicEulerCorrection_zero_left, mul_one, zero_sub, residuePair_neg]
  exact mul_div_cancel_right₀ _ (residuePair_ne_zero_closed hσ hβ)

theorem regularCubicSource_zero_right {σ α : ℂ} (hσ : 1 ≤ σ.re) (hα : α.re=0) :
    regularCubicSource σ α 0 = residuePair σ 0 := by
  simp only [regularCubicSource, cubicEulerCorrection_zero_right, mul_one, sub_zero]
  rw [mul_comm, mul_div_cancel_right₀ _ (residuePair_ne_zero_closed hσ hα)]

theorem regularAxisSource_zero (σ : ℂ) : regularAxisSource σ 0 = residuePair σ 0 := by
  simp [regularAxisSource, axisEulerCorrection_zero]

theorem regularCubicSource_one_zero : regularCubicSource 1 0 0 = 1 := by
  rw [regularCubicSource_zero_left (by simp) (by simp)]
  simp [residuePair]

def cubicRegularDomain : Set (Fin 3 → ℂ) :=
  {w | w ∈ cubicCoordinateTube ∧ residuePair (w 0) (w 1-w 2) ≠ 0}

private theorem differentiable_residuePair_comp {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun x => residuePair (f x) (g x)) :=
  (differentiable_zetaResidueFactor.comp (hf.add hg)).mul
    (differentiable_zetaResidueFactor.comp (hf.sub hg))

theorem isOpen_cubicRegularDomain : IsOpen cubicRegularDomain := by
  have hj : Continuous (fun w : Fin 3 → ℂ => residuePair (w 0) (w 1-w 2)) :=
    (differentiable_residuePair_comp (differentiable_apply 0)
      ((differentiable_apply 1).sub (differentiable_apply 2))).continuous
  exact isOpen_cubicCoordinateTube.inter (isOpen_ne_fun hj continuous_const)

theorem analyticOnNhd_regularCubicSource :
    AnalyticOnNhd ℂ (fun w : Fin 3 → ℂ => regularCubicSource (w 0) (w 1) (w 2))
      cubicRegularDomain := by
  have h0 : Differentiable ℂ (fun w : Fin 3 → ℂ => residuePair (w 0) (w 1)) :=
    differentiable_residuePair_comp (differentiable_apply 0) (differentiable_apply 1)
  have h1 : Differentiable ℂ (fun w : Fin 3 → ℂ => residuePair (w 0) (w 2)) :=
    differentiable_residuePair_comp (differentiable_apply 0) (differentiable_apply 2)
  have hd : Differentiable ℂ (fun w : Fin 3 → ℂ => residuePair (w 0) (w 1-w 2)) :=
    differentiable_residuePair_comp (differentiable_apply 0)
      ((differentiable_apply 1).sub (differentiable_apply 2))
  have hH := analyticOnNhd_cubicEulerCorrection.differentiableOn.mono
    (show cubicRegularDomain ⊆ cubicCoordinateTube from fun _ h => h.1)
  have hi := hd.differentiableOn.inv (S := cubicRegularDomain) (fun _ h => h.2)
  have hdiff : DifferentiableOn ℂ
      (fun w : Fin 3 → ℂ => regularCubicSource (w 0) (w 1) (w 2)) cubicRegularDomain := by
    convert ((h0.differentiableOn.mul h1.differentiableOn).mul hH).mul hi using 1 <;> rfl
  intro w hw
  exact GaloisForLFunctions.HTGeometry.analyticAt_of_differentiableOn
    isOpen_cubicRegularDomain hdiff hw

theorem closed_frequency_mem_cubicRegularDomain {σ α β : ℂ}
    (hσ : 1 ≤ σ.re) (hα : α.re=0) (hβ : β.re=0) :
    ![σ,α,β] ∈ cubicRegularDomain := by
  refine ⟨?_, ?_⟩
  · change (σ,α,β) ∈ cubicTube
    exact ⟨by linarith, by simp [hα], by simp [hβ]⟩
  · exact residuePair_ne_zero_closed hσ (by simp [hα,hβ])

def zetaPair (σ α : ℂ) : ℂ := riemannZeta (σ+α)*riemannZeta (σ-α)

def poleDenominator (σ α : ℂ) : ℂ := (σ-1)^2-α^2

def cubicMellinValue (σ α β : ℂ) : ℂ :=
  cubicEulerCorrection σ α β * zetaPair σ α * zetaPair σ β / zetaPair σ (α-β)

def axisMellinValue (σ α : ℂ) : ℂ := axisEulerCorrection σ α * zetaPair σ α

theorem zetaPair_ne_zero {σ α : ℂ} (hσ : 1 ≤ σ.re) (hα : α.re=0) : zetaPair σ α ≠ 0 := by
  apply mul_ne_zero <;> apply riemannZeta_ne_zero_of_one_le_re <;> simpa [hα] using hσ

theorem residuePair_eq {σ α : ℂ} (hp : σ+α ≠ 1) (hm : σ-α ≠ 1) :
    residuePair σ α = poleDenominator σ α * zetaPair σ α := by
  rw [residuePair, zetaResidueFactor_of_ne hp, zetaResidueFactor_of_ne hm]
  unfold poleDenominator zetaPair
  ring

private theorem frequency_ne_one {σ α : ℂ} (hσ : 1 < σ.re) (hα : α.re=0) :
    σ+α ≠ 1 ∧ σ-α ≠ 1 := by
  constructor <;> intro he <;> have h := congrArg Complex.re he <;> simp [hα] at h <;> linarith

theorem poleDenominator_ne_zero {σ α : ℂ} (hσ : 1 < σ.re) (hα : α.re=0) :
    poleDenominator σ α ≠ 0 := by
  have h := frequency_ne_one hσ hα
  rw [show poleDenominator σ α = (σ+α-1)*(σ-α-1) by unfold poleDenominator; ring]
  exact mul_ne_zero (sub_ne_zero.mpr h.1) (sub_ne_zero.mpr h.2)

private theorem ratio_clear {a b c X Y Z H : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hZ : Z ≠ 0) :
    H*X*Y/Z = (a*X*(b*Y)*H/(c*Z))*c/(a*b) := by
  field_simp

theorem cubicMellinValue_eq_regular {σ α β : ℂ}
    (hσ : 1 < σ.re) (hα : α.re=0) (hβ : β.re=0) :
    cubicMellinValue σ α β = regularCubicSource σ α β * poleDenominator σ (α-β) /
      (poleDenominator σ α * poleDenominator σ β) := by
  have hab : (α-β).re=0 := by simp [hα,hβ]
  have ha := frequency_ne_one hσ hα
  have hb := frequency_ne_one hσ hβ
  have hc := frequency_ne_one hσ hab
  unfold cubicMellinValue regularCubicSource
  rw [residuePair_eq ha.1 ha.2, residuePair_eq hb.1 hb.2, residuePair_eq hc.1 hc.2]
  exact ratio_clear (poleDenominator_ne_zero hσ hα) (poleDenominator_ne_zero hσ hβ)
    (poleDenominator_ne_zero hσ hab) (zetaPair_ne_zero hσ.le hab)

theorem axisMellinValue_eq_regular {σ α : ℂ} (hσ : 1 < σ.re) (hα : α.re=0) :
    axisMellinValue σ α = regularAxisSource σ α / poleDenominator σ α := by
  have ha := frequency_ne_one hσ hα
  unfold axisMellinValue regularAxisSource
  rw [residuePair_eq ha.1 ha.2]
  field_simp [poleDenominator_ne_zero hσ hα]

private theorem six_zeta_eq_mellin (σ α β : ℂ) :
    cubicEulerCorrection σ α β *
      ((riemannZeta (σ+(β-α)))⁻¹ * (riemannZeta (σ+(α-β)))⁻¹) *
      riemannZeta (σ+α) * riemannZeta (σ+β) *
      riemannZeta (σ-α) * riemannZeta (σ-β) = cubicMellinValue σ α β := by
  rw [show σ+(β-α) = σ-(α-β) by ring]
  simp only [cubicMellinValue, zetaPair, div_eq_mul_inv, mul_inv_rev]
  ring

theorem complete_weighted_offAxes_mellin {σ α β : ℂ}
    (hσ : 1 < σ.re) (hα : α.re=0) (hβ : β.re=0) :
    Filter.Tendsto (weightedOffAxesTrace σ α β) Filter.atTop
      (𝓝 (cubicMellinValue σ α β-axisMellinValue σ β-axisMellinValue σ α+1)) := by
  have h := complete_weighted_offAxes_trace hσ hα hβ
  rw [six_zeta_eq_mellin] at h
  simpa only [axisMellinValue, zetaPair, mul_assoc] using h

theorem poleDenominator_real_frequency (σ u : ℝ) :
    poleDenominator (σ : ℂ) ((u : ℂ)*Complex.I) = (((σ-1)^2+u^2 : ℝ) : ℂ) := by
  unfold poleDenominator
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

def realCubicSource (σ u v : ℝ) : ℂ :=
  regularCubicSource σ ((u : ℂ)*Complex.I) ((v : ℂ)*Complex.I)

def realAxisSource (σ u : ℝ) : ℂ := regularAxisSource σ ((u : ℂ)*Complex.I)

private theorem connected_kernel_identity (e u v A T U : ℂ)
    (hu : e^2+u^2 ≠ 0) (hv : e^2+v^2 ≠ 0) :
    A*(e^2+(u-v)^2)/((e^2+u^2)*(e^2+v^2))-T/(e^2+u^2)-U/(e^2+v^2)+1 =
      (A-T)/(e^2+u^2)+(A-U)/(e^2+v^2)-e^2*A/((e^2+u^2)*(e^2+v^2))-
      2*u*v*A/((e^2+u^2)*(e^2+v^2))+1 := by
  field_simp
  ring

/-- Exact connected source with all singular terms retained. The first two numerators
vanish on their respective axes; the third term carries the intersection mass. -/
theorem complete_weighted_offAxes_regular_kernel {σ : ℝ} (hσ : 1 < σ) (u v : ℝ) :
    Filter.Tendsto (weightedOffAxesTrace σ ((u : ℂ)*Complex.I) ((v : ℂ)*Complex.I)) Filter.atTop
      (𝓝 ((realCubicSource σ u v-realAxisSource σ u)/(((σ-1)^2+u^2 : ℝ) : ℂ) +
        (realCubicSource σ u v-realAxisSource σ v)/(((σ-1)^2+v^2 : ℝ) : ℂ) -
        ((σ-1 : ℝ) : ℂ)^2*realCubicSource σ u v /
          ((((σ-1)^2+u^2 : ℝ) : ℂ)*(((σ-1)^2+v^2 : ℝ) : ℂ)) -
        2*(u : ℂ)*(v : ℂ)*realCubicSource σ u v /
          ((((σ-1)^2+u^2 : ℝ) : ℂ)*(((σ-1)^2+v^2 : ℝ) : ℂ)) + 1)) := by
  have hc : 1 < (σ : ℂ).re := hσ
  have hu : ((u : ℂ)*Complex.I).re=0 := by simp
  have hv : ((v : ℂ)*Complex.I).re=0 := by simp
  have h := complete_weighted_offAxes_mellin hc hu hv
  rw [cubicMellinValue_eq_regular hc hu hv, axisMellinValue_eq_regular hc hu,
    axisMellinValue_eq_regular hc hv] at h
  rw [show (u : ℂ)*Complex.I-(v : ℂ)*Complex.I = ((u-v : ℝ) : ℂ)*Complex.I by push_cast; ring,
    poleDenominator_real_frequency, poleDenominator_real_frequency,
    poleDenominator_real_frequency] at h
  have hdu : ((σ-1 : ℝ) : ℂ)^2+(u : ℂ)^2 ≠ 0 := by
    exact_mod_cast (show (σ-1)^2+u^2 ≠ 0 by nlinarith [sq_nonneg u])
  have hdv : ((σ-1 : ℝ) : ℂ)^2+(v : ℂ)^2 ≠ 0 := by
    exact_mod_cast (show (σ-1)^2+v^2 ≠ 0 by nlinarith [sq_nonneg v])
  have heq := connected_kernel_identity ((σ-1 : ℝ) : ℂ) (u : ℂ) (v : ℂ)
    (realCubicSource σ u v) (realAxisSource σ u) (realAxisSource σ v) hdu hdv
  simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_sub] at h
  change Filter.Tendsto _ _ (𝓝 (_-_ - _+1)) at h
  have heq' :
      realCubicSource σ u v * (((σ : ℂ)-1)^2+((u : ℂ)-(v : ℂ))^2) /
        ((((σ : ℂ)-1)^2+(u : ℂ)^2)*(((σ : ℂ)-1)^2+(v : ℂ)^2)) -
        realAxisSource σ v / (((σ : ℂ)-1)^2+(v : ℂ)^2) -
        realAxisSource σ u / (((σ : ℂ)-1)^2+(u : ℂ)^2)+1 =
      (realCubicSource σ u v-realAxisSource σ u)/(((σ-1)^2+u^2 : ℝ) : ℂ) +
        (realCubicSource σ u v-realAxisSource σ v)/(((σ-1)^2+v^2 : ℝ) : ℂ) -
        ((σ-1 : ℝ) : ℂ)^2*realCubicSource σ u v /
          ((((σ-1)^2+u^2 : ℝ) : ℂ)*(((σ-1)^2+v^2 : ℝ) : ℂ)) -
        2*(u : ℂ)*(v : ℂ)*realCubicSource σ u v /
          ((((σ-1)^2+u^2 : ℝ) : ℂ)*(((σ-1)^2+v^2 : ℝ) : ℂ))+1 := by
    push_cast
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_sub, add_comm] using heq
  rw [← heq']
  exact h

def axisCoordinateTube : Set (Fin 2 → ℂ) := {w | (w 0,w 1) ∈ axisTube}

theorem isOpen_axisCoordinateTube : IsOpen axisCoordinateTube :=
  isOpen_axisTube.preimage ((continuous_apply 0).prodMk (continuous_apply 1))

private theorem differentiableOn_axisCoordinatePrimeFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (fun w : Fin 2 → ℂ => axisPrimeFactor p (w 0) (w 1))
      axisCoordinateTube := by
  have he : Differentiable ℂ (fun w : Fin 2 → ℂ => (w 0,w 1)) :=
    (differentiable_apply 0).prodMk (differentiable_apply 1)
  exact (differentiableOn_axisPrimeFactor p).comp
    (f := fun w : Fin 2 → ℂ => (w 0,w 1))
    (s := axisCoordinateTube) he.differentiableOn (fun _ hw => hw)

private theorem differentiableOn_axisCoordinatePrimeProduct (P : Finset Nat.Primes) :
    DifferentiableOn ℂ (fun w : Fin 2 → ℂ => ∏ p ∈ P, axisPrimeFactor p (w 0) (w 1))
      axisCoordinateTube := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableOn_const (1 : ℂ)
  | @insert p S hp hS =>
    have h := differentiableOn_axisCoordinatePrimeFactor p
    convert h.mul hS using 1 <;> try rfl
    funext w
    exact Finset.prod_insert hp

theorem analyticOnNhd_axisEulerCorrection :
    AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => axisEulerCorrection (w 0) (w 1))
      axisCoordinateTube := by
  obtain ⟨P, hP⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset Nat.Primes))
  have hc := hasProdLocallyUniformlyOn_axisPrimeFactor.comp
    (fun w : Fin 2 → ℂ => (w 0,w 1)) (fun _ hw => hw)
    ((continuous_apply 0).prodMk (continuous_apply 1)).continuousOn
  have hconv : TendstoLocallyUniformlyOn
      (fun n => fun w : Fin 2 → ℂ => ∏ p ∈ P n, axisPrimeFactor p (w 0) (w 1))
      (fun w => axisEulerCorrection (w 0) (w 1)) Filter.atTop axisCoordinateTube := by
    intro w hw r hr
    obtain ⟨t, ht, htr⟩ := hc w hw r hr
    exact ⟨t, ht, hP.eventually htr⟩
  exact GaloisForLFunctions.HTGeometry.analyticOnNhd_of_tendstoLocallyUniformlyOn
    isOpen_axisCoordinateTube (fun n => differentiableOn_axisCoordinatePrimeProduct (P n)) hconv

theorem analyticOnNhd_regularAxisSource :
    AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => regularAxisSource (w 0) (w 1))
      axisCoordinateTube := by
  have hj : Differentiable ℂ (fun w : Fin 2 → ℂ => residuePair (w 0) (w 1)) :=
    differentiable_residuePair_comp (differentiable_apply 0) (differentiable_apply 1)
  have hdiff := hj.differentiableOn.mul analyticOnNhd_axisEulerCorrection.differentiableOn
  exact fun w hw => GaloisForLFunctions.HTGeometry.analyticAt_of_differentiableOn
    isOpen_axisCoordinateTube hdiff hw

private def realFrequencyEmbedding (w : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![(w 0 : ℂ),(w 1 : ℂ)*Complex.I,(w 2 : ℂ)*Complex.I]

private theorem contDiff_realFrequencyEmbedding : ContDiff ℝ ∞ realFrequencyEmbedding := by
  apply contDiff_pi.2
  intro i
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 2)).mul contDiff_const

/-- The actual pole-removed cubic source has every joint real derivative at all critical
frequencies, including their intersection. There is no zeta zero-freeness premise. -/
theorem contDiffAt_realCubicSource {w : Fin 3 → ℝ} (hσ : 1 ≤ w 0) :
    ContDiffAt ℝ ∞ (fun z : Fin 3 → ℝ => realCubicSource (z 0) (z 1) (z 2)) w := by
  have hm : realFrequencyEmbedding w ∈ cubicRegularDomain :=
    closed_frequency_mem_cubicRegularDomain hσ (by simp) (by simp)
  have hs := analyticOnNhd_regularCubicSource (realFrequencyEmbedding w) hm
  have hreal : ContDiffAt ℝ ∞
      (fun z : Fin 3 → ℂ => regularCubicSource (z 0) (z 1) (z 2)) (realFrequencyEmbedding w) :=
    hs.contDiffAt.restrict_scalars ℝ
  exact hreal.comp w contDiff_realFrequencyEmbedding.contDiffAt

private def realAxisEmbedding (w : Fin 2 → ℝ) : Fin 2 → ℂ :=
  ![(w 0 : ℂ),(w 1 : ℂ)*Complex.I]

private theorem contDiff_realAxisEmbedding : ContDiff ℝ ∞ realAxisEmbedding := by
  apply contDiff_pi.2
  intro i
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const

theorem contDiffAt_realAxisSource {w : Fin 2 → ℝ} (hσ : 1 ≤ w 0) :
    ContDiffAt ℝ ∞ (fun z : Fin 2 → ℝ => realAxisSource (z 0) (z 1)) w := by
  have hm : realAxisEmbedding w ∈ axisCoordinateTube := by
    change 7/8 < (w 0 : ℂ).re ∧ |((w 1 : ℂ)*Complex.I).re| < 1/16
    exact ⟨by simpa using (show 7/8 < w 0 by linarith), by simp⟩
  have hs := analyticOnNhd_regularAxisSource (realAxisEmbedding w) hm
  have hreal : ContDiffAt ℝ ∞
      (fun z : Fin 2 → ℂ => regularAxisSource (z 0) (z 1)) (realAxisEmbedding w) :=
    hs.contDiffAt.restrict_scalars ℝ
  exact hreal.comp w contDiff_realAxisEmbedding.contDiffAt

theorem realCubicSource_axis_left {σ : ℝ} (hσ : 1 ≤ σ) (v : ℝ) :
    realCubicSource σ 0 v-realAxisSource σ 0 = 0 := by
  simp only [realCubicSource, realAxisSource, Complex.ofReal_zero, zero_mul]
  rw [regularCubicSource_zero_left hσ (by simp), regularAxisSource_zero, sub_self]

theorem realCubicSource_axis_right {σ : ℝ} (hσ : 1 ≤ σ) (u : ℝ) :
    realCubicSource σ u 0-realAxisSource σ 0 = 0 := by
  simp only [realCubicSource, realAxisSource, Complex.ofReal_zero, zero_mul]
  rw [regularCubicSource_zero_right hσ (by simp), regularAxisSource_zero, sub_self]

theorem realCubicSource_intersection : realCubicSource 1 0 0 = 1 := by
  simpa only [realCubicSource, Complex.ofReal_one, Complex.ofReal_zero, zero_mul] using
    regularCubicSource_one_zero

end RHTower.BAGTrace
