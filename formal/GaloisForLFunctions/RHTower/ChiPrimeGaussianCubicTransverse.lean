import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicLiftedAction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete physical transverse critical action

The exact three-coordinate Fourier coefficient exposes the defect
zeta + xi * upsilon. The reciprocal physical r-factor cancels the positive
transition Jacobian. All r-dependence and the full window Mellin line remain;
outer r-integrability and inner Mellin-integrability are proved explicitly.
The complete lifted critical atom action retains both contraction projectors
and the negligible comparison with the original sharp cubic. No stationary
approximation, sum/Mellin interchange or signed asymptotic saving is asserted.
-/

noncomputable section
open MeasureTheory
namespace RHTower.BAGTrace.Transverse
private abbrev E := EuclideanSpace ℝ (Fin 3)
private def coords : E ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.finTwoArrow.trans (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ))))

private lemma coords_apply (p q r : ℝ) : coords (WithLp.toLp 2 ![p,q,r])=(r,q,p) := rfl

private lemma coords_symm (z : ℝ × ℝ × ℝ) :
    coords.symm z=WithLp.toLp 2 ![z.2.2,z.2.1,z.1] := by
  apply coords.injective
  rw [coords.apply_symm_apply,coords_apply]

private lemma coords_preserving : MeasurePreserving coords := by
  exact (((MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap.comp (volume_preserving_finTwoArrow ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)).comp
        (PiLp.volume_preserving_ofLp (Fin 3))

/-- Exact volume-normalized coordinate decomposition in r,q,p order. -/
theorem integral_three (f : E → ℂ) (hf : Integrable f) :
    Integrable (fun r : ℝ => ∫ q : ℝ, ∫ p : ℝ, f (WithLp.toLp 2 ![p,q,r])) ∧
    (∫ v, f v) = ∫ r : ℝ, ∫ q : ℝ, ∫ p : ℝ, f (WithLp.toLp 2 ![p,q,r]) := by
  have hp : MeasurePreserving coords.symm := coords_preserving.symm coords
  have hi : Integrable (fun z : ℝ × ℝ × ℝ => f (coords.symm z)) :=
    (hp.integrable_comp_emb coords.symm.measurableEmbedding).mpr hf
  have he : (fun r : ℝ => ∫ z : ℝ × ℝ, f (coords.symm (r,z))) =ᵐ[volume]
      (fun r : ℝ => ∫ q : ℝ, ∫ p : ℝ, f (WithLp.toLp 2 ![p,q,r])) := by
    filter_upwards [hi.prod_right_ae] with r hr
    change (∫ z : ℝ × ℝ, f (coords.symm (r,z)) ∂volume.prod volume) = _
    rw [integral_prod _ hr]
    apply integral_congr_ae
    filter_upwards [] with q
    apply integral_congr_ae
    filter_upwards [] with p
    rw [coords_symm]
  refine ⟨hi.integral_prod_left.congr he,?_⟩
  rw [← hp.integral_comp' f]
  change (∫ z : ℝ × ℝ × ℝ, f (coords.symm z) ∂volume.prod volume) = _
  rw [integral_prod _ hi]
  exact integral_congr_ae he

end RHTower.BAGTrace.Transverse

namespace RHTower.BAGTrace
open GaloisForLFunctions.RHTower
open scoped FourierTransform ContDiff Topology
open Set Filter

/-- The full two-frequency transition of the actual Mellin slice. -/
def bagCubicTransverseTransition (N : ℝ) (η : ℝ → ℝ) (τ r ξ υ : ℝ) : ℂ :=
  ∫ α : ℝ, ∫ β : ℝ,
    bourgainOscillation (2*Real.pi*(r*υ*α+r*ξ*β-r*α*β))*
      ((𝓕 (bagCubicMellinSliceValue N η τ)) α*(𝓕 (bagCubicMellinSliceValue N η τ)) β)

/-- The entire Mellin line of the physical window remains in the profile. -/
def bagCubicTransverseProfile (N : ℝ) (η : ℝ → ℝ) (r ξ υ : ℝ) : ℂ :=
  ∫ τ : ℝ, bagWindowMellinCarrier (r*N) τ*bagCubicTransverseTransition N η τ r ξ υ

private def thirdFactor (N : ℝ) (η : ℝ → ℝ) (r ζ : ℝ) : ℂ :=
  (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*
    bourgainOscillation (2*Real.pi*(-r*ζ))

private def transverseRow (N : ℝ) (η : ℝ → ℝ) (w : BAGPhysicalSpace) (r : ℝ) : ℂ :=
  (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)*
    bourgainOscillation (2*Real.pi*(-r*(w 2+w 0*w 1)))*
      bagCubicTransverseProfile N η r (w 0) (w 1)

private lemma kernel_factor (N : ℝ) (η : ℝ → ℝ) (w : BAGPhysicalSpace) (p q r : ℝ) :
    Complex.exp ((-2*Real.pi*inner ℝ (WithLp.toLp 2 ![p,q,r] : BAGPhysicalSpace) w : ℝ)*Complex.I)*
      bagCubicPhysicalAmplitude N η (WithLp.toLp 2 ![p,q,r]) =
    thirdFactor N η r (w 2)*
      (bourgainOscillation (2*Real.pi*(p*q/r+(-w 0)*p+(-w 1)*q))*
        (bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q)*
          (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)) := by
  have he : Complex.exp ((-2*Real.pi*(p*w 0+q*w 1+r*w 2) : ℝ)*Complex.I)*
      bourgainOscillation (2*Real.pi*(p*q/r)) =
      bourgainOscillation (2*Real.pi*(-r*w 2))*
        bourgainOscillation (2*Real.pi*(p*q/r+(-w 0)*p+(-w 1)*q)) := by
    simp only [bourgainOscillation,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [bagCubicPhysicalAmplitude,thirdFactor,PiLp.inner_apply,Real.inner_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  linear_combination (norm := ring_nf)
    (2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q*
      (starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*
        (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)*he
private lemma physical_fourier_rows {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (w : BAGPhysicalSpace) :
    Integrable (fun r : ℝ => thirdFactor N η r (w 2)*bagCubicWindowKernel N η r (-w 0) (-w 1)) ∧
    (𝓕 (bagCubicPhysicalSchwartz hN hη hz)) w =
      ∫ r : ℝ, thirdFactor N η r (w 2)*bagCubicWindowKernel N η r (-w 0) (-w 1) := by
  let K : BAGPhysicalSpace → ℂ := fun v =>
    Complex.exp ((-2*Real.pi*inner ℝ v w : ℝ)*Complex.I)*bagCubicPhysicalAmplitude N η v
  have hcont : Continuous K := by
    exact ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const).cexp.mul
        (contDiff_bagCubicPhysicalAmplitude hN hη hz).continuous
  have hcompact : HasCompactSupport K := (hasCompactSupport_bagCubicPhysicalAmplitude N hz).mul_left
  have hi := Transverse.integral_three K (hcont.integrable_of_hasCompactSupport hcompact)
  have he (r : ℝ) : (∫ q : ℝ, ∫ p : ℝ, K (WithLp.toLp 2 ![p,q,r])) =
      thirdFactor N η r (w 2)*bagCubicWindowKernel N η r (-w 0) (-w 1) := by
    simp only [K,kernel_factor,bagCubicWindowKernel,integral_const_mul]
  constructor
  · exact hi.1.congr (Eventually.of_forall he)
  · rw [SchwartzMap.fourier_coe,Real.fourier_eq']
    change (∫ v, K v) = _
    simpa only [he] using hi.2

private lemma transition_eq {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (τ r ξ υ : ℝ) :
    bagHyperbolicTransition r (bagCubicMellinSlice hN hη hc hz τ)
      (bagCubicMellinSlice hN hη hc hz τ) (r*υ) (r*ξ) =
      bagCubicTransverseTransition N η τ r ξ υ := rfl

/-- The Mellin profile is absolutely integrable at every positive physical r. -/
theorem integrable_bagCubicTransverseProfile {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    {r : ℝ} (hr : 0 < r) (ξ υ : ℝ) :
    Integrable (fun τ : ℝ => bagWindowMellinCarrier (r*N) τ*
      bagCubicTransverseTransition N η τ r ξ υ) := by
  have h := (bagCubicWindowKernel_eq_full_transition hN hη hc hz hr (-ξ) (-υ)).1
  have he (τ : ℝ) : bagWindowMellinCarrier (r*N) τ*
      ((r : ℂ)*bourgainOscillation (2*Real.pi*(-r*(-ξ)*(-υ)))*
        bagHyperbolicTransition r (bagCubicMellinSlice hN hη hc hz τ)
          (bagCubicMellinSlice hN hη hc hz τ) (-r*(-υ)) (-r*(-ξ))) =
      ((r : ℂ)*bourgainOscillation (2*Real.pi*(-r*ξ*υ)))*
        (bagWindowMellinCarrier (r*N) τ*bagCubicTransverseTransition N η τ r ξ υ) := by
    rw [show -r*(-υ)=r*υ by ring,show -r*(-ξ)=r*ξ by ring,
      show r*ξ*(-υ) = -r*ξ*υ by ring,transition_eq]
    ring
  have hh := h.congr (Eventually.of_forall he)
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _))) _).mp hh

private lemma window_transition {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    {r : ℝ} (hr : 0 < r) (ξ υ : ℝ) :
    bagCubicWindowKernel N η r (-ξ) (-υ) =
      (r : ℂ)*bourgainOscillation (2*Real.pi*(-r*ξ*υ))*
        bagCubicTransverseProfile N η r ξ υ := by
  rw [(bagCubicWindowKernel_eq_full_transition hN hη hc hz hr (-ξ) (-υ)).2]
  unfold bagCubicTransverseProfile
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [show -r*(-υ)=r*υ by ring,show -r*(-ξ)=r*ξ by ring,
    show r*ξ*(-υ) = -r*ξ*υ by ring,transition_eq]
  ring

private lemma row_transition {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (w : BAGPhysicalSpace) (r : ℝ) :
    thirdFactor N η r (w 2)*bagCubicWindowKernel N η r (-w 0) (-w 1) =
      transverseRow N η w r := by
  by_cases hr : 0 < r
  · rw [window_transition hN hη hc hz hr]
    have he : bourgainOscillation (2*Real.pi*(-r*w 2))*
        bourgainOscillation (2*Real.pi*(-r*w 0*w 1)) =
        bourgainOscillation (2*Real.pi*(-r*(w 2+w 0*w 1))) := by
      simp only [bourgainOscillation,← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold thirdFactor transverseRow
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    calc
      _ = ((2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)/(r : ℂ)*(r : ℂ))*
          (bourgainOscillation (2*Real.pi*(-r*w 2))*bourgainOscillation (2*Real.pi*(-r*w 0*w 1)))*
            bagCubicTransverseProfile N η r (w 0) (w 1) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hr0,he]
  · have hz0 : η r=0 := hz r (fun h => hr ((by linarith : 0 < N).trans h.1))
    simp [thirdFactor,transverseRow,bagCubicMellinSliceValue,hz0]

/-- Complete physical Fourier coefficient with exact transverse phase and
full nested r/Mellin integrals; no lattice/Mellin interchange is asserted. -/
theorem bagCubicPhysicalFourier_eq_transverse {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (w : BAGPhysicalSpace) :
    let R := fun r : ℝ => (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)*
      bourgainOscillation (2*Real.pi*(-r*(w 2+w 0*w 1)))*bagCubicTransverseProfile N η r (w 0) (w 1)
    Integrable R ∧ (𝓕 (bagCubicPhysicalSchwartz hN hη hz)) w = ∫ r : ℝ, R r := by
  have hi := physical_fourier_rows hN hη hz w
  simpa only [row_transition hN hη hc hz,transverseRow] using hi

/-- Complete Fourier value with the transverse defect exposed. -/
def bagCubicTransverseFourier (N : ℝ) (η : ℝ → ℝ) (w : BAGPhysicalSpace) : ℂ :=
  ∫ r : ℝ, (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)*
    bourgainOscillation (2*Real.pi*(-r*(w 2+w 0*w 1)))*bagCubicTransverseProfile N η r (w 0) (w 1)

/-- Every integer lift of the exact transverse coefficient. -/
def bagCubicTransverseLiftedTest (N : ℝ) (η : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  ∑' k : ℤ × ℤ × ℤ, bagCubicTransverseFourier N η
    (bagIntegerTriple k-WithLp.toLp 2 ![x.1,x.2.1,x.2.2])

/-- The literal lifted test is the complete transverse action, with no
interchange of the integer sum and either integral. -/
theorem bagLiftedFourierTest_eq_transverse {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) :
    bagLiftedFourierTest (bagCubicPhysicalSchwartz hN hη hz) = bagCubicTransverseLiftedTest N η := by
  funext x
  change (∑' k : ℤ × ℤ × ℤ, (𝓕 (bagCubicPhysicalSchwartz hN hη hz))
    (bagIntegerTriple k-WithLp.toLp 2 ![x.1,x.2.1,x.2.2])) = _
  apply tsum_congr
  intro k
  exact (bagCubicPhysicalFourier_eq_transverse hN hη hc hz _).2

/-- Unconditional full signed transverse critical action, with all lifts,
both contractions, actual cutoffs and the original negligible edge error. -/
theorem exists_bagCompleteTransverseCriticalAction :
    ∃ η : ℕ → ℝ → ℝ,
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ w : BAGPhysicalSpace, Integrable (fun r : ℝ =>
          (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N (η N) 0 r)*
            bourgainOscillation (2*Real.pi*(-r*(w 2+w 0*w 1)))*
              bagCubicTransverseProfile N (η N) r (w 0) (w 1))) ∧
        (∀ r : ℝ, 0 < r → ∀ ξ υ : ℝ,
          Integrable (fun τ : ℝ => bagWindowMellinCarrier (r*N) τ*
            bagCubicTransverseTransition N (η N) τ r ξ υ)) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖bagCubicTransverseFourier N (η N) (bagIntegerTriple k-a)‖)) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N) =
          ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1)
              (bagCubicTransverseLiftedTest N (η N)))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1)
              (bagCubicTransverseLiftedTest N (η N)))‖) atTop (𝓝 0) := by
  obtain ⟨η,hη,herr⟩ := exists_primeGaussianCubic_smooth_band_negligible_error
  have he : ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N (η N) =
        ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
          (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1)
            (bagCubicTransverseLiftedTest N (η N))) := by
    filter_upwards [hη,eventually_ge_atTop (2 : ℕ)] with N hreg hN
    have hn : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    rw [← bagLiftedFourierTest_eq_transverse hn hreg.1 hreg.2.1 hreg.2.2.2.1]
    exact primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction hn.le hreg.2.2.2.1 _ (fun _ => rfl)
  refine ⟨η,?_,?_⟩
  · filter_upwards [hη,he,eventually_ge_atTop (2 : ℕ)] with N hreg heq hN
    obtain ⟨hsm,hco,hbo,hze,hpl⟩ := hreg
    have hn : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    refine ⟨hsm,hco,hbo,hze,hpl,?_,?_,?_,heq⟩
    · exact fun w => (bagCubicPhysicalFourier_eq_transverse hn hsm hco hze w).1
    · exact fun r hr ξ υ => integrable_bagCubicTransverseProfile hn hsm hco hze hr ξ υ
    · intro a
      have hv (w : BAGPhysicalSpace) : (𝓕 (bagCubicPhysicalSchwartz hn hsm hze)) w =
          bagCubicTransverseFourier N (η N) w :=
        (bagCubicPhysicalFourier_eq_transverse hn hsm hco hze w).2
      simpa only [hv,sub_eq_add_neg] using
        summable_norm_bagCubicPhysicalFourier hn hsm hze (-a)
  · apply herr.congr'
    filter_upwards [he] with N heq
    rw [heq]

end RHTower.BAGTrace
