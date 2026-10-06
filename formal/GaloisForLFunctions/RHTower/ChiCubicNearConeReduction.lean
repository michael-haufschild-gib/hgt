import GaloisForLFunctions.RHTower.ChiCubicExteriorSource

/-!
# Original sharp cubic reduced to its entire shrinking cone tube

The complementary arithmetic exterior decays on the full original natural
scale. Exact source linearity and the already proved same-cutoff smoothing
error leave only the complete near-cone action at the original normalization.
Every atom, lift, alias and both contraction projectors remain in that action.
Its arithmetic cancellation is not assumed or proved here.
-/

noncomputable section
open Set Filter
open scoped Topology FourierTransform
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace

/-- The entire retained smooth cone tube, on both signed sheets. -/
def bagCubicNearConePhysical (ε : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f-bagCubicExteriorPhysical ε f

theorem bagCubicNearConePhysical_fourier (ε : ℝ) (f : SchwartzMap E ℂ) (x : E) :
    (𝓕 (bagCubicNearConePhysical ε f)) x =
      bagCubicConeCutoff (bagCubicSignedDefect x/ε) • (𝓕 f) x := by
  simp only [bagCubicNearConePhysical,sub_eq_add_neg,FourierTransform.fourier_add,
    FourierTransform.fourier_neg,bagCubicExteriorPhysical,
    FourierTransform.fourier_fourierInv_eq,add_apply,neg_apply,
    bagCubicExteriorFourier_apply]
  simp only [add_smul,neg_smul,one_smul]
  abel

private theorem source_sub (P : Finset ℕ) (D : ℕ+)
    (f g : SchwartzMap E ℂ) :
    bagCriticalDefectAction P D (f-g)=
      bagCriticalDefectAction P D f-bagCriticalDefectAction P D g := by
  have hper : ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz (f-g)) =
      ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz f)-
        ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz g) := by
    funext x
    simp only [map_sub,ramanujanTriplePeriodicTest,sub_apply,sub_mul,Pi.sub_apply]
    exact (summable_ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz f) x).tsum_sub
      (summable_ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz g) x)
  simp only [bagCriticalDefectAction_eq,bagLiftedFourierTest_eq_periodic]
  rw [hper,map_sub,map_sub]

private def actual (N : BAGCubicExteriorScale) : SchwartzMap E ℂ :=
  bagCubicExpControlledPhysicalSchwartz ⟨N.1,N.2.1⟩
    ⟨N.1^((1 : ℝ)/4),Real.rpow_pos_of_pos
      (lt_of_lt_of_le (Real.exp_pos 1) N.2.1) _,N.2.2⟩

/-- The complete original critical source applied to the entire shrinking
cone tube. All rational atoms, lifts, aliases and both projectors remain. -/
def bagCubicNearConeAction (N : ℕ) : ℂ :=
  if h : Real.exp 1 ≤ (N : ℝ) ∧ (N : ℝ)^((1 : ℝ)/4)<(N : ℝ)/2 then
    bagCriticalDefectAction (Finset.range (⌊2*(N : ℝ)⌋₊+1)) (bagPhysicalProjectorLevel N)
      (bagCubicNearConePhysical ((N : ℝ)^(-(1 : ℝ)/8)) (actual ⟨N,h⟩))
  else 0

/-- Complete complementary arithmetic action, on the original natural scale. -/
def bagCubicCompleteExteriorAction (N : ℕ) : ℂ :=
  if h : Real.exp 1 ≤ (N : ℝ) ∧ (N : ℝ)^((1 : ℝ)/4)<(N : ℝ)/2 then
    bagCriticalDefectAction (Finset.range (⌊2*(N : ℝ)⌋₊+1)) (bagPhysicalProjectorLevel N)
      (bagCubicShrinkingExterior ⟨N,h⟩)
  else 0

theorem bagCubicCompleteExteriorAction_rapid_decay (a : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      ‖bagCubicCompleteExteriorAction N‖ ≤ C/(N : ℝ)^a := by
  obtain ⟨C,hC,hb⟩ := bagCubicShrinkingExterior_source_rapid_decay a
  refine ⟨C,hC,?_⟩
  filter_upwards [bagCubicExteriorScale_eventually] with N hN
  rw [bagCubicCompleteExteriorAction,dif_pos hN]
  exact hb ⟨N,hN⟩ _ _

private theorem log_weight_tendsto :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (s:=1) 2 (by norm_num)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simpa only [Function.comp_def,Real.rpow_two,Real.rpow_one] using h

/-- Vanishing of the entire exterior at the ORIGINAL cubic normalization. -/
theorem bagCubicCompleteExteriorAction_negligible :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
      ‖bagCubicCompleteExteriorAction N‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := bagCubicCompleteExteriorAction_rapid_decay 0
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity))
    (hb.mono (fun N hN => ?_))
    (by simpa using log_weight_tendsto.mul_const C)
  simpa using mul_le_mul_of_nonneg_left hN
    (show 0 ≤ (Real.log (N : ℝ))^2/(N : ℝ) by positivity)

/-- Exact split of the literal smoothed cubic on every sufficiently large
original natural scale, without an omitted source or geometric sector. -/
theorem primeGaussianCubicSmoothedOffDiagonal_nearCone_split :
    ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N
        (bagCubicControlledBandCutoff N ((N : ℝ)^((1 : ℝ)/4))) =
          bagCubicNearConeAction N+bagCubicCompleteExteriorAction N := by
  filter_upwards [bagCubicExteriorScale_eventually] with N hN
  have hN0 : (0 : ℝ)<N := lt_of_lt_of_le (Real.exp_pos 1) hN.1
  have hN1 : 1<(N : ℝ) := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) hN.1
  have hc := bagCubicControlledBandCutoff_properties ⟨N,hN0⟩
    ⟨(N : ℝ)^((1 : ℝ)/4),Real.rpow_pos_of_pos hN0 _,hN.2⟩
  rw [primeGaussianCubicSmoothedOffDiagonal_eq_defectAction hN1.le hc.2.2.2.1
    (actual ⟨N,hN⟩) (fun _ => rfl)]
  rw [bagCubicNearConeAction,dif_pos hN,bagCubicCompleteExteriorAction,dif_pos hN,
    bagCubicNearConePhysical,source_sub]
  change _ = (_-bagCriticalDefectAction _ _ (bagCubicShrinkingExterior ⟨N,hN⟩))+_
  abel

/-- The ORIGINAL sharp signed cubic differs negligibly from the ENTIRE
retained shrinking-cone action. Near-cone cancellation remains the next
arithmetic problem; no exact-positive-cone substitution is made. -/
theorem primeGaussianCubic_nearCone_reduction :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
      ‖primeGaussianCubicOffDiagonal (N : ℝ)-bagCubicNearConeAction N‖) atTop (𝓝 0) := by
  have ht := primeGaussianCubic_controlled_cutoff_negligible_error.add
    bagCubicCompleteExteriorAction_negligible
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ ht
  filter_upwards [primeGaussianCubicSmoothedOffDiagonal_nearCone_split] with N hsplit
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := norm_add_le (primeGaussianCubicOffDiagonal (N : ℝ)-
    primeGaussianCubicSmoothedOffDiagonal N
      (bagCubicControlledBandCutoff N ((N : ℝ)^((1 : ℝ)/4))))
    (bagCubicCompleteExteriorAction N)
  rw [hsplit] at hb ⊢
  convert hb using 1
  congr 1
  abel

end RHTower.BAGTrace
