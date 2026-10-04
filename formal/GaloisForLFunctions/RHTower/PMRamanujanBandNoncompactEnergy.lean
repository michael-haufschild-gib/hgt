import GaloisForLFunctions.RHTower.PMRamanujanBandPhysicalSeparation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Noncompact energy of the actual normalized complete bands

For every positive damping, one positive radius separates a cofinal actual
normalized band from every member of any totally bounded profile set. This
holds in both the critical-frequency and the original logarithmic carriers.

The proof uses uniform phase decay on totally bounded sets, the actual
bounded-source continuation and an unconditional positive critical zero.
It retains the complete signed source. It proves neither a growing-cutoff
energy upper bound nor small-damping admission or RH.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform
noncomputable section
namespace RHTower

theorem tendsto_pm_inner_phaseUnitary_zero (h F : SoninL2) :
    Tendsto (fun a : ℝ => inner ℂ h (MellinL2.fourierPhaseMulUnitary a F))
      atTop (𝓝 0) := by
  have hRL := (Real.tendsto_integral_exp_smul_cocompact
    (fun τ : ℝ => (starRingEnd ℂ) (h τ)*F τ)).mono_left
      (show (atBot : Filter ℝ) ≤ cocompact ℝ by
        rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
  have hn := hRL.comp tendsto_neg_atTop_atBot
  refine hn.congr fun a => ?_
  rw [pm_inner_phaseUnitary_eq_integral]
  apply integral_congr_ae
  exact .of_forall fun τ => by
    simp only [MellinL2.fourierPhase,Circle.smul_def,smul_eq_mul]
    rw [show -(τ * -a) = a*τ by ring]

theorem pm_inner_phaseUnitary_uniform_zero (h : SoninL2) {K : Set SoninL2}
    (hK : TotallyBounded K) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, ∀ F ∈ K, ‖inner ℂ h (MellinL2.fourierPhaseMulUnitary a F)‖ < η := by
  obtain ⟨S,hS,hcover⟩ := Metric.totallyBounded_iff.mp hK
    (η/(2*(‖h‖+1))) (by positivity)
  have he : ∀ᶠ a : ℝ in atTop, ∀ G ∈ S,
      ‖inner ℂ h (MellinL2.fourierPhaseMulUnitary a G)‖ < η/2 := by
    apply hS.eventually_all.mpr
    intro G hG
    exact ((tendsto_pm_inner_phaseUnitary_zero h G).norm).eventually
      (by simpa using (gt_mem_nhds (half_pos hη)))
  filter_upwards [he] with a ha
  intro F hF
  obtain ⟨G,hG,hFG⟩ := Set.mem_iUnion₂.mp (hcover hF)
  have hd : ‖F-G‖ < η/(2*(‖h‖+1)) := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hFG
  have hl : ‖inner ℂ h (MellinL2.fourierPhaseMulUnitary a F) -
      inner ℂ h (MellinL2.fourierPhaseMulUnitary a G)‖ ≤ ‖h‖*‖F-G‖ := by
    rw [← inner_sub_right,← map_sub]
    exact (norm_inner_le_norm h _).trans_eq (by rw [(MellinL2.fourierPhaseMulUnitary a).norm_map])
  have hsmall : ‖h‖*‖F-G‖ < η/2 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2*(‖h‖+1))).mp hd
    nlinarith [norm_nonneg (F-G)]
  have ht := norm_add_le
    (inner ℂ h (MellinL2.fourierPhaseMulUnitary a F)-inner ℂ h (MellinL2.fourierPhaseMulUnitary a G))
    (inner ℂ h (MellinL2.fourierPhaseMulUnitary a G))
  rw [sub_add_cancel] at ht
  exact lt_of_le_of_lt ht (by linarith [ha G hG])

theorem exists_bound_pmRamanujanMovingBandMellinVector_of_totallyBounded
    (ε : ℝ) {K : Set SoninL2} (hK : TotallyBounded K)
    (hm : ∀ X ∈ Ici (1 : ℝ), pmRamanujanNormalizedBandMellinVector ε X ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ Ici (1 : ℝ),
      ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C := by
  obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro X hX
  rw [pmRamanujanMovingBandMellinVector,(MellinL2.fourierPhaseMulUnitary _).norm_map]
  exact (hC _ (hm X hX)).trans (le_max_left _ _)

theorem tendsto_pmRamanujanBandTestedScale_exp_zero_of_totallyBounded
    (ε : ℝ) {K : Set SoninL2} (hK : TotallyBounded K)
    (hm : ∀ X ∈ Ici (1 : ℝ), pmRamanujanNormalizedBandMellinVector ε X ∈ K)
    (h : SoninL2) :
    Tendsto (fun u : ℝ => pmRamanujanBandTestedScale ε h (Real.exp u)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have ha : Tendsto (fun u : ℝ => u/(2*Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have he := ha.eventually (pm_inner_phaseUnitary_uniform_zero h hK hη)
  obtain ⟨B,hB⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop (0 : ℝ)))
  refine ⟨B,?_⟩
  intro u hu
  obtain ⟨hb,hu0⟩ := hB u hu
  have hx := hm (Real.exp u) (Real.one_le_exp hu0)
  have hh := hb _ hx
  simpa only [pmRamanujanBandTestedScale,pmRamanujanMovingBandMellinVector,
    Real.log_exp,Real.dist_eq,sub_zero,abs_norm] using hh

theorem pmRamanujanBandTestedScale_abel_zero_of_totallyBounded
    (ε : ℝ) {K : Set SoninL2} (hK : TotallyBounded K)
    (hm : ∀ X ∈ Ici (1 : ℝ), pmRamanujanNormalizedBandMellinVector ε X ∈ K)
    (h : SoninL2) {ρ : ℂ} (hρ : ρ.re = 1/2) :
    Tendsto (fun δ : ℝ => (δ : ℂ) *
      ∫ X in Ici (1 : ℝ), (X : ℂ)^(-(ρ+(δ : ℂ))-(1/2 : ℂ)) *
        pmRamanujanBandTestedScale ε h X) (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-((ρ.im : ℂ)*I)*(u : ℂ))*
    pmRamanujanBandTestedScale ε h (Real.exp u)
  have hp (u : ℝ) : ‖Complex.exp (-((ρ.im : ℂ)*I)*(u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hmeas : Measurable f :=
    (by fun_prop : Measurable (fun u : ℝ => Complex.exp (-((ρ.im : ℂ)*I)*(u : ℂ)))).mul
      ((measurable_pmRamanujanBandTestedScale ε h).comp Real.measurable_exp)
  obtain ⟨C,_hC,hbound⟩ := exists_bound_pmRamanujanMovingBandMellinVector_of_totallyBounded ε hK hm
  have hboundf : ∀ u ∈ Ioi (0 : ℝ), ‖f u‖ ≤ ‖h‖*C := by
    intro u hu
    dsimp only [f]
    rw [norm_mul,hp,one_mul]
    exact (norm_inner_le_norm h _).trans (mul_le_mul_of_nonneg_left
      (hbound (Real.exp u) (Real.one_le_exp hu.le)) (norm_nonneg _))
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [f,norm_mul,hp,one_mul,norm_zero] using
      (tendsto_pmRamanujanBandTestedScale_exp_zero_of_totallyBounded ε hK hm h).norm
  have hl := pm_bounded_null_abel_zero hmeas hboundf hf
  apply hl.congr
  intro δ
  rw [pmRamanujanBandTestedScale_eq_laplace ε h hρ δ]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only [f]
  rw [← mul_assoc,Complex.ofReal_exp,← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem pmbc_zeta_slope {ρ : ℂ} (hρ : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))/(δ : ℂ))
      (𝓝[>] 0) (𝓝 (deriv riemannZeta ρ)) := by
  have hd : HasDerivAt (fun w : ℂ => riemannZeta (ρ+w)) (deriv riemannZeta ρ) 0 := by
    have hz : HasDerivAt riemannZeta (deriv riemannZeta ρ) (ρ+0) := by
      simpa only [add_zero] using (differentiableAt_riemannZeta hρ).hasDerivAt
    have hi : HasDerivAt (fun w : ℂ => ρ+w) 1 0 :=
      (hasDerivAt_id (0 : ℂ)).const_add ρ
    simpa only [mul_one] using! hz.comp (0 : ℂ) hi
  have hdr : HasDerivAt (fun t : ℝ => riemannZeta (ρ+(t : ℂ))) (deriv riemannZeta ρ) 0 :=
    hd.comp_ofReal
  simpa only [zero_add,Complex.ofReal_zero,add_zero,hzero,sub_zero,
    Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm] using
      hdr.tendsto_slope_zero_right

private theorem pmbc_not_totallyBounded_of_critical_zero {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (hρi : 0 < ρ.im) (hzero : riemannZeta ρ = 0)
    {K : Set SoninL2} (hK : TotallyBounded K)
    (hm : ∀ X ∈ Ici (1 : ℝ), pmRamanujanNormalizedBandMellinVector ε X ∈ K) : False := by
  obtain ⟨C,_hC,hbound⟩ := exists_bound_pmRamanujanMovingBandMellinVector_of_totallyBounded ε hK hm
  obtain ⟨a,b,ha,hab,h,hrep,_hgap,_hint,hpos⟩ :=
    exists_pmRamanujanBandResidue_positive_L2_test hε hρ hzero
  have hsupp : ∀ᵐ τ : ℝ, τ ∉ Icc a b → h τ = 0 := by
    filter_upwards [hrep] with τ hτ
    intro ht
    rw [hτ,pmRamanujanBandResidueTest,indicator_of_notMem ht]
  let Q : ℝ → ℂ := fun δ => ∫ X in Ici (1 : ℝ),
    (X : ℂ)^(-(ρ+(δ : ℂ))-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X
  let R : ℂ → ℂ := fun w => ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
    (Icc a b).indicator (pmRamanujanBandClearedKernel ε w) τ
  have hρ1 : ρ ≠ 1 := by intro he; have hh := hρi; simp [he] at hh
  have hl := (pmbc_zeta_slope hρ1 hzero).mul
    (pmRamanujanBandTestedScale_abel_zero_of_totallyBounded ε hK hm h hρ)
  rw [mul_zero] at hl
  have hleft : Tendsto (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*Q δ) (𝓝[>] 0) (𝓝 0) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hn : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < δ from hδ).ne'
    rw [← mul_assoc,div_mul_cancel₀ _ hn]
  have hcont : ContinuousAt R ρ :=
    (differentiableAt_pmRamanujanBandClearedKernel_test hε.le h
      (show ρ ∈ pmRamanujanBandKernelTube a from ⟨by rw [hρ]; norm_num,hρi,ha⟩)).continuousAt
  have hshift : Tendsto (fun δ : ℝ => ρ+(δ : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
  have hright : Tendsto (fun δ : ℝ => R (ρ+(δ : ℂ))) (𝓝[>] 0) (𝓝 (R ρ)) :=
    hcont.tendsto.comp hshift
  have heq : (fun δ : ℝ => riemannZeta (ρ+(δ : ℂ))*Q δ) =ᶠ[𝓝[>] 0]
      (fun δ => R (ρ+(δ : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply pmRamanujanBandTestedScale_cleared_continuation_of_bound hε hbound h (hρi.trans ha) hsupp
    · simp only [Complex.add_re,Complex.ofReal_re,hρ]
      exact lt_add_of_pos_right _ hδ
    · simpa using hρi
    · simpa using ha
  have hRzero : R ρ = 0 := tendsto_nhds_unique hright (hleft.congr' heq)
  have hpair : R ρ = ∫ τ : ℝ, (starRingEnd ℂ) (h τ)*pmRamanujanBandResidueNumerator ε ρ τ := by
    apply integral_congr_ae
    filter_upwards [hsupp] with τ hτ
    by_cases ht : τ ∈ Icc a b
    · rw [indicator_of_mem ht,pmRamanujanBandClearedKernel_at_zero ε hzero τ]
    · simp [indicator_of_notMem ht,hτ ht]
  rw [← hpair,hRzero] at hpos
  exact (lt_irrefl 0) hpos
theorem not_totallyBounded_pmRamanujanNormalizedBandMellinVector {ε : ℝ} (hε : 0 < ε) :
    ¬ TotallyBounded (pmRamanujanNormalizedBandMellinVector ε '' Ici (1 : ℝ)) := by
  intro hK
  obtain ⟨T,hT,hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨γ,hγ,hzero⟩ := hzeros T le_rfl
  refine pmbc_not_totallyBounded_of_critical_zero hε (ρ := linePt γ) ?_ ?_ hzero hK
    (fun X hX => mem_image_of_mem _ hX)
  · norm_num [linePt]
  · simpa only [linePt,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
        hT.trans_le hγ.1

theorem totallyBounded_pmRamanujanNormalizedBandMellinVector_on_Icc
    {ε : ℝ} (hε : 0 ≤ ε) (B : ℝ) :
    TotallyBounded (pmRamanujanNormalizedBandMellinVector ε '' Icc (1 : ℝ) B) := by
  let V : ℕ × ℕ → SoninL2 := fun p =>
    if hp : 1 ≤ p.1 then pmRamanujanBandMellinVector ε p.1 p.2 hp else 0
  let J := (Finset.Iic ⌊B⌋₊).product (Finset.Iic ⌊2*B⌋₊)
  let C := (max B 1)^ε
  let K : ℕ × ℕ → Set SoninL2 := fun p =>
    (fun t : ℝ => (t : ℂ) • V p) '' Icc (0 : ℝ) C
  have hK (p : ℕ × ℕ) : IsCompact (K p) :=
    isCompact_Icc.image (by fun_prop)
  have ht : TotallyBounded (⋃ p ∈ (J : Set (ℕ × ℕ)), K p) :=
    (totallyBounded_biUnion J.finite_toSet).mpr fun p _ => (hK p).totallyBounded
  apply ht.subset
  rintro _ ⟨X,hX,rfl⟩
  have hmem : (⌊X⌋₊,⌊2*X⌋₊) ∈ J :=
    Finset.mem_product.mpr ⟨Finset.mem_Iic.mpr (Nat.floor_mono hX.2),
      Finset.mem_Iic.mpr (Nat.floor_mono (by linarith [hX.2]))⟩
  apply mem_iUnion₂.mpr
  refine ⟨(⌊X⌋₊,⌊2*X⌋₊),hmem,?_⟩
  refine ⟨X^ε,⟨Real.rpow_nonneg (by linarith [hX.1]) _,?_⟩,rfl⟩
  exact Real.rpow_le_rpow (by linarith [hX.1]) (hX.2.trans (le_max_left _ _)) hε

/-- One radius excludes every totally bounded collection of profiles on every tail. -/
theorem exists_uniform_pmRamanujanBandCompact_separation {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : Set SoninL2, TotallyBounded K → ∀ B : ℝ,
      ∃ X : ℝ, B ≤ X ∧ 1 ≤ X ∧
        ∀ F ∈ K, c ≤ ‖pmRamanujanNormalizedBandMellinVector ε X-F‖ := by
  have hn := not_totallyBounded_pmRamanujanNormalizedBandMellinVector hε
  rw [Metric.totallyBounded_iff] at hn
  push Not at hn
  obtain ⟨η,hη,hn⟩ := hn
  refine ⟨η/2,half_pos hη,?_⟩
  intro K hK B
  have ht := hK.union (totallyBounded_pmRamanujanNormalizedBandMellinVector_on_Icc hε.le B)
  obtain ⟨S,hS,hcover⟩ := Metric.totallyBounded_iff.mp ht (η/2) (half_pos hη)
  obtain ⟨v,hv,hnv⟩ := Set.not_subset.mp (hn S hS)
  obtain ⟨X,hX,rfl⟩ := hv
  have hfar (G : SoninL2) (hG : G ∈ S) :
      η ≤ dist (pmRamanujanNormalizedBandMellinVector ε X) G := by
    by_contra h
    exact hnv (mem_iUnion₂.mpr ⟨G,hG,by simpa only [Metric.mem_ball] using lt_of_not_ge h⟩)
  have hB : B ≤ X := by
    by_contra hb
    have hh := hcover (Or.inr (mem_image_of_mem _ ⟨hX,le_of_not_ge hb⟩))
    obtain ⟨G,hG,hd⟩ := mem_iUnion₂.mp hh
    have hd' : dist (pmRamanujanNormalizedBandMellinVector ε X) G < η/2 := hd
    linarith [hfar G hG]
  refine ⟨X,hB,hX,?_⟩
  intro F hF
  obtain ⟨G,hG,hd⟩ := mem_iUnion₂.mp (hcover (Or.inl hF))
  have hd' : dist F G < η/2 := hd
  have hh := dist_triangle (pmRamanujanNormalizedBandMellinVector ε X) F G
  have hf : η/2 ≤ dist (pmRamanujanNormalizedBandMellinVector ε X) F := by
    linarith [hfar G hG]
  simpa only [dist_eq_norm] using hf

theorem exists_uniform_pmRamanujanBandPhysicalCompact_separation {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : Set SoninL2, TotallyBounded K → ∀ B : ℝ,
      ∃ X : ℝ, B ≤ X ∧ 1 ≤ X ∧
        ∀ G ∈ K, c ≤ ‖pmRamanujanNormalizedBandLogVector ε X-G‖ := by
  obtain ⟨c,hc,h⟩ := exists_uniform_pmRamanujanBandCompact_separation hε
  have hκ : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  let V : SoninL2 → SoninL2 := fun G =>
    (Real.sqrt (2*Real.pi) : ℂ) • pmRamanujanCriticalMellinUnitary G
  have hV : UniformContinuous V := by
    simpa only [V,Pi.smul_apply] using!
      pmRamanujanCriticalMellinUnitary.isometry.uniformContinuous.const_smul
        (Real.sqrt (2*Real.pi) : ℂ)
  refine ⟨c/Real.sqrt (2*Real.pi),div_pos hc hκ,?_⟩
  intro K hK B
  obtain ⟨X,hX,hX1,hd⟩ := h (V '' K) (hK.image hV) B
  refine ⟨X,hX,hX1,?_⟩
  intro G hG
  have hh := hd (V G) (mem_image_of_mem _ hG)
  change c ≤ ‖pmRamanujanNormalizedBandMellinVector ε X-
    (Real.sqrt (2*Real.pi) : ℂ) • pmRamanujanCriticalMellinUnitary G‖ at hh
  rw [pmRamanujanNormalizedBandMellinVector_eq_unitary,← smul_sub,← map_sub,norm_smul,
    pmRamanujanCriticalMellinUnitary.norm_map,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hκ] at hh
  exact (div_le_iff₀ hκ).mpr (by simpa only [mul_comm] using hh)

end RHTower
