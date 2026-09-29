import GaloisForLFunctions.RHTower.DeckIncompleteEisensteinParseval

/-!
# Constants are orthogonal to the cuspidal carrier

**Ergodicity of positive point-pair averages** (`eq_of_ppApply_eq_self`).  Let `φ ≥ 0` be a
continuous kernel of unit mass, positive on `[0, R₀)`, and `G` a continuous deck-equivariant field
with `∫_𝒟 ‖G‖² < ∞` and `G(z) = ∫ φ(u(z,w)) G(w) dμ(w)`.  Jensen's identity
`∫ φ(u(z,w)) ‖G(w) - G(z)‖² dμ(w) = (L_φ‖G‖²)(z) - ‖G(z)‖²` integrates over `𝒟` to zero, because
`∫_𝒟 L_φ N = ∫_𝒟 N` for invariant `N ≥ 0`.  So `G` is constant on the disc `u(z, ·) < R₀` for almost
every `z`; this set of centres is invariant and conull, hence dense, so `G` is locally constant, hence
constant.

**Application** (`inner_onesL2_eq_zero_of_mem`).  The projection `g` of `𝟙` onto `CuspidalL2` satisfies
`L_φ g = g` (`L_φ` is symmetric, preserves the cuspidal carrier and fixes `𝟙`), so `g` is a constant
multiple of `𝟙`; a cuspidal multiple of `𝟙` is orthogonal to every incomplete Eisenstein series, which
forces it to vanish.  Hence `⟪𝟙, f⟫ = 0` for every cuspidal `f`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## The constant field -/

/-- The constant field `z ↦ 𝟙`. -/
def onesField (N : ℕ) : ℍ → DeckSpace N := fun _ => onesVec N

theorem deckEquivariant_onesField : deckEquivariant N (onesField N) := fun A _ =>
  (deckRho_onesVec A).symm

theorem memLp_onesField : MemLp (onesField N) 2 cellMeasure := memLp_const _

/-- The constant vector `𝟙 ∈ L²`. -/
def onesL2 (N : ℕ) : DeckL2 N := toDeckL2 (onesField N) memLp_onesField

theorem onesL2_coeFn : (onesL2 N : ℍ → DeckSpace N) =ᵐ[cellMeasure] onesField N :=
  MemLp.coeFn_toLp memLp_onesField

/-! ## Positive unit profiles -/

/-- A smooth nonnegative unit-mass point-pair profile, positive on `|u| < R`. -/
theorem exists_posUnitProfile {R : ℝ} (hR : 0 < R) :
    ∃ P : SmoothProfile, (∀ u, 0 ≤ P.toFun u) ∧ ppKernelMass P.toFun = 1 ∧
      ∀ u, |u| < R → 0 < P.toFun u := by
  let b : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  have hb0 : ∀ u, 0 ≤ b u := fun u => b.nonneg
  have hbR : ∀ u, R < |u| → b u = 0 := fun u hu => by
    have : u ∉ Function.support b := by
      rw [b.support_eq]
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
      exact hu.le
    simpa using this
  have hbc : Continuous b := b.contDiff (n := 0).continuous
  have hbM : ∀ u, |b u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (hb0 u)]; exact b.le_one
  have hfin : ppKernelMass b < ∞ :=
    kernelMass_lt_top hR.le hbM fun u hu => hbR u (lt_of_lt_of_le hu (le_abs_self u))
  have hpos : ppKernelMass b ≠ 0 := by
    unfold ppKernelMass
    intro h0
    have hopen : IsOpen {w : ℍ | pairU UpperHalfPlane.I w < R / 2} :=
      isOpen_lt (continuous_pairU_right _) continuous_const
    have hne : ({w : ℍ | pairU UpperHalfPlane.I w < R / 2} : Set ℍ).Nonempty :=
      ⟨UpperHalfPlane.I, by simp [pairU]; positivity⟩
    have hvol := hopen.measure_pos (volume : Measure ℍ) hne
    have hle : (volume : Measure ℍ) {w : ℍ | pairU UpperHalfPlane.I w < R / 2} ≤
        ∫⁻ w, ENNReal.ofReal |b (pairU UpperHalfPlane.I w)| := by
      rw [← setLIntegral_one]
      refine (setLIntegral_mono (ENNReal.measurable_ofReal.comp
        (hbc.comp (continuous_pairU_right _)).abs.measurable) fun w hw => ?_).trans
          (setLIntegral_le_lintegral _ _)
      have hw' : pairU UpperHalfPlane.I w ∈ Metric.closedBall (0 : ℝ) (R / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg (pairU_nonneg _ _)]
        exact le_of_lt hw
      simp only [Function.comp_apply]
      rw [b.one_of_mem_closedBall hw', abs_one, ENNReal.ofReal_one]
    rw [h0] at hle
    exact (hvol.trans_le hle).ne' rfl
  have hc : 0 < (ppKernelMass b).toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hpos hfin.ne)
  refine ⟨⟨fun u => (ppKernelMass b).toReal⁻¹ * b u, R, hR.le,
    contDiff_const.mul ((b.contDiff (n := ⊤)).of_le (by norm_cast)), fun u hu => by simp [hbR u hu]⟩,
    fun u => mul_nonneg hc.le (hb0 u), ?_, fun u hu => mul_pos hc (b.pos_of_mem_ball (by simpa using hu))⟩
  rw [ppKernelMass_smul hc.le, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hpos hfin.ne),
    ENNReal.ofReal_toReal hfin.ne, ENNReal.inv_mul_cancel hpos hfin.ne]

/-! ## Ergodicity -/

section Ergodic

variable {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
include hφc hφR

theorem integrable_pairKernel_mul {h : ℍ → ℝ} (hc : Continuous h) (z : ℍ) :
    Integrable (fun w : ℍ => φ (pairU z w) * h w) := by
  have hcont : Continuous (fun w : ℍ => φ (pairU z w) * h w) :=
    (hφc.comp (continuous_pairU_right z)).mul hc
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall z (1 + 2 * R))
    ?_).1 (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  intro w hw
  by_contra hwK
  apply hw
  have : R < pairU z w := by
    by_contra h
    push Not at h
    exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  simp [hφR _ this]

omit hφR in
theorem integral_pairKernel (hφ0 : ∀ u, 0 ≤ φ u) (hmass : ppKernelMass φ = 1) (z : ℍ) :
    ∫ w : ℍ, φ (pairU z w) = 1 := by
  have hm : Measurable fun w : ℍ => φ (pairU z w) := (hφc.comp (continuous_pairU_right z)).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w => hφ0 _)
    hm.aestronglyMeasurable]
  have h := kernelMass_centre φ z
  simp_rw [abs_of_nonneg (hφ0 _)] at h
  rw [h, hmass, ENNReal.toReal_one]

/-- **Ergodicity of positive point-pair averages.** -/
theorem eq_of_ppApply_eq_self (hφ0 : ∀ u, 0 ≤ φ u) (hmass : ppKernelMass φ = 1) {R₀ : ℝ}
    (hR₀ : 0 < R₀) (hφpos : ∀ u, |u| < R₀ → 0 < φ u) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G) (hGL : MemLp G 2 cellMeasure) (hfix : ∀ z, ppApply φ G z = G z)
    (z w : ℍ) : G z = G w := by
  -- the mean value identity
  have hmv : ∀ z, G z = ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • G w := fun z => by
    rw [← ppApply_eq_integral hφc hφR hGc hGe, hfix]
  set Nf : ℍ → ℝ := fun w => ‖G w‖ ^ 2
  have hNc : Continuous Nf := hGc.norm.pow 2
  have hNinv : ∀ (A : SL(2, ℤ)) w, Nf (A • w) = Nf w := fun A w => by
    simp only [Nf]
    rw [hGe A w]
    exact congrArg (· ^ 2) (LinearIsometryEquiv.norm_map _ _)
  set LN : ℍ → ℝ := fun z => ∫ w : ℍ, φ (pairU z w) * Nf w
  set D : ℍ → ℝ := fun z => ∫ w : ℍ, φ (pairU z w) * ‖G w - G z‖ ^ 2
  -- Jensen's identity
  have hjensen : ∀ z, D z = LN z - Nf z := fun z => by
    have hint1 := integrable_pairKernel_mul hφc hφR hNc z
    have hre : Continuous fun w => RCLike.re ⟪G w, G z⟫_ℂ :=
      RCLike.continuous_re.comp (hGc.inner continuous_const)
    have hint2 := integrable_pairKernel_mul hφc hφR hre z
    have hint3 := (integrable_pairKernel_mul hφc hφR (continuous_const (y := (1 : ℝ))) z)
    have hone := integral_pairKernel hφc hφ0 hmass z
    have hmean : ∫ w : ℍ, φ (pairU z w) * RCLike.re ⟪G w, G z⟫_ℂ = Nf z := by
      have hi := integrable_pairKernel_smul hφc hφR hGc z
      have h1 : RCLike.re ⟪G z, G z⟫_ℂ = Nf z := by
        simp only [Nf]; rw [inner_self_eq_norm_sq]
      rw [← h1]
      symm
      calc RCLike.re ⟪G z, G z⟫_ℂ
          = RCLike.re ⟪G z, ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • G w⟫_ℂ := by rw [← hmv z]
        _ = RCLike.re (∫ w : ℍ, ⟪G z, ((φ (pairU z w) : ℝ) : ℂ) • G w⟫_ℂ) := by
            rw [integral_inner hi]
        _ = ∫ w : ℍ, RCLike.re ⟪G z, ((φ (pairU z w) : ℝ) : ℂ) • G w⟫_ℂ :=
            (integral_re (hi.const_inner _)).symm
        _ = ∫ w : ℍ, φ (pairU z w) * RCLike.re ⟪G w, G z⟫_ℂ := by
            refine integral_congr_ae (Eventually.of_forall fun w => ?_)
            simp only
            rw [inner_smul_right, inner_re_symm (G w) (G z)]
            exact Complex.re_ofReal_mul _ _
    have hexp : ∀ w, φ (pairU z w) * ‖G w - G z‖ ^ 2 =
        φ (pairU z w) * Nf w - 2 * (φ (pairU z w) * RCLike.re ⟪G w, G z⟫_ℂ) +
          Nf z * (φ (pairU z w) * 1) := fun w => by
      simp only [Nf]
      rw [norm_sub_sq (𝕜 := ℂ)]
      ring
    have hA : Integrable fun w => φ (pairU z w) * Nf w - 2 * (φ (pairU z w) * RCLike.re ⟪G w, G z⟫_ℂ) :=
      hint1.sub (hint2.const_mul 2)
    have hB : Integrable fun w => Nf z * (φ (pairU z w) * 1) := hint3.const_mul _
    have hC : Integrable fun w => 2 * (φ (pairU z w) * RCLike.re ⟪G w, G z⟫_ℂ) := hint2.const_mul 2
    simp only [D, LN]
    simp_rw [hexp]
    rw [integral_add hA hB, integral_sub hint1 hC, integral_const_mul, integral_const_mul, hmean]
    simp_rw [mul_one]
    rw [hone]
    ring
  have hD0 : ∀ z, 0 ≤ D z := fun z => integral_nonneg fun w => mul_nonneg (hφ0 _) (sq_nonneg _)
  have hLN : ∀ z, LN z = D z + Nf z := fun z => by rw [hjensen z]; ring
  -- `∫_𝒟 L_φ N = ∫_𝒟 N`
  have hNm : Measurable fun w => ENNReal.ofReal (Nf w) := ENNReal.measurable_ofReal.comp hNc.measurable
  have hLNpt : ∀ z, ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
      ENNReal.ofReal (Nf z') = 2 * ENNReal.ofReal (LN z) := fun z => by
    have h := tsum_lintegral_fd_smul (fun w => ENNReal.ofReal |φ (pairU z w)| * ENNReal.ofReal (Nf w))
    simp only [hNinv] at h
    rw [h, ofReal_integral_eq_lintegral_ofReal (integrable_pairKernel_mul hφc hφR hNc z)
      (Eventually.of_forall fun w => mul_nonneg (hφ0 _) (sq_nonneg _))]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [abs_of_nonneg (hφ0 _), ENNReal.ofReal_mul (hφ0 _)]
  have hint := lintegral_tsum_kernel_mul hφc hNm
  simp_rw [hLNpt] at hint
  rw [lintegral_const_mul _ (by
      have hs : StronglyMeasurable fun z => LN z :=
        (((hφc.comp continuous_pairU).mul (hNc.comp continuous_snd)).stronglyMeasurable).integral_prod_right'
      exact ENNReal.measurable_ofReal.comp hs.measurable), hmass, mul_one] at hint
  have hLNeq : ∫⁻ z in fd, ENNReal.ofReal (LN z) = ∫⁻ z in fd, ENNReal.ofReal (Nf z) :=
    (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 hint
  have hNfin : ∫⁻ z in fd, ENNReal.ofReal (Nf z) ≠ ∞ :=
    (Integrable.lintegral_lt_top (hGL.integrable_norm_pow two_ne_zero)).ne
  -- `D = 0` almost everywhere on `𝒟`
  have hDint : ∫⁻ z in fd, ENNReal.ofReal (D z) = 0 := by
    have hle := le_lintegral_add (μ := volume.restrict fd) (fun z => ENNReal.ofReal (D z))
      (fun z => ENNReal.ofReal (Nf z))
    have hsum : ∫⁻ z in fd, ENNReal.ofReal (D z) + ENNReal.ofReal (Nf z) =
        ∫⁻ z in fd, ENNReal.ofReal (LN z) := by
      refine lintegral_congr fun z => ?_
      rw [hLN z, ENNReal.ofReal_add (hD0 z) (sq_nonneg _)]
    rw [hsum, hLNeq] at hle
    exact le_antisymm (ENNReal.le_of_add_le_add_right hNfin (by simpa using hle)) zero_le
  have hDm : Measurable D :=
    ((((hφc.comp continuous_pairU).mul (((hGc.comp continuous_snd).sub
      (hGc.comp continuous_fst)).norm.pow 2))).stronglyMeasurable).integral_prod_right'.measurable
  have hDae : ∀ᵐ z ∂(volume.restrict fd), D z = 0 := by
    have h := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hDm)).1 hDint
    filter_upwards [h] with z hz
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 hz) (hD0 z)
  -- discs of constancy
  set S : Set ℍ := {z | ∀ w, pairU z w < R₀ → G w = G z}
  have hS : ∀ z, D z = 0 → z ∈ S := fun z hz w hw => by
    have hk : Continuous fun w => φ (pairU z w) * ‖G w - G z‖ ^ 2 :=
      (hφc.comp (continuous_pairU_right z)).mul ((hGc.sub continuous_const).norm.pow 2)
    have hae := (integral_eq_zero_iff_of_nonneg (fun w => mul_nonneg (hφ0 _) (sq_nonneg _))
      (integrable_pairKernel_mul hφc hφR ((hGc.sub continuous_const).norm.pow 2) z)).1 hz
    have heq := congrFun ((Continuous.ae_eq_iff_eq volume hk continuous_const).1 hae) w
    have hp : 0 < φ (pairU z w) := hφpos _ (by rw [abs_of_nonneg (pairU_nonneg _ _)]; exact hw)
    have heq' : φ (pairU z w) * ‖G w - G z‖ ^ 2 = 0 := heq
    have h2 : ‖G w - G z‖ ^ 2 = 0 := (mul_eq_zero.1 heq').resolve_left hp.ne'
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))
  have hSinv : ∀ (A : SL(2, ℤ)) z, z ∈ S → A • z ∈ S := fun A z hz w hw => by
    have h1 : pairU z (A⁻¹ • w) < R₀ := by
      rwa [← pairU_smul_int A, smul_inv_smul]
    have h2 := hz _ h1
    rw [← smul_inv_smul A w, hGe A (A⁻¹ • w), hGe A z, h2]
  have hSnull : volume Sᶜ = 0 := by
    have hfd : volume (fd ∩ Sᶜ) = 0 := by
      have h := (ae_restrict_iff' isClosed_fd.measurableSet).1 (hDae.mono fun z hz => hS z hz)
      rw [ae_iff] at h
      convert h using 2
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, Classical.not_imp]
    have hsub : Sᶜ ⊆ ⋃ A : SL(2, ℤ), A • (fd ∩ Sᶜ) := by
      intro x hx
      obtain ⟨g, hg⟩ := exists_smul_mem_fd x
      refine mem_iUnion.2 ⟨g⁻¹, ⟨g • x, ⟨hg, fun h => hx ?_⟩, inv_smul_smul g x⟩⟩
      have := hSinv g⁻¹ _ h
      rwa [inv_smul_smul] at this
    refine measure_mono_null hsub (measure_iUnion_null fun A => ?_)
    rw [measure_smul]
    exact hfd
  -- local constancy
  obtain ⟨ε, hε, hcosh⟩ := Metric.eventually_nhds_iff.1
    ((Real.continuous_cosh.tendsto 0).eventually (gt_mem_nhds (show Real.cosh 0 < 1 + 2 * R₀ by
      rw [Real.cosh_zero]; linarith)))
  have hball : ∀ s ∈ S, ∀ w, dist s w < ε → G w = G s := fun s hs w hw => by
    refine hs w ?_
    have h := hcosh (y := dist s w) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg])
    rw [pairU_eq_cosh]
    linarith
  have hloc : IsLocallyConstant G := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z₀
    have hne : (ball z₀ (ε / 2) ∩ S).Nonempty := by
      by_contra h
      have hsub : ball z₀ (ε / 2) ⊆ Sᶜ := fun x hx hxS => h ⟨x, hx, hxS⟩
      exact (isOpen_ball.measure_pos volume ⟨z₀, mem_ball_self (half_pos hε)⟩).ne'
        (measure_mono_null hsub hSnull)
    obtain ⟨s, hs1, hs2⟩ := hne
    filter_upwards [ball_mem_nhds z₀ (half_pos hε)] with w hw
    have hsw : dist s w < ε := by
      have := dist_triangle s z₀ w
      rw [mem_ball] at hs1 hw
      rw [dist_comm] at hw
      linarith
    have hsz : dist s z₀ < ε := by
      rw [mem_ball] at hs1
      linarith
    rw [hball s hs2 w hsw, hball s hs2 z₀ hsz]
  exact hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _)

end Ergodic

/-! ## Constants are orthogonal to the cuspidal carrier -/

/-- An equivariant constant is a multiple of `𝟙`. -/
theorem eq_smul_onesVec_of_deckRho {c : DeckSpace N} (hc : ∀ A : SL(2, ℤ), deckRho N A c = c) :
    c = c 1 • onesVec N := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H A =>
    have h := congrArg (fun v : DeckSpace N => v 1) (hc A)
    simp only [deckRho_apply, one_mul] at h
    rw [PiLp.smul_apply, onesVec_apply, smul_eq_mul, mul_one, ← h]

theorem ppApply_onesField {φ : ℝ → ℝ} (hφc : Continuous φ) {R : ℝ} (hφR : KernelSupport φ R)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : ppKernelMass φ = 1) (z : ℍ) :
    ppApply φ (onesField N) z = onesVec N := by
  rw [ppApply_eq_integral (F := onesField N) hφc hφR continuous_const deckEquivariant_onesField]
  simp only [onesField]
  rw [integral_smul_const, integral_complex_ofReal, integral_pairKernel hφc hφ0 hmass,
    Complex.ofReal_one, one_smul]

/-- **Constants are orthogonal to the cuspidal carrier.** -/
theorem inner_onesL2_eq_zero_of_mem {f : DeckL2 N} (hf : f ∈ cuspidalL2Closure N) :
    ⟪onesL2 N, f⟫_ℂ = 0 := by
  set K := cuspidalL2Closure N
  haveI : CompleteSpace K := cuspidalL2_completeSpace N
  set g : DeckL2 N := K.starProjection (onesL2 N)
  have hgK : g ∈ K := K.starProjection_apply_mem _
  have horth : ∀ f ∈ K, ⟪onesL2 N, f⟫_ℂ = ⟪g, f⟫_ℂ := fun f hf => by
    have := K.starProjection_inner_eq_zero (onesL2 N) f hf
    rw [inner_sub_left, sub_eq_zero] at this
    exact this
  obtain ⟨P, hP0, hPm, hPpos⟩ := exists_posUnitProfile (R := 1) one_pos
  set L := P.pp.op N
  have hLones : L (onesL2 N) = onesL2 N := by
    change ppL2 _ _ _ _ (toDeckL2 (onesField N) memLp_onesField) = _
    rw [ppL2_toDeckL2_eq]
    exact toDeckL2_congr _ _ (Eventually.of_forall fun z =>
      ppApply_onesField P.pp.differentiable.continuous P.pp.support hP0 hPm z)
  have hLK : ∀ f ∈ K, L f ∈ K := fun f hf => (P.pp.cuspOp N ⟨f, hf⟩).2
  have hsym : ∀ x y, ⟪L x, y⟫_ℂ = ⟪x, L y⟫_ℂ := fun x y => P.pp.op_isSymmetric N x y
  have hLg : L g = g := by
    have h : ∀ f ∈ K, ⟪L g - g, f⟫_ℂ = 0 := fun f hf => by
      rw [inner_sub_left, hsym g f, ← horth _ (hLK f hf), ← hsym, hLones, horth f hf, sub_self]
    have hmem : L g - g ∈ K := K.sub_mem (hLK g hgK) hgK
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (h _ hmem))
  -- the continuous representative
  set G : ℍ → DeckSpace N := ppApply P.toFun g
  have hGc : Continuous G := continuous_ppApply P.pp.differentiable.continuous P.pp.abs_le
    P.pp.support (Lp.memLp g)
  have hGe : deckEquivariant N G := fun A z => ppApply_smul_point P.pp.support _ A z
  have hGg : G =ᵐ[cellMeasure] g := by
    have h := P.pp.op_coeFn g
    rw [hLg] at h
    exact h.symm
  have hGL : MemLp G 2 cellMeasure := (Lp.memLp g).ae_eq hGg.symm
  have hfix : ∀ z, ppApply P.toFun G z = G z := fun z => by
    rw [ppApply_congr_ae _ hGg]
  have hconst := eq_of_ppApply_eq_self P.pp.differentiable.continuous P.pp.support hP0 hPm
    one_pos (fun u hu => hPpos u hu) hGc hGe hGL hfix
  set c : DeckSpace N := G UpperHalfPlane.I
  have hcfix : ∀ A : SL(2, ℤ), deckRho N A c = c := fun A => by
    rw [← hGe A, hconst (A • UpperHalfPlane.I) UpperHalfPlane.I]
  have hgc : g = (c 1) • onesL2 N := by
    apply Lp.ext
    filter_upwards [hGg, Lp.coeFn_smul (c 1) (onesL2 N), onesL2_coeFn] with z h1 h2 h3
    rw [← h1, h2, Pi.smul_apply, h3, hconst z UpperHalfPlane.I, onesField]
    exact eq_smul_onesVec_of_deckRho hcfix
  -- a cuspidal multiple of `𝟙` vanishes
  have hc0 : c 1 = 0 := by
    set G' : ℍ → DeckSpace N := fun _ => c 1 • onesVec N
    have hG'c : Continuous G' := continuous_const
    have hG'e : deckEquivariant N G' := fun A _ => by
      change c 1 • onesVec N = deckRho N A (c 1 • onesVec N)
      rw [map_smul, deckRho_onesVec]
    have hgG' : (g : ℍ → DeckSpace N) =ᵐ[cellMeasure] G' := by
      rw [hgc]
      filter_upwards [Lp.coeFn_smul (c 1) (onesL2 N), onesL2_coeFn] with z h2 h3
      rw [h2, Pi.smul_apply, h3]
      rfl
    have hT : deckRho N ModularGroup.T (onesVec N) = onesVec N := deckRho_onesVec _
    have hzero : ∀ ψ : HeightProfile, ∫ y in Ioi (0 : ℝ),
        (y ^ 2)⁻¹ • (conj (ψ.toFun y) * horoAverage (onesVec N) G' y) = 0 := fun ψ => by
      have h1 := inner_incEisL2 ψ hT hgG' hG'c hG'e
      rw [inner_incEisL2_eq_zero_of_mem ψ hT hgK] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left two_ne_zero
    have h1 := eq_zero_of_forall_heightProfile (continuousOn_horoAverage hG'c _) hzero one_pos
    have hval : horoAverage (onesVec N) G' 1 = c 1 * ⟪onesVec N, onesVec N⟫_ℂ := by
      simp only [horoAverage, G', inner_smul_right]
      rw [setIntegral_const, Real.volume_real_Ico_of_le zero_le_one, sub_zero, one_smul]
    rw [hval] at h1
    have hne : ⟪onesVec N, onesVec N⟫_ℂ ≠ 0 := by
      rw [inner_self_ne_zero]
      intro h
      have := congrArg (fun v : DeckSpace N => v 1) h
      simp [onesVec_apply] at this
    exact (mul_eq_zero.1 h1).resolve_right hne
  rw [horth f hf, hgc, hc0, zero_smul, inner_zero_left]

end

end GaloisForLFunctions.RHTower.DeckPointPair
