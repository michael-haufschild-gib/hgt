import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryApplications

/-!
# The Weil form is unbounded above at every positive aperture

Every finite-dimensional linear reading leaves a nonzero real test in every positive support
interval. Apply this jointly to any prescribed reading, the low-frequency grid at an arbitrary
energy threshold, and the pole. The
near-radical concentration estimate and the grid estimate contradict any upper bound at that
threshold. Consequently no finite scalar `L²` source reserve has Bézout, even at an aperture
where Riemann–Roch and ampleness have already been established. Arbitrary postprocessing of a
finite-dimensional linear reading also fails Bézout: its kernel retains unbounded Weil energy.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Every finite-dimensional linear reading has a nonzero kernel at positive aperture. -/
theorem exists_nonzero_realTestAt_in_ker {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, (f : realTests) ≠ 0 ∧ L f = 0 := by
  classical
  let N := Module.finrank ℝ V + 1
  have hnhd : Ioo (-(r / 2)) (r / 2) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith only [hr]) (by linarith only [hr])
  obtain ⟨g, hgs, hgc, hgd, -, hg0⟩ := exists_contDiff_tsupport_subset (n := 2) hnhd
  have hgne : g ≠ 0 := fun h => by simp [h] at hg0
  let s : Fin N → ℝ := fun i => -(r / 2) + i * (r / N)
  have hNpos : (0 : ℝ) < N := by dsimp [N]; positivity
  have hstep : 0 < r / N := div_pos hr hNpos
  have hsinj : Function.Injective s := by
    intro i j hij
    simp only [s, add_right_inj] at hij
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hstep.ne' hij)
  have hs_mem : ∀ i, -(r / 2) ≤ s i ∧ s i ≤ r / 2 := by
    intro i
    have hi : (i : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    have h1 : 0 ≤ (i : ℝ) * (r / N) := by positivity
    have h2 : (i : ℝ) * (r / N) ≤ r := by
      calc (i : ℝ) * (r / N) ≤ N * (r / N) :=
            mul_le_mul_of_nonneg_right hi hstep.le
        _ = r := by field_simp
    constructor <;> dsimp [s] <;> linarith only [h1, h2]
  let v : Fin N → ℝ → ℝ := fun i u => g (u - s i)
  have hvd : ∀ i, ContDiff ℝ 2 (v i) :=
    fun _ => hgd.comp (contDiff_id.sub contDiff_const)
  have hvs : ∀ i, tsupport (v i) ⊆ Icc (-r) r := by
    intro i
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - s i ∈ Ioo (-(r / 2)) (r / 2) := hgs (subset_tsupport g hu)
    obtain ⟨hs0, hs1⟩ := hs_mem i
    exact ⟨by linarith only [hu'.1, hs0], by linarith only [hu'.2, hs1]⟩
  have hvc : ∀ i, HasCompactSupport (v i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hvs i)
  have hli : LinearIndependent ℝ v := linearIndependent_real_translate hsinj hgc hgne
  let vTest : Fin N → realTestsAt r := fun i => ⟨⟨v i, hvd i, hvc i⟩, hvs i⟩
  let B : (Fin N → ℝ) →ₗ[ℝ] realTestsAt r :=
    { toFun := fun c => ∑ i, c i • vTest i
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum] }
  have hdim : Module.finrank ℝ V < Module.finrank ℝ (Fin N → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    dsimp [N]
    omega
  obtain ⟨c, hcker, hc0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := L.comp B) hdim)
  refine ⟨B c, ?_, hcker⟩
  intro h0
  have hf0 : ∑ i, c i • v i = 0 := by
    simpa [B, vTest] using congrArg Subtype.val h0
  exact hc0 (funext ((Fintype.linearIndependent_iff.mp hli) c hf0))

/-- A finite family of Fourier evaluations as a real linear source reading. -/
def realTestAtFourierSamples (r : ℝ) {ι : Type*} (z : ι → ℂ) :
    realTestsAt r →ₗ[ℝ] (ι → ℂ) where
  toFun f i := paperFT (cx f.1.1) (z i)
  map_add' f g := by
    funext i
    change paperFT (cx (f.1.1 + g.1.1)) (z i) =
      paperFT (cx f.1.1) (z i) + paperFT (cx g.1.1) (z i)
    rw [cx_add]
    exact paperFT_add (cx_contDiff f.1.2.1).continuous (cx_hasCompactSupport f.1.2.2)
      (cx_contDiff g.1.2.1).continuous (cx_hasCompactSupport g.1.2.2) (z i)
  map_smul' t f := by
    funext i
    change paperFT (cx (t • f.1.1)) (z i) = t • paperFT (cx f.1.1) (z i)
    rw [cx_smul, paperFT_smul, Complex.real_smul]

/-- Finitely many transform samples cannot annihilate every test in a positive interval. -/
theorem exists_nonzero_realTestAt_vanishing_samples {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∃ f : realTestsAt r, (f : realTests) ≠ 0 ∧ ∀ i, paperFT (cx f.1.1) (z i) = 0 := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_realTestAt_in_ker hr (realTestAtFourierSamples r z)
  exact ⟨f, hf, fun i => congrFun hz i⟩

/-- The Weil Rayleigh quotient is unbounded in every finite-dimensional reading kernel. -/
theorem exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq
    {r : ℝ} (hr : 0 < r) (M : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 ∧ L f = 0 := by
  classical
  let ε := max M 0
  have hε : 0 ≤ ε := le_max_right _ _
  let T := horizonFreqEps r ε
  let G := lowGridOf T r
  let grid : Option G → ℂ := fun k => match k with
    | none => I / 2
    | some j => (((j : ℤ) : ℝ) * gridStepOf T r : ℝ)
  obtain ⟨f, hf0, hker⟩ :=
    exists_nonzero_realTestAt_in_ker hr (L.prod (realTestAtFourierSamples r grid))
  have hvan : ∀ i, paperFT (cx f.1.1) (grid i) = 0 :=
    fun i => congrFun (congrArg Prod.snd hker) i
  have hmass := integral_sq_pos_of_realTest_ne_zero f.1 hf0
  refine ⟨f, hmass, ?_, congrArg Prod.fst hker⟩
  have hFd := cx_contDiff f.1.2.1
  have hFc := cx_hasCompactSupport f.1.2.2
  have hFs : tsupport (cx f.1.1) ⊆ Icc (-r) r := by
    rw [tsupport_cx]
    exact f.2
  have hp : paperFT (cx f.1.1) (I / 2) = 0 := hvan none
  have hgrid : ∀ j ∈ G,
      paperFT (cx f.1.1) (((j : ℝ) * gridStepOf T r : ℝ) : ℂ) = 0 :=
    fun j hj => hvan (some ⟨j, hj⟩)
  have hW : (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re = weilPair f.1.1 f.1.1 := by
    rw [weilPair, RHTower.zeta_W_eq_weilFullFunctional_mixed hFd hFc hFd hFc]
  have hnorm : (∫ u, ‖cx f.1.1 u‖ ^ 2) = ∫ u : ℝ, (f.1.1 u) ^ 2 := by
    congr 1
    funext u
    rw [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hεW : ε * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 := by
    by_contra hle
    have hle' : (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re ≤ ε * ∫ u, ‖cx f.1.1 u‖ ^ 2 := by
      rw [hW, hnorm]
      exact le_of_not_gt hle
    have hlo := pi_mul_integral_le_of_re_W_le hε hFd hFs hp hle'
    have hhi := integral_band_le_of_lowGridOf (horizonFreqEps_nonneg r hε) hr.le
      hFd.continuous hFc hFs hgrid
    rw [hnorm] at hlo hhi
    have hπ : 1 < π := by linarith only [Real.pi_gt_three]
    have hstrict := mul_lt_mul_of_pos_right hπ hmass
    linarith only [hlo, hhi, hstrict]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left M 0) hmass.le) hεW

/-- Arbitrarily large Weil energy survives any fixed finite set of transform zeros. -/
theorem exists_realTestAt_weilPair_gt_mul_integral_sq_vanishing_samples
    {r : ℝ} (hr : 0 < r) (M : ℝ) {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 ∧
      ∀ i, paperFT (cx f.1.1) (z i) = 0 := by
  obtain ⟨f, hmass, hW, hker⟩ :=
    exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr M (realTestAtFourierSamples r z)
  exact ⟨f, hmass, hW, fun i => congrFun hker i⟩

/-- The Weil Rayleigh quotient exceeds every real threshold at every positive aperture. -/
theorem exists_realTestAt_weilPair_gt_mul_integral_sq {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 := by
  obtain ⟨f, hf, hW, -⟩ := exists_realTestAt_weilPair_gt_mul_integral_sq_vanishing_samples
    hr M (fun i : Fin 0 => Fin.elim0 i)
  exact ⟨f, hf, hW⟩

/-- The absolute Weil energy is unbounded in every finite-dimensional reading kernel. -/
theorem exists_realTestAt_in_ker_weilPair_gt {r : ℝ} (hr : 0 < r) (A : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, A < weilPair f.1.1 f.1.1 ∧ L f = 0 := by
  obtain ⟨f, -, hf, hker⟩ := exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr 0 L
  have hw : 0 < weilPair f.1.1 f.1.1 := by simpa only [zero_mul] using hf
  let t := Real.sqrt ((max A 0 + 1) / weilPair f.1.1 f.1.1)
  have ht2 : t ^ 2 = (max A 0 + 1) / weilPair f.1.1 f.1.1 :=
    Real.sq_sqrt (div_nonneg (by positivity) hw.le)
  have hprod : t ^ 2 * weilPair f.1.1 f.1.1 = max A 0 + 1 := by
    rw [ht2]
    field_simp [hw.ne']
  refine ⟨t • f, ?_, ?_⟩
  · change A < weilPair (t • f.1.1) (t • f.1.1)
    rw [weilPair_smul_left, weilPair_comm f.1.1 (t • f.1.1), weilPair_smul_left]
    nlinarith only [hprod, le_max_left A 0]
  · rw [map_smul, hker, smul_zero]

/-- On a finite-blind source fibre, the absolute Weil energy has no finite upper bound. -/
theorem exists_realTestAt_weilPair_gt_vanishing_samples {r : ℝ} (hr : 0 < r) (A : ℝ)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∃ f : realTestsAt r, A < weilPair f.1.1 f.1.1 ∧
      ∀ i, paperFT (cx f.1.1) (z i) = 0 := by
  obtain ⟨f, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt hr A (realTestAtFourierSamples r z)
  exact ⟨f, hW, fun i => congrFun hker i⟩

/-- Every finite scalar source reserve admits a negative-square cycle, even in its strict cone. -/
theorem exists_strictL2SourceCone_realTestsAt_negative_square {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ∃ x ∈ strictL2SourceCone c (realTestsAt r),
      (scalingSubsurface (realTestsAt r)).pair x x < 0 := by
  obtain ⟨f, -, hf⟩ := exists_realTestAt_weilPair_gt_mul_integral_sq hr (max c 0)
  obtain ⟨x, hx, hxx⟩ := exists_strictL2SourceCone_negative_square (le_max_right c 0)
    (realTestsAt r) f hf
  refine ⟨x, ?_, hxx⟩
  rw [mem_strictL2SourceCone_iff] at hx ⊢
  refine ⟨hx.1, hx.2.1, lt_of_le_of_lt ?_ hx.2.2⟩
  exact mul_le_mul_of_nonneg_right (le_max_left c 0) (integral_nonneg fun _ => sq_nonneg _)

/-- No finite `L²` reserve has Bézout on a positive-aperture scaling surface. -/
theorem realTestsAt_l2SourceCones_not_bezout {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom (l2SourceCone c (realTestsAt r)) ∧
      ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom (strictL2SourceCone c (realTestsAt r)) ∧
      ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom (gradedL2SourceCone c (realTestsAt r)) := by
  obtain ⟨x, hx, hxx⟩ := exists_strictL2SourceCone_realTestsAt_negative_square hr c
  have hx' : x ∈ l2SourceCone c (realTestsAt r) :=
    (scalingSubsurface (realTestsAt r)).strictSourceCone_subset_sourceCone _ hx
  have hxg : x ∈ gradedL2SourceCone c (realTestsAt r) :=
    (scalingSubsurface (realTestsAt r)).sourceCone_subset_gradedSourceCone _ hx'
  exact ⟨fun hB => (not_lt_of_ge (hB x hx' x hx')) hxx,
    fun hB => (not_lt_of_ge (hB x hx x hx)) hxx,
    fun hB => (not_lt_of_ge (hB x hxg x hxg)) hxx⟩

/-- The unconditional all-aperture graded RR cone never satisfies Bézout at positive aperture. -/
theorem gradedChebyshevSourceCone_riemannRoch_and_not_bezout {r : ℝ} (hr : 0 < r) :
    (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-(10 + 72 * Real.exp r)) (realTestsAt r)) ∧
      ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
        (gradedL2SourceCone (-(10 + 72 * Real.exp r)) (realTestsAt r)) :=
  ⟨(gradedL2SourceCone_realTestsAt_all_apertures_riemannRoch hr).1.1,
    (realTestsAt_l2SourceCones_not_bezout hr _).2.2⟩

/-- No postprocessing of a finite-dimensional linear reading supplies a Bézout source cone. -/
theorem finiteLinearReadingSourceCone_not_bezout {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => F (L x.2.2))) := by
  classical
  intro hB
  let Φ : (ℝ × ℝ × realTestsAt r) → ℝ :=
    fun x => F (L x.2.2)
  have hfib : ∀ (x : ℝ × ℝ × realTestsAt r) (a b : ℝ),
      Φ (x + a • (scalingSubsurface (realTestsAt r)).H +
        b • (scalingSubsurface (realTestsAt r)).V) = Φ x := by
    intro x a b
    simp [Φ, scalingSubsurface, scalingSurface]
  obtain ⟨f, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt hr (max (F 0) 0) L
  have hzero : Φ (0, 0, f) = F 0 := congrArg F hker
  let S := scalingSubsurface (realTestsAt r)
  let x := S.withFibreDegrees (0, 0, f) (max (F 0) 0) (1 / 2)
  have hx : x ∈ S.sourceCone Φ := by
    rw [S.mem_sourceCone_iff]
    dsimp only [x]
    rw [S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
      S.source_withFibreDegrees hfib, hzero, S.polar_self,
      S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    exact ⟨le_max_right _ _, by positivity, by linarith only [le_max_left (F 0) 0]⟩
  have hbound := hB _ hx _ hx
  change 0 ≤ S.pair x x at hbound
  dsimp only [x] at hbound
  rw [S.pair_withFibreDegrees, scalingSubsurface_defect_self] at hbound
  linarith only [hbound, hW]

/-- In particular, arbitrary finite Fourier postprocessing fails Bézout at every aperture. -/
theorem finiteFourierPostprocessingSourceCone_not_bezout {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (F : (ι → ℂ) → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => F (fun i => paperFT (cx x.2.2.1.1) (z i)))) :=
  finiteLinearReadingSourceCone_not_bezout hr (realTestAtFourierSamples r z) F

/-- Subtracting the value at zero does not remove the finite-reading obstruction. -/
theorem finiteFourierReadingSourceCone_not_bezout {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (F : (ι → ℂ) → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => F (fun i => paperFT (cx x.2.2.1.1) (z i)) - F 0)) :=
  finiteFourierPostprocessingSourceCone_not_bezout hr z (fun w => F w - F 0)

/-- In particular, a finite sum of squared transform samples cannot supply Bézout. -/
theorem finiteFourierSourceCone_not_bezout {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => ∑ i, ‖paperFT (cx x.2.2.1.1) (z i)‖ ^ 2)) := by
  exact finiteFourierPostprocessingSourceCone_not_bezout hr z (fun w => ∑ i, ‖w i‖ ^ 2)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_realTestAt_in_ker_weilPair_gt
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.realTestsAt_l2SourceCones_not_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.gradedChebyshevSourceCone_riemannRoch_and_not_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.finiteLinearReadingSourceCone_not_bezout
