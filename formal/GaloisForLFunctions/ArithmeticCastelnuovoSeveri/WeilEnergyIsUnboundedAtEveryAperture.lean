import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryApplications

/-!
# The Weil form is unbounded above at every positive aperture

Finitely many Fourier conditions leave a nonzero real test in every positive support interval.
Apply this to the low-frequency grid at an arbitrary energy threshold and the pole. The
near-radical concentration estimate and the grid estimate contradict any upper bound at that
threshold. Consequently no finite scalar `L²` source reserve has Bézout, even at an aperture
where Riemann–Roch and ampleness have already been established.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Finitely many transform samples cannot annihilate every test in a positive interval. -/
theorem exists_nonzero_realTestAt_vanishing_samples {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∃ f : realTestsAt r, (f : realTests) ≠ 0 ∧ ∀ i, paperFT (cx f.1.1) (z i) = 0 := by
  classical
  let N := 2 * Fintype.card ι + 1
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
  let L : (Fin N → ℝ) →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun c k => ∑ i, (c i : ℂ) * paperFT (cx (v i)) (z k)
      map_add' := fun c d => by
        funext k
        simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Complex.real_smul, Finset.mul_sum, mul_assoc] }
  have hdim : Module.finrank ℝ (ι → ℂ) < Module.finrank ℝ (Fin N → ℝ) := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    dsimp [N]
    omega
  obtain ⟨c, hcker, hc0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  let f : ℝ → ℝ := ∑ i, c i • v i
  have hfs : tsupport f ⊆ Icc (-r) r := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hu'
    apply hu
    simp only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hvs i h), mul_zero]
  have hfmem : f ∈ realTests := by
    refine ⟨?_, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs⟩
    have he : f = fun u => ∑ i, c i * v i u := by
      funext u
      simp only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    exact ContDiff.sum fun i _ => (hvd i).const_smul (c i)
  have hcxf : cx f = ∑ i, (c i : ℂ) • cx (v i) := by
    funext u
    simp [f, cx]
  refine ⟨⟨⟨f, hfmem⟩, hfs⟩, ?_, ?_⟩
  · intro h0
    have hf0 : f = 0 := congrArg Subtype.val h0
    exact hc0 (funext ((Fintype.linearIndependent_iff.mp hli) c hf0))
  · intro k
    change paperFT (cx f) (z k) = 0
    rw [hcxf, paperFT_sum_smul (fun i => cx (v i))
      (fun i => (cx_contDiff (hvd i)).continuous) (fun i => cx_hasCompactSupport (hvc i))]
    exact congrFun hcker k

/-- Arbitrarily large Weil energy survives any fixed finite set of transform zeros. -/
theorem exists_realTestAt_weilPair_gt_mul_integral_sq_vanishing_samples
    {r : ℝ} (hr : 0 < r) (M : ℝ) {ι : Type*} [Fintype ι] (z₀ : ι → ℂ) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 ∧
      ∀ i, paperFT (cx f.1.1) (z₀ i) = 0 := by
  classical
  let ε := max M 0
  have hε : 0 ≤ ε := le_max_right _ _
  let T := horizonFreqEps r ε
  let G := lowGridOf T r
  let grid : Option G → ℂ := fun k => match k with
    | none => I / 2
    | some j => (((j : ℤ) : ℝ) * gridStepOf T r : ℝ)
  let z : ι ⊕ Option G → ℂ := Sum.elim z₀ grid
  obtain ⟨f, hf0, hvan⟩ := exists_nonzero_realTestAt_vanishing_samples hr z
  have hmass := integral_sq_pos_of_realTest_ne_zero f.1 hf0
  refine ⟨f, hmass, ?_, fun i => hvan (Sum.inl i)⟩
  have hFd := cx_contDiff f.1.2.1
  have hFc := cx_hasCompactSupport f.1.2.2
  have hFs : tsupport (cx f.1.1) ⊆ Icc (-r) r := by
    rw [tsupport_cx]
    exact f.2
  have hp : paperFT (cx f.1.1) (I / 2) = 0 := hvan (Sum.inr none)
  have hgrid : ∀ j ∈ G,
      paperFT (cx f.1.1) (((j : ℝ) * gridStepOf T r : ℝ) : ℂ) = 0 :=
    fun j hj => hvan (Sum.inr (some ⟨j, hj⟩))
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

/-- The Weil Rayleigh quotient exceeds every real threshold at every positive aperture. -/
theorem exists_realTestAt_weilPair_gt_mul_integral_sq {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ f : realTestsAt r, 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 := by
  obtain ⟨f, hf, hW, -⟩ := exists_realTestAt_weilPair_gt_mul_integral_sq_vanishing_samples
    hr M (fun i : Fin 0 => nomatch i)
  exact ⟨f, hf, hW⟩

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

/-- A finite collection of transform samples cannot supply a Bézout source cone. -/
theorem finiteFourierSourceCone_not_bezout {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      ((scalingSubsurface (realTestsAt r)).sourceCone
        (fun x => ∑ i, ‖paperFT (cx x.2.2.1.1) (z i)‖ ^ 2)) := by
  classical
  intro hB
  let Φ : (ℝ × ℝ × realTestsAt r) → ℝ :=
    fun x => ∑ i, ‖paperFT (cx x.2.2.1.1) (z i)‖ ^ 2
  have hnn : ∀ x, 0 ≤ Φ x := fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfib : ∀ (x : ℝ × ℝ × realTestsAt r) (a b : ℝ),
      Φ (x + a • (scalingSubsurface (realTestsAt r)).H +
        b • (scalingSubsurface (realTestsAt r)).V) = Φ x := by
    intro x a b
    simp [Φ, scalingSubsurface, scalingSurface]
  obtain ⟨f, -, hW, hvan⟩ :=
    exists_realTestAt_weilPair_gt_mul_integral_sq_vanishing_samples hr 0 z
  have hbound := (scalingSubsurface (realTestsAt r)).defect_le_source_of_sourceCone_bezout
    hnn hfib hB (0, 0, f)
  rw [scalingSubsurface_defect_self] at hbound
  have hzero : Φ (0, 0, f) = 0 := by simp [Φ, hvan]
  rw [hzero] at hbound
  simpa only [zero_mul] using (not_lt_of_ge hbound) hW

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
