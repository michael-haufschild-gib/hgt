import GaloisForLFunctions.RHTower.DeckCuspidalLaplaceEigenbasis
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFluxLimit

/-!
# Vanishing constant terms on the cuspidal carrier

Through a fixed near set `L_φ f(z)` is bounded by `vol(𝒟)^{1/2} ‖f‖` uniformly for `z` on a
horocycle segment, so each level horocycle average of `L_φ f` is a Lipschitz function of
`f ∈ L²`.  It vanishes on classes of cuspidal pre-domain vectors (cusp-zero preservation) and hence
on the whole closed cuspidal carrier.  A cuspidal Laplace eigenfunction `U` is a nonzero multiple of
`L_φ` applied to its own class (Selberg's theorem for a concentrated unit profile), so its level
horocycle averages vanish and `U` belongs to the cuspidal Dirichlet pre-domain.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- `∫_𝒟 ‖f‖ ≤ vol(𝒟)^{1/2} ‖f‖_{L²}`. -/
theorem integral_norm_le_L2 (f : DeckL2 N) :
    ∫ z in fd, ‖(f : ℍ → DeckSpace N) z‖ ≤
      ((volume : Measure ℍ) fd).toReal ^ (1 / 2 : ℝ) * ‖f‖ := by
  have hm := (Lp.memLp f).1
  rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
  rw [Measure.restrict_apply_univ] at h
  have hfin : eLpNorm (f : ℍ → DeckSpace N) 2 cellMeasure * (volume fd) ^ (1 / (1 : ℝ≥0∞).toReal -
      1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) volume_fd_ne_top)
  refine (ENNReal.toReal_mono hfin h).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, mul_comm]
  norm_num

/-- Hyperbolically close centres have nested kernel supports. -/
theorem pairU_le_of_dist_le_of_pairU_le {z₀ z w : ℍ} {D R : ℝ} (hD : dist z₀ z ≤ D)
    (h : pairU z w ≤ R) : pairU z₀ w ≤ (Real.cosh (D + (1 + 2 * R)) - 1) / 2 := by
  have h1 := dist_le_of_pairU_le h
  have h2 : dist z₀ w ≤ D + (1 + 2 * R) := (dist_triangle z₀ z w).trans (add_le_add hD h1)
  rw [pairU_eq_cosh]
  have h3 : Real.cosh (dist z₀ w) ≤ Real.cosh (D + (1 + 2 * R)) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans h2)]
    exact h2
  linarith

/-- **Pointwise bound through a fixed near set.** -/
theorem norm_ppApply_le_near {φ : ℝ → ℝ} {M R R' : ℝ} (hφM : ∀ u, |φ u| ≤ M)
    (hφR : KernelSupport φ R) {z₀ z : ℍ} (hnear : ∀ w, pairU z w ≤ R → pairU z₀ w ≤ R')
    {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) :
    ‖ppApply φ F z‖ ≤ 1 / 2 * ((ppNearSet z₀ R').card * (M * ∫ z' in fd, ‖F z'‖)) := by
  have hF1 : Integrable F cellMeasure := hF.integrable one_le_two
  unfold ppApply
  rw [tsum_eq_sum (s := ppNearSet z₀ R') fun B hB => ppTerm_eq_zero hφR F z (by
    rintro ⟨z', hz', h⟩
    apply hB
    simp only [ppNearSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨z', hz', hnear _ h⟩), norm_smul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by norm_num)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun B _ => (norm_ppTerm_le φ F z B).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z' => by positivity)
    (hF1.norm.const_mul M) (Eventually.of_forall fun z' => ?_)
  exact mul_le_mul_of_nonneg_right (hφM _) (norm_nonneg _)

theorem ppApply_sub {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    (hφR : KernelSupport φ R) {F G : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure)
    (hG : MemLp G 2 cellMeasure) : ppApply φ (F - G) = ppApply φ F - ppApply φ G := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ppApply_add hφc hφM hφR hF hG.neg,
    show -G = (-1 : ℂ) • G by simp, ppApply_smul]
  simp

theorem dist_ofComplex_point_le {y : ℝ} (hy : 0 < y) {a x P : ℝ} (hP : 0 ≤ P)
    (hx : x ∈ Set.uIcc a (a + P)) :
    dist (ofComplex (SelbergMaassMean.point a y)) (ofComplex (SelbergMaassMean.point x y)) ≤
      1 + P ^ 2 / (2 * y ^ 2) := by
  have hp : ∀ t : ℝ, 0 < (SelbergMaassMean.point t y).im := fun t => by
    simp [SelbergMaassMean.point, hy]
  have hd := le_cosh_of_nonneg (dist_nonneg (x := ofComplex (SelbergMaassMean.point a y))
    (y := ofComplex (SelbergMaassMean.point x y)))
  have hu := pairU_eq_cosh (ofComplex (SelbergMaassMean.point a y))
    (ofComplex (SelbergMaassMean.point x y))
  have hpair : pairU (ofComplex (SelbergMaassMean.point a y)) (ofComplex (SelbergMaassMean.point x y))
      = (a - x) ^ 2 / (4 * y ^ 2) := by
    unfold pairU
    rw [ofComplex_apply_of_im_pos (hp a), ofComplex_apply_of_im_pos (hp x)]
    change dist (SelbergMaassMean.point a y) (SelbergMaassMean.point x y) ^ 2 /
      (4 * (SelbergMaassMean.point a y).im * (SelbergMaassMean.point x y).im) = _
    rw [Complex.dist_eq]
    simp only [SelbergMaassMean.point]
    rw [show ((a : ℂ) + (y : ℂ) * Complex.I) - ((x : ℂ) + (y : ℂ) * Complex.I) = ((a - x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp
    ring
  have hax : (a - x) ^ 2 ≤ P ^ 2 := by
    rw [uIcc_of_le (by linarith)] at hx
    nlinarith [hx.1, hx.2]
  have hq : (a - x) ^ 2 / (4 * y ^ 2) ≤ P ^ 2 / (4 * y ^ 2) :=
    div_le_div_of_nonneg_right hax (by positivity)
  have : P ^ 2 / (4 * y ^ 2) * 2 = P ^ 2 / (2 * y ^ 2) := by field_simp; ring
  linarith

section ConstantTerm

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
  (hφR : KernelSupport φ R)

/-- The level constant term of `L_φ f` at height `y` over `[a, a + N + 1]` in coordinate `q`. -/
def ctFun (φ : ℝ → ℝ) (q : Deck N) (y a : ℝ) (f : DeckL2 N) : ℂ :=
  ∫ x in a..a + ((N + 1 : ℕ) : ℝ), ppApply φ ⇑f (ofComplex (SelbergMaassMean.point x y)) q

include hφc hφM hφR in
theorem continuous_ctFun (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Continuous (ctFun (N := N) φ q y a) := by
  set P : ℝ := ((N + 1 : ℕ) : ℝ) with hPdef
  have hP : 0 ≤ P := Nat.cast_nonneg _
  set R' := (Real.cosh ((1 + P ^ 2 / (2 * y ^ 2)) + (1 + 2 * R)) - 1) / 2
  set z₀ := ofComplex (SelbergMaassMean.point a y)
  set K : ℝ := P * (1 / 2 * ((ppNearSet z₀ R').card *
    (M * (((volume : Measure ℍ) fd).toReal ^ (1 / 2 : ℝ)))))
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  have hK : 0 ≤ K := by positivity
  have hcont : ∀ f : DeckL2 N, Continuous (fun x : ℝ =>
      ppApply φ ⇑f (ofComplex (SelbergMaassMean.point x y)) q) := fun f =>
    (PiLp.continuous_apply 2 _ q).comp ((continuous_ppApply hφc hφM hφR (Lp.memLp f)).comp
      (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))
  have hlip : ∀ f g : DeckL2 N, ‖ctFun φ q y a f - ctFun φ q y a g‖ ≤ K * ‖f - g‖ := by
    intro f g
    unfold ctFun
    rw [← intervalIntegral.integral_sub ((hcont f).intervalIntegrable _ _)
      ((hcont g).intervalIntegrable _ _)]
    have hpt : ∀ x : ℝ, ppApply φ ⇑f (ofComplex (SelbergMaassMean.point x y)) q -
        ppApply φ ⇑g (ofComplex (SelbergMaassMean.point x y)) q =
        ppApply φ ⇑(f - g) (ofComplex (SelbergMaassMean.point x y)) q := by
      intro x
      rw [ppApply_congr_ae φ (Lp.coeFn_sub f g), ppApply_sub hφc hφM hφR (Lp.memLp f) (Lp.memLp g)]
      rfl
    simp_rw [hpt]
    have hb : ∀ x ∈ Set.uIoc a (a + P), ‖ppApply φ ⇑(f - g) (ofComplex (SelbergMaassMean.point x y)) q‖ ≤
        1 / 2 * ((ppNearSet z₀ R').card *
          (M * (((volume : Measure ℍ) fd).toReal ^ (1 / 2 : ℝ) * ‖f - g‖))) := by
      intro x hx
      have hxI : x ∈ Set.uIcc a (a + P) := Set.uIoc_subset_uIcc hx
      have hD := dist_ofComplex_point_le hy hP hxI
      refine (PiLp.norm_apply_le _ q).trans ((norm_ppApply_le_near hφM hφR (z₀ := z₀)
        (fun w hw => pairU_le_of_dist_le_of_pairU_le hD hw) (Lp.memLp (f - g))).trans ?_)
      gcongr
      exact integral_norm_le_L2 (f - g)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
    rw [show |a + P - a| = P by rw [add_sub_cancel_left, abs_of_nonneg hP]]
    ring
  refine Metric.continuous_iff.2 fun f ε hε => ⟨ε / (K + 1), by positivity, fun g hg => ?_⟩
  rw [dist_eq_norm] at hg ⊢
  calc ‖ctFun φ q y a g - ctFun φ q y a f‖ ≤ K * ‖g - f‖ := hlip g f
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hg.le hK
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

include hφc hφM hφR in
/-- **Cusp-zero passes to the whole cuspidal carrier**: for every `f` in the closed cuspidal `L²`
space, `L_φ f` has vanishing level horocycle averages. -/
theorem levelCuspZero_ppApply_of_mem {f : DeckL2 N} (hf : f ∈ cuspidalL2Closure N) :
    levelCuspZero N (ppApply φ ⇑f) := by
  intro q y hy a
  change ctFun φ q y a f = 0
  have hclosed : IsClosed {f : DeckL2 N | ctFun φ q y a f = 0} :=
    isClosed_eq (continuous_ctFun hφc hφM hφR q hy a) continuous_const
  have hbase : ∀ G : cuspidalFormPreDomain N,
      ctFun φ q y a (toDeckL2 (G : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp G)) = 0 := by
    intro G
    unfold ctFun
    rw [ppApply_congr_ae φ (show ⇑(toDeckL2 (G : ℍ → DeckSpace N)
      (cuspidalFormPreDomain.memLp G)) =ᵐ[cellMeasure] (G : ℍ → DeckSpace N) from
      MemLp.coeFn_toLp (cuspidalFormPreDomain.memLp G))]
    exact levelCuspZero_ppApply hφc hφR (continuous_of_isChartC1 (cuspidalFormPreDomain.c1 G))
      (fun A z => (cuspidalFormPreDomain.toFormPreDomain N G).2.2.1 A z)
      (cuspidalFormPreDomain.cusp_zero G) q hy a
  have hT : (cuspidalFormDomainClosure N : Set (FormTriple N)) ⊆
      (fun x : FormTriple N => x.ofLp 0) ⁻¹' {f : DeckL2 N | ctFun φ q y a f = 0} := by
    refine closure_minimal ?_ (hclosed.preimage (PiLp.continuous_apply 2 _ 0))
    rintro _ ⟨G, rfl⟩
    exact hbase G
  have hU : (cuspidalL2Closure N : Set (DeckL2 N)) ⊆ {f : DeckL2 N | ctFun φ q y a f = 0} := by
    refine closure_minimal ?_ hclosed
    rintro _ ⟨v, rfl⟩
    exact hT v.2
  exact hU hf

end ConstantTerm

/-! ## Cuspidal eigenfunctions -/

/-- Every real eigenvalue has a spectral parameter: `s(1 - s) = λ`. -/
theorem exists_spectral_parameter (lam : ℝ) : ∃ s : ℂ, s * (1 - s) = lam := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((1 / 4 : ℂ) - lam) (n := 2) (by norm_num)
  exact ⟨1 / 2 + t, by linear_combination -ht⟩

namespace IsCuspLaplaceEigen

variable {lam : ℝ} {U : ℍ → DeckSpace N}

/-- A cuspidal eigenfunction is a fixed multiple of a point-pair average of itself. -/
theorem exists_selberg_rep (hU : IsCuspLaplaceEigen N lam U) :
    ∃ (P : SmoothProfile) (h : ℂ), h ≠ 0 ∧ ∀ z, ppApply P.toFun U z = h • U z := by
  obtain ⟨s, hs⟩ := exists_spectral_parameter lam
  obtain ⟨R₀, hR₀, hne⟩ := exists_radius_selbergTransform_ne_zero s
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR₀
  refine ⟨P, selbergTransform P.toFun s,
    hne P.pp.differentiable.continuous hP0 hPm P.kernelSupport hPR, fun z => ?_⟩
  refine ppApply_eigen P.pp.differentiable.continuous P.kernelSupport hU.contDiffOn hU.equivariant
    (fun z => ?_) z
  rw [hU.eigen z, hs]
  push_cast
  ring_nf

/-- **Cuspidal eigenfunctions have vanishing level horocycle averages.** -/
theorem levelCuspZero (hU : IsCuspLaplaceEigen N lam U) : levelCuspZero N U := by
  obtain ⟨P, h, hh, hPU⟩ := hU.exists_selberg_rep
  have hrep : U = h⁻¹ • ppApply P.toFun ⇑(toDeckL2 U hU.memLp) := by
    funext z
    rw [ppApply_congr_ae _ (show ⇑(toDeckL2 U hU.memLp) =ᵐ[cellMeasure] U from
      MemLp.coeFn_toLp hU.memLp), Pi.smul_apply, hPU z, smul_smul, inv_mul_cancel₀ hh, one_smul]
  have h0 := levelCuspZero_ppApply_of_mem P.pp.differentiable.continuous P.pp.abs_le
    P.kernelSupport hU.cuspidal
  intro q y hy a
  rw [hrep]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  have h1 := h0 q hy a
  simp only [SmoothProfile.pp_toFun] at h1
  rw [h1, mul_zero]

/-- **Cuspidal eigenfunctions lie in the cuspidal Dirichlet pre-domain.** -/
theorem mem_cuspidalFormPreDomain (hU : IsCuspLaplaceEigen N lam U) :
    U ∈ cuspidalFormPreDomain N := by
  obtain ⟨P, h, hh, hPU⟩ := hU.exists_selberg_rep
  have hrep : U = ppApply P.toFun (h⁻¹ • U) := by
    funext z
    rw [ppApply_smul, Pi.smul_apply, hPU z, smul_smul, inv_mul_cancel₀ hh, one_smul]
  refine ⟨?_, hU.levelCuspZero⟩
  rw [hrep]
  exact ppApply_mem_formPreDomain P.pp.differentiable P.pp.continuous_deriv P.pp.abs_le
    P.pp.abs_deriv_le P.radius_nonneg P.pp.support (hU.memLp.const_smul _)

end IsCuspLaplaceEigen

end

end GaloisForLFunctions.RHTower.DeckPointPair
