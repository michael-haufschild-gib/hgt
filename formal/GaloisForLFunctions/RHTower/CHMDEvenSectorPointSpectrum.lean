import GaloisForLFunctions.RHTower.CHMDOddSectorCriterion
import GaloisForLFunctions.RHTower.WeilEvenConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion

/-!
# The even sector and the point spectrum of the arithmetic resolvent

The reflection `J` of the mass space fixes the ground vector `1` and negates the polar vector
`tanh`. On the even sector `{w : Jw = w}` the `tanh`-term of the Weil form vanishes, and the
constant graph vector is null for the Weil bilinear form, so the Weil form of an even graph vector
`p` equals the Doob energy of its even primitive part `p − 2⟪Sp,1⟫·(constant lift of 1)`.
Nonnegative Doob energy on the even primitive sector therefore gives Weil positivity on every even
real test, hence (splitting a complex test into its real and imaginary parts) on the even cone,
which is a criterion for RH. With the generic invariant-subspace dictionary:

`RH ⟺ R has no even primitive eigenvector above 1/2`.

Every eigenvector with eigenvalue `μ ≠ 1` is automatically primitive, and `1` is an eigenvalue
with eigenvector `1`, so the primitive-hyperplane criterion becomes a statement about the point
spectrum of `R` itself:

`RH ⟺ the point spectrum of R in (1/2, 1] is the simple eigenvalue 1 spanned by the ground vector`,

and the same holds within the even sector. Together with the odd criterion, odd bound states
above `1/2` and even primitive bound states above `1/2` exist simultaneously or not at all.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Parity of the polar vectors -/

theorem reflectMass_oneL : reflectMass oneL = oneL := by
  rw [Lp.ext_iff]
  have h1 := reflectMass_coeFn oneL
  have h2 : (oneL : ℝ → ℝ) =ᵐ[massMeasure] fun _ => (1 : ℝ) := by
    unfold oneL
    exact MemLp.coeFn_toLp _
  have h3 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx3
  rw [hx1, hx3, hx2]

theorem reflectMass_tanhL : reflectMass tanhL = -tanhL := by
  rw [Lp.ext_iff]
  have h1 := reflectMass_coeFn tanhL
  have h2 : (tanhL : ℝ → ℝ) =ᵐ[massMeasure] tanhHalf := by
    unfold tanhL
    exact MemLp.coeFn_toLp _
  have h3 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp h2
  have h4 := Lp.coeFn_neg tanhL
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx3
  rw [hx1, hx3, tanhHalf_neg, hx4, Pi.neg_apply, hx2]

/-- The polar vector `tanh` is orthogonal to every even vector. -/
theorem inner_tanhL_eq_zero_of_even {w : MassSpace} (hw : reflectMass w = w) :
    ⟪w, tanhL⟫_ℝ = 0 := by
  have h := reflectMass.inner_map_map w tanhL
  rw [hw, reflectMass_tanhL, inner_neg_right] at h
  linarith

/-! ## The even sector, the primitive sector and their intersection -/

def evenOp : MassSpace →L[ℝ] MassSpace :=
  reflectMass.toContinuousLinearMap - ContinuousLinearMap.id ℝ MassSpace

/-- The even sector `{w : Jw = w}`. -/
def evenSector : Submodule ℝ MassSpace := LinearMap.ker (evenOp : MassSpace →ₗ[ℝ] MassSpace)

theorem mem_evenSector {w : MassSpace} : w ∈ evenSector ↔ reflectMass w = w := by
  unfold evenSector
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  change reflectMass w - w = 0 ↔ _
  rw [sub_eq_zero]

theorem isClosed_evenSector : IsClosed (evenSector : Set MassSpace) := evenOp.isClosed_ker

theorem resolventInvariant_evenSector : ResolventInvariant evenSector := by
  intro w hw
  rw [mem_evenSector] at hw ⊢
  rw [← resolvent_reflectMass, hw]

/-- The primitive sector `{w : ⟪w, 1⟫ = 0}`. -/
def primitiveSector : Submodule ℝ MassSpace := (ℝ ∙ oneL)ᗮ

theorem mem_primitiveSector {w : MassSpace} : w ∈ primitiveSector ↔ ⟪w, oneL⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left

theorem isClosed_primitiveSector : IsClosed (primitiveSector : Set MassSpace) :=
  Submodule.isClosed_orthogonal _

theorem resolventInvariant_primitiveSector : ResolventInvariant primitiveSector := by
  intro w hw
  rw [mem_primitiveSector] at hw ⊢
  rw [inner_resolvent_oneL, real_inner_comm w oneL, hw]

/-- The even primitive sector. -/
def evenPrimitiveSector : Submodule ℝ MassSpace := evenSector ⊓ primitiveSector

theorem mem_evenPrimitiveSector {w : MassSpace} :
    w ∈ evenPrimitiveSector ↔ reflectMass w = w ∧ ⟪w, oneL⟫_ℝ = 0 := by
  unfold evenPrimitiveSector
  rw [Submodule.mem_inf, mem_evenSector, mem_primitiveSector]

theorem isClosed_evenPrimitiveSector : IsClosed (evenPrimitiveSector : Set MassSpace) := by
  unfold evenPrimitiveSector
  rw [Submodule.coe_inf]
  exact isClosed_evenSector.inter isClosed_primitiveSector

theorem resolventInvariant_evenPrimitiveSector : ResolventInvariant evenPrimitiveSector := by
  intro w hw
  rw [mem_evenPrimitiveSector] at hw ⊢
  exact ⟨mem_evenSector.mp (resolventInvariant_evenSector w (mem_evenSector.mpr hw.1)),
    mem_primitiveSector.mp (resolventInvariant_primitiveSector w (mem_primitiveSector.mpr hw.2))⟩

/-! ## The constant graph vector is null for the Weil bilinear form -/

theorem weilBilin_smul_left (a : ℝ) (p q : SourceGraph) :
    weilBilin (a • p) q = a * weilBilin p q := by
  unfold weilBilin
  have h : (a • p).val.fst = a • p.val.fst := rfl
  rw [h, inner_smul_graph]
  simp only [real_inner_smul_left]
  ring

theorem weilBilin_smul_right (a : ℝ) (p q : SourceGraph) :
    weilBilin p (a • q) = a * weilBilin p q := by
  rw [weilBilin_comm, weilBilin_smul_left, weilBilin_comm]

theorem weilBilin_constantLift_one (q : SourceGraph) : weilBilin q (constantLift 1) = 0 := by
  have h1 : ⟪q, constantLift 1⟫_ℝ = ⟪q.val.fst, oneL⟫_ℝ := by
    rw [← rieszLift_oneL, real_inner_comm (rieszLift oneL) q, inner_rieszLift,
      real_inner_comm q.val.fst oneL]
  have h2 : (constantLift 1).val.fst = oneL := oneL_eq_constantLift.symm
  unfold weilBilin
  rw [h1, h2, real_inner_self_eq_norm_sq, norm_oneL_sq, ← real_inner_comm oneL tanhL,
    inner_tanhL_oneL]
  ring

theorem weilBilin_constantLift_one_left (q : SourceGraph) : weilBilin (constantLift 1) q = 0 := by
  rw [weilBilin_comm, weilBilin_constantLift_one]

/-! ## Even polar reduction -/

/-- The even primitive part of a graph vector: subtract the constant graph vector carrying its
mass. -/
def evenPrimitivePart (p : SourceGraph) : SourceGraph :=
  p - (2 * ⟪p.val.fst, oneL⟫_ℝ) • constantLift 1

theorem evenPrimitivePart_fst (p : SourceGraph) :
    (evenPrimitivePart p).val.fst = p.val.fst - (2 * ⟪p.val.fst, oneL⟫_ℝ) • oneL := rfl

theorem inner_evenPrimitivePart_oneL (p : SourceGraph) :
    ⟪(evenPrimitivePart p).val.fst, oneL⟫_ℝ = 0 := by
  rw [evenPrimitivePart_fst, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_oneL_sq]
  ring

theorem evenPrimitivePart_fst_mem (p : SourceGraph) (hp : reflectMass p.val.fst = p.val.fst) :
    (evenPrimitivePart p).val.fst ∈ evenPrimitiveSector := by
  rw [mem_evenPrimitiveSector]
  refine ⟨?_, inner_evenPrimitivePart_oneL p⟩
  rw [evenPrimitivePart_fst, map_sub, map_smul, hp, reflectMass_oneL]

/-- **Even polar reduction.** The Weil form of an even graph vector is the Doob energy of its even
primitive part: both polar terms vanish there. -/
theorem weilForm_eq_sourceEnergy_evenPrimitivePart (p : SourceGraph)
    (hp : reflectMass p.val.fst = p.val.fst) :
    weilForm p = sourceEnergy (evenPrimitivePart p) := by
  have h0 : weilForm (evenPrimitivePart p) = weilForm p := by
    rw [weilForm_eq_weilBilin, weilForm_eq_weilBilin]
    unfold evenPrimitivePart
    simp only [weilBilin_sub_left, weilBilin_sub_right, weilBilin_smul_left, weilBilin_smul_right,
      weilBilin_constantLift_one, weilBilin_constantLift_one_left]
    ring
  rw [← h0]
  unfold weilForm
  rw [inner_evenPrimitivePart_oneL,
    inner_tanhL_eq_zero_of_even (mem_evenPrimitiveSector.mp (evenPrimitivePart_fst_mem p hp)).1]
  ring

/-! ## Even compact tests -/

theorem reflectMass_compactLift_fst_of_even {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (heven : ∀ x, v (-x) = v x) :
    reflectMass (compactLift v hv hvc).val.fst = (compactLift v hv hvc).val.fst := by
  rw [reflectMass_compactLift_fst, Lp.ext_iff]
  have h1 := compactLift_source_ae (fun x => v (-x)) (hv.comp contDiff_neg)
    (hvc.comp_homeomorph (Homeomorph.neg ℝ))
  have h3 := compactLift_source_ae v hv hvc
  filter_upwards [h1, h3] with x hx1 hx3
  rw [hx1, hx3, heven]

theorem weilForm_compactLift_nonneg_of_even_energy
    (hE : ∀ p : SourceGraph, p.val.fst ∈ evenPrimitiveSector → 0 ≤ sourceEnergy p)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (heven : ∀ x, v (-x) = v x) :
    0 ≤ weilForm (compactLift v hv hvc) := by
  have hp := reflectMass_compactLift_fst_of_even hv hvc heven
  rw [weilForm_eq_sourceEnergy_evenPrimitivePart _ hp]
  exact hE _ (evenPrimitivePart_fst_mem _ hp)

/-- Nonnegative Doob energy on the even primitive sector gives Weil positivity on every even real
test. -/
theorem re_W_ofReal_nonneg_of_even_energy
    (hE : ∀ p : SourceGraph, p.val.fst ∈ evenPrimitiveSector → 0 ≤ sourceEnergy p)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ x, g (-x) = g x) :
    0 ≤ (zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ))).re := by
  have hveven : ∀ x, phiDoobInv g (-x) = phiDoobInv g x := fun x => by
    unfold phiDoobInv
    rw [heven, WeilExcess.riemannKernelReal_neg]
  have h := weilForm_compactLift_nonneg_of_even_energy hE (contDiff_phiDoobInv hg)
    (hasCompactSupport_phiDoobInv hgc) hveven
  rw [weilForm_compactLift] at h
  simpa only [phiDoobTest_phiDoobInv] using h

/-! ## Complex even tests: real and imaginary parts -/

/-- The real part of the Weil functional of a complex test is the sum over its real and imaginary
parts. -/
theorem re_weilFullFunctional_split (lam : ℕ → ℝ) (F : WeilOneSided.WeilTestFn) :
    (weilFullFunctional lam (EF.weilTest F.1 F.1)).re =
      (weilFullFunctional lam (EF.weilTest (WeilWorkPBAP.paperRealPartTestFn F).1
        (WeilWorkPBAP.paperRealPartTestFn F).1)).re +
      (weilFullFunctional lam (EF.weilTest (WeilWorkPBAP.paperImagPartTestFn F).1
        (WeilWorkPBAP.paperImagPartTestFn F).1)).re := by
  classical
  set R := WeilWorkPBAP.paperRealPartTestFn F with hR
  set J := WeilWorkPBAP.paperImagPartTestFn F with hJ
  have hsplit : WeilWorkPBAP.paperSplitRealMixture (Finsupp.single F 1) =
      Finsupp.single R 1 + Finsupp.single J 1 := by
    simp [WeilWorkPBAP.paperSplitRealMixture, hR, hJ, Finsupp.mapDomain_single]
  have hE := WeilWorkPBAP.energy_paperSplitRealMixture (Finsupp.single F 1)
  have hD := WeilWorkPBAP.defect_paperSplitRealMixture (Finsupp.single F 1)
  rw [hsplit] at hE hD
  simp only [WeilWorkPBAP.energy, WeilWorkPBAP.defect, map_add, Finsupp.linearCombination_single,
    one_smul] at hE hD
  rw [WeilOneSided.re_weilFullFunctional_eq lam F, WeilOneSided.re_weilFullFunctional_eq lam R,
    WeilOneSided.re_weilFullFunctional_eq lam J, ← hE, ← hD, map_add]
  ring

/-- Nonnegative Doob energy on the even primitive sector gives Weil positivity on every even
complex test. -/
theorem re_weilFullFunctional_nonneg_of_even_energy
    (hE : ∀ p : SourceGraph, p.val.fst ∈ evenPrimitiveSector → 0 ≤ sourceEnergy p)
    (F : WeilOneSided.WeilEvenTestFn) :
    0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest F.1.1 F.1.1)).re := by
  rw [re_weilFullFunctional_split]
  have key : ∀ (g : ℝ → ℝ), ContDiff ℝ 2 g → HasCompactSupport g → (∀ x, g (-x) = g x) →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (g x : ℂ)) (fun x => (g x : ℂ)))).re := by
    intro g hg hgc heven
    have h := re_W_ofReal_nonneg_of_even_energy hE hg hgc heven
    have hgC : ContDiff ℝ 2 (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    rwa [zeta_W_eq_weilFullFunctional hgC hgcC] at h
  have hRpos := key (fun x => (F.1.1 x).re) (Complex.reCLM.contDiff.comp F.1.2.1)
    (F.1.2.2.comp_left (g := fun z : ℂ => z.re) (by simp))
    (fun x => congrArg Complex.re (F.2 x))
  have hJpos := key (fun x => (F.1.1 x).im) (Complex.imCLM.contDiff.comp F.1.2.1)
    (F.1.2.2.comp_left (g := fun z : ℂ => z.im) (by simp))
    (fun x => congrArg Complex.im (F.2 x))
  exact add_nonneg hRpos hJpos

/-! ## The even primitive sector detects RH -/

theorem sourceEnergy_nonneg_of_rh_evenPrimitive (hRH : RiemannHypothesis) (p : SourceGraph)
    (hp : p.val.fst ∈ evenPrimitiveSector) : 0 ≤ sourceEnergy p :=
  sourceEnergy_nonneg_of_rh hRH p (mem_evenPrimitiveSector.mp hp).2

theorem riemannHypothesis_of_evenPrimitive_energy
    (hE : ∀ p : SourceGraph, p.val.fst ∈ evenPrimitiveSector → 0 ≤ sourceEnergy p) :
    RiemannHypothesis := by
  rw [WeilOneSided.riemannHypothesis_iff_positiveOnEvenNonnegCone]
  intro c hc _
  exact Finsupp.sum_nonneg fun f _ =>
    mul_nonneg (hc f) (re_weilFullFunctional_nonneg_of_even_energy hE f)

/-- **RH ⟺ the arithmetic resolvent is at most `1/2` on the even primitive sector.** -/
theorem riemannHypothesis_iff_evenPrimitive_half_bound :
    RiemannHypothesis ↔ ∀ w ∈ evenPrimitiveSector, ⟪resolvent w, w⟫_ℝ ≤ (1 / 2) * ‖w‖ ^ 2 :=
  ⟨fun h => half_bound_on_of_energy resolventInvariant_evenPrimitiveSector
      (sourceEnergy_nonneg_of_rh_evenPrimitive h),
   fun h => riemannHypothesis_of_evenPrimitive_energy fun p hp =>
      energy_nonneg_on_of_half_bound h p hp⟩

/-- **The even primitive sector detects RH: RH ⟺ no even primitive eigenvector of the arithmetic
resolvent above `1/2`.** -/
theorem riemannHypothesis_iff_no_evenPrimitive_bound_state :
    RiemannHypothesis ↔
      ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → reflectMass w = w → ⟪w, oneL⟫_ℝ = 0 →
        resolvent w = μ • w → w = 0 := by
  rw [riemannHypothesis_iff_evenPrimitive_half_bound]
  constructor
  · intro h μ w hμ heven hprim heig
    exact eq_zero_of_eigenvector_of_half_bound h hμ
      (mem_evenPrimitiveSector.mpr ⟨heven, hprim⟩) heig
  · intro h
    exact half_bound_on_of_no_eigenvector resolventInvariant_evenPrimitiveSector
      isClosed_evenPrimitiveSector fun μ w hμ hw heig =>
        h μ w hμ (mem_evenPrimitiveSector.mp hw).1 (mem_evenPrimitiveSector.mp hw).2 heig

/-- **RH fails ⟺ an even primitive bound state above `1/2` exists.** -/
theorem not_riemannHypothesis_iff_exists_evenPrimitive_bound_state :
    ¬ RiemannHypothesis ↔
      ∃ (μ : ℝ) (w : MassSpace), 1 / 2 < μ ∧ w ≠ 0 ∧ reflectMass w = w ∧ ⟪w, oneL⟫_ℝ = 0 ∧
        resolvent w = μ • w := by
  rw [riemannHypothesis_iff_no_evenPrimitive_bound_state]
  constructor
  · intro h
    simp only [not_forall] at h
    obtain ⟨μ, w, hμ, heven, hprim, heig, hne⟩ := h
    exact ⟨μ, w, hμ, hne, heven, hprim, heig⟩
  · rintro ⟨μ, w, hμ, hne, heven, hprim, heig⟩ h
    exact hne (h μ w hμ heven hprim heig)

/-- **Parity pairing of bound states.** Odd bound states above `1/2` exist exactly when even
primitive bound states above `1/2` exist. -/
theorem exists_odd_bound_state_iff_exists_evenPrimitive_bound_state :
    (∃ (μ : ℝ) (w : MassSpace), 1 / 2 < μ ∧ w ≠ 0 ∧ reflectMass w = -w ∧ resolvent w = μ • w) ↔
      ∃ (μ : ℝ) (w : MassSpace), 1 / 2 < μ ∧ w ≠ 0 ∧ reflectMass w = w ∧ ⟪w, oneL⟫_ℝ = 0 ∧
        resolvent w = μ • w := by
  rw [← not_riemannHypothesis_iff_exists_odd_bound_state,
    ← not_riemannHypothesis_iff_exists_evenPrimitive_bound_state]

/-! ## The point spectrum above `1/2` -/

/-- Every eigenvector of the arithmetic resolvent with eigenvalue `μ ≠ 1` is primitive. -/
theorem inner_oneL_eq_zero_of_eigenvector {μ : ℝ} (hμ : μ ≠ 1) {w : MassSpace}
    (heig : resolvent w = μ • w) : ⟪w, oneL⟫_ℝ = 0 := by
  have h := inner_resolvent_oneL w
  rw [heig, real_inner_smul_left, real_inner_comm w oneL] at h
  have h' : (μ - 1) * ⟪w, oneL⟫_ℝ = 0 := by linarith
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hμ
  · exact h1

/-- Without primitive bound states, the eigenspace at `1` is spanned by the ground vector. -/
theorem eq_smul_oneL_of_eigen_one
    (h : ∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → ⟪w, oneL⟫_ℝ = 0 → resolvent w = μ • w → w = 0)
    {w : MassSpace} (heig : resolvent w = w) : w = (2 * ⟪w, oneL⟫_ℝ) • oneL := by
  have h0 := h 1 (w - (2 * ⟪w, oneL⟫_ℝ) • oneL) (by norm_num) ?_ ?_
  · exact sub_eq_zero.mp h0
  · rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_oneL_sq]
    ring
  · rw [map_sub, map_smul, heig, resolvent_oneL, one_smul]

/-- **RH ⟺ the point spectrum of the arithmetic resolvent above `1/2` is the simple eigenvalue
`1`, spanned by the ground vector.** -/
theorem riemannHypothesis_iff_point_spectrum_above_half :
    RiemannHypothesis ↔
      (∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → μ ≠ 1 → resolvent w = μ • w → w = 0) ∧
      (∀ w : MassSpace, resolvent w = w → w = (2 * ⟪w, oneL⟫_ℝ) • oneL) := by
  rw [riemannHypothesis_iff_no_primitive_bound_state]
  constructor
  · intro h
    exact ⟨fun μ w hμ hμ1 heig => h μ w hμ (inner_oneL_eq_zero_of_eigenvector hμ1 heig) heig,
      fun w heig => eq_smul_oneL_of_eigen_one h heig⟩
  · rintro ⟨h1, h2⟩ μ w hμ hprim heig
    by_cases hμ1 : μ = 1
    · subst hμ1
      rw [one_smul] at heig
      rw [h2 w heig, hprim, mul_zero, zero_smul]
    · exact h1 μ w hμ hμ1 heig

/-- **RH ⟺ the even point spectrum of the arithmetic resolvent above `1/2` is the simple
eigenvalue `1`, spanned by the ground vector.** -/
theorem riemannHypothesis_iff_even_point_spectrum_above_half :
    RiemannHypothesis ↔
      (∀ (μ : ℝ) (w : MassSpace), 1 / 2 < μ → μ ≠ 1 → reflectMass w = w →
        resolvent w = μ • w → w = 0) ∧
      (∀ w : MassSpace, reflectMass w = w → resolvent w = w → w = (2 * ⟪w, oneL⟫_ℝ) • oneL) := by
  rw [riemannHypothesis_iff_no_evenPrimitive_bound_state]
  constructor
  · intro h
    refine ⟨fun μ w hμ hμ1 heven heig =>
      h μ w hμ heven (inner_oneL_eq_zero_of_eigenvector hμ1 heig) heig, fun w heven heig => ?_⟩
    have h0 := h 1 (w - (2 * ⟪w, oneL⟫_ℝ) • oneL) (by norm_num) ?_ ?_ ?_
    · exact sub_eq_zero.mp h0
    · rw [map_sub, map_smul, heven, reflectMass_oneL]
    · rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_oneL_sq]
      ring
    · rw [map_sub, map_smul, heig, resolvent_oneL, one_smul]
  · rintro ⟨h1, h2⟩ μ w hμ heven hprim heig
    by_cases hμ1 : μ = 1
    · subst hμ1
      rw [one_smul] at heig
      rw [h2 w heven heig, hprim, mul_zero, zero_smul]
    · exact h1 μ w hμ hμ1 heven heig

theorem constantLift_fst_eq_smul_oneL (c : ℝ) : (constantLift c).val.fst = c • oneL := by
  apply Lp.ext
  have h1 : ((constantLift c).val.fst : ℝ → ℝ) =ᵐ[massMeasure] fun _ => c :=
    (memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).coeFn_toLp
  have h2 : (oneL : ℝ → ℝ) =ᵐ[massMeasure] fun _ => (1 : ℝ) :=
    (memLp_const 1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  filter_upwards [h1, Lp.coeFn_smul c oneL, h2] with x hx1 hsmul hx2
  rw [hx1, hsmul, Pi.smul_apply, hx2, smul_eq_mul, mul_one]

/-- **Unconditional simplicity of the ground eigenvalue `1` of the arithmetic resolvent.**
By ergodicity of the archimedean jump measure (`edge_zero_iff_constant`), any fixed vector of `R`
has zero graph edge and is therefore a scalar multiple of `oneL`. -/
theorem eq_smul_oneL_of_resolvent_eq {w : MassSpace} (heig : resolvent w = w) :
    w = (2 * ⟪w, oneL⟫_ℝ) • oneL := by
  have hedge : ‖(rieszLift w).val.snd‖ ^ 2 = 0 := by
    rw [edge_norm_sq_rieszLift, heig, real_inner_self_eq_norm_sq, sub_self]
  have hsnd : (rieszLift w).val.snd = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hedge)
  obtain ⟨c, hc⟩ := (edge_zero_iff_constant (rieszLift w)).mp hsnd
  have hw : w = c • oneL := by
    calc w = resolvent w := heig.symm
    _ = (rieszLift w).val.fst := rfl
    _ = (constantLift c).val.fst := by rw [hc]
    _ = c • oneL := constantLift_fst_eq_smul_oneL c
  have hc_eq : c = 2 * ⟪w, oneL⟫_ℝ := by
    have h1 : ⟪w, oneL⟫_ℝ = c * (1 / 2) := by
      rw [hw, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_oneL_sq]
    linarith
  rw [hc_eq] at hw
  exact hw

/-- **Strict spectral bound on the primitive hyperplane.** Every nonzero primitive eigenvector of
the arithmetic resolvent has eigenvalue strictly below `1`. -/
theorem eigenvalue_lt_one_of_primitive {μ : ℝ} {w : MassSpace} (hw : w ≠ 0)
    (hprim : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) : μ < 1 := by
  apply lt_of_le_of_ne (eigenvalue_le_one hw heig)
  intro hμ
  subst hμ
  rw [one_smul] at heig
  apply hw
  rw [eq_smul_oneL_of_resolvent_eq heig, hprim, mul_zero, zero_smul]

end RHTower.CHMDPolar
