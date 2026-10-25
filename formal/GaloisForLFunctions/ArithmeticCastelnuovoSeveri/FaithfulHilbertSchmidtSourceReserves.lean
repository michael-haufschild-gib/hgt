import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSharpAndTheHilbertAdjoint
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticMajorantsSupplyBezout
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveQuadraticSourceCones
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerHilbertSchmidtSource
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceDefect

/-!
# A faithful Hilbert–Schmidt reserve on the genuine Meyer surface

The full-Hasse convolution representation supplies a positive quadratic reserve
without an order assumption. Its excess over the actual source trace is exactly
half the squared adjoint defect. The cone has Bézout and ampleness; its Riemann–Roch
axiom detects simple critical zeros, including the higher-jet obstruction.
Representation of this reserve by a linear sharp-square degree has the same criterion.
-/

noncomputable section
open Complex Zeta23 RHTower ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private def sourceSharpRealLM : DeningerMeyerStrongLogTarget →ₗ[ℝ] DeningerMeyerStrongLogTarget where
  toFun := deningerMeyerSourceSharp
  map_add' g h := by
    simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_add, map_add]
  map_smul' a g := by
    change deningerMeyerStrongLogJ (deningerMeyerStrongLogConj ((a : ℂ) • g)) =
      (a : ℂ) • deningerMeyerStrongLogJ (deningerMeyerStrongLogConj g)
    rw [deningerMeyerStrongLogConj_smul, map_smul, Complex.star_def, Complex.conj_ofReal]

private def sourceOperatorRealLM : DeningerMeyerStrongLogTarget →ₗ[ℝ]
    (DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert) where
  toFun := deningerMeyerHilbertConvolution
  map_add' := deningerMeyerHilbertConvolution_add
  map_smul' a g := by
    change deningerMeyerHilbertConvolution ((a : ℂ) • g) =
      (a : ℂ) • deningerMeyerHilbertConvolution g
    exact deningerMeyerHilbertConvolution_smul _ _

private def cycleSourceLM : MeyerScalingCycle →ₗ[ℝ] DeningerMeyerStrongLogTarget where
  toFun x := x.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def cycleOperatorLM := sourceOperatorRealLM.comp cycleSourceLM
private def cycleSharpOperatorLM := sourceOperatorRealLM.comp (sourceSharpRealLM.comp cycleSourceLM)

private def realHsPullback {C H : Type*} [AddCommGroup C] [Module ℝ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : C →ₗ[ℝ] (H →L[ℂ] H)) (hL : ∀ x, (L x).IsHilbertSchmidt) :
    C →ₗ[ℝ] C →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (hsInner (L x) (L y)).re)
    (fun x y z => by rw [map_add, hsInner_add_left (hL x) (hL y) (hL z), Complex.add_re])
    (fun a x y => by
      rw [map_smul]
      change (hsInner ((a : ℂ) • L x) (L y)).re = a * (hsInner (L x) (L y)).re
      rw [hsInner_smul_left]
      simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero])
    (fun x y z => by rw [map_add, hsInner_add_right (hL x) (hL y) (hL z), Complex.add_re])
    (fun a x y => by
      rw [map_smul]
      change (hsInner (L x) ((a : ℂ) • L y)).re = a * (hsInner (L x) (L y)).re
      rw [hsInner_smul_right]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])

/-- The faithful source/sharp Hilbert–Schmidt reserve. -/
def meyerHilbertReserve (x : MeyerScalingCycle) : ℝ :=
  (hsNormSq (deningerMeyerHilbertConvolution x.2.2) +
    hsNormSq (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))) / 2

/-- The real bilinear form underlying the faithful reserve. -/
def meyerHilbertReserveBilinear : MeyerScalingCycle →ₗ[ℝ] MeyerScalingCycle →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    (realHsPullback cycleOperatorLM (fun x => meyerHilbertConvolution_isHilbertSchmidt x.2.2) +
      realHsPullback cycleSharpOperatorLM
        (fun x => meyerHilbertConvolution_isHilbertSchmidt (deningerMeyerSourceSharp x.2.2)))

theorem meyerHilbertReserveBilinear_self (x : MeyerScalingCycle) :
    meyerHilbertReserveBilinear x x = meyerHilbertReserve x := by
  change (1 / 2 : ℝ) * ((hsInner (deningerMeyerHilbertConvolution x.2.2)
      (deningerMeyerHilbertConvolution x.2.2)).re +
    (hsInner (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))
      (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))).re) = _
  rw [hsInner_self_re (meyerHilbertConvolution_isHilbertSchmidt _),
    hsInner_self_re (meyerHilbertConvolution_isHilbertSchmidt _)]
  unfold meyerHilbertReserve
  ring

theorem meyerHilbertReserveBilinear_symm (x y : MeyerScalingCycle) :
    meyerHilbertReserveBilinear x y = meyerHilbertReserveBilinear y x := by
  have hcomm (A B : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert) :
      (hsInner A B).re = (hsInner B A).re := by rw [hsInner_conj_symm A B]; rfl
  change (1 / 2 : ℝ) * ((hsInner (cycleOperatorLM x) (cycleOperatorLM y)).re +
      (hsInner (cycleSharpOperatorLM x) (cycleSharpOperatorLM y)).re) = _
  rw [hcomm (cycleOperatorLM x), hcomm (cycleSharpOperatorLM x)]
  rfl

theorem meyerHilbertReserve_nonneg (x : MeyerScalingCycle) : 0 ≤ meyerHilbertReserve x :=
  div_nonneg (add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)) (by norm_num)

private theorem reserve_neg (x : MeyerScalingCycle) :
    meyerHilbertReserve (-x) = meyerHilbertReserve x := by
  rw [← meyerHilbertReserveBilinear_self, ← meyerHilbertReserveBilinear_self]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

private theorem reserve_fibre (x : MeyerScalingCycle) (a b : ℝ) :
    meyerHilbertReserve (x + a • meyerScalingSurface.H + b • meyerScalingSurface.V) =
      meyerHilbertReserve x := by
  have he : (x + a • meyerScalingSurface.H + b • meyerScalingSurface.V).2.2 = x.2.2 := by
    change x.2.2 + a • (0 : DeningerMeyerStrongLogTarget) + b • 0 = x.2.2
    simp only [smul_zero, add_zero]
  simp only [meyerHilbertReserve, he]

/-- The reserve excess is precisely the actual full-Hasse adjoint defect. -/
theorem meyerHilbertReserve_sub_defect (x : MeyerScalingCycle) :
    meyerHilbertReserve x - meyerScalingSurface.defect x x =
      hsNormSq (deningerMeyerHilbertConvolution x.2.2 -
        adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))) / 2 := by
  rw [meyerScalingSurface_defect]
  exact half_hsNormSq_sum_sub_re_trace (meyerHilbertConvolution_isHilbertSchmidt _)
    (meyerHilbertConvolution_isHilbertSchmidt _)

theorem meyerHilbertReserve_add_defect (x : MeyerScalingCycle) :
    meyerHilbertReserve x + meyerScalingSurface.defect x x =
      hsNormSq (deningerMeyerHilbertConvolution x.2.2 +
        adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))) / 2 := by
  rw [meyerScalingSurface_defect]
  exact half_hsNormSq_sum_add_re_trace (meyerHilbertConvolution_isHilbertSchmidt _)
    (meyerHilbertConvolution_isHilbertSchmidt _)

/-- Unlike ordinary trace, the positive reserve detects every genuine cohomology class. -/
theorem meyerHilbertReserve_eq_zero_iff (x : MeyerScalingCycle) :
    meyerHilbertReserve x = 0 ↔ x.2.2 ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  constructor
  · intro h
    have hn : hsNormSq (deningerMeyerHilbertConvolution x.2.2) = 0 := by
      unfold meyerHilbertReserve at h
      linarith only [h, hsNormSq_nonneg (deningerMeyerHilbertConvolution x.2.2),
        hsNormSq_nonneg (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2))]
    exact (deningerMeyerHilbertConvolution_eq_zero_iff _).mp
      ((hsNormSq_eq_zero_iff (meyerHilbertConvolution_isHilbertSchmidt _)).mp hn)
  · intro h
    have hs : deningerMeyerSourceSharp x.2.2 ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
      obtain ⟨f, hf⟩ := h
      rw [← hf, meyerSourceSharp_boundary]
      exact ⟨_, rfl⟩
    rw [meyerHilbertReserve, (deningerMeyerHilbertConvolution_eq_zero_iff _).mpr h,
      (deningerMeyerHilbertConvolution_eq_zero_iff _).mpr hs]
    simp only [hsNormSq, zero_apply, norm_zero, zero_pow (by omega : 2 ≠ 0),
      tsum_zero, zero_add, zero_div]

/-- The reserve depends only on the genuine source class, including all jets. -/
theorem meyerHilbertReserve_congr {x y : MeyerScalingCycle}
    (he : (Submodule.Quotient.mk x.2.2 : DeningerMeyerStrongLogCohomology) =
      Submodule.Quotient.mk y.2.2) : meyerHilbertReserve x = meyerHilbertReserve y := by
  have hs := congrArg (fun u => deningerMeyerStrongLogCohomologyJ (deningerMeyerCohomologyConj u)) he
  change (Submodule.Quotient.mk (deningerMeyerSourceSharp x.2.2) :
    DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk (deningerMeyerSourceSharp y.2.2) at hs
  rw [meyerHilbertReserve, meyerHilbertReserve, deningerMeyerHilbertConvolution_congr he,
    deningerMeyerHilbertConvolution_congr hs]

/-- Effectivity from the faithful reserve, on the original Meyer intersection pairing. -/
def meyerHilbertSourceCone : Set MeyerScalingCycle :=
  meyerScalingSurface.sourceCone meyerHilbertReserve

theorem meyer_defect_sq_le_hilbertReserve (x y : MeyerScalingCycle) :
    meyerScalingSurface.defect x y ^ 2 ≤ meyerHilbertReserve x * meyerHilbertReserve y := by
  rw [← meyerHilbertReserveBilinear_self, ← meyerHilbertReserveBilinear_self]
  apply meyerScalingSurface.defect_sq_le_of_quadratic_majorant
    meyerHilbertReserveBilinear meyerHilbertReserveBilinear_symm
  · intro z
    rw [meyerHilbertReserveBilinear_self]
    have h := meyerHilbertReserve_sub_defect z
    have hn := hsNormSq_nonneg (deningerMeyerHilbertConvolution z.2.2 -
      adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp z.2.2)))
    linarith only [h, hn]
  · intro z
    rw [meyerHilbertReserveBilinear_self]
    have h := meyerHilbertReserve_add_defect z
    have hn := hsNormSq_nonneg (deningerMeyerHilbertConvolution z.2.2 +
      adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp z.2.2)))
    linarith only [h, hn]

/-- Bézout follows from the admitted Hilbert–Schmidt reserve without a spectral sign premise. -/
theorem meyerHilbertSourceCone_bezout : meyerScalingSurface.BezoutAxiom meyerHilbertSourceCone :=
  (meyerScalingSurface.sourceCone_bezout_iff_defect_sq_le meyerHilbertReserve_nonneg
    reserve_neg reserve_fibre).mpr meyer_defect_sq_le_hilbertReserve

theorem meyerHilbertSourceCone_ample : meyerScalingSurface.AmpleAxiom meyerHilbertSourceCone := by
  apply (meyerScalingSurface.sourceCone_ample_iff_defect_radical reserve_fibre).mpr
  intro x hx y
  have hz : meyerHilbertReserve x = 0 := le_antisymm hx (meyerHilbertReserve_nonneg x)
  obtain ⟨f, hf⟩ := (meyerHilbertReserve_eq_zero_iff x).mp hz
  rw [meyerScalingSurface_defect, ← hf]
  exact meyerSourceTrace_boundary_left f _

/-- Every effective ample-zero cycle is genuinely principal, without assuming simplicity. -/
theorem meyerHilbertSourceCone_ample_zero_iff (x : MeyerScalingCycle) :
    (x ∈ meyerHilbertSourceCone ∧ meyerScalingSurface.pair x meyerScalingSurface.ample = 0) ↔
      ∃ f : DeningerMeyerCap, x = meyerPrincipalCycle f := by
  constructor
  · rintro ⟨hx, hdeg⟩
    rw [meyerHilbertSourceCone, PolarSurface.mem_sourceCone_iff] at hx
    rw [PolarSurface.pair_ample] at hdeg
    have hH : meyerScalingSurface.pair x meyerScalingSurface.H = 0 := by
      linarith only [hx.1, hx.2.1, hdeg]
    have hV : meyerScalingSurface.pair x meyerScalingSurface.V = 0 := by
      linarith only [hx.1, hx.2.1, hdeg]
    have hP : meyerHilbertReserve x = 0 := by
      have hp := hx.2.2
      rw [PolarSurface.polar_self, hH, hV, mul_zero] at hp
      exact le_antisymm hp (meyerHilbertReserve_nonneg x)
    obtain ⟨f, hf⟩ := (meyerHilbertReserve_eq_zero_iff x).mp hP
    refine ⟨f, ?_⟩
    rw [meyerScalingSurface_pair_H] at hH
    rw [meyerScalingSurface_pair_V] at hV
    apply Prod.ext
    · change x.1 = -meyerPoleA (deningerMeyerStrongLogSumLM f)
      rw [hf]
      unfold meyerDegreeV at hV
      linarith only [hV]
    · apply Prod.ext
      · change x.2.1 = -meyerPoleB (deningerMeyerStrongLogSumLM f)
        rw [hf]
        unfold meyerDegreeH at hH
        linarith only [hH]
      · exact hf.symm
  · rintro ⟨f, rfl⟩
    have hP : meyerHilbertReserve (meyerPrincipalCycle f) = 0 :=
      (meyerHilbertReserve_eq_zero_iff _).mpr ⟨f, rfl⟩
    constructor
    · rw [meyerHilbertSourceCone, PolarSurface.mem_sourceCone_iff, PolarSurface.polar_self,
        meyerScalingSurface_pair_H, meyerScalingSurface_pair_V,
        meyerPrincipalCycle_degreeH, meyerPrincipalCycle_degreeV, hP]
      norm_num
    · rw [PolarSurface.pair_ample, meyerScalingSurface_pair_H, meyerScalingSurface_pair_V,
        meyerPrincipalCycle_degreeH, meyerPrincipalCycle_degreeV, zero_add]

private theorem cone_eq_quadratic : meyerHilbertSourceCone = meyerScalingSurface.sourceCone
    (fun x => meyerHilbertReserveBilinear x x) := by
  unfold meyerHilbertSourceCone
  congr 1
  exact funext fun x => (meyerHilbertReserveBilinear_self x).symm

theorem meyerHilbertSourceCone_add_closed :
    ∀ x ∈ meyerHilbertSourceCone, ∀ y ∈ meyerHilbertSourceCone, x + y ∈ meyerHilbertSourceCone := by
  rw [cone_eq_quadratic]
  exact meyerScalingSurface.sourceCone_quadratic_add_closed meyerHilbertReserveBilinear
    meyerHilbertReserveBilinear_symm
    (fun x => by rw [meyerHilbertReserveBilinear_self]; exact meyerHilbertReserve_nonneg x)

theorem meyerHilbertSourceCone_smul {a : ℝ} (ha : 0 ≤ a) {x : MeyerScalingCycle}
    (hx : x ∈ meyerHilbertSourceCone) : a • x ∈ meyerHilbertSourceCone := by
  rw [cone_eq_quadratic] at hx ⊢
  exact meyerScalingSurface.smul_mem_sourceCone_quadratic meyerHilbertReserveBilinear ha hx

theorem zero_mem_meyerHilbertSourceCone : (0 : MeyerScalingCycle) ∈ meyerHilbertSourceCone := by
  rw [cone_eq_quadratic]
  exact meyerScalingSurface.zero_mem_sourceCone_quadratic meyerHilbertReserveBilinear

theorem meyerHilbertSourceCone_convex : Convex ℝ meyerHilbertSourceCone := by
  rw [cone_eq_quadratic]
  exact meyerScalingSurface.sourceCone_quadratic_convex meyerHilbertReserveBilinear
    meyerHilbertReserveBilinear_symm
    (fun x => by rw [meyerHilbertReserveBilinear_self]; exact meyerHilbertReserve_nonneg x)

/-- The effective cone is pointed modulo the genuine Poisson principal cycles. -/
theorem meyerHilbertSourceCone_pointed_mod_principal {x : MeyerScalingCycle}
    (hx : x ∈ meyerHilbertSourceCone) (hnx : -x ∈ meyerHilbertSourceCone) :
    ∃ f : DeningerMeyerCap, x = meyerPrincipalCycle f := by
  apply (meyerHilbertSourceCone_ample_zero_iff x).mp
  refine ⟨hx, ?_⟩
  rw [meyerHilbertSourceCone, PolarSurface.mem_sourceCone_iff] at hx hnx
  have hnH : 0 ≤ -meyerScalingSurface.pair x meyerScalingSurface.H := by
    calc
      0 ≤ meyerScalingSurface.pair (-x) meyerScalingSurface.H := hnx.1
      _ = _ := (meyerScalingSurface.pair.flip meyerScalingSurface.H).map_neg x
  have hnV : 0 ≤ -meyerScalingSurface.pair x meyerScalingSurface.V := by
    calc
      0 ≤ meyerScalingSurface.pair (-x) meyerScalingSurface.V := hnx.2.1
      _ = _ := (meyerScalingSurface.pair.flip meyerScalingSurface.V).map_neg x
  rw [PolarSurface.pair_ample]
  linarith only [hx.1, hx.2.1, hnH, hnV]

theorem meyerHilbertSourceCone_generating (x : MeyerScalingCycle) :
    ∃ y ∈ meyerHilbertSourceCone, ∃ z ∈ meyerHilbertSourceCone, x = y - z := by
  apply meyerScalingSurface.sourceCone_generating reserve_fibre ?_ x
  rw [← meyerHilbertReserveBilinear_self]
  simp only [map_zero, LinearMap.zero_apply, le_refl]

/-- RR for the faithful reserve is exactly compatibility of arithmetic sharp with Hilbert adjoint. -/
theorem meyerHilbertSourceCone_riemannRoch_iff_adjoint :
    meyerScalingSurface.RiemannRochAxiom meyerHilbertSourceCone ↔
      ∀ g : DeningerMeyerStrongLogTarget,
        deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
          adjoint (deningerMeyerHilbertConvolution g) := by
  rw [meyerHilbertSourceCone, meyerScalingSurface.sourceCone_riemannRoch_iff_le_defect
    meyerHilbertReserve_nonneg reserve_neg reserve_fibre]
  have he (x : MeyerScalingCycle) : meyerHilbertReserve x ≤ meyerScalingSurface.defect x x ↔
      deningerMeyerHilbertConvolution x.2.2 =
        adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp x.2.2)) := by
    rw [meyerScalingSurface_defect]
    exact half_hsNormSq_sum_le_re_trace_iff (meyerHilbertConvolution_isHilbertSchmidt _)
      (meyerHilbertConvolution_isHilbertSchmidt _)
  constructor
  · intro h g
    have hg := congrArg adjoint ((he (0, 0, g)).mp (h (0, 0, g)))
    rw [adjoint_adjoint] at hg
    exact hg.symm
  · intro h x
    apply (he x).mpr
    rw [h x.2.2, adjoint_adjoint]

/-- The exact RR boundary adds simplicity to the ordinary trace criticality condition. -/
theorem meyerHilbertSourceCone_riemannRoch_iff :
    meyerScalingSurface.RiemannRochAxiom meyerHilbertSourceCone ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 :=
  meyerHilbertSourceCone_riemannRoch_iff_adjoint.trans meyerHilbertConvolution_sharp_eq_adjoint_iff

/-- A linear degree represents the faithful reserve exactly at simple criticality. -/
theorem exists_meyerHilbertReserve_linear_degree_iff :
    (∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget,
        meyerHilbertReserve (0, 0, g) =
          (d (Submodule.Quotient.mk
            (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · rintro ⟨d, hd⟩
    apply exists_faithful_positive_meyer_degree_iff.mp
    refine ⟨d, fun g hg => ?_⟩
    rw [← hd g]
    exact lt_of_le_of_ne (meyerHilbertReserve_nonneg _) (fun he =>
      hg ((meyerHilbertReserve_eq_zero_iff (0, 0, g)).mp he.symm))
  · intro h
    refine ⟨meyerCohomologyTraceDegree, fun g => ?_⟩
    rw [← meyerSourceTrace_eq_degree_product]
    have he := (meyerScalingSurface.sourceCone_riemannRoch_and_bezout_iff
      meyerHilbertReserve_nonneg reserve_neg reserve_fibre).mp
        ⟨meyerHilbertSourceCone_riemannRoch_iff.mpr h, meyerHilbertSourceCone_bezout⟩ (0, 0, g)
    simpa only [meyerScalingSurface_defect] using he

/-- For the faithful reserve, linear sharp-square representation and RR are equivalent. -/
theorem meyerHilbertSourceCone_riemannRoch_iff_linear_degree :
    meyerScalingSurface.RiemannRochAxiom meyerHilbertSourceCone ↔
      ∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
        ∀ g : DeningerMeyerStrongLogTarget,
          meyerHilbertReserve (0, 0, g) =
            (d (Submodule.Quotient.mk
              (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re :=
  meyerHilbertSourceCone_riemannRoch_iff.trans exists_meyerHilbertReserve_linear_degree_iff.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_sub_defect
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_add_defect
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_eq_zero_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertReserve_congr
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_ample_zero_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_convex
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_generating
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_pointed_mod_principal
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_riemannRoch_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_meyerHilbertReserve_linear_degree_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertSourceCone_riemannRoch_iff_linear_degree
