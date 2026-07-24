import GaloisForLFunctions.RHTower.ThetaFourierLaplaceLocalKummerCollision
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.XiZerosInfinite
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# RH supplies the differentiated Xi and theta Kummer roots

Under RH, the reflection-closed finite products for the canonical Xi product are complexifications
of split real polynomials.  Gauss--Lucas therefore puts every zero of their derivatives on the real
axis.  Locally uniform convergence of the differentiated products transfers this closed zero-locus
constraint to `deriv xiCanonicalProduct`, hence to `deriv XiC`.

Consequently `deriv xi` is zero-free on the right half-plane, while the differentiated
theta-cusp Fourier--Laplace source is zero-free on its right-zero band.  The existing simply
connected Kummer-branch theorem then supplies roots of every positive degree.  This discharges both
differentiated-source root interfaces under RH and turns each common-root collision into an exact
RH characterization.
-/

open Complex Filter Set Topology Polynomial

namespace RHTower

noncomputable section

open scoped Classical

private noncomputable def xiDerivativeWitnessSupport : XiDivisorSupport := by
  letI : Infinite XiDivisorSupport :=
    Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  exact Classical.choice inferInstance

private noncomputable def xiDerivativeWitnessZeroCopy : XiZeroCopy := by
  let rho : XiDivisorSupport := xiDerivativeWitnessSupport
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  exact ⟨rho, ⟨0, hn⟩⟩

/-- A zero of the derivative of a positive-degree split real polynomial remains real after
complexification. -/
theorem derivative_map_real_split_zero_im_eq_zero
    {p : Polynomial ℝ} (hsplit : p.Splits) (hpdeg : 0 < p.degree)
    {z : ℂ} (hz : (p.map Complex.ofRealHom).derivative.eval z = 0) :
    z.im = 0 := by
  let P : Polynomial ℂ := p.map Complex.ofRealHom
  have hPdeg : 0 < P.degree := by
    change 0 < (p.map Complex.ofRealHom).degree
    rw [Polynomial.degree_map_eq_of_injective
      Complex.ofRealHom.injective p]
    exact hpdeg
  have hPderiv : P.derivative ≠ 0 := by
    intro hzero
    have hnat := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hzero
    have hnatpos : 0 < P.natDegree :=
      Polynomial.natDegree_pos_iff_degree_pos.mpr hPdeg
    omega
  have hzroot : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hPderiv, hz⟩
  have hzHull :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hPdeg hzroot
  have hrootReal : P.rootSet ℂ ⊆ {w : ℂ | w.im = 0} := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    have hwroot : w ∈ P.roots :=
      (Polynomial.mem_roots hw.1).mpr hw.2
    have hroots := hsplit.roots_map_of_injective
      Complex.ofRealHom.injective
    change P.roots = _ at hroots
    rw [hroots] at hwroot
    obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp hwroot
    simp
  have hconvex : Convex ℝ {w : ℂ | w.im = 0} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [hx, hy]
  exact convexHull_min hrootReal hconvex hzHull

/-- Under RH, every zero of a nonempty reflection-closed finite-product derivative is real. -/
theorem xiPairedE1Product_deriv_zero_im_eq_zero_of_rh
    (hRH : RiemannHypothesis) (s : Finset XiDivisorSupport)
    (q : XiZeroCopy) (hq : q ∈ xiPairedCopyFinset s)
    {z : ℂ} (hz : deriv (xiPairedE1Product s) z = 0) :
    z.im = 0 := by
  let p : Polynomial ℝ := xiPairedPolynomial s
  let P : Polynomial ℂ := p.map Complex.ofRealHom
  have hP0 : P.eval 0 = 1 := by
    have h := xiPairedPolynomial_map_eval_eq_product_of_rh hRH s 0
    simpa only [P, p, xiPairedE1Product, zero_div,
      weierstrassE1_zero, Finset.prod_const_one] using h
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hP0
    norm_num at hP0
  have hprodZero : xiPairedE1Product s (xiSpectralPoint q) = 0 := by
    rw [xiPairedE1Product]
    apply Finset.prod_eq_zero hq
    rw [div_self (xiSpectralPoint_ne_zero q), weierstrassE1_one]
  have hroot : P.IsRoot (xiSpectralPoint q) := by
    rw [Polynomial.IsRoot]
    change P.eval (xiSpectralPoint q) = 0
    rw [show P.eval (xiSpectralPoint q) =
      xiPairedE1Product s (xiSpectralPoint q) by
        exact xiPairedPolynomial_map_eval_eq_product_of_rh hRH s _]
    exact hprodZero
  have hPdeg : 0 < P.degree :=
    Polynomial.degree_pos_of_root hPne hroot
  have hpdeg : 0 < p.degree := by
    rw [← Polynomial.degree_map_eq_of_injective
      Complex.ofRealHom.injective p]
    exact hPdeg
  have hderivEq :
      P.derivative.eval z = deriv (xiPairedE1Product s) z := by
    have hfun : (fun w : ℂ => P.eval w) = xiPairedE1Product s := by
      funext w
      exact xiPairedPolynomial_map_eval_eq_product_of_rh hRH s w
    have h := congrArg (fun f : ℂ → ℂ => deriv f z) hfun
    rw [← (P.hasDerivAt z).deriv]
    exact h
  apply derivative_map_real_split_zero_im_eq_zero
    (xiPairedPolynomial_splits s) hpdeg
  change P.derivative.eval z = 0
  rw [hderivEq, hz]

/-- The canonical Xi product is nonconstant, so its derivative is nonzero somewhere. -/
theorem exists_xiCanonicalProduct_deriv_ne_zero :
    ∃ a : ℂ, deriv xiCanonicalProduct a ≠ 0 := by
  by_contra hall
  have hzero : ∀ a : ℂ, deriv xiCanonicalProduct a = 0 := by
    intro a
    exact not_ne_iff.mp ((not_exists.mp hall) a)
  let q : XiZeroCopy := xiDerivativeWitnessZeroCopy
  have hconst : xiCanonicalProduct (xiSpectralPoint q) =
      xiCanonicalProduct 0 :=
    is_const_of_deriv_eq_zero
      (analyticOnNhd_univ_iff_differentiable.mp xiCanonicalProduct_analytic)
      hzero _ _
  rw [xiCanonicalProduct_eq_zero, xiCanonicalProduct_zero] at hconst
  exact zero_ne_one hconst

/-- Under RH, the derivative of the canonical Xi product has no nonreal zero. -/
theorem deriv_xiCanonicalProduct_zero_im_eq_zero_of_rh
    (hRH : RiemannHypothesis) {z : ℂ}
    (hz : deriv xiCanonicalProduct z = 0) :
    z.im = 0 := by
  let Fn : ℕ → ℂ → ℂ := fun n =>
    deriv (xiPairedE1Product (xiSupportExhaustionFinset n))
  have hconv : TendstoLocallyUniformly Fn
      (deriv xiCanonicalProduct) atTop := by
    have hbase : TendstoLocallyUniformly
        (deriv ∘ xiPairedE1Product)
        (deriv xiCanonicalProduct) atTop :=
      tendstoLocallyUniformlyOn_univ.mp
        xiPairedE1Product_deriv_tendstoLocallyUniformlyOn
    intro u hu x
    obtain ⟨t, ht, hevent⟩ := hbase u hu x
    refine ⟨t, ht, ?_⟩
    simpa only [Fn, Function.comp_apply] using
      xiSupportExhaustionFinset_tendsto_atTop.eventually hevent
  have hFn : ∀ᶠ n : ℕ in atTop, Differentiable ℂ (Fn n) := by
    apply Filter.Eventually.of_forall
    intro n w
    exact (((xiPairedE1Product_differentiable
      (xiSupportExhaustionFinset n)).analyticAt w).deriv).differentiableAt
  let q : XiZeroCopy := xiDerivativeWitnessZeroCopy
  have hqevent : ∀ᶠ n : ℕ in atTop,
      q ∈ xiPairedCopyFinset (xiSupportExhaustionFinset n) := by
    have hcomp : Tendsto
        (xiPairedCopyFinset ∘ xiSupportExhaustionFinset)
        atTop atTop :=
      xiPairedCopyFinset_tendsto_atTop.comp
        xiSupportExhaustionFinset_tendsto_atTop
    have hev : ∀ᶠ s : Finset XiZeroCopy in atTop, q ∈ s := by
      filter_upwards [eventually_ge_atTop ({q} : Finset XiZeroCopy)] with s hs
      exact hs (by simp)
    simpa only [Function.comp_apply] using hcomp.eventually hev
  have hzeroReal : ∀ᶠ n : ℕ in atTop, ∀ w, Fn n w = 0 →
      w.im = 0 := by
    filter_upwards [hqevent] with n hqn w hw
    exact xiPairedE1Product_deriv_zero_im_eq_zero_of_rh hRH
      (xiSupportExhaustionFinset n) q hqn hw
  obtain ⟨a, ha⟩ := exists_xiCanonicalProduct_deriv_ne_zero
  exact zero_mem_closed_of_tendstoLocallyUniformly
    hconv xiCanonicalProduct_analytic.deriv hFn
    (isClosed_eq Complex.continuous_im continuous_const)
    hzeroReal ha hz

/-- Under RH, every zero of the differentiated centered Xi function is real. -/
theorem deriv_XiC_zero_im_eq_zero_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : deriv XiC z = 0) :
    z.im = 0 := by
  apply deriv_xiCanonicalProduct_zero_im_eq_zero_of_rh hRH
  rw [XiC_deriv_eq_constant_mul_canonicalProduct] at hz
  exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne

/-- Under RH, the differentiated Xi source is zero-free on the open right half-plane. -/
theorem deriv_xi_ne_zero_rightHalf_of_rh
    (hRH : RiemannHypothesis) {s : ℂ} (hs : s ∈ rightHalf) :
    deriv xi s ≠ 0 := by
  intro hzero
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by
      rw [neg_mul, I_mul_I]
      ring
    rw [hI, mul_one]
    ring
  have hXiC : deriv XiC z = 0 := by
    rw [deriv_XiC_eq_deriv_xi_mul_I, hcoord, hzero, zero_mul]
  have him := deriv_XiC_zero_im_eq_zero_of_rh hRH hXiC
  have hzIm : z.im = 1 / 2 - s.re := by
    simp [z]
  have hsre : 1 / 2 < s.re := mem_rightHalf.mp hs
  linarith

/-- RH supplies common analytic Kummer roots of Xi and its derivative on the right half-plane
for every positive degree. -/
theorem xiDerivativeCommonKummerRootRightHalf_of_rh
    {d : ℕ} (hd : d ≠ 0) (hRH : RiemannHypothesis) :
    XiDerivativeCommonKummerRootRightHalf d := by
  have hsc : IsSimplyConnected rightHalf :=
    isSimplyConnected_of_convex convex_rightHalf
      ⟨1, by rw [mem_rightHalf]; norm_num⟩
  have hxi0 : ∀ s ∈ rightHalf, xi s ≠ 0 :=
    rh_iff_xi_ne_zero_right.mp hRH
  obtain ⟨g, hg, _hgne, hgpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_rightHalf hsc
      (xi_analyticOnNhd_univ.mono (Set.subset_univ _))
      hxi0 hd
  obtain ⟨h, hh, _hhne, hhpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_rightHalf hsc
      ((xi_analyticOnNhd_univ.deriv).mono (Set.subset_univ _))
      (fun s hs => deriv_xi_ne_zero_rightHalf_of_rh hRH hs)
      hd
  exact ⟨g, h, hg, hh, hgpow, hhpow⟩

/-- For every nontrivial degree, the common Xi/derivative Kummer-root interface is exactly RH. -/
theorem xiDerivativeCommonKummerRootRightHalf_iff_rh
    {d : ℕ} (hd : 1 < d) :
    XiDerivativeCommonKummerRootRightHalf d ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf hd,
    xiDerivativeCommonKummerRootRightHalf_of_rh
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd))⟩

/-- RH discharges the differentiated-Xi square-root interface. -/
theorem xiDerivativeSquareRootRightHalf_of_rh
    (hRH : RiemannHypothesis) :
    XiDerivativeSquareRootRightHalf := by
  obtain ⟨_g, h, _hg, hh, _hgpow, hhpow⟩ :=
    xiDerivativeCommonKummerRootRightHalf_of_rh
      (d := 2) (by norm_num) hRH
  exact ⟨h, hh, hhpow⟩

/-- The first multiplicity rung together with the formerly conditional derivative square root is
an exact RH characterization. -/
theorem rhLadder_one_and_xiDerivativeSquareRootRightHalf_iff_rh :
    RHLadder 1 ∧ XiDerivativeSquareRootRightHalf ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hroot⟩
    exact riemannHypothesis_of_rhLadder_one_of_xiDerivativeSquareRootRightHalf
      hladder hroot
  · intro hRH
    exact ⟨(rh_iff_forall_ladder.mp hRH) 1,
      xiDerivativeSquareRootRightHalf_of_rh hRH⟩

/-- The theta source right-zero band is convex. -/
theorem convex_thetaCuspFourierLaplaceRightZeroBand :
    Convex ℝ thetaCuspFourierLaplaceRightZeroBand := by
  rw [thetaCuspFourierLaplaceRightZeroBand]
  exact (convex_halfSpace_im_gt (-(1 : ℝ) / 2)).inter
    (convex_halfSpace_im_lt 0)

private theorem rightZeroBand_subset_fourierLaplaceStrip
    {w : ℂ} (hw : w ∈ thetaCuspFourierLaplaceRightZeroBand) :
    w ∈ thetaCuspFourierLaplaceStrip := by
  rw [thetaCuspFourierLaplaceRightZeroBand, Set.mem_setOf_eq] at hw
  rw [thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq]
  constructor <;> linarith [hw.1, hw.2]

/-- Under RH, the theta-cusp Fourier--Laplace source is zero-free on its right-zero band. -/
theorem thetaCuspFourierLaplace_ne_zero_rightZeroBand_of_rh
    (hRH : RiemannHypothesis) {w : ℂ}
    (hw : w ∈ thetaCuspFourierLaplaceRightZeroBand) :
    thetaCuspFourierLaplace w ≠ 0 := by
  rw [thetaCuspFourierLaplace_eq_XiC_on_strip
    (rightZeroBand_subset_fourierLaplaceStrip hw), XiC]
  apply rh_iff_xi_ne_zero_right.mp hRH
  rw [mem_rightHalf]
  simp
  linarith [hw.2]

/-- Under RH, the differentiated theta source is zero-free on its right-zero band. -/
theorem deriv_thetaCuspFourierLaplace_ne_zero_rightZeroBand_of_rh
    (hRH : RiemannHypothesis) {w : ℂ}
    (hw : w ∈ thetaCuspFourierLaplaceRightZeroBand) :
    deriv thetaCuspFourierLaplace w ≠ 0 := by
  intro hzero
  have hXiC : deriv XiC w = 0 := by
    rw [← deriv_thetaCuspFourierLaplace_eq_deriv_XiC
      (rightZeroBand_subset_fourierLaplaceStrip hw)]
    exact hzero
  have him := deriv_XiC_zero_im_eq_zero_of_rh hRH hXiC
  exact (ne_of_lt hw.2) him

/-- RH supplies common analytic Kummer roots of the theta source and its derivative on the
right-zero band for every positive degree. -/
theorem thetaCuspDerivativeCommonKummerRootRightZeroBand_of_rh
    {d : ℕ} (hd : d ≠ 0) (hRH : RiemannHypothesis) :
    ThetaCuspDerivativeCommonKummerRootRightZeroBand d := by
  have hnonempty : thetaCuspFourierLaplaceRightZeroBand.Nonempty := by
    refine ⟨-(I / 4), ?_⟩
    rw [thetaCuspFourierLaplaceRightZeroBand, Set.mem_setOf_eq]
    norm_num
  have hsc : IsSimplyConnected thetaCuspFourierLaplaceRightZeroBand :=
    isSimplyConnected_of_convex
      convex_thetaCuspFourierLaplaceRightZeroBand hnonempty
  have hanalytic :=
    analyticOnNhd_thetaCuspFourierLaplace.mono
      (fun _ hw => rightZeroBand_subset_fourierLaplaceStrip hw)
  obtain ⟨g, hg, _hgne, hgpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_thetaCuspFourierLaplaceRightZeroBand hsc
      hanalytic
      (fun w hw =>
        thetaCuspFourierLaplace_ne_zero_rightZeroBand_of_rh hRH hw)
      hd
  obtain ⟨h, hh, _hhne, hhpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_thetaCuspFourierLaplaceRightZeroBand hsc
      hanalytic.deriv
      (fun w hw =>
        deriv_thetaCuspFourierLaplace_ne_zero_rightZeroBand_of_rh
          hRH hw)
      hd
  exact ⟨g, h, hg, hh, hgpow, hhpow⟩

/-- For every nontrivial degree, the common theta-source/derivative Kummer-root interface is
exactly RH. -/
theorem thetaCuspDerivativeCommonKummerRootRightZeroBand_iff_rh
    {d : ℕ} (hd : 1 < d) :
    ThetaCuspDerivativeCommonKummerRootRightZeroBand d ↔
      RiemannHypothesis := by
  exact
    ⟨riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand hd,
      thetaCuspDerivativeCommonKummerRootRightZeroBand_of_rh
        (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd))⟩

/-- RH discharges the differentiated-theta square-root interface on the right-zero band. -/
theorem thetaCuspDerivativeSquareRootRightZeroBand_of_rh
    (hRH : RiemannHypothesis) :
    ThetaCuspDerivativeSquareRootRightZeroBand := by
  obtain ⟨_g, h, _hg, hh, _hgpow, hhpow⟩ :=
    thetaCuspDerivativeCommonKummerRootRightZeroBand_of_rh
      (d := 2) (by norm_num) hRH
  exact ⟨h, hh, hhpow⟩

/-- The first multiplicity rung together with the formerly conditional theta-derivative square
root is an exact RH characterization. -/
theorem rhLadder_one_and_thetaCuspDerivativeSquareRootRightZeroBand_iff_rh :
    RHLadder 1 ∧ ThetaCuspDerivativeSquareRootRightZeroBand ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hroot⟩
    exact
      riemannHypothesis_of_rhLadder_one_of_thetaCuspDerivativeSquareRootRightZeroBand
        hladder hroot
  · intro hRH
    exact ⟨(rh_iff_forall_ladder.mp hRH) 1,
      thetaCuspDerivativeSquareRootRightZeroBand_of_rh hRH⟩

end

end RHTower
