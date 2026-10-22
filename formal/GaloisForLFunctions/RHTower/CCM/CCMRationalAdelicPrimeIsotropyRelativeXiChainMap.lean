import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.Deninger.DeningerThreeTermOperations
import GaloisForLFunctions.RHTower.MobiusThetaSourceDaggerMinimalBoundaryLaw
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldResolvedXiLandingAnnihilation

/-!
# Prime-isotropy relative complex and strict Xi comparison

The previously used ordinary-prime tensor has product trace one, but was not proved to be a
Hochschild cycle.  This file replaces it by the low-degree relative complex forced by the actual
zero-adele fixed point.

For one ordinary prime `p`, the genuine adelic Bruhat--Schwartz core carries inverse scaling
`alpha_p` and zero evaluation `epsilon_0`.  The comparison from

`A --(alpha_p - 1)--> A`

to the zero-isotropy complex `C --0--> C` has the rotated mapping-cone differential

`D0 x = (alpha_p x - x, epsilon_0 x)`, `D1 (y,z) = epsilon_0 y`.

Its prime-isotropy cocycle `(0,1)` is retained.  The key point is analytic rather than
definitional: an adelic Schwartz tensor fixed by a nontrivial positive prime scaling has zero value
at the zero adele.  The proof reduces by finite-zero partial evaluation to decay and continuity of
an archimedean Schwartz function.

The second half gives a strict three-term comparison to the existing divisor-resolved Route-R Xi
complex.  The retained prime class lands on the nonzero prime-localized boundary of the actual
leading Xi conormal, and the next resolved differential kills it unconditionally.  This does not
assert scalar Cartier descent: the resolved target is flat for every centered rate, whereas its
scalar quotient remains RH-sharp.
-/

open Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

/-! ## Finite-zero partial evaluation and prime-scaling rigidity -/

/-- Bilinear finite-zero evaluation, retaining the full archimedean Schwartz factor. -/
def ccmRationalAdelicFiniteZeroPartialEvalBilinear :
    Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] Arch where
  toFun f :=
    { toFun := fun phi => phi.1 0 • f
      map_add' := by
        intro phi psi
        ext x
        simp [add_smul]
      map_smul' := by
        intro z phi
        ext x
        change (z * phi.1 0) * f x = z * (phi.1 0 * f x)
        ring }
  map_add' := by
    intro f g
    ext phi x
    simp [smul_add]
  map_smul' := by
    intro z f
    ext phi x
    change phi.1 0 * (z * f x) = z * (phi.1 0 * f x)
    ring

/-- Evaluate the finite-adele factor of an algebraic adelic tensor at zero. -/
def ccmRationalAdelicFiniteZeroPartialEval : Core →ₗ[ℂ] Arch :=
  TensorProduct.lift ccmRationalAdelicFiniteZeroPartialEvalBilinear

@[simp]
theorem ccmRationalAdelicFiniteZeroPartialEval_tmul
    (f : Arch) (phi : FinBruhat) :
    ccmRationalAdelicFiniteZeroPartialEval (f ⊗ₜ[ℂ] phi) =
      phi.1 0 • f :=
  rfl

/-- Partial zero evaluation intertwines diagonal adelic scaling with archimedean scaling. -/
theorem ccmRationalAdelicFiniteZeroPartialEval_scaling
    (k : CCMRationalAdelicScaling) (x : Core) :
    ccmRationalAdelicFiniteZeroPartialEval (k • x) =
      ccmRationalArchimedeanScaling k
        (ccmRationalAdelicFiniteZeroPartialEval x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [ccmRationalAdelicFiniteZeroPartialEval]
  | tmul f phi =>
      ext t
      simp [ccmRationalAdelicFiniteZeroPartialEval_tmul,
        ccmRationalAdelicScaling_smul_tmul,
        ccmRationalFiniteBruhatScaling_apply,
        ccmRationalArchimedeanScaling_apply]
  | add x y hx hy => simp [hx, hy]

/-- Full zero-adele evaluation is archimedean evaluation at zero after partial evaluation. -/
theorem ccmRationalAdelicFiniteZeroPartialEval_zero
    (x : Core) :
    ccmRationalAdelicFiniteZeroPartialEval x 0 =
      ccmRationalAdelicBruhatZeroEval x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [ccmRationalAdelicFiniteZeroPartialEval]
  | tmul f phi =>
      simp [ccmRationalAdelicFiniteZeroPartialEval_tmul,
        ccmRationalAdelicBruhatZeroEval_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- An archimedean Schwartz function fixed by positive ordinary-prime scaling vanishes at zero. -/
theorem ccmRationalArchimedeanPrimeScaling_fixed_zero
    (p : Nat.Primes) (f : Arch)
    (hfix : ccmRationalArchimedeanScaling
      (ccmRationalAdelicPrimeScaling p) f = f) :
    f 0 = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hscale (x : ℝ) : f ((p : ℝ)⁻¹ * x) = f x := by
    have h := congrArg (fun g : Arch => g x) hfix
    simpa [ccmRationalArchimedeanScaling_apply,
      ccmRationalAdelicPrimeScaling] using h
  have hpow_pos (n : ℕ) : f ((p : ℝ) ^ n) = f 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hscale ((p : ℝ) ^ (n + 1))
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp1)
        have harg :
            (p : ℝ)⁻¹ * (p : ℝ) ^ (n + 1) = (p : ℝ) ^ n := by
          rw [pow_succ]
          field_simp
        rw [harg] at hs
        exact hs.symm.trans ih
  have hpow_cocompact :
      Tendsto (fun n : ℕ => (p : ℝ) ^ n) atTop (cocompact ℝ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    simpa [Real.dist_eq] using tendsto_pow_atTop_atTop_of_one_lt hp1
  have hto0 : Tendsto (fun n : ℕ => f ((p : ℝ) ^ n)) atTop (nhds 0) :=
    (SchwartzMap.tendsto_cocompact f).comp hpow_cocompact
  have hconst : Tendsto (fun _ : ℕ => f 1) atTop (nhds (f 1)) :=
    tendsto_const_nhds
  have hf1 : f 1 = 0 :=
    tendsto_nhds_unique hconst (by simpa [hpow_pos] using hto0)
  have hpow_neg (n : ℕ) : f (((p : ℝ)⁻¹) ^ n) = f 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_comm]
        exact (hscale (((p : ℝ)⁻¹) ^ n)).trans ih
  have hinv_lt : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_trans (by norm_num) hp1)]
    exact (inv_lt_one₀ (lt_trans (by norm_num) hp1)).2 hp1
  have hpow_zero :
      Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv_lt
  have htozeroeval :
      Tendsto (fun n : ℕ => f (((p : ℝ)⁻¹) ^ n)) atTop (nhds (f 0)) :=
    f.continuous.continuousAt.tendsto.comp hpow_zero
  have hconst0 : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique htozeroeval
  convert hconst0 using 1
  funext n
  rw [hpow_neg, hf1]

/-- Every actual adelic tensor fixed by ordinary-prime scaling has zero zero-adele value. -/
theorem ccmRationalAdelicPrimeScaling_fixed_zeroEval
    (p : Nat.Primes) (x : Core)
    (hfix : ccmRationalAdelicPrimeScaling p • x = x) :
    ccmRationalAdelicBruhatZeroEval x = 0 := by
  have hpartial := congrArg ccmRationalAdelicFiniteZeroPartialEval hfix
  rw [ccmRationalAdelicFiniteZeroPartialEval_scaling] at hpartial
  have hzero := ccmRationalArchimedeanPrimeScaling_fixed_zero p
    (ccmRationalAdelicFiniteZeroPartialEval x) hpartial
  rw [ccmRationalAdelicFiniteZeroPartialEval_zero] at hzero
  exact hzero

/-! ## Genuine relative prime-isotropy complex -/

/-- Degree-one term of the rotated zero-isotropy mapping cone. -/
abbrev CCMRationalAdelicPrimeRelativeOne := Core × ℂ

/-- First relative differential: prime orbit difference together with fixed-point evaluation. -/
def ccmRationalAdelicPrimeRelativeD0
    (p : Nat.Primes) :
    Core →ₗ[ℂ] CCMRationalAdelicPrimeRelativeOne where
  toFun x :=
    (ccmRationalAdelicPrimeScaling p • x - x,
      ccmRationalAdelicBruhatZeroEval x)
  map_add' x y := by
    ext
    · change ccmRationalAdelicBruhatScaling
          (ccmRationalAdelicPrimeScaling p) (x + y) - (x + y) =
        (ccmRationalAdelicBruhatScaling
            (ccmRationalAdelicPrimeScaling p) x - x) +
          (ccmRationalAdelicBruhatScaling
            (ccmRationalAdelicPrimeScaling p) y - y)
      rw [map_add]
      abel
    · exact map_add ccmRationalAdelicBruhatZeroEval x y
  map_smul' c x := by
    ext
    · change ccmRationalAdelicBruhatScaling
          (ccmRationalAdelicPrimeScaling p) (c • x) - c • x =
        c • (ccmRationalAdelicBruhatScaling
          (ccmRationalAdelicPrimeScaling p) x - x)
      rw [map_smul]
      module
    · exact map_smul ccmRationalAdelicBruhatZeroEval c x

/-- Second relative differential: fixed-point evaluation of the orbit-difference coordinate. -/
def ccmRationalAdelicPrimeRelativeD1 :
    CCMRationalAdelicPrimeRelativeOne →ₗ[ℂ] ℂ where
  toFun x := ccmRationalAdelicBruhatZeroEval x.1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Fixed-point invariance makes the relative differential square to zero unconditionally. -/
theorem ccmRationalAdelicPrimeRelativeD1_comp_D0
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeD1.comp
      (ccmRationalAdelicPrimeRelativeD0 p) = 0 := by
  apply LinearMap.ext
  intro x
  simp [ccmRationalAdelicPrimeRelativeD1,
    ccmRationalAdelicPrimeRelativeD0,
    ccmRationalAdelicBruhatZeroEval_smul]

/-- Three-term relative complex of the actual prime-scaled adelic core and its zero isotropy. -/
def ccmRationalAdelicPrimeRelativeComplex
    (p : Nat.Primes) :
    DeningerArithmeticThreeTermComplex ℂ Core
      CCMRationalAdelicPrimeRelativeOne ℂ where
  d0 := ccmRationalAdelicPrimeRelativeD0 p
  d1 := ccmRationalAdelicPrimeRelativeD1
  d1_comp_d0 := ccmRationalAdelicPrimeRelativeD1_comp_D0 p

/-- Canonical ordinary-prime isotropy cocycle `(0,1)`. -/
def ccmRationalAdelicPrimeRelativeCocycle
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).cycles1 :=
  ⟨(0, 1), by
    simp [DeningerArithmeticThreeTermComplex.cycles1,
      ccmRationalAdelicPrimeRelativeComplex,
      ccmRationalAdelicPrimeRelativeD1]⟩

/-- Ordinary-prime class in the first cohomology of the relative zero-isotropy complex. -/
def ccmRationalAdelicPrimeRelativeClass
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 :=
  Submodule.Quotient.mk (ccmRationalAdelicPrimeRelativeCocycle p)

/-- The ordinary-prime class is retained: no fixed adelic Schwartz tensor can bound it. -/
theorem ccmRationalAdelicPrimeRelativeClass_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeClass p ≠ 0 := by
  intro hzero
  have hboundary :=
    ((ccmRationalAdelicPrimeRelativeComplex p).H1_mk_eq_zero_iff
      (ccmRationalAdelicPrimeRelativeCocycle p)).1 hzero
  rcases hboundary with ⟨x, hx⟩
  have hfirst := congrArg Prod.fst hx
  have hsecond := congrArg Prod.snd hx
  change ccmRationalAdelicPrimeScaling p • x - x = 0 at hfirst
  change ccmRationalAdelicBruhatZeroEval x = 1 at hsecond
  have hfix : ccmRationalAdelicPrimeScaling p • x = x :=
    sub_eq_zero.mp hfirst
  have heval := ccmRationalAdelicPrimeScaling_fixed_zeroEval p x hfix
  rw [hsecond] at heval
  exact one_ne_zero heval

/-! ## Strict comparison with the resolved actual-Xi complex -/

/-- The resolved Route-R differentials, packaged as a genuine three-term cochain complex. -/
def primeDepthBVWoldXiResolvedThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ
      PrimeDepthBVWoldXiResolvedZeroCochain
      PrimeDepthBVWoldXiResolvedOneCochain
      PrimeDepthBVWoldXiResolvedTwoCochain where
  d0 := primeDepthBVWoldXiResolvedCovariantD0
  d1 := primeDepthBVWoldXiResolvedCovariantD1
  d1_comp_d0 := by
    apply LinearMap.ext
    intro f
    funext rho i j k
    exact primeDepthBVWoldResolvedCovariantD1_comp_D0_apply _ _ _ _ _

/-- Actual leading Xi conormal, restricted to all depths over one retained ordinary prime. -/
def primeDepthBVWoldXiPrimeLocalizedLeadingConormal
    (p : Nat.Primes) : PrimeDepthBVWoldXiResolvedZeroCochain :=
  fun rho i =>
    if i.1 = p then
      (0, iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))
    else 0

/-- Degree-zero component of the relative source-to-Xi comparison. -/
def ccmRationalAdelicPrimeRelativeXiComparison0
    (p : Nat.Primes) :
    Core →ₗ[ℂ] PrimeDepthBVWoldXiResolvedZeroCochain where
  toFun x := ccmRationalAdelicBruhatZeroEval x •
    primeDepthBVWoldXiPrimeLocalizedLeadingConormal p
  map_add' x y := by simp [add_smul]
  map_smul' c x := by
    rw [map_smul, smul_eq_mul, smul_smul]
    simp only [RingHom.id_apply]

/-- Degree-one comparison reads the relative isotropy coordinate before taking the Xi boundary. -/
def ccmRationalAdelicPrimeRelativeXiComparison1
    (p : Nat.Primes) :
    CCMRationalAdelicPrimeRelativeOne →ₗ[ℂ]
      PrimeDepthBVWoldXiResolvedOneCochain where
  toFun x := x.2 • primeDepthBVWoldXiResolvedCovariantD0
    (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [smul_smul]

/-- The relative source has no further Xi output after the resolved boundary is formed. -/
def ccmRationalAdelicPrimeRelativeXiComparison2 :
    ℂ →ₗ[ℂ] PrimeDepthBVWoldXiResolvedTwoCochain :=
  0

/-- First strict chain-map square. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_commutes_d0
    (p : Nat.Primes) :
    primeDepthBVWoldXiResolvedCovariantD0.comp
        (ccmRationalAdelicPrimeRelativeXiComparison0 p) =
      (ccmRationalAdelicPrimeRelativeXiComparison1 p).comp
        (ccmRationalAdelicPrimeRelativeD0 p) := by
  apply LinearMap.ext
  intro x
  simp [ccmRationalAdelicPrimeRelativeXiComparison0,
    ccmRationalAdelicPrimeRelativeXiComparison1,
    ccmRationalAdelicPrimeRelativeD0]

/-- Second strict chain-map square; resolved frame flatness supplies the annihilation. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_commutes_d1
    (p : Nat.Primes) :
    primeDepthBVWoldXiResolvedCovariantD1.comp
        (ccmRationalAdelicPrimeRelativeXiComparison1 p) =
      ccmRationalAdelicPrimeRelativeXiComparison2.comp
        ccmRationalAdelicPrimeRelativeD1 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,
    ccmRationalAdelicPrimeRelativeXiComparison1,
    ccmRationalAdelicPrimeRelativeXiComparison2,
    LinearMap.zero_apply]
  change primeDepthBVWoldXiResolvedCovariantD1
      (x.2 • primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)) = 0
  rw [map_smul]
  have hz : primeDepthBVWoldXiResolvedCovariantD1
      (primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)) = 0 := by
    funext rho i j k
    exact primeDepthBVWoldResolvedCovariantD1_comp_D0_apply _ _ _ _ _
  rw [hz, smul_zero]

/-- Strict three-term source-to-Xi chain map. -/
def ccmRationalAdelicPrimeRelativeXiChainMap
    (p : Nat.Primes) :
    DeningerThreeTermHom
      (ccmRationalAdelicPrimeRelativeComplex p)
      primeDepthBVWoldXiResolvedThreeTermComplex where
  f0 := ccmRationalAdelicPrimeRelativeXiComparison0 p
  f1 := ccmRationalAdelicPrimeRelativeXiComparison1 p
  f2 := ccmRationalAdelicPrimeRelativeXiComparison2
  comm0 := ccmRationalAdelicPrimeRelativeXiComparison_commutes_d0 p
  comm1 := ccmRationalAdelicPrimeRelativeXiComparison_commutes_d1 p

/-- The retained ordinary-prime cocycle lands on the boundary of the localized actual Xi conormal. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_class_landing
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeXiComparison1 p
        (ccmRationalAdelicPrimeRelativeCocycle p) =
      primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) := by
  simp [ccmRationalAdelicPrimeRelativeXiComparison1,
    ccmRationalAdelicPrimeRelativeCocycle]

/-- Depth-zero and depth-one cells over the selected prime. -/
def ccmRationalAdelicPrimeRelativeXiCellZero
    (p : Nat.Primes) : PrimeDepthBVWoldCell :=
  (p, 0)

def ccmRationalAdelicPrimeRelativeXiCellOne
    (p : Nat.Primes) : PrimeDepthBVWoldCell :=
  (p, 1)

/-- The second coordinate of the landed prime boundary is the actual first nonzero Xi jet. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_class_landing_snd
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (primeDepthBVWoldXiResolvedCovariantD0
      (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)
      rho (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p)).2 =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) := by
  have hlog : Real.log (p : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  have hratio :
      xiGammaEulerPrimitivePrimeDepthLogClock
            (ccmRationalAdelicPrimeRelativeXiCellOne p) /
          xiGammaEulerPrimitivePrimeDepthLogClock
            (ccmRationalAdelicPrimeRelativeXiCellZero p) = 2 := by
    simp only [ccmRationalAdelicPrimeRelativeXiCellOne,
      ccmRationalAdelicPrimeRelativeXiCellZero,
      xiGammaEulerPrimitivePrimeDepthLogClock_apply]
    field_simp [hlog]
    norm_num
  simp only [primeDepthBVWoldXiResolvedCovariantD0,
    primeDepthBVWoldResolvedCovariantD0,
    primeDepthBVWoldResolvedTransport,
    primeDepthBVWoldXiPrimeLocalizedLeadingConormal,
    ccmRationalAdelicPrimeRelativeXiCellZero,
    ccmRationalAdelicPrimeRelativeXiCellOne,
    LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_sub]
  simp only [if_true]
  have hratio' :
      xiGammaEulerPrimitivePrimeDepthLogClock (p, 1) /
          xiGammaEulerPrimitivePrimeDepthLogClock (p, 0) = 2 := by
    simpa [ccmRationalAdelicPrimeRelativeXiCellOne,
      ccmRationalAdelicPrimeRelativeXiCellZero] using hratio
  rw [hratio']
  change (2 : ℂ) *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) -
        iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)
  ring

/-- The strict landing retains prime, depth, divisor, and nonzero conormal data. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_class_landing_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    primeDepthBVWoldXiResolvedCovariantD0
      (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)
      rho (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p) ≠ 0 := by
  intro hzero
  have hsnd := congrArg Prod.snd hzero
  rw [ccmRationalAdelicPrimeRelativeXiComparison_class_landing_snd] at hsnd
  exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho hsnd

/-- Unconditional source-derived `D1 D0 = 0` on the actual localized Xi landing. -/
theorem ccmRationalAdelicPrimeRelativeXiComparison_class_annihilated
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiResolvedCovariantD1
      (ccmRationalAdelicPrimeRelativeXiComparison1 p
        (ccmRationalAdelicPrimeRelativeCocycle p)) rho i j k = 0 := by
  rw [ccmRationalAdelicPrimeRelativeXiComparison_class_landing]
  exact primeDepthBVWoldResolvedCovariantD1_comp_D0_apply _ _ _ _ _

/-- The strict target image is a boundary, so the induced resolved `H1` class is zero. -/
theorem ccmRationalAdelicPrimeRelativeXiChainMap_H1_class_eq_zero
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeXiChainMap p).H1map
      (ccmRationalAdelicPrimeRelativeClass p) = 0 := by
  rw [ccmRationalAdelicPrimeRelativeClass,
    DeningerThreeTermHom.H1map_mk]
  apply ((primeDepthBVWoldXiResolvedThreeTermComplex).H1_mk_eq_zero_iff _).2
  refine ⟨primeDepthBVWoldXiPrimeLocalizedLeadingConormal p, ?_⟩
  change primeDepthBVWoldXiResolvedCovariantD0
      (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) =
    ccmRationalAdelicPrimeRelativeXiComparison1 p
      (ccmRationalAdelicPrimeRelativeCocycle p)
  exact (ccmRationalAdelicPrimeRelativeXiComparison_class_landing p).symm

end

end RHTower
