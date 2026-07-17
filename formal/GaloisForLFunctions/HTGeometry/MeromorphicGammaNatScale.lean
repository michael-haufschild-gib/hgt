import GaloisForLFunctions.HTGeometry.GammaMultiplication
import GaloisForLFunctions.HTGeometry.MeromorphicGammaSuperselection
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance natScaleDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance natScaleComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance natScaleComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance natScaleDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance natScaleRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance natScaleRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance natScaleDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance natScaleCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Entire reciprocal of `Gamma(n*z+a)`. -/
def reciprocalGammaNatScaleAnalytic (n : ℕ) (a : ℂ) :
    analyticSubring Set.univ :=
  univAnalytic (fun z => reciprocalGammaEntire ((n : ℂ) * z + a)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp
      (by fun_prop))

@[simp] theorem univGermEval_reciprocalGammaNatScaleAnalytic
    (n : ℕ) (a z : ℂ) :
    univGermEval z
        (reciprocalGammaNatScaleAnalytic n a :
          Germ (Filter.principal Set.univ) ℂ) =
      reciprocalGammaEntire ((n : ℂ) * z + a) := by
  rfl

@[simp] theorem univGermEval_reciprocalGammaShiftAnalytic
    (a z : ℂ) :
    univGermEval z
        (reciprocalGammaShiftAnalytic a :
          Germ (Filter.principal Set.univ) ℂ) =
      reciprocalGammaEntire (z + a) := by
  rfl

@[simp] theorem univGermEval_constToAnalytic_natScale
    (c z : ℂ) :
    univGermEval z
        (constToAnalytic Set.univ c :
          Germ (Filter.principal Set.univ) ℂ) = c := by
  rfl

@[simp] theorem univGermEval_analyticSubring_finset_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → analyticSubring Set.univ) (z : ℂ) :
    univGermEval z
        ((∏ i ∈ s, f i : analyticSubring Set.univ) :
          Germ (Filter.principal Set.univ) ℂ) =
      ∏ i ∈ s, univGermEval z
        (f i : Germ (Filter.principal Set.univ) ℂ) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi _ =>
      simp [hi]

/-- Meromorphic realization of `Gamma(n*z+a)`. -/
def gammaNatScaleMero (n : ℕ) (a : ℂ) : meroField Set.univ :=
  (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaNatScaleAnalytic n a))⁻¹

@[simp] theorem reciprocalGammaNatScaleAnalytic_one (a : ℂ) :
    reciprocalGammaNatScaleAnalytic 1 a = reciprocalGammaShiftAnalytic a := by
  apply Subtype.ext
  simp [reciprocalGammaNatScaleAnalytic, reciprocalGammaShiftAnalytic]

@[simp] theorem gammaNatScaleMero_one (a : ℂ) :
    gammaNatScaleMero 1 a = gammaShiftMero a := by
  rw [gammaNatScaleMero, gammaShiftMero,
    reciprocalGammaNatScaleAnalytic_one]

/-- The constant in the meromorphic Gauss reduction. -/
def gammaNatScaleGaussConstant (n : ℕ) (a : ℂ) : ℂ :=
  (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ a

theorem gammaNatScaleGaussConstant_ne_zero {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleGaussConstant n a ≠ 0 := by
  apply mul_ne_zero
  · exact inv_ne_zero (ofReal_ne_zero.mpr (multGammaProd_pos hn one_pos).ne')
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))

theorem reciprocalGammaNatScaleAnalytic_ne_zero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    reciprocalGammaNatScaleAnalytic n a ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  change Germ.ofFun (l := Filter.principal Set.univ)
      (fun z => reciprocalGammaEntire ((n : ℂ) * z + a)) =
    Germ.ofFun (l := Filter.principal Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvalue := eventually_principal.mp hv ((1 - a) / n) (Set.mem_univ _)
  have harg : (n : ℂ) * ((1 - a) / n) + a = 1 := by
    field_simp
    ring
  dsimp only at hvalue
  rw [harg] at hvalue
  simp [reciprocalGammaEntire] at hvalue

theorem gammaNatScaleMero_ne_zero {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleMero n a ≠ 0 := by
  apply inv_ne_zero
  intro hzero
  exact reciprocalGammaNatScaleAnalytic_ne_zero hn a
    ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
      (by simpa using hzero))

/-- The rational linear factor `n*X+a` in the parameter recurrence for
`Gamma(n*z+a)`. -/
def gammaNatScaleLinearFactorRat (n : ℕ) (a : ℂ) : RatFunc ℂ :=
  RatFunc.C (n : ℂ) * RatFunc.X + RatFunc.C a

theorem gammaNatScaleLinearFactorRat_ne_zero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleLinearFactorRat n a ≠ 0 := by
  rw [gammaNatScaleLinearFactorRat]
  rw [show RatFunc.C (n : ℂ) * RatFunc.X + RatFunc.C a =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a) by
    simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X]]
  apply RatFunc.algebraMap_ne_zero
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) hzero
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [hnC] at hcoeff

/-- The reciprocal-Gamma recurrence at positive natural clock scale, as an identity of
entire analytic germs. -/
theorem reciprocalGammaNatScaleAnalytic_add_one_mul_linear
    (n : ℕ) (a : ℂ) :
    reciprocalGammaNatScaleAnalytic n (a + 1) *
        polyToAnalytic Set.univ
          (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a) =
      reciprocalGammaNatScaleAnalytic n a := by
  apply Subtype.ext
  change
    (reciprocalGammaNatScaleAnalytic n (a + 1)).1 *
        (polyToAnalytic Set.univ
          (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a)).1 =
      (reciprocalGammaNatScaleAnalytic n a).1
  rw [show (reciprocalGammaNatScaleAnalytic n (a + 1)).1 =
      Germ.ofFun (l := Filter.principal Set.univ)
        (fun z => reciprocalGammaEntire ((n : ℂ) * z + (a + 1))) from rfl,
    show (polyToAnalytic Set.univ
        (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a)).1 =
      Germ.ofFun (l := Filter.principal Set.univ)
        (fun z =>
          (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a).eval z) from rfl,
    show (reciprocalGammaNatScaleAnalytic n a).1 =
      Germ.ofFun (l := Filter.principal Set.univ)
        (fun z => reciprocalGammaEntire ((n : ℂ) * z + a)) from rfl,
    ← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    have h := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
      ((n : ℂ) * z + a)
    change reciprocalGammaEntire ((n : ℂ) * z + a) =
      ((n : ℂ) * z + a) *
        reciprocalGammaEntire (((n : ℂ) * z + a) + 1) at h
    simp only [Pi.mul_apply, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [show (n : ℂ) * z + (a + 1) = ((n : ℂ) * z + a) + 1 by ring,
      h, mul_comm]

/-- **Scaled Gamma parameter recurrence.**  Increasing the additive parameter by one multiplies
`Gamma(n*z+a)` by the rational observable `n*z+a`. -/
theorem gammaNatScaleMero_add_one
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleMero n (a + 1) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaNatScaleLinearFactorRat n a) *
        gammaNatScaleMero n a := by
  let a0 := algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaNatScaleAnalytic n a)
  let a1 := algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaNatScaleAnalytic n (a + 1))
  let u := algebraMap (RatFunc ℂ) (meroField Set.univ)
    (gammaNatScaleLinearFactorRat n a)
  have hu : u ≠ 0 := by
    exact (map_ne_zero_iff _
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).injective).mpr
      (gammaNatScaleLinearFactorRat_ne_zero hn a)
  have huPoly :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ
            (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a)) = u := by
    change polyToMero Set.univ
        (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (gammaNatScaleLinearFactorRat n a)
    rw [show gammaNatScaleLinearFactorRat n a =
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a) by
      simp [gammaNatScaleLinearFactorRat, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X]]
    exact (ratfuncToMero_algebraMap_polynomial Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty Set.infinite_univ _).symm
  have hrec : a1 * u = a0 := by
    have h := congrArg
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
      (reciprocalGammaNatScaleAnalytic_add_one_mul_linear n a)
    simp only [map_mul] at h
    change a1 * algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (polyToAnalytic Set.univ
          (Polynomial.C (n : ℂ) * Polynomial.X + Polynomial.C a)) = a0 at h
    rw [huPoly] at h
    exact h
  rw [gammaNatScaleMero, gammaNatScaleMero]
  change a1⁻¹ = u * a0⁻¹
  rw [← hrec, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]

theorem reciprocalGammaNatScaleAnalytic_gauss
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    (∏ k ∈ Finset.range n,
        reciprocalGammaShiftAnalytic ((a + k) / n)) =
      constToAnalytic Set.univ (gammaNatScaleGaussConstant n a) *
        physicalExponentialAnalytic ((n : ℂ) * Complex.log (n : ℂ)) *
          reciprocalGammaNatScaleAnalytic n a := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  simp only [univGermEval_analyticSubring_finset_prod,
    univGermEval_reciprocalGammaShiftAnalytic,
    univGermEval_analyticSubring_mul,
    univGermEval_constToAnalytic_natScale,
    univGermEval_physicalExponentialAnalytic,
    univGermEval_reciprocalGammaNatScaleAnalytic]
  change (∏ k ∈ Finset.range n,
      reciprocalGammaEntire (z + (a + k) / n)) =
    gammaNatScaleGaussConstant n a *
      Complex.exp (((n : ℂ) * Complex.log (n : ℂ)) * z) *
        reciprocalGammaEntire ((n : ℂ) * z + a)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hgauss := gauss_multiplication_complex hn ((n : ℂ) * z + a)
  have harg (k : ℕ) : (((n : ℂ) * z + a + k) / n) =
      z + (a + k) / n := by
    field_simp
    ring
  simp_rw [harg] at hgauss
  have hpow : (n : ℂ) ^ ((n : ℂ) * z + a) =
      (n : ℂ) ^ a *
        Complex.exp (((n : ℂ) * Complex.log (n : ℂ)) * z) := by
    rw [Complex.cpow_def_of_ne_zero hnC,
      Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_add]
    congr 1
    ring
  rw [hpow] at hgauss
  simpa [reciprocalGammaEntire, gammaNatScaleGaussConstant, mul_assoc] using hgauss

/-- Gauss multiplication as an exact factorization in the genuine meromorphic field. -/
theorem gammaNatScaleMero_gauss
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleMero n a =
      algebraMap ℂ (meroField Set.univ) (gammaNatScaleGaussConstant n a) *
        physicalExponentialMero ((n : ℂ) * Complex.log (n : ℂ)) *
          ∏ k ∈ Finset.range n, gammaShiftMero ((a + k) / n) := by
  have hE : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (physicalExponentialAnalytic ((n : ℂ) * Complex.log (n : ℂ))) ≠ 0 := by
    change physicalExponentialMero ((n : ℂ) * Complex.log (n : ℂ)) ≠ 0
    exact physicalExponentialMero_ne_zero _
  have hmap := congrArg
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
    (reciprocalGammaNatScaleAnalytic_gauss hn a)
  simp only [map_mul] at hmap
  rw [gammaNatScaleMero]
  simp_rw [gammaShiftMero]
  rw [Finset.prod_inv_distrib, ← map_prod]
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (reciprocalGammaNatScaleAnalytic n a))⁻¹ =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ (gammaNatScaleGaussConstant n a)) *
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (physicalExponentialAnalytic ((n : ℂ) * Complex.log (n : ℂ))) *
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (∏ k ∈ Finset.range n,
          reciprocalGammaShiftAnalytic ((a + k) / n)))⁻¹
  rw [hmap]
  field_simp [gammaNatScaleGaussConstant_ne_zero hn a,
    reciprocalGammaNatScaleAnalytic_ne_zero hn a,
    hE]

/-- The common-scale orbit appearing in Gauss multiplication. -/
def gammaNatScaleGaussProductMero (n : ℕ) (a : ℂ) : meroField Set.univ :=
  ∏ k ∈ Finset.range n, gammaShiftMero ((a + k) / n)

/-- A nonempty positive-integer Gauss orbit is hypertranscendental. -/
theorem hypertranscendentalOver_gammaNatScaleGaussProductMero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaNatScaleGaussProductMero n a) := by
  let shifts : Fin n → ℂ := fun k => (a + (k : ℕ)) / n
  let charges : Fin n → ℤ := fun _ => 1
  let c0 : Fin n := ⟨0, hn⟩
  have horbit : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges c0
    · simp [charges]
    · intro c hc q hq
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hmulC : (c.val : ℂ) = (n : ℂ) * (q : ℂ) := by
        simp [shifts, c0] at hq
        field_simp [hnC] at hq
        linear_combination hq
      have hmulZ : (c.val : ℤ) = (n : ℤ) * q := by
        exact_mod_cast hmulC
      have hc0val : c0.val = 0 := rfl
      have hnZpos : (0 : ℤ) < n := by exact_mod_cast hn
      have hqnonneg : (0 : ℤ) ≤ q := by
        by_contra hq
        have hqneg : q < 0 := lt_of_not_ge hq
        have hprodneg : (n : ℤ) * q < 0 :=
          mul_neg_of_pos_of_neg hnZpos hqneg
        omega
      have hqzero : q = 0 := by
        by_contra hq
        have hqone : (1 : ℤ) ≤ q := by omega
        have hnZnonneg : (0 : ℤ) ≤ n := hnZpos.le
        have hnleprod : (n : ℤ) ≤ (n : ℤ) * q := by
          calc
            (n : ℤ) = (n : ℤ) * 1 := by ring
            _ ≤ (n : ℤ) * q := mul_le_mul_of_nonneg_left hqone hnZnonneg
        have hclt : (c.val : ℤ) < n := by exact_mod_cast c.isLt
        omega
      rw [hqzero, mul_zero] at hmulZ
      have hcval : c.val = 0 := by exact_mod_cast hmulZ
      apply hc
      exact Fin.ext hcval
  rw [gammaNatScaleGaussProductMero, ← Fin.prod_univ_eq_prod_range]
  simpa [gammaOrbitProductMero, shifts, charges] using horbit

/-- Constant rational functions and complex constants have the same image in the
genuine meromorphic field. -/
theorem ratFuncC_toMero_eq_complex_natScale (c : ℂ) :
    algebraMap (RatFunc ℂ) (meroField Set.univ) (RatFunc.C c) =
      algebraMap ℂ (meroField Set.univ) c := by
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (RatFunc.C c) =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c)
  rw [show RatFunc.C c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) by rfl,
    ratfuncToMero_algebraMap_polynomial]
  change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (polyToAnalytic Set.univ (Polynomial.C c)) =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c)
  congr 1
  apply Subtype.ext
  change Germ.ofFun (l := Filter.principal Set.univ)
      (fun z : ℂ => (Polynomial.C c).eval z) =
    Germ.ofFun (l := Filter.principal Set.univ) (fun _ : ℂ => c)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by simp

/-- The nonzero differentially algebraic gauge in the Gauss reduction. -/
def gammaNatScaleGaussGaugeMero (n : ℕ) (a : ℂ) : meroField Set.univ :=
  algebraMap ℂ (meroField Set.univ) (gammaNatScaleGaussConstant n a) *
    physicalExponentialMero ((n : ℂ) * Complex.log (n : ℂ))

theorem gammaNatScaleGaussGaugeMero_ne_zero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleGaussGaugeMero n a ≠ 0 := by
  apply mul_ne_zero
  · exact (map_ne_zero (algebraMap ℂ (meroField Set.univ))).2
      (gammaNatScaleGaussConstant_ne_zero hn a)
  · exact physicalExponentialMero_ne_zero _

theorem differentialAlgebraicOver_gammaNatScaleGaussGaugeMero
    (n : ℕ) (a : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaNatScaleGaussGaugeMero n a) := by
  rw [gammaNatScaleGaussGaugeMero,
    ← ratFuncC_toMero_eq_complex_natScale (gammaNatScaleGaussConstant n a)]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_algebraMap _)
    (differentialAlgebraicOver_physicalExponentialMero _)

/-- **Positive-integer clock-rescaling theorem.** Every genuine meromorphic
`Gamma(n*z+a)` with `n > 0` is hypertranscendental over `C(z)`. -/
theorem hypertranscendentalOver_gammaNatScaleMero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaNatScaleMero n a) := by
  rw [gammaNatScaleMero_gauss hn a]
  change HypertranscendentalOver (RatFunc ℂ)
    (gammaNatScaleGaussGaugeMero n a *
      gammaNatScaleGaussProductMero n a)
  have hiff := HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (x := gammaNatScaleGaussProductMero n a)
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero n a)
    (gammaNatScaleGaussGaugeMero_ne_zero hn a)
  rw [mul_comm]
  exact hiff.mpr (hypertranscendentalOver_gammaNatScaleGaussProductMero hn a)

/-- A finite signed family of positive-integer-scale Gamma clocks. -/
def gammaNatScaleFamilyMero {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleMero (n i) (a i) ^ m i

/-- Product of the nonzero DA Gauss gauges for a scaled Gamma family. -/
def gammaNatScaleFamilyGaugeMero {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleGaussGaugeMero (n i) (a i) ^ m i

/-- The common-unit-scale Gamma product left after refining every integer scale. -/
def gammaNatScaleFamilyRefinedMero {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleGaussProductMero (n i) (a i) ^ m i

/-- Exact simultaneous Gauss reduction for a finite commensurable-scale family. -/
theorem gammaNatScaleFamilyMero_normalForm
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaNatScaleFamilyMero n a m =
      gammaNatScaleFamilyGaugeMero n a m *
        gammaNatScaleFamilyRefinedMero n a m := by
  rw [gammaNatScaleFamilyMero, gammaNatScaleFamilyGaugeMero,
    gammaNatScaleFamilyRefinedMero]
  simp_rw [gammaNatScaleMero_gauss (hn _)]
  change (∏ i, (gammaNatScaleGaussGaugeMero (n i) (a i) *
      gammaNatScaleGaussProductMero (n i) (a i)) ^ m i) = _
  simp_rw [mul_zpow]
  exact Finset.prod_mul_distrib

theorem gammaNatScaleFamilyGaugeMero_ne_zero
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaNatScaleFamilyGaugeMero n a m ≠ 0 := by
  rw [gammaNatScaleFamilyGaugeMero, Finset.prod_ne_zero_iff]
  intro i _
  exact zpow_ne_zero _ (gammaNatScaleGaussGaugeMero_ne_zero (hn i) (a i))

theorem differentialAlgebraicOver_gammaNatScaleFamilyGaugeMero
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaNatScaleFamilyGaugeMero n a m) := by
  rw [gammaNatScaleFamilyGaugeMero]
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro i _
  have hi := differentialAlgebraicOver_gammaNatScaleGaussGaugeMero (n i) (a i)
  cases hm : m i with
  | ofNat k =>
      simpa [hm] using HTGeometry.differentialAlgebraicOver_pow hi k
  | negSucc k =>
      rw [zpow_negSucc]
      exact HTGeometry.differentialAlgebraicOver_inv
        (HTGeometry.differentialAlgebraicOver_pow hi (k + 1))

/-- All DA cancellation questions for a positive commensurable family reduce exactly to its
unit-scale refined Gamma product. -/
theorem differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_refined
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaNatScaleFamilyMero n a m) ↔
      DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaNatScaleFamilyRefinedMero n a m) := by
  rw [gammaNatScaleFamilyMero_normalForm n a m hn]
  constructor
  · intro hfamily
    have hdiv := HTGeometry.differentialAlgebraicOver_div hfamily
      (differentialAlgebraicOver_gammaNatScaleFamilyGaugeMero n a m)
    have heq : (gammaNatScaleFamilyGaugeMero n a m *
          gammaNatScaleFamilyRefinedMero n a m) /
        gammaNatScaleFamilyGaugeMero n a m =
          gammaNatScaleFamilyRefinedMero n a m := by
      field_simp [gammaNatScaleFamilyGaugeMero_ne_zero n a m hn]
    rwa [heq] at hdiv
  · exact HTGeometry.differentialAlgebraicOver_mul
      (differentialAlgebraicOver_gammaNatScaleFamilyGaugeMero n a m)

/-- Hypertranscendence of a positive commensurable Gamma family is exactly that of the refined
unit-scale orbit product. -/
theorem hypertranscendentalOver_gammaNatScaleFamilyMero_iff_refined
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    HypertranscendentalOver (RatFunc ℂ) (gammaNatScaleFamilyMero n a m) ↔
      HypertranscendentalOver (RatFunc ℂ)
        (gammaNatScaleFamilyRefinedMero n a m) := by
  rw [gammaNatScaleFamilyMero_normalForm n a m hn, mul_comm]
  exact HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaNatScaleFamilyGaugeMero n a m)
    (gammaNatScaleFamilyGaugeMero_ne_zero n a m hn)

/-- A finite shifted-Gamma product indexed by an arbitrary finite type.  This removes the
presentation restriction to `Fin d` when a natural refinement is indexed by a dependent finite
sum. -/
def gammaFintypeOrbitProductMero {ι : Type*} [Fintype ι]
    (b : ι → ℂ) (m : ι → ℤ) : meroField Set.univ :=
  ∏ i, gammaShiftMero (b i) ^ m i

/-- The separated-orbit Gamma criterion is invariant under every finite reindexing.  Other slots
may collide with one another; only the distinguished nonzero-charge slot must be separated from
all competitors. -/
theorem hypertranscendentalOver_gammaFintypeOrbitProductMero
    {ι : Type*} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ)
    (i0 : ι) (hm : m i0 ≠ 0)
    (hsep : ∀ i, i ≠ i0 → ∀ q : ℤ, b i - b i0 ≠ (q : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeOrbitProductMero b m) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let b' : Fin (Fintype.card ι) → ℂ := fun j => b (e.symm j)
  let m' : Fin (Fintype.card ι) → ℤ := fun j => m (e.symm j)
  have hfin : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero b' m') := by
    apply hypertranscendentalOver_gammaOrbitProductMero b' m' (e i0)
    · simpa [m'] using hm
    · intro j hj q
      have hj' : e.symm j ≠ i0 := by
        intro heq
        apply hj
        rw [← e.apply_symm_apply j, heq]
      simpa [b'] using hsep (e.symm j) hj' q
  have hprod : gammaOrbitProductMero b' m' =
      gammaFintypeOrbitProductMero b m := by
    rw [gammaOrbitProductMero, gammaFintypeOrbitProductMero]
    simpa [b', m'] using
      (Equiv.prod_comp e.symm (fun i => gammaShiftMero (b i) ^ m i))
  rwa [hprod] at hfin

/-- The shift attached to a dependent slot in the simultaneous Gauss refinement of an
integer-scale Gamma family. -/
def gammaNatScaleRefinedSlotShift {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x : Σ i, Fin (n i)) : ℂ :=
  (a x.1 + (x.2 : ℕ)) / n x.1

/-- Every refined slot inherits the signed charge of its parent scaled Gamma factor. -/
def gammaNatScaleRefinedSlotCharge {d : ℕ} {n : Fin d → ℕ}
    (m : Fin d → ℤ) (x : Σ i, Fin (n i)) : ℤ :=
  m x.1

/-- Flatten the nested Gauss products of a finite integer-scale family into one product on the
dependent refined-slot type. -/
theorem gammaNatScaleFamilyRefinedMero_eq_slotProduct
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) :
    gammaNatScaleFamilyRefinedMero n a m =
      gammaFintypeOrbitProductMero
        (gammaNatScaleRefinedSlotShift n a)
        (gammaNatScaleRefinedSlotCharge m) := by
  classical
  rw [gammaNatScaleFamilyRefinedMero, gammaFintypeOrbitProductMero,
    Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [gammaNatScaleGaussProductMero, ← Fin.prod_univ_eq_prod_range,
    ← Finset.prod_zpow]
  rfl

/-- **Exposed refined-orbit criterion.**  A finite signed family of positive integer-scale Gamma
clocks is HT whenever one Gauss-refined slot has nonzero charge and occupies an integer-translation
orbit disjoint from every other refined slot.  No conditions are imposed on collisions or signed
cancellations among the remaining slots. -/
theorem hypertranscendentalOver_gammaNatScaleFamilyMero_of_exposedRefinedOrbit
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) (x0 : Σ i, Fin (n i))
    (hm : m x0.1 ≠ 0)
    (hsep : ∀ x : Σ i, Fin (n i), x ≠ x0 → ∀ q : ℤ,
      gammaNatScaleRefinedSlotShift n a x -
          gammaNatScaleRefinedSlotShift n a x0 ≠ (q : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaNatScaleFamilyMero n a m) := by
  rw [hypertranscendentalOver_gammaNatScaleFamilyMero_iff_refined n a m hn,
    gammaNatScaleFamilyRefinedMero_eq_slotProduct]
  exact hypertranscendentalOver_gammaFintypeOrbitProductMero
    (gammaNatScaleRefinedSlotShift n a)
    (gammaNatScaleRefinedSlotCharge m) x0 hm hsep

/-- Entire reciprocal of `Gamma(-n*z+b)`. -/
def reciprocalGammaNegativeNatScaleAnalytic (n : ℕ) (b : ℂ) :
    analyticSubring Set.univ :=
  univAnalytic (fun z => reciprocalGammaEntire (-(n : ℂ) * z + b)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp
      (by fun_prop))

@[simp] theorem univGermEval_reciprocalGammaNegativeNatScaleAnalytic
    (n : ℕ) (b z : ℂ) :
    univGermEval z
        (reciprocalGammaNegativeNatScaleAnalytic n b :
          Germ (Filter.principal Set.univ) ℂ) =
      reciprocalGammaEntire (-(n : ℂ) * z + b) := by
  rfl

@[simp] theorem univGermEval_reciprocalGammaNegativeShiftAnalytic
    (b z : ℂ) :
    univGermEval z
        (reciprocalGammaNegativeShiftAnalytic b :
          Germ (Filter.principal Set.univ) ℂ) =
      reciprocalGammaEntire (-z + b) := by
  rfl

/-- Genuine meromorphic realization of `Gamma(-n*z+b)`. -/
def gammaNegativeNatScaleMero (n : ℕ) (b : ℂ) : meroField Set.univ :=
  (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaNegativeNatScaleAnalytic n b))⁻¹

@[simp] theorem reciprocalGammaNegativeNatScaleAnalytic_one (b : ℂ) :
    reciprocalGammaNegativeNatScaleAnalytic 1 b =
      reciprocalGammaNegativeShiftAnalytic b := by
  apply Subtype.ext
  simp [reciprocalGammaNegativeNatScaleAnalytic,
    reciprocalGammaNegativeShiftAnalytic]

@[simp] theorem gammaNegativeNatScaleMero_one (b : ℂ) :
    gammaNegativeNatScaleMero 1 b = gammaNegativeShiftMero b := by
  rw [gammaNegativeNatScaleMero, gammaNegativeShiftMero,
    reciprocalGammaNegativeNatScaleAnalytic_one]

theorem reciprocalGammaNegativeNatScaleAnalytic_ne_zero
    {n : ℕ} (hn : 0 < n) (b : ℂ) :
    reciprocalGammaNegativeNatScaleAnalytic n b ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  change Germ.ofFun (l := Filter.principal Set.univ)
      (fun z => reciprocalGammaEntire (-(n : ℂ) * z + b)) =
    Germ.ofFun (l := Filter.principal Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvalue := eventually_principal.mp hv ((b - 1) / n) (Set.mem_univ _)
  have harg : -(n : ℂ) * ((b - 1) / n) + b = 1 := by
    field_simp
    ring
  dsimp only at hvalue
  rw [harg] at hvalue
  simp [reciprocalGammaEntire] at hvalue

theorem gammaNegativeNatScaleMero_ne_zero
    {n : ℕ} (hn : 0 < n) (b : ℂ) :
    gammaNegativeNatScaleMero n b ≠ 0 := by
  apply inv_ne_zero
  intro hzero
  exact reciprocalGammaNegativeNatScaleAnalytic_ne_zero hn b
    ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
      (by simpa using hzero))

/-- Analytic Gauss refinement of a negative-orientation integer clock. -/
theorem reciprocalGammaNegativeNatScaleAnalytic_gauss
    {n : ℕ} (hn : 0 < n) (b : ℂ) :
    (∏ k ∈ Finset.range n,
        reciprocalGammaNegativeShiftAnalytic ((b + k) / n)) =
      constToAnalytic Set.univ (gammaNatScaleGaussConstant n b) *
        physicalExponentialAnalytic (-((n : ℂ) * Complex.log (n : ℂ))) *
          reciprocalGammaNegativeNatScaleAnalytic n b := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  simp only [univGermEval_analyticSubring_finset_prod,
    univGermEval_reciprocalGammaNegativeShiftAnalytic,
    univGermEval_analyticSubring_mul,
    univGermEval_constToAnalytic_natScale,
    univGermEval_physicalExponentialAnalytic,
    univGermEval_reciprocalGammaNegativeNatScaleAnalytic]
  change (∏ k ∈ Finset.range n,
      reciprocalGammaEntire (-z + (b + k) / n)) =
    gammaNatScaleGaussConstant n b *
      Complex.exp (-((n : ℂ) * Complex.log (n : ℂ)) * z) *
        reciprocalGammaEntire (-(n : ℂ) * z + b)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hgauss := gauss_multiplication_complex hn (-(n : ℂ) * z + b)
  have harg (k : ℕ) : ((-(n : ℂ) * z + b + k) / n) =
      -z + (b + k) / n := by
    field_simp
    ring
  simp_rw [harg] at hgauss
  have hpow : (n : ℂ) ^ (-(n : ℂ) * z + b) =
      (n : ℂ) ^ b *
        Complex.exp (-((n : ℂ) * Complex.log (n : ℂ)) * z) := by
    rw [Complex.cpow_def_of_ne_zero hnC,
      Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_add]
    congr 1
    ring
  rw [hpow] at hgauss
  simpa [reciprocalGammaEntire, gammaNatScaleGaussConstant, mul_assoc] using hgauss

/-- Unit-scale negative Gamma orbit appearing after Gauss refinement. -/
def gammaNegativeNatScaleGaussProductMero (n : ℕ) (b : ℂ) :
    meroField Set.univ :=
  ∏ k ∈ Finset.range n, gammaNegativeShiftMero ((b + k) / n)

/-- Nonzero DA gauge in the negative-orientation Gauss reduction. -/
def gammaNegativeNatScaleGaussGaugeMero (n : ℕ) (b : ℂ) :
    meroField Set.univ :=
  algebraMap ℂ (meroField Set.univ) (gammaNatScaleGaussConstant n b) *
    physicalExponentialMero (-((n : ℂ) * Complex.log (n : ℂ)))

theorem gammaNegativeNatScaleMero_gauss
    {n : ℕ} (hn : 0 < n) (b : ℂ) :
    gammaNegativeNatScaleMero n b =
      gammaNegativeNatScaleGaussGaugeMero n b *
        gammaNegativeNatScaleGaussProductMero n b := by
  have hE : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (physicalExponentialAnalytic (-((n : ℂ) * Complex.log (n : ℂ)))) ≠ 0 := by
    change physicalExponentialMero (-((n : ℂ) * Complex.log (n : ℂ))) ≠ 0
    exact physicalExponentialMero_ne_zero _
  have hmap := congrArg
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
    (reciprocalGammaNegativeNatScaleAnalytic_gauss hn b)
  simp only [map_mul] at hmap
  rw [gammaNegativeNatScaleMero]
  simp_rw [gammaNegativeNatScaleGaussProductMero, gammaNegativeShiftMero]
  rw [Finset.prod_inv_distrib, ← map_prod]
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (reciprocalGammaNegativeNatScaleAnalytic n b))⁻¹ =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ (gammaNatScaleGaussConstant n b)) *
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (physicalExponentialAnalytic (-((n : ℂ) * Complex.log (n : ℂ)))) *
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (∏ k ∈ Finset.range n,
          reciprocalGammaNegativeShiftAnalytic ((b + k) / n)))⁻¹
  rw [hmap]
  field_simp [gammaNatScaleGaussConstant_ne_zero hn b,
    reciprocalGammaNegativeNatScaleAnalytic_ne_zero hn b, hE]

theorem gammaNegativeNatScaleGaussGaugeMero_ne_zero
    {n : ℕ} (hn : 0 < n) (b : ℂ) :
    gammaNegativeNatScaleGaussGaugeMero n b ≠ 0 := by
  apply mul_ne_zero
  · exact (map_ne_zero (algebraMap ℂ (meroField Set.univ))).2
      (gammaNatScaleGaussConstant_ne_zero hn b)
  · exact physicalExponentialMero_ne_zero _

theorem differentialAlgebraicOver_gammaNegativeNatScaleGaussGaugeMero
    (n : ℕ) (b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaNegativeNatScaleGaussGaugeMero n b) := by
  rw [gammaNegativeNatScaleGaussGaugeMero,
    ← ratFuncC_toMero_eq_complex_natScale (gammaNatScaleGaussConstant n b)]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_algebraMap _)
    (differentialAlgebraicOver_physicalExponentialMero _)

/-- Finite signed family with both positive and negative integer clock orientations. -/
def gammaOrientedNatScaleFamilyMero {d : ℕ} (n : Fin d → ℕ)
    (a b : Fin d → ℂ) (p q : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleMero (n i) (a i) ^ p i *
    gammaNegativeNatScaleMero (n i) (b i) ^ q i

/-- Complete DA Gauss gauge of an oriented integer-scale family. -/
def gammaOrientedNatScaleFamilyGaugeMero {d : ℕ} (n : Fin d → ℕ)
    (a b : Fin d → ℂ) (p q : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleGaussGaugeMero (n i) (a i) ^ p i *
    gammaNegativeNatScaleGaussGaugeMero (n i) (b i) ^ q i

/-- Unit-scale oriented Gamma product after simultaneous Gauss refinement. -/
def gammaOrientedNatScaleFamilyRefinedMero {d : ℕ} (n : Fin d → ℕ)
    (a b : Fin d → ℂ) (p q : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNatScaleGaussProductMero (n i) (a i) ^ p i *
    gammaNegativeNatScaleGaussProductMero (n i) (b i) ^ q i

theorem gammaOrientedNatScaleFamilyMero_normalForm
    {d : ℕ} (n : Fin d → ℕ) (a b : Fin d → ℂ) (p q : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaOrientedNatScaleFamilyMero n a b p q =
      gammaOrientedNatScaleFamilyGaugeMero n a b p q *
        gammaOrientedNatScaleFamilyRefinedMero n a b p q := by
  rw [gammaOrientedNatScaleFamilyMero, gammaOrientedNatScaleFamilyGaugeMero,
    gammaOrientedNatScaleFamilyRefinedMero]
  simp_rw [gammaNatScaleMero_gauss (hn _),
    gammaNegativeNatScaleMero_gauss (hn _), mul_zpow]
  simp_rw [Finset.prod_mul_distrib]
  simp only [gammaNatScaleGaussGaugeMero, gammaNatScaleGaussProductMero]
  simp_rw [mul_zpow, Finset.prod_mul_distrib]
  ring

theorem gammaOrientedNatScaleFamilyGaugeMero_ne_zero
    {d : ℕ} (n : Fin d → ℕ) (a b : Fin d → ℂ) (p q : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaOrientedNatScaleFamilyGaugeMero n a b p q ≠ 0 := by
  rw [gammaOrientedNatScaleFamilyGaugeMero, Finset.prod_ne_zero_iff]
  intro i _
  exact mul_ne_zero
    (zpow_ne_zero _ (gammaNatScaleGaussGaugeMero_ne_zero (hn i) (a i)))
    (zpow_ne_zero _ (gammaNegativeNatScaleGaussGaugeMero_ne_zero (hn i) (b i)))

private theorem differentialAlgebraicOver_zpow_orientedNatScale
    {x : meroField Set.univ}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) (m : ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (x ^ m) := by
  cases m with
  | ofNat k => simpa using HTGeometry.differentialAlgebraicOver_pow hx k
  | negSucc k =>
      rw [zpow_negSucc]
      exact HTGeometry.differentialAlgebraicOver_inv
        (HTGeometry.differentialAlgebraicOver_pow hx (k + 1))

theorem differentialAlgebraicOver_gammaOrientedNatScaleFamilyGaugeMero
    {d : ℕ} (n : Fin d → ℕ) (a b : Fin d → ℂ) (p q : Fin d → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOrientedNatScaleFamilyGaugeMero n a b p q) := by
  rw [gammaOrientedNatScaleFamilyGaugeMero]
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro i _
  exact HTGeometry.differentialAlgebraicOver_mul
    (differentialAlgebraicOver_zpow_orientedNatScale
      (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero (n i) (a i)) (p i))
    (differentialAlgebraicOver_zpow_orientedNatScale
      (differentialAlgebraicOver_gammaNegativeNatScaleGaussGaugeMero (n i) (b i)) (q i))

theorem differentialAlgebraicOver_gammaOrientedNatScaleFamilyMero_iff_refined
    {d : ℕ} (n : Fin d → ℕ) (a b : Fin d → ℂ) (p q : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaOrientedNatScaleFamilyMero n a b p q) ↔
      DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaOrientedNatScaleFamilyRefinedMero n a b p q) := by
  rw [gammaOrientedNatScaleFamilyMero_normalForm n a b p q hn]
  constructor
  · intro hfamily
    have hdiv := HTGeometry.differentialAlgebraicOver_div hfamily
      (differentialAlgebraicOver_gammaOrientedNatScaleFamilyGaugeMero n a b p q)
    have heq : (gammaOrientedNatScaleFamilyGaugeMero n a b p q *
          gammaOrientedNatScaleFamilyRefinedMero n a b p q) /
        gammaOrientedNatScaleFamilyGaugeMero n a b p q =
          gammaOrientedNatScaleFamilyRefinedMero n a b p q := by
      field_simp [gammaOrientedNatScaleFamilyGaugeMero_ne_zero n a b p q hn]
    rwa [heq] at hdiv
  · exact HTGeometry.differentialAlgebraicOver_mul
      (differentialAlgebraicOver_gammaOrientedNatScaleFamilyGaugeMero n a b p q)

theorem hypertranscendentalOver_gammaOrientedNatScaleFamilyMero_iff_refined
    {d : ℕ} (n : Fin d → ℕ) (a b : Fin d → ℂ) (p q : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    HypertranscendentalOver (RatFunc ℂ)
        (gammaOrientedNatScaleFamilyMero n a b p q) ↔
      HypertranscendentalOver (RatFunc ℂ)
        (gammaOrientedNatScaleFamilyRefinedMero n a b p q) := by
  rw [gammaOrientedNatScaleFamilyMero_normalForm n a b p q hn, mul_comm]
  exact HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaOrientedNatScaleFamilyGaugeMero n a b p q)
    (gammaOrientedNatScaleFamilyGaugeMero_ne_zero n a b p q hn)

end

end GaloisForLFunctions
