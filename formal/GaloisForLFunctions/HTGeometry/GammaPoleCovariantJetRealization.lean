import GaloisForLFunctions.HTGeometry.SimplePoleJetLatticeHorizon
import GaloisForLFunctions.HTGeometry.GammaPoleAnalyticCoefficientFreeness
import GaloisForLFunctions.HTGeometry.GammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Dynamic covariant realization of the Gamma pole profile

The universal simple-pole profile is a running-point identity: its boundary
variable `X k` represents `U⁽ᵏ⁾(x)` before the local coordinate is frozen at
zero.  This module proves that exact analytic value law for `U(x) / x`, then
specializes it to the factorially normalized Gamma pole chart.

The Gamma specialization discharges all side conditions in the existing
source identity on a deleted neighborhood.  It identifies every native Gamma
jet, and hence every finite polynomial-coefficient jet packet, with its
dynamic covariant profile.  The final theorem reflects this value relation
through `meromorphicOrderAt`.

This is the analytic realization layer needed before a frozen boundary profile
can be used.  It does not assert that native pole-order cutoffs are already
equivalent to cutoffs of the frozen moving profile; Taylor variation of the
regular jets remains a separate triangular descent.
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions

noncomputable section

/-- Evaluate the universal regular-boundary variables on the running jet of
`U` at `x`. -/
def simplePoleBoundaryJetEval (U : ℂ → ℂ) (x : ℂ) :
    MvPolynomial ℕ ℂ →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ)
    (fun k => iteratedDeriv k U x)

/-- Evaluate the universal `j`th simple-pole profile at the running regular
jet and at pole variable `x⁻¹`. -/
def simplePoleCovariantJetValue (U : ℂ → ℂ) (j : ℕ) (x : ℂ) : ℂ :=
  Polynomial.eval₂ (simplePoleBoundaryJetEval U x) x⁻¹
    (HTGeometry.universalSimplePoleJetProfile j)

/-- The complete finite Laurent profile before its pole variable is evaluated. -/
def simplePoleCovariantJetLaurent (U : ℂ → ℂ) (j : ℕ) (x : ℂ) :
    LaurentPolynomial ℂ :=
  Polynomial.toLaurent
    ((HTGeometry.universalSimplePoleJetProfile j).map
      (simplePoleBoundaryJetEval U x))

/-- The inverse local coordinate as a unit on a punctured chart. -/
def puncturedInverseUnit (x : ℂ) (hx : x ≠ 0) : ℂˣ :=
  Units.mk0 x⁻¹ (inv_ne_zero hx)

/-- Evaluating the finite covariant Laurent profile at `x⁻¹` recovers its
scalar running-point value. -/
theorem eval₂_simplePoleCovariantJetLaurent
    (U : ℂ → ℂ) (j : ℕ) {x : ℂ} (hx : x ≠ 0) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (puncturedInverseUnit x hx)
        (simplePoleCovariantJetLaurent U j x) =
      simplePoleCovariantJetValue U j x := by
  simp [simplePoleCovariantJetLaurent, simplePoleCovariantJetValue,
    puncturedInverseUnit]
  rw [Polynomial.eval_map]

/-- Expanded value relation for the dynamic covariant profile. -/
theorem simplePoleCovariantJetValue_eq_sum
    (U : ℂ → ℂ) (j : ℕ) (x : ℂ) :
    simplePoleCovariantJetValue U j x =
      ∑ k ∈ range (j + 1),
        (j.choose k : ℂ) * iteratedDeriv k U x *
          ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) *
          x⁻¹ ^ (j - k + 1) := by
  simp [simplePoleCovariantJetValue, simplePoleBoundaryJetEval,
    HTGeometry.universalSimplePoleJetProfile,
    HTGeometry.universalSimplePoleRegularProfile,
    Polynomial.eval₂_finsetSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- **General dynamic realization law.**  The universal covariant profile is
exactly the `j`th derivative of `U(x) / x` at every punctured smooth point. -/
theorem simplePoleCovariantJetValue_eq_iteratedDeriv_div
    {U : ℂ → ℂ} {j : ℕ} {x : ℂ}
    (hU : ContDiffAt ℂ j U x) (hx : x ≠ 0) :
    simplePoleCovariantJetValue U j x =
      iteratedDeriv j (fun z => U z / z) x := by
  rw [simplePoleCovariantJetValue_eq_sum]
  change _ = iteratedDeriv j (U * fun z : ℂ => z⁻¹) x
  have hinv : ContDiffAt ℂ j (fun z : ℂ => z⁻¹) x :=
    (contDiffAt_id (𝕜 := ℂ)).inv hx
  rw [iteratedDeriv_mul hU hinv]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range, Nat.lt_succ_iff] at hk
  have hinvder := iteratedDeriv_inv_add_const 0 (j - k) x (by simpa using hx)
  simp only [add_zero] at hinvder
  rw [hinvder, inv_pow]
  ring

/-- The dynamic realization holds throughout a deleted neighborhood whenever
the regular numerator is analytic at the center. -/
theorem simplePoleCovariantJetValue_eventuallyEq_iteratedDeriv_div
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    simplePoleCovariantJetValue U j =ᶠ[𝓝[≠] 0]
      iteratedDeriv j (fun z => U z / z) := by
  have hUevent : ∀ᶠ x : ℂ in 𝓝[≠] 0, ContDiffAt ℂ j U x :=
    nhdsWithin_le_nhds (hU.eventually_analyticAt.mono fun _ hx => hx.contDiffAt)
  filter_upwards [hUevent, self_mem_nhdsWithin] with x hUx hx
  exact simplePoleCovariantJetValue_eq_iteratedDeriv_div hUx hx

/-- Analyticity of the regular numerator discharges meromorphicity of every
dynamic simple-pole jet profile. -/
theorem meromorphicAt_simplePoleCovariantJetValue
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    MeromorphicAt (simplePoleCovariantJetValue U j) 0 := by
  have hid : MeromorphicAt (fun z : ℂ => z) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z) 0).meromorphicAt
  have hdiv : MeromorphicAt (fun z => U z / z) 0 := hU.meromorphicAt.div hid
  have hderiv : MeromorphicAt (iteratedDeriv j (fun z => U z / z)) 0 := by
    rw [iteratedDeriv_eq_iterate]
    exact hdiv.iterated_deriv
  exact hderiv.congr
    (simplePoleCovariantJetValue_eventuallyEq_iteratedDeriv_div hU j).symm

/-- **Dynamic top-residue reflection.**  The running covariant jet retains
the exact highest pole residue of `U(x) / x`; all Taylor variation affects
only lower Laurent grades. -/
theorem tendsto_pow_succ_mul_simplePoleCovariantJetValue
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    Tendsto (fun x : ℂ => x ^ (j + 1) * simplePoleCovariantJetValue U j x)
      (𝓝[≠] 0) (𝓝 (U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)))) := by
  have hev : (fun x : ℂ => x ^ (j + 1) * simplePoleCovariantJetValue U j x) =ᶠ[𝓝[≠] 0]
      fun x => ∑ k ∈ range (j + 1),
        (j.choose k : ℂ) * iteratedDeriv k U x *
          ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) * x ^ k := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [simplePoleCovariantJetValue_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range, Nat.lt_succ_iff] at hk
    have hpow : x ^ (j + 1) * x⁻¹ ^ (j - k + 1) = x ^ k := by
      rw [inv_pow, ← pow_sub₀ x hx0 (by omega : j - k + 1 ≤ j + 1)]
      congr 1
      omega
    linear_combination
      ((j.choose k : ℂ) * iteratedDeriv k U x *
        ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ))) * hpow
  have hlim : Tendsto (fun x : ℂ => ∑ k ∈ range (j + 1),
      (j.choose k : ℂ) * iteratedDeriv k U x *
        ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) * x ^ k)
      (𝓝[≠] 0) (𝓝 (∑ k ∈ range (j + 1),
        (j.choose k : ℂ) * iteratedDeriv k U 0 *
          ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) * (0 : ℂ) ^ k)) := by
    apply tendsto_finsetSum
    intro k hk
    have hkcont : ContinuousAt (iteratedDeriv k U) 0 :=
      continuousAt_iteratedDeriv_of_contDiffAt hU.contDiffAt
    exact ((((continuousAt_const.mul hkcont).mul continuousAt_const).mul
      (continuousAt_id.pow k)).continuousWithinAt)
  have hvalue : (∑ k ∈ range (j + 1),
      (j.choose k : ℂ) * iteratedDeriv k U 0 *
        ((-1 : ℂ) ^ (j - k) * ((j - k).factorial : ℂ)) * (0 : ℂ) ^ k) =
      U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [zero_pow hk0, mul_zero]
    · intro h0
      exact (h0 (Finset.mem_range.mpr (Nat.zero_lt_succ j))).elim
  rw [hvalue] at hlim
  exact hlim.congr' (hev.mono fun _ h => h.symm)

/-- The covariant `j`-jet of `U/x`, after subtracting its unique pole monomial, is the analytic
`j`-jet of the divided difference of `U`. -/
theorem simplePoleCovariantJetValue_sub_principal_eventuallyEq
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    (fun x : ℂ => simplePoleCovariantJetValue U j x -
      U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1)) =ᶠ[𝓝[≠] 0]
      iteratedDeriv j (dslope U 0) := by
  filter_upwards [simplePoleCovariantJetValue_eventuallyEq_iteratedDeriv_div hU j,
    iteratedDeriv_div_id_sub_principal_eventuallyEq hU j] with x hcov hrem
  rw [hcov]
  exact hrem

/-- The subtracted simple-pole covariant jet has a removable singularity with an explicit
analytic extension. -/
theorem exists_analyticAt_simplePoleCovariantJetValue_sub_principal
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      (fun x : ℂ => simplePoleCovariantJetValue U j x -
        U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1)) =ᶠ[𝓝[≠] 0] R := by
  refine ⟨iteratedDeriv j (dslope U 0), ?_,
    simplePoleCovariantJetValue_sub_principal_eventuallyEq hU j⟩
  exact analyticAt_iteratedDeriv_of_analyticAt
    (analyticAt_dslope_zero_of_analyticAt hU) j

/-- The hypotheses of `gammaPoleRegularUnit_source_identity` hold throughout
a deleted neighborhood of the normalized pole coordinate. -/
theorem gammaPoleRegularUnit_source_eventuallyEq (branch : ℕ) :
    (fun x : ℂ => Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) =ᶠ[𝓝[≠] 0]
      (fun x : ℂ => -gammaPoleRegularUnit branch x / x) := by
  have hoff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    norm_num only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have haff : ContinuousAt
      (fun x : ℂ => reciprocalGammaFactorialScale branch * x + 1) 0 := by
    fun_prop
  have hpole : ∀ᶠ x : ℂ in 𝓝 0,
      ∀ p : ℕ, reciprocalGammaFactorialScale branch * x + 1 ≠ -(p : ℂ) :=
    haff (offPoles_isOpen.mem_nhds (by simpa using hoff))
  have hprodcont : ContinuousAt
      (reciprocalGammaNormalizedProduct branch) 0 := by
    unfold reciprocalGammaNormalizedProduct
    fun_prop
  have hprod : ∀ᶠ x : ℂ in 𝓝 0,
      reciprocalGammaNormalizedProduct branch x ≠ 0 :=
    hprodcont.eventually_ne (by
      rw [reciprocalGammaNormalizedProduct_zero]
      exact one_ne_zero)
  filter_upwards [nhdsWithin_le_nhds hpole, nhdsWithin_le_nhds hprod,
    self_mem_nhdsWithin] with x hxpole hxprod hx
  exact gammaPoleRegularUnit_source_identity branch hx hxpole hxprod

/-- The running-point covariant realization of a Gamma derivative in its
factorially normalized pole coordinate. -/
def gammaPoleCovariantJetValue (branch j : ℕ) (x : ℂ) : ℂ :=
  -(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
    simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x

/-- The finite running-point Laurent profile of the `j`th Gamma derivative,
including the exact affine-coordinate scale. -/
def gammaPoleCovariantDerivativeLaurent (branch j : ℕ) (x : ℂ) :
    LaurentPolynomial ℂ :=
  LaurentPolynomial.C (-(reciprocalGammaFactorialScale branch)⁻¹ ^ j) *
    simplePoleCovariantJetLaurent (gammaPoleRegularUnit branch) j x

/-- The Gamma derivative Laurent profile evaluates to the scalar covariant
Gamma jet value. -/
theorem eval₂_gammaPoleCovariantDerivativeLaurent
    (branch j : ℕ) {x : ℂ} (hx : x ≠ 0) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (puncturedInverseUnit x hx)
        (gammaPoleCovariantDerivativeLaurent branch j x) =
      gammaPoleCovariantJetValue branch j x := by
  simp [gammaPoleCovariantDerivativeLaurent, gammaPoleCovariantJetValue,
    eval₂_simplePoleCovariantJetLaurent]

/-- Every dynamic Gamma generator profile is meromorphic at the normalized
pole center, with no downstream hypothesis. -/
theorem meromorphicAt_gammaPoleCovariantJetValue (branch j : ℕ) :
    MeromorphicAt (gammaPoleCovariantJetValue branch j) 0 := by
  have hconst : MeromorphicAt
      (fun _ : ℂ => -(reciprocalGammaFactorialScale branch)⁻¹ ^ j) 0 :=
    analyticAt_const.meromorphicAt
  exact hconst.mul (meromorphicAt_simplePoleCovariantJetValue
    (gammaPoleRegularUnit_analyticAt_zero branch) j)

/-- Exact top-residue limit for a factorially normalized Gamma derivative. -/
theorem tendsto_pow_succ_mul_gammaPoleCovariantJetValue (branch j : ℕ) :
    Tendsto (fun x : ℂ => x ^ (j + 1) * gammaPoleCovariantJetValue branch j x)
      (𝓝[≠] 0)
      (𝓝 (-(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ)))) := by
  let c : ℂ := -(reciprocalGammaFactorialScale branch)⁻¹ ^ j
  have hc : Tendsto (fun _ : ℂ => c) (𝓝[≠] 0) (𝓝 c) := tendsto_const_nhds
  have h := hc.mul (tendsto_pow_succ_mul_simplePoleCovariantJetValue
    (gammaPoleRegularUnit_analyticAt_zero branch) j)
  have hev : (fun x : ℂ => x ^ (j + 1) *
      (c * simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x)) =ᶠ[𝓝[≠] 0]
      (fun x => c * (x ^ (j + 1) *
        simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x)) :=
    Filter.Eventually.of_forall fun x => by ring
  simpa only [gammaPoleRegularUnit_zero, one_mul] using
    h.congr' (hev.mono fun _ hx => hx.symm)

/-- Every normalized Gamma covariant jet has exact pole order `-(j+1)`. -/
theorem meromorphicOrderAt_gammaPoleCovariantJetValue (branch j : ℕ) :
    meromorphicOrderAt (gammaPoleCovariantJetValue branch j) 0 =
      ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (j + 1)
    (meromorphicAt_gammaPoleCovariantJetValue branch j)
  · have hscale : (-(reciprocalGammaFactorialScale branch)⁻¹ ^ j : ℂ) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _
        (inv_ne_zero (reciprocalGammaFactorialScale_ne_zero branch)))
    have hsign : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hfactorial : ((j.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    exact mul_ne_zero hscale (mul_ne_zero hsign hfactorial)
  · simpa using tendsto_pow_succ_mul_gammaPoleCovariantJetValue branch j

/-- The unique principal pole monomial of the `j`th normalized Gamma jet. -/
def gammaPoleJetPrincipalPartValue (branch j : ℕ) (x : ℂ) : ℂ :=
  -(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1)

/-- Subtracting the Gamma principal monomial leaves the explicitly scaled divided-difference jet. -/
theorem gammaPoleCovariantJetValue_sub_principal_eventuallyEq
    (branch j : ℕ) :
    (fun x : ℂ => gammaPoleCovariantJetValue branch j x -
      gammaPoleJetPrincipalPartValue branch j x) =ᶠ[𝓝[≠] 0]
      (fun x => -(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
        iteratedDeriv j (dslope (gammaPoleRegularUnit branch) 0) x) := by
  filter_upwards [simplePoleCovariantJetValue_sub_principal_eventuallyEq
    (gammaPoleRegularUnit_analyticAt_zero branch) j] with x hx
  rw [← hx]
  simp only [gammaPoleCovariantJetValue, gammaPoleJetPrincipalPartValue,
    gammaPoleRegularUnit_zero, one_mul]
  ring

/-- **Complete Gamma principal-part law.** Every normalized Gamma derivative is its single pole
monomial plus a germ analytic at the pole center. -/
theorem exists_analyticAt_gammaPoleCovariantJetValue_sub_principal
    (branch j : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      (fun x : ℂ => gammaPoleCovariantJetValue branch j x -
        gammaPoleJetPrincipalPartValue branch j x) =ᶠ[𝓝[≠] 0] R := by
  refine ⟨fun x => -(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
      iteratedDeriv j (dslope (gammaPoleRegularUnit branch) 0) x, ?_,
    gammaPoleCovariantJetValue_sub_principal_eventuallyEq branch j⟩
  exact analyticAt_const.mul (analyticAt_iteratedDeriv_of_analyticAt
    (analyticAt_dslope_zero_of_analyticAt
      (gammaPoleRegularUnit_analyticAt_zero branch)) j)

/-- **Gamma generator value relation.**  Every native Gamma derivative equals
its dynamic covariant simple-pole profile on a deleted neighborhood. -/
theorem gammaPoleJet_eventuallyEq_covariant (branch j : ℕ) :
    (fun x : ℂ => iteratedDeriv j Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) =ᶠ[𝓝[≠] 0]
      gammaPoleCovariantJetValue branch j := by
  let s := reciprocalGammaFactorialScale branch
  let F : ℂ → ℂ := fun x => Complex.Gamma (s * x + -(branch : ℂ))
  let G : ℂ → ℂ := fun x => -gammaPoleRegularUnit branch x / x
  have hsource : F =ᶠ[𝓝[≠] 0] G := by
    simpa [F, G, add_comm] using gammaPoleRegularUnit_source_eventuallyEq branch
  have hderiv := EventuallyEq.nhdsNE_iteratedDeriv hsource j
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hUevent : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      ContDiffAt ℂ j (gammaPoleRegularUnit branch) x :=
    nhdsWithin_le_nhds (hUan.eventually_analyticAt.mono fun _ hx => hx.contDiffAt)
  filter_upwards [hderiv, hUevent, self_mem_nhdsWithin] with x hDx hUx hx
  have hchain : iteratedDeriv j F x = s ^ j *
      iteratedDeriv j Complex.Gamma (s * x + -(branch : ℂ)) := by
    change iteratedDeriv j (fun x => Complex.Gamma (s * x + -(branch : ℂ))) x = _
    rw [show (fun x => Complex.Gamma (s * x + -(branch : ℂ))) =
        fun x => (fun z => Complex.Gamma (z + -(branch : ℂ))) (s * x) by rfl]
    rw [iteratedDeriv_comp_mul_left_uncond
      (fun z => Complex.Gamma (z + -(branch : ℂ))) s j x]
    rw [congrFun (iteratedDeriv_comp_add_const j Complex.Gamma (-(branch : ℂ)))
      (s * x)]
  have hG : iteratedDeriv j G x =
      -simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x := by
    have hcov := simplePoleCovariantJetValue_eq_iteratedDeriv_div hUx hx
    rw [show G = fun x => (-1 : ℂ) *
        (gammaPoleRegularUnit branch x / x) by
      funext y
      dsimp [G]
      ring]
    rw [congrFun (iteratedDeriv_const_mul_field (-1 : ℂ)
      (fun x => gammaPoleRegularUnit branch x / x) j) x, ← hcov]
    ring
  have hs : s ≠ 0 := reciprocalGammaFactorialScale_ne_zero branch
  change iteratedDeriv j Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) =
    gammaPoleCovariantJetValue branch j x
  change iteratedDeriv j Complex.Gamma (-(branch : ℂ) + s * x) = _
  rw [add_comm] at hchain ⊢
  rw [hchain, hG] at hDx
  unfold gammaPoleCovariantJetValue
  change iteratedDeriv j Complex.Gamma (s * x + -(branch : ℂ)) =
    -s⁻¹ ^ j * simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x
  have hpow : s⁻¹ ^ j * s ^ j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs, one_pow]
  have hDx' : s ^ j * iteratedDeriv j Complex.Gamma
      (s * x + -(branch : ℂ)) =
      -simplePoleCovariantJetValue (gammaPoleRegularUnit branch) j x := by
    simpa [add_comm] using hDx
  calc
    iteratedDeriv j Complex.Gamma (s * x + -(branch : ℂ)) =
        s⁻¹ ^ j * (s ^ j * iteratedDeriv j Complex.Gamma
          (s * x + -(branch : ℂ))) := by rw [← mul_assoc, hpow, one_mul]
    _ = -s⁻¹ ^ j * simplePoleCovariantJetValue
          (gammaPoleRegularUnit branch) j x := by rw [hDx']; ring

/-- **Native Gamma top-residue reflection.**  The exact dynamic residue limit
transfers through the affine Gamma value relation. -/
theorem tendsto_pow_succ_mul_gammaPoleJet_affine (branch j : ℕ) :
    Tendsto
      (fun x : ℂ => x ^ (j + 1) * iteratedDeriv j Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x))
      (𝓝[≠] 0)
      (𝓝 (-(reciprocalGammaFactorialScale branch)⁻¹ ^ j *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ)))) := by
  have hev :
      (fun x : ℂ => x ^ (j + 1) * iteratedDeriv j Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) =ᶠ[𝓝[≠] 0]
      (fun x => x ^ (j + 1) * gammaPoleCovariantJetValue branch j x) :=
    (gammaPoleJet_eventuallyEq_covariant branch j).mono fun x hx =>
      congrArg (fun y => x ^ (j + 1) * y) hx
  exact (tendsto_pow_succ_mul_gammaPoleCovariantJetValue branch j).congr'
    (hev.mono fun _ hx => hx.symm)

/-- Every native Gamma derivative in the normalized affine pole chart has
exact pole order `-(j+1)`. -/
theorem meromorphicOrderAt_gammaPoleJet_affine (branch j : ℕ) :
    meromorphicOrderAt
        (fun x : ℂ => iteratedDeriv j Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) 0 =
      ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  calc
    meromorphicOrderAt
        (fun x : ℂ => iteratedDeriv j Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) 0 =
        meromorphicOrderAt (gammaPoleCovariantJetValue branch j) 0 :=
      meromorphicOrderAt_congr (gammaPoleJet_eventuallyEq_covariant branch j)
    _ = ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_gammaPoleCovariantJetValue branch j

/-- The native affine Gamma derivative has the same complete principal part as its covariant
realization. -/
theorem exists_analyticAt_gammaPoleJet_affine_sub_principal
    (branch j : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      (fun x : ℂ => iteratedDeriv j Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
        gammaPoleJetPrincipalPartValue branch j x) =ᶠ[𝓝[≠] 0] R := by
  obtain ⟨R, hR, hcov⟩ :=
    exists_analyticAt_gammaPoleCovariantJetValue_sub_principal branch j
  refine ⟨R, hR, ?_⟩
  filter_upwards [gammaPoleJet_eventuallyEq_covariant branch j, hcov] with x hx hrem
  rw [hx]
  exact hrem

/-- After its unique principal pole monomial is removed, every native Gamma derivative has
nonnegative meromorphic order. -/
theorem meromorphicOrderAt_gammaPoleJet_affine_sub_principal_nonneg
    (branch j : ℕ) :
    0 ≤ meromorphicOrderAt
      (fun x : ℂ => iteratedDeriv j Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) -
        gammaPoleJetPrincipalPartValue branch j x) 0 := by
  obtain ⟨R, hR, hev⟩ :=
    exists_analyticAt_gammaPoleJet_affine_sub_principal branch j
  rw [meromorphicOrderAt_congr hev]
  exact hR.meromorphicOrderAt_nonneg

/-- Covariant local evaluation of a polynomial-coefficient Gamma jet packet. -/
def gammaPoleCovariantPolynomialJetEval (branch n : ℕ) (x : ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom
    (Polynomial.evalRingHom
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x))
    (fun j => gammaPoleCovariantJetValue branch (j : ℕ) x)

/-- The complete running-point Laurent packet.  Polynomial coefficients are
evaluated at the current affine coordinate, while Gamma generators retain
their finite covariant Laurent profiles. -/
def gammaPoleCovariantPolynomialJetLaurentEval (branch n : ℕ) (x : ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* LaurentPolynomial ℂ :=
  MvPolynomial.eval₂Hom
    ((LaurentPolynomial.C : ℂ →+* LaurentPolynomial ℂ).comp
      (Polynomial.evalRingHom
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)))
    (fun j => gammaPoleCovariantDerivativeLaurent branch (j : ℕ) x)

/-- **Finite Laurent packet value relation.**  Evaluation of the complete
running-point Laurent packet at `x⁻¹` is exactly the scalar covariant packet. -/
theorem eval₂_gammaPoleCovariantPolynomialJetLaurentEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
    {x : ℂ} (hx : x ≠ 0) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (puncturedInverseUnit x hx)
        (gammaPoleCovariantPolynomialJetLaurentEval branch n x P) =
      gammaPoleCovariantPolynomialJetEval branch n x P := by
  let lhs : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* ℂ :=
    (LaurentPolynomial.eval₂ (RingHom.id ℂ) (puncturedInverseUnit x hx)).comp
      (gammaPoleCovariantPolynomialJetLaurentEval branch n x)
  have hhom : lhs = gammaPoleCovariantPolynomialJetEval branch n x := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [lhs, gammaPoleCovariantPolynomialJetLaurentEval,
        gammaPoleCovariantPolynomialJetEval]
    · intro j
      simp [lhs, gammaPoleCovariantPolynomialJetLaurentEval,
        gammaPoleCovariantPolynomialJetEval,
        eval₂_gammaPoleCovariantDerivativeLaurent]
  exact RingHom.congr_fun hhom P

/-- Meromorphicity is closed under the complete covariant packet ring
interface. -/
theorem meromorphicAt_gammaPoleCovariantPolynomialJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    MeromorphicAt (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      have heq : (fun x => gammaPoleCovariantPolynomialJetEval branch n x
          (MvPolynomial.C p)) =
          fun x => p.eval
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) := by
        funext x
        simp [gammaPoleCovariantPolynomialJetEval]
      rw [heq]
      have haff : AnalyticAt ℂ
          (fun x : ℂ => -(branch : ℂ) +
            reciprocalGammaFactorialScale branch * x) 0 := by
        fun_prop
      have hp : AnalyticAt ℂ (fun z => p.eval z)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * 0) :=
        (AnalyticOnNhd.eval_polynomial p) _ (Set.mem_univ _)
      exact (AnalyticAt.comp (x := 0) (g := fun z => p.eval z)
        (f := fun x : ℂ => -(branch : ℂ) +
          reciprocalGammaFactorialScale branch * x) hp haff).meromorphicAt
  | add P Q hP hQ =>
      have heq : (fun x => gammaPoleCovariantPolynomialJetEval branch n x (P + Q)) =
          (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) +
            fun x => gammaPoleCovariantPolynomialJetEval branch n x Q := by
        funext x
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun x => gammaPoleCovariantPolynomialJetEval branch n x
          (P * MvPolynomial.X i)) =
          (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) *
            gammaPoleCovariantJetValue branch (i : ℕ) := by
        funext x
        simp [gammaPoleCovariantPolynomialJetEval]
      rw [heq]
      exact hP.mul (meromorphicAt_gammaPoleCovariantJetValue branch (i : ℕ))

/-- **Polynomial-packet value relation.**  Native evaluation of every finite
polynomial-coefficient Gamma jet packet equals its dynamic covariant profile
on a deleted neighborhood. -/
theorem gammaPolyJetEval_affine_eventuallyEq_covariant
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (fun x : ℂ => gammaPolyJetEval (n + 1)
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) =ᶠ[𝓝[≠] 0]
      (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      exact Filter.Eventually.of_forall fun x => by
        simp [gammaPolyJetEval, gammaPoleCovariantPolynomialJetEval]
  | add P Q hP hQ =>
      filter_upwards [hP, hQ] with x hxP hxQ
      simp only [map_add]
      rw [hxP, hxQ]
  | mul_X P i hP =>
      filter_upwards [hP, gammaPoleJet_eventuallyEq_covariant branch (i : ℕ)]
        with x hxP hxi
      rw [map_mul, map_mul]
      have hXnative : gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)
          (MvPolynomial.X i) =
          iteratedDeriv (i : ℕ) Complex.Gamma
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) := by
        simp [gammaPolyJetEval]
      have hXcov : gammaPoleCovariantPolynomialJetEval branch n x
          (MvPolynomial.X i) =
          gammaPoleCovariantJetValue branch (i : ℕ) x := by
        simp [gammaPoleCovariantPolynomialJetEval]
      rw [hXnative, hXcov, hxP, hxi]

/-- **Native-to-Laurent value relation.**  The native polynomial Gamma jet
packet is the evaluation at `x⁻¹` of the complete finite running-point Laurent
packet throughout a deleted neighborhood. -/
theorem gammaPolyJetEval_affine_eventuallyEq_laurentEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (fun x : ℂ => gammaPolyJetEval (n + 1)
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) =ᶠ[𝓝[≠] 0]
      (fun x => if hx : x ≠ 0 then
        LaurentPolynomial.eval₂ (RingHom.id ℂ) (puncturedInverseUnit x hx)
          (gammaPoleCovariantPolynomialJetLaurentEval branch n x P)
        else 0) := by
  filter_upwards [gammaPolyJetEval_affine_eventuallyEq_covariant branch n P,
    self_mem_nhdsWithin] with x hxvalue hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [hxvalue, dif_pos hx0,
    eval₂_gammaPoleCovariantPolynomialJetLaurentEval branch n P hx0]

/-- Native polynomial-coefficient Gamma jet packets are meromorphic at every
normalized pole center.  The covariant value relation discharges the property
without asking downstream users for generatorwise proofs. -/
theorem meromorphicAt_gammaPolyJetEval_affine
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    MeromorphicAt
      (fun x : ℂ => gammaPolyJetEval (n + 1)
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 := by
  exact (meromorphicAt_gammaPoleCovariantPolynomialJetEval branch n P).congr
    (gammaPolyJetEval_affine_eventuallyEq_covariant branch n P).symm

/-- **Native/covariant order reflection.**  The exact value relation induces
equality of meromorphic orders at the normalized pole coordinate. -/
theorem meromorphicOrderAt_gammaPolyJetEval_affine_eq_covariant
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 =
      meromorphicOrderAt
        (fun x => gammaPoleCovariantPolynomialJetEval branch n x P) 0 := by
  exact meromorphicOrderAt_congr
    (gammaPolyJetEval_affine_eventuallyEq_covariant branch n P)

end

end GaloisForLFunctions
