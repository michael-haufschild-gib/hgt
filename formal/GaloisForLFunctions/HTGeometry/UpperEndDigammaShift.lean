import GaloisForLFunctions.HTGeometry.UpperEndDifferentialField
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogCarrier
import GaloisForLFunctions.HTGeometry.UpperEndConstantField
import GaloisForLFunctions.HTGeometry.DirichletLeadingTerm
import GaloisForLFunctions.HTGeometry.ShiftJetTower
import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence
import Mathlib

/-!
# The digamma jets in the upper-end differential field

The digamma `psi = Gamma'/Gamma` is analytic on every upper half-plane, so it defines an element of
the upper-end meromorphic field, as does the coordinate reciprocal `1/s`.  The digamma difference
equation `psi(s+1) = psi(s) + 1/s` becomes a single identity between upper-end germs.

Because translation commutes with the field derivation, that one identity propagates to *all* jets:

`sigma (delta^n psi) = delta^n psi + delta^n (1/s)`.

This is the shift datum required by the jet-tower descent, obtained with no analysis beyond the
`n = 0` case.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance upperEndDigammaDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndDigammaDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

theorem isOpen_upperTail (H : ℝ) : IsOpen (upperTail H) :=
  isOpen_lt continuous_const Complex.continuous_im

theorem ne_negNat_of_mem_upperTail {z : ℂ} (hz : z ∈ upperTail 0) (n : ℕ) : z ≠ -(n : ℂ) := by
  intro h
  simp only [upperTail, mem_setOf_eq] at hz
  rw [h] at hz
  simp at hz

theorem ne_zero_of_mem_upperTail {z : ℂ} (hz : z ∈ upperTail 0) : z ≠ 0 := by
  simpa using ne_negNat_of_mem_upperTail hz 0

/-- The digamma function as a plain function. -/
def digammaFun : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z

theorem analyticOnNhd_gamma_upperTail :
    AnalyticOnNhd ℂ Complex.Gamma (upperTail 0) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_upperTail 0)
  intro z hz
  exact (Complex.differentiableAt_Gamma z (ne_negNat_of_mem_upperTail hz)).differentiableWithinAt

theorem analyticOnNhd_digamma_upperTail :
    AnalyticOnNhd ℂ digammaFun (upperTail 0) := by
  have hG := analyticOnNhd_gamma_upperTail
  have hD : AnalyticOnNhd ℂ (deriv Complex.Gamma) (upperTail 0) := fun z hz => (hG z hz).deriv
  refine AnalyticOnNhd.div hD hG ?_
  intro z hz
  exact Complex.Gamma_ne_zero (ne_negNat_of_mem_upperTail hz)

theorem analyticOnNhd_inv_upperTail :
    AnalyticOnNhd ℂ (fun z : ℂ => 1 / z) (upperTail 0) := by
  refine AnalyticOnNhd.div analyticOnNhd_const analyticOnNhd_id ?_
  intro z hz
  exact ne_zero_of_mem_upperTail hz

/-- The digamma as an upper-end analytic germ. -/
def digammaAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter digammaFun),
    ⟨digammaFun, 0, analyticOnNhd_digamma_upperTail, rfl⟩⟩

/-- The coordinate reciprocal as an upper-end analytic germ. -/
def invCoordAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z)),
    ⟨fun z : ℂ => 1 / z, 0, analyticOnNhd_inv_upperTail, rfl⟩⟩

/-- The digamma in the upper-end meromorphic field. -/
def digammaMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField digammaAnalytic

/-- The coordinate reciprocal in the upper-end meromorphic field. -/
def invCoordMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField invCoordAnalytic

/-- **The digamma difference equation, as an identity of upper-end germs.** -/
theorem upperEndTranslate_digammaAnalytic :
    upperEndTranslationAnalyticEquiv 1 digammaAnalytic
      = digammaAnalytic + invCoordAnalytic := by
  apply Subtype.ext
  change upperEndTranslateGerm 1 (Germ.coeRingHom upperEndFilter digammaFun)
    = (Germ.coeRingHom upperEndFilter digammaFun)
      + (Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z))
  have hev : ∀ᶠ z : ℂ in upperEndFilter,
      digammaFun (z + 1) = digammaFun z + 1 / z := by
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨0, trivial, fun z hz => ?_⟩
    exact digamma_recurrence z (ne_negNat_of_mem_upperTail hz)
  exact Germ.coe_eq.mpr hev

/-- The same identity in the meromorphic field. -/
theorem upperEndTranslate_digammaMero :
    upperEndTranslationMeroEquiv 1 digammaMero = digammaMero + invCoordMero := by
  rw [digammaMero, upperEndTranslationMeroEquiv_algebraMap,
    upperEndTranslate_digammaAnalytic, map_add]
  rfl

/-- The `n`-th digamma jet. -/
def digammaJetMero (n : ℕ) : upperEndMeroField := differentialJet n digammaMero

/-- The `n`-th defect. -/
def defectJetMero (n : ℕ) : upperEndMeroField := differentialJet n invCoordMero

/-- **All jets inherit the shift relation.**  Translation commutes with the derivation, so the
single `n = 0` identity propagates to every order. -/
theorem upperEndTranslate_digammaJetMero (n : ℕ) :
    upperEndTranslationMeroEquiv 1 (digammaJetMero n)
      = digammaJetMero n + defectJetMero n := by
  induction n with
  | zero => simpa [digammaJetMero, defectJetMero] using upperEndTranslate_digammaMero
  | succ n ih =>
      rw [digammaJetMero, defectJetMero, differentialJet_succ, differentialJet_succ,
        upperEndTranslationMeroEquiv_deriv]
      rw [show differentialJet n digammaMero = digammaJetMero n from rfl, ih]
      rw [show differentialJet n invCoordMero = defectJetMero n from rfl]
      exact map_add _ _ _

/-- The derivative of the coordinate reciprocal. -/
theorem upperEndAnalyticDeriv_invCoordAnalytic :
    upperEndAnalyticDeriv invCoordAnalytic = -(invCoordAnalytic * invCoordAnalytic) := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  show upperEndGermDeriv (Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z))
    = -((Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z))
        * (Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z)))
  have hev : ∀ᶠ z : ℂ in upperEndFilter,
      deriv (fun w : ℂ => 1 / w) z = -(1 / z * (1 / z)) := by
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨0, trivial, fun z hz => ?_⟩
    have hz0 : z ≠ 0 := ne_zero_of_mem_upperTail hz
    have h1 : (fun w : ℂ => 1 / w) = fun w : ℂ => w⁻¹ := by
      funext w; rw [one_div]
    rw [h1, deriv_inv]
    field_simp
  exact Germ.coe_eq.mpr hev

/-- The derivative of the coordinate reciprocal in the meromorphic field. -/
theorem deriv_invCoordMero :
    (invCoordMero)′ = -(invCoordMero * invCoordMero) := by
  rw [invCoordMero, upperEndMeroFieldDifferential_algebraMap,
    upperEndAnalyticDeriv_invCoordAnalytic, map_neg, map_mul]

/-- The `n`-th derivative of the coordinate reciprocal, as a function. -/
def invPowFun (n : ℕ) : ℂ → ℂ :=
  fun z => ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (z ^ (n + 1))⁻¹

theorem invPowFun_zero : invPowFun 0 = fun z : ℂ => 1 / z := by
  funext z; simp [invPowFun]

theorem deriv_invPowFun (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    deriv (invPowFun n) z = invPowFun (n + 1) z := by
  have hpow : (z : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hz
  have hd : HasDerivAt (fun w : ℂ => w ^ (n + 1)) ((n + 1 : ℕ) * z ^ n) z := by
    simpa using (hasDerivAt_pow (n + 1) z)
  have hinv : HasDerivAt (fun w : ℂ => (w ^ (n + 1))⁻¹)
      (-((n + 1 : ℕ) * z ^ n) / (z ^ (n + 1)) ^ 2) z := hd.inv hpow
  have hfull : HasDerivAt (invPowFun n)
      (((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        (-((n + 1 : ℕ) * z ^ n) / (z ^ (n + 1)) ^ 2)) z :=
    hinv.const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
  rw [hfull.deriv]
  show _ = ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ)) * (z ^ (n + 1 + 1))⁻¹
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem analyticOnNhd_invPowFun (n : ℕ) :
    AnalyticOnNhd ℂ (invPowFun n) (upperTail 0) := by
  refine AnalyticOnNhd.mul analyticOnNhd_const (AnalyticOnNhd.inv (analyticOnNhd_id.pow _) ?_)
  intro z hz
  exact pow_ne_zero _ (ne_zero_of_mem_upperTail hz)

/-- The `n`-th defect as an upper-end analytic germ. -/
def invPowAnalytic (n : ℕ) : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter (invPowFun n)),
    ⟨invPowFun n, 0, analyticOnNhd_invPowFun n, rfl⟩⟩

theorem invPowAnalytic_zero : invPowAnalytic 0 = invCoordAnalytic := by
  apply Subtype.ext
  change (Germ.coeRingHom upperEndFilter (invPowFun 0))
    = (Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z))
  rw [invPowFun_zero]

theorem upperEndAnalyticDeriv_invPowAnalytic (n : ℕ) :
    upperEndAnalyticDeriv (invPowAnalytic n) = invPowAnalytic (n + 1) := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  show upperEndGermDeriv (Germ.coeRingHom upperEndFilter (invPowFun n))
    = (Germ.coeRingHom upperEndFilter (invPowFun (n + 1)))
  have hev : ∀ᶠ z : ℂ in upperEndFilter, deriv (invPowFun n) z = invPowFun (n + 1) z := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨0, trivial, fun z hz => deriv_invPowFun n (ne_zero_of_mem_upperTail hz)⟩
  exact Germ.coe_eq.mpr hev

/-- **The defect jets are the explicit reciprocal powers.** -/
theorem defectJetMero_eq (n : ℕ) :
    defectJetMero n =
      algebraMap upperEndAnalyticSubring upperEndMeroField (invPowAnalytic n) := by
  induction n with
  | zero => rw [defectJetMero, differentialJet_zero, invPowAnalytic_zero, invCoordMero]
  | succ n ih =>
      rw [defectJetMero, differentialJet_succ,
        show differentialJet n invCoordMero = defectJetMero n from rfl, ih,
        upperEndMeroFieldDifferential_algebraMap, upperEndAnalyticDeriv_invPowAnalytic]

/-- The coordinate as an upper-end analytic germ. -/
def coordAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter (fun z : ℂ => z)),
    ⟨fun z : ℂ => z, 0, analyticOnNhd_id, rfl⟩⟩

/-- The coordinate in the upper-end meromorphic field. -/
def coordMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField coordAnalytic

/-- **The coordinate reciprocal inverts the coordinate.** -/
theorem invCoordAnalytic_mul_coordAnalytic :
    invCoordAnalytic * coordAnalytic = 1 := by
  apply Subtype.ext
  change (Germ.coeRingHom upperEndFilter (fun z : ℂ => 1 / z))
      * (Germ.coeRingHom upperEndFilter (fun z : ℂ => z)) = 1
  rw [← map_mul]
  have hev : ∀ᶠ z : ℂ in upperEndFilter, (fun z : ℂ => 1 / z) z * (fun z : ℂ => z) z = 1 := by
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨0, trivial, fun z hz => ?_⟩
    field_simp [ne_zero_of_mem_upperTail hz]
  exact Germ.coe_eq.mpr hev

theorem invCoordMero_mul_coordMero : invCoordMero * coordMero = 1 := by
  rw [invCoordMero, coordMero, ← map_mul, invCoordAnalytic_mul_coordAnalytic, map_one]

/-- **The defect jets scaled by a power of the coordinate are constants.**  This is the form used to
prove that the defects are linearly independent: a dependence relation becomes a polynomial identity
in the coordinate. -/
theorem defectJetMero_mul_coordMero_pow (n : ℕ) :
    defectJetMero n * coordMero ^ (n + 1)
      = (-1 : upperEndMeroField) ^ n * (n.factorial : upperEndMeroField) := by
  rw [defectJetMero_eq, coordMero, ← map_pow, ← map_mul]
  have hmul : invPowAnalytic n * coordAnalytic ^ (n + 1)
      = (-1 : upperEndAnalyticSubring) ^ n * (n.factorial : upperEndAnalyticSubring) := by
    apply Subtype.ext
    push_cast
    change (Germ.coeRingHom upperEndFilter (invPowFun n))
        * ((Germ.coeRingHom upperEndFilter (fun z : ℂ => z)) ^ (n + 1))
      = ((-1 : Germ upperEndFilter ℂ) ^ n * (n.factorial : Germ upperEndFilter ℂ))
    rw [← map_pow, ← map_mul]
    have hev : ∀ᶠ z : ℂ in upperEndFilter,
        invPowFun n z * (fun z : ℂ => z) z ^ (n + 1)
          = ((-1 : ℂ) ^ n * (n.factorial : ℂ)) := by
      rw [upperEndFilter_basis.eventually_iff]
      refine ⟨0, trivial, fun z hz => ?_⟩
      have hz0 : z ≠ 0 := ne_zero_of_mem_upperTail hz
      rw [invPowFun]
      field_simp
    calc (Germ.coeRingHom upperEndFilter
            (fun z : ℂ => invPowFun n z * (fun z : ℂ => z) z ^ (n + 1)))
        = (Germ.coeRingHom upperEndFilter
            (fun _ : ℂ => ((-1 : ℂ) ^ n * (n.factorial : ℂ)))) := Germ.coe_eq.mpr hev
      _ = ((-1 : Germ upperEndFilter ℂ) ^ n * (n.factorial : Germ upperEndFilter ℂ)) := by
          push_cast
          rfl
  rw [hmul]
  push_cast
  rfl

/-- **Closed form for the defect jets.**  Each defect is a nonzero constant multiple of a power of
the coordinate reciprocal. -/
theorem defectJetMero_eq_smul_pow (n : ℕ) :
    defectJetMero n
      = (-1 : upperEndMeroField) ^ n * (n.factorial : upperEndMeroField)
        * invCoordMero ^ (n + 1) := by
  have hmul := defectJetMero_mul_coordMero_pow n
  have hinv : invCoordMero ^ (n + 1) * coordMero ^ (n + 1) = 1 := by
    rw [← mul_pow, invCoordMero_mul_coordMero, one_pow]
  calc defectJetMero n
      = defectJetMero n * (coordMero ^ (n + 1) * invCoordMero ^ (n + 1)) := by
        rw [mul_comm (coordMero ^ (n + 1)), hinv, mul_one]
    _ = (defectJetMero n * coordMero ^ (n + 1)) * invCoordMero ^ (n + 1) := by ring
    _ = (-1 : upperEndMeroField) ^ n * (n.factorial : upperEndMeroField)
          * invCoordMero ^ (n + 1) := by rw [hmul]

/-- Every upper half-plane is infinite. -/
theorem infinite_upperTail (H : ℝ) : (upperTail H).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => Complex.I * (((H + n + 1 : ℝ)) : ℂ)) ?_ ?_
  · intro a b hab
    have him : (H + a + 1 : ℝ) = (H + b + 1 : ℝ) := by
      have := congrArg Complex.im hab
      simpa using this
    have : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast this
  · intro n
    show H < (Complex.I * (((H + n + 1 : ℝ)) : ℂ)).im
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, add_zero]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

section Independence

local instance upperEndDigammaComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

theorem coordAnalytic_eq_polyX : coordAnalytic = upperEndPolyToAnalytic Polynomial.X := by
  apply Subtype.ext
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  simp

theorem coordMero_eq_polyX : coordMero = upperEndPolyToMero Polynomial.X := by
  rw [coordMero, coordAnalytic_eq_polyX]
  rfl

/-- Evaluating a complex polynomial at the coordinate is the corpus polynomial realisation. -/
theorem aeval_coordMero_eq (P : Polynomial ℂ) :
    Polynomial.aeval coordMero P = upperEndPolyToMero P := by
  have hext : ((Polynomial.aeval coordMero : Polynomial ℂ →ₐ[ℂ] upperEndMeroField).toRingHom)
      = upperEndPolyToMero := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.aeval coordMero (Polynomial.C a) = upperEndPolyToMero (Polynomial.C a)
      rw [Polynomial.aeval_C]
      show upperEndComplexToMero a = _
      rw [upperEndPolyToMero]
      rfl
    · show Polynomial.aeval coordMero Polynomial.X = upperEndPolyToMero Polynomial.X
      rw [Polynomial.aeval_X, coordMero_eq_polyX]
  exact congrArg (fun f : Polynomial ℂ →+* upperEndMeroField => f P) hext

/-- **The coordinate is transcendental over the constants.** -/
theorem transcendental_coordMero : Transcendental ℂ coordMero := by
  rintro ⟨P, hPne, hP⟩
  refine hPne (upperEndPolyToMero_injective ?_)
  rw [map_zero, ← aeval_coordMero_eq P]
  exact hP

/-- The defect constants, as complex numbers. -/
def defectConst (n : ℕ) : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)

theorem defectConst_ne_zero (n : ℕ) : defectConst n ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  exact_mod_cast Nat.factorial_ne_zero n

theorem defectJetMero_mul_pow_eq_const (n : ℕ) :
    defectJetMero n * coordMero ^ (n + 1)
      = algebraMap ℂ upperEndMeroField (defectConst n) := by
  rw [defectJetMero_mul_coordMero_pow, defectConst, map_mul, map_pow, map_neg, map_one,
    map_natCast]

/-- **The defects are linearly independent over the constants.**  A dependence relation, multiplied
by `s ^ (n+1)`, becomes a polynomial identity in the coordinate with nonzero constant term. -/
theorem defectJetMero_not_mem_span (n : ℕ) :
    defectJetMero n ∉ Submodule.span ℂ (defectJetMero '' Set.Iio n) := by
  classical
  intro hmem
  set Q : upperEndMeroField → Prop := fun x =>
    ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧
      x * coordMero ^ (n + 1) = Polynomial.aeval coordMero p with hQ
  have hspan : Q (defectJetMero n) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨k, hk, rfl⟩
      refine ⟨Polynomial.C (defectConst k) * Polynomial.X ^ (n - k), ?_, ?_⟩
      · have hnk : n - k ≠ 0 := by
          simp only [Set.mem_Iio] at hk
          omega
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hnk]
      · simp only [Set.mem_Iio] at hk
        have hsplit : (n : ℕ) + 1 = (k + 1) + (n - k) := by omega
        rw [hsplit, pow_add, ← mul_assoc, defectJetMero_mul_pow_eq_const]
        simp [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    · exact ⟨0, by simp, by simp⟩
    · rintro x y - - ⟨px, hpx0, hpx⟩ ⟨py, hpy0, hpy⟩
      exact ⟨px + py, by simp [hpx0, hpy0], by rw [add_mul, hpx, hpy, map_add]⟩
    · rintro a x - ⟨px, hpx0, hpx⟩
      refine ⟨Polynomial.C a * px, by simp [hpx0], ?_⟩
      rw [Algebra.smul_def, mul_assoc, hpx, map_mul, Polynomial.aeval_C]
  obtain ⟨p, hp0, hp⟩ := hspan
  rw [defectJetMero_mul_pow_eq_const] at hp
  have hne : p - Polynomial.C (defectConst n) ≠ 0 := by
    intro h0
    have := congrArg (fun q : Polynomial ℂ => q.coeff 0) h0
    simp [hp0] at this
    exact defectConst_ne_zero n this
  refine transcendental_coordMero ⟨p - Polynomial.C (defectConst n), hne, ?_⟩
  rw [map_sub, ← hp, Polynomial.aeval_C, sub_self]

/-- The rational base field: the constants with the coordinate adjoined. -/
def ratBase : IntermediateField ℂ upperEndMeroField := IntermediateField.adjoin ℂ {coordMero}

theorem coordMero_mem_ratBase : coordMero ∈ ratBase :=
  IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

theorem coordMero_ne_zero : coordMero ≠ 0 := by
  intro h
  have := invCoordMero_mul_coordMero
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem invCoordMero_eq_inv : invCoordMero = coordMero⁻¹ :=
  eq_inv_of_mul_eq_one_left invCoordMero_mul_coordMero

theorem invCoordMero_mem_ratBase : invCoordMero ∈ ratBase := by
  rw [invCoordMero_eq_inv]
  exact inv_mem coordMero_mem_ratBase

theorem defectJetMero_mem_ratBase (n : ℕ) : defectJetMero n ∈ ratBase := by
  rw [defectJetMero_eq_smul_pow]
  refine mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) n) ?_)
    (pow_mem invCoordMero_mem_ratBase _)
  exact natCast_mem _ _

/-- **Translation shifts the coordinate by one.** -/
theorem upperEndTranslate_coordMero :
    upperEndTranslationMeroEquiv 1 coordMero = coordMero + 1 := by
  have hA : upperEndTranslationAnalyticEquiv 1 coordAnalytic = coordAnalytic + 1 := by
    apply Subtype.ext
    change upperEndTranslateGerm 1 (Germ.coeRingHom upperEndFilter (fun z : ℂ => z))
      = (Germ.coeRingHom upperEndFilter (fun z : ℂ => z)) + 1
    have h1 : (1 : Germ upperEndFilter ℂ) = Germ.coeRingHom upperEndFilter (fun _ : ℂ => (1 : ℂ)) :=
      rfl
    rw [h1, ← map_add]
    exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)
  rw [coordMero, upperEndTranslationMeroEquiv_algebraMap, hA, map_add, map_one]

theorem upperEndTranslate_algebraMap_complex (a : ℂ) :
    upperEndTranslationMeroEquiv 1 (algebraMap ℂ upperEndMeroField a)
      = algebraMap ℂ upperEndMeroField a := by
  have hdef : (algebraMap ℂ upperEndMeroField a)
      = algebraMap upperEndAnalyticSubring upperEndMeroField
          (upperEndPolyToAnalytic (Polynomial.C a)) := rfl
  rw [hdef, upperEndTranslationMeroEquiv_algebraMap]
  congr 1
  apply Subtype.ext
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  simp

theorem upperEndTranslate_symm_coordMero :
    (upperEndTranslationMeroEquiv 1).symm coordMero = coordMero - 1 := by
  have h : (upperEndTranslationMeroEquiv 1).symm
      (upperEndTranslationMeroEquiv 1 coordMero) = coordMero :=
    (upperEndTranslationMeroEquiv 1).symm_apply_apply coordMero
  rw [upperEndTranslate_coordMero] at h
  have hadd : (upperEndTranslationMeroEquiv 1).symm (coordMero + 1)
      = (upperEndTranslationMeroEquiv 1).symm coordMero
        + (upperEndTranslationMeroEquiv 1).symm 1 :=
    (upperEndTranslationMeroEquiv 1).symm.map_add coordMero 1
  rw [hadd, (upperEndTranslationMeroEquiv 1).symm.map_one] at h
  linear_combination h

theorem ratBase_map_mem (phi : upperEndMeroField ≃+* upperEndMeroField)
    (hphiC : ∀ a : ℂ, phi (algebraMap ℂ upperEndMeroField a) = algebraMap ℂ upperEndMeroField a)
    (hphix : phi coordMero ∈ ratBase) :
    ∀ t ∈ ratBase, phi t ∈ ratBase := by
  intro t ht
  refine IntermediateField.adjoin_induction (F := ℂ)
    (p := fun z _ => phi z ∈ ratBase) ?_ ?_ ?_ ?_ ?_ ht
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hphix
  · intro a
    rw [hphiC a]
    exact ratBase.algebraMap_mem a
  · intro p q _ _ hp hq
    rw [phi.map_add]; exact add_mem hp hq
  · intro p _ hp
    rw [map_inv₀ phi]; exact inv_mem hp
  · intro p q _ _ hp hq
    rw [phi.map_mul]; exact mul_mem hp hq

/-- **The rational base is stable under translation.** -/
theorem ratBase_stable (u : upperEndMeroField) :
    upperEndTranslationMeroEquiv 1 u ∈ ratBase ↔ u ∈ ratBase := by
  have hfwd := ratBase_map_mem (upperEndTranslationMeroEquiv 1)
    upperEndTranslate_algebraMap_complex
    (by rw [upperEndTranslate_coordMero]; exact add_mem coordMero_mem_ratBase (one_mem _))
  have hbwd := ratBase_map_mem (upperEndTranslationMeroEquiv 1).symm
    (fun a => by
      have h := upperEndTranslate_algebraMap_complex a
      exact (RingEquiv.symm_apply_eq _).mpr h.symm)
    (by rw [upperEndTranslate_symm_coordMero]
        exact sub_mem coordMero_mem_ratBase (one_mem _))
  refine ⟨fun hu => ?_, fun hu => hfwd u hu⟩
  have := hbwd _ hu
  rwa [(upperEndTranslationMeroEquiv 1).symm_apply_apply] at this

/-- **Translation acts on polynomial values by shifting the variable.** -/
theorem upperEndTranslate_aeval_coordMero (P : Polynomial ℂ) :
    upperEndTranslationMeroEquiv 1 (Polynomial.aeval coordMero P)
      = Polynomial.aeval coordMero (P.comp (Polynomial.X + Polynomial.C 1)) := by
  have hext :
      ((upperEndTranslationMeroEquiv 1).toRingHom.comp
        (Polynomial.aeval coordMero : Polynomial ℂ →ₐ[ℂ] upperEndMeroField).toRingHom)
      = ((Polynomial.aeval coordMero : Polynomial ℂ →ₐ[ℂ] upperEndMeroField).toRingHom.comp
          (Polynomial.aeval (Polynomial.X + Polynomial.C 1)
            : Polynomial ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show upperEndTranslationMeroEquiv 1 (Polynomial.aeval coordMero (Polynomial.C a))
        = Polynomial.aeval coordMero
            (Polynomial.aeval (Polynomial.X + Polynomial.C 1) (Polynomial.C a))
      simp only [Polynomial.aeval_C, Algebra.algebraMap_self_apply, Polynomial.aeval_C]
      rw [show ((algebraMap ℂ (Polynomial ℂ)) a) = Polynomial.C a from rfl,
        Polynomial.aeval_C]
      exact upperEndTranslate_algebraMap_complex a
    · show upperEndTranslationMeroEquiv 1 (Polynomial.aeval coordMero Polynomial.X)
        = Polynomial.aeval coordMero
            (Polynomial.aeval (Polynomial.X + Polynomial.C 1) Polynomial.X)
      rw [Polynomial.aeval_X, Polynomial.aeval_X, upperEndTranslate_coordMero]
      rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
      simp
  have := congrArg (fun f : Polynomial ℂ →+* upperEndMeroField => f P) hext
  simpa [Polynomial.comp_eq_aeval] using this

theorem aeval_coordMero_injective :
    Function.Injective (fun P : Polynomial ℂ => Polynomial.aeval coordMero P) := by
  intro P Q h
  by_contra hne
  refine transcendental_coordMero ⟨P - Q, sub_ne_zero.mpr hne, ?_⟩
  simp only [map_sub]
  simp only at h
  rw [h, sub_self]

/-- **Translation-invariant elements of the rational base are constants.** -/
theorem ratBase_fixed_const (u : upperEndMeroField) (hu : u ∈ ratBase)
    (hfix : upperEndTranslationMeroEquiv 1 u = u) :
    ∃ a : ℂ, u = algebraMap ℂ upperEndMeroField a := by
  classical
  obtain ⟨N, D, hND⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ u).mp hu
  rcases eq_or_ne D 0 with rfl | hD0
  · exact ⟨0, by simpa using hND⟩
  have hDK : Polynomial.aeval coordMero D ≠ 0 := fun h =>
    hD0 (aeval_coordMero_injective (by simpa using h))
  have hNK : Polynomial.aeval coordMero (N.comp (Polynomial.X + Polynomial.C 1))
      * Polynomial.aeval coordMero D
      = Polynomial.aeval coordMero N
        * Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1)) := by
    have hDsK : Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1)) ≠ 0 := by
      intro h
      have hz : upperEndTranslationMeroEquiv 1 (Polynomial.aeval coordMero D) = 0 := by
        rw [upperEndTranslate_aeval_coordMero]; exact h
      exact hDK ((upperEndTranslationMeroEquiv 1).map_eq_zero_iff.mp hz)
    have hsu : upperEndTranslationMeroEquiv 1 u
        = Polynomial.aeval coordMero (N.comp (Polynomial.X + Polynomial.C 1))
          / Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1)) := by
      rw [hND, map_div₀, upperEndTranslate_aeval_coordMero, upperEndTranslate_aeval_coordMero]
    rw [hsu, hND] at hfix
    field_simp at hfix
    linear_combination hfix
  have hpoly : (N.comp (Polynomial.X + Polynomial.C 1)) * D
      = N * (D.comp (Polynomial.X + Polynomial.C 1)) := by
    apply aeval_coordMero_injective
    simpa using hNK
  simp only [Polynomial.C_1] at hpoly
  obtain ⟨a, ha⟩ := _root_.HTGeometry.eq_const_mul_of_shift_ratio_fixed hD0 hpoly
  refine ⟨a, ?_⟩
  rw [hND, ha, map_mul, Polynomial.aeval_C]
  field_simp

/-- Every element of the defect span is `q(s)/s^m` with `deg q < m`. -/
theorem defectSpan_shape {v : upperEndMeroField}
    (hv : v ∈ Submodule.span ℂ (Set.range defectJetMero)) :
    ∃ (m : ℕ) (q : Polynomial ℂ), q.natDegree < m ∧
      v * coordMero ^ m = Polynomial.aeval coordMero q := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨k, rfl⟩
    refine ⟨k + 1, Polynomial.C (defectConst k), ?_, ?_⟩
    · simp
    · rw [defectJetMero_mul_pow_eq_const, Polynomial.aeval_C]
  · exact ⟨1, 0, by simp, by simp⟩
  · rintro x y - - ⟨m1, q1, hq1, hx⟩ ⟨m2, q2, hq2, hy⟩
    refine ⟨max m1 m2, q1 * Polynomial.X ^ (max m1 m2 - m1)
      + q2 * Polynomial.X ^ (max m1 m2 - m2), ?_, ?_⟩
    · refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      refine max_lt ?_ ?_
      · refine lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
        rw [Polynomial.natDegree_X_pow]
        have := le_max_left m1 m2
        omega
      · refine lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_
        rw [Polynomial.natDegree_X_pow]
        have := le_max_right m1 m2
        omega
    · have h1 : max m1 m2 = m1 + (max m1 m2 - m1) := by have := le_max_left m1 m2; omega
      have h2 : max m1 m2 = m2 + (max m1 m2 - m2) := by have := le_max_right m1 m2; omega
      rw [map_add, map_mul, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X_pow,
        ← hx, ← hy, add_mul]
      rw [show coordMero ^ max m1 m2 = coordMero ^ m1 * coordMero ^ (max m1 m2 - m1) by
        rw [← pow_add, ← h1]]
      nth_rewrite 2 [show coordMero ^ m1 * coordMero ^ (max m1 m2 - m1)
        = coordMero ^ m2 * coordMero ^ (max m1 m2 - m2) by
        rw [← pow_add, ← pow_add, ← h1, ← h2]]
      ring
  · rintro a x - ⟨m, q, hq, hx⟩
    refine ⟨m, Polynomial.C a * q, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_trans Polynomial.natDegree_mul_le (by simp)) hq
    · rw [map_mul, Polynomial.aeval_C, ← hx, Algebra.smul_def]
      ring

/-- **No nonzero defect is a shift defect of the rational base.** -/
theorem ratBase_defect_eq_zero (u : upperEndMeroField) (hu : u ∈ ratBase)
    (v : upperEndMeroField) (hv : v ∈ Submodule.span ℂ (Set.range defectJetMero))
    (hduv : upperEndTranslationMeroEquiv 1 u - u = v) :
    v = 0 := by
  classical
  obtain ⟨m, q, hqdeg, hvq⟩ := defectSpan_shape hv
  obtain ⟨N, D, hND⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ u).mp hu
  have hcm : coordMero ^ m ≠ 0 := pow_ne_zero _ coordMero_ne_zero
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [show u = 0 by simpa using hND] at hduv
    simp at hduv
    exact hduv.symm
  rcases eq_or_ne N 0 with rfl | hN0
  · rw [show u = 0 by simpa using hND] at hduv
    simp at hduv
    exact hduv.symm
  have hDK : Polynomial.aeval coordMero D ≠ 0 := fun h =>
    hD0 (aeval_coordMero_injective (by simpa using h))
  have hDsK : Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1)) ≠ 0 := by
    intro h
    have hz : upperEndTranslationMeroEquiv 1 (Polynomial.aeval coordMero D) = 0 := by
      rw [upperEndTranslate_aeval_coordMero]; exact h
    exact hDK ((upperEndTranslationMeroEquiv 1).map_eq_zero_iff.mp hz)
  have hsu : upperEndTranslationMeroEquiv 1 u
      = Polynomial.aeval coordMero (N.comp (Polynomial.X + Polynomial.C 1))
        / Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1)) := by
    rw [hND, map_div₀, upperEndTranslate_aeval_coordMero, upperEndTranslate_aeval_coordMero]
  rw [hsu, hND] at hduv
  have hfield : Polynomial.aeval coordMero
        ((N.comp (Polynomial.X + Polynomial.C 1) * D
          - N * D.comp (Polynomial.X + Polynomial.C 1)) * Polynomial.X ^ m)
      = Polynomial.aeval coordMero
          (q * (D.comp (Polynomial.X + Polynomial.C 1) * D)) := by
    simp only [map_mul, map_sub, Polynomial.aeval_X_pow]
    have hvv : v = Polynomial.aeval coordMero
        (N.comp (Polynomial.X + Polynomial.C 1)) *
          Polynomial.aeval coordMero D
        / (Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1))
            * Polynomial.aeval coordMero D)
        - Polynomial.aeval coordMero N *
          Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1))
        / (Polynomial.aeval coordMero (D.comp (Polynomial.X + Polynomial.C 1))
            * Polynomial.aeval coordMero D) := by
      rw [← hduv]; field_simp
    rw [hvv] at hvq
    field_simp at hvq
    linear_combination hvq
  have hpoly : (N.comp (Polynomial.X + Polynomial.C 1) * D
      - N * D.comp (Polynomial.X + Polynomial.C 1)) * Polynomial.X ^ m
      = q * (D.comp (Polynomial.X + Polynomial.C 1) * D) :=
    aeval_coordMero_injective hfield
  simp only [Polynomial.C_1] at hpoly
  have hq0 : q = 0 := by
    by_contra hqne
    obtain ⟨A', B', hmon, hcop, hid'⟩ :=
      _root_.HTGeometry.exists_coprime_monic_shift_identity (rd := Polynomial.X ^ m) (rn := q)
        hN0 hD0 hpoly
    exact _root_.HTGeometry.no_rational_shift_antiderivative hmon hcop hqne hqdeg hid'
  rw [hq0, map_zero] at hvq
  exact (mul_eq_zero.mp hvq).resolve_right hcm

/-- Translation as a `C`-algebra automorphism of the upper-end field. -/
def translationAlgEquiv : upperEndMeroField ≃ₐ[ℂ] upperEndMeroField :=
  AlgEquiv.ofRingEquiv (f := upperEndTranslationMeroEquiv 1)
    (fun a => upperEndTranslate_algebraMap_complex a)

/-- **Hölder's theorem at the upper-end carrier.**  Every digamma jet is transcendental over the
field generated by `C(s)` and its predecessors: `psi` satisfies no algebraic differential equation
with rational coefficients. -/
theorem digamma_jets_transcendental (n : ℕ) :
    Transcendental
      (_root_.HTGeometry.jetTower ratBase digammaJetMero n) (digammaJetMero n) :=
  _root_.HTGeometry.jetTower_transcendental translationAlgEquiv ratBase
    digammaJetMero defectJetMero
    ratBase_stable defectJetMero_mem_ratBase upperEndTranslate_digammaJetMero
    ratBase_fixed_const ratBase_defect_eq_zero defectJetMero_not_mem_span n

theorem upperEndTranslationMeroEquiv_zero (x : upperEndMeroField) :
    upperEndTranslationMeroEquiv 0 x = x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective upperEndAnalyticSubring x
  rw [map_div₀, upperEndTranslationMeroEquiv_algebraMap,
    upperEndTranslationMeroEquiv_algebraMap]
  congr 2 <;> (apply Subtype.ext; exact upperEndTranslateGerm_zero _)

/-- The enlarged base: the constants with the coordinate and every finite-abscissa Dirichlet germ
adjoined. -/
def zetaBase : IntermediateField ℂ upperEndMeroField :=
  IntermediateField.adjoin ℂ
    ({coordMero} ∪ Set.range finiteAbscissaLSeriesToUpperEndMero)

theorem coordMero_mem_zetaBase : coordMero ∈ zetaBase :=
  IntermediateField.subset_adjoin _ _ (Or.inl (Set.mem_singleton _))

theorem lseries_mem_zetaBase (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndMero f ∈ zetaBase :=
  IntermediateField.subset_adjoin _ _ (Or.inr ⟨f, rfl⟩)

theorem ratBase_le_zetaBase : ratBase ≤ zetaBase := by
  rw [ratBase]
  exact IntermediateField.adjoin_le_iff.mpr (by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact coordMero_mem_zetaBase)

theorem defectJetMero_mem_zetaBase (n : ℕ) : defectJetMero n ∈ zetaBase :=
  ratBase_le_zetaBase (defectJetMero_mem_ratBase n)

theorem zetaBase_map_mem (phi : upperEndMeroField ≃+* upperEndMeroField)
    (hphiC : ∀ a : ℂ, phi (algebraMap ℂ upperEndMeroField a) = algebraMap ℂ upperEndMeroField a)
    (hphix : phi coordMero ∈ zetaBase)
    (hphiL : ∀ f : finiteAbscissaArithmeticSubalgebra,
      phi (finiteAbscissaLSeriesToUpperEndMero f) ∈ zetaBase) :
    ∀ t ∈ zetaBase, phi t ∈ zetaBase := by
  intro t ht
  refine IntermediateField.adjoin_induction (F := ℂ)
    (p := fun z _ => phi z ∈ zetaBase) ?_ ?_ ?_ ?_ ?_ ht
  · rintro z (hz | ⟨f, rfl⟩)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hphix
    · exact hphiL f
  · intro a
    rw [hphiC a]
    exact zetaBase.algebraMap_mem a
  · intro p q _ _ hp hq
    rw [phi.map_add]; exact add_mem hp hq
  · intro p _ hp
    rw [map_inv₀ phi]; exact inv_mem hp
  · intro p q _ _ hp hq
    rw [phi.map_mul]; exact mul_mem hp hq

/-- **The enlarged base is stable under translation.**  The coefficient-side Dirichlet shift
realises the meromorphic translation, so the Dirichlet germs are permuted among themselves. -/
theorem zetaBase_stable (u : upperEndMeroField) :
    upperEndTranslationMeroEquiv 1 u ∈ zetaBase ↔ u ∈ zetaBase := by
  have hI : Complex.I * (-Complex.I) = 1 := by
    simp [Complex.I_mul_I]
  have hI' : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hfwdL : ∀ f : finiteAbscissaArithmeticSubalgebra,
      upperEndTranslationMeroEquiv 1 (finiteAbscissaLSeriesToUpperEndMero f) ∈ zetaBase := by
    intro f
    have h := finiteAbscissaLSeriesToUpperEndMero_dirichletShift (-Complex.I) f
    rw [hI] at h
    rw [← h]
    exact lseries_mem_zetaBase _
  have hbwdL : ∀ f : finiteAbscissaArithmeticSubalgebra,
      (upperEndTranslationMeroEquiv 1).symm (finiteAbscissaLSeriesToUpperEndMero f)
        ∈ zetaBase := by
    intro f
    have h := finiteAbscissaLSeriesToUpperEndMero_dirichletShift Complex.I f
    have hneg : Complex.I * Complex.I = -1 := hI'
    rw [hneg] at h
    have : upperEndTranslationMeroEquiv 1
        (finiteAbscissaLSeriesToUpperEndMero (finiteAbscissaDirichletShift Complex.I f))
        = finiteAbscissaLSeriesToUpperEndMero f := by
      rw [h, upperEndTranslationMeroEquiv_add]
      norm_num
      exact upperEndTranslationMeroEquiv_zero _
    rw [← this, (upperEndTranslationMeroEquiv 1).symm_apply_apply]
    exact lseries_mem_zetaBase _
  constructor
  · intro hu
    have hbwd := zetaBase_map_mem (upperEndTranslationMeroEquiv 1).symm
      (fun a => (RingEquiv.symm_apply_eq _).mpr (upperEndTranslate_algebraMap_complex a).symm)
      (by rw [upperEndTranslate_symm_coordMero]
          exact sub_mem coordMero_mem_zetaBase (one_mem _))
      hbwdL
    have := hbwd _ hu
    rwa [(upperEndTranslationMeroEquiv 1).symm_apply_apply] at this
  · intro hu
    exact zetaBase_map_mem (upperEndTranslationMeroEquiv 1)
      upperEndTranslate_algebraMap_complex
      (by rw [upperEndTranslate_coordMero]; exact add_mem coordMero_mem_zetaBase (one_mem _))
      hfwdL u hu

end Independence

end

end GaloisForLFunctions.HTGeometry
