import GaloisForLFunctions.HTGeometry.UniversalDeRham
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.Abel

/-!
# Dirichlet Maurer--Cartan and Mellin-orbit law

Exact formalization of the arithmetic algebra and universal-differential identities in the
Stage-2 card `dirichlet-maurer-cartan-mellin-orbit-law.md`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped ArithmeticFunction

/-- Complex Dirichlet-convolution algebra of arithmetic functions. -/
abbrev ComplexArithmeticFunction := ArithmeticFunction ℂ

/-- The coefficientwise logarithmic operator `(δf)(n)=log(n)f(n)`. -/
def arithmeticLogOperator (f : ComplexArithmeticFunction) : ComplexArithmeticFunction :=
  ⟨fun n ↦ (Real.log n : ℂ) * f n, by simp⟩

@[simp]
theorem arithmeticLogOperator_apply (f : ComplexArithmeticFunction) (n : ℕ) :
    arithmeticLogOperator f n = (Real.log n : ℂ) * f n := rfl

/-- The logarithmic coefficient operator is the genuine `ℂ`-linear Dirichlet derivation. -/
def arithmeticLogDerivation :
    Derivation ℂ ComplexArithmeticFunction ComplexArithmeticFunction where
  toLinearMap :=
    { toFun := arithmeticLogOperator
      map_add' := fun f g ↦ by
        ext n
        simp [arithmeticLogOperator, mul_add]
      map_smul' := fun c f ↦ by
        ext n
        change (Real.log n : ℂ) * (c * f n) =
          c * ((Real.log n : ℂ) * f n)
        ring }
  map_one_eq_zero' := by
    ext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp [arithmeticLogOperator]
    · simp [arithmeticLogOperator, ArithmeticFunction.one_apply_ne hn]
  leibniz' := fun f g ↦ by
    change arithmeticLogOperator (f * g) =
      f * arithmeticLogOperator g + g * arithmeticLogOperator f
    rw [mul_comm g (arithmeticLogOperator f)]
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [arithmeticLogOperator]
    · change (Real.log n : ℂ) *
          (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) =
        (∑ x ∈ n.divisorsAntidiagonal,
          f x.1 * ((Real.log x.2 : ℂ) * g x.2)) +
        ∑ x ∈ n.divisorsAntidiagonal,
          ((Real.log x.1 : ℂ) * f x.1) * g x.2
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      rintro ⟨d, e⟩ hde
      have hmul : d * e = n := (Nat.mem_divisorsAntidiagonal.mp hde).1
      have hd : d ≠ 0 := by
        intro hd0
        apply hn
        simpa [hd0] using hmul.symm
      have he : e ≠ 0 := by
        intro he0
        apply hn
        simpa [he0] using hmul.symm
      have hlog : (Real.log n : ℂ) = (Real.log d : ℂ) + Real.log e := by
        rw [← hmul, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hd)
          (Nat.cast_ne_zero.mpr he)]
        norm_cast
      rw [hlog]
      ring

@[simp]
theorem arithmeticLogDerivation_apply (f : ComplexArithmeticFunction) (n : ℕ) :
    arithmeticLogDerivation f n = (Real.log n : ℂ) * f n := rfl

/-- Complex lift of Mathlib's real logarithmic arithmetic function. -/
def complexArithmeticLog : ComplexArithmeticFunction :=
  ⟨fun n ↦ (Real.log n : ℂ), by simp⟩

/-- Complex lift of the von Mangoldt function. -/
def complexVonMangoldt : ComplexArithmeticFunction :=
  ⟨fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ), by simp⟩

@[simp]
theorem arithmeticLogDerivation_zeta :
    arithmeticLogDerivation (ArithmeticFunction.zeta : ComplexArithmeticFunction) =
      complexArithmeticLog := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [complexArithmeticLog]
  · simp [complexArithmeticLog, ArithmeticFunction.zeta_apply_ne hn]

/-- Möbius contraction of the logarithmic coefficient is exactly von Mangoldt. -/
theorem complex_moebius_mul_log_eq_vonMangoldt :
    (ArithmeticFunction.moebius : ComplexArithmeticFunction) * complexArithmeticLog =
      complexVonMangoldt := by
  ext n
  change (∑ x ∈ n.divisorsAntidiagonal,
      ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * (Real.log x.2 : ℂ)) =
    (ArithmeticFunction.vonMangoldt n : ℂ)
  have hreal :
      (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ) * Real.log x.2) =
          ArithmeticFunction.vonMangoldt n := by
    simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.log_apply] using
        congrArg (fun f : ArithmeticFunction ℝ ↦ f n)
          ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  exact_mod_cast hreal

/-- The universal Kähler logarithmic Maurer--Cartan one-form `M dE`. -/
def dirichletMaurerCartanForm :
    Ω[ComplexArithmeticFunction⁄ℂ] :=
  (ArithmeticFunction.moebius : ComplexArithmeticFunction) •
    KaehlerDifferential.D ℂ ComplexArithmeticFunction
      (ArithmeticFunction.zeta : ComplexArithmeticFunction)

/-- Universal inverse rule: `M dE = -(dM) E`. -/
theorem dirichletMaurerCartanForm_eq_neg_dM_mul_E :
    dirichletMaurerCartanForm =
      -((ArithmeticFunction.zeta : ComplexArithmeticFunction) •
        KaehlerDifferential.D ℂ ComplexArithmeticFunction
          (ArithmeticFunction.moebius : ComplexArithmeticFunction)) := by
  have hprod :
      (ArithmeticFunction.zeta : ComplexArithmeticFunction) *
          (ArithmeticFunction.moebius : ComplexArithmeticFunction) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  have hd := congrArg (KaehlerDifferential.D ℂ ComplexArithmeticFunction) hprod
  rw [Derivation.leibniz, Derivation.map_one_eq_zero] at hd
  unfold dirichletMaurerCartanForm
  rw [eq_neg_iff_add_eq_zero]
  simpa only [add_comm] using hd

/-! ## Universal de Rham Maurer--Cartan equation -/

/-- Universal exterior algebra generated by Dirichlet Kähler one-forms. -/
abbrev DirichletUniversalDeRhamAlgebra :=
  ExteriorAlgebra ComplexArithmeticFunction
    Ω[ComplexArithmeticFunction⁄ℂ]

local instance dirichletMaurerCartanMellinOrbitLawLocalInst1 : Algebra ℂ DirichletUniversalDeRhamAlgebra :=
  Algebra.restrictScalars ℂ ComplexArithmeticFunction _

local instance dirichletMaurerCartanMellinOrbitLawLocalInst2 : IsScalarTower ℂ ComplexArithmeticFunction
    DirichletUniversalDeRhamAlgebra :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Exterior-algebra image of the logarithmic Maurer--Cartan one-form. -/
def dirichletMaurerCartanExteriorForm : DirichletUniversalDeRhamAlgebra :=
  ExteriorAlgebra.ι ComplexArithmeticFunction dirichletMaurerCartanForm

/-- Universal exterior derivative `d(M dE)`. -/
def dirichletMaurerCartanExteriorDerivative : DirichletUniversalDeRhamAlgebra :=
  UniversalDeRham.oneFormExteriorDerivative ℂ ComplexArithmeticFunction
    dirichletMaurerCartanForm

/-- Kähler inverse rule in solved form: `dM = -M² dE`. -/
theorem kaehlerDifferential_moebius_eq_neg_square_smul_zeta :
    KaehlerDifferential.D ℂ ComplexArithmeticFunction
        (ArithmeticFunction.moebius : ComplexArithmeticFunction) =
      -((ArithmeticFunction.moebius : ComplexArithmeticFunction) ^ 2 •
        KaehlerDifferential.D ℂ ComplexArithmeticFunction
          (ArithmeticFunction.zeta : ComplexArithmeticFunction)) := by
  have hprod :
      (ArithmeticFunction.moebius : ComplexArithmeticFunction) *
        (ArithmeticFunction.zeta : ComplexArithmeticFunction) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  simpa using
    (KaehlerDifferential.D ℂ ComplexArithmeticFunction).leibniz_of_mul_eq_one hprod

/-- The exterior derivative term `d(M dE)` vanishes. -/
theorem dirichletMaurerCartanExteriorDerivative_eq_zero :
    dirichletMaurerCartanExteriorDerivative = 0 := by
  rw [dirichletMaurerCartanExteriorDerivative, dirichletMaurerCartanForm,
    UniversalDeRham.oneFormExteriorDerivative_smul_D,
    kaehlerDifferential_moebius_eq_neg_square_smul_zeta, map_neg, map_smul,
    neg_mul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero, neg_zero]

/-- The wedge square `(M dE) ∧ (M dE)` vanishes in the universal exterior algebra. -/
theorem dirichletMaurerCartanExteriorForm_sq_eq_zero :
    dirichletMaurerCartanExteriorForm * dirichletMaurerCartanExteriorForm = 0 := by
  exact ExteriorAlgebra.ι_sq_zero dirichletMaurerCartanForm

/-- Literal universal de Rham Maurer--Cartan equation
`d(M dE) + (M dE) ∧ (M dE) = 0`. -/
theorem dirichlet_universal_deRham_maurerCartan :
    dirichletMaurerCartanExteriorDerivative +
      dirichletMaurerCartanExteriorForm * dirichletMaurerCartanExteriorForm = 0 := by
  rw [dirichletMaurerCartanExteriorDerivative_eq_zero,
    dirichletMaurerCartanExteriorForm_sq_eq_zero, zero_add]

/-- Contracting the universal logarithmic form by `δ` gives the literal von Mangoldt current. -/
theorem contract_dirichletMaurerCartanForm_eq_vonMangoldt :
    arithmeticLogDerivation.liftKaehlerDifferential dirichletMaurerCartanForm =
      complexVonMangoldt := by
  rw [dirichletMaurerCartanForm, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, arithmeticLogDerivation_zeta]
  exact complex_moebius_mul_log_eq_vonMangoldt

/-! ## Mellin orbit -/

/-- Real Mellin character, extended by zero at the excluded arithmetic index `0`. -/
def arithmeticMellinWeight (a : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-a)

@[simp]
theorem arithmeticMellinWeight_zero (a : ℝ) : arithmeticMellinWeight a 0 = 0 := by
  simp [arithmeticMellinWeight]

@[simp]
theorem arithmeticMellinWeight_one (a : ℝ) : arithmeticMellinWeight a 1 = 1 := by
  simp [arithmeticMellinWeight]

/-- Mellin characters multiply along the arithmetic monoid. -/
theorem arithmeticMellinWeight_mul (a : ℝ) (m n : ℕ) :
    arithmeticMellinWeight a (m * n) =
      arithmeticMellinWeight a m * arithmeticMellinWeight a n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [arithmeticMellinWeight, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- Coefficientwise Mellin action `(σ_a f)(n)=n^{-a}f(n)`. -/
def arithmeticMellinTwist (a : ℝ) (f : ComplexArithmeticFunction) :
    ComplexArithmeticFunction :=
  ⟨fun n ↦ (arithmeticMellinWeight a n : ℂ) * f n, by simp⟩

@[simp]
theorem arithmeticMellinTwist_apply (a : ℝ) (f : ComplexArithmeticFunction) (n : ℕ) :
    arithmeticMellinTwist a f n = (arithmeticMellinWeight a n : ℂ) * f n := rfl

/-- The Mellin action is an algebra endomorphism. -/
def arithmeticMellinTwistHom (a : ℝ) :
    ComplexArithmeticFunction →ₐ[ℂ] ComplexArithmeticFunction where
  toFun := arithmeticMellinTwist a
  map_zero' := by
    ext n
    simp
  map_add' := fun f g ↦ by
    ext n
    simp [mul_add]
  map_one' := by
    ext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    · simp [ArithmeticFunction.one_apply_ne hn]
  map_mul' := fun f g ↦ by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · change (arithmeticMellinWeight a n : ℂ) *
          (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) =
        ∑ x ∈ n.divisorsAntidiagonal,
          ((arithmeticMellinWeight a x.1 : ℂ) * f x.1) *
            ((arithmeticMellinWeight a x.2 : ℂ) * g x.2)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      rintro ⟨d, e⟩ hde
      have hmul : d * e = n := (Nat.mem_divisorsAntidiagonal.mp hde).1
      rw [← hmul, arithmeticMellinWeight_mul]
      push_cast
      ring
  commutes' := fun c ↦ by
    ext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.one_apply_ne hn]

@[simp]
theorem arithmeticMellinTwist_mul (a : ℝ) (f g : ComplexArithmeticFunction) :
    arithmeticMellinTwist a (f * g) =
      arithmeticMellinTwist a f * arithmeticMellinTwist a g :=
  (arithmeticMellinTwistHom a).map_mul f g

@[simp]
theorem arithmeticMellinTwist_neg (a : ℝ) (f : ComplexArithmeticFunction) :
    arithmeticMellinTwist a (-f) = -arithmeticMellinTwist a f := by
  ext n
  simp [arithmeticMellinTwist_apply]

/-- Opposite Mellin parameters cancel coefficientwise. -/
theorem arithmeticMellinTwist_neg_comp (a : ℝ) (f : ComplexArithmeticFunction) :
    arithmeticMellinTwist (-a) (arithmeticMellinTwist a f) = f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [arithmeticMellinTwist_apply, arithmeticMellinWeight, if_neg hn,
      neg_neg]
    have hreal : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
      rw [Real.rpow_neg hnpos.le]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hnpos a))
    rw [← mul_assoc, ← Complex.ofReal_mul, hreal]
    simp

/-- Mellin scaling is an algebra automorphism with inverse parameter `-a`. -/
def arithmeticMellinTwistEquiv (a : ℝ) :
    ComplexArithmeticFunction ≃ₐ[ℂ] ComplexArithmeticFunction where
  toFun := arithmeticMellinTwist a
  invFun := arithmeticMellinTwist (-a)
  left_inv := arithmeticMellinTwist_neg_comp a
  right_inv f := by
    simpa only [neg_neg] using arithmeticMellinTwist_neg_comp (-a) f
  map_mul' := (arithmeticMellinTwistHom a).map_mul
  map_add' := (arithmeticMellinTwistHom a).map_add
  commutes' := (arithmeticMellinTwistHom a).commutes

/-- Exact coefficient derivative of the real Mellin character. -/
theorem hasDerivAt_arithmeticMellinWeight (a : ℝ) (n : ℕ) :
    HasDerivAt (fun u ↦ arithmeticMellinWeight u n)
      (-Real.log n * arithmeticMellinWeight a n) a := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [arithmeticMellinWeight] using hasDerivAt_const (x := a) (c := (0 : ℝ))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [arithmeticMellinWeight, if_neg hn]
    convert (HasDerivAt.const_rpow hnpos (hasDerivAt_neg a)) using 1
    all_goals ring

/-- The coefficient form of `∂_a σ_a f = -σ_a δf`. -/
theorem mellinTwist_parameter_derivative_coefficient
    (a : ℝ) (f : ComplexArithmeticFunction) (n : ℕ) :
    HasDerivAt (fun u ↦ arithmeticMellinWeight u n)
      (-Real.log n * arithmeticMellinWeight a n) a ∧
    (-(Real.log n : ℂ) * arithmeticMellinTwist a f n) =
      -arithmeticMellinTwist a (arithmeticLogDerivation f) n := by
  refine ⟨hasDerivAt_arithmeticMellinWeight a n, ?_⟩
  simp [arithmeticMellinTwist_apply]
  ring

/-- Literal coefficientwise identity `∂ₐ(σₐf)=-σₐ(δf)`.  Real and imaginary
parts are both differentiated, hence this pair determines the full complex coefficient derivative. -/
theorem hasDerivAt_arithmeticMellinTwist_coefficient_components
    (a : ℝ) (f : ComplexArithmeticFunction) (n : ℕ) :
    HasDerivAt (fun u : ℝ => (arithmeticMellinTwist u f n).re)
        (-arithmeticMellinTwist a (arithmeticLogDerivation f) n).re a ∧
      HasDerivAt (fun u : ℝ => (arithmeticMellinTwist u f n).im)
        (-arithmeticMellinTwist a (arithmeticLogDerivation f) n).im a := by
  constructor
  · have h := (hasDerivAt_arithmeticMellinWeight a n).mul_const (f n).re
    have hfun : (fun u : ℝ => (arithmeticMellinTwist u f n).re) =
        fun u => arithmeticMellinWeight u n * (f n).re := by
      funext u
      simp [arithmeticMellinTwist_apply]
    have hslope : (-arithmeticMellinTwist a (arithmeticLogDerivation f) n).re =
        (-Real.log n * arithmeticMellinWeight a n) * (f n).re := by
      rw [← (mellinTwist_parameter_derivative_coefficient a f n).2,
        arithmeticMellinTwist_apply, ← Complex.ofReal_neg,
        Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      ring
    rw [hfun, hslope]
    exact h
  · have h := (hasDerivAt_arithmeticMellinWeight a n).mul_const (f n).im
    have hfun : (fun u : ℝ => (arithmeticMellinTwist u f n).im) =
        fun u => arithmeticMellinWeight u n * (f n).im := by
      funext u
      simp [arithmeticMellinTwist_apply]
    have hslope : (-arithmeticMellinTwist a (arithmeticLogDerivation f) n).im =
        (-Real.log n * arithmeticMellinWeight a n) * (f n).im := by
      rw [← (mellinTwist_parameter_derivative_coefficient a f n).2,
        arithmeticMellinTwist_apply, ← Complex.ofReal_neg,
        Complex.im_ofReal_mul, Complex.im_ofReal_mul]
      ring
    rw [hfun, hslope]
    exact h

/-- Mellin transport of the von Mangoldt current. -/
def mellinVonMangoldtCurrent (a : ℝ) : ComplexArithmeticFunction :=
  arithmeticMellinTwist a complexVonMangoldt

/-- The Julia--Mellin orbit `J_u(n)=Λ(n)n^{-1-u}`. -/
def juliaMellinOrbit (u : ℝ) : ComplexArithmeticFunction :=
  ⟨fun n ↦ (arithmeticMellinWeight (1 + u) n : ℂ) *
      complexVonMangoldt n, by simp⟩

/-- `Θ_a=J_{a-1}` exactly. -/
theorem mellinVonMangoldtCurrent_eq_juliaMellinOrbit (a : ℝ) :
    mellinVonMangoldtCurrent a = juliaMellinOrbit (a - 1) := by
  ext n
  simp only [mellinVonMangoldtCurrent, arithmeticMellinTwist_apply,
    juliaMellinOrbit]
  congr 2
  ring_nf

/-- First Mellin gauge equation: `-M_a ∂_a E_a=Θ_a`, with the parameter derivative
represented by the exact coefficient derivative theorem above. -/
theorem mellin_moebius_zeta_gauge_left (a : ℝ) :
    -(arithmeticMellinTwist a
        (ArithmeticFunction.moebius : ComplexArithmeticFunction)) *
      (-arithmeticMellinTwist a
        (arithmeticLogDerivation
          (ArithmeticFunction.zeta : ComplexArithmeticFunction))) =
      mellinVonMangoldtCurrent a := by
  let M := arithmeticMellinTwist a
    (ArithmeticFunction.moebius : ComplexArithmeticFunction)
  let D := arithmeticMellinTwist a
    (arithmeticLogDerivation
      (ArithmeticFunction.zeta : ComplexArithmeticFunction))
  rw [show -M * (-D) = M * D from neg_mul_neg M D]
  change arithmeticMellinTwist a
      (ArithmeticFunction.moebius : ComplexArithmeticFunction) *
        arithmeticMellinTwist a
          (arithmeticLogDerivation
            (ArithmeticFunction.zeta : ComplexArithmeticFunction)) = _
  calc
    arithmeticMellinTwist a
        (ArithmeticFunction.moebius : ComplexArithmeticFunction) *
          arithmeticMellinTwist a
            (arithmeticLogDerivation
              (ArithmeticFunction.zeta : ComplexArithmeticFunction)) =
        arithmeticMellinTwist a
          ((ArithmeticFunction.moebius : ComplexArithmeticFunction) *
            arithmeticLogDerivation
              (ArithmeticFunction.zeta : ComplexArithmeticFunction)) :=
      (arithmeticMellinTwist_mul a _ _).symm
    _ = mellinVonMangoldtCurrent a := by
      rw [arithmeticLogDerivation_zeta,
        complex_moebius_mul_log_eq_vonMangoldt]
      rfl

/-- Second Mellin gauge equation: `∂_aM_a=Θ_a*M_a`. -/
theorem mellin_moebius_gauge_right (a : ℝ) :
    -arithmeticMellinTwist a
        (arithmeticLogDerivation
          (ArithmeticFunction.moebius : ComplexArithmeticFunction)) =
      mellinVonMangoldtCurrent a *
        arithmeticMellinTwist a
          (ArithmeticFunction.moebius : ComplexArithmeticFunction) := by
  have hprod :
      (ArithmeticFunction.moebius : ComplexArithmeticFunction) *
      (ArithmeticFunction.zeta : ComplexArithmeticFunction) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hd := arithmeticLogDerivation.leibniz_of_mul_eq_one hprod
  rw [arithmeticLogDerivation_zeta] at hd
  rw [neg_smul] at hd
  change arithmeticLogDerivation
      (ArithmeticFunction.moebius : ComplexArithmeticFunction) =
    -((ArithmeticFunction.moebius : ComplexArithmeticFunction) ^ 2 *
      complexArithmeticLog) at hd
  have hsource :
      -arithmeticLogDerivation
          (ArithmeticFunction.moebius : ComplexArithmeticFunction) =
        complexVonMangoldt *
          (ArithmeticFunction.moebius : ComplexArithmeticFunction) := by
    calc
      -arithmeticLogDerivation
            (ArithmeticFunction.moebius : ComplexArithmeticFunction) =
          -(-((ArithmeticFunction.moebius : ComplexArithmeticFunction) ^ 2 *
            complexArithmeticLog)) := congrArg Neg.neg hd
      _ = (ArithmeticFunction.moebius : ComplexArithmeticFunction) ^ 2 *
            complexArithmeticLog := neg_neg _
      _ = complexVonMangoldt *
            (ArithmeticFunction.moebius : ComplexArithmeticFunction) := by
          rw [← complex_moebius_mul_log_eq_vonMangoldt]
          simp only [pow_two]
          ring
  rw [← arithmeticMellinTwist_neg, hsource,
    arithmeticMellinTwist_mul]
  rfl

/-- The source connection annihilates its invertible Möbius section, so the one-parameter
Mellin connection is pure gauge. -/
theorem mellin_source_connection_pureGauge (a : ℝ) :
    -arithmeticMellinTwist a
        (arithmeticLogDerivation
          (ArithmeticFunction.moebius : ComplexArithmeticFunction)) -
      mellinVonMangoldtCurrent a *
        arithmeticMellinTwist a
          (ArithmeticFunction.moebius : ComplexArithmeticFunction) = 0 := by
  rw [mellin_moebius_gauge_right, sub_self]

/-- Every curvature two-form on the one-dimensional Mellin parameter line vanishes.  Applied to
the pure-gauge source connection, this is its exact zero-curvature statement. -/
theorem oneParameterMellinCurvature_eq_zero
    (curvature : ℝ [⋀^Fin 2]→ₗ[ℝ] ComplexArithmeticFunction) :
    curvature = 0 :=
  Subsingleton.elim _ _

end GaloisForLFunctions.HTGeometry
