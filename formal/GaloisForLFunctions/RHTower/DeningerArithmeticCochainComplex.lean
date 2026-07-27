import GaloisForLFunctions.RHTower.DeningerEntireQuotientCohomology
import GaloisForLFunctions.Bottcher.AnalyticDomain

/-!
# Completed-Xi comparison cochain complex

The completed Xi function determines a three-term cochain complex

`C⁰ = ℂ × Entire(ℂ)  --d⁰-->  C¹ = Entire(ℂ)  --d¹-->  C² = ℂ`,

where `d⁰(c,F) = XiC * F` and `d¹ = 0`.  The extra scalar summand in degree zero supplies the
endpoint class.  Analytic continuation makes multiplication by the nonzero entire function `XiC`
injective.  Consequently the cohomology is

`H⁰ ≃ ℂ`, `H¹ = Entire(ℂ)/(XiC)`, and `H² ≃ ℂ`.

This is an analytic comparison model, not the source-native arithmetic cohomology sought in
Deninger's program: the completed Xi function is built into its differential.  It avoids
enumerating the Xi divisor, but it cannot establish the missing comparison from an independently
constructed arithmetic coefficient to completed zeta.  Multiplication by the weight-one coordinate
`1/2 + I*z` is a cochain endomorphism.  It induces the previously constructed Frobenius generator
on `H¹`, while its endpoint actions have weights zero and two.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Degree-zero arithmetic cochains: endpoint constants plus entire gauge cochains. -/
abbrev DeningerArithmeticC0 := ℂ × DeningerEntire

/-- Degree-one arithmetic cochains. -/
abbrev DeningerArithmeticC1 := DeningerEntire

/-- Degree-two arithmetic cochains. -/
abbrev DeningerArithmeticC2 := ℂ

/-- Source differential in degree zero, multiplication by completed Xi. -/
def deningerArithmeticD0 :
    DeningerArithmeticC0 →ₗ[ℂ] DeningerArithmeticC1 where
  toFun x := deningerEntireXi * x.2
  map_add' x y := by
    apply DeningerEntire.ext
    intro z
    simp only [deningerEntire_mul_apply, deningerEntireXi_apply,
      Prod.snd_add, deningerEntire_add_apply]
    ring
  map_smul' c x := by
    apply DeningerEntire.ext
    intro z
    simp only [deningerEntire_mul_apply, deningerEntireXi_apply,
      Prod.smul_snd, deningerEntire_smul_apply, RingHom.id_apply]
    ring

/-- Source differential in degree one. -/
def deningerArithmeticD1 :
    DeningerArithmeticC1 →ₗ[ℂ] DeningerArithmeticC2 :=
  0

/-- The source differentials form a cochain complex. -/
theorem deningerArithmeticD1_comp_D0 :
    deningerArithmeticD1.comp deningerArithmeticD0 = 0 := by
  rfl

/-- Completed Xi is a nonzero element of the entire-function source algebra. -/
theorem deningerEntireXi_ne_zero :
    deningerEntireXi ≠ 0 := by
  intro hzero
  apply XiC_zero_ne
  have h := congrArg (fun F : DeningerEntire => F 0) hzero
  simpa only [deningerEntireXi_apply, deningerEntire_zero_apply] using h

/--
Multiplication by completed Xi is injective on entire functions.  This is the analytic identity
theorem, and is the only input needed to compute source `H⁰`.
-/
theorem deningerEntireXi_mul_injective :
    Function.Injective (fun F : DeningerEntire => deningerEntireXi * F) := by
  intro F G hFG
  have hprod :
      deningerEntireXi * (F - G) = 0 := by
    apply DeningerEntire.ext
    intro z
    have hz := congrArg (fun H : DeningerEntire => H z) hFG
    simp only [deningerEntire_mul_apply, deningerEntireXi_apply] at hz
    simp only [deningerEntire_mul_apply, deningerEntireXi_apply,
      deningerEntire_sub_apply, deningerEntire_zero_apply]
    linear_combination hz
  have hXiAnalytic :
      AnalyticOnNhd ℂ (deningerEntireXi : ℂ → ℂ) Set.univ :=
    fun z _ => deningerEntireXi.2.analyticAt z
  have hDiffAnalytic :
      AnalyticOnNhd ℂ ((F - G : DeningerEntire) : ℂ → ℂ) Set.univ :=
    fun z _ => (F - G).2.analyticAt z
  have hproduct :
      Set.EqOn
        (fun z =>
          (deningerEntireXi : ℂ → ℂ) z *
            ((F - G : DeningerEntire) : ℂ → ℂ) z)
        0 Set.univ := by
    intro z _
    have hz := congrArg (fun H : DeningerEntire => H z) hprod
    simpa only [deningerEntire_mul_apply, deningerEntire_zero_apply] using hz
  rcases Bottcher.analyticOnNhd_domain hXiAnalytic hDiffAnalytic
      isPreconnected_univ isOpen_univ hproduct with hXiZero | hDiffZero
  · exact (deningerEntireXi_ne_zero (DeningerEntire.ext fun z =>
      hXiZero (Set.mem_univ z))).elim
  · apply sub_eq_zero.mp
    exact DeningerEntire.ext fun z => hDiffZero (Set.mem_univ z)

/-- Degree-zero cocycles. -/
abbrev DeningerArithmeticH0 :=
  LinearMap.ker deningerArithmeticD0

/-- Degree-zero cohomology is exactly the endpoint scalar. -/
def deningerArithmeticH0Equiv :
    DeningerArithmeticH0 ≃ₗ[ℂ] ℂ where
  toFun x := x.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨(c, 0), by
    change deningerEntireXi * 0 = 0
    exact mul_zero deningerEntireXi⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx : deningerEntireXi * x.1.2 = 0 := x.2
      have heq :
          deningerEntireXi * x.1.2 =
            deningerEntireXi * (0 : DeningerEntire) := by
        simpa using hx
      exact (deningerEntireXi_mul_injective heq).symm
  right_inv _ := rfl

/-- The image of `d⁰` is exactly the principal Xi ideal. -/
theorem range_deningerArithmeticD0 :
    LinearMap.range deningerArithmeticD0 =
      deningerEntireXiIdeal.restrictScalars ℂ := by
  ext F
  change F ∈ LinearMap.range deningerArithmeticD0 ↔
    F ∈ deningerEntireXiIdeal
  constructor
  · rintro ⟨x, rfl⟩
    rw [deningerEntireXiIdeal, Ideal.mem_span_singleton']
    refine ⟨x.2, ?_⟩
    change x.2 * deningerEntireXi =
      deningerEntireXi * x.2
    exact mul_comm _ _
  · intro hF
    rw [deningerEntireXiIdeal, Ideal.mem_span_singleton'] at hF
    obtain ⟨G, hG⟩ := hF
    refine ⟨(0, G), ?_⟩
    change deningerEntireXi * G = F
    rw [mul_comm]
    exact hG

/--
Middle cohomology is the cokernel of `d⁰`, hence the intrinsic entire quotient already used for
the exact source-spectrum theorem.
-/
abbrev DeningerArithmeticH1 := DeningerEntireH1

/-- Degree-two cohomology is the endpoint scalar because `d¹=0`. -/
abbrev DeningerArithmeticH2 := ℂ

/-- Weight-zero cochain generator. -/
def deningerArithmeticThetaC0 :
    Module.End ℂ DeningerArithmeticC0 where
  toFun x := (0, deningerEntireThetaCoordinate * x.2)
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply DeningerEntire.ext
      intro z
      simp only [Prod.snd_add, deningerEntire_mul_apply,
        deningerEntireThetaCoordinate_apply, deningerEntire_add_apply]
      ring
  map_smul' c x := by
    apply Prod.ext
    · simp
    · apply DeningerEntire.ext
      intro z
      simp only [Prod.smul_snd, deningerEntire_mul_apply,
        deningerEntireThetaCoordinate_apply, deningerEntire_smul_apply,
        RingHom.id_apply]
      ring

/-- Weight-one cochain generator. -/
def deningerArithmeticThetaC1 :
    Module.End ℂ DeningerArithmeticC1 :=
  LinearMap.mulLeft ℂ deningerEntireThetaCoordinate

/-- Weight-two endpoint generator. -/
def deningerArithmeticThetaC2 :
    Module.End ℂ DeningerArithmeticC2 :=
  LinearMap.id

/-- Frobenius commutes with the source differential in degree zero. -/
theorem deningerArithmeticTheta_commutes_D0 :
    deningerArithmeticD0.comp deningerArithmeticThetaC0 =
      deningerArithmeticThetaC1.comp deningerArithmeticD0 := by
  apply LinearMap.ext
  intro x
  change
    deningerEntireXi * (deningerEntireThetaCoordinate * x.2) =
      deningerEntireThetaCoordinate * (deningerEntireXi * x.2)
  calc
    deningerEntireXi * (deningerEntireThetaCoordinate * x.2) =
        (deningerEntireXi * deningerEntireThetaCoordinate) * x.2 :=
      (mul_assoc _ _ _).symm
    _ = (deningerEntireThetaCoordinate * deningerEntireXi) * x.2 := by
      rw [mul_comm deningerEntireXi deningerEntireThetaCoordinate]
    _ = deningerEntireThetaCoordinate * (deningerEntireXi * x.2) :=
      mul_assoc _ _ _

/-- Frobenius commutes with the zero differential in degree one. -/
theorem deningerArithmeticTheta_commutes_D1 :
    deningerArithmeticD1.comp deningerArithmeticThetaC1 =
      deningerArithmeticThetaC2.comp deningerArithmeticD1 := by
  rfl

/-- The induced action on `H⁰ ≃ ℂ` is the zero operator. -/
theorem deningerArithmeticTheta_H0_eq_zero
    (x : DeningerArithmeticH0) :
    deningerArithmeticH0Equiv
        ⟨deningerArithmeticThetaC0 x.1, by
          change deningerArithmeticD0
            (deningerArithmeticThetaC0 x.1) = 0
          have hcomm := LinearMap.congr_fun
            deningerArithmeticTheta_commutes_D0 x.1
          change deningerArithmeticD0
              (deningerArithmeticThetaC0 x.1) =
            deningerArithmeticThetaC1
              (deningerArithmeticD0 x.1) at hcomm
          rw [x.2, map_zero] at hcomm
          exact hcomm⟩ = 0 := by
  rfl

/-- The cochain action induces the source-defined Frobenius generator on `H¹`. -/
theorem deningerArithmeticTheta_H1_class (F : DeningerEntire) :
    deningerEntireTheta (deningerEntireH1Class F) =
      deningerEntireH1Class (deningerArithmeticThetaC1 F) := by
  change
    deningerEntireThetaClass * deningerEntireH1Class F =
      deningerEntireH1Class (deningerEntireThetaCoordinate * F)
  rw [← deningerEntireH1Class_thetaCoordinate,
    map_mul deningerEntireH1Class]

/-- The induced action on `H² ≃ ℂ` is the identity, hence has weight two. -/
theorem deningerArithmeticTheta_H2_eq_id :
    deningerArithmeticThetaC2 = LinearMap.id := by
  rfl

end

end RHTower
