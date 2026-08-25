import GaloisForLFunctions.HTGeometry.SmallGrowthFiniteAbscissaCoefficientSeparation
import GaloisForLFunctions.HTGeometry.SmallGrowthRotatedDirichletCoefficientSeparation
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.LinearIndependentBaseChange
import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate
import GaloisForLFunctions.HTGeometry.FiniteLindemannWeierstrass

/-!
# Algebraic independence over the small-growth meromorphic field

Chiang--Feng coefficient separation upgrades constant-coefficient algebraic independence of a
finite-abscissa arithmetic family to algebraic independence of its analytic L-series realization
over Nagoshi's exact small-growth meromorphic field.
-/

open Filter Set Topology LSeries ArithmeticFunction ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance smallGrowthIndependenceUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

theorem smallGrowth_upperEndRotated_LSeries_relation_coeff_eq_zero {d : ℕ}
    (a : Fin d → ℕ → ℂ) {x₁ : ℝ}
    (hsum : ∀ i, LSeriesSummable (a i) (x₁ : ℂ))
    (phi : Fin d → SmallGrowthMeromorphicField) {B : ℝ}
    (hrel : ∀ᶠ z in Filter.codiscrete ℂ, B ≤ z.im →
      ∑ i, smallGrowthFunction (phi i) z *
        LSeries (a i) (-Complex.I * z) = 0) :
    ∀ n, 1 ≤ n →
      ∑ i, complexToSmallGrowthMeromorphic (a i n) * phi i = 0 :=
  smallGrowth_rotated_LSeries_relation_coeff_eq_zero a hsum phi hrel

/-- The finite-abscissa arithmetic function represented by one monomial in a source family. -/
def finiteAbscissaMonomial {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra) (m : I →₀ ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  m.prod fun i n => f i ^ n

@[simp]
theorem finiteAbscissaMonomial_apply {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra) (m : I →₀ ℕ) (n : ℕ) :
    (finiteAbscissaMonomial f m).1 n =
      (m.prod fun i k => f i ^ k).1 n :=
  rfl

@[simp]
theorem finiteAbscissaLSeriesToUpperEndMero_monomial {I : Type*}
    (f : I → finiteAbscissaArithmeticSubalgebra) (m : I →₀ ℕ) :
    finiteAbscissaLSeriesToUpperEndMero (finiteAbscissaMonomial f m) =
      m.prod fun i n => finiteAbscissaLSeriesToUpperEndMero (f i) ^ n := by
  rw [finiteAbscissaMonomial, Finsupp.prod, Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow]

/-- Distinct finitely supported monomials in an algebraically independent family are linearly
independent; no finiteness assumption on the ambient variable type is needed. -/
theorem finsuppMonomial_linearIndependent_of_algebraicIndependent
    {K I A : Type*} [Fintype K] [CommRing A] [Algebra ℂ A]
    (x : I → A) (hx : AlgebraicIndependent ℂ x)
    (m : K → I →₀ ℕ) (hm : Function.Injective m) :
    LinearIndependent ℂ (fun k => (m k).prod fun i n => x i ^ n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrel k
  let P : MvPolynomial I ℂ := ∑ j : K, MvPolynomial.monomial (m j) (c j)
  have hPev : MvPolynomial.aeval x P = 0 := by
    change MvPolynomial.aeval x
      (∑ j : K, MvPolynomial.monomial (m j) (c j)) = 0
    rw [map_sum]
    simpa only [MvPolynomial.aeval_monomial, Algebra.smul_def] using hrel
  have hP0 : P = 0 := hx.eq_zero_of_aeval_eq_zero P hPev
  have hcoeff := congrArg (MvPolynomial.coeff (m k)) hP0
  have hcoeffP : MvPolynomial.coeff (m k) P = c k := by
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      rw [if_neg]
      exact fun heq => hjk (hm heq)
    · simp
  rw [hcoeffP, MvPolynomial.coeff_zero] at hcoeff
  exact hcoeff

set_option maxHeartbeats 800000 in
/-- **Small-growth base upgrade.** Any finite-abscissa arithmetic family algebraically independent
over `ℂ` has an analytic L-series realization algebraically independent over Nagoshi's exact field
`F_s` of meromorphic functions of characteristic `o(r)`.
-/
theorem algebraicIndependent_finiteAbscissaLSeries_over_smallGrowth
    {I : Type*} (f : I → finiteAbscissaArithmeticSubalgebra)
    (hf : AlgebraicIndependent ℂ f) :
    AlgebraicIndependent SmallGrowthMeromorphicField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  classical
  let J := P.support
  let A : J → finiteAbscissaArithmeticSubalgebra := fun m =>
    finiteAbscissaMonomial f m.1
  let phi : J → SmallGrowthMeromorphicField := fun m => P.coeff m.1
  have hlinear :
      ∑ m : J, smallGrowthMeromorphicToUpperEnd (phi m) *
        finiteAbscissaLSeriesToUpperEndMero (A m) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq] at hP
    rw [← hP]
    rw [Finset.sum_subtype P.support (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp only [A, phi]
    rw [finiteAbscissaLSeriesToUpperEndMero_monomial]
    change algebraMap SmallGrowthMeromorphicField upperEndMeroField (P.coeff m.1) *
        (m.1.prod fun i n => finiteAbscissaLSeriesToUpperEndMero (f i) ^ n) = _
    simp only [Finsupp.prod]
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let AF : Fin (Fintype.card J) → finiteAbscissaArithmeticSubalgebra := A ∘ eJ
  let phiF : Fin (Fintype.card J) → SmallGrowthMeromorphicField := phi ∘ eJ
  have hlinearF :
      ∑ m, smallGrowthMeromorphicToUpperEnd (phiF m) *
        finiteAbscissaLSeriesToUpperEndMero (AF m) = 0 := by
    calc
      ∑ m, smallGrowthMeromorphicToUpperEnd (phiF m) *
          finiteAbscissaLSeriesToUpperEndMero (AF m) =
          ∑ m : J, smallGrowthMeromorphicToUpperEnd (phi m) *
            finiteAbscissaLSeriesToUpperEndMero (A m) := by
        exact Equiv.sum_comp eJ (fun m : J =>
          smallGrowthMeromorphicToUpperEnd (phi m) *
            finiteAbscissaLSeriesToUpperEndMero (A m))
      _ = 0 := hlinear
  obtain ⟨B, hrot⟩ :=
    upperEnd_smallGrowth_relation_eventually_rotated AF phiF hlinearF
  choose x₁ hx₁ using fun m : Fin (Fintype.card J) => (AF m).2
  let X : ℝ := ∑ m : Fin (Fintype.card J), (|x₁ m| + 1)
  have hsum : ∀ m : Fin (Fintype.card J),
      LSeriesSummable (fun n => (AF m).1 n) (X : ℂ) := by
    intro m
    have hm : x₁ m < X := by
      have hle : |x₁ m| + 1 ≤ X := by
        dsimp only [X]
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun i : Fin (Fintype.card J) => |x₁ i| + 1)
          (fun i _ => by positivity) (Finset.mem_univ m)
      linarith [le_abs_self (x₁ m)]
    exact hx₁ m X hm
  have hrot' : ∀ᶠ z in Filter.codiscrete ℂ, B + 1 ≤ z.im →
      ∑ i, smallGrowthFunction (phiF i) z *
        LSeries (fun n => (AF i).1 n) (-Complex.I * z) = 0 := by
    filter_upwards [hrot] with z hz
    intro hzB
    exact hz (by linarith)
  have hcoeff : ∀ n, 1 ≤ n →
      ∑ m : Fin (Fintype.card J),
        complexToSmallGrowthMeromorphic ((AF m).1 n) * phiF m = 0 :=
    smallGrowth_upperEndRotated_LSeries_relation_coeff_eq_zero
      (fun m => fun n => (AF m).1 n) hsum phiF hrot'
  have hmonomialLI : LinearIndependent ℂ
      (fun m : Fin (Fintype.card J) => fun n => (AF m).1 n) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hrel k
    let Q : MvPolynomial I ℂ :=
      ∑ m : Fin (Fintype.card J), MvPolynomial.monomial (eJ m).1 (c m)
    have hrelA : ∑ m, c m • finiteAbscissaMonomial f (eJ m).1 = 0 := by
      apply Subtype.val_injective
      apply ArithmeticFunction.ext
      intro n
      let ev : finiteAbscissaArithmeticSubalgebra →ₗ[ℂ] ℂ :=
        { toFun := fun g => g.1 n
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      change ev (∑ m, c m • finiteAbscissaMonomial f (eJ m).1) = ev 0
      rw [map_sum, map_zero ev]
      change ∑ m, c m * (finiteAbscissaMonomial f (eJ m).1).1 n = 0
      simpa only [AF, A, Function.comp_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hrel n
    have hQev : MvPolynomial.aeval f Q = 0 := by
      change MvPolynomial.aeval f
        (∑ m : Fin (Fintype.card J),
          MvPolynomial.monomial (eJ m).1 (c m)) = 0
      rw [map_sum]
      simpa only [MvPolynomial.aeval_monomial, Algebra.smul_def,
        finiteAbscissaMonomial] using hrelA
    have hQ0 : Q = 0 := hf.eq_zero_of_aeval_eq_zero Q hQev
    have hcoeffQ0 := congrArg (MvPolynomial.coeff (eJ k).1) hQ0
    have hcoeffQ : MvPolynomial.coeff (eJ k).1 Q = c k := by
      simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single k]
      · simp
      · intro m _ hmk
        rw [if_neg]
        exact fun heq => hmk (eJ.injective (Subtype.ext heq))
      · simp
    rw [hcoeffQ, MvPolynomial.coeff_zero] at hcoeffQ0
    exact hcoeffQ0
  have hcoeffAll : ∀ n,
      ∑ m : Fin (Fintype.card J),
        complexToSmallGrowthMeromorphic ((AF m).1 n) * phiF m = 0 := by
    intro n
    rcases n with _ | n
    · simp
    · exact hcoeff (n + 1) (by omega)
  obtain ⟨e, Q, _, hQ, heval⟩ :=
    exists_injective_evaluation_minor_of_linearIndependent
      (fun m : Fin (Fintype.card J) => fun n => (AF m).1 n) hmonomialLI
  let u : Fin (Fintype.card J) → Fin (Fintype.card J) → ℂ :=
    fun m r => (AF m).1 (e r)
  have hu : LinearIndependent ℂ u := by
    apply linearIndependent_of_coordinateMinor_det_ne_zero u id
    have hmatrix : coordinateMinor u id = Q := by
      ext r m
      exact (heval r m).symm
    rw [hmatrix]
    exact isUnit_iff_ne_zero.mp hQ
  have huF : LinearIndependent SmallGrowthMeromorphicField
      (fun m : Fin (Fintype.card J) => fun r =>
        complexToSmallGrowthMeromorphic (u m r)) :=
    BaseChange.linearIndependent_map_algebraMap_square hu
  have hrelation : ∑ m : Fin (Fintype.card J), phiF m •
      (fun r => complexToSmallGrowthMeromorphic (u m r)) = 0 := by
    funext r
    simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
      hcoeffAll (e r)
  have hphi : ∀ m : Fin (Fintype.card J), phiF m = 0 :=
    Fintype.linearIndependent_iff.mp huF phiF hrelation
  apply MvPolynomial.ext
  intro m
  by_cases hm : m ∈ P.support
  · let j : J := ⟨m, hm⟩
    simp only [MvPolynomial.coeff_zero]
    have hzero := hphi (eJ.symm j)
    change P.coeff (eJ (eJ.symm j)).1 = 0 at hzero
    simpa only [Equiv.apply_symm_apply, j] using hzero
  · rw [MvPolynomial.mem_support_iff] at hm
    simp only [MvPolynomial.coeff_zero]
    exact not_ne_iff.mp hm

end

end GaloisForLFunctions.HTGeometry
