import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLocalPolynomialPeriods
import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePrimeDifference

/-!
# Dirichlet series of the literal local polynomial model

The finite point-mass polynomial convolved with the constant sequence is exactly
the periodic coefficient sequence audited in `LocalPolynomialPeriods`.
Coprime masks either preserve the entire local polynomial or retain only its
constant coefficient. No full-positive source is asserted by this model.
-/

open Complex Polynomial Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

def localModelDirichletCoeff (p : ℕ) (P : Polynomial ℝ) : ℕ → ℂ :=
  ∑ j ∈ range (P.natDegree + 1), (P.coeff j : ℂ) • dirichletPoint (p ^ j)

def localModelForwardCoeff (p : ℕ) (P : Polynomial ℝ) : ℕ → ℂ :=
  LSeries.convolution (localModelDirichletCoeff p P) 1

def localModelFactor (p : ℕ) (P : Polynomial ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ range (P.natDegree + 1), (P.coeff j : ℂ) * ((p ^ j : ℕ) : ℂ) ^ (-s)

theorem summable_localModelDirichletCoeff (p : ℕ) (P : Polynomial ℝ) (s : ℂ) :
    LSeriesSummable (localModelDirichletCoeff p P) s := by
  unfold localModelDirichletCoeff
  exact LSeriesSummable.sum fun j _ =>
    LSeriesSummable.smul (P.coeff j : ℂ) (summable_dirichletPoint (p ^ j) s)

theorem LSeries_localModelDirichletCoeff {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ) (s : ℂ) :
    LSeries (localModelDirichletCoeff p P) s = localModelFactor p P s := by
  rw [localModelDirichletCoeff, LSeries_sum (fun j _ =>
    LSeriesSummable.smul (P.coeff j : ℂ) (summable_dirichletPoint (p ^ j) s))]
  unfold localModelFactor
  apply Finset.sum_congr rfl
  intro j _
  rw [LSeries_smul, LSeries_dirichletPoint (pow_ne_zero j hp)]

private theorem localModelForwardCoeff_eq_sum (p : ℕ) (P : Polynomial ℝ) (n : ℕ) :
    localModelForwardCoeff p P n = ∑ j ∈ range (P.natDegree + 1),
      (P.coeff j : ℂ) * LSeries.convolution (dirichletPoint (p ^ j)) 1 n := by
  simp only [localModelForwardCoeff, localModelDirichletCoeff, LSeries.convolution_def,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one, Finset.mul_sum]
  exact Finset.sum_comm

/-- The series and the finite-period variance use exactly the same coefficients. -/
theorem localModelForwardCoeff_eq_periodic {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    localModelForwardCoeff p P n =
      (localPolynomialCoefficientUpTo p P P.natDegree n : ℂ) := by
  rw [localModelForwardCoeff_eq_sum]
  simp only [localPolynomialCoefficientUpTo, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [convolution_dirichletPoint (pow_ne_zero j hp), if_neg hn]
  by_cases hd : p ^ j ∣ n <;> simp [hd]

theorem summable_localModelForwardCoeff (p : ℕ) (P : Polynomial ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (localModelForwardCoeff p P) s :=
  (summable_localModelDirichletCoeff p P s).convolution (LSeriesSummable_one_iff.mpr hs)

theorem LSeries_localModelForwardCoeff {p : ℕ} (hp : p ≠ 0) (P : Polynomial ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (localModelForwardCoeff p P) s = localModelFactor p P s * riemannZeta s := by
  rw [localModelForwardCoeff,
    LSeries_convolution' (summable_localModelDirichletCoeff p P s) (LSeriesSummable_one_iff.mpr hs),
    LSeries_localModelDirichletCoeff hp, LSeries_one_eq_riemannZeta hs]

private theorem coprimePart_localModelDirichletCoeff_sum (p Q : ℕ) (P : Polynomial ℝ) :
    coprimePart Q (localModelDirichletCoeff p P) =
      ∑ j ∈ range (P.natDegree + 1),
        ((coprimeMask Q (p ^ j) : ℂ) * (P.coeff j : ℂ)) • dirichletPoint (p ^ j) := by
  funext n
  simp only [coprimePart, localModelDirichletCoeff, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hn : n = p ^ j
  · subst n
    ring
  · simp [dirichletPoint, hn]

/-- A coprime mask sees only whether the base is allowed, not its valuation depth. -/
theorem coprimePart_localModelDirichletCoeff (p Q : ℕ) (P : Polynomial ℝ) :
    coprimePart Q (localModelDirichletCoeff p P) =
      if p.Coprime Q then localModelDirichletCoeff p P
        else (P.coeff 0 : ℂ) • dirichletPoint 1 := by
  rw [coprimePart_localModelDirichletCoeff_sum]
  by_cases hp : p.Coprime Q
  · rw [if_pos hp, localModelDirichletCoeff]
    apply Finset.sum_congr rfl
    intro j _
    have hc : (p ^ j).Coprime Q := hp.pow_left j
    simp only [coprimeMask, if_pos hc, Complex.ofReal_one, one_mul]
  · rw [if_neg hp, Finset.sum_eq_single 0]
    · simp [coprimeMask]
    · intro j _ hj
      have hc : ¬(p ^ j).Coprime Q := fun h =>
        hp ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hj) p Q).mp h)
      simp [coprimeMask, hc]
    · simp

theorem LSeries_coprimePart_localModelForwardCoeff {p : ℕ} (hp : p ≠ 0)
    (Q : ℕ) [NeZero Q] (P : Polynomial ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coprimePart Q (localModelForwardCoeff p P)) s =
      (if p.Coprime Q then localModelFactor p P s else (P.coeff 0 : ℂ)) *
        DirichletCharacter.LFunctionTrivChar Q s := by
  rw [localModelForwardCoeff, coprimePart_convolution,
    LSeries_convolution' (summable_coprimePart Q (summable_localModelDirichletCoeff p P s))
      (summable_coprimePart Q (LSeriesSummable_one_iff.mpr hs)),
    LSeries_coprimePart_one Q hs, coprimePart_localModelDirichletCoeff]
  by_cases hc : p.Coprime Q
  · rw [if_pos hc, if_pos hc, LSeries_localModelDirichletCoeff hp]
  · rw [if_neg hc, if_neg hc, LSeries_smul, LSeries_dirichletPoint (by norm_num : (1 : ℕ) ≠ 0)]
    simp

end RHTower.WeilSingularArithmetic
