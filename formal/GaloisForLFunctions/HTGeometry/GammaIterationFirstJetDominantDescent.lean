import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetDominantBoundary

/-!
# Factorial descent for polynomial relations among Gamma-iterate first jets

The factorial microscope first grades a relation by total raw derivative degree and then by point
degree.  This file proves the exact monomial rescaling, convergence of the normalized coefficients,
and the resulting descent to the nonzero dominant tail polynomial.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def firstJetTailMonomial (y : Fin k × Fin 2 → ℂ)
    (a : GammaIterateFirstJetIndex k →₀ ℕ) : ℂ :=
  MvPolynomial.eval y (MvPolynomial.monomial (firstJetTailExponent a) 1)

def firstJetScaleTail (s : ℂ) (y : Fin k × Fin 2 → ℂ) : Fin k × Fin 2 → ℂ :=
  fun i => Fin.cases (s * y i) (fun _ => y i) i.2

theorem firstJetDerivativeDegree_eq_sum
    (a : (Fin k × Fin 2) →₀ ℕ) :
    firstJetDerivativeDegree a = ∑ j : Fin k, a (j, 0) := by
  rw [firstJetDerivativeDegree, Finsupp.weight_apply,
    Finsupp.sum_fintype, Fintype.sum_prod_type]
  · simp [firstJetDerivativeWeight, Fin.sum_univ_two]
  · intro i
    simp

theorem firstJetTailMonomial_scale
    (s : ℂ) (y : Fin k × Fin 2 → ℂ)
    (a : GammaIterateFirstJetIndex k →₀ ℕ) :
    firstJetTailMonomial (firstJetScaleTail s y) a =
      s ^ firstJetFullDerivativeDegree a * firstJetTailMonomial y a := by
  rw [firstJetTailMonomial, firstJetTailMonomial,
    MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp only [one_mul]
  classical
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · simp only [Fintype.prod_prod_type, Fin.prod_univ_two,
      firstJetScaleTail, firstJetTailExponent,
      Finsupp.coe_equivFunOnFinite_symm, fin2_cases_one,
      Fin.cases_zero, mul_pow, Finset.prod_mul_distrib,
      firstJetFullDerivativeDegree,
      firstJetDerivativeDegree_eq_sum]
    have hsprod : (∏ j : Fin k, s ^ a (Sum.inr (j, 0))) =
        s ^ ∑ j : Fin k, a (Sum.inr (j, 0)) := by
      simpa using Finset.prod_pow_eq_pow_sum Finset.univ
        (fun j : Fin k => a (Sum.inr (j, 0))) s
    rw [hsprod]
    ring
  · intro i
    simp
  · intro i
    simp

theorem eval_firstJetPolynomial_as_sum
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (point : ℂ) (y : Fin k × Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => i.elim (fun _ => point) y) P =
      ∑ a ∈ P.support, MvPolynomial.coeff a P *
        (point ^ firstJetPointExponent a * firstJetTailMonomial y a) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.eval_monomial]
  rw [firstJetTailMonomial, MvPolynomial.eval_monomial]
  simp only [one_mul]
  congr 1
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · simp [Fintype.prod_sum_type, firstJetPointExponent, firstJetTailExponent]
  · intro i
    simp
  · intro i
    simp

def firstJetDominantLimitCoefficient
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (a : GammaIterateFirstJetIndex k →₀ ℕ) : ℂ :=
  if firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P ∧
      firstJetPointExponent a = firstJetTopPointDegree P then
    (-1 : ℂ) ^ firstJetTopPointDegree P * MvPolynomial.coeff a P
  else 0

def firstJetDominantCoefficient
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (a : GammaIterateFirstJetIndex k →₀ ℕ) (n : ℕ) (x : ℂ) : ℂ :=
  MvPolynomial.coeff a P * factorialBlowUpMonomialCoefficient n x
    (firstJetTopDerivativeDegree P - firstJetFullDerivativeDegree a)
    (firstJetPointExponent a) (firstJetTopPointDegree P)

theorem firstJetFullDerivativeDegree_le_top
    {P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ}
    {a : GammaIterateFirstJetIndex k →₀ ℕ} (ha : a ∈ P.support) :
    firstJetFullDerivativeDegree a ≤ firstJetTopDerivativeDegree P :=
  Finset.le_sup ha

theorem firstJetPointExponent_le_top
    {P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ}
    {a : GammaIterateFirstJetIndex k →₀ ℕ} (ha : a ∈ P.support)
    (hD : firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P) :
    firstJetPointExponent a ≤ firstJetTopPointDegree P := by
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨ha, hD⟩

theorem tendsto_firstJetDominantCoefficient
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    {a : GammaIterateFirstJetIndex k →₀ ℕ} (ha : a ∈ P.support) (x : ℂ) :
    Tendsto (fun n => firstJetDominantCoefficient P a n x) atTop
      (𝓝 (firstJetDominantLimitCoefficient P a)) := by
  have hDle := firstJetFullDerivativeDegree_le_top ha
  by_cases hD : firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P
  · have hple := firstJetPointExponent_le_top ha hD
    by_cases hp : firstJetPointExponent a = firstJetTopPointDegree P
    · have htop := tendsto_factorialBlowUpMonomialCoefficient_top x
          (firstJetTopPointDegree P)
      simpa [firstJetDominantCoefficient, firstJetDominantLimitCoefficient,
        hD, hp, mul_comm] using htop.const_mul (MvPolynomial.coeff a P)
    · have hplt : firstJetPointExponent a < firstJetTopPointDegree P :=
        lt_of_le_of_ne hple hp
      have hzero :=
        tendsto_factorialBlowUpMonomialCoefficient_of_pointExponent_lt x hplt
      simpa [firstJetDominantCoefficient, firstJetDominantLimitCoefficient,
        hD, hp] using hzero.const_mul (MvPolynomial.coeff a P)
  · have hlt : firstJetFullDerivativeDegree a < firstJetTopDerivativeDegree P :=
      lt_of_le_of_ne hDle hD
    have hpos : 1 ≤ firstJetTopDerivativeDegree P - firstJetFullDerivativeDegree a := by
      omega
    have hzero := tendsto_factorialBlowUpMonomialCoefficient_of_weightDefect_pos
      x hpos (firstJetPointExponent a) (firstJetTopPointDegree P)
    simpa [firstJetDominantCoefficient, firstJetDominantLimitCoefficient, hD]
      using hzero.const_mul (MvPolynomial.coeff a P)

theorem eval_firstJetDominantTailPolynomial
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (y : Fin k × Fin 2 → ℂ) :
    MvPolynomial.eval y (firstJetDominantTailPolynomial P) =
      ∑ a ∈ P.support,
        firstJetDominantLimitCoefficient P a * firstJetTailMonomial y a := by
  classical
  rw [firstJetDominantTailPolynomial, map_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_filter]
  unfold firstJetTopDerivativeSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hD : firstJetFullDerivativeDegree a = firstJetTopDerivativeDegree P
  · by_cases hp : firstJetPointExponent a = firstJetTopPointDegree P
    · rw [firstJetTailMonomial, MvPolynomial.eval_monomial]
      simp [hD, hp, firstJetDominantLimitCoefficient]
    · simp [hD, hp, firstJetDominantLimitCoefficient]
  · simp [hD, firstJetDominantLimitCoefficient]

theorem tendsto_firstJetTailMonomial
    {G : ℕ → Fin k × Fin 2 → ℂ} {J : Fin k × Fin 2 → ℂ}
    (hG : ∀ i, Tendsto (fun n => G n i) atTop (𝓝 (J i)))
    (a : GammaIterateFirstJetIndex k →₀ ℕ) :
    Tendsto (fun n => firstJetTailMonomial (G n) a) atTop
      (𝓝 (firstJetTailMonomial J a)) := by
  simp only [firstJetTailMonomial, MvPolynomial.eval_monomial, one_mul]
  exact tendsto_finsetProd _ (fun i _ => (hG i).pow (firstJetTailExponent a i))

theorem firstJetDominantTailPolynomial_vanishes_of_rescaled_relations
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) (x : ℂ)
    (G : ℕ → Fin k × Fin 2 → ℂ) (J : Fin k × Fin 2 → ℂ)
    (hG : ∀ i, Tendsto (fun n => G n i) atTop (𝓝 (J i)))
    (hrel : ∀ᶠ n : ℕ in atTop, ∑ a ∈ P.support,
      firstJetDominantCoefficient P a n x * firstJetTailMonomial (G n) a = 0) :
    MvPolynomial.eval J (firstJetDominantTailPolynomial P) = 0 := by
  have hlim : Tendsto
      (fun n => ∑ a ∈ P.support,
        firstJetDominantCoefficient P a n x * firstJetTailMonomial (G n) a)
      atTop
      (𝓝 (∑ a ∈ P.support,
        firstJetDominantLimitCoefficient P a * firstJetTailMonomial J a)) := by
    apply tendsto_finsetSum
    intro a ha
    exact (tendsto_firstJetDominantCoefficient P ha x).mul
      (tendsto_firstJetTailMonomial hG a)
  have hzero : Tendsto
      (fun n => ∑ a ∈ P.support,
        firstJetDominantCoefficient P a n x * firstJetTailMonomial (G n) a)
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hrel.mono fun _ hn => hn.symm)
  rw [eval_firstJetDominantTailPolynomial]
  exact tendsto_nhds_unique hlim hzero

theorem firstJetDominantRelation_of_relation_at
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (n : ℕ) (x : ℂ) (y : Fin k × Fin 2 → ℂ)
    (hP : MvPolynomial.eval
      (fun i => i.elim (fun _ =>
        -(n : ℂ) + reciprocalGammaFactorialScale n * x) y) P = 0) :
    ∑ a ∈ P.support,
      firstJetDominantCoefficient P a n x *
        firstJetTailMonomial
          (firstJetScaleTail (reciprocalGammaFactorialScale n) y) a = 0 := by
  let point : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  calc
    (∑ a ∈ P.support,
      firstJetDominantCoefficient P a n x *
        firstJetTailMonomial
          (firstJetScaleTail (reciprocalGammaFactorialScale n) y) a) =
        (reciprocalGammaFactorialScale n ^ firstJetTopDerivativeDegree P /
          (((n + 1 : ℕ) : ℂ) ^ firstJetTopPointDegree P)) *
          ∑ a ∈ P.support, MvPolynomial.coeff a P *
            (point ^ firstJetPointExponent a * firstJetTailMonomial y a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [firstJetDominantCoefficient, factorialBlowUpMonomialCoefficient,
        firstJetTailMonomial_scale]
      have hD := firstJetFullDerivativeDegree_le_top ha
      have hscale : reciprocalGammaFactorialScale n ^
            (firstJetTopDerivativeDegree P - firstJetFullDerivativeDegree a) *
          reciprocalGammaFactorialScale n ^ firstJetFullDerivativeDegree a =
          reciprocalGammaFactorialScale n ^ firstJetTopDerivativeDegree P := by
        rw [← pow_add, Nat.sub_add_cancel hD]
      dsimp only [point]
      calc
        MvPolynomial.coeff a P *
              (reciprocalGammaFactorialScale n ^
                    (firstJetTopDerivativeDegree P - firstJetFullDerivativeDegree a) *
                  (-↑n + reciprocalGammaFactorialScale n * x) ^
                    firstJetPointExponent a /
                ↑(n + 1) ^ firstJetTopPointDegree P) *
            (reciprocalGammaFactorialScale n ^ firstJetFullDerivativeDegree a *
              firstJetTailMonomial y a) =
          (reciprocalGammaFactorialScale n ^
                (firstJetTopDerivativeDegree P - firstJetFullDerivativeDegree a) *
              reciprocalGammaFactorialScale n ^ firstJetFullDerivativeDegree a) /
              ↑(n + 1) ^ firstJetTopPointDegree P *
            (MvPolynomial.coeff a P *
              ((-↑n + reciprocalGammaFactorialScale n * x) ^
                firstJetPointExponent a * firstJetTailMonomial y a)) := by ring
        _ = _ := by rw [hscale]
    _ = (reciprocalGammaFactorialScale n ^ firstJetTopDerivativeDegree P /
          (((n + 1 : ℕ) : ℂ) ^ firstJetTopPointDegree P)) *
        MvPolynomial.eval (fun i => i.elim (fun _ => point) y) P := by
      rw [eval_firstJetPolynomial_as_sum]
    _ = 0 := by
      rw [show MvPolynomial.eval (fun i => i.elim (fun _ => point) y) P = 0 by
        simpa [point] using hP, mul_zero]

end

end GaloisForLFunctions
