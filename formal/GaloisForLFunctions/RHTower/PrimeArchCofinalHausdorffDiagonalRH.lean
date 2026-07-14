import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH

/-!
# Cofinal Hausdorff diagonals already force RH

The calibrated Hausdorff criterion does not require an eventual two-index quadrant. It is enough
that arbitrarily large complete Bernstein diagonals are nonnegative. At such a degree the diagonal
values are the masses of the canonical finite Hausdorff--Bernstein atomic approximation. Choosing
one admissible degree beyond every cutoff gives a cofinal sequence of positive atomic systems;
their unconditional Bernstein convergence supplies the complete source moment cone and hence RH.
-/

open scoped BigOperators Polynomial
open Polynomial Filter Topology

namespace RHTower

noncomputable section

open HTGeometry

/-- Arbitrarily large complete calibrated Hausdorff diagonals are nonnegative. The diagonal
indexed by `N` has total Bernstein degree `N + 1`. -/
def CofinalScaledHausdorffDiagonalsNonnegative
    (R : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ ∀ k : ℕ, k ≤ N + 1 →
    0 ≤ scaledHausdorffMomentDifference R m k (N + 1 - k)

/-- One nonnegative calibrated diagonal gives nonnegative Bernstein masses for the
radius-normalized moment sequence at the same degree. -/
theorem momentFunctional_bernsteinPolynomial_nonnegative_of_scaledHausdorffDiagonal
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ} {N : ℕ}
    (hdiag : ∀ k : ℕ, k ≤ N →
      0 ≤ scaledHausdorffMomentDifference R m k (N - k)) :
    ∀ k : ℕ, 0 ≤ momentFunctional (radiusNormalizedMoment R m)
      (bernsteinPolynomial ℝ N k) := by
  intro k
  by_cases hk : k ≤ N
  · have hscale :
        momentFunctional (radiusNormalizedMoment R m) (bernsteinPolynomial ℝ N k) =
          (N.choose k : ℝ) *
            momentFunctional (radiusNormalizedMoment R m)
              ((Polynomial.X : Polynomial ℝ) ^ k *
                (1 - Polynomial.X) ^ (N - k)) := by
      rw [bernsteinPolynomial]
      rw [show (N.choose k : Polynomial ℝ) * Polynomial.X ^ k *
            (1 - Polynomial.X) ^ (N - k) =
          (N.choose k : ℝ) •
            (Polynomial.X ^ k * (1 - Polynomial.X) ^ (N - k)) by
        simp [Polynomial.smul_eq_C_mul]
        ring]
      exact momentFunctional_smul _ _ _
    rw [hscale, ← hausdorffMomentDifference_eq_momentFunctional,
      hausdorffMomentDifference_radiusNormalizedMoment hR]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (hdiag k hk) (pow_nonneg hR.le _))
  · rw [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_of_not_ge hk),
      momentFunctional_zero]

/-- A single degree of nonnegative Bernstein masses gives the corresponding finite positive
atomic approximation; positivity at unrelated degrees is not needed. -/
theorem finitePositiveAtomicMomentSequence_hausdorffBernsteinAtomicMoment_of_degree
    {m : ℕ → ℝ} (N : ℕ)
    (h : ∀ k : ℕ,
      0 ≤ momentFunctional m (bernsteinPolynomial ℝ (N + 1) k)) :
    FinitePositiveAtomicMomentSequence (hausdorffBernsteinAtomicMoment m N) := by
  let mass : Fin (N + 2) → ℝ := fun i =>
    momentFunctional m (bernsteinPolynomial ℝ (N + 1) i)
  let node : Fin (N + 2) → ℝ := fun i =>
    ((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)
  refine ⟨N + 2, mass, node, ?_, ?_, ?_⟩
  · intro i
    exact h i
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rfl

/-- Cofinal complete diagonal positivity places the full moment sequence in the local closure of
finite positive atomic systems. -/
theorem finitePositiveAtomicLocalMomentClosure_of_cofinalScaledHausdorffDiagonals
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : CofinalScaledHausdorffDiagonalsNonnegative R m) :
    FinitePositiveAtomicLocalMomentClosure m := by
  choose d hd hdiag using fun M => h M
  have hdTop : Tendsto d atTop atTop := by
    rw [tendsto_atTop]
    intro M
    exact eventually_atTop.2 ⟨M, fun n hn => le_trans hn (hd n)⟩
  let s := radiusNormalizedMoment R m
  let b : ℕ → ℕ → ℝ := fun j n =>
    R ^ n * hausdorffBernsteinAtomicMoment s (d j) n
  have hb : ∀ j, FinitePositiveAtomicMomentSequence (b j) := by
    intro j
    apply finitePositiveAtomicMomentSequence_radiusRescale hR.le
    apply finitePositiveAtomicMomentSequence_hausdorffBernsteinAtomicMoment_of_degree
    apply momentFunctional_bernsteinPolynomial_nonnegative_of_scaledHausdorffDiagonal hR
    exact hdiag j
  have htarget : (fun n => R ^ n * s n) = m := by
    funext n
    dsimp only [s, radiusNormalizedMoment]
    field_simp [hR.ne']
  apply finitePositiveAtomicLocalMomentClosure_of_tendsto hb
  rw [← htarget]
  apply tendsto_pi_nhds.mpr
  intro n
  exact ((tendsto_hausdorffBernsteinAtomicMoment_coordinate s n).comp hdTop).const_mul
    (R ^ n)

/-- Cofinal complete calibrated Hausdorff diagonals imply RH. -/
theorem riemannHypothesis_of_cofinalScaledPrimeArchHausdorffDiagonalsNonnegative
    {R : ℝ} (hR : 0 < R)
    (h : CofinalScaledHausdorffDiagonalsNonnegative R normalizedPrimeArchMoment) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
    (finitePositiveAtomicLocalMomentClosure_of_cofinalScaledHausdorffDiagonals hR h)

/-- Full calibrated Hausdorff positivity supplies arbitrarily large nonnegative diagonals. -/
theorem cofinalScaledHausdorffDiagonalsNonnegative_of_scaledHausdorffMomentDifferencesNonnegative
    {R : ℝ} {m : ℕ → ℝ}
    (h : ScaledHausdorffMomentDifferencesNonnegative R m) :
    CofinalScaledHausdorffDiagonalsNonnegative R m := by
  intro M
  exact ⟨M, le_rfl, fun k hk => h k (M + 1 - k)⟩

/-- At any positive radius containing all Xi thermal nodes, positivity on arbitrarily large
complete Hausdorff diagonals is exactly RH. -/
theorem cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis_of_node_le
    {R : ℝ} (hR : 0 < R) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R) :
    CofinalScaledHausdorffDiagonalsNonnegative R normalizedPrimeArchMoment ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_cofinalScaledPrimeArchHausdorffDiagonalsNonnegative hR
  · intro hRH
    exact cofinalScaledHausdorffDiagonalsNonnegative_of_scaledHausdorffMomentDifferencesNonnegative
      (scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
        R hnode hRH)

/-- **Endpoint cofinal-diagonal RH law.** Arbitrarily large complete diagonals, with no
compatibility required between their degrees, are equivalent to RH. -/
theorem cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis :
    CofinalScaledHausdorffDiagonalsNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      RiemannHypothesis :=
  cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis_of_node_le
    primeArchEndpointHausdorffRadius_pos
    xiThermalNode_le_primeArchEndpointHausdorffRadius

/-- **Cofinal-diagonal prime--polar endpoint law.** The target absolute-abscissa bound is
equivalent to nonnegativity on arbitrarily large complete calibrated Hausdorff diagonals. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffDiagonals
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      CofinalScaledHausdorffDiagonalsNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).trans
      ((scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis).trans
        cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis.symm)

end

end RHTower

namespace RHTower

noncomputable section

open HTGeometry

/-! ## Vanishing total negative Bernstein mass -/

/-- Total negative mass of the canonical signed Bernstein system at degree `N + 1`. -/
def hausdorffBernsteinNegativeMass (m : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin (N + 2),
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻

/-- The canonical Bernstein atomic approximation after replacing every signed mass by its
positive part. -/
def hausdorffBernsteinPositiveAtomicMoment (m : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ i : Fin (N + 2),
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁺ *
      (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n

/-- Positive-part truncation is a finite positive atomic moment sequence at every degree. -/
theorem finitePositiveAtomicMomentSequence_hausdorffBernsteinPositiveAtomicMoment
    (m : ℕ → ℝ) (N : ℕ) :
    FinitePositiveAtomicMomentSequence (hausdorffBernsteinPositiveAtomicMoment m N) := by
  refine ⟨N + 2,
    fun i => (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁺,
    fun i => ((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ),
    fun i => posPart_nonneg _,
    fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), rfl⟩

/-- The positive-part approximation differs from the signed Bernstein approximation by exactly
the atomic moment carried by the negative parts. -/
theorem hausdorffBernsteinPositiveAtomicMoment_sub_signed_eq
    (m : ℕ → ℝ) (N n : ℕ) :
    hausdorffBernsteinPositiveAtomicMoment m N n -
        hausdorffBernsteinAtomicMoment m N n =
      ∑ i : Fin (N + 2),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ *
          (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n := by
  rw [hausdorffBernsteinPositiveAtomicMoment, hausdorffBernsteinAtomicMoment]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdecomp := posPart_sub_negPart
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))
  have hdiff :
      (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁺ -
          momentFunctional m (bernsteinPolynomial ℝ (N + 1) i) =
        (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ := by
    linarith
  calc
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁺ *
          (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n -
        momentFunctional m (bernsteinPolynomial ℝ (N + 1) i) *
          (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n =
      ((momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁺ -
          momentFunctional m (bernsteinPolynomial ℝ (N + 1) i)) *
            (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n := by ring
    _ = _ := by rw [hdiff]

/-- Positive-part truncation only increases every Bernstein atomic moment. -/
theorem hausdorffBernsteinPositiveAtomicMoment_sub_signed_nonneg
    (m : ℕ → ℝ) (N n : ℕ) :
    0 ≤ hausdorffBernsteinPositiveAtomicMoment m N n -
      hausdorffBernsteinAtomicMoment m N n := by
  rw [hausdorffBernsteinPositiveAtomicMoment_sub_signed_eq]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (negPart_nonneg _)
    (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

/-- At every moment coordinate, the error introduced by positive-part truncation is bounded by
the single scalar total negative Bernstein mass. -/
theorem hausdorffBernsteinPositiveAtomicMoment_sub_signed_le_negativeMass
    (m : ℕ → ℝ) (N n : ℕ) :
    hausdorffBernsteinPositiveAtomicMoment m N n -
        hausdorffBernsteinAtomicMoment m N n ≤
      hausdorffBernsteinNegativeMass m N := by
  rw [hausdorffBernsteinPositiveAtomicMoment_sub_signed_eq,
    hausdorffBernsteinNegativeMass]
  apply Finset.sum_le_sum
  intro i hi
  have hnode0 : 0 ≤ ((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnode1 : ((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (by omega : (i : ℕ) ≤ N + 1)
  calc
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ *
        (((i : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ n ≤
      (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hnode0 hnode1) (negPart_nonneg _)
    _ = _ := mul_one _

/-- Along some cofinal degree schedule, the single scalar total negative Bernstein mass tends to
zero. The monotone defect theorem below shows that this forces exact positivity at every degree. -/
def CofinalHausdorffBernsteinNegativeMassVanishing
    (R : ℝ) (m : ℕ → ℝ) : Prop :=
  ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧
    Tendsto
      (fun j => hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) (d j))
      atTop (nhds 0)

/-- Cofinal vanishing of total negative Bernstein mass places the full moment sequence in the
local closure of finite positive atomic systems. -/
theorem finitePositiveAtomicLocalMomentClosure_of_cofinalHausdorffBernsteinNegativeMassVanishing
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : CofinalHausdorffBernsteinNegativeMassVanishing R m) :
    FinitePositiveAtomicLocalMomentClosure m := by
  obtain ⟨d, hd, hmass⟩ := h
  let s := radiusNormalizedMoment R m
  let b : ℕ → ℕ → ℝ := fun j n =>
    R ^ n * hausdorffBernsteinPositiveAtomicMoment s (d j) n
  have hb : ∀ j, FinitePositiveAtomicMomentSequence (b j) := by
    intro j
    exact finitePositiveAtomicMomentSequence_radiusRescale hR.le
      (finitePositiveAtomicMomentSequence_hausdorffBernsteinPositiveAtomicMoment s (d j))
  have htarget : (fun n => R ^ n * s n) = m := by
    funext n
    dsimp only [s, radiusNormalizedMoment]
    field_simp [hR.ne']
  apply finitePositiveAtomicLocalMomentClosure_of_tendsto hb
  rw [← htarget]
  apply tendsto_pi_nhds.mpr
  intro n
  have hsigned : Tendsto (fun j => hausdorffBernsteinAtomicMoment s (d j) n)
      atTop (nhds (s n)) :=
    (tendsto_hausdorffBernsteinAtomicMoment_coordinate s n).comp hd
  have herr : Tendsto
      (fun j => hausdorffBernsteinPositiveAtomicMoment s (d j) n -
        hausdorffBernsteinAtomicMoment s (d j) n)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro j
      exact hausdorffBernsteinPositiveAtomicMoment_sub_signed_nonneg s (d j) n
    · intro j
      exact hausdorffBernsteinPositiveAtomicMoment_sub_signed_le_negativeMass s (d j) n
    · simpa only [s] using hmass
  have hpos : Tendsto (fun j => hausdorffBernsteinPositiveAtomicMoment s (d j) n)
      atTop (nhds (s n)) := by
    convert hsigned.add herr using 1
    · funext j
      ring
    · ring
  exact hpos.const_mul (R ^ n)

/-- Vanishing total negative Bernstein mass along a cofinal degree schedule implies RH. -/
theorem riemannHypothesis_of_cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing
    {R : ℝ} (hR : 0 < R)
    (h : CofinalHausdorffBernsteinNegativeMassVanishing R normalizedPrimeArchMoment) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
    (finitePositiveAtomicLocalMomentClosure_of_cofinalHausdorffBernsteinNegativeMassVanishing
      hR h)

/-- Complete calibrated Hausdorff positivity makes every total negative Bernstein mass vanish. -/
theorem cofinalHausdorffBernsteinNegativeMassVanishing_of_scaledHausdorffMomentDifferencesNonnegative
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : ScaledHausdorffMomentDifferencesNonnegative R m) :
    CofinalHausdorffBernsteinNegativeMassVanishing R m := by
  let s := radiusNormalizedMoment R m
  have hbern (N : ℕ) : ∀ k : ℕ,
      0 ≤ momentFunctional s (bernsteinPolynomial ℝ (N + 1) k) := by
    apply momentFunctional_bernsteinPolynomial_nonnegative_of_scaledHausdorffDiagonal hR
    intro k hk
    exact h k (N + 1 - k)
  refine ⟨fun n => n, tendsto_id, ?_⟩
  have hzero : (fun j => hausdorffBernsteinNegativeMass s j) = fun _ => 0 := by
    funext j
    rw [hausdorffBernsteinNegativeMass]
    apply Finset.sum_eq_zero
    intro i hi
    exact negPart_eq_zero.mpr (hbern j i)
  rw [hzero]
  exact tendsto_const_nhds

/-- At a positive radius containing every Xi thermal node, cofinal vanishing of one scalar
negative-mass defect is exactly RH. -/
theorem cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis_of_node_le
    {R : ℝ} (hR : 0 < R) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R) :
    CofinalHausdorffBernsteinNegativeMassVanishing R normalizedPrimeArchMoment ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing hR
  · intro hRH
    exact cofinalHausdorffBernsteinNegativeMassVanishing_of_scaledHausdorffMomentDifferencesNonnegative
      hR (scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
        R hnode hRH)

/-- **Scalar Bernstein negative-mass RH law.** RH is equivalent to the existence of a cofinal
sequence of degrees along which the total negative Bernstein mass tends to zero. -/
theorem cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis :
    CofinalHausdorffBernsteinNegativeMassVanishing primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      RiemannHypothesis :=
  cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis_of_node_le
    primeArchEndpointHausdorffRadius_pos xiThermalNode_le_primeArchEndpointHausdorffRadius

/-- **Scalar negative-mass prime--polar endpoint law.** The target absolute-abscissa bound is
equivalent to a single total negative Bernstein mass tending to zero along some cofinal degree
schedule. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalBernsteinNegativeMassVanishing
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      CofinalHausdorffBernsteinNegativeMassVanishing primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).trans
      ((scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis).trans
        cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.symm)

end

end RHTower

namespace RHTower

noncomputable section

open HTGeometry

/-! ## Monotone order-unit defect under Bernstein degree elevation -/

/-- Bernstein degree elevation. The coefficients are the two adjacent barycentric weights. -/
theorem bernsteinPolynomial_degree_elevation (n i : ℕ) (hi : i ≤ n) :
    bernsteinPolynomial ℝ n i =
      (((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) •
          bernsteinPolynomial ℝ (n + 1) i +
        (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) •
          bernsteinPolynomial ℝ (n + 1) (i + 1) := by
  rw [bernsteinPolynomial, bernsteinPolynomial, bernsteinPolynomial]
  have hleft :
      (n.choose i : ℝ) * (n + 1 : ℝ) =
        ((n + 1).choose i : ℝ) * ((n - i) + 1 : ℕ) := by
    rw [← show n + 1 - i = (n - i) + 1 by omega]
    exact_mod_cast Nat.choose_mul_succ_eq n i
  have hright :
      (n + 1 : ℝ) * (n.choose i : ℝ) =
        ((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n i
  have hc : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [← sub_eq_zero]
  rw [← smul_eq_zero_iff_right hc]
  rw [smul_sub]
  apply sub_eq_zero.mpr
  simp only [smul_add, smul_smul]
  rw [mul_div_cancel₀ _ hc, mul_div_cancel₀ _ hc]
  simp only [smul_eq_C_mul]
  rw [show n + 1 - i = (n - i) + 1 by omega]
  rw [show n + 1 - (i + 1) = n - i by omega]
  rw [pow_succ, pow_succ]
  have hleftP :
      Polynomial.C ((n.choose i : ℝ) * (n + 1 : ℝ)) =
        Polynomial.C (((n + 1).choose i : ℝ) * ((n - i) + 1 : ℕ)) :=
    congrArg Polynomial.C hleft
  have hrightP :
      Polynomial.C ((n + 1 : ℝ) * (n.choose i : ℝ)) =
        Polynomial.C (((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℕ)) :=
    congrArg Polynomial.C hright
  simp only [map_mul, Nat.cast_add, Nat.cast_one] at hleftP hrightP ⊢
  rw [show (n.choose i : Polynomial ℝ) = Polynomial.C (n.choose i : ℝ) by simp,
    show ((n + 1).choose i : Polynomial ℝ) =
      Polynomial.C ((n + 1).choose i : ℝ) by simp,
    show ((n + 1).choose (i + 1) : Polynomial ℝ) =
      Polynomial.C ((n + 1).choose (i + 1) : ℝ) by simp]
  linear_combination
    (Polynomial.X ^ i * (1 - Polynomial.X) ^ ((n - i) + 1)) * hleftP +
    (Polynomial.X ^ (i + 1) * (1 - Polynomial.X) ^ (n - i)) * hrightP

/-- The negative part is subadditive. -/
lemma negPart_add_le_add_negPart (x y : ℝ) :
    (x + y)⁻ ≤ x⁻ + y⁻ := by
  rw [negPart_def, negPart_def, negPart_def]
  apply max_le
  · calc
      -(x + y) = -x + -y := by ring
      _ ≤ max (-x) 0 + max (-y) 0 :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- Multiplication by a nonnegative scalar commutes with the negative part. -/
lemma negPart_mul_of_nonneg (a x : ℝ) (ha : 0 ≤ a) :
    (a * x)⁻ = a * x⁻ := by
  rw [negPart_def, negPart_def]
  rw [show -(a * x) = a * (-x) by ring]
  rw [mul_max_of_nonneg (-x) 0 ha, mul_zero]

/-- The two barycentric columns in Bernstein degree elevation have total weight one. -/
lemma bernstein_elevation_weighted_sum (n : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n + 1),
        ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * g i +
          (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) * g (i + 1)) =
      ∑ i ∈ Finset.range (n + 2), g i := by
  have hc : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ i ∈ Finset.range (n + 1),
          (((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * g i) =
        ∑ i ∈ Finset.range (n + 2),
          (((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) * g i := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp
  have hsecond :
      (∑ i ∈ Finset.range (n + 1),
          (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) * g (i + 1)) =
        ∑ i ∈ Finset.range (n + 2),
          ((i : ℝ) / (n + 1 : ℝ)) * g i := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp
  rw [hfirst, hsecond, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hinat : i ≤ n + 1 := by
    simp only [Finset.mem_range] at hi
    omega
  rw [Nat.cast_sub hinat]
  field_simp
  push_cast
  ring

/-- Total Bernstein negative mass is nondecreasing under one degree elevation. -/
lemma bernsteinNegativeMassDegree_mono (m : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (momentFunctional m (bernsteinPolynomial ℝ n i))⁻) ≤
      ∑ i ∈ Finset.range (n + 2),
        (momentFunctional m (bernsteinPolynomial ℝ (n + 1) i))⁻ := by
  calc
    (∑ i ∈ Finset.range (n + 1),
        (momentFunctional m (bernsteinPolynomial ℝ n i))⁻) ≤
      ∑ i ∈ Finset.range (n + 1),
        ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) *
            (momentFunctional m (bernsteinPolynomial ℝ (n + 1) i))⁻ +
          (((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) *
            (momentFunctional m (bernsteinPolynomial ℝ (n + 1) (i + 1)))⁻) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by
        simp only [Finset.mem_range] at hi
        omega
      rw [bernsteinPolynomial_degree_elevation n i hin,
        momentFunctional_add, momentFunctional_smul, momentFunctional_smul]
      calc
        (_ + _)⁻ ≤
            ((((n + 1 - i : ℕ) : ℝ) / (n + 1 : ℝ)) *
                momentFunctional m (bernsteinPolynomial ℝ (n + 1) i))⁻ +
              ((((i + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) *
                momentFunctional m (bernsteinPolynomial ℝ (n + 1) (i + 1)))⁻ :=
          negPart_add_le_add_negPart _ _
        _ = _ := by
          rw [negPart_mul_of_nonneg, negPart_mul_of_nonneg]
          · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
          · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    _ = _ := bernstein_elevation_weighted_sum n
      (fun i => (momentFunctional m (bernsteinPolynomial ℝ (n + 1) i))⁻)

/-- **Monotone Bernstein defect law.** The total negative mass of the canonical Bernstein
system is nondecreasing with its degree. -/
theorem hausdorffBernsteinNegativeMass_monotone (m : ℕ → ℝ) :
    Monotone (hausdorffBernsteinNegativeMass m) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [hausdorffBernsteinNegativeMass, hausdorffBernsteinNegativeMass]
  calc
    (∑ i : Fin (N + 2),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻) =
      ∑ i ∈ Finset.range (N + 2),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ =>
          (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻) (N + 2)
    _ ≤ ∑ i ∈ Finset.range (N + 3),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 2) i))⁻ := by
      convert bernsteinNegativeMassDegree_mono m (N + 1) using 1
    _ = ∑ i : Fin (N + 3),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 2) i))⁻ :=
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ =>
          (momentFunctional m (bernsteinPolynomial ℝ (N + 2) i))⁻) (N + 3)).symm
    _ = ∑ i : Fin (N + 1 + 2),
        (momentFunctional m (bernsteinPolynomial ℝ (N + 1 + 1) i))⁻ := by
      congr 1

/-- Cofinal convergence of the monotone negative-mass defect to zero forces its exact vanishing
at every degree. This is the positive rigidity content of the cofinal condition. -/
theorem hausdorffBernsteinNegativeMass_eq_zero_of_cofinalVanishing
    {R : ℝ} {m : ℕ → ℝ}
    (h : CofinalHausdorffBernsteinNegativeMassVanishing R m) (N : ℕ) :
    hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) N = 0 := by
  obtain ⟨d, hd, hmass⟩ := h
  let E := hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m)
  have hmono : Monotone E := hausdorffBernsteinNegativeMass_monotone _
  have hdN : ∀ᶠ j in atTop, N ≤ d j := (tendsto_atTop.1 hd) N
  have hle : ∀ᶠ j in atTop, E N ≤ E (d j) := hdN.mono (fun _ hj => hmono hj)
  have hnonneg : 0 ≤ E N := by
    apply Finset.sum_nonneg
    intro i hi
    exact negPart_nonneg _
  have hnonpos : E N ≤ 0 := ge_of_tendsto hmass hle
  exact le_antisymm hnonpos hnonneg

/-- Total Bernstein negative mass is always nonnegative. -/
theorem hausdorffBernsteinNegativeMass_nonneg (m : ℕ → ℝ) (N : ℕ) :
    0 ≤ hausdorffBernsteinNegativeMass m N := by
  rw [hausdorffBernsteinNegativeMass]
  exact Finset.sum_nonneg fun _ _ => negPart_nonneg _

/-- **Cofinal zero-rigidity.**  Because degree elevation makes total Bernstein negativity
nondecreasing, convergence to zero along any cofinal degree schedule is equivalent to exact
vanishing at every finite degree. -/
theorem cofinalHausdorffBernsteinNegativeMassVanishing_iff_forall_eq_zero
    (R : ℝ) (m : ℕ → ℝ) :
    CofinalHausdorffBernsteinNegativeMassVanishing R m ↔
      ∀ N : ℕ,
        hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) N = 0 := by
  constructor
  · intro h N
    exact hausdorffBernsteinNegativeMass_eq_zero_of_cofinalVanishing h N
  · intro hzero
    refine ⟨fun n => n, tendsto_id, ?_⟩
    have hfun :
        (fun n : ℕ =>
          hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) n) =
            fun _ => 0 := by
      funext n
      exact hzero n
    rw [hfun]
    exact tendsto_const_nhds

/-- Failure of cofinal zero-rigidity produces a finite positive defect that persists under every
later Bernstein refinement. -/
theorem exists_persistent_hausdorffBernsteinNegativeMass_of_not_cofinal
    {R : ℝ} {m : ℕ → ℝ}
    (h : ¬ CofinalHausdorffBernsteinNegativeMassVanishing R m) :
    ∃ N : ℕ,
      0 < hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) N ∧
      ∀ M : ℕ, N ≤ M →
        hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) N ≤
          hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m) M := by
  let E := hausdorffBernsteinNegativeMass (radiusNormalizedMoment R m)
  have hex : ∃ N : ℕ, E N ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h ((cofinalHausdorffBernsteinNegativeMassVanishing_iff_forall_eq_zero R m).2 hall)
  obtain ⟨N, hN⟩ := hex
  have hpos : 0 < E N :=
    lt_of_le_of_ne (hausdorffBernsteinNegativeMass_nonneg _ N) (Ne.symm hN)
  exact ⟨N, hpos, fun M hNM => hausdorffBernsteinNegativeMass_monotone _ hNM⟩

/-- **Prime--archimedean Bernstein phase dichotomy.**  False RH is equivalent to the appearance
of a strictly positive finite-degree order-unit defect which survives at every finer Bernstein
degree. -/
theorem not_riemannHypothesis_iff_exists_persistent_primeArchBernsteinNegativeMass :
    ¬ RiemannHypothesis ↔
      ∃ N : ℕ,
        0 < hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) N ∧
        ∀ M : ℕ, N ≤ M →
          hausdorffBernsteinNegativeMass
              (radiusNormalizedMoment primeArchEndpointHausdorffRadius
                normalizedPrimeArchMoment) N ≤
            hausdorffBernsteinNegativeMass
              (radiusNormalizedMoment primeArchEndpointHausdorffRadius
                normalizedPrimeArchMoment) M := by
  constructor
  · intro hnot
    apply exists_persistent_hausdorffBernsteinNegativeMass_of_not_cofinal
    intro hcofinal
    exact hnot
      (cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.mp
        hcofinal)
  · rintro ⟨N, hpos, _⟩ hRH
    have hcofinal :=
      cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.mpr hRH
    have hzero :=
      hausdorffBernsteinNegativeMass_eq_zero_of_cofinalVanishing hcofinal N
    linarith

end

end RHTower
