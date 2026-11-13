import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation

/-!
# Positive-square energy of finite causal critical polynomials

Successive nonnegative delay increments parametrize ordered causal sums.
Removing the first delay and its ground-state coefficient leaves an exact
positive weighted square. Iteration diagonalizes the full arithmetic energy
in weighted suffix profiles.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

/-- A finite causal sum, parametrized by consecutive delay increments and real coefficients. -/
def criticalCausalPolynomial (F : ℝ → ℝ) : List (ℝ≥0 × ℝ) → ℝ → ℝ
  | [] => fun _ => 0
  | (h, c) :: l => fun u => criticalCausalPolynomial F l (u + h) + c * F (u + h)

/-- Cumulative delays convert increment coordinates to ordinary causal translates. -/
def criticalCausalCumulativeDelays : List (ℝ≥0 × ℝ) → List (ℝ≥0 × ℝ)
  | [] => []
  | (h, c) :: l => (h, c) ::
      (criticalCausalCumulativeDelays l).map (fun p => (h + p.1, p.2))

theorem criticalCausalPolynomial_eq_sum (F : ℝ → ℝ) (l : List (ℝ≥0 × ℝ)) (u : ℝ) :
    criticalCausalPolynomial F l u =
      ((criticalCausalCumulativeDelays l).map (fun p => p.2 * F (u + p.1))).sum := by
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    simp only [criticalCausalPolynomial, criticalCausalCumulativeDelays,
      List.map_cons, List.sum_cons, List.map_map, Function.comp_def, NNReal.coe_add]
    rw [ih]
    simp only [add_assoc]
    exact add_comm _ _

/-- Every ordered list of absolute delays is represented by nonnegative increments. -/
theorem exists_criticalCausalCumulativeDelays_from (l : List (ℝ≥0 × ℝ))
    (p : ℝ≥0) (hp : ∀ q ∈ l, p ≤ q.1)
    (hord : l.Pairwise (fun q r => q.1 ≤ r.1)) :
    ∃ k : List (ℝ≥0 × ℝ),
      (criticalCausalCumulativeDelays k).map (fun q => (p + q.1, q.2)) = l := by
  induction l generalizing p with
  | nil => exact ⟨[], rfl⟩
  | cons q l ih =>
    rcases q with ⟨s, c⟩
    rcases List.pairwise_cons.mp hord with ⟨hs, htail⟩
    obtain ⟨k, hk⟩ := ih s hs htail
    let h : ℝ≥0 := ⟨(s : ℝ) - p, sub_nonneg.mpr (hp (s, c) List.mem_cons_self)⟩
    have hph : p + h = s := by
      apply Subtype.ext
      change (p : ℝ) + ((s : ℝ) - p) = s
      ring
    refine ⟨(h, c) :: k, ?_⟩
    simp only [criticalCausalCumulativeDelays, List.map_cons, List.map_map,
      Function.comp_def, ← add_assoc, hph]
    rw [hk]

theorem exists_criticalCausalCumulativeDelays (l : List (ℝ≥0 × ℝ))
    (hord : l.Pairwise (fun q r => q.1 ≤ r.1)) :
    ∃ k : List (ℝ≥0 × ℝ), criticalCausalCumulativeDelays k = l := by
  obtain ⟨k, hk⟩ := exists_criticalCausalCumulativeDelays_from l 0
    (fun q _ => q.1.2) hord
  refine ⟨k, ?_⟩
  simp only [zero_add, Prod.mk.eta] at hk
  change (criticalCausalCumulativeDelays k).map id = l at hk
  simpa only [List.map_id] using hk

/-- Each square is the weighted mass of a suffix before its first delay. -/
def criticalCausalSquareTerms (F : ℝ → ℝ) : List (ℝ≥0 × ℝ) → List ℝ
  | [] => []
  | (h, c) :: l =>
      ((Real.exp (8 * (h : ℝ)) - 1) *
        criticalHalfLineExponentialPair
          (fun u => criticalCausalPolynomial F l u + c * F u)
          (fun u => criticalCausalPolynomial F l u + c * F u)) ::
      criticalCausalSquareTerms F l

/-- Ordered absolute tails carry the differences of successive exponential delay weights. -/
def criticalCausalOrderedSquareTerms (F : ℝ → ℝ) (p : ℝ) :
    List (ℝ≥0 × ℝ) → List ℝ
  | [] => []
  | (h, c) :: l =>
      ((Real.exp (-(8 * p)) - Real.exp (-(8 * (p + h)))) *
        criticalHalfLineExponentialPair
          (fun u => criticalCausalPolynomial F ((h, c) :: l) (u + p))
          (fun u => criticalCausalPolynomial F ((h, c) :: l) (u + p))) ::
      criticalCausalOrderedSquareTerms F (p + h) l

/-- Weighted translation makes the ordered tail formula identical to the successive-square formula. -/
theorem criticalCausalOrderedSquareTerms_eq (F : ℝ → ℝ)
    (l : List (ℝ≥0 × ℝ)) (p : ℝ) :
    criticalCausalOrderedSquareTerms F p l = criticalCausalSquareTerms F l := by
  induction l generalizing p with
  | nil => rfl
  | cons q l ih =>
    rcases q with ⟨h, c⟩
    simp only [criticalCausalOrderedSquareTerms, criticalCausalSquareTerms, ih]
    congr 1
    have hfun : (fun u => criticalCausalPolynomial F ((h, c) :: l) (u + p)) =
        (fun u => (fun v => criticalCausalPolynomial F l v + c * F v) (u + (p + h))) := by
      funext u
      simp only [criticalCausalPolynomial, add_assoc]
    rw [hfun, criticalHalfLineExponentialPair_comp_add_right
      (fun v => criticalCausalPolynomial F l v + c * F v)
      (fun v => criticalCausalPolynomial F l v + c * F v) (p + h)]
    have hcoef : (Real.exp (-(8 * p)) - Real.exp (-(8 * (p + h)))) *
        Real.exp (8 * (p + h)) = Real.exp (8 * (h : ℝ)) - 1 := by
      rw [sub_mul, ← Real.exp_add, ← Real.exp_add]
      rw [show -(8 * p) + 8 * (p + h) = 8 * (h : ℝ) by ring,
        neg_add_cancel, Real.exp_zero]
    rw [← mul_assoc, hcoef]

theorem CriticalHalfLineEnergyDomain.causalPolynomial {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (l : List (ℝ≥0 × ℝ)) :
    CriticalHalfLineEnergyDomain (criticalCausalPolynomial F l) := by
  induction l with
  | nil => simpa only [criticalCausalPolynomial, zero_mul] using hF.const_mul 0
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    exact (ih.add_const_mul hF c).causalTranslate h.2

theorem criticalHalfLineExponentialPair_self_nonneg (F : ℝ → ℝ) :
    0 ≤ criticalHalfLineExponentialPair F F := by
  rw [criticalHalfLineExponentialPair_self]
  exact integral_nonneg fun u => mul_nonneg (sq_nonneg (F u)) (Real.exp_nonneg _)

theorem criticalCausalSquareTerms_nonneg (F : ℝ → ℝ) (l : List (ℝ≥0 × ℝ)) :
    ∀ q ∈ criticalCausalSquareTerms F l, 0 ≤ q := by
  induction l with
  | nil => simp only [criticalCausalSquareTerms, List.not_mem_nil, false_implies, implies_true]
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by norm_num) h.2)))
        (criticalHalfLineExponentialPair_self_nonneg _)
    · exact ih q hq

theorem criticalCausalOrderedSquareTerms_nonneg (F : ℝ → ℝ)
    (l : List (ℝ≥0 × ℝ)) (p : ℝ) :
    ∀ q ∈ criticalCausalOrderedSquareTerms F p l, 0 ≤ q := by
  rw [criticalCausalOrderedSquareTerms_eq]
  exact criticalCausalSquareTerms_nonneg F l

/-- The full critical arithmetic energy is exactly a finite sum of nonnegative weighted squares. -/
theorem criticalHalfLineFullEnergy_causalPolynomial_eq_squares
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) :
    criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F l) =
      criticalAliasCoefficient W₀ * (criticalCausalSquareTerms F l).sum := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  induction l with
  | nil =>
    have hz := criticalHalfLineFullEnergy_const_mul W₀ F 0
    simpa only [criticalCausalPolynomial, criticalCausalSquareTerms, List.sum_nil,
      zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero] using hz
  | cons p l ih =>
    rcases p with ⟨h, c⟩
    have hd := (hdF.causalPolynomial l).add_const_mul hdF c
    have he := criticalHalfLineFullEnergy_comp_add_right hd h W₀
      (fun _ hu => hd.support _ (add_nonneg hu h.2))
    have hg := criticalHalfLineFullEnergy_causal_ground_shear hW hthreshold hF
      (hdF.causalPolynomial l) (h := 0) le_rfl c
    simp only [add_zero, mul_zero, Real.exp_zero, sub_self, zero_mul] at hg
    rw [hg, ih, ← criticalHalfLineExponentialPair_self] at he
    change criticalHalfLineFullEnergy W₀
      (fun u => criticalCausalPolynomial F l (u + h) + c * F (u + h)) = _ at he
    rw [criticalCausalPolynomial, he]
    simp only [criticalCausalSquareTerms, List.sum_cons]
    ring

/-- Absolute cumulative delays give the exact telescoping sum of weighted tail squares. -/
theorem criticalHalfLineFullEnergy_causalPolynomial_eq_ordered_squares
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) :
    criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F l) =
      criticalAliasCoefficient W₀ * (criticalCausalOrderedSquareTerms F 0 l).sum := by
  rw [criticalCausalOrderedSquareTerms_eq]
  exact criticalHalfLineFullEnergy_causalPolynomial_eq_squares hW hthreshold hF l

/-- Every ordered finite causal sum has the exact positive tail-square representation. -/
theorem criticalHalfLineFullEnergy_ordered_sum_eq_squares
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (l : List (ℝ≥0 × ℝ)) (hord : l.Pairwise (fun q r => q.1 ≤ r.1)) :
    ∃ k : List (ℝ≥0 × ℝ), criticalCausalCumulativeDelays k = l ∧
      criticalHalfLineFullEnergy W₀
        (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) =
          criticalAliasCoefficient W₀ * (criticalCausalOrderedSquareTerms F 0 k).sum := by
  obtain ⟨k, hk⟩ := exists_criticalCausalCumulativeDelays l hord
  refine ⟨k, hk, ?_⟩
  have hfun : (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) =
      criticalCausalPolynomial F k := by
    funext u
    rw [criticalCausalPolynomial_eq_sum, hk]
  rw [hfun]
  exact criticalHalfLineFullEnergy_causalPolynomial_eq_ordered_squares hW hthreshold hF k

/-- Every actual critical state has the exact positive-square formula for all finite causal sums. -/
theorem riemannHypothesis_or_exists_causalPolynomial_positive_square_formula :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ l : List (ℝ≥0 × ℝ),
        CriticalHalfLineEnergyDomain (criticalCausalPolynomial F l) ∧
        (∀ q ∈ criticalCausalSquareTerms F l, 0 ≤ q) ∧
        criticalHalfLineFullEnergy W₀ (criticalCausalPolynomial F l) =
          criticalAliasCoefficient W₀ * (criticalCausalSquareTerms F l).sum := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro l
    exact ⟨(criticalHalfLineEnergyDomain_of_groundState hF).causalPolynomial l,
      criticalCausalSquareTerms_nonneg F l,
      criticalHalfLineFullEnergy_causalPolynomial_eq_squares hW ht hF l⟩

/-- Failure of RH supplies the ordered tail-square formula for every actual finite causal sum. -/
theorem riemannHypothesis_or_exists_ordered_causal_tail_square_formula :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ l : List (ℝ≥0 × ℝ), l.Pairwise (fun q r => q.1 ≤ r.1) →
        ∃ k : List (ℝ≥0 × ℝ), criticalCausalCumulativeDelays k = l ∧
          (∀ q ∈ criticalCausalOrderedSquareTerms F 0 k, 0 ≤ q) ∧
          criticalHalfLineFullEnergy W₀
            (fun u => (l.map (fun p => p.2 * F (u + p.1))).sum) =
              criticalAliasCoefficient W₀ * (criticalCausalOrderedSquareTerms F 0 k).sum := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro l hord
    obtain ⟨k, hk, he⟩ := criticalHalfLineFullEnergy_ordered_sum_eq_squares hW ht hF l hord
    exact ⟨k, hk, criticalCausalOrderedSquareTerms_nonneg F k 0, he⟩

#print axioms criticalCausalPolynomial_eq_sum
#print axioms riemannHypothesis_or_exists_causalPolynomial_positive_square_formula
#print axioms riemannHypothesis_or_exists_ordered_causal_tail_square_formula

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
