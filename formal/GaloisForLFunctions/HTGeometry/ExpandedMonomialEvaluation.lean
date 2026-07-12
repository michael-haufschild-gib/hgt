import GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Coefficient-uniform upper-half-plane evaluation of expanded jet monomials

Distinct monomials remain linearly independent after their variables are restricted to any box
whose coordinate sets are infinite.  Consequently every finite differential-monomial pattern and
polynomial coefficient-degree bound has a square full-rank evaluation packet with every base
evaluation point arbitrarily high in the upper half-plane.  One packet detects every complex
coefficient vector of that pattern simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Linear evaluation of multivariate polynomials on a coordinate box. -/
noncomputable def restrictedEvaluationLinearMap
    (τ : Type*) (s : τ → Set ℂ) :
    MvPolynomial τ ℂ →ₗ[ℂ] (↥(Set.pi Set.univ s) → ℂ) where
  toFun P x := MvPolynomial.eval x.1 P
  map_add' P Q := by funext x; simp
  map_smul' c P := by funext x; simp

/-- Evaluation on a box with infinite coordinate sets is injective on complex multivariate
polynomials. -/
theorem restrictedEvaluationLinearMap_injective
    {τ : Type*} (s : τ → Set ℂ) (hs : ∀ i, (s i).Infinite) :
    Function.Injective (restrictedEvaluationLinearMap τ s) := by
  intro P Q h
  apply MvPolynomial.funext_set s hs
  intro x hx
  exact congrFun h ⟨x, hx⟩

/-- Distinct monomials remain linearly independent as functions on every box with infinite sides. -/
theorem restrictedMonomialEvaluation_linearIndependent
    {ι τ : Type*} (exponent : ι → (τ →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (s : τ → Set ℂ) (hs : ∀ i, (s i).Infinite) :
    LinearIndependent ℂ
      (fun i : ι => fun x : ↥(Set.pi Set.univ s) =>
        MvPolynomial.eval x.1 (MvPolynomial.monomial (exponent i) (1 : ℂ))) := by
  have hmono : LinearIndependent ℂ
      (fun d : τ →₀ ℕ => MvPolynomial.monomial d (1 : ℂ)) :=
    (MvPolynomial.basisMonomials τ ℂ).linearIndependent
  have hrestricted := hmono.comp exponent hexponent
  have hmapped := hrestricted.map' (restrictedEvaluationLinearMap τ s)
    (LinearMap.ker_eq_bot.mpr (restrictedEvaluationLinearMap_injective s hs))
  simpa [Function.comp_def, restrictedEvaluationLinearMap] using hmapped

/-- A finite family of distinct monomials has a square full-rank evaluation packet inside every
box with infinite sides. -/
theorem exists_fullRank_restrictedMonomialEvaluation_packet
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (exponent : ι → (τ →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (s : τ → Set ℂ) (hs : ∀ i, (s i).Infinite) :
    ∃ points : ι → ↥(Set.pi Set.univ s),
      IsUnit (Matrix.of fun a i =>
        MvPolynomial.eval (points a).1
          (MvPolynomial.monomial (exponent i) (1 : ℂ)) :
        Matrix ι ι ℂ) := by
  exact exists_fullRank_evaluation_packet _
    (restrictedMonomialEvaluation_linearIndependent exponent hexponent s hs)

/-- One distinguished variable is constrained above height `H`; all jet variables remain free. -/
def upperJetBox {σ : Type*} (H : ℝ) : Option σ → Set ℂ
  | none => {z | H < z.im}
  | some _ => Set.univ

theorem upperHalfPlaneAbove_infinite (H : ℝ) :
    Set.Infinite {z : ℂ | H < z.im} := by
  let vertical : ℝ → ℂ := fun y => (y : ℂ) * Complex.I
  have hvert : Function.Injective vertical := by
    intro y₁ y₂ h
    have him := congrArg Complex.im h
    simpa [vertical] using him
  have himage : Set.Infinite (vertical '' Set.Ioi H) :=
    (Set.Ioi_infinite H).image hvert.injOn
  apply himage.mono
  rintro z ⟨y, hy, rfl⟩
  simpa [vertical] using hy

theorem upperJetBox_infinite {σ : Type*} (H : ℝ) :
    ∀ i, (upperJetBox (σ := σ) H i).Infinite := by
  intro i
  cases i with
  | none => exact upperHalfPlaneAbove_infinite H
  | some i => exact Set.infinite_univ

/-- Combine the coefficient degree in the distinguished variable with a jet-monomial exponent. -/
noncomputable def expandedMonomialExponent {σ : Type*}
    (degree : ℕ) (jetExponent : σ →₀ ℕ) : Option σ →₀ ℕ :=
  Finsupp.single none degree +
    Finsupp.embDomain Function.Embedding.some jetExponent

@[simp] theorem expandedMonomialExponent_none {σ : Type*}
    (degree : ℕ) (jetExponent : σ →₀ ℕ) :
    expandedMonomialExponent degree jetExponent none = degree := by
  classical
  simp [expandedMonomialExponent, Finsupp.embDomain_apply]

@[simp] theorem expandedMonomialExponent_some {σ : Type*}
    (degree : ℕ) (jetExponent : σ →₀ ℕ) (i : σ) :
    expandedMonomialExponent degree jetExponent (some i) = jetExponent i := by
  classical
  simp [expandedMonomialExponent, Finsupp.embDomain_apply]

theorem expandedMonomialExponent_pair_injective
    {κ σ : Type*} (jetExponent : κ → (σ →₀ ℕ))
    (hjet : Function.Injective jetExponent) :
    Function.Injective
      (fun x : κ × ℕ => expandedMonomialExponent x.2 (jetExponent x.1)) := by
  intro x y h
  have hdegree : x.2 = y.2 := by
    simpa using congrArg (fun e => e none) h
  have hjetexp : jetExponent x.1 = jetExponent y.1 := by
    apply Finsupp.ext
    intro i
    simpa using congrArg (fun e => e (some i)) h
  exact Prod.ext (hjet hjetexp) hdegree

/-- The combined exponent evaluates to the expanded function `z^d M_β(x)`. -/
theorem eval_expandedMonomial {σ : Type*}
    (degree : ℕ) (jetExponent : σ →₀ ℕ) (point : Option σ → ℂ) :
    MvPolynomial.eval point
        (MvPolynomial.monomial (expandedMonomialExponent degree jetExponent) (1 : ℂ)) =
      point none ^ degree * jetExponent.prod (fun i e => point (some i) ^ e) := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  simp only [expandedMonomialExponent]
  rw [Finsupp.prod_add_index]
  · rw [Finsupp.prod_single_index, Finsupp.prod_embDomain]
    all_goals simp
  · intro a ha
    simp
  · intro a ha b₁ b₂
    simp [pow_add]

/-- Distinct expanded exponents admit a full-rank evaluation packet above every horizontal line. -/
theorem exists_fullRank_expandedMonomial_upper_packet
    {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (exponent : ι → (Option σ →₀ ℕ))
    (hexponent : Function.Injective exponent) (H : ℝ) :
    ∃ points : ι → (Option σ → ℂ),
      (∀ a, H < (points a none).im) ∧
      IsUnit (Matrix.of fun a i =>
        MvPolynomial.eval (points a)
          (MvPolynomial.monomial (exponent i) (1 : ℂ)) :
        Matrix ι ι ℂ) := by
  obtain ⟨points, hfull⟩ :=
    exists_fullRank_restrictedMonomialEvaluation_packet exponent hexponent
      (upperJetBox (σ := σ) H) (upperJetBox_infinite H)
  refine ⟨fun a => (points a).1, ?_, hfull⟩
  intro a
  exact (points a).2 none (Set.mem_univ none)

theorem expandedMonomialExponent_boundedDegree_injective
    {κ σ : Type*} {q : ℕ}
    (jetExponent : κ → (σ →₀ ℕ)) (hjet : Function.Injective jetExponent) :
    Function.Injective
      (fun x : κ × Fin (q + 1) =>
        expandedMonomialExponent (x.2 : ℕ) (jetExponent x.1)) := by
  intro x y h
  have hpair : (x.1, (x.2 : ℕ)) = (y.1, (y.2 : ℕ)) :=
    expandedMonomialExponent_pair_injective jetExponent hjet h
  have hfst : x.1 = y.1 := congrArg (fun p : κ × ℕ => p.1) hpair
  have hsnd : (x.2 : ℕ) = (y.2 : ℕ) := congrArg (fun p : κ × ℕ => p.2) hpair
  exact Prod.ext hfst (Fin.ext hsnd)

/-- **Upper coefficient-uniform detector.** For distinct jet monomials `M_β` and every coefficient
degree bound `q`, one square packet above height `H` makes the matrix `z_a^d M_β(x_a)` invertible.
Thus the packet detects every family of polynomial coefficients of degree at most `q`
simultaneously. -/
theorem exists_fullRank_polynomialCoefficientMonomial_upper_packet
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] (q : ℕ)
    (jetExponent : κ → (σ →₀ ℕ)) (hjet : Function.Injective jetExponent)
    (H : ℝ) :
    ∃ points : (κ × Fin (q + 1)) → (Option σ → ℂ),
      (∀ a, H < (points a none).im) ∧
      IsUnit (Matrix.of fun a b =>
        (points a none) ^ (b.2 : ℕ) *
          (jetExponent b.1).prod (fun i e => points a (some i) ^ e) :
        Matrix (κ × Fin (q + 1)) (κ × Fin (q + 1)) ℂ) := by
  obtain ⟨points, hupper, hfull⟩ :=
    exists_fullRank_expandedMonomial_upper_packet
      (fun x : κ × Fin (q + 1) =>
        expandedMonomialExponent (x.2 : ℕ) (jetExponent x.1))
      (expandedMonomialExponent_boundedDegree_injective jetExponent hjet) H
  refine ⟨points, hupper, ?_⟩
  simpa only [eval_expandedMonomial] using hfull

/-- The upper packet can be stated intrinsically as simultaneous detection of every coefficient
vector for the prescribed monomial support and degree bound. -/
theorem exists_upper_packet_detecting_all_polynomialCoefficients
    {κ σ : Type*} [Fintype κ] [DecidableEq κ] (q : ℕ)
    (jetExponent : κ → (σ →₀ ℕ)) (hjet : Function.Injective jetExponent)
    (H : ℝ) :
    ∃ points : (κ × Fin (q + 1)) → (Option σ → ℂ),
      (∀ a, H < (points a none).im) ∧
      ∀ c : (κ × Fin (q + 1)) → ℂ,
        (∀ a, ∑ b, c b * (points a none) ^ (b.2 : ℕ) *
          (jetExponent b.1).prod (fun i e => points a (some i) ^ e) = 0) →
        ∀ b, c b = 0 := by
  obtain ⟨points, hupper, hfull⟩ :=
    exists_fullRank_polynomialCoefficientMonomial_upper_packet q jetExponent hjet H
  refine ⟨points, hupper, ?_⟩
  intro c hvanish
  apply coefficients_eq_zero_of_fullRank_evaluation_packet
    (fun b point => point none ^ (b.2 : ℕ) *
      (jetExponent b.1).prod (fun i e => point (some i) ^ e))
    points hfull c
  intro a
  simpa only [mul_assoc] using hvanish a

/-- A spacing larger than every real-part difference in a finite shift packet. -/
noncomputable def shiftRealWidth {ι : Type*} [Fintype ι]
    (shift : ι → ℂ) : ℝ :=
  1 + ∑ i, ∑ j, |(shift j - shift i).re|

theorem shiftRealWidth_pos {ι : Type*} [Fintype ι] (shift : ι → ℂ) :
    0 < shiftRealWidth shift := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, |(shift j - shift i).re| :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => abs_nonneg _
  simp only [shiftRealWidth]
  linarith

theorem abs_shift_real_difference_lt_width
    {ι : Type*} [Fintype ι] (shift : ι → ℂ) (i j : ι) :
    |(shift j - shift i).re| < shiftRealWidth shift := by
  have hinner : |(shift j - shift i).re| ≤ ∑ k, |(shift k - shift i).re| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k => |(shift k - shift i).re|)
      (fun k hk => abs_nonneg _) (Finset.mem_univ j)
  have houter : (∑ k, |(shift k - shift i).re|) ≤
      ∑ l, ∑ k, |(shift k - shift l).re| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun l => ∑ k, |(shift k - shift l).re|)
      (fun l hl => Finset.sum_nonneg fun k hk => abs_nonneg _)
      (Finset.mem_univ i)
  simp only [shiftRealWidth]
  linarith

/-- Row real parts are integer multiples of a spacing larger than every shift difference. -/
noncomputable def separatedRowRealPart
    {row ι : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) (a : row) : ℝ :=
  ((Fintype.equivFin row a : Fin (Fintype.card row)) : ℕ) * shiftRealWidth shift

theorem abs_separatedRowRealPart_sub_ge_width
    {row ι : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) {a b : row} (hab : a ≠ b) :
    shiftRealWidth shift ≤
      |separatedRowRealPart shift a - separatedRowRealPart shift b| := by
  let ea := Fintype.equivFin row a
  let eb := Fintype.equivFin row b
  have he : ea ≠ eb := fun h => hab ((Fintype.equivFin row).injective h)
  have hval : ea.val ≠ eb.val := fun h => he (Fin.ext h)
  have habs : 1 ≤ |(ea.val : ℝ) - (eb.val : ℝ)| := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hltR : (ea.val : ℝ) < (eb.val : ℝ) := by exact_mod_cast hlt
      have hgapNat : ea.val + 1 ≤ eb.val := Nat.succ_le_iff.mpr hlt
      have hgapR : ((ea.val + 1 : ℕ) : ℝ) ≤ (eb.val : ℝ) := by
        exact_mod_cast hgapNat
      rw [abs_of_nonpos (sub_nonpos.mpr hltR.le)]
      push_cast at hgapR
      linarith
    · have hgtR : (eb.val : ℝ) < (ea.val : ℝ) := by exact_mod_cast hgt
      have hgapNat : eb.val + 1 ≤ ea.val := Nat.succ_le_iff.mpr hgt
      have hgapR : ((eb.val + 1 : ℕ) : ℝ) ≤ (ea.val : ℝ) := by
        exact_mod_cast hgapNat
      rw [abs_of_nonneg (sub_nonneg.mpr hgtR.le)]
      push_cast at hgapR
      linarith
  have hwidth := shiftRealWidth_pos shift
  rw [separatedRowRealPart, separatedRowRealPart, ← sub_mul, abs_mul,
    abs_of_pos hwidth]
  change shiftRealWidth shift ≤
    |(ea.val : ℝ) - (eb.val : ℝ)| * shiftRealWidth shift
  nlinarith

theorem separatedRowRealPart_avoids_shift_difference
    {row ι : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) {a b : row} (hab : a ≠ b) (i j : ι) :
    separatedRowRealPart shift a - separatedRowRealPart shift b ≠
      (shift j - shift i).re := by
  intro h
  have hge := abs_separatedRowRealPart_sub_ge_width shift hab
  have hlt := abs_shift_real_difference_lt_width shift i j
  rw [h] at hge
  linarith

/-- A row-dependent box whose distinguished coordinate lies on a separated vertical half-line. -/
def separatedUpperJetBox
    {row ι σ : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) (H : ℝ) (a : row) : Option σ → Set ℂ
  | none => {z | z.re = separatedRowRealPart shift a ∧ H < z.im}
  | some _ => Set.univ

theorem verticalLineAbove_infinite (R H : ℝ) :
    Set.Infinite {z : ℂ | z.re = R ∧ H < z.im} := by
  let line : ℝ → ℂ := fun y => (R : ℂ) + (y : ℂ) * Complex.I
  have hline : Function.Injective line := by
    intro y₁ y₂ h
    have him := congrArg Complex.im h
    simpa [line] using him
  have himage : Set.Infinite (line '' Set.Ioi H) :=
    (Set.Ioi_infinite H).image hline.injOn
  apply himage.mono
  rintro z ⟨y, hy, rfl⟩
  constructor
  · simp [line]
  · simpa [line] using hy

theorem separatedUpperJetBox_infinite
    {row ι σ : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) (H : ℝ) (a : row) :
    ∀ k, (separatedUpperJetBox (σ := σ) shift H a k).Infinite := by
  intro k
  cases k with
  | none => exact verticalLineAbove_infinite _ H
  | some k => exact Set.infinite_univ

universe uκ uι uσ

/-- **Noncolliding coefficient-uniform detector geometry.** For a finite injective shift packet,
distinct jet monomials, and a polynomial coefficient-degree bound, there is a square full-rank
expanded-monomial evaluation packet above every height whose complete row-by-shift node family is
injective. -/
theorem exists_noncolliding_fullRank_polynomialCoefficientMonomial_packet
    {κ : Type uκ} {ι : Type uι} {σ : Type uσ}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (jetExponent : κ → (σ →₀ ℕ))
    (hjet : Function.Injective jetExponent)
    (shift : ι → ℂ) (hshift : Function.Injective shift) (H : ℝ) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ, ∃ targetJet : Fin n → (σ → ℂ),
      (∀ a, H < (base a).im) ∧
      Function.Injective (fun x : Fin n × ι => base x.1 + shift x.2) ∧
      IsUnit (Matrix.of fun a b =>
        (base a) ^ ((Fintype.equivFin pattern).symm b).2.val *
          (jetExponent ((Fintype.equivFin pattern).symm b).1).prod
            (fun i e => targetJet a i ^ e) : Matrix (Fin n) (Fin n) ℂ) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  let equiv : pattern ≃ Fin n := Fintype.equivFin pattern
  let exponent : Fin n → (Option σ →₀ ℕ) := fun b =>
    expandedMonomialExponent ((equiv.symm b).2 : ℕ)
      (jetExponent (equiv.symm b).1)
  have hexponent : Function.Injective exponent := by
    apply (expandedMonomialExponent_boundedDegree_injective jetExponent hjet).comp
    exact equiv.symm.injective
  let X : Fin n → Type uσ := fun a =>
    ↥(Set.pi Set.univ (separatedUpperJetBox (σ := σ) shift H a))
  let evaluationVector : ∀ a, X a → (Fin n → ℂ) := fun a x b =>
    MvPolynomial.eval x.1 (MvPolynomial.monomial (exponent b) (1 : ℂ))
  have hspan : ∀ a, Submodule.span ℂ (Set.range (evaluationVector a)) = ⊤ := by
    intro a
    apply span_evaluationVectors_eq_top
    exact restrictedMonomialEvaluation_linearIndependent exponent hexponent
      (separatedUpperJetBox (σ := σ) shift H a)
      (separatedUpperJetBox_infinite shift H a)
  obtain ⟨points, hfull⟩ :=
    exists_fullRank_dependent_evaluation_packet X evaluationVector hspan
  let base : Fin n → ℂ := fun a => (points a).1 none
  let targetJet : Fin n → (σ → ℂ) := fun a i => (points a).1 (some i)
  refine ⟨base, targetJet, ?_, ?_, ?_⟩
  · intro a
    exact ((points a).2 none (Set.mem_univ none)).2
  · intro x y hxy
    rcases x with ⟨a, i⟩
    rcases y with ⟨b, j⟩
    by_cases hab : a = b
    · subst b
      have hij : shift i = shift j := add_left_cancel hxy
      exact Prod.ext rfl (hshift hij)
    · have hre := congrArg Complex.re hxy
      rw [Complex.add_re, Complex.add_re] at hre
      have hbasea := ((points a).2 none (Set.mem_univ none)).1
      have hbaseb := ((points b).2 none (Set.mem_univ none)).1
      exfalso
      apply (separatedRowRealPart_avoids_shift_difference shift hab i j)
      rw [Complex.sub_re]
      change (base a).re + (shift i).re = (base b).re + (shift j).re at hre
      change (base a).re = separatedRowRealPart shift a at hbasea
      change (base b).re = separatedRowRealPart shift b at hbaseb
      linarith
  · have hmatrix :
        (Matrix.of fun a b => evaluationVector a (points a) b :
          Matrix (Fin n) (Fin n) ℂ) =
        Matrix.of fun a b =>
          (base a) ^ (equiv.symm b).2.val *
            (jetExponent (equiv.symm b).1).prod (fun i e => targetJet a i ^ e) := by
      ext a b
      change MvPolynomial.eval (points a).1
          (MvPolynomial.monomial
            (expandedMonomialExponent ((equiv.symm b).2 : ℕ)
              (jetExponent (equiv.symm b).1)) (1 : ℂ)) = _
      rw [eval_expandedMonomial]
      rfl
    change IsUnit (Matrix.of fun a b =>
      (base a) ^ (equiv.symm b).2.val *
        (jetExponent (equiv.symm b).1).prod
          (fun i e => targetJet a i ^ e) : Matrix (Fin n) (Fin n) ℂ)
    rw [← hmatrix]
    exact hfull

end GaloisForLFunctions.HTGeometry
