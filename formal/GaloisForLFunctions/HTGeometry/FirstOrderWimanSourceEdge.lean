import GaloisForLFunctions.HTGeometry.FirstOrderWimanNewtonEdge

open Finset Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Equality of Newton weights at two distinct derivative powers forces a rational slope. -/
theorem exists_rational_eq_slope_of_eq_firstOrderNewtonWeight
    {A : ℕ × ℕ → Polynomial ℂ} {p : ℝ} {i j : ℕ × ℕ}
    (hij : i.2 ≠ j.2)
    (hweight : firstOrderNewtonWeight A p i = firstOrderNewtonWeight A p j) :
    ∃ s : ℚ, (s : ℝ) = p := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let s : ℚ :=
      (((A i).natDegree : ℚ) - (A j).natDegree) / ((j.2 : ℚ) - i.2)
    refine ⟨s, ?_⟩
    dsimp [s]
    push_cast
    have hijlt' : (i.2 : ℝ) < j.2 := by exact_mod_cast hijlt
    have hden : (j.2 : ℝ) - i.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hijlt')
    rw [div_eq_iff hden]
    rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hweight
    nlinarith
  · let s : ℚ :=
      (((A j).natDegree : ℚ) - (A i).natDegree) / ((i.2 : ℚ) - j.2)
    refine ⟨s, ?_⟩
    dsimp [s]
    push_cast
    have hjilt' : (j.2 : ℝ) < i.2 := by exact_mod_cast hjilt
    have hden : (i.2 : ℝ) - j.2 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hjilt')
    rw [div_eq_iff hden]
    rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hweight
    nlinarith

/-- Distinct exponent pairs on one total-degree face have distinct derivative exponents. -/
theorem snd_ne_of_ne_of_add_eq_add_eq
    {i j : ℕ × ℕ} {d : ℕ} (hi : i.1 + i.2 = d) (hj : j.1 + j.2 = d)
    (hij : i ≠ j) : i.2 ≠ j.2 := by
  intro hsnd
  apply hij
  apply Prod.ext
  · omega
  · exact hsnd

/-- Preimage, in the coefficient row reconstructing the source polynomial, of a Newton face in the
positive-derivative shifted row. -/
def firstOrderSourceNewtonFace (S₀ : Finset (ℕ × ℕ))
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (d : ℕ) (p w : ℝ) : Finset (ℕ × ℕ) :=
  S₀.filter fun i => firstOrderDerivativeShift i ∈ firstOrderMaxNewtonFace S A d p w

/-- A nonzero root of a Newton edge in the positive-derivative shifted row descends to the exact
coefficient row reconstructing the source polynomial.  The shifted edge polynomial is `X` times
the source edge polynomial, so a nonzero root cannot be contributed by the added derivative
factor. -/
theorem exists_sourceNewtonEdgeRoot_of_positiveDerivativeShift
    {P : MvPolynomial (Fin 3) ℂ} {S : Finset (ℕ × ℕ)}
    {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ} {p w : ℝ} {c : ℂ}
    (hshift : IsPositiveDerivativeCoefficientShift P S A d)
    (hdeg : ∀ i ∈ S, i.1 + i.2 ≤ d)
    (hfaceNonempty : (firstOrderMaxNewtonFace S A d p w).Nonempty)
    (hc : c ≠ 0)
    (hcroot : (firstOrderNewtonEdgePolynomial
      (firstOrderMaxNewtonFace S A d p w) A).IsRoot c) :
    ∃ (S₀ : Finset (ℕ × ℕ)) (A₀ : ℕ × ℕ → Polynomial ℂ),
      firstOrderMvPoly S₀ A₀ = P ∧
      (∀ i ∈ S₀, A₀ i ≠ 0) ∧
      S = S₀.image firstOrderDerivativeShift ∧
      (∀ i ∈ S₀,
        A (firstOrderDerivativeShift i) = Polynomial.X ^ d * A₀ i) ∧
      (∀ i ∈ S₀, i.1 + i.2 ≤ d - 1) ∧
      firstOrderSourceNewtonFace S₀ S A d p w =
        firstOrderMaxNewtonFace S₀ A₀ (d - 1) p (w - d - p) ∧
      (firstOrderNewtonEdgePolynomial
        (firstOrderMaxNewtonFace S₀ A₀ (d - 1) p (w - d - p)) A₀).IsRoot c := by
  classical
  obtain ⟨S₀, A₀, hpoly, hA₀, hS, hA⟩ := hshift
  let sourceFace : Finset (ℕ × ℕ) := firstOrderSourceNewtonFace S₀ S A d p w
  let outputFace : Finset (ℕ × ℕ) := firstOrderMaxNewtonFace S A d p w
  have hshinj : Function.Injective firstOrderDerivativeShift := by
    rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ hij
    simp only [firstOrderDerivativeShift, Prod.mk.injEq] at hij ⊢
    omega
  have hface : outputFace = sourceFace.image firstOrderDerivativeShift := by
    ext i
    constructor
    · intro hi
      have hiS : i ∈ S := by
        have hi' : i ∈ firstOrderMaxNewtonFace S A d p w := hi
        rw [firstOrderMaxNewtonFace, Finset.mem_filter] at hi'
        rw [firstOrderTopNewtonFace, Finset.mem_filter] at hi'
        exact hi'.1.1
      rw [hS] at hiS
      obtain ⟨u, huS₀, hui⟩ := Finset.mem_image.mp hiS
      subst i
      apply Finset.mem_image.mpr
      refine ⟨u, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨huS₀, hi⟩
    · intro hi
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hu).2
  obtain ⟨i, hiFace⟩ := hfaceNonempty
  have hiS : i ∈ S := by
    have hiFace' := hiFace
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at hiFace'
    exact hiFace'.1.1
  rw [hS] at hiS
  obtain ⟨u₀, hu₀, hu₀i⟩ := Finset.mem_image.mp hiS
  have hdpos : 0 < d := by
    have hiTop : i.1 + i.2 = d := by
      have hiFace' := hiFace
      rw [firstOrderMaxNewtonFace, Finset.mem_filter,
        firstOrderTopNewtonFace, Finset.mem_filter] at hiFace'
      exact hiFace'.1.2.1
    rw [← hu₀i] at hiTop
    simp only [firstOrderDerivativeShift] at hiTop
    omega
  have hnatDegree : ∀ u ∈ S₀,
      (A (firstOrderDerivativeShift u)).natDegree = d + (A₀ u).natDegree := by
    intro u hu
    rw [hA u hu, Polynomial.natDegree_mul
      (pow_ne_zero _ Polynomial.X_ne_zero) (hA₀ u hu), Polynomial.natDegree_X_pow]
  have hsourceDeg : ∀ u ∈ S₀, u.1 + u.2 ≤ d - 1 := by
    intro u hu
    have hushiftMem : firstOrderDerivativeShift u ∈ S := by
      rw [hS, Finset.mem_image]
      exact ⟨u, hu, rfl⟩
    have hushiftDeg := hdeg (firstOrderDerivativeShift u) hushiftMem
    simp only [firstOrderDerivativeShift] at hushiftDeg
    omega
  have hweight : ∀ u ∈ S₀,
      firstOrderNewtonWeight A p (firstOrderDerivativeShift u) =
        firstOrderNewtonWeight A₀ p u + d + p := by
    intro u hu
    rw [firstOrderNewtonWeight, firstOrderNewtonWeight, hnatDegree u hu]
    simp only [firstOrderDerivativeShift]
    push_cast
    ring
  have hsourceFace : sourceFace =
      firstOrderMaxNewtonFace S₀ A₀ (d - 1) p (w - d - p) := by
    ext u
    constructor
    · intro huSource
      change u ∈ firstOrderSourceNewtonFace S₀ S A d p w at huSource
      rw [firstOrderSourceNewtonFace, Finset.mem_filter] at huSource
      obtain ⟨hu, huOutput⟩ := huSource
      rw [firstOrderMaxNewtonFace, Finset.mem_filter,
        firstOrderTopNewtonFace, Finset.mem_filter] at huOutput
      obtain ⟨⟨_, hushiftDeg, _⟩, hushiftWeight⟩ := huOutput
      rw [firstOrderMaxNewtonFace, Finset.mem_filter,
        firstOrderTopNewtonFace, Finset.mem_filter]
      refine ⟨⟨hu, ?_, hA₀ u hu⟩, ?_⟩
      · simp only [firstOrderDerivativeShift] at hushiftDeg
        omega
      · rw [hweight u hu] at hushiftWeight
        linarith
    · intro huMax
      rw [firstOrderMaxNewtonFace, Finset.mem_filter,
        firstOrderTopNewtonFace, Finset.mem_filter] at huMax
      obtain ⟨⟨hu, huDeg, _⟩, huWeight⟩ := huMax
      change u ∈ firstOrderSourceNewtonFace S₀ S A d p w
      rw [firstOrderSourceNewtonFace, Finset.mem_filter]
      refine ⟨hu, ?_⟩
      rw [firstOrderMaxNewtonFace, Finset.mem_filter,
        firstOrderTopNewtonFace, Finset.mem_filter]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hS, Finset.mem_image]
        exact ⟨u, hu, rfl⟩
      · simp only [firstOrderDerivativeShift]
        omega
      · rw [hA u hu]
        exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (hA₀ u hu)
      · rw [hweight u hu]
        linarith
  have hedge : firstOrderNewtonEdgePolynomial outputFace A =
      Polynomial.X * firstOrderNewtonEdgePolynomial sourceFace A₀ := by
    rw [firstOrderNewtonEdgePolynomial, firstOrderNewtonEdgePolynomial, hface,
      Finset.sum_image hshinj.injOn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hA i (Finset.mem_filter.mp hi).1, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_X_pow]
    simp only [one_mul, firstOrderDerivativeShift]
    rw [pow_succ]
    ring
  refine ⟨S₀, A₀, hpoly, hA₀, hS, hA, hsourceDeg, hsourceFace, ?_⟩
  change Polynomial.eval c
    (firstOrderNewtonEdgePolynomial
      (firstOrderMaxNewtonFace S₀ A₀ (d - 1) p (w - d - p)) A₀) = 0
  rw [← hsourceFace]
  change Polynomial.eval c
    (firstOrderNewtonEdgePolynomial outputFace A) = 0 at hcroot
  rw [hedge, Polynomial.eval_mul, Polynomial.eval_X] at hcroot
  exact (mul_eq_zero.mp hcroot).resolve_left hc

end

end GaloisForLFunctions.HTGeometry
