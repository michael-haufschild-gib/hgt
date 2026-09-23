import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

/-!
# Quantitative rectangular nuclear bounds

The rectangular Schatten infrastructure previously established exact
incidence/Bures identities and trace-class membership for products of two
Hilbert--Schmidt maps.  This module supplies the missing sharp quantitative
bound.  It first proves that an arbitrary absolutely summable rectangular
rank-one expansion has nuclear norm at most its projective mass, then applies
Hilbert-basis Cauchy--Schwarz to obtain

`‖B ∘ A‖₁ ≤ ‖A‖₂ ‖B‖₂`

for three different Hilbert carriers.  No finite-dimensional or rank
hypothesis is used.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rectangular finite-rank budgets add. -/
theorem HasRectRankLE.add {S T : E →L[ℂ] F} {m n : ℕ}
    (hS : HasRectRankLE S m) (hT : HasRectRankLE T n) :
    HasRectRankLE (S + T) (m + n) := by
  obtain ⟨V, hVfd, hVrank, hSV⟩ := hS
  obtain ⟨W, hWfd, hWrank, hTW⟩ := hT
  letI : FiniteDimensional ℂ V := hVfd
  letI : FiniteDimensional ℂ W := hWfd
  refine ⟨V ⊔ W, inferInstance, ?_, fun z ↦ ?_⟩
  · have hdim := Submodule.finrank_sup_add_finrank_inf_eq V W
    omega
  · rw [ContinuousLinearMap.add_apply]
    exact Submodule.add_mem (V ⊔ W)
      ((show V ≤ V ⊔ W from le_sup_left) (hSV z))
      ((show W ≤ V ⊔ W from le_sup_right) (hTW z))

omit [CompleteSpace E] [CompleteSpace F] in
/-- A finite sum of rectangular rank-one terms has rank at most its number
of terms. -/
theorem hasRectRankLE_sum_finset_of_rankOne
    {ι : Type*} (A : ι → E →L[ℂ] F)
    (hA : ∀ i, HasRectRankLE (A i) 1) (s : Finset ι) :
    HasRectRankLE (∑ i ∈ s, A i) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRectRankLE_zero (E := E) (F := F) 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      simpa [Nat.add_comm] using (hA i).add ih

/-- Rectangular nuclear norm of a finite rank-one sum is bounded by the sum
of the operator norms of its terms. -/
theorem rectTraceNorm_sum_le_sum_norm_of_rankOneTerms
    {ι : Type*} (A : ι → E →L[ℂ] F)
    (hA : ∀ i, HasRectRankLE (A i) 1) (s : Finset ι) :
    rectTraceNorm E F (∑ i ∈ s, A i) ≤ ∑ i ∈ s, ‖A i‖ := by
  classical
  have hLower :
      rectangularLowerBlock (∑ i ∈ s, A i) =
        ∑ i ∈ s, rectangularLowerBlock (A i) := by
    induction s using Finset.induction_on with
    | empty =>
        ext z
        simp [rectangularLowerBlock_apply]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
        ext z
        apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
        simp [rectangularLowerBlock_apply]
  rw [rectTraceNorm_eq_traceNorm_lowerBlock, hLower]
  calc
    traceNorm (rectangularHilbertSum E F)
        (∑ i ∈ s, rectangularLowerBlock (A i)) ≤
        ∑ i ∈ s, ‖rectangularLowerBlock (A i)‖ :=
      traceNorm_sum_le_sum_norm_of_rankOneTerms
        (fun i ↦ rectangularLowerBlock (A i))
        (fun i ↦ (hA i).lowerBlock) s
    _ = ∑ i ∈ s, ‖A i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      exact norm_rectangularLowerBlock (A i)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Perturbing a rectangular operator in operator norm perturbs each
approximation number by at most that norm. -/
theorem rectApproxNumber_le_norm_sub_add
    (T S : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber T n ≤ ‖T - S‖ + rectApproxNumber S n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlt : rectApproxNumber S n < rectApproxNumber S n + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨r, hr, hrlt⟩ :=
    (csInf_lt_iff (rectApproxNumber_set_bddBelow S n)
      (rectApproxNumber_set_nonempty S n)).mp hlt
  obtain ⟨Q, hQ, rfl⟩ := hr
  calc
    rectApproxNumber T n ≤ ‖T - Q‖ := rectApproxNumber_le T n Q hQ
    _ = ‖(T - S) + (S - Q)‖ := by congr 1; abel
    _ ≤ ‖T - S‖ + ‖S - Q‖ := norm_add_le _ _
    _ ≤ ‖T - S‖ + rectApproxNumber S n + ε := by linarith

/-- **Absolute rectangular nuclear-series bound.**  Any operator-norm
convergent rank-one expansion has rectangular Schatten-one norm at most its
projective mass.  Index type is arbitrary. -/
theorem rectTraceNorm_tsum_rankOneTerms_le_tsum_norm
    {ι : Type*} (A : ι → E →L[ℂ] F)
    (hA : ∀ i, HasRectRankLE (A i) 1)
    (hnorm : Summable fun i ↦ ‖A i‖) :
    rectTraceNorm E F (∑' i, A i) ≤ ∑' i, ‖A i‖ := by
  classical
  have hsum : Summable A := Summable.of_norm hnorm
  unfold rectTraceNorm
  apply Real.tsum_le_of_sum_le (fun n ↦ rectApproxNumber_nonneg _ n)
  intro s
  apply le_of_forall_pos_le_add
  intro ε hε
  let c : ℝ := s.card
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  obtain ⟨u, hu⟩ : ∃ u : Finset ι,
      c * ‖(∑' i, A i) - ∑ i ∈ u, A i‖ < ε := by
    by_cases hc : c = 0
    · exact ⟨∅, by simp [hc, hε]⟩
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
      have htend : Tendsto (fun u : Finset ι ↦ ∑ i ∈ u, A i) atTop
          (nhds (∑' i, A i)) := hsum.hasSum
      have hevent : ∀ᶠ u : Finset ι in atTop,
          ‖(∑' i, A i) - ∑ i ∈ u, A i‖ < ε / c := by
        have hball := htend.eventually
          (Metric.ball_mem_nhds _ (div_pos hε hcpos))
        filter_upwards [hball] with u hu'
        rw [dist_eq_norm] at hu'
        simpa only [norm_sub_rev] using hu'
      obtain ⟨u, htail⟩ := hevent.exists
      exact ⟨u, by
        have heq : c * (ε / c) = ε := by field_simp [hc]
        nlinarith⟩
  let S : E →L[ℂ] F := ∑ i ∈ u, A i
  have hpoint : ∀ n, rectApproxNumber (∑' i, A i) n ≤
      ‖(∑' i, A i) - S‖ + rectApproxNumber S n :=
    fun n ↦ rectApproxNumber_le_norm_sub_add _ _ _
  have hSrank : HasRectRankLE S u.card := by
    simpa [S] using hasRectRankLE_sum_finset_of_rankOne A hA u
  have hSclass : MemRectSchattenClass 1 S := by
    rw [memRectSchattenClass_iff_lowerBlock]
    exact memSchattenClass_of_hasRankLE one_pos hSrank.lowerBlock
  have hSraw : Summable (fun n ↦ rectApproxNumber S n) :=
    (memRectSchattenClass_one_iff S).mp hSclass
  calc
    ∑ n ∈ s, rectApproxNumber (∑' i, A i) n ≤
        ∑ n ∈ s, (‖(∑' i, A i) - S‖ + rectApproxNumber S n) :=
      Finset.sum_le_sum fun n _ ↦ hpoint n
    _ = c * ‖(∑' i, A i) - S‖ +
        ∑ n ∈ s, rectApproxNumber S n := by
      simp [c, Finset.sum_add_distrib]
    _ ≤ c * ‖(∑' i, A i) - S‖ + rectTraceNorm E F S := by
      gcongr
      exact hSraw.sum_le_tsum s (fun n _ ↦ rectApproxNumber_nonneg S n)
    _ ≤ c * ‖(∑' i, A i) - S‖ + ∑ i ∈ u, ‖A i‖ := by
      gcongr
      exact rectTraceNorm_sum_le_sum_norm_of_rankOneTerms A hA u
    _ ≤ c * ‖(∑' i, A i) - S‖ + ∑' i, ‖A i‖ := by
      gcongr
      exact hnorm.sum_le_tsum u (fun i _ ↦ norm_nonneg _)
    _ ≤ ∑' i, ‖A i‖ + ε := by
      dsimp [S] at hu ⊢
      linarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- A Deninger rank-one term has rectangular rank at most one. -/
theorem deningerSmulRight_hasRectRankLE_one
    (φ : E →L[ℂ] ℂ) (y : F) :
    HasRectRankLE (φ.smulRight y : E →L[ℂ] F) 1 := by
  classical
  refine ⟨Submodule.span ℂ ({y} : Set F), ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton y)
  · have h := finrank_span_le_card (R := ℂ) ({y} : Set F)
    simpa using h
  · intro x
    rw [ContinuousLinearMap.smulRight_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

/-- Quantitative rectangular Schatten bound for any displayed nuclear
series. -/
theorem rectTraceNorm_le_of_hasSum_smulRight
    {ι : Type*} (φ : ι → E →L[ℂ] ℂ) (y : ι → F)
    (hmass : Summable fun i ↦ ‖φ i‖ * ‖y i‖)
    {T : E →L[ℂ] F}
    (hT : HasSum (fun i ↦ (φ i).smulRight (y i)) T) :
    rectTraceNorm E F T ≤ ∑' i, ‖φ i‖ * ‖y i‖ := by
  have hnorm : Summable fun i ↦ ‖(φ i).smulRight (y i)‖ := by
    simpa only [ContinuousLinearMap.norm_smulRight_apply] using hmass
  have hbound := rectTraceNorm_tsum_rankOneTerms_le_tsum_norm
    (fun i ↦ (φ i).smulRight (y i))
    (fun i ↦ deningerSmulRight_hasRectRankLE_one (φ i) (y i)) hnorm
  rw [hT.tsum_eq] at hbound
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using hbound

/-- Infinite Cauchy--Schwarz for nonnegative square-summable real families,
in the exact form used by Hilbert--Schmidt products. -/
theorem tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
    {ι : Type*} (f g : ι → ℝ)
    (hf : Summable fun i ↦ f i ^ (2 : ℕ))
    (hg : Summable fun i ↦ g i ^ (2 : ℕ))
    (hfn : ∀ i, 0 ≤ f i) (hgn : ∀ i, 0 ≤ g i) :
    ∑' i, f i * g i ≤
      Real.sqrt (∑' i, f i ^ (2 : ℕ)) * Real.sqrt (∑' i, g i ^ (2 : ℕ)) := by
  apply Real.tsum_le_of_sum_le (fun i ↦ mul_nonneg (hfn i) (hgn i))
  intro s
  calc
    ∑ i ∈ s, f i * g i ≤
        Real.sqrt (∑ i ∈ s, f i ^ (2 : ℕ)) *
          Real.sqrt (∑ i ∈ s, g i ^ (2 : ℕ)) :=
      Real.sum_mul_le_sqrt_mul_sqrt s f g
    _ ≤ Real.sqrt (∑' i, f i ^ (2 : ℕ)) *
          Real.sqrt (∑' i, g i ^ (2 : ℕ)) := by
      gcongr
      · exact hf.sum_le_tsum s (fun i _ ↦ sq_nonneg _)
      · exact hg.sum_le_tsum s (fun i _ ↦ sq_nonneg _)

/-- **Sharp rectangular Schatten Hölder law.**  A product of two
Hilbert--Schmidt maps between three arbitrary Hilbert spaces is nuclear, with
sharp constant one:

`‖B ∘ A‖₁ ≤ ‖A‖₂ ‖B‖₂`.
-/
theorem rectTraceNorm_comp_le_hsNorm_mul_hsNorm
    [TopologicalSpace.SeparableSpace F]
    {A : E →L[ℂ] F} {B : F →L[ℂ] G}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    rectTraceNorm E G (B ∘L A) ≤
      ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
  obtain ⟨ι, ⟨c⟩⟩ := exists_small_hilbertBasis (F := F)
  let φ : ι → E →L[ℂ] ℂ := fun i ↦ innerSL ℂ (adjoint A (c i))
  let y : ι → G := fun i ↦ B (c i)
  have hf : Summable fun i ↦ ‖adjoint A (c i)‖ ^ (2 : ℕ) := hA.adjoint.summable c
  have hg : Summable fun i ↦ ‖B (c i)‖ ^ (2 : ℕ) := hB.summable c
  have hmass : Summable fun i ↦ ‖φ i‖ * ‖y i‖ := by
    have heq : (fun i ↦ ‖φ i‖ * ‖y i‖) =
        fun i ↦ ‖adjoint A (c i)‖ * ‖B (c i)‖ := by
      funext i
      simp [φ, y, innerSL_apply_norm]
    rw [heq]
    exact deningerSummable_mul_of_sq hf hg
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hseries : HasSum (fun i ↦ (φ i).smulRight (y i)) (B ∘L A) := by
    have hsummable : Summable fun i ↦ (φ i).smulRight (y i) := by
      apply Summable.of_norm
      simpa only [ContinuousLinearMap.norm_smulRight_apply] using hmass
    obtain ⟨S, hS⟩ := hsummable
    have hST : S = B ∘L A := by
      ext x
      have hpoint := (ContinuousLinearMap.apply ℂ G x).hasSum hS
      have hrepr : HasSum (fun i ↦ (c.repr (A x)) i • c i) (A x) :=
        c.hasSum_repr (A x)
      have hBsum := B.hasSum hrepr
      have heq : (fun i ↦ (ContinuousLinearMap.apply ℂ G x)
          ((φ i).smulRight (y i))) =
          fun i ↦ B ((c.repr (A x)) i • c i) := by
        funext i
        change φ i x • y i = B ((c.repr (A x)) i • c i)
        rw [map_smul]
        congr 1
        show inner ℂ (adjoint A (c i)) x = (c.repr (A x)) i
        rw [c.repr_apply_apply, ContinuousLinearMap.adjoint_inner_left]
      rw [heq] at hpoint
      exact hpoint.unique hBsum
    rwa [hST] at hS
  have hprojective := rectTraceNorm_le_of_hasSum_smulRight φ y hmass hseries
  have hCS : ∑' i, ‖φ i‖ * ‖y i‖ ≤
      Real.sqrt (∑' i, ‖adjoint A (c i)‖ ^ (2 : ℕ)) *
        Real.sqrt (∑' i, ‖B (c i)‖ ^ (2 : ℕ)) := by
    simpa only [φ, y, innerSL_apply_norm] using
      tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
        (fun i ↦ ‖adjoint A (c i)‖) (fun i ↦ ‖B (c i)‖)
        hf hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  calc
    rectTraceNorm E G (B ∘L A) ≤ ∑' i, ‖φ i‖ * ‖y i‖ := hprojective
    _ ≤ Real.sqrt (∑' i, ‖adjoint A (c i)‖ ^ (2 : ℕ)) *
        Real.sqrt (∑' i, ‖B (c i)‖ ^ (2 : ℕ)) := hCS
    _ = ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
      have hAadj : (adjoint A).IsHilbertSchmidt := hA.adjoint
      rw [← ContinuousLinearMap.hsNormSq_eq hAadj c,
        hA.hsNormSq_adjoint,
        ← ContinuousLinearMap.hsNormSq_eq hB c]
      rfl

/-- **Unrestricted sharp rectangular Schatten Hölder law.**  The same constant-one estimate
holds without a separability instance on the intermediate Hilbert space.  The ambient Hilbert
basis may have arbitrary universe level; the quantitative nuclear-series bound itself has no
small-index restriction. -/
theorem rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
    {A : E →L[ℂ] F} {B : F →L[ℂ] G}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    rectTraceNorm E G (B ∘L A) ≤
      ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
  let c := ContinuousLinearMap.hsBasis ℂ F
  let φ := fun i ↦ innerSL ℂ (adjoint A (c i))
  let y := fun i ↦ B (c i)
  have hf : Summable fun i ↦ ‖adjoint A (c i)‖ ^ (2 : ℕ) := hA.adjoint.summable c
  have hg : Summable fun i ↦ ‖B (c i)‖ ^ (2 : ℕ) := hB.summable c
  have hmass : Summable fun i ↦ ‖φ i‖ * ‖y i‖ := by
    have heq : (fun i ↦ ‖φ i‖ * ‖y i‖) =
        fun i ↦ ‖adjoint A (c i)‖ * ‖B (c i)‖ := by
      funext i
      simp [φ, y, innerSL_apply_norm]
    rw [heq]
    exact deningerSummable_mul_of_sq hf hg
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hseries : HasSum (fun i ↦ (φ i).smulRight (y i)) (B ∘L A) := by
    have hsummable : Summable fun i ↦ (φ i).smulRight (y i) := by
      apply Summable.of_norm
      simpa only [ContinuousLinearMap.norm_smulRight_apply] using hmass
    obtain ⟨S, hS⟩ := hsummable
    have hST : S = B ∘L A := by
      ext x
      have hpoint := (ContinuousLinearMap.apply ℂ G x).hasSum hS
      have hrepr : HasSum (fun i ↦ (c.repr (A x)) i • c i) (A x) :=
        c.hasSum_repr (A x)
      have hBsum := B.hasSum hrepr
      have heq : (fun i ↦ (ContinuousLinearMap.apply ℂ G x)
          ((φ i).smulRight (y i))) =
          fun i ↦ B ((c.repr (A x)) i • c i) := by
        funext i
        change φ i x • y i = B ((c.repr (A x)) i • c i)
        rw [map_smul]
        congr 1
        show inner ℂ (adjoint A (c i)) x = (c.repr (A x)) i
        rw [c.repr_apply_apply, ContinuousLinearMap.adjoint_inner_left]
      rw [heq] at hpoint
      exact hpoint.unique hBsum
    rwa [hST] at hS
  have hprojective := rectTraceNorm_le_of_hasSum_smulRight φ y hmass hseries
  have hCS : ∑' i, ‖φ i‖ * ‖y i‖ ≤
      Real.sqrt (∑' i, ‖adjoint A (c i)‖ ^ (2 : ℕ)) *
        Real.sqrt (∑' i, ‖B (c i)‖ ^ (2 : ℕ)) := by
    simpa only [φ, y, innerSL_apply_norm] using
      tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
        (fun i ↦ ‖adjoint A (c i)‖) (fun i ↦ ‖B (c i)‖)
        hf hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  calc
    rectTraceNorm E G (B ∘L A) ≤ ∑' i, ‖φ i‖ * ‖y i‖ := hprojective
    _ ≤ Real.sqrt (∑' i, ‖adjoint A (c i)‖ ^ (2 : ℕ)) *
        Real.sqrt (∑' i, ‖B (c i)‖ ^ (2 : ℕ)) := hCS
    _ = ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
      have hAadj : (adjoint A).IsHilbertSchmidt := hA.adjoint
      rw [← ContinuousLinearMap.hsNormSq_eq hAadj c,
        hA.hsNormSq_adjoint,
        ← ContinuousLinearMap.hsNormSq_eq hB c]
      rfl

end RHTower
