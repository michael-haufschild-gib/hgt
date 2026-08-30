import GaloisForLFunctions.HTGeometry.CompositionRelativeVisibility
import GaloisForLFunctions.HTGeometry.ZeroFreeRadius

/-!
# The nonautonomous first-order composition: the inner state is recovered

A first-order relation for `f`, substituted along `g`, is a polynomial relation among `g`,
`h = f ∘ g` and `a = f′ ∘ g`.  Read as a polynomial in `a` it makes `a` algebraic over any field
containing `h` and `g`; read as a polynomial in `g` it makes `g` algebraic over `ℂ(h, a)` as soon as
one of its rows does not vanish identically, which is exactly the failure of autonomy.

The analytic input is that a nonzero entire function composed with a nonconstant entire function is
again nonzero: the zero set of the outer function is countable, while a nonconstant entire function
takes uncountably many values.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### A nonzero entire function stays nonzero after substitution -/

theorem countable_zeroSet_of_exists_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hne : ∃ w : ℂ, F w ≠ 0) : {w : ℂ | F w = 0}.Countable := by
  refine countable_zeroSet hF ?_
  intro z hcon
  obtain ⟨w, hw⟩ := hne
  have hFan : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
    hF.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at hcon
  have hall := hFan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hcon.frequently
  have h := hall (Set.mem_univ w)
  simp only [Pi.zero_apply] at h
  exact hw h

/-- **A nonzero entire function composed with a nonconstant entire function is nonzero.** -/
theorem exists_ne_zero_comp {F g : ℂ → ℂ} (hF : Differentiable ℂ F) (hg : Differentiable ℂ g)
    (hFne : ∃ w : ℂ, F w ≠ 0) (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    ∃ z : ℂ, F (g z) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hZ : {w : ℂ | F w = 0}.Countable := countable_zeroSet_of_exists_ne_zero hF hFne
  have hlevel : ∀ r : ℂ, {z : ℂ | g z = r}.Countable := by
    intro r
    have hdiff : Differentiable ℂ fun z : ℂ => g z - r := hg.sub (differentiable_const _)
    have hne : ∃ w : ℂ, (fun z : ℂ => g z - r) w ≠ 0 := by
      by_contra hcon'
      push Not at hcon'
      exact hncg ⟨r, fun z => by have := hcon' z; simpa [sub_eq_zero] using this⟩
    have hcount := countable_zeroSet_of_exists_ne_zero hdiff hne
    have hset : {z : ℂ | g z = r} = {z : ℂ | (fun w : ℂ => g w - r) z = 0} := by
      ext z
      simp [sub_eq_zero]
    rw [hset]
    exact hcount
  have hcover : (Set.univ : Set ℂ) ⊆ ⋃ r ∈ {w : ℂ | F w = 0}, {z : ℂ | g z = r} := by
    intro z _
    exact Set.mem_biUnion (show g z ∈ {w : ℂ | F w = 0} from hcon z) rfl
  have hunion : (⋃ r ∈ {w : ℂ | F w = 0}, {z : ℂ | g z = r}).Countable :=
    Set.Countable.biUnion hZ (fun r _ => hlevel r)
  exact absurd (hunion.mono hcover) Set.not_countable_univ

/-! ### The rows as entire functions -/

theorem analyticOnNhd_rowFun {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℕ → ℕ → Polynomial ℂ)
    (m i : ℕ) : AnalyticOnNhd ℂ (rowFun f c m i) (Set.univ : Set ℂ) :=
  analyticOnNhd_rowComp hf differentiable_id c m i

theorem differentiable_rowFun {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℕ → ℕ → Polynomial ℂ)
    (m i : ℕ) : Differentiable ℂ (rowFun f c m i) :=
  fun z => ((analyticOnNhd_rowFun hf c m i) z (Set.mem_univ z)).differentiableAt

/-- **A row that does not vanish identically gives a nonzero element of the field.** -/
theorem rowElem_ne_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) (c : ℕ → ℕ → Polynomial ℂ) (m i : ℕ)
    (hrow : ∃ w : ℂ, rowFun f c m i w ≠ 0) (hncg : ¬ ∃ cst : ℂ, ∀ z : ℂ, g z = cst) :
    (∑ k ∈ Finset.range (m + 1),
      Polynomial.aeval (jetElem hcomp 0) (c i k) * (compJetElem hf hg 1) ^ k) ≠ 0 := by
  rw [← analyticMeroElement_rowComp hf hg hcomp c m i]
  intro hzero
  have hz := (analyticMeroElement_eq_zero_iff (analyticOnNhd_rowComp hf hg c m i)).mp hzero
  obtain ⟨z, hzne⟩ := exists_ne_zero_comp (differentiable_rowFun hf c m i) hg hrow hncg
  exact hzne (hz z (Set.mem_univ z))

/-! ### Reading the relation as a polynomial in the composed derivative -/

/-- The substituted relation, grouped by the powers of the composed derivative. -/
theorem firstOrder_relation_mero_swap {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w)) {d m : ℕ}
    {c : ℕ → ℕ → Polynomial ℂ}
    (hrel : ∀ w : ℂ, ∑ i ∈ Finset.range (d + 1), rowFun f c m i w * w ^ i = 0) :
    ∑ k ∈ Finset.range (m + 1),
        (∑ i ∈ Finset.range (d + 1),
          Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i)
        * (compJetElem hf hg 1) ^ k = 0 := by
  have h := firstOrder_relation_mero hf hg hcomp hrel
  have hL : ∑ k ∈ Finset.range (m + 1),
        (∑ i ∈ Finset.range (d + 1),
          Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i)
        * (compJetElem hf hg 1) ^ k
      = ∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (d + 1),
        Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i
          * (compJetElem hf hg 1) ^ k :=
    Finset.sum_congr rfl fun k _ => Finset.sum_mul _ _ _
  have hR : ∑ i ∈ Finset.range (d + 1),
        (∑ k ∈ Finset.range (m + 1),
          Polynomial.aeval (jetElem hcomp 0) (c i k) * (compJetElem hf hg 1) ^ k)
        * (jetElem hg 0) ^ i
      = ∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (d + 1),
        Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i
          * (compJetElem hf hg 1) ^ k := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.range (d + 1)) => Finset.sum_mul _ _ _,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hL, ← hR]
  exact h

/-! ### The composed derivative is algebraic over any field seeing `g` and `h` -/

/-- **A nonautonomous first-order relation makes the composed derivative algebraic** over every
field containing the composition and algebraic over the inner function. -/
theorem isAlgebraic_compJetElem_one_of_firstOrder {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    {d m i₀ k₀ : ℕ} {c : ℕ → ℕ → Polynomial ℂ} (hi₀ : i₀ ≤ d) (hk₀ : k₀ ≤ m)
    (hne : c i₀ k₀ ≠ 0)
    (hrel : ∀ w : ℂ, ∑ i ∈ Finset.range (d + 1), rowFun f c m i w * w ^ i = 0)
    {P : IntermediateField ℂ (meroField (Set.univ : Set ℂ))}
    (hH : jetElem hcomp 0 ∈ P) (hG : IsAlgebraic ↥P (jetElem hg 0)) :
    IsAlgebraic ↥P (compJetElem hf hg 1) := by
  classical
  set M : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    (algebraicClosure ↥P (meroField (Set.univ : Set ℂ))).restrictScalars ℂ with hM
  have hPM : ∀ y ∈ P, y ∈ M := fun y hy =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨y, hy⟩ : ↥P))
  have hHM : jetElem hcomp 0 ∈ M := hPM _ hH
  have hGM : jetElem hg 0 ∈ M := mem_algebraicClosure_iff.mpr hG
  have haevalM : ∀ p : Polynomial ℂ, Polynomial.aeval (jetElem hcomp 0) p ∈ M := by
    intro p
    have h1 : Polynomial.aeval (jetElem hcomp 0) p
        ∈ Algebra.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ))) :=
      Polynomial.aeval_mem_adjoin_singleton ℂ _
    have h2 : Algebra.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))
        ≤ M.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro y rfl
      exact hHM
    exact h2 h1
  have hβM : ∀ k : ℕ, (∑ i ∈ Finset.range (d + 1),
      Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i) ∈ M := by
    intro k
    refine sum_mem fun i _ => ?_
    exact IntermediateField.mul_mem _ (haevalM (c i k)) (IntermediateField.pow_mem _ hGM i)
  have hβne : ∃ k ∈ Finset.range (m + 1), (∑ i ∈ Finset.range (d + 1),
      Polynomial.aeval (jetElem hcomp 0) (c i k) * (jetElem hg 0) ^ i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hk₀' : k₀ ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hzero := hcon k₀ hk₀'
    have := eq_zero_of_sum_aeval_mul_pow hf hg hcomp hfnp hgnp hncg hncomp hzero
    exact hne (this i₀ (Finset.mem_range.mpr (by omega)))
  have hswap := firstOrder_relation_mero_swap hf hg hcomp hrel
  have halgM : IsAlgebraic ↥M (compJetElem hf hg 1) :=
    isAlgebraic_of_finsetSum_relation hβM hβne hswap
  exact mem_algebraicClosure_iff.mp (mem_algebraicClosure_of_isAlgebraic halgM)

/-! ### The chain rule inside the field -/

theorem jetElem_comp_one_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) :
    jetElem hcomp 1 = compJetElem hf hg 1 * jetElem hg 1 := by
  have h := deriv_compJetElem hf hg 0
  rw [compJetElem_zero hf hg hcomp, deriv_jetElem hcomp 0] at h
  exact h

/-! ### Relative visibility: the primitive-rigid case -/

/-- **Relative visibility, primitive-rigid case.**  If the inner function is algebraic over its own
shadow field, a first-order outer factor contributes exactly one transcendence degree. -/
theorem trdeg_visibilityField_primitive_rigid {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hfo : FirstOrderDA f)
    (hpi : IsAlgebraic ↥(IntermediateField.adjoin ℂ (shadowSet hg)) (jetElem hg 0)) :
    Algebra.trdeg ℂ ↥(visibilityField hg hcomp)
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 1 := by
  obtain ⟨d, m, c, ⟨i₀, hi₀, k₀, hk₀, hne⟩, hrel⟩ := hfo
  refine trdeg_visibilityField_eq_of_isAlgebraic_deriv hf hg hcomp hfnp hgnp ?_
  set Kh : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)) with hKh
  have hH : jetElem hcomp 0 ∈ Kh := IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  have hKle : IntermediateField.adjoin ℂ (shadowSet hg) ≤ Kh := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ hy)
  have hG : IsAlgebraic ↥Kh (jetElem hg 0) := isAlgebraic_of_le hKle hpi
  have ha := isAlgebraic_compJetElem_one_of_firstOrder hf hg hcomp hfnp hgnp hncg hncomp
    hi₀ hk₀ hne hrel hH hG
  have hjg1 : jetElem hg 1 ∈ Kh :=
    IntermediateField.subset_adjoin ℂ _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
  rw [jetElem_comp_one_eq hf hg hcomp]
  exact mem_algebraicClosure_iff.mp (mul_mem (mem_algebraicClosure_iff.mpr ha)
    (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨_, hjg1⟩ : ↥Kh))))

/-! ### Relative visibility: the nonautonomous case -/

/-- The field generated by the shadow field, the inner function and the composition. -/
def ghField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (insert (jetElem hg 0) (shadowSet hg)))

theorem jetElem_comp_zero_mem_ghField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) : jetElem hcomp 0 ∈ ghField hg hcomp :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)

theorem jetElem_zero_mem_ghField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) : jetElem hg 0 ∈ ghField hg hcomp :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem coordElem_mem_ghField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) : coordElem ∈ ghField hg hcomp :=
  IntermediateField.subset_adjoin ℂ _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem jetElem_succ_mem_ghField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) (j : ℕ) :
    jetElem hg (j + 1) ∈ ghField hg hcomp :=
  IntermediateField.subset_adjoin ℂ _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩)))

/-- Every element of `K(g,h)` has an algebraic derivative once the composed derivative does. -/
theorem deriv_isAlgebraic_ghField {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (ha : IsAlgebraic ↥(ghField hg hcomp) (compJetElem hf hg 1)) :
    ∀ y ∈ ghField hg hcomp, IsAlgebraic ↥(ghField hg hcomp) y′ := by
  rw [ghField]
  refine deriv_isAlgebraic_of_generators ?_
  rintro x (rfl | rfl | rfl | ⟨j, rfl⟩)
  · refine ⟨isAlgebraic_algebraMap
      (⟨_, jetElem_comp_zero_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp)), ?_⟩
    rw [deriv_jetElem hcomp 0, jetElem_comp_one_eq hf hg hcomp]
    exact mem_algebraicClosure_iff.mp (mul_mem (mem_algebraicClosure_iff.mpr ha)
      (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap
        (⟨_, jetElem_succ_mem_ghField hg hcomp 0⟩ : ↥(ghField hg hcomp)))))
  · refine ⟨isAlgebraic_algebraMap
      (⟨_, jetElem_zero_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp)), ?_⟩
    rw [deriv_jetElem hg 0]
    exact isAlgebraic_algebraMap
      (⟨_, jetElem_succ_mem_ghField hg hcomp 0⟩ : ↥(ghField hg hcomp))
  · refine ⟨isAlgebraic_algebraMap
      (⟨_, coordElem_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp)), ?_⟩
    rw [deriv_coordElem]
    exact isAlgebraic_algebraMap
      (⟨(1 : meroField (Set.univ : Set ℂ)), one_mem _⟩ : ↥(ghField hg hcomp))
  · refine ⟨isAlgebraic_algebraMap
      (⟨_, jetElem_succ_mem_ghField hg hcomp j⟩ : ↥(ghField hg hcomp)), ?_⟩
    rw [deriv_jetElem hg (j + 1)]
    exact isAlgebraic_algebraMap
      (⟨_, jetElem_succ_mem_ghField hg hcomp (j + 1)⟩ : ↥(ghField hg hcomp))

/-- **The visibility field is algebraic over `K(g,h)`.** -/
theorem isAlgebraic_visibilityField_over_ghField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (ha : IsAlgebraic ↥(ghField hg hcomp) (compJetElem hf hg 1)) :
    ∀ y : meroField (Set.univ : Set ℂ), y ∈ visibilityField hg hcomp →
      IsAlgebraic ↥(ghField hg hcomp) y := by
  intro y hy
  refine isAlgebraic_of_adjoin_of_generators (ghField hg hcomp)
    (shadowSet hg ∪ compSet hcomp) ?_ hy
  rintro w (hw | hw)
  · rcases hw with rfl | ⟨j, rfl⟩
    · exact isAlgebraic_algebraMap (⟨_, coordElem_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp))
    · exact isAlgebraic_algebraMap (⟨_, jetElem_succ_mem_ghField hg hcomp j⟩ :
        ↥(ghField hg hcomp))
  · rcases hw with rfl | ⟨k, rfl⟩
    · exact isAlgebraic_algebraMap (⟨_, coordElem_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp))
    · exact forall_isAlgebraic_jetElem hcomp (deriv_isAlgebraic_ghField hf hg hcomp ha)
        (jetElem_comp_zero_mem_ghField hg hcomp) k

/-- **`K(g,h)` is algebraic over the visibility field** once the inner function is. -/
theorem isAlgebraic_ghField_over_visibilityField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hG : IsAlgebraic ↥(visibilityField hg hcomp) (jetElem hg 0)) :
    ∀ y : meroField (Set.univ : Set ℂ), y ∈ ghField hg hcomp →
      IsAlgebraic ↥(visibilityField hg hcomp) y := by
  intro y hy
  rw [ghField] at hy
  refine isAlgebraic_of_adjoin_of_generators _
    (insert (jetElem hcomp 0) (insert (jetElem hg 0) (shadowSet hg))) ?_ hy
  rintro w (rfl | rfl | rfl | ⟨j, rfl⟩)
  · exact isAlgebraic_algebraMap
      (⟨_, IntermediateField.subset_adjoin ℂ _ (Or.inr (Set.mem_insert_of_mem _ ⟨0, rfl⟩))⟩ :
        ↥(visibilityField hg hcomp))
  · exact hG
  · exact isAlgebraic_algebraMap
      (⟨coordElem, IntermediateField.subset_adjoin ℂ _ (Or.inl (Set.mem_insert _ _))⟩ :
        ↥(visibilityField hg hcomp))
  · exact isAlgebraic_algebraMap
      (⟨_, IntermediateField.subset_adjoin ℂ _ (Or.inl (Set.mem_insert_of_mem _ ⟨j, rfl⟩))⟩ :
        ↥(visibilityField hg hcomp))

/-- The composed derivative lies in the visibility field. -/
theorem compJetElem_one_mem_visibilityField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    compJetElem hf hg 1 ∈ visibilityField hg hcomp := by
  have hg1ne : jetElem hg 1 ≠ 0 := jetElem_one_ne_zero hg hncg
  have hdiv : compJetElem hf hg 1 = jetElem hcomp 1 / jetElem hg 1 := by
    rw [jetElem_comp_one_eq hf hg hcomp, mul_div_assoc, div_self hg1ne, mul_one]
  rw [hdiv]
  exact IntermediateField.div_mem _
    (IntermediateField.subset_adjoin ℂ _ (Or.inr (Set.mem_insert_of_mem _ ⟨1, rfl⟩)))
    (IntermediateField.subset_adjoin ℂ _ (Or.inl (Set.mem_insert_of_mem _ ⟨0, rfl⟩)))

/-- **The inner function is algebraic over the visibility field** when the outer factor is
nonautonomous. -/
theorem isAlgebraic_inner_over_visibilityField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    {d m i₀ k₀ : ℕ} {c : ℕ → ℕ → Polynomial ℂ} (hi₀ : i₀ ≤ d) (hk₀ : k₀ ≤ m)
    (hne : c i₀ k₀ ≠ 0)
    (hrel : ∀ w : ℂ, ∑ i ∈ Finset.range (d + 1), rowFun f c m i w * w ^ i = 0)
    (hnaut : ¬ AutonomousFirstOrder f) :
    IsAlgebraic ↥(visibilityField hg hcomp) (jetElem hg 0) := by
  have hNmemH : jetElem hcomp 0 ∈ visibilityField hg hcomp :=
    IntermediateField.subset_adjoin ℂ _ (Or.inr (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
  have haN : compJetElem hf hg 1 ∈ visibilityField hg hcomp :=
    compJetElem_one_mem_visibilityField hf hg hcomp hncg
  have hρmem : ∀ i : ℕ, (∑ k ∈ Finset.range (m + 1),
      Polynomial.aeval (jetElem hcomp 0) (c i k) * (compJetElem hf hg 1) ^ k)
      ∈ visibilityField hg hcomp := by
    intro i
    refine sum_mem fun k _ => ?_
    refine IntermediateField.mul_mem _ ?_ (IntermediateField.pow_mem _ haN k)
    have h1 : Polynomial.aeval (jetElem hcomp 0) (c i k)
        ∈ Algebra.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ))) :=
      Polynomial.aeval_mem_adjoin_singleton ℂ _
    have h2 : Algebra.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))
        ≤ (visibilityField hg hcomp).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro y rfl
      exact hNmemH
    exact h2 h1
  have hrow : ∃ w : ℂ, rowFun f c m i₀ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnaut (autonomousFirstOrder_of_rowFun_eq_zero hk₀ hne hcon)
  exact isAlgebraic_of_finsetSum_relation hρmem
    ⟨i₀, Finset.mem_range.mpr (by omega), rowElem_ne_zero hf hg hcomp c m i₀ hrow hncg⟩
    (firstOrder_relation_mero hf hg hcomp hrel)

/-- **Relative visibility, nonautonomous case.**  A nonautonomous first-order outer factor applied
to a primitive-free input contributes two transcendence degrees: the inner primitive state survives
in the output differential field. -/
theorem trdeg_visibilityField_nonautonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hfo : FirstOrderDA f) (hnaut : ¬ AutonomousFirstOrder f)
    (hpi : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ (shadowSet hg)) (jetElem hg 0)) :
    Algebra.trdeg ℂ ↥(visibilityField hg hcomp)
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 2 := by
  classical
  obtain ⟨d, m, c, ⟨i₀, hi₀, k₀, hk₀, hne⟩, hrel⟩ := hfo
  have hstep1 : Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
      (insert (jetElem hg 0) (shadowSet hg)))
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 1 :=
    trdeg_adjoin_insert_eq_add_one hpi
  have htrH : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ
      (insert (jetElem hg 0) (shadowSet hg))) (jetElem hcomp 0) := by
    intro halg
    refine not_isAlgebraic_comp_over_jetField hf hg hcomp hfnp hgnp (isAlgebraic_of_le ?_ halg)
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl | ⟨j, rfl⟩)
    · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩)
    · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
    · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨j + 1, rfl⟩)
  have hstep2 : Algebra.trdeg ℂ ↥(ghField hg hcomp)
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert (jetElem hg 0) (shadowSet hg))) + 1 :=
    trdeg_adjoin_insert_eq_add_one htrH
  have haKgh : IsAlgebraic ↥(ghField hg hcomp) (compJetElem hf hg 1) :=
    isAlgebraic_compJetElem_one_of_firstOrder hf hg hcomp hfnp hgnp hncg hncomp hi₀ hk₀ hne hrel
      (jetElem_comp_zero_mem_ghField hg hcomp)
      (isAlgebraic_algebraMap (⟨_, jetElem_zero_mem_ghField hg hcomp⟩ : ↥(ghField hg hcomp)))
  have hGalgN : IsAlgebraic ↥(visibilityField hg hcomp) (jetElem hg 0) :=
    isAlgebraic_inner_over_visibilityField hf hg hcomp hncg hi₀ hk₀ hne hrel hnaut
  have hEq := trdeg_eq_of_mutually_algebraic
    (isAlgebraic_visibilityField_over_ghField hf hg hcomp haKgh)
    (isAlgebraic_ghField_over_visibilityField hg hcomp hGalgN)
  rw [hEq, hstep2, hstep1]
  ring

end

end GaloisForLFunctions.HTGeometry
