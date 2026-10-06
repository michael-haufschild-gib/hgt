import GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure
import GaloisForLFunctions.HTGeometry.PositiveIntervalConvolutionDomain

/-!
# Permutation-averaged first-failure source tomography

Sources are `k` probability laws `μ_1, …, μ_k` on `[0, 1]`, with moment survivals
`s_i(n) = a_i(n)²`, `a_i(n) = ∫ yⁿ dμ_i` (`(PFF.1)`), and the observer records the
schedule-averaged first-failure coordinates `W_r(s(n))` for every `n ≥ 1` and every position
(`(PFF.2)`–`(PFF.4)`).

* the observer is invariant under relabelling the sources;
* **`(PFF.9)`–`(PFF.12)`**: `ρ_i = μ_i ⊠ μ_i` has moments `s_i(n)`; the coefficient measures
  `E_r = ∑_{|A| = r} ⊠_{i ∈ A} ρ_i` have moments `e_r(s(n))` and are recovered from the observer;
* **`(PFF.13)`–`(PFF.15)`**: the restrictions `α_i = ρ_i|_{(0,1]}` satisfy
  `E_r|_{(0,1]} = ∑_{|A| = r} ⊠_{i ∈ A} α_i`, the coefficients of `∏_i (T + α_i)` over the domain
  `M((0,1])`;
* **`(PFF.19)`** `ρ_i = α_i + (1 - α_i((0,1])) δ_0`; **Lemma 6.1**: `μ ⊠ μ = ν ⊠ ν ⇒ μ = ν`;
* **Theorem 7.1**: the observer is injective on unordered source multisets.
-/

open MeasureTheory Set Filter Topology Polynomial Finset
open scoped ENNReal NNReal unitInterval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FirstFailure

open MeasureConvolution

variable {k : ℕ}

/-! ### Setup -/

/-- **`(PFF.1)`** the moment `a(n) = ∫ yⁿ dμ`. -/
def sourceMoment (μ : ProbabilityMeasure I) (n : ℕ) : ℝ := ∫ x, (x : ℝ) ^ n ∂(μ : Measure I)

/-- **`(PFF.1)`** the moment survival `s(n) = a(n)²`. -/
def survival (μ : ProbabilityMeasure I) (n : ℕ) : ℝ := sourceMoment μ n ^ 2

/-- **`(PFF.3)`–`(PFF.4)`** the observer: the schedule-averaged first-failure coordinate at
response moment `n + 1 ≥ 1` and position `r`. -/
def observer (μ : Fin k → ProbabilityMeasure I) (p : ℕ × Fin k) : ℝ :=
  averagedFirstFailure (fun i => survival (μ i) (p.1 + 1)) p.2

theorem esymm_comp_perm {R : Type*} [CommRing R] (s : Fin k → R) (τ : Equiv.Perm (Fin k))
    (r : ℕ) : esymm (s ∘ τ) r = esymm s r := by
  rw [esymm, esymm]
  refine Finset.sum_nbij' (fun A => A.map τ.toEmbedding) (fun A => A.map τ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_powersetCard] at hA ⊢
    exact ⟨Finset.subset_univ _, by rw [card_map]; exact hA.2⟩
  · intro A hA
    rw [mem_powersetCard] at hA ⊢
    exact ⟨Finset.subset_univ _, by rw [card_map]; exact hA.2⟩
  · intro A _; ext x; simp
  · intro A _; ext x; simp
  · intro A _; rw [prod_map]; rfl

theorem averagedFirstFailure_comp_perm {R : Type*} [Field R] [CharZero R] (s : Fin k → R)
    (τ : Equiv.Perm (Fin k)) (r : Fin k) :
    averagedFirstFailure (s ∘ τ) r = averagedFirstFailure s r := by
  rw [averagedFirstFailure_eq_div_choose, averagedFirstFailure_eq_div_choose, esymm_comp_perm,
    esymm_comp_perm]

/-- **`(PFF.4)`** the observer is invariant under relabelling the sources. -/
theorem observer_comp_perm (μ : Fin k → ProbabilityMeasure I) (τ : Equiv.Perm (Fin k)) :
    observer (μ ∘ τ) = observer μ := by
  funext p
  exact averagedFirstFailure_comp_perm (fun i => survival (μ i) (p.1 + 1)) τ p.2

/-! ### Multiplicative convolution and coefficient measures -/

theorem integral_pow_mconv (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂(μ ∗ₘ ν) = (∫ x, (x : ℝ) ^ n ∂μ) * ∫ x, (x : ℝ) ^ n ∂ν := by
  rw [Measure.mconv, integral_map measurable_mul.aemeasurable
    ((measurable_subtype_coe.pow_const n).aestronglyMeasurable)]
  calc ∫ p : I × I, ((p.1 * p.2 : I) : ℝ) ^ n ∂(μ.prod ν) =
        ∫ p : I × I, (p.1 : ℝ) ^ n * (p.2 : ℝ) ^ n ∂(μ.prod ν) :=
        integral_congr_ae (ae_of_all _ fun p => by dsimp only; rw [Set.Icc.coe_mul, mul_pow])
    _ = _ := integral_prod_mul (fun x : I => (x : ℝ) ^ n) (fun x : I => (x : ℝ) ^ n)

/-- **`(PFF.9)`** `ρ = μ ⊠ μ`. -/
def selfConv (μ : ProbabilityMeasure I) : Measure I := (μ : Measure I) ∗ₘ (μ : Measure I)

instance (μ : ProbabilityMeasure I) : IsProbabilityMeasure (selfConv μ) := by
  unfold selfConv Measure.mconv
  exact Measure.isProbabilityMeasure_map measurable_mul.aemeasurable

/-- **`(PFF.10)`** `∫ xⁿ dρ = a(n)² = s(n)`. -/
theorem integral_pow_selfConv (μ : ProbabilityMeasure I) (n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂selfConv μ = survival μ n := by
  rw [selfConv, integral_pow_mconv, survival, sourceMoment, sq]

/-- The coercion `I →* ℝ`. -/
def coeHom : I →* ℝ where
  toFun x := x
  map_one' := rfl
  map_mul' x y := Set.Icc.coe_mul x y

/-- The iterated multiplicative convolution `⊠_{i ∈ A} ρ_i`. -/
def prodConv (A : Finset (Fin k)) (ρ : Fin k → Measure I) : Measure I :=
  (Measure.pi fun i : A => ρ i).map fun x => ∏ i, x i

theorem measurable_prod_coords (A : Finset (Fin k)) :
    Measurable fun x : (A → I) => ∏ i, x i :=
  Finset.measurable_prod _ fun i _ => measurable_pi_apply i

instance (A : Finset (Fin k)) (ρ : Fin k → Measure I) [∀ i, IsProbabilityMeasure (ρ i)] :
    IsProbabilityMeasure (prodConv A ρ) := by
  unfold prodConv
  exact Measure.isProbabilityMeasure_map (measurable_prod_coords A).aemeasurable

instance (A : Finset (Fin k)) (ρ : Fin k → Measure I) [∀ i, IsFiniteMeasure (ρ i)] :
    IsFiniteMeasure (prodConv A ρ) := by
  unfold prodConv; infer_instance

theorem integral_pow_prodConv (A : Finset (Fin k)) (ρ : Fin k → Measure I)
    [∀ i, IsFiniteMeasure (ρ i)] (n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂prodConv A ρ = ∏ i ∈ A, ∫ x, (x : ℝ) ^ n ∂ρ i := by
  rw [prodConv, integral_map (measurable_prod_coords A).aemeasurable
    ((measurable_subtype_coe.pow_const n).aestronglyMeasurable)]
  have hcoe : ∀ x : A → I, ((∏ i, x i : I) : ℝ) ^ n = ∏ i, ((x i : I) : ℝ) ^ n := fun x => by
    rw [Finset.prod_pow]
    exact congrArg (· ^ n) (map_prod coeHom x univ)
  simp_rw [hcoe]
  rw [integral_fintype_prod_eq_prod (fun (i : A) (x : I) => ((x : ℝ)) ^ n)]
  exact Finset.prod_coe_sort A (fun i => ∫ x, (x : ℝ) ^ n ∂ρ i)

/-- **`(PFF.11)`** the coefficient measure `E_r = ∑_{|A| = r} ⊠_{i ∈ A} ρ_i`. -/
def coeffMeasure (ρ : Fin k → Measure I) (r : ℕ) : Measure I :=
  ∑ A ∈ (univ : Finset (Fin k)).powersetCard r, prodConv A ρ

instance (ρ : Fin k → Measure I) [∀ i, IsFiniteMeasure (ρ i)] (r : ℕ) :
    IsFiniteMeasure (coeffMeasure ρ r) := by
  unfold coeffMeasure; infer_instance

/-- **`(PFF.11)`** `E_0 = δ_1`. -/
theorem coeffMeasure_zero (ρ : Fin k → Measure I) : coeffMeasure ρ 0 = Measure.dirac 1 := by
  haveI : IsEmpty (∅ : Finset (Fin k)) := ⟨fun i => Finset.notMem_empty _ i.2⟩
  rw [coeffMeasure, powersetCard_zero, sum_singleton, prodConv, Measure.pi_of_empty]
  refine (Measure.map_dirac' (measurable_prod_coords (∅ : Finset (Fin k))) _).trans ?_
  congr 1

/-- **`(PFF.11)`–`(PFF.12)`** `E_r` has total mass `C(k, r)` and moments `e_r(s(n))`. -/
theorem integral_pow_coeffMeasure (ρ : Fin k → Measure I) [∀ i, IsFiniteMeasure (ρ i)] (r n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂coeffMeasure ρ r = esymm (fun i => ∫ x, (x : ℝ) ^ n ∂ρ i) r := by
  rw [coeffMeasure, integral_finsetSum_measure (f := fun x : I => (x : ℝ) ^ n) fun A _ =>
    (integrable_const (1 : ℝ)).mono' ((measurable_subtype_coe.pow_const n).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg x.2.1]; exact pow_le_one₀ x.2.1 x.2.2)]
  exact Finset.sum_congr rfl fun A _ => integral_pow_prodConv A ρ n

theorem coeffMeasure_univ (ρ : Fin k → Measure I) [∀ i, IsProbabilityMeasure (ρ i)] (r : ℕ) :
    coeffMeasure ρ r univ = (k.choose r : ℝ≥0∞) := by
  rw [coeffMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-! ### Recovery of the coefficient measures -/

/-- The survivals `s_i(n)` of a source family. -/
def survivals (μ : Fin k → ProbabilityMeasure I) (n : ℕ) : Fin k → ℝ := fun i => survival (μ i) n

theorem observer_apply (μ : Fin k → ProbabilityMeasure I) (n : ℕ) (r : Fin k) :
    observer μ (n, r) = averagedFirstFailure (survivals μ (n + 1)) r := rfl

/-- The coefficient measure `E_r` of a source family. -/
def sourceCoeffMeasure (μ : Fin k → ProbabilityMeasure I) (r : ℕ) : Measure I :=
  coeffMeasure (fun i => selfConv (μ i)) r

instance (μ : Fin k → ProbabilityMeasure I) (r : ℕ) : IsFiniteMeasure (sourceCoeffMeasure μ r) := by
  unfold sourceCoeffMeasure; infer_instance

theorem integral_pow_sourceCoeffMeasure (μ : Fin k → ProbabilityMeasure I) (r n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂sourceCoeffMeasure μ r = esymm (survivals μ n) r := by
  rw [sourceCoeffMeasure, integral_pow_coeffMeasure]
  simp_rw [integral_pow_selfConv]
  rfl

theorem survival_zero (μ : ProbabilityMeasure I) : survival μ 0 = 1 := by
  simp [survival, sourceMoment]

/-- **`(PFF.7)`, `(PFF.12)`**: the observer recovers every coefficient measure `E_r`, `r ≤ k`
(Hausdorff determinacy; the zeroth moment is the total mass `C(k, r)`). -/
theorem sourceCoeffMeasure_eq_of_observer_eq {μ ν : Fin k → ProbabilityMeasure I}
    (h : observer μ = observer ν) {r : ℕ} (hr : r ≤ k) :
    sourceCoeffMeasure μ r = sourceCoeffMeasure ν r := by
  refine MeasureConvolution.measure_eq_of_moments_eq _ _ fun n => ?_
  rw [integral_pow_sourceCoeffMeasure, integral_pow_sourceCoeffMeasure]
  rcases n with _ | n
  · have hμ : survivals μ 0 = fun _ => 1 := funext fun i => survival_zero _
    have hν : survivals ν 0 = fun _ => 1 := funext fun i => survival_zero _
    rw [hμ, hν]
  · have hobs : ∀ r' : Fin k, averagedFirstFailure (survivals μ (n + 1)) r' =
        averagedFirstFailure (survivals ν (n + 1)) r' := fun r' => by
      rw [← observer_apply, ← observer_apply, h]
    exact esymm_eq_of_averagedFirstFailure_eq (R := ℝ) hobs r hr

/-! ### The absorbing-zero repair -/

/-- **`(PFF.13)`** the restriction `α = ρ|_{(0,1]}`. -/
def posPart (ρ : Measure I) : Measure I := ρ.restrict ({0}ᶜ : Set I)

instance (ρ : Measure I) [IsFiniteMeasure ρ] : IsFiniteMeasure (posPart ρ) := by
  unfold posPart; infer_instance

theorem posPart_singleton_zero (ρ : Measure I) : posPart ρ ({0} : Set I) = 0 := by
  rw [posPart, Measure.restrict_apply (measurableSet_singleton 0)]
  simp

theorem prod_ne_zero_iff (A : Finset (Fin k)) (x : A → I) :
    (∏ i, x i) ≠ 0 ↔ ∀ i, x i ≠ 0 := by
  have hcoe : ((∏ i, x i : I) : ℝ) = ∏ i, ((x i : I) : ℝ) := map_prod coeHom x univ
  constructor
  · intro h i hi
    apply h
    apply Subtype.ext
    rw [hcoe]
    exact Finset.prod_eq_zero (mem_univ i) (by rw [hi]; rfl)
  · intro h hprod
    have := congrArg Subtype.val hprod
    rw [hcoe] at this
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 this
    exact h i (Subtype.ext hi)

theorem posPart_prodConv (A : Finset (Fin k)) (ρ : Fin k → Measure I)
    [∀ i, IsFiniteMeasure (ρ i)] : posPart (prodConv A ρ) = prodConv A fun i => posPart (ρ i) := by
  rw [posPart, prodConv, Measure.restrict_map (measurable_prod_coords A)
    (measurableSet_singleton 0).compl]
  have hpre : (fun x : A → I => ∏ i, x i) ⁻¹' ({0}ᶜ : Set I) =
      Set.univ.pi fun _ : A => ({0}ᶜ : Set I) := by
    ext x
    simp only [Set.mem_preimage, mem_compl_iff, mem_singleton_iff, mem_univ_pi]
    exact prod_ne_zero_iff A x
  rw [hpre, Measure.restrict_pi_pi]
  rfl

theorem posPart_finset_sum {ι : Type*} (s : Finset ι) (ρ : ι → Measure I) :
    posPart (∑ i ∈ s, ρ i) = ∑ i ∈ s, posPart (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [posPart]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, posPart, Measure.restrict_add, ← ih]; rfl

/-- **`(PFF.14)`** `E_r|_{(0,1]} = ∑_{|A| = r} ⊠_{i ∈ A} α_i`. -/
theorem posPart_coeffMeasure (ρ : Fin k → Measure I) [∀ i, IsFiniteMeasure (ρ i)] (r : ℕ) :
    posPart (coeffMeasure ρ r) = coeffMeasure (fun i => posPart (ρ i)) r := by
  rw [coeffMeasure, coeffMeasure, posPart_finset_sum]
  exact Finset.sum_congr rfl fun A _ => posPart_prodConv A ρ

/-- **`(PFF.19)`** `ρ = α + (1 - α((0,1])) δ_0` for a probability law `ρ`. -/
theorem eq_posPart_add_atom (ρ : Measure I) [IsProbabilityMeasure ρ] :
    ρ = posPart ρ + (1 - posPart ρ univ) • Measure.dirac 0 := by
  have hsplit := Measure.restrict_add_restrict_compl (μ := ρ) (measurableSet_singleton (0 : I))
  rw [Measure.restrict_singleton] at hsplit
  rw [posPart, Measure.restrict_apply_univ, prob_compl_eq_one_sub (measurableSet_singleton 0),
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  conv_lhs => rw [← hsplit]
  rw [add_comm]

/-- **Lemma 6.1**: the positive convolution square root is unique. -/
theorem selfConv_injective {μ ν : ProbabilityMeasure I} (h : selfConv μ = selfConv ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  refine MeasureConvolution.measure_eq_of_moments_eq _ _ fun n => ?_
  have h2 : survival μ n = survival ν n := by
    rw [← integral_pow_selfConv, ← integral_pow_selfConv, h]
  have hnn : ∀ ρ : ProbabilityMeasure I, 0 ≤ sourceMoment ρ n := fun ρ =>
    integral_nonneg fun x => pow_nonneg x.2.1 n
  exact (sq_eq_sq₀ (hnn μ) (hnn ν)).1 h2

/-! ### The formation polynomial over `M((0,1])` -/

theorem ofMeasure_apply_singleton_zero (α : Measure I) [IsFiniteMeasure α]
    (h : α ({0} : Set I) = 0) : ofMeasure α ({0} : Set I) = 0 := by
  rw [ofMeasure_apply _ (measurableSet_singleton 0), h]; simp

/-- A finite measure without atom at `0` as an element of `M((0,1])`. -/
def toPositive (α : Measure I) [IsFiniteMeasure α] (h : α ({0} : Set I) = 0) : positiveSupport :=
  ⟨ConvMeasure.ofComplexMeasure (ofMeasure α), ofMeasure_apply_singleton_zero α h⟩

/-- The moment homomorphism of the convolution ring. -/
def momentHom : ConvMeasure →* (ℕ → ℂ) where
  toFun := momentSeq
  map_one' := momentSeq_one
  map_mul' := momentSeq_mul

theorem momentSeq_ofMeasure (α : Measure I) [IsFiniteMeasure α] (n : ℕ) :
    momentSeq (ofMeasure α) n = ((∫ x, (x : ℝ) ^ n ∂α : ℝ) : ℂ) := by
  rw [momentSeq, pair_ofMeasure _ (isTest_powTest n), integral_powTest]

/-- **§10, boundary 2**: on all of `[0, 1]` the absorbing atom is a zero divisor,
`δ_0 ⊠ (δ_1 - δ_{1/2}) = 0` with both factors nonzero; the restriction to `(0, 1]` is
load-bearing. -/
theorem absorbing_zero_divisor :
    ConvMeasure.ofComplexMeasure (ofMeasure (Measure.dirac (0 : I))) *
        ConvMeasure.ofComplexMeasure (ofMeasure (Measure.dirac (1 : I)) -
          ofMeasure (Measure.dirac (⟨1 / 2, by norm_num, by norm_num⟩ : I))) = 0 ∧
      ConvMeasure.ofComplexMeasure (ofMeasure (Measure.dirac (0 : I))) ≠ 0 ∧
      ConvMeasure.ofComplexMeasure (ofMeasure (Measure.dirac (1 : I)) -
          ofMeasure (Measure.dirac (⟨1 / 2, by norm_num, by norm_num⟩ : I))) ≠ 0 := by
  have hd : ∀ (x : I) (n : ℕ),
      momentSeq (ofMeasure (Measure.dirac x)) n = (((x : ℝ) ^ n : ℝ) : ℂ) :=
    fun x n => by rw [momentSeq_ofMeasure, integral_dirac]
  have hdiff : ∀ n, momentSeq (ofMeasure (Measure.dirac (1 : I)) -
      ofMeasure (Measure.dirac (⟨1 / 2, by norm_num, by norm_num⟩ : I))) n =
        1 - (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) := fun n => by
    rw [momentSeq, pair_sub _ _ (isTest_powTest n), ← momentSeq, ← momentSeq, hd, hd]
    simp
  have hzero : momentSeq (0 : ConvMeasure) = 0 := funext fun n => pair_zero (isTest_powTest n)
  refine ⟨momentSeq_injective ?_, fun h => ?_, fun h => ?_⟩
  · rw [momentSeq_mul, hzero]
    funext n
    rw [Pi.mul_apply, Pi.zero_apply]
    change momentSeq (ofMeasure (Measure.dirac (0 : I))) n * momentSeq (ofMeasure
      (Measure.dirac (1 : I)) - ofMeasure (Measure.dirac (⟨1 / 2, by norm_num, by norm_num⟩ : I)))
        n = 0
    rw [hd, hdiff]
    rcases n with _ | n
    · simp
    · simp
  · have := congrArg (fun c : ConvMeasure => momentSeq c 0) h
    simp only [hzero, Pi.zero_apply] at this
    change momentSeq (ofMeasure (Measure.dirac (0 : I))) 0 = 0 at this
    rw [hd] at this
    simp at this
  · have := congrArg (fun c : ConvMeasure => momentSeq c 1) h
    simp only [hzero, Pi.zero_apply] at this
    change momentSeq (ofMeasure (Measure.dirac (1 : I)) - ofMeasure (Measure.dirac
      (⟨1 / 2, by norm_num, by norm_num⟩ : I))) 1 = 0 at this
    rw [hdiff] at this
    norm_num at this

/-- In the convolution ring, `∏_{i ∈ A} α_i = ⊠_{i ∈ A} α_i`. -/
theorem prod_ofMeasure (A : Finset (Fin k)) (α : Fin k → Measure I) [∀ i, IsFiniteMeasure (α i)] :
    ∏ i ∈ A, ConvMeasure.ofComplexMeasure (ofMeasure (α i)) =
      ConvMeasure.ofComplexMeasure (ofMeasure (prodConv A α)) := by
  apply momentSeq_injective
  change momentHom (∏ i ∈ A, ConvMeasure.ofComplexMeasure (ofMeasure (α i))) = _
  rw [map_prod]
  funext n
  rw [Finset.prod_apply]
  change ∏ i ∈ A, momentSeq (ofMeasure (α i)) n = momentSeq (ofMeasure (prodConv A α)) n
  simp_rw [momentSeq_ofMeasure, integral_pow_prodConv]
  push_cast
  rfl

theorem ofMeasure_add (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ofMeasure (μ + ν) = ofMeasure μ + ofMeasure ν := by
  refine VectorMeasure.ext fun S hS => ?_
  rw [FunLike.coe_add, Pi.add_apply, ofMeasure_apply _ hS, ofMeasure_apply _ hS,
    ofMeasure_apply _ hS, Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
  push_cast
  rfl

theorem ofMeasure_finset_sum {ι : Type*} (s : Finset ι) (ρ : ι → Measure I)
    [∀ i, IsFiniteMeasure (ρ i)] :
    ConvMeasure.ofComplexMeasure (ofMeasure (∑ i ∈ s, ρ i)) =
      ∑ i ∈ s, ConvMeasure.ofComplexMeasure (ofMeasure (ρ i)) := by
  change ofMeasure (∑ i ∈ s, ρ i) = ∑ i ∈ s, ofMeasure (ρ i)
  refine VectorMeasure.ext fun S hS => ?_
  have h1 : (∑ i ∈ s, ρ i) S = ∑ i ∈ s, ρ i S := by simp
  rw [ofMeasure_apply _ hS, h1, ENNReal.toReal_sum fun i _ => measure_ne_top _ _,
    Complex.ofReal_sum]
  conv_rhs => rw [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (ofMeasure_apply _ hS).symm

/-- The restricted self-convolution `α = (μ ⊠ μ)|_{(0,1]}` as an element of `M((0,1])`. -/
def alphaElem (μ : ProbabilityMeasure I) : positiveSupport :=
  toPositive (posPart (selfConv μ)) (posPart_singleton_zero _)

/-- **`(PFF.15)`** the formation polynomial `∏_i (T + α_i)` over the domain `M((0,1])`. -/
def formationPoly (μ : Fin k → ProbabilityMeasure I) : Polynomial positiveSupport :=
  ((univ.val.map fun i => alphaElem (μ i)).map fun a => X + C a).prod

/-- The elementary coefficients of `∏ (T + α_i)` are the restricted coefficient measures. -/
theorem esymm_alphaElem (μ : Fin k → ProbabilityMeasure I) (r : ℕ) :
    ((univ.val.map fun i => alphaElem (μ i)).esymm r : ConvMeasure) =
      ConvMeasure.ofComplexMeasure (ofMeasure (posPart (sourceCoeffMeasure μ r))) := by
  have hm : posPart (sourceCoeffMeasure μ r) =
      ∑ A ∈ (univ : Finset (Fin k)).powersetCard r,
        prodConv A fun i => posPart (selfConv (μ i)) := posPart_coeffMeasure _ r
  simp only [hm]
  rw [ofMeasure_finset_sum, Finset.esymm_map_val, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [SubmonoidClass.coe_finsetProd]
  exact prod_ofMeasure A _

/-- **Theorem 7.1**: the observer is injective on unordered source multisets. -/
theorem observer_injective {μ ν : Fin k → ProbabilityMeasure I}
    (h : observer μ = observer ν) : univ.val.map μ = univ.val.map ν := by
  have hcoef : ∀ r, (univ.val.map fun i => alphaElem (μ i)).esymm r =
      (univ.val.map fun i => alphaElem (ν i)).esymm r := by
    intro r
    by_cases hr : r ≤ k
    · apply Subtype.ext
      rw [esymm_alphaElem, esymm_alphaElem]
      simp only [sourceCoeffMeasure_eq_of_observer_eq h hr]
    · have hcard : ∀ ρ : Fin k → ProbabilityMeasure I,
          (univ.val.map fun i => alphaElem (ρ i)).esymm r = 0 := fun ρ => by
        rw [Finset.esymm_map_val, powersetCard_eq_empty.2 (by simpa using hr), sum_empty]
      rw [hcard, hcard]
  have hpoly : formationPoly μ = formationPoly ν := by
    rw [formationPoly, formationPoly, Multiset.prod_X_add_C_eq_sum_esymm,
      Multiset.prod_X_add_C_eq_sum_esymm]
    simp only [Multiset.card_map, hcoef]
  have hα := multiset_eq_of_prod_X_add_C_eq _ _ hpoly
  have hinj : Function.Injective alphaElem := by
    intro a b hab
    have h1 : ofMeasure (posPart (selfConv a)) = ofMeasure (posPart (selfConv b)) :=
      congrArg (fun e : positiveSupport => ConvMeasure.toMeasure (e : ConvMeasure)) hab
    have h2 : posPart (selfConv a) = posPart (selfConv b) := by
      have := congrArg ComplexMeasure.re h1
      rw [re_ofMeasure, re_ofMeasure, Measure.toSignedMeasure_eq_toSignedMeasure_iff] at this
      exact this
    apply selfConv_injective
    rw [eq_posPart_add_atom (selfConv a), eq_posPart_add_atom (selfConv b), h2]
  have hμ : univ.val.map (fun i => alphaElem (μ i)) = (univ.val.map μ).map alphaElem := by
    rw [Multiset.map_map]; rfl
  have hν : univ.val.map (fun i => alphaElem (ν i)) = (univ.val.map ν).map alphaElem := by
    rw [Multiset.map_map]; rfl
  rw [hμ, hν] at hα
  exact Multiset.map_injective hinj hα

/-- Tuples with the same multiset of entries differ by a permutation. -/
theorem exists_perm_of_multiset_eq {μ ν : Fin k → ProbabilityMeasure I}
    (hm : univ.val.map μ = univ.val.map ν) : ∃ τ : Equiv.Perm (Fin k), μ = ν ∘ τ := by
  classical
  have key : ∀ (f : Fin k → ProbabilityMeasure I) (c : ProbabilityMeasure I),
      Fintype.card {a // f a = c} = Multiset.count c (univ.val.map f) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun a _ => eq_comm
  have hcard : ∀ c, Fintype.card {a // μ a = c} = Fintype.card {a // ν a = c} := fun c => by
    rw [key μ c, key ν c, hm]
  let e := Equiv.ofFiberEquiv (f := μ) (g := ν) fun c => Fintype.equivOfCardEq (hcard c)
  exact ⟨e, funext fun a => (Equiv.ofFiberEquiv_map _ a).symm⟩

/-- **Theorem 7.1** (permutation form): equal observations force the source tuples to differ only
by a permutation. -/
theorem exists_perm_of_observer_eq {μ ν : Fin k → ProbabilityMeasure I}
    (h : observer μ = observer ν) : ∃ τ : Equiv.Perm (Fin k), μ = ν ∘ τ :=
  exists_perm_of_multiset_eq (observer_injective h)

end GaloisForLFunctions.HTGeometry.FirstFailure
