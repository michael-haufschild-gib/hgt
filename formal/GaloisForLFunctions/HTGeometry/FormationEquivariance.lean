import GaloisForLFunctions.HTGeometry.FormationCumulants
import GaloisForLFunctions.HTGeometry.FormationCompactOpenTopology
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Functional-equation action is information-neutral

A continuous monoid endomorphism `A : K → K` acts on `M(K)` by pushforward,
`(A_*Φ)(f) = Φ(f ∘ A)`.  This is a contractive unital algebra homomorphism, since
`f(A(xy)) = f(A x · A y)`, and it preserves positivity.  For a continuous monoid automorphism it is
an isometric algebra automorphism with inverse `(A⁻¹)_*`.

**Theorem 8.1.**  The action on finite packets, `A ↦ (A_*α_j)_j`, extends coefficientwise to the
compactification: `A_* F(z) = Exp_⋆(z A_*γ) ⋆ Π_j (δ_1 + z A_*α_j)`.  It
preserves the mass law, the atomic/dust layers and every cumulant degree, is continuous in the
compact-open weak topology (testing `A_*F` against `f` is testing `F` against `f ∘ A`), and is the
unique continuous extension of the packet action to the decorated formations.  An involution lifts
to an involution.  Pushforward under a homeomorphism transports Radon–Nikodym derivatives and
singular parts, so every `f`-divergence `D_f(μ‖ν) = ∫ f(dμ/dν) dν + f'(∞) μ_⊥(K)` is invariant.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

attribute [local instance] ratAlgebra

/-! ### Pushforward -/

/-- Composition with a continuous map, a contraction of `C(K, ℂ)`. -/
def compCLM (A : C(K, K)) : C(K, ℂ) →L[ℂ] C(K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun f => by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x)

/-- The pushforward `(A_*Φ)(f) = Φ(f ∘ A)`. -/
def push (A : C(K, K)) (Φ : MeasureAlgebra K) : MeasureAlgebra K :=
  ofDual ((toDual Φ).comp (compCLM A))

omit [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] [MeasurableSpace K]
  [BorelSpace K] in
@[simp] theorem push_apply (A : C(K, K)) (Φ : MeasureAlgebra K) (f : C(K, ℂ)) :
    push A Φ f = Φ (f.comp A) := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem norm_push_le (A : C(K, K)) (Φ : MeasureAlgebra K) : ‖push A Φ‖ ≤ ‖Φ‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun f => (le_opNorm Φ _).trans
    (mul_le_mul_of_nonneg_left ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x =>
      f.norm_coe_le_norm (A x)) (norm_nonneg _))

omit [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] [MeasurableSpace K]
  [BorelSpace K] in
theorem push_push (A B : C(K, K)) (Φ : MeasureAlgebra K) :
    push A (push B Φ) = push (A.comp B) Φ := rfl

omit [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] [MeasurableSpace K]
  [BorelSpace K] in
theorem push_id (Φ : MeasureAlgebra K) : push (ContinuousMap.id K) Φ = Φ := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem push_add (A : C(K, K)) (Φ Ψ : MeasureAlgebra K) :
    push A (Φ + Ψ) = push A Φ + push A Ψ := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem push_smul (A : C(K, K)) (c : ℂ) (Φ : MeasureAlgebra K) :
    push A (c • Φ) = c • push A Φ := rfl

omit [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] [MeasurableSpace K]
  [BorelSpace K] in
theorem isPositive_push (A : C(K, K)) {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    IsPositive (push A Φ) := fun f hf => hΦ (f.comp A) fun x => hf (A x)

/-- Pushforward along a continuous monoid endomorphism, as a unital `ℂ`-algebra homomorphism. -/
def pushAlgHom (A : K →ₜ* K) : MeasureAlgebra K →ₐ[ℂ] MeasureAlgebra K where
  toFun := push A.toContinuousMap
  map_one' := MeasureAlgebra.ext fun f => by simp
  map_mul' Φ Ψ := MeasureAlgebra.ext fun f => by
    rw [push_apply, mul_apply, mul_apply]
    have h : rightTransform Ψ (f.comp A.toContinuousMap) =
        (rightTransform (push A.toContinuousMap Ψ) f).comp A.toContinuousMap := by
      ext x
      rw [rightTransform_apply, ContinuousMap.comp_apply, rightTransform_apply, push_apply]
      congr 1
      ext y
      simp [shift_apply, map_mul]
    rw [h]
    rfl
  map_zero' := rfl
  map_add' := push_add _
  commutes' c := MeasureAlgebra.ext fun f => by simp [algebraMap_apply']

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem pushAlgHom_apply (A : K →ₜ* K) (Φ : MeasureAlgebra K) :
    pushAlgHom A Φ = push A.toContinuousMap Φ := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem continuous_pushAlgHom (A : K →ₜ* K) : Continuous (pushAlgHom A) :=
  AddMonoidHomClass.continuous_of_bound (pushAlgHom A) 1 fun Φ => by
    rw [one_mul]; exact norm_push_le _ Φ

/-! ### Transport of formations -/

section Transport

variable (A : K →ₜ* K)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem pushAlgHom_exp (X : MeasureAlgebra K) : pushAlgHom A (exp X) = exp (pushAlgHom A X) :=
  map_exp (pushAlgHom A) (continuous_pushAlgHom A) X

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem pushAlgHom_formation {m : ℕ} (α : Fin m → MeasureAlgebra K) (z : ℂ) :
    pushAlgHom A (formation α z) = formation (fun j => pushAlgHom A (α j)) z := by
  simp [formation, map_prod]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- the pushforward of a decorated formation is the decorated formation of the
pushed dust and atoms. -/
theorem pushAlgHom_decorated {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) (z : ℂ) :
    pushAlgHom A (decorated γ α z) =
      decorated (pushAlgHom A γ) (fun j => pushAlgHom A (α j)) z := by
  have hprod := (multipliable_formation hα z).hasProd.map (pushAlgHom A) (continuous_pushAlgHom A)
  rw [decorated, decorated, map_mul, pushAlgHom_exp, map_smul, ← hprod.tprod_eq]
  congr 1
  refine tprod_congr fun j => ?_
  simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem summable_norm_push {α : ℕ → MeasureAlgebra K} (hα : Summable fun j => ‖α j‖) :
    Summable fun j => ‖pushAlgHom A (α j)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_push_le _ _) hα

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The pushforward transports every cumulant. -/
theorem pushAlgHom_cumulant {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hα : Summable fun j => ‖α j‖) (r : ℕ) :
    pushAlgHom A (cumulant γ α r) = cumulant (pushAlgHom A γ) (fun j => pushAlgHom A (α j)) r := by
  cases r with
  | zero => simp [cumulant]
  | succ r =>
    have hs := (summable_norm_pow hα r).of_norm
    rw [cumulant, cumulant, map_add, map_smul]
    congr 1
    · split_ifs <;> simp
    · congr 1
      have := (hs.hasSum.map (pushAlgHom A) (continuous_pushAlgHom A)).tsum_eq
      simpa [Function.comp_def, map_pow] using this.symm

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Positivity and the mass law are preserved: pushforward maps the decorated formations of
mass `≤ C` into themselves, dust to dust and atoms to atoms. -/
theorem push_mem_decoratedSet {C : ℝ} {F : ℂ → MeasureAlgebra K} (hF : F ∈ decoratedSet C) :
    (fun z => pushAlgHom A (F z)) ∈ decoratedSet C := by
  obtain ⟨γ, α, hγ, hα, hs, hm, rfl⟩ := hF
  refine ⟨pushAlgHom A γ, fun j => pushAlgHom A (α j), isPositive_push _ hγ,
    fun j => isPositive_push _ (hα j), summable_norm_push A hs, ?_,
    funext fun z => pushAlgHom_decorated A hs z⟩
  refine le_trans (add_le_add (norm_push_le _ γ)
    ((summable_norm_push A hs).tsum_le_tsum (fun j => norm_push_le _ _) hs)) hm

end Transport

/-! ### Automorphisms: isometry, inverse, involution -/

section Automorphism

variable (A : K ≃ₜ* K)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem push_symm_push (Φ : MeasureAlgebra K) :
    pushAlgHom (A.symm : K →ₜ* K) (pushAlgHom (A : K →ₜ* K) Φ) = Φ :=
  MeasureAlgebra.ext fun f => by
    simp only [pushAlgHom_apply, push_apply]
    congr 1
    ext x
    simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem push_push_symm (Φ : MeasureAlgebra K) :
    pushAlgHom (A : K →ₜ* K) (pushAlgHom (A.symm : K →ₜ* K) Φ) = Φ :=
  MeasureAlgebra.ext fun f => by
    simp only [pushAlgHom_apply, push_apply]
    congr 1
    ext x
    simp

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- pushforward along an automorphism is a total-variation isometry. -/
theorem norm_push_aut (Φ : MeasureAlgebra K) : ‖pushAlgHom (A : K →ₜ* K) Φ‖ = ‖Φ‖ :=
  le_antisymm (norm_push_le _ _) (by
    conv_lhs => rw [← push_symm_push A Φ]
    exact norm_push_le _ _)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- An involutive automorphism lifts to an involution. -/
theorem push_involutive (hA : ∀ x, A (A x) = x) (Φ : MeasureAlgebra K) :
    pushAlgHom (A : K →ₜ* K) (pushAlgHom (A : K →ₜ* K) Φ) = Φ :=
  MeasureAlgebra.ext fun f => by
    simp only [pushAlgHom_apply, push_apply]
    congr 1
    ext x
    simp [hA]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- The mass law is preserved exactly. -/
theorem mass_push_aut (γ : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) :
    ‖pushAlgHom (A : K →ₜ* K) γ‖ + ∑' j, ‖pushAlgHom (A : K →ₜ* K) (α j)‖ =
      ‖γ‖ + ∑' j, ‖α j‖ := by
  simp only [norm_push_aut]

end Automorphism

/-! ### Continuity and unique extension -/

/-- Pushforward of measure-valued functions of `z`. -/
def pushForm (A : K →ₜ* K) (F : FormSpace K) : FormSpace K := fun z => pushAlgHom A (F z)

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem testMap_pushForm (A : K →ₜ* K) (f : C(K, ℂ)) (F : FormSpace K) :
    testMap f (pushForm A F) = testMap (f.comp A.toContinuousMap) F := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Pushforward is uniformly continuous for the compact-open weak uniformity. -/
theorem uniformContinuous_pushForm (A : K →ₜ* K) : UniformContinuous (pushForm A) :=
  uniformContinuous_iInf_rng.2 fun f =>
    uniformContinuous_comap' (uniformContinuous_testMap (f.comp A.toContinuousMap))

/-- **Theorem 8.1, unique extension.**  A continuous self-map of the compact-open weak space that
pushes every factor of each positive finite packet of mass `≤ C` forward agrees with the
pushforward on all decorated formations of mass `≤ C`. -/
theorem eqOn_pushForm_of_continuous (A : K →ₜ* K) (C : ℝ) {T : FormSpace K → FormSpace K}
    (hT : Continuous T)
    (h : ∀ {m : ℕ} (α : Fin m → MeasureAlgebra K), (∀ j, IsPositive (α j)) → packetMass α ≤ C →
      T (formation α) = formation fun j => pushAlgHom A (α j)) :
    EqOn T (pushForm A) (inFormSpace (decoratedSet C)) := by
  rw [← closure_packetFormationSet]
  refine EqOn.closure ?_ hT (uniformContinuous_pushForm A).continuous
  rintro _ ⟨m, α, hpos, hmass, rfl⟩
  rw [h α hpos hmass]
  funext z
  exact (pushAlgHom_formation A α z).symm

/-! ### Positive formations -/

theorem isPositive_pow {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) (n : ℕ) :
    IsPositive (Φ ^ n) := by
  induction n with
  | zero => simpa using isPositive_one
  | succ n ih => rw [pow_succ]; exact IsPositive.mul ih hΦ

theorem isPositive_prod {ι : Type*} (s : Finset ι) {Φ : ι → MeasureAlgebra K}
    (h : ∀ i ∈ s, IsPositive (Φ i)) : IsPositive (∏ i ∈ s, Φ i) :=
  Finset.prod_induction Φ IsPositive (fun _ _ ha hb => IsPositive.mul ha hb) isPositive_one h

theorem isPositive_exp {X : MeasureAlgebra K} (hX : IsPositive X) : IsPositive (exp X) := by
  have h := exp_series_hasSum_exp' (𝕂 := ℝ) X
  refine isPositive_of_tendsto (Φ := fun n => ∑ i ∈ Finset.range n,
    ((i.factorial : ℝ)⁻¹) • X ^ i) (fun n => isPositive_sum _ fun i _ => ?_)
    fun f => ((evalAt f).continuous.tendsto _).comp h.tendsto_sum_nat
  have := IsPositive.smul (isPositive_pow hX i) (c := (i.factorial : ℝ)⁻¹) (by positivity)
  rwa [Complex.coe_smul] at this

/-- Decorated formations are positive measures at real `t ≥ 0`. -/
theorem isPositive_decorated {γ : MeasureAlgebra K} {α : ℕ → MeasureAlgebra K}
    (hγ : IsPositive γ) (hα : ∀ j, IsPositive (α j)) (hs : Summable fun j => ‖α j‖) {t : ℝ}
    (ht : 0 ≤ t) : IsPositive (decorated γ α t) := by
  refine IsPositive.mul (isPositive_exp (IsPositive.smul hγ ht)) ?_
  refine isPositive_of_tendsto (fun n => isPositive_prod _ fun j _ =>
    isPositive_one.add (IsPositive.smul (hα j) ht)) fun f =>
      ((evalAt f).continuous.tendsto _).comp (multipliable_formation hs t).tendsto_prod_tprod_nat

/-! ### `f`-divergences -/

section Divergence

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The `f`-divergence `D_f(μ ‖ ν) = ∫ f(dμ/dν) dν + c μ_⊥(X)`, with `c = f'(∞)` the recession
slope of `f` and `μ_⊥` the part of `μ` singular to `ν`. -/
def fDivergence (f : ℝ → ℝ) (c : ℝ) (μ ν : Measure X) : ℝ :=
  ∫ x, f (μ.rnDeriv ν x).toReal ∂ν + c * (μ.singularPart ν univ).toReal

/-- `f`-divergences are invariant under pushforward along a measurable embedding. -/
theorem fDivergence_map {e : X → Y} (he : MeasurableEmbedding e) (f : ℝ → ℝ) (c : ℝ)
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    fDivergence f c (μ.map e) (ν.map e) = fDivergence f c μ ν := by
  unfold fDivergence
  rw [he.integral_map, he.singularPart_map μ ν, Measure.map_apply he.measurable MeasurableSet.univ,
    preimage_univ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [he.rnDeriv_map μ ν] with x hx
  rw [hx]

end Divergence

/-- The finite measure representing a positive element (Riesz–Markov–Kakutani). -/
def toFiniteMeasure {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) : FiniteMeasure K :=
  hΦ.exists_ofMeasure_eq.choose

omit [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] in
theorem ofMeasure_toFiniteMeasure {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    ofMeasure (toFiniteMeasure hΦ) = Φ :=
  hΦ.exists_ofMeasure_eq.choose_spec

omit [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K] in
theorem push_ofMeasure (A : C(K, K)) (μ : FiniteMeasure K) :
    push A (ofMeasure μ) = ofMeasure (μ.map A) := by
  ext f
  rw [push_apply, ofMeasure_apply, ofMeasure_apply, FiniteMeasure.toMeasure_map,
    integral_map A.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rfl

omit [CommMonoid K] [ContinuousMul K] in
theorem toFiniteMeasure_push (A : C(K, K)) {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    toFiniteMeasure (isPositive_push A hΦ) = (toFiniteMeasure hΦ).map A := by
  apply ofMeasure_injective
  rw [ofMeasure_toFiniteMeasure, ← push_ofMeasure, ofMeasure_toFiniteMeasure]

omit [ContinuousMul K] in
/-- **Theorem 8.1, information neutrality.**  Pushforward along a continuous monoid automorphism
preserves every `f`-divergence between positive measures, in particular between normalized
positive formations. -/
theorem fDivergence_push (A : K ≃ₜ* K) (f : ℝ → ℝ) (c : ℝ) {Φ Ψ : MeasureAlgebra K}
    (hΦ : IsPositive Φ) (hΨ : IsPositive Ψ) :
    fDivergence f c (toFiniteMeasure (isPositive_push (A : K →ₜ* K).toContinuousMap hΦ) :
        Measure K) (toFiniteMeasure (isPositive_push (A : K →ₜ* K).toContinuousMap hΨ)) =
      fDivergence f c (toFiniteMeasure hΦ : Measure K) (toFiniteMeasure hΨ) := by
  rw [toFiniteMeasure_push, toFiniteMeasure_push, FiniteMeasure.toMeasure_map,
    FiniteMeasure.toMeasure_map]
  exact fDivergence_map A.toHomeomorph.measurableEmbedding f c _ _

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Normalization commutes with the automorphism action. -/
theorem push_normalize (A : K ≃ₜ* K) (Φ : MeasureAlgebra K) :
    pushAlgHom (A : K →ₜ* K) ((‖Φ‖⁻¹ : ℂ) • Φ) =
      ((‖pushAlgHom (A : K →ₜ* K) Φ‖⁻¹ : ℂ) • pushAlgHom (A : K →ₜ* K) Φ) := by
  rw [map_smul, norm_push_aut]

end GaloisForLFunctions.HTGeometry.FormationDust
