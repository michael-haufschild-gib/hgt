import Mathlib
import GaloisForLFunctions.Core

/-!
# Initial-execution symmetry inheritance and anomaly necessity

An initial object inherits every categorical symmetry: for an autoequivalence `F` of `E` and an
initial `I`, the unique arrow `I ⟶ F I` is an isomorphism, it is the identity for `F = 𝟭`, and it
satisfies the strict cocycle law for composites.  Consequently the image of an initial execution
under any isomorphism-invariant, equivariant observation is a fixed point of the acting group, so
it cannot lie in a free nontrivial orbit.

Therefore an exactly symmetric source with an equivariant execution doctrine cannot canonically
produce a symmetry-breaking event.  The infinitesimal form of the same obstruction: a new
differential whose commutator with the grading operator vanishes still commutes with the whole
radial flow, so a nonzero commutator is necessary for radial selection.

That scalar condition is strictly weaker than its componentwise refinement.  The anomaly is linear
in the derivation slot, so the anomaly of a contracted derivation `∑ c i • D i` is the same
contraction of the component anomalies; consequently it can be nonzero while a component anomaly
vanishes, and — for the prime logarithms `log 2`, `log 3` — it can vanish while every component
anomaly is nonzero and the contracted derivation itself is nonzero.  Rational proportionality of
the component anomalies excludes that cancellation, because prime logarithms are linearly
independent over `ℚ`.
-/

namespace HTGeometry.ConstraintRelativity

open CategoryTheory CategoryTheory.Limits

/-! ## Initial objects inherit symmetry -/

section Initial

variable {E : Type*} [Category E]

/-- The canonical comparison arrow from an initial object to its translate. -/
noncomputable def initialCompare {I : E} (hI : IsInitial I) (F : E ⥤ E) : I ⟶ F.obj I :=
  hI.to (F.obj I)

/-- **Uniqueness.**  There is exactly one comparison arrow. -/
theorem initialCompare_unique {I : E} (hI : IsInitial I) (F : E ⥤ E) (f : I ⟶ F.obj I) :
    f = initialCompare hI F :=
  hI.hom_ext f _

/-- **The identity translate.**  `α_1 = id`. -/
theorem initialCompare_id {I : E} (hI : IsInitial I) :
    initialCompare hI (𝟭 E) = 𝟙 I :=
  hI.hom_ext _ _

/-- **The cocycle law.**  `α_{gh} = F_g(α_h) ∘ α_g` in the composition order of the translates. -/
theorem initialCompare_comp {I : E} (hI : IsInitial I) (F F' : E ⥤ E) :
    initialCompare hI (F ⋙ F') = initialCompare hI F' ≫ F'.map (initialCompare hI F) :=
  hI.hom_ext _ _

/-- An autoequivalence sends an initial object to an initial object. -/
noncomputable def isInitialMap {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    IsInitial (F.obj I) :=
  hI.isInitialObj F I

/-- **The comparison arrow is an isomorphism.** -/
theorem isIso_initialCompare {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    IsIso (initialCompare hI F) := by
  have h := isInitialMap hI F
  refine ⟨h.to I, ?_, ?_⟩
  · exact hI.hom_ext _ _
  · exact h.hom_ext _ _

/-- The initial object is isomorphic to each of its translates. -/
noncomputable def initialIsoMap {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    I ≅ F.obj I :=
  hI.uniqueUpToIso (isInitialMap hI F)

end Initial

/-! ## The image of an initial execution is a fixed point -/

section Equivariant

variable {E : Type*} [Category E] {X : Type*} {G : Type*} [Group G] [MulAction G X]

/-- **Equivariant initial execution lands in the fixed locus.**  If a group acts on `E` by
autoequivalences and an isomorphism-invariant observation `P` is equivariant, then the observation
of an initial object is fixed by the whole group. -/
theorem smul_obs_initial (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) (g : G) :
    g • P I = P I := by
  have h1 : P I = P ((F g).obj I) := hPiso (initialIsoMap hI (F g))
  rw [hPequiv g I] at h1
  exact h1.symm

/-- **No free nontrivial orbit contains the observation of an initial execution.** -/
theorem not_free_orbit_obs_initial (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) :
    ¬ ∃ g : G, g ≠ 1 ∧ g • P I ≠ P I := by
  rintro ⟨g, _, hne⟩
  exact hne (smul_obs_initial F hI P hPiso hPequiv g)

/-- The stabilizer of the observation of an initial execution is the whole group. -/
theorem stabilizer_obs_initial_eq_top (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) :
    MulAction.stabilizer G (P I) = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  exact smul_obs_initial F hI P hPiso hPequiv g

end Equivariant

/-! ## Infinitesimal anomaly necessity -/

section Anomaly

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A radial flow: a family of operators acting on each eigenspace of the grading operator `∂` by
a scalar. -/
structure RadialFlow (K M : Type*) [Field K] [AddCommGroup M] [Module K M] where
  /-- The grading operator. -/
  grading : M →ₗ[K] M
  /-- The flow. -/
  flow : K → (M →ₗ[K] M)
  /-- The flow acts on each eigenspace of the grading by a scalar. -/
  weight : K → K → K
  /-- The scalar action on eigenvectors. -/
  flow_eigen : ∀ (c lam : K) (v : M), grading v = lam • v → flow c v = weight c lam • v
  /-- The eigenvectors span. -/
  span_eigen : ∀ v : M, ∃ (n : ℕ) (lam : Fin n → K) (w : Fin n → M),
    (∀ i, grading (w i) = lam i • w i) ∧ v = ∑ i, w i

/-- **Anomaly necessity.**  A new differential whose commutator with the grading operator vanishes
still commutes with the whole radial flow.  Hence a nonzero commutator `[d, ∂] ≠ 0` is a necessary
condition for a radially selecting execution. -/
theorem commute_flow_of_commute_grading (Γ : RadialFlow K M) (d : M →ₗ[K] M)
    (hcomm : d.comp Γ.grading = Γ.grading.comp d) (c : K) :
    d.comp (Γ.flow c) = (Γ.flow c).comp d := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨n, lam, w, hw, rfl⟩ := Γ.span_eigen v
  simp only [LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdw : Γ.grading (d (w i)) = lam i • d (w i) := by
    have h1 := congrArg (fun f => f (w i)) hcomm
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hw i, map_smul]
  rw [Γ.flow_eigen c (lam i) (w i) (hw i), Γ.flow_eigen c (lam i) (d (w i)) hdw, map_smul]

/-- The contrapositive: a radial flow that fails to commute with a new differential forces a
nonzero commutator with the grading operator. -/
theorem grading_commutator_ne_zero (Γ : RadialFlow K M) (d : M →ₗ[K] M) (c : K)
    (h : d.comp (Γ.flow c) ≠ (Γ.flow c).comp d) :
    d.comp Γ.grading ≠ Γ.grading.comp d :=
  fun hcomm => h (commute_flow_of_commute_grading Γ d hcomm c)

/-! ### The prime-component refinement of the anomaly

The anomaly of a differential against a single derivation is its commutator.  A logarithmic
derivation is a linear combination `∑ c i • D i` of component derivations, and the anomaly is
linear in that slot, so the anomaly of the contraction is the same combination of the component
anomalies.  The contraction therefore sees strictly less than the component family: it can be
nonzero while some component anomaly vanishes, and it can vanish while every component anomaly is
nonzero. -/

/-- The commutator `[d, D]` of a differential with a derivation. -/
def anomalyBracket (d D : M →ₗ[K] M) : M →ₗ[K] M := d.comp D - D.comp d

theorem anomalyBracket_eq_zero_iff (d D : M →ₗ[K] M) :
    anomalyBracket d D = 0 ↔ d.comp D = D.comp d := sub_eq_zero

/-- The identity is central: it contributes no anomaly. -/
theorem anomalyBracket_id (d : M →ₗ[K] M) : anomalyBracket d (LinearMap.id) = 0 := by
  simp [anomalyBracket]

theorem anomalyBracket_add (d D E : M →ₗ[K] M) :
    anomalyBracket d (D + E) = anomalyBracket d D + anomalyBracket d E := by
  ext v
  simp only [anomalyBracket, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
    map_add]
  abel

theorem anomalyBracket_smul (c : K) (d D : M →ₗ[K] M) :
    anomalyBracket d (c • D) = c • anomalyBracket d D := by
  ext v
  simp only [anomalyBracket, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_sub]

/-- **The contraction law.**  The anomaly of a contracted derivation is the same contraction of the
component anomalies: `[d, ∑ c i • D i] = ∑ c i • [d, D i]`. -/
theorem anomalyBracket_sum_smul {n : ℕ} (d : M →ₗ[K] M) (c : Fin n → K)
    (D : Fin n → M →ₗ[K] M) :
    anomalyBracket d (∑ i, c i • D i) = ∑ i, c i • anomalyBracket d (D i) := by
  ext v
  simp [anomalyBracket, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, smul_sub,
    Finset.sum_sub_distrib]

/-- A nonzero contracted anomaly forces at least one nonzero component anomaly. -/
theorem exists_anomalyBracket_ne_zero_of_contraction_ne_zero {n : ℕ} (d : M →ₗ[K] M)
    (c : Fin n → K) (D : Fin n → M →ₗ[K] M)
    (h : anomalyBracket d (∑ i, c i • D i) ≠ 0) :
    ∃ i, anomalyBracket d (D i) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [anomalyBracket_sum_smul]
  exact Finset.sum_eq_zero fun i _ => by rw [hcon i, smul_zero]

/-- The bracket form of anomaly necessity: a differential that fails to commute with the radial
flow has a nonzero commutator with the grading operator. -/
theorem anomalyBracket_grading_ne_zero_of_not_commute_flow (Γ : RadialFlow K M) (d : M →ₗ[K] M)
    (c : K) (h : d.comp (Γ.flow c) ≠ (Γ.flow c).comp d) :
    anomalyBracket d Γ.grading ≠ 0 :=
  fun hz => grading_commutator_ne_zero Γ d c h ((anomalyBracket_eq_zero_iff d Γ.grading).1 hz)

/-! ### Radial flows exist, and the anomaly condition is satisfiable -/

section AnomalyWitness

variable {K : Type*} [Field K]

/-- The diagonal grading operator with weights `μ`. -/
def diagonalGrading {n : ℕ} (μ : Fin n → K) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v := fun i => μ i * v i
  map_add' _ _ := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    show μ i * (c * v i) = c * (μ i * v i)
    ring

@[simp] theorem diagonalGrading_apply {n : ℕ} (μ : Fin n → K) (v : Fin n → K) (i : Fin n) :
    diagonalGrading μ v i = μ i * v i := rfl

/-- **Radial flows exist.**  Any weight family `μ` and any weight law `g` give a radial flow on the
graded space `Kⁿ`: the grading is diagonal with eigenvalues `μ`, and the flow is diagonal with
entries `g c (μ i)`.  The anomaly theorems above are therefore not vacuous. -/
def diagonalRadialFlow {n : ℕ} (μ : Fin n → K) (g : K → K → K) :
    RadialFlow K (Fin n → K) where
  grading := diagonalGrading μ
  flow c := diagonalGrading fun i => g c (μ i)
  weight := g
  flow_eigen c lam v hv := by
    funext i
    have hi : μ i * v i = lam * v i := congrFun hv i
    show g c (μ i) * v i = g c lam * v i
    rcases eq_or_ne (v i) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · rw [mul_right_cancel₀ h0 hi]
  span_eigen v := by
    classical
    refine ⟨n, μ, fun i => Pi.single i (v i), fun i => ?_, ?_⟩
    · funext j
      simp only [diagonalGrading_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne j i with rfl | hji
      · rfl
      · rw [Pi.single_eq_of_ne hji, mul_zero, mul_zero]
    · exact (Finset.univ_sum_single v).symm

/-- The two-dimensional graded model with weights `0` and `1`, whose flow is the grading itself. -/
def anomalyFlow : RadialFlow K (Fin 2 → K) :=
  diagonalRadialFlow ![0, 1] fun _ lam => lam

/-- The lowering operator `d(v₀, v₁) = (v₁, 0)`. -/
def anomalyDifferential : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, 0]
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp

/-- **The anomaly condition is satisfiable.**  On the two-dimensional graded model the lowering
operator fails to commute with the radial flow, so the hypothesis of `grading_commutator_ne_zero`
is met and its conclusion is a genuine obstruction, not a vacuous one. -/
theorem anomalyDifferential_not_commute_flow (c : K) :
    (anomalyDifferential (K := K)).comp ((anomalyFlow (K := K)).flow c)
      ≠ ((anomalyFlow (K := K)).flow c).comp anomalyDifferential := by
  intro h
  have h1 := congrArg (fun f => f ![0, 1]) h
  have h2 : (1 : K) = 0 := by
    have h3 := congrFun h1 0
    simp [anomalyDifferential, anomalyFlow, diagonalRadialFlow, diagonalGrading] at h3
  exact one_ne_zero h2

/-- Consequently the commutator with the grading operator is nonzero on that model. -/
theorem anomalyDifferential_grading_commutator_ne_zero :
    (anomalyDifferential (K := K)).comp (anomalyFlow (K := K)).grading
      ≠ (anomalyFlow (K := K)).grading.comp anomalyDifferential :=
  grading_commutator_ne_zero _ _ 0 (anomalyDifferential_not_commute_flow 0)

/-! ### The contraction sees strictly less than the component family -/

theorem anomalyBracket_anomalyDifferential_grading_ne_zero :
    anomalyBracket (anomalyDifferential (K := K)) (anomalyFlow (K := K)).grading ≠ 0 :=
  fun hz => anomalyDifferential_grading_commutator_ne_zero
    ((anomalyBracket_eq_zero_iff _ _).1 hz)

/-- A two-component family whose second component is the central operator `1`. -/
def partialComponents : Fin 2 → ((Fin 2 → K) →ₗ[K] (Fin 2 → K)) :=
  ![(anomalyFlow (K := K)).grading, LinearMap.id]

/-- The second component carries no anomaly. -/
theorem partialComponents_bracket_one_eq_zero :
    anomalyBracket (anomalyDifferential (K := K)) (partialComponents (K := K) 1) = 0 := by
  simp [partialComponents, anomalyBracket_id]

/-- **A nonzero contracted anomaly does not make every component anomaly nonzero.**  For every
coefficient family with a nonzero first entry the contracted anomaly of `partialComponents` is
nonzero, while its second component anomaly vanishes. -/
theorem partialComponents_contraction_ne_zero (c : Fin 2 → K) (hc : c 0 ≠ 0) :
    anomalyBracket (anomalyDifferential (K := K)) (∑ i, c i • partialComponents (K := K) i)
      ≠ 0 := by
  rw [anomalyBracket_sum_smul, Fin.sum_univ_two]
  simp only [partialComponents, Matrix.cons_val_zero, Matrix.cons_val_one, anomalyBracket_id,
    smul_zero, add_zero]
  exact smul_ne_zero hc anomalyBracket_anomalyDifferential_grading_ne_zero

end AnomalyWitness

/-! ### Logarithmic contraction against prime logarithms

The logarithmic derivation is the contraction `∂_log = ∑_ℓ (log ℓ) ∂_ℓ` of the component
derivations against prime logarithms.  Its anomaly can vanish although every component anomaly is
nonzero, so the scalar condition `[d, ∂_log] ≠ 0` is strictly weaker than the componentwise
refinement `[d, ∂_ℓ] ≠ 0`.  Rational proportionality of the component anomalies is exactly what
rules the cancellation out: prime logarithms are linearly independent over `ℚ`. -/

section PrimeContraction

theorem anomaly_log_two_ne_zero : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'

theorem anomaly_log_three_ne_zero : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'

/-- The prime-logarithm coefficients of the logarithmic contraction at the primes `2` and `3`. -/
noncomputable def logContractionCoeff : Fin 2 → ℝ := ![Real.log 2, Real.log 3]

/-- Two component derivations whose anomalies cancel against the prime logarithms while their
contraction is still a nonzero derivation. -/
noncomputable def entangledComponents : Fin 2 → ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :=
  ![Real.log 3 • (anomalyFlow (K := ℝ)).grading + LinearMap.id,
    (-Real.log 2) • (anomalyFlow (K := ℝ)).grading]

/-- Every component anomaly is nonzero. -/
theorem entangledComponents_bracket_ne_zero (i : Fin 2) :
    anomalyBracket (anomalyDifferential (K := ℝ)) (entangledComponents i) ≠ 0 := by
  fin_cases i
  · show anomalyBracket _ (Real.log 3 • _ + LinearMap.id) ≠ 0
    rw [anomalyBracket_add, anomalyBracket_smul, anomalyBracket_id, add_zero]
    exact smul_ne_zero anomaly_log_three_ne_zero
      anomalyBracket_anomalyDifferential_grading_ne_zero
  · show anomalyBracket _ ((-Real.log 2) • _) ≠ 0
    rw [anomalyBracket_smul]
    exact smul_ne_zero (neg_ne_zero.2 anomaly_log_two_ne_zero)
      anomalyBracket_anomalyDifferential_grading_ne_zero

/-- The contraction collapses to a multiple of the central operator. -/
theorem entangledComponents_contraction_eq :
    ∑ i, logContractionCoeff i • entangledComponents i
      = Real.log 2 • (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) := by
  simp only [Fin.sum_univ_two, logContractionCoeff, entangledComponents, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  module

/-- The contracted derivation is itself nonzero, so the vanishing below is not degenerate. -/
theorem entangledComponents_contraction_ne_zero :
    ∑ i, logContractionCoeff i • entangledComponents i ≠ 0 := by
  rw [entangledComponents_contraction_eq]
  intro h
  have h0 := congrFun (congrArg (fun f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => f ![1, 0]) h) 0
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, Pi.zero_apply, Matrix.cons_val_zero, mul_one] at h0
  exact anomaly_log_two_ne_zero h0

/-- **The logarithmic contraction is not faithful.**  Every component anomaly is nonzero and the
contracted derivation is nonzero, yet the anomaly of the contraction vanishes.  A nonzero
commutator that appears only after logarithmic contraction therefore carries strictly less
information than the componentwise refinement. -/
theorem entangledComponents_anomaly_contraction_eq_zero :
    anomalyBracket (anomalyDifferential (K := ℝ))
      (∑ i, logContractionCoeff i • entangledComponents i) = 0 := by
  rw [entangledComponents_contraction_eq, anomalyBracket_smul, anomalyBracket_id, smul_zero]

/-- A nontrivial rational combination of prime logarithms is nonzero. -/
theorem sum_log_primes_mul_rat_ne_zero {n : ℕ} (ps : Fin n → Nat.Primes)
    (hps : Function.Injective ps) (q : Fin n → ℚ) (hq : q ≠ 0) :
    ∑ i, Real.log ((ps i : ℕ) : ℝ) * (q i : ℝ) ≠ 0 := by
  intro h
  have hli : LinearIndependent ℚ (fun i : Fin n => Real.log (((ps i : ℕ) : ℝ))) :=
    GaloisForLFunctions.linearIndependent_log_primes.comp ps hps
  have h0 : ∑ i, q i • Real.log (((ps i : ℕ) : ℝ)) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [Rat.smul_def, mul_comm]
  exact hq (funext fun i => Fintype.linearIndependent_iff.mp hli q h0 i)

/-- **Rational proportionality rules out the cancellation.**  If the component anomalies are
rational multiples of one nonzero operator, with not all multipliers zero, then the anomaly of the
logarithmic contraction against distinct prime logarithms is nonzero. -/
theorem contraction_ne_zero_of_rational_components {M : Type*} [AddCommGroup M] [Module ℝ M]
    {n : ℕ} (ps : Fin n → Nat.Primes) (hps : Function.Injective ps)
    (d : M →ₗ[ℝ] M) (D : Fin n → M →ₗ[ℝ] M) (A : M →ₗ[ℝ] M) (hA : A ≠ 0)
    (q : Fin n → ℚ) (hq : q ≠ 0)
    (hcomp : ∀ i, anomalyBracket d (D i) = (q i : ℝ) • A) :
    anomalyBracket d (∑ i, Real.log ((ps i : ℕ) : ℝ) • D i) ≠ 0 := by
  rw [anomalyBracket_sum_smul]
  have hsum : ∑ i, Real.log ((ps i : ℕ) : ℝ) • anomalyBracket d (D i)
      = (∑ i, Real.log ((ps i : ℕ) : ℝ) * (q i : ℝ)) • A := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [hcomp i, smul_smul]
  rw [hsum]
  exact smul_ne_zero (sum_log_primes_mul_rat_ne_zero ps hps q hq) hA

/-- The rationally proportional situation occurs: on the two-dimensional graded model the rational
multiples of the grading operator have that shape, and their logarithmic contraction has a nonzero
anomaly for every nontrivial rational multiplier family. -/
theorem rationalComponents_contraction_ne_zero {n : ℕ} (ps : Fin n → Nat.Primes)
    (hps : Function.Injective ps) (q : Fin n → ℚ) (hq : q ≠ 0) :
    anomalyBracket (anomalyDifferential (K := ℝ))
      (∑ i, Real.log ((ps i : ℕ) : ℝ) • ((q i : ℝ) • (anomalyFlow (K := ℝ)).grading)) ≠ 0 :=
  contraction_ne_zero_of_rational_components ps hps _ _
    (anomalyBracket (anomalyDifferential (K := ℝ)) (anomalyFlow (K := ℝ)).grading)
    anomalyBracket_anomalyDifferential_grading_ne_zero q hq
    (fun _ => anomalyBracket_smul _ _ _)

end PrimeContraction

end Anomaly

end HTGeometry.ConstraintRelativity
