import Mathlib

/-!
# Passive fibre size, hidden dimension, and the minimal experiment budget

A passive observer and a family of experiments jointly reconstruct a state only if the experiments
can separate every passive fibre.  Counting gives an exact lower bound on the number of experiments
in the finite case, and rank–nullity gives the sharp linear statement: the minimal number of scalar
response experiments needed for exact reconstruction is exactly the dimension of the hidden space
`ker q₀`, with both sides allowed to be infinite.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Theorem 1 — finite information -/

section FiniteInformation

variable {X : Type*} {Y₀ : Type*} {ι : Type*} [Fintype ι]
  {Y : ι → Type*} [∀ i, Finite (Y i)]

/-- The joint response of a passive observer and a family of experiments, equation (1). -/
def jointResponse (q₀ : X → Y₀) (q : ∀ i, X → Y i) (x : X) : Y₀ × (∀ i, Y i) :=
  (q₀ x, fun i => q i x)

omit [Fintype ι] [∀ (i : ι), Finite (Y i)] in
/-- On a passive fibre, the experiments alone already separate states. -/
theorem experiments_injective_on_fibre (q₀ : X → Y₀) (q : ∀ i, X → Y i)
    (hQ : Function.Injective (jointResponse q₀ q)) (y : Y₀) :
    Function.Injective (fun z : {x : X // q₀ x = y} => fun i => q i (z : X)) := by
  intro a b hab
  apply Subtype.ext
  apply hQ
  refine Prod.ext ?_ hab
  show q₀ (a : X) = q₀ (b : X)
  rw [a.2, b.2]

/-- **Theorem 1, equation (2).**  Every passive fibre is bounded by the total experimental
capacity. -/
theorem card_passiveFibre_le (q₀ : X → Y₀) (q : ∀ i, X → Y i)
    (hQ : Function.Injective (jointResponse q₀ q)) (y : Y₀) :
    Nat.card {x : X // q₀ x = y} ≤ ∏ i, Nat.card (Y i) := by
  classical
  have h1 : Nat.card {x : X // q₀ x = y} ≤ Nat.card (∀ i, Y i) :=
    Nat.card_le_card_of_injective _ (experiments_injective_on_fibre q₀ q hQ y)
  rwa [Nat.card_pi] at h1

/-- **Theorem 1, equation (3), power form.**  If every experiment has capacity at most `k`, the
passive fibre is bounded by `k^r`. -/
theorem card_passiveFibre_le_pow (q₀ : X → Y₀) (q : ∀ i, X → Y i)
    (hQ : Function.Injective (jointResponse q₀ q)) {k : ℕ}
    (hk : ∀ i, Nat.card (Y i) ≤ k) (y : Y₀) :
    Nat.card {x : X // q₀ x = y} ≤ k ^ Fintype.card ι := by
  refine (card_passiveFibre_le q₀ q hQ y).trans ?_
  calc ∏ i, Nat.card (Y i) ≤ ∏ _i : ι, k := Finset.prod_le_prod' fun i _ => hk i
    _ = k ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

/-- **Theorem 1, equation (3), logarithmic form.**  The number of experiments is at least
`log_k` of the largest passive fibre. -/
theorem log_card_passiveFibre_le (q₀ : X → Y₀) (q : ∀ i, X → Y i)
    (hQ : Function.Injective (jointResponse q₀ q)) {k : ℕ} (hk1 : 1 < k)
    (hk : ∀ i, Nat.card (Y i) ≤ k) (y : Y₀) :
    Nat.log k (Nat.card {x : X // q₀ x = y}) ≤ Fintype.card ι := by
  have h := card_passiveFibre_le_pow q₀ q hQ hk y
  calc Nat.log k (Nat.card {x : X // q₀ x = y}) ≤ Nat.log k (k ^ Fintype.card ι) :=
        Nat.log_mono_right h
    _ = Fintype.card ι := Nat.log_pow hk1 _

end FiniteInformation

/-! ## Theorem 2 — linear hidden dimension -/

section LinearHiddenDimension

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ι : Type*}

/-- The joint linear observer of equation (4). -/
def linearJointObserver (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K) : V →ₗ[K] W × (ι → K) :=
  q₀.prod (LinearMap.pi ℓ)

theorem ker_linearJointObserver (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K) :
    LinearMap.ker (linearJointObserver q₀ ℓ)
      = LinearMap.ker q₀ ⊓ ⨅ i, LinearMap.ker (ℓ i) := by
  rw [linearJointObserver, LinearMap.ker_prod, LinearMap.ker_pi]

/-- **Theorem 2, equation (5).**  The joint observer is injective exactly when the experiments
separate the hidden space. -/
theorem linearJointObserver_injective_iff (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K) :
    Function.Injective (linearJointObserver q₀ ℓ)
      ↔ LinearMap.ker q₀ ⊓ ⨅ i, LinearMap.ker (ℓ i) = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_linearJointObserver]

/-- The experiments restricted to the hidden space. -/
def hiddenRestriction (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K) :
    (LinearMap.ker q₀) →ₗ[K] (ι → K) :=
  (LinearMap.pi ℓ).comp (LinearMap.ker q₀).subtype

theorem hiddenRestriction_injective (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K)
    (h : Function.Injective (linearJointObserver q₀ ℓ)) :
    Function.Injective (hiddenRestriction q₀ ℓ) := by
  intro a b hab
  apply Subtype.ext
  apply h
  refine Prod.ext ?_ hab
  show q₀ (a : V) = q₀ (b : V)
  rw [LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]

/-- **Theorem 2, lower bound.**  Exact reconstruction needs at least `dim ker q₀` scalar
experiments. -/
theorem finrank_ker_le_card [Fintype ι] (q₀ : V →ₗ[K] W) (ℓ : ι → V →ₗ[K] K)
    (h : Function.Injective (linearJointObserver q₀ ℓ)) :
    Module.finrank K (LinearMap.ker q₀) ≤ Fintype.card ι := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (hiddenRestriction_injective q₀ ℓ h)
  rwa [Module.finrank_pi] at h1

/-- **Theorem 2, sufficiency.**  Exactly `dim ker q₀` scalar experiments suffice: extend a
coordinate system of the hidden space to the whole space. -/
theorem exists_experiments (q₀ : V →ₗ[K] W) [FiniteDimensional K (LinearMap.ker q₀)] :
    ∃ ℓ : Fin (Module.finrank K (LinearMap.ker q₀)) → V →ₗ[K] K,
      Function.Injective (linearJointObserver q₀ ℓ) := by
  classical
  set b := Module.finBasis K (LinearMap.ker q₀) with hb
  have hext : ∀ i, ∃ g : V →ₗ[K] K, g ∘ₗ (LinearMap.ker q₀).subtype = b.coord i :=
    fun i => LinearMap.exists_extend (b.coord i)
  choose ℓ hℓ using hext
  refine ⟨ℓ, ?_⟩
  rw [linearJointObserver_injective_iff, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hx0, hxi⟩ := hx
  have hzero : (⟨x, hx0⟩ : LinearMap.ker q₀) = 0 := by
    refine b.forall_coord_eq_zero_iff.mp ?_
    intro i
    have h1 : (b.coord i) (⟨x, hx0⟩ : LinearMap.ker q₀) = ℓ i x := by
      rw [← hℓ i]
      rfl
    rw [h1]
    have := Submodule.mem_iInf _ |>.mp hxi i
    exact LinearMap.mem_ker.mp this
  simpa using congrArg (fun z : LinearMap.ker q₀ => (z : V)) hzero

end LinearHiddenDimension

/-! ## Theorem 3 — the experimental dimension -/

section ExperimentalDimension

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A budget of `r` scalar experiments suffices for exact reconstruction. -/
def IsExperimentBudget (q₀ : V →ₗ[K] W) (r : ℕ) : Prop :=
  ∃ ℓ : Fin r → V →ₗ[K] K, Function.Injective (linearJointObserver q₀ ℓ)

/-- The scalar experimental dimension of a linear passive observer. -/
noncomputable def edim (q₀ : V →ₗ[K] W) : ℕ := sInf {r | IsExperimentBudget q₀ r}

/-- **Equation (6), finite case.**  The experimental dimension is the hidden dimension. -/
theorem edim_eq_finrank_ker (q₀ : V →ₗ[K] W) [FiniteDimensional K (LinearMap.ker q₀)] :
    edim q₀ = Module.finrank K (LinearMap.ker q₀) := by
  obtain ⟨ℓ, hℓ⟩ := exists_experiments q₀
  have hmem : Module.finrank K (LinearMap.ker q₀) ∈ {r | IsExperimentBudget q₀ r} := ⟨ℓ, hℓ⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨ℓ', hℓ'⟩ := Nat.sInf_mem ⟨_, hmem⟩
  have h := finrank_ker_le_card q₀ ℓ' hℓ'
  rwa [Fintype.card_fin] at h

/-- **Equation (6), infinite case.**  If the hidden space is infinite-dimensional, no finite family
of scalar experiments reconstructs the state. -/
theorem not_isExperimentBudget_of_infinite (q₀ : V →ₗ[K] W)
    (h : ¬ FiniteDimensional K (LinearMap.ker q₀)) (r : ℕ) : ¬ IsExperimentBudget q₀ r := by
  rintro ⟨ℓ, hℓ⟩
  exact h (Module.Finite.of_injective _ (hiddenRestriction_injective q₀ ℓ hℓ))

/-- The experiment-budget set is empty exactly when the hidden space is infinite-dimensional. -/
theorem isExperimentBudget_nonempty_iff (q₀ : V →ₗ[K] W) :
    {r | IsExperimentBudget q₀ r}.Nonempty ↔ FiniteDimensional K (LinearMap.ker q₀) := by
  constructor
  · rintro ⟨r, ℓ, hℓ⟩
    exact Module.Finite.of_injective _ (hiddenRestriction_injective q₀ ℓ hℓ)
  · intro hfin
    obtain ⟨ℓ, hℓ⟩ := exists_experiments q₀
    exact ⟨_, ℓ, hℓ⟩

/-- **The law.**  The passive observer forces a minimum experiment budget equal to its hidden
dimension, and forces an infinite one when the hidden space is infinite-dimensional. -/
theorem passive_fibre_forces_experiment_budget (q₀ : V →ₗ[K] W) :
    (∀ (ι : Type) (_ : Fintype ι) (ℓ : ι → V →ₗ[K] K),
        Function.Injective (linearJointObserver q₀ ℓ) →
        Module.finrank K (LinearMap.ker q₀) ≤ Fintype.card ι) ∧
      (FiniteDimensional K (LinearMap.ker q₀) →
        edim q₀ = Module.finrank K (LinearMap.ker q₀)) ∧
      (¬ FiniteDimensional K (LinearMap.ker q₀) → ∀ r : ℕ, ¬ IsExperimentBudget q₀ r) := by
  refine ⟨fun ι _ ℓ h => finrank_ker_le_card q₀ ℓ h, fun hfin => ?_,
    not_isExperimentBudget_of_infinite q₀⟩
  exact edim_eq_finrank_ker q₀

end ExperimentalDimension

end GaloisForLFunctions.HTGeometry
