import GaloisForLFunctions.HTGeometry.ResetPathSingularity

/-!
# Executing the reset process: finite observer order forces infinite source order

The finite-dimensional laws of a Markov chain with kernel `L` and initial law `ν` are built step by
step: `P_{k+1} = (P_k ⊗ L(last)) ∘ snoc`.  For the reset lift `L((x, n)) = δ_{Rx} ⊗ κ_{Rx}` started
from the formed packet `δ_x ⊗ κ_x`, the law over times `0, …, k` is the independent product
`∏_j δ_{R^j x} ⊗ κ_{R^j x}`: every step discards the old recovery coordinate.

* **Theorem 4.1, `(RFDM.12)`–`(RFDM.15)`**: a measurable bijection `T` of a source space with a
  packet factor `Π` executing the reset process and `T^N = I`, `N > 0`, forces `R^N x = x` and
  `κ_x` to be Dirac: the time-`(0, N)` pair is `κ_x ⊗ κ_x` by execution and diagonal by
  periodicity.
* **Corollary 4.2, `(RFDM.16)`**: for an involution `R` the formed law closes after two steps, yet
  every execution of a reset process with a non-Dirac recovery law has infinite order.
-/

open MeasureTheory InformationTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResetDilation

/-! ### Finite-dimensional laws of a Markov chain -/

section MarkovPath

variable {α : Type*} [MeasurableSpace α]

/-- Appending a coordinate: `(w, a) ↦ (w_0, …, w_k, a)`. -/
def snocPair (k : ℕ) (p : (Fin (k + 1) → α) × α) : Fin (k + 2) → α :=
  Fin.snoc (α := fun _ => α) p.1 p.2

theorem measurable_snocPair (k : ℕ) : Measurable (snocPair (α := α) k) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [snocPair, Fin.snoc_last]; exact measurable_snd
  · simp only [snocPair, Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst

/-- **`(RFDM.13)`** the law over times `0, …, k` of the Markov chain with initial law `ν` and
kernel `L`. -/
def markovPath (ν : Measure α) (L : Kernel α α) : (k : ℕ) → Measure (Fin (k + 1) → α)
  | 0 => ν.map fun a _ => a
  | k + 1 => ((markovPath ν L k) ⊗ₘ
      (L.comap (fun w : Fin (k + 1) → α => w (Fin.last k)) (measurable_pi_apply _))).map
        (snocPair k)

/-- A box of a product measure over `Fin (k + 2)` splits into the first `k + 1` factors and the
last one. -/
theorem pi_prod_map_snocPair {k : ℕ} (μ : Fin (k + 2) → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.pi fun j : Fin (k + 1) => μ j.castSucc).prod (μ (Fin.last (k + 1)))).map
        (snocPair k) = Measure.pi μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_snocPair k) (MeasurableSet.univ_pi hs)]
  have hpre : snocPair k ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun j : Fin (k + 1) => s j.castSucc) ×ˢ s (Fin.last (k + 1)) := by
    ext ⟨w, a⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, snocPair]
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_castSucc (fun i => μ i (s i))]

/-- The path kernel: started at a point `a`, the law over times `0, …, k` of the Markov chain
with kernel `L`. -/
def markovPathKernel (L : Kernel α α) : (k : ℕ) → Kernel α (Fin (k + 1) → α)
  | 0 => Kernel.deterministic (fun a _ => a) (measurable_pi_lambda _ fun _ => measurable_id)
  | k + 1 => ((Kernel.id ×ₖ
      (L.comap (fun w : Fin (k + 1) → α => w (Fin.last k)) (measurable_pi_apply _))) ∘ₖ
        markovPathKernel L k).map (snocPair k)

theorem isProbabilityMeasure_markovPath (ν : Measure α) [IsProbabilityMeasure ν]
    (L : Kernel α α) [IsMarkovKernel L] (k : ℕ) : IsProbabilityMeasure (markovPath ν L k) := by
  induction k with
  | zero =>
    rw [markovPath]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_lambda _ fun _ => measurable_id).aemeasurable
  | succ k ih =>
    rw [markovPath]
    exact Measure.isProbabilityMeasure_map (measurable_snocPair k).aemeasurable

/-- **Markov property in the initial law**: the path law from `ν` is the `ν`-mixture of the path
laws from points. -/
theorem markovPath_eq_comp (ν : Measure α) [IsProbabilityMeasure ν] (L : Kernel α α)
    [IsMarkovKernel L] (k : ℕ) : markovPath ν L k = markovPathKernel L k ∘ₘ ν := by
  induction k with
  | zero => rw [markovPath, markovPathKernel, Measure.deterministic_comp_eq_map]
  | succ k ih =>
    haveI := isProbabilityMeasure_markovPath ν L k
    rw [markovPath, markovPathKernel, Measure.compProd_eq_comp_prod, ih, Measure.comp_assoc,
      Measure.map_comp _ _ (measurable_snocPair k)]

theorem markovPathKernel_apply (L : Kernel α α) [IsMarkovKernel L] (k : ℕ) (a : α) :
    markovPathKernel L k a = markovPath (Measure.dirac a) L k := by
  rw [markovPath_eq_comp, Measure.dirac_bind (Kernel.measurable _)]

end MarkovPath

/-! ### The reset chain from a Dirac observer -/

section ResetChain

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (κ : Kernel X ℕ)
  [IsMarkovKernel κ] (R : X → X) (hR : Measurable R)

instance : IsMarkovKernel (formationLiftKernel κ R hR) := by
  unfold formationLiftKernel; infer_instance

omit [MeasurableSingletonClass X] in
theorem formationLiftKernel_apply (z : X × ℕ) :
    formationLiftKernel κ R hR z = (Measure.dirac (R z.1)).prod (κ (R z.1)) := by
  simp only [formationLiftKernel, Kernel.comp_apply, Kernel.deterministic_apply,
    Measure.dirac_bind (Kernel.measurable _), Kernel.prod_apply, Kernel.id_apply]

theorem splitFormation_dirac (x : X) :
    splitFormation (Measure.dirac x) κ = (Measure.dirac x).prod (κ x) := by
  ext s hs
  rw [splitFormation, Measure.compProd_apply hs, lintegral_dirac, Measure.prod_apply hs,
    lintegral_dirac]

/-- The time-`j` marginal `δ_{R^j x} ⊗ κ_{R^j x}` of the reset chain started at `x`. -/
def resetMarginal (x : X) (j : ℕ) : Measure (X × ℕ) :=
  (Measure.dirac (R^[j] x)).prod (κ (R^[j] x))

instance (x : X) (j : ℕ) : IsProbabilityMeasure (resetMarginal κ R x j) := by
  unfold resetMarginal; infer_instance

theorem resetMarginal_fst_ae (x : X) (j : ℕ) :
    ∀ᵐ z ∂resetMarginal κ R x j, z.1 = R^[j] x := by
  rw [ae_iff]
  have : {z : X × ℕ | ¬ z.1 = R^[j] x} = ({R^[j] x}ᶜ : Set X) ×ˢ Set.univ := by
    ext z; simp
  rw [this, resetMarginal, Measure.prod_prod, Measure.dirac_apply' _
    (MeasurableSet.singleton _).compl, Set.indicator_of_notMem (by simp), zero_mul]

/-- **The reset chain is a product**: started from the formed packet `δ_x ⊗ κ_x`, the law over
times `0, …, k` is `∏_j δ_{R^j x} ⊗ κ_{R^j x}`. -/
theorem markovPath_reset (x : X) (k : ℕ) :
    markovPath (splitFormation (Measure.dirac x) κ) (formationLiftKernel κ R hR) k =
      Measure.pi fun j : Fin (k + 1) => resetMarginal κ R x j := by
  induction k with
  | zero =>
    rw [markovPath, splitFormation_dirac]
    have h := (measurePreserving_funUnique (resetMarginal κ R x 0) (Fin 1)).symm
    have hfun : (fun j : Fin 1 => resetMarginal κ R x (j : ℕ)) = fun _ => resetMarginal κ R x 0 :=
      funext fun j => by rw [Fin.fin_one_eq_zero j]; rfl
    rw [hfun]
    exact Eq.trans rfl h.map_eq
  | succ k ih =>
    rw [markovPath, ih]
    have hae : (formationLiftKernel κ R hR).comap
        (fun w : Fin (k + 1) → X × ℕ => w (Fin.last k)) (measurable_pi_apply _) =ᵐ[
          Measure.pi fun j : Fin (k + 1) => resetMarginal κ R x j]
        Kernel.const _ (resetMarginal κ R x (k + 1)) := by
      have hlast := (measurePreserving_eval
        (fun j : Fin (k + 1) => resetMarginal κ R x j) (Fin.last k)).quasiMeasurePreserving.ae
          (resetMarginal_fst_ae κ R x k)
      filter_upwards [hlast] with w hw
      rw [Kernel.comap_apply, formationLiftKernel_apply, Kernel.const_apply, resetMarginal]
      simp only [Function.eval] at hw
      rw [hw, ← Function.iterate_succ_apply' R k x]
    rw [Measure.compProd_congr hae, Measure.compProd_const]
    have h := pi_prod_map_snocPair (fun j : Fin (k + 2) => resetMarginal κ R x j)
    simp only [Fin.val_castSucc, Fin.val_last] at h
    exact h

/-- The reset path kernel `x ↦ (law over times 0, …, k started from δ_x ⊗ κ_x)`. -/
def resetPathKernel (k : ℕ) : Kernel X (Fin (k + 1) → X × ℕ) :=
  markovPathKernel (formationLiftKernel κ R hR) k ∘ₖ (Kernel.id ×ₖ κ)

theorem resetPathKernel_apply (k : ℕ) (x : X) :
    resetPathKernel κ R hR k x =
      markovPath (splitFormation (Measure.dirac x) κ) (formationLiftKernel κ R hR) k := by
  rw [resetPathKernel, Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply,
    splitFormation_dirac, markovPath_eq_comp]

omit [MeasurableSingletonClass X] in
/-- **`(RFDM.13)` for every initial observer law**: the reset chain from `E_κ(μ)` is the
`μ`-mixture of the reset chains from the observers. -/
theorem markovPath_splitFormation (μ : Measure X) [IsProbabilityMeasure μ] (k : ℕ) :
    markovPath (splitFormation μ κ) (formationLiftKernel κ R hR) k =
      resetPathKernel κ R hR k ∘ₘ μ := by
  haveI : IsProbabilityMeasure (splitFormation μ κ) := by unfold splitFormation; infer_instance
  rw [markovPath_eq_comp, splitFormation, Measure.compProd_eq_comp_prod, Measure.comp_assoc]
  rfl

end ResetChain

/-! ### Theorem 4.1: no finite-order execution of a non-Dirac reset -/

section Execution

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {κ : Kernel X ℕ}
  [IsMarkovKernel κ] {R : X → X} {hR : Measurable R}

/-- **`(RFDM.12)`–`(RFDM.13)`** a deterministic execution of the reset process: a measurable
bijection `T` of a source space `Z`, a packet factor `Π : Z → X × ℕ`, and source laws `P_x` (one
for each initial observer; a general initial law `μ` gives the mixture `∫ P_x dμ`) such that the
packets along every `T`-orbit have the finite-dimensional laws of the reset Markov chain. -/
structure ResetExecution (κ : Kernel X ℕ) [IsMarkovKernel κ] (R : X → X) (hR : Measurable R)
    (Z : Type*) [MeasurableSpace Z] where
  /-- the source dynamics -/
  T : Z → Z
  measurable_T : Measurable T
  bijective_T : Function.Bijective T
  /-- the packet factor -/
  packet : Z → X × ℕ
  measurable_packet : Measurable packet
  /-- the source law above each initial observer -/
  source : Kernel X Z
  isMarkov_source : IsMarkovKernel source
  /-- the finite-dimensional laws are those of the reset chain -/
  fdd : ∀ x k, (source x).map (fun z (j : Fin (k + 1)) => packet (T^[j] z)) =
    markovPath (splitFormation (Measure.dirac x) κ) (formationLiftKernel κ R hR) k

omit [MeasurableSingletonClass X] in
theorem measurable_orbitPackets {Z : Type*} [MeasurableSpace Z] (E : ResetExecution κ R hR Z)
    (k : ℕ) : Measurable fun z (j : Fin (k + 1)) => E.packet (E.T^[j] z) :=
  measurable_pi_lambda _ fun j => E.measurable_packet.comp (E.measurable_T.iterate j)

/-- A probability law on `ℕ` whose distinct atoms have zero products is Dirac. -/
theorem exists_eq_dirac_of_mul_eq_zero (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (h : ∀ i j, i ≠ j → ν {i} * ν {j} = 0) : ∃ n, ν = Measure.dirac n := by
  obtain ⟨n, hn⟩ : ∃ n, ν {n} ≠ 0 := by
    by_contra! hall
    have h1 := measure_univ (μ := ν)
    rw [← Set.iUnion_of_singleton_coe (Set.univ : Set ℕ), measure_iUnion
      (fun i j hij => Set.disjoint_singleton.2 fun h => hij (Subtype.ext h))
      (fun _ => MeasurableSet.singleton _)] at h1
    simp [hall] at h1
  refine ⟨n, Measure.ext_of_singleton fun m => ?_⟩
  by_cases hm : m = n
  · subst hm
    have hcompl : ν {m}ᶜ = 0 := by
      have hc : ({m}ᶜ : Set ℕ) = ⋃ j ∈ ({m}ᶜ : Set ℕ), {j} := by ext; simp
      rw [hc, measure_biUnion_null_iff (Set.to_countable _)]
      intro j hj
      have := h m j (Ne.symm hj)
      exact (mul_eq_zero.1 this).resolve_left hn
    have := measure_add_measure_compl (μ := ν) (MeasurableSet.singleton m)
    rw [hcompl, add_zero, measure_univ] at this
    rw [this, Measure.dirac_apply_of_mem (Set.mem_singleton m)]
  · rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
      Set.indicator_of_notMem (by simpa using Ne.symm hm)]
    exact (mul_eq_zero.1 (h n m (Ne.symm hm))).resolve_left hn

/-- **Theorem 4.1 (local form)**: if the source law `P` above `x` executes the reset chain up to
time `N > 0` and `T^N = I`, then `R^N x = x` and `κ_x` is Dirac. -/
theorem dirac_of_periodic_execution {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (T : Z → Z) (hT : Measurable T) (packet : Z → X × ℕ)
    (hpacket : Measurable packet) (x : X) {N : ℕ} (hN : 0 < N)
    (hfdd : P.map (fun z (j : Fin (N + 1)) => packet (T^[j] z)) =
      markovPath (splitFormation (Measure.dirac x) κ) (formationLiftKernel κ R hR) N)
    (hper : T^[N] = id) :
    R^[N] x = x ∧ ∃ n, κ x = Measure.dirac n := by
  rw [markovPath_reset] at hfdd
  set F := fun z (j : Fin (N + 1)) => packet (T^[j] z)
  have hF : Measurable F := measurable_pi_lambda _ fun j => hpacket.comp (hT.iterate j)
  have h0last : (0 : Fin (N + 1)) ≠ Fin.last N := by
    rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; exact hN.ne
  -- under the path law the endpoints coincide
  have hdiag : ∀ A B : Set (X × ℕ), MeasurableSet A → MeasurableSet B → Disjoint A B →
      (Measure.pi fun j : Fin (N + 1) => resetMarginal κ R x j)
        (Set.univ.pi fun j => if j = 0 then A else if j = Fin.last N then B else Set.univ) = 0 := by
    intro A B hA hB hAB
    rw [← hfdd, Measure.map_apply hF (MeasurableSet.univ_pi fun j => by
      split_ifs <;> first | exact hA | exact hB | exact MeasurableSet.univ)]
    convert measure_empty (μ := P)
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_empty_iff_false, iff_false]
    intro hz
    have h0 := hz 0
    have hl := hz (Fin.last N)
    rw [if_pos rfl] at h0
    rw [if_neg (Ne.symm h0last), if_pos rfl] at hl
    simp only [F, Fin.val_last, Fin.val_zero, Function.iterate_zero, id_eq, hper] at h0 hl
    exact Set.disjoint_left.1 hAB h0 hl
  have hbox : ∀ A B : Set (X × ℕ), MeasurableSet A → MeasurableSet B →
      (Measure.pi fun j : Fin (N + 1) => resetMarginal κ R x j)
        (Set.univ.pi fun j => if j = 0 then A else if j = Fin.last N then B else Set.univ) =
        resetMarginal κ R x 0 A * resetMarginal κ R x N B := by
    intro A B _ _
    rw [Measure.pi_pi]
    rw [Finset.prod_eq_mul (0 : Fin (N + 1)) (Fin.last N) h0last
      (fun c _ hc => by rw [if_neg hc.1, if_neg hc.2, measure_univ]) (by simp) (by simp)]
    rw [if_pos rfl, if_neg (Ne.symm h0last), if_pos rfl, Fin.val_zero, Fin.val_last]
  -- the observer returns
  have hret : R^[N] x = x := by
    by_contra hne
    have h := hdiag ({x} ×ˢ Set.univ) ({x}ᶜ ×ˢ Set.univ)
      ((MeasurableSet.singleton x).prod MeasurableSet.univ)
      ((MeasurableSet.singleton x).compl.prod MeasurableSet.univ)
      (Set.disjoint_prod.2 (Or.inl disjoint_compl_right))
    rw [hbox _ _ ((MeasurableSet.singleton x).prod MeasurableSet.univ)
      ((MeasurableSet.singleton x).compl.prod MeasurableSet.univ), resetMarginal, resetMarginal,
      Measure.prod_prod, Measure.prod_prod, Function.iterate_zero, id_eq,
      Measure.dirac_apply_of_mem (Set.mem_singleton x),
      Measure.dirac_apply_of_mem (Set.mem_compl_singleton_iff.2 hne)] at h
    simp at h
  refine ⟨hret, exists_eq_dirac_of_mul_eq_zero (κ x) fun i j hij => ?_⟩
  have h := hdiag ({x} ×ˢ {i}) ({x} ×ˢ {j})
    ((MeasurableSet.singleton x).prod (MeasurableSet.singleton i))
    ((MeasurableSet.singleton x).prod (MeasurableSet.singleton j))
    (Set.disjoint_prod.2 (Or.inr (Set.disjoint_singleton.2 hij)))
  rw [hbox _ _ ((MeasurableSet.singleton x).prod (MeasurableSet.singleton i))
    ((MeasurableSet.singleton x).prod (MeasurableSet.singleton j)), resetMarginal, resetMarginal,
    Measure.prod_prod, Measure.prod_prod, Function.iterate_zero, id_eq, hret,
    Measure.dirac_apply_of_mem (Set.mem_singleton x), one_mul, one_mul] at h
  exact h

/-- **Theorem 4.1**: a periodic execution `T^N = I`, `N > 0`, of the reset process forces every
recovery law to be Dirac; equivalently, a reset process with a non-Dirac recovery law has no
finite-order deterministic execution. -/
theorem resetExecution_not_periodic {Z : Type*} [MeasurableSpace Z]
    (E : ResetExecution κ R hR Z) {N : ℕ} (hN : 0 < N) (hper : E.T^[N] = id) (x : X) :
    R^[N] x = x ∧ ∃ n, κ x = Measure.dirac n := by
  haveI := E.isMarkov_source
  exact dirac_of_periodic_execution (E.source x) E.T E.measurable_T E.packet E.measurable_packet
    x hN (E.fdd x N) hper

/-- An execution realizes the reset process for every initial observer law `μ`, with source law
`∫ P_x dμ(x)`. -/
theorem ResetExecution.fdd_initialLaw {Z : Type*} [MeasurableSpace Z]
    (E : ResetExecution κ R hR Z) (μ : Measure X) [IsProbabilityMeasure μ] (k : ℕ) :
    (E.source ∘ₘ μ).map (fun z (j : Fin (k + 1)) => E.packet (E.T^[j] z)) =
      markovPath (splitFormation μ κ) (formationLiftKernel κ R hR) k := by
  have hker : E.source.map (fun z (j : Fin (k + 1)) => E.packet (E.T^[j] z)) =
      resetPathKernel κ R hR k := Kernel.ext fun x => by
    rw [Kernel.map_apply _ (measurable_orbitPackets E k), E.fdd, resetPathKernel_apply]
  rw [Measure.map_comp _ _ (measurable_orbitPackets E k), markovPath_splitFormation, hker]

/-- **Theorem 4.1**, in the form of `(RFDM.12)`–`(RFDM.13)`: if every initial observer law has a
source law on `Z` whose packet orbit has the reset finite-dimensional laws, and the recovery law
is non-Dirac on a set of positive measure for some initial law, then `T^N ≠ I` for every
`N > 0`. -/
theorem not_periodic_of_executes {Z : Type*} [MeasurableSpace Z] (T : Z → Z) (hT : Measurable T)
    (packet : Z → X × ℕ) (hpacket : Measurable packet)
    (hexec : ∀ μ : Measure X, IsProbabilityMeasure μ → ∃ P : Measure Z, IsProbabilityMeasure P ∧
      ∀ k, P.map (fun z (j : Fin (k + 1)) => packet (T^[j] z)) =
        markovPath (splitFormation μ κ) (formationLiftKernel κ R hR) k)
    (μ : Measure X) (hpos : μ {x | ¬ ∃ n, κ x = Measure.dirac n} ≠ 0) :
    ∀ N, 0 < N → T^[N] ≠ id := by
  intro N hN hper
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos
  obtain ⟨P, hP, hfdd⟩ := hexec (Measure.dirac x) inferInstance
  exact hx (dirac_of_periodic_execution P T hT packet hpacket x hN (hfdd N) hper).2

/-- **Corollary 4.2, `(RFDM.16)`**: for an involution `R`, the formed law closes after two lift
steps, but every execution of a reset process with a non-Dirac recovery law has infinite order. -/
theorem finiteObserverSymmetry_not_finiteSourceSymmetry (hinv : ∀ x, R (R x) = x)
    (μ : Measure X) [IsFiniteMeasure μ] {Z : Type*} [MeasurableSpace Z]
    (E : ResetExecution κ R hR Z) (x : X) (hx : ¬ ∃ n, κ x = Measure.dirac n) :
    formationLiftKernel κ R hR ∘ₘ (formationLiftKernel κ R hR ∘ₘ splitFormation μ κ) =
        splitFormation μ κ ∧
      ∀ N, 0 < N → E.T^[N] ≠ id :=
  ⟨formationLiftKernel_involution_on_formation μ κ R hR hinv,
    fun _ hN hper => hx (resetExecution_not_periodic E hN hper x).2⟩

end Execution

end GaloisForLFunctions.HTGeometry.ResetDilation
