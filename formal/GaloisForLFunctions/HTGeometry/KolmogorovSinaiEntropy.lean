import GaloisForLFunctions.HTGeometry.ConditionalEntropyGeneratingLimit

/-!
# Kolmogorov–Sinai entropy

For a measure-preserving map `T` of a probability space and a countably-valued observable `f`,
the `n`-block `f^{(n)} = (f, f ∘ T, …, f ∘ T^{n-1})` has subadditive entropy, the entropy rate is
`h(T, f) = inf_n H(f^{(n)})/n = lim_n H(f^{(n)})/n` (Fekete), and the Kolmogorov–Sinai entropy is
`h_KS(T) = sup_f h(T, f)` over measurable `ℕ`-valued observables of finite entropy.

* `ksEntropy_le_of_factor`: a measure-preserving factor map `Φ` with `Φ ∘ T = T' ∘ Φ` a.e. gives
  `h_KS(T') ≤ h_KS(T)`; in particular mod-zero conjugacies preserve Kolmogorov–Sinai entropy.
* `obsEntropy_blockObs_le_window`: for invertible `T`, the block entropy of `f` is bounded by the
  entropy of a window of a second observable `ξ` plus `n` times the conditional entropy of `f`
  given the centred window — the estimate behind the Kolmogorov–Sinai generator theorem.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ObservableEntropy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → Ω)
variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- The `n`-block `ω ↦ (f ω, f (T ω), …, f (T^{n-1} ω))`. -/
def blockObs (f : Ω → α) (n : ℕ) (ω : Ω) : Fin n → α := fun i => f (T^[i] ω)

omit [MeasurableSingletonClass α] [Countable α] in
theorem measurable_blockObs {T : Ω → Ω} (hT : Measurable T) {f : Ω → α} (hf : Measurable f)
    (n : ℕ) : Measurable (blockObs T f n) :=
  measurable_pi_lambda _ fun i => hf.comp (hT.iterate i)

/-- The entropy rate `h(T, f) = inf_n H(f^{(n+1)})/(n+1)`. -/
def entropyRate (f : Ω → α) : ℝ≥0∞ :=
  ⨅ n : ℕ, obsEntropy μ (blockObs T f (n + 1)) / ((n : ℝ≥0∞) + 1)

/-- The **Kolmogorov–Sinai entropy** `h_KS(T) = sup_f h(T, f)` over measurable `ℕ`-valued
observables of finite entropy. -/
def ksEntropy : ℝ≥0∞ :=
  ⨆ (f : Ω → ℕ) (_ : Measurable f) (_ : obsEntropy μ f ≠ ⊤), entropyRate μ T f

/-! ### Relabelling and subsingletons -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Countable β] in
theorem entropyRate_comp {f : Ω → α} {φ : α → β} (hφ : Function.Injective φ) :
    entropyRate μ T (φ ∘ f) = entropyRate μ T f := by
  unfold entropyRate
  congr 1
  funext n
  have hinj : Function.Injective fun (w : Fin (n + 1) → α) (i : Fin (n + 1)) => φ (w i) :=
    fun u v h => funext fun i => hφ (congrFun h i)
  have : blockObs T (φ ∘ f) (n + 1) = (fun w i => φ (w i)) ∘ blockObs T f (n + 1) := rfl
  rw [this, obsEntropy_comp μ hinj]

omit [MeasurableSingletonClass β] [Countable β] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable α] [MeasurableSpace β] in
/-- A constant observable has no conditional entropy. -/
theorem obsCondEntropy_of_subsingleton [Subsingleton α] (f : Ω → α) (g : Ω → β) :
    obsCondEntropy μ f g = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun p => ?_
  have hf : f ⁻¹' {p.1} = univ := by
    ext ω; simp [Subsingleton.elim (f ω) p.1]
  rw [hf, univ_inter, condTerm]
  by_cases h0 : (μ (g ⁻¹' {p.2})).toReal = 0
  · rw [h0]; simp
  rw [div_self h0, Real.log_one, mul_zero, ENNReal.ofReal_zero]

/-! ### Subadditivity of block entropies -/

/-- Block conditional subadditivity `H(F_0, …, F_{n-1} | Z) ≤ ∑_i H(F_i | Z)`. -/
theorem obsCondEntropy_tuple_le [IsFiniteMeasure μ] {Z : Ω → β} (hZ : Measurable Z) :
    ∀ (n : ℕ) (F : Fin n → Ω → α), (∀ i, Measurable (F i)) →
      obsCondEntropy μ (fun ω i => F i ω) Z ≤ ∑ i, obsCondEntropy μ (F i) Z
  | 0, F, _ => by rw [obsCondEntropy_of_subsingleton]; exact zero_le
  | n + 1, F, hF => by
    have hsnoc : (fun ω (i : Fin (n + 1)) => F i ω) =
        (fun p : (Fin n → α) × α => Fin.snoc (α := fun _ => α) p.1 p.2) ∘
          pairObs (fun ω (i : Fin n) => F i.castSucc ω) (F (Fin.last n)) := by
      funext ω i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [pairObs]
      · simp [pairObs]
    have hinj : Function.Injective fun p : (Fin n → α) × α => Fin.snoc (α := fun _ => α) p.1 p.2 :=
      fun p q h => Prod.ext (Fin.snoc_injective2 h).1 (Fin.snoc_injective2 h).2
    rw [hsnoc, obsCondEntropy_comp_left μ hinj, Fin.sum_univ_castSucc]
    refine (obsCondEntropy_pairObs_le_add μ (measurable_pi_lambda _ fun i => hF _) (hF _)
      hZ).trans (add_le_add ?_ le_rfl)
    exact obsCondEntropy_tuple_le hZ n (fun i => F i.castSucc) fun i => hF _

/-- Block entropy subadditivity `H(f^{(m+n)}) ≤ H(f^{(m)}) + H(f^{(n)})`. -/
theorem obsEntropy_blockObs_add_le [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → α} (hf : Measurable f) (m n : ℕ) :
    obsEntropy μ (blockObs T f (m + n)) ≤
      obsEntropy μ (blockObs T f m) + obsEntropy μ (blockObs T f n) := by
  have happ : blockObs T f (m + n) = (fun p : (Fin m → α) × (Fin n → α) => Fin.append p.1 p.2) ∘
      pairObs (blockObs T f m) (blockObs T f n ∘ T^[m]) := by
    funext ω i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [pairObs, blockObs]
    · simp only [Function.comp_apply, pairObs, Fin.append_right, blockObs, Fin.val_natAdd]
      rw [add_comm, Function.iterate_add_apply]
  have hinj : Function.Injective fun p : (Fin m → α) × (Fin n → α) => Fin.append p.1 p.2 := by
    intro p q h
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · have := congrFun h (Fin.castAdd n i)
      simpa using this
    · have := congrFun h (Fin.natAdd m j)
      simpa using this
  rw [happ, obsEntropy_comp μ hinj]
  refine (obsEntropy_pairObs_le μ (measurable_blockObs hT.measurable hf m)
    ((measurable_blockObs hT.measurable hf n).comp (hT.measurable.iterate m))).trans
    (le_of_eq ?_)
  rw [obsEntropy_comp_measurePreserving μ (hT.iterate m) (measurable_blockObs hT.measurable hf n)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem obsEntropy_blockObs_one (f : Ω → α) :
    obsEntropy μ (blockObs T f 1) = obsEntropy μ f := by
  have hinj : Function.Injective fun (a : α) (_ : Fin 1) => a :=
    fun a b h => congrFun h 0
  have : blockObs T f 1 = (fun (a : α) (_ : Fin 1) => a) ∘ f := by
    funext ω i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [this, obsEntropy_comp μ hinj]

theorem obsEntropy_blockObs_le [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → α} (hf : Measurable f) (n : ℕ) :
    obsEntropy μ (blockObs T f n) ≤ n * obsEntropy μ f := by
  induction n with
  | zero =>
    have : obsEntropy μ (blockObs T f 0) = 0 := by
      rw [← obsCondEntropy_const μ _ ()]
      exact obsCondEntropy_of_subsingleton μ _ _
    rw [this]; exact zero_le
  | succ n ih =>
    refine (obsEntropy_blockObs_add_le μ hT hf n 1).trans ?_
    rw [obsEntropy_blockObs_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add ih le_rfl

/-! ### Fekete: the entropy rate is a limit -/

/-- **Fekete**: for a finite-entropy observable, `H(f^{(n+1)})/(n+1) → h(T, f)`. -/
theorem tendsto_entropyRate [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → α} (hf : Measurable f) (hH : obsEntropy μ f ≠ ⊤) :
    Tendsto (fun n : ℕ => obsEntropy μ (blockObs T f (n + 1)) / ((n : ℝ≥0∞) + 1)) atTop
      (𝓝 (entropyRate μ T f)) := by
  have hfin : ∀ n, obsEntropy μ (blockObs T f n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hH)
      (obsEntropy_blockObs_le μ hT hf n)
  set u : ℕ → ℝ := fun n => (obsEntropy μ (blockObs T f n)).toReal
  have hsub : Subadditive u := fun m n => by
    simp only [u]
    rw [← ENNReal.toReal_add (hfin m) (hfin n)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin m, hfin n⟩)
      (obsEntropy_blockObs_add_le μ hT hf m n)
  have hbdd : BddBelow (range fun n => u n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg n)⟩
  have hlim := hsub.tendsto_lim hbdd
  have hterm : ∀ n : ℕ, obsEntropy μ (blockObs T f (n + 1)) / ((n : ℝ≥0∞) + 1) =
      ENNReal.ofReal (u (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_toReal (hfin _),
      ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  have hseq : Tendsto (fun n : ℕ => obsEntropy μ (blockObs T f (n + 1)) / ((n : ℝ≥0∞) + 1))
      atTop (𝓝 (ENNReal.ofReal hsub.lim)) := by
    simp_rw [hterm]
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_add_atTop_iff_nat 1).2 hlim)
  have heq : entropyRate μ T f = ENNReal.ofReal hsub.lim := by
    refine le_antisymm (ge_of_tendsto' hseq fun n => ?_) (le_iInf fun n => ?_)
    · unfold entropyRate
      exact iInf_le (fun n : ℕ => obsEntropy μ (blockObs T f (n + 1)) / ((n : ℝ≥0∞) + 1)) n
    rw [hterm]
    exact ENNReal.ofReal_le_ofReal (hsub.lim_le_div hbdd (Nat.succ_ne_zero n))
  rw [heq]
  exact hseq

/-! ### Factors -/

omit [MeasurableSingletonClass α] [Countable α] in
theorem iterate_comp_ae_eq {Ω' : Type*} {T' : Ω' → Ω'}
    {Φ : Ω → Ω'} (hT : MeasurePreserving T μ μ) (hcomm : Φ ∘ T =ᵐ[μ] T' ∘ Φ) (i : ℕ) :
    Φ ∘ T^[i] =ᵐ[μ] T'^[i] ∘ Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (Φ ∘ T^[i]) ∘ T =ᵐ[μ] (T'^[i] ∘ Φ) ∘ T := by
      refine ae_eq_comp hT.measurable.aemeasurable ?_
      rw [hT.map_eq]
      exact ih
    have h2 : T'^[i] ∘ (Φ ∘ T) =ᵐ[μ] T'^[i] ∘ (T' ∘ Φ) := hcomm.fun_comp _
    rw [Function.iterate_succ, Function.iterate_succ]
    exact h1.trans h2

omit [Countable α] in
/-- Block entropies are carried through a measure-preserving factor map. -/
theorem obsEntropy_blockObs_factor {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {T : Ω → Ω} {T' : Ω' → Ω'} {Φ : Ω → Ω'} (hΦ : MeasurePreserving Φ μ μ')
    (hT : MeasurePreserving T μ μ) (hT' : Measurable T') (hcomm : Φ ∘ T =ᵐ[μ] T' ∘ Φ)
    {f : Ω' → α} (hf : Measurable f) (n : ℕ) :
    obsEntropy μ (blockObs T (f ∘ Φ) n) = obsEntropy μ' (blockObs T' f n) := by
  have hae : blockObs T (f ∘ Φ) n =ᵐ[μ] blockObs T' f n ∘ Φ := by
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n, Φ (T^[i] ω) = T'^[i] (Φ ω) :=
      ae_all_iff.2 fun i => iterate_comp_ae_eq μ T hT hcomm i
    filter_upwards [hall] with ω hω
    funext i
    simp only [blockObs, Function.comp_apply, hω i]
  rw [obsEntropy_congr_ae μ hae,
    obsEntropy_comp_measurePreserving μ hΦ (measurable_blockObs hT' hf n)]

/-- **Factor inequality**: a measure-preserving factor map intertwining the dynamics a.e. does
not increase Kolmogorov–Sinai entropy. -/
theorem ksEntropy_le_of_factor {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {T : Ω → Ω}
    {T' : Ω' → Ω'} {Φ : Ω → Ω'} (hΦ : MeasurePreserving Φ μ μ') (hT : MeasurePreserving T μ μ)
    (hT' : Measurable T') (hcomm : Φ ∘ T =ᵐ[μ] T' ∘ Φ) :
    ksEntropy μ' T' ≤ ksEntropy μ T := by
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hH => ?_
  have hrate : entropyRate μ' T' f = entropyRate μ T (f ∘ Φ) := by
    unfold entropyRate
    congr 1
    funext n
    rw [obsEntropy_blockObs_factor μ hΦ hT hT' hcomm hf]
  have hH' : obsEntropy μ (f ∘ Φ) ≠ ⊤ := by
    rwa [obsEntropy_comp_measurePreserving μ hΦ hf]
  rw [hrate]
  exact le_iSup_of_le (f ∘ Φ) (le_iSup_of_le (hf.comp hΦ.measurable) (le_iSup_of_le hH' le_rfl))

/-! ### The window estimate -/

/-- The window `ω ↦ (ξ(T^j T'^k ω))_{j < m}`, covering the times `-k, …, m - k - 1`. -/
def windowObs (T' : Ω → Ω) (ξ : Ω → β) (k m : ℕ) : Ω → Fin m → β := blockObs T ξ m ∘ T'^[k]

omit [MeasurableSingletonClass β] [Countable β] in
theorem measurable_windowObs {T T' : Ω → Ω} (hT : Measurable T) (hT' : Measurable T')
    {ξ : Ω → β} (hξ : Measurable ξ) (k m : ℕ) : Measurable (windowObs T T' ξ k m) :=
  (measurable_blockObs hT hξ m).comp (hT'.iterate k)

/-- **Window estimate**: for invertible measure-preserving `T`,
`H(f^{(n)}) ≤ H(ξ^{(n+2k)}) + n H(f | ξ_{[-k,k]})`. -/
theorem obsEntropy_blockObs_le_window [IsProbabilityMeasure μ] {T T' : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (hT' : MeasurePreserving T' μ μ) (hinv : ∀ ω, T (T' ω) = ω)
    (hinv' : ∀ ω, T' (T ω) = ω) {f : Ω → α} (hf : Measurable f) {ξ : Ω → β}
    (hξ : Measurable ξ) (n k : ℕ) :
    obsEntropy μ (blockObs T f n) ≤ obsEntropy μ (blockObs T ξ (n + 2 * k)) +
      n * obsCondEntropy μ f (windowObs T T' ξ k (2 * k + 1)) := by
  set Z := windowObs T T' ξ k (n + 2 * k)
  set W := windowObs T T' ξ k (2 * k + 1)
  have hZ : Measurable Z := measurable_windowObs hT.measurable hT'.measurable hξ k _
  have hW : Measurable W := measurable_windowObs hT.measurable hT'.measurable hξ k _
  have hcomm : Function.Commute T' T := fun ω => by rw [hinv, hinv']
  -- the centred window at time `i` is a coordinate selection of `Z`
  have hsel : ∀ i : Fin n, W ∘ T^[i] = (fun (w : Fin (n + 2 * k) → β) (j : Fin (2 * k + 1)) =>
      w ⟨j + i, by omega⟩) ∘ Z := by
    intro i
    funext ω j
    simp only [W, Z, windowObs, blockObs, Function.comp_apply]
    rw [(hcomm.iterate_iterate k i) ω, ← Function.iterate_add_apply]
  have hstep : ∀ i : Fin n, obsCondEntropy μ (f ∘ T^[i]) Z ≤ obsCondEntropy μ f W := by
    intro i
    have h := obsCondEntropy_le_comp μ (hf.comp (hT.measurable.iterate i)) hZ
      (fun (w : Fin (n + 2 * k) → β) (j : Fin (2 * k + 1)) => w ⟨j + i, by omega⟩)
    rw [← hsel i, obsCondEntropy_comp_measurePreserving μ (hT.iterate i) hf hW] at h
    exact h
  have hblock : obsCondEntropy μ (blockObs T f n) Z ≤ n * obsCondEntropy μ f W := by
    refine (obsCondEntropy_tuple_le μ hZ n (fun i => f ∘ T^[i])
      (fun i => hf.comp (hT.measurable.iterate i))).trans ?_
    refine (Finset.sum_le_sum fun i _ => hstep i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZent : obsEntropy μ Z = obsEntropy μ (blockObs T ξ (n + 2 * k)) :=
    obsEntropy_comp_measurePreserving μ (hT'.iterate k) (measurable_blockObs hT.measurable hξ _)
  calc obsEntropy μ (blockObs T f n)
      ≤ obsEntropy μ (pairObs (blockObs T f n) Z) :=
        obsEntropy_le_pairObs μ (measurable_blockObs hT.measurable hf n) hZ
    _ = obsEntropy μ Z + obsCondEntropy μ (blockObs T f n) Z :=
        obsEntropy_pairObs μ (measurable_blockObs hT.measurable hf n) hZ
    _ ≤ _ := by rw [hZent]; exact add_le_add le_rfl hblock

end GaloisForLFunctions.HTGeometry.ObservableEntropy
