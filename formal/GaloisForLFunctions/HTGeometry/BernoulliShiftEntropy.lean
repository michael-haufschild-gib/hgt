import GaloisForLFunctions.HTGeometry.KolmogorovSinaiEntropy
import Mathlib.Probability.ProductMeasure

/-!
# Kolmogorov–Sinai entropy of a bilateral Bernoulli shift

For a probability law `p` on a countable alphabet `A`, the bilateral Bernoulli shift is
`(A^ℤ, p^ℤ, S)` with `(S ω)_j = ω_{j+1}`.  Proved here:

* the coordinates are independent with law `p`, so the `n`-block of the time-zero coordinate has
  law `p^n` and entropy `n H(p)`;
* the centred windows `(ω_{-k}, …, ω_k)` generate the product σ-algebra;
* **`(HEO.13)`** `h_KS(S, p^ℤ) = H(p)` when `H(p) < ∞`: the coordinate gives `h ≥ H(p)`, and for
  every finite-entropy observable `f` the window estimate
  `H(f^{(n)}) ≤ (n + 2k) H(p) + n H(f | ω_{[-k,k]})` with `H(f | ω_{[-k,k]}) → 0` gives
  `h(S, f) ≤ H(p)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ObservableEntropy

/-- The Shannon entropy `H(p) = ∑_a η(p{a})` of a law on a countable alphabet. -/
def shannonEntropy {A : Type*} [MeasurableSpace A] (p : Measure A) : ℝ≥0∞ := obsEntropy p id

theorem obsEntropy_eq_shannonEntropy_map {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure Ω) {f : Ω → A} (hf : Measurable f) :
    obsEntropy μ f = shannonEntropy (μ.map f) := by
  rw [shannonEntropy, obsEntropy, obsEntropy]
  refine tsum_congr fun a => ?_
  rw [Set.preimage_id, Measure.map_apply hf (measurableSet_singleton a)]

theorem shannonEntropy_congr {A : Type*} [MeasurableSpace A] {p q : Measure A}
    (h : ∀ a, p {a} = q {a}) : shannonEntropy p = shannonEntropy q := by
  rw [shannonEntropy, shannonEntropy, obsEntropy, obsEntropy]
  exact tsum_congr fun a => by rw [preimage_id, h]

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
  (p : Measure A) [IsProbabilityMeasure p]

/-! ### Product laws on blocks -/

/-- `H(p^n) = n H(p)`. -/
theorem shannonEntropy_pi (n : ℕ) :
    shannonEntropy (Measure.pi fun _ : Fin n => p) = n * shannonEntropy p := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, shannonEntropy, ← obsCondEntropy_const _ _ ()]
    exact obsCondEntropy_of_subsingleton _ _ _
  | succ n ih =>
    set μ := Measure.pi fun _ : Fin (n + 1) => p
    let init : (Fin (n + 1) → A) → Fin n → A := fun w i => w i.castSucc
    let last : (Fin (n + 1) → A) → A := fun w => w (Fin.last n)
    have hinit : Measurable init := measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hlast : Measurable last := measurable_pi_apply _
    have hbox : ∀ (s : Fin n → Set A) (t : Set A),
        μ (init ⁻¹' Set.univ.pi s ∩ last ⁻¹' t) = (∏ i, p (s i)) * p t := by
      intro s t
      have : init ⁻¹' Set.univ.pi s ∩ last ⁻¹' t =
          Set.univ.pi (Fin.lastCases (motive := fun _ => Set A) t s) := by
        ext w
        simp only [mem_inter_iff, mem_preimage, mem_univ_pi, init, last]
        rw [Fin.forall_fin_succ'
          (P := fun i => w i ∈ Fin.lastCases (motive := fun _ => Set A) t s i)]
        simp
      rw [this, Measure.pi_pi, Fin.prod_univ_castSucc]
      simp
    have hindep : ∀ u a, μ (init ⁻¹' {u} ∩ last ⁻¹' {a}) = μ (init ⁻¹' {u}) * μ (last ⁻¹' {a}) := by
      intro u a
      have h1 := hbox (fun i => {u i}) {a}
      have h2 := hbox (fun i => {u i}) univ
      have h3 := hbox (fun _ => univ) {a}
      rw [Set.univ_pi_singleton, preimage_univ, inter_univ] at h2
      rw [Set.univ_pi_singleton] at h1
      rw [Set.pi_univ, preimage_univ, univ_inter] at h3
      rw [h1, h2, h3, measure_univ, mul_one]
      simp
    have hpair : (id : (Fin (n + 1) → A) → Fin (n + 1) → A) =
        (fun q : (Fin n → A) × A => Fin.snoc (α := fun _ => A) q.1 q.2) ∘ pairObs init last := by
      funext w i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [pairObs, last]
      · simp [pairObs, init]
    have hinj : Function.Injective fun q : (Fin n → A) × A => Fin.snoc (α := fun _ => A) q.1 q.2 :=
      fun q r h => Prod.ext (Fin.snoc_injective2 h).1 (Fin.snoc_injective2 h).2
    rw [shannonEntropy, hpair, obsEntropy_comp μ hinj,
      obsEntropy_pairObs_of_indep μ hinit hlast hindep, obsEntropy_eq_shannonEntropy_map μ hinit,
      obsEntropy_eq_shannonEntropy_map μ hlast]
    have hmi : shannonEntropy (μ.map init) = shannonEntropy (Measure.pi fun _ : Fin n => p) := by
      refine shannonEntropy_congr fun u => ?_
      rw [Measure.map_apply hinit (measurableSet_singleton u)]
      have := hbox (fun i => {u i}) univ
      rw [Set.univ_pi_singleton, preimage_univ, inter_univ, measure_univ, mul_one] at this
      rw [this, ← Set.univ_pi_singleton, Measure.pi_pi]
    have hml : shannonEntropy (μ.map last) = shannonEntropy p := by
      refine shannonEntropy_congr fun a => ?_
      rw [Measure.map_apply hlast (measurableSet_singleton a)]
      have := hbox (fun _ => univ) {a}
      rw [Set.pi_univ, preimage_univ, univ_inter] at this
      rw [this]
      simp
    rw [hmi, hml, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-! ### The bilateral shift -/

/-- The Bernoulli history law `p^ℤ`. -/
def bernoulliLaw : Measure (ℤ → A) := Measure.infinitePi fun _ : ℤ => p

instance : IsProbabilityMeasure (bernoulliLaw p) := by unfold bernoulliLaw; infer_instance

/-- The bilateral left shift `(S ω)_j = ω_{j+1}`. -/
def leftShift (ω : ℤ → A) : ℤ → A := fun j => ω (j + 1)

/-- The inverse shift `(S⁻¹ ω)_j = ω_{j-1}`. -/
def rightShift (ω : ℤ → A) : ℤ → A := fun j => ω (j - 1)

/-- The time-zero coordinate. -/
def coordObs (ω : ℤ → A) : A := ω 0

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem leftShift_rightShift (ω : ℤ → A) : leftShift (rightShift ω) = ω := by
  funext j; simp [leftShift, rightShift]

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem rightShift_leftShift (ω : ℤ → A) : rightShift (leftShift ω) = ω := by
  funext j; simp [leftShift, rightShift]

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurable_leftShift : Measurable (leftShift (A := A)) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j + 1)

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurable_rightShift : Measurable (rightShift (A := A)) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j - 1)

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurable_coordObs : Measurable (coordObs (A := A)) := measurable_pi_apply 0

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem leftShift_iterate (i : ℕ) (ω : ℤ → A) (j : ℤ) : (leftShift^[i] ω) j = ω (j + i) := by
  induction i generalizing ω with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [leftShift]
    congr 1; push_cast; ring

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem rightShift_iterate (i : ℕ) (ω : ℤ → A) (j : ℤ) : (rightShift^[i] ω) j = ω (j - i) := by
  induction i generalizing ω with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [rightShift]
    congr 1; push_cast; ring

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurePreserving_leftShift :
    MeasurePreserving leftShift (bernoulliLaw p) (bernoulliLaw p) := by
  refine ⟨measurable_leftShift, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => p) (Equiv.addRight (-1 : ℤ))
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => A) (Equiv.addRight (-1 : ℤ))) =
      leftShift := by
    funext ω j
    rw [MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : ℤ => A) (Equiv.addRight (-1 : ℤ)) ω (j + 1)
    simp only [Equiv.coe_addRight, add_neg_cancel_right] at this
    exact this
  rw [hfun] at h
  exact h

omit [MeasurableSingletonClass A] [Countable A] in
theorem measurePreserving_rightShift :
    MeasurePreserving rightShift (bernoulliLaw p) (bernoulliLaw p) := by
  refine ⟨measurable_rightShift, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => p) (Equiv.addRight (1 : ℤ))
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => A) (Equiv.addRight (1 : ℤ))) =
      rightShift := by
    funext ω j
    rw [MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : ℤ => A) (Equiv.addRight (1 : ℤ)) ω (j - 1)
    simp only [Equiv.coe_addRight, sub_add_cancel] at this
    exact this
  rw [hfun] at h
  exact h

/-! ### Blocks of the coordinate process -/

omit [MeasurableSingletonClass A] [Countable A] in
theorem bernoulliLaw_map_blockObs (n : ℕ) :
    (bernoulliLaw p).map (blockObs leftShift coordObs n) = Measure.pi fun _ : Fin n => p := by
  classical
  have hmeas := measurable_blockObs measurable_leftShift (measurable_coordObs (A := A)) n
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let I : Finset ℤ :=
    (Finset.univ : Finset (Fin n)).image fun j : Fin n => ((j : ℕ) : ℤ)
  let t : ℤ → Set A := fun i => if h : 0 ≤ i ∧ i.toNat < n then s ⟨i.toNat, h.2⟩ else Set.univ
  have ht : ∀ j : Fin n, t ((j : ℕ) : ℤ) = s j := fun j => by
    have h : 0 ≤ ((j : ℕ) : ℤ) ∧ ((j : ℕ) : ℤ).toNat < n :=
      ⟨by positivity, by have := j.isLt; simp only [Int.toNat_natCast]; omega⟩
    simp only [t, dif_pos h]
    exact congrArg s (Fin.ext (by simp))
  have hset : blockObs leftShift coordObs n ⁻¹' Set.univ.pi s = (I : Set ℤ).pi t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, I, Finset.mem_image,
      Finset.mem_univ, true_and, blockObs, coordObs, leftShift_iterate, zero_add]
    constructor
    · rintro hω i ⟨j, rfl⟩
      rw [ht]; exact hω j (Set.mem_univ j)
    · intro hω j _
      have := hω _ ⟨j, rfl⟩
      rwa [ht] at this
  have hinj : Set.InjOn (fun j : Fin n => ((j : ℕ) : ℤ))
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)) :=
    fun a _ b _ h => by simpa [Fin.ext_iff] using h
  rw [hset, bernoulliLaw, Measure.infinitePi_pi _ (fun i _ => by
      simp only [t]; split_ifs <;> first | exact hs _ | exact MeasurableSet.univ),
    Finset.prod_image hinj]
  exact Finset.prod_congr rfl fun j _ => by rw [ht]

/-- `H(ξ^{(n)}) = n H(p)` for the coordinate process. -/
theorem obsEntropy_blockObs_coordObs (n : ℕ) :
    obsEntropy (bernoulliLaw p) (blockObs leftShift coordObs n) = n * shannonEntropy p := by
  rw [obsEntropy_eq_shannonEntropy_map _
    (measurable_blockObs measurable_leftShift (measurable_coordObs (A := A)) n),
    bernoulliLaw_map_blockObs, shannonEntropy_pi]

/-! ### The centred windows generate -/

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem windowObs_apply (k m : ℕ) (ω : ℤ → A) (j : Fin m) :
    windowObs leftShift rightShift coordObs k m ω j = ω ((j : ℤ) - k) := by
  simp only [windowObs, blockObs, coordObs, Function.comp_apply, leftShift_iterate,
    rightShift_iterate, zero_add]

omit [MeasurableSingletonClass A] [Countable A] in
theorem comap_windowObs_mono :
    Monotone fun k => MeasurableSpace.comap
      (windowObs leftShift rightShift (coordObs (A := A)) k (2 * k + 1)) inferInstance := by
  refine monotone_nat_of_le_succ fun k => ?_
  have hsel : windowObs leftShift rightShift (coordObs (A := A)) k (2 * k + 1) =
      (fun (w : Fin (2 * (k + 1) + 1) → A) (j : Fin (2 * k + 1)) => w ⟨j + 1, by omega⟩) ∘
        windowObs leftShift rightShift coordObs (k + 1) (2 * (k + 1) + 1) := by
    funext ω j
    simp only [Function.comp_apply, windowObs_apply]
    congr 1; push_cast; ring
  simp only [hsel]
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_lambda _ fun j => measurable_pi_apply _).comap_le

omit [MeasurableSingletonClass A] [Countable A] in
theorem pi_le_iSup_comap_windowObs :
    (MeasurableSpace.pi : MeasurableSpace (ℤ → A)) ≤
      ⨆ k, MeasurableSpace.comap
        (windowObs leftShift rightShift (coordObs (A := A)) k (2 * k + 1)) inferInstance := by
  refine iSup_le fun j => ?_
  let k := j.natAbs
  have hj : 0 ≤ j + k ∧ (j + k).toNat < 2 * k + 1 := by omega
  have heval : (fun ω : ℤ → A => ω j) = (fun w : Fin (2 * k + 1) → A => w ⟨(j + k).toNat, hj.2⟩) ∘
      windowObs leftShift rightShift coordObs k (2 * k + 1) := by
    funext ω
    simp only [Function.comp_apply, windowObs_apply]
    congr 1; omega
  refine le_iSup_of_le k ?_
  change MeasurableSpace.comap (fun ω : ℤ → A => ω j) inferInstance ≤ _
  rw [heval, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-! ### `(HEO.13)` -/

omit [MeasurableSingletonClass A] [Countable A] in
theorem map_coordObs : (bernoulliLaw p).map coordObs = p :=
  (measurePreserving_eval_infinitePi (fun _ : ℤ => p) 0).map_eq

omit [Countable A] in
theorem obsEntropy_coordObs :
    obsEntropy (bernoulliLaw p) (coordObs (A := A)) = shannonEntropy p := by
  rw [obsEntropy_eq_shannonEntropy_map _ measurable_coordObs, map_coordObs]

theorem mul_div_cancel_left_ennreal {a b : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) : a * b / a = b :=
  ((ENNReal.eq_div_iff ha ha').2 rfl).symm

/-- The coordinate process has entropy rate `H(p)`. -/
theorem entropyRate_coordObs :
    entropyRate (bernoulliLaw p) leftShift (coordObs (A := A)) = shannonEntropy p := by
  unfold entropyRate
  have hterm : ∀ n : ℕ, obsEntropy (bernoulliLaw p) (blockObs leftShift coordObs (n + 1)) /
      ((n : ℝ≥0∞) + 1) = shannonEntropy p := fun n => by
    rw [obsEntropy_blockObs_coordObs, Nat.cast_add, Nat.cast_one]
    exact mul_div_cancel_left_ennreal (by positivity) (by simp)
  simp_rw [hterm]
  exact iInf_const

/-- Every finite-entropy observable has entropy rate at most `H(p)`. -/
theorem entropyRate_le_shannonEntropy (hp : shannonEntropy p ≠ ⊤) {f : (ℤ → A) → ℕ}
    (hf : Measurable f) (hH : obsEntropy (bernoulliLaw p) f ≠ ⊤) :
    entropyRate (bernoulliLaw p) leftShift f ≤ shannonEntropy p := by
  set H := shannonEntropy p
  set ε : ℕ → ℝ≥0∞ := fun k => obsCondEntropy (bernoulliLaw p) f
    (windowObs leftShift rightShift coordObs k (2 * k + 1))
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_obsCondEntropy_of_generating (bernoulliLaw p)
      (fun k => measurable_windowObs measurable_leftShift measurable_rightShift
        measurable_coordObs k _) comap_windowObs_mono
      (hf.mono pi_le_iSup_comap_windowObs le_rfl) hH
  have hk : ∀ k, entropyRate (bernoulliLaw p) leftShift f ≤ H + ε k := by
    intro k
    have hn : ∀ n : ℕ, entropyRate (bernoulliLaw p) leftShift f ≤
        H + 2 * k * H / ((n : ℝ≥0∞) + 1) + ε k := by
      intro n
      have hwin := obsEntropy_blockObs_le_window (bernoulliLaw p)
        (measurePreserving_leftShift p) (measurePreserving_rightShift p) leftShift_rightShift
        rightShift_leftShift hf measurable_coordObs (n + 1) k
      rw [obsEntropy_blockObs_coordObs] at hwin
      have hN0 : ((n : ℝ≥0∞) + 1) ≠ 0 := by positivity
      have hNt : ((n : ℝ≥0∞) + 1) ≠ ⊤ := by simp
      refine (iInf_le _ n).trans ?_
      rw [ENNReal.div_le_iff hN0 hNt]
      refine hwin.trans (le_of_eq ?_)
      rw [add_mul, add_mul, ENNReal.div_mul_cancel hN0 hNt]
      push_cast
      ring
    have hlim : Tendsto (fun n : ℕ => H + 2 * k * H / ((n : ℝ≥0∞) + 1) + ε k) atTop
        (𝓝 (H + 0 + ε k)) := by
      refine (tendsto_const_nhds.add ?_).add tendsto_const_nhds
      have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp
      have hc : 2 * (k : ℝ≥0∞) * H ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top k)) hp
      have := ENNReal.Tendsto.const_mul hinv (Or.inr hc)
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [div_eq_mul_inv]
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim hn
  have hlim : Tendsto (fun k => H + ε k) atTop (𝓝 (H + 0)) := tendsto_const_nhds.add hε
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hk

/-- **`(HEO.13)`** `h_KS(S, p^ℤ) = H(p)` for a law of finite Shannon entropy on a countable
alphabet. -/
theorem ksEntropy_bernoulli (hp : shannonEntropy p ≠ ⊤) :
    ksEntropy (bernoulliLaw p) leftShift = shannonEntropy p := by
  refine le_antisymm (iSup_le fun f => iSup_le fun hf => iSup_le fun hH =>
    entropyRate_le_shannonEntropy p hp hf hH) ?_
  obtain ⟨e, he⟩ := exists_injective_nat A
  have hfin : obsEntropy (bernoulliLaw p) (e ∘ coordObs (A := A)) ≠ ⊤ := by
    rwa [obsEntropy_comp _ he, obsEntropy_coordObs]
  rw [← entropyRate_coordObs p, ← entropyRate_comp _ _ he]
  exact le_iSup_of_le (e ∘ coordObs) (le_iSup_of_le ((measurable_of_countable e).comp
    measurable_coordObs) (le_iSup_of_le hfin le_rfl))

end GaloisForLFunctions.HTGeometry.ObservableEntropy
