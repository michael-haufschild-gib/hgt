import GaloisForLFunctions.HTGeometry.ResetMarkovExecution
import Mathlib.Probability.ProductMeasure

/-!
# The bilateral reversible reset dilation

Let `U = [0, 1)` with Lebesgue measure `λ`, `Ω = U^ℤ` with the product law `λ^ℤ` and the
bilateral shift `(S ω)_j = ω_{j+1}`.  With the cumulative recovery masses
`c_n(x) = ∑_{j < n} κ_x(j)`, the inverse-transform sampler `G(x, u) = n ⟺ c_n(x) ≤ u < c_{n+1}(x)`
satisfies `λ{G(x, ·) = n} = κ_x(n)`.

* **Theorem 6.1, `(RFDM.19)`–`(RFDM.24)`**: `𝒯(x, ω) = (Rx, Sω)` is a measurable bijection with
  inverse `(Rx, S⁻¹ω)`; with the packet factor `Π(x, ω) = (x, G(x, ω_0))` and source laws
  `δ_x ⊗ λ^ℤ` it executes the reset process, `𝒯² = (x, S²ω)`, `𝒯` has infinite order and almost
  every seed history is nonperiodic.
* **Theorem 6.2, `(RFDM.25)`–`(RFDM.27)`**: `D(μ ⊗ λ^ℤ ‖ ν ⊗ λ^ℤ) = D(μ ‖ ν)`, the same after
  `𝒯_*`, and `Π_*(μ ⊗ λ^ℤ) = E_κ(μ)` with `D(E_κ μ ‖ E_κ ν) = D(μ ‖ ν)`.
-/

open MeasureTheory InformationTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResetDilation

/-! ### The seed space `U = [0, 1)` and its product law -/

/-- The seed interval `U = [0, 1)`. -/
abbrev Seed : Type := Set.Ico (0 : ℝ) 1

/-- Lebesgue measure on the seed interval. -/
def seedLaw : Measure Seed := volume.comap Subtype.val

theorem seedLaw_apply (s : Set Seed) : seedLaw s = volume (Subtype.val '' s) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Ico).comap_apply _ _

instance : IsProbabilityMeasure seedLaw := by
  constructor
  rw [seedLaw_apply, Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq, Real.volume_Ico]
  norm_num

theorem seedLaw_singleton (u : Seed) : seedLaw {u} = 0 := by
  rw [seedLaw_apply, Set.image_singleton, Real.volume_singleton]

/-- The seed-history space `Ω = U^ℤ`. -/
abbrev SeedHistory : Type := ℤ → Seed

/-- The product law `λ^ℤ`. -/
def historyLaw : Measure SeedHistory := Measure.infinitePi fun _ : ℤ => seedLaw

instance : IsProbabilityMeasure historyLaw := by unfold historyLaw; infer_instance

/-- The bilateral shift `(S ω)_j = ω_{j+1}`. -/
def seedShift (ω : SeedHistory) : SeedHistory := fun j => ω (j + 1)

/-- The inverse shift `(S⁻¹ ω)_j = ω_{j-1}`. -/
def seedShiftInv (ω : SeedHistory) : SeedHistory := fun j => ω (j - 1)

theorem seedShift_seedShiftInv (ω : SeedHistory) : seedShift (seedShiftInv ω) = ω := by
  funext j; simp [seedShift, seedShiftInv]

theorem seedShiftInv_seedShift (ω : SeedHistory) : seedShiftInv (seedShift ω) = ω := by
  funext j; simp [seedShift, seedShiftInv]

theorem measurable_seedShift : Measurable seedShift :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j + 1)

theorem measurable_seedShiftInv : Measurable seedShiftInv :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j - 1)

theorem seedShift_iterate (N : ℕ) (ω : SeedHistory) (j : ℤ) :
    (seedShift^[N] ω) j = ω (j + N) := by
  induction N generalizing ω with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [seedShift]
    congr 1; push_cast; ring

/-! ### The inverse-transform sampler -/

section Sampler

variable {X : Type*} [MeasurableSpace X] (κ : Kernel X ℕ) [IsMarkovKernel κ]

/-- The cumulative masses `c_n(x) = κ_x({0, …, n-1})`. -/
def cumulative (x : X) (n : ℕ) : ℝ := (κ x (Set.Iio n)).toReal

omit [IsMarkovKernel κ] in
theorem cumulative_zero (x : X) : cumulative κ x 0 = 0 := by simp [cumulative]

theorem cumulative_succ (x : X) (n : ℕ) :
    cumulative κ x (n + 1) = cumulative κ x n + (κ x {n}).toReal := by
  have hset : Set.Iio (n + 1) = Set.Iio n ∪ {n} := by
    ext m; simp [le_iff_lt_or_eq]
  rw [cumulative, cumulative, hset, measure_union (by simp) (MeasurableSet.singleton n),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

theorem cumulative_mono (x : X) : Monotone (cumulative κ x) :=
  monotone_nat_of_le_succ fun n => by rw [cumulative_succ]; simp

omit [IsMarkovKernel κ] in
theorem cumulative_nonneg (x : X) (n : ℕ) : 0 ≤ cumulative κ x n := ENNReal.toReal_nonneg

theorem cumulative_le_one (x : X) (n : ℕ) : cumulative κ x n ≤ 1 := by
  rw [cumulative, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

theorem tendsto_cumulative (x : X) :
    Filter.Tendsto (cumulative κ x) Filter.atTop (nhds 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := κ x) (s := fun n : ℕ => Set.Iio n)
    (fun a b hab => Set.Iio_subset_Iio hab)
  rw [Set.iUnion_Iio, measure_univ] at h
  have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  rw [ENNReal.toReal_one] at this
  exact this

omit [IsMarkovKernel κ] in
theorem measurable_cumulative (n : ℕ) : Measurable fun x => cumulative κ x n :=
  (κ.measurable_coe measurableSet_Iio).ennreal_toReal

theorem exists_lt_cumulative (x : X) (u : Seed) : ∃ n, (u : ℝ) < cumulative κ x (n + 1) := by
  obtain ⟨n, hn⟩ := ((tendsto_cumulative κ x).eventually (lt_mem_nhds u.2.2)).exists_forall_of_atTop
  exact ⟨n, hn (n + 1) (Nat.le_succ n)⟩

open Classical in
/-- **`(RFDM.19)`** the inverse-transform sampler `G(x, u) = n ⟺ c_n(x) ≤ u < c_{n+1}(x)`. -/
def sampler (x : X) (u : Seed) : ℕ := Nat.find (exists_lt_cumulative κ x u)

theorem sampler_eq_iff (x : X) (u : Seed) (n : ℕ) :
    sampler κ x u = n ↔ cumulative κ x n ≤ u ∧ (u : ℝ) < cumulative κ x (n + 1) := by
  classical
  rw [sampler, Nat.find_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cumulative_zero]; exact u.2.1
    · have := h2 (n - 1) (Nat.sub_lt hn one_pos)
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn.ne')] at this
      exact not_lt.1 this
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun m hm => not_lt.2 ?_⟩
    exact (cumulative_mono κ x (Nat.succ_le_of_lt hm)).trans h1

theorem measurable_sampler : Measurable fun p : X × Seed => sampler κ p.1 p.2 := by
  refine measurable_to_countable' fun n => ?_
  have hset : (fun p : X × Seed => sampler κ p.1 p.2) ⁻¹' {n} =
      {p | cumulative κ p.1 n ≤ (p.2 : ℝ)} ∩ {p | (p.2 : ℝ) < cumulative κ p.1 (n + 1)} := by
    ext p; simp [sampler_eq_iff]
  rw [hset]
  have hu : Measurable fun p : X × Seed => (p.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  exact (measurableSet_le ((measurable_cumulative κ n).comp measurable_fst) hu).inter
    (measurableSet_lt hu ((measurable_cumulative κ (n + 1)).comp measurable_fst))

/-- **`(RFDM.20)`** `λ{u : G(x, u) = n} = κ_x(n)`: the sampler pushes `λ` to `κ_x`. -/
theorem seedLaw_map_sampler (x : X) : seedLaw.map (sampler κ x) = κ x := by
  have hmeas : Measurable (sampler κ x) := measurable_sampler κ |>.comp measurable_prodMk_left
  refine Measure.ext_of_singleton fun n => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.singleton n), seedLaw_apply]
  have himage : Subtype.val '' (sampler κ x ⁻¹' {n}) =
      Set.Ico (cumulative κ x n) (cumulative κ x (n + 1)) := by
    ext r
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, sampler_eq_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · rintro ⟨h1, h2⟩
      refine ⟨⟨r, (cumulative_nonneg κ x n).trans h1,
        h2.trans_le (cumulative_le_one κ x (n + 1))⟩, ⟨h1, h2⟩, rfl⟩
  rw [himage, Real.volume_Ico, cumulative_succ, add_sub_cancel_left,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Sampler

/-! ### Finite marginals of the seed history -/

/-- The seed coordinates `0, …, k` of `λ^ℤ` are independent uniforms. -/
theorem historyLaw_map_initial (k : ℕ) :
    historyLaw.map (fun ω (j : Fin (k + 1)) => ω ((j : ℕ) : ℤ)) =
      Measure.pi fun _ : Fin (k + 1) => seedLaw := by
  classical
  have hmeas : Measurable fun ω : SeedHistory => fun j : Fin (k + 1) => ω ((j : ℕ) : ℤ) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  let I : Finset ℤ :=
    (Finset.univ : Finset (Fin (k + 1))).image fun j : Fin (k + 1) => ((j : ℕ) : ℤ)
  let t : ℤ → Set Seed := fun i => if h : 0 ≤ i ∧ i.toNat < k + 1 then s ⟨i.toNat, h.2⟩ else
    Set.univ
  have ht : ∀ j : Fin (k + 1), t ((j : ℕ) : ℤ) = s j := fun j => by
    have h : 0 ≤ ((j : ℕ) : ℤ) ∧ ((j : ℕ) : ℤ).toNat < k + 1 :=
      ⟨by positivity, by have := j.isLt; simp only [Int.toNat_natCast]; omega⟩
    simp only [t, dif_pos h]
    exact congrArg s (Fin.ext (by simp))
  have hset : (fun ω : SeedHistory => fun j : Fin (k + 1) => ω ((j : ℕ) : ℤ)) ⁻¹'
      Set.univ.pi s = (I : Set ℤ).pi t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, I, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro hω i ⟨j, rfl⟩
      rw [ht]; exact hω j (Set.mem_univ j)
    · intro hω j _
      have := hω _ ⟨j, rfl⟩
      rwa [ht] at this
  have hinj : Set.InjOn (fun j : Fin (k + 1) => ((j : ℕ) : ℤ))
      ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))) :=
    fun a _ b _ h => by simpa [Fin.ext_iff] using h
  rw [hset, historyLaw, Measure.infinitePi_pi _ (fun i _ => by
      simp only [t]; split_ifs <;> first | exact hs _ | exact MeasurableSet.univ),
    Finset.prod_image hinj]
  exact Finset.prod_congr rfl fun j _ => by rw [ht]

/-- The seed coordinates `0` and `N ≠ 0` are independent uniforms. -/
theorem historyLaw_map_pair {N : ℤ} (hN : N ≠ 0) :
    historyLaw.map (fun ω => (ω 0, ω N)) = seedLaw.prod seedLaw := by
  classical
  have hmeas : Measurable fun ω : SeedHistory => (ω 0, ω N) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply N)
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply hmeas (hA.prod hB)]
  let t : ℤ → Set Seed := fun i => if i = 0 then A else if i = N then B else Set.univ
  have ht0 : t 0 = A := if_pos rfl
  have htN : t N = B := by simp [t, hN]
  have hset : (fun ω : SeedHistory => (ω 0, ω N)) ⁻¹' A ×ˢ B =
      (({0, N} : Finset ℤ) : Set ℤ).pi t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq, ht0, htN]
  rw [hset, historyLaw, Measure.infinitePi_pi _ (fun i _ => by
      simp only [t]; split_ifs <;> first | exact hA | exact hB | exact MeasurableSet.univ),
    Finset.prod_pair (Ne.symm hN), ht0, htN]

/-- Almost every seed history is nonperiodic. -/
theorem historyLaw_periodic_null {N : ℕ} (hN : 0 < N) :
    historyLaw {ω | seedShift^[N] ω = ω} = 0 := by
  have hdiag : MeasurableSet {p : Seed × Seed | p.1 = p.2} := by
    have : {p : Seed × Seed | p.1 = p.2} =
        (fun p : Seed × Seed => ((p.1 : ℝ), (p.2 : ℝ))) ⁻¹' Set.diagonal ℝ := by
      ext p; simp [Set.mem_diagonal_iff, Subtype.ext_iff]
    rw [this]
    exact isClosed_diagonal.measurableSet.preimage
      ((measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd))
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  refine measure_mono_null (t := (fun ω : SeedHistory => (ω 0, ω (N : ℤ))) ⁻¹'
    {p | p.1 = p.2}) (fun ω hω => ?_) ?_
  · simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have := congrFun hω 0
    rw [seedShift_iterate, zero_add] at this
    exact this.symm
  · rw [← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_pi_apply _)) hdiag,
      historyLaw_map_pair hNz, Measure.prod_apply hdiag]
    simp only [Set.preimage_setOf_eq]
    have : ∀ u : Seed, {v : Seed | u = v} = {u} := fun u => by ext; simp [eq_comm]
    simp only [this, seedLaw_singleton, lintegral_zero]

/-- The bilateral shift preserves `λ^ℤ`. -/
theorem historyLaw_map_seedShift : historyLaw.map seedShift = historyLaw := by
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => seedLaw) (Equiv.addRight (-1 : ℤ))
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => Seed) (Equiv.addRight (-1 : ℤ))) =
      seedShift := by
    funext ω j
    rw [MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : ℤ => Seed) (Equiv.addRight (-1 : ℤ)) ω (j + 1)
    simp only [Equiv.coe_addRight, add_neg_cancel_right] at this
    exact this
  rw [hfun] at h
  exact h

/-! ### Theorem 6.1: the reversible natural extension -/

section Dilation

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (κ : Kernel X ℕ)
  [IsMarkovKernel κ] (R : X → X)

/-- **`(RFDM.21)`** `𝒯(x, ω) = (Rx, Sω)`. -/
def dilationMap (z : X × SeedHistory) : X × SeedHistory := (R z.1, seedShift z.2)

/-- **`(RFDM.22)`** `𝒯⁻¹(x, ω) = (Rx, S⁻¹ω)`. -/
def dilationInv (z : X × SeedHistory) : X × SeedHistory := (R z.1, seedShiftInv z.2)

/-- **`(RFDM.21)`** the packet factor `Π(x, ω) = (x, G(x, ω_0))`. -/
def dilationPacket (z : X × SeedHistory) : X × ℕ := (z.1, sampler κ z.1 (z.2 0))

/-- The source law `δ_x ⊗ λ^ℤ` above the initial observer `x`. -/
def dilationSource : Kernel X (X × SeedHistory) :=
  Kernel.deterministic id measurable_id ×ₖ Kernel.const X historyLaw

instance : IsMarkovKernel (dilationSource (X := X)) := by unfold dilationSource; infer_instance

omit [MeasurableSingletonClass X] in
theorem dilationSource_apply (x : X) :
    dilationSource x = (Measure.dirac x).prod historyLaw := by
  rw [dilationSource, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply, id]

omit [MeasurableSingletonClass X] in
theorem measurable_dilationMap (hR : Measurable R) : Measurable (dilationMap R) :=
  (hR.comp measurable_fst).prodMk (measurable_seedShift.comp measurable_snd)

omit [MeasurableSingletonClass X] in
theorem measurable_dilationInv (hR : Measurable R) : Measurable (dilationInv R) :=
  (hR.comp measurable_fst).prodMk (measurable_seedShiftInv.comp measurable_snd)

omit [MeasurableSingletonClass X] in
theorem measurable_dilationPacket : Measurable (dilationPacket κ) :=
  measurable_fst.prodMk ((measurable_sampler κ).comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)))

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- **`(RFDM.22)`** `𝒯` is a bijection with inverse `(Rx, S⁻¹ω)`. -/
theorem dilation_inverse (hinv : ∀ x, R (R x) = x) :
    (∀ z, dilationInv R (dilationMap R z) = z) ∧ ∀ z, dilationMap R (dilationInv R z) = z :=
  ⟨fun z => by simp [dilationInv, dilationMap, hinv, seedShiftInv_seedShift],
    fun z => by simp [dilationInv, dilationMap, hinv, seedShift_seedShiftInv]⟩

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem dilationMap_iterate (j : ℕ) (z : X × SeedHistory) :
    (dilationMap R)^[j] z = (R^[j] z.1, seedShift^[j] z.2) := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [dilationMap, Function.iterate_succ_apply]

omit [MeasurableSingletonClass X] in
theorem dilationPacket_iterate (j : ℕ) (z : X × SeedHistory) :
    dilationPacket κ ((dilationMap R)^[j] z) = (R^[j] z.1, sampler κ (R^[j] z.1) (z.2 j)) := by
  rw [dilationMap_iterate, dilationPacket]
  simp only
  rw [seedShift_iterate, zero_add]

omit [MeasurableSingletonClass X] in
/-- **Theorem 6.1, `(RFDM.23)`**: above `x`, the packets along the dilation are independent with
laws `δ_{R^j x} ⊗ κ_{R^j x}`. -/
theorem dilation_fdd (hR : Measurable R) (x : X) (k : ℕ) :
    (dilationSource x).map (fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z)) =
      Measure.pi fun j : Fin (k + 1) => resetMarginal κ R x j := by
  have hg : ∀ j : Fin (k + 1), Measurable fun u : Seed =>
      ((R^[j] x, sampler κ (R^[j] x) u) : X × ℕ) := fun j =>
    measurable_const.prodMk ((measurable_sampler κ).comp (measurable_const.prodMk measurable_id))
  have hproj : Measurable fun ω : SeedHistory => fun j : Fin (k + 1) => ω ((j : ℕ) : ℤ) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hG : Measurable fun (v : Fin (k + 1) → Seed) (j : Fin (k + 1)) =>
      ((R^[j] x, sampler κ (R^[j] x) (v j)) : X × ℕ) :=
    measurable_pi_lambda _ fun j => (hg j).comp (measurable_pi_apply j)
  have hfun : (fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z)) ∘
      Prod.mk x = (fun (v : Fin (k + 1) → Seed) (j : Fin (k + 1)) =>
        ((R^[j] x, sampler κ (R^[j] x) (v j)) : X × ℕ)) ∘
        (fun ω (j : Fin (k + 1)) => ω ((j : ℕ) : ℤ)) := by
    funext ω j
    simp only [Function.comp_apply, dilationPacket_iterate]
  have hF : Measurable fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z) :=
    measurable_pi_lambda _ fun j =>
      (measurable_dilationPacket κ).comp ((measurable_dilationMap R hR).iterate j)
  rw [dilationSource_apply, Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left, hfun,
    ← Measure.map_map hG hproj, historyLaw_map_initial,
    Measure.pi_map_pi (f := fun (j : Fin (k + 1)) (u : Seed) =>
      ((R^[j] x, sampler κ (R^[j] x) u) : X × ℕ)) (fun j => (hg j).aemeasurable)]
  congr 1
  funext j
  have hmS : Measurable (sampler κ (R^[j] x)) :=
    (measurable_sampler κ).comp measurable_prodMk_left
  rw [resetMarginal, Measure.dirac_prod, ← seedLaw_map_sampler κ (R^[j] x),
    Measure.map_map measurable_prodMk_left hmS]
  rfl

/-- **Theorem 6.1**: for every observer law `μ`, under `μ ⊗ λ^ℤ` the factor process
`Π, Π𝒯, Π𝒯², …` has the finite-dimensional laws of the reset Markov process started from
`E_κ(μ)`. -/
theorem dilation_fdd_initialLaw (hR : Measurable R) (μ : Measure X) [IsProbabilityMeasure μ]
    (k : ℕ) :
    (μ.prod historyLaw).map
        (fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z)) =
      markovPath (splitFormation μ κ) (formationLiftKernel κ R hR) k := by
  have hF : Measurable fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z) :=
    measurable_pi_lambda _ fun j =>
      (measurable_dilationPacket κ).comp ((measurable_dilationMap R hR).iterate j)
  have hker : (Kernel.id ×ₖ Kernel.const X historyLaw).map
      (fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z)) =
        resetPathKernel κ R hR k := Kernel.ext fun x => by
    rw [Kernel.map_apply _ hF, resetPathKernel_apply, markovPath_reset]
    exact dilation_fdd κ R hR x k
  rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hF, hker,
    markovPath_splitFormation]

/-- **Theorem 6.1**: the bilateral dilation is a deterministic execution of the reset process. -/
def resetDilation (hR : Measurable R) (hinv : ∀ x, R (R x) = x) :
    ResetExecution κ R hR (X × SeedHistory) where
  T := dilationMap R
  measurable_T := measurable_dilationMap R hR
  bijective_T := by
    obtain ⟨h1, h2⟩ := dilation_inverse R hinv
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩
  packet := dilationPacket κ
  measurable_packet := measurable_dilationPacket κ
  source := dilationSource
  isMarkov_source := inferInstance
  fdd x k := by rw [markovPath_reset]; exact dilation_fdd κ R hR x k

omit [MeasurableSingletonClass X] in
/-- **Theorem 6.1, `(RFDM.23)`**: `Pr(H_0 = n_0, …, H_k = n_k | X_0 = x) = ∏_j κ_{R^j x}(n_j)`. -/
theorem dilation_history_law (hR : Measurable R) (x : X) (k : ℕ) (n : Fin (k + 1) → ℕ) :
    dilationSource x {z | ∀ j : Fin (k + 1), (dilationPacket κ ((dilationMap R)^[j] z)).2 = n j} =
      ∏ j : Fin (k + 1), κ (R^[j] x) {n j} := by
  have hF : Measurable fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z) :=
    measurable_pi_lambda _ fun j =>
      (measurable_dilationPacket κ).comp ((measurable_dilationMap R hR).iterate j)
  have hset : {z | ∀ j : Fin (k + 1), (dilationPacket κ ((dilationMap R)^[j] z)).2 = n j} =
      (fun z (j : Fin (k + 1)) => dilationPacket κ ((dilationMap R)^[j] z)) ⁻¹'
        Set.univ.pi fun j => Set.univ ×ˢ {n j} := by
    ext z; simp
  rw [hset, ← Measure.map_apply hF (MeasurableSet.univ_pi fun j =>
    MeasurableSet.univ.prod (MeasurableSet.singleton _)), dilation_fdd κ R hR, Measure.pi_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [resetMarginal, Measure.prod_prod, measure_univ, one_mul]

omit [MeasurableSingletonClass X] in
/-- The dilation acts on product laws by `μ ⊗ λ^ℤ ↦ R_*μ ⊗ λ^ℤ`. -/
theorem map_dilationMap_prod (hR : Measurable R) (μ : Measure X) [SFinite μ] :
    (μ.prod historyLaw).map (dilationMap R) = (μ.map R).prod historyLaw := by
  conv_rhs => rw [← historyLaw_map_seedShift]
  rw [Measure.map_prod_map μ historyLaw hR measurable_seedShift]
  rfl

omit [MeasurableSingletonClass X] in
/-- Under every law `μ ⊗ λ^ℤ` almost every lifted state has infinite `𝒯`-period. -/
theorem prod_historyLaw_periodic_null (μ : Measure X) [IsFiniteMeasure μ] {N : ℕ} (hN : 0 < N) :
    (μ.prod historyLaw) {z | (dilationMap R)^[N] z = z} = 0 := by
  refine measure_mono_null (t := Set.univ ×ˢ {ω | seedShift^[N] ω = ω}) (fun z hz => ?_) ?_
  · simp only [Set.mem_setOf_eq] at hz
    rw [dilationMap_iterate] at hz
    exact ⟨Set.mem_univ _, congrArg Prod.snd hz⟩
  · rw [Measure.prod_prod, historyLaw_periodic_null hN, mul_zero]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- **Theorem 6.1, `(RFDM.24)`**: `𝒯²(x, ω) = (x, S²ω)`; `𝒯` has infinite order and almost every
seed history is nonperiodic. -/
theorem dilation_open_history (hinv : ∀ x, R (R x) = x) :
    (∀ z : X × SeedHistory, (dilationMap R)^[2] z = (z.1, seedShift^[2] z.2)) ∧
      (∀ N, 0 < N → [Nonempty X] → (dilationMap R)^[N] ≠ id) ∧
      ∀ N, 0 < N → historyLaw {ω | seedShift^[N] ω = ω} = 0 := by
  refine ⟨fun z => by rw [dilationMap_iterate]; simp [hinv], fun N hN _ hper => ?_,
    fun N hN => historyLaw_periodic_null hN⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  let ω : SeedHistory := fun j => if j = 0 then ⟨0, by norm_num, by norm_num⟩ else
    ⟨1 / 2, by norm_num, by norm_num⟩
  have h := congrArg (fun z => (z.2 : SeedHistory) 0) (congrFun hper (x, ω))
  simp only [dilationMap_iterate, id_eq, seedShift_iterate, zero_add] at h
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [ω, if_neg hNz, if_pos rfl, Subtype.mk.injEq] at h
  norm_num at h

/-! ### Theorem 6.2: endpoint information neutrality survives the dilation -/

omit [MeasurableSingletonClass X] in
/-- **`(RFDM.25)`** `D(μ ⊗ λ^ℤ ‖ ν ⊗ λ^ℤ) = D(μ ‖ ν)`. -/
theorem klDiv_prod_historyLaw (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod historyLaw) (ν.prod historyLaw) = klDiv μ ν := by
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact klDiv_compProd_left μ ν _

omit [MeasurableSingletonClass X] in
/-- Two finite measures on `X × ℕ` agreeing on all rectangles `A × {n}` are equal. -/
theorem ext_prod_nat {μ₁ μ₂ : Measure (X × ℕ)}
    (h : ∀ A, MeasurableSet A → ∀ n, μ₁ (A ×ˢ {n}) = μ₂ (A ×ˢ {n})) : μ₁ = μ₂ := by
  ext s hs
  have hdec : s = ⋃ n : ℕ, ((fun x => (x, n)) ⁻¹' s) ×ˢ ({n} : Set ℕ) := by
    ext ⟨x, m⟩; simp
  have hmeas : ∀ n : ℕ, MeasurableSet (((fun x => (x, n)) ⁻¹' s) ×ˢ ({n} : Set ℕ)) := fun n =>
    (measurable_prodMk_right hs).prod (MeasurableSet.singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : ℕ => ((fun x => (x, n)) ⁻¹' s) ×ˢ ({n} : Set ℕ)) := fun a b hab =>
    Set.disjoint_prod.2 (Or.inr (Set.disjoint_singleton.2 hab))
  rw [hdec, measure_iUnion hdisj hmeas, measure_iUnion hdisj hmeas]
  exact tsum_congr fun n => h _ (measurable_prodMk_right hs) n

omit [MeasurableSingletonClass X] in
/-- **Theorem 6.2, `(RFDM.27)`**: `Π_*(μ ⊗ λ^ℤ) = E_κ(μ)`. -/
theorem map_dilationPacket (μ : Measure X) [IsFiniteMeasure μ] :
    (μ.prod historyLaw).map (dilationPacket κ) = splitFormation μ κ := by
  refine ext_prod_nat fun A hA n => ?_
  have hset : dilationPacket κ ⁻¹' A ×ˢ {n} =
      {z : X × SeedHistory | z.1 ∈ A ∧ sampler κ z.1 (z.2 0) = n} := by
    ext z; simp [dilationPacket]
  have hmeasS : MeasurableSet {z : X × SeedHistory | z.1 ∈ A ∧ sampler κ z.1 (z.2 0) = n} :=
    (measurable_fst hA).inter ((measurable_sampler κ).comp (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd)) (MeasurableSet.singleton n))
  rw [Measure.map_apply (measurable_dilationPacket κ) (hA.prod (MeasurableSet.singleton n)), hset,
    Measure.prod_apply hmeasS, splitFormation, Measure.compProd_apply_prod hA
      (MeasurableSet.singleton n), ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    have hpre : Prod.mk x ⁻¹' {z : X × SeedHistory | z.1 ∈ A ∧ sampler κ z.1 (z.2 0) = n} =
        Function.eval (0 : ℤ) ⁻¹' (sampler κ x ⁻¹' {n}) := by
      ext ω; simp [hx]
    have hmS : Measurable (sampler κ x) := (measurable_sampler κ).comp measurable_prodMk_left
    have h0 : historyLaw.map (fun f : SeedHistory => f 0) = seedLaw :=
      (measurePreserving_eval_infinitePi (fun _ : ℤ => seedLaw) 0).map_eq
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) (hmS (MeasurableSet.singleton n)), h0,
      ← Measure.map_apply hmS (MeasurableSet.singleton n), seedLaw_map_sampler]
  · rw [Set.indicator_of_notMem hx]
    have hpre : Prod.mk x ⁻¹' {z : X × SeedHistory | z.1 ∈ A ∧ sampler κ z.1 (z.2 0) = n} = ∅ := by
      ext ω; simp [hx]
    rw [hpre, measure_empty]

omit [MeasurableSingletonClass X] in
/-- **Theorem 6.2, `(RFDM.25)`–`(RFDM.28)`**: one common seed history supports exact endpoint
information neutrality and the infinite-order reversible execution. -/
theorem dilation_information_neutral (hR : Measurable R) (hinv : ∀ x, R (R x) = x)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.prod historyLaw) (ν.prod historyLaw) = klDiv μ ν ∧
      klDiv ((μ.prod historyLaw).map (dilationMap R)) ((ν.prod historyLaw).map (dilationMap R)) =
        klDiv μ ν ∧
      klDiv ((μ.prod historyLaw).map (dilationPacket κ))
          ((ν.prod historyLaw).map (dilationPacket κ)) = klDiv μ ν := by
  have hemb : MeasurableEmbedding (dilationMap R) := by
    obtain ⟨h1, h2⟩ := dilation_inverse R hinv
    exact MeasurableEmbedding.of_measurable_inverse (measurable_dilationMap R hR)
      (by
        have : Set.range (dilationMap R) = Set.univ :=
          Set.range_eq_univ.2 (Function.RightInverse.surjective h2)
        rw [this]; exact MeasurableSet.univ)
      (measurable_dilationInv R hR) (fun z => h1 z)
  refine ⟨klDiv_prod_historyLaw μ ν, ?_, ?_⟩
  · rw [klDiv_map_measurableEmbedding hemb, klDiv_prod_historyLaw]
  · rw [map_dilationPacket, map_dilationPacket, klDiv_splitFormation]

end Dilation

end GaloisForLFunctions.HTGeometry.ResetDilation
