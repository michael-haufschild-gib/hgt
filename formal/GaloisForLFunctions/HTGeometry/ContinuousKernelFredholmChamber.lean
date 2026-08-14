import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmSimplex

open Set MeasureTheory Filter
open scoped BigOperators

noncomputable section

theorem monotone_snoc {n : ℕ} {p : Fin n → ℝ} {x : ℝ}
    (hp : Monotone p) (hpx : ∀ i, p i ≤ x) :
    Monotone (Fin.snoc p x) := by
  intro i j hij
  by_cases hj : j = Fin.last n
  · subst j
    rw [Fin.snoc_last]
    by_cases hi : i = Fin.last n
    · subst i
      rw [Fin.snoc_last]
    · rw [← Fin.castSucc_castPred i hi, Fin.snoc_castSucc]
      exact hpx _
  · have hi : i ≠ Fin.last n := Fin.ne_last_of_lt
      (Fin.lt_of_le_of_lt hij (Fin.lt_last_iff_ne_last.mpr hj))
    rw [← Fin.castSucc_castPred i hi, ← Fin.castSucc_castPred j hj,
      Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hp (Fin.castPred_le_castPred hij hj)

theorem volume_apply_eq_apply_zero' {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    volume {x : Fin (n + 1) → ℝ | x i = x j} = 0 := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let T : Set (ℝ × (Fin n → ℝ)) := {p | p.1 = p.2 k}
  have hTmeas : MeasurableSet T := by
    exact measurableSet_eq_fun measurable_fst (measurable_pi_apply k |>.comp measurable_snd)
  have hTzero : volume T = 0 := by
    rw [show (volume : Measure (ℝ × (Fin n → ℝ))) =
        (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) by rfl]
    rw [Measure.measure_prod_null hTmeas]
    filter_upwards with x
    have hsection : Prod.mk x ⁻¹' T = {v : Fin n → ℝ | v k = x} := by
      ext v
      simp [T, eq_comm]
    rw [hsection, volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) k x
  have hpre := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).preimage_null hTzero
  have hset : e ⁻¹' T = {x : Fin (n + 1) → ℝ | x i = x j} := by
    ext x
    simp only [e, T, mem_preimage, mem_setOf_eq, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_symm_mk, Fin.removeNth_apply]
    rw [hk]
  rwa [hset] at hpre

theorem ae_injective_fin_tuple' (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂volume, Function.Injective x := by
  cases n with
  | zero =>
      exact ae_of_all _ fun x i => Fin.elim0 i
  | succ n =>
      have hpairs : ∀ᵐ x : Fin (n + 1) → ℝ ∂volume,
          ∀ i j, i ≠ j → x i ≠ x j := by
        rw [Filter.eventually_all]
        intro i
        rw [Filter.eventually_all]
        intro j
        by_cases hij : i = j
        · exact ae_of_all _ fun _ h => (h hij).elim
        · filter_upwards [compl_mem_ae_iff.2 (volume_apply_eq_apply_zero' i j hij)] with x hx
          intro _
          simpa using hx
      filter_upwards [hpairs] with x hx
      intro i j h
      by_contra hij
      exact hx i j hij h

def finCube (n : ℕ) (a : ℝ) : Set (Fin n → ℝ) :=
  Icc (fun _ => 0) (fun _ => a)

def orderedChamber (n : ℕ) (a : ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  finCube n a ∩ {x | Monotone (x ∘ σ)}

theorem measurableSet_orderedChamber (n : ℕ) (a : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (orderedChamber n a σ) := by
  apply measurableSet_Icc.inter
  rw [show {x : Fin n → ℝ | Monotone (x ∘ σ)} =
      ⋂ i : Fin n, ⋂ j : Fin n, {x | i ≤ j → x (σ i) ≤ x (σ j)} by
    ext x
    simp [Monotone, Function.comp_apply]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i ≤ j
  · simpa [hij] using measurableSet_le (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
  · simp [hij]

def permuteTuple {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  x ∘ σ

/-- Extend a permutation by fixing a new last coordinate. -/
def extendLastPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun i := Fin.lastCases (Fin.last n) (fun j => (σ j).castSucc) i
  invFun i := Fin.lastCases (Fin.last n) (fun j => (σ.symm j).castSucc) i
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

@[simp] theorem extendLastPerm_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    extendLastPerm σ (Fin.last n) = Fin.last n := by
  simp [extendLastPerm]

@[simp] theorem extendLastPerm_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLastPerm σ i.castSucc = (σ i).castSucc := by
  simp [extendLastPerm]

noncomputable def permuteMeasurableEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm

theorem coe_permuteMeasurableEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ⇑(permuteMeasurableEquiv σ) = permuteTuple σ := by
  funext x i
  rw [permuteMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft]
  simpa [permuteTuple, Function.comp_def] using
    (Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ.symm x (σ i))

theorem measurePreserving_permuteTuple {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteTuple σ) (volume : Measure (Fin n → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  rwa [show MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm =
      permuteMeasurableEquiv σ by rfl, coe_permuteMeasurableEquiv] at h

theorem permuteTuple_mem_finCube_iff {n : ℕ} (a : ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    permuteTuple σ x ∈ finCube n a ↔ x ∈ finCube n a := by
  simp only [finCube, mem_Icc, Pi.le_def, permuteTuple, Function.comp_apply]
  constructor
  · intro h
    constructor
    · intro i
      simpa using h.1 (σ.symm i)
    · intro i
      simpa using h.2 (σ.symm i)
  · intro h
    exact ⟨fun i => h.1 (σ i), fun i => h.2 (σ i)⟩

theorem exists_unique_monotone_permutation {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) :
    ∃! σ : Equiv.Perm (Fin n), Monotone (x ∘ σ) := by
  refine ⟨Tuple.sort x, Tuple.monotone_sort x, ?_⟩
  intro σ hσ
  apply Equiv.ext
  intro i
  apply hx
  exact congrFun (Tuple.unique_monotone hσ (Tuple.monotone_sort x)) i

theorem sum_chamber_indicator_eq_cube_indicator {n : ℕ} (a : ℝ)
    (f : (Fin n → ℝ) → ℂ) {x : Fin n → ℝ} (hx : Function.Injective x) :
    (∑ σ : Equiv.Perm (Fin n), (orderedChamber n a σ).indicator f x) =
      (finCube n a).indicator f x := by
  by_cases hcube : x ∈ finCube n a
  · obtain ⟨σ, hσ, huniq⟩ := exists_unique_monotone_permutation x hx
    rw [Finset.sum_eq_single σ]
    · simp [orderedChamber, hcube, hσ]
    · intro τ hτ hτσ
      have hnmono : ¬Monotone (x ∘ τ) := fun h => hτσ (huniq τ h)
      simp [orderedChamber, hnmono]
    · intro hσmem
      simp at hσmem
  · have hnone : ∀ σ : Equiv.Perm (Fin n), x ∉ orderedChamber n a σ := by
      intro σ hxσ
      exact hcube hxσ.1
    rw [indicator_of_notMem hcube]
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [indicator_of_notMem (hnone σ)]

theorem integral_cube_eq_sum_chambers {n : ℕ} {a : ℝ} (_ha : 0 ≤ a)
    (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) :
    ∫ x in finCube n a, f x =
      ∑ σ : Equiv.Perm (Fin n), ∫ x in orderedChamber n a σ, f x := by
  have hcompact : IsCompact (finCube n a) := isCompact_Icc
  have hfint : IntegrableOn f (finCube n a) := hf.continuousOn.integrableOn_compact hcompact
  have hchint : ∀ σ : Equiv.Perm (Fin n), IntegrableOn f (orderedChamber n a σ) := by
    intro σ
    exact hfint.mono_set inter_subset_left
  have hcubeMeas : MeasurableSet (finCube n a) := measurableSet_Icc
  rw [← integral_indicator hcubeMeas]
  simp_rw [← integral_indicator (measurableSet_orderedChamber n a _)]
  rw [← integral_finsetSum Finset.univ (fun σ _ => (hchint σ).integrable_indicator
    (measurableSet_orderedChamber n a σ))]
  apply integral_congr_ae
  filter_upwards [ae_injective_fin_tuple' n] with x hx
  simpa only [Finset.sum_apply] using (sum_chamber_indicator_eq_cube_indicator a f hx).symm

theorem integral_orderedChamber_eq_identity {n : ℕ} (a : ℝ)
    (f : (Fin n → ℝ) → ℂ)
    (hsym : ∀ σ : Equiv.Perm (Fin n), ∀ x, f (permuteTuple σ x) = f x)
    (σ : Equiv.Perm (Fin n)) :
    ∫ x in orderedChamber n a σ, f x =
      ∫ x in orderedChamber n a (Equiv.refl _), f x := by
  let e := permuteMeasurableEquiv σ
  let g : (Fin n → ℝ) → ℂ := (orderedChamber n a (Equiv.refl _)).indicator f
  have hepres : MeasurePreserving (⇑e) (volume : Measure (Fin n → ℝ)) volume := by
    change MeasurePreserving (⇑(permuteMeasurableEquiv σ)) volume volume
    rw [coe_permuteMeasurableEquiv]
    exact measurePreserving_permuteTuple σ
  have hcomp := hepres.integral_comp' g
  have hpoint : ∀ x : Fin n → ℝ,
      g (e x) = (orderedChamber n a σ).indicator f x := by
    intro x
    have heval : e x = permuteTuple σ x := by
      exact congrFun (coe_permuteMeasurableEquiv σ) x
    have hmem : e x ∈ orderedChamber n a (Equiv.refl _) ↔
        x ∈ orderedChamber n a σ := by
      rw [heval]
      simp only [orderedChamber, mem_inter_iff, permuteTuple_mem_finCube_iff,
        Equiv.coe_refl, Function.comp_id]
      rfl
    by_cases hx : x ∈ orderedChamber n a σ
    · dsimp [g]
      rw [indicator_of_mem hx, indicator_of_mem (hmem.2 hx), heval, hsym]
    · dsimp [g]
      rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [← integral_indicator (measurableSet_orderedChamber n a σ),
    ← integral_indicator (measurableSet_orderedChamber n a (Equiv.refl _))]
  calc
    (∫ x, (orderedChamber n a σ).indicator f x) = ∫ x, g (e x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (hpoint x).symm
    _ = ∫ x, g x := hcomp

theorem integral_cube_eq_factorial_mul_identity_chamber {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f : (Fin n → ℝ) → ℂ) (hf : Continuous f)
    (hsym : ∀ σ : Equiv.Perm (Fin n), ∀ x, f (permuteTuple σ x) = f x) :
    ∫ x in finCube n a, f x =
      (n.factorial : ℂ) * ∫ x in orderedChamber n a (Equiv.refl _), f x := by
  rw [integral_cube_eq_sum_chambers ha f hf]
  simp_rw [integral_orderedChamber_eq_identity a f hsym]
  simp [Fintype.card_perm]

namespace ContinuousKernelFredholm

theorem cubeIntervalIntegral_eq_setIntegral
    (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) :
    cubeIntervalIntegral n a f = ∫ x in finCube n a, f x := by
  induction n with
  | zero =>
      have hset : finCube 0 a = (Set.univ : Set (Fin 0 → ℝ)) := by
        ext x
        simp [finCube]
      have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun i => Fin.elim0 i) := by
        rw [volume_pi, Measure.pi_of_empty]
        congr
      rw [hset, hvol]
      simp [cubeIntervalIntegral]
  | succ n ih =>
      rw [cubeIntervalIntegral]
      have hinner : ∀ t : ℝ,
          cubeIntervalIntegral n a (fun v => f (Fin.cons t v)) =
            ∫ v in finCube n a, f (Fin.cons t v) := by
        intro t
        apply ih
        apply hf.comp
        fun_prop
      simp_rw [hinner]
      rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let F : ℝ × (Fin n → ℝ) → ℂ := fun p => f (Fin.cons p.1 p.2)
      have hFcont : Continuous F := by
        apply hf.comp
        fun_prop
      have hprodCompact : IsCompact (Icc (0 : ℝ) a ×ˢ finCube n a) :=
        isCompact_Icc.prod isCompact_Icc
      have hFint : IntegrableOn F (Icc (0 : ℝ) a ×ˢ finCube n a) :=
        hFcont.continuousOn.integrableOn_compact hprodCompact
      have hFubini := setIntegral_prod F hFint
      rw [← Measure.volume_eq_prod] at hFubini
      rw [← hFubini]
      have hprodMeas : MeasurableSet (Icc (0 : ℝ) a ×ˢ finCube n a) :=
        measurableSet_Icc.prod measurableSet_Icc
      have hcubeMeas : MeasurableSet (finCube n.succ a) := measurableSet_Icc
      rw [← integral_indicator hprodMeas, ← integral_indicator hcubeMeas]
      have hepres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hcomp := hepres.integral_comp'
        ((Icc (0 : ℝ) a ×ˢ finCube n a).indicator F)
      rw [← hcomp]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        have heval : e x = (x 0, fun j => x j.succ) := by
          apply Prod.ext
          · rfl
          · funext j
            rfl
        have hmem : x ∈ finCube n.succ a ↔ e x ∈ Icc (0 : ℝ) a ×ˢ finCube n a := by
          rw [heval]
          simp only [finCube, mem_Icc, Pi.le_def, mem_prod]
          constructor
          · intro h
            exact ⟨⟨h.1 0, h.2 0⟩,
              ⟨fun j => h.1 j.succ, fun j => h.2 j.succ⟩⟩
          · intro h
            constructor
            · intro i
              refine Fin.cases h.1.1 (fun j => h.2.1 j) i
            · intro i
              refine Fin.cases h.1.2 (fun j => h.2.2 j) i
        by_cases hx : x ∈ finCube n.succ a
        · change (Icc (0 : ℝ) a ×ˢ finCube n a).indicator F (e x) =
            (finCube n.succ a).indicator f x
          rw [indicator_of_mem hx, indicator_of_mem (hmem.1 hx), heval]
          apply congrArg f
          funext i
          exact Fin.cases rfl (fun j => rfl) i
        · change (Icc (0 : ℝ) a ×ˢ finCube n a).indicator F (e x) =
            (finCube n.succ a).indicator f x
          rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.2 h))]

theorem orderedSimplexIntegral_eq_setIntegral
    (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) :
    orderedSimplexIntegral n a f =
      ∫ x in orderedChamber n a (Equiv.refl _), f x := by
  induction n generalizing a with
  | zero =>
      have hset : orderedChamber 0 a (Equiv.refl _) =
          (Set.univ : Set (Fin 0 → ℝ)) := by
        ext x
        simp only [orderedChamber, finCube, mem_inter_iff, mem_Icc, Pi.le_def,
          Equiv.coe_refl, Function.comp_id, mem_univ, iff_true]
        exact ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
          fun i => Fin.elim0 i⟩
      have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun i => Fin.elim0 i) := by
        rw [volume_pi, Measure.pi_of_empty]
        congr
      rw [hset, hvol]
      simp [orderedSimplexIntegral]
  | succ n ih =>
      rw [orderedSimplexIntegral]
      rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
      have hinner : ∀ t ∈ Icc (0 : ℝ) a,
          orderedSimplexIntegral n t (fun v => f (Fin.snoc v t)) =
            ∫ v in orderedChamber n t (Equiv.refl _), f (Fin.snoc v t) := by
        intro t ht
        apply ih ht.1
        apply hf.comp
        fun_prop
      apply Eq.trans (setIntegral_congr_fun measurableSet_Icc hinner)
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
      let S : Set (ℝ × (Fin n → ℝ)) :=
        {p | p.1 ∈ Icc (0 : ℝ) a ∧ p.2 ∈ orderedChamber n p.1 (Equiv.refl _)}
      let F : ℝ × (Fin n → ℝ) → ℂ := fun p => f (Fin.snoc p.2 p.1)
      have hevalSymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.snoc p.2 p.1 := by
        intro p
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      have hSpre : S = e.symm ⁻¹' orderedChamber n.succ a (Equiv.refl _) := by
        ext p
        rw [mem_preimage, hevalSymm]
        simp only [S, mem_setOf_eq, orderedChamber, mem_inter_iff, finCube, mem_Icc,
          Pi.le_def, Equiv.coe_refl, Function.comp_id]
        constructor
        · intro h
          constructor
          · constructor
            · intro i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simpa using h.1.1
              · simpa using h.2.1.1 j
            · intro i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simpa using h.1.2
              · simpa using (h.2.1.2 j).trans h.1.2
          · exact monotone_snoc h.2.2 h.2.1.2
        · intro h
          have hlast0 := h.1.1 (Fin.last n)
          have hlasta := h.1.2 (Fin.last n)
          have hvBounds : p.2 ∈ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => p.1) := by
            constructor
            · intro j
              simpa using h.1.1 j.castSucc
            · intro j
              simpa using h.2 (Fin.le_last j.castSucc)
          have hlast0' : 0 ≤ p.1 := by simpa using hlast0
          have hlasta' : p.1 ≤ a := by simpa using hlasta
          refine ⟨⟨hlast0', hlasta'⟩, ?_⟩
          refine ⟨?_, ?_⟩
          · exact hvBounds
          · intro i j hij
            simpa using h.2 (Fin.castSucc_le_castSucc_iff.mpr hij)
      have hSmeas : MeasurableSet S := by
        rw [hSpre]
        exact (measurableSet_orderedChamber n.succ a (Equiv.refl _)).preimage e.symm.measurable
      have hFcont : Continuous F := by
        apply hf.comp
        fun_prop
      have hSsub : S ⊆ Icc (0 : ℝ) a ×ˢ finCube n a := by
        intro p hp
        refine ⟨hp.1, ?_⟩
        rcases hp.2.1 with ⟨hv0, hvt⟩
        exact ⟨hv0, fun j => (hvt j).trans hp.1.2⟩
      have hprodCompact : IsCompact (Icc (0 : ℝ) a ×ˢ finCube n a) :=
        isCompact_Icc.prod isCompact_Icc
      have hSint : IntegrableOn F S :=
        (hFcont.continuousOn.integrableOn_compact hprodCompact).mono_set hSsub
      have hSind : Integrable (S.indicator F) volume := hSint.integrable_indicator hSmeas
      have hFubini := integral_prod (S.indicator F) (by
        rwa [← Measure.volume_eq_prod])
      rw [← Measure.volume_eq_prod] at hFubini
      have hiter :
          (∫ t in Icc (0 : ℝ) a,
            ∫ v in orderedChamber n t (Equiv.refl _), f (Fin.snoc v t)) =
            ∫ t : ℝ, ∫ v : Fin n → ℝ, S.indicator F (t, v) := by
        rw [← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        exact ae_of_all _ fun t => by
          by_cases ht : t ∈ Icc (0 : ℝ) a
          · rw [indicator_of_mem ht,
              ← integral_indicator (measurableSet_orderedChamber n t (Equiv.refl _))]
            apply integral_congr_ae
            exact ae_of_all _ fun v => by
              by_cases hv : v ∈ orderedChamber n t (Equiv.refl _)
              · rw [indicator_of_mem hv]
                change f (Fin.snoc v t) = S.indicator F (t, v)
                rw [indicator_of_mem (show (t, v) ∈ S from ⟨ht, hv⟩)]
              · rw [indicator_of_notMem hv]
                change 0 = S.indicator F (t, v)
                rw [indicator_of_notMem (fun hp : (t, v) ∈ S => hv hp.2)]
          · rw [indicator_of_notMem ht]
            symm
            apply integral_eq_zero_of_ae
            exact ae_of_all _ fun v => by
              change S.indicator F (t, v) = 0
              exact indicator_of_notMem (fun hp : (t, v) ∈ S => ht hp.1) F
      rw [hiter, ← hFubini]
      rw [← integral_indicator (measurableSet_orderedChamber n.succ a (Equiv.refl _))]
      have hepres := volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
      have hcomp := hepres.integral_comp' (S.indicator F)
      rw [← hcomp]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        have hmem : e x ∈ S ↔ x ∈ orderedChamber n.succ a (Equiv.refl _) := by
          rw [hSpre]
          change e.symm (e x) ∈ orderedChamber n.succ a (Equiv.refl _) ↔ _
          rw [e.symm_apply_apply]
        have hF : F (e x) = f x := by
          have heval : e x = (x (Fin.last n), fun j => x j.castSucc) := by
            apply Prod.ext
            · rfl
            · funext j
              change Fin.removeNth (Fin.last n) x j = x j.castSucc
              rw [Fin.removeNth_last]
              rfl
          rw [heval]
          apply congrArg f
          funext i
          refine Fin.lastCases (by simp) (fun j => by simp) i
        by_cases hx : x ∈ orderedChamber n.succ a (Equiv.refl _)
        · change S.indicator F (e x) =
            (orderedChamber n.succ a (Equiv.refl _)).indicator f x
          rw [indicator_of_mem hx, indicator_of_mem (hmem.2 hx), hF]
        · change S.indicator F (e x) =
            (orderedChamber n.succ a (Equiv.refl _)).indicator f x
          rw [indicator_of_notMem hx,
            indicator_of_notMem (fun h => hx (hmem.1 h))]

theorem continuous_fredholmIntegrand
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry) (n : ℕ) :
    Continuous (fredholmIntegrand K n) := by
  change Continuous (fun x : Fin n → ℝ =>
    Matrix.det (fun i j : Fin n => K (x i) (x j)))
  apply Continuous.matrix_det
  fun_prop

theorem fredholmIntegrand_permuteTuple
    (K : ℝ → ℝ → ℂ) (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    fredholmIntegrand K n (permuteTuple σ x) = fredholmIntegrand K n x := by
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => K (x i) (x j)
  have hreindex : Matrix.reindex σ.symm σ.symm A =
      fun i j => K (x (σ i)) (x (σ j)) := by
    ext i j
    simp [A, Matrix.reindex_apply]
  rw [fredholmIntegrand, permuteTuple]
  change Matrix.det (fun i j => K (x (σ i)) (x (σ j))) = Matrix.det A
  rw [← hreindex, Matrix.det_reindex_self]

theorem cubeIntervalIntegral_eq_factorial_mul_orderedSimplexIntegral
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    cubeIntervalIntegral n a (fredholmIntegrand K n) =
      (n.factorial : ℂ) * orderedSimplexIntegral n a (fredholmIntegrand K n) := by
  rw [cubeIntervalIntegral_eq_setIntegral n ha _ (continuous_fredholmIntegrand K hK n)]
  rw [integral_cube_eq_factorial_mul_identity_chamber ha _
    (continuous_fredholmIntegrand K hK n)
    (fredholmIntegrand_permuteTuple K n)]
  rw [orderedSimplexIntegral_eq_setIntegral n ha _ (continuous_fredholmIntegrand K hK n)]

theorem fredholmCoefficient_eq_orderedFredholmCoefficient
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    fredholmCoefficient K a n = orderedFredholmCoefficient K a n := by
  rw [fredholmCoefficient, orderedFredholmCoefficient,
    cubeIntervalIntegral_eq_factorial_mul_orderedSimplexIntegral K hK n ha]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

theorem determinant_eq_orderedDeterminant
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry) {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    determinant K a z = orderedDeterminant K a z := by
  apply tsum_congr
  intro n
  rw [fredholmCoefficient_eq_orderedFredholmCoefficient K hK n ha]

/-- Cube/factorial coefficient of the first Fredholm minor. -/
noncomputable def fredholmMinorCoefficient
    (K : ℝ → ℝ → ℂ) (a : ℝ) (n : ℕ) (x y : ℝ) : ℂ :=
  cubeIntervalIntegral n a (fredholmMinorIntegrand K n x y) / (n.factorial : ℂ)

/-- Literal cube-series first Fredholm minor. -/
noncomputable def fredholmMinor
    (K : ℝ → ℝ → ℂ) (a : ℝ) (z : ℂ) (x y : ℝ) : ℂ :=
  ∑' n : ℕ, z ^ n * fredholmMinorCoefficient K a n x y

/-- Continuity of a first-minor integrand in its integration variables. -/
theorem continuous_fredholmMinorIntegrand_fixed
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    (n : ℕ) (x y : ℝ) :
    Continuous (fredholmMinorIntegrand K n x y) := by
  change Continuous ((fun p : (ℝ × ℝ) × (Fin n → ℝ) =>
    fredholmMinorIntegrand K n p.1.1 p.1.2 p.2) ∘
      fun t : Fin n → ℝ => ((x, y), t))
  exact (continuous_fredholmMinorIntegrand K hK n).comp (by fun_prop)

/-- Simultaneously permuting internal rows and columns preserves a first-minor integrand. -/
theorem fredholmMinorIntegrand_permuteTuple
    (K : ℝ → ℝ → ℂ) (n : ℕ) (x y : ℝ)
    (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) :
    fredholmMinorIntegrand K n x y (permuteTuple σ t) =
      fredholmMinorIntegrand K n x y t := by
  let τ : Equiv.Perm (Fin (n + 1)) := extendLastPerm σ
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
    K (@Fin.snoc n (fun _ => ℝ) t x i) (@Fin.snoc n (fun _ => ℝ) t y j)
  have hτlast : τ (Fin.last n) = Fin.last n := by
    simp [τ]
  have hτcast (i : Fin n) : τ i.castSucc = (σ i).castSucc := by
    simp [τ]
  have hreindex : Matrix.reindex τ.symm τ.symm A =
      fun i j => K
        (@Fin.snoc n (fun _ => ℝ) (permuteTuple σ t) x i)
        (@Fin.snoc n (fun _ => ℝ) (permuteTuple σ t) y j) := by
    ext i j
    refine Fin.lastCases ?_ (fun r => ?_) i
    · refine Fin.lastCases ?_ (fun s => ?_) j
      · simp [A, Matrix.reindex_apply, hτlast]
      · simp [A, Matrix.reindex_apply, hτlast, hτcast, permuteTuple]
    · refine Fin.lastCases ?_ (fun s => ?_) j
      · simp [A, Matrix.reindex_apply, hτlast, hτcast, permuteTuple]
      · simp [A, Matrix.reindex_apply, hτcast, permuteTuple]
  rw [fredholmMinorIntegrand]
  change Matrix.det (fun i j => K
    (@Fin.snoc n (fun _ => ℝ) (permuteTuple σ t) x i)
    (@Fin.snoc n (fun _ => ℝ) (permuteTuple σ t) y j)) = Matrix.det A
  rw [← hreindex, Matrix.det_reindex_self]

/-- Cube and ordered-simplex first-minor coefficients agree for continuous kernels. -/
theorem fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    fredholmMinorCoefficient K a n x y =
      orderedFredholmMinorCoefficient K a n x y := by
  rw [fredholmMinorCoefficient, orderedFredholmMinorCoefficient]
  rw [cubeIntervalIntegral_eq_setIntegral n ha _
    (continuous_fredholmMinorIntegrand_fixed K hK n x y)]
  rw [integral_cube_eq_factorial_mul_identity_chamber ha _
    (continuous_fredholmMinorIntegrand_fixed K hK n x y)
    (fredholmMinorIntegrand_permuteTuple K n x y)]
  rw [orderedSimplexIntegral_eq_setIntegral n ha _
    (continuous_fredholmMinorIntegrand_fixed K hK n x y)]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- Literal cube and ordered-simplex first-minor series agree. -/
theorem fredholmMinor_eq_orderedFredholmMinor
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    {a : ℝ} (ha : 0 ≤ a) (z : ℂ) (x y : ℝ) :
    fredholmMinor K a z x y = orderedFredholmMinor K a z x y := by
  apply tsum_congr
  intro n
  rw [fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient K hK n ha]

/-- Moving-aperture derivative of the literal cube-series Fredholm determinant.  The chamber
decomposition above proves that this is the same determinant as the ordered-simplex series; the
derivative is therefore the diagonal first Fredholm minor, without defining either object through
the desired differential equation. -/
theorem hasDerivAt_determinant
    (K : ℝ → ℝ → ℂ) (hKcont : Continuous K.uncurry)
    {a A M : ℝ} (ha : 0 < a) (haA : a < A) (hM : 0 ≤ M)
    (hK : ∀ x ∈ Icc (0 : ℝ) A, ∀ y ∈ Icc (0 : ℝ) A, ‖K x y‖ ≤ M)
    (z : ℂ) :
    HasDerivAt (fun u : ℝ => determinant K u z)
      (z * orderedFredholmMinor K a z a a) a := by
  have hordered := hasDerivAt_orderedDeterminant K hKcont ha haA hM hK z
  apply hordered.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with u hu
  exact determinant_eq_orderedDeterminant K hKcont hu.le z

def moveToLastPerm {n : ℕ} (k : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  k.cycleRange.symm * (Fin.last n).cycleRange

@[simp] theorem moveToLastPerm_last {n : ℕ} (k : Fin (n + 1)) :
    moveToLastPerm k (Fin.last n) = k := by
  simp [moveToLastPerm]

@[simp] theorem moveToLastPerm_castSucc {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    moveToLastPerm k i.castSucc = k.succAbove i := by
  rw [moveToLastPerm, show i.castSucc = (Fin.last n).succAbove i by simp]
  change k.cycleRange.symm
    ((Fin.last n).cycleRange ((Fin.last n).succAbove i)) = k.succAbove i
  rw [Fin.cycleRange_succAbove, Fin.cycleRange_symm_succ]
theorem reindex_fredholmMinorCofactor (K : ℝ → ℝ → ℂ) {n : ℕ} (x y : ℝ)
    (t : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := fun i j ↦
      K (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t x i)
        (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t y j)
    let C := A.submatrix (Fin.last (n + 1)).succAbove k.castSucc.succAbove
    let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j ↦
      K (@Fin.snoc n (fun _ ↦ ℝ) (Fin.removeNth k t) (t k) i)
        (@Fin.snoc n (fun _ ↦ ℝ) (Fin.removeNth k t) y j)
    Matrix.reindex (moveToLastPerm k).symm (Equiv.refl _) C = B := by
  dsimp only
  ext i j
  refine Fin.lastCases ?_ (fun r ↦ ?_) i
  · refine Fin.lastCases ?_ (fun s ↦ ?_) j
    · simp [Matrix.reindex_apply]
    · simp [Matrix.reindex_apply, Fin.removeNth]
  · refine Fin.lastCases ?_ (fun s ↦ ?_) j
    · simp [Matrix.reindex_apply, Fin.removeNth]
    · simp [Matrix.reindex_apply, Fin.removeNth]

theorem det_fredholmMinorCofactor (K : ℝ → ℝ → ℂ) {n : ℕ} (x y : ℝ)
    (t : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := fun i j ↦
      K (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t x i)
        (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t y j)
    Matrix.det (A.submatrix (Fin.last (n + 1)).succAbove k.castSucc.succAbove) =
      (-1 : ℂ) ^ ((k : ℕ) + n) *
        fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t) := by
  dsimp only
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := fun i j ↦
    K (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t x i)
      (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t y j)
  let C := A.submatrix (Fin.last (n + 1)).succAbove k.castSucc.succAbove
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j ↦
    K (@Fin.snoc n (fun _ ↦ ℝ) (Fin.removeNth k t) (t k) i)
      (@Fin.snoc n (fun _ ↦ ℝ) (Fin.removeNth k t) y j)
  have hmatrix : Matrix.reindex (moveToLastPerm k).symm (Equiv.refl _) C = B := by
    exact reindex_fredholmMinorCofactor K x y t k
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_reindex] at hdet
  have hsign :
      ((Equiv.Perm.sign (moveToLastPerm k) : ℤˣ) : ℂ) =
        (-1 : ℂ) ^ ((k : ℕ) + n) := by
    rw [moveToLastPerm]
    rw [map_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Fin.sign_cycleRange]
    norm_num [pow_add]
  change Matrix.det C = _
  change ((Equiv.Perm.sign (moveToLastPerm k) : ℤˣ) : ℂ) * Matrix.det C =
    Matrix.det B at hdet
  rw [hsign] at hdet
  rw [fredholmMinorIntegrand]
  change Matrix.det C = _ * Matrix.det B
  calc
    Matrix.det C = ((-1 : ℂ) ^ ((k : ℕ) + n)) ^ 2 * Matrix.det C := by
      rw [show ((-1 : ℂ) ^ ((k : ℕ) + n)) ^ 2 = 1 by
        rw [← pow_mul]; norm_num]
      simp
    _ = (-1 : ℂ) ^ ((k : ℕ) + n) * Matrix.det B := by
      rw [← hdet]
      ring

theorem fredholmMinorIntegrand_succ_laplace
    (K : ℝ → ℝ → ℂ) (n : ℕ) (x y : ℝ) (t : Fin (n + 1) → ℝ) :
    fredholmMinorIntegrand K (n + 1) x y t =
      K x y * fredholmIntegrand K (n + 1) t -
        ∑ k : Fin (n + 1),
          K x (t k) * fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t) := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := fun i j ↦
    K (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t x i)
      (@Fin.snoc (n + 1) (fun _ ↦ ℝ) t y j)
  rw [fredholmMinorIntegrand]
  change Matrix.det A = _
  rw [Matrix.det_succ_row A (Fin.last (n + 1)), Fin.sum_univ_castSucc]
  have hinternal (k : Fin (n + 1)) :
      (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (k.castSucc : ℕ)) *
          A (Fin.last (n + 1)) k.castSucc *
          Matrix.det (A.submatrix (Fin.last (n + 1)).succAbove
            k.castSucc.succAbove) =
        - (K x (t k) * fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) := by
    rw [det_fredholmMinorCofactor K x y t k]
    have hsign :
        (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (k.castSucc : ℕ)) *
            (-1 : ℂ) ^ ((k : ℕ) + n) = -1 := by
      rw [← pow_add]
      have hexp :
          ((Fin.last (n + 1) : ℕ) + (k.castSucc : ℕ)) + ((k : ℕ) + n) =
            2 * (n + (k : ℕ)) + 1 := by
        simp only [Fin.val_last, Fin.val_castSucc]
        omega
      rw [hexp, pow_succ, pow_mul]
      norm_num
    simp only [A, Fin.snoc_last, Fin.snoc_castSucc]
    calc
      (-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (k.castSucc : ℕ)) * K x (t k) *
          ((-1 : ℂ) ^ ((k : ℕ) + n) *
            fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) =
          ((-1 : ℂ) ^ ((Fin.last (n + 1) : ℕ) + (k.castSucc : ℕ)) *
            (-1 : ℂ) ^ ((k : ℕ) + n)) *
              (K x (t k) * fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) := by
            ac_rfl
      _ = _ := by rw [hsign]; simp
  have hlast :
      (-1 : ℂ) ^
          ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) *
          A (Fin.last (n + 1)) (Fin.last (n + 1)) *
          Matrix.det (A.submatrix (Fin.last (n + 1)).succAbove
            (Fin.last (n + 1)).succAbove) =
        K x y * fredholmIntegrand K (n + 1) t := by
    rw [fredholmIntegrand]
    have hsub : A.submatrix (Fin.last (n + 1)).succAbove
        (Fin.last (n + 1)).succAbove =
          fun i j : Fin (n + 1) ↦ K (t i) (t j) := by
      ext i j
      simp [A]
    rw [hsub]
    simp only [A, Fin.snoc_last]
    have heven :
        ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) =
          2 * (n + 1) := by
      simp only [Fin.val_last]
      omega
    rw [heven, pow_mul]
    norm_num
  rw [hlast]
  rw [Finset.sum_congr rfl (fun k _ ↦ hinternal k)]
  rw [Finset.sum_neg_distrib]
  ring

/-- Fubini after extracting any selected coordinate of a finite cube. -/
theorem cubeIntervalIntegral_removeNth
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (k : Fin (n + 1))
    (f : ℝ → (Fin n → ℝ) → ℂ)
    (hf : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ f p.1 p.2)) :
    cubeIntervalIntegral (n + 1) a
        (fun t ↦ f (t k) (Fin.removeNth k t)) =
      ∫ u in (0 : ℝ)..a, cubeIntervalIntegral n a (f u) := by
  have hsourceCont : Continuous (fun t : Fin (n + 1) → ℝ ↦
      f (t k) (Fin.removeNth k t)) := by
    change Continuous ((fun p : ℝ × (Fin n → ℝ) ↦ f p.1 p.2) ∘
      fun t : Fin (n + 1) → ℝ ↦ (t k, Fin.removeNth k t))
    apply hf.comp
    apply Continuous.prodMk (continuous_apply k)
    apply continuous_pi
    intro i
    exact continuous_apply (k.succAbove i)
  rw [cubeIntervalIntegral_eq_setIntegral (n + 1) ha _ hsourceCont]
  have hinner (u : ℝ) :
      cubeIntervalIntegral n a (f u) = ∫ v in finCube n a, f u v := by
    apply cubeIntervalIntegral_eq_setIntegral n ha
    change Continuous ((fun p : ℝ × (Fin n → ℝ) ↦ f p.1 p.2) ∘
      fun v : Fin n → ℝ ↦ (u, v))
    apply hf.comp
    fun_prop
  simp_rw [hinner]
  rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k
  let F : ℝ × (Fin n → ℝ) → ℂ := fun p ↦ f p.1 p.2
  have hFcont : Continuous F := hf
  have hprodCompact : IsCompact (Icc (0 : ℝ) a ×ˢ finCube n a) :=
    isCompact_Icc.prod isCompact_Icc
  have hFint : IntegrableOn F (Icc (0 : ℝ) a ×ˢ finCube n a) :=
    hFcont.continuousOn.integrableOn_compact hprodCompact
  have hFubini := setIntegral_prod F hFint
  rw [← Measure.volume_eq_prod] at hFubini
  rw [← hFubini]
  have hprodMeas : MeasurableSet (Icc (0 : ℝ) a ×ˢ finCube n a) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hcubeMeas : MeasurableSet (finCube (n + 1) a) := measurableSet_Icc
  rw [← integral_indicator hcubeMeas, ← integral_indicator hprodMeas]
  have hepres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k
  have hcomp := hepres.integral_comp'
    ((Icc (0 : ℝ) a ×ˢ finCube n a).indicator F)
  rw [← hcomp]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    have heval : e t = (t k, Fin.removeNth k t) := by
      rfl
    have hmem : t ∈ finCube (n + 1) a ↔
        e t ∈ Icc (0 : ℝ) a ×ˢ finCube n a := by
      rw [heval]
      simp only [finCube, mem_Icc, Pi.le_def, mem_prod, Fin.removeNth_apply]
      constructor
      · intro h
        exact ⟨⟨h.1 k, h.2 k⟩,
          ⟨fun j ↦ h.1 (k.succAbove j), fun j ↦ h.2 (k.succAbove j)⟩⟩
      · intro h
        constructor
        · rw [k.forall_iff_succAbove]
          exact ⟨h.1.1, h.2.1⟩
        · rw [k.forall_iff_succAbove]
          exact ⟨h.1.2, h.2.2⟩
    by_cases ht : t ∈ finCube (n + 1) a
    · change (finCube (n + 1) a).indicator
          (fun t ↦ f (t k) (Fin.removeNth k t)) t =
        (Icc (0 : ℝ) a ×ˢ finCube n a).indicator F (e t)
      rw [indicator_of_mem ht, indicator_of_mem (hmem.1 ht), heval]
    · change (finCube (n + 1) a).indicator
          (fun t ↦ f (t k) (Fin.removeNth k t)) t =
        (Icc (0 : ℝ) a ×ˢ finCube n a).indicator F (e t)
      rw [indicator_of_notMem ht, indicator_of_notMem (fun h ↦ ht (hmem.2 h))]

/-- Integrated Laplace recurrence for first Fredholm minors. -/
theorem cubeIntervalIntegral_fredholmMinor_succ
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x y : ℝ) :
    cubeIntervalIntegral (n + 1) a (fredholmMinorIntegrand K (n + 1) x y) =
      K x y * cubeIntervalIntegral (n + 1) a (fredholmIntegrand K (n + 1)) -
        ((n + 1 : ℕ) : ℂ) *
          (∫ u in (0 : ℝ)..a,
            K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)) := by
  let g : (Fin (n + 1) → ℝ) → ℂ := fredholmMinorIntegrand K (n + 1) x y
  let d : (Fin (n + 1) → ℝ) → ℂ := fredholmIntegrand K (n + 1)
  let q : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ := fun k t ↦
    K x (t k) * fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)
  let J : ℂ := ∫ u in (0 : ℝ)..a,
    K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)
  have hg : Continuous g := continuous_fredholmMinorIntegrand_fixed K hK (n + 1) x y
  have hd : Continuous d := continuous_fredholmIntegrand K hK (n + 1)
  have hq (k : Fin (n + 1)) : Continuous (q k) := by
    apply Continuous.mul
    · change Continuous (K.uncurry ∘ fun t : Fin (n + 1) → ℝ ↦ (x, t k))
      apply hK.comp
      fun_prop
    · change Continuous ((fun p : (ℝ × ℝ) × (Fin n → ℝ) ↦
          fredholmMinorIntegrand K n p.1.1 p.1.2 p.2) ∘
        fun t : Fin (n + 1) → ℝ ↦ ((t k, y), Fin.removeNth k t))
      apply (continuous_fredholmMinorIntegrand K hK n).comp
      apply Continuous.prodMk
      · fun_prop
      · apply continuous_pi
        intro i
        exact continuous_apply (k.succAbove i)
  have hcubeCompact : IsCompact (finCube (n + 1) a) := isCompact_Icc
  have hgInt : IntegrableOn g (finCube (n + 1) a) :=
    hg.continuousOn.integrableOn_compact hcubeCompact
  have hdInt : IntegrableOn d (finCube (n + 1) a) :=
    hd.continuousOn.integrableOn_compact hcubeCompact
  have hqInt (k : Fin (n + 1)) : IntegrableOn (q k) (finCube (n + 1) a) :=
    (hq k).continuousOn.integrableOn_compact hcubeCompact
  rw [cubeIntervalIntegral_eq_setIntegral (n + 1) ha g hg]
  rw [cubeIntervalIntegral_eq_setIntegral (n + 1) ha d hd]
  calc
    (∫ t in finCube (n + 1) a, g t) =
        ∫ t in finCube (n + 1) a, K x y * d t - ∑ k : Fin (n + 1), q k t := by
          apply integral_congr_ae
          exact ae_of_all _ fun t ↦ fredholmMinorIntegrand_succ_laplace K n x y t
    _ = K x y * (∫ t in finCube (n + 1) a, d t) -
          ∑ k : Fin (n + 1), ∫ t in finCube (n + 1) a, q k t := by
      rw [integral_sub]
      · rw [integral_const_mul]
        rw [integral_finsetSum]
        intro k _
        exact hqInt k
      · exact hdInt.const_mul (K x y)
      · exact (integrable_finsetSum _ fun k _ ↦
          hqInt k)
    _ = K x y * (∫ t in finCube (n + 1) a, d t) -
          ∑ _k : Fin (n + 1), J := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      change (∫ t in finCube (n + 1) a,
        K x (t k) * fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) = J
      rw [← cubeIntervalIntegral_eq_setIntegral (n + 1) ha _ (hq k)]
      change cubeIntervalIntegral (n + 1) a
          (fun t ↦ K x (t k) *
            fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) =
        ∫ u in (0 : ℝ)..a,
          K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)
      have hjoint : Continuous (fun p : ℝ × (Fin n → ℝ) ↦
          K x p.1 * fredholmMinorIntegrand K n p.1 y p.2) := by
        apply Continuous.mul
        · change Continuous (K.uncurry ∘ fun p : ℝ × (Fin n → ℝ) ↦ (x, p.1))
          apply hK.comp
          fun_prop
        · change Continuous ((fun p : (ℝ × ℝ) × (Fin n → ℝ) ↦
            fredholmMinorIntegrand K n p.1.1 p.1.2 p.2) ∘
              fun p : ℝ × (Fin n → ℝ) ↦ ((p.1, y), p.2))
          apply (continuous_fredholmMinorIntegrand K hK n).comp
          fun_prop
      calc
        cubeIntervalIntegral (n + 1) a
            (fun t ↦ K x (t k) *
              fredholmMinorIntegrand K n (t k) y (Fin.removeNth k t)) =
            ∫ u in (0 : ℝ)..a,
              cubeIntervalIntegral n a
                (fun v ↦ K x u * fredholmMinorIntegrand K n u y v) :=
          cubeIntervalIntegral_removeNth ha k
            (fun u v ↦ K x u * fredholmMinorIntegrand K n u y v) hjoint
        _ = ∫ u in (0 : ℝ)..a,
              K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y) := by
          apply intervalIntegral.integral_congr
          intro u _
          have hminor := continuous_fredholmMinorIntegrand_fixed K hK n u y
          change cubeIntervalIntegral n a
              (fun v ↦ K x u * fredholmMinorIntegrand K n u y v) =
            K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)
          calc
            cubeIntervalIntegral n a
                (fun v ↦ K x u * fredholmMinorIntegrand K n u y v) =
                ∫ v in finCube n a,
                  K x u * fredholmMinorIntegrand K n u y v :=
              cubeIntervalIntegral_eq_setIntegral n ha _ (continuous_const.mul hminor)
            _ = K x u * ∫ v in finCube n a,
                  fredholmMinorIntegrand K n u y v := by rw [integral_const_mul]
            _ = K x u * cubeIntervalIntegral n a
                  (fredholmMinorIntegrand K n u y) := by
              rw [cubeIntervalIntegral_eq_setIntegral n ha _ hminor]
    _ = K x y * (∫ t in finCube (n + 1) a, d t) - ((n + 1 : ℕ) : ℂ) * J := by
      simp

/-- Coefficient-level Fredholm resolvent recurrence. -/
theorem fredholmMinorCoefficient_succ_add_integral
    (K : ℝ → ℝ → ℂ) (hK : Continuous K.uncurry)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x y : ℝ) :
    fredholmMinorCoefficient K a (n + 1) x y +
        (∫ u in (0 : ℝ)..a,
          K x u * fredholmMinorCoefficient K a n u y) =
      K x y * fredholmCoefficient K a (n + 1) := by
  let CM : ℂ := cubeIntervalIntegral (n + 1) a
    (fredholmMinorIntegrand K (n + 1) x y)
  let CD : ℂ := cubeIntervalIntegral (n + 1) a
    (fredholmIntegrand K (n + 1))
  let J : ℂ := ∫ u in (0 : ℝ)..a,
    K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)
  have hrec : CM = K x y * CD - ((n + 1 : ℕ) : ℂ) * J := by
    exact cubeIntervalIntegral_fredholmMinor_succ K hK ha n x y
  have hfac : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hsucc : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hcast : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
    push_cast
    rfl
  rw [hcast] at hrec
  have hInt :
      (∫ u in (0 : ℝ)..a,
          K x u * fredholmMinorCoefficient K a n u y) =
        J / (n.factorial : ℂ) := by
    simp only [fredholmMinorCoefficient, div_eq_mul_inv]
    change (∫ u in (0 : ℝ)..a,
      K x u * (cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y) *
        (n.factorial : ℂ)⁻¹)) = J * (n.factorial : ℂ)⁻¹
    simpa only [mul_assoc] using
      (intervalIntegral.integral_mul_const (n.factorial : ℂ)⁻¹
        (fun u : ℝ ↦
          K x u * cubeIntervalIntegral n a (fredholmMinorIntegrand K n u y)))
  rw [fredholmMinorCoefficient, fredholmCoefficient, hInt]
  change CM / (((n + 1).factorial : ℕ) : ℂ) + J / (n.factorial : ℂ) =
    K x y * (CD / (((n + 1).factorial : ℕ) : ℂ))
  rw [Nat.factorial_succ]
  push_cast
  rw [hrec]
  field_simp [hfac, hsucc]
  ring

/-- Dominated-convergence interchange for a kernel multiplied by the first-minor series. -/
theorem hasSum_intervalIntegral_kernel_fredholmMinor
    (K : ℝ → ℝ → ℂ) (hKcont : Continuous K.uncurry)
    {a M x y : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hx : x ∈ Icc (0 : ℝ) a) (hy : y ∈ Icc (0 : ℝ) a)
    (hK : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, ‖K u v‖ ≤ M)
    (z : ℂ) :
    HasSum
      (fun n : ℕ ↦ ∫ u in (0 : ℝ)..a,
        K x u * (z ^ n * fredholmMinorCoefficient K a n u y))
      (∫ u in (0 : ℝ)..a, K x u * fredholmMinor K a z u y) := by
  let B : ℝ := ‖z‖ * (a * M)
  let c : ℝ := max M B
  let b : ℕ → ℝ := fun n ↦
    (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg z) (mul_nonneg ha hM)
  have hc : 0 ≤ c := le_max_of_le_left hM
  have hMc : M ≤ c := le_max_left _ _
  have hBc : B ≤ c := le_max_right _ _
  have hbSummable : Summable b := summable_succ_hadamard_majorant c hc
  have htermBound (n : ℕ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) a) :
      ‖z ^ n * fredholmMinorCoefficient K a n u y‖ ≤ b n := by
    rw [fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient K hKcont n ha]
    rw [norm_mul, norm_pow]
    have hsqrt : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
    calc
      ‖z‖ ^ n * ‖orderedFredholmMinorCoefficient K a n u y‖ ≤
          ‖z‖ ^ n * (a ^ n / (n.factorial : ℝ) *
            (Real.sqrt (n + 1) * M) ^ (n + 1)) := by
        gcongr
        exact orderedFredholmMinorCoefficient_norm_le K ha hM hu hy hK n
      _ = (Real.sqrt (n + 1) * M) *
          (Real.sqrt (n + 1) * B) ^ n / (n.factorial : ℝ) := by
        rw [pow_succ']
        dsimp [B]
        ring
      _ ≤ (Real.sqrt (n + 1) * c) *
          (Real.sqrt (n + 1) * c) ^ n / (n.factorial : ℝ) := by
        gcongr
      _ = b n := by
        dsimp [b]
        rw [pow_succ']
  have hcoeffCont (n : ℕ) :
      Continuous (fun u : ℝ ↦ fredholmMinorCoefficient K a n u y) := by
    rw [show (fun u : ℝ ↦ fredholmMinorCoefficient K a n u y) =
        fun u ↦ orderedFredholmMinorCoefficient K a n u y by
      funext u
      exact fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient K hKcont n ha u y]
    change Continuous ((fun p : (ℝ × ℝ) × ℝ ↦
      orderedFredholmMinorCoefficient K p.2 n p.1.1 p.1.2) ∘
        fun u : ℝ ↦ ((u, y), a))
    apply (continuous_orderedFredholmMinorCoefficient K hKcont n).comp
    fun_prop
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n (_u : ℝ) ↦ M * b n)
  · intro n
    have hKxu : Continuous (fun u : ℝ ↦ K x u) := by
      change Continuous (K.uncurry ∘ fun u : ℝ ↦ (x, u))
      apply hKcont.comp
      fun_prop
    exact (hKxu.mul ((continuous_const.mul (hcoeffCont n)))).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun u hu ↦ by
      have hu' : u ∈ Icc (0 : ℝ) a := by
        have := uIoc_subset_uIcc hu
        rwa [uIcc_of_le ha] at this
      rw [norm_mul]
      exact mul_le_mul (hK x hx u hu') (htermBound n u hu')
        (norm_nonneg _) hM
  · exact ae_of_all _ fun _u _hu ↦ hbSummable.mul_left M
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun u hu ↦ by
      have hu' : u ∈ Icc (0 : ℝ) a := by
        have := uIoc_subset_uIcc hu
        rwa [uIcc_of_le ha] at this
      have hsOrdered := orderedFredholmMinor_summable K ha hM hu' hy hK z
      have hsCube : Summable (fun n : ℕ ↦
          z ^ n * fredholmMinorCoefficient K a n u y) := by
        apply hsOrdered.congr
        intro n
        rw [fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient K hKcont n ha]
      have hsum : HasSum
          (fun n : ℕ ↦ z ^ n * fredholmMinorCoefficient K a n u y)
          (fredholmMinor K a z u y) := by
        simpa only [fredholmMinor] using hsCube.hasSum
      simpa only [mul_assoc] using hsum.mul_left (K x u)

theorem fredholmMinorCoefficient_zero (K : ℝ → ℝ → ℂ) (a x y : ℝ) :
    fredholmMinorCoefficient K a 0 x y = K x y := by
  simp [fredholmMinorCoefficient, cubeIntervalIntegral, fredholmMinorIntegrand]
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.snoc_last, Fin.snoc_last]

theorem fredholmCoefficient_zero (K : ℝ → ℝ → ℂ) (a : ℝ) :
    fredholmCoefficient K a 0 = 1 := by
  simp [fredholmCoefficient, cubeIntervalIntegral, fredholmIntegrand]

/-- First Fredholm minor solves the continuous-kernel resolvent equation. -/
theorem fredholmMinor_add_integral_eq_kernel_mul_determinant
    (K : ℝ → ℝ → ℂ) (hKcont : Continuous K.uncurry)
    {a M x y : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hx : x ∈ Icc (0 : ℝ) a) (hy : y ∈ Icc (0 : ℝ) a)
    (hK : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, ‖K u v‖ ≤ M)
    (z : ℂ) :
    fredholmMinor K a z x y +
        z * (∫ u in (0 : ℝ)..a, K x u * fredholmMinor K a z u y) =
      K x y * determinant K a z := by
  let m : ℕ → ℂ := fun n ↦ z ^ n * fredholmMinorCoefficient K a n x y
  let d : ℕ → ℂ := fun n ↦ z ^ n * fredholmCoefficient K a n
  let q : ℕ → ℂ := fun n ↦ ∫ u in (0 : ℝ)..a,
    K x u * (z ^ n * fredholmMinorCoefficient K a n u y)
  have hmsumOrdered := orderedFredholmMinor_summable K ha hM hx hy hK z
  have hmsum : Summable m := by
    apply hmsumOrdered.congr
    intro n
    dsimp [m]
    rw [fredholmMinorCoefficient_eq_orderedFredholmMinorCoefficient K hKcont n ha]
  have hdsum : Summable d := determinant_summable K ha hM hK z
  have hqHasSum : HasSum q
      (∫ u in (0 : ℝ)..a, K x u * fredholmMinor K a z u y) := by
    exact hasSum_intervalIntegral_kernel_fredholmMinor K hKcont ha hM hx hy hK z
  have hqsum : Summable q := hqHasSum.summable
  have hqScale (n : ℕ) :
      q n = z ^ n * (∫ u in (0 : ℝ)..a,
        K x u * fredholmMinorCoefficient K a n u y) := by
    dsimp [q]
    calc
      (∫ u in (0 : ℝ)..a,
          K x u * (z ^ n * fredholmMinorCoefficient K a n u y)) =
          ∫ u in (0 : ℝ)..a,
            z ^ n * (K x u * fredholmMinorCoefficient K a n u y) := by
        apply intervalIntegral.integral_congr
        intro u _
        ring
      _ = z ^ n * (∫ u in (0 : ℝ)..a,
          K x u * fredholmMinorCoefficient K a n u y) := by
        rw [intervalIntegral.integral_const_mul]
  have hrec (n : ℕ) : m (n + 1) + z * q n = K x y * d (n + 1) := by
    have hc := fredholmMinorCoefficient_succ_add_integral K hKcont ha n x y
    have hscaled := congrArg (fun w : ℂ ↦ z ^ (n + 1) * w) hc
    dsimp [m, d]
    rw [hqScale]
    calc
      z ^ (n + 1) * fredholmMinorCoefficient K a (n + 1) x y +
          z * (z ^ n * (∫ u in (0 : ℝ)..a,
            K x u * fredholmMinorCoefficient K a n u y)) =
          z ^ (n + 1) *
            (fredholmMinorCoefficient K a (n + 1) x y +
              (∫ u in (0 : ℝ)..a,
                K x u * fredholmMinorCoefficient K a n u y)) := by
        rw [pow_succ']
        ring
      _ = z ^ (n + 1) * (K x y * fredholmCoefficient K a (n + 1)) := hscaled
      _ = K x y * (z ^ (n + 1) * fredholmCoefficient K a (n + 1)) := by ring
  have hmtail : Summable (fun n : ℕ ↦ m (n + 1)) :=
    (summable_nat_add_iff 1).2 hmsum
  have hdtail : Summable (fun n : ℕ ↦ d (n + 1)) :=
    (summable_nat_add_iff 1).2 hdsum
  have htailEq :
      (∑' n : ℕ, m (n + 1)) + z * (∑' n : ℕ, q n) =
        K x y * (∑' n : ℕ, d (n + 1)) := by
    rw [← tsum_mul_left]
    rw [← hmtail.tsum_add (hqsum.mul_left z)]
    calc
      (∑' n : ℕ, (m (n + 1) + z * q n)) =
          ∑' n : ℕ, (K x y * d (n + 1)) := tsum_congr hrec
      _ = K x y * (∑' n : ℕ, d (n + 1)) := by rw [tsum_mul_left]
  change (∑' n : ℕ, m n) + z *
      (∫ u in (0 : ℝ)..a, K x u * fredholmMinor K a z u y) =
    K x y * (∑' n : ℕ, d n)
  rw [← hqHasSum.tsum_eq]
  rw [hmsum.tsum_eq_zero_add, hdsum.tsum_eq_zero_add]
  have hm0 : m 0 = K x y := by
    simp [m, fredholmMinorCoefficient_zero]
  have hd0 : d 0 = 1 := by
    simp [d, fredholmCoefficient_zero]
  rw [hm0, hd0]
  rw [add_assoc, htailEq]
  ring


/-- Uniform convergence makes the first Fredholm minor continuous in its left distinguished
point on a compact aperture. -/
theorem continuousOn_fredholmMinor_left
    (K : ℝ → ℝ → ℂ) (hKcont : Continuous K.uncurry)
    {a M y : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hy : y ∈ Icc (0 : ℝ) a)
    (hK : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, ‖K u v‖ ≤ M)
    (z : ℂ) :
    ContinuousOn (fun x : ℝ ↦ fredholmMinor K a z x y) (Icc (0 : ℝ) a) := by
  rw [show (fun x : ℝ ↦ fredholmMinor K a z x y) =
      fun x ↦ orderedFredholmMinor K a z x y by
    funext x
    exact fredholmMinor_eq_orderedFredholmMinor K hKcont ha z x y]
  change ContinuousOn (fun x : ℝ ↦ ∑' n : ℕ,
    z ^ n * orderedFredholmMinorCoefficient K a n x y) (Icc (0 : ℝ) a)
  let B : ℝ := ‖z‖ * (a * M)
  let c : ℝ := max M B
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg z) (mul_nonneg ha hM)
  have hc : 0 ≤ c := le_max_of_le_left hM
  have hMc : M ≤ c := le_max_left _ _
  have hBc : B ≤ c := le_max_right _ _
  apply continuousOn_tsum
  · intro n
    apply Continuous.continuousOn
    change Continuous ((fun p : (ℝ × ℝ) × ℝ ↦
      z ^ n * orderedFredholmMinorCoefficient K p.2 n p.1.1 p.1.2) ∘
        fun x : ℝ ↦ ((x, y), a))
    apply (continuous_const.mul
      (continuous_orderedFredholmMinorCoefficient K hKcont n)).comp
    fun_prop
  · exact summable_succ_hadamard_majorant c hc
  · intro n x hx
    rw [norm_mul, norm_pow]
    have hsqrt : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
    calc
      ‖z‖ ^ n * ‖orderedFredholmMinorCoefficient K a n x y‖ ≤
          ‖z‖ ^ n * (a ^ n / (n.factorial : ℝ) *
            (Real.sqrt (n + 1) * M) ^ (n + 1)) := by
        gcongr
        exact orderedFredholmMinorCoefficient_norm_le K ha hM hx hy hK n
      _ = (Real.sqrt (n + 1) * M) *
          (Real.sqrt (n + 1) * B) ^ n / (n.factorial : ℝ) := by
        rw [pow_succ']
        dsimp [B]
        ring
      _ ≤ (Real.sqrt (n + 1) * c) *
          (Real.sqrt (n + 1) * c) ^ n / (n.factorial : ℝ) := by
        gcongr
      _ = (Real.sqrt (n + 1) * c) ^ (n + 1) / (n.factorial : ℝ) := by
        rw [pow_succ']



end ContinuousKernelFredholm
