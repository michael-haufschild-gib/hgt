import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent

/-! # The first circuit-distance crossing as a measurable time origin -/
open Set Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- Distance from the physical evolution to the projective circuit set
in the independent Gaussian coefficient coordinates. -/
def pathGateDistance (n j : ℕ) (x : PrefixIndex n → ℝ) (t : ℝ) : ℝ :=
  Metric.infDist (unitaryEvolution (numberedGenerator n x) t) (phaseCircuitMatrixImageAtMost (n+2) j)

private theorem continuous_distance (n j : ℕ) :
    Continuous (fun p : (PrefixIndex n → ℝ) × ℝ => pathGateDistance n j p.1 p.2) := by
  have hH : Continuous (numberedGenerator n) := by unfold numberedGenerator; fun_prop
  exact (Metric.continuous_infDist_pt _).comp
    (continuous_unitaryEvolution.comp ((hH.comp continuous_fst).prodMk continuous_snd))

theorem distance_dilate (n j : ℕ) (a : ℝ) (x : PrefixIndex n → ℝ) (t : ℝ) :
    pathGateDistance n j (a • x) t = pathGateDistance n j x (a*t) := by
  have hH : numberedGenerator n (a • x) = (a:ℂ) • numberedGenerator n x := by
    unfold numberedGenerator
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,smul_smul]
  simp only [pathGateDistance,hH,unitaryEvolution_smul_generator]

private def crossingTimes (n j : ℕ) (η : ℝ) (x : PrefixIndex n → ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ η ≤ pathGateDistance n j x t}

/-- First time at or above the separation level, with value zero on prefixes
that never reach it. -/
def crossingOrigin (n j : ℕ) (η : ℝ) (x : PrefixIndex n → ℝ) : ℝ :=
  sInf (crossingTimes n j η x)

private theorem crossing_least {n j : ℕ} {η : ℝ} {x : PrefixIndex n → ℝ}
    (h : (crossingTimes n j η x).Nonempty) :
    IsLeast (crossingTimes n j η x) (crossingOrigin n j η x) := by
  have hc : IsClosed (crossingTimes n j η x) := isClosed_Ici.inter
    (isClosed_le continuous_const ((continuous_distance n j).comp (continuous_const.prodMk continuous_id)))
  have hb : BddBelow (crossingTimes n j η x) := ⟨0,fun _ ht => ht.1⟩
  exact ⟨hc.csInf_mem h hb, fun _ ht => csInf_le hb ht⟩

theorem crossingOrigin_eq_of_first {n j : ℕ} {η σ : ℝ} {x : PrefixIndex n → ℝ}
    (hσ : 0 ≤ σ) (he : pathGateDistance n j x σ = η)
    (hbefore : ∀ t ∈ Ico 0 σ, pathGateDistance n j x t < η) :
    crossingOrigin n j η x = σ := by
  apply IsLeast.csInf_eq (s := crossingTimes n j η x)
  refine ⟨⟨hσ,he.ge⟩,fun t ht => ?_⟩
  exact le_of_not_gt fun hh => (hbefore t ⟨ht.1,hh⟩).not_ge ht.2

/-- Scaling a fixed generator rescales the whole first-passage time inversely. -/
theorem smul_crossingOrigin (n j : ℕ) (η : ℝ) {a : ℝ} (ha : 0 < a) (x : PrefixIndex n → ℝ) :
    a * crossingOrigin n j η (a • x) = crossingOrigin n j η x := by
  have iffhit (t : ℝ) : t ∈ crossingTimes n j η (a • x) ↔ a*t ∈ crossingTimes n j η x := by
    change (0 ≤ t ∧ _) ↔ (0 ≤ a*t ∧ _)
    rw [distance_dilate, mul_nonneg_iff_of_pos_left ha]
  have cancel (v : ℝ) : a*(v/a) = v := by rw [mul_comm,div_mul_cancel₀ _ ha.ne']
  by_cases hx : (crossingTimes n j η x).Nonempty
  · obtain ⟨w,hw⟩ := hx
    have hscaled : w/a ∈ crossingTimes n j η (a • x) :=
      (iffhit _).mpr (by rwa [cancel])
    have hmin := crossing_least ⟨_,hscaled⟩
    have hleast : IsLeast (crossingTimes n j η x) (a*crossingOrigin n j η (a • x)) := by
      refine ⟨(iffhit _).mp hmin.1,fun t ht => ?_⟩
      have hc := hmin.2 ((iffhit (t/a)).mpr (by rwa [cancel]))
      calc
        _ ≤ a*(t/a) := mul_le_mul_of_nonneg_left hc ha.le
        _ = t := cancel t
    exact hleast.csInf_eq.symm
  · have hs : ¬(crossingTimes n j η (a • x)).Nonempty := fun ⟨t,ht⟩ => hx ⟨a*t,(iffhit _).mp ht⟩
    simp only [crossingOrigin,not_nonempty_iff_eq_empty.mp hx,not_nonempty_iff_eq_empty.mp hs,
      Real.sInf_empty,mul_zero]

/-- A closed observation window relative to the crossing scales exactly,
including both endpoints and the full short-circuit target. -/
theorem crossing_window_dilate (n j s : ℕ) (η ε d b : ℝ) {a : ℝ} (ha : 0 < a)
    (x : PrefixIndex n → ℝ) :
    let o := crossingOrigin n j η
    (∃ t ∈ Icc (o (a • x)+d) (o (a • x)+d+b), pathGateDistance n s (a • x) t ≤ ε) ↔
      ∃ t ∈ Icc (o x+a*d) (o x+a*d+a*b), pathGateDistance n s x t ≤ ε := by
  intro o
  have ho : a*o (a • x) = o x := smul_crossingOrigin n j η ha x
  have hleft : a*(o (a • x)+d) = o x+a*d := by rw [mul_add,ho]
  have hright : a*(o (a • x)+d+b) = o x+a*d+a*b := by rw [mul_add,hleft]
  constructor
  · rintro ⟨t,ht,hd⟩
    rw [distance_dilate] at hd
    exact ⟨a*t,⟨hleft ▸ mul_le_mul_of_nonneg_left ht.1 ha.le,
      hright ▸ mul_le_mul_of_nonneg_left ht.2 ha.le⟩,hd⟩
  · rintro ⟨t,ht,hd⟩
    have he : a*(t/a) = t := by rw [mul_comm, div_mul_cancel₀ _ ha.ne']
    refine ⟨t/a,⟨(mul_le_mul_iff_right₀ ha).mp ?_,(mul_le_mul_iff_right₀ ha).mp ?_⟩,?_⟩
    · rw [hleft,he]; exact ht.1
    · rw [hright,he]; exact ht.2
    · rwa [distance_dilate,he]

/-- Existential quantification over a compact interval preserves closedness
of a joint coefficient and time condition. -/
private theorem compact_time_projection {X : Type*} [TopologicalSpace X] {Z : Set (X × ℝ)}
    (hZ : IsClosed Z) (b : ℝ) :
    IsClosed {x : X | ∃ t ∈ Icc 0 b, (x,t) ∈ Z} := by
  let K := Icc 0 b
  letI : CompactSpace ↥K := inferInstanceAs (CompactSpace (Icc (0:ℝ) b))
  let S := (fun p : X × ↥K => (p.1,p.2.val)) ⁻¹' Z
  have hS : IsClosed S := hZ.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have he : {x : X | ∃ t ∈ Icc 0 b, (x,t) ∈ Z} = Prod.fst '' S := by
    ext x
    exact ⟨fun ⟨t,ht,h⟩ => ⟨(x,⟨t,ht⟩),h,rfl⟩,fun ⟨⟨_,t⟩,ht,rfl⟩ => ⟨t.val,t.property,ht⟩⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hS

private theorem measurable_first_closed_time {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (τ : X → ℝ) {Z : Set (X × ℝ)} (hZ : IsClosed Z)
    (hmin : ∀ x, (∃ t : ℝ, 0 ≤ t ∧ (x,t) ∈ Z) → IsLeast {t : ℝ | 0 ≤ t ∧ (x,t) ∈ Z} (τ x))
    (hempty : ∀ x, ¬(∃ t : ℝ, 0 ≤ t ∧ (x,t) ∈ Z) → τ x = 0) : Measurable τ := by
  let B (b : ℝ) : Set X := {x | ∃ t ∈ Icc 0 b, (x,t) ∈ Z}
  have hB (b : ℝ) : MeasurableSet (B b) :=
    (compact_time_projection hZ b).measurableSet
  let E := {x : X | ∃ t : ℝ, 0 ≤ t ∧ (x,t) ∈ Z}
  have hE : MeasurableSet E := by
    have he : E = ⋃ i : ℕ, B i := by
      ext x
      constructor
      · rintro ⟨t,h0,ht⟩
        exact mem_iUnion.mpr ⟨⌈t⌉₊,t,⟨h0,Nat.le_ceil _⟩,ht⟩
      · intro h
        obtain ⟨i,t,ht,hh⟩ := mem_iUnion.mp h
        exact ⟨t,ht.1,hh⟩
    rw [he]
    exact MeasurableSet.iUnion fun i => hB i
  apply measurable_of_Iic
  intro b
  have he : τ ⁻¹' Iic b = B b ∪ (Eᶜ ∩ {_x : X | (0:ℝ) ≤ b}) := by
    ext x
    by_cases h : x ∈ E
    · have hm := hmin x h
      exact ⟨fun hx => Or.inl ⟨_,⟨hm.1.1,hx⟩,hm.1.2⟩,fun hx => hx.elim
        (fun ⟨t,ht,hh⟩ => (hm.2 ⟨ht.1,hh⟩).trans ht.2) (fun hc => (hc.1 h).elim)⟩
    · have hz := hempty x h
      constructor
      · intro hx
        exact Or.inr ⟨h,hz ▸ hx⟩
      · rintro (⟨t,ht,hh⟩ | ⟨_,hb⟩)
        · exact (h ⟨t,ht.1,hh⟩).elim
        · exact hz.le.trans hb
  rw [he]
  exact (hB b).union (hE.compl.inter (measurableSet_le measurable_const measurable_const))

theorem measurable_crossingOrigin (n j : ℕ) (η : ℝ) : Measurable (crossingOrigin n j η) := by
  let Z := {p : (PrefixIndex n → ℝ) × ℝ | η ≤ pathGateDistance n j p.1 p.2}
  have hZ : IsClosed Z := isClosed_le continuous_const (continuous_distance n j)
  refine measurable_first_closed_time _ hZ (fun _ h => crossing_least h) ?_
  intro x h
  have he : crossingTimes n j η x = ∅ := not_nonempty_iff_eq_empty.mp h
  rw [crossingOrigin,he,Real.sInf_empty]

private theorem measurable_shifted_sublevel {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    (f : X × ℝ → ℝ) (hf : Continuous f) (o : X → ℝ) (ho : Measurable o) (d b ε : ℝ) :
    MeasurableSet {x | ∃ t ∈ Icc (o x+d) (o x+d+b), f (x,t) ≤ ε} := by
  let F (p : (X × ℝ) × ℝ) := f (p.1.1,p.1.2+p.2)
  have hg : Continuous (fun p : (X × ℝ) × ℝ => (p.1.1,p.1.2+p.2)) := by fun_prop
  have hc : Continuous F := hf.comp hg
  let Z := {p | F p ≤ ε}
  have hZ : IsClosed Z := isClosed_le hc continuous_const
  have h := (compact_time_projection hZ b).measurableSet.preimage
    (measurable_id.prodMk (ho.add_const d))
  apply h.congr
  symm
  ext x
  constructor
  · rintro ⟨t,ht,hh⟩
    exact ⟨t-(o x+d),⟨sub_nonneg.mpr ht.1, by linarith only [ht.2]⟩,
      by change f (x,(o x+d)+(t-(o x+d))) ≤ ε; rwa [show o x+d+(t-(o x+d))=t by ring]⟩
  · rintro ⟨t,ht,hh⟩
    exact ⟨o x+d+t,⟨le_add_of_nonneg_right ht.1,add_le_add le_rfl ht.2⟩,hh⟩

/-- A visit in a fixed-length interval after a measurable origin is measurable
even when the first crossing jumps as the Hamiltonian varies. -/
theorem measurable_shifted_window (n s : ℕ) (o : (PrefixIndex n → ℝ) → ℝ)
    (ho : Measurable o) (d b : ℝ) :
    MeasurableSet {x | ∃ t ∈ Icc (o x+d) (o x+d+b), pathGateDistance n s x t ≤ 1/10} :=
  measurable_shifted_sublevel _ (continuous_distance n s) o ho d b (1/10)

#print axioms measurable_crossingOrigin
#print axioms smul_crossingOrigin
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
