import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorPairOccupation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Three-anchor rigidity and the first overlap correction

Three distinct anchors require three complementary gaps. At the first
radius where this is possible, they form a regular triangle. Thus the
third and higher terms in inclusion–exclusion vanish through that radius.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- When intersection masses depend only on the size of the index set,
inclusion–exclusion groups them with binomial coefficients. -/
theorem measureReal_biUnion_eq_sum_choose_card {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (t : Finset I) (A : I → Set Ω)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (m : ℕ → ℝ)
    (hm : ∀ u : Finset I, u ⊆ t → u.Nonempty → μ.real (⋂ i ∈ u, A i) = m u.card) :
    μ.real (⋃ i ∈ t, A i) = ∑ k ∈ Finset.range (t.card + 1),
      (t.card.choose k : ℝ) * (if k = 0 then 0 else (-1 : ℝ) ^ (k + 1) * m k) := by
  classical
  rw [measureReal_biUnion_eq_sum_powerset hA, Finset.sum_filter, Finset.sum_powerset]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hreplace : ∀ u ∈ t.powersetCard k,
      (if u.Nonempty then (-1 : ℝ) ^ (u.card + 1) * μ.real (⋂ i ∈ u, A i) else 0) =
      (if k = 0 then 0 else (-1 : ℝ) ^ (k + 1) * m k) := by
    intro u hu
    obtain ⟨hut, hcard⟩ := Finset.mem_powersetCard.mp hu
    by_cases h : u.Nonempty
    · have hk : k ≠ 0 := by simpa only [hcard] using (Finset.card_pos.mpr h).ne'
      rw [if_pos h, hm u hut h, hcard, if_neg hk]
    · have hk : k = 0 := hcard.symm.trans (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h))
      rw [if_neg h, if_pos hk]
  rw [Finset.sum_congr rfl hreplace, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- Uniform single and pair masses give a two-term formula when all triple
intersections of distinct events are null. -/
theorem measureReal_biUnion_eq_mul_sub_choose_two {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (t : Finset I) (A : I → Set Ω)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (p q : ℝ) (hP : ∀ i ∈ t, μ.real (A i) = p)
    (hQ : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ.real (A i ∩ A j) = q)
    (hnull : ∀ i ∈ t, ∀ j ∈ t, ∀ k ∈ t, i ≠ j → i ≠ k → j ≠ k → μ ((A i ∩ A j) ∩ A k) = 0) :
    μ.real (⋃ i ∈ t, A i) = (t.card : ℝ) * p - (t.card.choose 2 : ℝ) * q := by
  classical
  let m (k : ℕ) := if k = 1 then p else if k = 2 then q else 0
  have hm (u : Finset I) (hut : u ⊆ t) (hu : u.Nonempty) : μ.real (⋂ i ∈ u, A i) = m u.card := by
    by_cases h1 : u.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
      have hit : i ∈ t := hut (by simpa only [hi] using Finset.mem_singleton_self i)
      rw [show m u.card = p by dsimp only [m]; rw [if_pos h1], hi]
      have he : (⋂ j ∈ ({i} : Finset I), A j) = A i := by
        ext x
        simp only [mem_iInter, Finset.mem_singleton, forall_eq]
      rw [he, hP i hit]
    · by_cases h2 : u.card = 2
      · obtain ⟨i, j, hij, huij⟩ := Finset.card_eq_two.mp h2
        have hit : i ∈ t := hut (by rw [huij]; exact Finset.mem_insert_self i {j})
        have hjt : j ∈ t := hut (by rw [huij]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
        rw [show m u.card = q by dsimp only [m]; rw [if_neg h1, if_pos h2], huij]
        have he : (⋂ k ∈ ({i, j} : Finset I), A k) = A i ∩ A j := by
          ext x
          simp only [mem_iInter, Finset.mem_insert, Finset.mem_singleton, or_imp, forall_and, forall_eq, mem_inter_iff]
        rw [he, hQ i hit j hjt hij]
      · have hlt : 2 < u.card := by have pp := Finset.card_pos.mpr hu; omega
        obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hlt
        have hsub : (⋂ l ∈ u, A l) ⊆ (A i ∩ A j) ∩ A k := fun x hx =>
          ⟨⟨mem_iInter.mp (mem_iInter.mp hx i) hi, mem_iInter.mp (mem_iInter.mp hx j) hj⟩,
            mem_iInter.mp (mem_iInter.mp hx k) hk⟩
        have hμ := measure_mono_null hsub (hnull i (hut hi) j (hut hj) k (hut hk) hij hik hjk)
        simp only [Measure.real, hμ, ENNReal.toReal_zero, m, if_neg h1, if_neg h2]
  let f (k : ℕ) := (t.card.choose k : ℝ) * (if k = 0 then 0 else (-1 : ℝ) ^ (k + 1) * m k)
  have hlong : ∑ k ∈ Finset.range (t.card + 1), f k = ∑ k ∈ Finset.range (max (t.card + 1) 3), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro k _ hk
    have hlt : t.card < k := by simp only [Finset.mem_range, not_lt] at hk; omega
    simp only [f, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
  have hshort : ∑ k ∈ Finset.range 3, f k = ∑ k ∈ Finset.range (max (t.card + 1) 3), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
    intro k _ hk
    have hk' : 3 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have h1 : k ≠ 1 := by omega
    have h2 : k ≠ 2 := by omega
    simp only [f, m, if_neg h1, if_neg h2, mul_zero, ite_self]
  calc
    μ.real (⋃ i ∈ t, A i) = ∑ k ∈ Finset.range (t.card + 1), f k :=
      measureReal_biUnion_eq_sum_choose_card t A hA m hm
    _ = ∑ k ∈ Finset.range 3, f k := hlong.trans hshort.symm
    _ = _ := by
      norm_num [f, m, Finset.sum_range_succ, Nat.choose_one_right]
      ring

section Geometry

variable {ι : Type*}

/-- Three distinct anchor phases through two thirds of a turn force the
endpoint radius and the two nonzero vertices of a regular triangle. -/
theorem three_anchoredUnitArc_rigidity (x : ι → UnitAddCircle) {i j k : ι}
    (r : Icc (1 / 2 : ℝ) (2 / 3)) (hij : x i ≠ x j) (hik : x i ≠ x k) (hjk : x j ≠ x k)
    (hi : x ∈ anchoredUnitArc i r) (hj : x ∈ anchoredUnitArc j r) (hk : x ∈ anchoredUnitArc k r) :
    (r : ℝ) = 2 / 3 ∧
      ((x j - x i = ((1 / 3 : ℝ) : UnitAddCircle) ∧ x k - x i = ((2 / 3 : ℝ) : UnitAddCircle)) ∨
        (x j - x i = ((2 / 3 : ℝ) : UnitAddCircle) ∧ x k - x i = ((1 / 3 : ℝ) : UnitAddCircle))) := by
  let R : Ico (1 / 2 : ℝ) 1 := ⟨r, r.2.1, r.2.2.trans_lt (by norm_num)⟩
  let W := unitArcAnchorSeparation R
  have hW : W = (((↑) : ℝ → UnitAddCircle) '' Icc (1 - (r : ℝ)) (r : ℝ)) :=
    unitArcAnchorSeparation_eq_image R
  have hsep {a b : ι} (h : x a ≠ x b) (ha : x ∈ anchoredUnitArc a r) (hb : x ∈ anchoredUnitArc b r) :
      x b - x a ∈ W := by
    have hab : a ≠ b := fun he => h (congrArg x he)
    exact ⟨ha b hab.symm, by simpa only [neg_sub] using hb a hab, sub_ne_zero.mpr h.symm⟩
  have hji := hsep hij hi hj
  have hki := hsep hik hi hk
  rw [hW] at hji hki
  obtain ⟨a, ha, hea⟩ := hji
  obtain ⟨b, hb, heb⟩ := hki
  have hordered {s t : ℝ} (hs : s ∈ Icc (1 - (r : ℝ)) (r : ℝ)) (ht : t ∈ Icc (1 - (r : ℝ)) (r : ℝ))
      (hst : s ≤ t) (hgap : ((t - s : ℝ) : UnitAddCircle) ∈ W) :
      (r : ℝ) = 2 / 3 ∧ s = 1 / 3 ∧ t = 2 / 3 := by
    rw [hW] at hgap
    obtain ⟨d, hd, he⟩ := hgap
    have h0 : 0 ≤ 1 - (r : ℝ) := sub_nonneg.mpr R.2.2.le
    have h1 : d ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨h0.trans hd.1, by simpa only [zero_add] using hd.2.trans_lt R.2.2⟩
    have h2 : t - s ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨sub_nonneg.mpr hst, by simpa only [zero_add] using
        ((sub_le_self _ (h0.trans hs.1)).trans ht.2).trans_lt R.2.2⟩
    have hdiff := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) h1 h2).mp he
    have hsep' : 1 - (r : ℝ) ≤ t - s := hdiff ▸ hd.1
    have hr : (r : ℝ) = 2 / 3 := by linarith only [hsep', hs.1, ht.2, r.2.2]
    exact ⟨hr, by linarith only [hr, hsep', hs.1, ht.2], by linarith only [hr, hsep', hs.1, ht.2]⟩
  rcases le_total a b with hab | hba
  · have hd : ((b - a : ℝ) : UnitAddCircle) ∈ W := by
      rw [AddCircle.coe_sub, heb, hea, sub_sub_sub_cancel_right]
      exact hsep hjk hj hk
    obtain ⟨hr, ha', hb'⟩ := hordered ha hb hab hd
    exact ⟨hr, Or.inl ⟨by simpa only [ha'] using hea.symm, by simpa only [hb'] using heb.symm⟩⟩
  · have hd : ((a - b : ℝ) : UnitAddCircle) ∈ W := by
      rw [AddCircle.coe_sub, hea, heb, sub_sub_sub_cancel_right]
      exact hsep hjk.symm hk hj
    obtain ⟨hr, hb', ha'⟩ := hordered hb ha hba hd
    exact ⟨hr, Or.inr ⟨by simpa only [ha'] using hea.symm, by simpa only [hb'] using heb.symm⟩⟩

end Geometry

section Relative

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance tripleOccupationCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

local instance tripleOccupationCircleNoAtoms : NullSingletonClass (volume : Measure UnitAddCircle) :=
  ⟨fun x => by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩

/-- A nontrivial phase difference avoids every finite set almost surely. -/
theorem ae_phaseDifference_avoids_finite (ref : ι) {i j : ι} (hij : i ≠ j)
    {B : Set UnitAddCircle} (hB : B.Finite) :
    ∀ᵐ x ∂(volume : Measure ({k : ι // k ≠ ref} → UnitAddCircle)),
      relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i ∉ B := by
  rw [ae_iff]
  let f := fun x : {k : ι // k ≠ ref} → UnitAddCircle =>
    relativeUnitPhasePacket ref x j - relativeUnitPhasePacket ref x i
  have he : {x | ¬ f x ∉ B} = f ⁻¹' B := by
    ext x
    simp only [mem_setOf_eq, not_not, mem_preimage]
  change volume {x | ¬ f x ∉ B} = 0
  rw [he, (measurePreserving_relativePhaseDifference ref hij).measure_preimage
    hB.measurableSet.nullMeasurableSet]
  exact hB.measure_zero _

/-- Coincidences and regular triangles have Haar measure zero, so three
distinct covering anchors have no joint mass through two thirds of a turn. -/
theorem volume_relativeAnchoredUnitArc_triple (ref : ι) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Icc (1 / 2 : ℝ) (2 / 3)) :
    volume ((relativeAnchoredUnitArc ref i r ∩ relativeAnchoredUnitArc ref j r) ∩
      relativeAnchoredUnitArc ref k r) = 0 := by
  let B : Set UnitAddCircle := {0, ((1 / 3 : ℝ) : UnitAddCircle), ((2 / 3 : ℝ) : UnitAddCircle)}
  have hB : B.Finite := ((finite_singleton _).insert _).insert _
  let T := (relativeAnchoredUnitArc ref i r ∩ relativeAnchoredUnitArc ref j r) ∩ relativeAnchoredUnitArc ref k r
  have h : ∀ᵐ x ∂(volume : Measure ({k : ι // k ≠ ref} → UnitAddCircle)), x ∉ T := by
    filter_upwards [ae_phaseDifference_avoids_finite ref hij hB, ae_phaseDifference_avoids_finite ref hik hB,
      ae_phaseDifference_avoids_finite ref hjk hB] with x hj hi hk
    intro hx
    let z := relativeUnitPhasePacket ref x
    have hij' : z i ≠ z j := by intro e; exact hj (by simp [z, e, B])
    have hik' : z i ≠ z k := by intro e; exact hi (by simp [z, e, B])
    have hjk' : z j ≠ z k := by intro e; exact hk (by simp [z, e, B])
    have hr := three_anchoredUnitArc_rigidity z r hij' hik' hjk' hx.1.1 hx.1.2 hx.2
    apply hj
    change z j - z i ∈ B
    rcases hr.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp [B]
  rw [ae_iff] at h
  simpa only [not_not, setOf_mem_eq] using h

/-- The Haar occupation above a semicircle is the single-anchor term minus
the exact pair term, through the endpoint at two thirds of a turn. -/
theorem relativeUnitArcMass_eq_pairCorrection (ref : ι) (r : Icc (1 / 2 : ℝ) (2 / 3)) :
    relativeUnitArcMass ref r = (Fintype.card ι : ℝ) * (r : ℝ) ^ (Fintype.card ι - 1) -
      ((Fintype.card ι).choose 2 : ℝ) * (2 * (r : ℝ) - 1) ^ (Fintype.card ι - 1) := by
  let A (i : ι) := relativeAnchoredUnitArc ref i (r : ℝ)
  let R : Ico (1 / 2 : ℝ) 1 := ⟨r, r.2.1, r.2.2.trans_lt (by norm_num)⟩
  let R' : Icc (0 : ℝ) 1 := ⟨r, (by norm_num : (0 : ℝ) ≤ 1 / 2).trans r.2.1, R.2.2.le⟩
  have hM (i : ι) : MeasurableSet (A i) := (isClosed_relativeAnchoredUnitArc ref i r).measurableSet
  have hP (i : ι) : volume.real (A i) = (r : ℝ) ^ (Fintype.card ι - 1) := by
    rw [Measure.real, volume_relativeAnchoredUnitArc_full ref i R', ENNReal.toReal_pow, ENNReal.toReal_ofReal R'.2.1]
  have hQ (i j : ι) (hij : i ≠ j) :
      volume.real (A i ∩ A j) = (2 * (r : ℝ) - 1) ^ (Fintype.card ι - 1) := by
    rw [Measure.real, volume_relativeAnchoredUnitArc_inter ref hij.symm R, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith only [r.2.1] : 0 ≤ 2 * (r : ℝ) - 1)]
  have h := measureReal_biUnion_eq_mul_sub_choose_two (μ := volume) (Finset.univ : Finset ι) A
    (fun i _ => hM i) _ _ (fun i _ => hP i) (fun i _ j _ => hQ i j)
    (fun _ _ _ _ _ _ hij hik hjk => volume_relativeAnchoredUnitArc_triple ref hij hik hjk r)
  simpa [relativeUnitArcMass, relativeEnclosingUnitArc, enclosingUnitArc, preimage_iUnion, A] using h

/-- The first two pieces of the full occupation profile have one expression
using the positive part of the pair-overlap length. -/
theorem relativeUnitArcMass_eq_through_twoThirds (ref : ι) (r : Icc (0 : ℝ) (2 / 3)) :
    relativeUnitArcMass ref r = (Fintype.card ι : ℝ) * (r : ℝ) ^ (Fintype.card ι - 1) -
      ((Fintype.card ι).choose 2 : ℝ) * max 0 (2 * (r : ℝ) - 1) ^ (Fintype.card ι - 1) := by
  by_cases h : (1 / 2 : ℝ) ≤ (r : ℝ)
  · rw [max_eq_right (by linarith only [h])]
    exact relativeUnitArcMass_eq_pairCorrection ref ⟨r, h, r.2.2⟩
  · rw [max_eq_left (by linarith only [lt_of_not_ge h])]
    have hzero : ((Fintype.card ι).choose 2 : ℝ) * (0 : ℝ) ^ (Fintype.card ι - 1) = 0 := by
      by_cases hc : Fintype.card ι < 2
      · rw [Nat.choose_eq_zero_of_lt hc, Nat.cast_zero, zero_mul]
      · rw [zero_pow (by omega : Fintype.card ι - 1 ≠ 0), mul_zero]
    rw [hzero, sub_zero]
    exact relativeUnitArcMass_eq_power ref ⟨r, r.2.1, (lt_of_not_ge h).le⟩

end Relative

/-- The two-term arc occupation formula on a qubit register. -/
theorem zeroGateFullArcMass_eq_through_twoThirds (n : ℕ) (r : Icc (0 : ℝ) (2 / 3)) :
    zeroGateFullArcMass n r = (2 : ℝ) ^ n * (r : ℝ) ^ (2 ^ n - 1) -
      ((2 ^ n : ℕ).choose 2 : ℝ) * max 0 (2 * (r : ℝ) - 1) ^ (2 ^ n - 1) := by
  simpa only [zeroGateFullArcMass, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using relativeUnitArcMass_eq_through_twoThirds (fun _ : Fin n => false) r

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- On one typical Gaussian draw, every prefix of at least three sites has
the explicit limiting fraction through two thirds of a turn. -/
theorem gaussian_path_zeroGate_fullArcOccupation_through_twoThirds :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Icc (0 : ℝ) (2 / 3), ∀ a : ℝ,
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      let D : ℕ := 2 ^ (k + 3)
      Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
        (𝓝 ((D : ℝ) * (r : ℝ) ^ (D - 1) - (D.choose 2 : ℝ) * max 0 (2 * (r : ℝ) - 1) ^ (D - 1))) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro k r a
  let R : Icc (0 : ℝ) 1 := ⟨r, r.2.1, r.2.2.trans (by norm_num)⟩
  have h := hω k R a
  have he : zeroGateFullArcMass (k + 3) R = ((2 ^ (k + 3) : ℕ) : ℝ) *
      (r : ℝ) ^ (2 ^ (k + 3) - 1) - ((2 ^ (k + 3) : ℕ).choose 2 : ℝ) *
        max 0 (2 * (r : ℝ) - 1) ^ (2 ^ (k + 3) - 1) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using zeroGateFullArcMass_eq_through_twoThirds (k + 3) r
  rwa [he] at h

#print axioms measureReal_biUnion_eq_sum_choose_card
#print axioms measureReal_biUnion_eq_mul_sub_choose_two
#print axioms three_anchoredUnitArc_rigidity
#print axioms volume_relativeAnchoredUnitArc_triple
#print axioms relativeUnitArcMass_eq_through_twoThirds
#print axioms gaussian_path_zeroGate_fullArcOccupation_through_twoThirds

end

end GaloisForLFunctions.HTGeometry
