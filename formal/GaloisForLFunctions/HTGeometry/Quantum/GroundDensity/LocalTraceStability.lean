import GaloisForLFunctions.HTGeometry.Quantum.GroundDensity.LocalTracePotential

/-!
# Sharp stability for local ground-state measurements

Multiplicative errors in the pairwise amplitude ratios preserve the scale
invariance of the local trace. At an observed site, the inverse potential
is a nonnegative weighted sum of these ratios and of the hidden ones.
Varying the center amplitude realizes the extremal errors simultaneously.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every measured amplitude ratio agrees within a common multiplicative
factor. Both orientations of each ratio are measured on the patch. -/
def LocalAmplitudeRatiosWithin (S : Finset V) (f g : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, g.1 u / g.1 v ≤ (ρ : ℝ) * (f.1 u / f.1 v)

private theorem noiseFactor_pos (ρ : Ici (1 : ℝ)) : 0 < (ρ : ℝ) :=
  zero_lt_one.trans_le ρ.2

omit [Fintype V] [DecidableEq V] in
private theorem localAmplitudeRatiosWithin_refl (S : Finset V) (f : PositiveAmplitude V)
    (ρ : Ici (1 : ℝ)) : LocalAmplitudeRatiosWithin S f f ρ := by
  intro u _ v _
  exact le_mul_of_one_le_left (div_nonneg (f.2 u).le (f.2 v).le) ρ.2

omit [Fintype V] [DecidableEq V] in
private theorem lower_ratio_of_within {S : Finset V} {f g : PositiveAmplitude V} {ρ : Ici (1 : ℝ)}
    (h : LocalAmplitudeRatiosWithin S f g ρ) {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    (ρ : ℝ)⁻¹ * (f.1 u / f.1 v) ≤ g.1 u / g.1 v := by
  have h' : g.1 v / g.1 u ≤ ((ρ : ℝ) * f.1 v) / f.1 u := by
    rw [mul_div_assoc]
    exact h v hv u hu
  have hc := (div_le_div_iff₀ (g.2 u) (f.2 u)).mp h'
  rw [mul_comm (ρ : ℝ)⁻¹, ← div_eq_mul_inv, div_div,
    div_le_div_iff₀ (mul_pos (f.2 v) (noiseFactor_pos ρ)) (g.2 v)]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hc

/-- Potential values compatible with amplitude ratios measured to within
a prescribed multiplicative factor at fixed ground energy. -/
def noisyLocalTracePotentialValues (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : V) : Set ℝ :=
  (fun g : PositiveAmplitude V => G.inversePotential g E v) ''
    {g : PositiveAmplitude V | LocalAmplitudeRatiosWithin S f g ρ}

/-- The part of the inverse potential coming from the observed amplitudes,
expressed as a sum of weighted ratios. -/
def localTraceObservedRatio (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (v : V) : ℝ :=
  ∑ u ∈ S, G.w v u * (f.1 u / f.1 v)

omit [Fintype V] [DecidableEq V] in
theorem localTraceObservedRatio_nonneg (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (v : V) : 0 ≤ G.localTraceObservedRatio S f v :=
  Finset.sum_nonneg fun u _ => mul_nonneg (G.w_nonneg v u) (div_nonneg (f.2 u).le (f.2 v).le)

theorem localTracePotentialFloor_eq_add_observedRatio (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) {v : V} (hv : v ∈ S) :
    G.localTracePotentialFloor S f E v = E - G.mass v + G.localTraceObservedRatio S f v := by
  rw [localTracePotentialFloor, if_pos hv, localTraceObservedRatio, div_eq_mul_inv, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc, div_eq_mul_inv]

omit [Fintype V] [DecidableEq V] in
private theorem observedRatio_bounds (G : WeightedGraph V) {S : Finset V}
    {f g : PositiveAmplitude V} {ρ : Ici (1 : ℝ)} (hg : LocalAmplitudeRatiosWithin S f g ρ)
    {v : V} (hv : v ∈ S) :
    (ρ : ℝ)⁻¹ * G.localTraceObservedRatio S f v ≤ G.localTraceObservedRatio S g v ∧
      G.localTraceObservedRatio S g v ≤ (ρ : ℝ) * G.localTraceObservedRatio S f v := by
  have hsum (c : ℝ) : c * G.localTraceObservedRatio S f v =
      ∑ u ∈ S, G.w v u * (c * (f.1 u / f.1 v)) := by
    rw [localTraceObservedRatio, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [mul_left_comm]
  constructor
  · rw [hsum]
    exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (lower_ratio_of_within hg hu hv) (G.w_nonneg v u)
  · rw [hsum]
    exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hg u hu v hv) (G.w_nonneg v u)

omit [DecidableEq V] in
private theorem exact_values_subset_noisy (G : WeightedGraph V) {S : Finset V}
    {f g : PositiveAmplitude V} {ρ : Ici (1 : ℝ)} (h : LocalAmplitudeRatiosWithin S f g ρ)
    (E : ℝ) (v : V) :
    G.localTracePotentialValues S g E v ⊆ G.noisyLocalTracePotentialValues S f ρ E v := by
  rintro z ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  change LocalAmplitudeRatiosWithin S f p ρ
  intro u hu w hw
  have hpu : p.1 u = g.1 u := hp hu
  have hpw : p.1 w = g.1 w := hp hw
  rw [hpu, hpw]
  exact h u hu w hw

private def adjustedAmplitude (f : PositiveAmplitude V) (v : V) (t : Ioi (0 : ℝ)) :
    PositiveAmplitude V :=
  ⟨fun u => (if u = v then (t : ℝ)⁻¹ else 1) * f.1 u, fun u => by
    change 0 < (if u = v then (t : ℝ)⁻¹ else 1) * f.1 u
    apply mul_pos _ (f.2 u)
    split_ifs
    · exact inv_pos.mpr t.2
    · exact one_pos⟩

omit [Fintype V] in
private theorem adjustedAmplitude_within (S : Finset V) (f : PositiveAmplitude V) (v : V)
    (ρ : Ici (1 : ℝ)) (t : Ioi (0 : ℝ)) (ht : (t : ℝ) ∈ Icc (ρ : ℝ)⁻¹ (ρ : ℝ)) :
    LocalAmplitudeRatiosWithin S f (adjustedAmplitude f v t) ρ := by
  have htpos : 0 < (t : ℝ) := t.2
  have hinv : (t : ℝ)⁻¹ ≤ (ρ : ℝ) := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr (noiseFactor_pos ρ)) ht.1
  intro u hu w hw
  let c (x : V) : ℝ := if x = v then (t : ℝ)⁻¹ else 1
  have hcoef : c u / c w ≤ (ρ : ℝ) := by
    by_cases hu' : u = v <;> by_cases hw' : w = v
    · simp only [c, if_pos hu', if_pos hw', div_self (inv_pos.mpr htpos).ne']
      exact ρ.2
    · simpa only [c, if_pos hu', if_neg hw', div_one] using hinv
    · simpa only [c, if_neg hu', if_pos hw', one_div, inv_inv] using ht.2
    · simp only [c, if_neg hu', if_neg hw', div_one]
      exact ρ.2
  change c u * f.1 u / (c w * f.1 w) ≤ _
  rw [mul_div_mul_comm]
  exact mul_le_mul_of_nonneg_right hcoef (div_nonneg (f.2 u).le (f.2 w).le)

omit [Fintype V] in
private theorem observedRatio_adjustedAmplitude (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (v : V) (t : Ioi (0 : ℝ)) :
    G.localTraceObservedRatio S (adjustedAmplitude f v t) v = (t : ℝ) * G.localTraceObservedRatio S f v := by
  rw [localTraceObservedRatio, localTraceObservedRatio, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = v
  · subst u
    rw [G.w_diag, zero_mul, zero_mul, mul_zero]
  · change G.w v u * (((if u = v then (t : ℝ)⁻¹ else 1) * f.1 u) /
      ((if v = v then (t : ℝ)⁻¹ else 1) * f.1 v)) = _
    rw [if_neg hu, if_pos rfl, one_mul, div_mul_eq_div_div, div_inv_eq_mul]
    ring

/-- The exact noisy range at every site. At an observed site with all its
neighbors observed it is a closed interval. A hidden neighbor gives an
open half-line, and at an unobserved site the exact trace already allows
all the values available under noise. -/
theorem noisyLocalTracePotentialValues_eq (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : V) :
    G.noisyLocalTracePotentialValues S f ρ E v =
      if v ∈ S then
        if 0 < G.localTracePotentialMissingWeight S v then
          Ioi (E - G.mass v + (ρ : ℝ)⁻¹ * G.localTraceObservedRatio S f v)
        else Icc (E - G.mass v + (ρ : ℝ)⁻¹ * G.localTraceObservedRatio S f v)
          (E - G.mass v + (ρ : ℝ) * G.localTraceObservedRatio S f v)
      else G.localTracePotentialValues S f E v := by
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    let B := E - G.mass v
    let A := G.localTraceObservedRatio S f v
    let L := B + (ρ : ℝ)⁻¹ * A
    let U := B + (ρ : ℝ) * A
    change G.noisyLocalTracePotentialValues S f ρ E v =
      if 0 < G.localTracePotentialMissingWeight S v then Ioi L else Icc L U
    have hbounds (g : PositiveAmplitude V) (hg : LocalAmplitudeRatiosWithin S f g ρ) :
        L ≤ G.localTracePotentialFloor S g E v ∧ G.localTracePotentialFloor S g E v ≤ U := by
      have h := G.observedRatio_bounds hg hv
      rw [G.localTracePotentialFloor_eq_add_observedRatio S g E hv]
      change B + (ρ : ℝ)⁻¹ * A ≤ B + G.localTraceObservedRatio S g v ∧
        B + G.localTraceObservedRatio S g v ≤ B + (ρ : ℝ) * A
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have hattain (t : ℝ) (ht : t ∈ Icc (ρ : ℝ)⁻¹ (ρ : ℝ)) :
        (if 0 < G.localTracePotentialMissingWeight S v then Ioi (B + t * A)
        else {B + t * A}) ⊆ G.noisyLocalTracePotentialValues S f ρ E v := by
      let s : Ioi (0 : ℝ) := ⟨t, (inv_pos.mpr (noiseFactor_pos ρ)).trans_le ht.1⟩
      let g := adjustedAmplitude f v s
      have hg : LocalAmplitudeRatiosWithin S f g ρ := adjustedAmplitude_within S f v ρ s ht
      have hsub := G.exact_values_subset_noisy hg E v
      have hfloor : G.localTracePotentialFloor S g E v = B + t * A := by
        rw [G.localTracePotentialFloor_eq_add_observedRatio S g E hv]
        change B + G.localTraceObservedRatio S (adjustedAmplitude f v s) v = _
        rw [G.observedRatio_adjustedAmplitude]
      rw [G.localTracePotentialValues_eq, hfloor] at hsub
      exact hsub
    have hmin : (ρ : ℝ)⁻¹ ∈ Icc (ρ : ℝ)⁻¹ (ρ : ℝ) := by
      refine ⟨le_rfl, ?_⟩
      rw [← one_div]
      exact ((div_le_one₀ (noiseFactor_pos ρ)).mpr ρ.2).trans ρ.2
    by_cases hM : 0 < G.localTracePotentialMissingWeight S v
    · rw [if_pos hM]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨g, hg, he⟩
        have hz : z ∈ G.localTracePotentialValues S g E v := ⟨g, fun _ _ => rfl, he⟩
        rw [G.localTracePotentialValues_eq, if_pos hM] at hz
        exact (hbounds g hg).1.trans_lt hz
      · have h := hattain _ hmin
        rw [if_pos hM] at h
        exact h
    · rw [if_neg hM]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨g, hg, he⟩
        have hz : z ∈ G.localTracePotentialValues S g E v := ⟨g, fun _ _ => rfl, he⟩
        rw [G.localTracePotentialValues_eq, if_neg hM] at hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hbounds g hg
      · intro z hz
        have hzL : B + (ρ : ℝ)⁻¹ * A ≤ z := hz.1
        have hzU : z ≤ B + (ρ : ℝ) * A := hz.2
        have hA : 0 ≤ A := G.localTraceObservedRatio_nonneg S f v
        by_cases ha : 0 < A
        · let t := (z - B) / A
          have ht : t ∈ Icc (ρ : ℝ)⁻¹ (ρ : ℝ) := ⟨
            (le_div_iff₀ ha).mpr (by linarith only [hzL]),
            (div_le_iff₀ ha).mpr (by linarith only [hzU])⟩
          have he : B + t * A = z := by
            dsimp only [t]
            rw [div_mul_cancel₀ _ ha.ne']
            ring
          have h := hattain t ht
          rw [if_neg hM, he] at h
          exact h (Set.mem_singleton z)
        · have hzero : A = 0 := le_antisymm (le_of_not_gt ha) hA
          rw [hzero, mul_zero, add_zero] at hzL hzU
          have he : z = B := le_antisymm hzU hzL
          have h := hattain _ hmin
          rw [if_neg hM, hzero, mul_zero, add_zero, ← he] at h
          exact h (Set.mem_singleton z)
  · rw [if_neg hv]
    have hsame : G.localTracePotentialValues ∅ f E v = G.localTracePotentialValues S f E v := by
      rw [G.localTracePotentialValues_eq ∅ f E v, G.localTracePotentialValues_eq S f E v]
      simp [localTracePotentialMissingWeight, localTracePotentialFloor, hv]
    refine Subset.antisymm ?_ (G.exact_values_subset_noisy (localAmplitudeRatiosWithin_refl S f ρ) E v)
    rw [← hsame]
    rintro z ⟨g, hg, he⟩
    refine ⟨g, ?_, he⟩
    intro u hu
    simp at hu

/-- Noisy data from actual positive, normalized ground states. -/
def noisyLocalGroundPotentialValues (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : V) : Set ℝ :=
  {z | ∃ (a : V → ℝ) (g : PositiveAmplitude V),
    G.IsGroundAt a E g.1 ∧ LocalAmplitudeRatiosWithin S f g ρ ∧ a v = z}

omit [DecidableEq V] in
/-- Every value allowed by the noisy trace is realized by a physical
ground state, with the same noise tolerance and energy. -/
theorem noisyLocalGroundPotentialValues_eq_trace (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : V) :
    G.noisyLocalGroundPotentialValues S f ρ E v = G.noisyLocalTracePotentialValues S f ρ E v := by
  ext z
  constructor
  · rintro ⟨a, g, ha, hg, he⟩
    have hp : a = G.inversePotential g E := (G.isGroundAt_positive_iff ⟨g, ha.1⟩ a E).mp ha
    exact ⟨g, hg, (congrFun hp v).symm.trans he⟩
  · rintro ⟨g, hg, rfl⟩
    have ha : G.inversePotential g E ∈ G.localGroundPotentials S b g E := by
      rw [G.localGroundPotentials_eq_trace]
      exact ⟨g, fun _ _ => rfl, rfl⟩
    obtain ⟨p, hp, hratio⟩ := ha
    obtain ⟨c, hc, -⟩ := (eqOn_localAmplitudeRatio_iff S b g p).mp hratio
    refine ⟨G.inversePotential g E, p, hp, ?_, rfl⟩
    have hpos : 0 < (c : ℝ) := c.2
    intro u hu w hw
    have hratio' : p.1 u / p.1 w = g.1 u / g.1 w := by
      have hu' : (c : ℝ) * p.1 u = g.1 u := hc hu
      have hw' : (c : ℝ) * p.1 w = g.1 w := hc hw
      rw [← hu', ← hw', mul_div_mul_left _ _ hpos.ne']
    rw [hratio']
    exact hg u hu w hw

/-- Sharp coordinate ranges for noise in the local ground eigenpair
measurement on a finite weighted graph. -/
theorem noisyLocalGroundPotentialValues_eq (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : V) :
    G.noisyLocalGroundPotentialValues S f ρ E v =
      if v ∈ S then
        if 0 < G.localTracePotentialMissingWeight S v then
          Ioi (E - G.mass v + (ρ : ℝ)⁻¹ * G.localTraceObservedRatio S f v)
        else Icc (E - G.mass v + (ρ : ℝ)⁻¹ * G.localTraceObservedRatio S f v)
          (E - G.mass v + (ρ : ℝ) * G.localTraceObservedRatio S f v)
      else G.localGroundPotentialValues S b f E v := by
  rw [G.noisyLocalGroundPotentialValues_eq_trace S b f ρ E v,
    G.noisyLocalTracePotentialValues_eq S f ρ E v, G.localGroundPotentialValues_eq_trace S b f E v]

/-- At a site whose neighbors are all observed, the worst absolute error
is the observed ratio sum times the excess noise factor. It is attained. -/
theorem isGreatest_noisyLocalGroundPotential_error (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (ρ : Ici (1 : ℝ)) (E : ℝ) (v : ↥S)
    (hmissing : G.localTracePotentialMissingWeight S v = 0) :
    IsGreatest ((fun z : ℝ => |z - G.inversePotential f E v|) ''
      G.noisyLocalGroundPotentialValues S f ρ E v)
      (((ρ : ℝ) - 1) * G.localTraceObservedRatio S f v) := by
  let B := E - G.mass v
  let A := G.localTraceObservedRatio S f v
  have hA : 0 ≤ A := G.localTraceObservedRatio_nonneg S f v
  have hρ : 1 ≤ (ρ : ℝ) := ρ.2
  have hm : ¬ 0 < G.localTracePotentialMissingWeight S v := by
    rw [hmissing]
    exact lt_irrefl 0
  have hrange : G.noisyLocalGroundPotentialValues S f ρ E v =
      Icc (B + (ρ : ℝ)⁻¹ * A) (B + (ρ : ℝ) * A) := by
    rw [G.noisyLocalGroundPotentialValues_eq S b f ρ E v, if_pos v.2, if_neg hm]
  have hcenter : G.inversePotential f E v = B + A := by
    have hz : G.inversePotential f E v ∈ G.localTracePotentialValues S f E v :=
      ⟨f, fun _ _ => rfl, rfl⟩
    rw [G.localTracePotentialValues_eq, if_neg hm] at hz
    exact (Set.mem_singleton_iff.mp hz).trans (G.localTracePotentialFloor_eq_add_observedRatio S f E v.2)
  have hinv : (ρ : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (noiseFactor_pos ρ)).mpr hρ
  have hsym : 1 - (ρ : ℝ)⁻¹ ≤ (ρ : ℝ) - 1 := by
    apply (mul_le_mul_iff_right₀ (noiseFactor_pos ρ)).mp
    rw [mul_sub, mul_one, mul_comm (ρ : ℝ) (ρ : ℝ)⁻¹, inv_mul_cancel₀ (noiseFactor_pos ρ).ne',
      mul_comm (ρ : ℝ)]
    exact le_mul_of_one_le_right (sub_nonneg.mpr hρ) hρ
  rw [hrange, hcenter]
  refine ⟨?_, ?_⟩
  · have he : B + (ρ : ℝ)⁻¹ * A ≤ B + (ρ : ℝ) * A := by
      linarith only [mul_le_mul_of_nonneg_right (hinv.trans hρ) hA]
    refine ⟨B + (ρ : ℝ) * A, ⟨he, le_rfl⟩, ?_⟩
    have hval : B + (ρ : ℝ) * A - (B + A) = ((ρ : ℝ) - 1) * A := by ring
    change |B + (ρ : ℝ) * A - (B + A)| = ((ρ : ℝ) - 1) * A
    rw [hval, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hρ) hA)]
  · rintro x ⟨z, hz, rfl⟩
    change |z - (B + A)| ≤ ((ρ : ℝ) - 1) * A
    have hlo : B + (ρ : ℝ)⁻¹ * A ≤ z := hz.1
    have hhi : z ≤ B + (ρ : ℝ) * A := hz.2
    rw [abs_le]
    exact ⟨by linarith only [hlo, mul_le_mul_of_nonneg_right hsym hA], by linarith only [hhi]⟩

#print axioms localTracePotentialFloor_eq_add_observedRatio
#print axioms noisyLocalTracePotentialValues_eq
#print axioms noisyLocalGroundPotentialValues_eq_trace
#print axioms noisyLocalGroundPotentialValues_eq
#print axioms isGreatest_noisyLocalGroundPotential_error

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
