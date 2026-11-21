import GaloisForLFunctions.HTGeometry.Quantum.GroundDensity.GraphPotential

/-!
# Inverse potentials from a local ground-state trace

For a weighted graph, the ground-state equation reads the potential at a
site from the amplitude there and at its neighbors. Apply the local eigenpair
measurement of Hong (arXiv:2611.16596) in this graph setting. The inverse
ground-state transform realizes every positive extension of the measured
trace and gives the exact range of each potential coordinate.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All potential values at one site compatible with the observed amplitudes
and the fixed ground energy. -/
def localTracePotentialValues (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) : Set ℝ :=
  (fun g : PositiveAmplitude V => G.inversePotential g E v) ''
    {g : PositiveAmplitude V | EqOn g.1 f.1 (S : Set V)}

/-- The lower endpoint of the range of potentials allowed by the trace. -/
def localTracePotentialFloor (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) : ℝ :=
  E - G.mass v + if v ∈ S then (∑ u ∈ S, G.w v u * f.1 u) / f.1 v else 0

/-- At an observed site only edges to unobserved amplitudes contribute
uncertainty. At an unobserved site the denominator is itself unknown. -/
def localTracePotentialMissingWeight (G : WeightedGraph V) (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then ∑ u ∈ Sᶜ, G.w v u else G.mass v

omit [Fintype V] [DecidableEq V] in
private theorem weightedAmplitudeSum_eq_zero_iff (G : WeightedGraph V) (A : Finset V)
    (g : PositiveAmplitude V) (v : V) :
    (∑ u ∈ A, G.w v u * g.1 u) = 0 ↔ (∑ u ∈ A, G.w v u) = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => mul_nonneg (G.w_nonneg v u) (g.2 u).le),
    Finset.sum_eq_zero_iff_of_nonneg (fun u _ => G.w_nonneg v u)]
  exact ⟨fun h u hu => (mul_eq_zero.mp (h u hu)).resolve_right (g.2 u).ne',
    fun h u hu => by rw [h u hu, zero_mul]⟩

omit [Fintype V] [DecidableEq V] in
private theorem weightedAmplitudeSum_pos (G : WeightedGraph V) (A : Finset V)
    (g : PositiveAmplitude V) (v : V) (h : 0 < ∑ u ∈ A, G.w v u) :
    0 < ∑ u ∈ A, G.w v u * g.1 u := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun u _ => mul_nonneg (G.w_nonneg v u) (g.2 u).le) ?_
  exact fun he => h.ne' ((G.weightedAmplitudeSum_eq_zero_iff A g v).mp he.symm)

/-- At an observed site, the remaining contribution is linear in the
unobserved amplitudes, with explicit nonnegative coefficients. -/
theorem inversePotential_eq_localTraceFloor_add_hidden (G : WeightedGraph V) (S : Finset V)
    (f g : PositiveAmplitude V) (E : ℝ) (v : V)
    (hv : v ∈ S) (hg : EqOn g.1 f.1 (S : Set V)) :
    G.inversePotential g E v = G.localTracePotentialFloor S f E v +
      (∑ u ∈ Sᶜ, G.w v u * g.1 u) / f.1 v := by
  have he : (∑ u ∈ S, G.w v u * g.1 u) = ∑ u ∈ S, G.w v u * f.1 u := by
    exact Finset.sum_congr rfl fun u hu => congrArg (G.w v u * ·) (hg hu)
  rw [inversePotential, localTracePotentialFloor, if_pos hv, ← Finset.sum_add_sum_compl S
    (fun u => G.w v u * g.1 u), he, hg hv, add_div, add_assoc]

omit [DecidableEq V] in
private theorem localTracePotentialValues_eq_singleton_of_const (G : WeightedGraph V)
    (S : Finset V) (f : PositiveAmplitude V) (E : ℝ) (v : V) (L : ℝ)
    (h : ∀ g : PositiveAmplitude V, EqOn g.1 f.1 (S : Set V) → G.inversePotential g E v = L) :
    G.localTracePotentialValues S f E v = {L} := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Set.mem_singleton_iff.mpr (h g hg)
  · intro hz
    exact ⟨f, fun _ _ => rfl, (h f (fun _ _ => rfl)).trans (Set.mem_singleton_iff.mp hz).symm⟩

/-- A local amplitude trace fixes a site's potential exactly when its
missing weight is zero. Otherwise every value strictly above the explicit
lower endpoint is realized by a positive amplitude with that trace. -/
theorem localTracePotentialValues_eq (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    G.localTracePotentialValues S f E v =
      if 0 < G.localTracePotentialMissingWeight S v then Ioi (G.localTracePotentialFloor S f E v)
      else {G.localTracePotentialFloor S f E v} := by
  let L := G.localTracePotentialFloor S f E v
  by_cases hv : v ∈ S
  · let M := ∑ u ∈ Sᶜ, G.w v u
    change G.localTracePotentialValues S f E v = if 0 < G.localTracePotentialMissingWeight S v then Ioi L else {L}
    rw [localTracePotentialMissingWeight, if_pos hv]
    by_cases hM : 0 < M
    · rw [if_pos hM]
      apply Subset.antisymm
      · rintro z ⟨g, hg, rfl⟩
        change L < G.inversePotential g E v
        rw [G.inversePotential_eq_localTraceFloor_add_hidden S f g E v hv hg]
        exact lt_add_of_pos_right _ (div_pos (G.weightedAmplitudeSum_pos Sᶜ g v hM) (f.2 v))
      · intro z hz
        have hz' : L < z := hz
        let c := (z - L) * f.1 v / M
        have hc : 0 < c := div_pos (mul_pos (sub_pos.mpr hz') (f.2 v)) hM
        let g : PositiveAmplitude V := ⟨fun u => if u ∈ S then f.1 u else c, by
          intro u
          change 0 < (if u ∈ S then f.1 u else c)
          split_ifs with hu
          · exact f.2 u
          · exact hc⟩
        have hg : EqOn g.1 f.1 (S : Set V) := fun u hu => if_pos hu
        have hs : (∑ u ∈ Sᶜ, G.w v u * g.1 u) = M * c := by
          rw [show M = ∑ u ∈ Sᶜ, G.w v u from rfl, Finset.sum_mul]
          exact Finset.sum_congr rfl fun u hu =>
            congrArg (G.w v u * ·) (if_neg (Finset.mem_compl.mp hu))
        refine ⟨g, hg, ?_⟩
        change G.inversePotential g E v = z
        rw [G.inversePotential_eq_localTraceFloor_add_hidden S f g E v hv hg, hs]
        change L + M * ((z - L) * f.1 v / M) / f.1 v = z
        rw [mul_comm M, div_mul_cancel₀ _ hM.ne', mul_div_cancel_right₀ _ (f.2 v).ne']
        ring
    · rw [if_neg hM]
      have h0 : M = 0 := le_antisymm (le_of_not_gt hM) (Finset.sum_nonneg fun u _ => G.w_nonneg v u)
      apply G.localTracePotentialValues_eq_singleton_of_const
      intro g hg
      rw [G.inversePotential_eq_localTraceFloor_add_hidden S f g E v hv hg,
        (G.weightedAmplitudeSum_eq_zero_iff Sᶜ g v).mpr h0, zero_div, add_zero]
  · have hL : L = E - G.mass v := by simp only [L, localTracePotentialFloor, if_neg hv, add_zero]
    rw [localTracePotentialMissingWeight, if_neg hv]
    by_cases hm : 0 < G.mass v
    · rw [if_pos hm]
      apply Subset.antisymm
      · rintro z ⟨g, hg, rfl⟩
        change L < G.inversePotential g E v
        rw [hL, inversePotential]
        exact lt_add_of_pos_right _ (div_pos (G.weightedAmplitudeSum_pos Finset.univ g v hm) (g.2 v))
      · intro z hz
        have hz' : L < z := hz
        let A := ∑ u, G.w v u * f.1 u
        have hA : 0 < A := G.weightedAmplitudeSum_pos Finset.univ f v hm
        let c := A / (z - L)
        let g : PositiveAmplitude V := ⟨Function.update f.1 v c, by
          intro u
          by_cases hu : u = v
          · subst u
            rw [Function.update_self]
            exact div_pos hA (sub_pos.mpr hz')
          · rw [Function.update_of_ne hu]
            exact f.2 u⟩
        have hg : EqOn g.1 f.1 (S : Set V) := by
          intro u hu
          exact Function.update_of_ne (fun he : u = v => hv (he ▸ hu)) _ _
        have hs : (∑ u, G.w v u * g.1 u) = A := by
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u = v
          · subst u
            rw [G.w_diag, zero_mul, zero_mul]
          · exact congrArg (G.w v u * ·) (Function.update_of_ne hu _ _)
        refine ⟨g, hg, ?_⟩
        change G.inversePotential g E v = z
        rw [inversePotential, hs, ← hL]
        change L + A / Function.update f.1 v c v = z
        rw [Function.update_self]
        change L + A / (A / (z - L)) = z
        rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hA.ne']
        ring
    · rw [if_neg hm]
      have h0 : G.mass v = 0 := le_antisymm (le_of_not_gt hm) (G.mass_nonneg v)
      apply G.localTracePotentialValues_eq_singleton_of_const
      intro g hg
      rw [inversePotential, (G.weightedAmplitudeSum_eq_zero_iff Finset.univ g v).mpr h0, zero_div, add_zero]
      exact hL.symm

/-- A recovered potential is unique at isolated sites and at observed sites
whose positive-weight neighbors are all observed. -/
theorem localTracePotentialValues_subsingleton_iff (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    (G.localTracePotentialValues S f E v).Subsingleton ↔
      G.mass v = 0 ∨ (v ∈ S ∧ ∀ u, 0 < G.w v u → u ∈ S) := by
  have hweights (A : Finset V) : (∑ u ∈ A, G.w v u) = 0 ↔ ∀ u ∈ A, G.w v u = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg (fun u _ => G.w_nonneg v u)
  have hobs : (∑ u ∈ Sᶜ, G.w v u) = 0 ↔ ∀ u, 0 < G.w v u → u ∈ S := by
    rw [hweights]
    constructor
    · intro h u hu
      by_contra hs
      exact hu.ne' (h u (Finset.mem_compl.mpr hs))
    · intro h u hu
      exact le_antisymm (le_of_not_gt (fun hp => (Finset.mem_compl.mp hu) (h u hp))) (G.w_nonneg v u)
  have hzero : G.localTracePotentialMissingWeight S v = 0 ↔
      G.mass v = 0 ∨ (v ∈ S ∧ ∀ u, 0 < G.w v u → u ∈ S) := by
    by_cases hv : v ∈ S
    · rw [localTracePotentialMissingWeight, if_pos hv, hobs]
      simp only [hv, true_and]
      exact ⟨Or.inr, fun h => h.elim (fun hm u hu =>
        False.elim (hu.ne' ((hweights Finset.univ).mp hm u (Finset.mem_univ u)))) id⟩
    · rw [localTracePotentialMissingWeight, if_neg hv]
      simp only [hv, false_and, or_false]
  have hnonneg : 0 ≤ G.localTracePotentialMissingWeight S v := by
    unfold localTracePotentialMissingWeight
    split_ifs
    · exact Finset.sum_nonneg fun u _ => G.w_nonneg v u
    · exact G.mass_nonneg v
  rw [G.localTracePotentialValues_eq S f E v, ← hzero]
  by_cases h : 0 < G.localTracePotentialMissingWeight S v
  · rw [if_pos h]
    refine ⟨fun hs => ?_, fun hz => (h.ne' hz).elim⟩
    let L := G.localTracePotentialFloor S f E v
    have h₁ : L + 1 ∈ Ioi L := mem_Ioi.mpr (lt_add_of_pos_right _ one_pos)
    have h₂ : L + 2 ∈ Ioi L := mem_Ioi.mpr (lt_add_of_pos_right _ (by norm_num))
    have he := hs h₁ h₂
    linarith only [he]
  · rw [if_neg h]
    exact ⟨fun _ => le_antisymm (le_of_not_gt h) hnonneg, fun _ => Set.subsingleton_singleton⟩

omit [Fintype V] [DecidableEq V] in
/-- Ratios to a site in the observed patch specify a unique positive
rescaling that matches the measured amplitudes on the entire patch. -/
theorem eqOn_localAmplitudeRatio_iff (S : Finset V) (b : ↥S)
    (f g : PositiveAmplitude V) :
    EqOn (fun u => g.1 u / g.1 b) (fun u => f.1 u / f.1 b) (S : Set V) ↔
      ∃! c : Ioi (0 : ℝ), EqOn (fun u => (c : ℝ) * g.1 u) f.1 (S : Set V) := by
  constructor
  · intro h
    let c : Ioi (0 : ℝ) := ⟨f.1 b / g.1 b, div_pos (f.2 b) (g.2 b)⟩
    refine ⟨c, ?_, fun d hd => Subtype.ext ?_⟩
    · intro u hu
      change f.1 b / g.1 b * g.1 u = f.1 u
      have he : g.1 u / g.1 b = f.1 u / f.1 b := h hu
      rw [div_mul_eq_mul_div, div_eq_iff (g.2 b).ne', mul_comm (f.1 b)]
      exact (div_eq_div_iff (g.2 b).ne' (f.2 b).ne').mp he
    · have he : (d : ℝ) * g.1 b = f.1 b := hd b.2
      exact (eq_div_iff (g.2 b).ne').mpr he
  · rintro ⟨c, hc, -⟩ u hu
    have hb : (c : ℝ) * g.1 b = f.1 b := hc b.2
    have hv : (c : ℝ) * g.1 u = f.1 u := hc hu
    have hpos : 0 < (c : ℝ) := c.2
    change g.1 u / g.1 b = f.1 u / f.1 b
    rw [← hv, ← hb]
    exact (mul_div_mul_left (g.1 u) (g.1 b) hpos.ne').symm

private def scalePositive (c : Ioi (0 : ℝ)) (f : PositiveAmplitude V) : PositiveAmplitude V :=
  ⟨fun v => (c : ℝ) * f.1 v, fun v => mul_pos c.2 (f.2 v)⟩

omit [Fintype V] [DecidableEq V] in
private theorem scalePositive_ratio (c : Ioi (0 : ℝ)) (f : PositiveAmplitude V) (b v : V) :
    (scalePositive c f).1 v / (scalePositive c f).1 b = f.1 v / f.1 b := by
  have hc : 0 < (c : ℝ) := c.2
  change ((c : ℝ) * f.1 v) / ((c : ℝ) * f.1 b) = _
  exact mul_div_mul_left _ _ hc.ne'

omit [DecidableEq V] in
private theorem inversePotential_scalePositive (G : WeightedGraph V) (c : Ioi (0 : ℝ))
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    G.inversePotential (scalePositive c f) E v = G.inversePotential f E v := by
  have hc : 0 < (c : ℝ) := c.2
  have hs : (∑ u, G.w v u * (scalePositive c f).1 u) = (c : ℝ) * ∑ u, G.w v u * f.1 u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    change G.w v u * ((c : ℝ) * f.1 u) = (c : ℝ) * (G.w v u * f.1 u)
    ring
  rw [inversePotential, inversePotential, hs]
  congr 1
  change (c : ℝ) * (∑ u, G.w v u * f.1 u) / ((c : ℝ) * f.1 v) = _
  exact mul_div_mul_left _ _ hc.ne'

omit [DecidableEq V] in
private theorem exists_normalized_scalePositive (f : PositiveAmplitude V) (b : V) :
    ∃ c : Ioi (0 : ℝ), potentialForm (fun _ => 1) (scalePositive c f).1 = 1 := by
  let q := potentialForm (fun _ => 1) f.1
  have hb : f.1 b * f.1 b ≤ q := by
    simpa only [q, potentialForm, one_mul] using (Finset.single_le_sum
      (f := fun u => f.1 u * f.1 u) (fun u _ => mul_self_nonneg (f.1 u)) (Finset.mem_univ b))
  have hq : 0 < q := (mul_pos (f.2 b) (f.2 b)).trans_le hb
  let c : Ioi (0 : ℝ) := ⟨(Real.sqrt q)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hq)⟩
  have he : potentialForm (fun _ => 1) (scalePositive c f).1 = (c : ℝ) ^ 2 * q := by
    simp only [potentialForm, q, one_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    change ((c : ℝ) * f.1 u) * ((c : ℝ) * f.1 u) = (c : ℝ) ^ 2 * (f.1 u * f.1 u)
    ring
  refine ⟨c, he.trans ?_⟩
  change ((Real.sqrt q)⁻¹) ^ 2 * q = 1
  rw [inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']

/-- Compatible potential fields when the data are one energy and the trace
of a positive ground state, normalized at a site in the observed patch. -/
def localGroundPotentials (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) : Set (V → ℝ) :=
  {a | ∃ g : PositiveAmplitude V, G.IsGroundAt a E g.1 ∧
    EqOn (fun u => g.1 u / g.1 b) (fun u => f.1 u / f.1 b) (S : Set V)}

omit [DecidableEq V] in
/-- Every positive extension of the trace realizes a compatible
potential field after global normalization of the ground state. -/
theorem localGroundPotentials_eq_trace (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) :
    G.localGroundPotentials S b f E = (fun g : PositiveAmplitude V => G.inversePotential g E) ''
      {g : PositiveAmplitude V | EqOn g.1 f.1 (S : Set V)} := by
  ext a
  constructor
  · rintro ⟨g, ha, hg⟩
    obtain ⟨c, hc, -⟩ := (eqOn_localAmplitudeRatio_iff S b f g).mp hg
    have hpot : a = G.inversePotential g E :=
      (G.isGroundAt_positive_iff ⟨g, ha.1⟩ a E).mp ha
    refine ⟨scalePositive c g, hc, ?_⟩
    funext v
    exact (G.inversePotential_scalePositive c g E v).trans (congrFun hpot v).symm
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := exists_normalized_scalePositive g b
    let h := scalePositive c g
    refine ⟨h, ?_, ?_⟩
    · have ha := G.inversePotential_ground ⟨h, hc⟩ E
      have he : G.inversePotential h E = G.inversePotential g E :=
        funext fun v => G.inversePotential_scalePositive c g E v
      change G.IsGroundAt (G.inversePotential h E) E h.1 at ha
      rwa [he] at ha
    · intro u hu
      change (scalePositive c g).1 u / (scalePositive c g).1 b = f.1 u / f.1 b
      rw [scalePositive_ratio, hg hu, hg b.2]

/-- The set of potential values at a site of a compatible ground state. -/
def localGroundPotentialValues (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) : Set ℝ :=
  (fun a : V → ℝ => a v) '' G.localGroundPotentials S b f E

omit [DecidableEq V] in
theorem localGroundPotentialValues_eq_trace (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    G.localGroundPotentialValues S b f E v = G.localTracePotentialValues S f E v := by
  simp only [localGroundPotentialValues, G.localGroundPotentials_eq_trace, Set.image_image,
    localTracePotentialValues]

/-- The potential coordinate compatible with the local ground eigenpair is
either fixed or ranges over the entire open half-line above its floor. -/
theorem localGroundPotentialValues_eq (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    G.localGroundPotentialValues S b f E v =
      if 0 < G.localTracePotentialMissingWeight S v then Ioi (G.localTracePotentialFloor S f E v)
      else {G.localTracePotentialFloor S f E v} :=
  (G.localGroundPotentialValues_eq_trace S b f E v).trans (G.localTracePotentialValues_eq S f E v)

/-- The local ground-state data identify a site potential exactly at an
isolated site or an observed site with all its neighbors observed. -/
theorem localGroundPotentialValues_subsingleton_iff (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) (v : V) :
    (G.localGroundPotentialValues S b f E v).Subsingleton ↔
      G.mass v = 0 ∨ (v ∈ S ∧ ∀ u, 0 < G.w v u → u ∈ S) := by
  rw [G.localGroundPotentialValues_eq_trace, G.localTracePotentialValues_subsingleton_iff]

/-- The energy and local ground-state trace determine the whole potential
field exactly when all unobserved sites are isolated. -/
theorem localGroundPotentials_subsingleton_iff (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) :
    (G.localGroundPotentials S b f E).Subsingleton ↔ ∀ v ∉ S, G.mass v = 0 := by
  constructor
  · intro h v hv
    have hs : (G.localGroundPotentialValues S b f E v).Subsingleton := by
      rintro z ⟨a, ha, rfl⟩ w ⟨c, hc, rfl⟩
      exact congrFun (h ha hc) v
    exact ((G.localGroundPotentialValues_subsingleton_iff S b f E v).mp hs).resolve_right
      (fun hv' => hv hv'.1)
  · intro h a ha c hc
    funext v
    have hsite : G.mass v = 0 ∨ (v ∈ S ∧ ∀ u, 0 < G.w v u → u ∈ S) := by
      by_cases hv : v ∈ S
      · refine Or.inr ⟨hv, fun u hw => ?_⟩
        by_contra hu
        have hsum : (∑ w, G.w u w) = 0 := h u hu
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => G.w_nonneg u w)).mp
          hsum v (Finset.mem_univ v)
        exact hw.ne' ((G.w_symm v u).trans hzero)
      · exact Or.inl (h v hv)
    exact (G.localGroundPotentialValues_subsingleton_iff S b f E v).mpr hsite
      ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩

/-- The potentials on the observed patch have the exact joint range of the
affine map from the unobserved positive amplitudes. -/
theorem image_localGroundPotentials_observed_eq_range (G : WeightedGraph V) (S : Finset V) (b : ↥S)
    (f : PositiveAmplitude V) (E : ℝ) :
    (fun a : V → ℝ => fun v : ↥S => a v) '' G.localGroundPotentials S b f E =
      Set.range (fun q : PositiveAmplitude V => fun v : ↥S =>
        G.localTracePotentialFloor S f E v + (∑ u ∈ Sᶜ, G.w v u * q.1 u) / f.1 v) := by
  rw [G.localGroundPotentials_eq_trace]
  ext p
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, ?_⟩
    funext v
    exact (G.inversePotential_eq_localTraceFloor_add_hidden S f g E v v.2 hg).symm
  · rintro ⟨q, rfl⟩
    let g : PositiveAmplitude V := ⟨fun u => if u ∈ S then f.1 u else q.1 u, by
      intro u
      change 0 < (if u ∈ S then f.1 u else q.1 u)
      split_ifs
      · exact f.2 u
      · exact q.2 u⟩
    have hg : EqOn g.1 f.1 (S : Set V) := fun u hu => if_pos hu
    refine ⟨G.inversePotential g E, ⟨g, hg, rfl⟩, ?_⟩
    funext v
    change G.inversePotential g E v =
      G.localTracePotentialFloor S f E v + (∑ u ∈ Sᶜ, G.w v u * q.1 u) / f.1 v
    rw [G.inversePotential_eq_localTraceFloor_add_hidden S f g E v v.2 hg]
    have he : (∑ u ∈ Sᶜ, G.w v u * g.1 u) = ∑ u ∈ Sᶜ, G.w v u * q.1 u :=
      Finset.sum_congr rfl fun u hu => congrArg (G.w v u * ·) (if_neg (Finset.mem_compl.mp hu))
    rw [he]

/-- The coefficient of one unobserved amplitude in a linear combination
of potentials at observed sites. -/
def localTraceAmplitudeCoefficient (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (γ : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ S, γ v * (G.w v u / f.1 v)

/-- The observed potential vector is affine in the unobserved amplitudes. -/
theorem sum_mul_inversePotential_sub_localTraceFloor (G : WeightedGraph V) (S : Finset V)
    (f g : PositiveAmplitude V) (E : ℝ) (γ : V → ℝ)
    (hg : EqOn g.1 f.1 (S : Set V)) :
    ∑ v ∈ S, γ v * (G.inversePotential g E v - G.localTracePotentialFloor S f E v) =
      ∑ u ∈ Sᶜ, G.localTraceAmplitudeCoefficient S f γ u * g.1 u := by
  calc
    _ = ∑ v ∈ S, ∑ u ∈ Sᶜ, (γ v * (G.w v u / f.1 v)) * g.1 u := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [G.inversePotential_eq_localTraceFloor_add_hidden S f g E v hv hg,
        add_sub_cancel_left, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm

/-- A linear combination of observed potentials is determined by the trace
precisely when every unobserved amplitude has coefficient zero. -/
theorem localTraceLinearCombination_identifiable_iff (G : WeightedGraph V) (S : Finset V)
    (f : PositiveAmplitude V) (E : ℝ) (γ : V → ℝ) :
    (∀ g : PositiveAmplitude V, EqOn g.1 f.1 (S : Set V) →
      (∑ v ∈ S, γ v * G.inversePotential g E v) = ∑ v ∈ S, γ v * G.inversePotential f E v) ↔
      ∀ u ∉ S, G.localTraceAmplitudeCoefficient S f γ u = 0 := by
  let P (g : PositiveAmplitude V) := ∑ v ∈ S, γ v * G.inversePotential g E v
  let Q := ∑ v ∈ S, γ v * G.localTracePotentialFloor S f E v
  let A := G.localTraceAmplitudeCoefficient S f γ
  have he (g : PositiveAmplitude V) (hg : EqOn g.1 f.1 (S : Set V)) :
      P g - Q = ∑ u ∈ Sᶜ, A u * g.1 u := by
    simpa only [P, Q, A, mul_sub, Finset.sum_sub_distrib] using
      G.sum_mul_inversePotential_sub_localTraceFloor S f g E γ hg
  change (∀ g : PositiveAmplitude V, EqOn g.1 f.1 (S : Set V) → P g = P f) ↔
    ∀ u ∉ S, A u = 0
  constructor
  · intro h u hu
    let g : PositiveAmplitude V := ⟨Function.update f.1 u (f.1 u + 1), by
      intro x
      by_cases hx : x = u
      · subst x
        rw [Function.update_self]
        exact add_pos (f.2 u) one_pos
      · rw [Function.update_of_ne hx]
        exact f.2 x⟩
    have hg : EqOn g.1 f.1 (S : Set V) := by
      intro x hx
      exact Function.update_of_ne (fun hxu : x = u => hu (hxu ▸ hx)) _ _
    have hsum : (∑ x ∈ Sᶜ, A x * g.1 x) = ∑ x ∈ Sᶜ, A x * f.1 x :=
      (he g hg).symm.trans ((congrArg (· - Q) (h g hg)).trans (he f fun _ _ => rfl))
    have hz : (∑ x ∈ Sᶜ, (A x * g.1 x - A x * f.1 x)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    rw [Finset.sum_eq_single u] at hz
    · change A u * Function.update f.1 u (f.1 u + 1) u - A u * f.1 u = 0 at hz
      rwa [Function.update_self, mul_add, mul_one, add_sub_cancel_left] at hz
    · intro x hx hxu
      change A x * Function.update f.1 u (f.1 u + 1) x - A x * f.1 x = 0
      rw [Function.update_of_ne hxu, sub_self]
    · exact fun hu' => (hu' (Finset.mem_compl.mpr hu)).elim
  · intro h g hg
    have hzero (p : PositiveAmplitude V) : (∑ u ∈ Sᶜ, A u * p.1 u) = 0 := by
      exact Finset.sum_eq_zero fun u hu => by rw [h u (Finset.mem_compl.mp hu), zero_mul]
    have h₁ := (he g hg).trans (hzero g)
    have h₂ := (he f fun _ _ => rfl).trans (hzero f)
    linarith only [h₁, h₂]

#print axioms inversePotential_eq_localTraceFloor_add_hidden
#print axioms localTracePotentialValues_eq
#print axioms localTracePotentialValues_subsingleton_iff
#print axioms eqOn_localAmplitudeRatio_iff
#print axioms localGroundPotentials_eq_trace
#print axioms localGroundPotentialValues_eq
#print axioms localGroundPotentials_subsingleton_iff
#print axioms image_localGroundPotentials_observed_eq_range
#print axioms sum_mul_inversePotential_sub_localTraceFloor
#print axioms localTraceLinearCombination_identifiable_iff

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
