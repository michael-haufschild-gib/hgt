import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.EntropyBoundaryAsymptotics
import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphBoundaryFlow
import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphPropagation

/-!
# Initial free-energy loss for finite Pauli-blocked transport

An initially empty or full site contributes to the logarithmic
free-energy loss through its inward initial current. The sum of these
currents detects exactly the active boundary edges.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

variable {V : Type*} [Fintype V]

/-- Inward derivative at an empty or full coordinate. Interior
coordinates contribute zero on the logarithmic scale. -/
def boundaryEntropyRate (G : WeightedGraph V) (E f : V → ℝ) (v : V) : ℝ :=
  if f v = 0 then clippedDrift G E f v
  else if f v = 1 then -clippedDrift G E f v else 0

/-- Coefficient of the initial free-energy loss on the scale of negative time times log time. -/
def boundaryEntropyCoefficient (G : WeightedGraph V) (E f : V → ℝ) : ℝ :=
  ∑ v, boundaryEntropyRate G E f v

/-- An edge is active at the boundary if it can supply a particle to an
empty site or a vacancy to a full site. -/
def HasActiveBoundaryEdge (G : WeightedGraph V) (f : V → ℝ) : Prop :=
  ∃ v u, 0 < G.w v u ∧ ((f v = 0 ∧ 0 < f u) ∨ (f v = 1 ∧ f u < 1))

theorem boundaryEntropyRate_at_empty (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) {v : V} (hv : f v = 0) :
    boundaryEntropyRate G E f v = ∑ u, G.w v u * Real.exp (E u) * f u := by
  rw [boundaryEntropyRate, if_pos hv, clippedDrift_eq_of_box G E f hf v, hv]
  simp only [sub_zero, mul_one, mul_zero, zero_mul]

theorem boundaryEntropyRate_at_full (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) {v : V} (hv : f v = 1) :
    boundaryEntropyRate G E f v = ∑ u, G.w v u * Real.exp (E v) * (1 - f u) := by
  have hv₀ : f v ≠ 0 := by rw [hv]; exact one_ne_zero
  rw [boundaryEntropyRate, if_neg hv₀, if_pos hv, clippedDrift_eq_of_box G E f hf v, hv]
  simp only [sub_self, mul_zero, one_mul, zero_sub, Finset.sum_neg_distrib, neg_neg]

theorem boundaryEntropyRate_nonneg (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) (v : V) : 0 ≤ boundaryEntropyRate G E f v := by
  by_cases h₀ : f v = 0
  · rw [boundaryEntropyRate_at_empty G E f hf h₀]
    exact Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le) (hf u).1
  by_cases h₁ : f v = 1
  · rw [boundaryEntropyRate_at_full G E f hf h₁]
    exact Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le) (sub_nonneg.mpr (hf u).2)
  simp only [boundaryEntropyRate, if_neg h₀, if_neg h₁, le_refl]

theorem boundaryEntropyCoefficient_nonneg (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) : 0 ≤ boundaryEntropyCoefficient G E f :=
  Finset.sum_nonneg fun v _ => boundaryEntropyRate_nonneg G E f hf v

private theorem sum_mul_pos_iff (a b : V → ℝ) (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) :
    (0 < ∑ u, a u * b u) ↔ ∃ u, 0 < a u ∧ 0 < b u := by
  constructor
  · intro hs
    have hex : ∃ u, 0 < a u * b u := by
      by_contra! h
      exact (not_le_of_gt hs) (Finset.sum_nonpos fun u _ => h u)
    obtain ⟨u, hu⟩ := hex
    exact ⟨u, pos_of_mul_pos_left hu (hb u), pos_of_mul_pos_right hu (ha u)⟩
  · rintro ⟨u, h₁, h₂⟩
    exact (mul_pos h₁ h₂).trans_le
      (Finset.single_le_sum (fun w _ => mul_nonneg (ha w) (hb w)) (Finset.mem_univ u))

theorem boundaryEntropyRate_pos_iff (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) (v : V) :
    0 < boundaryEntropyRate G E f v ↔
      ∃ u, 0 < G.w v u ∧ ((f v = 0 ∧ 0 < f u) ∨ (f v = 1 ∧ f u < 1)) := by
  have hexp (u : V) (e : ℝ) : 0 < G.w v u * Real.exp e ↔ 0 < G.w v u :=
    ⟨fun h => pos_of_mul_pos_left h (Real.exp_pos _).le, fun h => mul_pos h (Real.exp_pos _)⟩
  by_cases h₀ : f v = 0
  · rw [boundaryEntropyRate_at_empty G E f hf h₀,
      sum_mul_pos_iff _ _ (fun u => mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le) (fun u => (hf u).1)]
    simp only [hexp, h₀, zero_ne_one, true_and, false_and, or_false]
  by_cases h₁ : f v = 1
  · rw [boundaryEntropyRate_at_full G E f hf h₁,
      sum_mul_pos_iff _ _ (fun u => mul_nonneg (G.w_nonneg v u) (Real.exp_pos _).le)
        (fun u => sub_nonneg.mpr (hf u).2)]
    simp only [hexp, h₁, one_ne_zero, true_and, false_and, false_or, sub_pos]
  rw [boundaryEntropyRate, if_neg h₀, if_neg h₁]
  simp only [lt_irrefl, h₀, h₁, false_and, or_self, and_false, exists_false]

/-- The logarithmic coefficient is positive exactly when an edge supplies
an initially empty or full site. -/
theorem boundaryEntropyCoefficient_pos_iff (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ u, f u ∈ Icc (0 : ℝ) 1) :
    0 < boundaryEntropyCoefficient G E f ↔ HasActiveBoundaryEdge G f := by
  have hsum := sum_mul_pos_iff (fun _ : V => (1 : ℝ)) (boundaryEntropyRate G E f)
    (fun _ => zero_le_one) (boundaryEntropyRate_nonneg G E f hf)
  simp only [one_mul, zero_lt_one, true_and] at hsum
  unfold boundaryEntropyCoefficient HasActiveBoundaryEdge
  rw [hsum]
  exact exists_congr fun v => boundaryEntropyRate_pos_iff G E f hf v

/-- For binary initial occupation, each full-to-empty edge contributes
the same current to both endpoints of the entropy coefficient. -/
theorem boundaryEntropyCoefficient_eq_binary_cut (G : WeightedGraph V) (E f : V → ℝ)
    (hf : ∀ v, f v = 0 ∨ f v = 1) :
    boundaryEntropyCoefficient G E f =
      2 * ∑ v, ∑ u, if f v = 1 ∧ f u = 0 then G.w v u * Real.exp (E v) else 0 := by
  let J (v u : V) := if f v = 1 ∧ f u = 0 then G.w v u * Real.exp (E v) else 0
  have hbox (v : V) : f v ∈ Icc (0 : ℝ) 1 := by
    rcases hf v with h₀ | h₁
    · rw [h₀]
      exact ⟨le_rfl, zero_le_one⟩
    · rw [h₁]
      exact ⟨zero_le_one, le_rfl⟩
  have hj (v : V) : boundaryEntropyRate G E f v = (∑ u, J v u) + ∑ u, J u v := by
    rcases hf v with h₀ | h₁
    · have hout : (∑ u, J v u) = 0 := Finset.sum_eq_zero fun u _ => by simp [J, h₀]
      rw [boundaryEntropyRate_at_empty G E f hbox h₀, hout, zero_add]
      refine Finset.sum_congr rfl fun u _ => ?_
      rcases hf u with hu | hu
      · simp [J, h₀, hu]
      · simp [J, h₀, hu, G.w_symm u v]
    · have hin : (∑ u, J u v) = 0 := Finset.sum_eq_zero fun u _ => by simp [J, h₁]
      rw [boundaryEntropyRate_at_full G E f hbox h₁, hin, add_zero]
      refine Finset.sum_congr rfl fun u _ => ?_
      rcases hf u with hu | hu <;> simp [J, h₁, hu]
  have hswap : (∑ v, ∑ u, J u v) = ∑ v, ∑ u, J v u := Finset.sum_comm
  change (∑ v, boundaryEntropyRate G E f v) = 2 * ∑ v, ∑ u, J v u
  simp only [hj, Finset.sum_add_distrib, hswap, two_mul]

variable {G : WeightedGraph V} {E : V → ℝ} {x : ℝ → V → ℝ}

private theorem eventually_occupation_in_box (h : IsBoxOccupationFlow G E x) (v : V) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x t v ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h.in_box t (mem_Ioi.mp ht).le v

private theorem eventually_vacancy_in_box (h : IsBoxOccupationFlow G E x) (v : V) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 1 - x t v ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [eventually_occupation_in_box h v] with t ht
  exact ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩

private theorem hasDerivAt_initial_entropy (h : IsBoxOccupationFlow G E x) (v : V)
    (h₀ : x 0 v ≠ 0) (h₁ : x 0 v ≠ 1) :
    HasDerivAt (fun s => Real.binEntropy (x s v))
      ((Real.log (1 - x 0 v) - Real.log (x 0 v)) * clippedDrift G E (x 0) v) 0 := by
  change HasDerivAt (Real.binEntropy ∘ fun s => x s v) _ 0
  exact (Real.hasDerivAt_binEntropy h₀ h₁).comp 0 (h.hasDerivAt_coordinate 0 le_rfl v)

/-- Coordinate entropy picks out the inward derivative exactly at the endpoints. -/
theorem IsBoxOccupationFlow.tendsto_entropy_change_log_scaled (h : IsBoxOccupationFlow G E x)
    (v : V) :
    Tendsto (fun t : ℝ => (Real.binEntropy (x t v) - Real.binEntropy (x 0 v)) / (t * -Real.log t))
      (𝓝[>] 0) (𝓝 (boundaryEntropyRate G E (x 0) v)) := by
  have hd := h.hasDerivAt_coordinate 0 le_rfl v
  by_cases h₀ : x 0 v = 0
  · have hscale : Tendsto (fun t : ℝ => x t v / t ^ 1) (𝓝[>] 0)
        (𝓝 (clippedDrift G E (x 0) v)) := by
      simpa only [h₀, sub_zero, pow_one] using tendsto_right_difference_quotient hd
    have he := tendsto_binEntropy_div_pow_mul_neg_log (fun t => x t v) 1 (eventually_occupation_in_box h v) hscale
    rw [boundaryEntropyRate, if_pos h₀]
    simpa only [h₀, Real.binEntropy_zero, sub_zero, pow_one, Nat.cast_one, one_mul] using he
  by_cases h₁ : x 0 v = 1
  · have hscale : Tendsto (fun t : ℝ => (1 - x t v) / t ^ 1) (𝓝[>] 0)
        (𝓝 (-clippedDrift G E (x 0) v)) := by
      simpa only [h₁, sub_self, sub_zero, pow_one] using
        tendsto_right_difference_quotient (hd.const_sub 1)
    have he := tendsto_binEntropy_div_pow_mul_neg_log (fun t => 1 - x t v) 1
      (eventually_vacancy_in_box h v) hscale
    have hz : x 0 v ≠ 0 := by rw [h₁]; exact one_ne_zero
    rw [boundaryEntropyRate, if_neg hz, if_pos h₁]
    simpa only [h₁, Real.binEntropy_one_sub, Real.binEntropy_one, sub_zero, pow_one, Nat.cast_one,
      one_mul] using he
  simpa only [boundaryEntropyRate, if_neg h₀, if_neg h₁] using
    tendsto_right_log_scaled_difference_of_deriv (hasDerivAt_initial_entropy h v h₀ h₁)

/-- Initial free-energy loss is asymptotic on the negative time-log-time
scale to the sum of inward currents at the initially saturated sites. -/
theorem IsBoxOccupationFlow.tendsto_freeEnergy_log_loss (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => (freeEnergy E (x 0) - freeEnergy E (x t)) / (t * -Real.log t))
      (𝓝[>] 0) (𝓝 (boundaryEntropyCoefficient G E (x 0))) := by
  have hv (v : V) : Tendsto (fun t : ℝ =>
      (Real.binEntropy (x t v) - Real.binEntropy (x 0 v)) / (t * -Real.log t) -
        (E v * x t v - E v * x 0 v) / (t * -Real.log t))
      (𝓝[>] 0) (𝓝 (boundaryEntropyRate G E (x 0) v)) := by
    have he := tendsto_right_log_scaled_difference_of_deriv
      ((h.hasDerivAt_coordinate 0 le_rfl v).const_mul (E v))
    simpa only [sub_zero] using (h.tendsto_entropy_change_log_scaled v).sub he
  have hs := tendsto_finsetSum Finset.univ (fun v _ => hv v)
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  change _ = (freeEnergy E (x 0) - freeEnergy E (x t)) / (t * -Real.log t)
  unfold freeEnergy
  conv_rhs => rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- An active boundary edge forces the initial free-energy right slope to minus infinity. -/
theorem IsBoxOccupationFlow.tendsto_freeEnergy_right_slope_atBot (h : IsBoxOccupationFlow G E x)
    (he : HasActiveBoundaryEdge G (x 0)) :
    Tendsto (fun t : ℝ => (freeEnergy E (x t) - freeEnergy E (x 0)) / t) (𝓝[>] 0) atBot :=
  tendsto_right_slope_atBot_of_log_loss
    ((boundaryEntropyCoefficient_pos_iff G E _ (h.in_box 0 le_rfl)).mpr he)
    h.tendsto_freeEnergy_log_loss

/-- With no active boundary edge, each initially saturated coordinate
lies in a zero cut and stays at its initial endpoint. -/
theorem IsBoxOccupationFlow.boundary_constant_of_no_active_edge (h : IsBoxOccupationFlow G E x)
    (hno : ¬ HasActiveBoundaryEdge G (x 0)) (v : V) (hv : x 0 v = 0 ∨ x 0 v = 1)
    {t : ℝ} (ht : 0 ≤ t) : x t v = x 0 v := by
  classical
  let S := Finset.univ.filter fun u => x 0 u = x 0 v
  have hm (u : V) : u ∈ S ↔ x 0 u = x 0 v := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcut : ∀ a ∈ S, ∀ b ∉ S, G.w a b = 0 := by
    intro a ha b hb
    apply le_antisymm _ (G.w_nonneg a b)
    by_contra! hpos
    have hab : x 0 a = x 0 v := (hm a).mp ha
    have hne : x 0 b ≠ x 0 v := fun he => hb ((hm b).mpr he)
    apply hno
    refine ⟨a, b, hpos, ?_⟩
    rcases hv with h₀ | h₁
    · have hposb : 0 < x 0 b :=
        lt_of_le_of_ne (h.in_box 0 le_rfl b).1 (fun he => hne (he.symm.trans h₀.symm))
      exact Or.inl ⟨hab.trans h₀, hposb⟩
    · have hltb : x 0 b < 1 :=
        lt_of_le_of_ne (h.in_box 0 le_rfl b).2 (fun he => hne (he.trans h₁.symm))
      exact Or.inr ⟨hab.trans h₁, hltb⟩
  have hvS : v ∈ S := (hm v).mpr rfl
  have hmass := h.mass_on_zero_cut S hcut ht
  rcases hv with h₀ | h₁
  · have hz : (∑ u ∈ S, x 0 u) = 0 :=
      Finset.sum_eq_zero fun u hu => ((hm u).mp hu).trans h₀
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => (h.in_box t ht u).1)).mp
      (hmass.trans hz) v hvS
    exact he.trans h₀.symm
  · have hmass' : (∑ u ∈ S, (1 - x t u)) = ∑ u ∈ S, (1 - x 0 u) := by
      simp only [Finset.sum_sub_distrib, hmass]
    have hz : (∑ u ∈ S, (1 - x 0 u)) = 0 :=
      Finset.sum_eq_zero fun u hu => sub_eq_zero.mpr (((hm u).mp hu).trans h₁).symm
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => sub_nonneg.mpr (h.in_box t ht u).2)).mp
      (hmass'.trans hz) v hvS
    exact (sub_eq_zero.mp he).symm.trans h₁.symm

/-- With no active boundary edge, the initial right derivative is the
finite sum of chemical-potential power at interior coordinates. -/
theorem IsBoxOccupationFlow.tendsto_freeEnergy_right_slope_of_no_active_edge
    (h : IsBoxOccupationFlow G E x) (hno : ¬ HasActiveBoundaryEdge G (x 0)) :
    Tendsto (fun t : ℝ => (freeEnergy E (x t) - freeEnergy E (x 0)) / t) (𝓝[>] 0)
      (𝓝 (∑ v, if x 0 v = 0 ∨ x 0 v = 1 then 0 else
        (E v + Real.log (x 0 v) - Real.log (1 - x 0 v)) * clippedDrift G E (x 0) v)) := by
  let f (v : V) (s : ℝ) := E v * x s v - Real.binEntropy (x s v)
  let d (v : V) := if x 0 v = 0 ∨ x 0 v = 1 then 0 else
    (E v + Real.log (x 0 v) - Real.log (1 - x 0 v)) * clippedDrift G E (x 0) v
  have hv (v : V) : Tendsto (fun t : ℝ => (f v t - f v 0) / t) (𝓝[>] 0) (𝓝 (d v)) := by
    by_cases hb : x 0 v = 0 ∨ x 0 v = 1
    · have hd : d v = 0 := if_pos hb
      rw [hd]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have he := h.boundary_constant_of_no_active_edge hno v hb (mem_Ioi.mp ht).le
      simp only [f, he, sub_self, zero_div]
    · have h₀ : x 0 v ≠ 0 := fun hz => hb (Or.inl hz)
      have h₁ : x 0 v ≠ 1 := fun hz => hb (Or.inr hz)
      have hh := ((h.hasDerivAt_coordinate 0 le_rfl v).const_mul (E v)).sub
        (hasDerivAt_initial_entropy h v h₀ h₁)
      have he : E v * clippedDrift G E (x 0) v -
          (Real.log (1 - x 0 v) - Real.log (x 0 v)) * clippedDrift G E (x 0) v = d v := by
        simp only [d, if_neg hb]
        ring
      rw [he] at hh
      exact tendsto_right_difference_quotient hh
  have hs := tendsto_finsetSum Finset.univ (fun v _ => hv v)
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  change _ = (freeEnergy E (x t) - freeEnergy E (x 0)) / t
  unfold freeEnergy
  conv_rhs => rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => div_eq_mul_inv _ _

/-- The ordinary initial right slope diverges to minus infinity
exactly when there is an active boundary edge. -/
theorem IsBoxOccupationFlow.freeEnergy_right_slope_atBot_iff (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => (freeEnergy E (x t) - freeEnergy E (x 0)) / t) (𝓝[>] 0) atBot ↔
      HasActiveBoundaryEdge G (x 0) := by
  constructor
  · intro hbot
    by_contra hno
    obtain ⟨b, hfin⟩ : ∃ b : ℝ,
        Tendsto (fun t : ℝ => (freeEnergy E (x t) - freeEnergy E (x 0)) / t) (𝓝[>] 0) (𝓝 b) :=
      ⟨_, h.tendsto_freeEnergy_right_slope_of_no_active_edge hno⟩
    have hgt := (tendsto_order.mp hfin).1 (b - 1) (by linarith)
    have hle := (tendsto_atBot.mp hbot) (b - 1)
    obtain ⟨_, hgt, hle⟩ := (hgt.and hle).exists
    exact (not_lt_of_ge hle) hgt
  · exact h.tendsto_freeEnergy_right_slope_atBot

/-- In a connected graph of nontrivial mass, the singular initial
free-energy loss occurs exactly when there is a saturated site. -/
theorem IsBoxOccupationFlow.boundaryEntropyCoefficient_pos_iff_saturated
    (h : IsBoxOccupationFlow G E x) (root : V)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    (hm : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ)) :
    0 < boundaryEntropyCoefficient G E (x 0) ↔ ∃ v, x 0 v = 0 ∨ x 0 v = 1 := by
  rw [boundaryEntropyCoefficient_pos_iff G E _ (h.in_box 0 le_rfl)]
  constructor
  · rintro ⟨v, _, _, hv⟩
    rcases hv with hv | hv
    · exact ⟨v, Or.inl hv.1⟩
    · exact ⟨v, Or.inr hv.1⟩
  · rintro ⟨v, hv⟩
    by_contra hno
    have hc := h.boundary_constant_of_no_active_edge hno v hv (t := 1) zero_le_one
    have hi := h.interior_of_nontrivial_mass root hpath hm 1 one_pos v
    rw [hc] at hi
    rcases hv with hv | hv
    · exact hi.1.ne' hv
    · exact hi.2.ne hv

/-- Particle arrival along a shortest walk gives the corresponding
higher-order entropy coefficient at that site. -/
theorem IsBoxOccupationFlow.tendsto_entropy_at_particle_arrival (h : IsBoxOccupationFlow G E x)
    (n : ℕ) (v : V) (hshort : ∀ j < n, ∀ u, PositiveEdgeWalk G j u v → x 0 u = 0)
    (hseed : ∃ u, PositiveEdgeWalk G n u v ∧ 0 < x 0 u) :
    Tendsto (fun t : ℝ => Real.binEntropy (x t v) / (t ^ n * -Real.log t)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * (ratePower (particleRate G E) (x 0) n v / (n.factorial : ℝ)))) :=
  tendsto_binEntropy_div_pow_mul_neg_log (fun t => x t v) n
    (eventually_occupation_in_box h v) (h.particle_first_arrival n v hshort hseed).2

/-- Vacancy arrival gives the same entropy law with transposed rates. -/
theorem IsBoxOccupationFlow.tendsto_entropy_at_vacancy_arrival (h : IsBoxOccupationFlow G E x)
    (n : ℕ) (v : V) (hshort : ∀ j < n, ∀ u, PositiveEdgeWalk G j u v → 1 - x 0 u = 0)
    (hseed : ∃ u, PositiveEdgeWalk G n u v ∧ 0 < 1 - x 0 u) :
    let r := fun u w => particleRate G E w u
    Tendsto (fun t : ℝ => Real.binEntropy (x t v) / (t ^ n * -Real.log t)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * (ratePower r (fun u => 1 - x 0 u) n v / (n.factorial : ℝ)))) := by
  have he := tendsto_binEntropy_div_pow_mul_neg_log (fun t => 1 - x t v) n
    (eventually_vacancy_in_box h v) (h.vacancy_first_arrival n v hshort hseed).2
  simpa only [Real.binEntropy_one_sub] using he

#print axioms boundaryEntropyCoefficient_pos_iff
#print axioms boundaryEntropyCoefficient_eq_binary_cut
#print axioms IsBoxOccupationFlow.tendsto_freeEnergy_log_loss
#print axioms IsBoxOccupationFlow.tendsto_freeEnergy_right_slope_atBot
#print axioms IsBoxOccupationFlow.boundary_constant_of_no_active_edge
#print axioms IsBoxOccupationFlow.tendsto_freeEnergy_right_slope_of_no_active_edge
#print axioms IsBoxOccupationFlow.freeEnergy_right_slope_atBot_iff
#print axioms IsBoxOccupationFlow.boundaryEntropyCoefficient_pos_iff_saturated
#print axioms IsBoxOccupationFlow.tendsto_entropy_at_particle_arrival
#print axioms IsBoxOccupationFlow.tendsto_entropy_at_vacancy_arrival

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
