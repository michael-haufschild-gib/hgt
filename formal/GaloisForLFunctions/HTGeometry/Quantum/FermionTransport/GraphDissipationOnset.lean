import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphEntropyOnset

/-!
# Initial dissipation of finite Pauli-blocked transport

At an initially saturated site, the chemical potential can have a
logarithmic singularity. Its product with the velocity retains only
the initial inward current. The same coefficient governs the
instantaneous dissipation and the initial free-energy loss.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

private theorem tendsto_log_div_neg_log_of_ne_zero {p : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0)
    (hp : Tendsto p (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => Real.log (p t) / -Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hlog := (Real.continuousAt_log ha).tendsto.comp hp
  simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using hlog.mul tendsto_inv_neg_log_right

private theorem nonneg_of_right_limit_of_eventually_nonneg {p : ℝ → ℝ} {a : ℝ}
    (hp : Tendsto p (𝓝[>] 0) (𝓝 a)) (hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ p t) : 0 ≤ a := by
  by_contra! hneg
  have he := (tendsto_order.mp hp).2 0 hneg
  obtain ⟨_, hlt, hle⟩ := (he.and hn).exists
  exact (not_le_of_gt hlt) hle

/-- A positive leading coefficient of order `t^n` gives logarithmic
slope `-n` when normalized by `-log t`. -/
theorem tendsto_log_div_neg_log_of_power (p : ℝ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (hp : Tendsto (fun t : ℝ => p t / t ^ n) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => Real.log (p t) / -Real.log t) (𝓝[>] 0) (𝓝 (-(n : ℝ))) := by
  let r (t : ℝ) := p t / t ^ n
  have hr : Tendsto r (𝓝[>] 0) (𝓝 a) := hp
  have hc := tendsto_log_div_neg_log_of_ne_zero ha.ne' hr
  have hconst : Tendsto (fun _ : ℝ => (n : ℝ)) (𝓝[>] 0) (𝓝 (n : ℝ)) := tendsto_const_nhds
  have hs : Tendsto (fun t : ℝ => Real.log (r t) / -Real.log t - (n : ℝ))
      (𝓝[>] 0) (𝓝 (-(n : ℝ))) := by
    simpa only [zero_sub] using hc.sub hconst
  have hrpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < r t := (tendsto_order.mp hr).1 0 ha
  have hlt : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hlt, hrpos] with t ht ht₁ hr₁
  have hpow : 0 < t ^ n := pow_pos (mem_Ioi.mp ht) n
  have he : Real.log (p t) = Real.log (r t) + (n : ℝ) * Real.log t := by
    calc
      _ = Real.log (r t * t ^ n) := congrArg _ (div_mul_cancel₀ _ hpow.ne').symm
      _ = _ := by rw [Real.log_mul hr₁.ne' hpow.ne', Real.log_pow]
  have hn : Real.log t ≠ 0 := (Real.log_neg (mem_Ioi.mp ht) (mem_Iio.mp ht₁)).ne
  change Real.log (r t) / -Real.log t - (n : ℝ) = Real.log (p t) / -Real.log t
  rw [he]
  field_simp [hn]
  ring

/-- At a zero initial coordinate the scaled log times the derivative
retains the negative initial derivative. A delayed arrival contributes
zero because its initial derivative vanishes. -/
theorem tendsto_log_scaled_derivative (p dp : ℝ → ℝ) {d : ℝ} (hp : HasDerivAt p d 0)
    (hd : Tendsto dp (𝓝[>] 0) (𝓝 d))
    (hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ p t)
    (hshape : p 0 = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), p t = 0) ∨
      ∃ (n : ℕ) (a : ℝ), 0 < a ∧ Tendsto (fun t : ℝ => p t / t ^ n) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => Real.log (p t) / -Real.log t * dp t) (𝓝[>] 0)
      (𝓝 (if p 0 = 0 then -d else 0)) := by
  by_cases h₀ : p 0 = 0
  · rw [if_pos h₀]
    by_cases hdz : d = 0
    · simp only [hdz, neg_zero]
      rcases hshape h₀ with hz | ⟨n, a, ha, hs⟩
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hz] with t ht
        simp only [ht, Real.log_zero, zero_div, zero_mul]
      · simpa only [hdz, mul_zero] using (tendsto_log_div_neg_log_of_power p n ha hs).mul hd
    · have hratio : Tendsto (fun t : ℝ => p t / t) (𝓝[>] 0) (𝓝 d) := by
        simpa only [h₀, sub_zero] using tendsto_right_difference_quotient hp
      have hdpos : 0 < d := by
        refine lt_of_le_of_ne (nonneg_of_right_limit_of_eventually_nonneg hratio ?_) (Ne.symm hdz)
        filter_upwards [hn, self_mem_nhdsWithin] with t hp' ht
        exact div_nonneg hp' (mem_Ioi.mp ht).le
      have hpow : Tendsto (fun t : ℝ => p t / t ^ 1) (𝓝[>] 0) (𝓝 d) := by
        simpa only [pow_one] using hratio
      simpa only [Nat.cast_one, neg_one_mul] using
        (tendsto_log_div_neg_log_of_power p 1 hdpos hpow).mul hd
  · rw [if_neg h₀]
    have hc : Tendsto p (𝓝[>] 0) (𝓝 (p 0)) :=
      hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using (tendsto_log_div_neg_log_of_ne_zero h₀ hc).mul hd

noncomputable section

variable {V : Type*} [Fintype V]

/-- Negative chemical-potential power on the closed Pauli box. The real
logarithm convention is used on the boundary. -/
def boxDissipation (G : WeightedGraph V) (E f : V → ℝ) : ℝ :=
  -(∑ v, (E v + Real.log (f v) - Real.log (1 - f v)) * clippedDrift G E f v)

/-- On interior occupations the box expression is the original
edgewise dissipation. -/
theorem boxDissipation_eq_dissipation (G : WeightedGraph V) (E : V → ℝ) (p : V → Occupation) :
    boxDissipation G E (fun v => (p v : ℝ)) = dissipation G E p := by
  have hbox (v : V) : (p v : ℝ) ∈ Icc 0 1 := ⟨(p v).property.1.le, (p v).property.2.le⟩
  have hd : clippedDrift G E (fun v => (p v : ℝ)) = drift G E p := by
    funext v
    rw [clippedDrift_eq_of_box G E _ hbox v, drift, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [flux_eq_particle_hole]; ring
  have hμ (v : V) :
      E v + Real.log (p v : ℝ) - Real.log (1 - (p v : ℝ)) = chemicalPotential E p v := by
    rw [chemicalPotential, Real.log_div (p v).property.1.ne' (sub_pos.mpr (p v).property.2).ne']
    ring
  unfold boxDissipation
  rw [hd]
  simp_rw [hμ]
  rw [sum_chemicalPotential_mul_drift, neg_neg]

variable {G : WeightedGraph V} {E : V → ℝ} {x : ℝ → V → ℝ}

private def polynomialDrift (G : WeightedGraph V) (E f : V → ℝ) (v : V) : ℝ :=
  ∑ u, (G.w v u * Real.exp (E u) * (f u * (1 - f v)) -
    G.w v u * Real.exp (E v) * (f v * (1 - f u)))

private theorem polynomialDrift_eq (h : IsBoxOccupationFlow G E x) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    polynomialDrift G E (x t) v = clippedDrift G E (x t) v :=
  (clippedDrift_eq_of_box G E _ (h.in_box t ht) v).symm

private theorem differentiableAt_polynomialDrift_zero (h : IsBoxOccupationFlow G E x) (v : V) :
    DifferentiableAt ℝ (fun t => polynomialDrift G E (x t) v) 0 := by
  have hx (u : V) : DifferentiableAt ℝ (fun t : ℝ => x t u) 0 :=
    (h.hasDerivAt_coordinate 0 le_rfl u).differentiableAt
  unfold polynomialDrift
  apply DifferentiableAt.fun_sum
  intro u _
  fun_prop

private theorem tendsto_clippedDrift_coordinate_right (h : IsBoxOccupationFlow G E x) (v : V) :
    Tendsto (fun t : ℝ => clippedDrift G E (x t) v) (𝓝[>] 0) (𝓝 (clippedDrift G E (x 0) v)) := by
  have hp : Tendsto (fun t => polynomialDrift G E (x t) v) (𝓝[>] 0)
      (𝓝 (polynomialDrift G E (x 0) v)) :=
    (differentiableAt_polynomialDrift_zero h v).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [polynomialDrift_eq h v le_rfl] at hp
  refine hp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact polynomialDrift_eq h v (mem_Ioi.mp ht).le

private theorem occupation_zero_of_no_seed (h : IsBoxOccupationFlow G E x) (v : V)
    (hno : ¬ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < x 0 u)
    {t : ℝ} (ht : 0 < t) : x t v = 0 :=
  (le_of_not_gt fun hp => hno ((h.pos_iff_initial_particle v ht).mp hp)).antisymm (h.in_box t ht.le v).1

private theorem vacancy_zero_of_no_seed (h : IsBoxOccupationFlow G E x) (v : V)
    (hno : ¬ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < 1 - x 0 u)
    {t : ℝ} (ht : 0 < t) : 1 - x t v = 0 :=
  (le_of_not_gt fun hp => hno ((h.vacancy_pos_iff_initial_vacancy v ht).mp hp)).antisymm
    (sub_nonneg.mpr (h.in_box t ht.le v).2)

private theorem occupation_zero_or_power (h : IsBoxOccupationFlow G E x) (v : V) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), x t v = 0) ∨
      ∃ (n : ℕ) (a : ℝ), 0 < a ∧ Tendsto (fun t : ℝ => x t v / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  by_cases hs : ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < x 0 u
  · obtain ⟨n, hn⟩ := h.exists_particle_onset_order v hs
    exact Or.inr ⟨n, _, hn.1, hn.2⟩
  · left
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact occupation_zero_of_no_seed h v hs (mem_Ioi.mp ht)

private theorem vacancy_zero_or_power (h : IsBoxOccupationFlow G E x) (v : V) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 1 - x t v = 0) ∨
      ∃ (n : ℕ) (a : ℝ), 0 < a ∧ Tendsto (fun t : ℝ => (1 - x t v) / t ^ n) (𝓝[>] 0) (𝓝 a) := by
  by_cases hs : ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < 1 - x 0 u
  · obtain ⟨n, hn⟩ := h.exists_vacancy_onset_order v hs
    exact Or.inr ⟨n, _, hn.1, hn.2⟩
  · left
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact vacancy_zero_of_no_seed h v hs (mem_Ioi.mp ht)

private theorem tendsto_boxDissipation_site_div_neg_log (h : IsBoxOccupationFlow G E x) (v : V) :
    Tendsto (fun t : ℝ =>
      -((E v + Real.log (x t v) - Real.log (1 - x t v)) * clippedDrift G E (x t) v) / -Real.log t)
      (𝓝[>] 0) (𝓝 (boundaryEntropyRate G E (x 0) v)) := by
  let d (t : ℝ) := clippedDrift G E (x t) v
  have hd : Tendsto d (𝓝[>] 0) (𝓝 (d 0)) := tendsto_clippedDrift_coordinate_right h v
  have hp₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x t v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.in_box t (mem_Ioi.mp ht).le v).1
  have hq₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ 1 - x t v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_nonneg.mpr (h.in_box t (mem_Ioi.mp ht).le v).2
  have hp := tendsto_log_scaled_derivative (fun t => x t v) d
    (h.hasDerivAt_coordinate 0 le_rfl v) hd hp₀ (fun _ => occupation_zero_or_power h v)
  have hq := tendsto_log_scaled_derivative (fun t => 1 - x t v) (fun t => -d t)
    ((h.hasDerivAt_coordinate 0 le_rfl v).const_sub 1) hd.neg hq₀ (fun _ => vacancy_zero_or_power h v)
  have hE : Tendsto (fun t : ℝ => E v * d t / -Real.log t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => E v) (𝓝[>] (0 : ℝ)) (𝓝 (E v)) := tendsto_const_nhds
    simpa only [mul_zero, div_eq_mul_inv] using (hc.mul hd).mul tendsto_inv_neg_log_right
  have hlimit : -(0 : ℝ) - (if x 0 v = 0 then -d 0 else 0) -
      (if 1 - x 0 v = 0 then -(-d 0) else 0) = boundaryEntropyRate G E (x 0) v := by
    by_cases he : x 0 v = 0
    · simp [he, d, boundaryEntropyRate]
    by_cases hf : x 0 v = 1
    · simp [hf, d, boundaryEntropyRate]
    have hq : 1 - x 0 v ≠ 0 := fun hq => hf (sub_eq_zero.mp hq).symm
    simp [he, hf, hq, boundaryEntropyRate]
  have hs := (hE.neg.sub hp).sub hq
  rw [hlimit] at hs
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  change -(E v * d t / -Real.log t) - (Real.log (x t v) / -Real.log t * d t) -
    (Real.log (1 - x t v) / -Real.log t * -d t) =
      -((E v + Real.log (x t v) - Real.log (1 - x t v)) * d t) / -Real.log t
  simp only [div_eq_mul_inv]
  ring

/-- Instantaneous dissipation divided by `-log t` tends to the same
boundary coefficient as the initial free-energy loss. -/
theorem IsBoxOccupationFlow.tendsto_boxDissipation_div_neg_log (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => boxDissipation G E (x t) / -Real.log t) (𝓝[>] 0)
      (𝓝 (boundaryEntropyCoefficient G E (x 0))) := by
  have hs := tendsto_finsetSum Finset.univ (fun v _ => tendsto_boxDissipation_site_div_neg_log h v)
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  change _ = boxDissipation G E (x t) / -Real.log t
  unfold boxDissipation
  conv_rhs => rw [← Finset.sum_neg_distrib, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => div_eq_mul_inv _ _

/-- The original edgewise dissipation has this limit on a connected
graph with nontrivial mass, including for saturated initial data. -/
theorem IsBoxOccupationFlow.tendsto_dissipation_div_neg_log (h : IsBoxOccupationFlow G E x)
    (root : V) (hpath : ∀ v, Relation.ReflTransGen (fun a b => 0 < G.w a b) root v)
    (hm : (∑ v, x 0 v) ∈ Ioo (0 : ℝ) (Fintype.card V : ℝ)) :
    Tendsto (fun t : ℝ => if ht : 0 < t then
      dissipation G E (fun v => ⟨x t v, h.interior_of_nontrivial_mass root hpath hm t ht v⟩) /
        -Real.log t else 0) (𝓝[>] 0) (𝓝 (boundaryEntropyCoefficient G E (x 0))) := by
  refine h.tendsto_boxDissipation_div_neg_log.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := mem_Ioi.mp ht
  let p (v : V) : Occupation := ⟨x t v, h.interior_of_nontrivial_mass root hpath hm t ht' v⟩
  change boxDissipation G E (x t) / -Real.log t =
    if hv : 0 < t then
      dissipation G E (fun v => ⟨x t v, h.interior_of_nontrivial_mass root hpath hm t hv v⟩) /
        -Real.log t else 0
  rw [dif_pos ht']
  exact congrArg (fun a : ℝ => a / -Real.log t) (boxDissipation_eq_dissipation G E p)

private theorem eventually_const_of_positive_time_boundary (h : IsBoxOccupationFlow G E x)
    {t : ℝ} (ht : 0 < t) (v : V) (hb : x t v = 0 ∨ x t v = 1) :
    (fun s => x s v) =ᶠ[𝓝 t] fun _ => x t v := by
  rcases hb with hb | hb
  · have hno : ¬ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < x 0 u := by
      intro hs
      exact ((h.pos_iff_initial_particle v ht).mpr hs).ne' hb
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (occupation_zero_of_no_seed h v hno (mem_Ioi.mp hs)).trans hb.symm
  · have hno : ¬ ∃ u, Relation.ReflTransGen (fun a b => 0 < G.w a b) u v ∧ 0 < 1 - x 0 u := by
      intro hs
      have hv := (h.vacancy_pos_iff_initial_vacancy v ht).mpr hs
      rw [hb, sub_self] at hv
      exact (lt_irrefl (0 : ℝ)) hv
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (sub_eq_zero.mp (vacancy_zero_of_no_seed h v hno (mem_Ioi.mp hs))).symm.trans hb.symm

/-- On every positive-time box trajectory, the negative free-energy
derivative is the box dissipation. Saturated components contribute zero. -/
theorem IsBoxOccupationFlow.hasDerivAt_freeEnergy_pos (h : IsBoxOccupationFlow G E x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => freeEnergy E (x s)) (-boxDissipation G E (x t)) t := by
  unfold boxDissipation freeEnergy
  rw [neg_neg]
  apply HasDerivAt.fun_sum
  intro v _
  have hd := h.hasDerivAt_coordinate t ht.le v
  by_cases hb : x t v = 0 ∨ x t v = 1
  · have he := eventually_const_of_positive_time_boundary h ht v hb
    have hconst := (hasDerivAt_const t (x t v)).congr_of_eventuallyEq he
    have hzero : clippedDrift G E (x t) v = 0 := hd.deriv.symm.trans hconst.deriv
    rw [hzero, mul_zero]
    refine (hasDerivAt_const t (E v * x t v - Real.binEntropy (x t v))).congr_of_eventuallyEq ?_
    filter_upwards [he] with s hs
    rw [hs]
  · have h₀ : x t v ≠ 0 := fun he => hb (Or.inl he)
    have h₁ : x t v ≠ 1 := fun he => hb (Or.inr he)
    have hh : HasDerivAt (fun s => Real.binEntropy (x s v))
        ((Real.log (1 - x t v) - Real.log (x t v)) * clippedDrift G E (x t) v) t := by
      change HasDerivAt (Real.binEntropy ∘ fun s => x s v) _ t
      exact (Real.hasDerivAt_binEntropy h₀ h₁).comp t hd
    have hd' := (hd.const_mul (E v)).sub hh
    have he : E v * clippedDrift G E (x t) v -
        (Real.log (1 - x t v) - Real.log (x t v)) * clippedDrift G E (x t) v =
        (E v + Real.log (x t v) - Real.log (1 - x t v)) * clippedDrift G E (x t) v := by
      ring
    rw [he] at hd'
    exact hd'

/-- The derivative itself has logarithmic scale with the negative
initial boundary coefficient. -/
theorem IsBoxOccupationFlow.tendsto_freeEnergy_deriv_div_neg_log (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => deriv (fun s => freeEnergy E (x s)) t / -Real.log t)
      (𝓝[>] 0) (𝓝 (-boundaryEntropyCoefficient G E (x 0))) := by
  refine h.tendsto_boxDissipation_div_neg_log.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [(h.hasDerivAt_freeEnergy_pos (mem_Ioi.mp ht)).deriv, neg_div]

/-- The finite contribution left after subtracting the logarithmic
singularity. Each initially saturated site contributes a correction
of minus its inward current times its log. -/
def boundaryDissipationFinitePart (G : WeightedGraph V) (E f : V → ℝ) : ℝ :=
  boxDissipation G E f - ∑ v, boundaryEntropyRate G E f v * Real.log (boundaryEntropyRate G E f v)

private theorem tendsto_t_mul_neg_log_right :
    Tendsto (fun t : ℝ => t * -Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have h := Real.continuous_mul_log.continuousAt (x := (0 : ℝ))
  simpa only [ContinuousAt, zero_mul, neg_zero, mul_neg] using
    h.tendsto.neg.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

private theorem tendsto_drift_error_mul_log (p dp : ℝ → ℝ) (d : ℝ)
    (hquot : ∃ b, Tendsto (fun t : ℝ => (dp t - d) / t) (𝓝[>] 0) (𝓝 b))
    (hshape : (∀ᶠ t in 𝓝[>] (0 : ℝ), p t = 0) ∨
      ∃ (n : ℕ) (a : ℝ), 0 < a ∧ Tendsto (fun t : ℝ => p t / t ^ n) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => (dp t - d) * Real.log (p t)) (𝓝[>] 0) (𝓝 0) := by
  rcases hshape with hz | ⟨n, a, ha, hs⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hz] with t ht
    simp only [ht, Real.log_zero, mul_zero]
  · obtain ⟨b, hb⟩ := hquot
    have h := hb.mul ((tendsto_log_div_neg_log_of_power p n ha hs).mul tendsto_t_mul_neg_log_right)
    simp only [mul_zero] at h
    refine h.congr' ?_
    have hlt : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht₁
    have ht₀ : 0 < t := mem_Ioi.mp ht
    have hl : Real.log t ≠ 0 := (Real.log_neg ht₀ (mem_Iio.mp ht₁)).ne
    change (dp t - d) / t * (Real.log (p t) / -Real.log t * (t * -Real.log t)) =
      (dp t - d) * Real.log (p t)
    field_simp [ht₀.ne', hl]

private theorem tendsto_log_product_finite_part (p dp : ℝ → ℝ) {d : ℝ} (hp : HasDerivAt p d 0)
    (hd : Tendsto dp (𝓝[>] 0) (𝓝 d))
    (hquot : ∃ b, Tendsto (fun t : ℝ => (dp t - d) / t) (𝓝[>] 0) (𝓝 b))
    (hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ p t)
    (hshape : (∀ᶠ t in 𝓝[>] (0 : ℝ), p t = 0) ∨
      ∃ (n : ℕ) (a : ℝ), 0 < a ∧ Tendsto (fun t : ℝ => p t / t ^ n) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => Real.log (p t) * dp t - (if p 0 = 0 then d else 0) * Real.log t)
      (𝓝[>] 0) (𝓝 (Real.log (if p 0 = 0 then d else p 0) * d)) := by
  by_cases h₀ : p 0 = 0
  · simp only [if_pos h₀]
    have he := tendsto_drift_error_mul_log p dp d hquot hshape
    by_cases hdz : d = 0
    · simpa only [hdz, sub_zero, zero_mul, mul_zero, mul_comm] using he
    have hratio : Tendsto (fun t : ℝ => p t / t) (𝓝[>] 0) (𝓝 d) := by
      simpa only [h₀, sub_zero] using tendsto_right_difference_quotient hp
    have hdpos : 0 < d := by
      refine lt_of_le_of_ne (nonneg_of_right_limit_of_eventually_nonneg hratio ?_) (Ne.symm hdz)
      filter_upwards [hn, self_mem_nhdsWithin] with t ht hs
      exact div_nonneg ht (mem_Ioi.mp hs).le
    have hl := (Real.continuousAt_log hdz).tendsto.comp hratio
    have hc : Tendsto (fun _ : ℝ => d) (𝓝[>] 0) (𝓝 d) := tendsto_const_nhds
    have hs := he.add (hl.mul hc)
    simp only [zero_add] at hs
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin, (tendsto_order.mp hratio).1 0 hdpos] with t ht hr
    have hp' : p t ≠ 0 := by
      intro hz
      simp only [hz, zero_div, lt_irrefl] at hr
    change (dp t - d) * Real.log (p t) + Real.log (p t / t) * d = _
    rw [Real.log_div hp' (mem_Ioi.mp ht).ne']
    ring
  · simp only [if_neg h₀, zero_mul, sub_zero]
    have hp' : Tendsto p (𝓝[>] 0) (𝓝 (p 0)) :=
      hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ((Real.continuousAt_log h₀).tendsto.comp hp').mul hd

private theorem exists_clippedDrift_right_quotient (h : IsBoxOccupationFlow G E x) (v : V) :
    ∃ b, Tendsto (fun t : ℝ => (clippedDrift G E (x t) v - clippedDrift G E (x 0) v) / t)
      (𝓝[>] 0) (𝓝 b) := by
  have hd := tendsto_right_difference_quotient (differentiableAt_polynomialDrift_zero h v).hasDerivAt
  rw [polynomialDrift_eq h v le_rfl] at hd
  refine ⟨_, hd.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [polynomialDrift_eq h v (mem_Ioi.mp ht).le]

private theorem tendsto_dissipation_site_finite_part (h : IsBoxOccupationFlow G E x) (v : V) :
    Tendsto (fun t : ℝ =>
      -((E v + Real.log (x t v) - Real.log (1 - x t v)) * clippedDrift G E (x t) v) -
        boundaryEntropyRate G E (x 0) v * -Real.log t) (𝓝[>] 0)
      (𝓝 (-((E v + Real.log (x 0 v) - Real.log (1 - x 0 v)) * clippedDrift G E (x 0) v) -
        boundaryEntropyRate G E (x 0) v * Real.log (boundaryEntropyRate G E (x 0) v))) := by
  let d (t : ℝ) := clippedDrift G E (x t) v
  have hd : Tendsto d (𝓝[>] 0) (𝓝 (d 0)) := tendsto_clippedDrift_coordinate_right h v
  have hquot : ∃ b, Tendsto (fun t : ℝ => (d t - d 0) / t) (𝓝[>] 0) (𝓝 b) :=
    exists_clippedDrift_right_quotient h v
  have hnegquot : ∃ b, Tendsto (fun t : ℝ => (-d t - -d 0) / t) (𝓝[>] 0) (𝓝 b) := by
    obtain ⟨b, hb⟩ := hquot
    refine ⟨-b, hb.neg.congr' (Eventually.of_forall fun t => ?_)⟩
    change -((d t - d 0) / t) = (-d t - -d 0) / t
    rw [← neg_div, neg_sub, neg_sub_neg]
  have hp₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x t v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.in_box t (mem_Ioi.mp ht).le v).1
  have hq₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ 1 - x t v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_nonneg.mpr (h.in_box t (mem_Ioi.mp ht).le v).2
  have hp := tendsto_log_product_finite_part (fun t => x t v) d
    (h.hasDerivAt_coordinate 0 le_rfl v) hd hquot hp₀ (occupation_zero_or_power h v)
  have hq := tendsto_log_product_finite_part (fun t => 1 - x t v) (fun t => -d t)
    ((h.hasDerivAt_coordinate 0 le_rfl v).const_sub 1) hd.neg hnegquot hq₀ (vacancy_zero_or_power h v)
  have hE : Tendsto (fun _ : ℝ => E v) (𝓝[>] 0) (𝓝 (E v)) := tendsto_const_nhds
  have hs := (((hE.mul hd).add hp).add hq).neg
  have hlimit : -(E v * d 0 + Real.log (if x 0 v = 0 then d 0 else x 0 v) * d 0 +
        Real.log (if 1 - x 0 v = 0 then -d 0 else 1 - x 0 v) * -d 0) =
      -((E v + Real.log (x 0 v) - Real.log (1 - x 0 v)) * d 0) -
        boundaryEntropyRate G E (x 0) v * Real.log (boundaryEntropyRate G E (x 0) v) := by
    by_cases h₀ : x 0 v = 0
    · simp [h₀, boundaryEntropyRate, d]; ring
    by_cases h₁ : x 0 v = 1
    · simp [h₁, boundaryEntropyRate, d]; ring
    have hq' : 1 - x 0 v ≠ 0 := fun hz => h₁ (sub_eq_zero.mp hz).symm
    simp only [h₀, h₁, hq', if_false, boundaryEntropyRate, zero_mul, sub_zero]
    ring
  rw [hlimit] at hs
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  change -(E v * d t + (Real.log (x t v) * d t - (if x 0 v = 0 then d 0 else 0) * Real.log t) +
    (Real.log (1 - x t v) * -d t - (if 1 - x 0 v = 0 then -d 0 else 0) * Real.log t)) =
    -((E v + Real.log (x t v) - Real.log (1 - x t v)) * d t) -
      boundaryEntropyRate G E (x 0) v * -Real.log t
  by_cases h₀ : x 0 v = 0
  · simp [h₀, boundaryEntropyRate, d]; ring
  by_cases h₁ : x 0 v = 1
  · simp [h₁, boundaryEntropyRate, d]; ring
  have hq' : 1 - x 0 v ≠ 0 := fun hz => h₁ (sub_eq_zero.mp hz).symm
  simp only [h₀, h₁, hq', if_false, boundaryEntropyRate, zero_mul, sub_zero]
  ring

/-- Subtracting the boundary logarithm leaves a finite limit even
when several sites enter the interior at different orders. -/
theorem IsBoxOccupationFlow.tendsto_boxDissipation_finite_part (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => boxDissipation G E (x t) - boundaryEntropyCoefficient G E (x 0) * -Real.log t)
      (𝓝[>] 0) (𝓝 (boundaryDissipationFinitePart G E (x 0))) := by
  have hs := tendsto_finsetSum Finset.univ (fun v _ => tendsto_dissipation_site_finite_part h v)
  simpa only [Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_mul,
    boxDissipation, boundaryDissipationFinitePart, boundaryEntropyCoefficient] using hs

/-- When every boundary edge is inactive, the instantaneous dissipation
has a finite right limit equal to the box expression at time zero. -/
theorem IsBoxOccupationFlow.tendsto_boxDissipation_of_no_active_edge
    (h : IsBoxOccupationFlow G E x) (hno : ¬ HasActiveBoundaryEdge G (x 0)) :
    Tendsto (fun t : ℝ => boxDissipation G E (x t)) (𝓝[>] 0) (𝓝 (boxDissipation G E (x 0))) := by
  have hbox := h.in_box 0 le_rfl
  have hz (v : V) : boundaryEntropyRate G E (x 0) v = 0 := by
    refine le_antisymm (le_of_not_gt ?_) (boundaryEntropyRate_nonneg G E _ hbox v)
    intro hp
    obtain ⟨u, hu⟩ := (boundaryEntropyRate_pos_iff G E _ hbox v).mp hp
    exact hno ⟨v, u, hu⟩
  simpa only [boundaryEntropyCoefficient, boundaryDissipationFinitePart, hz, zero_mul,
    Finset.sum_const_zero, sub_zero] using h.tendsto_boxDissipation_finite_part

private theorem tendsto_right_slope_of_derivative_limit {f f' : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousOn f (Ici 0)) (hd : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t)
    (hl : Tendsto f' (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => (f t - f 0) / t) (𝓝[>] 0) (𝓝 a) := by
  refine tendsto_def.mpr fun u hu => ?_
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), f' t ∈ u := hl.eventually hu
  obtain ⟨δ, hδ, hinside⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
  refine (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨s, hs, hmean⟩ := exists_hasDerivAt_eq_slope f f' ht.1
    (hc.mono fun _ hr => hr.1) (fun r hr => hd r hr.1)
  rw [sub_zero] at hmean
  change (f t - f 0) / t ∈ u
  rw [← hmean]
  exact hinside ⟨hs.1, hs.2.trans ht.2⟩

/-- Averaging the logarithmic dissipation over `(0, t)` adds one
boundary coefficient to the finite part of the free-energy loss rate. -/
theorem IsBoxOccupationFlow.tendsto_freeEnergy_loss_rate_finite_part (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => (freeEnergy E (x 0) - freeEnergy E (x t)) / t -
        boundaryEntropyCoefficient G E (x 0) * -Real.log t) (𝓝[>] 0)
      (𝓝 (boundaryDissipationFinitePart G E (x 0) + boundaryEntropyCoefficient G E (x 0))) := by
  let F (t : ℝ) := freeEnergy E (x t)
  let C := boundaryEntropyCoefficient G E (x 0)
  let g (t : ℝ) := F 0 - F t + C * (t * Real.log t)
  let g' (t : ℝ) := boxDissipation G E (x t) + C * (Real.log t + 1)
  have hF : ContinuousOn F (Ici 0) := by
    unfold F freeEnergy
    apply continuousOn_finsetSum
    intro v _
    have hx : ContinuousOn (fun t : ℝ => x t v) (Ici 0) := fun t ht =>
      (h.hasDerivAt_coordinate t ht v).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul hx).sub (Real.binEntropy_continuous.comp_continuousOn hx)
  have hg : ContinuousOn g (Ici 0) :=
    (continuousOn_const.sub hF).add (Real.continuous_mul_log.const_mul C).continuousOn
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt g (g' t) t := by
    simpa only [g, g', Pi.add_def, neg_neg] using
      ((h.hasDerivAt_freeEnergy_pos ht).const_sub (F 0)).add
        ((Real.hasDerivAt_mul_log ht.ne').const_mul C)
  have hC : Tendsto (fun _ : ℝ => C) (𝓝[>] 0) (𝓝 C) := tendsto_const_nhds
  have hl : Tendsto g' (𝓝[>] 0) (𝓝 (boundaryDissipationFinitePart G E (x 0) + C)) := by
    refine (h.tendsto_boxDissipation_finite_part.add hC).congr' (Eventually.of_forall fun t => ?_)
    change boxDissipation G E (x t) - C * -Real.log t + C =
      boxDissipation G E (x t) + C * (Real.log t + 1)
    ring
  refine (tendsto_right_slope_of_derivative_limit hg hd hl).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : 0 < t := mem_Ioi.mp ht
  have hg₀ : g 0 = 0 := by simp [g]
  have hc : (C * (t * Real.log t)) / t = C * Real.log t := by
    rw [mul_comm t (Real.log t), ← mul_assoc, mul_div_cancel_right₀ _ ht₀.ne']
  change (F 0 - F t + C * (t * Real.log t) - g 0) / t = (F 0 - F t) / t - C * -Real.log t
  rw [hg₀, sub_zero, add_div, hc, mul_neg, sub_neg_eq_add]

/-- Instantaneous dissipation diverges at time zero exactly when a
positive-weight edge supplies a saturated site. -/
theorem IsBoxOccupationFlow.boxDissipation_atTop_iff_active_edge (h : IsBoxOccupationFlow G E x) :
    Tendsto (fun t : ℝ => boxDissipation G E (x t)) (𝓝[>] 0) atTop ↔ HasActiveBoundaryEdge G (x 0) := by
  constructor
  · intro htop
    by_contra hno
    have hlim := h.tendsto_boxDissipation_of_no_active_edge hno
    have hlt := (tendsto_order.mp hlim).2 (boxDissipation G E (x 0) + 1) (by linarith)
    have hge := (tendsto_atTop.mp htop) (boxDissipation G E (x 0) + 1)
    obtain ⟨_, hlt, hge⟩ := (hlt.and hge).exists
    exact (not_le_of_gt hlt) hge
  · intro ha
    have hc := (boundaryEntropyCoefficient_pos_iff G E _ (h.in_box 0 le_rfl)).mpr ha
    have hp := Tendsto.pos_mul_atTop hc h.tendsto_boxDissipation_div_neg_log tendsto_neg_log_right
    refine hp.congr' ?_
    have hlt : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht₁
    exact div_mul_cancel₀ _ (neg_pos.mpr (Real.log_neg (mem_Ioi.mp ht) (mem_Iio.mp ht₁))).ne'

#print axioms tendsto_log_div_neg_log_of_power
#print axioms tendsto_log_scaled_derivative
#print axioms boxDissipation_eq_dissipation
#print axioms IsBoxOccupationFlow.tendsto_boxDissipation_div_neg_log
#print axioms IsBoxOccupationFlow.tendsto_dissipation_div_neg_log
#print axioms IsBoxOccupationFlow.hasDerivAt_freeEnergy_pos
#print axioms IsBoxOccupationFlow.tendsto_freeEnergy_deriv_div_neg_log
#print axioms IsBoxOccupationFlow.tendsto_boxDissipation_of_no_active_edge
#print axioms IsBoxOccupationFlow.tendsto_boxDissipation_finite_part
#print axioms IsBoxOccupationFlow.tendsto_freeEnergy_loss_rate_finite_part
#print axioms IsBoxOccupationFlow.boxDissipation_atTop_iff_active_edge

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
