import GaloisForLFunctions.RHTower.DeningerArithmeticPositiveCalderonKoszul

/-!
# All-place Green-form uniform-packet no-go

Operator-norm summability of local Green forms on one defining Banach disk forces their norms to
vanish.  Hence one disk cannot contain unit-norm packets whose own-place Green diagonal remains
one.  Applied to Route L, graph-normalized high-prime packets must escape every fixed source disk
or acquire arithmetic damping before the all-place form sum can converge.

This is unconditional functional analysis.  It uses no Xi zero, spectral projector, numerical
computation, or RH premise.
-/

namespace RHTower

open Filter Topology

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm summability forces the norms of the summands to vanish. -/
theorem deningerSummableTerm_norm_tendsto_zero
    {A : Type*} [SeminormedAddCommGroup A]
    (f : ℕ → A) (hf : Summable f) :
    Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  have hzero : Tendsto f atTop (𝓝 0) := hf.tendsto_atTop_zero
  simpa using hzero.norm

/-- A uniform positive operator-norm floor forbids all-place form summability. -/
theorem deningerGreenForm_not_summable_of_uniform_norm_floor
    (localForm : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hfloor : ∀ n, ε ≤ ‖localForm n‖) :
    ¬ Summable localForm := by
  intro hforms
  have hvanish := deningerSummableTerm_norm_tendsto_zero localForm hforms
  have heventually : ∀ᶠ n in atTop, ‖localForm n‖ < ε :=
    hvanish.eventually_lt_const hε
  rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
  exact (not_lt_of_ge (hfloor N)) (hN N le_rfl)

/-- A unit vector with unit Green diagonal forces the form norm to be at least one. -/
theorem deningerGreenForm_one_le_norm_of_normalized_packet
    (G : E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hx : ‖x‖ = 1) (henergy : G x x = 1) :
    1 ≤ ‖G‖ := by
  have hinner := (G x).le_opNorm x
  have houter := G.le_opNorm x
  rw [henergy, hx, norm_one, mul_one] at hinner
  rw [hx, mul_one] at houter
  exact hinner.trans houter

/-- Quantitative operator-norm inequality behind normalized-packet escape. -/
theorem deningerGreenForm_one_le_norm_mul_packet_norm_sq
    (G : E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (henergy : G x x = 1) :
    1 ≤ ‖G‖ * ‖x‖ ^ (2 : ℕ) := by
  have hinner := (G x).le_opNorm x
  have houter := G.le_opNorm x
  calc
    1 = ‖G x x‖ := by rw [henergy, norm_one]
    _ ≤ ‖G x‖ * ‖x‖ := hinner
    _ ≤ (‖G‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right houter (norm_nonneg x)
    _ = ‖G‖ * ‖x‖ ^ (2 : ℕ) := by ring

/-- Under all-place form summability, unit own-place energy forces packet norms to infinity. -/
theorem deningerGreenForm_normalized_packets_norm_tendsto_atTop
    (localForm : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (packet : ℕ → E)
    (hforms : Summable localForm)
    (hpacket_energy : ∀ n, localForm n (packet n) (packet n) = 1) :
    Tendsto (fun n => ‖packet n‖) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  let M : ℝ := max b 1
  have hbM : b ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hthreshold : 0 < (M ^ (2 : ℕ))⁻¹ := inv_pos.mpr (sq_pos_of_pos hM)
  have hvanish := deningerSummableTerm_norm_tendsto_zero localForm hforms
  have heventually : ∀ᶠ n in atTop, ‖localForm n‖ < (M ^ (2 : ℕ))⁻¹ :=
    hvanish.eventually_lt_const hthreshold
  rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  by_contra hnot
  have hxlt : ‖packet n‖ < b := lt_of_not_ge hnot
  have hxle : ‖packet n‖ ≤ M := (le_of_lt hxlt).trans hbM
  have hsq : ‖packet n‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hM.le).2 hxle
  have hxne : packet n ≠ 0 := by
    intro hx
    simpa [hx] using hpacket_energy n
  have hxnormsq : 0 < ‖packet n‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr hxne)
  have hprodlt :
      ‖localForm n‖ * ‖packet n‖ ^ (2 : ℕ) < (M ^ (2 : ℕ))⁻¹ * M ^ (2 : ℕ) :=
    mul_lt_mul (hN n hn) hsq hxnormsq hthreshold.le
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hM.ne')] at hprodlt
  exact (not_lt_of_ge
    (deningerGreenForm_one_le_norm_mul_packet_norm_sq
      (localForm n) (packet n) (hpacket_energy n))) hprodlt

/-- Unit-norm packets with unit own-place Green energy obstruct all-place form summability. -/
theorem deningerGreenForm_not_summable_of_normalized_packets
    (localForm : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (packet : ℕ → E)
    (hpacket_norm : ∀ n, ‖packet n‖ = 1)
    (hpacket_energy : ∀ n, localForm n (packet n) (packet n) = 1) :
    ¬ Summable localForm :=
  deningerGreenForm_not_summable_of_uniform_norm_floor
    localForm zero_lt_one fun n =>
      deningerGreenForm_one_le_norm_of_normalized_packet
        (localForm n) (packet n) (hpacket_norm n) (hpacket_energy n)

/-- Orthogonal/disjoint packets can be summed from a maximum-tail estimate, without an `ℓ¹`
majorant for the individual operator norms. -/
theorem deningerSummable_of_max_tail_control
    {ι F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ι → F)
    (hvanish : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0))
    (hmax : ∀ (s : Finset ι) (C : ℝ), 0 ≤ C →
      (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C) :
    Summable f := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have heventually : ∀ᶠ i in cofinite, ‖f i‖ < ε / 2 :=
    hvanish.eventually_lt_const hε2
  classical
  refine ⟨heventually.toFinset, fun t ht => ?_⟩
  have hcoeff : ∀ i ∈ t, ‖f i‖ ≤ ε / 2 := by
    intro i hi
    have hiout : i ∉ heventually.toFinset :=
      Finset.disjoint_left.mp ht hi
    have higood : ‖f i‖ < ε / 2 := by
      simpa only [heventually.mem_toFinset, Set.mem_compl_iff,
        Classical.not_not, Set.mem_setOf_eq] using hiout
    exact higood.le
  exact (hmax t (ε / 2) hε2.le hcoeff).trans_lt (half_lt_self hε)

/-- Under a maximum-tail estimate, summability is equivalent to decay of individual term norms. -/
theorem deningerSummable_iff_norm_tendsto_cofinite_of_max_tail_control
    {ι F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ι → F)
    (hmax : ∀ (s : Finset ι) (C : ℝ), 0 ≤ C →
      (∀ i ∈ s, ‖f i‖ ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C) :
    Summable f ↔ Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
  constructor
  · intro hf
    have hzero : Tendsto f cofinite (𝓝 0) := hf.tendsto_cofinite_zero
    simpa using hzero.norm
  · exact fun hvanish => deningerSummable_of_max_tail_control f hvanish hmax

end RHTower
