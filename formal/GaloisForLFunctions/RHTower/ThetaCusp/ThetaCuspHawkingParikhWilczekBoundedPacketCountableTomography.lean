import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekFinitePacketEndpointTomography
import GaloisForLFunctions.HTGeometry.BoundedPowerSeriesUnique

/-!
# Countable PW endpoint tomography for every bounded grade packet

Finite PW grade packets are recovered from finitely many endpoint samples.  Here the same explicit
physical schedule

`epsilon_j = 1/(4(j+1))`

is shown to recover every uniformly bounded infinite packet.  Its endpoint nodes are
`q_j=exp(-(j+1))`, a nonzero sequence converging to zero.  Strong coefficient peeling divides the
sampled identity by `q_j^m` after lower coefficients vanish; the remaining tail is bounded by
`C q_j/(1-q_j)` and therefore tends to zero.  This forces the next coefficient to vanish.

The proof first establishes a reusable mathematical theorem for any nonzero node sequence tending
to zero.  Unlike interval-based power-series uniqueness already in the corpus, only countably many
samples are used.  The PW specialization needs no `l1` premise: endpoint geometric damping makes
every bounded packet response summable at each sample.

`[NEW] [COUNTABLE SOURCE TOMOGRAPHY] [BOUNDED INFINITE PACKETS]
[ZERO-SEQUENCE COEFFICIENT PEELING] [LEAN-PROVED]`
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Bounded power-series uniqueness from a zero sequence.**  If a bounded real coefficient
sequence has zero power-series sum at every member of a positive node sequence inside the unit disk
that tends to zero, then every coefficient vanishes. -/
theorem boundedPowerSeries_coeff_eq_zero_of_zeroSequence
    {c : ℕ → ℝ} {C : ℝ} {q : ℕ → ℝ}
    (hbound : ∀ n, |c n| ≤ C)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, |q j| < 1)
    (hqlim : Tendsto q atTop (𝓝 0))
    (hzero : ∀ j, ∑' n : ℕ, c n * q j ^ n = 0) :
    ∀ n, c n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hshift : ∀ j, ∑' n : ℕ, c (n + m) * q j ^ n = 0 := by
      intro j
      have hsum := GaloisForLFunctions.HTGeometry.summable_of_bounded_coeff hbound (hq1 j)
      have hsplit := hsum.sum_add_tsum_nat_add m
      have hzeros : ∑ n ∈ Finset.range m, c n * q j ^ n = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [ih n (Finset.mem_range.mp hn), zero_mul]
      rw [hzeros, zero_add, hzero j] at hsplit
      have htail : ∑' n : ℕ, c (n + m) * q j ^ (n + m) = 0 := hsplit
      have hfactor : ∑' n : ℕ, c (n + m) * q j ^ (n + m) =
          q j ^ m * ∑' n : ℕ, c (n + m) * q j ^ n := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [pow_add]
        ring
      rw [hfactor] at htail
      exact (mul_eq_zero.mp htail).resolve_left (pow_ne_zero m (hq0 j).ne')
    have hbnd : ∀ j, |c m| ≤ C * |q j| / (1 - |q j|) := by
      intro j
      have hsum : Summable fun n : ℕ => c (n + m) * q j ^ n := by
        refine Summable.of_norm_bounded (g := fun n : ℕ => C * |q j| ^ n)
          ((summable_geometric_of_lt_one (abs_nonneg (q j)) (hq1 j)).mul_left C) ?_
        intro n
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)
      have hpeel := hsum.sum_add_tsum_nat_add 1
      rw [hshift j] at hpeel
      have hhead : ∑ n ∈ Finset.range 1, c (n + m) * q j ^ n = c m := by
        simp
      rw [hhead] at hpeel
      have hval : c m = -∑' n : ℕ, c (n + 1 + m) * q j ^ (n + 1) := by
        linarith [hpeel]
      rw [hval, abs_neg]
      exact GaloisForLFunctions.HTGeometry.abs_tsum_shift_tail_le hbound (hq1 j) m
    have htailLimit : Tendsto (fun j => C * |q j| / (1 - |q j|)) atTop (𝓝 0) := by
      have hcont : ContinuousAt (fun t : ℝ => C * |t| / (1 - |t|)) 0 := by
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · norm_num
      simpa [Function.comp_def] using hcont.tendsto.comp hqlim
    have hle : |c m| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htailLimit
        (Filter.Eventually.of_forall hbnd)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- Countable endpoint response of an arbitrary bounded grade packet at the `j`-th prescribed
physical backreaction scale. -/
def schwarzschildParikhWilczekBoundedPacketEndpointResponse
    (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' n : ℕ, c n *
    schwarzschildParikhWilczekWindingTerm n
      (schwarzschildParikhWilczekEndpointTomographyScale j)
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint
        (schwarzschildParikhWilczekEndpointTomographyScale j))

/-- Each bounded-packet endpoint sample is its shifted power-series value at the corresponding
physical Laplace node. -/
theorem schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq
    (c : ℕ → ℝ) (j : ℕ) :
    schwarzschildParikhWilczekBoundedPacketEndpointResponse c j =
      ∑' n : ℕ, c n * schwarzschildParikhWilczekEndpointTomographyNode j ^ (n + 1) := by
  rw [schwarzschildParikhWilczekBoundedPacketEndpointResponse]
  apply tsum_congr
  intro n
  rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow n
      (schwarzschildParikhWilczekEndpointTomographyScale_pos j),
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_sample]

/-- Prescribed physical endpoint nodes converge to the interior accumulation point zero. -/
theorem tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero :
    Tendsto schwarzschildParikhWilczekEndpointTomographyNode atTop (𝓝 0) := by
  have hplus : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun j : ℕ => -((j : ℝ) + 1)) atTop atBot := by
    exact tendsto_neg_atTop_atBot.comp hplus
  exact Real.tendsto_exp_atBot.comp hneg

/-- **Countable source-exact bounded PW tomography.**  A bounded infinite grade packet has zero
response at every prescribed physical scale iff it is the zero packet. -/
theorem schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq_zero_iff
    {c : ℕ → ℝ} {C : ℝ} (hbound : ∀ n, |c n| ≤ C) :
    (∀ j : ℕ, schwarzschildParikhWilczekBoundedPacketEndpointResponse c j = 0) ↔
      c = 0 := by
  constructor
  · intro h
    let q : ℕ → ℝ := schwarzschildParikhWilczekEndpointTomographyNode
    have hq0 (j : ℕ) : 0 < q j := Real.exp_pos _
    have hq1 (j : ℕ) : |q j| < 1 := by
      rw [abs_of_pos (hq0 j)]
      change Real.exp (-((j : ℝ) + 1)) < 1
      rw [Real.exp_lt_one_iff]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hqzero (j : ℕ) : ∑' n : ℕ, c n * q j ^ n = 0 := by
      have hs := h j
      rw [schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq] at hs
      have hfactor : (∑' n : ℕ, c n * q j ^ (n + 1)) =
          q j * ∑' n : ℕ, c n * q j ^ n := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
      rw [hfactor] at hs
      exact (mul_eq_zero.mp hs).resolve_left (hq0 j).ne'
    funext n
    exact boundedPowerSeries_coeff_eq_zero_of_zeroSequence hbound hq0 hq1
      tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero hqzero n
  · rintro rfl
    intro j
    simp [schwarzschildParikhWilczekBoundedPacketEndpointResponse]

end

end RHTower
