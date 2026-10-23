import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingCenteredSemigroup
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# The receiver is the chain orbit of the reciprocal

The centered arithmetic damping chain `C_η` acts on `c₀` (state `n + 1` at index `n`).  Its value on
the **reciprocal observable** `r(k) = 1/k` is the normalized centered Möbius source
(`centeredOperator_reciprocal_apply`):

`(C_η r)(n) = P_η(n + 1)/(n + 1)`,  `P_η(m) = Σ_{d ≤ m} μ(d) d^{−η} ⌊m/d⌋ − m/ζ(1 + η)`.

Since `C_s C_t = C_{s+t}`, the damped source is the semigroup orbit `η ↦ C_η r`
(`centeredOperator_orbit`): **damping is the time of the chain**, and continuation towards zero
damping is backward evolution of a compact semigroup.

The critical energy is the weighted `ℓ²` energy of the orbit (`dampedMobiusEnergy_eq_orbitEnergy`),
`E_η(T) = Σ_{m<T} (m+1)/(m+2) · (C_η r)(m)²`, so

* admission at `η` is `ℓ²`-membership of the orbit (`admits_iff_summable_orbit`), and the Riemann
  hypothesis is the orbit entering `ℓ²` at arbitrarily small times
  (`riemannHypothesis_iff_orbit_summable`);
* **truncations approximate the receiver** (`tendsto_truncation_partialEnergy`): the partial orbit
  energies of the finite truncations of `r` converge to those of `r`, so admission is decided by
  the chain on finitely supported sequences;
* in these coordinates the **centring is indispensable** (`not_summable_transition_first_column`):
  the uncentred transition sends the first state to a column converging to the positive entrance
  mass `e_η(1)`, which is not square summable at any damping.

So the receiver norm on the chain's own coordinate is `ℓ²` — the pronic energy of the prefix
`P = n · (C r)` — and not the pronic weight on the chain coordinate, where the centring functional
is unbounded below half damping (`BezoutValuationIncidence.exists_pronicPairing_gt`).
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- A sequence tending to zero, as a `c₀` vector. -/
def c0OfTendsto (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : C₀(ℕ, ℝ) :=
  ⟨⟨f, continuous_of_discreteTopology⟩, by rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]⟩

@[simp] theorem c0OfTendsto_apply (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) (n : ℕ) :
    c0OfTendsto f hf n = f n := rfl

theorem abs_c0_apply_le_norm (b : C₀(ℕ, ℝ)) (k : ℕ) : |b k| ≤ ‖b‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact b.toBCF.norm_coe_le_norm k

theorem norm_c0_le {b : C₀(ℕ, ℝ)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ k, |b k| ≤ C) : ‖b‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 fun k => by rw [Real.norm_eq_abs]; exact h k

/-- The reciprocal observable `1/k` on the positive states `k = n + 1`. -/
def reciprocalObservable : C₀(ℕ, ℝ) :=
  c0OfTendsto (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat

@[simp] theorem reciprocalObservable_apply (n : ℕ) :
    reciprocalObservable n = 1 / ((n : ℝ) + 1) := rfl

private theorem sum_range_succ_shift (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range m, f (k + 1) = ∑ k ∈ Icc 1 m, f k :=
  (RHTower.sum_Icc_eq_sum_range_shift f m).symm

/-- **The source is the chain image of the reciprocal**: `(C_η r)(n) = P_η(n+1)/(n+1)`. -/
theorem centeredOperator_reciprocal_apply {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη reciprocalObservable n =
      RHTower.pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1) := by
  rw [arithmeticDampingCenteredOperator_apply]
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re with hρ
  -- the transition part is a finite sum, the entrance part is the reciprocal mass `ρ`
  have hfin : ∀ k ∉ range (n + 1),
      arithmeticDampingTransition η (n + 1) (k + 1) * reciprocalObservable k = 0 := by
    intro k hk
    rw [arithmeticDampingTransition_eq_zero_of_lt η (by simp at hk; omega), zero_mul]
  have hA : HasSum (fun k => arithmeticDampingTransition η (n + 1) (k + 1) *
      reciprocalObservable k)
      (∑ k ∈ range (n + 1), arithmeticDampingTransition η (n + 1) (k + 1) *
        reciprocalObservable k) := hasSum_sum_of_ne_finset_zero hfin
  have hB : HasSum (fun k => arithmeticDampingEntrance η (k + 1) * reciprocalObservable k) ρ := by
    have h := hasSum_arithmeticDampingEntrance_reciprocal_tail hη 0
    simp only [zero_add, Nat.cast_one, Real.one_rpow, mul_one] at h
    refine h.congr_fun fun k => ?_
    simp only [reciprocalObservable_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hsum := (hA.sub hB).tsum_eq
  have hrow : (fun k => arithmeticDampingCenteredRow η n k * reciprocalObservable k) =
      fun k => arithmeticDampingTransition η (n + 1) (k + 1) * reciprocalObservable k -
        arithmeticDampingEntrance η (k + 1) * reciprocalObservable k := by
    funext k
    simp only [arithmeticDampingCenteredRow]
    ring
  rw [hrow, hsum]
  have hsrc : ∑ k ∈ range (n + 1), arithmeticDampingTransition η (n + 1) (k + 1) *
      reciprocalObservable k = arithmeticDampingMean η (n + 1) := by
    rw [← arithmeticDampingTransition_source η (Nat.succ_pos n), ← sum_range_succ_shift]
    refine sum_congr rfl fun k _ => ?_
    simp only [reciprocalObservable_apply, Nat.cast_add, Nat.cast_one]
    ring
  rw [hsrc, RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
  unfold arithmeticDampingMean arithmeticDampingPrefix
  have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hn]
  field_simp
  ring

/-- **Damping is the time of the chain**: `C_s (C_t r) = C_{s+t} r`. -/
theorem centeredOperator_orbit {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    arithmeticDampingCenteredOperator hs (arithmeticDampingCenteredOperator ht reciprocalObservable)
      = arithmeticDampingCenteredOperator (add_pos hs ht) reciprocalObservable := by
  rw [← arithmeticDampingCenteredOperator_semigroup hs ht]
  rfl

/-- **The critical energy is the weighted `ℓ²` energy of the orbit.** -/
theorem dampedMobiusEnergy_eq_orbitEnergy {η : ℝ} (hη : 0 < η) (T : ℕ) :
    dampedMobiusEnergy η T = ∑ m ∈ range T,
      ((m : ℝ) + 1) / ((m : ℝ) + 2) *
        arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 := by
  change RHTower.pmPowerDampedDivisorDiscreteEnergy η T = _
  unfold RHTower.pmPowerDampedDivisorDiscreteEnergy
  rw [← sum_range_succ_shift]
  refine sum_congr rfl fun m _ => ?_
  rw [centeredOperator_reciprocal_apply]
  push_cast
  have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Admission is `ℓ²`-membership of the orbit.** -/
theorem admits_iff_summable_orbit {η : ℝ} (hη : 0 < η) :
    Admits dampedMobiusEnergy η ↔
      Summable fun m => arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 := by
  have hw : ∀ m : ℕ, (1 / 2 : ℝ) ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) ∧
      ((m : ℝ) + 1) / ((m : ℝ) + 2) ≤ 1 := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    constructor
    · rw [le_div_iff₀ (by positivity)]; linarith
    · rw [div_le_one (by positivity)]; linarith
  constructor
  · rintro ⟨B, hB⟩
    refine summable_of_sum_range_le (c := 2 * B) (fun m => sq_nonneg _) fun T => ?_
    have h := hB T
    rw [dampedMobiusEnergy_eq_orbitEnergy hη] at h
    have hle : ∀ m : ℕ, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 ≤
        2 * (((m : ℝ) + 1) / ((m : ℝ) + 2) *
          arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2) := by
      intro m
      have h1 := (hw m).1
      have h2 := sq_nonneg (arithmeticDampingCenteredOperator hη reciprocalObservable m)
      nlinarith
    calc ∑ m ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2
        ≤ ∑ m ∈ range T, 2 * (((m : ℝ) + 1) / ((m : ℝ) + 2) *
            arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2) :=
          sum_le_sum fun m _ => hle m
      _ = 2 * ∑ m ∈ range T, ((m : ℝ) + 1) / ((m : ℝ) + 2) *
            arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 := by rw [mul_sum]
      _ ≤ 2 * B := by linarith
  · intro hs
    refine ⟨∑' m, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2, fun T => ?_⟩
    rw [dampedMobiusEnergy_eq_orbitEnergy hη]
    calc ∑ m ∈ range T, ((m : ℝ) + 1) / ((m : ℝ) + 2) *
          arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2
        ≤ ∑ m ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2 :=
          sum_le_sum fun m _ => by
            have h1 := (hw m).2
            have h2 := sq_nonneg (arithmeticDampingCenteredOperator hη reciprocalObservable m)
            nlinarith
      _ ≤ _ := hs.sum_le_tsum _ fun m _ => sq_nonneg _

/-- **The Riemann hypothesis is the orbit entering `ℓ²` at arbitrarily small times.** -/
theorem riemannHypothesis_iff_orbit_summable :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, ∃ hε : 0 < ε, ε < δ ∧
      Summable fun m => arithmeticDampingCenteredOperator hε reciprocalObservable m ^ 2 := by
  rw [riemannHypothesis_iff_cofinallyAdmits]
  constructor
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, ha⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, (admits_iff_summable_orbit hε).mp ha⟩
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, hs⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, (admits_iff_summable_orbit hε).mpr hs⟩

/-- The finitely supported truncation of the reciprocal. -/
def reciprocalTruncation (N : ℕ) : C₀(ℕ, ℝ) :=
  c0OfTendsto (fun k => if k < N then 1 / ((k : ℝ) + 1) else 0) (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    simp [not_lt.mpr hk])

theorem tendsto_reciprocalTruncation :
    Tendsto reciprocalTruncation atTop (𝓝 reciprocalObservable) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine norm_c0_le (by positivity) fun k => ?_
  change |(if k < N then 1 / ((k : ℝ) + 1) else 0) - 1 / ((k : ℝ) + 1)| ≤ 1 / ((N : ℝ) + 1)
  split_ifs with hk
  · simp only [sub_self, abs_zero]; positivity
  · rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
    have : (N : ℝ) ≤ k := by exact_mod_cast not_lt.mp hk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **Truncations approximate the receiver at every horizon**: the partial orbit energies of the
finitely supported truncations of `r` converge to those of `r`. -/
theorem tendsto_truncation_partialEnergy {η : ℝ} (hη : 0 < η) (T : ℕ) :
    Tendsto (fun N => ∑ m ∈ range T,
        arithmeticDampingCenteredOperator hη (reciprocalTruncation N) m ^ 2) atTop
      (𝓝 (∑ m ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2)) := by
  have hC := ((arithmeticDampingCenteredOperator hη).continuous.tendsto _).comp
    tendsto_reciprocalTruncation
  refine tendsto_finsetSum _ fun m _ => ?_
  refine Tendsto.pow ?_ 2
  rw [tendsto_iff_norm_sub_tendsto_zero] at hC ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hC
  rw [Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.sub_apply]
  exact abs_c0_apply_le_norm _ m

/-- The entrance mass of the first state is positive. -/
theorem arithmeticDampingEntrance_one_pos {η : ℝ} (hη : 0 < η) :
    0 < arithmeticDampingEntrance η 1 := by
  unfold arithmeticDampingEntrance
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have h2 : ((1 + 1 : ℕ) : ℝ) ^ (-1 - η) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h2 ⊢
  exact mul_pos hρ (by linarith)

/-- **The centring is indispensable in receiver coordinates.**  The uncentred transition sends the
first state to a column that converges to the positive entrance mass, so it is not square summable:
the transition itself is unbounded in `ℓ²` at every damping. -/
theorem not_summable_transition_first_column {η : ℝ} (hη : 0 < η) :
    ¬ Summable fun n : ℕ => arithmeticDampingTransition η (n + 1) 1 ^ 2 := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  have h1 : Tendsto (fun n : ℕ => arithmeticDampingTransition η (n + 1) 1 ^ 2) atTop
      (𝓝 (arithmeticDampingEntrance η 1 ^ 2)) :=
    ((tendsto_arithmeticDampingTransition hη 1).comp (tendsto_add_atTop_nat 1)).pow 2
  have := tendsto_nhds_unique h1 h0
  have hp := arithmeticDampingEntrance_one_pos hη
  have : 0 < arithmeticDampingEntrance η 1 ^ 2 := by positivity
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
