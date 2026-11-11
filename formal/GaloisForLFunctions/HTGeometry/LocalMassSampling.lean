import GaloisForLFunctions.HTGeometry.BoundedFiberMassHasSummablePowerTails
import Mathlib.Analysis.MeanInequalities

/-!
# Sampling summable cell bounds against locally bounded mass

A mass bound on windows of any fixed positive length gives a bound on
unit windows. Consequently every summable bound on the integer cells
remains summable after sampling against that mass.
-/

open Finset Set

namespace GaloisForLFunctions.HTGeometry

/-- A bound on fixed-length windows extends to unit windows by finite covering. -/
theorem exists_unit_local_mass_bound {ι : Type*} (t : ι → ℝ)
    {w : ι → ℝ} {L B : ℝ} (hL : 0 < L)
    (hlocal : ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + L) → ∑ i ∈ s, w i ≤ B) :
    ∃ D : ℝ, ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + 1) → ∑ i ∈ s, w i ≤ D := by
  classical
  have hn : ∀ n : ℕ, ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + n * L) →
      ∑ i ∈ s, w i ≤ (n + 1 : ℝ) * B := by
    intro n
    induction n with
    | zero =>
      intro x s hs
      simpa only [Nat.cast_zero, zero_add, one_mul] using hlocal x s (by
        intro i hi
        have h := hs i hi
        refine ⟨h.1, ?_⟩
        have hi0 : t i ≤ x := by simpa only [Nat.cast_zero, zero_mul, add_zero] using h.2
        exact hi0.trans (le_add_of_nonneg_right hL.le))
    | succ n ih =>
      intro x s hs
      have hleft := ih x (s.filter (fun i => t i ≤ x + n * L)) (by
        intro i hi
        exact ⟨(hs i (mem_filter.mp hi).1).1, (mem_filter.mp hi).2⟩)
      have hright := hlocal (x + n * L) (s.filter (fun i => ¬ t i ≤ x + n * L)) (by
        intro i hi
        have h := hs i (mem_filter.mp hi).1
        refine ⟨(lt_of_not_ge (mem_filter.mp hi).2).le, ?_⟩
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h.2)
      have heq := sum_filter_add_sum_filter_not s (fun i => t i ≤ x + n * L) w
      push_cast
      linarith only [hleft, hright, heq]
  let n : ℕ := ⌈1 / L⌉₊
  have hcover : 1 ≤ (n : ℝ) * L := (div_le_iff₀ hL).mp (Nat.le_ceil (1 / L))
  refine ⟨(n + 1 : ℝ) * B, fun x s hs => hn n x s ?_⟩
  intro i hi
  exact ⟨(hs i hi).1, (hs i hi).2.trans (add_le_add le_rfl hcover)⟩

/-- An integer-cell majorant transfers through any uniformly locally bounded mass. -/
theorem summable_mul_of_local_mass_cells {ι : Type*} (t : ι → ℝ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {L B : ℝ} (hL : 0 < L)
    (hlocal : ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + L) → ∑ i ∈ s, w i ≤ B)
    {v : ℤ → ℝ} (hv : ∀ k, 0 ≤ v k) (hvs : Summable v) :
    Summable (fun i => w i * v ⌊t i⌋) := by
  obtain ⟨D, hD⟩ := exists_unit_local_mass_bound t hL hlocal
  apply summable_mul_of_bounded_fiber_mass (fun i => ⌊t i⌋) hw (B := D) _ hv hvs
  intro k s
  let incl : {i // ⌊t i⌋ = k} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have h := hD k (s.map incl) (by
    intro i hi
    obtain ⟨i, _, rfl⟩ := mem_map.mp hi
    constructor
    · change (k : ℝ) ≤ t i
      simpa only [i.2] using Int.floor_le (t i)
    · change t i ≤ (k : ℝ) + 1
      simpa only [i.2] using (Int.lt_floor_add_one (t i)).le)
  rw [sum_map] at h
  exact h

/-- Hölder pairs an `ℓᵖ` family with an `ℓᑫ` cell bound sampled against
uniformly bounded local mass. -/
theorem summable_mass_mul_of_lp_cell_bound {ι : Type*} (t : ι → ℝ)
    {w a : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    {L B : ℝ} (hL : 0 < L)
    (hlocal : ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + L) → ∑ i ∈ s, w i ≤ B)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (has : Summable (fun i => a i ^ p))
    {v : ℤ → ℝ} (hv : ∀ k, 0 ≤ v k) (hvs : Summable (fun k => v k ^ q)) :
    Summable (fun i => w i * a i * v ⌊t i⌋) := by
  classical
  have hwB : ∀ i, w i ≤ B := by
    intro i
    simpa only [sum_singleton] using hlocal (t i) {i} (by
      intro j hj
      have hj' := mem_singleton.mp hj
      subst j
      exact ⟨le_rfl, le_add_of_nonneg_right hL.le⟩)
  let K := max B 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hwpow : ∀ i, w i ^ q ≤ K ^ (q - 1) * w i := by
    intro i
    rcases eq_or_lt_of_le (hw i) with hi | hi
    · rw [← hi, Real.zero_rpow hpq.symm.ne_zero, mul_zero]
    · calc
        w i ^ q = w i ^ (q - 1) * w i := by
          conv_lhs => rw [show q = (q - 1) + 1 by ring]
          rw [Real.rpow_add hi, Real.rpow_one]
        _ ≤ K ^ (q - 1) * w i := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (hw i) ((hwB i).trans (le_max_left _ _))
            hpq.symm.sub_one_pos.le) (hw i)
  have hsample := summable_mul_of_local_mass_cells t hw hL hlocal
    (fun k => Real.rpow_nonneg (hv k) q) hvs
  have hq : Summable (fun i => (w i * v ⌊t i⌋) ^ q) := by
    refine Summable.of_nonneg_of_le
      (fun i => Real.rpow_nonneg (mul_nonneg (hw i) (hv _)) _) ?_
      (hsample.mul_left (K ^ (q - 1)))
    intro i
    rw [Real.mul_rpow (hw i) (hv _)]
    calc
      w i ^ q * v ⌊t i⌋ ^ q ≤ (K ^ (q - 1) * w i) * v ⌊t i⌋ ^ q :=
        mul_le_mul_of_nonneg_right (hwpow i) (Real.rpow_nonneg (hv _) _)
      _ = K ^ (q - 1) * (w i * v ⌊t i⌋ ^ q) := by ring
  exact (Real.summable_mul_of_Lp_Lq_of_nonneg hpq ha
    (fun i => mul_nonneg (hw i) (hv _)) has hq).congr fun i => by ring

end GaloisForLFunctions.HTGeometry
