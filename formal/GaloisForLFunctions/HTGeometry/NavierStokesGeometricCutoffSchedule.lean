import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyFinite

/-!
# Geometric cutoff schedules

This file formalizes the cutoff-schedule and geometric-tail core of Lemma 5.4 in the supplied
Navier--Stokes paper. A doubling scale leaves every fixed positive-parameter neighborhood after
finitely many stages. Consequently cutoff supports are locally finite, and the remaining numerical
budget has the exact `2⁻ʲ` tail used by the construction.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry.NavierStokesGeometricCutoffSchedule

noncomputable section

/-- Explicit doubling schedule used to localize successive correction stages. -/
def geometricCutoffScale (a : ℝ) (j : ℕ) : ℝ := a * (2 : ℝ) ^ j

@[simp] theorem geometricCutoffScale_zero (a : ℝ) :
    geometricCutoffScale a 0 = a := by
  simp [geometricCutoffScale]

theorem geometricCutoffScale_succ (a : ℝ) (j : ℕ) :
    geometricCutoffScale a (j + 1) = 2 * geometricCutoffScale a j := by
  simp [geometricCutoffScale, pow_succ]
  ring

theorem geometricCutoffScale_pos {a : ℝ} (ha : 0 < a) (j : ℕ) :
    0 < geometricCutoffScale a j := by
  exact mul_pos ha (pow_pos (by norm_num) _)

/-- At each fixed positive scale parameter, all sufficiently late cutoffs have left their support. -/
theorem eventually_one_le_geometricCutoffScale_mul {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    ∀ᶠ j : ℕ in atTop, 1 ≤ geometricCutoffScale a j * q := by
  have hpow : ∀ᶠ j : ℕ in atTop, 1 / (a * q) ≤ (2 : ℝ) ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [hpow] with j hj
  have haq : 0 < a * q := mul_pos ha hq
  have hmul := mul_le_mul_of_nonneg_right hj haq.le
  calc
    1 = (1 / (a * q)) * (a * q) := by field_simp [haq.ne']
    _ ≤ (2 : ℝ) ^ j * (a * q) := hmul
    _ = geometricCutoffScale a j * q := by simp [geometricCutoffScale]; ring

theorem eventually_geometricCutoff_eq_zero {E : Type*} [Zero E]
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (χ : ℝ → E)
    (hχ : ∀ x, 1 ≤ x → χ x = 0) :
    ∀ᶠ j : ℕ in atTop, χ (geometricCutoffScale a j * q) = 0 :=
  (eventually_one_le_geometricCutoffScale_mul ha hq).mono fun _ hj ↦ hχ _ hj

theorem finite_geometricCutoff_support {E : Type*} [Zero E]
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (χ : ℝ → E)
    (hχ : ∀ x, 1 ≤ x → χ x = 0) :
    (Function.support fun j : ℕ ↦ χ (geometricCutoffScale a j * q)).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_geometricCutoff_eq_zero ha hq χ hχ)
  refine (Finset.range N).finite_toSet.subset ?_
  intro j hj
  simp only [Function.mem_support] at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  exact hj (hN j (Nat.le_of_not_gt hnot))

/-- Positive scale parameters on which the `j`th cutoff can still be active. -/
def geometricCutoffRegion (a : ℝ) (j : ℕ) : Set {q : ℝ // 0 < q} :=
  {q | geometricCutoffScale a j * (q : ℝ) < 1}

/-- The active regions of a doubling cutoff schedule are locally finite on `q > 0`. -/
theorem locallyFinite_geometricCutoffRegion {a : ℝ} (ha : 0 < a) :
    LocallyFinite (geometricCutoffRegion a) := by
  intro q
  let U : Set {q : ℝ // 0 < q} := {y | (q : ℝ) / 2 < (y : ℝ)}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_subtype_val
  have hqU : q ∈ U := by
    dsimp [U]
    linarith [q.property]
  have hev := eventually_one_le_geometricCutoffScale_mul ha (half_pos q.property)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨U, hUopen.mem_nhds hqU, (Finset.range N).finite_toSet.subset ?_⟩
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hjN
  have hNj : N ≤ j := Nat.le_of_not_gt hjN
  rcases hj with ⟨y, hyRegion, hyU⟩
  have hscalePos : 0 < geometricCutoffScale a j := geometricCutoffScale_pos ha j
  have hlt : geometricCutoffScale a j * ((q : ℝ) / 2) <
      geometricCutoffScale a j * (y : ℝ) :=
    mul_lt_mul_of_pos_left hyU hscalePos
  exact (not_lt_of_ge (hN j hNj)) (hlt.trans hyRegion)

theorem locallyFinite_geometricCutoff_support {E : Type*} [Zero E]
    {a : ℝ} (ha : 0 < a) (χ : ℝ → E) (hχ : ∀ x, 1 ≤ x → χ x = 0) :
    LocallyFinite fun j : ℕ ↦
      Function.support fun q : {q : ℝ // 0 < q} ↦ χ (geometricCutoffScale a j * (q : ℝ)) := by
  refine (locallyFinite_geometricCutoffRegion ha).subset fun j q hq ↦ ?_
  simp only [Function.mem_support] at hq
  simp only [geometricCutoffRegion, Set.mem_setOf_eq]
  exact lt_of_not_ge fun h ↦ hq (hχ _ h)

/-- Exact tail budget behind the `2⁻ʲ` estimate in Lemma 5.4. -/
theorem hasSum_geometricCutoffTail (J : ℕ) :
    HasSum (fun k : ℕ ↦ (1 / 2 : ℝ) ^ (J + 1 + k)) ((1 / 2 : ℝ) ^ J) := by
  convert hasSum_geometric_two' ((1 / 2 : ℝ) ^ J) using 1
  · ext k
    rw [pow_add, pow_add]
    simp only [div_eq_mul_inv, pow_one]
    rw [← inv_pow]
    ac_rfl

theorem tsum_geometricCutoffTail (J : ℕ) :
    ∑' k : ℕ, (1 / 2 : ℝ) ^ (J + 1 + k) = (1 / 2 : ℝ) ^ J :=
  (hasSum_geometricCutoffTail J).tsum_eq

end

end GaloisForLFunctions.HTGeometry.NavierStokesGeometricCutoffSchedule
