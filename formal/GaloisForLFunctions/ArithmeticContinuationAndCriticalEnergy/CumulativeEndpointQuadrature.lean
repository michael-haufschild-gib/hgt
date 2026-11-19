import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Right-endpoint quadrature on cumulative mass

Pain's discrete monotone inequality (arXiv:2603.08959, Theorem 2.1) holds
on uneven partitions, including repeated endpoints. The difference from the
integral gains a factor of the mesh. On an infinite partition with bounded
steps the difference has a limit, with a tail controlled by the remaining
variation of the integrand.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.CumulativeQuadrature

/-- The weight at each right endpoint is the mass gained since its predecessor. -/
def rightSum (x : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (x (i+1) - x i) * g (x (i+1))

/-- Signed difference between the integral and its right-endpoint reading. -/
def defect (x : ℕ → ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∫ t in x 0..x n, g t) - rightSum x g n

private theorem cell_bounds {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : AntitoneOn g (Set.Icc a b)) :
    (b-a)*g b ≤ ∫ t in a..b, g t ∧ (∫ t in a..b, g t) ≤ (b-a)*g a := by
  have hg' : AntitoneOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hi := hg'.intervalIntegrable (μ := volume)
  have h₁ := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := g b)) hi
    (fun t ht => hg ht ⟨hab, le_rfl⟩ ht.2)
  have h₂ := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := g a))
    (fun t ht => hg ⟨le_rfl, hab⟩ ht ht.1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using And.intro h₁ h₂

private theorem step {x : ℕ → ℝ} {g : ℝ → ℝ} (hx : Monotone x) (i : ℕ)
    (hg : AntitoneOn g (Set.Icc (x 0) (x (i+1)))) :
    0 ≤ defect x g (i+1) - defect x g i ∧
      defect x g (i+1) - defect x g i ≤
        (x (i+1)-x i) * (g (x i)-g (x (i+1))) := by
  have h₀ := hx (Nat.zero_le i)
  have h₁ := hx (Nat.le_succ i)
  have hleft := hg.mono (Set.Icc_subset_Icc le_rfl h₁)
  have hright := hg.mono (Set.Icc_subset_Icc h₀ le_rfl)
  have hcell := cell_bounds h₁ hright
  rw [← Set.uIcc_of_le h₀] at hleft
  rw [← Set.uIcc_of_le h₁] at hright
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hleft.intervalIntegrable (μ := volume)) hright.intervalIntegrable
  simp only [defect, rightSum, Finset.sum_range_succ, ← hsplit, mul_sub]
  constructor <;> linarith only [hcell.1, hcell.2]

/-- Pain's inequality, with an upper bound for its loss in terms of the
mesh and the oscillation of the integrand. -/
theorem defect_bounds {x : ℕ → ℝ} {g : ℝ → ℝ} {M : ℝ} (n : ℕ)
    (hx : Monotone x) (hg : AntitoneOn g (Set.Icc (x 0) (x n)))
    (hmesh : ∀ i < n, x (i+1)-x i ≤ M) :
    0 ≤ defect x g n ∧ defect x g n ≤ M*(g (x 0)-g (x n)) := by
  induction n with
  | zero => simp [defect, rightSum]
  | succ n ih =>
    have hs := step hx n hg
    have hn := hx (Nat.le_succ n)
    obtain ⟨hl, hu⟩ := ih (hg.mono (Set.Icc_subset_Icc le_rfl hn))
      (fun i hi => hmesh i (Nat.lt_succ_of_lt hi))
    have hdrop := sub_nonneg.mpr (hg ⟨hx (Nat.zero_le n), hn⟩
      ⟨hx (Nat.zero_le _), le_rfl⟩ hn)
    have h := hs.2.trans (mul_le_mul_of_nonneg_right (hmesh n (Nat.lt_succ_self n)) hdrop)
    constructor
    · linarith only [hl, hs.1]
    · rw [mul_sub] at h hu ⊢
      linarith only [h, hu]

/-- A nonnegative decreasing density on an infinite partition has a limiting
quadrature defect. The remaining error after any endpoint is at most the
mesh times the density there. -/
theorem limiting_defect {x : ℕ → ℝ} {g : ℝ → ℝ} {M : ℝ}
    (hx : Monotone x) (hg : AntitoneOn g (Set.Ici (x 0)))
    (hpos : ∀ i, 0 ≤ g (x i)) (hmesh : ∀ i, x (i+1)-x i ≤ M) :
    ∃ c : ℝ, Tendsto (defect x g) atTop (𝓝 c) ∧
      ∀ n, 0 ≤ c - defect x g n ∧ c - defect x g n ≤ M*g (x n) := by
  have hM := (sub_nonneg.mpr (hx (Nat.le_succ 0))).trans (hmesh 0)
  have hs (i : ℕ) := step hx i (hg.mono (fun _ ht => ht.1))
  have hmono := monotone_nat_of_le_succ (fun i => sub_nonneg.mp (hs i).1)
  have hanti : Antitone (fun i => defect x g i + M*g (x i)) := by
    apply antitone_nat_of_succ_le
    intro i
    have hi := hx (Nat.le_succ i)
    have hd := hg (hx (Nat.zero_le i)) (hx (Nat.zero_le (i+1))) hi
    have h := (hs i).2.trans (mul_le_mul_of_nonneg_right (hmesh i) (sub_nonneg.mpr hd))
    rw [mul_sub] at h
    linarith only [h]
  have hb : BddAbove (Set.range (defect x g)) := by
    refine ⟨defect x g 0 + M*g (x 0), ?_⟩
    rintro _ ⟨i,rfl⟩
    exact (le_add_of_nonneg_right (mul_nonneg hM (hpos i))).trans (hanti (Nat.zero_le i))
  have ht := tendsto_atTop_ciSup hmono hb
  refine ⟨_, ht, fun n => ⟨sub_nonneg.mpr (le_ciSup hb n), ?_⟩⟩
  apply sub_le_iff_le_add'.mpr
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with i hi
  exact (le_add_of_nonneg_right (mul_nonneg hM (hpos i))).trans (hanti hi)

#print axioms defect_bounds
#print axioms limiting_defect

end GaloisForLFunctions.CumulativeQuadrature
