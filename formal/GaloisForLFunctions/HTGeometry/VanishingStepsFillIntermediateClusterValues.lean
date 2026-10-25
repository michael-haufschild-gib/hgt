import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Vanishing steps fill intermediate cluster values

The first late crossing overshoots its target by at most one step. Vanishing
step size makes every value between two subsequential limits a limit too.
-/
section

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Vanishing successive steps make arbitrarily late crossings approach their target. -/
theorem exists_late_approx_of_vanishing_steps
    (f : ℕ → ℝ) (c : ℝ)
    (hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0))
    (hbelow : ∀ N : ℕ, ∃ n, N ≤ n ∧ f n < c)
    (habove : ∀ N : ℕ, ∃ n, N ≤ n ∧ c < f n)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, N ≤ k ∧ |f k - c| < δ := by
  classical
  have hnorm : Tendsto (fun n => |f (n + 1) - f n|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using hstep.norm
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hnorm.eventually (gt_mem_nhds hδ))
  obtain ⟨n, hn, hfn⟩ := hbelow (max N M)
  obtain ⟨m, hnm, hfm⟩ := habove n
  have hex : ∃ k : ℕ, n ≤ k ∧ c ≤ f k := ⟨m, hnm, hfm.le⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  change n ≤ k ∧ c ≤ f k at hk
  have hnk : n < k := by
    by_contra h
    have hkn : k = n := le_antisymm (le_of_not_gt h) hk.1
    rw [hkn] at hk
    exact hfn.not_ge hk.2
  have hprev : f (k - 1) < c := by
    apply lt_of_not_ge
    intro h
    exact Nat.find_min hex (by omega : k - 1 < k) ⟨by omega, h⟩
  have hδk := hM (k - 1) (by omega : M ≤ k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hδk
  refine ⟨k, by omega, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hk.2)]
  have hupper := (abs_lt.mp hδk).2
  linarith only [hupper, hprev]

/-- A real sequence with vanishing steps has an increasing subsequence at each
value crossed arbitrarily late in both directions. -/
theorem exists_strictMono_subseq_of_late_crossings
    (f : ℕ → ℝ) (c : ℝ)
    (hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0))
    (hbelow : ∀ N : ℕ, ∃ n, N ≤ n ∧ f n < c)
    (habove : ∀ N : ℕ, ∃ n, N ≤ n ∧ c < f n) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun j => f (ns j)) atTop (𝓝 c) := by
  have hex (j : ℕ) := exists_late_approx_of_vanishing_steps f c hstep hbelow habove j
    (show 0 < 1 / ((j : ℝ) + 1) by positivity)
  choose k hk hclose using hex
  have hkTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.mpr fun N => ?_
    exact (eventually_ge_atTop N).mono fun j hj => hj.trans (hk j)
  have hf : Tendsto (fun j => f (k j)) atTop (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by
      simpa only [Real.norm_eq_abs] using (hclose j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨φ, hφ, hmono⟩ := strictMono_subseq_of_tendsto_atTop hkTop
  exact ⟨k ∘ φ, hmono, hf.comp hφ.tendsto_atTop⟩

/-- Every intermediate value of two subsequential real limits is again a
subsequential limit when the original sequence has vanishing successive steps. -/
theorem exists_strictMono_subseq_tendsto_between
    (f : ℕ → ℝ) (u v : ℕ → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    {a b c : ℝ} (ha : Tendsto (fun j => f (u j)) atTop (𝓝 a))
    (hb : Tendsto (fun j => f (v j)) atTop (𝓝 b))
    (hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0))
    (hac : a < c) (hcb : c < b) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun j => f (ns j)) atTop (𝓝 c) := by
  apply exists_strictMono_subseq_of_late_crossings f c hstep
  · intro N
    obtain ⟨j, hjN, hjc⟩ := ((hu.tendsto_atTop.eventually_ge_atTop N).and
      (ha.eventually (gt_mem_nhds hac))).exists
    exact ⟨u j, hjN, hjc⟩
  · intro N
    obtain ⟨j, hjN, hjc⟩ := ((hv.tendsto_atTop.eventually_ge_atTop N).and
      (hb.eventually (lt_mem_nhds hcb))).exists
    exact ⟨v j, hjN, hjc⟩

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_strictMono_subseq_tendsto_between
end
end

