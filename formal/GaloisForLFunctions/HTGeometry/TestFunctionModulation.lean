import GaloisForLFunctions.HTGeometry.TestFunctionTruncatedTrace
import GaloisForLFunctions.HTGeometry.FlowTemperedGrowth

/-!
# Modulation preserves the test space, and the seminorm bound it needs

Multiplying a test function by a unimodular exponential keeps it smooth and does not enlarge its
support, so the modulated weights of the temperedness argument are again test functions.

The bound the trace estimate needs is stated as a uniform bound on Fréchet derivatives up to a
fixed order; that is the same thing as a bound on the finite supremum of the test-space seminorms
up to that order.

* `complexModulatedWeight_mem_deningerTestSpace` : modulation preserves the test space.
* `sup_le_of_forall_norm_iteratedFDeriv_le` : the converse bridge between the two bound shapes.
-/

namespace GaloisForLFunctions.HTGeometry

open TopologicalSpace

section Modulation

variable {J : Set ℝ}

/-- **Modulation preserves the test space.**  The modulating exponential is smooth and never
vanishes, so the product is smooth and supported where the original weight is. -/
theorem complexModulatedWeight_mem_deningerTestSpace {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) (x : ℝ) :
    complexModulatedWeight phi x ∈ deningerTestSpace J := by
  refine ⟨(contDiff_modulation x).mul hphi.1, ?_⟩
  refine le_trans (closure_mono ?_) hphi.2
  intro t ht
  by_contra hnot
  have hzero : phi t = 0 := Function.notMem_support.mp hnot
  exact ht (by simp [complexModulatedWeight, hzero])

end Modulation

section SupBound

variable {J : Compacts ℝ}

/-- **The converse bridge.**  A uniform bound on all Fréchet derivatives up to order `k` bounds
the finite supremum of the test-space seminorms up to that order. -/
theorem sup_le_of_forall_norm_iteratedFDeriv_le {phi : DeningerTest J} {k : ℕ} {B : ℝ}
    (h : ∀ m ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ m ((phi : ℝ → ℂ)) t‖ ≤ B) :
    ((Finset.range (k + 1)).sup (deningerTestFamily J)) phi ≤ B := by
  have hnonneg : 0 ≤ B := le_trans (norm_nonneg _) (h 0 (Nat.zero_le _) 0)
  have hpt : ∀ m ∈ Finset.range (k + 1), (deningerTestFamily J m) phi ≤ B := by
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hval : (deningerTestFamily J m) phi = deningerTestSupNorm m ((phi : ℝ → ℂ)) := rfl
    rw [hval]
    refine deningerTestSupNorm_le m fun t => ?_
    have hFD := h m hmk t
    rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFD
  exact Seminorm.finset_sup_apply_le hnonneg hpt

end SupBound

end GaloisForLFunctions.HTGeometry
