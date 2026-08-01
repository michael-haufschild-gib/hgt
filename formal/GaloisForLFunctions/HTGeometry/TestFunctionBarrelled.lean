import GaloisForLFunctions.HTGeometry.TestFunctionComplete
import GaloisForLFunctions.HTGeometry.BarrelledSeminormBound
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The test space is barrelled, and the trace bound it yields

The test space is a complete, separated, first-countable uniform space, hence completely
metrizable, hence a Baire space, hence barrelled.  Uniform boundedness therefore turns a
pointwise bounded family of continuous functionals into a single bound by finitely many of the
derivative sup-norms — equivalently, by the `C^k` norm for one order `k`.

* `instBaireSpaceDeningerTest`, `instBarrelledSpaceDeningerTest` : the space is barrelled.
* `deningerTest_exists_order_bound` : the `C^k` bound for a dominated functional.
-/

namespace GaloisForLFunctions.HTGeometry

open TopologicalSpace

section Barrelled

variable {J : Compacts ℝ}

instance instBaireSpaceDeningerTest (J : Compacts ℝ) : BaireSpace (DeningerTest J) :=
  inferInstance

instance instBarrelledSpaceDeningerTest (J : Compacts ℝ) :
    BarrelledSpace ℝ (DeningerTest J) :=
  inferInstance

/-- **The seminorm bound on the test space.**  A functional dominated by a pointwise bounded
family of continuous functionals is bounded by finitely many derivative sup-norms. -/
theorem deningerTest_exists_bound {kappa : Type*} [Nonempty kappa]
    (F : kappa → DeningerTest J →L[ℝ] ℝ) (T : DeningerTest J → ℝ)
    (H : ∀ x : DeningerTest J, BddAbove (Set.range fun k => ‖F k x‖))
    (hT : ∀ x : DeningerTest J, ‖T x‖ ≤ ⨆ k, ‖F k x‖) :
    ∃ (s : Finset ℕ) (C : NNReal), ∀ x : DeningerTest J,
      ‖T x‖ ≤ C * (s.sup (deningerTestFamily J)) x :=
  exists_seminorm_bound_of_le_iSup (withSeminorms_deningerTest J) F T H hT

/-- **The `C^k` form of the bound.**  There is a single order `k` and a constant `C` with
`‖T φ‖ ≤ C · max_{m ≤ k} ‖φ⁽ᵐ⁾‖_∞` for every test function. -/
theorem deningerTest_exists_order_bound {kappa : Type*} [Nonempty kappa]
    (F : kappa → DeningerTest J →L[ℝ] ℝ) (T : DeningerTest J → ℝ)
    (H : ∀ x : DeningerTest J, BddAbove (Set.range fun k => ‖F k x‖))
    (hT : ∀ x : DeningerTest J, ‖T x‖ ≤ ⨆ k, ‖F k x‖) :
    ∃ (k : ℕ) (C : NNReal), ∀ x : DeningerTest J,
      ‖T x‖ ≤ C * ((Finset.range (k + 1)).sup (deningerTestFamily J)) x := by
  obtain ⟨s, C, hbound⟩ := deningerTest_exists_bound F T H hT
  refine ⟨s.sup id, C, fun x => ?_⟩
  refine le_trans (hbound x) ?_
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro m hm
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    exact Finset.le_sup (f := id) hm
  have hmono : s.sup (deningerTestFamily J)
      ≤ (Finset.range (s.sup id + 1)).sup (deningerTestFamily J) :=
    Finset.sup_mono hsub
  exact mul_le_mul_of_nonneg_left (hmono x) (NNReal.coe_nonneg C)

end Barrelled

end GaloisForLFunctions.HTGeometry
