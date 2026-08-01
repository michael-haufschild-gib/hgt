import GaloisForLFunctions.HTGeometry.TestFunctionTopology
import GaloisForLFunctions.HTGeometry.UniformCauchyLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Cauchy sequences in the test space are uniformly Cauchy at every order

A sequence that is Cauchy for the seminorm topology of the test space has, at every order of
differentiation, a uniformly Cauchy sequence of derivatives.  This is the bridge between the
abstract uniform structure and the analytic statements about uniform limits.

* `deningerTestSupNorm_sub` : the derivative of a difference.
* `uniformCauchySeqOn_iteratedDeriv_of_cauchySeq` : the bridge.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology TopologicalSpace

section CauchyBridge

variable {J : Compacts ℝ}

/-- The iterated derivative of a difference of test functions. -/
theorem iteratedDeriv_sub_of_mem {phi psi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace (J : Set ℝ)) (hpsi : psi ∈ deningerTestSpace (J : Set ℝ))
    (m : ℕ) (t : ℝ) :
    iteratedDeriv m (phi - psi) t = iteratedDeriv m phi t - iteratedDeriv m psi t := by
  refine iteratedDeriv_sub ?_ ?_
  · exact (hphi.1.of_le (by exact_mod_cast le_top)).contDiffAt
  · exact (hpsi.1.of_le (by exact_mod_cast le_top)).contDiffAt

/-- The pointwise bound of a derivative difference by the sup-norm of the difference. -/
theorem norm_iteratedDeriv_sub_le {phi psi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace (J : Set ℝ)) (hpsi : psi ∈ deningerTestSpace (J : Set ℝ))
    (m : ℕ) (t : ℝ) :
    ‖iteratedDeriv m phi t - iteratedDeriv m psi t‖
      ≤ deningerTestSupNorm m (phi - psi) := by
  rw [← iteratedDeriv_sub_of_mem hphi hpsi m t]
  exact norm_iteratedDeriv_le_supNorm J.isCompact
    ((deningerTestSpace (J : Set ℝ)).sub_mem hphi hpsi) m t

/-- **Cauchy in the test space means uniformly Cauchy at every order.** -/
theorem uniformCauchySeqOn_iteratedDeriv_of_cauchySeq {u : ℕ → DeningerTest J}
    (hu : CauchySeq u) (m : ℕ) :
    UniformCauchySeqOn (fun n => iteratedDeriv m ((u n : ℝ → ℂ))) Filter.atTop Set.univ := by
  have hten : Filter.Tendsto (fun q : ℕ × ℕ => u q.1 - u q.2)
      (Filter.atTop ×ˢ Filter.atTop) (𝓝 0) :=
    ((IsUniformAddGroup.cauchy_map_iff_tendsto _ _).mp hu).2
  rw [(withSeminorms_deningerTest J).tendsto_nhds] at hten
  rw [Metric.uniformCauchySeqOn_iff]
  intro eps heps
  have hev := hten m eps heps
  rw [Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := hev
  obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp hpa
  obtain ⟨Nb, hNb⟩ := Filter.eventually_atTop.mp hpb
  refine ⟨max Na Nb, fun n hn k hk t _ => ?_⟩
  have hkey := hP (hNa n (le_trans (le_max_left Na Nb) hn))
    (hNb k (le_trans (le_max_right Na Nb) hk))
  have hcoe : deningerTestFamily J m (u n - u k)
      = deningerTestSupNorm m ((u n : ℝ → ℂ) - (u k : ℝ → ℂ)) := by
    show deningerTestSupNorm m (((u n - u k : DeningerTest J) : ℝ → ℂ)) = _
    rw [Submodule.coe_sub]
  have hlt : deningerTestSupNorm m ((u n : ℝ → ℂ) - (u k : ℝ → ℂ)) < eps := by
    rw [← hcoe]
    simpa using hkey
  refine lt_of_le_of_lt ?_ hlt
  rw [dist_eq_norm]
  exact norm_iteratedDeriv_sub_le (u n).2 (u k).2 m t

end CauchyBridge

end GaloisForLFunctions.HTGeometry
