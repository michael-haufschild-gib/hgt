import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalForcingRegularity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalH2Response
import GaloisForLFunctions.HTGeometry.PlanarSobolevSmoothRepresentative

/-!
The scalar cutoff identity and globally smooth original forcing give every local Sobolev order for the actual response.
-/

open MeasureTheory TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

private theorem all_orders_sum_sobolev {s : ℝ} {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev s 2 (f i)) : MemSobolev s 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

private theorem global_response_all_orders_step (q : XiZeroCopy) (minusBranch : Bool)
    (s : ℝ)
    (hh : ∀ g : PlanarChartTest, MemSobolev s 2
      (g.localDistribution (embedding (weakResponse q minusBranch)))) (g : PlanarChartTest) :
    MemSobolev (s+1) 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  have hscalar (a : PlanarChartTest) := (hh a).mono (show s-1 ≤ s by linarith)
  have hsource (a : PlanarChartTest) :=
    full_forcing_global_local_sobolev q minusBranch a (s-1)
  have hl : MemSobolev (s-1) 2
      (Δ (g.localDistribution (embedding (weakResponse q minusBranch)))) := by
    rw [full_response_global_cutoff_laplacian]
    have hD := all_orders_sum_sobolev (fun i =>
      (hh (g.derivative (direction i))).lineDerivOp (m := direction i))
    exact (((hD.smul (2:ℂ)).sub (hscalar g.laplacianTest)).add
      ((hscalar (g.divHeight 2)).smul (parameter q minusBranch))).add (hsource (g.divHeight 2))
  have hout := planar_sobolev_gain_two (hscalar g) hl
  convert hout using 1
  ring

/-- The actual globally lifted response has every local Sobolev order, with no seam exclusion. -/
theorem full_response_global_local_all_orders (q : XiZeroCopy) (branch : Bool)
    (n : ℕ) (g : PlanarChartTest) :
    MemSobolev (n : ℝ) 2 (g.localDistribution (embedding (weakResponse q branch))) := by
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero]
    exact (full_response_global_local_H1 q branch g).mono (by norm_num)
  | succ n ih =>
    simpa only [Nat.cast_add,Nat.cast_one] using global_response_all_orders_step q branch n ih g

/-- Every compact chart localization of the actual global response has a constructed smooth representative. -/
theorem full_response_global_local_smooth (q : XiZeroCopy) (branch : Bool) (g : PlanarChartTest) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᵐ[volume] g.localValue (embedding (weakResponse q branch)) := by
  obtain ⟨f,hf,he⟩ := planar_all_sobolev_smooth_representative
    (g.localVector (embedding (weakResponse q branch)))
    (fun n => full_response_global_local_all_orders q branch n g)
  exact ⟨f,hf,he.trans (g.localValue_memLp _).coeFn_toLp⟩

end
end RHTower.D4BMModularCore
