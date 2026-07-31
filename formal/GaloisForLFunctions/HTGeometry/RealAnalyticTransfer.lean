import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real smoothness of a holomorphic function along the real axis

A function holomorphic on an open subset of the plane is infinitely differentiable there over the
reals as well, so its restriction to the real axis is smooth wherever that axis meets the domain.
This is the standard route to real smoothness of `Gamma`, `zeta` and `xi` on the rays where they
have no poles: no real-variable estimate is needed, only holomorphy plus scalar restriction.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A holomorphic function restricted to the real axis is smooth as a real function. -/
theorem contDiffAt_re_comp_ofReal {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) {x : ℝ} (hx : (x : ℂ) ∈ s) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun y : ℝ => (f (y : ℂ)).re) x := by
  have hC : ContDiffOn ℂ n f s := hf.contDiffOn hs
  have hR : ContDiffOn ℝ n f s := hC.restrict_scalars ℝ
  have hat : ContDiffAt ℝ n f ((x : ℂ)) := hR.contDiffAt (hs.mem_nhds hx)
  have h1 : ContDiffAt ℝ n (fun y : ℝ => ((y : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.contDiff (n := n)).contDiffAt
  have h2 : ContDiffAt ℝ n (fun z : ℂ => z.re) ((x : ℂ)) :=
    (Complex.reCLM.contDiff (n := n)).contDiffAt
  exact h2.comp x (hat.comp x h1)

end GaloisForLFunctions.HTGeometry
