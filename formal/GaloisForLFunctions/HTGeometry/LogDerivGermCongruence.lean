import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Germ congruence for logarithmic derivatives

The logarithmic derivative depends only on the germ of a function, both on an ordinary and a
punctured neighborhood.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

theorem logDeriv_congr_nhds {f g : 𝕜 → 𝕜'} {x : 𝕜}
    (h : f =ᶠ[𝓝 x] g) : logDeriv f =ᶠ[𝓝 x] logDeriv g :=
  h.deriv.div h

theorem logDeriv_congr_nhdsNE {f g : 𝕜 → 𝕜'} {x : 𝕜}
    (h : f =ᶠ[𝓝[≠] x] g) : logDeriv f =ᶠ[𝓝[≠] x] logDeriv g :=
  h.nhdsNE_deriv.div h

end GaloisForLFunctions.HTGeometry
