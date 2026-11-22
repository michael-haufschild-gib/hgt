import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivLocalForm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Local decomposition of the logarithmic derivative at an analytic zero. -/

open Complex Filter Topology

namespace GlobalTheory.ExplicitRect

theorem logDeriv_pole {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hn : analyticOrderAt f p ≠ ⊤) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = (analyticOrderNatAt f p : ℂ) / (s - p) + g s := by
  have hord : meromorphicOrderAt f p = ((analyticOrderNatAt f p : ℤ) : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hn, ENat.map_coe]
  obtain ⟨g, hg, he⟩ := GaloisForLFunctions.HTGeometry.exists_analyticAt_logDeriv_local_form
    hf.meromorphicAt hord
  refine ⟨g, hg, ?_⟩
  filter_upwards [he] with z hz
  simpa only [logDeriv_apply, Int.cast_natCast] using hz

theorem analyticAt_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p :=
  analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hu)

end GlobalTheory.ExplicitRect
