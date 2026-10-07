import GaloisForLFunctions.RHTower.WindingNumber
import GaloisForLFunctions.Bottcher.CircleDegree
import GaloisForLFunctions.Bottcher.WindDynamics

open Topology unitInterval Complex Pi1CMinusZero

namespace RHTower

/-- Affine reparametrization identifies real-parameter winding with exponential-cover degree. -/
theorem bottcher_wind_eq_windingNumber {X : Type*} [TopologicalSpace X]
    (g : X → ℂ) (hg : Continuous g) (hgn : ∀ x, g x ≠ 0)
    {x : X} (p : Path x x) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsLoop γ a b)
    (hp : ∀ t : I, γ (a + (b - a) * (t : ℝ)) = g (p t)) :
    Bottcher.wind g hg hgn p = windingNumber γ a b := by
  obtain ⟨hLc, hLe⟩ := contLog_spec hγ.continuous hγ.nonzero
  have hbase : γ a = g x := by simpa using hp 0
  let L : C(I, ℂ) :=
    ⟨fun t => contLog γ (a + (b - a) * (t : ℝ)) - contLog γ a,
      (hLc.comp (by fun_prop)).sub continuous_const⟩
  change degZ ⟦Bottcher.transLoop g hg hgn p⟧ = _
  apply degZ_eq_of_lift (Bottcher.transLoop g hg hgn p) L
  · funext t
    apply Subtype.ext
    change exp (contLog γ (a + (b - a) * (t : ℝ)) - contLog γ a) = g (p t) / g x
    rw [exp_sub, hLe, hLe, hp t, hbase]
  · simp [L, e0]
  · simpa [L] using contLog_increment hγ hLc hLe

end RHTower
