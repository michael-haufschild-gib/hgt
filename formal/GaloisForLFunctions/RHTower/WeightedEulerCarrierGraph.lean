import GaloisForLFunctions.RHTower.WeightedEulerCarrierFunctionals

/-!
# The symmetrised Euler tangent on the right pair of blocks

The two blocks `D.Kt` sit in the open strip `0 < Re < 1`, where both the Euler tangent and its
functional-equation reflection are holomorphic, so the symmetrised tangent restricts to a
continuous function there.  Complex conjugation fixes it, which is the hypothesis the doubling
across the real axis consumes.

* `RHTower.QuadrantCarrierData.feTangentKt`;
* `RHTower.QuadrantCarrierData.sigmaMap_feTangentKt`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

namespace QuadrantCarrierData

variable {f₂ : holoQuadrant →L[ℝ] ℝ} (D : QuadrantCarrierData f₂)

theorem Kt_re_pos {z : ℂ} (hz : z ∈ D.Kt) : 0 < z.re := by
  have h := D.Kt_re hz
  have := D.ha
  linarith

theorem Kt_re_lt_one {z : ℂ} (hz : z ∈ D.Kt) : z.re < 1 := by
  have h : z.re ≤ D.b := ((mem_doubledRect.mp hz).1).2
  have := D.hb
  linarith

/-- The symmetrised Euler tangent, restricted to the right pair of blocks. -/
def feTangentKt {p : ℕ} (hp : p.Prime) : C(D.Kt, ℂ) := by
  refine ⟨fun z => feEulerTangent p (z : ℂ), ?_⟩
  have hcont : ContinuousOn (eulerTangent p) {s : ℂ | 0 < s.re} :=
    (differentiableOn_eulerTangent hp).continuousOn
  have hsub : D.Kt ⊆ {s : ℂ | 0 < s.re} := fun z hz => D.Kt_re_pos hz
  have hmaps : Set.MapsTo (fun z : ℂ => 1 - z) D.Kt {s : ℂ | 0 < s.re} := by
    intro z hz
    have h1 : z.re < 1 := D.Kt_re_lt_one hz
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
    linarith
  have h1 : ContinuousOn (fun z : ℂ => eulerTangent p z) D.Kt := hcont.mono hsub
  have h2 : ContinuousOn (fun z : ℂ => eulerTangent p (1 - z)) D.Kt :=
    hcont.comp (continuousOn_const.sub continuousOn_id) hmaps
  exact (h1.sub h2).restrict

@[simp] theorem feTangentKt_apply {p : ℕ} (hp : p.Prime) (z : D.Kt) :
    D.feTangentKt hp z = feEulerTangent p (z : ℂ) := rfl

/-- **Conjugation fixes the symmetrised Euler tangent on the doubled carrier.** -/
theorem sigmaMap_feTangentKt {p : ℕ} (hp : p.Prime) :
    sigmaMap (fun _ hz => D.conj_mem_Kt hz) (D.feTangentKt hp) = D.feTangentKt hp := by
  ext z
  rw [sigmaMap_apply, feTangentKt_apply, conjMap_apply, feTangentKt_apply,
    feEulerTangent_conj hp.pos, Complex.conj_conj]

end QuadrantCarrierData

end RHTower
