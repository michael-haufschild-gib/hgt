import GaloisForLFunctions.RHTower.WeightedEulerCarrierFunctionals
import GaloisForLFunctions.HTGeometry.PrimeQuadrantGraph
import GaloisForLFunctions.RHTower.WeightedEulerCarrierTangent
import GaloisForLFunctions.RHTower.WeightedEulerGrowingCarrierElimination

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

theorem precompCLM_feTangentKt (p : Nat.Primes) :
    precompCLM (inclMap D.Kc_subset_Kt) (D.feTangentKt p.2)
      = quadrantRestrict D.hquad (eulerTangentElement p) := by
  ext z
  rfl

/-- **The total functional evaluates on the Euler tangent to twice the realized functional.** -/
theorem total_feTangent (p : Nat.Primes) (h : C(D.Ktot, ℂ))
    (hval : ∀ z : D.Ktot, h z = eulerTangent (p : ℕ) (z : ℂ)) :
    D.total h = ((2 * f₂ (eulerTangentElement p) : ℝ) : ℂ) := by
  have hsplit : precompCLM (inclMap D.Kt_subset_Ktot) h
      - precompCLM (feReflMap (fun _ hz => D.one_sub_mem_Kt' hz))
          (precompCLM (inclMap D.Kt'_subset_Ktot) h) = D.feTangentKt p.2 := by
    ext z
    simp only [ContinuousMap.sub_apply, precompCLM_apply, feTangentKt_apply]
    rw [hval, hval]
    rfl
  have hD : D.total h = D.doubled (D.feTangentKt p.2) := by
    rw [total]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, reflected,
      feReflFunctional_apply, ← map_sub, hsplit]
  rw [hD, doubled, doubledFunctional_apply_of_sigma_eq _ _ _ (D.sigmaMap_feTangentKt p.2),
    D.precompCLM_feTangentKt p]
  exact congrArg (fun r : ℝ => ((2 * r : ℝ) : ℂ)) (D.hL (eulerTangentElement p))

theorem mem_Ktot_corner : ((D.a : ℂ) + (D.c : ℂ) * Complex.I) ∈ D.Ktot := by
  refine D.Kt_subset_Ktot (D.Kc_subset_Kt ?_)
  rw [Kc, mem_rect]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      linarith [D.hab, D.hcd]

/-- **The total functional kills every power of the coordinate.** -/
theorem total_coord_pow_eq_zero (f₁ : PrimeTangent →L[ℝ] ℝ)
    (hgr : ∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0)
    (m : ℕ) : D.total (coordMap D.Ktot ^ m) = 0 := by
  classical
  haveI : Nonempty D.Ktot := ⟨⟨_, D.mem_Ktot_corner⟩⟩
  set lam : ℕ → ℂ := fun n =>
    if h : n.Prime then ((2 * f₁ (primeTangentGen ⟨n, h⟩) : ℝ) : ℂ) else 0 with hlam
  have hre : ∀ z ∈ D.Ktot, (1 - D.b) ≤ z.re := fun z hz => (D.Ktot_re hz).1
  have hgraph : ∀ p : ℕ, p.Prime →
      lam p + D.total (compactPrimeEulerUnitTangent (coordMap D.Ktot) p) = 0 := by
    intro p hp
    have hval : ∀ z : D.Ktot,
        compactPrimeEulerUnitTangent (coordMap D.Ktot) p z = eulerTangent p (z : ℂ) := by
      intro z
      rw [compactPrimeEulerUnitTangent_coordMap D.one_sub_b_pos hre hp.two_le z]
      rfl
    rw [D.total_feTangent ⟨p, hp⟩ _ hval, hlam]
    simp only [dif_pos hp]
    rw [← Complex.ofReal_add]
    have := hgr ⟨p, hp⟩
    have h2 : 2 * f₁ (primeTangentGen ⟨p, hp⟩) + 2 * f₂ (eulerTangentElement ⟨p, hp⟩) = 0 := by
      linarith
    rw [h2, Complex.ofReal_zero]
  have hdual : ∀ p : ℕ, p.Prime →
      ‖lam p‖ ≤ (2 * ‖f₁‖) * criticalNorm_weightedEulerDualReduction (primeCoordinateField p) := by
    intro p hp
    rw [hlam]
    simp only [dif_pos hp, Complex.norm_real, Real.norm_eq_abs, criticalNorm_coordinate hp]
    have hb := f₁.le_opNorm (primeTangentGen ⟨p, hp⟩)
    rw [norm_primeTangentGen] at hb
    have hw : primeTangentWeight ⟨p, hp⟩ = Real.log p / p := rfl
    rw [hw] at hb
    rw [abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have habs : |f₁ (primeTangentGen ⟨p, hp⟩)| ≤ ‖f₁‖ * (Real.log p / p) := by
      simpa [Real.norm_eq_abs] using hb
    calc 2 * |f₁ (primeTangentGen ⟨p, hp⟩)| ≤ 2 * (‖f₁‖ * (Real.log p / p)) := by linarith
      _ = 2 * ‖f₁‖ * (Real.log p / p) := by ring
  exact (compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical D.total
    (coordMap D.Ktot) lam D.one_sub_b_pos (by positivity)
    (fun k => D.Ktot_re k.2) D.hb hgraph hdual).2 m

end QuadrantCarrierData

end RHTower
