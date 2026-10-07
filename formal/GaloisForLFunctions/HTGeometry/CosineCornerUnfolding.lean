import GaloisForLFunctions.HTGeometry.CosineProductRepair
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Two analytic submersions at the reflected-cosine corner

An algebraic correction resolves the conic branch at infinity. An independent
exponential coordinate then makes the target-fiber equation analytic at the
corner. Only the scalar holomorphic implicit-function theorem is used from the
legacy parametric-branch module; there is no spectral input.
-/

namespace GaloisForLFunctions.HTGeometry.CosineCornerUnfolding

open Complex Filter
open scoped Topology

noncomputable section

private theorem partial_apply_one
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P × ℂ → ℂ} {p : P} {u d : ℂ}
    (hf : DifferentiableAt ℂ f (p, u))
    (hd : HasDerivAt (fun z : ℂ ↦ f (p, z)) d u) :
    (fderiv ℂ f (p, u)) (0, 1) = d := by
  have hi : HasFDerivAt (fun z : ℂ ↦ (p, z)) (ContinuousLinearMap.inr ℂ P ℂ) u := by
    simpa using ((ContinuousLinearMap.inr ℂ P ℂ).hasFDerivAt (x := u)).add_const (p, (0 : ℂ))
  have hc := hf.hasFDerivAt.comp u hi
  have he := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) (hc.unique hd.hasFDerivAt)
  simpa using he

def conicRelation (c : ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  2 * (2 * Real.pi + p.1.1 * p.1.2) * p.2 - p.1.1 * p.2 ^ 2 - c * p.1.1

theorem exists_conic_correction (c u₀ : ℂ) :
    ∃ E : ℂ × ℂ → ℂ, AnalyticAt ℂ E (0, u₀) ∧ E (0, u₀) = 0 ∧
      ∀ᶠ p in 𝓝 (0, u₀), conicRelation c (p, E p) = 0 := by
  have hf : AnalyticAt ℂ (conicRelation c) ((0, u₀), 0) := by
    have ht : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ p.1.1) ((0, u₀), 0) :=
      analyticAt_fst.comp (f := Prod.fst) analyticAt_fst
    have hu : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ p.1.2) ((0, u₀), 0) :=
      analyticAt_snd.comp (f := Prod.fst) analyticAt_fst
    have he : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ p.2) ((0, u₀), 0) := analyticAt_snd
    exact (((analyticAt_const.mul (analyticAt_const.add (ht.mul hu))).mul he).sub
      (ht.mul (he.pow 2))).sub (analyticAt_const.mul ht)
  have hd : HasDerivAt (fun e : ℂ ↦ conicRelation c ((0, u₀), e)) (4 * Real.pi) 0 := by
    convert! (hasDerivAt_id (0 : ℂ)).const_mul (4 * (Real.pi : ℂ)) using 1 <;>
      simp only [conicRelation, zero_mul, add_zero, sub_zero, mul_one]
    funext e
    dsimp
    ring
  have hn : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)
  apply parametric_holo_implicit hf (by simp [conicRelation])
  rw [partial_apply_one hf.differentiableAt hd]
  exact hn

def smallCoordinate (E : ℂ × ℂ → ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  p.1.2 * exp (-p.2 + E (p.1.1, p.2))

def fiberEquation (E : ℂ × ℂ → ℂ) (a d : ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  2 * smallCoordinate E p /
      (1 - 2 * a * smallCoordinate E p + smallCoordinate E p ^ 2) -
    (cos p.2 - a)⁻¹ - d

theorem smallCoordinate_corner (E : ℂ × ℂ → ℂ) (t u : ℂ) :
    smallCoordinate E ((t, 0), u) = 0 := by simp [smallCoordinate]

theorem fiberEquation_corner (E : ℂ × ℂ → ℂ) (a d t u : ℂ) :
    fiberEquation E a d ((t, 0), u) = -(cos u - a)⁻¹ - d := by
  simp [fiberEquation, smallCoordinate_corner]

theorem smallCoordinate_analyticAt {E : ℂ × ℂ → ℂ} {u₀ : ℂ}
    (hE : AnalyticAt ℂ E (0, u₀)) :
    AnalyticAt ℂ (smallCoordinate E) ((0, 0), u₀) := by
  have hp : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ (p.1.1, p.2)) ((0, 0), u₀) := by
    exact (analyticAt_fst.comp (f := Prod.fst) analyticAt_fst).prod analyticAt_snd
  have he := hE.comp (f := fun p : (ℂ × ℂ) × ℂ ↦ (p.1.1, p.2)) hp
  have hx : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ -p.2 + E (p.1.1, p.2))
      ((0, 0), u₀) := by
    exact analyticAt_snd.neg.add he
  exact (analyticAt_snd.comp (f := Prod.fst) analyticAt_fst).mul
    ((Complex.differentiable_exp.analyticAt _).comp hx)

theorem fiberEquation_analyticAt {E : ℂ × ℂ → ℂ} {a d u₀ : ℂ}
    (hE : AnalyticAt ℂ E (0, u₀)) (ha : cos u₀ ≠ a) :
    AnalyticAt ℂ (fiberEquation E a d) ((0, 0), u₀) := by
  have hz := smallCoordinate_analyticAt hE
  have hp : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ ↦ cos p.2 - a) ((0, 0), u₀) := by
    exact ((Complex.differentiable_cos.analyticAt _).comp
      (f := fun p : (ℂ × ℂ) × ℂ ↦ p.2) analyticAt_snd).sub analyticAt_const
  exact ((analyticAt_const.mul hz).div
    ((analyticAt_const.sub (analyticAt_const.mul hz)).add (hz.pow 2))
    (by simp [smallCoordinate_corner])).sub (hp.inv (sub_ne_zero.mpr ha)) |>.sub analyticAt_const

theorem fiberEquation_partial (E : ℂ × ℂ → ℂ) (a d u₀ : ℂ) (ha : cos u₀ ≠ a) :
    HasDerivAt (fun u : ℂ ↦ fiberEquation E a d ((0, 0), u))
      (-sin u₀ / (cos u₀ - a) ^ 2) u₀ := by
  simp_rw [fiberEquation_corner]
  convert! (((Complex.hasDerivAt_cos u₀).sub_const a).inv (sub_ne_zero.mpr ha)).neg.sub_const d using 1
  ring

theorem exists_corner_branch (a c d u₀ : ℂ)
    (ha : cos u₀ ≠ a) (hs : sin u₀ ≠ 0) (hd : -(cos u₀ - a)⁻¹ = d) :
    ∃ E u : ℂ × ℂ → ℂ,
      AnalyticAt ℂ E (0, u₀) ∧ E (0, u₀) = 0 ∧
      (∀ᶠ p in 𝓝 (0, u₀), conicRelation c (p, E p) = 0) ∧
      AnalyticAt ℂ u (0, 0) ∧ u (0, 0) = u₀ ∧
      ∀ᶠ p in 𝓝 (0, 0), fiberEquation E a d (p, u p) = 0 := by
  obtain ⟨E, hE, hE0, hrel⟩ := exists_conic_correction c u₀
  have hf := fiberEquation_analyticAt (d := d) hE ha
  have hroot : fiberEquation E a d ((0, 0), u₀) = 0 := by
    rw [fiberEquation_corner, hd, sub_self]
  have hpartial := fiberEquation_partial E a d u₀ ha
  have hn : -sin u₀ / (cos u₀ - a) ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hs) (pow_ne_zero 2 (sub_ne_zero.mpr ha))
  obtain ⟨u, hu, hu0, huf⟩ := parametric_holo_implicit hf hroot
    (by rw [partial_apply_one hf.differentiableAt hpartial]; exact hn)
  exact ⟨E, u, hE, hE0, hrel, hu, hu0, huf⟩

end

end GaloisForLFunctions.HTGeometry.CosineCornerUnfolding
