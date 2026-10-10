import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! Surjectivity of finite quadratic maps is stable near a balanced diagonal
whose coefficient vectors span the target. This supplies the local analytic
step for exact realization by separated actual Gram packets. -/

open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

variable {J C : Type} [Fintype J]

def finiteWeilQuadraticMap (K : J → J → C → ℝ) (t : J → ℝ) : C → ℝ :=
  ∑ i, ∑ j, (t i * t j) • K i j

def finiteWeilQuadraticDiagonal (v : J → C → ℝ) : J → J → C → ℝ :=
  fun i j => if i = j then v i else 0

theorem finiteWeilQuadraticMap_diagonal (v : J → C → ℝ) (t : J → ℝ) :
    finiteWeilQuadraticMap (finiteWeilQuadraticDiagonal v) t =
      ∑ i, (t i * t i) • v i := by
  simp [finiteWeilQuadraticMap, finiteWeilQuadraticDiagonal]

theorem finiteWeilQuadraticMap_smul (K : J → J → C → ℝ) (r : ℝ) (t : J → ℝ) :
    finiteWeilQuadraticMap K (r • t) = r ^ 2 • finiteWeilQuadraticMap K t := by
  simp only [finiteWeilQuadraticMap, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

variable [Fintype C]

private theorem quadratic_surjective_of_range_nhds (K : J → J → C → ℝ)
    (h : Set.range (finiteWeilQuadraticMap K) ∈ 𝓝 (0 : C → ℝ)) :
    Function.Surjective (finiteWeilQuadraticMap K) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  intro y
  let c : ℝ := ε / (‖y‖ + 1)
  have hd : 0 < ‖y‖ + 1 := by positivity
  have hc : 0 < c := div_pos hε hd
  have hce : c * (‖y‖ + 1) = ε := div_mul_cancel₀ ε hd.ne'
  have hsmall : c • y ∈ Metric.ball (0 : C → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith
  obtain ⟨t, ht⟩ := hball hsmall
  refine ⟨(Real.sqrt c)⁻¹ • t, ?_⟩
  rw [finiteWeilQuadraticMap_smul, inv_pow, Real.sq_sqrt hc.le, ht, smul_smul,
    inv_mul_cancel₀ hc.ne', one_smul]

/-- One bounded amplitude ball covers a target neighborhood uniformly over nearby kernels. -/
theorem exists_eventually_bounded_finiteWeilQuadraticMap_diagonal (v : J → C → ℝ)
    (hz : ∑ i, v i = 0)
    (hspan : Function.Surjective (fun t : J → ℝ => ∑ i, t i • v i)) :
    ∃ M ε : ℝ, 0 < M ∧ 0 < ε ∧
      ∀ᶠ K in 𝓝 (finiteWeilQuadraticDiagonal v),
        ∀ y : C → ℝ, ‖y‖ < ε →
          ∃ t : J → ℝ, finiteWeilQuadraticMap K t = y ∧ ‖t‖ < M := by
  let P := J → J → C → ℝ
  let V := J → ℝ
  let E := C → ℝ
  let K₀ : P := finiteWeilQuadraticDiagonal v
  let f : P × V → E := fun p => finiteWeilQuadraticMap p.1 p.2
  have hcont : ContDiff ℝ 1 f := by
    dsimp [f, finiteWeilQuadraticMap]
    fun_prop
  let A : P × V →L[ℝ] E := fderiv ℝ f (K₀, 1)
  have hf : HasStrictFDerivAt f A (K₀, 1) :=
    hcont.contDiffAt.hasStrictFDerivAt one_ne_zero
  let B : V →L[ℝ] E := ∑ i : J,
    ((ContinuousLinearMap.proj i : V →L[ℝ] ℝ) + ContinuousLinearMap.proj i).smulRight (v i)
  have hB (t : V) : B t = ∑ i, (t i + t i) • v i := by
    simp only [B, _root_.sum_apply]
    rfl
  have hBsurj : Function.Surjective B := by
    intro y
    obtain ⟨t, ht⟩ := hspan y
    refine ⟨fun i => t i / 2, ?_⟩
    rw [hB]
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have hdiag : HasStrictFDerivAt (fun t : V => f (K₀, t)) B 1 := by
    have hi (i : J) : HasStrictFDerivAt (fun t : V => (t i * t i) • v i)
        (((ContinuousLinearMap.proj i : V →L[ℝ] ℝ) +
          ContinuousLinearMap.proj i).smulRight (v i)) 1 := by
      have hp := (ContinuousLinearMap.proj i : V →L[ℝ] ℝ).hasStrictFDerivAt (x := 1)
      simpa using (hp.mul hp).smul_const (v i)
    simpa only [f, K₀, finiteWeilQuadraticMap_diagonal] using
      (HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i))
  let e : V →L[ℝ] P × V := (0 : V →L[ℝ] P).prod (ContinuousLinearMap.id ℝ V)
  have he : HasStrictFDerivAt (fun t : V => (K₀, t)) e 1 :=
    (hasStrictFDerivAt_const K₀ (1 : V)).prodMk (hasStrictFDerivAt_id 1)
  have heq : A.comp e = B := (hf.comp 1 he).hasFDerivAt.unique hdiag.hasFDerivAt
  have hA (t : V) : A (0, t) = B t := by
    have h := congrArg (fun L : V →L[ℝ] E => L t) heq
    simpa [e] using h
  let H : P × V → P × E := fun p => (p.1, f p)
  have hH : HasStrictFDerivAt H ((ContinuousLinearMap.fst ℝ P V).prod A) (K₀, 1) :=
    hasStrictFDerivAt_fst.prodMk hf
  have hHsurj : Function.Surjective ((ContinuousLinearMap.fst ℝ P V).prod A) := by
    rintro ⟨p, y⟩
    obtain ⟨t, ht⟩ := hBsurj (y - A (p, 0))
    refine ⟨(p, t), ?_⟩
    change (p, A (p, t)) = (p, y)
    congr 1
    have hsplit : A (p, t) = A (p, 0) + A (0, t) := by
      rw [← map_add]
      change A (p, t) = A (p + 0, 0 + t)
      rw [add_zero, zero_add]
    rw [hsplit, hA, ht]
    abel
  have hzero : H (K₀, 1) = (K₀, 0) := by
    change (K₀, finiteWeilQuadraticMap (finiteWeilQuadraticDiagonal v) (1 : V)) = (K₀, 0)
    congr 1
    rw [finiteWeilQuadraticMap_diagonal]
    change (∑ i, ((1 : ℝ) * 1) • v i) = 0
    simpa only [one_mul, one_smul] using hz
  let M : ℝ := ‖(1 : V)‖ + 1
  let S : Set (P × V) := {p | ‖p.2‖ < M}
  have hM : 0 < M := by dsimp [M]; positivity
  have hS : S ∈ 𝓝 (K₀, (1 : V)) := by
    apply (isOpen_lt continuous_snd.norm continuous_const).mem_nhds
    change ‖(1 : V)‖ < ‖(1 : V)‖ + 1
    linarith
  have hrange : H '' S ∈ 𝓝 (K₀, (0 : E)) := by
    rw [← hzero, ← hH.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hHsurj)]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hS fun p hp => ⟨p, hp, rfl⟩)
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp hrange
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨M, ε, hM, hε, ?_⟩
  filter_upwards [hU] with K hK
  intro y hy
  have hyW : y ∈ W := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  obtain ⟨⟨K', t⟩, ht, he⟩ := hUW (show (K, y) ∈ U ×ˢ W from ⟨hK, hyW⟩)
  have hp : K' = K := congrArg Prod.fst he
  subst K'
  exact ⟨t, congrArg Prod.snd he, ht⟩

/-- A positive balance supplies the zero-sum premise; actual dictionary
representation supplies the spanning premise. -/
theorem eventually_surjective_finiteWeilQuadraticMap_diagonal (v : J → C → ℝ)
    (hz : ∑ i, v i = 0)
    (hspan : Function.Surjective (fun t : J → ℝ => ∑ i, t i • v i)) :
    ∀ᶠ K in 𝓝 (finiteWeilQuadraticDiagonal v),
      Function.Surjective (finiteWeilQuadraticMap K) := by
  obtain ⟨M, ε, _, hε, hK⟩ := exists_eventually_bounded_finiteWeilQuadraticMap_diagonal v hz hspan
  filter_upwards [hK] with K hK
  apply quadratic_surjective_of_range_nhds K
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hε, ?_⟩
  intro y hy
  obtain ⟨t, ht, _⟩ := hK y (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  exact ⟨t, ht⟩

end RHTower
