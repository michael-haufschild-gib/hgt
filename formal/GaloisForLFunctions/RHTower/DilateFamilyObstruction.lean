import GaloisForLFunctions.RHTower.MuentzZetaRelationImpossible
import GaloisForLFunctions.RHTower.FractDilateBalance

/-!
# The dilate family is obstructed too

`BorderDeterminantVanishing.infDist_pos_of_linearIndependent_pairings` states the obstruction for an
arbitrary family in the carrier: independence of the detector pairings puts the target at positive distance
from the span.  This file uses it on a second family, the unbalanced dilates

`fractDilate θ : u ↦ {θu}/u`,

whose pairings `FractDilateBalance.inner_bdDetector_fractDilate` gives as
`θ^s·(−ζ(s)/s) − θ/(1−s)`.

* `dilateRowFun` — those pairings, with the target pairing `1/s`, as functions on the strip;
* **`linearIndependent_dilateRowFun`** — they are linearly independent for *any* distinct positive dilations;
  the bound `θ ≤ 1` is needed only by the pairing identity, not by the independence argument.
  Multiplying a relation by `s(1−s)` gives a function analytic on the convex half-plane `Re s < 1`; the two
  trivial zeros `ζ(−2) = ζ(−4) = 0` leave a `2×2` system in the constant and the dilate mass which forces
  both to vanish, after which `ζ(3/4) ≠ 0` kills the exponential sum and Dedekind's characters kill the
  coefficients;
* **`infDist_pos_fractDilate`** — hence `1/u` is at positive distance from the span of any finite family of
  distinct dilates in `(0,1]`, the value `θ = 1` included: `fractDilate 1 = {u}/u` is not the zero vector, and
  the character argument needs no exclusion once the constant has been shown to vanish.

Two trivial zeros are needed here where the Báez-Duarte generators needed one: the extra term `θ/(1−s)`
contributes an unknown that a single evaluation cannot separate from the constant.  That is the precise
formal cost of dropping Báez-Duarte's normalisation.
-/

open Complex Set Filter Topology

noncomputable section

namespace RHTower

/-- The sampled pairings of the dilate family, bordered by the target pairing. -/
def dilateRowFun {N : ℕ} (θ : Fin N → ℝ) : Fin (N + 1) → (StripPoint → ℂ) :=
  (Fin.snoc
    (fun (i : Fin N) (s : StripPoint) =>
      ((θ i : ℝ) : ℂ) ^ (s : ℂ) * (-(riemannZeta (s : ℂ) / (s : ℂ)))
        - ((θ i : ℝ) : ℂ) * (1 / (1 - (s : ℂ))))
    (fun (s : StripPoint) => 1 / (s : ℂ)) : Fin (N + 1) → (StripPoint → ℂ))

theorem dilateRowFun_castSucc {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) (s : StripPoint) :
    dilateRowFun θ i.castSucc s
      = ((θ i : ℝ) : ℂ) ^ (s : ℂ) * (-(riemannZeta (s : ℂ) / (s : ℂ)))
        - ((θ i : ℝ) : ℂ) * (1 / (1 - (s : ℂ))) := by
  simp [dilateRowFun]

theorem dilateRowFun_last {N : ℕ} (θ : Fin N → ℝ) (s : StripPoint) :
    dilateRowFun θ (Fin.last N) s = 1 / (s : ℂ) := by
  simp [dilateRowFun]

/-- **The dilate pairings are independent.**  For distinct dilations in `(0,1)` no nontrivial combination of
the dilate pairings equals a multiple of the target pairing on the strip. -/
theorem linearIndependent_dilateRowFun {N : ℕ} (θ : Fin N → ℝ)
    (hθ0 : ∀ i, 0 < θ i) (hinj : Function.Injective θ) :
    LinearIndependent ℂ (dilateRowFun θ) := by
  classical
  by_contra hdep
  obtain ⟨c, hrel, ⟨i₀, hi₀⟩⟩ := Fintype.not_linearIndependent_iff.1 hdep
  set b : Fin N → ℂ := fun i => c i.castSucc with hb
  set K : ℂ := ∑ i : Fin N, b i * ((θ i : ℝ) : ℂ) with hK
  set P : ℂ → ℂ := fun s => muentzSum θ b s with hP
  have hPdiff : Differentiable ℂ P := differentiable_muentzSum θ b
  -- the relation, evaluated on the strip
  have hval : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, b i * (((θ i : ℝ) : ℂ) ^ s * (-(riemannZeta s / s))
          - ((θ i : ℝ) : ℂ) * (1 / (1 - s))))
        + c (Fin.last N) * (1 / s) = 0 := by
    intro s hs hs1
    have h0 := congrFun hrel ⟨s, hs, hs1⟩
    rw [Fin.sum_univ_castSucc] at h0
    simpa [Pi.add_apply, Finset.sum_apply, dilateRowFun_castSucc, dilateRowFun_last] using h0
  -- cleared of denominators it is analytic on the half-plane
  set H : ℂ → ℂ := fun s =>
    -(P s * riemannZeta s * (1 - s)) - s * K + c (Fin.last N) * (1 - s) with hH
  set U : Set ℂ := {s : ℂ | s.re < 1} with hU
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUconv : Convex ℝ U := convex_halfSpace_re_lt 1
  have hHan : AnalyticOnNhd ℂ H U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    have hs1 : s ≠ 1 := by
      intro h
      rw [hU, Set.mem_setOf_eq, h, Complex.one_re] at hs
      norm_num at hs
    rw [hH]
    have hz := differentiableAt_riemannZeta hs1
    have hp := hPdiff s
    have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
      (differentiableAt_const 1).sub differentiableAt_id
    exact ((((hp.mul hz).mul hlin).neg.sub (differentiableAt_id.mul_const K)).add
      (hlin.const_mul (c (Fin.last N)))).differentiableWithinAt
  have hHzero : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → H s = 0 := by
    intro s hs hs1
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hs
      norm_num at hs
    have hone : (1 : ℂ) - s ≠ 0 := by
      intro h
      have : s = 1 := by linear_combination -h
      rw [this, Complex.one_re] at hs1
      norm_num at hs1
    have h := hval s hs hs1
    have hsplit : (∑ i : Fin N, b i * (((θ i : ℝ) : ℂ) ^ s * (-(riemannZeta s / s))
          - ((θ i : ℝ) : ℂ) * (1 / (1 - s))))
        = (∑ i : Fin N, b i * ((θ i : ℝ) : ℂ) ^ s) * (-(riemannZeta s / s))
          - (∑ i : Fin N, b i * ((θ i : ℝ) : ℂ)) * (1 / (1 - s)) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, ← muentzSum_eq_cpow θ hθ0 b s, ← hK] at h
    have hPs : muentzSum θ b s = P s := rfl
    rw [hPs] at h
    have hmul : H s = (P s * (-(riemannZeta s / s)) - K * (1 / (1 - s))
        + c (Fin.last N) * (1 / s)) * (s * (1 - s)) := by
      rw [hH]
      field_simp
    rw [hmul, h, zero_mul]
  -- the relation propagates to the whole half-plane
  set w₀ : ℂ := ((3 / 4 : ℝ) : ℂ) with hw₀
  have hw₀re : w₀.re = 3 / 4 := Complex.ofReal_re _
  have hw₀U : w₀ ∈ U := by
    rw [hU, Set.mem_setOf_eq, hw₀re]
    norm_num
  have hevlo : ∀ᶠ s in 𝓝 w₀, 1 / 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      (by show (1 : ℝ) / 2 < w₀.re; rw [hw₀re]; norm_num)
  have hevhi : ∀ᶠ s in 𝓝 w₀, s.re < 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).eventually_mem
      (by show w₀.re < (1 : ℝ); rw [hw₀re]; norm_num)
  have hHev : H =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hevlo, hevhi] with s h2 h3
    exact hHzero s h2 h3
  have hall : Set.EqOn H 0 U :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected hw₀U hHev
  -- the two trivial zeros pin the constant and the dilate mass
  have hz2 : riemannZeta (-2 : ℂ) = 0 := by
    have := riemannZeta_neg_two_mul_nat_add_one 0
    norm_num at this
    exact this
  have hz4 : riemannZeta (-4 : ℂ) = 0 := by
    have := riemannZeta_neg_two_mul_nat_add_one 1
    norm_num at this
    exact this
  have hmem2 : ((-2 : ℂ)) ∈ U := by rw [hU, Set.mem_setOf_eq]; norm_num
  have hmem4 : ((-4 : ℂ)) ∈ U := by rw [hU, Set.mem_setOf_eq]; norm_num
  have heq2 : 2 * K + 3 * c (Fin.last N) = 0 := by
    have h := hall hmem2
    rw [hH] at h
    simp only [hz2, mul_zero, zero_mul, neg_zero, Pi.zero_apply] at h
    linear_combination h
  have heq4 : 4 * K + 5 * c (Fin.last N) = 0 := by
    have h := hall hmem4
    rw [hH] at h
    simp only [hz4, mul_zero, zero_mul, neg_zero, Pi.zero_apply] at h
    linear_combination h
  have hlast : c (Fin.last N) = 0 := by linear_combination 2 * heq2 - heq4
  have hKzero : K = 0 := by linear_combination (heq2 - 3 * hlast) / 2
  -- so the exponential sum vanishes near 3/4, hence everywhere
  have hz₀ : riemannZeta w₀ ≠ 0 :=
    riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num)
  have hne1 : w₀ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw₀re
    norm_num at hw₀re
  have hevz : ∀ᶠ s in 𝓝 w₀, riemannZeta s ≠ 0 :=
    ((differentiableAt_riemannZeta hne1).continuousAt).eventually_ne hz₀
  have hPzero : P =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hevz, hevhi] with s hzs hUs
    have hmem : s ∈ U := by rw [hU, Set.mem_setOf_eq]; exact hUs
    have h0 := hall hmem
    rw [hH, hlast, hKzero] at h0
    simp only [mul_zero, zero_mul, sub_zero, add_zero, Pi.zero_apply, neg_eq_zero] at h0
    have hone : (1 : ℂ) - s ≠ 0 := by
      intro h
      have : s = 1 := by linear_combination -h
      rw [this, Complex.one_re] at hUs
      norm_num at hUs
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hone)).resolve_right hzs
  have hPan : AnalyticOnNhd ℂ P Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hPdiff
  have hPall : Set.EqOn P 0 Set.univ :=
    hPan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w₀) hPzero
  have hsum : ∀ s : ℂ, ∑ i : Fin N, b i * ((θ i : ℝ) : ℂ) ^ s = 0 := by
    intro s
    have h0 : P s = 0 := hPall (Set.mem_univ s)
    rw [← muentzSum_eq_cpow θ hθ0 b s]
    exact h0
  have hbz := eq_zero_of_forall_sum_cpow_eq_zero θ hθ0 hinj b hsum
  refine hi₀ ?_
  refine Fin.lastCases ?_ ?_ i₀
  · exact hlast
  · intro i
    exact hbz i

/-- **The dilate family is obstructed.**  The Nyman--Beurling target is at positive distance from the span of
any finite family of distinct dilates `{u ↦ {θu}/u}` with `θ ∈ (0,1)` — unconditionally. -/
theorem infDist_pos_fractDilate {N : ℕ} (θ : Fin N → ℝ)
    (hθ0 : ∀ i, 0 < θ i) (hθ1 : ∀ i, θ i ≤ 1) (hinj : Function.Injective θ) :
    0 < Metric.infDist bdTarget
      (Submodule.span ℂ (Set.range fun i : Fin N => fractDilate (θ i)) : Set BDCarrier) :=
  infDist_pos_of_linearIndependent_pairings (fun i => fractDilate (θ i)) bdTarget (dilateRowFun θ)
    (fun i s => by
      rw [dilateRowFun_castSucc,
        inner_bdDetector_fractDilate s.2.1 s.2.2 (hθ0 i) (hθ1 i)])
    (fun s => by rw [dilateRowFun_last, inner_bdDetector_bdTarget s.2.1])
    (linearIndependent_dilateRowFun θ hθ0 hinj)

end RHTower

end
