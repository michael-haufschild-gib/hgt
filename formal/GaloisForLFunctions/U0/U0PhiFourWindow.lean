/-
# The circle window EXISTS: an explicit Böttcher branch for `b = 4` on a disk containing the circle

The circle-window reduction (`U0PhiCircleWindow`) left one analytic input: a window continuation
`(Ω, φ)` of the Böttcher coordinate touching the unit circle.  This file CONSTRUCTS it for the
disconnected parameter `b = 4`.

The mechanism: for `‖z‖ < 21/20`, one quadratic step lands in a uniform far field —
`‖z² + 4‖ ≥ 4 − (21/20)² = 1159/400 > 289/100` — and the region `{‖w‖ > 289/100}` is forward
invariant (`(289/100)² − 4 > 289/100`) with `‖4/w²‖ ≤ 40000/83521 < 1/2`, so the Böttcher
log-series `bottcherLog 4` converges geometrically and is analytic there (the in-tree escape
regime `‖c‖ ≤ ‖z‖` is NOT needed at this parameter: the orbit bound is self-improving).  Hence

  `phiFour z := exp(½ · bottcherLog 4 (z² + 4))`

is analytic on the open disk `Ω := ball 0 (21/20)` — which CONTAINS the whole unit circle — and is
canonically a Böttcher branch: `phiFour z ^ 2 = bottcherCoord 4 (z² + 4)` definitionally
(`phiFour_sq`).  Feeding `Ω, phiFour, z₁ = 1` to the windowed engine yields
`u0_phiFour_no_relation`: u₀ admits no positive-degree polynomial relation over `ℂ(z)` with this
Böttcher branch — with NO window hypothesis left.  The `u₀ ⟂ φ_b` content is therefore now
unconditional at `b = 4` up to (i) the min-poly separability normalization of a given relation and
(ii) the `u₀`-degree-0 residue (φ-transcendence over `ℂ(z)`, the φ-side card).
-/
import GaloisForLFunctions.U0.U0PhiCircleWindow
import GaloisForLFunctions.Bottcher.BottcherCoord

open Complex Filter Topology Metric Set Polynomial Bottcher
open U0 U0NaturalBoundary U0Transcendence U0PhiCard

namespace U0PhiFourWindow

/-- The `b = 4` window far field `{‖w‖ > 289/100}`: reached from the disk `‖z‖ < 21/20` in one
quadratic step, forward invariant, and inside the geometric-convergence regime of the Böttcher
log-series. -/
def farW : Set ℂ := {w : ℂ | (289 / 100 : ℝ) < ‖w‖}

theorem isOpen_farW : IsOpen farW := isOpen_lt continuous_const continuous_norm

/-- One quadratic step grows the norm on `farW`: `‖w² + 4‖ ≥ ‖w‖² − 4 > 289/100`. -/
theorem farW_invariant {w : ℂ} (hw : w ∈ farW) : quadratic 4 w ∈ farW := by
  have h1 : (289 / 100 : ℝ) < ‖w‖ := hw
  show (289 / 100 : ℝ) < ‖w ^ 2 + 4‖
  have htri : ‖w ^ 2‖ ≤ ‖w ^ 2 + 4‖ + ‖(-4 : ℂ)‖ := by
    calc ‖w ^ 2‖ = ‖w ^ 2 + 4 + (-4)‖ := by ring_nf
      _ ≤ ‖w ^ 2 + 4‖ + ‖(-4 : ℂ)‖ := norm_add_le _ _
  have h4 : ‖(-4 : ℂ)‖ = 4 := by
    rw [norm_neg]; exact Complex.norm_ofNat 4
  have hp : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
  nlinarith [h1, htri]

theorem farW_iterate (k : ℕ) {w : ℂ} (hw : w ∈ farW) : (quadratic 4)^[k] w ∈ farW := by
  induction k with
  | zero => simpa using hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact farW_invariant ih

theorem farW_ne_zero {w : ℂ} (hw : w ∈ farW) : w ≠ 0 := by
  intro h
  have : (289 / 100 : ℝ) < ‖w‖ := hw
  rw [h] at this
  simp at this
  linarith

/-- The series ratio is uniformly small on `farW`: `‖4/w²‖ ≤ 1/2`. -/
theorem farW_ratio_le {w : ℂ} (hw : w ∈ farW) : ‖(4 : ℂ) / w ^ 2‖ ≤ 1 / 2 := by
  have h1 : (289 / 100 : ℝ) < ‖w‖ := hw
  rw [norm_div, norm_pow, Complex.norm_ofNat]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- **Geometric term bound on the window far field.** `‖bottcherLogTerm 4 w k‖ ≤ (1/2)^(k+1)` —
no escape-regime hypothesis: the far field `farW` is self-improving. -/
theorem norm_term_le {w : ℂ} (hw : w ∈ farW) (k : ℕ) :
    ‖bottcherLogTerm 4 w k‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have hA : (quadratic 4)^[k] w ∈ farW := farW_iterate k hw
  have hq : ‖(4 : ℂ) / ((quadratic 4)^[k] w) ^ 2‖ ≤ 1 / 2 := farW_ratio_le hA
  have hlog := norm_clog_one_add_le hq
  unfold bottcherLogTerm
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc ((2 : ℝ) ^ (k + 1))⁻¹ * ‖Complex.log (1 + 4 / ((quadratic 4)^[k] w) ^ 2)‖
      ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * (2 * (1 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖Complex.log (1 + 4 / ((quadratic 4)^[k] w) ^ 2)‖
            ≤ 2 * ‖(4 : ℂ) / ((quadratic 4)^[k] w) ^ 2‖ := hlog
          _ ≤ 2 * (1 / 2) := by linarith
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
        rw [one_div, inv_pow]
        norm_num

/-- The Böttcher log-series tail is differentiable on the window far field (Weierstrass M-test
with the geometric bound). -/
theorem tail_differentiableOn :
    DifferentiableOn ℂ (fun w => ∑' k, bottcherLogTerm 4 w k) farW := by
  have hqd : Differentiable ℂ (quadratic (4 : ℂ)) := by
    have : (quadratic (4 : ℂ)) = fun z => z ^ 2 + 4 := by
      funext z; exact quadratic_apply 4 z
    rw [this]
    exact (differentiable_pow 2).add_const 4
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k => (1 / 2 : ℝ) ^ (k + 1)) ?_ ?_ isOpen_farW ?_
  · have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 / 2)) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    refine hgeom.congr fun k => ?_
    rw [← pow_succ]
  · intro k w hw
    apply DifferentiableAt.differentiableWithinAt
    have hA : (quadratic 4)^[k] w ∈ farW := farW_iterate k hw
    have hAne : ((quadratic 4)^[k] w) ^ 2 ≠ 0 := pow_ne_zero 2 (farW_ne_zero hA)
    have hiter : DifferentiableAt ℂ ((quadratic (4 : ℂ))^[k]) w := (hqd.iterate k).differentiableAt
    have hinner : DifferentiableAt ℂ (fun v => 1 + (4 : ℂ) / ((quadratic 4)^[k] v) ^ 2) w := by
      have hdiv : DifferentiableAt ℂ (fun v => (4 : ℂ) / ((quadratic 4)^[k] v) ^ 2) w :=
        (differentiableAt_const _).div (hiter.pow 2) hAne
      exact (differentiableAt_const (1 : ℂ)).add hdiv
    have hslit : (1 + (4 : ℂ) / ((quadratic 4)^[k] w) ^ 2) ∈ slitPlane := by
      refine Or.inl ?_
      have hre : |((4 : ℂ) / ((quadratic 4)^[k] w) ^ 2).re|
          ≤ ‖(4 : ℂ) / ((quadratic 4)^[k] w) ^ 2‖ := Complex.abs_re_le_norm _
      have hq := farW_ratio_le hA
      have : (1 + (4 : ℂ) / ((quadratic 4)^[k] w) ^ 2).re
          = 1 + ((4 : ℂ) / ((quadratic 4)^[k] w) ^ 2).re := by
        simp [Complex.add_re]
      rw [this]
      have habs := abs_le.mp hre
      linarith [habs.1]
    exact (hinner.clog hslit).const_mul _
  · intro k w hw
    exact norm_term_le hw k

/-- **The explicit `b = 4` window branch**: `phiFour z = exp(½ · bottcherLog 4 (z² + 4))`. -/
noncomputable def phiFour (z : ℂ) : ℂ :=
  Complex.exp ((2 : ℂ)⁻¹ * bottcherLog 4 (quadratic 4 z))

/-- `phiFour` is a canonical Böttcher branch: its square is the genuine `bottcherCoord 4` one
quadratic step ahead. -/
theorem phiFour_sq (z : ℂ) : phiFour z ^ 2 = bottcherCoord 4 (quadratic 4 z) := by
  unfold phiFour bottcherCoord
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem phiFour_ne_zero (z : ℂ) : phiFour z ≠ 0 := Complex.exp_ne_zero _

/-- The window disk `Ω = ball 0 (21/20)` — an open set CONTAINING the whole unit circle. -/
theorem quadFour_re_lower {z : ℂ} (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    (1159 / 400 : ℝ) < (quadratic 4 z).re := by
  have hz' : ‖z‖ < 21 / 20 := by simpa [mem_ball, dist_zero_right] using hz
  have hre : |(z ^ 2).re| ≤ ‖z ^ 2‖ := Complex.abs_re_le_norm _
  have hp : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have h1 : (quadratic 4 z).re = (z ^ 2).re + 4 := by
    show (z ^ 2 + 4 : ℂ).re = (z ^ 2).re + 4
    simp [Complex.add_re]
  rw [h1]
  have habs := abs_le.mp hre
  nlinarith [habs.1, hz', norm_nonneg z]

theorem quadFour_mem_farW {z : ℂ} (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    quadratic 4 z ∈ farW := by
  have hre := quadFour_re_lower hz
  have hle : (quadratic 4 z).re ≤ ‖quadratic 4 z‖ := Complex.re_le_norm _
  show (289 / 100 : ℝ) < ‖quadratic 4 z‖
  linarith

theorem quadFour_mem_slitPlane {z : ℂ} (hz : z ∈ ball (0 : ℂ) (21 / 20)) :
    quadratic 4 z ∈ slitPlane := by
  refine Or.inl ?_
  have := quadFour_re_lower hz
  linarith

/-- **`phiFour` is analytic on the whole disk `ball 0 (21/20)` — across the unit circle.** -/
theorem phiFour_analytic : AnalyticOnNhd ℂ phiFour (ball (0 : ℂ) (21 / 20)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hqd : DifferentiableAt ℂ (quadratic (4 : ℂ)) z := by
    have : (quadratic (4 : ℂ)) = fun v => v ^ 2 + 4 := by
      funext v; exact quadratic_apply 4 v
    rw [this]
    exact ((differentiable_pow 2).add_const 4).differentiableAt
  have hlog : DifferentiableAt ℂ (fun v => Complex.log (quadratic 4 v)) z :=
    hqd.clog (quadFour_mem_slitPlane hz)
  have htail : DifferentiableAt ℂ (fun v => ∑' k, bottcherLogTerm 4 (quadratic 4 v) k) z := by
    have hT : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm 4 w k) (quadratic 4 z) :=
      tail_differentiableOn.differentiableAt (isOpen_farW.mem_nhds (quadFour_mem_farW hz))
    exact hT.comp z hqd
  have hsum : DifferentiableAt ℂ (fun v => bottcherLog 4 (quadratic 4 v)) z := by
    have : (fun v => bottcherLog 4 (quadratic 4 v))
        = fun v => Complex.log (quadratic 4 v)
            + ∑' k, bottcherLogTerm 4 (quadratic 4 v) k := by
      funext v; rfl
    rw [this]
    exact hlog.add htail
  exact (hsum.const_mul _).cexp

/-- The window annulus `ball 0 (21/20) ∩ Ext = {1 < ‖z‖ < 21/20}` is preconnected (polar image of
`Ioo (1, 21/20) × 𝕊¹`). -/
theorem isPreconnected_annulus : IsPreconnected (ball (0 : ℂ) (21 / 20) ∩ Ext) := by
  have hprod : IsConnected ((Ioo (1 : ℝ) (21 / 20)) ×ˢ Metric.sphere (0 : ℂ) 1) := by
    refine IsConnected.prod ⟨⟨41 / 40, by norm_num, by norm_num⟩, isPreconnected_Ioo⟩ ?_
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num) 0 (by norm_num)
  have hcont : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) := by fun_prop
  have himg := hprod.image _ hcont.continuousOn
  have hset : ball (0 : ℂ) (21 / 20) ∩ Ext
      = (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) '' ((Ioo (1 : ℝ) (21 / 20)) ×ˢ Metric.sphere (0 : ℂ) 1) := by
    ext z
    simp only [Ext, Set.mem_inter_iff, mem_ball, dist_zero_right, mem_setOf_eq, Set.mem_image,
      Set.mem_prod, mem_Ioo, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨hlt, hgt⟩
      have hz0 : ‖z‖ ≠ 0 := by positivity
      refine ⟨⟨‖z‖, (‖z‖⁻¹ : ℝ) • z⟩, ⟨⟨hgt, hlt⟩, ?_⟩, ?_⟩
      · show ‖(‖z‖⁻¹ : ℝ) • z‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_cancel₀ hz0]
      · show (↑‖z‖ : ℂ) • ((‖z‖⁻¹ : ℝ) • z) = z
        rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hz0, Complex.ofReal_one, one_mul]
    · rintro ⟨⟨r, w⟩, ⟨⟨hr1, hr2⟩, hw⟩, rfl⟩
      have hnorm : ‖(↑r : ℂ) • w‖ = r := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one,
          abs_of_pos (by linarith)]
      constructor
      · rw [hnorm]; exact hr2
      · show 1 < ‖(↑r : ℂ) • w‖
        rw [hnorm]; exact hr1
  rw [hset]
  exact himg.isPreconnected

/-- **u₀ ⟂ the `b = 4` Böttcher branch — UNCONDITIONAL window instance.** No polynomial relation
`P(z, phiFour z, u₀ z) = 0` of positive `u₀`-degree (with separable specialization at some point
of the disk) can hold on any nonempty open subset of the annulus `{1 < ‖z‖ < 21/20}`.  The window
object is CONSTRUCTED — no continuation hypothesis remains. -/
theorem u0_phiFour_no_relation
    (P : (Polynomial (Polynomial ℂ))[X]) (hd : 1 ≤ P.natDegree)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) (21 / 20))
    (hleadw : (∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (phiFour w)) * X ^ (i : ℕ) : ℂ[X]).coeff
        P.natDegree ≠ 0)
    (hsepw : (∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (phiFour w)) * X ^ (i : ℕ) : ℂ[X]).Separable)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVD : V ⊆ ball (0 : ℂ) (21 / 20) ∩ Ext)
    (hrel : ∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (phiFour z)) (u0 z) = 0) : False := by
  refine U0PhiCircleWindow.u0_phi_windowed_no_relation_3var isOpen_ball
    ((convex_ball (0 : ℂ) (21 / 20)).isPreconnected) isPreconnected_annulus
    phiFour_analytic P hd hw hleadw hsepw (z₁ := 1) ?_ ?_ hVo hVne hVD hrel
  · show (1 : ℂ) ∈ ball (0 : ℂ) (21 / 20)
    simp only [mem_ball, dist_zero_right, norm_one]
    norm_num
  · simp

end U0PhiFourWindow

namespace U0PhiFourWindow

/-- **u₀ is not a rational expression in `z` and the Böttcher branch (UNCONDITIONAL, `b = 4`).**
There are no polynomials `A, B ∈ ℂ[z][W]` with `A(z, phiFour z)` not identically zero and
`A(z, phiFour z)·u₀(z) = B(z, phiFour z)` on a nonempty open subset of the annulus
`{1 < ‖z‖ < 21/20}` — the degree-one case of `u0_phiFour_no_relation`, with the leading and
separability data discharged automatically (a linear specialization is separable outright).  No
window hypothesis, no separability hypothesis: only the nonvanishing witness for `A`. -/
theorem u0_not_rational_in_phiFour (A B : Polynomial (Polynomial ℂ))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) (21 / 20))
    (hA : A.eval₂ (evalRingHom w) (phiFour w) ≠ 0)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVD : V ⊆ ball (0 : ℂ) (21 / 20) ∩ Ext)
    (hrel : ∀ z ∈ V, A.eval₂ (evalRingHom z) (phiFour z) * u0 z
        = B.eval₂ (evalRingHom z) (phiFour z)) : False := by
  set P : (Polynomial (Polynomial ℂ))[X] := C A * X - C B with hP
  have hAne : A ≠ 0 := by
    intro h
    rw [h] at hA
    simp at hA
  have hcoeff1 : P.coeff 1 = A := by
    rw [hP]
    simp
  have hcoeff0 : P.coeff 0 = -B := by
    rw [hP]
    simp
  have hdeg : P.natDegree = 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hcoeff1]; exact hAne))
    rw [hP]
    refine le_trans (natDegree_sub_le _ _) ?_
    refine max_le (le_trans (natDegree_C_mul_le _ _) (by simp)) (by simp)
  have hsum_eq : (∑ i : Fin (P.natDegree + 1),
        C ((P.coeff (i : ℕ)).eval₂ (evalRingHom w) (phiFour w)) * X ^ (i : ℕ))
      = C ((-B).eval₂ (evalRingHom w) (phiFour w))
        + C (A.eval₂ (evalRingHom w) (phiFour w)) * X := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => C ((P.coeff k).eval₂ (evalRingHom w) (phiFour w)) * X ^ k) (P.natDegree + 1),
      hdeg, Finset.sum_range_succ, Finset.sum_range_one, hcoeff0, hcoeff1]
    simp
  refine u0_phiFour_no_relation P (by rw [hdeg]) hw ?_ ?_ hVo hVne hVD ?_
  · rw [hsum_eq, hdeg]
    simpa using hA
  · rw [hsum_eq]
    have hsep : (C (A.eval₂ (evalRingHom w) (phiFour w)) * X
        + C ((-B).eval₂ (evalRingHom w) (phiFour w))).Separable := by
      have hder : derivative (C (A.eval₂ (evalRingHom w) (phiFour w)) * X
          + C ((-B).eval₂ (evalRingHom w) (phiFour w)))
          = C (A.eval₂ (evalRingHom w) (phiFour w)) := by
        simp
      unfold Polynomial.Separable
      rw [hder]
      exact ⟨0, C (A.eval₂ (evalRingHom w) (phiFour w))⁻¹,
        by simp [← C_mul, inv_mul_cancel₀ hA]⟩
    rw [add_comm] at hsep
    exact hsep
  · intro z hz
    rw [hP]
    simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, coe_eval₂RingHom]
    rw [hrel z hz]
    ring
