import GaloisForLFunctions.RHTower.Suzuki.SuzukiDeBrangesLift
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRaySpaces

noncomputable section

/-!
# `E 𝖥(V(t))` is a de Branges subspace

The four clauses of the de Branges axioms are read off the model-space picture.

Entirety and membership in `H(E)` come from the basis expansion.  Point evaluation above the axis
is `E(w)` times the reproducing pairing, hence bounded; below the axis it is the conjugate of the
evaluation of the sharp reflection.  The sharp reflection is the involution `κ f = Θ conj f`, which
preserves `𝖥(V(t))` and its norm.

For the last axiom, a zero of the entire representative at `w` above the axis is exactly a vanishing
Cauchy transform there, and the Blaschke symbol `(x - conj w)/(x - w)` then keeps the element in
`𝖥(V(t))`.  Splitting that symbol into partial fractions against a second Cauchy kernel shows the
entire representative gets multiplied by `(z - conj w)/(z - w)`, and the symbol is unimodular on the
axis, so the norm is unchanged.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem suzukiDeBrangesLift_eq_integral (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ suzukiModelSpace) :
    suzukiDeBrangesLift hRH G w
      = xiHedenmalmDeBrangesE w
        * ((-I / (2 * (Real.pi : ℂ))) * ∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) := by
  rw [suzukiDeBrangesLift_apply hRH hw hG, inner_suzukiModelKernelLp hRH hw hG]

theorem integral_eq_zero_of_suzukiDeBrangesLift_eq_zero (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ suzukiModelSpace)
    (h : suzukiDeBrangesLift hRH G w = 0) :
    (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0 := by
  have hpi := Real.pi_pos
  have hE : xiHedenmalmDeBrangesE w ≠ 0 :=
    xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh hRH hw
  have hc : (-I / (2 * (Real.pi : ℂ))) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  rw [suzukiDeBrangesLift_eq_integral hRH hw hG] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hE)).resolve_left hc

/-- Dividing out a zero above the axis keeps an element of the model space in the model space. -/
theorem blaschkeMul_mem_suzukiModelSpace {w : ℂ} (hw : 0 < w.im)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ suzukiModelSpace)
    (hzero : (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    blaschkeMul w G ∈ suzukiModelSpace := by
  have hG' : G ∈ suzukiModelRay 0 := by rw [suzukiModelRay_zero]; exact hG
  have h := blaschkeMul_mem_suzukiModelRay (t := 0) le_rfl hw hG' hzero
  rwa [suzukiModelRay_zero] at h

/-- **The Blaschke transform of the lift.**  Multiplying by `(z - conj w)/(z - w)` on the model
space multiplies the entire representative by the same factor. -/
theorem suzukiDeBrangesLift_blaschkeMul (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ suzukiModelSpace)
    (hzero : (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) {z : ℂ} (hz : 0 < z.im) :
    suzukiDeBrangesLift hRH (blaschkeMul w G) z * (z - w)
      = suzukiDeBrangesLift hRH G z * (z - (starRingEnd ℂ) w) := by
  have hpi := Real.pi_pos
  have hGb := blaschkeMul_mem_suzukiModelSpace hw hG hzero
  by_cases hzw : z = w
  · subst hzw
    rw [sub_self, mul_zero, suzukiDeBrangesLift_eq_integral hRH hz hG, hzero]
    ring
  · have hzwne : w - z ≠ 0 := fun h => hzw (by linear_combination -h)
    have hzsub : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have hint1 := integrable_lp_div_sub (ne_of_gt hw) G
    have hint2 := integrable_lp_div_sub (ne_of_gt hz) G
    have hae : (fun x : ℝ => (blaschkeMul w G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - z))
        =ᵐ[volume] fun x : ℝ =>
          ((w - (starRingEnd ℂ) w) / (w - z)) * ((G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
            + ((z - (starRingEnd ℂ) w) / (z - w)) * ((G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - z)) := by
      filter_upwards [coeFn_blaschkeMul w G] with x h
      rw [h, mul_comm (blaschkeSymbol w x), mul_div_assoc,
        blaschke_partialFraction (ne_of_gt hw) (ne_of_gt hz) hzwne x]
      ring
    have hsplit : (∫ x : ℝ, (blaschkeMul w G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - z))
        = ((z - (starRingEnd ℂ) w) / (z - w))
          * ∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - z) := by
      rw [MeasureTheory.integral_congr_ae hae,
        MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hzero]
      ring
    rw [suzukiDeBrangesLift_eq_integral hRH hz hGb, suzukiDeBrangesLift_eq_integral hRH hz hG,
      hsplit]
    field_simp

/-! ## The de Branges axioms for `E 𝖥(V(t))` -/

/-- Every element of `𝖥(V(t))` has an entire `E`-multiple lying in `H(E)`. -/
theorem memDeBranges_suzukiDeBrangesLift_of_ray (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ suzukiModelRay t) :
    MemDeBranges (suzukiDeBrangesLift hRH G) :=
  memDeBranges_suzukiDeBrangesLift hRH (suzukiModelRay_le_suzukiModelSpace ht hG)

/-- **(dB1) below the axis.**  Point evaluation is bounded there too, through the sharp
reflection. -/
theorem norm_suzukiDeBrangesLift_le_lower (hRH : RiemannHypothesis) {z : ℂ} (hz : z.im < 0)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    ‖suzukiDeBrangesLift hRH F z‖
      ≤ ‖xiHedenmalmDeBrangesE ((starRingEnd ℂ) z)‖
          * ‖(memLp_suzukiModelKernel hRH (show 0 < ((starRingEnd ℂ) z).im by simpa using hz)).toLp
              (fun x : ℝ =>
                suzukiModelKernel ((starRingEnd ℂ) z) ((x : ℝ) : ℂ))‖ * ‖F‖ := by
  have hzc : 0 < ((starRingEnd ℂ) z).im := by simpa using hz
  have hsharp := suzukiDeBrangesLift_thetaMul_star hRH hF ((starRingEnd ℂ) z)
  rw [Complex.conj_conj] at hsharp
  have hnorm : ‖suzukiDeBrangesLift hRH F z‖
      = ‖suzukiDeBrangesLift hRH (thetaMul (star F)) ((starRingEnd ℂ) z)‖ := by
    rw [hsharp, RCLike.norm_conj]
  rw [hnorm, ← norm_thetaMul_star F]
  exact norm_suzukiDeBrangesLift_le hRH hzc (thetaMul_star_mem_suzukiModelSpace hF)

/-- **Suzuki, Theorem 5.3.**  For every `t ≥ 0` the space `E 𝖥(V(t))` is a de Branges subspace of
`H(E)`: its elements are entire and lie in `H(E)`; point evaluation off the real axis is bounded;
the sharp involution preserves the space isometrically; and a zero above the axis may be moved to
its reflection by the Blaschke factor, isometrically. -/
theorem suzuki_deBranges_subspace (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) :
    (∀ G ∈ suzukiModelRay t, MemDeBranges (suzukiDeBrangesLift hRH G))
      ∧ (∀ (w : ℂ), 0 < w.im → ∃ C : ℝ, ∀ G ∈ suzukiModelRay t,
          ‖suzukiDeBrangesLift hRH G w‖ ≤ C * ‖G‖)
      ∧ (∀ (z : ℂ), z.im < 0 → ∃ C : ℝ, ∀ G ∈ suzukiModelRay t,
          ‖suzukiDeBrangesLift hRH G z‖ ≤ C * ‖G‖)
      ∧ (∀ G ∈ suzukiModelRay t, thetaMul (star G) ∈ suzukiModelRay t
          ∧ ‖thetaMul (star G)‖ = ‖G‖
          ∧ ∀ z : ℂ, suzukiDeBrangesLift hRH (thetaMul (star G)) z
              = (starRingEnd ℂ) (suzukiDeBrangesLift hRH G ((starRingEnd ℂ) z)))
      ∧ (∀ (w : ℂ), 0 < w.im → ∀ G ∈ suzukiModelRay t,
          suzukiDeBrangesLift hRH G w = 0 →
            blaschkeMul w G ∈ suzukiModelRay t
              ∧ ‖blaschkeMul w G‖ = ‖G‖
              ∧ ∀ z : ℂ, 0 < z.im →
                  suzukiDeBrangesLift hRH (blaschkeMul w G) z * (z - w)
                    = suzukiDeBrangesLift hRH G z * (z - (starRingEnd ℂ) w)) := by
  refine ⟨fun G hG => memDeBranges_suzukiDeBrangesLift_of_ray hRH ht hG, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨‖xiHedenmalmDeBrangesE w‖ * ‖(memLp_suzukiModelKernel hRH hw).toLp
      (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ))‖, fun G hG => ?_⟩
    exact norm_suzukiDeBrangesLift_le hRH hw (suzukiModelRay_le_suzukiModelSpace ht hG)
  · intro z hz
    have hzc : 0 < ((starRingEnd ℂ) z).im := by simpa using hz
    refine ⟨‖xiHedenmalmDeBrangesE ((starRingEnd ℂ) z)‖ *
      ‖(memLp_suzukiModelKernel hRH hzc).toLp
        (fun x : ℝ => suzukiModelKernel ((starRingEnd ℂ) z) ((x : ℝ) : ℂ))‖, fun G hG => ?_⟩
    exact norm_suzukiDeBrangesLift_le_lower hRH hz (suzukiModelRay_le_suzukiModelSpace ht hG)
  · intro G hG
    exact ⟨suzukiKappa_mem_suzukiModelRay hG, norm_thetaMul_star G,
      fun z => suzukiDeBrangesLift_thetaMul_star hRH
        (suzukiModelRay_le_suzukiModelSpace ht hG) z⟩
  · intro w hw G hG hzero
    have hGm := suzukiModelRay_le_suzukiModelSpace ht hG
    have hint := integral_eq_zero_of_suzukiDeBrangesLift_eq_zero hRH hw hGm hzero
    exact ⟨blaschkeMul_mem_suzukiModelRay ht hw hG hint,
      norm_blaschkeMul (ne_of_gt hw) G,
      fun z hz => suzukiDeBrangesLift_blaschkeMul hRH hw hGm hint hz⟩

end RHTower
