import GaloisForLFunctions.RHTower.SuzukiMovableAnchorClarkCoherence

/-!
# The ground frame carries no coherence defect at the origin

Source coherence is a projective quantity: it depends on the mode only through the complex line the
mode spans.  Hence a mode family whose rescalings converge to a fixed nonzero ground direction has
coherence tending to one, no matter what the rescaling factors are.  Applied to the first visible
ground expansion `P₀e^{-ixX} = (-ix)^k u + O(x^{k+1})`, this says that the apparent coherence zero
at zero frequency is an artefact of the vanishing of the vector, not a loss of alignment.

The residual loss is projective rotation.  The exact deficit is the distance from the mode to the
line through the anchor:

`‖lineProj u w - w‖² = ‖w‖² (1 - coherence)`.

Consequently a transport bound on that distance is exactly a coherence floor, and through the Clark
budget a uniform bound on the number of orthonormal modes in the window.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Coherence is projective -/

/-- Coherence does not see a nonzero rescaling of the mode. -/
theorem suzukiSourceCoherence_smul_right (u : E) {a : ℂ} (w : E) (ha : a ≠ 0) :
    suzukiSourceCoherence u (a • w) = suzukiSourceCoherence u w := by
  by_cases hw : w = 0
  · subst hw; simp
  by_cases hu : u = 0
  · subst hu; simp [suzukiSourceCoherence]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [suzukiSourceCoherence, suzukiSourceCoherence, inner_smul_right, norm_mul, norm_smul,
    mul_pow, mul_pow]
  field_simp

/-- A nonzero vector is perfectly coherent with itself. -/
@[simp] theorem suzukiSourceCoherence_self {u : E} (hu : u ≠ 0) :
    suzukiSourceCoherence u u = 1 := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [suzukiSourceCoherence, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg u)]
  field_simp

/-- Coherence against a fixed anchor is continuous in the mode at every nonzero mode. -/
theorem continuousAt_suzukiSourceCoherence (u : E) {w : E} (hw : w ≠ 0) :
    ContinuousAt (suzukiSourceCoherence u) w := by
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  by_cases hu : u = 0
  · subst hu
    have h0 : suzukiSourceCoherence (0 : E) = fun _ : E => (0 : ℝ) := by
      funext v; simp [suzukiSourceCoherence]
    rw [h0]
    exact continuousAt_const
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnum : ContinuousAt (fun v : E => ‖inner ℂ u v‖ ^ 2) w :=
    (((innerSL ℂ u).continuous.norm.pow 2)).continuousAt
  have hden : ContinuousAt (fun v : E => ‖u‖ ^ 2 * ‖v‖ ^ 2) w :=
    (continuous_const.mul (continuous_norm.pow 2)).continuousAt
  exact hnum.div hden (by positivity)

/-- **`(69)`–`(70)`: no coherence defect in the ground frame.**  If some nonzero rescaling of the
mode family converges to the anchor direction, the coherence tends to one. -/
theorem tendsto_suzukiSourceCoherence_one
    {ι : Type*} {l : Filter ι} {w : ι → E} {s : ι → ℂ} {u : E}
    (hu : u ≠ 0) (hs : ∀ᶠ i in l, s i ≠ 0)
    (hlim : Tendsto (fun i => s i • w i) l (𝓝 u)) :
    Tendsto (fun i => suzukiSourceCoherence u (w i)) l (𝓝 1) := by
  have hcont : ContinuousAt (suzukiSourceCoherence u) u :=
    continuousAt_suzukiSourceCoherence u hu
  have hcomp : Tendsto (fun i => suzukiSourceCoherence u (s i • w i)) l
      (𝓝 (suzukiSourceCoherence u u)) := hcont.tendsto.comp hlim
  rw [suzukiSourceCoherence_self hu] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [hs] with i hi
  exact suzukiSourceCoherence_smul_right u (w i) hi

/-! ## The exact projective deficit -/

/-- The component of a vector along the complex line through a nonzero anchor. -/
def lineProj (u v : E) : E := ((inner ℂ u v) / ((‖u‖ : ℂ) ^ 2)) • u

@[simp] theorem lineProj_zero_left (v : E) : lineProj (0 : E) v = 0 := by
  simp [lineProj]

/-- **The exact projective deficit.**  The squared distance from a mode to the anchor line is the
squared norm of the mode times its coherence defect. -/
theorem norm_lineProj_sub_sq (u w : E) :
    ‖lineProj u w - w‖ ^ 2 = ‖w‖ ^ 2 * (1 - suzukiSourceCoherence u w) := by
  by_cases hu : u = 0
  · subst hu
    simp [suzukiSourceCoherence]
  by_cases hw : w = 0
  · subst hw
    simp [lineProj]
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  set c : ℂ := (inner ℂ u w) / ((‖u‖ : ℂ) ^ 2) with hc
  have hcnorm : ‖((‖u‖ : ℂ) ^ 2)‖ = ‖u‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
  have hconj : (starRingEnd ℂ) ((‖u‖ : ℂ) ^ 2) = ((‖u‖ : ℂ) ^ 2) := by
    rw [map_pow, Complex.conj_ofReal]
  have hcu : ‖c • u‖ ^ 2 = ‖inner ℂ u w‖ ^ 2 / ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow, hc, norm_div, hcnorm]
    field_simp
  have hnum : (starRingEnd ℂ) (inner ℂ u w) * inner ℂ u w = ((‖inner ℂ u w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hval : inner ℂ (c • u) w = ((‖inner ℂ u w‖ ^ 2 / ‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_left, hc, map_div₀, hconj, div_mul_eq_mul_div, hnum]
    push_cast
    ring
  have hcross : RCLike.re (inner ℂ (c • u) w) = ‖inner ℂ u w‖ ^ 2 / ‖u‖ ^ 2 := by
    rw [hval]
    exact RCLike.ofReal_re _
  rw [lineProj, ← hc, norm_sub_sq (𝕜 := ℂ), hcu, hcross, suzukiSourceCoherence]
  field_simp
  ring

/-- **The projective coherence floor.**  A transport bound on the distance from the mode to the
anchor line is exactly a coherence floor. -/
theorem one_sub_sq_le_suzukiSourceCoherence {u w : E} (hw : w ≠ 0) {L : ℝ}
    (hL : ‖lineProj u w - w‖ ≤ L * ‖w‖) :
    1 - L ^ 2 ≤ suzukiSourceCoherence u w := by
  have hw2 : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  have h0 : 0 ≤ ‖lineProj u w - w‖ := norm_nonneg _
  have hsq : ‖w‖ ^ 2 * (1 - suzukiSourceCoherence u w) ≤ L ^ 2 * ‖w‖ ^ 2 := by
    rw [← norm_lineProj_sub_sq]
    calc ‖lineProj u w - w‖ ^ 2 ≤ (L * ‖w‖) ^ 2 := pow_le_pow_left₀ h0 hL 2
      _ = L ^ 2 * ‖w‖ ^ 2 := by ring
  nlinarith [hsq, hw2]

/-! ## Transport of the ground direction -/

theorem lineProj_add (u a b : E) : lineProj u (a + b) = lineProj u a + lineProj u b := by
  rw [lineProj, lineProj, lineProj, inner_add_right, add_div, add_smul]

theorem lineProj_self {u : E} (hu : u ≠ 0) : lineProj u u = u := by
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hcast : ((‖u‖ : ℂ)) ≠ 0 := by exact_mod_cast hnu
  have hself : inner ℂ u u = ((‖u‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K u
  rw [lineProj, hself, div_self (pow_ne_zero 2 hcast), one_smul]

/-- The line component and the transverse component are orthogonal. -/
theorem inner_lineProj_sub_eq_zero (u v : E) :
    inner ℂ (lineProj u v) (v - lineProj u v) = 0 := by
  by_cases hu : u = 0
  · subst hu; simp
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hcast : ((‖u‖ : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hnu)
  have hself : inner ℂ u u = ((‖u‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K u
  rw [lineProj, inner_smul_left, inner_sub_right, inner_smul_right, hself,
    div_mul_cancel₀ _ hcast, sub_self, mul_zero]

/-- The transverse component is a contraction. -/
theorem norm_sub_lineProj_le (u v : E) : ‖v - lineProj u v‖ ≤ ‖v‖ := by
  have hpyth : ‖v‖ ^ 2 = ‖lineProj u v‖ ^ 2 + ‖v - lineProj u v‖ ^ 2 := by
    have hsum : lineProj u v + (v - lineProj u v) = v := by abel
    have h := norm_add_sq (𝕜 := ℂ) (lineProj u v) (v - lineProj u v)
    rw [hsum, inner_lineProj_sub_eq_zero] at h
    simpa using h
  nlinarith [norm_nonneg (v - lineProj u v), norm_nonneg v, sq_nonneg ‖lineProj u v‖]

/-- **Transport of the ground direction.**  The projective deficit of a mode is bounded by its
displacement from the anchor. -/
theorem norm_lineProj_sub_le_norm_sub {u : E} (hu : u ≠ 0) (w : E) :
    ‖lineProj u w - w‖ ≤ ‖w - u‖ := by
  have hsplit : w - lineProj u w = (w - u) - lineProj u (w - u) := by
    have hadd : lineProj u ((w - u) + u) = lineProj u (w - u) + lineProj u u := lineProj_add _ _ _
    rw [show (w - u) + u = w by abel, lineProj_self hu] at hadd
    rw [hadd]
    abel
  calc ‖lineProj u w - w‖ = ‖w - lineProj u w‖ := by rw [norm_sub_rev]
    _ = ‖(w - u) - lineProj u (w - u)‖ := by rw [hsplit]
    _ ≤ ‖w - u‖ := norm_sub_lineProj_le u (w - u)

/-- **A displacement budget is a coherence floor.** -/
theorem one_sub_sq_le_suzukiSourceCoherence_of_norm_sub {u w : E} (hu : u ≠ 0) (hw : w ≠ 0)
    {L : ℝ} (hL : ‖w - u‖ ≤ L * ‖w‖) :
    1 - L ^ 2 ≤ suzukiSourceCoherence u w :=
  one_sub_sq_le_suzukiSourceCoherence hw (le_trans (norm_lineProj_sub_le_norm_sub hu w) hL)

/-! ## The angular form -/

/-- **`(71)`: the Fubini–Study speed** of a mode path — the transverse part of the velocity,
normalized by the length of the mode. -/
def fubiniStudySpeed (w w' : E) : ℝ := ‖w' - lineProj w w'‖ / ‖w‖

theorem fubiniStudySpeed_nonneg (w w' : E) : 0 ≤ fubiniStudySpeed w w' := by
  rw [fubiniStudySpeed]
  positivity

/-- The projective angle between the anchor and the mode. -/
def projectiveAngle (u w : E) : ℝ := Real.arccos (Real.sqrt (suzukiSourceCoherence u w))

/-- **`(73)`: a subcritical angular budget is a coherence floor.**  If the projective angle stays
below `π/2 - ε`, the coherence is at least `sin(ε)²`. -/
theorem sin_sq_le_suzukiSourceCoherence {u w : E} {ε : ℝ} (hε : 0 ≤ ε)
    (hangle : projectiveAngle u w ≤ Real.pi / 2 - ε) :
    Real.sin ε ^ 2 ≤ suzukiSourceCoherence u w := by
  have hcoh0 : 0 ≤ suzukiSourceCoherence u w := suzukiSourceCoherence_nonneg u w
  have hcoh1 : suzukiSourceCoherence u w ≤ 1 := suzukiSourceCoherence_le_one u w
  have hs0 : 0 ≤ Real.sqrt (suzukiSourceCoherence u w) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (suzukiSourceCoherence u w) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hcoh1
  have hcos : Real.cos (projectiveAngle u w) = Real.sqrt (suzukiSourceCoherence u w) := by
    rw [projectiveAngle, Real.cos_arccos (by linarith) hs1]
  have hmono : Real.cos (Real.pi / 2 - ε) ≤ Real.cos (projectiveAngle u w) := by
    refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ hangle
    · rw [projectiveAngle]
      exact Real.arccos_nonneg _
    · linarith [Real.pi_pos]
  rw [Real.cos_pi_div_two_sub, hcos] at hmono
  have harc : (0 : ℝ) ≤ projectiveAngle u w := Real.arccos_nonneg _
  have hεhalf : ε ≤ Real.pi / 2 := by linarith
  have hsin : 0 ≤ Real.sin ε :=
    Real.sin_nonneg_of_nonneg_of_le_pi hε (by linarith [Real.pi_pos])
  nlinarith [Real.sq_sqrt hcoh0, hs0, hsin, hmono]

/-- **The Clark-count consequence.**  A projective transport budget below one gives a uniform
bound on the number of orthonormal Clark modes in the window. -/
theorem card_mul_le_one_of_lineProj_budget
    {ι : Type*} [Fintype ι] {anchor : E} {mode : ι → E} {L : ℝ}
    (hanchor : ‖anchor‖ = 1) (hmode : Orthonormal ℂ mode) {u : E}
    (hbudget : ∀ i, ‖lineProj u (mode i) - mode i‖ ≤ L * ‖mode i‖)
    (hfloor : ∀ i, suzukiSourceCoherence u (mode i) ≤
      suzukiSourceCoherence anchor (mode i)) :
    (Fintype.card ι : ℝ) * (1 - L ^ 2) ≤ 1 := by
  refine card_mul_le_one_of_suzukiSourceCoherence_floor hanchor hmode fun i => ?_
  exact le_trans (one_sub_sq_le_suzukiSourceCoherence (hmode.ne_zero i) (hbudget i)) (hfloor i)

end GaloisForLFunctions.RHTower
