import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfAPulse

/-!
# The gravitational wave of a pulse is regular across the horizon

In the ingoing coordinate `v = t + r_*`, `r_* = ½ log((r − 1)/(r + 1))`, the change of coordinates
`(v, r, x, y) ↦ (t, r, x, y)` has `dt = dv − dr/F`, `F = r² − 1`. The background becomes
`−F dv² + 2 dv dr + r²(dx² + dy²)/y²` (`ingoing_background`), smooth with determinant `−r⁴/y⁴` at
`r = 1`.

A row with profile `(m, m₁)` has blocks `h_{ti} = σᵢ (F m(S) + m₁(S))` and `h_{ri} = σᵢ (r/F) m₁(S)`,
`S = t + γ(r) + log s`. In ingoing coordinates `S = v − log(2r/(r + 1)) + log s`, and

`h_{vi} = h_{ti} = σᵢ (F m(S) + m₁(S))`,   `h_{ri} − h_{ti}/F = σᵢ (m₁(S)/(r + 1) − m(S))`,

since `r − 1 = F/(r + 1)`: the pole of `r/F` cancels against the shift of `t`
(`ingoing_imageMetric`). Every entry is smooth on `r > 0`, so the exact vacuum perturbation of every
compact profile, in particular the gravitational wave of every pulse, extends smoothly through the
future horizon `r = 1` (`contDiffAt_ingoingMetric`).
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped ContDiff Matrix

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry
open _root_.RHTower
open EisensteinSeries

/-! ### Ingoing coordinates -/

/-- The hyperboloidal time `τ = v − log(2r/(r + 1))` in ingoing coordinates. -/
def ingoingTime (z : Fin 4 → ℝ) : ℝ := z 0 - Real.log (2 * z 1 / (z 1 + 1))

/-- The exterior point `(v − r_*, r, x, y)` of the ingoing point `(v, r, x, y)`. -/
def exteriorOfIngoing (z : Fin 4 → ℝ) : Fin 4 → ℝ := ![z 0 - tortoise (z 1), z 1, z 2, z 3]

theorem hyperTime_exteriorOfIngoing {z : Fin 4 → ℝ} (hr : 1 < z 1) :
    hyperTime (exteriorOfIngoing z) = ingoingTime z := by
  show (z 0 - tortoise (z 1)) + radialPhase (z 1) = ingoingTime z
  have h1 : 0 < z 1 - 1 := by linarith
  have h2 : 0 < z 1 + 1 := by linarith
  have h3 : 0 < z 1 := by linarith
  simp only [tortoise, radialPhase, ingoingTime]
  rw [Real.log_div h1.ne' h2.ne', show z 1 ^ 2 - 1 = (z 1 - 1) * (z 1 + 1) by ring,
    Real.log_mul h1.ne' h2.ne', Real.log_div (by positivity) h2.ne',
    Real.log_mul two_ne_zero h3.ne']
  ring

/-- `F = r² − 1` does not vanish on the exterior. -/
theorem rowF_ne_zero {z : Fin 4 → ℝ} (hr : 1 < z 1) : rowF z ≠ 0 := by
  have h : rowF z = ((z 1 ^ 2 - 1 : ℝ) : ℂ) := by
    simp only [rowF]
    push_cast
    ring
  rw [h]
  have : (0 : ℝ) < z 1 ^ 2 - 1 := by nlinarith
  exact_mod_cast this.ne'

/-- The phase of a row in ingoing coordinates. -/
def ingoingS (c d : ℝ) (z : Fin 4 → ℝ) : ℝ := ingoingTime z + Real.log (rowHgt c d (z 2) (z 3))

theorem rowS_exteriorOfIngoing (c d : ℝ) {z : Fin 4 → ℝ} (hr : 1 < z 1) :
    rowS c d (exteriorOfIngoing z) = ingoingS c d z := by
  rw [rowS_eq, hyperTime_exteriorOfIngoing hr]
  rfl

/-- The Jacobian `dt = dv − dr/F` of the change to ingoing coordinates. -/
def ingoingJacobian (z : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, -(rowF z)⁻¹, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **The background in ingoing coordinates** is `−F dv² + 2 dv dr + r²(dx² + dy²)/y²`. -/
theorem ingoing_background {z : Fin 4 → ℝ} (hr : 1 < z 1) :
    (ingoingJacobian z)ᵀ * D4BMBackground.metric (z 1) (z 3) * ingoingJacobian z =
      !![-rowF z, 1, 0, 0; 1, 0, 0, 0; 0, 0, (z 1 : ℂ) ^ 2 * ((z 3 : ℂ)⁻¹) ^ 2, 0;
        0, 0, 0, (z 1 : ℂ) ^ 2 * ((z 3 : ℂ)⁻¹) ^ 2] := by
  have hF : rowF z ≠ 0 := rowF_ne_zero hr
  have hF' : (z 1 : ℂ) ^ 2 - 1 = rowF z := by simp only [rowF]; ring
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, ingoingJacobian, D4BMBackground.metric,
      Matrix.diagonal, hF']
  all_goals field_simp
  all_goals ring

/-! ### The blocks of a row -/

/-- The `dv dxⁱ` block of a row. -/
def rowVin (c d : ℝ) (m m₁ : ℝ → ℂ) (i : Fin 2) (z : Fin 4 → ℝ) : ℂ :=
  (rowSigma c d i z : ℂ) * (rowF z * m (ingoingS c d z) + m₁ (ingoingS c d z))

/-- The `dr dxⁱ` block of a row: `σᵢ (m₁(S)/(r + 1) − m(S))`, with no pole at `r = 1`. -/
def rowRin (c d : ℝ) (m m₁ : ℝ → ℂ) (i : Fin 2) (z : Fin 4 → ℝ) : ℂ :=
  (rowSigma c d i z : ℂ) * (m₁ (ingoingS c d z) * ((z 1 : ℂ) + 1)⁻¹ - m (ingoingS c d z))

theorem rowT_exteriorOfIngoing (c d : ℝ) (m m₁ : ℝ → ℂ) (i : Fin 2) {z : Fin 4 → ℝ}
    (hr : 1 < z 1) : rowT c d m m₁ i (exteriorOfIngoing z) = rowVin c d m m₁ i z := by
  unfold rowT rowVin
  rw [rowS_exteriorOfIngoing c d hr]
  change (rowSigma c d i z : ℂ) * rowF z * m (ingoingS c d z) +
    (rowSigma c d i z : ℂ) * m₁ (ingoingS c d z) = _
  ring

/-- **The pole cancels.** `h_{ri} − h_{ti}/F = σᵢ (m₁(S)/(r + 1) − m(S))`. -/
theorem rowR_sub_rowT_exteriorOfIngoing (c d : ℝ) (m m₁ : ℝ → ℂ) (i : Fin 2) {z : Fin 4 → ℝ}
    (hr : 1 < z 1) :
    rowR c d m₁ i (exteriorOfIngoing z) - rowT c d m m₁ i (exteriorOfIngoing z) * (rowF z)⁻¹ =
      rowRin c d m m₁ i z := by
  have h0 : (z 1 : ℂ) - 1 ≠ 0 := by
    have : (0 : ℝ) < z 1 - 1 := by linarith
    exact_mod_cast this.ne'
  have h1 : (z 1 : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < z 1 + 1 := by linarith
    exact_mod_cast this.ne'
  have hFr : rowF z = ((z 1 : ℂ) - 1) * ((z 1 : ℂ) + 1) := by simp only [rowF]; ring
  unfold rowR rowT rowRin
  rw [rowS_exteriorOfIngoing c d hr]
  change (rowSigma c d i z : ℂ) * ((z 1 : ℂ) * (rowF z)⁻¹) * m₁ (ingoingS c d z) -
    ((rowSigma c d i z : ℂ) * rowF z * m (ingoingS c d z) +
      (rowSigma c d i z : ℂ) * m₁ (ingoingS c d z)) * (rowF z)⁻¹ = _
  rw [hFr]
  field_simp
  ring

/-! ### The perturbation of a compact profile in ingoing coordinates -/

/-- The `dv dxⁱ` block of the sum over rows. -/
def imageVin (m : CompactPulse) (i : Fin 2) (z : Fin 4 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0, rowVin (rowC p) (rowD p) m m.D i z

/-- The `dr dxⁱ` block of the sum over rows. -/
def imageRin (m : CompactPulse) (i : Fin 2) (z : Fin 4 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0, rowRin (rowC p) (rowD p) m m.D i z

/-- **The perturbation in ingoing coordinates `(v, r, x, y)`.** -/
def ingoingMetric (m : CompactPulse) (z : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, imageVin m 0 z, imageVin m 1 z;
    0, 0, imageRin m 0 z, imageRin m 1 z;
    imageVin m 0 z, imageRin m 0 z, 0, 0;
    imageVin m 1 z, imageRin m 1 z, 0, 0]

/-- The rows that can contribute at an exterior point. -/
theorem exists_finset_exterior (m : CompactPulse) {z : Fin 4 → ℝ} (hr : 1 < z 1) (hy : 0 < z 3) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ p ∉ S,
      m (ingoingS (rowC p) (rowD p) z) = 0 ∧ m.D (ingoingS (rowC p) (rowD p) z) = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_metric m ⟨exteriorOfIngoing z, hr, hy⟩
  refine ⟨S, fun p hp => ?_⟩
  have h := hS.self_of_nhds p hp
  rwa [rowS_exteriorOfIngoing _ _ hr] at h

/-- **The perturbation transforms as a tensor.** On the exterior,
`Jᵀ h J` is the ingoing perturbation `ingoingMetric`. -/
theorem ingoing_imageMetric (m : CompactPulse) {z : Fin 4 → ℝ} (hr : 1 < z 1) (hy : 0 < z 3) :
    (ingoingJacobian z)ᵀ * imageMetric m (exteriorOfIngoing z) * ingoingJacobian z =
      ingoingMetric m z := by
  obtain ⟨S, hS⟩ := exists_finset_exterior m hr hy
  have hzero : ∀ p ∉ S, ∀ i : Fin 2,
      rowT (rowC p) (rowD p) m m.D i (exteriorOfIngoing z) = 0 ∧
        rowR (rowC p) (rowD p) m.D i (exteriorOfIngoing z) = 0 ∧
        rowVin (rowC p) (rowD p) m m.D i z = 0 ∧ rowRin (rowC p) (rowD p) m m.D i z = 0 := by
    intro p hp i
    obtain ⟨h0, h1⟩ := hS p hp
    simp only [rowT, rowR, rowVin, rowRin, rowS_exteriorOfIngoing _ _ hr, h0, h1]
    simp
  have hT : ∀ i : Fin 2, imageT m i (exteriorOfIngoing z) = imageVin m i z := by
    intro i
    rw [imageT, imageVin, tsum_eq_sum (s := S) fun p hp => (hzero p hp i).1,
      tsum_eq_sum (s := S) fun p hp => (hzero p hp i).2.2.1]
    congr 1
    exact Finset.sum_congr rfl fun p _ => rowT_exteriorOfIngoing _ _ _ _ i hr
  have hR : ∀ i : Fin 2, imageR m i (exteriorOfIngoing z) -
      imageT m i (exteriorOfIngoing z) * (rowF z)⁻¹ = imageRin m i z := by
    intro i
    rw [imageR, imageT, imageRin, tsum_eq_sum (s := S) fun p hp => (hzero p hp i).2.1,
      tsum_eq_sum (s := S) fun p hp => (hzero p hp i).1,
      tsum_eq_sum (s := S) fun p hp => (hzero p hp i).2.2.2]
    have e : (1 / 2 : ℂ) * ∑ p ∈ S, (rowR (rowC p) (rowD p) m.D i (exteriorOfIngoing z) -
        rowT (rowC p) (rowD p) m m.D i (exteriorOfIngoing z) * (rowF z)⁻¹) =
        (1 / 2 : ℂ) * ∑ p ∈ S, rowR (rowC p) (rowD p) m.D i (exteriorOfIngoing z) -
          ((1 / 2 : ℂ) * ∑ p ∈ S, rowT (rowC p) (rowD p) m m.D i (exteriorOfIngoing z)) *
            (rowF z)⁻¹ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [← e]
    congr 1
    exact Finset.sum_congr rfl fun p _ => rowR_sub_rowT_exteriorOfIngoing _ _ _ _ i hr
  have hV0 := hT 0
  have hV1 := hT 1
  have hR0 := hR 0
  have hR1 := hR 1
  unfold ingoingMetric
  rw [← hV0, ← hV1, ← hR0, ← hR1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, ingoingJacobian, imageMetric] <;>
    ring

/-! ### Regularity -/

theorem contDiffAt_rowSigma_of_pos {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y)
    (i : Fin 2) {z : Fin 4 → ℝ} (hy : 0 < z 3) :
    ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => (rowSigma c d i w : ℂ)) z := by
  have hD := hden (z 2) (z 3) hy
  have hD2 : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => rowDen c d (w 2) (w 3) ^ 2) z :=
    contDiffAt_rowDen.pow 2
  have hne : rowDen c d (z 2) (z 3) ^ 2 ≠ 0 := pow_ne_zero 2 hD.ne'
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp z ?_
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => rowSigma c d 0 w) z
    simp only [rowSigma, if_true]
    exact ContDiffAt.div (by fun_prop) hD2 hne
  · change ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => rowSigma c d 1 w) z
    simp only [rowSigma, Fin.isValue, one_ne_zero, if_false]
    exact (ContDiffAt.div (by fun_prop) hD2 hne).neg

theorem contDiffAt_ingoingTime {z : Fin 4 → ℝ} (hr : 0 < z 1) :
    ContDiffAt ℝ ∞ ingoingTime z := by
  have h1 : z 1 + 1 ≠ 0 := by linarith
  have hq : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => 2 * w 1 / (w 1 + 1)) z :=
    ContDiffAt.div (by fun_prop) (by fun_prop) h1
  have hpos : 2 * z 1 / (z 1 + 1) ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  exact (contDiff_apply ℝ ℝ 0).contDiffAt.sub (hq.log hpos)

theorem contDiffAt_ingoingS {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y)
    {z : Fin 4 → ℝ} (hr : 0 < z 1) (hy : 0 < z 3) : ContDiffAt ℝ ∞ (ingoingS c d) z := by
  have hD := hden (z 2) (z 3) hy
  have hS : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => rowHgt c d (w 2) (w 3)) z :=
    ContDiffAt.div (by fun_prop) contDiffAt_rowDen hD.ne'
  exact (contDiffAt_ingoingTime hr).add (hS.log (div_pos hy hD).ne')

theorem contDiffAt_rowVin {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y)
    (m : CompactPulse) (i : Fin 2) {z : Fin 4 → ℝ} (hr : 0 < z 1) (hy : 0 < z 3) :
    ContDiffAt ℝ ∞ (rowVin c d m m.D i) z := by
  have hF : ContDiffAt ℝ ∞ rowF z := by
    have hR : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => (w 1 : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
    exact (hR.mul hR).add contDiffAt_const
  have hm := m.smooth.contDiffAt.comp z (contDiffAt_ingoingS hden hr hy)
  have hm₁ := m.D.smooth.contDiffAt.comp z (contDiffAt_ingoingS hden hr hy)
  exact (contDiffAt_rowSigma_of_pos hden i hy).mul ((hF.mul hm).add hm₁)

theorem contDiffAt_rowRin {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y)
    (m : CompactPulse) (i : Fin 2) {z : Fin 4 → ℝ} (hr : 0 < z 1) (hy : 0 < z 3) :
    ContDiffAt ℝ ∞ (rowRin c d m m.D i) z := by
  have hR : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => (w 1 : ℂ) + 1) z :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt.add contDiffAt_const
  have h1 : (z 1 : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < z 1 + 1 := by linarith
    exact_mod_cast this.ne'
  have hm := m.smooth.contDiffAt.comp z (contDiffAt_ingoingS hden hr hy)
  have hm₁ := m.D.smooth.contDiffAt.comp z (contDiffAt_ingoingS hden hr hy)
  exact (contDiffAt_rowSigma_of_pos hden i hy).mul ((hm₁.mul (hR.inv h1)).sub hm)

/-- Near any point with `r > 0`, `y > 0`, only finitely many rows contribute. -/
theorem exists_finset_ingoing (m : CompactPulse) {z : Fin 4 → ℝ} (hr : 0 < z 1) (hy : 0 < z 3) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ᶠ w in 𝓝 z, ∀ p ∉ S,
      m (ingoingS (rowC p) (rowD p) w) = 0 ∧ m.D (ingoingS (rowC p) (rowD p) w) = 0 := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_box m (ingoingTime z) (z 2) hy
  obtain ⟨S₂, h₂⟩ := exists_finset_box m.D (ingoingTime z) (z 2) hy
  refine ⟨S₁ ∪ S₂, ?_⟩
  have hτ : ∀ᶠ w in 𝓝 z, |ingoingTime w - ingoingTime z| < 1 := by
    have := (contDiffAt_ingoingTime hr).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with w hw
    simpa [Real.dist_eq] using hw
  have hx2 : ∀ᶠ w : Fin 4 → ℝ in 𝓝 z, |w 2 - z 2| < 1 := by
    have := (continuous_apply 2).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (z 2) one_pos)
    filter_upwards [this] with w hw
    simpa [Real.dist_eq] using hw
  have hx3 : ∀ᶠ w : Fin 4 → ℝ in 𝓝 z, w 3 ∈ Ioo (z 3 / 2) (2 * z 3) :=
    (continuous_apply 3).continuousAt.tendsto.eventually
      (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hτ, hx2, hx3] with w a1 a2 a3 p hp
  simp only [Finset.mem_union, not_or] at hp
  have hY : 0 < w 3 := by linarith [a3.1]
  have hs := rowHgt_pos_row p (w 2) hY
  exact ⟨pulseF_eq_zero_iff _ _ hs (h₁ _ _ _ a1.le a2.le (Ioo_subset_Icc_self a3) p hp.1),
    pulseF_eq_zero_iff _ _ hs (h₂ _ _ _ a1.le a2.le (Ioo_subset_Icc_self a3) p hp.2)⟩

/-- **The gravitational wave of every compact profile is smooth across the horizon.** Every entry
of the ingoing perturbation is `C^∞` at every point with `r > 0` and `y > 0`, the horizon `r = 1`
included. -/
theorem contDiffAt_ingoingMetric (m : CompactPulse) {z : Fin 4 → ℝ} (hr : 0 < z 1)
    (hy : 0 < z 3) (a b : Fin 4) : ContDiffAt ℝ ∞ (fun w => ingoingMetric m w a b) z := by
  obtain ⟨S, hS⟩ := exists_finset_ingoing m hr hy
  have hV : ∀ i : Fin 2, ContDiffAt ℝ ∞ (imageVin m i) z := by
    intro i
    have hsum : ContDiffAt ℝ ∞ (fun w => (1 / 2 : ℂ) *
        ∑ p ∈ S, rowVin (rowC p) (rowD p) m m.D i w) z :=
      contDiffAt_const.mul (ContDiffAt.sum fun p _ =>
        contDiffAt_rowVin (rowDen_pos p) m i hr hy)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hS] with w hw
    rw [imageVin, tsum_eq_sum (s := S) fun p hp => by
      simp [rowVin, (hw p hp).1, (hw p hp).2]]
  have hR : ∀ i : Fin 2, ContDiffAt ℝ ∞ (imageRin m i) z := by
    intro i
    have hsum : ContDiffAt ℝ ∞ (fun w => (1 / 2 : ℂ) *
        ∑ p ∈ S, rowRin (rowC p) (rowD p) m m.D i w) z :=
      contDiffAt_const.mul (ContDiffAt.sum fun p _ =>
        contDiffAt_rowRin (rowDen_pos p) m i hr hy)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hS] with w hw
    rw [imageRin, tsum_eq_sum (s := S) fun p hp => by
      simp [rowRin, (hw p hp).1, (hw p hp).2]]
  fin_cases a <;> fin_cases b
  all_goals first
    | exact contDiffAt_const | exact hV 0 | exact hV 1 | exact hR 0 | exact hR 1

end GaloisForLFunctions.BlackHoleRingdown

end
