import GaloisForLFunctions.RHTower.SuzukiCoalescingHalfPlaneNormality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The full coalescing quotient on a first-order chart

The characteristic quotient of a movable anchor is the Cayley factor times the ratio of the
transform of the shifted deficiency vector at `z` and at `-z`.  Reflection symmetry of the ground
space makes that transform have a definite parity, so on a first-order chart the ratio is

`ε (1 + 2c H(z)/G(z) + o(c))`,

with `G` the transform of the leading ground vector and `H` the transform of the next one.  The
Cayley factor contributes `1 - 2ic/z + O(c²)`.  Both first-order terms survive the singular
normalization by `c`, and the limit of the normalized resolvent is the **two-port coordinate**

`i/z - H(z)/G(z)`.

When the leading ground vector is the only visible one — the nonadjacent case — the second term
vanishes identically and the limit is the universal `i/z`.

Every finite member of the family has strictly positive real part, since it is a positive multiple
of the inverse Cayley transform of a Schur function; hence so does the limit, weakly.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-! ## Parity of the ground transform -/

/-- The transform of a ground vector, evaluated at a complex frequency. -/
def parityFourier (u : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, u x * Complex.exp (z * I * (x : ℂ))

/-- **`(92)`: parity of the ground transform.**  A vector with a reflection parity has a transform
with the same parity. -/
theorem parityFourier_neg {u : ℝ → ℂ} {ε : ℂ} (hu : ∀ x : ℝ, u (-x) = ε * u x) (z : ℂ) :
    parityFourier u (-z) = ε * parityFourier u z := by
  have hsub := integral_neg_eq_self
    (fun x : ℝ => u x * Complex.exp (-z * I * (x : ℂ))) volume
  have hleft : ∀ x : ℝ,
      u (-x) * Complex.exp (-z * I * ((-x : ℝ) : ℂ)) = ε * (u x * Complex.exp (z * I * (x : ℂ))) := by
    intro x
    rw [hu x]
    push_cast
    ring_nf
  calc parityFourier u (-z)
      = ∫ x : ℝ, u x * Complex.exp (-z * I * (x : ℂ)) := by
        rw [parityFourier]
    _ = ∫ x : ℝ, u (-x) * Complex.exp (-z * I * ((-x : ℝ) : ℂ)) := hsub.symm
    _ = ∫ x : ℝ, ε * (u x * Complex.exp (z * I * (x : ℂ))) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ε * parityFourier u z := by
        rw [parityFourier, integral_const_mul]

/-! ## The two-port limit -/

/-- The Cayley factor tends to one as the anchor collapses. -/
theorem tendsto_suzukiCoalescingCayley_one {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => suzukiCoalescingCayley c z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hnum : Tendsto (fun c : ℝ => z - (c : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have : Tendsto (fun c : ℝ => ((c : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    simpa using tendsto_const_nhds.sub (this.mul tendsto_const_nhds)
  have hden : Tendsto (fun c : ℝ => z + (c : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have : Tendsto (fun c : ℝ => ((c : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    simpa using tendsto_const_nhds.add (this.mul tendsto_const_nhds)
  have hlim := hnum.div hden hz
  rw [div_self hz] at hlim
  exact hlim

/-- The first-order rate of the Cayley factor. -/
theorem tendsto_suzukiCoalescingCayley_rate_two_port {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => (suzukiCoalescingCayley c z - 1) / (c : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * I) / z)) := by
  have hden : Tendsto (fun c : ℝ => z + (c : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have : Tendsto (fun c : ℝ => ((c : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    simpa using tendsto_const_nhds.add (this.mul tendsto_const_nhds)
  have hlim : Tendsto (fun c : ℝ => -(2 * I) / (z + (c : ℂ) * I))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(2 * I) / z)) := tendsto_const_nhds.div hden hz
  have hne : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), z + (c : ℂ) * I ≠ 0 := hden.eventually_ne hz
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hne] with c hc hden0
  have hcne : ((c : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hc
  have hkey : suzukiCoalescingCayley c z - 1 = -(2 * I) * (c : ℂ) / (z + (c : ℂ) * I) := by
    rw [suzukiCoalescingCayley]
    field_simp
    ring
  rw [hkey]
  field_simp

/-- **`(94)`: the full first-order limit.**  If the reflected transform ratio has first-order rate
`2H/G`, the singularly normalized quotient converges to the two-port coordinate. -/
theorem tendsto_twoPort_of_ratio_rate {z G H : ℂ} (hz : z ≠ 0)
    {q : ℝ → ℂ}
    (hq : Tendsto (fun c : ℝ => (q c - 1) / (c : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * H / G))) :
    Tendsto (fun c : ℝ =>
        (1 - suzukiCoalescingCayley c z * q c) /
          ((c : ℂ) * (1 + suzukiCoalescingCayley c z * q c)))
      (𝓝[>] (0 : ℝ)) (𝓝 (I / z - H / G)) := by
  have hcz : Tendsto (fun c : ℝ => ((c : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  have hq1 : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hprod : Tendsto (fun c : ℝ => ((c : ℂ)) * ((q c - 1) / (c : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 * (2 * H / G))) := hcz.mul hq
    rw [zero_mul] at hprod
    have hsub : Tendsto (fun c : ℝ => q c - 1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine hprod.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with c hc
      have hcne : ((c : ℂ)) ≠ 0 := by simpa using ne_of_gt hc
      field_simp
    have := hsub.add (tendsto_const_nhds (x := (1 : ℂ)))
    simpa using this
  have hb := tendsto_suzukiCoalescingCayley_one hz
  have hbrate := tendsto_suzukiCoalescingCayley_rate_two_port hz
  have hnum : Tendsto (fun c : ℝ => (suzukiCoalescingCayley c z * q c - 1) / (c : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * H / G + -(2 * I) / z)) := by
    have hsum := (hb.mul hq).add hbrate
    have hsum' : Tendsto
        (fun c : ℝ => suzukiCoalescingCayley c z * ((q c - 1) / (c : ℂ))
          + (suzukiCoalescingCayley c z - 1) / (c : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 * (2 * H / G) + -(2 * I) / z)) := (hb.mul hq).add hbrate
    rw [one_mul] at hsum'
    refine hsum'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcne : ((c : ℂ)) ≠ 0 := by simpa using ne_of_gt hc
    field_simp
    ring
  have hden : Tendsto (fun c : ℝ => 1 + suzukiCoalescingCayley c z * q c)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ)) (f := 𝓝[>] (0 : ℝ))).add (hb.mul hq1)
    norm_num at h
    exact h
  have hlim := (hnum.div hden (by norm_num)).neg
  have hval : -((2 * H / G + -(2 * I) / z) / 2) = I / z - H / G := by
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : ((c : ℂ)) ≠ 0 := by simpa using ne_of_gt hc
  simp only [Pi.div_apply]
  rcases eq_or_ne (1 + suzukiCoalescingCayley c z * q c) 0 with h0 | h0
  · rw [h0, div_zero, neg_zero, mul_zero, div_zero]
  · field_simp
    ring

/-- **`(98)`: the nonadjacent universal limit.**  With no second visible ground vector the two-port
coordinate degenerates to the universal `i/z`. -/
theorem tendsto_twoPort_universal {z G : ℂ} (hz : z ≠ 0) {q : ℝ → ℂ}
    (hq : Tendsto (fun c : ℝ => (q c - 1) / (c : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun c : ℝ =>
        (1 - suzukiCoalescingCayley c z * q c) /
          ((c : ℂ) * (1 + suzukiCoalescingCayley c z * q c)))
      (𝓝[>] (0 : ℝ)) (𝓝 (I / z)) := by
  have h := tendsto_twoPort_of_ratio_rate (z := z) (G := G) (H := 0) hz
    (by simpa using hq)
  simpa using h

/-! ## Positivity of the finite family and of the limit -/

/-- The inverse Cayley transform of a Schur value has strictly positive real part. -/
theorem re_one_sub_div_one_add_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < ((1 - w) / (1 + w)).re := by
  have hne : 1 + w ≠ 0 := by
    intro h
    have : w = -1 := by linear_combination h
    rw [this] at hw
    simp at hw
  have hpos : (0 : ℝ) < Complex.normSq (1 + w) := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_pos_iff.mpr hne
    positivity
  have hlt : w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ) < 1 := by
    have hsq : ‖w‖ ^ (2 : ℕ) < 1 := by nlinarith [norm_nonneg w]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
    nlinarith
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, zero_sub]
  rw [← add_div, div_pos_iff]
  refine Or.inl ⟨by nlinarith, hpos⟩

/-- **Every finite member has positive real part.**  The singularly normalized resolvent of a Schur
carrier is a positive multiple of an inverse Cayley transform. -/
theorem re_suzukiCoalescingResolvent_pos {θ : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hθ : ‖θ z‖ < 1) :
    0 < (suzukiCoalescingResolvent θ c z).re := by
  have hbase := re_one_sub_div_one_add_pos hθ
  have hsplit : suzukiCoalescingResolvent θ c z = ((c : ℂ))⁻¹ * ((1 - θ z) / (1 + θ z)) := by
    rw [suzukiCoalescingResolvent]
    field_simp
  rw [hsplit]
  have hinv : ((c : ℂ))⁻¹ = ((c⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hinv, Complex.re_ofReal_mul]
  exact mul_pos (inv_pos.mpr hc) hbase

/-- The limit of a family with positive real parts has nonnegative real part. -/
theorem re_nonneg_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℂ} {L : ℂ}
    (hf : Tendsto f l (𝓝 L)) (hpos : ∀ᶠ i in l, 0 ≤ (f i).re) :
    0 ≤ L.re :=
  ge_of_tendsto ((Complex.continuous_re.tendsto L).comp hf) hpos

end RHTower
