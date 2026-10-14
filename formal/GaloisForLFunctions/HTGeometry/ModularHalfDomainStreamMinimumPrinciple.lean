import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A minimum principle for stream functions on the half fundamental domain

Let `D₊ = {0 ≤ x ≤ ½, x² + y² ≥ 1, y ≥ 0}` be the right half of the standard fundamental domain of
`SL₂(ℤ)`, bounded by the walls `x = 0`, `x = ½` and the bottom arc `x² + y² = 1`.  Let `Z(x, y)`
solve the stream equation

`y (Z_xx + Z_yy) − Z_y = 0`  on `y > 0`

(the Stokes stream function of an axisymmetric potential; for `Z = ψ`, `div(y⁻¹ ∇ψ) = 0`).

**Theorem** (`le_of_halfDomainStreamMinimum`).  Suppose `m ≤ Z` on both walls,
`Z ≥ m − δ` for all large heights (every `δ > 0`), and at every point `(x, √(1 − x²))` of the
open arc (`0 < x < ½`) the derivative of `Z` along the outward ray `t ↦ (1 + t)(x, √(1 − x²))`
is negative.
Then `m ≤ Z` on all of `D₊`.

Proof.  Otherwise put `η = m − Z(x₀, y₀) > 0`, truncate at a height `Y` where `Z ≥ m − η/4`, and
minimize `f = Z − η x²` on the compact truncated region.  The minimum is `≤ m − η`.  It is not on a
wall (`f ≥ m − η/4` there), not on the top, not on the open arc (the ray derivative of `f` is
negative, so `f` decreases into the region), and not in the interior: there the one-dimensional
second-derivative tests (`nonneg_of_isLocalMin_of_hasDerivAt`) give `Z_xx ≥ 2η`, `Z_yy ≥ 0`,
`Z_y = 0`, contradicting the equation.
-/

open Filter Topology Set

namespace GaloisForLFunctions
namespace HTGeometry

/-- The half fundamental domain truncated at height `Y`. -/
def halfDomainRegion (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ Y ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2}

theorem isCompact_halfDomainRegion (Y : ℝ) : IsCompact (halfDomainRegion Y) := by
  have hsub : halfDomainRegion Y ⊆ Icc (0 : ℝ) (1 / 2) ×ˢ Icc 0 Y := fun p hp =>
    ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2.1⟩⟩
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  have heq : halfDomainRegion Y = {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p | p.1 ≤ 1 / 2} ∩ {p | 0 ≤ p.2} ∩
      {p | p.2 ≤ Y} ∩ {p | 1 ≤ p.1 ^ 2 + p.2 ^ 2} := by
    ext p; simp only [halfDomainRegion, mem_inter_iff, mem_setOf_eq]; tauto
  rw [heq]
  refine ((((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter
    (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_) <;> fun_prop

theorem halfDomainRegion_y_pos {Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ halfDomainRegion Y) : 0 < p.2 := by
  obtain ⟨h0, h1, h2, -, h4⟩ := hp
  rcases h2.lt_or_eq with h | h
  · exact h
  · rw [← h] at h4; nlinarith

/-- **Minimum principle for stream functions on the half fundamental domain.** -/
theorem le_of_halfDomainStreamMinimum {Z Zx Zxx Zy Zyy : ℝ → ℝ → ℝ} {m : ℝ}
    (hx : ∀ x y, 0 < y → HasDerivAt (fun s => Z s y) (Zx x y) x)
    (hxx : ∀ x y, 0 < y → HasDerivAt (fun s => Zx s y) (Zxx x y) x)
    (hy : ∀ x y, 0 < y → HasDerivAt (fun s => Z x s) (Zy x y) y)
    (hyy : ∀ x y, 0 < y → HasDerivAt (fun s => Zy x s) (Zyy x y) y)
    (hL : ∀ x y, 0 < y → y * (Zxx x y + Zyy x y) - Zy x y = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2) {p | 0 < p.2})
    (hwall0 : ∀ y, 0 < y → m ≤ Z 0 y) (hwall1 : ∀ y, 0 < y → m ≤ Z (1 / 2) y)
    (htop : ∀ δ > 0, ∃ Y, ∀ x y, 0 ≤ x → x ≤ 1 / 2 → Y ≤ y → m - δ ≤ Z x y)
    (harc : ∀ x, 0 < x → x < 1 / 2 → ∃ D < 0,
      HasDerivAt (fun t => Z ((1 + t) * x) ((1 + t) * Real.sqrt (1 - x ^ 2))) D 0)
    {x₀ y₀ : ℝ} (hx0 : 0 ≤ x₀) (hx1 : x₀ ≤ 1 / 2) (hy0 : 0 ≤ y₀) (hr : 1 ≤ x₀ ^ 2 + y₀ ^ 2) :
    m ≤ Z x₀ y₀ := by
  by_contra hlt
  rw [not_le] at hlt
  set η := m - Z x₀ y₀ with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨Y₁, hY₁⟩ := htop (η / 4) (by linarith)
  set Y := max Y₁ (y₀ + 2) with hYdef
  have hY₁Y : Y₁ ≤ Y := le_max_left _ _
  have hy₀Y : y₀ + 2 ≤ Y := le_max_right _ _
  set f : ℝ × ℝ → ℝ := fun p => Z p.1 p.2 - η * p.1 ^ 2 with hf
  set K := halfDomainRegion Y with hK
  have hP₀ : (x₀, y₀) ∈ K := ⟨hx0, hx1, hy0, by linarith, hr⟩
  have hfc : ContinuousOn f K := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2) K :=
      hcont.mono fun p hp => halfDomainRegion_y_pos hp
    exact h1.sub (by fun_prop)
  obtain ⟨P, hPK, hPmin⟩ := (isCompact_halfDomainRegion Y).exists_isMinOn ⟨_, hP₀⟩ hfc
  have hfP : f P ≤ m - η := by
    have h : f P ≤ f (x₀, y₀) := hPmin hP₀
    simp only [hf] at h ⊢
    nlinarith [mul_nonneg hη0.le (sq_nonneg x₀)]
  obtain ⟨hPx0, hPx1, hPy0, hPyY, hPr⟩ := hPK
  have hPy : 0 < P.2 := halfDomainRegion_y_pos ⟨hPx0, hPx1, hPy0, hPyY, hPr⟩
  -- walls
  rcases hPx0.lt_or_eq with hPx0' | hPx0'
  swap
  · have := hwall0 P.2 hPy
    simp only [hf, ← hPx0'] at hfP
    nlinarith
  rcases hPx1.lt_or_eq with hPx1' | hPx1'
  swap
  · have := hwall1 P.2 hPy
    simp only [hf, hPx1'] at hfP
    nlinarith
  -- top
  rcases hPyY.lt_or_eq with hPyY' | hPyY'
  swap
  · have := hY₁ P.1 P.2 hPx0 hPx1 (hPyY' ▸ hY₁Y)
    simp only [hf] at hfP
    nlinarith [mul_le_mul_of_nonneg_left (show P.1 ^ 2 ≤ 1 / 4 by nlinarith) hη0.le]
  -- arc or interior
  rcases hPr.lt_or_eq with hPr' | hPr'
  · -- interior
    have hev : ∀ᶠ q in 𝓝 P, q ∈ K := by
      have ho : IsOpen {q : ℝ × ℝ | 0 < q.1 ∧ q.1 < 1 / 2 ∧ 0 < q.2 ∧ q.2 < Y ∧
          1 < q.1 ^ 2 + q.2 ^ 2} := by
        have c0 : Continuous fun _ : ℝ × ℝ => (0 : ℝ) := continuous_const
        have c1 : Continuous fun _ : ℝ × ℝ => (1 / 2 : ℝ) := continuous_const
        have cY : Continuous fun _ : ℝ × ℝ => Y := continuous_const
        have cO : Continuous fun _ : ℝ × ℝ => (1 : ℝ) := continuous_const
        have cr : Continuous fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 := by fun_prop
        exact (isOpen_lt c0 continuous_fst).inter ((isOpen_lt continuous_fst c1).inter
          ((isOpen_lt c0 continuous_snd).inter ((isOpen_lt continuous_snd cY).inter
            (isOpen_lt cO cr))))
      filter_upwards [ho.mem_nhds ⟨hPx0', hPx1', hPy, hPyY', hPr'⟩] with q hq
      exact ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.1.le, hq.2.2.2.2.le⟩
    -- the `x`-slice
    have hminx : IsLocalMin (fun s => Z s P.2 - η * s ^ 2) P.1 := by
      have hc : Continuous fun s : ℝ => (s, P.2) := by fun_prop
      have h := hc.continuousAt.tendsto.eventually hev
      filter_upwards [h] with s hs
      have := hPmin hs
      simpa [hf] using this
    have hminy : IsLocalMin (fun s => Z P.1 s - η * P.1 ^ 2) P.2 := by
      have hc : Continuous fun s : ℝ => (P.1, s) := by fun_prop
      have h := hc.continuousAt.tendsto.eventually hev
      filter_upwards [h] with s hs
      have := hPmin hs
      simpa [hf] using this
    have hyev : ∀ᶠ s in 𝓝 P.2, 0 < s := lt_mem_nhds hPy
    have hxx' : 0 ≤ Zxx P.1 P.2 - η * 2 := by
      refine nonneg_of_isLocalMin_of_hasDerivAt (g' := fun s => Zx s P.2 - η * (2 * s)) hminx
        (Eventually.of_forall fun s => ?_) ?_
      · refine (hx s P.2 hPy).sub ?_
        simpa using (hasDerivAt_pow 2 s).const_mul η
      · refine (hxx P.1 P.2 hPy).sub ?_
        simpa using ((hasDerivAt_id P.1).const_mul (2 : ℝ)).const_mul η
    have hyy' : 0 ≤ Zyy P.1 P.2 := by
      refine nonneg_of_isLocalMin_of_hasDerivAt (g' := fun s => Zy P.1 s) hminy ?_
        (hyy P.1 P.2 hPy)
      filter_upwards [hyev] with s hs
      exact (hy P.1 s hs).sub_const _
    have hy0' : Zy P.1 P.2 = 0 := by
      have := hminy.hasDerivAt_eq_zero ((hy P.1 P.2 hPy).sub_const (η * P.1 ^ 2))
      exact this
    have := hL P.1 P.2 hPy
    rw [hy0'] at this
    nlinarith
  · -- the open arc
    have hPy' : P.2 = Real.sqrt (1 - P.1 ^ 2) := by
      rw [show 1 - P.1 ^ 2 = P.2 ^ 2 by linarith, Real.sqrt_sq hPy0]
    obtain ⟨D, hD, hDer⟩ := harc P.1 hPx0' hPx1'
    have hpoly : HasDerivAt (fun t : ℝ => η * ((1 + t) * P.1) ^ 2) (η * (2 * P.1 * P.1)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (1 + t) * P.1) (1 * P.1) 0 :=
        ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const P.1
      have h2 := (h1.pow 2).const_mul η
      refine h2.congr_deriv ?_
      simp
    have hh := hDer.sub hpoly
    have hneg : D - η * (2 * P.1 * P.1) < 0 := by nlinarith [sq_nonneg P.1]
    -- the ray points lie in `K` for small `t > 0`
    have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((1 + t) * P.1, (1 + t) * Real.sqrt (1 - P.1 ^ 2)) ∈ K := by
      rw [← hPy']
      have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t) * P.1 < 1 / 2 := by
        have hc : Continuous fun t : ℝ => (1 + t) * P.1 := by fun_prop
        exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hPx1')
      have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t) * P.2 < Y := by
        have hc : Continuous fun t : ℝ => (1 + t) * P.2 := by fun_prop
        exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hPyY')
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
        with t ht1 ht2 (ht3 : 0 < t)
      refine ⟨by positivity, ht1.le, by positivity, ht2.le, ?_⟩
      have : 1 ≤ (1 + t) ^ 2 := by nlinarith
      nlinarith
    -- but `f` strictly decreases along the ray
    set g : ℝ → ℝ := fun t => Z ((1 + t) * P.1) ((1 + t) * Real.sqrt (1 - P.1 ^ 2)) -
      η * ((1 + t) * P.1) ^ 2 with hg
    have hh' : HasDerivAt g (D - η * (2 * P.1 * P.1)) 0 := hh
    have hslope : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 (D - η * (2 * P.1 * P.1))) :=
      hh'.tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
    have hev := hslope.eventually (gt_mem_nhds hneg)
    obtain ⟨t, ⟨hsl, hmem⟩, ht0⟩ := ((hev.and hray).and self_mem_nhdsWithin).exists
    have ht0' : (0 : ℝ) < t := ht0
    have hge : f P ≤ f ((1 + t) * P.1, (1 + t) * Real.sqrt (1 - P.1 ^ 2)) := hPmin hmem
    have hg0 : g 0 = f P := by
      simp only [hg, hf, add_zero, one_mul]
      rw [← hPy']
    have hgt : g t = f ((1 + t) * P.1, (1 + t) * Real.sqrt (1 - P.1 ^ 2)) := by
      simp only [hg, hf]
    rw [slope_def_field, sub_zero, div_neg_iff] at hsl
    rcases hsl with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · linarith

end HTGeometry
end GaloisForLFunctions
