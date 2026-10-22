import GaloisForLFunctions.RHTower.ShortIntervalBlockReduction

/-!
# The block reduction for the Chebyshev function

The real-analytic block reduction of `ShortIntervalBlockReduction` applied to `P = Chebyshev.psi`.
Everything here is integrability bookkeeping: `ψ` is monotone, hence measurable, and it is bounded on
a compact interval, so each of the three increments appearing in the reduction has an integrable
square.  With that in place the reduction specialises to

`∫_X^{2X} (ψ(x+y) − ψ(x) − y)² ≤ 2J² ∫_X^{3X} (ψ(u+δu) − ψ(u) − δu)² + 2 ∫_X^{2X} (boundary)²`,

which converts a second moment for the multiplicative window into one for a window of fixed
length `y`.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory intervalIntegral Finset

noncomputable section

/-- `ψ` is measurable, being monotone. -/
theorem measurable_psi : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable

/-- The multiplicative increment of `ψ` is measurable. -/
theorem measurable_multIncr_psi (δ : ℝ) :
    Measurable (fun u : ℝ => multIncr Chebyshev.psi δ u) := by
  unfold multIncr
  exact (((measurable_psi.comp (measurable_id.mul_const (1 + δ)))).sub measurable_psi).sub
    (measurable_const.mul measurable_id)

/-- The fixed-length increment of `ψ` is measurable. -/
theorem measurable_fixedIncr_psi (y : ℝ) :
    Measurable (fun x : ℝ => fixedIncr Chebyshev.psi y x) := by
  unfold fixedIncr
  exact ((measurable_psi.comp (measurable_id.add_const y)).sub measurable_psi).sub
    measurable_const

/-- The boundary increment of `ψ` is measurable. -/
theorem measurable_bdryIncr_psi (y δ : ℝ) (J : ℕ) :
    Measurable (fun x : ℝ => bdryIncr Chebyshev.psi y x δ J) := by
  unfold bdryIncr gridPt
  exact (((measurable_psi.comp (measurable_id.mul_const ((1 + δ) ^ J))).sub
    (measurable_psi.comp (measurable_id.add_const y))).sub
    ((measurable_id.mul_const ((1 + δ) ^ J)).sub (measurable_id.add_const y)))

/-- A measurable function with a uniform bound on `[a, b]` has an integrable square there. -/
theorem intervalIntegrable_sq_of_bound {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : Measurable f) (hb : ∀ x ∈ Set.Ioc a b, |f x| ≤ M) :
    IntervalIntegrable (fun x => (f x) ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := M ^ 2) ?_ ((hf.pow_const 2).aestronglyMeasurable) ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h := hb x hx
    have h0 : (0 : ℝ) ≤ |f x| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f x), h, h0]

/-- On `[a, b]` with `0 ≤ a`, the multiplicative increment of `ψ` is bounded by
`ψ((1+δ)b) + ψ(b) + δ b`. -/
theorem abs_multIncr_psi_le {δ a b x : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hx : x ∈ Set.Ioc a b) :
    |multIncr Chebyshev.psi δ x| ≤ Chebyshev.psi ((1 + δ) * b) + Chebyshev.psi b + δ * b := by
  obtain ⟨hx1, hx2⟩ := hx
  have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx1)
  have h1 : Chebyshev.psi (x * (1 + δ)) ≤ Chebyshev.psi ((1 + δ) * b) := by
    refine Chebyshev.psi_mono ?_
    nlinarith
  have h2 : Chebyshev.psi x ≤ Chebyshev.psi b := Chebyshev.psi_mono hx2
  have h3 : (0 : ℝ) ≤ Chebyshev.psi (x * (1 + δ)) := Chebyshev.psi_nonneg _
  have h4 : (0 : ℝ) ≤ Chebyshev.psi x := Chebyshev.psi_nonneg _
  have h5 : δ * x ≤ δ * b := mul_le_mul_of_nonneg_left hx2 hδ
  have h6 : (0 : ℝ) ≤ δ * x := mul_nonneg hδ hx0
  unfold multIncr
  rw [abs_le]
  constructor <;> nlinarith

/-- The square of the multiplicative increment of `ψ` is interval integrable. -/
theorem intervalIntegrable_sq_multIncr_psi {δ a b : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (multIncr Chebyshev.psi δ u) ^ 2) volume a b :=
  intervalIntegrable_sq_of_bound hab (measurable_multIncr_psi δ)
    fun _x hx => abs_multIncr_psi_le hδ ha hx

/-- On `[a, b]` with `0 ≤ a ≤ b` and `0 ≤ y`, the fixed increment of `ψ` is bounded by
`ψ(b + y) + ψ(b) + y`. -/
theorem abs_fixedIncr_psi_le {y a b x : ℝ} (hy : 0 ≤ y) (_ha : 0 ≤ a) (hx : x ∈ Set.Ioc a b) :
    |fixedIncr Chebyshev.psi y x| ≤ Chebyshev.psi (b + y) + Chebyshev.psi b + y := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : Chebyshev.psi (x + y) ≤ Chebyshev.psi (b + y) := Chebyshev.psi_mono (by linarith)
  have h2 : Chebyshev.psi x ≤ Chebyshev.psi b := Chebyshev.psi_mono hx2
  have h3 : (0 : ℝ) ≤ Chebyshev.psi (x + y) := Chebyshev.psi_nonneg _
  have h4 : (0 : ℝ) ≤ Chebyshev.psi x := Chebyshev.psi_nonneg _
  unfold fixedIncr
  rw [abs_le]
  constructor <;> nlinarith

/-- The square of the fixed increment of `ψ` is interval integrable. -/
theorem intervalIntegrable_sq_fixedIncr_psi {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (fixedIncr Chebyshev.psi y x) ^ 2) volume a b :=
  intervalIntegrable_sq_of_bound hab (measurable_fixedIncr_psi y)
    fun _x hx => abs_fixedIncr_psi_le hy ha hx

/-- On `[a, b]` with `0 ≤ a` and `1 ≤ (1+δ)^J`, the boundary increment of `ψ` is bounded. -/
theorem abs_bdryIncr_psi_le {y δ a b x : ℝ} {J : ℕ} (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hc : (1 : ℝ) ≤ (1 + δ) ^ J) (hx : x ∈ Set.Ioc a b) :
    |bdryIncr Chebyshev.psi y x δ J|
      ≤ Chebyshev.psi (b * (1 + δ) ^ J) + Chebyshev.psi (b + y) + (b * (1 + δ) ^ J + b + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx1)
  have hb0 : 0 ≤ b := le_trans hx0 hx2
  have hgrid : gridPt δ x J = x * (1 + δ) ^ J := rfl
  have h1 : Chebyshev.psi (x * (1 + δ) ^ J) ≤ Chebyshev.psi (b * (1 + δ) ^ J) :=
    Chebyshev.psi_mono (by nlinarith)
  have h2 : Chebyshev.psi (x + y) ≤ Chebyshev.psi (b + y) := Chebyshev.psi_mono (by linarith)
  have h3 : (0 : ℝ) ≤ Chebyshev.psi (x * (1 + δ) ^ J) := Chebyshev.psi_nonneg _
  have h4 : (0 : ℝ) ≤ Chebyshev.psi (x + y) := Chebyshev.psi_nonneg _
  have h5 : x * (1 + δ) ^ J ≤ b * (1 + δ) ^ J := by nlinarith
  have h6 : (0 : ℝ) ≤ x * (1 + δ) ^ J := by nlinarith
  unfold bdryIncr
  rw [hgrid, abs_le]
  constructor <;> nlinarith

/-- The square of the boundary increment of `ψ` is interval integrable. -/
theorem intervalIntegrable_sq_bdryIncr_psi {y δ a b : ℝ} {J : ℕ} (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hab : a ≤ b) (hc : (1 : ℝ) ≤ (1 + δ) ^ J) :
    IntervalIntegrable (fun x => (bdryIncr Chebyshev.psi y x δ J) ^ 2) volume a b :=
  intervalIntegrable_sq_of_bound hab (measurable_bdryIncr_psi y δ J)
    fun _x hx => abs_bdryIncr_psi_le hy ha hc hx

/-- **The block reduction for `ψ`.**  The second moment of the fixed-length window increment on
`[X, 2X]` is at most `2J²` times the second moment of the multiplicative window increment on
`[X, 3X]`, plus twice the boundary term. -/
theorem integral_sq_fixedIncr_psi_le {δ X y : ℝ} (hδ : 0 < δ) (hX : 0 < X) (hy : 0 ≤ y) (J : ℕ)
    (hJ : 2 * (1 + δ) ^ J ≤ 3) :
    ∫ x in X..(2 * X), (fixedIncr Chebyshev.psi y x) ^ 2
      ≤ 2 * (J : ℝ) ^ 2 * (∫ u in X..(3 * X), (multIncr Chebyshev.psi δ u) ^ 2)
        + 2 * ∫ x in X..(2 * X), (bdryIncr Chebyshev.psi y x δ J) ^ 2 := by
  have hδ1 : (1 : ℝ) ≤ 1 + δ := by linarith
  have hc : (1 : ℝ) ≤ (1 + δ) ^ J := one_le_pow₀ hδ1
  refine integral_sq_fixedIncr_le Chebyshev.psi hδ hX J hJ
    (intervalIntegrable_sq_multIncr_psi hδ.le hX.le (by linarith)) ?_
    (intervalIntegrable_sq_fixedIncr_psi hy hX.le (by linarith))
    (intervalIntegrable_sq_bdryIncr_psi hy hX.le (by linarith) hc)
  intro j _
  have hcj : (1 : ℝ) ≤ (1 + δ) ^ j := one_le_pow₀ hδ1
  have hbnd : ∀ x ∈ Set.Ioc X (2 * X),
      |multIncr Chebyshev.psi δ (gridPt δ x j)|
        ≤ Chebyshev.psi ((1 + δ) * (2 * X * (1 + δ) ^ j))
          + Chebyshev.psi (2 * X * (1 + δ) ^ j) + δ * (2 * X * (1 + δ) ^ j) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hX hx.1
    refine abs_multIncr_psi_le (a := 0) (b := 2 * X * (1 + δ) ^ j) hδ.le le_rfl ?_
    refine ⟨?_, ?_⟩
    · show 0 < x * (1 + δ) ^ j
      positivity
    · show x * (1 + δ) ^ j ≤ 2 * X * (1 + δ) ^ j
      have hpow : (0 : ℝ) ≤ (1 + δ) ^ j := by positivity
      exact mul_le_mul_of_nonneg_right hx.2 hpow
  exact intervalIntegrable_sq_of_bound (by linarith)
    ((measurable_multIncr_psi δ).comp (measurable_id.mul_const ((1 + δ) ^ j))) hbnd


/-- **The boundary increment is a multiplicative increment.**  If the last grid point lies in
`[x + y, (x + y)(1 + δ)]` then, `ψ` being monotone, the boundary increment is controlled by the
multiplicative increment at `x + y` plus the length of the overshoot.  This removes the dependence of
the boundary term on the block count. -/
theorem abs_bdryIncr_psi_le_multIncr {δ y x : ℝ} {J : ℕ} (_hδ0 : 0 ≤ δ) (_hxy : 0 ≤ x + y)
    (hlo : x + y ≤ gridPt δ x J) (hhi : gridPt δ x J ≤ (x + y) * (1 + δ)) :
    |bdryIncr Chebyshev.psi y x δ J| ≤ |multIncr Chebyshev.psi δ (x + y)| + δ * (x + y) := by
  have hmono : Chebyshev.psi (x + y) ≤ Chebyshev.psi (gridPt δ x J) := Chebyshev.psi_mono hlo
  have hup : Chebyshev.psi (gridPt δ x J) ≤ Chebyshev.psi ((x + y) * (1 + δ)) :=
    Chebyshev.psi_mono hhi
  have hover : gridPt δ x J - (x + y) ≤ δ * (x + y) := by nlinarith
  have hover0 : (0 : ℝ) ≤ gridPt δ x J - (x + y) := by linarith
  have hM : multIncr Chebyshev.psi δ (x + y)
      = Chebyshev.psi ((x + y) * (1 + δ)) - Chebyshev.psi (x + y) - δ * (x + y) := rfl
  have hMabs : Chebyshev.psi ((x + y) * (1 + δ)) - Chebyshev.psi (x + y) - δ * (x + y)
      ≤ |multIncr Chebyshev.psi δ (x + y)| := by rw [hM]; exact le_abs_self _
  have habs0 : (0 : ℝ) ≤ |multIncr Chebyshev.psi δ (x + y)| := abs_nonneg _
  unfold bdryIncr
  rw [abs_le]
  refine ⟨by linarith, by linarith⟩


/-- **The pointwise bound with a uniform block count and no boundary dependence.**  Taking the
pointwise count from `exists_blockCount` and bounding its boundary increment by a multiplicative one
leaves an integrand that depends only on `δ` and `J₀`. -/
theorem sq_fixedIncr_psi_le_uniform {δ X y x : ℝ} {J₀ : ℕ} (hδ : 0 < δ) (hX : 0 < X) (hy : 0 ≤ y)
    (hJ₀ : X + y ≤ gridPt δ X J₀) (hx : x ∈ Set.Icc X (2 * X)) :
    (fixedIncr Chebyshev.psi y x) ^ 2
      ≤ 2 * (J₀ : ℝ) * (∑ j ∈ Finset.range J₀, (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
        + 4 * (multIncr Chebyshev.psi δ (x + y)) ^ 2 + 4 * δ ^ 2 * (x + y) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le hX hx.1
  have hxy0 : 0 ≤ x + y := by linarith
  have hpow : (0 : ℝ) < (1 + δ) ^ J₀ := by positivity
  -- the uniform count already reaches past `x + y`
  have hJx : x + y ≤ gridPt δ x J₀ := by
    have hXy : X + y ≤ X * (1 + δ) ^ J₀ := hJ₀
    have hratio : (1 : ℝ) + y / X ≤ (1 + δ) ^ J₀ := by
      rw [← sub_nonneg]
      have e : (1 + δ) ^ J₀ - (1 + y / X) = (X * (1 + δ) ^ J₀ - (X + y)) / X := by
        field_simp
      rw [e]
      exact div_nonneg (by linarith) hX.le
    show x + y ≤ x * (1 + δ) ^ J₀
    have h1 : x * (1 + y / X) ≤ x * (1 + δ) ^ J₀ :=
      mul_le_mul_of_nonneg_left hratio hx0.le
    have hxy : y ≤ x * (y / X) := by
      have e2 : x * (y / X) - y = y * (x - X) / X := by field_simp
      have hnn : (0 : ℝ) ≤ y * (x - X) / X :=
        div_nonneg (mul_nonneg hy (by linarith [hx.1])) hX.le
      linarith [e2 ▸ hnn]
    have h2 : x + y ≤ x * (1 + y / X) := by nlinarith [hxy]
    linarith
  obtain ⟨J, hJlo, hJhi, hJmin⟩ := exists_blockCount hδ hx0 hy
  have hJle : J ≤ J₀ := hJmin J₀ hJx
  have hmain := sq_fixedIncr_le_of_le Chebyshev.psi (ne_of_gt hδ) y x J J₀ hJle
  have hbd := abs_bdryIncr_psi_le_multIncr (J := J) hδ.le hxy0 hJlo hJhi
  have habs0 : (0 : ℝ) ≤ |multIncr Chebyshev.psi δ (x + y)| := abs_nonneg _
  have hδxy : (0 : ℝ) ≤ δ * (x + y) := mul_nonneg hδ.le hxy0
  have hsq : (bdryIncr Chebyshev.psi y x δ J) ^ 2
      ≤ 2 * (multIncr Chebyshev.psi δ (x + y)) ^ 2 + 2 * (δ * (x + y)) ^ 2 := by
    have h1 : (bdryIncr Chebyshev.psi y x δ J) ^ 2
        ≤ (|multIncr Chebyshev.psi δ (x + y)| + δ * (x + y)) ^ 2 := by
      have := abs_nonneg (bdryIncr Chebyshev.psi y x δ J)
      nlinarith [hbd, sq_abs (bdryIncr Chebyshev.psi y x δ J)]
    nlinarith [h1, sq_abs (multIncr Chebyshev.psi δ (x + y)),
      sq_nonneg (|multIncr Chebyshev.psi δ (x + y)| - δ * (x + y))]
  nlinarith [hmain, hsq]

end

end RHTower
