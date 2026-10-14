import GaloisForLFunctions.RHTower.TwistedArcStreamMoment

/-!
# The Stokes stream function of a finite Whittaker sum

For frequencies `k_i = 2π(i + 2)` and real coefficients `a_i` (`i < N`), the decaying Whittaker sum
`v = Σ a_i K₀(k_i y) cos(k_i x)` solves `div(y ∇v) = 0`, the axisymmetric Laplace equation.  Its
Stokes stream function (`∇ψ = y J∇v`) is

`ψ(x, y) = Σ a_i y K₁(k_i y) sin(k_i x)`   (`whStream`).

* `ψ` solves the stream equation `y (ψ_xx + ψ_yy) − ψ_y = 0` (`whStream_pde`), from
  `d/dy [y K₁(ky)] = −k y K₀(ky)` (`hasDerivAt_mul_kMoment_one`, Bessel's equation `kMoment_ode`).
* `ψ = 0` on the walls `x = 0` and `x = ½` (`whStream_zero`, `whStream_half`), since
  `sin(k_i/2) = sin(π(i+2)) = 0`, and `ψ → 0` uniformly as `y → ∞` (`exists_abs_whStream_le`).
* Along the outward ray through the arc point `(c, √(1 − c²))` its derivative is the arc flux
  `G(c) = Σ a_i (1 − c²) S_{k_i}(c)` (`hasDerivAt_whStream_ray`, `arcStreamFlux`), where
  `S_k(c) = d/dc [K₀(k√(1 − c²)) cos(kc)]` is the arc Whittaker slope.
* At the corner `ρ = ½ + i√3/2`: `ψ_x(ρ) = 2 G(½)` (`whStreamX_half_eq`) and
  `∂_y ψ_x(ρ) = √3 (G'(½) − 2 G(½))` (`hasDerivAt_arcStreamFlux_half`, `whStreamXY_half_eq`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### `y K₁(ky)` and `y K₀(ky)` -/

theorem kMoment_two_eq {r : ℝ} (hr : 0 < r) : kMoment 2 r = kMoment 0 r + kMoment 1 r / r := by
  have := kMoment_ode hr
  field_simp
  linarith

theorem hasDerivAt_kMoment_comp_mul (j : ℕ) {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (fun y => kMoment j (k * y)) (-kMoment (j + 1) (k * y) * k) y := by
  have h1 : HasDerivAt (fun y : ℝ => k * y) k y := by simpa using (hasDerivAt_id y).const_mul k
  exact (hasDerivAt_kMoment j (mul_pos hk hy)).comp y h1

/-- `d/dy [y K₁(ky)] = −k y K₀(ky)`. -/
theorem hasDerivAt_mul_kMoment_one {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (fun y => y * kMoment 1 (k * y)) (-(k * y * kMoment 0 (k * y))) y := by
  have h := (hasDerivAt_id y).mul (hasDerivAt_kMoment_comp_mul 1 hk hy)
  refine h.congr_deriv ?_
  have hky : 0 < k * y := mul_pos hk hy
  rw [show (1 + 1 : ℕ) = 2 by rfl, kMoment_two_eq hky]
  simp only [id]
  field_simp
  ring

/-- `d/dy [−k y K₀(ky)] = −k K₀(ky) + k² y K₁(ky)`. -/
theorem hasDerivAt_neg_mul_kMoment_zero {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (fun y => -(k * y * kMoment 0 (k * y)))
      (-(k * kMoment 0 (k * y)) + k ^ 2 * y * kMoment 1 (k * y)) y := by
  have h := (((hasDerivAt_id y).const_mul k).mul (hasDerivAt_kMoment_comp_mul 0 hk hy)).neg
  refine h.congr_deriv ?_
  simp only [id, zero_add]
  ring

/-! ### One mode -/

/-- `y K₁(ky) sin(kx)`. -/
def modeStream (k x y : ℝ) : ℝ := y * kMoment 1 (k * y) * Real.sin (k * x)
/-- Its `x`-derivative. -/
def modeStreamX (k x y : ℝ) : ℝ := y * kMoment 1 (k * y) * (k * Real.cos (k * x))
/-- Its second `x`-derivative. -/
def modeStreamXX (k x y : ℝ) : ℝ := y * kMoment 1 (k * y) * (-(k ^ 2) * Real.sin (k * x))
/-- Its `y`-derivative. -/
def modeStreamY (k x y : ℝ) : ℝ := -(k * y * kMoment 0 (k * y)) * Real.sin (k * x)
/-- Its second `y`-derivative. -/
def modeStreamYY (k x y : ℝ) : ℝ :=
  (-(k * kMoment 0 (k * y)) + k ^ 2 * y * kMoment 1 (k * y)) * Real.sin (k * x)
/-- The mixed derivative `∂_y ∂_x`. -/
def modeStreamXY (k x y : ℝ) : ℝ := -(k * y * kMoment 0 (k * y)) * (k * Real.cos (k * x))

theorem hasDerivAt_modeStream_x (k x y : ℝ) :
    HasDerivAt (fun s => modeStream k s y) (modeStreamX k x y) x := by
  have h : HasDerivAt (fun s => Real.sin (k * s)) (Real.cos (k * x) * k) x := by
    simpa using ((hasDerivAt_id x).const_mul k).sin
  unfold modeStream modeStreamX
  exact (h.const_mul _).congr_deriv (by ring)

theorem hasDerivAt_modeStreamX_x (k x y : ℝ) :
    HasDerivAt (fun s => modeStreamX k s y) (modeStreamXX k x y) x := by
  have h : HasDerivAt (fun s => Real.cos (k * s)) (-Real.sin (k * x) * k) x := by
    simpa using ((hasDerivAt_id x).const_mul k).cos
  unfold modeStreamX modeStreamXX
  exact ((h.const_mul k).const_mul _).congr_deriv (by ring)

theorem hasDerivAt_modeStream_y {k : ℝ} (hk : 0 < k) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => modeStream k x s) (modeStreamY k x y) y := by
  unfold modeStream modeStreamY
  exact (hasDerivAt_mul_kMoment_one hk hy).mul_const _

theorem hasDerivAt_modeStreamY_y {k : ℝ} (hk : 0 < k) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => modeStreamY k x s) (modeStreamYY k x y) y := by
  unfold modeStreamY modeStreamYY
  exact (hasDerivAt_neg_mul_kMoment_zero hk hy).mul_const _

theorem hasDerivAt_modeStreamX_y {k : ℝ} (hk : 0 < k) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => modeStreamX k x s) (modeStreamXY k x y) y := by
  unfold modeStreamX modeStreamXY
  exact (hasDerivAt_mul_kMoment_one hk hy).mul_const _

theorem modeStream_pde (k x y : ℝ) :
    y * (modeStreamXX k x y + modeStreamYY k x y) - modeStreamY k x y = 0 := by
  unfold modeStreamXX modeStreamYY modeStreamY
  ring

/-- The ray derivative through `(x, y)`: `x ψ_x + y ψ_y`. -/
theorem hasDerivAt_modeStream_ray {k : ℝ} (hk : 0 < k) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => modeStream k ((1 + t) * x) ((1 + t) * y))
      (x * modeStreamX k x y + y * modeStreamY k x y) 0 := by
  have hr : HasDerivAt (fun t : ℝ => (1 + t) * y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const y
  have hΦ := (hasDerivAt_mul_kMoment_one hk (show 0 < (1 + 0) * y by simpa using hy)).comp 0 hr
  have hs : HasDerivAt (fun t : ℝ => Real.sin (k * ((1 + t) * x)))
      (Real.cos (k * x) * (k * x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => k * ((1 + t) * x)) (k * x) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const x).const_mul k
    simpa using h1.sin
  have h := hΦ.mul hs
  unfold modeStream modeStreamX modeStreamY
  refine h.congr_deriv ?_
  simp only [add_zero, one_mul, Function.comp]
  ring

/-! ### The finite sum -/

/-- The frequency `k_i = 2π(i + 2)` of the twisted moment `M_i`. -/
def streamFreq (i : ℕ) : ℝ := arcFreq (i + 1)

theorem streamFreq_pos (i : ℕ) : 0 < streamFreq i := arcFreq_pos _

theorem streamFreq_half (i : ℕ) : streamFreq i * (1 / 2) = ((i + 2 : ℕ) : ℝ) * Real.pi := by
  unfold streamFreq arcFreq; push_cast; ring

theorem sin_streamFreq_half (i : ℕ) : Real.sin (streamFreq i * (1 / 2)) = 0 := by
  rw [streamFreq_half, Real.sin_nat_mul_pi]

variable {N : ℕ}

/-- `ψ(x, y) = Σ a_i y K₁(k_i y) sin(k_i x)`. -/
def whStream (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStream (streamFreq i) x y
/-- `ψ_x`. -/
def whStreamX (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStreamX (streamFreq i) x y
/-- `ψ_xx`. -/
def whStreamXX (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStreamXX (streamFreq i) x y
/-- `ψ_y`. -/
def whStreamY (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStreamY (streamFreq i) x y
/-- `ψ_yy`. -/
def whStreamYY (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStreamYY (streamFreq i) x y
/-- `∂_y ψ_x`. -/
def whStreamXY (a : Fin N → ℝ) (x y : ℝ) : ℝ := ∑ i, a i * modeStreamXY (streamFreq i) x y

theorem hasDerivAt_whStream_x (a : Fin N → ℝ) (x y : ℝ) :
    HasDerivAt (fun s => whStream a s y) (whStreamX a x y) x := by
  unfold whStream whStreamX
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_modeStream_x _ x y).const_mul (a i)

theorem hasDerivAt_whStreamX_x (a : Fin N → ℝ) (x y : ℝ) :
    HasDerivAt (fun s => whStreamX a s y) (whStreamXX a x y) x := by
  unfold whStreamX whStreamXX
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_modeStreamX_x _ x y).const_mul (a i)

theorem hasDerivAt_whStream_y (a : Fin N → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => whStream a x s) (whStreamY a x y) y := by
  unfold whStream whStreamY
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_modeStream_y (streamFreq_pos i) x hy).const_mul (a i)

theorem hasDerivAt_whStreamY_y (a : Fin N → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => whStreamY a x s) (whStreamYY a x y) y := by
  unfold whStreamY whStreamYY
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_modeStreamY_y (streamFreq_pos i) x hy).const_mul (a i)

theorem hasDerivAt_whStreamX_y (a : Fin N → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun s => whStreamX a x s) (whStreamXY a x y) y := by
  unfold whStreamX whStreamXY
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_modeStreamX_y (streamFreq_pos i) x hy).const_mul (a i)

theorem whStream_pde (a : Fin N → ℝ) (x y : ℝ) :
    y * (whStreamXX a x y + whStreamYY a x y) - whStreamY a x y = 0 := by
  unfold whStreamXX whStreamYY whStreamY
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun i _ => by
    have := modeStream_pde (streamFreq i) x y
    linear_combination a i * this

theorem hasDerivAt_whStream_ray (a : Fin N → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => whStream a ((1 + t) * x) ((1 + t) * y))
      (x * whStreamX a x y + y * whStreamY a x y) 0 := by
  unfold whStream whStreamX whStreamY
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) fun i _ =>
    (hasDerivAt_modeStream_ray (streamFreq_pos i) x hy).const_mul (a i)
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem whStream_zero (a : Fin N → ℝ) (y : ℝ) : whStream a 0 y = 0 := by
  unfold whStream modeStream
  simp

theorem whStream_half (a : Fin N → ℝ) (y : ℝ) : whStream a (1 / 2) y = 0 := by
  unfold whStream modeStream
  exact Finset.sum_eq_zero fun i _ => by rw [sin_streamFreq_half]; ring

theorem continuousOn_whStream (a : Fin N → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => whStream a p.1 p.2) {p | 0 < p.2} := by
  intro p hp
  have hk : ∀ i : Fin N, ContinuousAt (fun q : ℝ × ℝ => kMoment 1 (streamFreq i * q.2)) p := by
    intro i
    have hpos : 0 < streamFreq i * p.2 := mul_pos (streamFreq_pos i) hp
    exact ContinuousAt.comp (g := kMoment 1) (f := fun q : ℝ × ℝ => streamFreq i * q.2)
      ((continuousOn_kMoment 1 (streamFreq i * p.2) hpos).continuousAt (Ioi_mem_nhds hpos))
      (by fun_prop)
  unfold whStream modeStream
  refine ContinuousAt.continuousWithinAt ?_
  refine tendsto_finsetSum _ fun i _ => ?_
  have := hk i
  have hc : ContinuousAt (fun q : ℝ × ℝ => a i * (q.2 * kMoment 1 (streamFreq i * q.2) *
      Real.sin (streamFreq i * q.1))) p := by fun_prop
  exact hc

/-- **Decay.** `ψ → 0` uniformly as `y → ∞`. -/
theorem exists_abs_whStream_le (a : Fin N → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Y, ∀ x y, Y ≤ y → |whStream a x y| ≤ δ := by
  set A := ∑ i, |a i| * (kMoment 1 (streamFreq i) * Real.exp 1) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (kMoment_nonneg _ _) (Real.exp_pos 1).le)
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  obtain ⟨Y₀, hY₀⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < δ / (A + 1) by positivity)))
    |>.exists_forall_of_atTop
  refine ⟨max Y₀ 1, fun x y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hyY : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hE := hY₀ y hyY
  simp only [pow_one] at hE
  have hterm : ∀ i : Fin N, |a i * modeStream (streamFreq i) x y| ≤
      |a i| * (kMoment 1 (streamFreq i) * Real.exp 1) * (y * Real.exp (-y)) := by
    intro i
    have hk := streamFreq_pos i
    have hk1 : 1 ≤ streamFreq i := by
      have := two_pi_le_arcFreq (i + 1); unfold streamFreq; linarith [Real.pi_gt_three]
    have hK := kMoment_le_exp_mul 1 hk (show streamFreq i ≤ streamFreq i * y by nlinarith)
    have hexp : Real.exp (-(streamFreq i * y - streamFreq i)) ≤ Real.exp 1 * Real.exp (-y) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    unfold modeStream
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < y),
      abs_of_nonneg (kMoment_nonneg _ _)]
    have hs := Real.abs_sin_le_one (streamFreq i * x)
    have hKn := kMoment_nonneg 1 (streamFreq i)
    calc |a i| * (y * kMoment 1 (streamFreq i * y) * |Real.sin (streamFreq i * x)|)
        ≤ |a i| * (y * (Real.exp (-(streamFreq i * y - streamFreq i)) *
            kMoment 1 (streamFreq i)) * 1) := by
          gcongr
      _ ≤ |a i| * (y * ((Real.exp 1 * Real.exp (-y)) * kMoment 1 (streamFreq i)) * 1) := by
          gcongr
      _ = _ := by ring
  calc |whStream a x y| ≤ ∑ i, |a i * modeStream (streamFreq i) x y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * (kMoment 1 (streamFreq i) * Real.exp 1) * (y * Real.exp (-y)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = A * (y * Real.exp (-y)) := by rw [hA, Finset.sum_mul]
    _ ≤ A * (δ / (A + 1)) := mul_le_mul_of_nonneg_left hE.le hA0
    _ ≤ δ := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith

/-! ### The arc flux -/

/-- `G(c) = Σ a_i (1 − c²) S_{k_i}(c)`. -/
def arcStreamFlux (a : Fin N → ℝ) (c : ℝ) : ℝ :=
  ∑ i, a i * ((1 - c ^ 2) * arcWhittakerSlope (streamFreq i) c)

theorem modeStream_ray_eq_flux (k : ℝ) {c : ℝ} (hc : |c| < 1) :
    c * modeStreamX k c (modularArcHeight c) +
      modularArcHeight c * modeStreamY k c (modularArcHeight c) =
      (1 - c ^ 2) * arcWhittakerSlope k c := by
  have hy := modularArcHeight_pos_of_abs_lt hc
  have hy2 := modularArcHeight_sq_of_abs_lt hc
  unfold modeStreamX modeStreamY arcWhittakerSlope
  rw [← hy2]
  field_simp
  ring

/-- The ray derivative of `ψ` at the arc point `(c, √(1 − c²))` is the arc flux `G(c)`. -/
theorem whStream_ray_eq_flux (a : Fin N → ℝ) {c : ℝ} (hc : |c| < 1) :
    c * whStreamX a c (modularArcHeight c) +
      modularArcHeight c * whStreamY a c (modularArcHeight c) =
      arcStreamFlux a c := by
  unfold whStreamX whStreamY arcStreamFlux
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    have := modeStream_ray_eq_flux (streamFreq i) hc
    linear_combination a i * this

end

end RHTower
