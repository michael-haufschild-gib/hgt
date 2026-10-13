import GaloisForLFunctions.RHTower.FiniteLevelDecayWitness

/-!
# Atomic pole filters: decay-class generators from five dilations

For an arc point `u + iy` let `ψ_u` be the symmetric pair of `s = ½` Poisson vectors
(`arcPairVector`) and `Q_u(v) = e^{v/2} ψ_u(e^v)` its log-scale profile. Dilation by `e^w` acts by
`D_w ψ(x) = e^{−w/2} ψ(x e^{−w})` (`dilatedArcPair`), and shifts the profile: `Q_u(v − w)`.

For `b > 0`, `C = cosh(b/2)`, put `c = (δ_b + δ_{−b})/(2C)` and `m = δ − 2c + c ⋆ c`, i.e. the five weights
`m₀ = 1 + 1/(2C²)`, `m_{±b} = −1/C`, `m_{±2b} = 1/(4C²)`. The **atomic generator**

`h_{b,u} = m₀ ψ_u + m_{b}(D_b + D_{−b})ψ_u + m_{2b}(D_{2b} + D_{−2b})ψ_u`  (`atomicArcVector`)

is a finite superposition of Poisson vectors at the ten points `e^{jb}(±u + iy)`, `|j| ≤ 2`.

* `m̂(τ) = (1 − cos(bτ)/C)² > 0` (`atomicWeight_cos`), so the profile is strictly positive definite
  (`integral_cos_mul_atomicArcProfile_pos`).
* `Σ m_j e^{λ w_j} = (1 − cosh(λb)/C)²` (`atomicWeight_exp`). It vanishes doubly at `λ = ±½`, so the
  edge term `2√y e^{−|v|/2}` of `Q_u` cancels exactly. Hence `|e^{v/2} h(e^v)| ≤ C_b e^{−3|v|/2}`
  (`abs_atomicArcProfile_le`) and `∫ h = 0` (`integral_atomicArcVector_eq_zero`).
* Its sine moments are `Σ_j m_j e^{−w_j/2} J_u(c e^{w_j})` (`integral_atomicArcDeriv_mul_sin`).
  They lie within `4√(π/2) √c · 3/C` of `J_u(c)` uniformly on the arc
  (`abs_integral_atomicArcDeriv_mul_sin_sub_le`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Dilated arc pairs -/

/-- The dilate `e^{−w/2} ψ_u(x e^{−w})`. -/
def dilatedArcPair (u : ArcParam) (w x : ℝ) : ℝ :=
  Real.exp (-(w / 2)) * arcPairVector u (x * Real.exp (-w))

/-- Its derivative `e^{−3w/2} ψ_u'(x e^{−w})`. -/
def dilatedArcPairDeriv (u : ArcParam) (w x : ℝ) : ℝ :=
  Real.exp (-(3 * w / 2)) * arcPairDeriv u (x * Real.exp (-w))

theorem continuous_dilatedArcPair (u : ArcParam) (w : ℝ) : Continuous (dilatedArcPair u w) :=
  continuous_const.mul ((continuous_arcPairVector u).comp (by fun_prop))

theorem continuous_dilatedArcPairDeriv (u : ArcParam) (w : ℝ) :
    Continuous (dilatedArcPairDeriv u w) :=
  continuous_const.mul ((continuous_arcPairDeriv u).comp (by fun_prop))

theorem hasDerivAt_dilatedArcPair (u : ArcParam) (w x : ℝ) :
    HasDerivAt (dilatedArcPair u w) (dilatedArcPairDeriv u w x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * Real.exp (-w)) (Real.exp (-w)) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.exp (-w))
  have h := ((hasDerivAt_arcPairVector u (x * Real.exp (-w))).comp x hc).const_mul
    (Real.exp (-(w / 2)))
  refine h.congr_deriv ?_
  have he : Real.exp (-(w / 2)) * Real.exp (-w) = Real.exp (-(3 * w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold dilatedArcPairDeriv
  rw [← he]; ring

theorem dilatedArcPair_neg (u : ArcParam) (w x : ℝ) :
    dilatedArcPair u w (-x) = dilatedArcPair u w x := by
  unfold dilatedArcPair; rw [neg_mul, arcPairVector_neg]

theorem dilatedArcPair_inv (u : ArcParam) (w : ℝ) {x : ℝ} (hx : x ≠ 0) :
    dilatedArcPair u w (1 / x) = |x| * dilatedArcPair u (-w) x := by
  have hxe : x * Real.exp w ≠ 0 := mul_ne_zero hx (Real.exp_pos w).ne'
  have e1 : 1 / x * Real.exp (-w) = 1 / (x * Real.exp w) := by rw [Real.exp_neg]; field_simp
  unfold dilatedArcPair
  rw [e1, arcPairVector_inv u hxe, abs_mul, abs_of_pos (Real.exp_pos w), neg_neg]
  have e2 : Real.exp (-(w / 2)) * Real.exp w = Real.exp (-(-w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← e2]; ring

theorem exp_half_mul_dilatedArcPair (u : ArcParam) (w v : ℝ) :
    Real.exp (v / 2) * dilatedArcPair u w (Real.exp v) = arcPairProfile u (v - w) := by
  unfold dilatedArcPair arcPairProfile
  have e1 : Real.exp v * Real.exp (-w) = Real.exp (v - w) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * Real.exp (-(w / 2)) = Real.exp ((v - w) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, ← e2]; ring

theorem abs_dilatedArcPairDeriv_le (u : ArcParam) (w x : ℝ) :
    |dilatedArcPairDeriv u w x| ≤
      64 * Real.exp (-(3 * w / 2)) * (1 + (x * Real.exp (-w)) ^ 2)⁻¹ := by
  unfold dilatedArcPairDeriv
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (abs_arcPairDeriv_le u _) (Real.exp_pos _).le

theorem integrable_dilatedArcPairDeriv (u : ArcParam) (w : ℝ) :
    Integrable (dilatedArcPairDeriv u w) :=
  ((integrable_inv_one_add_sq.comp_mul_right' (Real.exp_pos (-w)).ne').const_mul
    (64 * Real.exp (-(3 * w / 2)))).mono' (continuous_dilatedArcPairDeriv u w).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_dilatedArcPairDeriv_le u w x)

theorem integral_dilatedArcPairDeriv_mul_sin (u : ArcParam) (w : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ x, dilatedArcPairDeriv u w x * Real.sin (c * x) =
      Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w) := by
  have e : (fun x => dilatedArcPairDeriv u w x * Real.sin (c * x)) = fun x =>
      Real.exp (-(3 * w / 2)) * (arcPairDeriv u (x * Real.exp (-w)) *
        Real.sin (c * Real.exp w * (x * Real.exp (-w)))) := by
    funext x
    have : c * Real.exp w * (x * Real.exp (-w)) = c * x := by rw [Real.exp_neg]; field_simp
    simp only [dilatedArcPairDeriv]; rw [this]; ring
  rw [e, integral_const_mul]
  have hcv := Measure.integral_comp_mul_right
    (fun t : ℝ => arcPairDeriv u t * Real.sin (c * Real.exp w * t)) (Real.exp (-w))
  rw [hcv, integral_arcPairDeriv_mul_sin u (by positivity), abs_of_pos (inv_pos.mpr
    (Real.exp_pos _)), smul_eq_mul, ← Real.exp_neg, neg_neg]
  have : Real.exp (-(3 * w / 2)) * Real.exp w = Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

/-! ### The five weights -/

/-- `m₀ = 1 + 1/(2C²)`. -/
def atomW0 (b : ℝ) : ℝ := 1 + 1 / (2 * Real.cosh (b / 2) ^ 2)

/-- `m_{±b} = −1/C`. -/
def atomW1 (b : ℝ) : ℝ := -(1 / Real.cosh (b / 2))

/-- `m_{±2b} = 1/(4C²)`. -/
def atomW2 (b : ℝ) : ℝ := 1 / (4 * Real.cosh (b / 2) ^ 2)

/-- **The multiplier**: `m₀ + 2m_b cos(bτ) + 2m_{2b} cos(2bτ) = (1 − cos(bτ)/C)²`. -/
theorem atomicWeight_cos (b τ : ℝ) :
    atomW0 b + atomW1 b * (2 * Real.cos (b * τ)) + atomW2 b * (2 * Real.cos (2 * b * τ)) =
      (1 - Real.cos (b * τ) / Real.cosh (b / 2)) ^ 2 := by
  have hC := Real.cosh_pos (b / 2)
  rw [show 2 * b * τ = 2 * (b * τ) by ring, Real.cos_two_mul]
  unfold atomW0 atomW1 atomW2
  field_simp
  ring

/-- **The exponential tilt**: `Σ m_j e^{λ w_j} = (1 − cosh(λb)/C)²`. -/
theorem atomicWeight_exp (b l : ℝ) :
    atomW0 b + atomW1 b * (Real.exp (l * b) + Real.exp (l * -b)) +
      atomW2 b * (Real.exp (l * (2 * b)) + Real.exp (l * -(2 * b))) =
      (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 := by
  have hC := Real.cosh_pos (b / 2)
  have h1 : Real.exp (l * b) + Real.exp (l * -b) = 2 * Real.cosh (l * b) := by
    rw [Real.cosh_eq, mul_neg]; ring
  have h2 : Real.exp (l * (2 * b)) + Real.exp (l * -(2 * b)) =
      2 * (2 * Real.cosh (l * b) ^ 2 - 1) := by
    have hc2 : Real.cosh (2 * (l * b)) = 2 * Real.cosh (l * b) ^ 2 - 1 := by
      rw [Real.cosh_two_mul, Real.sinh_sq]; ring
    rw [← hc2, Real.cosh_eq, show 2 * (l * b) = l * (2 * b) by ring, mul_neg]; ring
  rw [h1, h2]
  unfold atomW0 atomW1 atomW2
  field_simp
  ring

/-- The weighted edge sums vanish: `Σ m_j e^{± w_j / 2} = 0`. -/
theorem atomicWeight_edge (b σ : ℝ) (hσ : σ = 1 / 2 ∨ σ = -(1 / 2)) :
    atomW0 b + atomW1 b * (Real.exp (σ * b) + Real.exp (σ * -b)) +
      atomW2 b * (Real.exp (σ * (2 * b)) + Real.exp (σ * -(2 * b))) = 0 := by
  rw [atomicWeight_exp]
  have hC := Real.cosh_pos (b / 2)
  have : Real.cosh (σ * b) = Real.cosh (b / 2) := by
    rcases hσ with rfl | rfl
    · congr 1; ring
    · rw [show -(1 / 2) * b = -(b / 2) by ring, Real.cosh_neg]
  rw [this, div_self hC.ne', sub_self]; norm_num

/-! ### The atomic generator -/

/-- The atomic generator `h_{b,u}`. -/
def atomicArcVector (b : ℝ) (u : ArcParam) (x : ℝ) : ℝ :=
  atomW0 b * dilatedArcPair u 0 x + atomW1 b * (dilatedArcPair u b x + dilatedArcPair u (-b) x) +
    atomW2 b * (dilatedArcPair u (2 * b) x + dilatedArcPair u (-(2 * b)) x)

/-- Its derivative. -/
def atomicArcDeriv (b : ℝ) (u : ArcParam) (x : ℝ) : ℝ :=
  atomW0 b * dilatedArcPairDeriv u 0 x +
    atomW1 b * (dilatedArcPairDeriv u b x + dilatedArcPairDeriv u (-b) x) +
    atomW2 b * (dilatedArcPairDeriv u (2 * b) x + dilatedArcPairDeriv u (-(2 * b)) x)

/-- Its profile `Σ m_j Q_u(v − w_j)`. -/
def atomicArcProfile (b : ℝ) (u : ArcParam) (v : ℝ) : ℝ :=
  atomW0 b * arcPairProfile u v + atomW1 b * (arcPairProfile u (v - b) + arcPairProfile u (v + b)) +
    atomW2 b * (arcPairProfile u (v - 2 * b) + arcPairProfile u (v + 2 * b))

theorem hasDerivAt_atomicArcVector (b : ℝ) (u : ArcParam) (x : ℝ) :
    HasDerivAt (atomicArcVector b u) (atomicArcDeriv b u x) x := by
  unfold atomicArcVector atomicArcDeriv
  exact (((hasDerivAt_dilatedArcPair u 0 x).const_mul _).add
    (((hasDerivAt_dilatedArcPair u b x).add (hasDerivAt_dilatedArcPair u (-b) x)).const_mul _)).add
    (((hasDerivAt_dilatedArcPair u (2 * b) x).add
      (hasDerivAt_dilatedArcPair u (-(2 * b)) x)).const_mul _)

theorem continuous_atomicArcVector (b : ℝ) (u : ArcParam) : Continuous (atomicArcVector b u) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_atomicArcVector b u x).continuousAt

theorem atomicArcVector_neg (b : ℝ) (u : ArcParam) (x : ℝ) :
    atomicArcVector b u (-x) = atomicArcVector b u x := by
  simp only [atomicArcVector, dilatedArcPair_neg]

theorem atomicArcVector_inv (b : ℝ) (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    atomicArcVector b u (1 / x) = |x| * atomicArcVector b u x := by
  simp only [atomicArcVector, dilatedArcPair_inv u _ hx, neg_neg, neg_zero]
  ring

theorem exp_half_mul_atomicArcVector (b : ℝ) (u : ArcParam) (v : ℝ) :
    Real.exp (v / 2) * atomicArcVector b u (Real.exp v) = atomicArcProfile b u v := by
  unfold atomicArcVector atomicArcProfile
  simp only [mul_add, mul_left_comm (Real.exp (v / 2)), exp_half_mul_dilatedArcPair, sub_zero,
    sub_neg_eq_add]

theorem atomicArcProfile_neg (b : ℝ) (u : ArcParam) (v : ℝ) :
    atomicArcProfile b u (-v) = atomicArcProfile b u v := by
  unfold atomicArcProfile
  rw [arcPairProfile_neg, show -v - b = -(v + b) by ring, show -v + b = -(v - b) by ring,
    show -v - 2 * b = -(v + 2 * b) by ring, show -v + 2 * b = -(v - 2 * b) by ring,
    arcPairProfile_neg, arcPairProfile_neg, arcPairProfile_neg, arcPairProfile_neg]
  ring

theorem continuous_atomicArcProfile (b : ℝ) (u : ArcParam) : Continuous (atomicArcProfile b u) := by
  have h := continuous_arcPairProfile u
  unfold atomicArcProfile
  exact ((continuous_const.mul h).add (continuous_const.mul ((h.comp (by fun_prop)).add
    (h.comp (by fun_prop))))).add (continuous_const.mul ((h.comp (by fun_prop)).add
      (h.comp (by fun_prop))))

/-! ### Strict positive definiteness -/

theorem integrable_cos_mul_arcPairProfile_sub (u : ArcParam) (τ w : ℝ) :
    Integrable fun v => Real.cos (τ * v) * arcPairProfile u (v - w) :=
  ((integrable_arcPairProfile u).comp_sub_right w).bdd_mul (by fun_prop)
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The five shifts `0, ±b, ±2b`. -/
def atomShift (b : ℝ) : Fin 5 → ℝ := ![0, b, -b, 2 * b, -(2 * b)]

/-- The five weights. -/
def atomWeight (b : ℝ) : Fin 5 → ℝ := ![atomW0 b, atomW1 b, atomW1 b, atomW2 b, atomW2 b]

theorem atomicArcProfile_eq_sum (b : ℝ) (u : ArcParam) (v : ℝ) :
    atomicArcProfile b u v = ∑ j, atomWeight b j * arcPairProfile u (v - atomShift b j) := by
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, atomicArcProfile, sub_zero, sub_neg_eq_add]
  ring

theorem atomWeight_cos_sum (b τ : ℝ) :
    ∑ j, atomWeight b j * Real.cos (τ * atomShift b j) =
      (1 - Real.cos (b * τ) / Real.cosh (b / 2)) ^ 2 := by
  rw [← atomicWeight_cos]
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, Real.cos_zero, mul_neg, Real.cos_neg]
  rw [show τ * b = b * τ by ring, show τ * (2 * b) = 2 * b * τ by ring]
  ring

/-- **The atomic generator is strictly positive definite.** -/
theorem integral_cos_mul_atomicArcProfile (b : ℝ) (u : ArcParam) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * atomicArcProfile b u v =
      (1 - Real.cos (b * τ) / Real.cosh (b / 2)) ^ 2 *
        ∫ v, Real.cos (τ * v) * arcPairProfile u v := by
  have hi := integrable_cos_mul_arcPairProfile_sub u τ
  have e : ∀ v, Real.cos (τ * v) * atomicArcProfile b u v =
      ∑ j, atomWeight b j * (Real.cos (τ * v) * arcPairProfile u (v - atomShift b j)) := fun v => by
    rw [atomicArcProfile_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  simp_rw [integral_const_mul, integral_cos_mul_arcPairProfile_shift]
  rw [← atomWeight_cos_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem integral_cos_mul_atomicArcProfile_pos {b : ℝ} (hb : 0 < b) (u : ArcParam) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * atomicArcProfile b u v := by
  rw [integral_cos_mul_atomicArcProfile]
  refine mul_pos ?_ ?_
  · have hC : 1 < Real.cosh (b / 2) := Real.one_lt_cosh.mpr (by positivity)
    have h1 : Real.cos (b * τ) / Real.cosh (b / 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [Real.cos_le_one (b * τ)]
    have := sub_pos.mpr h1
    positivity
  · have hc : |(u : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith [u.2.1, u.2.2]
    have e : (fun v => Real.cos (τ * v) * arcPairProfile u v) = fun v =>
        Real.sqrt (modularArcHeight u / 2) * (Real.cos (τ * v) * symCoshKernel u v) := by
      funext v; rw [arcPairProfile_eq]; ring
    rw [e, integral_const_mul]
    exact mul_pos (Real.sqrt_pos.mpr (by have := modularArcHeight_pos u.2; positivity))
      (integral_cos_mul_symCoshKernel_pos hc τ)

end

end RHTower
