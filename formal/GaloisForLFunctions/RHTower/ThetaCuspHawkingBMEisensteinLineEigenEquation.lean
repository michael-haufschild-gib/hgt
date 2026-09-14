import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinModeJetMajorants
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualCanonicalMaassWeld

/-!
# The eigen-equation of the completed Eisenstein Fourier model at every height and parameter

The Fourier model `E*(u; x, Y) = constant part + 2 (tail₊ + tail₋)` is differentiated termwise in
`x` and in `Y` at every height `Y > 0` and every parameter `u`: the all-heights majorants of the
mode jets make the series of termwise derivatives locally uniformly convergent, so
`hasDerivAt_tsum_of_isPreconnected` applies (on `ℝ` in `x`, on `(Y/2, 2Y)` in `Y`).  Summing the
per-mode eigen-equations and adding the elementary constant-part identity gives

`Y² (∂²_x E* + ∂²_Y E*) = (u² − 1/4) E*`

for every `u ∈ ℂ` and every `(x, Y)` with `Y > 0`.  No parameter restriction and no identity
theorem is needed: the eigen-equation is termwise.  The model is identified with the corpus cusp
leg `d4BMCompletedEisensteinCuspLeg .scalar u x Y`.
-/

open Real Set

namespace RHTower

noncomputable section

/-! ## The weighted signed tails and their termwise derivatives -/

/-- The Whittaker coefficient of the `N`-th mode. -/
def modeCoefficient (u : ℂ) (N : ℕ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩

/-- The signed weighted tail `Σ_N a_N(u) · mode_N`. -/
def weightedTail (u : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ, modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y

/-- Termwise `∂_x` of the weighted tail. -/
def weightedTailX (u : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ, modeCoefficient u N * d4BMSignedWhittakerModeHorizontalFirstJet negative N u x Y

/-- Termwise `∂_Y` of the weighted tail. -/
def weightedTailY (u : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ, modeCoefficient u N * d4BMSignedWhittakerModeVerticalFirstJet negative N u x Y

/-- Termwise `∂²_x` of the weighted tail. -/
def weightedTailXX (u : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ, modeCoefficient u N * d4BMSignedWhittakerModeHorizontalSecondJet negative N u x Y

/-- Termwise `∂²_Y` of the weighted tail. -/
def weightedTailYY (u : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ, modeCoefficient u N * signedModeVerticalSecondJetR negative N u x Y

/-- The uniform majorant on the window, for a weighted family, uniformly in `x`. -/
theorem exists_majorant_of_windowDominatedX {Y₀ : ℝ} (hY₀ : 0 < Y₀) {d : ℕ}
    {f : ℕ → ℂ → ℝ → ℝ → ℂ} (u : ℂ) (hf : WindowDominatedX Y₀ ‖u‖ d f) :
    ∃ v : ℕ → ℝ, Summable v ∧ ∀ (N : ℕ) (x : ℝ), ∀ Y ∈ Icc (Y₀ / 2) (2 * Y₀),
      ‖modeCoefficient u N * f N u x Y‖ ≤ v N := by
  obtain ⟨K, hK, h⟩ := hf.weighted le_rfl
  refine ⟨fun N => K * (((N : ℝ) + 1) ^ (d + ⌈3 * ‖u‖ + 1⌉₊) *
    besselModeMajorant Y₀ (‖u‖ + 2) N),
    (summable_pow_mul_besselModeMajorant hY₀ (‖u‖ + 2) _).mul_left K, fun N x Y hY => ?_⟩
  have := h N x Y hY
  unfold modeCoefficient
  linarith [this]

theorem summable_weighted_of_windowDominatedX {Y₀ : ℝ} (hY₀ : 0 < Y₀) {d : ℕ}
    {f : ℕ → ℂ → ℝ → ℝ → ℂ} (u : ℂ) (hf : WindowDominatedX Y₀ ‖u‖ d f) (x : ℝ) {Y : ℝ}
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) :
    Summable fun N : ℕ => modeCoefficient u N * f N u x Y := by
  obtain ⟨v, hv, hvb⟩ := exists_majorant_of_windowDominatedX hY₀ u hf
  exact Summable.of_norm_bounded hv fun N => hvb N x Y hY

theorem mem_window_self {Y : ℝ} (hY : 0 < Y) : Y ∈ Icc (Y / 2) (2 * Y) :=
  ⟨by linarith, by linarith⟩

theorem summable_weightedTail (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun N : ℕ => modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y :=
  summable_weighted_of_windowDominatedX hY u (windowDominatedX_mode hY negative) x
    (mem_window_self hY)

theorem summable_weightedTailX (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun N : ℕ =>
      modeCoefficient u N * d4BMSignedWhittakerModeHorizontalFirstJet negative N u x Y :=
  summable_weighted_of_windowDominatedX hY u (windowDominatedX_mode_horizontalFirst hY negative) x
    (mem_window_self hY)

theorem summable_weightedTailY (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun N : ℕ =>
      modeCoefficient u N * d4BMSignedWhittakerModeVerticalFirstJet negative N u x Y :=
  summable_weighted_of_windowDominatedX hY u (windowDominatedX_mode_verticalFirst hY negative) x
    (mem_window_self hY)

theorem summable_weightedTailXX (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun N : ℕ =>
      modeCoefficient u N * d4BMSignedWhittakerModeHorizontalSecondJet negative N u x Y :=
  summable_weighted_of_windowDominatedX hY u (windowDominatedX_mode_horizontalSecond hY negative) x
    (mem_window_self hY)

theorem summable_weightedTailYY (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun N : ℕ => modeCoefficient u N * signedModeVerticalSecondJetR negative N u x Y :=
  summable_weighted_of_windowDominatedX hY u (windowDominatedX_mode_verticalSecondR hY negative) x
    (mem_window_self hY)

/-- `∂_x` of the weighted tail is the termwise derivative. -/
theorem hasDerivAt_weightedTail_x (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => weightedTail u negative q Y) (weightedTailX u negative x Y) x := by
  obtain ⟨v, hv, hvb⟩ := exists_majorant_of_windowDominatedX hY u
    (windowDominatedX_mode_horizontalFirst hY negative)
  refine hasDerivAt_tsum_of_isPreconnected hv isOpen_univ isPreconnected_univ
    (fun N q _ => (hasDerivAt_d4BMSignedWhittakerMode_horizontal negative N u q Y).const_mul
      (modeCoefficient u N))
    (fun N q _ => hvb N q Y (mem_window_self hY)) (Set.mem_univ x)
    (summable_weightedTail u negative x hY) (Set.mem_univ x)

/-- `∂²_x` of the weighted tail is the termwise second derivative. -/
theorem hasDerivAt_weightedTailX_x (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => weightedTailX u negative q Y) (weightedTailXX u negative x Y) x := by
  obtain ⟨v, hv, hvb⟩ := exists_majorant_of_windowDominatedX hY u
    (windowDominatedX_mode_horizontalSecond hY negative)
  refine hasDerivAt_tsum_of_isPreconnected hv isOpen_univ isPreconnected_univ
    (fun N q _ => (hasDerivAt_d4BMSignedWhittakerModeHorizontalFirstJet_horizontal negative N u q Y).const_mul
      (modeCoefficient u N))
    (fun N q _ => hvb N q Y (mem_window_self hY)) (Set.mem_univ x)
    (summable_weightedTailX u negative x hY) (Set.mem_univ x)

theorem window_open_mem {Y : ℝ} (hY : 0 < Y) : Y ∈ Ioo (Y / 2) (2 * Y) := ⟨by linarith, by linarith⟩

theorem window_of_mem_Ioo {Y q : ℝ} (hq : q ∈ Ioo (Y / 2) (2 * Y)) : q ∈ Icc (Y / 2) (2 * Y) :=
  ⟨hq.1.le, hq.2.le⟩

/-- `∂_Y` of the weighted tail is the termwise derivative. -/
theorem hasDerivAt_weightedTail_y (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => weightedTail u negative x q) (weightedTailY u negative x Y) Y := by
  obtain ⟨v, hv, hvb⟩ := exists_majorant_of_windowDominatedX hY u
    (windowDominatedX_mode_verticalFirst hY negative)
  refine hasDerivAt_tsum_of_isPreconnected hv isOpen_Ioo isPreconnected_Ioo
    (fun N q hq => ?_) (fun N q hq => hvb N x q (window_of_mem_Ioo hq)) (window_open_mem hY)
    (summable_weightedTail u negative x hY) (window_open_mem hY)
  have hqpos : 0 < q := lt_of_lt_of_le (by linarith) hq.1.le
  exact (hasDerivAt_d4BMSignedWhittakerMode_vertical negative N u x ⟨q, hqpos⟩).const_mul
    (modeCoefficient u N)

/-- `∂²_Y` of the weighted tail is the termwise second derivative. -/
theorem hasDerivAt_weightedTailY_y (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => weightedTailY u negative x q) (weightedTailYY u negative x Y) Y := by
  obtain ⟨v, hv, hvb⟩ := exists_majorant_of_windowDominatedX hY u
    (windowDominatedX_mode_verticalSecondR hY negative)
  refine hasDerivAt_tsum_of_isPreconnected hv isOpen_Ioo isPreconnected_Ioo
    (fun N q hq => ?_) (fun N q hq => hvb N x q (window_of_mem_Ioo hq)) (window_open_mem hY)
    (summable_weightedTailY u negative x hY) (window_open_mem hY)
  have hqpos : 0 < q := lt_of_lt_of_le (by linarith) hq.1.le
  have h := (hasDerivAt_d4BMSignedWhittakerModeVerticalFirstJet_vertical negative N u x
    ⟨q, hqpos⟩).const_mul (modeCoefficient u N)
  rw [← signedModeVerticalSecondJetR_eq] at h
  exact h

/-- **Eigen-equation of the weighted tail** at every height. -/
theorem weightedTail_eigen (u : ℂ) (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (weightedTailXX u negative x Y + weightedTailYY u negative x Y) =
      (u ^ 2 - 1 / 4) * weightedTail u negative x Y := by
  unfold weightedTailXX weightedTailYY weightedTail
  rw [← (summable_weightedTailXX u negative x hY).tsum_add (summable_weightedTailYY u negative x hY),
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun N => ?_
  have h := d4BM_signedWhittakerMode_secondJet_eigenEquation negative N u x ⟨Y, hY⟩
  rw [← signedModeVerticalSecondJetR_eq] at h
  linear_combination (modeCoefficient u N) * h

/-! ## The constant part -/

/-- `d/dY` of `Y^w` for real `Y > 0`. -/
theorem hasDerivAt_ofReal_cpow_const (w : ℂ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) ^ w)) (w * (Y : ℂ) ^ (w - 1)) Y := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ w) (w * (Y : ℂ) ^ (w - 1)) (Y : ℂ) := by
    have := (hasDerivAt_id (Y : ℂ)).cpow_const (c := w) (Or.inl (by simpa using hY))
    simpa using this
  exact h1.comp_ofReal

/-- `d/dY` of one constant Weyl term. -/
theorem hasDerivAt_cuspConstantTerm (u : ℂ) (ε : Bool) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => d4BMCompletedEisensteinCuspConstantTerm .scalar u ε q)
      (d4BMCompletedEisensteinCuspConstantFirstJetTerm u ε Y) Y := by
  unfold d4BMCompletedEisensteinCuspConstantTerm d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  simp only [mul_one]
  exact (hasDerivAt_ofReal_cpow_const _ hY).const_mul _

/-- `d/dY` of one constant first-jet term. -/
theorem hasDerivAt_cuspConstantFirstJetTerm (u : ℂ) (ε : Bool) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => d4BMCompletedEisensteinCuspConstantFirstJetTerm u ε q)
      (d4BMCompletedEisensteinCuspConstantSecondJetTerm u ε Y) Y := by
  unfold d4BMCompletedEisensteinCuspConstantFirstJetTerm
    d4BMCompletedEisensteinCuspConstantSecondJetTerm
  set w := d4BMCompletedEisensteinCuspWeylExponent u ε with hw
  have h := ((hasDerivAt_ofReal_cpow_const (w - 1) hY).const_mul w).const_mul
    (d4BMCompletedEisensteinCuspConstantCoefficient u ε)
  refine h.congr_deriv ?_
  rw [show w - 1 - 1 = w - 2 by ring]
  ring

/-- The `Y`-derivative of the constant part. -/
def constantPartY (u : ℂ) (Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantFirstJetTerm u false Y +
    d4BMCompletedEisensteinCuspConstantFirstJetTerm u true Y

/-- The second `Y`-derivative of the constant part. -/
def constantPartYY (u : ℂ) (Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantSecondJetTerm u false Y +
    d4BMCompletedEisensteinCuspConstantSecondJetTerm u true Y

theorem hasDerivAt_constantPart (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => d4BMCompletedEisensteinCuspConstantPart .scalar u q)
      (constantPartY u Y) Y := by
  unfold d4BMCompletedEisensteinCuspConstantPart constantPartY
  exact (hasDerivAt_cuspConstantTerm u false hY).add (hasDerivAt_cuspConstantTerm u true hY)

theorem hasDerivAt_constantPartY (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => constantPartY u q) (constantPartYY u Y) Y := by
  unfold constantPartY constantPartYY
  exact (hasDerivAt_cuspConstantFirstJetTerm u false hY).add
    (hasDerivAt_cuspConstantFirstJetTerm u true hY)

theorem constantPart_eigen (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * constantPartYY u Y =
      (u ^ 2 - 1 / 4) * d4BMCompletedEisensteinCuspConstantPart .scalar u Y := by
  have h := d4BM_cuspConstantFullSecondJet_eigenEquation u hY
  exact h

/-! ## The full Fourier model -/

/-- The Fourier model as constant part plus twice the two signed weighted tails. -/
def lineModel (u : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantPart .scalar u Y +
    2 * (weightedTail u false x Y + weightedTail u true x Y)

theorem weightedTail_eq_signedSqrtWhittakerTail (u : ℂ) (negative : Bool) (x Y : ℝ) :
    weightedTail u negative x Y =
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y := by
  unfold weightedTail d4BMCompletedEisensteinSignedSqrtWhittakerTail
  refine tsum_congr fun N => ?_
  unfold modeCoefficient d4BMSignedWhittakerMode d4BMWhittakerP0
  have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
  rw [hc]
  simp only [pow_zero, mul_one]
  ring

/-- The model equals the corpus cusp leg. -/
theorem lineModel_eq_cuspLeg (u : ℂ) (x Y : ℝ) :
    lineModel u x Y = d4BMCompletedEisensteinCuspLeg .scalar u x Y := by
  unfold lineModel d4BMCompletedEisensteinCuspLeg d4BMCompletedEisensteinCuspTailPart
    d4BMCompletedEisensteinFullSignedZeroWord
  rw [weightedTail_eq_signedSqrtWhittakerTail, weightedTail_eq_signedSqrtWhittakerTail]

def lineModelX (u : ℂ) (x Y : ℝ) : ℂ :=
  2 * (weightedTailX u false x Y + weightedTailX u true x Y)

def lineModelXX (u : ℂ) (x Y : ℝ) : ℂ :=
  2 * (weightedTailXX u false x Y + weightedTailXX u true x Y)

def lineModelY (u : ℂ) (x Y : ℝ) : ℂ :=
  constantPartY u Y + 2 * (weightedTailY u false x Y + weightedTailY u true x Y)

def lineModelYY (u : ℂ) (x Y : ℝ) : ℂ :=
  constantPartYY u Y + 2 * (weightedTailYY u false x Y + weightedTailYY u true x Y)

theorem hasDerivAt_lineModel_x (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => lineModel u q Y) (lineModelX u x Y) x := by
  unfold lineModel lineModelX
  have h := (((hasDerivAt_weightedTail_x u false x hY).add
    (hasDerivAt_weightedTail_x u true x hY)).const_mul (2 : ℂ)).const_add
    (d4BMCompletedEisensteinCuspConstantPart .scalar u Y)
  exact h

theorem hasDerivAt_lineModelX_x (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => lineModelX u q Y) (lineModelXX u x Y) x := by
  unfold lineModelX lineModelXX
  have h := ((hasDerivAt_weightedTailX_x u false x hY).add
    (hasDerivAt_weightedTailX_x u true x hY)).const_mul (2 : ℂ)
  exact h

theorem hasDerivAt_lineModel_y (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => lineModel u x q) (lineModelY u x Y) Y := by
  unfold lineModel lineModelY
  have h := (hasDerivAt_constantPart u hY).add
    (((hasDerivAt_weightedTail_y u false x hY).add (hasDerivAt_weightedTail_y u true x hY)).const_mul
      (2 : ℂ))
  exact h

theorem hasDerivAt_lineModelY_y (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun q : ℝ => lineModelY u x q) (lineModelYY u x Y) Y := by
  unfold lineModelY lineModelYY
  have h := (hasDerivAt_constantPartY u hY).add
    (((hasDerivAt_weightedTailY_y u false x hY).add (hasDerivAt_weightedTailY_y u true x hY)).const_mul
      (2 : ℂ))
  exact h

/-- **The eigen-equation of the completed Eisenstein Fourier model** at every height and every
parameter: `Y² (∂²_x E* + ∂²_Y E*) = (u² − 1/4) E*`. -/
theorem lineModel_eigen (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (lineModelXX u x Y + lineModelYY u x Y) = (u ^ 2 - 1 / 4) * lineModel u x Y := by
  unfold lineModelXX lineModelYY lineModel
  have h0 := constantPart_eigen u hY
  have h1 := weightedTail_eigen u false x hY
  have h2 := weightedTail_eigen u true x hY
  linear_combination h0 + 2 * h1 + 2 * h2

/-- The eigen-equation in terms of iterated `deriv`s. -/
theorem lineModel_eigen_deriv (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ 2 * (deriv (fun q : ℝ => deriv (fun p : ℝ => lineModel u p Y) q) x +
        deriv (fun q : ℝ => deriv (fun p : ℝ => lineModel u x p) q) Y) =
      (u ^ 2 - 1 / 4) * lineModel u x Y := by
  have hx : (fun q : ℝ => deriv (fun p : ℝ => lineModel u p Y) q) = fun q => lineModelX u q Y :=
    funext fun q => (hasDerivAt_lineModel_x u q hY).deriv
  have hy : (fun q : ℝ => deriv (fun p : ℝ => lineModel u x p) q) =ᶠ[nhds Y]
      fun q => lineModelY u x q := by
    filter_upwards [Ioi_mem_nhds hY] with q hq
    exact (hasDerivAt_lineModel_y u x hq).deriv
  rw [hx, hy.deriv_eq, (hasDerivAt_lineModelX_x u x hY).deriv, (hasDerivAt_lineModelY_y u x hY).deriv]
  exact lineModel_eigen u x hY

end

end RHTower
