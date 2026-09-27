import GaloisForLFunctions.RHTower.ThetaAllSieveSeedProjector
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.HTGeometry.SampledSmallComplex
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay

/-!
# Global reflected Riccati positivity does not orient an order-one Fourier divisor

The damped three-Gaussian family `g_ε(x) = exp(-ε(cosh(x/σ) - 1)) (h_σ(x) + a h_σ(x - σ/2) +
a h_σ(x + σ/2))`, `h_σ(x) = exp(-x²/(2σ²))`, `0 < a < 1/2`, has:

* `log g_ε = -ε(cosh(x/σ)-1) - x²/(2σ²) + f(x/(2σ))` with the three-point cumulant function
  `f(y) = log(1 + β e^y + β e^{-y})`, `0 ≤ f⁽²⁾ ≤ 1`, `f⁽⁴⁾ ≥ -3`;
* strict reflected positivity `A, A_t, A_tt > 0` and the uniform Riccati margin
  `2A_tA_tt - A_ttt ≥ 66 c⁴ t`, `c = 1/(2σ)`, and `(log g_ε)⁽²⁾ ≤ -3/(4σ²)`;
* an entire Fourier transform with `F₀(z) = σ√(2π) e^{-σ²z²/2}(1 + 2a cos(σz/2))`, zeros
  `z_n = (2/σ)((2n+1)π + i arcosh(1/(2a)))`, locally uniform convergence `F_ε → F₀` and Hurwitz
  persistence of isolated zeros;
* order-one growth, superexponential decay of every derivative and real-analyticity for `ε > 0`.

**Theorem** (`globalRiccati_offline_countermodel`): for every `N`, `η > 0` and interval `(α, β)`
some member has at least `N` distinct Fourier zeros with `Re z ∈ (α, β)`, `0 < Im z < η`.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-! ## The three-point cumulant function -/

/-- `D(y) = 1 + 2β cosh y`. -/
noncomputable def riccatiMgf (β y : ℝ) : ℝ := 1 + 2 * β * Real.cosh y

/-- Mean `s(y) = 2β sinh y / D(y)` of the three-point law on `{-1,0,1}`. -/
noncomputable def riccatiMean (β y : ℝ) : ℝ := 2 * β * Real.sinh y / riccatiMgf β y

/-- Second moment `C(y) = 2β cosh y / D(y)`. -/
noncomputable def riccatiSecond (β y : ℝ) : ℝ := 2 * β * Real.cosh y / riccatiMgf β y

/-- The cumulant function `f(y) = log(1 + β e^y + β e^{-y})`. -/
noncomputable def riccatiCumulant (β y : ℝ) : ℝ := Real.log (riccatiMgf β y)

/-- `f'' = C - s²`. -/
noncomputable def riccatiCumulantTwo (β y : ℝ) : ℝ := riccatiSecond β y - riccatiMean β y ^ 2

/-- `f''' = s - 3Cs + 2s³`. -/
noncomputable def riccatiCumulantThree (β y : ℝ) : ℝ :=
  riccatiMean β y - 3 * riccatiSecond β y * riccatiMean β y + 2 * riccatiMean β y ^ 3

/-- `f'''' = C - 4s² - 3C² + 12Cs² - 6s⁴`. -/
noncomputable def riccatiCumulantFour (β y : ℝ) : ℝ :=
  riccatiSecond β y - 4 * riccatiMean β y ^ 2 - 3 * riccatiSecond β y ^ 2 +
    12 * riccatiSecond β y * riccatiMean β y ^ 2 - 6 * riccatiMean β y ^ 4

theorem riccatiMgf_pos {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) : 0 < riccatiMgf β y := by
  unfold riccatiMgf
  have := Real.cosh_pos y
  positivity

theorem hasDerivAt_riccatiMgf (β y : ℝ) :
    HasDerivAt (riccatiMgf β) (2 * β * Real.sinh y) y := by
  unfold riccatiMgf
  simpa using ((Real.hasDerivAt_cosh y).const_mul (2 * β)).const_add 1

theorem hasDerivAt_riccatiCumulant {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    HasDerivAt (riccatiCumulant β) (riccatiMean β y) y := by
  unfold riccatiCumulant riccatiMean
  have h := (hasDerivAt_riccatiMgf β y).log (riccatiMgf_pos hβ y).ne'
  exact h

theorem hasDerivAt_riccatiMean {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    HasDerivAt (riccatiMean β) (riccatiCumulantTwo β y) y := by
  have hD := riccatiMgf_pos hβ y
  have h := ((Real.hasDerivAt_sinh y).const_mul (2 * β)).div (hasDerivAt_riccatiMgf β y) hD.ne'
  unfold riccatiMean
  refine h.congr_deriv ?_
  unfold riccatiCumulantTwo riccatiSecond riccatiMean riccatiMgf
  have hD' : 1 + 2 * β * Real.cosh y ≠ 0 := hD.ne'
  field_simp

theorem hasDerivAt_riccatiSecond {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    HasDerivAt (riccatiSecond β) (riccatiMean β y - riccatiSecond β y * riccatiMean β y) y := by
  have hD := riccatiMgf_pos hβ y
  have h := ((Real.hasDerivAt_cosh y).const_mul (2 * β)).div (hasDerivAt_riccatiMgf β y) hD.ne'
  unfold riccatiSecond
  refine h.congr_deriv ?_
  unfold riccatiMean riccatiMgf
  have hD' : 1 + 2 * β * Real.cosh y ≠ 0 := hD.ne'
  field_simp

theorem hasDerivAt_riccatiCumulantTwo {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    HasDerivAt (riccatiCumulantTwo β) (riccatiCumulantThree β y) y := by
  have h := (hasDerivAt_riccatiSecond hβ y).sub ((hasDerivAt_riccatiMean hβ y).pow 2)
  have e : riccatiCumulantTwo β = fun z => riccatiSecond β z - riccatiMean β z ^ 2 := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold riccatiCumulantThree riccatiCumulantTwo
  push_cast
  ring

theorem hasDerivAt_riccatiCumulantThree {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    HasDerivAt (riccatiCumulantThree β) (riccatiCumulantFour β y) y := by
  have hs := hasDerivAt_riccatiMean hβ y
  have hC := hasDerivAt_riccatiSecond hβ y
  have h := (hs.sub ((hC.const_mul 3).mul hs)).add ((hs.pow 3).const_mul 2)
  have e : riccatiCumulantThree β = fun z => riccatiMean β z -
      3 * riccatiSecond β z * riccatiMean β z + 2 * riccatiMean β z ^ 3 := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold riccatiCumulantFour riccatiCumulantTwo
  push_cast
  ring

theorem riccatiSecond_sq_sub_mean_sq {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    riccatiSecond β y ^ 2 - riccatiMean β y ^ 2 = (2 * β / riccatiMgf β y) ^ 2 := by
  have hD := riccatiMgf_pos hβ y
  unfold riccatiSecond riccatiMean
  have h := Real.cosh_sq_sub_sinh_sq y
  field_simp
  linear_combination β ^ 2 * h

theorem riccatiSecond_nonneg {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) : 0 ≤ riccatiSecond β y := by
  unfold riccatiSecond
  have := riccatiMgf_pos hβ y
  have := Real.cosh_pos y
  positivity

theorem riccatiSecond_le_one {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) : riccatiSecond β y ≤ 1 := by
  have hD := riccatiMgf_pos hβ y
  unfold riccatiSecond
  rw [div_le_one hD]
  unfold riccatiMgf
  linarith

theorem riccatiMean_sq_le {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    riccatiMean β y ^ 2 ≤ riccatiSecond β y ^ 2 := by
  have := riccatiSecond_sq_sub_mean_sq hβ y
  nlinarith [sq_nonneg (2 * β / riccatiMgf β y)]

/-- `0 ≤ f'' ≤ 1`: the variance of a law on `{-1,0,1}`. -/
theorem riccatiCumulantTwo_mem {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) :
    0 ≤ riccatiCumulantTwo β y ∧ riccatiCumulantTwo β y ≤ 1 := by
  have h0 := riccatiSecond_nonneg hβ y
  have h1 := riccatiSecond_le_one hβ y
  have h2 := riccatiMean_sq_le hβ y
  unfold riccatiCumulantTwo
  constructor <;> nlinarith [sq_nonneg (riccatiMean β y)]

/-- `f'''' ≥ -3`: the fourth cumulant of a law on `{-1,0,1}`. -/
theorem riccatiCumulantFour_ge {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) : -3 ≤ riccatiCumulantFour β y := by
  have h0 := riccatiSecond_nonneg hβ y
  have h1 := riccatiSecond_le_one hβ y
  have h2 := riccatiMean_sq_le hβ y
  set C := riccatiSecond β y
  set u := riccatiMean β y ^ 2
  have hu : 0 ≤ u := sq_nonneg _
  have hC2 : C ^ 2 ≤ C := by nlinarith
  unfold riccatiCumulantFour
  rw [show riccatiMean β y ^ 4 = u ^ 2 by rw [← pow_mul]]
  nlinarith [mul_nonneg hu h0, mul_nonneg hu (sub_nonneg.mpr h1), mul_nonneg hu hu]

/-- `f'''(y + v) - f'''(y - v) ≥ -6v` for `v ≥ 0`. -/
theorem riccatiCumulantThree_increment {β : ℝ} (hβ : 0 ≤ β) (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    -(6 * v) ≤ riccatiCumulantThree β (y + v) - riccatiCumulantThree β (y - v) := by
  have hmono : Monotone fun z => riccatiCumulantThree β z + 3 * z := by
    have hd : ∀ z, HasDerivAt (fun z => riccatiCumulantThree β z + 3 * z)
        (riccatiCumulantFour β z + 3 * 1) z := fun z =>
      (hasDerivAt_riccatiCumulantThree hβ z).add ((hasDerivAt_id' z).const_mul 3)
    refine monotone_of_deriv_nonneg (fun z => (hd z).differentiableAt) fun z => ?_
    rw [(hd z).deriv]
    linarith [riccatiCumulantFour_ge hβ z]
  have := hmono (show y - v ≤ y + v by linarith)
  simp only at this
  linarith

/-! ## The damped three-Gaussian family with shift `σ/2` -/

/-- The Gaussian `h_σ(x) = exp(-x²/(2σ²))`. -/
noncomputable def riccatiGauss (σ x : ℝ) : ℝ := Real.exp (-x ^ 2 / (2 * σ ^ 2))

/-- `g₀(x) = h_σ(x) + a h_σ(x - σ/2) + a h_σ(x + σ/2)`. -/
noncomputable def riccatiBase (a σ x : ℝ) : ℝ :=
  riccatiGauss σ x + a * riccatiGauss σ (x - σ / 2) + a * riccatiGauss σ (x + σ / 2)

/-- The damped source `g_ε(x) = exp(-ε(cosh(x/σ) - 1)) g₀(x)`. -/
noncomputable def riccatiSource (a σ ε x : ℝ) : ℝ :=
  Real.exp (-(ε * (Real.cosh (x / σ) - 1))) * riccatiBase a σ x

/-- The cumulant weight `β = a e^{-1/8}`. -/
noncomputable def riccatiWeight (a : ℝ) : ℝ := a * Real.exp (-(1 / 8))

/-- The logarithm `ℓ = log g_ε`. -/
noncomputable def riccatiLog (a σ ε x : ℝ) : ℝ :=
  -(ε * (Real.cosh (x / σ) - 1)) - x ^ 2 / (2 * σ ^ 2) +
    riccatiCumulant (riccatiWeight a) (x / (2 * σ))

/-- The first logarithmic derivative. -/
noncomputable def riccatiLogOne (a σ ε x : ℝ) : ℝ :=
  -(ε / σ * Real.sinh (x / σ)) - x / σ ^ 2 +
    1 / (2 * σ) * riccatiMean (riccatiWeight a) (x / (2 * σ))

/-- The second logarithmic derivative. -/
noncomputable def riccatiLogTwo (a σ ε x : ℝ) : ℝ :=
  -(ε / σ ^ 2 * Real.cosh (x / σ)) - 1 / σ ^ 2 +
    (1 / (2 * σ)) ^ 2 * riccatiCumulantTwo (riccatiWeight a) (x / (2 * σ))

/-- The third logarithmic derivative. -/
noncomputable def riccatiLogThree (a σ ε x : ℝ) : ℝ :=
  -(ε / σ ^ 3 * Real.sinh (x / σ)) +
    (1 / (2 * σ)) ^ 3 * riccatiCumulantThree (riccatiWeight a) (x / (2 * σ))

theorem riccatiWeight_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ riccatiWeight a := by
  unfold riccatiWeight
  positivity

theorem riccatiBase_eq {a σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    riccatiBase a σ x = riccatiGauss σ x * riccatiMgf (riccatiWeight a) (x / (2 * σ)) := by
  unfold riccatiBase riccatiGauss riccatiMgf riccatiWeight
  rw [Real.cosh_eq]
  have e1 : -(x - σ / 2) ^ 2 / (2 * σ ^ 2) = -x ^ 2 / (2 * σ ^ 2) + (-(1 / 8) + x / (2 * σ)) := by
    field_simp; ring
  have e2 : -(x + σ / 2) ^ 2 / (2 * σ ^ 2) = -x ^ 2 / (2 * σ ^ 2) + (-(1 / 8) + -(x / (2 * σ))) := by
    field_simp; ring
  rw [e1, e2, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

theorem riccatiSource_eq_exp {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε x : ℝ) :
    riccatiSource a σ ε x = Real.exp (riccatiLog a σ ε x) := by
  have hM := riccatiMgf_pos (riccatiWeight_nonneg ha) (x / (2 * σ))
  have e : riccatiLog a σ ε x = -(ε * (Real.cosh (x / σ) - 1)) + -x ^ 2 / (2 * σ ^ 2) +
      Real.log (riccatiMgf (riccatiWeight a) (x / (2 * σ))) := by
    unfold riccatiLog riccatiCumulant; ring
  rw [e, Real.exp_add, Real.exp_add, Real.exp_log hM, riccatiSource, riccatiBase_eq hσ,
    riccatiGauss]
  ring

theorem riccatiSource_pos {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε x : ℝ) :
    0 < riccatiSource a σ ε x := by
  rw [riccatiSource_eq_exp ha hσ]
  exact Real.exp_pos _

theorem riccatiSource_neg (a σ ε x : ℝ) : riccatiSource a σ ε (-x) = riccatiSource a σ ε x := by
  unfold riccatiSource riccatiBase riccatiGauss
  rw [neg_div, Real.cosh_neg, show -x - σ / 2 = -(x + σ / 2) by ring,
    show -x + σ / 2 = -(x - σ / 2) by ring]
  simp only [neg_sq]
  ring

theorem hasDerivAt_riccatiLog {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε x : ℝ) :
    HasDerivAt (riccatiLog a σ ε) (riccatiLogOne a σ ε x) x := by
  have hβ := riccatiWeight_nonneg ha
  have h1 := (((Real.hasDerivAt_cosh (x / σ)).comp x ((hasDerivAt_id' x).div_const σ)).sub_const
    1).const_mul ε |>.neg
  have h2 := ((hasDerivAt_id' x).pow 2).div_const (2 * σ ^ 2)
  have h3 := (hasDerivAt_riccatiCumulant hβ (x / (2 * σ))).comp x
    ((hasDerivAt_id' x).div_const (2 * σ))
  unfold riccatiLog
  refine ((h1.sub h2).add h3).congr_deriv ?_
  unfold riccatiLogOne
  field_simp
  ring

theorem hasDerivAt_riccatiLogOne {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε x : ℝ) :
    HasDerivAt (riccatiLogOne a σ ε) (riccatiLogTwo a σ ε x) x := by
  have hβ := riccatiWeight_nonneg ha
  have h1 := ((Real.hasDerivAt_sinh (x / σ)).comp x ((hasDerivAt_id' x).div_const σ)).const_mul
    (ε / σ) |>.neg
  have h2 := (hasDerivAt_id' x).div_const (σ ^ 2)
  have h3 := ((hasDerivAt_riccatiMean hβ (x / (2 * σ))).comp x
    ((hasDerivAt_id' x).div_const (2 * σ))).const_mul (1 / (2 * σ))
  unfold riccatiLogOne
  refine ((h1.sub h2).add h3).congr_deriv ?_
  unfold riccatiLogTwo
  field_simp

theorem hasDerivAt_riccatiLogTwo {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε x : ℝ) :
    HasDerivAt (riccatiLogTwo a σ ε) (riccatiLogThree a σ ε x) x := by
  have hβ := riccatiWeight_nonneg ha
  have h1 := ((Real.hasDerivAt_cosh (x / σ)).comp x ((hasDerivAt_id' x).div_const σ)).const_mul
    (ε / σ ^ 2) |>.neg
  have h3 := ((hasDerivAt_riccatiCumulantTwo hβ (x / (2 * σ))).comp x
    ((hasDerivAt_id' x).div_const (2 * σ))).const_mul ((1 / (2 * σ)) ^ 2)
  unfold riccatiLogTwo
  refine ((h1.sub_const (1 / σ ^ 2)).add h3).congr_deriv ?_
  unfold riccatiLogThree
  field_simp

/-- `ℓ'' ≤ -3/(4σ²)` for every `ε ≥ 0`. -/
theorem riccatiLogTwo_le {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (hε : 0 ≤ ε) (x : ℝ) :
    riccatiLogTwo a σ ε x ≤ -(3 / (4 * σ ^ 2)) := by
  have hβ := riccatiWeight_nonneg ha
  have hf := (riccatiCumulantTwo_mem hβ (x / (2 * σ))).2
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hdamp : 0 ≤ ε / σ ^ 2 * Real.cosh (x / σ) := by
    have := Real.cosh_pos (x / σ); positivity
  unfold riccatiLogTwo
  have : (1 / (2 * σ)) ^ 2 = 1 / (4 * σ ^ 2) := by field_simp; ring
  rw [this]
  have h4 : 1 / (4 * σ ^ 2) * riccatiCumulantTwo (riccatiWeight a) (x / (2 * σ)) ≤
      1 / (4 * σ ^ 2) := by
    have : 0 < 1 / (4 * σ ^ 2) := by positivity
    nlinarith
  have e : -(3 / (4 * σ ^ 2)) = -(1 / σ ^ 2) + 1 / (4 * σ ^ 2) := by field_simp; ring
  linarith

/-! ## Reflected action, displacement jets and the Riccati margin -/

/-- The reflected action `A(u,t) = 2ℓ(u) - ℓ(u+t) - ℓ(u-t)`. -/
noncomputable def riccatiAction (a σ ε u t : ℝ) : ℝ :=
  2 * riccatiLog a σ ε u - riccatiLog a σ ε (u + t) - riccatiLog a σ ε (u - t)

/-- `A_t`. -/
noncomputable def riccatiJetOne (a σ ε u t : ℝ) : ℝ :=
  riccatiLogOne a σ ε (u - t) - riccatiLogOne a σ ε (u + t)

/-- `A_tt`. -/
noncomputable def riccatiJetTwo (a σ ε u t : ℝ) : ℝ :=
  -riccatiLogTwo a σ ε (u + t) - riccatiLogTwo a σ ε (u - t)

/-- `A_ttt`. -/
noncomputable def riccatiJetThree (a σ ε u t : ℝ) : ℝ :=
  riccatiLogThree a σ ε (u - t) - riccatiLogThree a σ ε (u + t)

/-- The Riccati margin `2 A_t A_tt - A_ttt`. -/
noncomputable def riccatiMargin (a σ ε u t : ℝ) : ℝ :=
  2 * riccatiJetOne a σ ε u t * riccatiJetTwo a σ ε u t - riccatiJetThree a σ ε u t

theorem hasDerivAt_riccatiAction {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε u t : ℝ) :
    HasDerivAt (riccatiAction a σ ε u) (riccatiJetOne a σ ε u t) t := by
  have hp := (hasDerivAt_riccatiLog ha hσ ε (u + t)).comp t ((hasDerivAt_id' t).const_add u)
  have hm := (hasDerivAt_riccatiLog ha hσ ε (u - t)).comp t ((hasDerivAt_id' t).const_sub u)
  unfold riccatiAction
  refine (((hasDerivAt_const t (2 * riccatiLog a σ ε u)).sub hp).sub hm).congr_deriv ?_
  unfold riccatiJetOne
  ring

theorem hasDerivAt_riccatiJetOne {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε u t : ℝ) :
    HasDerivAt (riccatiJetOne a σ ε u) (riccatiJetTwo a σ ε u t) t := by
  have hp := (hasDerivAt_riccatiLogOne ha hσ ε (u + t)).comp t ((hasDerivAt_id' t).const_add u)
  have hm := (hasDerivAt_riccatiLogOne ha hσ ε (u - t)).comp t ((hasDerivAt_id' t).const_sub u)
  unfold riccatiJetOne
  refine (hm.sub hp).congr_deriv ?_
  unfold riccatiJetTwo
  ring

theorem hasDerivAt_riccatiJetTwo {a σ : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (ε u t : ℝ) :
    HasDerivAt (riccatiJetTwo a σ ε u) (riccatiJetThree a σ ε u t) t := by
  have hp := (hasDerivAt_riccatiLogTwo ha hσ ε (u + t)).comp t ((hasDerivAt_id' t).const_add u)
  have hm := (hasDerivAt_riccatiLogTwo ha hσ ε (u - t)).comp t ((hasDerivAt_id' t).const_sub u)
  unfold riccatiJetTwo
  refine (hp.neg.sub hm).congr_deriv ?_
  unfold riccatiJetThree
  ring

theorem riccatiJetTwo_ge {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (hε : 0 ≤ ε) (u t : ℝ) :
    3 / (2 * σ ^ 2) ≤ riccatiJetTwo a σ ε u t := by
  have h1 := riccatiLogTwo_le ha hσ hε (u + t)
  have h2 := riccatiLogTwo_le ha hσ hε (u - t)
  have hσ2 : 0 < σ ^ 2 := by positivity
  unfold riccatiJetTwo
  have e : 3 / (2 * σ ^ 2) = 3 / (4 * σ ^ 2) + 3 / (4 * σ ^ 2) := by field_simp; ring
  linarith

theorem riccatiJetOne_ge {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (hε : 0 ≤ ε) (u : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : 3 / (2 * σ ^ 2) * t ≤ riccatiJetOne a σ ε u t := by
  have hd : ∀ τ, HasDerivAt (fun τ => riccatiJetOne a σ ε u τ - 3 / (2 * σ ^ 2) * τ)
      (riccatiJetTwo a σ ε u τ - 3 / (2 * σ ^ 2) * 1) τ := fun τ =>
    (hasDerivAt_riccatiJetOne ha hσ ε u τ).sub ((hasDerivAt_id' τ).const_mul _)
  have hmono : Monotone fun τ => riccatiJetOne a σ ε u τ - 3 / (2 * σ ^ 2) * τ :=
    monotone_of_deriv_nonneg (fun τ => (hd τ).differentiableAt) fun τ => by
      rw [(hd τ).deriv]; linarith [riccatiJetTwo_ge ha hσ hε u τ]
  have h := hmono ht
  simp only [riccatiJetOne, add_zero, sub_zero, sub_self, mul_zero] at h
  unfold riccatiJetOne
  linarith

theorem riccatiAction_ge {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : σ ≠ 0) (hε : 0 ≤ ε) (u : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : 3 / (4 * σ ^ 2) * t ^ 2 ≤ riccatiAction a σ ε u t := by
  have hd : ∀ τ, HasDerivAt (fun τ => riccatiAction a σ ε u τ - 3 / (4 * σ ^ 2) * τ ^ 2)
      (riccatiJetOne a σ ε u τ - 3 / (4 * σ ^ 2) * (2 * τ)) τ := fun τ => by
    have := (hasDerivAt_riccatiAction ha hσ ε u τ).sub (((hasDerivAt_id' τ).pow 2).const_mul
      (3 / (4 * σ ^ 2)))
    refine this.congr_deriv ?_
    push_cast
    ring
  have hmono : MonotoneOn (fun τ => riccatiAction a σ ε u τ - 3 / (4 * σ ^ 2) * τ ^ 2) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun τ _ => (hd τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hd τ).differentiableAt.differentiableWithinAt) fun τ hτ => ?_
    rw [interior_Ici] at hτ
    rw [(hd τ).deriv]
    have := riccatiJetOne_ge ha hσ hε u (le_of_lt hτ)
    have hσ2 : 0 < σ ^ 2 := by positivity
    have e : 3 / (4 * σ ^ 2) * (2 * τ) = 3 / (2 * σ ^ 2) * τ := by field_simp; ring
    linarith
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [riccatiAction, add_zero, sub_zero] at h
  unfold riccatiAction
  nlinarith

theorem riccatiJetOne_split (a σ ε u t : ℝ) :
    riccatiJetOne a σ ε u t = riccatiJetOne a σ 0 u t +
      ε / σ * (Real.sinh ((u + t) / σ) - Real.sinh ((u - t) / σ)) := by
  unfold riccatiJetOne riccatiLogOne
  ring

theorem riccatiJetTwo_split (a σ ε u t : ℝ) :
    riccatiJetTwo a σ ε u t = riccatiJetTwo a σ 0 u t +
      ε / σ ^ 2 * (Real.cosh ((u + t) / σ) + Real.cosh ((u - t) / σ)) := by
  unfold riccatiJetTwo riccatiLogTwo
  ring

theorem riccatiJetThree_split {σ : ℝ} (hσ : σ ≠ 0) (a ε u t : ℝ) :
    riccatiJetThree a σ ε u t = riccatiJetThree a σ 0 u t +
      ε / σ * (Real.sinh ((u + t) / σ) - Real.sinh ((u - t) / σ)) / σ ^ 2 := by
  unfold riccatiJetThree riccatiLogThree
  field_simp
  ring

theorem riccatiJetThree_zero_le {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (u : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : riccatiJetThree a σ 0 u t ≤ 6 * (1 / (2 * σ)) ^ 4 * t := by
  have hβ := riccatiWeight_nonneg ha
  have hv : 0 ≤ t / (2 * σ) := by positivity
  have h := riccatiCumulantThree_increment hβ (u / (2 * σ)) hv
  rw [show u / (2 * σ) + t / (2 * σ) = (u + t) / (2 * σ) by ring,
    show u / (2 * σ) - t / (2 * σ) = (u - t) / (2 * σ) by ring] at h
  unfold riccatiJetThree riccatiLogThree
  have hc : 0 < (1 / (2 * σ)) ^ 3 := by positivity
  have key : (1 / (2 * σ)) ^ 3 * (riccatiCumulantThree (riccatiWeight a) ((u - t) / (2 * σ)) -
      riccatiCumulantThree (riccatiWeight a) ((u + t) / (2 * σ))) ≤
      (1 / (2 * σ)) ^ 3 * (6 * (t / (2 * σ))) := mul_le_mul_of_nonneg_left (by linarith) hc.le
  have e : (1 / (2 * σ)) ^ 3 * (6 * (t / (2 * σ))) = 6 * (1 / (2 * σ)) ^ 4 * t := by
    field_simp
  simp only [zero_div, zero_mul, neg_zero, zero_add]
  linarith

/-- **Uniform global Riccati margin.**  For `a ≥ 0`, `σ > 0`, `ε ≥ 0` and `t ≥ 0`,
`2A_tA_tt - A_ttt ≥ 66 c⁴ t` with `c = 1/(2σ)`. -/
theorem riccatiMargin_ge {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) (u : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : 66 * (1 / (2 * σ)) ^ 4 * t ≤ riccatiMargin a σ ε u t := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hJ1 := riccatiJetOne_ge ha hσ0 le_rfl u ht
  have hJ2 := riccatiJetTwo_ge ha hσ0 (le_refl (0 : ℝ)) u t
  have hJ3 := riccatiJetThree_zero_le ha hσ u ht
  have hEt : 0 ≤ ε / σ * (Real.sinh ((u + t) / σ) - Real.sinh ((u - t) / σ)) := by
    refine mul_nonneg (by positivity) (sub_nonneg.mpr (Real.sinh_le_sinh.mpr ?_))
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  have hEtt : 0 ≤ ε / σ ^ 2 * (Real.cosh ((u + t) / σ) + Real.cosh ((u - t) / σ)) := by
    have := Real.cosh_pos ((u + t) / σ); have := Real.cosh_pos ((u - t) / σ); positivity
  unfold riccatiMargin
  rw [riccatiJetOne_split, riccatiJetTwo_split, riccatiJetThree_split hσ0]
  set E1 := ε / σ * (Real.sinh ((u + t) / σ) - Real.sinh ((u - t) / σ))
  set E2 := ε / σ ^ 2 * (Real.cosh ((u + t) / σ) + Real.cosh ((u - t) / σ))
  set J1 := riccatiJetOne a σ 0 u t
  set J2 := riccatiJetTwo a σ 0 u t
  set J3 := riccatiJetThree a σ 0 u t
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hc4 : (1 / (2 * σ)) ^ 4 = 1 / (16 * σ ^ 4) := by field_simp; ring
  have hJ1n : 0 ≤ J1 := le_trans (by positivity) hJ1
  have hJ2n : 0 ≤ J2 := le_trans (by positivity) hJ2
  have hmain : 66 * (1 / (2 * σ)) ^ 4 * t ≤ 2 * J1 * J2 - J3 := by
    have h1 : 2 * (3 / (2 * σ ^ 2) * t) * (3 / (2 * σ ^ 2)) ≤ 2 * J1 * J2 := by
      have := mul_le_mul hJ1 hJ2 (by positivity) hJ1n
      linarith
    have e : 2 * (3 / (2 * σ ^ 2) * t) * (3 / (2 * σ ^ 2)) = 72 * (1 / (2 * σ)) ^ 4 * t := by
      rw [hc4]; field_simp; ring
    linarith
  have hJ2' : 1 / σ ^ 2 ≤ 2 * J2 := by
    have : 3 / (2 * σ ^ 2) = 1 / σ ^ 2 + 1 / (2 * σ ^ 2) := by field_simp; ring
    have : 0 < 1 / (2 * σ ^ 2) := by positivity
    have : 0 < 1 / σ ^ 2 := by positivity
    linarith
  have e : E1 / σ ^ 2 = E1 * (1 / σ ^ 2) := by ring
  nlinarith [mul_nonneg hJ1n hEtt, mul_nonneg hEt hEtt, mul_le_mul_of_nonneg_left hJ2' hEt]

/-- **Strict reflected positivity.**  For `t > 0`: `A > 0`, `A_t > 0`, `A_tt > 0` and
`2A_tA_tt - A_ttt > 0`. -/
theorem riccati_reflected_positivity {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) (u : ℝ)
    {t : ℝ} (ht : 0 < t) :
    0 < riccatiAction a σ ε u t ∧ 0 < riccatiJetOne a σ ε u t ∧ 0 < riccatiJetTwo a σ ε u t ∧
      0 < riccatiMargin a σ ε u t := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  refine ⟨lt_of_lt_of_le (by positivity) (riccatiAction_ge ha hσ0 hε u ht.le),
    lt_of_lt_of_le (by positivity) (riccatiJetOne_ge ha hσ0 hε u ht.le),
    lt_of_lt_of_le (by positivity) (riccatiJetTwo_ge ha hσ0 hε u t),
    lt_of_lt_of_le (by positivity) (riccatiMargin_ge ha hσ hε u ht.le)⟩

/-- **Strong log-concavity.**  `log g_ε` is strictly concave, with `(log g_ε)'' ≤ -3/(4σ²)`. -/
theorem strictConcaveOn_log_riccatiSource {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    StrictConcaveOn ℝ univ (fun x => Real.log (riccatiSource a σ ε x)) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have heq : (fun x => Real.log (riccatiSource a σ ε x)) = riccatiLog a σ ε := by
    funext x; rw [riccatiSource_eq_exp ha hσ0, Real.log_exp]
  rw [heq]
  have hderiv : deriv (riccatiLog a σ ε) = riccatiLogOne a σ ε :=
    funext fun x => (hasDerivAt_riccatiLog ha hσ0 ε x).deriv
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ
    (fun x _ => (hasDerivAt_riccatiLog ha hσ0 ε x).continuousAt.continuousWithinAt) ?_
  rw [hderiv]
  refine (strictAnti_of_deriv_neg fun x => ?_).strictAntiOn _
  rw [(hasDerivAt_riccatiLogOne ha hσ0 ε x).deriv]
  have := riccatiLogTwo_le ha hσ0 hε x
  have : 0 < 3 / (4 * σ ^ 2) := by positivity
  linarith

/-! ## Gaussian integrability -/

theorem integrable_exp_quadratic_real {b : ℝ} (hb : b < 0) (c d : ℝ) :
    Integrable (fun x : ℝ => Real.exp (b * x ^ 2 + c * x + d)) := by
  have h := (integrable_cexp_quadratic' (b := (b : ℂ)) (by simpa using hb) (c : ℂ) (d : ℂ)).norm
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, sq]

theorem exp_mul_abs_le (c x : ℝ) : Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-c * x)]
  · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (c * x)]

theorem integrable_shiftedGauss_mul_exp_abs {s : ℝ} (hs : 0 < s) (m c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-(x - m) ^ 2 / (2 * s ^ 2)) * Real.exp (c * |x|)) := by
  have hb : -(1 / (2 * s ^ 2)) < 0 := by
    have : 0 < 1 / (2 * s ^ 2) := by positivity
    linarith
  have h1 := integrable_exp_quadratic_real hb (m / s ^ 2 + c) (-(m ^ 2 / (2 * s ^ 2)))
  have h2 := integrable_exp_quadratic_real hb (m / s ^ 2 - c) (-(m ^ 2 / (2 * s ^ 2)))
  refine Integrable.mono' (h1.add h2) (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have e1 : Real.exp (-(x - m) ^ 2 / (2 * s ^ 2)) * Real.exp (c * x) =
      Real.exp (-(1 / (2 * s ^ 2)) * x ^ 2 + (m / s ^ 2 + c) * x + -(m ^ 2 / (2 * s ^ 2))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e2 : Real.exp (-(x - m) ^ 2 / (2 * s ^ 2)) * Real.exp (-c * x) =
      Real.exp (-(1 / (2 * s ^ 2)) * x ^ 2 + (m / s ^ 2 - c) * x + -(m ^ 2 / (2 * s ^ 2))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  simp only [Pi.add_apply]
  rw [← e1, ← e2, ← mul_add]
  exact mul_le_mul_of_nonneg_left (exp_mul_abs_le c x) (Real.exp_pos _).le

/-- A uniform Gaussian envelope: for `0 < s ≤ S` and `|m| ≤ S/2`,
`exp(-(x-m)²/(2s²)) ≤ e^{1/8} exp(-x²/(8S²))`. -/
theorem gauss_le_envelope {s S m : ℝ} (hs : 0 < s) (hsS : s ≤ S) (hm : |m| ≤ S / 2) (x : ℝ) :
    Real.exp (-(x - m) ^ 2 / (2 * s ^ 2)) ≤
      Real.exp (1 / 8) * Real.exp (-(x - 0) ^ 2 / (2 * (2 * S) ^ 2)) := by
  have hS : 0 < S := lt_of_lt_of_le hs hsS
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  rcases le_or_gt |x| S with hx | hx
  · have h1 : -(x - m) ^ 2 / (2 * s ^ 2) ≤ 0 := by
      have : 0 ≤ (x - m) ^ 2 / (2 * s ^ 2) := by positivity
      rw [neg_div]; linarith
    have h2 : -(1 / 8) ≤ -(x - 0) ^ 2 / (2 * (2 * S) ^ 2) := by
      rw [sub_zero, neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
      have : x ^ 2 ≤ S ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith
    linarith
  · have hxm : |x| / 2 ≤ |x - m| := by
      have := abs_sub_abs_le_abs_sub x m
      linarith
    have hsq : x ^ 2 / 4 ≤ (x - m) ^ 2 := by
      rw [← sq_abs (x - m), show x ^ 2 / 4 = (|x| / 2) ^ 2 by rw [div_pow, sq_abs]; ring]
      exact pow_le_pow_left₀ (by positivity) hxm 2
    have h1 : -(x - m) ^ 2 / (2 * s ^ 2) ≤ -(x ^ 2 / 4) / (2 * S ^ 2) := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      calc x ^ 2 / 4 / (2 * S ^ 2) ≤ (x - m) ^ 2 / (2 * S ^ 2) := by gcongr
        _ ≤ (x - m) ^ 2 / (2 * s ^ 2) := by gcongr
    have e : -(x ^ 2 / 4) / (2 * S ^ 2) = -(x - 0) ^ 2 / (2 * (2 * S) ^ 2) := by
      field_simp; ring
    linarith

theorem riccatiGauss_le_one (σ x : ℝ) : riccatiGauss σ x ≤ 1 := by
  unfold riccatiGauss
  rw [Real.exp_le_one_iff]
  have : 0 ≤ x ^ 2 / (2 * σ ^ 2) := by positivity
  rw [neg_div]; linarith

theorem riccatiSource_le_base {a σ ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (x : ℝ) :
    riccatiSource a σ ε x ≤ riccatiBase a σ x := by
  unfold riccatiSource
  have hb : 0 ≤ riccatiBase a σ x := by unfold riccatiBase riccatiGauss; positivity
  have hd : Real.exp (-(ε * (Real.cosh (x / σ) - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := Real.one_le_cosh (x / σ)
    nlinarith
  calc Real.exp (-(ε * (Real.cosh (x / σ) - 1))) * riccatiBase a σ x ≤ 1 * riccatiBase a σ x :=
        mul_le_mul_of_nonneg_right hd hb
    _ = _ := one_mul _

theorem riccatiSource_nonneg {a σ ε : ℝ} (ha : 0 ≤ a) (x : ℝ) : 0 ≤ riccatiSource a σ ε x := by
  unfold riccatiSource riccatiBase riccatiGauss
  positivity

/-- The uniform envelope of the family for `0 < σ ≤ S`, `ε ≥ 0`. -/
theorem riccatiSource_le_envelope {a σ ε S : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσS : σ ≤ S)
    (hε : 0 ≤ ε) (x : ℝ) :
    riccatiSource a σ ε x ≤
      (1 + 2 * a) * (Real.exp (1 / 8) * Real.exp (-(x - 0) ^ 2 / (2 * (2 * S) ^ 2))) := by
  refine (riccatiSource_le_base ha hε x).trans ?_
  have hS : 0 < S := lt_of_lt_of_le hσ hσS
  have hm : ∀ m, |m| ≤ S / 2 → riccatiGauss σ (x - m) ≤
      Real.exp (1 / 8) * Real.exp (-(x - 0) ^ 2 / (2 * (2 * S) ^ 2)) := fun m hm =>
    gauss_le_envelope hσ hσS hm x
  have h0 := hm 0 (by simp; positivity)
  have h1 := hm (σ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have h2 := hm (-(σ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  unfold riccatiBase
  rw [show riccatiGauss σ x = riccatiGauss σ (x - 0) by rw [sub_zero],
    show riccatiGauss σ (x + σ / 2) = riccatiGauss σ (x - -(σ / 2)) by rw [sub_neg_eq_add]]
  nlinarith

theorem integrable_envelope_mul_exp_abs {S : ℝ} (hS : 0 < S) (C c : ℝ) :
    Integrable (fun x : ℝ => C * (Real.exp (1 / 8) * Real.exp (-(x - 0) ^ 2 / (2 * (2 * S) ^ 2))) *
      Real.exp (c * |x|)) := by
  have h := (integrable_shiftedGauss_mul_exp_abs (s := 2 * S) (by positivity) 0 c).const_mul
    (C * Real.exp (1 / 8))
  exact h.congr (ae_of_all _ fun x => by simp only; ring)

theorem integrable_riccatiSource_mul_exp_abs {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (c : ℝ) : Integrable (fun x => riccatiSource a σ ε x * Real.exp (c * |x|)) := by
  have hc : Continuous fun x => riccatiSource a σ ε x * Real.exp (c * |x|) := by
    unfold riccatiSource riccatiBase riccatiGauss; fun_prop
  refine Integrable.mono' (integrable_envelope_mul_exp_abs hσ (1 + 2 * a) c) hc.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (riccatiSource_nonneg ha x) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (riccatiSource_le_envelope ha hσ le_rfl hε x) (Real.exp_pos _).le

/-! ## The Fourier transform -/

/-- The Fourier transform `F(z) = ∫ g_ε(x) e^{izx} dx`. -/
noncomputable def riccatiFourier (a σ ε : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (riccatiSource a σ ε x : ℂ) * Complex.exp (I * z * x)

theorem norm_cexp_I_mul (z : ℂ) (x : ℝ) :
    ‖Complex.exp (I * z * x)‖ = Real.exp (-(z.im * x)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_cexp_I_mul_le_exp_abs (z : ℂ) (x : ℝ) :
    ‖Complex.exp (I * z * x)‖ ≤ Real.exp (|z.im| * |x|) := by
  rw [norm_cexp_I_mul]
  refine Real.exp_le_exp.mpr ?_
  calc -(z.im * x) ≤ |z.im * x| := neg_le_abs _
    _ = |z.im| * |x| := abs_mul _ _

theorem integrable_riccatiFourier {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) (z : ℂ) :
    Integrable (fun x : ℝ => (riccatiSource a σ ε x : ℂ) * Complex.exp (I * z * x)) := by
  have hc : Continuous fun x : ℝ => (riccatiSource a σ ε x : ℂ) * Complex.exp (I * z * x) := by
    unfold riccatiSource riccatiBase riccatiGauss; fun_prop
  refine Integrable.mono' (integrable_riccatiSource_mul_exp_abs ha hσ hε |z.im|)
    hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (riccatiSource_nonneg ha x)]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp_abs z x) (riccatiSource_nonneg ha x)

/-- The Fourier transform of the family is entire. -/
theorem differentiable_riccatiFourier {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    Differentiable ℂ (riccatiFourier a σ ε) := by
  intro z₀
  set c := |z₀.im| + 2
  have hbound := integrable_riccatiSource_mul_exp_abs ha hσ hε c
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z x => (riccatiSource a σ ε x : ℂ) * Complex.exp (I * z * x))
    (F' := fun z x => (riccatiSource a σ ε x : ℂ) * (I * x * Complex.exp (I * z * x)))
    (x₀ := z₀) (bound := fun x => riccatiSource a σ ε x * Real.exp (c * |x|))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (integrable_riccatiFourier ha hσ hε z).aestronglyMeasurable)
    (integrable_riccatiFourier ha hσ hε z₀)
    (by
      have : Continuous fun x : ℝ =>
          (riccatiSource a σ ε x : ℂ) * (I * x * Complex.exp (I * z₀ * x)) := by
        unfold riccatiSource riccatiBase riccatiGauss; fun_prop
      exact this.aestronglyMeasurable)
    (ae_of_all _ fun x z hz => ?_) hbound (ae_of_all _ fun x z _ => ?_)
  · exact key.2.differentiableAt
  · have hzim : |z.im| ≤ |z₀.im| + 1 := by
      have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 : ‖z - z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (riccatiSource_nonneg ha x), norm_mul,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (riccatiSource_nonneg ha x)
    calc |x| * ‖Complex.exp (I * z * x)‖ ≤ Real.exp |x| * Real.exp (|z.im| * |x|) :=
          mul_le_mul (by linarith [Real.add_one_le_exp |x|]) (norm_cexp_I_mul_le_exp_abs z x)
            (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (c * |x|) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
  · have h := ((hasDerivAt_id' z).const_mul (I * (x : ℂ))).cexp.const_mul
      (riccatiSource a σ ε x : ℂ)
    refine (h.congr_deriv (by ring_nf)).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only
    ring_nf

/-- The Fourier transform of a translated Gaussian. -/
theorem integral_riccatiGauss_mul_cexp {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (z : ℂ) :
    (∫ x : ℝ, (riccatiGauss σ (x - m) : ℂ) * Complex.exp (I * z * x)) =
      Complex.exp (I * z * m) * ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        Complex.exp (-(σ ^ 2 * z ^ 2 / 2)) := by
  have hσ2 : (σ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (by positivity : σ ^ 2 ≠ 0)
  set b : ℂ := -(1 / (2 * (σ : ℂ) ^ 2))
  have hb : b.re < 0 := by
    have : b = ((-(1 / (2 * σ ^ 2)) : ℝ) : ℂ) := by simp [b]
    rw [this, Complex.ofReal_re]
    have : 0 < 1 / (2 * σ ^ 2) := by positivity
    linarith
  have h := integral_cexp_quadratic hb ((m : ℂ) / (σ : ℂ) ^ 2 + I * z) (-((m : ℂ) ^ 2 / (2 * σ ^ 2)))
  have hint : (fun x : ℝ => (riccatiGauss σ (x - m) : ℂ) * Complex.exp (I * z * x)) =
      fun x : ℝ => Complex.exp (b * (x : ℂ) ^ 2 + ((m : ℂ) / (σ : ℂ) ^ 2 + I * z) * x +
        -((m : ℂ) ^ 2 / (2 * σ ^ 2))) := by
    funext x
    unfold riccatiGauss
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [b]
    field_simp
    ring
  rw [hint, h]
  have hpow : ((Real.pi : ℂ) / -b) ^ (1 / 2 : ℂ) = ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    have e1 : (Real.pi : ℂ) / -b = ((2 * Real.pi * σ ^ 2 : ℝ) : ℂ) := by
      simp only [b, neg_neg]; push_cast; field_simp
    rw [e1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    congr 1
    rw [show 2 * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hσ.le]
  rw [hpow, mul_comm (Complex.exp (I * z * m)), mul_assoc, ← Complex.exp_add]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  congr 2
  simp only [b]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Closed form of the undamped transform.**
`F₀(z) = σ√(2π) e^{-σ²z²/2} (1 + 2a cos(σz/2))`. -/
theorem riccatiFourier_zero {σ : ℝ} (hσ : 0 < σ) (a : ℝ) (z : ℂ) :
    riccatiFourier a σ 0 z = ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      Complex.exp (-(σ ^ 2 * z ^ 2 / 2)) * (1 + 2 * a * Complex.cos (σ * z / 2)) := by
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hI : ∀ m : ℝ, Integrable (fun x : ℝ => (riccatiGauss σ (x - m) : ℂ) *
      Complex.exp (I * z * x)) := by
    intro m
    have h := integrable_cexp_quadratic' (b := -(1 / (2 * (σ : ℂ) ^ 2)))
      (by
        have : -(1 / (2 * (σ : ℂ) ^ 2)) = ((-(1 / (2 * σ ^ 2)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
        have : 0 < 1 / (2 * σ ^ 2) := by positivity
        linarith) ((m : ℂ) / (σ : ℂ) ^ 2 + I * z) (-((m : ℂ) ^ 2 / (2 * σ ^ 2)))
    refine h.congr (ae_of_all _ fun x => ?_)
    unfold riccatiGauss
    simp only
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hfun : ∀ x : ℝ, (riccatiSource a σ 0 x : ℂ) * Complex.exp (I * z * x) =
      (riccatiGauss σ (x - 0) : ℂ) * Complex.exp (I * z * x) +
        (a : ℂ) * ((riccatiGauss σ (x - σ / 2) : ℂ) * Complex.exp (I * z * x)) +
        (a : ℂ) * ((riccatiGauss σ (x - -(σ / 2)) : ℂ) * Complex.exp (I * z * x)) := by
    intro x
    unfold riccatiSource riccatiBase
    rw [sub_zero, sub_neg_eq_add, zero_mul, neg_zero, Real.exp_zero, one_mul]
    push_cast
    ring
  have i0 : Integrable (fun x : ℝ => (riccatiGauss σ (x - 0) : ℂ) * Complex.exp (I * z * x)) :=
    hI 0
  have i1 : Integrable (fun x : ℝ => (a : ℂ) * ((riccatiGauss σ (x - σ / 2) : ℂ) *
      Complex.exp (I * z * x))) := (hI _).const_mul _
  have i2 : Integrable (fun x : ℝ => (a : ℂ) * ((riccatiGauss σ (x - -(σ / 2)) : ℂ) *
      Complex.exp (I * z * x))) := (hI _).const_mul _
  have i01 : Integrable (fun x : ℝ => (riccatiGauss σ (x - 0) : ℂ) * Complex.exp (I * z * x) +
      (a : ℂ) * ((riccatiGauss σ (x - σ / 2) : ℂ) * Complex.exp (I * z * x))) := i0.add i1
  unfold riccatiFourier
  rw [integral_congr_ae (ae_of_all _ hfun), integral_add i01 i2, integral_add i0 i1,
    integral_const_mul, integral_const_mul,
    integral_riccatiGauss_mul_cexp hσ, integral_riccatiGauss_mul_cexp hσ,
    integral_riccatiGauss_mul_cexp hσ, Complex.cos]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  rw [show I * z * ((σ : ℂ) / 2) = σ * z / 2 * I by ring,
    show I * z * -((σ : ℂ) / 2) = -(σ * z / 2 * I) by ring]
  ring_nf

/-! ## Spectral zeros of the undamped transform -/

/-- `A₀ = arcosh(1/(2a))`. -/
noncomputable def riccatiDepth (a : ℝ) : ℝ := Real.arcosh (1 / (2 * a))

/-- The upper spectral zeros `z_n = (2/σ)((2n+1)π + iA₀)`. -/
noncomputable def riccatiZero (a σ : ℝ) (n : ℤ) : ℂ :=
  (2 / σ : ℝ) * (((2 * n + 1) * Real.pi : ℝ) + (riccatiDepth a : ℂ) * I)

theorem riccatiDepth_pos {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) : 0 < riccatiDepth a := by
  unfold riccatiDepth
  refine Real.arcosh_pos ?_
  rw [lt_div_iff₀ (by positivity)]
  linarith

theorem cosh_riccatiDepth {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.cosh (riccatiDepth a) = 1 / (2 * a) := by
  unfold riccatiDepth
  exact Real.cosh_arcosh (by rw [le_div_iff₀ (by positivity)]; linarith)

theorem riccatiFourier_zero_eq_zero_iff {σ : ℝ} (hσ : 0 < σ) (a : ℝ) (w : ℂ) :
    riccatiFourier a σ 0 w = 0 ↔ 1 + 2 * a * Complex.cos (σ * w / 2) = 0 := by
  rw [riccatiFourier_zero hσ]
  have h1 : ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : σ * Real.sqrt (2 * Real.pi) ≠ 0)
  simp only [mul_eq_zero, h1, Complex.exp_ne_zero, false_or]

theorem cos_riccatiCritical (a : ℝ) :
    Complex.cos (Real.pi + (riccatiDepth a : ℂ) * I) = -(Real.cosh (riccatiDepth a) : ℂ) := by
  rw [Complex.cos_add_mul_I, Complex.cos_pi, Complex.sin_pi, ← Complex.ofReal_cosh]
  ring

theorem riccatiFourier_riccatiZero {a σ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hσ : 0 < σ) (n : ℤ) :
    riccatiFourier a σ 0 (riccatiZero a σ n) = 0 := by
  rw [riccatiFourier_zero_eq_zero_iff hσ]
  have hz : (σ : ℂ) * riccatiZero a σ n / 2 = Real.pi + (riccatiDepth a : ℂ) * I + (n : ℂ) * (2 * Real.pi) := by
    unfold riccatiZero
    have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    push_cast
    field_simp
    ring
  rw [hz, Complex.cos_add_int_mul_two_pi, cos_riccatiCritical, cosh_riccatiDepth ha ha2]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp
  ring

/-- Every zero of the undamped transform lies in one of the two lattices
`(2/σ)(2kπ ± (π + iA₀))`. -/
theorem riccatiFourier_zero_eq_zero_lattice {a σ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hσ : 0 < σ)
    {w : ℂ} (hw : riccatiFourier a σ 0 w = 0) :
    ∃ k : ℤ, (σ : ℂ) * w / 2 = 2 * k * Real.pi + (Real.pi + (riccatiDepth a : ℂ) * I) ∨
      (σ : ℂ) * w / 2 = 2 * k * Real.pi - (Real.pi + (riccatiDepth a : ℂ) * I) := by
  rw [riccatiFourier_zero_eq_zero_iff hσ] at hw
  have hcos : Complex.cos (σ * w / 2) = Complex.cos (Real.pi + (riccatiDepth a : ℂ) * I) := by
    rw [cos_riccatiCritical, cosh_riccatiDepth ha ha2]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
    linear_combination hw
  exact Complex.cos_eq_cos_iff.mp hcos.symm |>.imp fun k h => h

/-- The zeros `z_n` are isolated: no other zero lies within `4 min(π, A₀)/σ`. -/
theorem riccatiZero_isolated {a σ : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 < σ) (n : ℤ)
    {w : ℂ} (hw : riccatiFourier a σ 0 w = 0)
    (hdist : ‖w - riccatiZero a σ n‖ < 4 * min Real.pi (riccatiDepth a) / σ) :
    w = riccatiZero a σ n := by
  have hA := riccatiDepth_pos ha ha2
  obtain ⟨k, hk | hk⟩ := riccatiFourier_zero_eq_zero_lattice ha ha2.le hσ hw
  · have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have hwk : w = riccatiZero a σ k := by
      unfold riccatiZero
      have : w = 2 / σ * ((σ : ℂ) * w / 2) := by field_simp
      rw [this, hk]
      push_cast
      ring
    by_cases hkn : k = n
    · rw [hwk, hkn]
    · exfalso
      have hre : (w - riccatiZero a σ n).re = 4 * Real.pi * (k - n) / σ := by
        rw [hwk]
        unfold riccatiZero
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
        field_simp
        ring
      have h1 : |(w - riccatiZero a σ n).re| ≤ ‖w - riccatiZero a σ n‖ := Complex.abs_re_le_norm _
      rw [hre] at h1
      have hkn' : (1 : ℝ) ≤ |(k : ℝ) - n| := by
        have : (1 : ℤ) ≤ |k - n| := Int.one_le_abs (sub_ne_zero.mpr hkn)
        exact_mod_cast this
      have h2 : 4 * Real.pi / σ ≤ |4 * Real.pi * (k - n) / σ| := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi),
          abs_of_pos hσ]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hσ.le
      have h3 : 4 * min Real.pi (riccatiDepth a) / σ ≤ 4 * Real.pi / σ :=
        div_le_div_of_nonneg_right (by linarith [min_le_left Real.pi (riccatiDepth a)]) hσ.le
      linarith
  · exfalso
    have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have hwe : w = 2 / σ * (2 * k * Real.pi - (Real.pi + (riccatiDepth a : ℂ) * I)) := by
      have : w = 2 / σ * ((σ : ℂ) * w / 2) := by field_simp
      rw [this, hk]
    have him : (w - riccatiZero a σ n).im = -(4 * riccatiDepth a / σ) := by
      rw [hwe]
      unfold riccatiZero
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.sub_re]
      norm_num
      field_simp
      ring
    have h1 : |(w - riccatiZero a σ n).im| ≤ ‖w - riccatiZero a σ n‖ := Complex.abs_im_le_norm _
    rw [him, abs_neg, abs_of_pos (by positivity)] at h1
    have h3 : 4 * min Real.pi (riccatiDepth a) / σ ≤ 4 * riccatiDepth a / σ :=
      div_le_div_of_nonneg_right (by linarith [min_le_right Real.pi (riccatiDepth a)]) hσ.le
    linarith

/-! ## Locally uniform convergence of the damped transforms -/

theorem continuous_riccatiSource_params (a x : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => riccatiSource a p.1 p.2 x) {p | p.1 ≠ 0} := by
  intro p hp
  have hp' : p.1 ≠ 0 := hp
  unfold riccatiSource riccatiBase riccatiGauss
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun q : ℝ × ℝ => x / q.1) p :=
    continuousAt_const.div continuousAt_fst hp'
  have h2 : ContinuousAt (fun q : ℝ × ℝ => 2 * q.1 ^ 2) p := by fun_prop
  have h2' : 2 * p.1 ^ 2 ≠ 0 := by positivity
  have hg : ∀ m : ℝ → ℝ, Continuous m → ContinuousAt
      (fun q : ℝ × ℝ => Real.exp (-(x - m q.1) ^ 2 / (2 * q.1 ^ 2))) p := by
    intro m hm
    exact Real.continuous_exp.continuousAt.comp
      (((((continuousAt_const.sub (hm.continuousAt.comp continuousAt_fst)).pow 2).neg).div h2 h2'))
  have g0 := hg (fun _ => 0) continuous_const
  have g1 := hg (fun s => s / 2) (continuous_id.div_const 2)
  have g2 := hg (fun s => -(s / 2)) (continuous_id.div_const 2).neg
  simp only [sub_zero, sub_neg_eq_add] at g0 g2
  exact (Real.continuous_exp.continuousAt.comp ((continuousAt_snd.mul
    ((Real.continuous_cosh.continuousAt.comp h1).sub continuousAt_const)).neg)).mul
    ((g0.add (continuousAt_const.mul g1)).add (continuousAt_const.mul g2))

/-- **Locally uniform convergence.**  If `σ_k → σ₀ > 0` and `ε_k → 0` with `ε_k ≥ 0`, the damped
transforms converge locally uniformly on `ℂ` to the undamped transform at `σ₀`. -/
theorem tendstoLocallyUniformly_riccatiFourier {a : ℝ} (ha : 0 ≤ a) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {σk εk : ℕ → ℝ} (hσk : ∀ k, 0 < σk k) (hεk : ∀ k, 0 ≤ εk k)
    (hσlim : Tendsto σk atTop (𝓝 σ₀)) (hεlim : Tendsto εk atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun k => riccatiFourier a (σk k) (εk k)) (riccatiFourier a σ₀ 0)
      atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R' := max R 0
  set S := 2 * σ₀
  have hS : 0 < S := by positivity
  have hev : ∀ᶠ k in atTop, σk k ≤ S :=
    hσlim.eventually (Iic_mem_nhds (by linarith : σ₀ < S))
  -- the integral of the source difference against `e^{R'|x|}` tends to zero
  set E : ℝ → ℝ := fun x => (1 + 2 * a) * (Real.exp (1 / 8) *
    Real.exp (-(x - 0) ^ 2 / (2 * (2 * S) ^ 2)))
  have hdiff : Tendsto (fun k => ∫ x, |riccatiSource a (σk k) (εk k) x -
      riccatiSource a σ₀ 0 x| * Real.exp (R' * |x|)) atTop (𝓝 0) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun (k : ℕ) (x : ℝ) => |riccatiSource a (σk k) (εk k) x - riccatiSource a σ₀ 0 x| *
        Real.exp (R' * |x|))
      (f := fun x => |riccatiSource a σ₀ 0 x - riccatiSource a σ₀ 0 x| * Real.exp (R' * |x|))
      (fun x => 2 * E x * Real.exp (R' * |x|))
      (Eventually.of_forall fun k => by
        have : Continuous fun x => |riccatiSource a (σk k) (εk k) x -
            riccatiSource a σ₀ 0 x| * Real.exp (R' * |x|) := by
          unfold riccatiSource riccatiBase riccatiGauss; fun_prop
        exact this.aestronglyMeasurable) ?_ ?_ ?_
    · simpa using hlim
    · filter_upwards [hev] with k hk
      refine ae_of_all _ fun x => ?_
      have h1 := riccatiSource_le_envelope ha (hσk k) hk (hεk k) x
      have h2 := riccatiSource_le_envelope ha hσ₀ (by linarith : σ₀ ≤ S) le_rfl x
      have h3 := riccatiSource_nonneg (σ := σk k) (ε := εk k) ha x
      have h4 := riccatiSource_nonneg (σ := σ₀) (ε := 0) ha x
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      simp only [E]
      rw [abs_le]
      constructor <;> linarith
    · have := (integrable_envelope_mul_exp_abs hS (1 + 2 * a) R').const_mul 2
      exact this.congr (ae_of_all _ fun x => by simp only [E]; ring)
    · refine ae_of_all _ fun x => ?_
      have hp : Tendsto (fun k => (σk k, εk k)) atTop (𝓝 (σ₀, 0)) := hσlim.prodMk_nhds hεlim
      have hc := ((continuous_riccatiSource_params a x) (σ₀, 0) (by simp [hσ₀.ne'])).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hp, Eventually.of_forall fun k => (hσk k).ne'⟩)
      exact ((hc.sub tendsto_const_nhds).abs).mul_const (Real.exp (R' * |x|))
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hdiff.eventually (gt_mem_nhds hδ)] with k hk z hz
  have hzR : |z.im| ≤ R' := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_max_left _ _))
  have hg_int : Integrable (fun x => |riccatiSource a (σk k) (εk k) x -
      riccatiSource a σ₀ 0 x| * Real.exp (R' * |x|)) := by
    have hc : Continuous fun x => |riccatiSource a (σk k) (εk k) x -
        riccatiSource a σ₀ 0 x| * Real.exp (R' * |x|) := by
      unfold riccatiSource riccatiBase riccatiGauss; fun_prop
    refine Integrable.mono' ((integrable_riccatiSource_mul_exp_abs ha (hσk k) (hεk k) R').add
      (integrable_riccatiSource_mul_exp_abs ha hσ₀ le_rfl R')) hc.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h3 := riccatiSource_nonneg (σ := σk k) (ε := εk k) ha x
    have h4 := riccatiSource_nonneg (σ := σ₀) (ε := 0) ha x
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [abs_le]
    constructor <;> linarith
  rw [dist_eq_norm]
  unfold riccatiFourier
  rw [← integral_sub (integrable_riccatiFourier ha hσ₀ le_rfl z)
    (integrable_riccatiFourier ha (hσk k) (hεk k) z)]
  calc ‖∫ x : ℝ, ((riccatiSource a σ₀ 0 x : ℂ) * Complex.exp (I * z * x) -
        (riccatiSource a (σk k) (εk k) x : ℂ) * Complex.exp (I * z * x))‖
      ≤ ∫ x, |riccatiSource a (σk k) (εk k) x - riccatiSource a σ₀ 0 x| *
        Real.exp (R' * |x|) := norm_integral_le_of_norm_le hg_int (ae_of_all _ fun x => by
          rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_sub_comm]
          refine mul_le_mul_of_nonneg_left ((norm_cexp_I_mul_le_exp_abs z x).trans ?_) (abs_nonneg _)
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzR (abs_nonneg _)))
    _ < δ := hk

/-! ## Order-one growth of the damped transform -/

theorem mul_sub_exp_le_mul_log {s κ y : ℝ} (hs : 0 ≤ s) (hκ : 0 < κ) :
    s * y - κ * Real.exp y ≤ s * Real.log (1 + s / κ) := by
  set y₀ := Real.log (1 + s / κ)
  have h1 : 0 < 1 + s / κ := by positivity
  have hey₀ : Real.exp y₀ = 1 + s / κ := Real.exp_log h1
  rcases le_or_gt y y₀ with hy | hy
  · have := mul_le_mul_of_nonneg_left hy hs
    have := Real.exp_pos y
    nlinarith
  · have hexp : Real.exp y₀ * (1 + (y - y₀)) ≤ Real.exp y := by
      rw [show Real.exp y = Real.exp y₀ * Real.exp (y - y₀) by rw [← Real.exp_add]; ring_nf]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (y - y₀)])
        (Real.exp_pos _).le
    rw [hey₀] at hexp
    have hk : κ * (1 + s / κ) = κ + s := by field_simp
    have := mul_le_mul_of_nonneg_left hexp hκ.le
    nlinarith

theorem exp_abs_div_le_two_cosh (x σ : ℝ) : Real.exp (|x| / σ) ≤ 2 * Real.cosh (x / σ) := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-(x / σ))]
  · rw [h, neg_div]; linarith [Real.exp_pos (x / σ)]

theorem integrable_exp_neg_exp_abs {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Integrable (fun x : ℝ => Real.exp (-(κ * Real.exp (|x| / σ)))) := by
  have hb : -(κ / (2 * σ ^ 2)) < 0 := by
    have : 0 < κ / (2 * σ ^ 2) := by positivity
    linarith
  refine Integrable.mono' (integrable_exp_quadratic_real hb 0 0) (by fun_prop)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.mpr ?_
  have hy : 0 ≤ |x| / σ := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy
  have h2 : (|x| / σ) ^ 2 = x ^ 2 / σ ^ 2 := by rw [div_pow, sq_abs]
  have h3 : x ^ 2 / (2 * σ ^ 2) ≤ Real.exp (|x| / σ) := by
    have e : x ^ 2 / (2 * σ ^ 2) = (|x| / σ) ^ 2 / 2 := by rw [h2]; ring
    linarith
  have h4 : κ * (x ^ 2 / (2 * σ ^ 2)) ≤ κ * Real.exp (|x| / σ) :=
    mul_le_mul_of_nonneg_left h3 hκ.le
  have e : -(κ / (2 * σ ^ 2)) * x ^ 2 + 0 * x + 0 = -(κ * (x ^ 2 / (2 * σ ^ 2))) := by ring
  linarith

/-- **Order-one growth.**  For `ε > 0`,
`‖F_ε(z)‖ ≤ C exp(σ‖z‖ log(1 + 4σ‖z‖/ε))`. -/
theorem norm_riccatiFourier_le {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C, 0 < C ∧ ∀ z : ℂ, ‖riccatiFourier a σ ε z‖ ≤
      C * Real.exp (σ * ‖z‖ * Real.log (1 + 4 * σ * ‖z‖ / ε)) := by
  set K := ∫ x : ℝ, Real.exp (-(ε / 4 * Real.exp (|x| / σ)))
  have hKi := integrable_exp_neg_exp_abs hσ (by positivity : 0 < ε / 4)
  have hK : 0 < K := integral_exp_pos hKi
  refine ⟨(1 + 2 * a) * Real.exp ε * K, by positivity, fun z => ?_⟩
  set R := ‖z‖
  have hR : 0 ≤ R := norm_nonneg z
  have hpt : ∀ x : ℝ, riccatiSource a σ ε x * Real.exp (R * |x|) ≤
      (1 + 2 * a) * Real.exp ε * Real.exp (σ * R * Real.log (1 + 4 * σ * R / ε)) *
        Real.exp (-(ε / 4 * Real.exp (|x| / σ))) := by
    intro x
    have hbase : riccatiBase a σ x ≤ 1 + 2 * a := by
      unfold riccatiBase
      have := riccatiGauss_le_one σ x
      have := riccatiGauss_le_one σ (x - σ / 2)
      have := riccatiGauss_le_one σ (x + σ / 2)
      nlinarith
    have hdamp : Real.exp (-(ε * (Real.cosh (x / σ) - 1))) ≤
        Real.exp ε * Real.exp (-(ε / 2 * Real.exp (|x| / σ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have := exp_abs_div_le_two_cosh x σ
      nlinarith
    have hlog := mul_sub_exp_le_mul_log (s := σ * R) (κ := ε / 4) (y := |x| / σ) (by positivity)
      (by positivity)
    have hlog' : R * |x| - ε / 4 * Real.exp (|x| / σ) ≤
        σ * R * Real.log (1 + 4 * σ * R / ε) := by
      have e1 : σ * R * (|x| / σ) = R * |x| := by field_simp
      have e2 : σ * R / (ε / 4) = 4 * σ * R / ε := by field_simp
      rw [e1, e2] at hlog
      exact hlog
    have hs0 : 0 ≤ riccatiBase a σ x := by unfold riccatiBase riccatiGauss; positivity
    unfold riccatiSource
    calc Real.exp (-(ε * (Real.cosh (x / σ) - 1))) * riccatiBase a σ x * Real.exp (R * |x|)
        ≤ Real.exp ε * Real.exp (-(ε / 2 * Real.exp (|x| / σ))) * (1 + 2 * a) *
            Real.exp (R * |x|) := by gcongr
      _ = (1 + 2 * a) * Real.exp ε * Real.exp (R * |x| - ε / 4 * Real.exp (|x| / σ)) *
            Real.exp (-(ε / 4 * Real.exp (|x| / σ))) := by
          have e : Real.exp (R * |x| - ε / 4 * Real.exp (|x| / σ)) *
              Real.exp (-(ε / 4 * Real.exp (|x| / σ))) =
              Real.exp (-(ε / 2 * Real.exp (|x| / σ))) * Real.exp (R * |x|) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          rw [mul_assoc ((1 + 2 * a) * Real.exp ε), e]
          ring
      _ ≤ _ := by gcongr
  have hint : Integrable (fun x : ℝ => riccatiSource a σ ε x * Real.exp (R * |x|)) :=
    integrable_riccatiSource_mul_exp_abs ha hσ hε.le R
  unfold riccatiFourier
  calc ‖∫ x : ℝ, (riccatiSource a σ ε x : ℂ) * Complex.exp (I * z * x)‖
      ≤ ∫ x : ℝ, riccatiSource a σ ε x * Real.exp (R * |x|) :=
        norm_integral_le_of_norm_le hint (ae_of_all _ fun x => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (riccatiSource_nonneg ha x)]
          refine mul_le_mul_of_nonneg_left ((norm_cexp_I_mul_le_exp_abs z x).trans ?_)
            (riccatiSource_nonneg ha x)
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z)
            (abs_nonneg _)))
    _ ≤ ∫ x : ℝ, (1 + 2 * a) * Real.exp ε * Real.exp (σ * R * Real.log (1 + 4 * σ * R / ε)) *
          Real.exp (-(ε / 4 * Real.exp (|x| / σ))) :=
        integral_mono hint (hKi.const_mul _) hpt
    _ = (1 + 2 * a) * Real.exp ε * K * Real.exp (σ * R * Real.log (1 + 4 * σ * R / ε)) := by
        rw [integral_const_mul]; ring

/-- **Entire of order at most one.**  For every `δ > 0`, `‖F_ε(z)‖ ≤ exp(‖z‖^{1+δ})` for all
large `‖z‖`. -/
theorem riccatiFourier_order_le_one {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ R₀, ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖riccatiFourier a σ ε z‖ ≤ Real.exp (‖z‖ ^ (1 + δ)) := by
  obtain ⟨C, hC, hbound⟩ := norm_riccatiFourier_le ha hσ hε
  set K := 2 * σ * (8 * σ / ε) ^ (δ / 2) / δ
  set M := 2 * K + 2 * |Real.log C| + 1
  have hK : 0 ≤ K := by positivity
  have hM : 1 ≤ M := by have := abs_nonneg (Real.log C); linarith
  refine ⟨max (max 1 (ε / (4 * σ))) (M ^ (2 / δ)), fun z hz => ?_⟩
  set R := ‖z‖
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hRε : ε / (4 * σ) ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hRM : M ^ (2 / δ) ≤ R := le_trans (le_max_right _ _) hz
  have hR0 : 0 < R := by linarith
  have hRδ : M ≤ R ^ (δ / 2) := by
    have h := Real.rpow_le_rpow (by positivity) hRM (by positivity : 0 ≤ δ / 2)
    rwa [← Real.rpow_mul (by linarith), show 2 / δ * (δ / 2) = 1 by field_simp,
      Real.rpow_one] at h
  have hu : 1 ≤ 4 * σ * R / ε := by
    rw [le_div_iff₀ hε, one_mul]
    have := mul_le_mul_of_nonneg_left hRε (by positivity : (0 : ℝ) ≤ 4 * σ)
    rw [show 4 * σ * (ε / (4 * σ)) = ε by field_simp] at this
    linarith
  have hlog : Real.log (1 + 4 * σ * R / ε) ≤ (8 * σ * R / ε) ^ (δ / 2) / (δ / 2) := by
    refine le_trans (Real.log_le_log (by positivity) (show 1 + 4 * σ * R / ε ≤ 8 * σ * R / ε by
      have : 8 * σ * R / ε = 2 * (4 * σ * R / ε) := by ring
      linarith)) ?_
    exact Real.log_le_rpow_div (by positivity) (by positivity)
  have hsplit : (8 * σ * R / ε) ^ (δ / 2) = (8 * σ / ε) ^ (δ / 2) * R ^ (δ / 2) := by
    rw [show 8 * σ * R / ε = 8 * σ / ε * R by ring, Real.mul_rpow (by positivity) hR0.le]
  have hmain : σ * R * Real.log (1 + 4 * σ * R / ε) ≤ K * R ^ (1 + δ / 2) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ σ * R)
    rw [hsplit] at h1
    rw [Real.rpow_add hR0, Real.rpow_one]
    calc σ * R * Real.log (1 + 4 * σ * R / ε) ≤
        σ * R * ((8 * σ / ε) ^ (δ / 2) * R ^ (δ / 2) / (δ / 2)) := h1
      _ = K * (R * R ^ (δ / 2)) := by simp only [K]; field_simp
  have hpow : R ^ (1 + δ) = R ^ (1 + δ / 2) * R ^ (δ / 2) := by
    rw [← Real.rpow_add hR0]; ring_nf
  have hR1' : 1 ≤ R ^ (1 + δ / 2) := Real.one_le_rpow hR1 (by positivity)
  have hfinal : Real.log C + σ * R * Real.log (1 + 4 * σ * R / ε) ≤ R ^ (1 + δ) := by
    rw [hpow]
    have h2 : M * R ^ (1 + δ / 2) ≤ R ^ (1 + δ / 2) * R ^ (δ / 2) := by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left hRδ (by positivity)
    have h3 : Real.log C ≤ |Real.log C| * R ^ (1 + δ / 2) := by
      have := le_abs_self (Real.log C)
      nlinarith [abs_nonneg (Real.log C)]
    nlinarith
  calc ‖riccatiFourier a σ ε z‖ ≤ C * Real.exp (σ * R * Real.log (1 + 4 * σ * R / ε)) := hbound z
    _ = Real.exp (Real.log C + σ * R * Real.log (1 + 4 * σ * R / ε)) := by
        rw [Real.exp_add, Real.exp_log hC]
    _ ≤ Real.exp (R ^ (1 + δ)) := Real.exp_le_exp.mpr hfinal

/-! ## Entire extension, derivative decay and real-analyticity -/

/-- The entire extension of the damped source. -/
noncomputable def riccatiSourceC (a σ ε : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(ε * (Complex.cosh (w / σ) - 1))) *
    (Complex.exp (-w ^ 2 / (2 * σ ^ 2)) + a * Complex.exp (-(w - σ / 2) ^ 2 / (2 * σ ^ 2)) +
      a * Complex.exp (-(w + σ / 2) ^ 2 / (2 * σ ^ 2)))

theorem differentiable_riccatiSourceC (a σ ε : ℝ) : Differentiable ℂ (riccatiSourceC a σ ε) := by
  unfold riccatiSourceC
  fun_prop

theorem riccatiSourceC_ofReal (a σ ε x : ℝ) :
    riccatiSourceC a σ ε x = (riccatiSource a σ ε x : ℂ) := by
  unfold riccatiSourceC riccatiSource riccatiBase riccatiGauss
  push_cast
  rfl

theorem re_ccosh (z : ℂ) : (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  rw [Complex.cosh, Complex.div_re, Complex.add_re, Complex.exp_re, Complex.exp_re,
    Complex.neg_re, Complex.neg_im, Real.cos_neg, Real.cosh_eq]
  simp
  ring

theorem norm_riccatiSourceC_le {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 ≤ ε) {w : ℂ}
    (hw : |w.im| ≤ min 1 σ) :
    ‖riccatiSourceC a σ ε w‖ ≤ (1 + 2 * a) * Real.exp (1 / 2) * Real.exp ε *
      Real.exp (-(ε * Real.cos 1 * Real.cosh (w.re / σ))) := by
  have hwσ : |w.im| ≤ σ := hw.trans (min_le_right _ _)
  have hw1 : |w.im / σ| ≤ 1 := by
    rw [abs_div, abs_of_pos hσ, div_le_one hσ]; exact hwσ
  have hcos : Real.cos 1 ≤ Real.cos (w.im / σ) := by
    rw [← Real.cos_abs (w.im / σ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) hw1
  have hre : (w / σ).re = w.re / σ := by simp
  have him : (w / σ).im = w.im / σ := by simp
  have hdamp : ‖Complex.exp (-(ε * (Complex.cosh (w / σ) - 1)))‖ ≤
      Real.exp ε * Real.exp (-(ε * Real.cos 1 * Real.cosh (w.re / σ))) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (-((ε : ℂ) * (Complex.cosh (w / σ) - 1))).re = ε - ε * (Complex.cosh (w / σ)).re := by
      simp [Complex.mul_re]
      ring
    rw [this, re_ccosh, hre, him]
    have hc := Real.cosh_pos (w.re / σ)
    have := mul_le_mul_of_nonneg_left hcos (by positivity : (0 : ℝ) ≤ ε * Real.cosh (w.re / σ))
    nlinarith
  have hg : ∀ m : ℝ, ‖Complex.exp (-(w - m) ^ 2 / (2 * σ ^ 2))‖ ≤ Real.exp (1 / 2) := by
    intro m
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
    have e : (-(w - m) ^ 2 / (2 * (σ : ℂ) ^ 2)).re =
        (w.im ^ 2 - (w.re - m) ^ 2) / (2 * σ ^ 2) := by
      have : (2 * (σ : ℂ) ^ 2) = ((2 * σ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.div_ofReal_re]
      simp [sq, Complex.mul_re]
    rw [e, div_le_iff₀ hσ2]
    have : w.im ^ 2 ≤ σ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hwσ 2
    nlinarith [sq_nonneg (w.re - m)]
  have hg0 := hg 0
  have hg1 := hg (σ / 2)
  have hg2 := hg (-(σ / 2))
  push_cast at hg0 hg1 hg2
  simp only [sub_zero, sub_neg_eq_add] at hg0 hg2
  unfold riccatiSourceC
  rw [norm_mul]
  have hsum : ‖Complex.exp (-w ^ 2 / (2 * (σ : ℂ) ^ 2)) +
      (a : ℂ) * Complex.exp (-(w - (σ : ℂ) / 2) ^ 2 / (2 * σ ^ 2)) +
      (a : ℂ) * Complex.exp (-(w + (σ : ℂ) / 2) ^ 2 / (2 * σ ^ 2))‖ ≤
      (1 + 2 * a) * Real.exp (1 / 2) := by
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
    nlinarith
  calc ‖Complex.exp (-(ε * (Complex.cosh (w / σ) - 1)))‖ * ‖_‖
      ≤ (Real.exp ε * Real.exp (-(ε * Real.cos 1 * Real.cosh (w.re / σ)))) *
        ((1 + 2 * a) * Real.exp (1 / 2)) :=
        mul_le_mul hdamp hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem contDiff_riccatiSource (a σ ε : ℝ) : ContDiff ℝ ⊤ (riccatiSource a σ ε) := by
  unfold riccatiSource riccatiBase riccatiGauss
  fun_prop

/-- **Real-analyticity.**  The damped source is real-analytic on `ℝ`. -/
theorem analyticAt_riccatiSource (a σ ε x : ℝ) : AnalyticAt ℝ (riccatiSource a σ ε) x := by
  have hG := ((differentiable_riccatiSourceC a σ ε).analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)
  have h := (Complex.reCLM.analyticAt _).comp (hG.comp (Complex.ofRealCLM.analyticAt x))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp [riccatiSourceC_ofReal]

/-- **Superexponential decay of every derivative.**  For `ε > 0`, every derivative of the damped
source decays faster than every exponential. -/
theorem iteratedDeriv_riccatiSource_decay {a σ ε : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hε : 0 < ε)
    (k : ℕ) (A : ℝ) : ∃ C, ∀ x : ℝ,
      |iteratedDeriv k (riccatiSource a σ ε) x| ≤ C * Real.exp (-(A * |x|)) := by
  set A' := max A 0
  set ρ := min 1 σ
  have hρ : 0 < ρ := lt_min one_pos hσ
  set κ := ε * Real.cos 1 * Real.exp (-(1 / σ)) / 2
  have hκ : 0 < κ := by have := Real.cos_one_pos; positivity
  set B := (1 + 2 * a) * Real.exp (1 / 2) * Real.exp ε
  set L := A' * σ * Real.log (1 + A' * σ / κ)
  refine ⟨k.factorial * (B * Real.exp L * Real.exp A') / ρ ^ k, fun x => ?_⟩
  have htransfer : ((iteratedDeriv k (riccatiSource a σ ε) x : ℝ) : ℂ) =
      iteratedDeriv k (riccatiSourceC a σ ε) (x : ℂ) := by
    have h1 := GaloisForLFunctions.iteratedDeriv_ofReal_comp
      ((contDiff_riccatiSource a σ ε).of_le le_top) k
    have h2 := HTGeometry.iteratedDeriv_comp_ofReal k (differentiable_riccatiSourceC a σ ε)
    have e : (fun u : ℝ => ((riccatiSource a σ ε u : ℝ) : ℂ)) =
        fun u : ℝ => riccatiSourceC a σ ε (u : ℂ) := funext fun u => (riccatiSourceC_ofReal a σ ε u).symm
    rw [e, h2] at h1
    exact (congrFun h1 x).symm
  have hsphere : ∀ w ∈ Metric.sphere (x : ℂ) ρ,
      ‖riccatiSourceC a σ ε w‖ ≤ B * Real.exp L * Real.exp A' * Real.exp (-(A * |x|)) := by
    intro w hw
    have hdist : ‖w - x‖ = ρ := by rw [← dist_eq_norm]; exact hw
    have him : |w.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (w - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hdist] at this
      exact this
    have hre : |x| - 1 ≤ |w.re| := by
      have h1 := Complex.abs_re_le_norm (w - x)
      rw [Complex.sub_re, Complex.ofReal_re, hdist] at h1
      have := abs_sub_abs_le_abs_sub x w.re
      rw [abs_sub_comm] at this
      have : ρ ≤ 1 := min_le_left _ _
      linarith
    refine (norm_riccatiSourceC_le ha hσ hε.le him).trans ?_
    have hcosh : Real.exp (|x| / σ) * Real.exp (-(1 / σ)) / 2 ≤ Real.cosh (w.re / σ) := by
      have h := exp_abs_div_le_two_cosh w.re σ
      have : Real.exp (|x| / σ) * Real.exp (-(1 / σ)) ≤ Real.exp (|w.re| / σ) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        rw [show |x| / σ + -(1 / σ) = (|x| - 1) / σ by ring]
        exact div_le_div_of_nonneg_right hre hσ.le
      linarith
    have hkey : -(ε * Real.cos 1 * Real.cosh (w.re / σ)) ≤ -(κ * Real.exp (|x| / σ)) := by
      have := mul_le_mul_of_nonneg_left hcosh
        (by have := Real.cos_one_pos; positivity : (0 : ℝ) ≤ ε * Real.cos 1)
      simp only [κ]
      nlinarith
    have hlog := mul_sub_exp_le_mul_log (s := A' * σ) (κ := κ) (y := |x| / σ)
      (by positivity) hκ
    rw [show A' * σ * (|x| / σ) = A' * |x| by field_simp] at hlog
    have hA : A * |x| ≤ A' * |x| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    have hexp : Real.exp (-(ε * Real.cos 1 * Real.cosh (w.re / σ))) ≤
        Real.exp L * Real.exp A' * Real.exp (-(A * |x|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ A' := le_max_right _ _
      linarith
    calc B * Real.exp (-(ε * Real.cos 1 * Real.cosh (w.re / σ)))
        ≤ B * (Real.exp L * Real.exp A' * Real.exp (-(A * |x|))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hC := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ
    (differentiable_riccatiSourceC a σ ε).diffContOnCl hsphere
  rw [← htransfer, Complex.norm_real, Real.norm_eq_abs] at hC
  calc |iteratedDeriv k (riccatiSource a σ ε) x|
      ≤ k.factorial * (B * Real.exp L * Real.exp A' * Real.exp (-(A * |x|))) / ρ ^ k := hC
    _ = _ := by ring

/-! ## Persistence of the selected spectral zeros -/

/-- The isolation radius `min(π, A₀)/σ`. -/
noncomputable def riccatiRadius (a σ : ℝ) : ℝ := min Real.pi (riccatiDepth a) / σ

theorem riccatiRadius_pos {a σ : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 < σ) :
    0 < riccatiRadius a σ := by
  unfold riccatiRadius
  have := riccatiDepth_pos ha ha2
  have := Real.pi_pos
  positivity

/-- **Hurwitz persistence.**  Along damping/scale sequences converging to `(σ₀, 0)`, eventually
every closed ball of radius `min(π, A₀)/σ₀` around a selected zero `z_n` contains a zero of the
damped transform. -/
theorem eventually_riccatiZeros {ι : Type*} [Finite ι] {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {σk εk : ℕ → ℝ} (hσk : ∀ k, 0 < σk k) (hεk : ∀ k, 0 ≤ εk k)
    (hσlim : Tendsto σk atTop (𝓝 σ₀)) (hεlim : Tendsto εk atTop (𝓝 0)) (n : ι → ℤ) :
    ∀ᶠ k in atTop, ∀ j, ∃ w ∈ Metric.closedBall (riccatiZero a σ₀ (n j)) (riccatiRadius a σ₀),
      riccatiFourier a (σk k) (εk k) w = 0 := by
  rw [Filter.eventually_all]
  intro j
  refine GaloisForLFunctions.HTGeometry.eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_riccatiFourier ha.le hσ₀ hσk hεk hσlim hεlim)
    (differentiable_riccatiFourier ha.le hσ₀ le_rfl)
    (Eventually.of_forall fun k => differentiable_riccatiFourier ha.le (hσk k) (hεk k))
    (riccatiRadius_pos ha ha2 hσ₀) (riccatiFourier_riccatiZero ha ha2.le hσ₀ (n j))
    (fun w hw hw0 => ?_)
  have hr := riccatiRadius_pos ha ha2 hσ₀
  have hwd : ‖w - riccatiZero a σ₀ (n j)‖ = riccatiRadius a σ₀ := by
    rw [← dist_eq_norm]; exact hw
  have heq := riccatiZero_isolated ha ha2 hσ₀ (n j) hw0 (by
    rw [hwd]; unfold riccatiRadius
    have : 0 < min Real.pi (riccatiDepth a) := lt_min Real.pi_pos (riccatiDepth_pos ha ha2)
    rw [div_lt_div_iff_of_pos_right hσ₀]
    linarith)
  rw [heq, sub_self, norm_zero] at hwd
  linarith

theorem riccatiZero_re (a σ : ℝ) (n : ℤ) :
    (riccatiZero a σ n).re = 2 / σ * ((2 * n + 1) * Real.pi) := by
  unfold riccatiZero
  simp

theorem riccatiZero_im (a σ : ℝ) (n : ℤ) : (riccatiZero a σ n).im = 2 / σ * riccatiDepth a := by
  unfold riccatiZero
  simp

/-! ## Symmetry of the transform -/

theorem riccatiFourier_neg (a σ ε : ℝ) (z : ℂ) : riccatiFourier a σ ε (-z) = riccatiFourier a σ ε z := by
  unfold riccatiFourier
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [riccatiSource_neg, Complex.ofReal_neg]
  ring_nf

theorem riccatiFourier_conj (a σ ε : ℝ) (z : ℂ) :
    riccatiFourier a σ ε ((starRingEnd ℂ) z) = (starRingEnd ℂ) (riccatiFourier a σ ε z) := by
  unfold riccatiFourier
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal, riccatiSource_neg, ← Complex.exp_conj,
    Complex.conj_I, Complex.ofReal_neg]
  ring_nf

/-! ## The global Riccati countermodel -/

/-- **Global reflected Riccati positivity does not orient an order-one Fourier divisor.**
For every `N`, `η > 0` and `α < β` there are parameters such that `g = g_ε` is strictly positive,
even, real-analytic, has superexponentially decaying derivatives, an entire Fourier transform of
order at most one, strictly concave logarithm with the strict global reflected Riccati law, and
at least `N` distinct Fourier zeros with `Re z ∈ (α, β)` and `0 < Im z < η`. -/
theorem globalRiccati_offline_countermodel (N : ℕ) {η : ℝ} (hη : 0 < η) {α β : ℝ}
    (hαβ : α < β) :
    ∃ a σ ε : ℝ, 0 < a ∧ a < 1 / 2 ∧ 0 < σ ∧ 0 < ε ∧
      (∀ x, 0 < riccatiSource a σ ε x) ∧
      (∀ x, riccatiSource a σ ε (-x) = riccatiSource a σ ε x) ∧
      (∀ x, AnalyticAt ℝ (riccatiSource a σ ε) x) ∧
      (∀ (k : ℕ) (A : ℝ), ∃ C, ∀ x : ℝ,
        |iteratedDeriv k (riccatiSource a σ ε) x| ≤ C * Real.exp (-(A * |x|))) ∧
      Differentiable ℂ (riccatiFourier a σ ε) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R₀, ∀ z : ℂ, R₀ ≤ ‖z‖ →
        ‖riccatiFourier a σ ε z‖ ≤ Real.exp (‖z‖ ^ (1 + δ))) ∧
      StrictConcaveOn ℝ univ (fun x => Real.log (riccatiSource a σ ε x)) ∧
      (∀ u t, riccatiAction a σ ε u t = 2 * Real.log (riccatiSource a σ ε u) -
        Real.log (riccatiSource a σ ε (u + t)) - Real.log (riccatiSource a σ ε (u - t))) ∧
      (∀ u t, HasDerivAt (riccatiAction a σ ε u) (riccatiJetOne a σ ε u t) t) ∧
      (∀ u t, HasDerivAt (riccatiJetOne a σ ε u) (riccatiJetTwo a σ ε u t) t) ∧
      (∀ u t, HasDerivAt (riccatiJetTwo a σ ε u) (riccatiJetThree a σ ε u t) t) ∧
      (∀ u t, 0 < t → 0 < riccatiAction a σ ε u t ∧ 0 < riccatiJetOne a σ ε u t ∧
        0 < riccatiJetTwo a σ ε u t ∧ 0 < riccatiMargin a σ ε u t) ∧
      ∃ w : Fin N → ℂ, Function.Injective w ∧ ∀ j, riccatiFourier a σ ε (w j) = 0 ∧
        (w j).re ∈ Ioo α β ∧ 0 < (w j).im ∧ (w j).im < η := by
  set a : ℝ := 1 / 4
  have ha : 0 < a := by norm_num [a]
  have ha2 : a < 1 / 2 := by norm_num [a]
  set A₀ := riccatiDepth a
  have hA₀ := riccatiDepth_pos ha ha2
  set σ := max (3 * A₀ / η) ((4 * N + 3) * Real.pi / (β - α)) + 1
  have hσ1 : 3 * A₀ / η < σ := by
    have := le_max_left (3 * A₀ / η) ((4 * N + 3) * Real.pi / (β - α)); linarith
  have hσ2 : (4 * N + 3) * Real.pi / (β - α) < σ := by
    have := le_max_right (3 * A₀ / η) ((4 * N + 3) * Real.pi / (β - α)); linarith
  have hσ : 0 < σ := lt_of_le_of_lt (by positivity) hσ1
  set n₀ : ℤ := ⌈α * σ / (4 * Real.pi)⌉
  set n : Fin N → ℤ := fun j => n₀ + j
  have hev := eventually_riccatiZeros ha ha2 hσ (σk := fun _ => σ)
    (εk := fun k => 1 / ((k : ℝ) + 1)) (fun _ => hσ) (fun k => by positivity)
    tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat n
  obtain ⟨k, hk⟩ := hev.exists
  set ε : ℝ := 1 / ((k : ℝ) + 1)
  have hε : 0 < ε := by positivity
  choose w hwball hwzero using hk
  set r := riccatiRadius a σ
  have hr : 0 < r := riccatiRadius_pos ha ha2 hσ
  have hrπ : r ≤ Real.pi / σ := div_le_div_of_nonneg_right (min_le_left _ _) hσ.le
  have hrA : r ≤ A₀ / σ := div_le_div_of_nonneg_right (min_le_right _ _) hσ.le
  have hre : ∀ j, |(w j).re - (riccatiZero a σ (n j)).re| ≤ r := fun j => by
    have := Complex.abs_re_le_norm (w j - riccatiZero a σ (n j))
    rw [Complex.sub_re] at this
    exact this.trans (by rw [← dist_eq_norm]; exact hwball j)
  have him : ∀ j, |(w j).im - (riccatiZero a σ (n j)).im| ≤ r := fun j => by
    have := Complex.abs_im_le_norm (w j - riccatiZero a σ (n j))
    rw [Complex.sub_im] at this
    exact this.trans (by rw [← dist_eq_norm]; exact hwball j)
  have hn₀ : α * σ / (4 * Real.pi) ≤ n₀ := Int.le_ceil _
  have hn₀' : (n₀ : ℝ) < α * σ / (4 * Real.pi) + 1 := Int.ceil_lt_add_one _
  refine ⟨a, σ, ε, ha, ha2, hσ, hε, riccatiSource_pos ha.le hσ.ne' ε,
    riccatiSource_neg a σ ε, analyticAt_riccatiSource a σ ε,
    iteratedDeriv_riccatiSource_decay ha.le hσ hε, differentiable_riccatiFourier ha.le hσ hε.le,
    fun δ hδ => riccatiFourier_order_le_one ha.le hσ hε hδ,
    strictConcaveOn_log_riccatiSource ha.le hσ hε.le, fun u t => ?_,
    hasDerivAt_riccatiAction ha.le hσ.ne' ε, hasDerivAt_riccatiJetOne ha.le hσ.ne' ε,
    hasDerivAt_riccatiJetTwo ha.le hσ.ne' ε,
    fun u t ht => riccati_reflected_positivity ha.le hσ hε.le u ht, w, ?_, fun j => ?_⟩
  · unfold riccatiAction
    simp only [riccatiSource_eq_exp ha.le hσ.ne', Real.log_exp]
  · intro i j hij
    by_contra hne
    have hnij : n i ≠ n j := by
      simp only [n]; intro h; exact hne (Fin.ext (by exact_mod_cast add_left_cancel h))
    have hdist : 4 * Real.pi / σ ≤
        |(riccatiZero a σ (n i)).re - (riccatiZero a σ (n j)).re| := by
      rw [riccatiZero_re, riccatiZero_re, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
      have hk1 : (1 : ℝ) ≤ |((n i : ℝ) - n j)| := by
        have : (1 : ℤ) ≤ |n i - n j| := Int.one_le_abs (sub_ne_zero.mpr hnij)
        exact_mod_cast this
      rw [show (2 * (n i : ℝ) + 1) * Real.pi - (2 * (n j : ℝ) + 1) * Real.pi =
        2 * Real.pi * ((n i : ℝ) - n j) by ring, abs_mul, abs_of_pos (by positivity)]
      have : 2 / σ * (2 * Real.pi * 1) ≤ 2 / σ * (2 * Real.pi * |(n i : ℝ) - n j|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk1 (by positivity)) (by positivity)
      calc 4 * Real.pi / σ = 2 / σ * (2 * Real.pi * 1) := by ring
        _ ≤ _ := this
    have h1 := hre i
    have h2 := hre j
    rw [hij] at h1
    have := abs_sub_le ((riccatiZero a σ (n i)).re) ((w j).re) ((riccatiZero a σ (n j)).re)
    rw [abs_sub_comm] at h1
    have h4 : 4 * Real.pi / σ ≤ 2 * r := by linarith
    have : 2 * r ≤ 2 * (Real.pi / σ) := by linarith
    have : 0 < Real.pi / σ := by positivity
    have : 4 * Real.pi / σ = 4 * (Real.pi / σ) := by ring
    linarith
  · refine ⟨hwzero j, ?_, ?_, ?_⟩
    · have hj := hre j
      rw [riccatiZero_re] at hj
      have hjN : (j : ℝ) ≤ N - 1 := by
        have := j.isLt
        have : (j : ℕ) + 1 ≤ N := this
        have : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
        linarith
      have hnj : (n j : ℝ) = n₀ + j := by simp [n]
      rw [hnj] at hj
      constructor
      · have hlow : α < 2 / σ * ((2 * ((n₀ : ℝ) + j) + 1) * Real.pi) - r := by
          have e1 : α ≤ 4 * Real.pi * n₀ / σ := by
            rw [le_div_iff₀ hσ]
            have := mul_le_mul_of_nonneg_left hn₀ (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
            rw [show 4 * Real.pi * (α * σ / (4 * Real.pi)) = α * σ by field_simp] at this
            linarith
          have e2 : 2 / σ * ((2 * ((n₀ : ℝ) + j) + 1) * Real.pi) - r ≥
              4 * Real.pi * n₀ / σ + Real.pi / σ := by
            have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
            have : 2 / σ * ((2 * ((n₀ : ℝ) + j) + 1) * Real.pi) =
                4 * Real.pi * n₀ / σ + 4 * Real.pi * j / σ + 2 * Real.pi / σ := by
              field_simp; ring
            rw [this]
            have : 0 ≤ 4 * Real.pi * j / σ := by positivity
            have : 2 * Real.pi / σ = Real.pi / σ + Real.pi / σ := by ring
            linarith
          have : 0 < Real.pi / σ := by positivity
          linarith
        rw [abs_le] at hj
        linarith
      · have hupp : 2 / σ * ((2 * ((n₀ : ℝ) + j) + 1) * Real.pi) + r < β := by
          have e1 : 4 * Real.pi * n₀ / σ < α + 4 * Real.pi / σ := by
            rw [div_lt_iff₀ hσ]
            have := mul_lt_mul_of_pos_left hn₀' (by positivity : (0 : ℝ) < 4 * Real.pi)
            rw [mul_add, show 4 * Real.pi * (α * σ / (4 * Real.pi)) = α * σ by field_simp] at this
            have e : (α + 4 * Real.pi / σ) * σ = α * σ + 4 * Real.pi := by field_simp
            linarith
          have e2 : (4 * N + 3) * Real.pi / σ < β - α := by
            rw [div_lt_iff₀ hσ]
            rw [div_lt_iff₀ (by linarith)] at hσ2
            linarith
          have : 2 / σ * ((2 * ((n₀ : ℝ) + j) + 1) * Real.pi) =
              4 * Real.pi * n₀ / σ + 4 * Real.pi * j / σ + 2 * Real.pi / σ := by
            field_simp; ring
          rw [this]
          have hjle : 4 * Real.pi * j / σ ≤ 4 * Real.pi * (N - 1) / σ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjN (by positivity)) hσ.le
          have e3 : (4 * N + 3) * Real.pi / σ =
              4 * Real.pi / σ + 4 * Real.pi * (N - 1) / σ + 2 * Real.pi / σ + Real.pi / σ := by
            field_simp; ring
          linarith
        rw [abs_le] at hj
        linarith
    · have hj := him j
      rw [riccatiZero_im, abs_le] at hj
      have e : 2 / σ * riccatiDepth a = 2 * (A₀ / σ) := by simp only [A₀]; ring
      have hAσ : 0 < A₀ / σ := by positivity
      linarith
    · have hj := him j
      rw [riccatiZero_im, abs_le] at hj
      have h3 : 3 * A₀ / σ < η := by
        rw [div_lt_iff₀ hσ]
        rw [div_lt_iff₀ hη] at hσ1
        linarith
      have e : 2 / σ * riccatiDepth a = 2 * (A₀ / σ) := by simp only [A₀]; ring
      have e3 : 3 * A₀ / σ = 3 * (A₀ / σ) := by ring
      linarith

/-- The zeros `z_n` are simple: `F₀'(z_n) ≠ 0`. -/
theorem riccatiZero_simple {a σ : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 < σ) (n : ℤ) :
    deriv (riccatiFourier a σ 0) (riccatiZero a σ n) ≠ 0 := by
  set P : ℂ → ℂ := fun z => ((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (-(σ ^ 2 * z ^ 2 / 2))
  set Q : ℂ → ℂ := fun z => 1 + 2 * a * Complex.cos (σ * z / 2)
  have hF : riccatiFourier a σ 0 = fun z => P z * Q z := funext fun z => riccatiFourier_zero hσ a z
  set z₀ := riccatiZero a σ n
  have hP : HasDerivAt P (((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      (Complex.exp (-(σ ^ 2 * z₀ ^ 2 / 2)) * (-(σ ^ 2 * (2 * z₀) / 2)))) z₀ := by
    have h0 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z₀) z₀ := by
      simpa using hasDerivAt_pow 2 z₀
    have h1 : HasDerivAt (fun z : ℂ => -((σ : ℂ) ^ 2 * z ^ 2 / 2)) (-((σ : ℂ) ^ 2 * (2 * z₀) / 2))
        z₀ := ((h0.const_mul ((σ : ℂ) ^ 2)).div_const 2).neg
    exact h1.cexp.const_mul _
  have hQ : HasDerivAt Q (2 * a * (-Complex.sin (σ * z₀ / 2) * (σ / 2))) z₀ := by
    have h1 : HasDerivAt (fun z : ℂ => (σ : ℂ) * z / 2) ((σ : ℂ) / 2) z₀ := by
      simpa using ((hasDerivAt_id' z₀).const_mul (σ : ℂ)).div_const 2
    exact ((h1.ccos.const_mul (2 * (a : ℂ))).const_add 1)
  have hQ0 : Q z₀ = 0 := by
    have := riccatiFourier_riccatiZero ha ha2.le hσ n
    rw [riccatiFourier_zero_eq_zero_iff hσ] at this
    exact this
  have hPQ : HasDerivAt (fun z => P z * Q z) (((σ * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      (Complex.exp (-(σ ^ 2 * z₀ ^ 2 / 2)) * (-(σ ^ 2 * (2 * z₀) / 2))) * Q z₀ +
      P z₀ * (2 * a * (-Complex.sin (σ * z₀ / 2) * (σ / 2)))) z₀ := hP.mul hQ
  rw [hF, hPQ.deriv, hQ0, mul_zero, zero_add]
  have hPz : P z₀ ≠ 0 := by
    simp only [P]
    exact mul_ne_zero (by exact_mod_cast (by positivity : σ * Real.sqrt (2 * Real.pi) ≠ 0))
      (Complex.exp_ne_zero _)
  have hsin : Complex.sin (σ * z₀ / 2) ≠ 0 := by
    have hz : (σ : ℂ) * z₀ / 2 = Real.pi + (riccatiDepth a : ℂ) * I + (n : ℂ) * (2 * Real.pi) := by
      simp only [z₀]
      unfold riccatiZero
      have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
      push_cast
      field_simp
      ring
    rw [hz, Complex.sin_add_int_mul_two_pi, Complex.sin_add_mul_I, Complex.sin_pi, Complex.cos_pi,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
    have hs : Real.sinh (riccatiDepth a) ≠ 0 := (Real.sinh_pos_iff.mpr (riccatiDepth_pos ha ha2)).ne'
    intro h
    have : ((Real.sinh (riccatiDepth a) : ℝ) : ℂ) = 0 := by
      have h' : (0 : ℂ) * Real.cosh (riccatiDepth a) + -1 * Real.sinh (riccatiDepth a) * I = 0 := h
      have : -((Real.sinh (riccatiDepth a) : ℂ) * I) = 0 := by rw [← h']; ring
      have := neg_eq_zero.mp this
      exact (mul_eq_zero.mp this).resolve_right Complex.I_ne_zero
    exact hs (by exact_mod_cast this)
  refine mul_ne_zero hPz ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  refine mul_ne_zero (mul_ne_zero (by norm_num) ha') (mul_ne_zero (neg_ne_zero.mpr hsin) ?_)
  exact div_ne_zero hσ' (by norm_num)

end RHTower
