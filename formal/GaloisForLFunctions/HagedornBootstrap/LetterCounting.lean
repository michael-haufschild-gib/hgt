import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Letters of free `𝒩 = 4` super Yang–Mills on `S³` and the Hagedorn point

On a unit three-sphere each free field is a tower of oscillators. Counting the modes of the six
conformally coupled scalars, the four Weyl fermions and the transverse gauge field by energy gives
one uniform law: at energy `k/2` there are `2(k² − 1)` letters (`letterCount`). With `y = e^{-β/2}`
the single-letter partition function is therefore
`z(y) = Σ 2(k² − 1) yᵏ = 2y²(3 − y)/(1 − y)³` (`hasSum_letterCount`).

* The bosonic and fermionic parts are `z_B(x) = (6x + 12x² − 2x³)/(1 − x)³` and
  `z_F = 16 y³/(1 − y²)³`, with `z(y) = z_B(y²) + z_F(y)`. The transverse gauge field alone has the
  same degeneracy law in `x = y²`, so its letter function in `x` is `z` itself.
* **Hagedorn point.** `z(y) = 1` is the cubic `(y + 1)(y² − 4y + 1) = 0`; its only root in
  `[0, 1)` is `y_H = 2 − √3 = (2 + √3)⁻¹`, and `z < 1` exactly below it.
* **Slope.** `z'(y) = 12y/(1 − y)⁴`, so the Polyakov-loop mass `1 − z(e^{-β/2})` has
  `β`-derivative `3/2` at `β₀ = 2 log(2 + √3)`.
* **One loop.** The one-loop mass coefficient `d₁` loses its logarithm at `y_H` and equals `3/2`
  there. The two values `3/2` cancel in the linearized mass, so the Hagedorn temperature is
  raised by exactly the factor `1 + 2g²`.
* **First soft mode.** Below `y_H` every winding mode `n` is massive; the mode `n = 1` is the
  first to go soft, since `z_n(y) ≤ z(yⁿ) < z(y)` for `n ≥ 2`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-- Transport a sum along pointwise equal terms and an equal value. -/
theorem hasSum_of_eq {f g : ℕ → ℝ} {a b : ℝ} (h : HasSum g b) (hf : ∀ n, f n = g n)
    (hab : a = b) : HasSum f a := by
  rw [funext hf, hab]; exact h

/-! ### Power sums against a geometric weight -/

/-- `Σ n² rⁿ = r(1 + r)/(1 − r)³`. -/
theorem hasSum_sq_mul_geometric {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs]
  have h1 : (1 - r) ≠ 0 := by linarith [(abs_lt.mp hr).2]
  have hC := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr'
  have hN := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr'
  have hG := hasSum_geometric_of_abs_lt_one hr
  -- `n² = 2·C(n+2, 2) − 3n − 2`
  have hsum := ((hC.mul_left 2).sub (hN.mul_left 3)).sub (hG.mul_left 2)
  refine hasSum_of_eq hsum (fun n => ?_) ?_
  · rw [Nat.cast_choose_two]
    push_cast
    ring
  · field_simp
    ring

/-- `Σ n(n + 1) rⁿ = 2r/(1 − r)³`. -/
theorem hasSum_mul_succ_mul_geometric {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * (n + 1) * r ^ n) (2 * r / (1 - r) ^ 3) := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs]
  have h1 : (1 - r) ≠ 0 := by linarith [(abs_lt.mp hr).2]
  have hsum := (hasSum_sq_mul_geometric hr).add (hasSum_coe_mul_geometric_of_norm_lt_one hr')
  refine hasSum_of_eq hsum (fun n => ?_) ?_
  · ring
  · field_simp; ring

/-! ### The letter census -/

/-- Number of letters of free `𝒩 = 4` super Yang–Mills on the unit `S³` at energy `k/2`. -/
def letterCount (k : ℕ) : ℕ := 2 * (k ^ 2 - 1)

theorem letterCount_cast_of_pos {k : ℕ} (hk : 1 ≤ k) :
    (letterCount k : ℝ) = 2 * ((k : ℝ) ^ 2 - 1) := by
  unfold letterCount
  rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hk)]
  push_cast
  ring

theorem letterCount_cast (k : ℕ) :
    (letterCount k : ℝ) = 2 * (k : ℝ) ^ 2 - 2 + if k = 0 then 2 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [letterCount]
  · rw [if_neg hk.ne', letterCount_cast_of_pos hk]
    ring

/-- Even energies `n`: six scalars contribute `6n²`, the gauge field `2(n² − 1)`. -/
theorem letterCount_two_mul (n : ℕ) : letterCount (2 * n) = 6 * n ^ 2 + letterCount n := by
  unfold letterCount
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    have h2 : 1 ≤ (2 * n) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring

/-- Half-odd energies `m + 1/2`: the fermions contribute `8m(m + 1)`. -/
theorem letterCount_two_mul_add_one (m : ℕ) : letterCount (2 * m + 1) = 8 * m * (m + 1) := by
  unfold letterCount
  have h : 1 ≤ (2 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h]
  ring

/-- The single-letter partition function `z(y) = 2y²(3 − y)/(1 − y)³`, `y = e^{-β/2}`. -/
def singleLetterZ (y : ℝ) : ℝ := 2 * y ^ 2 * (3 - y) / (1 - y) ^ 3

/-- The letter census sums to `z`: `Σ 2(k² − 1) yᵏ = 2y²(3 − y)/(1 − y)³`. -/
theorem hasSum_letterCount {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k : ℕ => (letterCount k : ℝ) * y ^ k) (singleLetterZ y) := by
  have h1 : (1 - y) ≠ 0 := by linarith [(abs_lt.mp hy).2]
  have hD : HasSum (fun k : ℕ => if k = 0 then (2 : ℝ) else 0) 2 := hasSum_ite_eq 0 2
  have hsum := (((hasSum_sq_mul_geometric hy).mul_left 2).sub
    ((hasSum_geometric_of_abs_lt_one hy).mul_left 2)).add hD
  refine hasSum_of_eq hsum (fun k => ?_) ?_
  · rw [letterCount_cast]
    split_ifs with h
    · subst h; norm_num
    · ring
  · unfold singleLetterZ
    field_simp
    ring

/-- Bosonic letters: `z_B(x) = (6x + 12x² − 2x³)/(1 − x)³`. -/
def bosonZ (x : ℝ) : ℝ := (6 * x + 12 * x ^ 2 - 2 * x ^ 3) / (1 - x) ^ 3

/-- Fermionic letters: `z_F = 16y³/(1 − y²)³`. -/
def fermionZ (y : ℝ) : ℝ := 16 * y ^ 3 / (1 - y ^ 2) ^ 3

/-- Scalars `6n²` and gauge modes `2(n² − 1)` at integer energy `n` sum to `z_B`. -/
theorem hasSum_bosonLetters {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((6 * n ^ 2 + letterCount n : ℕ) : ℝ) * x ^ n) (bosonZ x) := by
  have h1 : (1 - x) ≠ 0 := by linarith [(abs_lt.mp hx).2]
  have hsum := ((hasSum_sq_mul_geometric hx).mul_left 6).add (hasSum_letterCount hx)
  refine hasSum_of_eq hsum (fun n => ?_) ?_
  · push_cast; ring
  · unfold bosonZ singleLetterZ
    field_simp
    ring

/-- The fermions `8m(m + 1)` at energy `m + 1/2` sum to `z_F`. -/
theorem hasSum_fermionLetters {y : ℝ} (hy : |y| < 1) :
    HasSum (fun m : ℕ => ((8 * m * (m + 1) : ℕ) : ℝ) * y ^ (2 * m + 1)) (fermionZ y) := by
  have hy2 : |y ^ 2| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg y) hy (by norm_num)
  have h1 : (1 - y ^ 2) ≠ 0 := by
    have := (abs_lt.mp hy2).2; linarith
  have hsum := ((hasSum_mul_succ_mul_geometric hy2).mul_left (8 * y))
  refine hasSum_of_eq hsum (fun m => ?_) ?_
  · push_cast; ring
  · unfold fermionZ
    field_simp
    ring

/-- The census by parity: `z(y) = z_B(y²) + z_F(y)`. -/
theorem singleLetterZ_eq_boson_add_fermion {y : ℝ} (hy : |y| < 1) :
    singleLetterZ y = bosonZ (y ^ 2) + fermionZ y := by
  have h1 : (1 - y) ≠ 0 := by linarith [(abs_lt.mp hy).2]
  have h2 : (1 + y) ≠ 0 := by linarith [(abs_lt.mp hy).1]
  unfold singleLetterZ bosonZ fermionZ
  rw [show 1 - y ^ 2 = (1 - y) * (1 + y) by ring]
  field_simp
  ring

/-- The transverse gauge field alone, counted in `x`, has the full letter function:
its degeneracy `2(n² − 1)` at energy `n` is the census law at energy `k/2`. -/
theorem hasSum_gaugeLetters_eq_singleLetterZ {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (letterCount n : ℝ) * x ^ n) (singleLetterZ x) :=
  hasSum_letterCount hx

/-! ### The Hagedorn point -/

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The free Hagedorn point `y_H = 2 − √3`. -/
def hagedornY : ℝ := 2 - Real.sqrt 3

theorem hagedornY_pos : 0 < hagedornY := by unfold hagedornY; linarith [sqrt_three_lt_two]

theorem hagedornY_lt_one : hagedornY < 1 := by unfold hagedornY; linarith [one_lt_sqrt_three]

theorem hagedornY_quadratic : hagedornY ^ 2 - 4 * hagedornY + 1 = 0 := by
  unfold hagedornY; nlinarith [sqrt_three_sq]

/-- `y_H` is the inverse of the unit `2 + √3`. -/
theorem hagedornY_mul_unit : hagedornY * (2 + Real.sqrt 3) = 1 := by
  unfold hagedornY; nlinarith [sqrt_three_sq]

/-- The free Hagedorn Boltzmann factor `x_H = y_H² = 7 − 4√3`. -/
theorem hagedornY_sq : hagedornY ^ 2 = 7 - 4 * Real.sqrt 3 := by
  unfold hagedornY; nlinarith [sqrt_three_sq]

/-- The two companions of `y_H`: `(1 + y_H)² = 6y_H` and `(1 − y_H)² = 2y_H`. -/
theorem one_add_hagedornY_sq : (1 + hagedornY) ^ 2 = 6 * hagedornY := by
  nlinarith [hagedornY_quadratic]

theorem one_sub_hagedornY_sq : (1 - hagedornY) ^ 2 = 2 * hagedornY := by
  nlinarith [hagedornY_quadratic]

/-- `z − 1 = (y + 1)(y − y_H)((2 + √3) − y)/(1 − y)³`. -/
theorem singleLetterZ_sub_one {y : ℝ} (hy : y ≠ 1) :
    singleLetterZ y - 1 =
      (y + 1) * (y - hagedornY) * ((2 + Real.sqrt 3) - y) / (1 - y) ^ 3 := by
  have h1 : (1 - y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  unfold singleLetterZ
  rw [div_sub_one (pow_ne_zero 3 h1)]
  congr 1
  unfold hagedornY
  linear_combination (-(y + 1)) * sqrt_three_sq

/-- On `[0, 1)`, `z − 1` is a positive multiple of `y − y_H`. -/
theorem singleLetterZ_sub_one_eq_mul {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    ∃ P : ℝ, 0 < P ∧ singleLetterZ y - 1 = P * (y - hagedornY) := by
  refine ⟨(y + 1) * ((2 + Real.sqrt 3) - y) / (1 - y) ^ 3, ?_, ?_⟩
  · have : 0 < (1 - y) ^ 3 := pow_pos (by linarith) 3
    have : 0 < (2 + Real.sqrt 3) - y := by linarith [one_lt_sqrt_three]
    positivity
  · rw [singleLetterZ_sub_one h1.ne]
    ring

theorem singleLetterZ_lt_one_iff {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    singleLetterZ y < 1 ↔ y < hagedornY := by
  obtain ⟨P, hP, hz⟩ := singleLetterZ_sub_one_eq_mul h0 h1
  constructor
  · intro h
    by_contra hc
    nlinarith
  · intro h
    nlinarith

/-- `y_H` is the only point of `[0, 1)` where `z = 1`. -/
theorem singleLetterZ_eq_one_iff {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    singleLetterZ y = 1 ↔ y = hagedornY := by
  obtain ⟨P, hP, hz⟩ := singleLetterZ_sub_one_eq_mul h0 h1
  constructor
  · intro h
    have : P * (y - hagedornY) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hP.ne'
    linarith
  · intro h
    subst h
    rw [sub_self, mul_zero] at hz
    linarith

theorem singleLetterZ_hagedornY : singleLetterZ hagedornY = 1 :=
  (singleLetterZ_eq_one_iff hagedornY_pos.le hagedornY_lt_one).mpr rfl

/-- `z'(y) = 12y/(1 − y)⁴`. -/
theorem hasDerivAt_singleLetterZ {y : ℝ} (hy : y ≠ 1) :
    HasDerivAt singleLetterZ (12 * y / (1 - y) ^ 4) y := by
  have h1 : (1 - y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (3 - y)) (12 * y - 6 * y ^ 2) y := by
    refine (((hasDerivAt_pow 2 y).const_mul 2).mul ((hasDerivAt_id y).const_sub 3)).congr_deriv ?_
    norm_num
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 - y) ^ 3) (-(3 * (1 - y) ^ 2)) y := by
    refine (((hasDerivAt_id y).const_sub 1).pow 3).congr_deriv ?_
    norm_num
  refine (hnum.div hden (pow_ne_zero 3 h1)).congr_deriv ?_
  field_simp
  ring

/-- `z` is strictly increasing on `[0, 1)`. -/
theorem singleLetterZ_strictMonoOn : StrictMonoOn singleLetterZ (Set.Ico 0 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ico] at ha hb
  unfold singleLetterZ
  have hA : 0 < (1 - a) ^ 3 := pow_pos (by linarith) 3
  have hB : 0 < (1 - b) ^ 3 := pow_pos (by linarith) 3
  rw [div_lt_div_iff₀ hA hB]
  -- the numerator increases and the denominator decreases
  have hnum : 2 * a ^ 2 * (3 - a) ≤ 2 * b ^ 2 * (3 - b) := by
    have key : 2 * b ^ 2 * (3 - b) - 2 * a ^ 2 * (3 - a) =
        (b - a) * (6 * (a + b) - 2 * (a ^ 2 + a * b + b ^ 2)) := by ring
    have h2 : 0 ≤ 6 * (a + b) - 2 * (a ^ 2 + a * b + b ^ 2) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hab.le) h2]
  have hden : (1 - b) ^ 3 < (1 - a) ^ 3 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  have hpos : 0 ≤ 2 * a ^ 2 * (3 - a) := by
    have : 0 ≤ 3 - a := by linarith
    positivity
  have hpos' : 0 < 2 * b ^ 2 * (3 - b) := by
    have : 0 < b := lt_of_le_of_lt ha.1 hab
    have : 0 < 3 - b := by linarith
    positivity
  nlinarith

/-- The free inverse Hagedorn temperature `β₀ = −log x_H`. -/
def hagedornBeta : ℝ := -2 * Real.log hagedornY

/-- `β₀ = 2 log(2 + √3)`: the logarithm of the square of the unit `2 + √3`. -/
theorem hagedornBeta_eq : hagedornBeta = 2 * Real.log (2 + Real.sqrt 3) := by
  unfold hagedornBeta
  have : hagedornY = (2 + Real.sqrt 3)⁻¹ := eq_inv_of_mul_eq_one_left hagedornY_mul_unit
  rw [this, Real.log_inv]
  ring

theorem exp_neg_hagedornBeta_half : Real.exp (-(hagedornBeta / 2)) = hagedornY := by
  unfold hagedornBeta
  rw [show -(-2 * Real.log hagedornY / 2) = Real.log hagedornY by ring,
    Real.exp_log hagedornY_pos]

theorem hagedornBeta_pos : 0 < hagedornBeta := by
  unfold hagedornBeta
  have := Real.log_neg hagedornY_pos hagedornY_lt_one
  linarith

/-- The Polyakov-loop mass `1 − z(e^{-β/2})` crosses zero at `β₀` with slope `x z'(x) = 3/2`. -/
theorem hasDerivAt_polyakovMass :
    HasDerivAt (fun β : ℝ => 1 - singleLetterZ (Real.exp (-(β / 2)))) (3 / 2) hagedornBeta := by
  have hexp : HasDerivAt (fun β : ℝ => Real.exp (-(β / 2)))
      (Real.exp (-(hagedornBeta / 2)) * (-(1 / 2))) hagedornBeta :=
    (((hasDerivAt_id hagedornBeta).div_const 2).neg).exp
  rw [exp_neg_hagedornBeta_half] at hexp
  have hz : HasDerivAt singleLetterZ (12 * hagedornY / (1 - hagedornY) ^ 4)
      (Real.exp (-(hagedornBeta / 2))) := by
    rw [exp_neg_hagedornBeta_half]; exact hasDerivAt_singleLetterZ hagedornY_lt_one.ne
  refine ((hz.comp hagedornBeta hexp).const_sub 1).congr_deriv ?_
  have h4 : (1 - hagedornY) ^ 4 = 4 * hagedornY ^ 2 := by
    rw [show (1 - hagedornY) ^ 4 = ((1 - hagedornY) ^ 2) ^ 2 by ring, one_sub_hagedornY_sq]
    ring
  have hy := hagedornY_pos
  rw [h4]
  field_simp
  ring

/-! ### One loop: the shift of the Hagedorn temperature -/

/-- The one-loop coefficient of `|u₁|²`, in closed form in `y`. -/
def oneLoopD1 (y : ℝ) : ℝ :=
  2 * (1 + y) ^ 2 / (1 - y) ^ 6 *
    (-(1 - 4 * y + y ^ 2) ^ 2 * Real.log (1 - y ^ 2) - y ^ 2 * (1 - 8 * y + 2 * y ^ 2))

/-- At the Hagedorn point the logarithm drops out and `d₁(x_H) = 3/2`. -/
theorem oneLoopD1_hagedornY : oneLoopD1 hagedornY = 3 / 2 := by
  have hq := hagedornY_quadratic
  have hy := hagedornY_pos
  have e1 : 1 - 4 * hagedornY + hagedornY ^ 2 = 0 := by linarith
  have e2 : 1 - 8 * hagedornY + 2 * hagedornY ^ 2 = -1 := by linarith
  have e3 : (1 - hagedornY) ^ 6 = 8 * hagedornY ^ 3 := by
    rw [show (1 - hagedornY) ^ 6 = ((1 - hagedornY) ^ 2) ^ 3 by ring, one_sub_hagedornY_sq]
    ring
  unfold oneLoopD1
  rw [e1, e2, e3, one_add_hagedornY_sq]
  field_simp
  ring

/-- The linearized Polyakov-loop mass `(3/2)(β − β₀) + 2g²β·d₁(x_H)`. -/
def linearPolyakovMass (g2 β : ℝ) : ℝ :=
  3 / 2 * (β - hagedornBeta) + 2 * g2 * β * oneLoopD1 hagedornY

/-- The slope and `d₁` cancel: the linearized mass vanishes exactly at `β₀/(1 + 2g²)`, so the
Hagedorn temperature is raised by the factor `1 + 2g²`. -/
theorem linearPolyakovMass_eq_zero_iff {g2 β : ℝ} (hg : 0 ≤ g2) :
    linearPolyakovMass g2 β = 0 ↔ β = hagedornBeta / (1 + 2 * g2) := by
  unfold linearPolyakovMass
  rw [oneLoopD1_hagedornY]
  have h : (1 + 2 * g2) ≠ 0 := by positivity
  constructor
  · intro hm
    field_simp
    linarith
  · intro hb
    rw [hb]
    field_simp
    ring

/-! ### Winding modes -/

/-- The `n`-fold winding letter function `z_n(y) = z_B(y^{2n}) + (−1)^{n+1} z_F(yⁿ)`. -/
def windingZ (n : ℕ) (y : ℝ) : ℝ := bosonZ (y ^ (2 * n)) + (-1) ^ (n + 1) * fermionZ (y ^ n)

theorem fermionZ_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : 0 ≤ fermionZ y := by
  unfold fermionZ
  have : 0 < 1 - y ^ 2 := by nlinarith
  positivity

theorem windingZ_le_singleLetterZ_pow {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    windingZ n y ≤ singleLetterZ (y ^ n) := by
  have hyn0 : 0 ≤ y ^ n := pow_nonneg h0 n
  have hyn1 : y ^ n < 1 := pow_lt_one₀ h0 h1 (by omega)
  have habs : |y ^ n| < 1 := by rw [abs_of_nonneg hyn0]; exact hyn1
  rw [singleLetterZ_eq_boson_add_fermion habs, windingZ, ← pow_mul, mul_comm n 2]
  have hF := fermionZ_nonneg hyn0 hyn1
  rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> linarith

/-- Below the Hagedorn point every winding mode is massive: `z_n(y) < 1` for all `n ≥ 1`. -/
theorem windingZ_lt_one {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (h0 : 0 ≤ y) (hy : y < hagedornY) :
    windingZ n y < 1 := by
  have h1 : y < 1 := hy.trans hagedornY_lt_one
  have hyn : y ^ n ≤ y := pow_le_of_le_one h0 h1.le (by omega)
  have hyn0 : 0 ≤ y ^ n := pow_nonneg h0 n
  calc windingZ n y ≤ singleLetterZ (y ^ n) := windingZ_le_singleLetterZ_pow hn h0 h1
    _ < 1 := (singleLetterZ_lt_one_iff hyn0 (lt_of_le_of_lt hyn h1)).mpr (lt_of_le_of_lt hyn hy)

/-- The mode `n = 1` is the first to go soft: `z_n(y) < z_1(y)` for `n ≥ 2`, `0 < y < 1`. -/
theorem windingZ_lt_windingZ_one {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    windingZ n y < windingZ 1 y := by
  have hyn : y ^ n < y := pow_lt_self_of_lt_one₀ h0 h1 (by omega)
  have hone : windingZ 1 y = singleLetterZ y := by
    have habs : |y| < 1 := by rw [abs_of_pos h0]; exact h1
    rw [singleLetterZ_eq_boson_add_fermion habs]; simp [windingZ]
  rw [hone]
  calc windingZ n y ≤ singleLetterZ (y ^ n) := windingZ_le_singleLetterZ_pow (by omega) h0.le h1
    _ < singleLetterZ y := singleLetterZ_strictMonoOn
        ⟨pow_nonneg h0.le n, lt_trans hyn h1⟩ ⟨h0.le, h1⟩ hyn

end GaloisForLFunctions.HagedornBootstrap
