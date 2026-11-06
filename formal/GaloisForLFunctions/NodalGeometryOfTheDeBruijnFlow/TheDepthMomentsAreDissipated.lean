import GaloisForLFunctions.RHTower.Heat.HeatLocalizedEnergyDissipation
import GaloisForLFunctions.ArithmeticElectrostatics.SimpleHeatZeroBranches

/-!
# The depth moments are dissipated

For a horizontal cutoff `w`, let `E₁(t) = Σ_k w(Re z_k − X) (Im z_k)²` and `E₂(t) = Σ_k w(Re z_k − X) (Im z_k)⁴`,
sums over the zeros of `H_t` with multiplicity. Zeros attract vertically, so the depth moments decrease. A
conjugate pair loses `4` per unit time in `E₁` and `8y²` in `E₂`. The cutoff flux is paid by the same moment,
at the price `O(log X)`, with no inverse gap:

`E₂(b) − E₂(a) + 4 ∫_a^b E₁ ≤ K log X ∫_a^b E₂^{outer}`   (`exists_uniform_heatLocalizedQuarticEnergy_evolution`).

The proof of the pair inequality (`quarticPairForce_le`) has one term more than for `E₁`: after the trapezoid
rule the singular part leaves `−½(v + v')·d·(y + y')·(y − y')³`, which Young's inequality pays with the good
term and `v² ≤ 4Mw`. The inequality passes through collisions by continuity of the observables.
-/

open Complex Filter Topology Set Metric MeasureTheory Finset
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The quartic pair force -/


/-- A nonnegative function with `M`-Lipschitz derivative obeys `v² ≤ 4Mw`. -/
theorem sq_deriv_le_of_nonneg {w v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, HasDerivAt w (v x) x) (hv : ∀ x y, |v x - v y| ≤ M * |x - y|)
    (hwn : ∀ x, 0 ≤ w x) (x : ℝ) : v x ^ 2 ≤ 4 * M * w x := by
  -- the one-sided bound `v(x) h ≤ w(x) + M h²`
  have hbound (h : ℝ) : v x * h ≤ w x + M * h ^ 2 := by
    have htrap := abs_trapezoid_remainder_le_of_lipschitz_deriv hw hv x (x - h)
    have hvv := hv x (x - h)
    rw [show x - (x - h) = h by ring] at htrap hvv
    have h1 := (abs_le.mp htrap).2
    have h2 := hwn (x - h)
    have h3 : (v x - v (x - h)) * h ≤ M * h ^ 2 := by
      calc (v x - v (x - h)) * h ≤ |(v x - v (x - h)) * h| := le_abs_self _
        _ = |v x - v (x - h)| * |h| := abs_mul _ _
        _ ≤ (M * |h|) * |h| := mul_le_mul_of_nonneg_right hvv (abs_nonneg h)
        _ = M * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    nlinarith only [h1, h2, h3]
  rcases hM.eq_or_lt with rfl | hpos
  · by_contra hne
    have hv0 : v x ≠ 0 := by
      intro h0
      rw [h0] at hne
      apply hne
      simp
    have := hbound ((w x + 1) / v x)
    rw [mul_div_cancel₀ _ hv0] at this
    linarith only [this]
  · have := hbound (v x / (2 * M))
    have hmul : v x * (v x / (2 * M)) = v x ^ 2 / (2 * M) := by ring
    have hsq : M * (v x / (2 * M)) ^ 2 = v x ^ 2 / (4 * M) := by
      field_simp
      ring
    rw [hmul, hsq] at this
    have h4 : v x ^ 2 / (2 * M) - v x ^ 2 / (4 * M) = v x ^ 2 / (4 * M) := by
      field_simp
      ring
    have h5 : v x ^ 2 / (4 * M) ≤ w x := by linarith only [this, h4]
    rw [div_le_iff₀ (by positivity)] at h5
    linarith only [h5]

/-- If `P² ≤ 4UV` with `U, V ≥ 0` then `P ≤ U + V`. -/
theorem le_add_of_sq_le_four_mul {P U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (h : P ^ 2 ≤ 4 * (U * V)) :
    P ≤ U + V := by
  have h2 : P ^ 2 ≤ (U + V) ^ 2 := by nlinarith only [h, sq_nonneg (U - V)]
  exact (le_abs_self P).trans (abs_le_of_sq_le_sq h2 (add_nonneg hU hV))

/-- The pair contribution to the derivative of the localized fourth moment of the heights. -/
def quarticPairForce (w v : ℝ → ℝ) (x x' y y' : ℝ) : ℝ :=
  2 * ((v x * y ^ 4 - v x' * y' ^ 4) * (x - x') -
    4 * (w x * y ^ 3 - w x' * y' ^ 3) * (y - y')) / ((x - x') ^ 2 + (y - y') ^ 2)

/-- **The quartic pair force.** The cutoff error is paid by fourth powers of the heights, uniformly as
the zero gap shrinks; the singular force cancels through the trapezoid rule and Young's inequality. -/
theorem quarticPairForce_le {w v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, HasDerivAt w (v x) x) (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (hwn : ∀ x, 0 ≤ w x) (x x' y y' : ℝ) (hsep : 0 < (x - x') ^ 2 + (y - y') ^ 2) :
    quarticPairForce w v x x' y y' ≤ 16 * M * (y ^ 4 + y' ^ 4) := by
  set d := x - x' with hd
  set e := y - y' with he
  set s := y + y' with hs
  set Q := y ^ 2 + y * y' + y' ^ 2 with hQ
  set E := y ^ 4 + y' ^ 4 with hE
  set W := w x + w x' with hW
  set a := v x + v x' with ha
  set r := a * d / 2 - (w x - w x') with hr
  have hEn : 0 ≤ E := by positivity
  have hWn : 0 ≤ W := add_nonneg (hwn _) (hwn _)
  have hQn : 0 ≤ Q := by nlinarith only [sq_nonneg (y + y'), sq_nonneg y, sq_nonneg y']
  have hrb : |r| ≤ M * d ^ 2 / 2 := abs_trapezoid_remainder_le_of_lipschitz_deriv hw hv x x'
  -- the identity
  have hid : (v x * y ^ 4 - v x' * y' ^ 4) * d - 4 * (w x * y ^ 3 - w x' * y' ^ 3) * e =
      -(a * d * s * e ^ 3 / 2) + (v x - v x') * d * E / 2 - 2 * W * (Q * e ^ 2) +
        2 * r * ((y ^ 3 + y' ^ 3) * e) := by
    simp only [hd, he, hs, hQ, hE, hW, ha, hr]
    ring
  -- the variation of the derivative
  have hvar : (v x - v x') * d * E / 2 ≤ M * d ^ 2 * E / 2 := by
    have h1 : (v x - v x') * d ≤ M * d ^ 2 := by
      calc (v x - v x') * d ≤ |(v x - v x') * d| := le_abs_self _
        _ = |v x - v x'| * |d| := abs_mul _ _
        _ ≤ (M * |d|) * |d| := mul_le_mul_of_nonneg_right (hv x x') (abs_nonneg d)
        _ = M * d ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hEn) (by norm_num)
  -- the trapezoid remainder
  have hcube : |(y ^ 3 + y' ^ 3) * e| ≤ 2 * E := by
    have h1 : |y ^ 3 + y' ^ 3| ≤ |y| ^ 3 + |y'| ^ 3 := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_pow, abs_pow]
    have h2 : |e| ≤ |y| + |y'| := abs_sub _ _
    rw [abs_mul]
    have hy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    have hy4' : |y'| ^ 4 = y' ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc |y ^ 3 + y' ^ 3| * |e| ≤ (|y| ^ 3 + |y'| ^ 3) * (|y| + |y'|) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ 2 * (|y| ^ 4 + |y'| ^ 4) := by
          nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg y) (abs_nonneg y'))
            (sq_nonneg (|y| - |y'|)), sq_nonneg (|y| ^ 2 - |y'| ^ 2),
            mul_nonneg (abs_nonneg y) (abs_nonneg y'), sq_nonneg (|y| - |y'|),
            mul_nonneg (mul_nonneg (abs_nonneg y) (abs_nonneg y')) (mul_nonneg (abs_nonneg y) (abs_nonneg y'))]
      _ = 2 * E := by rw [hy4, hy4']
  have htrap : 2 * r * ((y ^ 3 + y' ^ 3) * e) ≤ 2 * M * d ^ 2 * E := by
    calc 2 * r * ((y ^ 3 + y' ^ 3) * e) ≤ |2 * r * ((y ^ 3 + y' ^ 3) * e)| := le_abs_self _
      _ = 2 * (|r| * |(y ^ 3 + y' ^ 3) * e|) := by
          rw [abs_mul, abs_mul]
          simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
      _ ≤ 2 * ((M * d ^ 2 / 2) * (2 * E)) := by
          gcongr
      _ = 2 * M * d ^ 2 * E := by ring
  -- the leftover first-order term, by Young
  have ha2 : a ^ 2 ≤ 8 * M * W := by
    have h1 := sq_deriv_le_of_nonneg hM hw hv hwn x
    have h2 := sq_deriv_le_of_nonneg hM hw hv hwn x'
    simp only [ha, hW]
    nlinarith only [h1, h2, sq_nonneg (v x - v x')]
  have hs2 : 3 * s ^ 2 ≤ 4 * Q := by
    simp only [hs, hQ]
    nlinarith only [sq_nonneg (y - y')]
  have he4 : e ^ 4 ≤ 8 * E := by
    simp only [he, hE]
    nlinarith only [sq_nonneg (y ^ 2 - y' ^ 2), sq_nonneg (y + y'), sq_nonneg (y - y'),
      mul_nonneg (sq_nonneg (y + y')) (sq_nonneg (y - y')),
      mul_nonneg (sq_nonneg y) (sq_nonneg y'), sq_nonneg (y ^ 2 + y' ^ 2 - 2 * y * y'),
      sq_nonneg (y ^ 2 + y' ^ 2 + 2 * y * y')]
  have hyoung : -(a * d * s * e ^ 3 / 2) ≤ W * (Q * e ^ 2) + 16 / 3 * M * d ^ 2 * E := by
    apply le_add_of_sq_le_four_mul (by positivity) (by positivity)
    have h1 : (-(a * d * s * e ^ 3 / 2)) ^ 2 = a ^ 2 * (s ^ 2 * (e ^ 4 * (d ^ 2 * e ^ 2))) / 4 := by
      ring
    rw [h1]
    have h2 : a ^ 2 * (s ^ 2 * (e ^ 4 * (d ^ 2 * e ^ 2))) ≤
        (8 * M * W) * (4 / 3 * Q * ((8 * E) * (d ^ 2 * e ^ 2))) := by
      have hb : s ^ 2 ≤ 4 / 3 * Q := by linarith only [hs2]
      gcongr
    have h3 : (8 * M * W) * (4 / 3 * Q * ((8 * E) * (d ^ 2 * e ^ 2))) / 4 =
        4 * (W * (Q * e ^ 2) * (16 / 3 * M * d ^ 2 * E)) := by ring
    calc _ ≤ (8 * M * W) * (4 / 3 * Q * ((8 * E) * (d ^ 2 * e ^ 2))) / 4 :=
          div_le_div_of_nonneg_right h2 (by norm_num)
      _ = _ := h3
  -- assembling
  have hnum : (v x * y ^ 4 - v x' * y' ^ 4) * d - 4 * (w x * y ^ 3 - w x' * y' ^ 3) * e ≤
      8 * M * E * (d ^ 2 + e ^ 2) := by
    rw [hid]
    have hgood : 0 ≤ W * (Q * e ^ 2) := by positivity
    have hpaid : M * d ^ 2 * E ≤ M * E * (d ^ 2 + e ^ 2) := by
      have := mul_nonneg (mul_nonneg hM hEn) (sq_nonneg e)
      nlinarith only [this]
    have hnn : 0 ≤ M * d ^ 2 * E := by positivity
    nlinarith only [hyoung, hvar, htrap, hgood, hpaid, hnn]
  unfold quarticPairForce
  rw [div_le_iff₀ hsep]
  nlinarith only [hnum]

/-- A conjugate pair dissipates `8w y²`. -/
theorem quarticPairForce_conjugate (w v : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    quarticPairForce w v x x y (-y) = -8 * w x * y ^ 2 := by
  have hden : (x - x) ^ 2 + (y - -y) ^ 2 ≠ 0 := by
    have h := sq_pos_of_ne_zero hy
    nlinarith only [h]
  unfold quarticPairForce
  field_simp [hden]
  ring



/-! ## The finite packet -/

private theorem quartic_pair_separation {a b : ℂ} (hab : a ≠ b) :
    0 < (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 := by
  have h := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
  simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, sq] using h

private theorem quartic_pair_force_with_conjugate {w v : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|) (hwn : ∀ x, 0 ≤ w x) (a b : ℂ) :
    quarticPairForce w v a.re b.re a.im b.im ≤
      -(if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 8 * w a.re * a.im ^ 2 else 0) +
        16 * M * (a.im ^ 4 + b.im ^ 4) := by
  by_cases hc : a.im ≠ 0 ∧ b = starRingEnd ℂ a
  · rcases hc with ⟨ha, rfl⟩
    simp only [ha, ne_eq, not_false_eq_true, and_self, if_true, Complex.conj_re, Complex.conj_im]
    rw [quarticPairForce_conjugate w v a.re ha]
    have hnon : 0 ≤ 16 * M * (a.im ^ 4 + (-a.im) ^ 4) := by positivity
    linarith only [hnon]
  rw [if_neg hc, neg_zero, zero_add]
  by_cases hab : a = b
  · subst b
    simp only [quarticPairForce, sub_self, mul_zero, zero_div]
    positivity
  exact quarticPairForce_le hM hw hv hwn _ _ _ _ (quartic_pair_separation hab)

/-- Fourth powers of the heights of a packet. -/
def packetQuarticEnergy (S : Finset ℂ) : ℝ := ∑ a ∈ S, a.im ^ 4

/-- Squared heights of a packet, weighted by the cutoff. -/
def packetSquareWeight (S : Finset ℂ) (w : ℝ → ℝ) : ℝ := ∑ a ∈ S, w a.re * a.im ^ 2

/-- Sum of the pair contributions, counting each unordered pair once. -/
def packetQuarticPairDrift (S : Finset ℂ) (w v : ℝ → ℝ) : ℝ :=
  (∑ a ∈ S, ∑ b ∈ S, quarticPairForce w v a.re b.re a.im b.im) / 2

/-- Conjugate pairs pay the weighted squared heights; cutoff error costs only fourth powers. -/
theorem packetQuarticPairDrift_le {S : Finset ℂ} {w v : ℝ → ℝ} {M : ℝ}
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S) (hM : 0 ≤ M) (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|) (hwn : ∀ x, 0 ≤ w x) :
    packetQuarticPairDrift S w v ≤ -4 * packetSquareWeight S w +
      16 * M * S.card * packetQuarticEnergy S := by
  classical
  have hsum := sum_le_sum fun a (_ : a ∈ S) =>
    sum_le_sum fun b (_ : b ∈ S) => quartic_pair_force_with_conjugate hM hw hv hwn a b
  have hpen : (∑ a ∈ S, ∑ b ∈ S, if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 8 * w a.re * a.im ^ 2 else 0) =
      8 * packetSquareWeight S w := by
    rw [packetSquareWeight, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    by_cases hy : a.im = 0
    · simp [hy]
    · have hcond : ∀ b, (a.im ≠ 0 ∧ b = starRingEnd ℂ a) ↔ b = starRingEnd ℂ a := fun b =>
        ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      simp only [hcond, sum_ite_eq', hconj a ha, if_true]
      ring
  have herr : (∑ a ∈ S, ∑ b ∈ S, 16 * M * (a.im ^ 4 + b.im ^ 4)) =
      32 * M * S.card * packetQuarticEnergy S := by
    calc
      _ = 16 * M * (∑ a ∈ S, ∑ b ∈ S, (a.im ^ 4 + b.im ^ 4)) := by
        simp only [mul_sum]
      _ = 16 * M * ((S.card : ℝ) * packetQuarticEnergy S + (S.card : ℝ) * packetQuarticEnergy S) := by
        congr 1
        simp only [packetQuarticEnergy, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      _ = _ := by ring
  simp only [sum_add_distrib, sum_neg_distrib] at hsum
  rw [hpen, herr] at hsum
  unfold packetQuarticPairDrift
  linarith only [hsum]

/-- Exterior-field contribution to the derivative of the fourth moment. -/
def packetQuarticExteriorDrift (S : Finset ℂ) (w v : ℝ → ℝ) (Q : ℂ → ℂ) : ℝ :=
  ∑ a ∈ S, (v a.re * a.im ^ 4 * (2 * (Q a).re) + 4 * w a.re * a.im ^ 3 * (2 * (Q a).im))

/-- A real-symmetric exterior field charges only fourth powers. -/
theorem packetQuarticExteriorDrift_le {S : Finset ℂ} {w v : ℝ → ℝ} {Q : ℂ → ℂ} {K V W : ℝ}
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hw : ∀ a ∈ S, 0 ≤ w a.re ∧ w a.re ≤ W)
    (hv : ∀ a ∈ S, |v a.re| ≤ V) (hQr : ∀ a ∈ S, |(Q a).re| ≤ K)
    (hQi : ∀ a ∈ S, |(Q a).im| ≤ K * |a.im|) :
    packetQuarticExteriorDrift S w v Q ≤ (2 * V + 8 * W) * K * packetQuarticEnergy S := by
  unfold packetQuarticExteriorDrift packetQuarticEnergy
  rw [mul_sum]
  refine sum_le_sum fun a ha => ?_
  have hvr : v a.re * (Q a).re ≤ V * K := by
    calc
      _ ≤ |v a.re * (Q a).re| := le_abs_self _
      _ = |v a.re| * |(Q a).re| := abs_mul _ _
      _ ≤ V * K := mul_le_mul (hv a ha) (hQr a ha) (abs_nonneg _) hV
  have hyi : a.im ^ 3 * (Q a).im ≤ K * a.im ^ 4 := by
    calc
      _ ≤ |a.im ^ 3 * (Q a).im| := le_abs_self _
      _ = |a.im| ^ 3 * |(Q a).im| := by rw [abs_mul, abs_pow]
      _ ≤ |a.im| ^ 3 * (K * |a.im|) := mul_le_mul_of_nonneg_left (hQi a ha) (by positivity)
      _ = K * |a.im| ^ 4 := by ring
      _ = K * a.im ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hy4 : 0 ≤ a.im ^ 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hvr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hy4)
  have h2 := mul_le_mul_of_nonneg_left hyi (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (hw a ha).1)
  have h3 := mul_le_mul_of_nonneg_right (hw a ha).2 (mul_nonneg hK hy4)
  nlinarith only [h1, h2, h3]

private theorem quartic_pair_force_eq_field_pair (w v : ℝ → ℝ) (a b : ℂ) :
    (v a.re * a.im ^ 4 * (2 * (a - b)⁻¹.re) + 4 * w a.re * a.im ^ 3 * (2 * (a - b)⁻¹.im)) +
    (v b.re * b.im ^ 4 * (2 * (b - a)⁻¹.re) + 4 * w b.re * b.im ^ 3 * (2 * (b - a)⁻¹.im)) =
      quarticPairForce w v a.re b.re a.im b.im := by
  have hn : Complex.normSq (b - a) = Complex.normSq (a - b) := by
    rw [← Complex.normSq_neg, neg_sub]
  simp only [Complex.inv_re, Complex.inv_im, Complex.sub_re, Complex.sub_im, hn, quarticPairForce]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The pair drift is exactly the work of the finite reciprocal field. -/
theorem packetQuarticPairDrift_eq_field (S : Finset ℂ) (w v : ℝ → ℝ) :
    packetQuarticPairDrift S w v =
      ∑ a ∈ S, (v a.re * a.im ^ 4 * (2 * (∑ b ∈ S, (a - b)⁻¹).re) +
        4 * w a.re * a.im ^ 3 * (2 * (∑ b ∈ S, (a - b)⁻¹).im)) := by
  let F := fun a b : ℂ => v a.re * a.im ^ 4 * (2 * (a - b)⁻¹.re) +
    4 * w a.re * a.im ^ 3 * (2 * (a - b)⁻¹.im)
  have he : (∑ a ∈ S, ∑ b ∈ S, (F a b + F b a)) = 2 * (∑ a ∈ S, ∑ b ∈ S, F a b) := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun a b => F b a)]
    ring
  have hp : (∑ a ∈ S, ∑ b ∈ S, quarticPairForce w v a.re b.re a.im b.im) =
      2 * (∑ a ∈ S, ∑ b ∈ S, F a b) := by
    rw [← he]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
      (quartic_pair_force_eq_field_pair w v a b).symm
  unfold packetQuarticPairDrift
  rw [hp, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  refine sum_congr rfl fun a _ => ?_
  simp only [F, Complex.re_sum, Complex.im_sum, mul_sum, sum_add_distrib]

/-! ## The actual zeros -/

/-- The localized fourth moment of the heights of the zeros of `H_t`, with multiplicity. -/
def heatLocalizedQuarticEnergy (X : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  heatLocalizedZeroObservable X w (fun y => y ^ 4) t

private theorem eventually_heat_nonzero_on_compact' {t : ℝ} (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ z ∈ K, riemannHeat t z ≠ 0) :
    ∀ᶠ s in 𝓝 t, ∀ z ∈ K, riemannHeat (max s 0) z ≠ 0 := by
  have hc : ContinuousOn (fun z : ℂ => ‖riemannHeat t z‖) K :=
    (differentiable_riemannHeat ht).continuous.norm.continuousOn
  obtain ⟨δ, hδ, hmin⟩ := hK.exists_forall_le' hc (fun z hz => norm_pos_iff.mpr (hnz z hz))
  have hconv := tendstoLocallyUniformly_riemannHeat_clamped_nhds t
  rw [max_eq_left ht] at hconv
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu δ hδ] with s hs z hz hzero
  have hlt : ‖riemannHeat t z‖ < δ := by
    simpa only [hzero, dist_zero_right] using hs z hz
  exact (not_lt_of_ge (hmin z hz)) hlt

/-- At a simple time the localized fourth moment is a finite sum of simple zero branches on a short
right interval. -/
theorem heatLocalizedQuarticEnergy_hasDerivWithinAt_of_simple {t X : ℝ} (ht : 0 < t) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x) (hsupp : ∀ x, 1 ≤ |x| → w x = 0) {S : Finset ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0) :
    HasDerivWithinAt (fun h => heatLocalizedQuarticEnergy X w (t + h))
      (∑ a ∈ S, (v (a.re - X) * a.im ^ 4 *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
        4 * w (a.re - X) * a.im ^ 3 *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im))
      (Ici 0) 0 := by
  classical
  let V : ℂ → ℂ := fun a => deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a
  obtain ⟨d, hd, hsep⟩ := exists_pos_sep S
  choose r₀ hr₀ hbranch using fun a : S =>
    GaloisForLFunctions.ArithmeticElectrostatics.exists_simple_heat_zero_branch ht
      ((hpacket a).mp a.property).1 (hsimple a a.property)
  let r : S → ℝ := fun a => min (r₀ a) (d / 3)
  have hr (a : S) : 0 < r a := lt_min (hr₀ a) (by positivity)
  have hr₀le (a : S) : r a ≤ r₀ a := min_le_left _ _
  have hrd (a : S) : r a ≤ d / 3 := min_le_right _ _
  choose δ hδ ζ hζ0 hζd hζ using fun a : S => hbranch a (r a) (hr a) (hr₀le a)
  let K : Set ℂ := closedBall (X : ℂ) 2 \ ⋃ a : S, ball (a : ℂ) (r a)
  have hK : IsCompact K := (isCompact_closedBall (X : ℂ) 2).diff
    (isOpen_iUnion fun _ => isOpen_ball)
  have hKfree : ∀ z ∈ K, riemannHeat t z ≠ 0 := by
    intro z hz hzero
    have hnorm : ‖z - (X : ℂ)‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hz.1
    have hre : |z.re - X| ≤ 2 := by
      have h := Complex.abs_re_le_norm (z - (X : ℂ))
      simp only [sub_re, ofReal_re] at h
      exact h.trans hnorm
    have hzS := (hpacket z).mpr ⟨hzero, hre⟩
    exact hz.2 (mem_iUnion.mpr ⟨⟨z, hzS⟩, mem_ball_self (hr ⟨z, hzS⟩)⟩)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_heat_nonzero_on_compact' ht.le hK hKfree)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_finset_of_pos S.attach (fun a _ => hδ a)
  let η := min δ₀ (ε / 2)
  have hη : 0 < η := lt_min hδ₀ (by positivity)
  have hstep (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) (a : S) :
      ζ a h ∈ ball (a : ℂ) (r a) ∧
        zeroMult (riemannHeat (t + h)) (ζ a h) = 1 ∧
        ∀ z ∈ ball (a : ℂ) (r a), riemannHeat (t + h) z = 0 ↔ z = ζ a h := by
    exact hζ a h ⟨hh.1, hh.2.trans ((min_le_left _ _).trans
      (hδ₀le a (Finset.mem_attach S a)))⟩
  have hfree (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) :
      ∀ z ∈ K, riemannHeat (t + h) z ≠ 0 := by
    have he : dist (t + h) t < ε := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hh.1]
      have hhε := hh.2.trans (min_le_right δ₀ (ε / 2))
      linarith only [hhε, hε]
    simpa only [max_eq_left (add_nonneg ht.le hh.1)] using hnear he
  have hinj (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) : Function.Injective (fun a : S => ζ a h) := by
    intro a b heq
    change ζ a h = ζ b h at heq
    by_contra hab
    have hab' : (a : ℂ) ≠ (b : ℂ) := fun he => hab (Subtype.ext he)
    have hgap := hsep a a.property b b.property hab'
    have ha := mem_ball.mp (hstep h hh a).1
    have hb := mem_ball.mp (hstep h hh b).1
    rw [← heq] at hb
    have htri := dist_triangle (a : ℂ) (ζ a h) (b : ℂ)
    rw [dist_comm (a : ℂ) (ζ a h)] at htri
    linarith only [hgap, ha, hb, htri, hrd a, hrd b, hd]
  have hrepr (h : ℝ) (hh : h ∈ Icc (0 : ℝ) η) :
      heatLocalizedQuarticEnergy X w (t + h) =
        ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im ^ 4 := by
    let Z := S.attach.image (fun a => ζ a h)
    have hsum : heatLocalizedQuarticEnergy X w (t + h) =
        ∑ z ∈ Z, (zeroMult (riemannHeat (t + h)) z : ℝ) * (w (z.re - X) * z.im ^ 4) := by
      unfold heatLocalizedQuarticEnergy heatLocalizedZeroObservable heatWeightedZeroSum
      apply tsum_eq_sum
      intro z hz
      change (zeroMult (riemannHeat (t + h)) z : ℝ) * (w (z.re - X) * z.im ^ 4) = 0
      by_cases hzero : riemannHeat (t + h) z = 0
      · by_cases hweight : w (z.re - X) * z.im ^ 4 = 0
        · rw [hweight, mul_zero]
        exfalso
        have hre : |z.re - X| < 1 := lt_of_not_ge fun hr =>
          hweight (by rw [hsupp _ hr, zero_mul])
        have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg
          (add_nonneg ht.le hh.1) hzero
        have hzball : z ∈ closedBall (X : ℂ) 2 := by
          rw [mem_closedBall, dist_eq_norm]
          have hn := Complex.norm_le_abs_re_add_abs_im (z - (X : ℂ))
          simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
          linarith only [hn, hre, him]
        have hu : z ∈ ⋃ a : S, ball (a : ℂ) (r a) := by
          by_contra hnot
          exact hfree h hh z ⟨hzball, hnot⟩ hzero
        obtain ⟨a, hza⟩ := mem_iUnion.mp hu
        have hza' := ((hstep h hh a).2.2 z hza).mp hzero
        exact hz (Finset.mem_image.mpr ⟨a, Finset.mem_attach S a, hza'.symm⟩)
      · rw [zeroMult_riemannHeat_eq_zero (add_nonneg ht.le hh.1) hzero, Nat.cast_zero, zero_mul]
    rw [hsum, Finset.sum_image
      (f := fun z : ℂ => (zeroMult (riemannHeat (t + h)) z : ℝ) * (w (z.re - X) * z.im ^ 4))
      (fun a _ b _ heq => hinj h hh heq)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [(hstep h hh a).2.1, Nat.cast_one, one_mul]
  have hdbranch (a : S) :
      HasDerivWithinAt (fun h => w ((ζ a h).re - X) * (ζ a h).im ^ 4)
        (v ((a : ℂ).re - X) * (a : ℂ).im ^ 4 * (V a).re +
          4 * w ((a : ℂ).re - X) * (a : ℂ).im ^ 3 * (V a).im) (Ici 0) 0 := by
    have hre : HasDerivWithinAt (fun h => (ζ a h).re) (V a).re (Ici 0) 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    have him : HasDerivWithinAt (fun h => (ζ a h).im) (V a).im (Ici 0) 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt 0 (hζd a)
    have hcomp := (hw ((ζ a 0).re - X)).comp_hasDerivWithinAt 0 (hre.sub_const X)
    convert hcomp.mul (him.pow 4) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply, Function.comp_apply, hζ0]; norm_num; ring)
  have hds := HasDerivWithinAt.sum (u := S.attach) (fun a _ => hdbranch a)
  have hsumfun : (∑ a ∈ S.attach, fun h : ℝ => w ((ζ a h).re - X) * (ζ a h).im ^ 4) =
      (fun h => ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im ^ 4) := by
    funext h
    rw [Finset.sum_apply]
  rw [hsumfun] at hds
  have heq : (fun h => heatLocalizedQuarticEnergy X w (t + h)) =ᶠ[𝓝[Ici 0] 0]
      (fun h => ∑ a ∈ S.attach, w ((ζ a h).re - X) * (ζ a h).im ^ 4) := by
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, h < η := Iio_mem_nhds hη
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hh0
    change 0 ≤ h at hh0
    exact hrepr h ⟨hh0, hh.le⟩
  have hder := hds.congr_of_eventuallyEq heq (hrepr 0 ⟨le_rfl, hη.le⟩)
  rw [Finset.sum_attach S (fun a : ℂ =>
    v (a.re - X) * a.im ^ 4 * (V a).re + 4 * w (a.re - X) * a.im ^ 3 * (V a).im)] at hder
  exact hder

/-- The outer cutoff majorizes the fourth powers of the heights of the force packet. -/
theorem packetQuarticEnergy_le_outer {t X : ℝ} (ht : 0 ≤ t) {S : Finset ℂ}
    (hpacket : ∀ a ∈ S, riemannHeat t a = 0 ∧ |a.re - X| ≤ 2) :
    packetQuarticEnergy S ≤ heatLocalizedQuarticEnergy X heatOuterCutoff t := by
  have hsum := summable_heatLocalizedZeroObservable hasCompactSupport_heatOuterCutoff
    (fun y => y ^ 4) X ht
  calc
    _ ≤ ∑ a ∈ S, (zeroMult (riemannHeat t) a : ℝ) * (heatOuterCutoff (a.re - X) * a.im ^ 4) := by
      refine Finset.sum_le_sum fun a ha => ?_
      rw [heatOuterCutoff_eq_one (hpacket a ha).2, one_mul]
      have hm : (1 : ℝ) ≤ zeroMult (riemannHeat t) a := by
        exact_mod_cast one_le_zeroMult_riemannHeat ht (hpacket a ha).1
      have hy4 : 0 ≤ a.im ^ 4 := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm hy4
    _ ≤ _ := Summable.sum_le_tsum S
      (fun a _ => mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (heatOuterCutoff_nonneg _) (by positivity))) hsum

/-- Nonnegative cutoffs have zero derivative wherever the cutoff vanishes. -/
private theorem cutoff_deriv_eq_zero {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x) (hwn : ∀ x, 0 ≤ w x) {x : ℝ} (hx : w x = 0) : v x = 0 := by
  have hmin : IsLocalMin w x := Filter.Eventually.of_forall fun y => by
    rw [hx]
    exact hwn y
  exact hmin.hasDerivAt_eq_zero (hw x)

/-- At a simple time the actual fourth moment obeys the uniform flux estimate. -/
private theorem heatLocalizedQuarticEnergy_simple_drift_le
    {t X M V W K : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hV : 0 ≤ V) (hW : 0 ≤ W) (hK : 0 ≤ K) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x) (hwn : ∀ x, 0 ≤ w x) (hwW : ∀ x, w x ≤ W)
    (hvV : ∀ x, |v x| ≤ V) (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0) {S : Finset ℂ} {Q : ℂ → ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hcount : ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ K)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖Q z‖ ≤ K ∧ |(Q z).im| ≤ K * |z.im| ∧
        (riemannHeat t z ≠ 0 → logDeriv (riemannHeat t) z =
          (∑ a ∈ S, (zeroMult (riemannHeat t) a : ℂ) / (z - a)) + Q z)) :
    ∃ D : ℝ, HasDerivWithinAt (heatLocalizedQuarticEnergy X w) D (Ici t) t ∧
      D ≤ -4 * heatLocalizedVerticalEnergy X w t +
        (16 * M + 2 * V + 8 * W) * K * heatLocalizedQuarticEnergy X heatOuterCutoff t := by
  classical
  let ws := fun x => w (x - X)
  let vs := fun x => v (x - X)
  let Qs := fun z : ℂ => if |z.re - X| < 1 then Q z else 0
  have hws (x : ℝ) : HasDerivAt ws (vs x) x := by
    simpa only [ws, vs, Function.comp_def, mul_one] using
      (hw (x - X)).comp (h := fun r : ℝ => r - X) x ((hasDerivAt_id x).sub_const X)
  have hvs (x x' : ℝ) : |vs x - vs x'| ≤ M * |x - x'| := by
    simpa only [vs, sub_sub_sub_cancel_right] using hv (x - X) (x' - X)
  have hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S := by
    intro a ha
    obtain ⟨hz, hr⟩ := (hpacket a).mp ha
    apply (hpacket (starRingEnd ℂ a)).mpr
    refine ⟨?_, by simpa only [Complex.conj_re] using hr⟩
    rw [riemannHeat_conj ht.le, hz, map_zero]
  have hQr (a : ℂ) (ha : a ∈ S) : |(Qs a).re| ≤ K := by
    by_cases hr : |a.re - X| < 1
    · simpa only [Qs, if_pos hr] using (Complex.abs_re_le_norm (Q a)).trans
        (hQ a hr.le (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht.le
          ((hpacket a).mp ha).1)).2.1
    · simpa only [Qs, if_neg hr, Complex.zero_re, abs_zero] using hK
  have hQi (a : ℂ) (ha : a ∈ S) : |(Qs a).im| ≤ K * |a.im| := by
    by_cases hr : |a.re - X| < 1
    · simpa only [Qs, if_pos hr] using
        (hQ a hr.le (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht.le
          ((hpacket a).mp ha).1)).2.2.1
    · simpa only [Qs, if_neg hr, Complex.zero_im, abs_zero] using
        mul_nonneg hK (abs_nonneg a.im)
  have hm (a : ℂ) (ha : a ∈ S) : zeroMult (riemannHeat t) a = 1 :=
    zeroMult_riemannHeat_eq_one ht.le ((hpacket a).mp ha).1 (hsimple a ha)
  have hcard : (S.card : ℝ) ≤ K := by
    have he : (∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) = S.card := by
      calc
        _ = ∑ _ ∈ S, 1 := Finset.sum_congr rfl hm
        _ = _ := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rwa [he] at hcount
  -- the derivative at time `t`, in the time variable
  have hder := heatLocalizedQuarticEnergy_hasDerivWithinAt_of_simple ht hw hsupp hpacket hsimple
  have hg : HasDerivWithinAt (fun r : ℝ => r - t) 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  set D : ℝ := ∑ a ∈ S, (v (a.re - X) * a.im ^ 4 *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
    4 * w (a.re - X) * a.im ^ 3 *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) with hDdef
  have hder' : HasDerivWithinAt (fun h => heatLocalizedQuarticEnergy X w (t + h)) D (Ici 0) (t - t) := by
    simpa only [sub_self] using hder
  have hc := hder'.comp (h := fun r : ℝ => r - t) t hg (fun r hr => by
    change t ≤ r at hr
    change 0 ≤ r - t
    exact sub_nonneg.mpr hr)
  have hfun : (fun r => heatLocalizedQuarticEnergy X w (t + (r - t))) =
      heatLocalizedQuarticEnergy X w := by
    funext r
    congr 1
    ring
  change HasDerivWithinAt (fun r => heatLocalizedQuarticEnergy X w (t + (r - t))) (D * 1) (Ici t) t at hc
  rw [hfun, mul_one] at hc
  refine ⟨D, hc, ?_⟩
  -- the derivative as packet work
  have hsumfield : D = packetQuarticPairDrift S ws vs + packetQuarticExteriorDrift S ws vs Qs := by
    rw [hDdef, packetQuarticPairDrift_eq_field, packetQuarticExteriorDrift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases hr : |a.re - X| < 1
    · have hvel := simple_heat_zero_velocity_eq_exterior ht hpacket
        (fun z hr hi => ⟨(hQ z hr hi).1, (hQ z hr hi).2.2.2⟩) ((hpacket a).mp ha).1 (hsimple a ha) hr
      have hsum : (∑ b ∈ S.erase a, (zeroMult (riemannHeat t) b : ℂ) / (a - b)) =
          ∑ b ∈ S, (a - b)⁻¹ := by
        calc
          _ = ∑ b ∈ S.erase a, (a - b)⁻¹ := by
            refine Finset.sum_congr rfl fun b hb => ?_
            have hbS := (Finset.mem_erase.mp hb).2
            rw [hm b hbS, Nat.cast_one, one_div]
          _ = _ := by
            simpa only [sub_self, inv_zero, add_zero] using
              (Finset.sum_erase_add S (fun b : ℂ => (a - b)⁻¹) ha)
      rw [hsum] at hvel
      simp only [hvel, if_pos hr, Complex.mul_re, Complex.mul_im, Qs, ws, vs,
        show (2 : ℂ).re = (2 : ℝ) from rfl, show (2 : ℂ).im = (0 : ℝ) from rfl,
        zero_mul, sub_zero, add_zero, Complex.add_re, Complex.add_im]
      ring
    · have hw0 := hsupp _ (le_of_not_gt hr)
      have hv0 := cutoff_deriv_eq_zero hw hwn hw0
      simp only [ws, vs, Qs, if_neg hr, hw0, hv0, zero_mul, mul_zero, add_zero]
  have hp := packetQuarticPairDrift_le hconj hM hws hvs (fun x => hwn (x - X))
  have he := packetQuarticExteriorDrift_le (S := S) (w := ws) (v := vs) (Q := Qs) hK hV
    (fun a _ => ⟨hwn _, hwW _⟩) (fun a _ => hvV _) hQr hQi
  have hn : packetSquareWeight S ws = heatLocalizedVerticalEnergy X w t := by
    have h1 := heatLocalizedZeroObservable_eq_sum ht.le w (fun y => y ^ 2) hsupp S
      (fun z hz hr => (hpacket z).mpr ⟨hz, by linarith only [hr]⟩)
    change heatLocalizedVerticalEnergy X w t = _ at h1
    rw [h1, packetSquareWeight]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hm a ha, Nat.cast_one, one_mul]
  have hEn : 0 ≤ packetQuarticEnergy S := Finset.sum_nonneg fun _ _ => by positivity
  have houter := packetQuarticEnergy_le_outer ht.le (fun a ha => (hpacket a).mp ha)
  have hcoeff : 16 * M * (S.card : ℝ) + (2 * V + 8 * W) * K ≤ (16 * M + 2 * V + 8 * W) * K := by
    have h := mul_le_mul_of_nonneg_left hcard (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hM)
    nlinarith only [h]
  have hc0 : 0 ≤ (16 * M + 2 * V + 8 * W) * K := by positivity
  rw [hsumfield, ← hn]
  have h1 := mul_le_mul_of_nonneg_right hcoeff hEn
  have h2 := mul_le_mul_of_nonneg_left houter hc0
  nlinarith only [hp, he, h1, h2]

/-- **Dissipation of the fourth moment.** The localized fourth moment of the heights pays the integrated
second moment, through arbitrary collisions and from the unheated endpoint; the cutoff and exterior flux
cost `O(log X)` times nearby fourth moments. -/
theorem exists_uniform_heatLocalizedQuarticEnergy_evolution :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ (w v : ℝ → ℝ) (M V W : ℝ),
        0 ≤ M → 0 ≤ V → 0 ≤ W →
        (∀ x, HasDerivAt w (v x) x) →
        (∀ x, 0 ≤ w x) → (∀ x, w x ≤ W) → (∀ x, |v x| ≤ V) →
        (∀ x x', |v x - v x'| ≤ M * |x - x'|) →
        (∀ x, 1 ≤ |x| → w x = 0) →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 8 → b * Real.log X ≤ 1 →
          heatLocalizedQuarticEnergy X w b - heatLocalizedQuarticEnergy X w a +
              4 * (∫ s in a..b, heatLocalizedVerticalEnergy X w s) ≤
            (16 * M + 2 * V + 8 * W) * (C * Real.log X) *
              ∫ s in a..b, heatLocalizedQuarticEnergy X heatOuterCutoff s := by
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX w v M V W hM hV hW hw hwn hwW hvV hv hsupp a b ha hab hb hbX
  have hL : 0 ≤ Real.log X := (Real.log_pos (by linarith only [hX, hX₀])).le
  have hK : 0 ≤ C * Real.log X := mul_nonneg hC.le hL
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hcompact := hasCompactSupport_heat_cutoff hsupp
  let A := (16 * M + 2 * V + 8 * W) * (C * Real.log X)
  let E₂ := fun s => heatLocalizedQuarticEnergy X heatOuterCutoff (max s 0)
  let E₁ := fun s => heatLocalizedVerticalEnergy X w (max s 0)
  have hE₂c : Continuous E₂ := continuous_heatLocalizedZeroObservable_clamped
    continuous_heatOuterCutoff (by fun_prop : Continuous (fun y : ℝ => y ^ 4))
    hasCompactSupport_heatOuterCutoff X
  have hE₁c : Continuous E₁ := continuous_heatLocalizedZeroObservable_clamped
    hwc (by fun_prop : Continuous (fun y : ℝ => y ^ 2)) hcompact X
  have hfc : Continuous fun s => heatLocalizedQuarticEnergy X w (max s 0) :=
    continuous_heatLocalizedZeroObservable_clamped hwc
      (by fun_prop : Continuous (fun y : ℝ => y ^ 4)) hcompact X
  have hf : ContinuousOn (heatLocalizedQuarticEnergy X w) (Icc a b) :=
    hfc.continuousOn.congr fun s hs => by
      simp only [max_eq_left (ha.trans hs.1)]
  have hB : Continuous (fun s => A * E₂ s - 4 * E₁ s) :=
    (continuous_const.mul hE₂c).sub (continuous_const.mul hE₁c)
  have hineq := sub_le_integral_of_forward_deriv_le hab hf hB (by
    intro x hx
    have hx0 : 0 < x := ha.trans_lt hx.1
    obtain ⟨δ, hδ, hregular⟩ := exists_compact_simple_riemannHeat_zeros_forward
      hx0 (isCompact_closedBall (X : ℂ) 3)
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsb
    have hs0 : 0 < s := hx0.trans hs.1
    have hs8 : s ≤ 1 / 8 := hsb.le.trans hb
    have hsX : s * Real.log X ≤ 1 := (mul_le_mul_of_nonneg_right hsb.le hL).trans hbX
    obtain ⟨S, Q, hpacket, hcount, _, hQ⟩ := hcofactor X hX s hs0.le hs8 hsX
    have hsimple (z : ℂ) (hz : z ∈ S) : deriv (riemannHeat s) z ≠ 0 := by
      obtain ⟨hzero, hr⟩ := (hpacket z).mp hz
      have hi := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs0.le hzero
      have hzball : z ∈ closedBall (X : ℂ) 3 := by
        rw [mem_closedBall, dist_eq_norm]
        have hn := Complex.norm_le_abs_re_add_abs_im (z - (X : ℂ))
        simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
        linarith only [hn, hr, hi]
      exact (hregular s hs.1 hs.2 z hzball hzero).1
    obtain ⟨D, hD, hDb⟩ := heatLocalizedQuarticEnergy_simple_drift_le hs0 hM hV hW hK
      hw hwn hwW hvV hv hsupp hpacket hcount hsimple
      (fun z hr hi => ⟨(hQ z hr hi).1, (hQ z hr hi).2.1,
        (hQ z hr hi).2.2.2.1, (hQ z hr hi).2.2.2.2⟩)
    refine ⟨D, hD, ?_⟩
    dsimp only [A, E₁, E₂]
    rw [max_eq_left hs0.le]
    linarith only [hDb])
  have hE₂I : IntervalIntegrable E₂ volume a b := hE₂c.intervalIntegrable a b
  have hE₁I : IntervalIntegrable E₁ volume a b := hE₁c.intervalIntegrable a b
  have hE₂int : (∫ s in a..b, E₂ s) = ∫ s in a..b, heatLocalizedQuarticEnergy X heatOuterCutoff s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact congrArg (heatLocalizedQuarticEnergy X heatOuterCutoff) (max_eq_left (ha.trans hs.1))
  have hE₁int : (∫ s in a..b, E₁ s) = ∫ s in a..b, heatLocalizedVerticalEnergy X w s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact congrArg (heatLocalizedVerticalEnergy X w) (max_eq_left (ha.trans hs.1))
  rw [intervalIntegral.integral_sub (hE₂I.const_mul A) (hE₁I.const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hE₂int, hE₁int] at hineq
  linarith only [hineq]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
