import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.WindowEnergyLaplace
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The Bessel–Szegő certificate of the Zhukovsky collision loop

For a reflection-closed zero window and a Zhukovsky stage `n` (focal half-length `c`, Laurent
radius `ρ`, major axis `a = (c/2)(ρ + ρ⁻¹)`), assume the **stage-`n` corridor with margin `η`**:
twice every depth stays `η` below the vertex gap, `2 (Re z - 1/2) ≤ 1/2 - a - η`. Then every pair
difference `d = z - w` lies left of the focal segment, and the collision loop
`Λ(u) = P(J_n(u))²` admits an explicit closed-disk unit multiplier.

1. **Inner root** (`zhukovskyInnerRoot`): `v(p) = (p - √(p-c)√(p+c))/c` solves `c v² - 2pv + c = 0`,
   satisfies `|v| < 1`, `v(p̄) = conj v(p)`, and `ρ |v| ≤ 1 - η` once `Re p ≥ a + η`.
2. **Splitting** (`zhukovskyLoop_sub_eq_inner`): `J_n(u) - d = (c/(2v))(1 + ρ v u)(1 + v ū/ρ)` on `S¹`.
3. **Exact multiplier** (`exactSzegoMultiplier`): `F = ∏ ((1 + v u/ρ)/(1 + ρ v u))^{2 m_z m_w}` is a
   closed-disk unit with `F · Λ > 0` on `S¹`; its logarithm is the cepstral series
   `2 ∑ (1 - ρ^{-2k}) S_k u^k / k`, `S_k = ∑ m_z m_w (-ρ v_{z-w})^k`.
4. **Finite certificate** (`szegoCertificate`): `exp (2 ∑_{k ≤ K} (1 - ρ^{-2k}) S_k u^k / k)` is an
   entire zero-free multiplier, and it already certifies `Re (F_K Λ) > 0` once
   `2 D² (1 - η)^{K+1} / η < π / 2`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 The inner Zhukovsky root left of the focal segment -/

/-- Product of principal square roots `√(p - c) √(p + c)`. -/
def zhukovskySqrtPart (c : ℝ) (p : ℂ) : ℂ :=
  (p - c) ^ (2⁻¹ : ℂ) * (p + c) ^ (2⁻¹ : ℂ)

/-- Inner root `v = (p - √(p - c) √(p + c)) / c` of `c v² - 2 p v + c = 0`. -/
def zhukovskyInnerRoot (c : ℝ) (p : ℂ) : ℂ :=
  (p - zhukovskySqrtPart c p) / c

theorem zhukovskySqrtPart_sq (c : ℝ) (p : ℂ) :
    zhukovskySqrtPart c p ^ 2 = p ^ 2 - (c : ℂ) ^ 2 := by
  unfold zhukovskySqrtPart
  rw [mul_pow, Complex.cpow_ofNat_inv_pow, Complex.cpow_ofNat_inv_pow]
  ring

theorem zhukovskyInnerRoot_quadratic {c : ℝ} (hc : c ≠ 0) (p : ℂ) :
    (c : ℂ) * zhukovskyInnerRoot c p ^ 2 - 2 * p * zhukovskyInnerRoot c p + c = 0 := by
  have hs := zhukovskySqrtPart_sq c p
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hexp : (c : ℂ) * zhukovskyInnerRoot c p ^ 2 - 2 * p * zhukovskyInnerRoot c p + c =
      (zhukovskySqrtPart c p ^ 2 - p ^ 2 + (c : ℂ) ^ 2) / c := by
    unfold zhukovskyInnerRoot
    field_simp
    ring
  rw [hexp, hs]
  simp

/-- The principal square root of a right half-plane point lies in the sector `|arg| < π/4`. -/
theorem abs_im_lt_re_cpow_inv_two {x : ℂ} (hx : 0 < x.re) :
    |(x ^ (2⁻¹ : ℂ)).im| < (x ^ (2⁻¹ : ℂ)).re := by
  set A := x ^ (2⁻¹ : ℂ) with hA
  have hA2 : A ^ 2 = x := by rw [hA]; exact Complex.cpow_ofNat_inv_pow x 2
  have hre0 : 0 ≤ A.re := by rw [hA, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hre2 : A.re ^ 2 - A.im ^ 2 = x.re := by
    rw [← hA2]
    simp only [sq, Complex.mul_re]
  exact abs_lt_of_sq_lt_sq (by linarith) hre0

/-- `|v(p)| < 1` right of the focal point. -/
theorem norm_zhukovskyInnerRoot_lt_one {c : ℝ} {p : ℂ} (hc : 0 < c) (hp : c < p.re) :
    ‖zhukovskyInnerRoot c p‖ < 1 := by
  set A := (p - c) ^ (2⁻¹ : ℂ) with hA
  set B := (p + c) ^ (2⁻¹ : ℂ) with hB
  have hA2 : A ^ 2 = p - c := by rw [hA]; exact Complex.cpow_ofNat_inv_pow _ 2
  have hB2 : B ^ 2 = p + c := by rw [hB]; exact Complex.cpow_ofNat_inv_pow _ 2
  have hAre : |A.im| < A.re := abs_im_lt_re_cpow_inv_two (by simp; linarith)
  have hBre : |B.im| < B.re := abs_im_lt_re_cpow_inv_two (by simp; linarith)
  have hp_eq : p = (A ^ 2 + B ^ 2) / 2 := by rw [hA2, hB2]; ring
  have hcross : 0 < A.re * B.re + A.im * B.im := by
    have h1 : |A.im * B.im| < A.re * B.re := by
      rw [abs_mul]
      exact mul_lt_mul'' hAre hBre (abs_nonneg _) (abs_nonneg _)
    linarith [neg_abs_le (A.im * B.im)]
  have hBpos : 0 < B.re := lt_of_le_of_lt (abs_nonneg _) hBre
  have hsum : 0 < A.re ^ 2 + A.im ^ 2 + B.re ^ 2 + B.im ^ 2 := by positivity
  have hkey : p.re * (A * B).re + p.im * (A * B).im =
      (A.re * B.re + A.im * B.im) * (A.re ^ 2 + A.im ^ 2 + B.re ^ 2 + B.im ^ 2) / 2 := by
    rw [hp_eq]
    simp only [Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im, sq,
      Complex.mul_re, Complex.mul_im]
    norm_num
    ring
  have hlt : Complex.normSq (p - A * B) < Complex.normSq (p + A * B) := by
    rw [Complex.normSq_sub, Complex.normSq_add]
    have hre : (p * (starRingEnd ℂ) (A * B)).re = p.re * (A * B).re + p.im * (A * B).im := by
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hre, hkey]
    nlinarith [mul_pos hcross hsum]
  have hspart : zhukovskySqrtPart c p = A * B := rfl
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hvW : zhukovskyInnerRoot c p * ((p + A * B) / c) = 1 := by
    have hs2 := zhukovskySqrtPart_sq c p
    rw [hspart] at hs2
    unfold zhukovskyInnerRoot
    rw [hspart, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hc' hc')]
    linear_combination -hs2
  have hnorm : ‖zhukovskyInnerRoot c p‖ * ‖(p + A * B) / c‖ = 1 := by
    rw [← norm_mul, hvW, norm_one]
  have hlt' : ‖zhukovskyInnerRoot c p‖ < ‖(p + A * B) / c‖ := by
    unfold zhukovskyInnerRoot
    rw [hspart, norm_div, norm_div]
    refine div_lt_div_of_pos_right ?_ (norm_pos_iff.mpr hc')
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
  nlinarith [norm_nonneg (zhukovskyInnerRoot c p)]

theorem cpow_inv_two_star {y : ℂ} (hy : 0 < y.re) :
    (star y) ^ (2⁻¹ : ℂ) = star (y ^ (2⁻¹ : ℂ)) := by
  have harg : (star y).arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    simp only [Complex.star_def, Complex.conj_re] at this
    linarith
  have h := Complex.cpow_conj (star y) (2⁻¹ : ℂ) harg
  have hn : (starRingEnd ℂ) (2⁻¹ : ℂ) = 2⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [hn] at h
  simpa only [Complex.star_def, Complex.conj_conj] using h

/-- Conjugation symmetry of the inner root. -/
theorem zhukovskyInnerRoot_star {c : ℝ} {p : ℂ} (hc : 0 < c) (hp : c < p.re) :
    zhukovskyInnerRoot c (star p) = star (zhukovskyInnerRoot c p) := by
  unfold zhukovskyInnerRoot zhukovskySqrtPart
  have h1 : star p - (c : ℂ) = star (p - c) := by simp [star_sub]
  have h2 : star p + (c : ℂ) = star (p + c) := by simp [star_add]
  rw [h1, h2, cpow_inv_two_star (by simp; linarith), cpow_inv_two_star (by simp; linarith)]
  simp [star_div₀, star_sub, star_mul']

theorem two_le_add_inv {ρ : ℝ} (hρ : 0 < ρ) : 2 ≤ ρ + ρ⁻¹ := by
  have h : ρ + ρ⁻¹ - 2 = (ρ - 1) ^ 2 / ρ := by field_simp; ring
  have : 0 ≤ (ρ - 1) ^ 2 / ρ := by positivity
  linarith

/-- **Quantitative inner root bound.** If `Re p ≥ (c/2)(ρ + ρ⁻¹) + η` with `c ρ ≤ 1` and
`0 < η ≤ 1/2`, then `ρ |v(p)| ≤ 1 - η`. -/
theorem mul_norm_zhukovskyInnerRoot_le {c ρ η : ℝ} {p : ℂ} (hc : 0 < c) (hρ : 1 < ρ)
    (hcρ : c * ρ ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hp : c / 2 * (ρ + ρ⁻¹) + η ≤ p.re) :
    ρ * ‖zhukovskyInnerRoot c p‖ ≤ 1 - η := by
  have hρ0 : 0 < ρ := by linarith
  have hAM : c ≤ c / 2 * (ρ + ρ⁻¹) := by nlinarith [two_le_add_inv hρ0]
  have hpc : c < p.re := by linarith
  set v := zhukovskyInnerRoot c p with hv
  have hv1 : ‖v‖ < 1 := norm_zhukovskyInnerRoot_lt_one hc hpc
  have hq := zhukovskyInnerRoot_quadratic hc.ne' p
  rw [← hv] at hq
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hq
    simp at hq
    exact hc.ne' hq
  have hp_eq : p = (c : ℂ) / 2 * (v + v⁻¹) := by
    field_simp
    linear_combination -hq
  set r := ‖v‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hv0
  have hre_le : p.re ≤ c / 2 * (r + r⁻¹) := by
    calc p.re ≤ ‖p‖ := Complex.re_le_norm p
      _ = ‖(c : ℂ) / 2 * (v + v⁻¹)‖ := by rw [← hp_eq]
      _ ≤ c / 2 * (r + r⁻¹) := by
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          Complex.norm_ofNat]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_add_le _ _).trans ?_
        rw [norm_inv]
  set R := r⁻¹ with hR
  have hR1 : 1 < R := by rw [hR]; exact one_lt_inv₀ hr0 |>.mpr hv1
  have hRr : R⁻¹ = r := by rw [hR, inv_inv]
  have hineq : 2 * η / c ≤ (R + R⁻¹) - (ρ + ρ⁻¹) := by
    rw [div_le_iff₀ hc]
    have : c / 2 * (ρ + ρ⁻¹) + η ≤ c / 2 * (R + R⁻¹) := by
      rw [hRr]; linarith [add_comm r r⁻¹]
    nlinarith
  have hRρ : (R - ρ) * (R * ρ - 1) = R * ρ * ((R + R⁻¹) - (ρ + ρ⁻¹)) := by
    field_simp
    ring
  have hRρ1 : 0 < R * ρ - 1 := by nlinarith
  have hstep : R * ρ * (2 * η / c) ≤ (R - ρ) * (R * ρ - 1) := by
    rw [hRρ]
    exact mul_le_mul_of_nonneg_left hineq (by positivity)
  have hpos : 0 < R * ρ * (2 * η / c) := by positivity
  have hRmρ : 0 < R - ρ := by
    by_contra h
    have h' : R - ρ ≤ 0 := not_lt.mp h
    nlinarith
  have hRgt : 2 * η / c < R - ρ := by
    by_contra h
    have h' : R - ρ ≤ 2 * η / c := not_lt.mp h
    nlinarith
  have h2η : ρ ≤ 2 * (1 - η) / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hfinal : ρ ≤ (1 - η) * R := by
    have h1 : (1 - η) * (ρ + 2 * η / c) ≤ (1 - η) * R :=
      mul_le_mul_of_nonneg_left (by linarith : ρ + 2 * η / c ≤ R) (by linarith)
    have h2 : ρ ≤ (1 - η) * (ρ + 2 * η / c) := by
      have : η * ρ ≤ η * (2 * (1 - η) / c) := mul_le_mul_of_nonneg_left h2η hη.le
      have hexp : (1 - η) * (ρ + 2 * η / c) = ρ - η * ρ + η * (2 * (1 - η) / c) := by ring
      linarith
    linarith
  have hρr : ρ * r = ρ / R := by rw [hR, div_inv_eq_mul]
  rw [hρr, div_le_iff₀ (by linarith)]
  linarith

/-! ## §2 Inner splitting of the Zhukovsky loop -/

/-- **Inner Zhukovsky splitting.** On `S¹`, `J_n(u) - d = (c / (2v)) (1 + ρ v u) (1 + v ū / ρ)`
with `v` the inner root at `1/2 - d`. -/
theorem zhukovskyLoop_sub_eq_inner (n : ℕ) (d : ℂ) (u : HTGeometry.UnitCircle) :
    zhukovskyLoop n u - d =
      (zhukovskyFocal n : ℂ) / (2 * zhukovskyInnerRoot (zhukovskyFocal n) (1 / 2 - d)) *
        (1 + (zhukovskyRadius n : ℂ) * zhukovskyInnerRoot (zhukovskyFocal n) (1 / 2 - d) * u) *
        (1 + zhukovskyInnerRoot (zhukovskyFocal n) (1 / 2 - d) * star (u : ℂ) /
          (zhukovskyRadius n : ℂ)) := by
  set c := zhukovskyFocal n with hc_def
  set ρ := zhukovskyRadius n with hρ_def
  set v := zhukovskyInnerRoot c (1 / 2 - d) with hv
  have hc := zhukovskyFocal_pos n
  have hq := zhukovskyInnerRoot_quadratic hc.ne' (1 / 2 - d)
  rw [← hv] at hq
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hq
    simp at hq
    exact hc.ne' hq
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
  have huu : (u : ℂ) * star (u : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', HTGeometry.norm_coe_unitCircle]
    norm_num
  have hu_inv : (u : ℂ)⁻¹ = star (u : ℂ) := unitCircle_inv_eq_star u
  change zhukovskyMap n ((ρ : ℂ) * u) - d = _
  unfold zhukovskyMap
  rw [mul_inv, hu_inv]
  field_simp
  linear_combination (-(ρ : ℂ)) * hq + (-(c : ℂ) * ρ * v ^ 2) * huu


/-! ## §3 The exact outer multiplier of a corridor window -/

theorem zhukovskyFocal_lt_majorAxis (n : ℕ) : zhukovskyFocal n < zhukovskyMajorAxis n := by
  have ha := zhukovskyMajorAxis_pos n
  have hb := zhukovskyMinorAxis_pos n
  have hc := zhukovskyFocal_pos n
  have hsq := zhukovskyFocal_sq n
  nlinarith

theorem zhukovskyFocal_mul_radius_le_one (n : ℕ) : zhukovskyFocal n * zhukovskyRadius n ≤ 1 := by
  rw [zhukovskyFocal_mul_radius]
  linarith [zhukovskyMajorAxis_lt_half n, zhukovskyMinorAxis_le_sixth n]

theorem zhukovskyInnerRoot_ne_zero {c : ℝ} (hc : c ≠ 0) (p : ℂ) : zhukovskyInnerRoot c p ≠ 0 := by
  intro h0
  have hq := zhukovskyInnerRoot_quadratic hc p
  rw [h0] at hq
  simp at hq
  exact hc hq

private theorem prod_prod_mul (s : Finset ℂ) (f g : ℂ → ℂ → ℂ) :
    (∏ z ∈ s, ∏ w ∈ s, f z w) * (∏ z ∈ s, ∏ w ∈ s, g z w) =
      ∏ z ∈ s, ∏ w ∈ s, f z w * g z w := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun z _ => Finset.prod_mul_distrib.symm

theorem one_add_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 + x ≠ 0 := by
  intro h
  have h' : x = -1 := by linear_combination h
  rw [h', norm_neg, norm_one] at hx
  exact lt_irrefl 1 hx

namespace ReflectedWindow

/-- Inner Zhukovsky root `v_d` of a pair difference `d` at stage `n`. -/
def pairInnerRoot (n : ℕ) (d : ℂ) : ℂ :=
  zhukovskyInnerRoot (zhukovskyFocal n) (1 / 2 - d)

/-- Numerator factor `1 + v_d u / ρ`. -/
def innerNum (n : ℕ) (d u : ℂ) : ℂ :=
  1 + pairInnerRoot n d * u / (zhukovskyRadius n : ℂ)

/-- Denominator factor `1 + ρ v_d u`. -/
def innerDen (n : ℕ) (d u : ℂ) : ℂ :=
  1 + (zhukovskyRadius n : ℂ) * pairInnerRoot n d * u

variable (W : ReflectedWindow) (n : ℕ)

/-- Stage-`n` corridor with margin `η`: `2 (Re z - 1/2) ≤ 1/2 - a_n - η` on the window. -/
def InCorridor (η : ℝ) : Prop :=
  ∀ z ∈ W.Z, 2 * (z.re - 1 / 2) ≤ 1 / 2 - zhukovskyMajorAxis n - η

/-- Exact outer multiplier `F(u) = ∏ ((1 + v u / ρ) / (1 + ρ v u))^{2 m_z m_w}`. -/
def exactSzegoMultiplier (u : ℂ) : ℂ :=
  ∏ z ∈ W.Z, ∏ w ∈ W.Z,
    (innerNum n (z - w) u / innerDen n (z - w) u) ^ (2 * (W.mult z * W.mult w))

/-- Cepstral coefficients `S_k = ∑ m_z m_w (-ρ v_{z-w})^k`. -/
def cepstralCoeff (k : ℕ) : ℂ :=
  ∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) *
    (-(zhukovskyRadius n : ℂ) * pairInnerRoot n (z - w)) ^ k

variable {W n}

theorem InCorridor.pair_re {η : ℝ} (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z)
    (hw : w ∈ W.Z) : zhukovskyMajorAxis n + η ≤ (1 / 2 - (z - w)).re := by
  have h := W.re_sub_le (δ := (1 / 2 - zhukovskyMajorAxis n - η) / 2)
    (fun z hz => by have := hcorr z hz; linarith) hz hw
  have hre : (1 / 2 - (z - w)).re = 1 / 2 - (z - w).re := by simp
  rw [hre]
  linarith

theorem InCorridor.focal_lt {η : ℝ} (hη : 0 ≤ η) (hcorr : W.InCorridor n η) {z w : ℂ}
    (hz : z ∈ W.Z) (hw : w ∈ W.Z) : zhukovskyFocal n < (1 / 2 - (z - w)).re := by
  linarith [hcorr.pair_re hz hw, zhukovskyFocal_lt_majorAxis n]

theorem InCorridor.radius_mul_norm_le {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) :
    zhukovskyRadius n * ‖pairInnerRoot n (z - w)‖ ≤ 1 - η :=
  mul_norm_zhukovskyInnerRoot_le (zhukovskyFocal_pos n) (one_lt_zhukovskyRadius n)
    (zhukovskyFocal_mul_radius_le_one n) hη hη2
    (by rw [zhukovskyAxis_major_identity]; exact hcorr.pair_re hz hw)

theorem InCorridor.norm_lt_one {η : ℝ} (hη : 0 ≤ η) (hcorr : W.InCorridor n η) {z w : ℂ}
    (hz : z ∈ W.Z) (hw : w ∈ W.Z) : ‖pairInnerRoot n (z - w)‖ < 1 :=
  norm_zhukovskyInnerRoot_lt_one (zhukovskyFocal_pos n) (hcorr.focal_lt hη hz hw)

theorem InCorridor.innerDen_ne_zero {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) {u : ℂ}
    (hu : ‖u‖ ≤ 1) : innerDen n (z - w) u ≠ 0 := by
  refine one_add_ne_zero_of_norm_lt_one ?_
  have hb := hcorr.radius_mul_norm_le hη hη2 hz hw
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zhukovskyRadius_pos n)]
  calc zhukovskyRadius n * ‖pairInnerRoot n (z - w)‖ * ‖u‖
      ≤ zhukovskyRadius n * ‖pairInnerRoot n (z - w)‖ * 1 :=
        mul_le_mul_of_nonneg_left hu (mul_nonneg (zhukovskyRadius_pos n).le (norm_nonneg _))
    _ < 1 := by linarith

theorem InCorridor.innerNum_ne_zero {η : ℝ} (hη : 0 ≤ η) (hcorr : W.InCorridor n η) {z w : ℂ}
    (hz : z ∈ W.Z) (hw : w ∈ W.Z) {u : ℂ} (hu : ‖u‖ ≤ 1) : innerNum n (z - w) u ≠ 0 := by
  refine one_add_ne_zero_of_norm_lt_one ?_
  have hv := hcorr.norm_lt_one hη hz hw
  have hρ := one_lt_zhukovskyRadius n
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zhukovskyRadius_pos n), div_lt_one (zhukovskyRadius_pos n)]
  calc ‖pairInnerRoot n (z - w)‖ * ‖u‖ ≤ ‖pairInnerRoot n (z - w)‖ * 1 :=
        mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ < zhukovskyRadius n := by linarith

/-- Conjugation of a corridor pair difference conjugates its inner root. -/
theorem InCorridor.pairInnerRoot_star {η : ℝ} (hη : 0 ≤ η) (hcorr : W.InCorridor n η)
    {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) :
    pairInnerRoot n (star (z - w)) = star (pairInnerRoot n (z - w)) := by
  unfold pairInnerRoot
  have h : (1 / 2 : ℂ) - star (z - w) = star (1 / 2 - (z - w)) := by
    rw [star_sub]
    simp
  rw [h]
  exact zhukovskyInnerRoot_star (zhukovskyFocal_pos n) (hcorr.focal_lt hη hz hw)

/-- **The exact multiplier is a closed-disk unit.** -/
theorem isDiskUnit_exactSzegoMultiplier {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) : IsDiskUnit (W.exactSzegoMultiplier n) := by
  refine ⟨?_, fun u hu => ?_⟩
  · unfold exactSzegoMultiplier
    refine continuousOn_finsetProd _ fun z hz => continuousOn_finsetProd _ fun w hw => ?_
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ fun u hu => ?_) _
    · unfold innerNum; fun_prop
    · unfold innerDen; fun_prop
    · rw [Metric.mem_closedBall, dist_zero_right] at hu
      exact hcorr.innerDen_ne_zero hη hη2 hz hw hu
  · rw [Metric.mem_closedBall, dist_zero_right] at hu
    unfold exactSzegoMultiplier
    exact Finset.prod_ne_zero_iff.mpr fun z hz => Finset.prod_ne_zero_iff.mpr fun w hw =>
      pow_ne_zero _ (div_ne_zero (hcorr.innerNum_ne_zero hη.le hz hw hu)
        (hcorr.innerDen_ne_zero hη hη2 hz hw hu))


/-- **Exact Szegő positivity.** On `S¹`, `F · Λ` is a positive real number:
`F_B B = κ X X̄` with `κ = ∏ (c/(2v))^{m}` real by conjugation symmetry of the pair divisor. -/
theorem exactSzegoMultiplier_mul_loop_eq_pos {P : Polynomial ℂ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η)
    (u : HTGeometry.UnitCircle) :
    ∃ r : ℝ, 0 < r ∧ W.exactSzegoMultiplier n u * polyZhukovskyLaurentLoop n P u = r := by
  have hu1 : ‖(u : ℂ)‖ ≤ 1 := (HTGeometry.norm_coe_unitCircle u).le
  have hc0 : (zhukovskyFocal n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyFocal_pos n).ne'
  set κ : ℂ := ∏ z ∈ W.Z, ∏ w ∈ W.Z,
    ((zhukovskyFocal n : ℂ) / (2 * pairInnerRoot n (z - w))) ^ (W.mult z * W.mult w) with hκ
  set X : ℂ := ∏ z ∈ W.Z, ∏ w ∈ W.Z, innerNum n (z - w) u ^ (W.mult z * W.mult w) with hX
  set Y : ℂ := ∏ z ∈ W.Z, ∏ w ∈ W.Z,
    innerNum n (z - w) (star (u : ℂ)) ^ (W.mult z * W.mult w) with hY
  set FB : ℂ := ∏ z ∈ W.Z, ∏ w ∈ W.Z,
    (innerNum n (z - w) u / innerDen n (z - w) u) ^ (W.mult z * W.mult w) with hFB_def
  have hFB : FB * P.eval (zhukovskyLoop n u) = κ * X * Y := by
    rw [heval, hFB_def, prod_prod_mul, hκ, hX, hY, prod_prod_mul, prod_prod_mul]
    refine Finset.prod_congr rfl fun z hz => Finset.prod_congr rfl fun w hw => ?_
    have hs : zhukovskyLoop n u - (z - w) =
        (zhukovskyFocal n : ℂ) / (2 * pairInnerRoot n (z - w)) * innerDen n (z - w) u *
          innerNum n (z - w) (star (u : ℂ)) := zhukovskyLoop_sub_eq_inner n (z - w) u
    rw [← mul_pow, ← mul_pow, ← mul_pow, hs]
    congr 1
    have hden := hcorr.innerDen_ne_zero hη hη2 hz hw hu1
    field_simp
  have hYX : Y = star X := by
    rw [hY, hX, W.prod_pair_conj (fun d => innerNum n d (star (u : ℂ)))]
    simp only [Complex.star_def, map_prod, map_pow]
    refine Finset.prod_congr rfl fun z hz => Finset.prod_congr rfl fun w hw => ?_
    congr 1
    have hv := hcorr.pairInnerRoot_star hη.le hz hw
    simp only [Complex.star_def] at hv
    unfold innerNum
    rw [hv]
    simp [map_div₀]
  have hκstar : star κ = κ := by
    have h1 : κ = ∏ z ∈ W.Z, ∏ w ∈ W.Z, ((zhukovskyFocal n : ℂ) /
        (2 * pairInnerRoot n (star (z - w)))) ^ (W.mult z * W.mult w) :=
      hκ.trans (W.prod_pair_conj (fun d => (zhukovskyFocal n : ℂ) / (2 * pairInnerRoot n d)))
    calc star κ = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (star ((zhukovskyFocal n : ℂ) /
          (2 * pairInnerRoot n (z - w)))) ^ (W.mult z * W.mult w) := by
          rw [hκ]
          simp only [Complex.star_def, map_prod, map_pow]
      _ = ∏ z ∈ W.Z, ∏ w ∈ W.Z, ((zhukovskyFocal n : ℂ) /
          (2 * pairInnerRoot n (star (z - w)))) ^ (W.mult z * W.mult w) := by
          refine Finset.prod_congr rfl fun z hz => Finset.prod_congr rfl fun w hw => ?_
          rw [hcorr.pairInnerRoot_star hη.le hz hw]
          simp only [Complex.star_def, map_div₀, map_mul, map_ofNat, Complex.conj_ofReal]
      _ = κ := h1.symm
  have hκreal : κ = (κ.re : ℂ) := (Complex.conj_eq_iff_re.mp hκstar).symm
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact Finset.prod_ne_zero_iff.mpr fun z _ => Finset.prod_ne_zero_iff.mpr fun w _ =>
      pow_ne_zero _ (div_ne_zero hc0 (mul_ne_zero two_ne_zero
        (zhukovskyInnerRoot_ne_zero (zhukovskyFocal_pos n).ne' _)))
  have hκre0 : κ.re ≠ 0 := by
    intro h
    apply hκ0
    rw [hκreal, h, Complex.ofReal_zero]
  have hX0 : X ≠ 0 := by
    rw [hX]
    exact Finset.prod_ne_zero_iff.mpr fun z hz => Finset.prod_ne_zero_iff.mpr fun w hw =>
      pow_ne_zero _ (hcorr.innerNum_ne_zero hη.le hz hw hu1)
  have hF : W.exactSzegoMultiplier n u = FB ^ 2 := by
    unfold exactSzegoMultiplier
    rw [hFB_def, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← pow_mul, mul_comm]
  refine ⟨(κ.re * ‖X‖ ^ 2) ^ 2, by positivity, ?_⟩
  rw [hF, polyZhukovskyLaurentLoop_apply, ← mul_pow, hFB, hYX]
  rw [mul_assoc, Complex.star_def, Complex.mul_conj', hκreal]
  push_cast
  simp only [Complex.ofReal_re]


/-! ### Cepstral series -/

/-- Per-pair cepstral series `∑ (1 - ρ^{-2k}) a^k u^k / k = log (1 + v u/ρ) - log (1 + ρ v u)`,
`a = -ρ v`. -/
theorem InCorridor.hasSum_pair_log {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    HasSum (fun k : ℕ => (1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
        (-(zhukovskyRadius n : ℂ) * pairInnerRoot n (z - w)) ^ k / k * u ^ k)
      (Complex.log (innerNum n (z - w) u) - Complex.log (innerDen n (z - w) u)) := by
  set ρ : ℂ := (zhukovskyRadius n : ℂ) with hρ
  set v := pairInnerRoot n (z - w) with hv
  have hρ1 := one_lt_zhukovskyRadius n
  have hρ0 : ρ ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
  have hnormρ : ‖ρ‖ = zhukovskyRadius n := by
    rw [hρ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zhukovskyRadius_pos n)]
  set A : ℂ := -ρ * v * u with hA
  set B : ℂ := A * (ρ⁻¹) ^ 2 with hB
  have hAn : ‖A‖ < 1 := by
    have hb := hcorr.radius_mul_norm_le hη hη2 hz hw
    rw [hA, norm_mul, norm_mul, norm_neg, hnormρ]
    calc zhukovskyRadius n * ‖v‖ * ‖u‖ ≤ zhukovskyRadius n * ‖v‖ * 1 :=
          mul_le_mul_of_nonneg_left hu (mul_nonneg (zhukovskyRadius_pos n).le (norm_nonneg _))
      _ < 1 := by linarith
  have hBn : ‖B‖ < 1 := by
    rw [hB, norm_mul, norm_pow, norm_inv, hnormρ]
    have hle : (zhukovskyRadius n)⁻¹ ^ 2 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (zhukovskyRadius_pos n).le) (inv_le_one_of_one_le₀ hρ1.le)
    calc ‖A‖ * (zhukovskyRadius n)⁻¹ ^ 2 ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ < 1 := by linarith
  have hden : 1 - A = innerDen n (z - w) u := by
    unfold innerDen
    rw [← hρ, ← hv, hA]
    ring
  have hnum : 1 - B = innerNum n (z - w) u := by
    unfold innerNum
    rw [← hρ, ← hv, hB, hA]
    field_simp
    ring
  have h := (Complex.hasSum_taylorSeries_neg_log hAn).sub (Complex.hasSum_taylorSeries_neg_log hBn)
  rw [hden, hnum] at h
  have hfun : (fun k : ℕ => (1 - ρ⁻¹ ^ (2 * k)) * (-ρ * v) ^ k / k * u ^ k) =
      fun k : ℕ => A ^ k / k - B ^ k / k := by
    funext k
    have h1 : B ^ k = A ^ k * ρ⁻¹ ^ (2 * k) := by rw [hB, mul_pow, ← pow_mul]
    have h2 : A ^ k = (-ρ * v) ^ k * u ^ k := by rw [hA, mul_pow]
    rw [h1, h2]
    ring
  rw [hfun, show Complex.log (innerNum n (z - w) u) - Complex.log (innerDen n (z - w) u) =
    -Complex.log (innerDen n (z - w) u) - -Complex.log (innerNum n (z - w) u) by ring]
  exact h

/-- **Cepstral series of the exact multiplier.** On the closed disk,
`∑_k 2 (1 - ρ^{-2k}) S_k u^k / k` sums to `∑ 2 m_z m_w (log (1 + v u/ρ) - log (1 + ρ v u))`. -/
theorem InCorridor.hasSum_cepstral {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    HasSum (fun k : ℕ => 2 * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
        W.cepstralCoeff n k / k * u ^ k))
      (∑ z ∈ W.Z, ∑ w ∈ W.Z, (((2 * (W.mult z * W.mult w) : ℕ) : ℂ)) *
        (Complex.log (innerNum n (z - w) u) - Complex.log (innerDen n (z - w) u))) := by
  have hpairs := fun z (hz : z ∈ W.Z) => hasSum_sum fun w (hw : w ∈ W.Z) =>
    (hcorr.hasSum_pair_log hη hη2 hz hw hu).mul_left (((2 * (W.mult z * W.mult w) : ℕ) : ℂ))
  have hfun : (fun k : ℕ => 2 * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
      W.cepstralCoeff n k / k * u ^ k)) = fun k : ℕ => ∑ z ∈ W.Z, ∑ w ∈ W.Z,
        (((2 * (W.mult z * W.mult w) : ℕ) : ℂ)) * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
          (-(zhukovskyRadius n : ℂ) * pairInnerRoot n (z - w)) ^ k / k * u ^ k) := by
    funext k
    unfold cepstralCoeff
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    ring
  rw [hfun]
  exact hasSum_sum hpairs

/-- **Cepstral formula.** On the closed disk the exact multiplier is
`F(u) = exp (∑_k 2 (1 - ρ^{-2k}) S_k u^k / k)`. -/
theorem InCorridor.exactSzegoMultiplier_eq_exp {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    W.exactSzegoMultiplier n u = cexp (∑' k : ℕ, 2 * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
        W.cepstralCoeff n k / k * u ^ k)) := by
  rw [(hcorr.hasSum_cepstral hη hη2 hu).tsum_eq, Complex.exp_sum]
  unfold exactSzegoMultiplier
  refine Finset.prod_congr rfl fun z hz => ?_
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Complex.exp_nat_mul, Complex.exp_sub,
    Complex.exp_log (hcorr.innerNum_ne_zero hη.le hz hw hu),
    Complex.exp_log (hcorr.innerDen_ne_zero hη hη2 hz hw hu)]

/-! ### The finite certificate -/

/-- `‖S_k‖ ≤ D² (1 - η)^k` on a corridor window. -/
theorem InCorridor.norm_cepstralCoeff_le {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) (k : ℕ) :
    ‖W.cepstralCoeff n k‖ ≤ (W.degree : ℝ) ^ 2 * (1 - η) ^ k := by
  unfold cepstralCoeff degree
  rw [sq, Nat.cast_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zhukovskyRadius_pos n), Complex.norm_natCast]
  push_cast
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg (zhukovskyRadius_pos n).le (norm_nonneg _))
      (hcorr.radius_mul_norm_le hη hη2 hz hw) k) (by positivity)

end ReflectedWindow

/-- Finite Szegő certificate `exp (∑_{k ≤ K} 2 (1 - ρ^{-2k}) s_k u^k / k)` with coefficients `s`. -/
def szegoCertificate (n K : ℕ) (s : ℕ → ℂ) (u : ℂ) : ℂ :=
  cexp (∑ k ∈ Finset.range (K + 1),
    2 * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) * s k / k * u ^ k))

/-- Every finite certificate is an entire zero-free function, hence a closed-disk unit. -/
theorem isDiskUnit_szegoCertificate (n K : ℕ) (s : ℕ → ℂ) :
    IsDiskUnit (szegoCertificate n K s) := by
  refine ⟨?_, fun u _ => Complex.exp_ne_zero _⟩
  unfold szegoCertificate
  fun_prop

namespace ReflectedWindow

variable {W : ReflectedWindow} {n : ℕ}

/-- **Finite certificate completeness.** On a corridor window with margin `η`, the order-`K`
certificate built from the cepstral coefficients makes the collision loop sectorial as soon as
`2 D² (1 - η)^{K+1} / η < π / 2`. -/
theorem InCorridor.szegoCertificate_mul_loop_pos {P : Polynomial ℂ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) {K : ℕ}
    (hK : 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ (K + 1) / η < Real.pi / 2)
    (u : HTGeometry.UnitCircle) :
    0 < (szegoCertificate n K (W.cepstralCoeff n) u * polyZhukovskyLaurentLoop n P u).re := by
  have hu1 : ‖(u : ℂ)‖ ≤ 1 := (HTGeometry.norm_coe_unitCircle u).le
  set t : ℕ → ℂ := fun k => 2 * ((1 - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)) *
    W.cepstralCoeff n k / k * (u : ℂ) ^ k) with ht
  have hsum := hcorr.hasSum_cepstral hη hη2 hu1
  set L := ∑ z ∈ W.Z, ∑ w ∈ W.Z, (((2 * (W.mult z * W.mult w) : ℕ) : ℂ)) *
    (Complex.log (innerNum n (z - w) (u : ℂ)) - Complex.log (innerDen n (z - w) (u : ℂ)))
  have hF : W.exactSzegoMultiplier n u = cexp L := by
    rw [hcorr.exactSzegoMultiplier_eq_exp hη hη2 hu1, hsum.tsum_eq]
  set T := L - ∑ k ∈ Finset.range (K + 1), t k with hT
  have htail : HasSum (fun j => t (j + (K + 1))) T := (hasSum_nat_add_iff' (K + 1)).mpr hsum
  have hterm : ∀ k : ℕ, ‖t k‖ ≤ 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [ht, mul_zero, pow_zero, sub_self, zero_mul, zero_div, norm_zero]
      positivity
    have hρk : ‖(1 : ℂ) - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)‖ ≤ 1 := by
      have h0 : 0 ≤ (zhukovskyRadius n)⁻¹ ^ (2 * k) :=
        pow_nonneg (inv_nonneg.mpr (zhukovskyRadius_pos n).le) _
      have h1 : (zhukovskyRadius n)⁻¹ ^ (2 * k) ≤ 1 :=
        pow_le_one₀ (inv_nonneg.mpr (zhukovskyRadius_pos n).le)
          (inv_le_one_of_one_le₀ (one_lt_zhukovskyRadius n).le)
      rw [show (1 : ℂ) - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k) =
        ((1 - (zhukovskyRadius n)⁻¹ ^ (2 * k) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hS := hcorr.norm_cepstralCoeff_le hη hη2 k
    simp only [ht]
    rw [norm_mul, norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
      HTGeometry.norm_coe_unitCircle, one_pow, mul_one, Complex.norm_ofNat]
    have hdiv : ‖W.cepstralCoeff n k‖ / (k : ℝ) ≤ ‖W.cepstralCoeff n k‖ :=
      div_le_self (norm_nonneg _) hk1
    calc 2 * (‖(1 : ℂ) - ((zhukovskyRadius n : ℂ)⁻¹) ^ (2 * k)‖ * ‖W.cepstralCoeff n k‖ / k)
        ≤ 2 * (1 * ‖W.cepstralCoeff n k‖ / k) := by gcongr
      _ ≤ 2 * ((W.degree : ℝ) ^ 2 * (1 - η) ^ k) := by rw [one_mul]; gcongr; linarith
      _ = 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ k := by ring
  have hgeom : HasSum (fun j : ℕ => 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ (K + 1) * (1 - η) ^ j)
      (2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ (K + 1) * (1 - (1 - η))⁻¹) :=
    (hasSum_geometric_of_lt_one (by linarith) (by linarith)).mul_left _
  have hTle : ‖T‖ ≤ 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ (K + 1) / η := by
    have h := htail.norm_le_of_bounded hgeom fun j => by
      refine (hterm (j + (K + 1))).trans (le_of_eq ?_)
      rw [pow_add]; ring
    rw [sub_sub_cancel, ← div_eq_mul_inv] at h
    exact h
  obtain ⟨r, hr, hFΛ⟩ := W.exactSzegoMultiplier_mul_loop_eq_pos heval hη hη2 hcorr u
  have hcert : szegoCertificate n K (W.cepstralCoeff n) u = W.exactSzegoMultiplier n u * cexp (-T) := by
    rw [hF, ← Complex.exp_add, hT]
    unfold szegoCertificate
    congr 1
    ring
  rw [hcert, mul_comm (W.exactSzegoMultiplier n u), mul_assoc, hFΛ, Complex.re_mul_ofReal,
    Complex.exp_re]
  have him : |(-T).im| < Real.pi / 2 := by
    rw [Complex.neg_im, abs_neg]
    exact (Complex.abs_im_le_norm T).trans_lt (hTle.trans_lt hK)
  have hcos : 0 < Real.cos (-T).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (-T).im],
    by linarith [le_abs_self (-T).im]⟩
  positivity

end ReflectedWindow

/-! ## §5 Bessel form of the cepstrum -/

/-- Modified Bessel function of integer order, `I_j(x) = ∑_i (x/2)^{j+2i} / (i! (j+i)!)`. -/
def besselI (j : ℕ) (x : ℝ) : ℝ :=
  ∑' i : ℕ, (x / 2) ^ (j + 2 * i) / ((i.factorial : ℝ) * ((j + i).factorial : ℝ))

theorem summable_besselI_term (j : ℕ) (x : ℝ) :
    Summable fun i : ℕ => (x / 2) ^ (j + 2 * i) / ((i.factorial : ℝ) * ((j + i).factorial : ℝ)) := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left (|x / 2| ^ j)) fun i => ?_
  have hi : (0 : ℝ) < i.factorial := Nat.cast_pos.mpr (Nat.factorial_pos i)
  have hji : (1 : ℝ) ≤ (j + i).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have key : |(x / 2) ^ (j + 2 * i)| = |x / 2| ^ j * ((x / 2) ^ 2) ^ i := by
    rw [abs_pow, pow_add, pow_mul, sq_abs]
  have hden : (0 : ℝ) < (i.factorial : ℝ) * ((j + i).factorial : ℝ) := mul_pos hi (by linarith)
  rw [Real.norm_eq_abs, abs_div, key, abs_of_pos hden]
  have h1 : |x / 2| ^ j * ((x / 2) ^ 2) ^ i / ((i.factorial : ℝ) * ((j + i).factorial : ℝ)) ≤
      |x / 2| ^ j * ((x / 2) ^ 2) ^ i / (i.factorial : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hi (by nlinarith)
  calc _ ≤ _ := h1
    _ = |x / 2| ^ j * (((x / 2) ^ 2) ^ i / (i.factorial : ℝ)) := by ring

theorem besselI_nonneg (j : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ besselI j x :=
  tsum_nonneg fun i => by positivity

/-- `I_{m+2}(x) ≤ I_m(x)` for `x ≥ 0`: termwise `i!(m+i+2)! ≥ (i+1)!(m+i+1)!`. -/
theorem besselI_add_two_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : besselI (m + 2) x ≤ besselI m x := by
  have hs := summable_besselI_term m x
  have hs1 : Summable fun i : ℕ => (x / 2) ^ (m + 2 * (i + 1)) /
      (((i + 1).factorial : ℝ) * ((m + (i + 1)).factorial : ℝ)) :=
    (summable_nat_add_iff 1).mpr hs
  unfold besselI
  rw [hs.tsum_eq_zero_add]
  have hle : ∑' i : ℕ, (x / 2) ^ (m + 2 + 2 * i) /
      ((i.factorial : ℝ) * ((m + 2 + i).factorial : ℝ)) ≤
      ∑' i : ℕ, (x / 2) ^ (m + 2 * (i + 1)) /
        (((i + 1).factorial : ℝ) * ((m + (i + 1)).factorial : ℝ)) := by
    refine (summable_besselI_term (m + 2) x).tsum_le_tsum (fun i => ?_) hs1
    have hexp : m + 2 + 2 * i = m + 2 * (i + 1) := by ring
    rw [hexp]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    have h1 : ((i + 1).factorial : ℝ) = (i + 1) * i.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h2 : ((m + 2 + i).factorial : ℝ) = (m + i + 2) * (m + (i + 1)).factorial := by
      rw [show m + 2 + i = (m + (i + 1)) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [h1, h2]
    have hf1 : (0 : ℝ) ≤ i.factorial := Nat.cast_nonneg _
    have hf2 : (0 : ℝ) ≤ (m + (i + 1)).factorial := Nat.cast_nonneg _
    have hmi : (i : ℝ) + 1 ≤ m + i + 2 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    nlinarith [mul_nonneg hf1 hf2]
  have h0 : 0 ≤ (x / 2) ^ (m + 2 * 0) / (((0 : ℕ).factorial : ℝ) * ((m + 0).factorial : ℝ)) := by
    positivity
  linarith

/-- Integral of a Fourier mode over one period. -/
theorem integral_exp_int_mul_I (m : ℤ) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), cexp ((m : ℂ) * I * θ) =
      if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hm
  · simp [hm]
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : cexp ((m : ℂ) * I * (2 * (Real.pi : ℂ))) = 1 := by
      rw [show (m : ℂ) * I * (2 * (Real.pi : ℂ)) = m * (2 * Real.pi * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    push_cast
    simp [h1]

/-- Termwise integration of an absolutely summable Fourier series over one period. -/
theorem integral_tsum_modes {ι : Type*} [Countable ι] (c : ι → ℂ) (m : ι → ℤ)
    (hc : Summable fun i => ‖c i‖) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∑' i, c i * cexp ((m i : ℂ) * I * θ) =
      ∑' i, c i * (if m i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
  have hnorm : ∀ i (θ : ℝ), ‖c i * cexp ((m i : ℂ) * I * θ)‖ = ‖c i‖ := by
    intro i θ
    rw [norm_mul, Complex.norm_exp]
    simp
  have hint : ∀ i, Integrable (fun θ : ℝ => c i * cexp ((m i : ℂ) * I * θ))
      (volume.restrict (Ioc 0 (2 * Real.pi))) := fun i =>
    ((by fun_prop : Continuous fun θ : ℝ => c i * cexp ((m i : ℂ) * I * θ)).integrableOn_Icc
      (a := 0) (b := 2 * Real.pi)).mono_set Ioc_subset_Icc_self
  have hsum : Summable fun i => ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
      ‖c i * cexp ((m i : ℂ) * I * θ)‖ := by
    simp_rw [hnorm, setIntegral_const, smul_eq_mul]
    exact hc.mul_left _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun i => ?_
  rw [integral_const_mul, integral_exp_int_mul_I]


/-- Exponential splitting `e^{-t J(e^{iθ})} = e^{-t/2} exp(A e^{iθ}) exp(A' e^{-iθ})` with
`A = -cρt/2`, `A' = -ct/(2ρ)`. -/
theorem exp_neg_zhukovskyLoop_circleExp (n : ℕ) (t θ : ℝ) :
    cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) =
      cexp (-((t : ℂ) / 2)) *
        (cexp (((-(zhukovskyFocal n * zhukovskyRadius n * t / 2) : ℝ) : ℂ) * cexp (θ * I)) *
          cexp (((-(zhukovskyFocal n * t / (2 * zhukovskyRadius n)) : ℝ) : ℂ) *
            cexp (-(θ * I)))) := by
  have hρ0 : (zhukovskyRadius n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
  change cexp (-(zhukovskyMap n ((zhukovskyRadius n : ℂ) * cexp (θ * I)) * t)) = _
  unfold zhukovskyMap
  rw [← Complex.exp_add, ← Complex.exp_add, mul_inv, ← Complex.exp_neg]
  congr 1
  push_cast
  field_simp
  ring

/-- `(-ρ y)^{b+j} (-y/ρ)^b = (-ρ)^j y^{j+2b}`. -/
private theorem bessel_coeff_identity {ρ : ℝ} (hρ : ρ ≠ 0) (y : ℝ) (b j : ℕ) :
    (-ρ * y) ^ (b + j) * (-y / ρ) ^ b = (-ρ) ^ j * y ^ (j + 2 * b) := by
  have h : (-ρ * y) ^ b * (-y / ρ) ^ b = (y ^ 2) ^ b := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (-ρ * y) ^ (b + j) * (-y / ρ) ^ b
      = ((-ρ * y) ^ b * (-y / ρ) ^ b) * (-ρ * y) ^ j := by rw [pow_add]; ring
    _ = (y ^ 2) ^ b * (-ρ * y) ^ j := by rw [h]
    _ = (-ρ) ^ j * y ^ (j + 2 * b) := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- **Fourier coefficients of `e^{-tJ}`.** The `j`-th Fourier coefficient of
`θ ↦ e^{-t J_n(e^{iθ})}` is `e^{-t/2} (-ρ)^j I_j(c t)`. -/
theorem integral_mode_mul_exp_neg_zhukovskyLoop (n j : ℕ) (t : ℝ) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        cexp (((-(j : ℤ) : ℤ) : ℂ) * I * θ) * cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) =
      ((2 * Real.pi * (Real.exp (-(t / 2)) * (-zhukovskyRadius n) ^ j *
        besselI j (zhukovskyFocal n * t)) : ℝ) : ℂ) := by
  set ρ := zhukovskyRadius n with hρ_def
  have hρ0 : ρ ≠ 0 := (zhukovskyRadius_pos n).ne'
  set A : ℝ := -(zhukovskyFocal n * ρ * t / 2) with hA
  set A' : ℝ := -(zhukovskyFocal n * t / (2 * ρ)) with hA'
  set cf : ℕ × ℕ → ℂ := fun p => cexp (-((t : ℂ) / 2)) *
    ((A ^ p.1 * A' ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) : ℝ) : ℂ) with hcf
  set md : ℕ × ℕ → ℤ := fun p => (p.1 : ℤ) - p.2 - j with hmd
  have hprod : Summable fun p : ℕ × ℕ => (|A| ^ p.1 / (p.1.factorial : ℝ)) *
      (|A'| ^ p.2 / (p.2.factorial : ℝ)) := by
    refine summable_mul_of_summable_norm (f := fun a : ℕ => |A| ^ a / (a.factorial : ℝ))
      (g := fun b : ℕ => |A'| ^ b / (b.factorial : ℝ)) ?_ ?_
    · simpa [Real.norm_eq_abs, abs_div, abs_pow] using Real.summable_pow_div_factorial |A|
    · simpa [Real.norm_eq_abs, abs_div, abs_pow] using Real.summable_pow_div_factorial |A'|
  have hcf_sum : Summable fun p => ‖cf p‖ := by
    refine (hprod.mul_left ‖cexp (-((t : ℂ) / 2))‖).congr fun p => ?_
    rw [hcf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (p.1.factorial : ℝ) * (p.2.factorial : ℝ))]
    ring
  have hexp_series : ∀ x : ℂ, cexp x = ∑' a : ℕ, x ^ a / (a.factorial : ℂ) := fun x => by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have hsx : ∀ x : ℂ, Summable fun a : ℕ => ‖x ^ a / (a.factorial : ℂ)‖ := fun x => by
    simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖x‖
  have hexpand : ∀ θ : ℝ,
      cexp (((-(j : ℤ) : ℤ) : ℂ) * I * θ) * cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) =
        ∑' p : ℕ × ℕ, cf p * cexp ((md p : ℂ) * I * θ) := by
    intro θ
    rw [exp_neg_zhukovskyLoop_circleExp, hexp_series ((A : ℂ) * cexp (θ * I)),
      hexp_series ((A' : ℂ) * cexp (-(θ * I))),
      tsum_mul_tsum_of_summable_norm (hsx _) (hsx _), ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    rw [hcf, hmd]
    simp only [mul_pow, ← Complex.exp_nat_mul]
    rw [show (((((p.1 : ℤ) - p.2 - j : ℤ)) : ℂ)) * I * θ =
        (((-(j : ℤ) : ℤ) : ℂ) * I * θ) + (p.1 * (θ * I)) + (p.2 * -(θ * I)) by push_cast; ring,
      Complex.exp_add, Complex.exp_add]
    push_cast
    ring
  have hint := integral_tsum_modes cf md hcf_sum
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hexpand θ), hint]
  -- only the diagonal `p = (b + j, b)` survives
  have hinj : Function.Injective fun b : ℕ => (b + j, b) := fun b₁ b₂ h => by
    simpa using congrArg Prod.snd h
  have hsupp : Function.support (fun p : ℕ × ℕ =>
      cf p * (if md p = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0)) ⊆
        Set.range fun b : ℕ => (b + j, b) := by
    intro p hp
    by_cases h : md p = 0
    · refine ⟨p.2, ?_⟩
      have h' : (p.1 : ℤ) = p.2 + j := by rw [hmd] at h; simp only at h; linarith
      have h'' : p.1 = p.2 + j := by exact_mod_cast h'
      ext <;> simp [h'']
    · exact absurd (by simp [h]) hp
  rw [← hinj.tsum_eq hsupp]
  have hdiag : ∀ b : ℕ, md (b + j, b) = 0 := fun b => by simp [hmd]
  simp only [hdiag, if_true]
  have hterm : ∀ b : ℕ, cf (b + j, b) * ((2 * Real.pi : ℝ) : ℂ) =
      ((2 * Real.pi * (Real.exp (-(t / 2)) * ((-ρ) ^ j * ((zhukovskyFocal n * t / 2) ^ (j + 2 * b) /
        ((b.factorial : ℝ) * ((j + b).factorial : ℝ))))) : ℝ) : ℂ) := by
    intro b
    rw [hcf]
    simp only
    have hAeq : A = -ρ * (zhukovskyFocal n * t / 2) := by rw [hA]; ring
    have hA'eq : A' = -(zhukovskyFocal n * t / 2) / ρ := by rw [hA']; field_simp
    rw [hAeq, hA'eq, bessel_coeff_identity hρ0, add_comm b j]
    push_cast
    ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  congr 1
  rw [besselI]
  ring


/-- Mode integral of a geometric Laurent tail:
`∫ e^{-ikθ} q e^{isθ} / (1 - q e^{isθ}) dθ = ∑_i q^{i+1} · 2π [s(i+1) = k]`. -/
theorem integral_mode_mul_geom {q : ℂ} (hq : ‖q‖ < 1) (s k : ℤ) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), cexp (((-k : ℤ) : ℂ) * I * θ) *
        (q * cexp ((s : ℂ) * I * θ) / (1 - q * cexp ((s : ℂ) * I * θ))) =
      ∑' i : ℕ, q ^ (i + 1) *
        (if s * (i + 1) - k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
  have hnorm : ∀ θ : ℝ, ‖q * cexp ((s : ℂ) * I * θ)‖ = ‖q‖ := by
    intro θ
    rw [norm_mul, Complex.norm_exp]
    simp
  have hexpand : ∀ θ : ℝ, cexp (((-k : ℤ) : ℂ) * I * θ) *
      (q * cexp ((s : ℂ) * I * θ) / (1 - q * cexp ((s : ℂ) * I * θ))) =
        ∑' i : ℕ, q ^ (i + 1) * cexp ((((s * (i + 1) - k : ℤ)) : ℂ) * I * θ) := by
    intro θ
    have hg := hasSum_geometric_of_norm_lt_one (hnorm θ ▸ hq)
    rw [div_eq_mul_inv, ← hg.tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [mul_pow, ← Complex.exp_nat_mul,
      show ((((s * (i + 1) - k : ℤ)) : ℂ)) * I * θ =
        (((-k : ℤ) : ℂ) * I * θ) + ((s : ℂ) * I * θ) + (i * ((s : ℂ) * I * θ)) by push_cast; ring,
      Complex.exp_add, Complex.exp_add, pow_succ]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hexpand θ),
    integral_tsum_modes (fun i : ℕ => q ^ (i + 1)) (fun i : ℕ => s * (i + 1) - k)]
  refine ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖).congr fun i => ?_
  rw [norm_pow, pow_succ]
  ring

namespace ReflectedWindow

variable {W : ReflectedWindow} {n : ℕ}

/-- Logarithmic-derivative symbol of one pair factor on `S¹`:
`(cρ/2)(u - ρ^{-2} ū) / (J_n(u) - d)`. -/
def pairLogDerivSymbol (n : ℕ) (d : ℂ) (θ : ℝ) : ℂ :=
  ((zhukovskyFocal n * zhukovskyRadius n / 2 : ℝ) : ℂ) *
      (cexp (θ * I) - ((zhukovskyRadius n : ℂ)⁻¹) ^ 2 * cexp (-(θ * I))) /
    (zhukovskyLoop n (HTGeometry.circleExp θ) - d)

/-- **Per-pair cepstral coefficient.** For a corridor pair `d = z - w` and `k ≥ 1`,
the `k`-th Fourier coefficient of `(cρ/2)(u - ρ^{-2}ū)/(J_n(u) - d)` is `-(-ρ v_d)^k`. -/
theorem InCorridor.integral_mode_pairLogDerivSymbol {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * pairLogDerivSymbol n (z - w) θ =
      -((2 * Real.pi : ℝ) : ℂ) * (-(zhukovskyRadius n : ℂ) * pairInnerRoot n (z - w)) ^ k := by
  set ρ : ℂ := (zhukovskyRadius n : ℂ) with hρ
  set v := pairInnerRoot n (z - w) with hv
  have hρ0 : ρ ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
  have hnormρ : ‖ρ‖ = zhukovskyRadius n := by
    rw [hρ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zhukovskyRadius_pos n)]
  set a : ℂ := -ρ * v with ha
  set β : ℂ := -v / ρ with hβ
  have hb := hcorr.radius_mul_norm_le hη hη2 hz hw
  have han : ‖a‖ < 1 := by
    rw [ha, norm_mul, norm_neg, hnormρ]; linarith
  have hβn : ‖β‖ < 1 := by
    have hv1 := hcorr.norm_lt_one hη.le hz hw
    have hρ1 := one_lt_zhukovskyRadius n
    rw [hβ, norm_div, norm_neg, hnormρ, div_lt_one (zhukovskyRadius_pos n)]
    linarith
  have hc0 : (zhukovskyFocal n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyFocal_pos n).ne'
  have hv0 : v ≠ 0 := zhukovskyInnerRoot_ne_zero (zhukovskyFocal_pos n).ne' _
  -- pointwise partial fractions on the circle
  have hsplit : ∀ θ : ℝ, pairLogDerivSymbol n (z - w) θ =
      -(a * cexp (((1 : ℤ) : ℂ) * I * θ) / (1 - a * cexp (((1 : ℤ) : ℂ) * I * θ))) +
        β * cexp (((-1 : ℤ) : ℂ) * I * θ) / (1 - β * cexp (((-1 : ℤ) : ℂ) * I * θ)) := by
    intro θ
    set e := cexp (θ * I) with he
    set e' := cexp (-(θ * I)) with he'
    have hJ : zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w) =
        (zhukovskyFocal n : ℂ) / (2 * v) * (1 + ρ * v * e) * (1 + v * e' / ρ) := by
      have h := zhukovskyLoop_sub_eq_inner n (z - w) (HTGeometry.circleExp θ)
      have hu : ((HTGeometry.circleExp θ : HTGeometry.UnitCircle) : ℂ) = e := rfl
      have hus : star e = e' := by
        rw [he, he', Complex.star_def, ← Complex.exp_conj]; simp
      rw [hu, hus] at h
      exact h
    have hden : 1 + ρ * v * e ≠ 0 :=
      hcorr.innerDen_ne_zero hη hη2 hz hw (by rw [he, Complex.norm_exp_ofReal_mul_I])
    have hnum : 1 + v * e' / ρ ≠ 0 :=
      hcorr.innerNum_ne_zero hη.le hz hw (by
        rw [he', show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I])
    have h3 : cexp (((1 : ℤ) : ℂ) * I * θ) = e := by rw [he]; push_cast; ring_nf
    have h4 : cexp (((-1 : ℤ) : ℂ) * I * θ) = e' := by rw [he']; push_cast; ring_nf
    have hden' : 1 - a * e ≠ 0 := by
      rw [show 1 - a * e = 1 + ρ * v * e by rw [ha]; ring]; exact hden
    have hnum' : 1 - β * e' ≠ 0 := by
      rw [show 1 - β * e' = 1 + v * e' / ρ by rw [hβ]; ring]; exact hnum
    have hL : pairLogDerivSymbol n (z - w) θ = (β * e' - a * e) / ((1 - a * e) * (1 - β * e')) := by
      unfold pairLogDerivSymbol
      rw [hJ, show (1 + ρ * v * e) = 1 - a * e by rw [ha]; ring,
        show (1 + v * e' / ρ) = 1 - β * e' by rw [hβ]; ring,
        div_eq_div_iff (mul_ne_zero (mul_ne_zero (div_ne_zero hc0 (mul_ne_zero two_ne_zero hv0))
          hden') hnum') (mul_ne_zero hden' hnum')]
      rw [ha, hβ]
      push_cast
      rw [← hρ, ← he, ← he']
      field_simp
      ring
    rw [hL, h3, h4, ← neg_div, div_add_div _ _ hden' hnum']
    congr 1
    ring
  have hcont : ∀ (q : ℂ) (s : ℤ), ‖q‖ < 1 → Continuous fun θ : ℝ =>
      cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
        (q * cexp ((s : ℂ) * I * θ) / (1 - q * cexp ((s : ℂ) * I * θ))) := by
    intro q s hq
    refine Continuous.mul (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) fun θ => ?_)
    refine sub_ne_zero.mpr fun h => ?_
    have h' := congrArg norm h
    rw [norm_one, norm_mul, Complex.norm_exp] at h'
    simp at h'
    linarith
  have hintegrable : ∀ (q : ℂ) (s : ℤ), ‖q‖ < 1 → IntegrableOn (fun θ : ℝ =>
      cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
        (q * cexp ((s : ℂ) * I * θ) / (1 - q * cexp ((s : ℂ) * I * θ)))) (Ioc 0 (2 * Real.pi)) :=
    fun q s hq => ((hcont q s hq).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpoint : ∀ θ : ℝ, cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * pairLogDerivSymbol n (z - w) θ =
      -(cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
          (a * cexp (((1 : ℤ) : ℂ) * I * θ) / (1 - a * cexp (((1 : ℤ) : ℂ) * I * θ)))) +
        cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
          (β * cexp (((-1 : ℤ) : ℂ) * I * θ) / (1 - β * cexp (((-1 : ℤ) : ℂ) * I * θ))) := by
    intro θ
    rw [hsplit θ]
    ring
  have hneg : IntegrableOn (fun θ : ℝ => -(cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
      (a * cexp (((1 : ℤ) : ℂ) * I * θ) / (1 - a * cexp (((1 : ℤ) : ℂ) * I * θ)))))
      (Ioc 0 (2 * Real.pi)) := (hintegrable a 1 han).neg
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpoint θ),
    integral_add hneg (hintegrable β (-1) hβn), integral_neg,
    integral_mode_mul_geom han, integral_mode_mul_geom hβn]
  have h1 : ∑' i : ℕ, a ^ (i + 1) *
      (if (1 : ℤ) * (i + 1) - k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) =
      a ^ k * ((2 * Real.pi : ℝ) : ℂ) := by
    rw [tsum_eq_single (k - 1)]
    · rw [if_pos (by push_cast [Nat.cast_sub hk]; ring), Nat.sub_add_cancel hk]
    · intro i hi
      rw [if_neg, mul_zero]
      intro h
      apply hi
      omega
  have h2 : ∑' i : ℕ, β ^ (i + 1) *
      (if (-1 : ℤ) * (i + 1) - k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) = 0 := by
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [if_neg, mul_zero]
    omega
  rw [h1, h2, ha]
  ring


/-- Corridor pair differences never meet the Zhukovsky loop. -/
theorem InCorridor.zhukovskyLoop_sub_ne_zero {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z)
    (u : HTGeometry.UnitCircle) : zhukovskyLoop n u - (z - w) ≠ 0 := by
  have hu1 : ‖(u : ℂ)‖ ≤ 1 := (HTGeometry.norm_coe_unitCircle u).le
  have hus1 : ‖star (u : ℂ)‖ ≤ 1 := by rw [norm_star]; exact hu1
  have h : zhukovskyLoop n u - (z - w) =
      (zhukovskyFocal n : ℂ) / (2 * pairInnerRoot n (z - w)) * innerDen n (z - w) u *
        innerNum n (z - w) (star (u : ℂ)) := zhukovskyLoop_sub_eq_inner n (z - w) u
  rw [h]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (zhukovskyFocal_pos n).ne')
    (mul_ne_zero two_ne_zero (zhukovskyInnerRoot_ne_zero (zhukovskyFocal_pos n).ne' _)))
    (hcorr.innerDen_ne_zero hη hη2 hz hw hu1)) (hcorr.innerNum_ne_zero hη.le hz hw hus1)

end ReflectedWindow

/-- The Zhukovsky loop stays right of its vertex `1/2 - a_n`. -/
theorem re_zhukovskyLoop_circleExp_ge (n : ℕ) (θ : ℝ) :
    1 / 2 - zhukovskyMajorAxis n ≤ (zhukovskyLoop n (HTGeometry.circleExp θ)).re := by
  rw [zhukovskyLoop_circleExp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  norm_num
  nlinarith [Real.neg_one_le_cos θ, zhukovskyMajorAxis_pos n]

namespace ReflectedWindow

variable {W : ReflectedWindow} {n : ℕ}

/-- Mode weight `e^{-ikθ} (cρ/2)(e^{iθ} - ρ^{-2} e^{-iθ})` extracting the `k`-th cepstral
coefficient from the pair resolvent on the Zhukovsky loop. -/
def cepstralModeWeight (n k : ℕ) (θ : ℝ) : ℂ :=
  cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) *
    (((zhukovskyFocal n * zhukovskyRadius n / 2 : ℝ) : ℂ) *
      (cexp (θ * I) - ((zhukovskyRadius n : ℂ)⁻¹) ^ 2 * cexp (-(θ * I))))

theorem continuous_cepstralModeWeight (n k : ℕ) : Continuous (cepstralModeWeight n k) := by
  unfold cepstralModeWeight
  fun_prop

/-- **Resolvent form of the cepstrum.** On a corridor window, for `k ≥ 1`,
`∫₀^{2π} e^{-ikθ}(cρ/2)(e^{iθ} - ρ^{-2}e^{-iθ}) R(J_n(e^{iθ})) dθ = -2π S_k`, where `R` is the
pair resolvent. -/
theorem InCorridor.integral_cepstralModeWeight_mul_pairResolvent {η : ℝ} (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        cepstralModeWeight n k θ * W.pairResolvent (zhukovskyLoop n (HTGeometry.circleExp θ)) =
      -((2 * Real.pi : ℝ) : ℂ) * W.cepstralCoeff n k := by
  have hJcont : Continuous fun θ : ℝ => zhukovskyLoop n (HTGeometry.circleExp θ) :=
    (zhukovskyLoop n).continuous.comp HTGeometry.continuous_circleExp
  have hpt : ∀ θ : ℝ, cepstralModeWeight n k θ *
      W.pairResolvent (zhukovskyLoop n (HTGeometry.circleExp θ)) =
        ∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) *
          (cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * pairLogDerivSymbol n (z - w) θ) := by
    intro θ
    unfold pairResolvent pairLogDerivSymbol cepstralModeWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  have hint : ∀ z ∈ W.Z, ∀ w ∈ W.Z, IntegrableOn (fun θ : ℝ =>
      ((W.mult z * W.mult w : ℕ) : ℂ) *
        (cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * pairLogDerivSymbol n (z - w) θ))
      (Ioc 0 (2 * Real.pi)) := by
    intro z hz w hw
    have hsym : Continuous (pairLogDerivSymbol n (z - w)) := by
      unfold pairLogDerivSymbol
      exact Continuous.div (by fun_prop) (hJcont.sub continuous_const)
        fun θ => hcorr.zhukovskyLoop_sub_ne_zero hη hη2 hz hw _
    have hcont : Continuous fun θ : ℝ => ((W.mult z * W.mult w : ℕ) : ℂ) *
        (cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * pairLogDerivSymbol n (z - w) θ) :=
      continuous_const.mul ((by fun_prop : Continuous fun θ : ℝ =>
        cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ)).mul hsym)
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpt θ),
    integral_finsetSum _ fun z hz => integrable_finsetSum _ fun w hw => hint z hz w hw]
  unfold cepstralCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [integral_finsetSum _ fun w hw => hint z hz w hw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [integral_const_mul, hcorr.integral_mode_pairLogDerivSymbol hη hη2 hz hw hk]
  ring

end ReflectedWindow

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
