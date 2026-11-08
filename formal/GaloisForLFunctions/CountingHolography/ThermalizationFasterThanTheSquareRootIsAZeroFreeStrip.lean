import GaloisForLFunctions.CountingHolography.TheHorocycleRateIsTheSquareRootFareyLaw
import GaloisForLFunctions.RHTower.InvZetaRHSubpolynomial
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Thermalization faster than the square root is a zero-free strip

**The second physical question** of the modular horizon: does a long closed horocycle thermalize faster
than `y^{1/2}` by any power? Read as counts: does every smoothed Farey count reach its limit faster than
the trivial rate? The answer is exactly the zero-free strip (`zeroFreeStrip_iff_fareyCount_rate`): for
`0 < δ ≤ 1/4`,

  every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ`
  ⟺ every Farey count reaches its limit at rate `y^{1/2 + δ - ε}` for every `ε > 0`.

At `δ = 1/4` this is Zagier's theorem (`riemannHypothesis_iff_fareyCount_rate`). So a gain of any power
over the trivial thermalization is quasi-RH, and the gain `y^δ` is the width `2δ` of the strip.

**Proof.** Rate `y^α` forces `Re ρ ≤ 2 - 2α` (`re_le_of_fareyCount_rate`). Conversely a zero-free
half-plane `Re s > σ₀` makes `1/ζ` polynomially bounded on every strip `Re s ≥ σ₀ + δ`: on discs about
`3 + it` that avoid the pole and stay right of `σ₀`, `ζ` has a holomorphic logarithm, and the two-radius
three-circles bound with the polynomial growth of `ζ` on the large disc and its size on the small disc in
`Re s > 2` bounds `ζ` below by `exp(-B (K log t)^θ)` with `θ < 1`; bounded heights are a compact box. The
Mellin contour shift of the horocycle mean (`BlackHoleRingdown.norm_horocycleMean_sub_le_of_zeroFree`)
then gives the rate `y^{1 - σ₀/2 - ε}`.

**The analytic tool.** Zero-freeness of a half-plane is exactly a polynomial lower bound for `ζ` on its
vertical strips (`zeroFree_iff_zeta_lower_bound`); small heights are zero-free by
`RHTower.riemannZeta_ne_zero_of_im_sq_le`.
-/

open Complex Metric Set Filter
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open HTGeometry BlackHoleRingdown
open _root_.RHTower _root_.RHTower.Sieve

/-! ### The three-circles lower bound right of a zero-free half-plane -/


private theorem one_le_mul_of_one_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ x * y := by
  simpa only [one_mul] using
    mul_le_mul hx hy zero_le_one (le_trans zero_le_one hx)

private theorem rpow_one_sub_le_self {B w : ℝ} (hB : 1 ≤ B) (hw : 0 ≤ w) :
    B ^ (1 - w) ≤ B := by
  calc
    B ^ (1 - w) ≤ B ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by linarith)
    _ = B := Real.rpow_one B

private theorem nonneg_two_mul_add_one_mul_div {x r q : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hq : 0 ≤ q) :
    0 ≤ 2 * (x + 1) * r / q := by
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hr) hq

private theorem rpow_le_rpow_two_stage {X Y w θ : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) (hw : 0 ≤ w) (hY : 1 ≤ Y) (hwθ : w ≤ θ) :
    X ^ w ≤ Y ^ θ :=
  le_trans (Real.rpow_le_rpow hX hXY hw)
    (Real.rpow_le_rpow_of_exponent_le hY hwθ)

private theorem mul_le_mul_two_stage {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    a * c ≤ b * d :=
  mul_le_mul hab hcd hc hb

private theorem rewrite_two_radius_lower {fc fs rawB rawX B X w : ℝ}
    (hB : rawB = B) (hX : rawX = X)
    (h : fc * Real.exp (-(rawB ^ (1 - w) * rawX ^ w)) ≤ fs) :
    fc * Real.exp (-(B ^ (1 - w) * X ^ w)) ≤ fs := by
  simpa only [hB, hX] using h

/-- Polynomial zeta growth on the large discs of the three-circles argument right of `σ₀`. -/
private theorem exists_bound_riemannZeta_disc_high {σ₀ δ : ℝ} (hσ0 : 0 ≤ σ₀) (hδ : 0 < δ) :
    ∃ E : ℝ, 3 ≤ E ∧ ∀ t : ℝ, 6 ≤ |t| → ∀ z : ℂ,
      ‖z - ((3 : ℂ) + (t : ℝ) * I)‖ ≤ 3 - (σ₀ + δ / 4) →
        ‖riemannZeta z‖ ≤ E * (2 + |t|) := by
  let E : ℝ := 3 * (1 + 4 / δ)
  have hfrac : 0 ≤ 4 / δ := by positivity
  have hE3 : 3 ≤ E := by dsimp only [E]; nlinarith
  refine ⟨E, hE3, fun t ht z hz => ?_⟩
  let c : ℂ := (3 : ℂ) + (t : ℝ) * I
  have hcre : c.re = 3 := by dsimp only [c]; simp
  have hcim : c.im = t := by dsimp only [c]; simp
  have hreabs := Complex.abs_re_le_norm (z - c)
  rw [Complex.sub_re, hcre] at hreabs
  have hrelo : σ₀ + δ / 4 ≤ z.re := by
    have h := (abs_le.mp (hreabs.trans (by simpa only [c] using hz))).1
    linarith
  have hzre : 0 < z.re := by linarith
  have hcNorm := Complex.norm_le_abs_re_add_abs_im c
  rw [hcre, hcim, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hcNorm
  have hnormz : ‖z‖ ≤ 3 * (2 + |t|) := by
    have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - c) c
    have hzc : ‖z - c‖ ≤ 3 - (σ₀ + δ / 4) := by simpa only [c] using hz
    linarith [abs_nonneg t]
  have htC : |t| ≤ ‖c - 1‖ := by
    have him := Complex.abs_im_le_norm (c - 1)
    rw [Complex.sub_im, hcim] at him
    simpa using him
  have hc1 : ‖c - 1‖ ≤ ‖c - z‖ + ‖z - 1‖ := by
    have hsplit : c - 1 = (c - z) + (z - 1) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hcz : ‖c - z‖ = ‖z - c‖ := norm_sub_rev c z
  rw [hcz] at hc1
  have hzc : ‖z - c‖ ≤ 3 - (σ₀ + δ / 4) := by simpa only [c] using hz
  have hden1 : 1 ≤ ‖z - 1‖ := by linarith
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hden1
  have hreInv : 1 / z.re ≤ 4 / δ := by
    apply (div_le_div_iff₀ hzre hδ).2
    nlinarith
  have hfirst : ‖z‖ / ‖z - 1‖ ≤ ‖z‖ := div_le_self (norm_nonneg z) hden1
  have hsecond : ‖z‖ / z.re ≤ ‖z‖ * (4 / δ) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hreInv) (norm_nonneg z)
  have hzeta := Sieve.norm_riemannZeta_strip_le hzre hz1
  calc
    ‖riemannZeta z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re := hzeta
    _ ≤ ‖z‖ + ‖z‖ * (4 / δ) := add_le_add hfirst hsecond
    _ = ‖z‖ * (1 + 4 / δ) := by ring
    _ ≤ (3 * (2 + |t|)) * (1 + 4 / δ) :=
      mul_le_mul_of_nonneg_right hnormz (by positivity)
    _ = E * (2 + |t|) := by dsimp only [E]; ring

/-- The three-circles lower bound for `ζ` right of a zero-free half-plane `Re s > σ₀`. -/
private theorem exists_three_circles_zeta_lower_bound_of_zeroFree {σ₀ δ : ℝ} (hσ0 : 0 ≤ σ₀)
    (hδ : 0 < δ) (hσδ : σ₀ + δ < 1)
    (hZ : ∀ z : ℂ, σ₀ < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    ∃ B K θ : ℝ, 0 < B ∧ 0 < K ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ s : ℂ,
      σ₀ + δ ≤ s.re → 6 ≤ |s.im| →
        (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log (2 + |s.im|))) ^ θ))
          ≤ ‖riemannZeta s‖ := by
  set a : ℝ := 3 with ha
  set r₃ : ℝ := a - (σ₀ + δ / 2) with hr₃
  set R : ℝ := a - (σ₀ + δ / 4) with hR
  have hr₃big : (2 : ℝ) < r₃ := by rw [hr₃, ha]; linarith
  have hRbig : r₃ < R := by rw [hr₃, hR]; linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hR3 : R < 3 := by rw [hR, ha]; linarith
  have hr₁ρ : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  have hρR : (1 : ℝ) / 2 ≤ R := by linarith
  have hr₁r₃ : (1 : ℝ) / 4 < r₃ := by linarith
  obtain ⟨E, hE3, hdisc0⟩ := exists_bound_riemannZeta_disc_high hσ0 hδ
  have hE0 : 0 < E := lt_of_lt_of_le (by norm_num) hE3
  have h4E : (1 : ℝ) ≤ 4 * E := by nlinarith
  set B : ℝ :=
    2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) * (1 / 4) / (1 / 2 - 1 / 4) with hB
  have hlog12 : 0 ≤ Real.log (3 / (1 / 4 : ℝ)) := Real.log_nonneg (by norm_num)
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    have hsimp :
        2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) * (1 / 4) / (1 / 2 - 1 / 4)
          = 2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) := by ring
    rw [hsimp]
    linarith
  have hB0 : 0 < B := by linarith
  set K : ℝ := 8 * r₃ / δ * (Real.log (4 * E) + 2) with hK
  have hlogE : 0 ≤ Real.log (4 * E) := Real.log_nonneg h4E
  have hfac : (8 : ℝ) ≤ 8 * r₃ / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; nlinarith
  set θ : ℝ :=
    (Real.log (a - σ₀ - δ) - Real.log (1 / 4)) /
      (Real.log r₃ - Real.log (1 / 4)) with hθ
  have hgap : (1 : ℝ) / 4 < a - σ₀ - δ := by rw [ha]; linarith
  have hgap2 : a - σ₀ - δ < r₃ := by rw [hr₃]; linarith
  have hden : 0 < Real.log r₃ - Real.log (1 / 4) := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) hr₁r₃
    linarith
  have hnum : 0 ≤ Real.log (a - σ₀ - δ) - Real.log (1 / 4) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hgap.le
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg hnum hden.le
  clear_value θ K B R r₃ a
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < a - σ₀ - δ) hgap2
    linarith
  refine ⟨B, K, θ, hB0, hK0, hθ0, hθ1, fun s hs ht => ?_⟩
  set t : ℝ := s.im with htdef
  have hbase : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hlogbase : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg hbase
  have hone : (1 : ℝ) ≤ 1 + Real.log (2 + |t|) := by linarith
  have hKpos : 0 ≤ K * (1 + Real.log (2 + |t|)) :=
    mul_nonneg hK0.le (by linarith)
  have hexpnn : 0 ≤ B * (K * (1 + Real.log (2 + |t|))) ^ θ :=
    mul_nonneg hB0.le (Real.rpow_nonneg hKpos _)
  rcases le_or_gt s.re (a - 1 / 4) with hleft | hright
  · set c : ℂ := (a : ℂ) + (t : ℝ) * I with hc
    have hcre : c.re = a := by rw [hc]; simp
    have hcim : c.im = t := by rw [hc]; simp
    have hsc : s - c = (((s.re - a : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hc, htdef]
    have hscnorm : ‖s - c‖ = a - s.re := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hz1 : (1 : ℝ) / 4 ≤ ‖s - c‖ := by rw [hscnorm]; linarith
    have hz3 : ‖s - c‖ ≤ r₃ := by rw [hscnorm, hr₃]; linarith
    have hballre : ∀ z ∈ ball c R, σ₀ < z.re := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      have hAR : a - R = σ₀ + δ / 4 := by rw [hR]; ring
      linarith
    have hpole : ∀ z ∈ ball c R, z ≠ 1 := by
      intro z hz hzone
      subst z
      have hd : ‖(1 : ℂ) - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      have him := Complex.abs_im_le_norm ((1 : ℂ) - c)
      rw [Complex.sub_im, hcim] at him
      simp only [Complex.one_im, zero_sub, abs_neg] at him
      have ht' : 6 ≤ |t| := by simpa [t] using ht
      linarith
    have hne : ∀ z ∈ ball c R, riemannZeta z ≠ 0 := fun z hz => hZ z (hballre z hz) (hpole z hz)
    have hf : DifferentiableOn ℂ riemannZeta (ball c R) := by
      intro z hz
      exact (differentiableAt_riemannZeta (hpole z hz)).differentiableWithinAt
    have hMi : ∀ z ∈ ball c (1 / 2), ‖riemannZeta z‖ ≤ 3 := by
      intro z hz
      have hd : ‖z - c‖ < 1 / 2 := by rwa [mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      have hzeta := Sieve.norm_riemannZeta_le (s := z) (by rw [ha] at h2; linarith)
      have hinv : 1 / (z.re - 1) ≤ 1 := by
        rw [div_le_one (by rw [ha] at h2; linarith)]
        rw [ha] at h2
        linarith
      linarith
    have hmc : (1 : ℝ) / 4 ≤ ‖riemannZeta c‖ := by
      apply norm_riemannZeta_ge_of_two_le_re
      rw [hcre, ha]
      norm_num
    have hM : ∀ z ∈ ball c R, ‖riemannZeta z‖ ≤ E * (2 + |t|) := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      exact hdisc0 t (by simpa [t] using ht) z (by
        calc
          ‖z - ((3 : ℂ) + (t : ℝ) * I)‖ = ‖z - c‖ := by
            rw [show (3 : ℂ) = (((3 : ℝ) : ℂ)) by norm_num, hc, ha]
          _ ≤ R := hd.le
          _ = 3 - (σ₀ + δ / 4) := by rw [hR, ha])
    have hmain := norm_lower_bound_of_two_radii
      (by norm_num : (0 : ℝ) < 1 / 4) hr₁ρ hρR hr₁r₃ hRbig hf hne hMi
      (by norm_num : (0 : ℝ) < 1 / 4) hmc hM
      (by norm_num : (0 : ℝ) < 1 / 4) hmc hz1 hz3
    set w : ℝ :=
      (Real.log ‖s - c‖ - Real.log (1 / 4)) /
        (Real.log r₃ - Real.log (1 / 4)) with hw
    have hw0 : 0 ≤ w := by
      rw [hw]
      have hnum' := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hz1
      exact div_nonneg (by linarith) hden.le
    have hwθ : w ≤ θ := by
      rw [hw, hθ, div_le_div_iff_of_pos_right hden]
      have hle : ‖s - c‖ ≤ a - σ₀ - δ := by rw [hscnorm]; linarith
      have h2 := Real.log_le_log (by linarith : (0 : ℝ) < ‖s - c‖) hle
      linarith
    have hMm : E * (2 + |t|) / (1 / 4) = 4 * E * (2 + |t|) := by ring
    have hlogsplit : Real.log (4 * E * (2 + |t|)) =
        Real.log (4 * E) + Real.log (2 + |t|) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have hr₃0 : 0 < r₃ := by linarith
    have hRr : R - r₃ = δ / 4 := by rw [hR, hr₃]; ring
    have hRr0 : 0 < R - r₃ := by rw [hRr]; linarith
    have hfac0 : 0 < 8 * r₃ / δ := by positivity
    let X : ℝ :=
      2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ / (R - r₃)
    let Y : ℝ := K * (1 + Real.log (2 + |t|))
    have houter : X ≤ Y := by
      dsimp only [X, Y]
      rw [hMm, hlogsplit, hRr, hK]
      have hkey : Real.log (4 * E) + Real.log (2 + |t|) + 1
          ≤ (Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|)) := by
        have hexpand :
            (Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|)) =
              Real.log (4 * E) + Real.log (2 + |t|) + 1 +
                (Real.log (4 * E) * Real.log (2 + |t|) +
                  Real.log (2 + |t|) + 1) := by ring
        rw [hexpand]
        have hprodlog : 0 ≤ Real.log (4 * E) * Real.log (2 + |t|) :=
          mul_nonneg hlogE hlogbase
        exact le_add_of_nonneg_right (by linarith only [hprodlog, hlogbase])
      calc
        2 * (Real.log (4 * E) + Real.log (2 + |t|) + 1) * r₃ / (δ / 4)
            = 8 * r₃ / δ *
                (Real.log (4 * E) + Real.log (2 + |t|) + 1) := by
                  field_simp
                  ring
        _ ≤ 8 * r₃ / δ *
              ((Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|))) :=
                mul_le_mul_of_nonneg_left hkey hfac0.le
        _ = 8 * r₃ / δ * (Real.log (4 * E) + 2) *
              (1 + Real.log (2 + |t|)) :=
                (mul_assoc _ _ _).symm
    have houter1 : 1 ≤ Y := by
      dsimp only [Y]
      calc
        (1 : ℝ) ≤ K := hK1
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (1 + Real.log (2 + |t|)) :=
          mul_le_mul_of_nonneg_left hone hK0.le
    have hlogM : 0 ≤ Real.log (E * (2 + |t|) / (1 / 4)) := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) ≤ 4 * E * (2 + |t|) :=
          one_le_mul_of_one_le h4E hbase
        _ = E * (2 + |t|) / (1 / 4) := hMm.symm
    have hbase0 : 0 ≤ X := by
      dsimp only [X]
      exact nonneg_two_mul_add_one_mul_div hlogM hr₃0.le hRr0.le
    have hpow1 : B ^ (1 - w) ≤ B := rpow_one_sub_le_self hB1 hw0
    have hpow3 : X ^ w ≤ Y ^ θ :=
      rpow_le_rpow_two_stage hbase0 houter hw0 houter1 hwθ
    have hXpow : 0 ≤ X ^ w := Real.rpow_nonneg hbase0 w
    have hprod : B ^ (1 - w) * X ^ w ≤ B * Y ^ θ :=
      mul_le_mul_two_stage hpow1 hpow3 hXpow hB0.le
    have hmainNamed :
        ‖riemannZeta c‖ * Real.exp (-(B ^ (1 - w) * X ^ w)) ≤ ‖riemannZeta s‖ :=
      rewrite_two_radius_lower (B := B) (X := X) hB.symm (by rfl) hmain
    change (1 : ℝ) / 4 * Real.exp (-(B * Y ^ θ)) ≤ ‖riemannZeta s‖
    calc
      (1 : ℝ) / 4 * Real.exp (-(B * Y ^ θ))
          ≤ 1 / 4 * Real.exp (-(B ^ (1 - w) * X ^ w)) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith only [hprod])) (by norm_num)
      _ ≤ ‖riemannZeta c‖ * Real.exp (-(B ^ (1 - w) * X ^ w)) :=
            mul_le_mul_of_nonneg_right hmc (Real.exp_pos _).le
      _ ≤ ‖riemannZeta s‖ := hmainNamed
  · have hge : 2 ≤ s.re := by rw [ha] at hright; linarith
    have hval := norm_riemannZeta_ge_of_two_le_re hge
    calc
      (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log (2 + |t|))) ^ θ))
          ≤ 1 / 4 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Real.exp_le_one_iff.mpr (by linarith)
      _ = 1 / 4 := by ring
      _ ≤ ‖riemannZeta s‖ := hval


/-! ### Polynomial growth of `1/ζ` right of a zero-free half-plane -/

/-- Right of a zero-free half-plane `Re s > σ₀`, `1/ζ` grows at most polynomially on every vertical
strip `σ₀ + δ ≤ Re s ≤ d`, `|Im s| ≥ 2`. -/
private theorem invZeta_poly_of_zeroFree {σ₀ : ℝ} (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ < 1)
    (hZ : ∀ z : ℂ, σ₀ < z.re → z ≠ 1 → riemannZeta z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (d : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, σ₀ + δ ≤ z.re → z.re ≤ d → 2 ≤ |z.im| →
      ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
  -- a smaller offset inside the admissible range
  set δ' : ℝ := min δ ((1 - σ₀) / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hσδ : σ₀ + δ' < 1 := by have := min_le_right δ ((1 - σ₀) / 2); linarith
  obtain ⟨B, K, θ, hB0, hK0, hθ0, hθ1, hlow⟩ :=
    exists_three_circles_zeta_lower_bound_of_zeroFree hσ0 hδ'0 hσδ hZ
  set N : ℕ := ⌈B * K⌉₊ with hN
  -- bounded height: a compact box on which `ζ` is continuous and nonvanishing
  set box : Set ℂ := Icc (σ₀ + δ) (max d (σ₀ + δ)) ×ℂ Icc (-6 : ℝ) 6
  have hbox : IsCompact box := isCompact_reProdIm_Icc _ _ _ _
  set box' : Set ℂ := box ∩ {z | 2 ≤ |z.im|}
  have hbox' : IsCompact box' :=
    hbox.inter_right (isClosed_le continuous_const (continuous_abs.comp continuous_im))
  have hne1 : ∀ z ∈ box', z ≠ 1 := by
    intro z hz h1
    have := hz.2
    simp only [Set.mem_setOf_eq, h1, one_im, abs_zero] at this
    linarith
  have hcont : ContinuousOn (fun z => (riemannZeta z)⁻¹) box' := by
    intro z hz
    have hz0 : riemannZeta z ≠ 0 := hZ z (by have := hz.1.1.1; linarith) (hne1 z hz)
    exact ((differentiableAt_riemannZeta (hne1 z hz)).continuousAt.inv₀ hz0).continuousWithinAt
  obtain ⟨M, hM⟩ := hbox'.exists_bound_of_continuousOn hcont
  refine ⟨max (max M 0) (4 * Real.exp (B + B * K) * 2 ^ N), N, by positivity,
    fun z hz1 hz2 hzt => ?_⟩
  have hpow1 : (1 : ℝ) ≤ |z.im| ^ N := one_le_pow₀ (by linarith)
  rcases le_or_gt |z.im| 6 with hsmall | hbig
  · have hmem : z ∈ box' := by
      refine ⟨⟨⟨hz1, le_trans hz2 (le_max_left _ _)⟩, ?_⟩, hzt⟩
      exact ⟨by linarith [neg_abs_le z.im], le_trans (le_abs_self _) hsmall⟩
    calc ‖(riemannZeta z)⁻¹‖ ≤ M := hM z hmem
      _ ≤ max M 0 := le_max_left _ _
      _ ≤ max (max M 0) (4 * Real.exp (B + B * K) * 2 ^ N) := le_max_left _ _
      _ = max (max M 0) (4 * Real.exp (B + B * K) * 2 ^ N) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow1 (by positivity)
  · have hlb := hlow z (by linarith) hbig.le
    set T : ℝ := 2 + |z.im| with hT
    set L : ℝ := K * (1 + Real.log T) with hL
    have hbase : (1 : ℝ) ≤ T := by linarith [abs_nonneg z.im]
    have hT0 : 0 < T := by linarith
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hbase
    have hL0 : 0 ≤ L := mul_nonneg hK0.le (by linarith)
    -- `L^θ ≤ 1 + L`
    have hLθ : L ^ θ ≤ 1 + L := by
      rcases le_or_gt L 1 with hL1 | hL1
      · have := Real.rpow_le_one hL0 hL1 hθ0
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le hL1.le hθ1.le
        rw [Real.rpow_one] at this
        linarith
    have hzeta0 : 0 < ‖riemannZeta z‖ := lt_of_lt_of_le (by positivity) hlb
    have hinv : ‖(riemannZeta z)⁻¹‖ ≤ 4 * Real.exp (B * L ^ θ) := by
      rw [norm_inv, inv_le_comm₀ hzeta0 (by positivity)]
      have : (4 * Real.exp (B * L ^ θ))⁻¹ = 1 / 4 * Real.exp (-(B * L ^ θ)) := by
        rw [Real.exp_neg]
        field_simp
      rw [this]
      exact hlb
    -- `exp(B L^θ) ≤ e^{B + BK} T^{BK} ≤ e^{B + BK} T^N`
    have hexp : Real.exp (B * L ^ θ) ≤ Real.exp (B + B * K) * T ^ N := by
      have h1 : B * L ^ θ ≤ (B + B * K) + (B * K) * Real.log T := by
        have := mul_le_mul_of_nonneg_left hLθ hB0.le
        rw [hL] at this
        nlinarith
      have h2 : Real.exp ((B + B * K) + (B * K) * Real.log T) = Real.exp (B + B * K) * T ^ (B * K) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hT0, mul_comm (Real.log T)]
      have h3 : T ^ (B * K) ≤ T ^ N := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil _)
      calc Real.exp (B * L ^ θ) ≤ Real.exp ((B + B * K) + (B * K) * Real.log T) := Real.exp_le_exp.mpr h1
        _ = Real.exp (B + B * K) * T ^ (B * K) := h2
        _ ≤ Real.exp (B + B * K) * T ^ N := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hTt : T ^ N ≤ 2 ^ N * |z.im| ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by rw [hT]; linarith) N
    calc ‖(riemannZeta z)⁻¹‖ ≤ 4 * Real.exp (B * L ^ θ) := hinv
      _ ≤ 4 * (Real.exp (B + B * K) * T ^ N) := by linarith
      _ ≤ 4 * (Real.exp (B + B * K) * (2 ^ N * |z.im| ^ N)) := by gcongr
      _ = 4 * Real.exp (B + B * K) * 2 ^ N * |z.im| ^ N := by ring
      _ ≤ max (max M 0) (4 * Real.exp (B + B * K) * 2 ^ N) * |z.im| ^ N :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Zero-free half-planes are polynomial lower bounds for `ζ`.** For `0 ≤ σ₀ < 1`, `ζ` has no zero
in `Re s > σ₀` iff on every strip `σ₀ + δ ≤ Re s ≤ d`, `|Im s| ≥ 2`, it is bounded below by an inverse
power of the height. -/
theorem zeroFree_iff_zeta_lower_bound {σ₀ : ℝ} (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ < 1) :
    (∀ z : ℂ, σ₀ < z.re → z ≠ 1 → riemannZeta z ≠ 0) ↔
      ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 < K ∧ ∀ z : ℂ, σ₀ + δ ≤ z.re → z.re ≤ d →
        2 ≤ |z.im| → 1 ≤ K * |z.im| ^ N * ‖riemannZeta z‖ := by
  constructor
  · intro hZ δ hδ d
    obtain ⟨K, N, hK, hb⟩ := invZeta_poly_of_zeroFree hσ0 hσ1 hZ hδ d
    refine ⟨K + 1, N, by linarith, fun z hz1 hz2 hzt => ?_⟩
    have hz1' : z ≠ 1 := fun h => by rw [h, one_im, abs_zero] at hzt; linarith
    have h0 : riemannZeta z ≠ 0 := hZ z (by linarith) hz1'
    have hn : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr h0
    have h1 := hb z hz1 hz2 hzt
    rw [norm_inv] at h1
    have hpow : 0 ≤ |z.im| ^ N := pow_nonneg (abs_nonneg _) N
    have h2 : 1 ≤ K * |z.im| ^ N * ‖riemannZeta z‖ := by
      rw [inv_le_iff_one_le_mul₀' hn] at h1
      linarith
    nlinarith [mul_nonneg hpow hn.le]
  · intro h z hz hz1 h0
    rcases le_or_gt 2 |z.im| with hzt | hzt
    · obtain ⟨K, N, -, hK⟩ := h (z.re - σ₀) (by linarith) z.re
      have := hK z (by linarith) le_rfl hzt
      rw [h0, norm_zero, mul_zero] at this
      linarith
    · have hsq : z.im ^ 2 ≤ 32 := by
        have : |z.im| ^ 2 ≤ 4 := by nlinarith [abs_nonneg z.im]
        rw [sq_abs] at this
        linarith
      exact _root_.RHTower.riemannZeta_ne_zero_of_im_sq_le hz1 (by linarith) hsq h0

/-! ### The second physical question -/

/-- **Thermalization faster than the square root is a zero-free strip.** For `0 < δ ≤ 1/4`, every zero
of `ζ` with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ` iff every Farey count of a smooth source above depth one
reaches its limit at rate `y^{1/2 + δ - ε}` for every `ε > 0`. -/
theorem zeroFreeStrip_iff_fareyCount_rate {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ) ↔
      ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
        ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖fareyCount (fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (1 / 2 + δ - ε) := by
  constructor
  · intro hz ε hε φ hφ hc hs
    set σ₀ : ℝ := 1 - 2 * δ with hσ₀
    have hσ0 : 0 ≤ σ₀ := by linarith
    have hσ1 : σ₀ < 1 := by linarith
    have hZ : ∀ z : ℂ, σ₀ < z.re → z ≠ 1 → riemannZeta z ≠ 0 := by
      intro z hz1 _ h0
      rcases lt_or_ge z.re 1 with h | h
      · have := hz z h0 (by linarith)
        linarith
      · exact riemannZeta_ne_zero_of_one_le_re h h0
    have hXi : ∀ z : ℂ, σ₀ < z.re → xi z ≠ 0 := by
      intro z hz1
      rcases lt_or_ge z.re 1 with h | h
      · have h1 : z ≠ 1 := fun h1 => by rw [h1, one_re] at h; exact lt_irrefl _ h
        rw [Ne, xi_eq_zero_iff (by linarith) h1]
        exact hZ z hz1 h1
      · exact xi_ne_zero_of_one_le_re h
    obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
    have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
    obtain ⟨C, hC0, hrate⟩ := norm_horocycleMean_sub_le_of_zeroFree hψ ha hσ0 hσ1.le hXi
      (fun δ' hδ' d => invZeta_poly_of_zeroFree hσ0 hσ1 hZ hδ' d)
      (ε := min ε (1 / 2)) (lt_min hε (by norm_num)) (by linarith [min_le_right ε (1 / 2)])
    refine ⟨residueConst (fun t => (φ t : ℂ)), C, fun y hy hy1 => ?_⟩
    rw [← horocycleMean_eq_fareyCount hφ hc hs hy hy1]
    refine (hrate y hy hy1).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith [min_le_left ε (1 / 2)])
  · intro h ρ hρ hρ0
    by_contra hlt
    push Not at hlt
    set ε : ℝ := (ρ.re - (1 - 2 * δ)) / 4 with hε
    have hε0 : 0 < ε := by linarith
    have := re_le_of_fareyCount_rate (h ε hε0) hρ hρ0
    linarith

end GaloisForLFunctions.CountingHolography

end
