import GaloisForLFunctions.ExceptionalLayerTheory.TheGrowingGaussianErrorIsHolomorphic
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianFilteredCofactorLocalization

/-!
# Uniform logarithmic damping of the higher arithmetic error

The Mellin twist suppresses growth along the half-strip. Its logarithmic
factor costs only a fixed constant, while rotation spends one extra height
power per moment order. Equal-radius Cauchy estimates then retain every
spacing factor through a growing polynomial filter.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem exp_neg_mul_affine_le {lam s L : ℝ}
    (hlam : 1 / 2 ≤ lam) (hs : -1 ≤ s) (hL : 0 ≤ L) :
    Real.exp (-lam * s) * (L + s) ≤ (L + 2) * Real.exp lam := by
  have hlam0 : 0 ≤ lam := by linarith only [hlam]
  have he1 : 1 ≤ Real.exp lam := Real.one_le_exp hlam0
  by_cases hs0 : s ≤ 0
  · calc
      _ ≤ Real.exp (-lam * s) * L :=
        mul_le_mul_of_nonneg_left (by linarith only [hs0]) (Real.exp_pos _).le
      _ ≤ Real.exp lam * L := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hs hlam0])) hL
      _ ≤ _ := by nlinarith only [Real.exp_pos lam]
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs0).le
    have he0 : Real.exp (-lam * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hlam0, hs0])
    have he : Real.exp (-lam * s) ≤ Real.exp (-(s / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hlam hs0])
    have hx : s / 2 ≤ Real.exp (s / 2) := by
      have hh := Real.add_one_le_exp (s / 2)
      linarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-(s / 2))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
    have hsbound : Real.exp (-lam * s) * s ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_right he hs0
      nlinarith only [hm, hh]
    have hmain := mul_le_mul_of_nonneg_right he0 hL
    have htarget := mul_le_mul_of_nonneg_left he1 (show 0 ≤ L + 2 by positivity)
    nlinarith only [hsbound, hmain, htarget]

/-- A negative scale power and its logarithm stay bounded after the Mellin twist. -/
theorem damping_scale_log_transport {X Y s p β : ℝ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hs : -1 ≤ s)
    (hp : 1 / 2 ≤ p) (hβ : 1 / 2 ≤ β)
    (hlo : Real.log X + s - Real.log 2 ≤ Real.log Y)
    (hhi : Real.log Y ≤ Real.log X + s + Real.log 2) :
    Real.exp ((1 / 2 - β) * s) * Y ^ (-p) * (1 + Real.log Y) ≤
      4 * Real.exp (β + p) * (2 : ℝ) ^ p * X ^ (-p) * (1 + Real.log X) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hlogX := Real.log_nonneg hX
  have hlogY := Real.log_nonneg hY
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  let L := 1 + Real.log X + Real.log 2
  let lam := β + p - 1 / 2
  have hlam : 1 / 2 ≤ lam := by dsimp [lam]; linarith only [hp, hβ]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlog : 1 + Real.log Y ≤ L + s := by dsimp [L]; linarith only [hhi]
  have hpower : Real.exp ((1 / 2 - β) * s) * Y ^ (-p) ≤
      X ^ (-p) * (2 : ℝ) ^ p * Real.exp (-lam * s) := by
    rw [Real.rpow_def_of_pos hY0, Real.rpow_def_of_pos hX0,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_right hlo (neg_nonpos.mpr hp0)
    dsimp only [lam]
    nlinarith only [hh]
  have hscalar := exp_neg_mul_affine_le hlam hs hL
  have hLp : L + 2 ≤ 4 * (1 + Real.log X) := by
    dsimp only [L]
    linarith only [hlog2le, hlogX]
  have hexp : Real.exp lam ≤ Real.exp (β + p) :=
    Real.exp_le_exp.mpr (by dsimp only [lam]; linarith)
  calc
    _ ≤ (X ^ (-p) * (2 : ℝ) ^ p * Real.exp (-lam * s)) * (L + s) :=
      mul_le_mul hpower hlog (by positivity) (by positivity)
    _ = (X ^ (-p) * (2 : ℝ) ^ p) * (Real.exp (-lam * s) * (L + s)) := by ring
    _ ≤ (X ^ (-p) * (2 : ℝ) ^ p) * ((L + 2) * Real.exp lam) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ ≤ (X ^ (-p) * (2 : ℝ) ^ p) * (4 * (1 + Real.log X) * Real.exp (β + p)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hLp hexp (Real.exp_pos _).le (by positivity))
        (by positivity)
    _ = _ := by ring

/-- The usual Mellin twist of the full higher-moment arithmetic error. -/
def twistedGaussianHigherCentredVaughanError (r : ℕ) (β t : ℝ) (U V : ℕ)
    (ε z : ℂ) : ℂ :=
  Complex.exp ((((1 / 2 : ℂ) + t * I) - β) * z) *
    gaussianHigherCentredVaughanError r (1 / 2) t U V (ε * Complex.exp (-2 * z))

/-- An explicit bound before the exponential order cost is absorbed by height powers. -/
def gaussianHigherErrorStripBound (r : ℕ) (β t X : ℝ) (U V : ℕ) : ℝ :=
  4 * Real.exp (β + 1) * gaussianGrowingMomentConstant *
    (t ^ (7 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
        (Real.exp ((2 * r : ℕ) - (1 / 2 : ℝ)) *
          (2 : ℝ) ^ ((2 * r : ℕ) - (1 / 2 : ℝ))) *
        X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) +
      (V : ℝ) * t ^ (4 * r + 1) *
        (Real.exp (1 / 2) * (2 : ℝ) ^ (1 / 2 : ℝ)) * X ^ (-(1 / 2 : ℝ))) *
    (1 + Real.log X)

/-- Rotation spends one additional height power per moment order. -/
theorem gaussianHigherErrorStripBound_le_height (r : ℕ) {β t X : ℝ}
    (ht : 4 * Real.exp 2 ≤ t) (hX : 1 ≤ X) (U V : ℕ) :
    gaussianHigherErrorStripBound r β t X U V ≤
      8 * Real.exp (β + 2) * gaussianGrowingMomentConstant *
        (t ^ (8 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
            X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) +
          (V : ℝ) * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ))) * (1 + Real.log X) := by
  have ht0 : 0 < t := (by positivity : 0 < 4 * Real.exp 2).trans_le ht
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hG := gaussianGrowingMomentConstant_pos
  have hlogX := Real.log_nonneg hX
  have h₁ : Real.exp ((2 * r : ℕ) - (1 / 2 : ℝ)) *
      (2 : ℝ) ^ ((2 * r : ℕ) - (1 / 2 : ℝ)) ≤ t ^ r := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    calc
      _ ≤ Real.exp ((r : ℝ) * (2 + 2 * Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith only [hlog2]
      _ = (4 * Real.exp 2) ^ r := by
        rw [Real.exp_nat_mul, Real.exp_add]
        have he : Real.exp (2 * Real.log 2) = 4 := by
          rw [show 2 * Real.log 2 = ((2 : ℕ) : ℝ) * Real.log 2 by norm_num,
            Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
        rw [he, mul_comm]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) ht r
  have h₂ : Real.exp (1 / 2) * (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * Real.exp 1 := by
    have hp : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have he := mul_le_mul (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)) hp
      (by positivity) (Real.exp_pos _).le
    simpa only [mul_comm] using he
  have hc : 4 * Real.exp (β + 1) ≤ 8 * Real.exp (β + 2) := by
    have hh := Real.exp_le_exp.mpr (show β + 1 ≤ β + 2 by linarith)
    nlinarith only [hh, Real.exp_pos (β + 2)]
  have he : 4 * Real.exp (β + 1) * (2 * Real.exp 1) = 8 * Real.exp (β + 2) := by
    calc
      _ = 8 * (Real.exp (β + 1) * Real.exp 1) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hp : t ^ (7 * r) * t ^ r = t ^ (8 * r) := by
    rw [← pow_add]
    congr 1
    omega
  unfold gaussianHigherErrorStripBound
  calc
    _ ≤ 4 * Real.exp (β + 1) * gaussianGrowingMomentConstant *
        (t ^ (7 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) * t ^ r *
            X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) +
          (V : ℝ) * t ^ (4 * r + 1) * (2 * Real.exp 1) * X ^ (-(1 / 2 : ℝ))) *
        (1 + Real.log X) := by gcongr
    _ = ((4 * Real.exp (β + 1)) *
          (gaussianGrowingMomentConstant * t ^ (8 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
            X ^ ((1 / 2 : ℝ) - (2 * r : ℕ))) +
        (8 * Real.exp (β + 2)) *
          (gaussianGrowingMomentConstant * (V : ℝ) * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ)))) *
        (1 + Real.log X) := by
      rw [← hp, ← he]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ gaussianGrowingMomentConstant * t ^ (8 * r) *
          ((U * V : ℕ) : ℝ) ^ (2 * r) * X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) by positivity)
      have hh' := mul_le_mul_of_nonneg_right
        (add_le_add_right hh (8 * Real.exp (β + 2) *
          (gaussianGrowingMomentConstant * (V : ℝ) * t ^ (4 * r + 1) * X ^ (-(1 / 2 : ℝ)))))
        (show 0 ≤ 1 + Real.log X by positivity)
      convert hh' using 1 <;> first | rfl | ring

/-- Small order speed and a polynomial gap in the product cutoff make the
entire half-strip bound exponentially small. -/
theorem gaussianHigherErrorStripBound_le_exponential (r J : ℕ)
    {β a κ t : ℝ} (ha : 0 < a) (hκ : κ ≤ a / 32) (hJ : 4 ≤ J)
    (hJκ : 2 * a ≤ (2 * (J : ℝ) - 8) * κ)
    (ht : 1 ≤ t) (htE : 4 * Real.exp 2 ≤ t)
    (hrlo : κ * t ≤ 2 * r * Real.log t) (hrhi : (r : ℝ) * Real.log t ≤ κ * t)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hVt : (V : ℝ) ≤ t)
    (hcut : ((U * V : ℕ) : ℝ) * t ^ J ≤ Real.exp (a * t)) :
    gaussianHigherErrorStripBound r β t (Real.exp (a * t)) U V ≤
      (8 * Real.exp (β + 2) * gaussianGrowingMomentConstant) *
        (1 + t ^ 2) * (1 + a * t) * Real.exp (-(3 * a / 8) * t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hUV : (0 : ℝ) < ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hX : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
  have hD : 0 ≤ 2 * (J : ℝ) - 8 := by
    have hh : (4 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith only [hh]
  have hlow : a * t ≤ (2 * (J : ℝ) - 8) * r * Real.log t := by
    have h₁ := mul_le_mul_of_nonneg_left hrlo hD
    have h₂ := mul_le_mul_of_nonneg_right hJκ ht0.le
    nlinarith only [h₁, h₂]
  have hlogcut : Real.log ((U * V : ℕ) : ℝ) + (J : ℝ) * Real.log t ≤ a * t := by
    have hh := Real.log_le_log (mul_pos hUV (pow_pos ht0 J)) hcut
    rw [Real.log_mul hUV.ne' (pow_ne_zero _ ht0.ne'), Real.log_pow, Real.log_exp] at hh
    exact hh
  have hp {u : ℝ} (hu : 0 < u) (m : ℕ) :
      u ^ m = Real.exp ((m : ℝ) * Real.log u) := by
    rw [Real.exp_nat_mul, Real.exp_log hu]
  have hA : t ^ (8 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
      Real.exp (a * t) ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) ≤
        Real.exp (-(3 * a / 8) * t) := by
    rw [hp ht0, hp hUV, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlogcut
      (show 0 ≤ 2 * (r : ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith only [hh, hlow, mul_pos ha ht0]
  have hB : (V : ℝ) * t ^ (4 * r + 1) * Real.exp (a * t) ^ (-(1 / 2 : ℝ)) ≤
      t ^ 2 * Real.exp (-(3 * a / 8) * t) := by
    calc
      _ ≤ t ^ (4 * r + 2) * Real.exp (a * t) ^ (-(1 / 2 : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_right hVt
          (show 0 ≤ t ^ (4 * r + 1) * Real.exp (a * t) ^ (-(1 / 2 : ℝ)) by positivity)
        calc
          _ = (V : ℝ) * (t ^ (4 * r + 1) * Real.exp (a * t) ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ t * (t ^ (4 * r + 1) * Real.exp (a * t) ^ (-(1 / 2 : ℝ))) := hh
          _ = _ := by
            rw [show 4 * r + 2 = (4 * r + 1) + 1 by omega, pow_succ]
            ring
      _ = t ^ 2 * Real.exp (((4 * r : ℕ) : ℝ) * Real.log t - a * t / 2) := by
        rw [pow_add, hp ht0 (4 * r), Real.rpow_def_of_pos (Real.exp_pos _),
          Real.log_exp, show a * t * (-(1 / 2 : ℝ)) = -(a * t / 2) by ring,
          Real.exp_neg, Real.exp_sub]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg t)
        have hh := mul_le_mul_of_nonneg_right hκ ht0.le
        push_cast
        nlinarith only [hrhi, hh]
  have hC := gaussianGrowingMomentConstant_pos
  have H := gaussianHigherErrorStripBound_le_height r (β := β) htE hX U V
  rw [Real.log_exp] at H
  apply H.trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hA hB)
      (show 0 ≤ 8 * Real.exp (β + 2) * gaussianGrowingMomentConstant by positivity))
    (show 0 ≤ 1 + a * t by positivity)
  convert hh using 1 <;> ring

/-- The actual higher-moment error is uniformly bounded on a reciprocal-height
half-strip, including the logarithmic continuum correction. -/
theorem norm_twistedGaussianHigherCentredVaughanError_le_strip {r : ℕ} (hr : r ≠ 0)
    {β α ξ t X : ℝ} (hβ : 1 / 2 ≤ β) (hα : 0 < α) (ht : 8192 ≤ t)
    (hrt : (r : ℝ) ≤ t) (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t)
    (hX : 1 ≤ X) (hscale : α * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (1 / (16 * t))) :
    ‖twistedGaussianHigherCentredVaughanError r β t U V ((α : ℂ) - ξ * I) z‖ ≤
      gaussianHigherErrorStripBound r β t X U V := by
  let ε := ((α : ℂ) - ξ * I) * Complex.exp (-2 * z)
  have ht0 : 0 < t := by linarith only [ht]
  have ht4 : 4 ≤ t := by linarith only [ht]
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hradius : 1 / (16 * t) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [ht])
  have hs : -1 ≤ z.re := by linarith only [hz.1, hradius]
  have him : t * |z.im| ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_left hz.2.le ht0.le
    have he : t * (1 / (16 * t)) = 1 / 16 := by field_simp
    exact hh.trans_eq he
  obtain ⟨hε, hεlo, hεhi, Y, hY, hscaleY, hYlo⟩ :=
    exists_damping_rotated_scale hα ht4 hlo hhi him hX0 hscale
  change 0 < ε.re at hε
  change ε.re ≤ -ε.im at hεlo
  change -ε.im ≤ 2 * ε.re * t at hεhi
  change ε.re * Y ^ 2 = 2 at hscaleY
  have hYhi := cofactor_rotated_scale_upper hα ht4 hlo hhi him hX0 hscale hY hscaleY
  have hUVY : ((U * V : ℕ) : ℝ) ≤ Y := by
    have hex : 1 ≤ Real.exp 1 * Real.exp z.re := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith only [hs])
    have h₁ := mul_le_mul_of_nonneg_right hex (Nat.cast_nonneg (U * V) : (0 : ℝ) ≤ ((U * V : ℕ) : ℝ))
    have h₂ := mul_le_mul_of_nonneg_right hUV (Real.exp_pos z.re).le
    nlinarith only [h₁, h₂, hYlo]
  have hY1 : 1 ≤ Y :=
    (by exact_mod_cast Nat.mul_pos hU hV : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVY
  have hεsector : ‖ε‖ ≤ 4 * ε.re * t := by
    have hh := Complex.norm_le_abs_re_add_abs_im ε
    rw [abs_of_pos hε, abs_of_nonpos (by linarith only [hεlo, hε] : ε.im ≤ 0)] at hh
    have hm := mul_le_mul_of_nonneg_left ht4 hε.le
    nlinarith only [hh, hεhi, hm, hε]
  have hloglo : Real.log X + z.re - Real.log 2 ≤ Real.log Y := by
    have hh := Real.log_le_log (by positivity : 0 < X * Real.exp z.re / 2) hYlo
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
    exact hh
  have hloghi : Real.log Y ≤ Real.log X + z.re + Real.log 2 := by
    have hh := Real.log_le_log hY hYhi
    rw [Real.log_mul (by positivity : 2 * X ≠ 0) (Real.exp_pos _).ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne', Real.log_exp] at hh
    linarith only [hh]
  have hr2 : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hp : 1 / 2 ≤ ((2 * r : ℕ) : ℝ) - 1 / 2 := by linarith only [hr2]
  have h₁ := damping_scale_log_transport hX hY1 hs hp hβ hloglo hloghi
  have h₂ := damping_scale_log_transport hX hY1 hs (le_refl (1 / 2 : ℝ)) hβ hloglo hloghi
  rw [show -(((2 * r : ℕ) : ℝ) - 1 / 2) = 1 / 2 - (2 * r : ℕ) by ring] at h₁
  have hphase : Real.exp (-t * z.im) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs z.im) ht0.le
    linarith only [hh, him]
  let A := t ^ (7 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r)
  let B := (V : ℝ) * t ^ (4 * r + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC := gaussianGrowingMomentConstant_pos
  have hE := norm_gaussianHigherCentredVaughanError_le_height r hr ht hrt hε hεsector hY hscaleY hU hV hUVY
  have hER : ‖twistedGaussianHigherCentredVaughanError r β t U V ((α : ℂ) - ξ * I) z‖ ≤
      Real.exp (-t * z.im) * gaussianGrowingMomentConstant *
        (A * (Real.exp ((1 / 2 - β) * z.re) * Y ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) *
          (1 + Real.log Y)) +
         B * (Real.exp ((1 / 2 - β) * z.re) * Y ^ (-(1 / 2 : ℝ)) * (1 + Real.log Y))) := by
    unfold twistedGaussianHigherCentredVaughanError
    rw [norm_mul, Complex.norm_exp]
    have he : ((((1 / 2 : ℂ) + t * I) - β) * z).re =
        (1 / 2 - β) * z.re + (-t * z.im) := by simp; ring
    rw [he, Real.exp_add]
    apply (mul_le_mul_of_nonneg_left hE (by positivity)).trans_eq
    dsimp only [A, B]
    ring
  apply hER.trans
  calc
    _ ≤ Real.exp 1 * gaussianGrowingMomentConstant *
        (A * (4 * Real.exp (β + ((2 * r : ℕ) - (1 / 2 : ℝ))) *
            (2 : ℝ) ^ ((2 * r : ℕ) - (1 / 2 : ℝ)) *
            X ^ ((1 / 2 : ℝ) - (2 * r : ℕ)) * (1 + Real.log X)) +
         B * (4 * Real.exp (β + 1 / 2) * (2 : ℝ) ^ (1 / 2 : ℝ) *
            X ^ (-(1 / 2 : ℝ)) * (1 + Real.log X))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hphase hC.le
      · exact add_le_add (mul_le_mul_of_nonneg_left h₁ hA)
          (mul_le_mul_of_nonneg_left h₂ hB)
      · have hlogY := Real.log_nonneg hY1; positivity
      · positivity
    _ = _ := by
      unfold gaussianHigherErrorStripBound
      rw [Real.exp_add β, Real.exp_add β, Real.exp_add β]
      dsimp only [A, B]
      ring

/-- The full arithmetic error retains every spacing factor through a filter
of logarithmically growing degree, uniformly in the Vaughan cutoffs. -/
theorem norm_filtered_gaussianHigherCentredVaughanError_le_growing {r : ℕ} (hr : r ≠ 0)
    {β α ξ t X h B κ : ℝ} (hβ : 1 / 2 ≤ β) (hα : 0 < α)
    (ht : max 8192 (34 + 2 * Real.exp 1) ≤ t) (hrt : (r : ℝ) ≤ t)
    (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t) (hX : 1 ≤ X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ X)
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hBt : B ≤ t ^ 2) (hhB : h * B ≤ 1)
    (ws : List ℂ) (hws : ∀ ω ∈ ws, ‖ω‖ ≤ B)
    (hdt : (ws.length : ℝ) ≤ t) (hdegree : (ws.length : ℝ) * Real.log t ≤ κ * t) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianHigherCentredVaughanError r β t U V ((α : ℂ) - ξ * I)
          ((j : ℂ) * h)‖ ≤
      gaussianHigherErrorStripBound r β t X U V * h ^ ws.length * Real.exp (3 * κ * t) := by
  have ht8 : 8192 ≤ t := (le_max_left _ _).trans ht
  have ht4 : 4 ≤ t := by linarith only [ht8]
  have ht0 : 0 < t := by linarith only [ht8]
  have hM : 0 ≤ gaussianHigherErrorStripBound r β t X U V := by
    have hC := gaussianGrowingMomentConstant_pos
    have hlogX := Real.log_nonneg hX
    unfold gaussianHigherErrorStripBound
    positivity
  apply norm_dampingFilterPolynomial_sum_le_growing_order hM hh hB
    ((le_max_right _ _).trans ht) hBt hhB ws hws hdt hdegree
  · intro z hz
    have him : t * |z.im| ≤ 1 / 16 := by
      have hh := mul_le_mul_of_nonneg_left hz.2.le ht0.le
      have he : t * (1 / (16 * t)) = 1 / 16 := by field_simp
      exact hh.trans_eq he
    have hgeom := exists_damping_rotated_scale hα ht4 hlo hhi him
      (zero_lt_one.trans_le hX) hscale
    have hd := differentiableAt_gaussianHigherCentredVaughanError hr
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      t U V hgeom.1
    have he : DifferentiableAt ℂ
        (fun w : ℂ => ((α : ℂ) - ξ * I) * Complex.exp (-2 * w)) z := by fun_prop
    have hw : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp ((((1 / 2 : ℂ) + t * I) - β) * w)) z := by fun_prop
    exact (hw.mul (hd.comp z he)).differentiableWithinAt
  · intro z hz
    exact norm_twistedGaussianHigherCentredVaughanError_le_strip hr hβ hα ht8 hrt
      hlo hhi hX hscale hU hV hUV hz

/-- At exponential observation scale, simultaneous moment growth and filter
growth leave an exponentially small arithmetic error. -/
theorem norm_filtered_gaussianHigherCentredVaughanError_le_exponential
    (r J : ℕ) (hr : r ≠ 0) {β a κ α ξ t h B : ℝ}
    (ha : 0 < a) (hκ : κ ≤ a / 32) (hJ : 4 ≤ J)
    (hJκ : 2 * a ≤ (2 * (J : ℝ) - 8) * κ)
    (hβ : 1 / 2 ≤ β) (hα : 0 < α)
    (ht : max 8192 (34 + 2 * Real.exp 1) ≤ t) (htE : 4 * Real.exp 2 ≤ t)
    (hrt : (r : ℝ) ≤ t) (hrlo : κ * t ≤ 2 * r * Real.log t)
    (hrhi : (r : ℝ) * Real.log t ≤ κ * t)
    (hlo : 2 * α ≤ ξ) (hhi : ξ ≤ α * t) (hscale : α * Real.exp (a * t) ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hVt : (V : ℝ) ≤ t)
    (hUV : 2 * Real.exp 1 * ((U * V : ℕ) : ℝ) ≤ Real.exp (a * t))
    (hcut : ((U * V : ℕ) : ℝ) * t ^ J ≤ Real.exp (a * t))
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hBt : B ≤ t ^ 2) (hhB : h * B ≤ 1)
    (ws : List ℂ) (hws : ∀ ω ∈ ws, ‖ω‖ ≤ B)
    (hdt : (ws.length : ℝ) ≤ t) (hdegree : (ws.length : ℝ) * Real.log t ≤ (a / 24) * t) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j *
        twistedGaussianHigherCentredVaughanError r β t U V ((α : ℂ) - ξ * I)
          ((j : ℂ) * h)‖ ≤
      (8 * Real.exp (β + 2) * gaussianGrowingMomentConstant) *
        (1 + t ^ 2) * (1 + a * t) * h ^ ws.length * Real.exp (-(a / 4) * t) := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ) ≤ 8192).trans ((le_max_left _ _).trans ht)
  have hX : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
  have H := norm_filtered_gaussianHigherCentredVaughanError_le_growing hr hβ hα ht hrt
    hlo hhi hX hscale hU hV hUV hh hB hBt hhB ws hws hdt hdegree
  have HM := gaussianHigherErrorStripBound_le_exponential r J (β := β) ha hκ hJ hJκ
    ht1 htE hrlo hrhi hU hV hVt hcut
  have he : Real.exp (-(3 * a / 8) * t) * Real.exp (3 * (a / 24) * t) =
      Real.exp (-(a / 4) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply H.trans
  calc
    _ ≤ ((8 * Real.exp (β + 2) * gaussianGrowingMomentConstant) *
        (1 + t ^ 2) * (1 + a * t) * Real.exp (-(3 * a / 8) * t)) *
        h ^ ws.length * Real.exp (3 * (a / 24) * t) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right HM (pow_nonneg hh _)) (Real.exp_pos _).le
    _ = _ := by
      calc
        _ = ((8 * Real.exp (β + 2) * gaussianGrowingMomentConstant) *
            (1 + t ^ 2) * (1 + a * t) * h ^ ws.length) *
            (Real.exp (-(3 * a / 8) * t) * Real.exp (3 * (a / 24) * t)) := by ring
        _ = _ := by rw [he]

/-- Concrete growing moment order and Vaughan cutoffs give an exponentially
accurate filter transfer, uniformly over admissible roots and spacings. -/
theorem eventually_filtered_gaussianHigherCentredVaughanError_decay {a β : ℝ}
    (ha : 0 < a) (hβ : 1 / 2 ≤ β) :
    ∀ᶠ t : ℝ in atTop, ∀ α ξ h B : ℝ, 0 < α → 2 * α ≤ ξ → ξ ≤ α * t →
      α * Real.exp (a * t) ^ 2 = 2 → 0 ≤ h → 0 ≤ B → B ≤ t ^ 2 → h * B ≤ 1 →
      ∀ ws : List ℂ, (∀ ω ∈ ws, ‖ω‖ ≤ B) →
        (ws.length : ℝ) * Real.log t ≤ (a / 24) * t →
        ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
          (dampingFilterPolynomial h ws).coeff j *
            twistedGaussianHigherCentredVaughanError (gaussianGrowingMomentOrder (a / 64) t)
              β t (gaussianGrowingLongCutoff a 68 t) ⌊t⌋₊ ((α : ℂ) - ξ * I)
                ((j : ℂ) * h)‖ ≤ h ^ ws.length * Real.exp (-(a / 8) * t) := by
  let K := 8 * Real.exp (β + 2) * gaussianGrowingMomentConstant
  let C := 2 * K * (1 + a)
  have hK : 0 < K := by
    have hh := gaussianGrowingMomentConstant_pos
    dsimp only [K]
    positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hp : Tendsto (fun t : ℝ => t ^ 3 * Real.exp (-(a / 8) * t)) atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) (a / 8) (by positivity)
  have hp' := hp.const_mul C
  simp only [mul_zero] at hp'
  filter_upwards [eventually_gaussianGrowingMomentOrder_bounds (by positivity : 0 < a / 64),
    eventually_gaussianGrowingLongCutoff_bounds ha 68,
    eventually_ge_atTop (max 8192 (34 + 2 * Real.exp 1)),
    eventually_ge_atTop (4 * Real.exp 2), eventually_ge_atTop (2 * Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (a / 24))),
    hp'.eventually_lt_const zero_lt_one]
    with t hr hcut ht htE ht2e hlog hsmall α ξ h B hα hlo hhi hscale hh hB hBt hhB ws hws hdegree
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ) ≤ 8192).trans ((le_max_left _ _).trans ht)
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le ((le_max_left _ _).trans hlog)
  have hdt : (ws.length : ℝ) ≤ t := by
    have hℓ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hlog) ht0.le
    nlinarith only [hdegree, hℓ, hlog0]
  have hUV : 2 * Real.exp 1 *
      ((gaussianGrowingLongCutoff a 68 t * ⌊t⌋₊ : ℕ) : ℝ) ≤ Real.exp (a * t) := by
    have ht68 : t ≤ t ^ 68 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 68)
    calc
      _ ≤ t ^ 68 * ((gaussianGrowingLongCutoff a 68 t * ⌊t⌋₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (ht2e.trans ht68) (Nat.cast_nonneg _)
      _ ≤ _ := by simpa only [mul_comm] using hcut.2.2.2.1
  have H := norm_filtered_gaussianHigherCentredVaughanError_le_exponential
    (gaussianGrowingMomentOrder (a / 64) t) 68 hr.1 ha
    (by linarith only [ha] : a / 64 ≤ a / 32) (by norm_num : 4 ≤ 68)
    (by norm_num; linarith : 2 * a ≤ (2 * (68 : ℝ) - 8) * (a / 64))
    hβ hα ht htE hr.2.1 hr.2.2.1 hr.2.2.2 hlo hhi hscale
    hcut.1 hcut.2.1 hcut.2.2.1 hUV hcut.2.2.2.1 hh hB hBt hhB ws hws hdt hdegree
  have hpoly : K * (1 + t ^ 2) * (1 + a * t) ≤ C * t ^ 3 := by
    have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
    have h₁ : 1 + t ^ 2 ≤ 2 * t ^ 2 := by linarith only [ht2]
    have h₂ : 1 + a * t ≤ (1 + a) * t := by nlinarith only [ht1]
    have h₃ := mul_le_mul
      (mul_le_mul_of_nonneg_left h₁ hK.le) h₂ (by positivity) (by positivity)
    convert h₃ using 1 <;> try dsimp only [C]
    all_goals first | rfl | ring
  have hcost : K * (1 + t ^ 2) * (1 + a * t) * Real.exp (-(a / 8) * t) ≤ 1 := by
    calc
      _ ≤ (C * t ^ 3) * Real.exp (-(a / 8) * t) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ ≤ 1 := by simpa only [mul_assoc] using hsmall.le
  have he : Real.exp (-(a / 4) * t) =
      Real.exp (-(a / 8) * t) * Real.exp (-(a / 8) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply H.trans
  change K * (1 + t ^ 2) * (1 + a * t) * h ^ ws.length * Real.exp (-(a / 4) * t) ≤ _
  rw [he]
  calc
    _ = (K * (1 + t ^ 2) * (1 + a * t) * Real.exp (-(a / 8) * t)) *
        (h ^ ws.length * Real.exp (-(a / 8) * t)) := by ring
    _ ≤ 1 * (h ^ ws.length * Real.exp (-(a / 8) * t)) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = _ := one_mul _

end GaloisForLFunctions.ExceptionalLayerTheory
