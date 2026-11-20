import GaloisForLFunctions.ArithmeticProducerTheory.OneSidedTransferAlongPositiveDilationKernels
import GaloisForLFunctions.ExceptionalLayerTheory.EveryRightZeroForcesBothSignsOfThePrimeError
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.LocalizingAPrimeSurplusToAFiniteMidpointWindow
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.SquareRootThreshold.TheFiveSixthsFacesOfTheZeroAbscissa

/-!
# Every contracting dilation stencil of the prime error is a one-sided meter

For a positive dilation stencil `(a_j, λ_j)` the centred gap of the prime error
`V(x) = θ(x) − x` is `G(x) = V(x) − Σ_j a_j V(λ_j x)`
`= θ(x) − Σ_j a_j θ(λ_j x) − (1 − ρ(1)) x` (`primeErrorGap`); on a stencil with barycentre `1` it is
the plain Jensen gap of `θ`.

* `signed_theta_sub_le_of_primeErrorGap_le`: if `ρ(1) ≤ 1` and `ρ(s) < 1`, `s ≤ 1`, a one-sided
  bound `±G ≤ A x^s` gives `±V ≤ A / (1 − ρ(s)) · x^s`. The only a priori input is the prime number
  theorem, which removes the neutral mode `x`.
* `zetaZeroAbscissa_le_of_signed_theta`: a one-sided bound of either sign on `V` at an exponent
  `b ≥ ½` excludes zeros of `ζ` to the right of `b`.
* `primeErrorGap_upper_spectrum_iff`: if `ρ < 1` on `(½, 1)`, the exponents at which `±G` has a
  one-sided power bound are exactly those above the zero abscissa.
* `thetaJensenGap_upper_spectrum_iff`: this holds for every barycentric stencil.

So the halving increment, the midpoint and every Jensen gap `θ(x) − Σ a_j θ(λ_j x)` are one meter:
each measures the zero abscissa one-sidedly, with either sign.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

variable {ι : Type*}

/-- The centred gap of the prime error `V(x) = θ(x) − x` on a dilation stencil:
`V(x) − Σ_j a_j V(λ_j x)`. -/
def primeErrorGap (t : Finset ι) (a lam : ι → ℝ) (x : ℝ) : ℝ :=
  (Chebyshev.theta x - x) - ∑ j ∈ t, a j * (Chebyshev.theta (lam j * x) - lam j * x)

/-- The centred gap is the stencil gap of `θ` minus the main term `(1 − ρ(1)) x`. -/
theorem primeErrorGap_eq (t : Finset ι) (a lam : ι → ℝ) (x : ℝ) :
    primeErrorGap t a lam x =
      Chebyshev.theta x - ∑ j ∈ t, a j * Chebyshev.theta (lam j * x) -
        (1 - dilationGain t a lam 1) * x := by
  have e : ∑ j ∈ t, a j * (Chebyshev.theta (lam j * x) - lam j * x) =
      ∑ j ∈ t, a j * Chebyshev.theta (lam j * x) - (∑ j ∈ t, a j * lam j) * x := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [primeErrorGap, e, dilationGain_one]
  ring

/-- On a stencil with barycentre `1` the main terms cancel: the centred gap is the Jensen gap of
`θ`. -/
theorem primeErrorGap_of_barycentre {t : Finset ι} {a lam : ι → ℝ}
    (h1 : ∑ j ∈ t, a j * lam j = 1) (x : ℝ) :
    primeErrorGap t a lam x =
      Chebyshev.theta x - ∑ j ∈ t, a j * Chebyshev.theta (lam j * x) := by
  rw [primeErrorGap_eq, dilationGain_one, h1]
  ring

/-- **The prime number theorem as an a priori bound at the neutral exponent.** For every `ε > 0`
and `s ≤ 1`, `|θ(x) − x| ≤ ε x + B x^s` on all of `x > 0`. -/
theorem abs_theta_sub_le_eps_mul_add_rpow {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 1) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → |Chebyshev.theta x - x| ≤ ε * x + B * x ^ s := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (_root_.RHTower.chebyshevTheta_eventually_relative hε)
  have hX1 : (1 : ℝ) ≤ max X₀ 1 := le_max_right _ _
  have hX0 : 0 < max X₀ 1 := lt_of_lt_of_le one_pos hX1
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨(Real.log 4 + 1) * max X₀ 1 ^ (1 - s), fun x hx => ?_⟩
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx.le s
  rcases le_total (max X₀ 1) x with hXx | hxX
  · have h := hX₀ x ((le_max_left _ _).trans hXx)
    have h2 : 0 ≤ (Real.log 4 + 1) * max X₀ 1 ^ (1 - s) * x ^ s :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hX0.le _)) hxs
    linarith
  · have hθ0 := Chebyshev.theta_nonneg x
    have hθ1 := Chebyshev.theta_le_log4_mul_x hx.le
    have hlx : 0 ≤ Real.log 4 * x := mul_nonneg hlog hx.le
    have habs : |Chebyshev.theta x - x| ≤ (Real.log 4 + 1) * x := by
      rw [abs_le]
      constructor <;> linarith
    have hsplit : x = x ^ (1 - s) * x ^ s := by
      rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
    have hpow : x ^ (1 - s) ≤ max X₀ 1 ^ (1 - s) := Real.rpow_le_rpow hx.le hxX (by linarith)
    have hmul : x ^ (1 - s) * x ^ s ≤ max X₀ 1 ^ (1 - s) * x ^ s :=
      mul_le_mul_of_nonneg_right hpow hxs
    have hfin : (Real.log 4 + 1) * x ≤ (Real.log 4 + 1) * max X₀ 1 ^ (1 - s) * x ^ s := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsplit.le.trans hmul) (by linarith)
    have hεx : 0 ≤ ε * x := (mul_pos hε hx).le
    linarith

/-- **Transfer for the prime error.** On a positive stencil with `ρ(1) ≤ 1`, at an exponent
`s ≤ 1` with `ρ(s) < 1`, a one-sided bound of either sign on the centred gap is the same bound on
the prime error, with the exact factor `1 / (1 − ρ(s))`. The a priori input is the prime number
theorem. -/
theorem signed_theta_sub_le_of_primeErrorGap_le {t : Finset ι} {a lam : ι → ℝ}
    (ha : ∀ j ∈ t, 0 ≤ a j) (hl : ∀ j ∈ t, 0 < lam j) (h1 : dilationGain t a lam 1 ≤ 1)
    {s A σ : ℝ} (hs1 : s ≤ 1) (hs : dilationGain t a lam s < 1) (hA : 0 ≤ A) (hσ : |σ| = 1)
    (h : ∀ x : ℝ, 0 < x → σ * primeErrorGap t a lam x ≤ A * x ^ s) :
    ∀ x : ℝ, 0 < x →
      σ * (Chebyshev.theta x - x) ≤ A / (1 - dilationGain t a lam s) * x ^ s := by
  refine le_rpow_of_le_add_dilate_of_isLittleO ha hl
    (f := fun x => σ * (Chebyshev.theta x - x)) (g := fun x => σ * primeErrorGap t a lam x)
    (u := 1) hA hs h1 (fun x _ => ?_) h (fun ε hε => ?_)
  · have e : ∑ j ∈ t, a j * (σ * (Chebyshev.theta (lam j * x) - lam j * x)) =
        σ * ∑ j ∈ t, a j * (Chebyshev.theta (lam j * x) - lam j * x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    show σ * (Chebyshev.theta x - x) ≤ σ * primeErrorGap t a lam x +
      ∑ j ∈ t, a j * (σ * (Chebyshev.theta (lam j * x) - lam j * x))
    rw [e, primeErrorGap]
    exact le_of_eq (by ring)
  · obtain ⟨B, hB⟩ := abs_theta_sub_le_eps_mul_add_rpow hε hs1
    refine ⟨B, s, hs, fun x hx => ?_⟩
    have h2 : σ * (Chebyshev.theta x - x) ≤ |Chebyshev.theta x - x| := by
      calc σ * (Chebyshev.theta x - x) ≤ |σ * (Chebyshev.theta x - x)| := le_abs_self _
        _ = |Chebyshev.theta x - x| := by rw [abs_mul, hσ, one_mul]
    show σ * (Chebyshev.theta x - x) ≤ ε * x ^ (1 : ℝ) + B * x ^ s
    rw [Real.rpow_one]
    exact h2.trans (hB x hx)

/-- A one-sided power bound of either sign for `ψ(n) − n` on the integers excludes zeros to its
right: a zero with larger real part forces peaks of both signs at its own power. -/
theorem zetaZeroAbscissa_le_of_signed_psi {b B σ : ℝ} (hb : 1 / 2 ≤ b) (hσ : |σ| = 1)
    (h : ∀ n : ℕ, 1 ≤ n → σ * (Chebyshev.psi n - n) ≤ B * (n : ℝ) ^ b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b := by
  refine csSup_le _root_.RHTower.zetaZeroReSet_nonempty fun x hx => ?_
  obtain ⟨ρ, hz, rfl⟩ := hx
  by_contra! hlt
  have h1 : ρ.re < 1 := lt_of_not_ge fun hh => riemannZeta_ne_zero_of_one_le_re hh hz
  obtain ⟨c, hc, hpeak⟩ :=
    GaloisForLFunctions.ExceptionalLayerTheory.both_prime_error_peaks_at_every_large_cutoff
      (hb.trans_lt hlt) h1 hz
  have hlim : Tendsto (fun n : ℕ => B * (n : ℝ) ^ (-(ρ.re - b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).comp
      tendsto_natCast_atTop_atTop).const_mul B
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  obtain ⟨N, hl, hNk⟩ := (hpeak.and (eventually_ge_atTop (k ^ 2))).exists
  obtain ⟨n, hn, hs, hlarge⟩ := hl σ hσ
  have hkr : (k : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by exact_mod_cast hNk)
  have hr : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have ht := mul_lt_mul_of_pos_right (hk n (Nat.cast_le.mp (hkr.trans hs.le)))
    (Real.rpow_pos_of_pos hr ρ.re)
  rw [mul_assoc, ← Real.rpow_add hr, show -(ρ.re - b) + ρ.re = b by ring] at ht
  linarith only [ht, h n (Finset.mem_Icc.mp hn).1, hlarge]

/-- **Landing.** A one-sided power bound of either sign for `θ(x) − x` at an exponent `b ≥ ½`
excludes zeros of `ζ` to the right of `b`. -/
theorem zetaZeroAbscissa_le_of_signed_theta {b B σ : ℝ} (hb : 1 / 2 ≤ b) (hσ : σ = 1 ∨ σ = -1)
    (h : ∀ x : ℝ, 1 ≤ x → σ * (Chebyshev.theta x - x) ≤ B * x ^ b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b := by
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hσ' : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  refine zetaZeroAbscissa_le_of_signed_psi (B := |B| + |D|) hb hσ' fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 0 ≤ (n : ℝ) ^ b := Real.rpow_nonneg (Nat.cast_nonneg n) b
  have hθ := (h n hn1).trans (mul_le_mul_of_nonneg_right (le_abs_self B) hpow)
  have hsqrt : Real.sqrt n ≤ (n : ℝ) ^ b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hb
  have hprop := (hD n).trans
    (mul_le_mul (le_abs_self D) hsqrt (Real.sqrt_nonneg _) (abs_nonneg D))
  have hψθ := Chebyshev.theta_le_psi (n : ℝ)
  have hDn := mul_nonneg (abs_nonneg D) hpow
  have hBn := mul_nonneg (abs_nonneg B) hpow
  rcases hσ with rfl | rfl
  · linarith
  · linarith

/-- Above the zero abscissa the prime error has a two-sided power envelope on all of `x > 0`. -/
theorem abs_theta_sub_le_rpow_of_zetaZeroAbscissa_le {b s : ℝ} (hb : 1 / 2 ≤ b)
    (h : _root_.RHTower.zetaZeroAbscissa ≤ b) (hbs : b < s) (hs1 : s ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → |Chebyshev.theta y - y| ≤ M * y ^ s := by
  have hsup : _root_.RHTower.zeroReSup < s :=
    ((GaloisForLFunctions.SquareRootThreshold.zeroReSup_le_iff_zetaZeroAbscissa_le hb).mpr
      h).trans_lt hbs
  obtain ⟨M, hM, hbound⟩ :=
    GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.theta_power_envelope_of_zero_sup
      hsup (hb.trans hbs.le)
  refine ⟨M + 1, by linarith, fun y hy => ?_⟩
  have hys : 0 ≤ y ^ s := Real.rpow_nonneg hy.le s
  rcases le_total 1 y with h1 | h1
  · have h2 := hbound y h1
    linarith
  · rw [Chebyshev.theta_eq_zero_of_lt_two (by linarith), zero_sub, abs_neg, abs_of_pos hy]
    have hle : y ≤ y ^ s := by
      calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ s := Real.rpow_le_rpow_of_exponent_ge hy h1 hs1
    have h3 := mul_nonneg hM hys
    linarith

/-- Above the zero abscissa every positive stencil has a two-sided power bound on its centred
gap. -/
theorem abs_primeErrorGap_le_of_zetaZeroAbscissa_le {t : Finset ι} {a lam : ι → ℝ}
    (ha : ∀ j ∈ t, 0 ≤ a j) (hl : ∀ j ∈ t, 0 < lam j) {b s : ℝ} (hb : 1 / 2 ≤ b)
    (h : _root_.RHTower.zetaZeroAbscissa ≤ b) (hbs : b < s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → |primeErrorGap t a lam x| ≤ C * x ^ s := by
  obtain ⟨M, hM, hV⟩ := abs_theta_sub_le_rpow_of_zetaZeroAbscissa_le hb h hbs hs1
  refine ⟨M * (1 + dilationGain t a lam s), fun x hx => ?_⟩
  have hsum : |∑ j ∈ t, a j * (Chebyshev.theta (lam j * x) - lam j * x)| ≤
      M * (dilationGain t a lam s * x ^ s) := by
    calc |∑ j ∈ t, a j * (Chebyshev.theta (lam j * x) - lam j * x)|
        ≤ ∑ j ∈ t, |a j * (Chebyshev.theta (lam j * x) - lam j * x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ t, a j * (M * (lam j * x) ^ s) := Finset.sum_le_sum fun j hj => by
          rw [abs_mul, abs_of_nonneg (ha j hj)]
          exact mul_le_mul_of_nonneg_left (hV _ (mul_pos (hl j hj) hx)) (ha j hj)
      _ = M * (dilationGain t a lam s * x ^ s) := by
          rw [← sum_mul_rpow_dilate a hl s hx, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have h0 := abs_le.mp (hV x hx)
  have h2 := abs_le.mp hsum
  rw [primeErrorGap, abs_le]
  constructor <;> linarith [h0.1, h0.2, h2.1, h2.2]

/-- **The one-sided spectrum of a contracting stencil is the zero abscissa.** If `ρ(1) ≤ 1` and
`ρ < 1` on `(½, 1)`, then for either sign the exponents `s < 1` at which `±G(x) ≤ C x^s` holds are
exactly those above the zero abscissa of `ζ`. -/
theorem primeErrorGap_upper_spectrum_iff {t : Finset ι} {a lam : ι → ℝ}
    (ha : ∀ j ∈ t, 0 ≤ a j) (hl : ∀ j ∈ t, 0 < lam j) (h1 : dilationGain t a lam 1 ≤ 1)
    (hρ : ∀ s : ℝ, 1 / 2 < s → s < 1 → dilationGain t a lam s < 1)
    {b σ : ℝ} (hb : 1 / 2 ≤ b) (hσ : σ = 1 ∨ σ = -1) :
    (∀ s : ℝ, b < s → s < 1 →
        ∃ C : ℝ, ∀ x : ℝ, 0 < x → σ * primeErrorGap t a lam x ≤ C * x ^ s) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  have hσ' : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  constructor
  · intro h
    refine le_of_forall_gt_imp_ge_of_dense fun s hbs => ?_
    rcases lt_or_ge s 1 with hs1 | hs1
    · obtain ⟨C, hC⟩ := h s hbs hs1
      have hs := hρ s (hb.trans_lt hbs) hs1
      have htr := signed_theta_sub_le_of_primeErrorGap_le ha hl h1 hs1.le hs (abs_nonneg C) hσ'
        (fun x hx => (hC x hx).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx.le s)))
      exact zetaZeroAbscissa_le_of_signed_theta (hb.trans hbs.le) hσ
        fun x hx => htr x (lt_of_lt_of_le one_pos hx)
    · exact _root_.RHTower.zetaZeroAbscissa_le_one.trans hs1
  · intro h s hbs hs1
    obtain ⟨C, hC⟩ := abs_primeErrorGap_le_of_zetaZeroAbscissa_le ha hl hb h hbs hs1.le
    refine ⟨C, fun x hx => ?_⟩
    calc σ * primeErrorGap t a lam x ≤ |σ * primeErrorGap t a lam x| := le_abs_self _
      _ = |primeErrorGap t a lam x| := by rw [abs_mul, hσ', one_mul]
      _ ≤ C * x ^ s := hC x hx

/-- **Every Jensen gap of `θ` is a one-sided meter.** For a barycentric stencil and either sign,
the exponents `s < 1` with `±(θ(x) − Σ_j a_j θ(λ_j x)) ≤ C x^s` are exactly those above the zero
abscissa of `ζ`. -/
theorem thetaJensenGap_upper_spectrum_iff {t : Finset ι} {a lam : ι → ℝ}
    (hst : IsBarycentric t a lam) {b σ : ℝ} (hb : 1 / 2 ≤ b) (hσ : σ = 1 ∨ σ = -1) :
    (∀ s : ℝ, b < s → s < 1 → ∃ C : ℝ, ∀ x : ℝ, 0 < x →
        σ * (Chebyshev.theta x - ∑ j ∈ t, a j * Chebyshev.theta (lam j * x)) ≤ C * x ^ s) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [← primeErrorGap_upper_spectrum_iff (fun j hj => (hst.weight_pos j hj).le) hst.scale_pos
    hst.gain_one.le (fun s hs0 hs1 => hst.gain_lt_one (by linarith) hs1) hb hσ]
  simp only [primeErrorGap_of_barycentre hst.barycentre]

end GaloisForLFunctions.ArithmeticProducerTheory
