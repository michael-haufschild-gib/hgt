import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bilateral prime-angle moderation: the growth dichotomy and the selector

For a prime `p` and `s : ℂ`, the critical half-density character is
`λ_p(s) = p^(1/2 - s)`, with `‖λ_p(s)‖ = p^(1/2 - Re s)`.  The bilateral jet family at
logarithmic grade `k` is `c_e = e^k · λ_p(s)^e` over `e : ℤ` — the coefficient family of the
FE-sewn bilateral boundary value in the prime angle.

A bilateral family is **moderate** when its coefficients have polynomial two-sided growth; by
the classical Schwartz characterization this says exactly that the family is the Fourier
coefficient family of a distribution on the circle, and the growth form is the mathematical
content formalized here.

Results, all unconditional:

* `norm_bilateralHalfDensityCharacter_eq_one_iff` — `‖λ_p(s)‖ = 1 ↔ Re s = 1/2`.
* **The moderation dichotomy** — the jet family is moderate iff `Re s = 1/2`, at every grade:
  off the line one Fourier side grows geometrically and beats every polynomial
  (`exists_one_le_and_pow_gt_poly`).
* `bilateralJetFamily_zpow_on_line` — on the line the character powers are the phase family
  `e ↦ exp(-i e γ log p)` of the point conormal at angle `γ log p`: the delta-derivative
  identification of the selector.
* `re_eq_half_of_moderate_bilateral_eigen` — **the selector**: a *nonzero* moderate bilateral
  family which is a shift eigenfamily with character `λ_p(s)` forces `Re s = 1/2`.  This is
  the distributional off-unitary Koszul vanishing: at moderate regularity nothing survives off
  the unitary prime spectrum.

No zeta value, zero datum, functional-equation premise, or positivity input occurs anywhere.
-/

noncomputable section

open Complex

namespace RHTower

/-- Polynomial two-sided growth of a bilateral coefficient family: the growth form of "is the
Fourier coefficient family of a circle distribution". -/
def bilateralModerate (c : ℤ → ℂ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), ∀ e : ℤ, ‖c e‖ ≤ C * (1 + (e.natAbs : ℝ)) ^ m

/-- The critical half-density character `λ_p(s) = p^(1/2 - s)`. -/
def bilateralHalfDensityCharacter (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - s)

/-- The bilateral logarithmic-jet family `e ↦ e^k λ_p(s)^e`. -/
def bilateralJetFamily (p : ℕ) (s : ℂ) (k : ℕ) (e : ℤ) : ℂ :=
  (e : ℂ) ^ k * bilateralHalfDensityCharacter p s ^ e

/-- Geometric growth beats every polynomial: for `r > 1` there is `n ≥ 1` with
`C (1+n)^m < r^n`. -/
theorem exists_one_le_and_pow_gt_poly {r : ℝ} (hr : 1 < r) (C : ℝ) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ C * (1 + (n : ℝ)) ^ m < r ^ n := by
  set C' : ℝ := max C 1 with hC'
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le one_pos hC'1
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have hrinv : ‖r⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    exact (inv_lt_one₀ hr0).mpr hr
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ m * r⁻¹ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one m hrinv
  have hpos : (0 : ℝ) < 1 / (C' * 2 ^ m) := by positivity
  have hev := hsum.tendsto_atTop_zero.eventually_lt_const hpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set n : ℕ := max N 1 with hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right N 1
  have hsmall := hN n (le_max_left N 1)
  rw [inv_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < C' * 2 ^ m)] at hsmall
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
  have hstep : C * (1 + (n : ℝ)) ^ m ≤ C' * (2 * n) ^ m := by
    apply mul_le_mul (le_max_left C 1)
      (pow_le_pow_left₀ (by positivity) (by linarith) m)
      (by positivity) (le_of_lt hC'0)
  have hkey : C' * (2 * (n : ℝ)) ^ m < r ^ n := by
    rw [mul_pow]
    calc C' * (2 ^ m * (n : ℝ) ^ m)
        = ((n : ℝ) ^ m * (r ^ n)⁻¹ * (C' * 2 ^ m)) * r ^ n := by
          field_simp
      _ < 1 * r ^ n := mul_lt_mul_of_pos_right hsmall hrn
      _ = r ^ n := one_mul _
  linarith

/-- One-sided geometric growth along either Fourier direction defeats moderation. -/
theorem not_bilateralModerate_of_growth {c : ℤ → ℂ} {r : ℝ} (hr : 1 < r)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hgrow : ∀ n : ℕ, 1 ≤ n → r ^ n ≤ ‖c (sign * n)‖) :
    ¬ bilateralModerate c := by
  rintro ⟨C, m, hC⟩
  obtain ⟨n, hn1, hlt⟩ := exists_one_le_and_pow_gt_poly hr C m
  have hle := hC (sign * n)
  have habs : (((sign * (n : ℤ)).natAbs : ℝ)) = (n : ℝ) := by
    rcases hsign with h | h <;> simp [h]
  rw [habs] at hle
  have hg := hgrow n hn1
  linarith

/-- Modulus of the half-density character: `p^(1/2 - Re s)`. -/
theorem norm_bilateralHalfDensityCharacter {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖bilateralHalfDensityCharacter p s‖ = (p : ℝ) ^ ((1 / 2 : ℝ) - s.re) := by
  rw [bilateralHalfDensityCharacter]
  have hcast : ((p : ℝ) : ℂ) = (p : ℂ) := by push_cast; rfl
  rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp)]
  congr 1

/-- **The unitarity criterion**: the half-density character is unimodular iff `Re s = 1/2`. -/
theorem norm_bilateralHalfDensityCharacter_eq_one_iff {p : ℕ} (hp : 2 ≤ p)
    (s : ℂ) :
    ‖bilateralHalfDensityCharacter p s‖ = 1 ↔ s.re = 1 / 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hp
  rw [norm_bilateralHalfDensityCharacter hp0]
  constructor
  · intro h
    have h0 : (1 / 2 : ℝ) - s.re = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hlt' := (Real.rpow_lt_rpow_left_iff hp1).mpr hlt
        rw [Real.rpow_zero, h] at hlt'
        exact lt_irrefl 1 hlt'
      · have hgt' := (Real.rpow_lt_rpow_left_iff hp1).mpr hgt
        rw [Real.rpow_zero, h] at hgt'
        exact lt_irrefl 1 hgt'
    linarith
  · intro h
    rw [h]
    norm_num

/-- Norm of the jet family: `|e|^k · r^e` with `r = p^(1/2 - Re s)`. -/
theorem norm_bilateralJetFamily {p : ℕ} (hp : 0 < p) (s : ℂ) (k : ℕ) (e : ℤ) :
    ‖bilateralJetFamily p s k e‖ =
      (e.natAbs : ℝ) ^ k * ((p : ℝ) ^ ((1 / 2 : ℝ) - s.re)) ^ e := by
  rw [bilateralJetFamily, norm_mul, norm_zpow,
    norm_bilateralHalfDensityCharacter hp, norm_pow, Complex.norm_intCast]
  have habs : |((e : ℤ) : ℝ)| = (e.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [habs]

/-- **Moderation on the critical line**: every jet grade has polynomially bounded bilateral
coefficients. -/
theorem bilateralModerate_jetFamily_of_re_eq_half {p : ℕ} (hp : 0 < p) (k : ℕ)
    {s : ℂ} (h : s.re = 1 / 2) :
    bilateralModerate (bilateralJetFamily p s k) := by
  refine ⟨1, k, fun e => ?_⟩
  rw [norm_bilateralJetFamily hp, h, sub_self, Real.rpow_zero, one_zpow,
    mul_one, one_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith [le_refl (e.natAbs : ℝ)]) k

/-- **Off the critical line no jet grade is moderate**: one Fourier side grows geometrically
and beats every polynomial. -/
theorem not_bilateralModerate_jetFamily_of_re_ne_half {p : ℕ} (hp : 2 ≤ p)
    (k : ℕ) {s : ℂ} (h : s.re ≠ 1 / 2) :
    ¬ bilateralModerate (bilateralJetFamily p s k) := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hp
  set r : ℝ := (p : ℝ) ^ ((1 / 2 : ℝ) - s.re) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hne : (1 / 2 : ℝ) - s.re ≠ 0 := fun hh => h (by linarith)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- exponent negative: `r < 1`, the negative Fourier side grows like `(r⁻¹)^n`
    have hrlt : r < 1 := by
      have := (Real.rpow_lt_rpow_left_iff hp1).mpr hlt
      rwa [Real.rpow_zero] at this
    have hrinv : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hrlt
    apply not_bilateralModerate_of_growth hrinv (Or.inr rfl)
    intro n hn1
    have hval := norm_bilateralJetFamily hp0 s k ((-1) * (n : ℤ))
    rw [← hrdef] at hval
    have habs : ((((-1) * (n : ℤ)).natAbs : ℝ)) = (n : ℝ) := by
      simp
    rw [habs] at hval
    have hzpow : r ^ ((-1) * (n : ℤ)) = (r⁻¹) ^ n := by
      rw [neg_one_mul, zpow_neg, zpow_natCast, inv_pow]
    rw [hzpow] at hval
    rw [hval]
    have hn1' : (1 : ℝ) ≤ (n : ℝ) ^ k :=
      one_le_pow₀ (by exact_mod_cast hn1)
    have hrn : (0 : ℝ) < (r⁻¹) ^ n := pow_pos (inv_pos.mpr hr0) n
    nlinarith
  · -- exponent positive: `r > 1`, the positive Fourier side grows like `r^n`
    have hrgt : 1 < r := by
      have := (Real.rpow_lt_rpow_left_iff hp1).mpr hgt
      rwa [Real.rpow_zero] at this
    apply not_bilateralModerate_of_growth hrgt (Or.inl rfl)
    intro n hn1
    have hval := norm_bilateralJetFamily hp0 s k ((1 : ℤ) * (n : ℤ))
    rw [← hrdef] at hval
    have habs : ((((1 : ℤ) * (n : ℤ)).natAbs : ℝ)) = (n : ℝ) := by
      simp
    rw [habs] at hval
    have hzpow : r ^ ((1 : ℤ) * (n : ℤ)) = r ^ n := by
      rw [one_mul, zpow_natCast]
    rw [hzpow] at hval
    rw [hval]
    have hn1' : (1 : ℝ) ≤ (n : ℝ) ^ k :=
      one_le_pow₀ (by exact_mod_cast hn1)
    have hrn : (0 : ℝ) < r ^ n := pow_pos (lt_trans one_pos hrgt) n
    nlinarith

/-- **The moderation dichotomy**, packaged: at every grade, the bilateral jet family is
moderate iff `s` lies on the critical line. -/
theorem bilateralModerate_jetFamily_iff_re_eq_half {p : ℕ} (hp : 2 ≤ p) (k : ℕ)
    (s : ℂ) :
    bilateralModerate (bilateralJetFamily p s k) ↔ s.re = 1 / 2 := by
  constructor
  · intro hmod
    by_contra hne
    exact not_bilateralModerate_jetFamily_of_re_ne_half hp k hne hmod
  · exact bilateralModerate_jetFamily_of_re_eq_half
      (lt_of_lt_of_le two_pos hp) k

/-- On the critical line the character powers are the phase family of the point conormal at
angle `γ log p`: `λ_p(1/2 + iγ)^e = exp(-i e γ log p)`. -/
theorem bilateralJetFamily_zpow_on_line {p : ℕ} (hp : 0 < p) (γ : ℝ) (e : ℤ) :
    bilateralHalfDensityCharacter p (((1 / 2 : ℝ) : ℂ) + γ * Complex.I) ^ e =
      Complex.exp (-(((e : ℝ) * (γ * Real.log p) : ℝ) : ℂ) * Complex.I) := by
  have hp0 : ((p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (by exact_mod_cast hp : (0 : ℝ) < (p : ℝ))
  have hchar : bilateralHalfDensityCharacter p (((1 / 2 : ℝ) : ℂ) + γ * Complex.I) =
      Complex.exp (-((γ * Real.log p : ℝ) : ℂ) * Complex.I) := by
    rw [bilateralHalfDensityCharacter]
    have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.cpow_def_of_ne_zero hp0]
    rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    congr 1
    push_cast
    ring
  rw [hchar, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- **The selector (distributional off-unitary Koszul vanishing).**  A moderate bilateral
family which is a shift eigenfamily with an off-unitary character is identically zero: the
recursion propagates one geometric side, and moderation kills it. -/
theorem bilateral_shift_eigen_eq_zero_of_norm_ne_one {lam : ℂ}
    (hlam : ‖lam‖ ≠ 1) {c : ℤ → ℂ} (hmod : bilateralModerate c)
    (heig : ∀ e : ℤ, c (e - 1) = lam * c e) : c = 0 := by
  by_cases hlam0 : lam = 0
  · funext e
    have := heig (e + 1)
    rw [add_sub_cancel_right, hlam0, zero_mul] at this
    exact this
  · have hdown : ∀ n : ℕ, c (-(n : ℤ)) = lam ^ n * c 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have hstep := heig (-(n : ℤ))
          have harg : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [harg, ih] at hstep
          rw [hstep, pow_succ]
          ring
    have hup : ∀ n : ℕ, c (n : ℤ) = (lam⁻¹) ^ n * c 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have hstep := heig ((n + 1 : ℕ) : ℤ)
          have harg : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by push_cast; ring
          rw [harg, ih] at hstep
          have : c (((n + 1 : ℕ) : ℤ)) = lam⁻¹ * ((lam⁻¹) ^ n * c 0) := by
            apply mul_left_cancel₀ hlam0
            rw [← hstep, mul_inv_cancel_left₀ hlam0]
          rw [this, pow_succ]
          ring
    have hc0 : c 0 = 0 := by
      by_contra hc0ne
      have hc0pos : 0 < ‖c 0‖ := norm_pos_iff.mpr hc0ne
      rcases lt_or_gt_of_ne hlam with hlt | hgt
      · -- ‖lam‖ < 1: the positive side grows with ratio ‖lam‖⁻¹ > 1
        have hlam0' : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
        have hrinv : 1 < ‖lam‖⁻¹ := (one_lt_inv₀ hlam0').mpr hlt
        obtain ⟨C, m, hC⟩ := hmod
        obtain ⟨n, hn1, hbig⟩ :=
          exists_one_le_and_pow_gt_poly hrinv (C / ‖c 0‖) m
        have hval : ‖c (n : ℤ)‖ = (‖lam‖⁻¹) ^ n * ‖c 0‖ := by
          rw [hup n, norm_mul, norm_pow, norm_inv]
        have hle := hC (n : ℤ)
        rw [hval] at hle
        have habs : (((n : ℤ)).natAbs : ℝ) = (n : ℝ) := by simp
        rw [habs] at hle
        have : (‖lam‖⁻¹) ^ n * ‖c 0‖ ≤ C * (1 + (n : ℝ)) ^ m := hle
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0pos] at hbig
        linarith
      · -- ‖lam‖ > 1: the negative side grows with ratio ‖lam‖ > 1
        obtain ⟨C, m, hC⟩ := hmod
        obtain ⟨n, hn1, hbig⟩ :=
          exists_one_le_and_pow_gt_poly hgt (C / ‖c 0‖) m
        have hval : ‖c (-(n : ℤ))‖ = ‖lam‖ ^ n * ‖c 0‖ := by
          rw [hdown n, norm_mul, norm_pow]
        have hle := hC (-(n : ℤ))
        rw [hval] at hle
        have habs : ((-(n : ℤ)).natAbs : ℝ) = (n : ℝ) := by simp
        rw [habs] at hle
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0pos] at hbig
        linarith
    funext e
    induction e using Int.induction_on with
    | zero => exact hc0
    | succ n ih =>
        have := hup (n + 1)
        rw [hc0, mul_zero] at this
        exact_mod_cast this
    | pred n ih =>
        have := hdown (n + 1)
        rw [hc0, mul_zero] at this
        have harg : (-((n + 1 : ℕ) : ℤ)) = (-(n : ℤ) - 1) := by push_cast; ring
        rw [harg] at this
        exact this

/-- **The moderation selector for the prime half-density character**: a nonzero moderate
bilateral shift eigenfamily with character `λ_p(s)` forces `Re s = 1/2`. -/
theorem re_eq_half_of_moderate_bilateral_eigen {p : ℕ} (hp : 2 ≤ p) {s : ℂ}
    {c : ℤ → ℂ} (hc : c ≠ 0) (hmod : bilateralModerate c)
    (heig : ∀ e : ℤ, c (e - 1) = bilateralHalfDensityCharacter p s * c e) :
    s.re = 1 / 2 := by
  by_contra hne
  apply hc
  apply bilateral_shift_eigen_eq_zero_of_norm_ne_one _ hmod heig
  intro h1
  exact hne ((norm_bilateralHalfDensityCharacter_eq_one_iff hp s).mp h1)

end RHTower
