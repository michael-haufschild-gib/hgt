import GaloisForLFunctions.RigidArithmeticOfCuts.TheZeroOfMaximalAngle
import GaloisForLFunctions.RigidArithmeticOfCuts.ExponentialTypeCannotDecayOnARay
import GaloisForLFunctions.RHTower.ResonanceClosedForm
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.RHTower.ZetaTypicalHeightLogDeriv
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.RHLadderTheory
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Rotated relations need coefficients of the size of `Q`

For which class of coefficients is a rotated relation `T Q = A Q(ϑ·) + B Q(ϑ̄·)` neither vacuous nor refuted? This module fixes the
boundary from below.

**Theorem** (`rotated_relation_trivial`). If `T, A, B` are entire with `‖f(w)‖ ≤ C exp(C √‖w‖)`, the relation forces `T = A = B = 0`.

The class contains polynomials, rational coefficients cleared of denominators and all functions of order below `½`. It stops
just below `Q` itself: `‖Q(−x)‖` grows like `exp(½ √x log √x)`, and with `a = b = Q` the relation holds identically
(`self_coefficient_rotated_relation`). So a non-vacuous rotated relation must have coefficients of the exact growth of `Q`, up to the
factor `log` in the exponent.

**The mechanism** (`exists_norm_squaredXi_rot_le`). On the negative axis `Q` dominates every rotation of itself: for `ϑ ≠ 1`,

`‖Q(ϑ(−r²))‖ ≤ exp(−K r) ‖Q(−r²)‖` for every `K`, for all large `r`.

Indeed `Q(−r²) = ξ(½ + r)`, and `Q(ϑ(−r²)) = ξ(½ + rω)` with `ω² = ϑ`, `Re ω < 1`. The Gamma factor sets the size, and `Γ(a)/Γ(b) ≤ 4/⌊b − a⌋!` beats every exponential. This is
Gamma speed as dominance.

Thus `T(−r²)` decays faster than every exponential in `r`, and an entire function of exponential type in `z = ir` cannot do that
(`eq_zero_of_decaysOnRay`).
-/

open Complex Filter Topology RHTower

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### `ξ` through its Gamma factor -/

private lemma xi_eq_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hre : 0 < s.re) :
    _root_.RHTower.xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  rw [_root_.RHTower.xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp

private lemma norm_Gammaℝ_le {s : ℂ} (hre : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-(s.re / 2)) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : ‖((Real.pi : ℝ) : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-(s.re / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]
    congr 1
    simp
    ring
  have hre2 : (s / 2).re = s.re / 2 := by simp
  have h2 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have := _root_.RHTower.norm_Gamma_le_Gamma_re (z := s / 2) (by rw [hre2]; linarith)
    rwa [hre2] at this
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

private lemma norm_Gammaℝ_ofReal {σ : ℝ} (hσ : 0 < σ) :
    ‖Complex.Gammaℝ (σ : ℂ)‖ = Real.pi ^ (-(σ / 2)) * Real.Gamma (σ / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : ‖((Real.pi : ℝ) : ℂ) ^ (-(σ : ℂ) / 2)‖ = Real.pi ^ (-(σ / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]
    congr 1
    simp
    ring
  have h2 : Complex.Gamma ((σ : ℂ) / 2) = ((Real.Gamma (σ / 2) : ℝ) : ℂ) := by
    have : ((σ : ℂ) / 2) = ((σ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.Gamma_ofReal]
  rw [h1, h2, Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le]

/-- The Gamma recursion with its factorial gain. -/
private lemma Gamma_mul_factorial_le {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Real.Gamma a * a * (m.factorial : ℝ) ≤ Real.Gamma (a + m + 1) := by
  have hG := Real.Gamma_pos_of_pos ha
  induction m with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.cast_zero, add_zero]
    rw [Real.Gamma_add_one ha.ne']
    linarith [mul_comm a (Real.Gamma a)]
  | succ m ih =>
    have hpos : 0 < a + m + 1 := by positivity
    have heq : a + ((m + 1 : ℕ) : ℝ) + 1 = (a + m + 1) + 1 := by
      push_cast
      ring
    rw [heq, Real.Gamma_add_one hpos.ne', Nat.factorial_succ]
    push_cast
    have h1 : ((m : ℝ) + 1) ≤ a + m + 1 := by linarith
    have hnn : 0 ≤ Real.Gamma a * a * (m.factorial : ℝ) := by positivity
    calc Real.Gamma a * a * (((m : ℝ) + 1) * (m.factorial : ℝ))
        = ((m : ℝ) + 1) * (Real.Gamma a * a * (m.factorial : ℝ)) := by ring
      _ ≤ (a + m + 1) * Real.Gamma (a + m + 1) :=
          mul_le_mul h1 ih hnn hpos.le

/-! ### Dominance on the negative axis -/

/-- `Q(−(r ω)²) = ξ(½ + r ω)`. -/
theorem squaredXi_neg_sq (r ω : ℂ) : squaredXi (-(r * ω) ^ 2) = _root_.RHTower.xi (1 / 2 + r * ω) := by
  have h1 : -(r * ω) ^ 2 = (r * ω * I) ^ 2 := by
    rw [mul_pow (r * ω) I, Complex.I_sq]
    ring
  rw [h1, squaredXi_sq, ← XiC_even, XiC]
  congr 1
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (-(r * ω)) * hI

/-- A factorial beats every exponential of its index. -/
private lemma exists_exp_le_factorial {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r → Real.exp (B * r) ≤ ((⌊δ * r⌋₊ - 1).factorial : ℝ) := by
  set R : ℝ := Real.exp (2 * B / δ) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop R
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)))
  refine ⟨((m₀ : ℝ) + 4) / δ, by positivity, fun r hr => ?_⟩
  have hδr : (m₀ : ℝ) + 4 ≤ δ * r := by
    rw [div_le_iff₀ hδ] at hr
    linarith
  have hfl : (m₀ : ℝ) + 3 < (⌊δ * r⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one (δ * r)
    linarith
  have hflN : m₀ + 3 < ⌊δ * r⌋₊ := by exact_mod_cast hfl
  set m := ⌊δ * r⌋₊ - 1 with hm
  have hmm₀ : m₀ ≤ m := by omega
  have hfac : R ^ m ≤ (m.factorial : ℝ) := by
    have h1 := hm₀ m hmm₀
    rw [div_lt_one (by positivity)] at h1
    exact h1.le
  refine le_trans ?_ hfac
  rw [hR, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  -- `m ≥ δ r − 2 ≥ δ r / 2`.
  have hmR : δ * r / 2 ≤ (m : ℝ) := by
    have hcast : ((m : ℕ) : ℝ) = (⌊δ * r⌋₊ : ℝ) - 1 := by
      rw [hm, Nat.cast_sub (by omega)]
      simp
    rw [hcast]
    have h1 := Nat.lt_floor_add_one (δ * r)
    have : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
    linarith
  have hval : B * r = (δ * r / 2) * (2 * B / δ) := by
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_right hmR (by positivity)

/-- **`Q` dominates its rotations on the negative axis, faster than every exponential.** -/
theorem exists_norm_squaredXi_rot_le {ϑ : ℂ} (hn : ‖ϑ‖ = 1) (h1 : ϑ ≠ 1) (K : ℝ) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      ‖squaredXi (ϑ * -((r : ℂ) ^ 2))‖ ≤ Real.exp (-(K * r)) * ‖squaredXi (-((r : ℂ) ^ 2))‖ := by
  set θ := Complex.arg ϑ with hθ
  set ω : ℂ := Complex.exp (((θ / 2 : ℝ) : ℂ) * I) with hω
  have hωsq : ω ^ 2 = ϑ := by
    have h2 : ω ^ 2 = Complex.exp ((θ : ℂ) * I) := by
      rw [hω, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h3 := Complex.norm_mul_exp_arg_mul_I ϑ
    rw [hn] at h3
    simp only [Complex.ofReal_one, one_mul] at h3
    rw [h2]
    exact h3
  have hωnorm : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set c : ℝ := Real.cos (θ / 2) with hc
  have hωre : ω.re = c := Complex.exp_ofReal_mul_I_re _
  have hωim : ω.im = Real.sin (θ / 2) := Complex.exp_ofReal_mul_I_im _
  have hθ1 := Complex.neg_pi_lt_arg ϑ
  have hθ2 := Complex.arg_le_pi ϑ
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hθne : θ ≠ 0 := by
    intro h0
    apply h1
    have h3 := Complex.norm_mul_exp_arg_mul_I ϑ
    rw [hn, ← hθ, h0] at h3
    simpa using h3.symm
  have hc1 : c < 1 := by
    have hle := Real.cos_le_one (θ / 2)
    refine lt_of_le_of_ne hle fun heq => hθne ?_
    obtain ⟨n, hn'⟩ := (Real.cos_eq_one_iff (θ / 2)).mp heq
    have hbound : |θ / 2| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> linarith [Real.pi_pos]
    have hn0 : n = 0 := by
      by_contra hne
      have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      rw [← hn', abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos] at hbound
      have h5 : 0 < 2 * Real.pi := by positivity
      nlinarith
    rw [hn0] at hn'
    simp at hn'
    linarith
  set δ : ℝ := (1 - c) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hlogπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set B : ℝ := |K| + δ * Real.log Real.pi + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨r₁, hr₁0, hfac⟩ := exists_exp_le_factorial hB0 hδ0
  -- Height at which the abscissa of `½ + r ω` is either `½` or at least `2`.
  set r₀ : ℝ := max (max r₁ 400) (max (4 / δ) (3 / (2 * c))) with hr₀
  have hr400 : (400 : ℝ) ≤ r₀ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨r₀, by linarith, fun r hr => ?_⟩
  have hr1 : r₁ ≤ r := ((le_max_left _ _).trans (le_max_left _ _)).trans hr
  have hr4 : 400 ≤ r := hr400.trans hr
  have hr0 : 0 < r := by linarith
  have hδr : 4 ≤ δ * r := by
    have h2 : 4 / δ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
    rwa [div_le_iff₀ hδ0, mul_comm] at h2
  have hval1 : squaredXi (ϑ * -((r : ℂ) ^ 2)) = _root_.RHTower.xi (1 / 2 + (r : ℂ) * ω) := by
    rw [← squaredXi_neg_sq, mul_pow, hωsq]
    congr 1
    ring
  have hval2 : squaredXi (-((r : ℂ) ^ 2)) = _root_.RHTower.xi (1 / 2 + (r : ℂ)) := by
    have := squaredXi_neg_sq (r : ℂ) 1
    simpa using this
  rw [hval1, hval2]
  -- The two points.
  set s₁ : ℂ := 1 / 2 + (r : ℂ) * ω with hs₁
  set σ₂ : ℝ := 1 / 2 + r with hσ₂
  have hs₂ : (1 / 2 + (r : ℂ)) = (σ₂ : ℂ) := by
    rw [hσ₂]
    push_cast
    ring
  have hσ₂2 : 2 ≤ σ₂ := by rw [hσ₂]; linarith
  have hs₁re : s₁.re = 1 / 2 + r * c := by
    rw [hs₁]
    simp [hωre]
  have hs₁im : s₁.im = r * Real.sin (θ / 2) := by
    rw [hs₁]
    simp [hωim]
  have hs₁pos : 0 < s₁.re := by
    rw [hs₁re]
    positivity
  have hs₁norm : ‖s₁‖ ≤ σ₂ := by
    rw [hs₁, hσ₂]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hωnorm, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    norm_num
  have hs₁norm2 : ‖s₁ - 1‖ ≤ σ₂ := by
    have h2 : s₁ - 1 = -(1 / 2) + (r : ℂ) * ω := by
      rw [hs₁]
      ring
    rw [h2, hσ₂]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hωnorm, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    norm_num
  have hs₁ne0 : s₁ ≠ 0 := fun h => by
    rw [h] at hs₁pos
    simp at hs₁pos
  -- `ζ` at the rotated point has polynomial size.
  have hζ : ‖riemannZeta s₁‖ ≤ 2 + 4 * r := by
    by_cases hc00 : c = 0
    · have hsin : |Real.sin (θ / 2)| = 1 := by
        have h2 := Real.sin_sq_add_cos_sq (θ / 2)
        rw [← hc, hc00] at h2
        have h3 : Real.sin (θ / 2) * Real.sin (θ / 2) = 1 := by nlinarith
        rcases mul_self_eq_one_iff.mp h3 with h | h <;> simp [h]
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = r * Real.sin (θ / 2) := ⟨_, rfl⟩
      rw [← ht] at hs₁im
      have hsplit : s₁ = (((1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I := by
        apply Complex.ext
        · rw [hs₁re, hc00]
          simp
        · rw [hs₁im]
          simp
      have htabs : |t| = r := by
        rw [ht, abs_mul, hsin, mul_one, abs_of_pos hr0]
      have h2 := _root_.RHTower.norm_riemannZeta_le_of_re_pos (σ := 1 / 2) (t := t)
        (by norm_num) (by norm_num) (by rw [htabs]; linarith)
      rw [htabs, ← hsplit] at h2
      have h3 : 2 + 2 * r / (1 / 2) = 2 + 4 * r := by ring
      rwa [h3] at h2
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc00)
      have h2 : 3 / (2 * c) ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hr
      rw [div_le_iff₀ (by positivity)] at h2
      have h3 : 2 ≤ s₁.re := by
        rw [hs₁re]
        linarith
      have h4 := (_root_.RHTower.norm_riemannZeta_bounds_of_two_le_re h3).2
      linarith
  have hs₁ne1 : s₁ ≠ 1 := by
    intro h
    have hre1 : s₁.re = 1 := by rw [h]; simp
    rw [hs₁re] at hre1
    by_cases hc00 : c = 0
    · rw [hc00] at hre1
      norm_num at hre1
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc00)
      have h2 : 3 / (2 * c) ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hr
      rw [div_le_iff₀ (by positivity)] at h2
      linarith
  -- The Gamma factors.
  set a : ℝ := s₁.re / 2 with ha
  set b : ℝ := σ₂ / 2 with hb
  have haval : a = 1 / 4 + r * c / 2 := by
    rw [ha, hs₁re]
    ring
  have hbval : b = 1 / 4 + r / 2 := by
    rw [hb, hσ₂]
    ring
  have ha4 : 1 / 4 ≤ a := by
    rw [haval]
    have : 0 ≤ r * c / 2 := by positivity
    linarith
  have ha0 : 0 < a := by linarith
  have hb2 : 2 ≤ b := by
    rw [hbval]
    linarith
  have hgap : b - a = δ * r := by
    rw [haval, hbval, hδ]
    ring
  set n := ⌊δ * r⌋₊ with hn'
  have hn4 : 4 ≤ n := Nat.le_floor (by exact_mod_cast hδr)
  have hnle : (n : ℝ) ≤ δ * r := Nat.floor_le (by positivity)
  set m := n - 1 with hm
  have hmn : ((m : ℝ) + 1) = n := by
    rw [hm, Nat.cast_sub (by omega)]
    simp
  have hGamma : Real.Gamma a * a * (m.factorial : ℝ) ≤ Real.Gamma b := by
    refine (Gamma_mul_factorial_le ha0 m).trans ?_
    have h2 : a + m + 1 = a + n := by linarith
    rw [h2]
    refine Real.Gamma_strictMonoOn_Ici.monotoneOn ?_ (Set.mem_Ici.mpr hb2) (by linarith)
    rw [Set.mem_Ici]
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hGa := Real.Gamma_pos_of_pos ha0
  have hGb := Real.Gamma_pos_of_pos (by linarith : 0 < b)
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hGratio : Real.Gamma a * (m.factorial : ℝ) ≤ 4 * Real.Gamma b := by
    have h2 : Real.Gamma a * (1 / 4) * (m.factorial : ℝ) ≤ Real.Gamma a * a * (m.factorial : ℝ) := by
      gcongr
    linarith
  -- The numerator.
  have hπ := Real.pi_pos
  set Pb : ℝ := Real.pi ^ (-b) with hPb
  have hPbpos : 0 < Pb := Real.rpow_pos_of_pos hπ _
  set Eπ : ℝ := Real.exp (δ * r * Real.log Real.pi) with hEπ
  have hPa : Real.pi ^ (-a) = Pb * Eπ := by
    have h2 : -a = -b + δ * r := by linarith
    rw [h2, Real.rpow_add hπ, hPb, hEπ, Real.rpow_def_of_pos hπ (δ * r)]
    congr 2
    ring
  have hnum : ‖_root_.RHTower.xi s₁‖ ≤ (σ₂ ^ 2 / 2) * ((Pb * Eπ) * Real.Gamma a) * (2 + 4 * r) := by
    rw [xi_eq_mul hs₁ne0 hs₁ne1 hs₁pos, norm_mul, norm_mul, norm_div, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hG := norm_Gammaℝ_le hs₁pos
    rw [hPa] at hG
    have h3 : ‖s₁‖ * ‖s₁ - 1‖ / 2 ≤ σ₂ ^ 2 / 2 := by
      have := mul_le_mul hs₁norm hs₁norm2 (norm_nonneg _) (by linarith)
      rw [sq]
      linarith
    have hnn : 0 ≤ (Pb * Eπ) * Real.Gamma a := by positivity
    calc _ ≤ (σ₂ ^ 2 / 2) * (((Pb * Eπ) * Real.Gamma a) * (2 + 4 * r)) :=
          mul_le_mul h3 (mul_le_mul hG hζ (norm_nonneg _) hnn) (by positivity) (by positivity)
      _ = _ := by ring
  -- The denominator.
  have hσne0 : (σ₂ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ₂ ≠ 0)
  have hσne1 : (σ₂ : ℂ) ≠ 1 := by exact_mod_cast (by linarith : σ₂ ≠ 1)
  have hσre : ((σ₂ : ℂ)).re = σ₂ := by simp
  have hden : (σ₂ ^ 2 / 12) * (Pb * Real.Gamma b) ≤ ‖_root_.RHTower.xi (σ₂ : ℂ)‖ := by
    rw [xi_eq_mul hσne0 hσne1 (by rw [hσre]; linarith), norm_mul, norm_mul, norm_div, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, norm_Gammaℝ_ofReal (by linarith)]
    have hz3 := (_root_.RHTower.norm_riemannZeta_bounds_of_two_le_re (s := (σ₂ : ℂ)) (by rw [hσre]; exact hσ₂2)).1
    have hnorm1 : ‖(σ₂ : ℂ)‖ = σ₂ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hnorm2 : ‖(σ₂ : ℂ) - 1‖ = σ₂ - 1 := by
      have : (σ₂ : ℂ) - 1 = ((σ₂ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hnorm1, hnorm2]
    have h3 : σ₂ ^ 2 / 4 ≤ σ₂ * (σ₂ - 1) / 2 := by nlinarith
    have hnn : 0 ≤ Pb * Real.Gamma b := by positivity
    calc (σ₂ ^ 2 / 12) * (Pb * Real.Gamma b) = (σ₂ ^ 2 / 4) * ((Pb * Real.Gamma b) * (1 / 3)) := by ring
      _ ≤ (σ₂ * (σ₂ - 1) / 2) * ((Pb * Real.Gamma b) * ‖riemannZeta (σ₂ : ℂ)‖) :=
          mul_le_mul h3 (mul_le_mul_of_nonneg_left hz3 hnn) (by positivity) (by nlinarith)
  -- The factorial beats everything.
  have hfacbig := hfac r hr1
  rw [← hn', ← hm] at hfacbig
  have hpoly : 24 * (2 + 4 * r) ≤ Real.exp r := by
    have h2 : (1 + r / 2) ≤ Real.exp (r / 2) := by linarith [Real.add_one_le_exp (r / 2)]
    have h3 : (1 + r / 2) ^ 2 ≤ Real.exp r := by
      have h4 : Real.exp r = Real.exp (r / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h4]
      exact pow_le_pow_left₀ (by linarith) h2 2
    nlinarith
  have hbig : 24 * (2 + 4 * r) * Eπ * Real.exp (K * r) ≤ (m.factorial : ℝ) := by
    refine le_trans ?_ hfacbig
    have h2 : Eπ * Real.exp (K * r) = Real.exp (δ * r * Real.log Real.pi + K * r) := by
      rw [hEπ, ← Real.exp_add]
    rw [mul_assoc, h2]
    calc _ ≤ Real.exp r * Real.exp (δ * r * Real.log Real.pi + K * r) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = Real.exp (r + (δ * r * Real.log Real.pi + K * r)) := by rw [Real.exp_add]
      _ ≤ _ := by
          refine Real.exp_le_exp.mpr ?_
          have hK : K * r ≤ |K| * r := mul_le_mul_of_nonneg_right (le_abs_self K) hr0.le
          rw [hB]
          nlinarith
  -- Assembly.
  rw [hs₂]
  refine hnum.trans (le_trans ?_ (mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le))
  have hE : Real.exp (-(K * r)) * Real.exp (K * r) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmain : 24 * (2 + 4 * r) * Eπ * (Real.Gamma a) * (m.factorial : ℝ) * Real.exp (K * r) ≤
      (m.factorial : ℝ) * (24 * (2 + 4 * r) * Eπ * Real.exp (K * r)) * Real.Gamma a := by
    apply le_of_eq
    ring
  have hkey : 24 * (2 + 4 * r) * Eπ * Real.Gamma a ≤ Real.exp (-(K * r)) * (24 * Real.Gamma b) := by
    have h2 : 24 * (2 + 4 * r) * Eπ * Real.exp (K * r) * Real.Gamma a ≤
        (m.factorial : ℝ) * Real.Gamma a := mul_le_mul_of_nonneg_right hbig hGa.le
    have h3 : (m.factorial : ℝ) * Real.Gamma a ≤ 4 * Real.Gamma b := by linarith
    have h4 : 24 * (2 + 4 * r) * Eπ * Real.Gamma a =
        Real.exp (-(K * r)) * (24 * (2 + 4 * r) * Eπ * Real.exp (K * r) * Real.Gamma a) := by
      calc _ = (Real.exp (-(K * r)) * Real.exp (K * r)) * (24 * (2 + 4 * r) * Eπ * Real.Gamma a) := by
            rw [hE, one_mul]
        _ = _ := by ring
    rw [h4]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    nlinarith
  have hfinal : (σ₂ ^ 2 / 2) * ((Pb * Eπ) * Real.Gamma a) * (2 + 4 * r) =
      (σ₂ ^ 2 / 48) * Pb * (24 * (2 + 4 * r) * Eπ * Real.Gamma a) := by ring
  rw [hfinal]
  calc (σ₂ ^ 2 / 48) * Pb * (24 * (2 + 4 * r) * Eπ * Real.Gamma a)
      ≤ (σ₂ ^ 2 / 48) * Pb * (Real.exp (-(K * r)) * (24 * Real.Gamma b)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-! ### The boundary -/

/-- Growth at most `exp(C √|w|)`: order at most `½`, of finite type. -/
def HasSqrtGrowth (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖f w‖ ≤ C * Real.exp (C * Real.sqrt ‖w‖)

theorem HasSqrtGrowth.comp_unit {f : ℂ → ℂ} (hf : HasSqrtGrowth f) {u : ℂ} (hu : ‖u‖ = 1) :
    HasSqrtGrowth fun w => f (u * w) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C, hC, fun w => ?_⟩
  have := h (u * w)
  rwa [norm_mul, hu, one_mul] at this

theorem HasSqrtGrowth.neg {f : ℂ → ℂ} (hf : HasSqrtGrowth f) : HasSqrtGrowth fun w => -f w := by
  obtain ⟨C, hC, h⟩ := hf
  exact ⟨C, hC, fun w => by rw [norm_neg]; exact h w⟩

theorem hasSqrtGrowth_zero : HasSqrtGrowth fun _ => 0 :=
  ⟨0, le_rfl, fun w => by simp⟩

private lemma HasSqrtGrowth.le_max {f : ℂ → ℂ} {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D)
    (h : ∀ w, ‖f w‖ ≤ C * Real.exp (C * Real.sqrt ‖w‖)) (w : ℂ) :
    ‖f w‖ ≤ D * Real.exp (D * Real.sqrt ‖w‖) := by
  refine (h w).trans (mul_le_mul hCD ?_ (Real.exp_pos _).le (hC.trans hCD))
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _))

/-- One coefficient of a relation with two rotations vanishes. -/
theorem eq_zero_of_two_rotations {T A B : ℂ → ℂ} (hT : Differentiable ℂ T) (hTg : HasSqrtGrowth T)
    (hAg : HasSqrtGrowth A) (hBg : HasSqrtGrowth B) {ϑ₁ ϑ₂ : ℂ} (hn₁ : ‖ϑ₁‖ = 1) (hn₂ : ‖ϑ₂‖ = 1)
    (h₁ : ϑ₁ ≠ 1) (h₂ : ϑ₂ ≠ 1)
    (hrel : ∀ w, T w * squaredXi w = A w * squaredXi (ϑ₁ * w) + B w * squaredXi (ϑ₂ * w)) : T = 0 := by
  obtain ⟨C₁, hC₁, hT'⟩ := hTg
  obtain ⟨C₂, hC₂, hA'⟩ := hAg
  obtain ⟨C₃, hC₃, hB'⟩ := hBg
  set C : ℝ := max (max C₁ C₂) C₃ with hC
  have hC₁le : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC₂le : C₂ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC₃le : C₃ ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := hC₁.trans hC₁le
  have hTb := HasSqrtGrowth.le_max hC₁ hC₁le hT'
  have hAb := HasSqrtGrowth.le_max hC₂ hC₂le hA'
  have hBb := HasSqrtGrowth.le_max hC₃ hC₃le hB'
  set f : ℂ → ℂ := fun z => T (-(z ^ 2)) with hf
  have hfd : Differentiable ℂ f := hT.comp (by fun_prop)
  have hsqrt : ∀ z : ℂ, Real.sqrt ‖-(z ^ 2)‖ = ‖z‖ := fun z => by
    rw [norm_neg, norm_pow, Real.sqrt_sq (norm_nonneg z)]
  have hfg : ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖) := fun z => by
    have := hTb (-(z ^ 2))
    rwa [hsqrt] at this
  have hfe : ∀ z, f (-z) = f z := fun z => by simp [hf]
  have hdec : DecaysOnRay f := by
    intro K
    set K₁ : ℝ := K + C with hK₁
    obtain ⟨r₁, hr₁, h1⟩ := exists_norm_squaredXi_rot_le hn₁ h₁ K₁
    obtain ⟨r₂, hr₂, h2⟩ := exists_norm_squaredXi_rot_le hn₂ h₂ K₁
    set r₀ : ℝ := max (max r₁ r₂) 1 with hr₀
    have hr₀1 : 1 ≤ r₀ := le_max_right _ _
    refine ⟨max (2 * C) (C * Real.exp ((C + |K|) * r₀)), fun r hr => ?_⟩
    by_cases hlarge : r₀ ≤ r
    · have hr1 : r₁ ≤ r := ((le_max_left _ _).trans (le_max_left _ _)).trans hlarge
      have hr2 : r₂ ≤ r := ((le_max_right _ _).trans (le_max_left _ _)).trans hlarge
      have hrge : 1 ≤ r := hr₀1.trans hlarge
      set w : ℂ := -((r : ℂ) ^ 2) with hw
      have hnw : Real.sqrt ‖w‖ = r := by
        rw [hw, hsqrt, Complex.norm_real, Real.norm_of_nonneg hr]
      have hQne : squaredXi w ≠ 0 := by
        have h3 := squaredXi_neg_sq (r : ℂ) 1
        rw [mul_one] at h3
        rw [hw, h3]
        refine _root_.RHTower.xi_ne_zero_of_one_le_re ?_
        simp
        linarith
      have hQpos : 0 < ‖squaredXi w‖ := norm_pos_iff.mpr hQne
      have hrelw := hrel w
      have hnorm : ‖T w‖ * ‖squaredXi w‖ ≤
          (C * Real.exp (C * r)) * (Real.exp (-(K₁ * r)) * ‖squaredXi w‖) +
            (C * Real.exp (C * r)) * (Real.exp (-(K₁ * r)) * ‖squaredXi w‖) := by
        rw [← norm_mul, hrelw]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]
          have hb := hAb w
          rw [hnw] at hb
          exact mul_le_mul hb (h1 r hr1) (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          have hb := hBb w
          rw [hnw] at hb
          exact mul_le_mul hb (h2 r hr2) (norm_nonneg _) (by positivity)
      have hval : Real.exp (C * r) * Real.exp (-(K₁ * r)) = Real.exp (-(K * r)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hK₁]
        ring
      have hcancel : ‖T w‖ * ‖squaredXi w‖ ≤ (2 * C * Real.exp (-(K * r))) * ‖squaredXi w‖ := by
        calc _ ≤ _ := hnorm
          _ = (2 * C * (Real.exp (C * r) * Real.exp (-(K₁ * r)))) * ‖squaredXi w‖ := by ring
          _ = _ := by rw [hval]
      have hle := le_of_mul_le_mul_right hcancel hQpos
      exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · push Not at hlarge
      have hfr := hfg (r : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hr] at hfr
      refine hfr.trans ?_
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC0
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h3 : C * r ≤ C * r₀ := mul_le_mul_of_nonneg_left hlarge.le hC0
      have h4 : -(K * r) ≥ -(|K| * r₀) := by
        have h5 : K * r ≤ |K| * r := mul_le_mul_of_nonneg_right (le_abs_self K) hr
        have h6 : |K| * r ≤ |K| * r₀ := mul_le_mul_of_nonneg_left hlarge.le (abs_nonneg K)
        linarith
      nlinarith
  have hzero := eq_zero_of_decaysOnRay hfd hC0 hfg hfe hdec
  funext w
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-w) (n := 2) (by norm_num)
  have h3 : f z = T w := by
    simp only [hf]
    rw [hz, neg_neg]
  rw [← h3, hzero]
  rfl

/-- **Rotated relations need coefficients of the size of `Q`.** A relation
`T Q = A Q(ϑ·) + B Q(ϑ̄·)` with `T, A, B` entire of growth `exp(C √|w|)` and `ϑ` a unit off the real axis is trivial. -/
theorem rotated_relation_trivial {T A B : ℂ → ℂ} (hT : Differentiable ℂ T) (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hTg : HasSqrtGrowth T) (hAg : HasSqrtGrowth A) (hBg : HasSqrtGrowth B)
    {ϑ : ℂ} (hn : ‖ϑ‖ = 1) (him : ϑ.im ≠ 0)
    (hrel : ∀ w, T w * squaredXi w = A w * squaredXi (ϑ * w) + B w * squaredXi (star ϑ * w)) :
    T = 0 ∧ A = 0 ∧ B = 0 := by
  have hns : ‖star ϑ‖ = 1 := by rwa [norm_star]
  have hne1 : ϑ ≠ 1 := fun h => him (by rw [h]; simp)
  have hnes : star ϑ ≠ 1 := fun h => hne1 (by simpa using congrArg star h)
  have hTz := eq_zero_of_two_rotations hT hTg hAg hBg hn hns hne1 hnes hrel
  have hrel0 : ∀ w, A w * squaredXi (ϑ * w) + B w * squaredXi (star ϑ * w) = 0 := fun w => by
    rw [← hrel w, hTz]
    simp
  have hprod : ϑ * star ϑ = 1 := by
    have h1 : ϑ * star ϑ = ((‖ϑ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, hn]
    simp
  have hprod' : star ϑ * ϑ = 1 := by rw [mul_comm, hprod]
  have hsqne : ∀ u : ℂ, ‖u‖ = 1 → u.im ≠ 0 → u ^ 2 ≠ 1 := by
    intro u _ hu h
    rw [sq] at h
    rcases mul_self_eq_one_iff.mp h with h1 | h1 <;> exact hu (by rw [h1]; simp)
  have himst : (star ϑ).im ≠ 0 := by
    simpa [Complex.star_def] using him
  have hnsq : ‖star ϑ ^ 2‖ = 1 := by rw [norm_pow, hns, one_pow]
  have hnsq' : ‖ϑ ^ 2‖ = 1 := by rw [norm_pow, hn, one_pow]
  -- The coefficient `A`, at `w ↦ ϑ̄ w`.
  have hAz : (fun w => A (star ϑ * w)) = 0 := by
    refine eq_zero_of_two_rotations (B := fun _ => 0) (hA.comp (differentiable_id.const_mul _))
      (hAg.comp_unit hns) (hBg.comp_unit hns).neg hasSqrtGrowth_zero hnsq hnsq
      (hsqne _ hns himst) (hsqne _ hns himst) (fun w => ?_)
    have h1 := hrel0 (star ϑ * w)
    have h2 : ϑ * (star ϑ * w) = w := by rw [← mul_assoc, hprod, one_mul]
    have h3 : star ϑ * (star ϑ * w) = star ϑ ^ 2 * w := by ring
    rw [h2, h3] at h1
    linear_combination h1
  -- The coefficient `B`, at `w ↦ ϑ w`.
  have hBz : (fun w => B (ϑ * w)) = 0 := by
    refine eq_zero_of_two_rotations (B := fun _ => 0) (hB.comp (differentiable_id.const_mul _))
      (hBg.comp_unit hn) (hAg.comp_unit hn).neg hasSqrtGrowth_zero hnsq' hnsq'
      (hsqne _ hn him) (hsqne _ hn him) (fun w => ?_)
    have h1 := hrel0 (ϑ * w)
    have h2 : star ϑ * (ϑ * w) = w := by rw [← mul_assoc, hprod', one_mul]
    have h3 : ϑ * (ϑ * w) = ϑ ^ 2 * w := by ring
    rw [h2, h3] at h1
    linear_combination h1
  refine ⟨hTz, ?_, ?_⟩
  · funext w
    have h1 := congrFun hAz (ϑ * w)
    simpa [← mul_assoc, hprod'] using h1
  · funext w
    have h1 := congrFun hBz (star ϑ * w)
    simpa [← mul_assoc, hprod] using h1

end GaloisForLFunctions.RigidArithmeticOfCuts
