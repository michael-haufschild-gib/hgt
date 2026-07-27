import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact modulus of the Gamma function on vertical lines

On the two base lines `Re z = 1/2` and `Re z = 1` the reflection formula
`Γ(z) Γ(1-z) = π / sin (π z)` computes the modulus of `Γ` exactly, because the reflected point is
the complex conjugate:

```
‖Γ(1/2 + i t)‖² = π / cosh (π t),        ‖Γ(1 + i t)‖² = π |t| / |sinh (π t)|.
```

Together with `‖Γ(z+1)‖ = ‖z‖ ‖Γ(z)‖` these give two-sided bounds on every line `Re z ∈ ½ℤ`, with
the exact exponential factor `e^{-π|t|/2}` and no appeal to Stirling's formula.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- Reflection sends `1/2 + it` to its conjugate. -/
theorem one_sub_half_add_I (t : ℝ) :
    (1 : ℂ) - (1 / 2 + (t : ℂ) * Complex.I) = (starRingEnd ℂ) (1 / 2 + (t : ℂ) * Complex.I) := by
  refine Complex.ext ?_ ?_
  · simp
    norm_num
  · simp

/-- The sine at the reflection point of the critical line. -/
theorem sin_pi_mul_half_add_I (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (1 / 2 + (t : ℂ) * Complex.I))
      = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  have hsplit : (Real.pi : ℂ) * (1 / 2 + (t : ℂ) * Complex.I)
      = (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    Complex.cos_mul_I, Complex.ofReal_cosh]
  ring

/-- **Exact modulus on the critical line.** -/
theorem norm_Gamma_half_add_I_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz, one_sub_half_add_I t, Complex.Gamma_conj, sin_pi_mul_half_add_I t] at hrefl
  have hnorm := congrArg (fun w : ℂ => ‖w‖) hrefl
  simp only [norm_mul, RCLike.norm_conj, norm_div, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _)] at hnorm
  rw [hz, ← hnorm]
  ring

/-- The sine at the reflection point of the line `Re z = 1`. -/
theorem norm_sin_pi_mul_I (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I))‖ = |Real.sinh (Real.pi * t)| := by
  have hsplit : (Real.pi : ℂ) * ((t : ℂ) * Complex.I) = ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.sin_mul_I, ← Complex.ofReal_sinh, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **Exact modulus on the line `Re z = 1`.** -/
theorem norm_Gamma_one_add_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2
      = Real.pi * |t| / |Real.sinh (Real.pi * t)| := by
  have htI : ((t : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, ht]
  have hstep : Complex.Gamma ((t : ℂ) * Complex.I + 1)
      = ((t : ℂ) * Complex.I) * Complex.Gamma ((t : ℂ) * Complex.I) :=
    Complex.Gamma_add_one _ htI
  have hcomm : ((t : ℂ) * Complex.I + 1) = 1 + (t : ℂ) * Complex.I := by ring
  rw [hcomm] at hstep
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * Complex.I)
  have hconj : (1 : ℂ) - (t : ℂ) * Complex.I = (starRingEnd ℂ) (1 + (t : ℂ) * Complex.I) := by
    simp only [map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, Complex.Gamma_conj] at hrefl
  -- `Γ(ti) · conj (Γ(1+ti)) = π / sin (π t i)` and `Γ(1+ti) = (ti) Γ(ti)`
  have hn := congrArg (fun w : ℂ => ‖w‖) hrefl
  simp only [norm_mul, RCLike.norm_conj, norm_div] at hn
  have htn : ‖(t : ℂ) * Complex.I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hG : ‖(t : ℂ) * Complex.I‖ * ‖Complex.Gamma ((t : ℂ) * Complex.I)‖
      = ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := by
    rw [← norm_mul, ← hstep]
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I))‖
      = |Real.sinh (Real.pi * t)| := norm_sin_pi_mul_I t
  have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2
      = (‖(t : ℂ) * Complex.I‖ * ‖Complex.Gamma ((t : ℂ) * Complex.I)‖) *
          ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := by rw [hG]; ring
    _ = ‖(t : ℂ) * Complex.I‖ *
          (‖Complex.Gamma ((t : ℂ) * Complex.I)‖ *
            ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖) := by ring
    _ = |t| * (Real.pi / |Real.sinh (Real.pi * t)|) := by
        rw [htn, hn, hpi, hsin]
    _ = Real.pi * |t| / |Real.sinh (Real.pi * t)| := by ring

/-- The functional equation in modulus form. -/
theorem norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) :
    ‖Complex.Gamma (z + 1)‖ = ‖z‖ * ‖Complex.Gamma z‖ := by
  rw [Complex.Gamma_add_one z hz, norm_mul]

/-- **Two-sided exponential bounds on the critical line.**  `cosh` is between `e^{|x|}/2` and
`e^{|x|}`, so the modulus of `Γ` on `Re z = 1/2` is exactly of size `e^{-π|t|/2}`. -/
theorem norm_Gamma_half_add_I_bounds (t : ℝ) :
    Real.sqrt Real.pi * Real.exp (-(Real.pi * |t| / 2))
        ≤ ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖
        ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hcosh : Real.cosh (Real.pi * t) = Real.cosh (Real.pi * |t|) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hsq := norm_Gamma_half_add_I_sq t
  rw [hcosh] at hsq
  have hcpos : 0 < Real.cosh (Real.pi * |t|) := Real.cosh_pos _
  have hE : (0 : ℝ) < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have he : (0 : ℝ) < Real.exp (-(Real.pi * |t|)) := Real.exp_pos _
  have hEinv : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  have hlow : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * |t|) := by
    rw [Real.cosh_eq]; linarith [he]
  have hpit : (0 : ℝ) ≤ Real.pi * |t| := by positivity
  have hhigh : Real.cosh (Real.pi * |t|) ≤ Real.exp (Real.pi * |t|) := by
    rw [Real.cosh_eq]
    have hmono : Real.exp (-(Real.pi * |t|)) ≤ Real.exp (Real.pi * |t|) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hnn : 0 ≤ ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hexpsq : Real.exp (-(Real.pi * |t| / 2)) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hkey : Real.pi * (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) = Real.pi := by
    rw [hEinv, mul_one]
  constructor
  · have hb : (Real.sqrt Real.pi * Real.exp (-(Real.pi * |t| / 2))) ^ 2
        ≤ ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, hexpsq, hsq, le_div_iff₀ hcpos]
      nlinarith [mul_le_mul_of_nonneg_left hhigh (mul_nonneg Real.pi_pos.le he.le), hkey]
    have hA : 0 ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi * |t| / 2)) := by positivity
    calc Real.sqrt Real.pi * Real.exp (-(Real.pi * |t| / 2))
        = Real.sqrt ((Real.sqrt Real.pi * Real.exp (-(Real.pi * |t| / 2))) ^ 2) :=
          (Real.sqrt_sq hA).symm
      _ ≤ Real.sqrt (‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ := Real.sqrt_sq hnn
  · have hb : ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq, hsq, div_le_iff₀ hcpos]
      nlinarith [mul_le_mul_of_nonneg_left hlow
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|))), hkey]
    have hB : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2)) := by positivity
    calc ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖
        = Real.sqrt (‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) ^ 2) :=
          Real.sqrt_le_sqrt hb
      _ = Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2)) := Real.sqrt_sq hB

/-- **The modulus of `Γ` on a vertical line is largest on the real axis.**  Immediate from the
integral representation: the integrand's modulus is the real integrand at `Re s`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin, mellin]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-t) : ℝ) : ℂ)‖ = Real.exp (-t) * t ^ (s.re - 1) := by
    intro t ht
    have htpos : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, ← Real.Gamma_eq_integral hs]

/-- Iterating the functional equation in modulus form. -/
theorem norm_Gamma_add_nat (z : ℂ) (m : ℕ) (hz : ∀ i : ℕ, i < m → z + (i : ℂ) ≠ 0) :
    ‖Complex.Gamma (z + (m : ℂ))‖
      = (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖) * ‖Complex.Gamma z‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hzi : z + (m : ℂ) ≠ 0 := hz m (Nat.lt_succ_self m)
      have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
      have hstep : Complex.Gamma (z + ((m + 1 : ℕ) : ℂ))
          = (z + (m : ℂ)) * Complex.Gamma (z + (m : ℂ)) := by
        rw [hcast, ← add_assoc]
        exact Complex.Gamma_add_one _ hzi
      rw [hstep, norm_mul, ih fun i hi => hz i (Nat.lt_succ_of_lt hi), Finset.prod_range_succ]
      ring

/-- **Shifting a two-sided vertical bound by a natural number.**  Each factor `‖z+i‖` lies between
`|t|` and `(σ+m+1)|t|`, so the polynomial factor is `|t|^m` on both sides. -/
theorem norm_Gamma_shift_bounds {c₁ c₂ σ : ℝ} (hσ : 0 ≤ σ) (hc₁ : 0 ≤ c₁) (m : ℕ) {t : ℝ}
    (ht : 1 ≤ |t|)
    (hlowbase : c₁ * Real.exp (-(Real.pi * |t| / 2))
      ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
    (hhighbase : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ c₂ * Real.exp (-(Real.pi * |t| / 2))) :
    c₁ * |t| ^ m * Real.exp (-(Real.pi * |t| / 2))
        ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + (m : ℂ))‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + (m : ℂ))‖
        ≤ c₂ * ((σ + m + 1) * |t|) ^ m * Real.exp (-(Real.pi * |t| / 2)) := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hre : ∀ i : ℕ, (z + (i : ℂ)).re = σ + i := by intro i; rw [hz]; simp
  have him : ∀ i : ℕ, (z + (i : ℂ)).im = t := by intro i; rw [hz]; simp
  have hne : ∀ i : ℕ, i < m → z + (i : ℂ) ≠ 0 := by
    intro i _ h
    have hi := him i
    rw [h] at hi
    simp only [Complex.zero_im] at hi
    rw [← hi] at ht
    norm_num at ht
  have hprod := norm_Gamma_add_nat z m hne
  have hlow : |t| ^ m ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ := by
    have hb : ∀ i ∈ Finset.range m, |t| ≤ ‖z + (i : ℂ)‖ := by
      intro i _
      have h := Complex.abs_im_le_norm (z + (i : ℂ))
      rwa [him i] at h
    calc |t| ^ m = ∏ _i ∈ Finset.range m, |t| := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ :=
          Finset.prod_le_prod (fun i _ => le_of_lt ht0) hb
  have hhigh : (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖) ≤ ((σ + m + 1) * |t|) ^ m := by
    have hb : ∀ i ∈ Finset.range m, ‖z + (i : ℂ)‖ ≤ (σ + m + 1) * |t| := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h := Complex.norm_le_abs_re_add_abs_im (z + (i : ℂ))
      rw [hre i, him i] at h
      have hi' : (i : ℝ) ≤ m := by exact_mod_cast le_of_lt hi
      have habs : |σ + (i : ℝ)| = σ + i := by
        rw [abs_of_nonneg (by positivity)]
      rw [habs] at h
      nlinarith [ht, hi', Nat.cast_nonneg (α := ℝ) i]
    calc (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖)
        ≤ ∏ _i ∈ Finset.range m, ((σ + m + 1) * |t|) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) hb
      _ = ((σ + m + 1) * |t|) ^ m := by rw [Finset.prod_const, Finset.card_range]
  refine ⟨?_, ?_⟩
  · rw [hprod]
    calc c₁ * |t| ^ m * Real.exp (-(Real.pi * |t| / 2))
        = |t| ^ m * (c₁ * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖) * ‖Complex.Gamma z‖ :=
          mul_le_mul hlow hlowbase (by positivity) (by positivity)
  · rw [hprod]
    calc (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖) * ‖Complex.Gamma z‖
        ≤ ((σ + m + 1) * |t|) ^ m * (c₂ * Real.exp (-(Real.pi * |t| / 2))) :=
          mul_le_mul hhigh hhighbase (norm_nonneg _) (by positivity)
      _ = c₂ * ((σ + m + 1) * |t|) ^ m * Real.exp (-(Real.pi * |t| / 2)) := by ring

/-- **Two-sided bounds on the shifted critical line `Re z = 1/2 + m`.** -/
theorem norm_Gamma_half_add_nat_bounds (m : ℕ) {t : ℝ} (ht : 1 ≤ |t|) :
    Real.sqrt Real.pi * |t| ^ m * Real.exp (-(Real.pi * |t| / 2))
        ≤ ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + (m : ℂ))‖ ∧
      ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + (m : ℂ))‖
        ≤ Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + m) * |t|) ^ m *
            Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨hlowbase, hhighbase⟩ := norm_Gamma_half_add_I_bounds t
  have hcast : (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [← hcast] at hlowbase hhighbase ⊢
  have h := norm_Gamma_shift_bounds (σ := (1 : ℝ) / 2) (by norm_num)
    (Real.sqrt_nonneg _) m ht hlowbase hhighbase
  have hshape : (1 : ℝ) / 2 + m + 1 = (3 : ℝ) / 2 + m := by ring
  rwa [hshape] at h

/-- **Two-sided bounds on the line `Re z = 1`.**  `sinh x` is between `(1-e^{-2}) e^x / 2` and
`e^x / 2` for `x ≥ 1`. -/
theorem norm_Gamma_one_add_I_bounds {t : ℝ} (ht : 1 ≤ |t|) :
    Real.sqrt (2 * Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2))
        ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖
        ≤ Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
            Real.exp (-(Real.pi * |t| / 2)) := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; norm_num at ht
  have hx : (1 : ℝ) ≤ Real.pi * |t| := by nlinarith [Real.two_le_pi]
  have hsinhsign : ∀ x : ℝ, 0 < x → 0 < Real.sinh x := by
    intro x hx
    rw [Real.sinh_eq]
    have hlt := Real.exp_lt_exp.mpr (show -x < x by linarith)
    linarith
  have hsinhabs : |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
    rcases lt_trichotomy t 0 with h | h | h
    · have hs : Real.sinh (Real.pi * t) < 0 := by
        have hp := hsinhsign (-(Real.pi * t)) (by nlinarith [Real.pi_pos])
        rw [Real.sinh_neg] at hp
        linarith
      rw [abs_of_neg hs, abs_of_neg h, mul_neg, Real.sinh_neg]
    · exact absurd h htne
    · rw [abs_of_pos (hsinhsign (Real.pi * t) (by nlinarith [Real.pi_pos])), abs_of_pos h]
  have hsq := norm_Gamma_one_add_I_sq htne
  rw [hsinhabs] at hsq
  have hE : (0 : ℝ) < Real.exp (Real.pi * |t|) := Real.exp_pos _
  have he2 : Real.exp (-2 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  have he2pos : (0 : ℝ) < 1 - Real.exp (-2 : ℝ) := by linarith
  have hupper : Real.sinh (Real.pi * |t|) ≤ Real.exp (Real.pi * |t|) / 2 := by
    rw [Real.sinh_eq]
    have : (0 : ℝ) < Real.exp (-(Real.pi * |t|)) := Real.exp_pos _
    linarith
  have hlower : (1 - Real.exp (-2 : ℝ)) * Real.exp (Real.pi * |t|) / 2
      ≤ Real.sinh (Real.pi * |t|) := by
    rw [Real.sinh_eq]
    have hkey : Real.exp (-(Real.pi * |t|)) ≤ Real.exp (-2 : ℝ) * Real.exp (Real.pi * |t|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hspos : (0 : ℝ) < Real.sinh (Real.pi * |t|) := by nlinarith
  have hnn : 0 ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hexpsq : Real.exp (-(Real.pi * |t| / 2)) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hEinv : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  constructor
  · have hb : (Real.sqrt (2 * Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2))) ^ 2
        ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq, hsq, le_div_iff₀ hspos]
      nlinarith [mul_le_mul_of_nonneg_left hupper
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))), hEinv,
        Real.pi_pos, ht0]
    have hA : 0 ≤ Real.sqrt (2 * Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2)) := by positivity
    calc Real.sqrt (2 * Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2))
        = Real.sqrt ((Real.sqrt (2 * Real.pi * |t|) * Real.exp (-(Real.pi * |t| / 2))) ^ 2) :=
          (Real.sqrt_sq hA).symm
      _ ≤ Real.sqrt (‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ := Real.sqrt_sq hnn
  · have hb : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ (Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
            Real.exp (-(Real.pi * |t| / 2))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq, hsq, div_le_iff₀ hspos]
      have hmul := mul_le_mul_of_nonneg_left hlower
        (by positivity :
          (0 : ℝ) ≤ 2 * Real.pi * |t| / (1 - Real.exp (-2)) * Real.exp (-(Real.pi * |t|)))
      have hcancel : 2 * Real.pi * |t| / (1 - Real.exp (-2)) * (1 - Real.exp (-2))
          = 2 * Real.pi * |t| := by field_simp
      nlinarith [hmul, hcancel, hEinv, Real.pi_pos, ht0]
    have hB : 0 ≤ Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
        Real.exp (-(Real.pi * |t| / 2)) := by positivity
    calc ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖
        = Real.sqrt (‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
            Real.exp (-(Real.pi * |t| / 2))) ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) *
            Real.exp (-(Real.pi * |t| / 2)) := Real.sqrt_sq hB

/-- **Two-sided bounds on the line `Re z = 1 + m`.** -/
theorem norm_Gamma_one_add_nat_bounds (m : ℕ) {t : ℝ} (ht : 1 ≤ |t|) :
    Real.sqrt (2 * Real.pi * |t|) * |t| ^ m * Real.exp (-(Real.pi * |t| / 2))
        ≤ ‖Complex.Gamma (1 + (t : ℂ) * Complex.I + (m : ℂ))‖ ∧
      ‖Complex.Gamma (1 + (t : ℂ) * Complex.I + (m : ℂ))‖
        ≤ Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) * (((2 : ℝ) + m) * |t|) ^ m *
            Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨hlowbase, hhighbase⟩ := norm_Gamma_one_add_I_bounds ht
  rw [← Complex.ofReal_one] at hlowbase hhighbase
  have h := norm_Gamma_shift_bounds (σ := (1 : ℝ)) zero_le_one (Real.sqrt_nonneg _) m ht
    hlowbase hhighbase
  rw [Complex.ofReal_one] at h
  have hshape : (1 : ℝ) + m + 1 = (2 : ℝ) + m := by ring
  rwa [hshape] at h

/-- **Lower bound to the left of a base line.**  Multiplying out the recursion: a lower bound at
`Re z = a + m` gives one at `Re z = a`, up to the polynomial factor `((|a|+m+1)|t|)^m`. -/
theorem norm_Gamma_lower_of_shift {a : ℝ} (m : ℕ) {t : ℝ} (ht : 1 ≤ |t|) {c : ℝ}
    (hlow : c * Real.exp (-(Real.pi * |t| / 2))
      ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I + (m : ℂ))‖) :
    c * Real.exp (-(Real.pi * |t| / 2))
      ≤ ((|a| + m + 1) * |t|) ^ m * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I with hz
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hre : ∀ i : ℕ, (z + (i : ℂ)).re = a + i := by intro i; rw [hz]; simp
  have him : ∀ i : ℕ, (z + (i : ℂ)).im = t := by intro i; rw [hz]; simp
  have hne : ∀ i : ℕ, i < m → z + (i : ℂ) ≠ 0 := by
    intro i _ h
    have hi := him i
    rw [h] at hi
    simp only [Complex.zero_im] at hi
    rw [← hi] at ht
    norm_num at ht
  have hprod := norm_Gamma_add_nat z m hne
  have hhigh : (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖) ≤ ((|a| + m + 1) * |t|) ^ m := by
    have hb : ∀ i ∈ Finset.range m, ‖z + (i : ℂ)‖ ≤ (|a| + m + 1) * |t| := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h := Complex.norm_le_abs_re_add_abs_im (z + (i : ℂ))
      rw [hre i, him i] at h
      have hi' : (i : ℝ) ≤ m := by exact_mod_cast le_of_lt hi
      have habs : |a + (i : ℝ)| ≤ |a| + (i : ℝ) := by
        have h1 : |a + (i : ℝ)| ≤ |a| + |(i : ℝ)| := by
          simpa [Real.norm_eq_abs] using norm_add_le a ((i : ℝ))
        have h2 : |((i : ℕ) : ℝ)| = (i : ℝ) := abs_of_nonneg (Nat.cast_nonneg i)
        linarith [h1, h2]
      nlinarith [ht, hi', Nat.cast_nonneg (α := ℝ) i, abs_nonneg a]
    calc (∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖)
        ≤ ∏ _i ∈ Finset.range m, ((|a| + m + 1) * |t|) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) hb
      _ = ((|a| + m + 1) * |t|) ^ m := by rw [Finset.prod_const, Finset.card_range]
  refine hlow.trans ?_
  rw [hprod]
  exact mul_le_mul_of_nonneg_right hhigh (norm_nonneg _)

/-- The modulus of the real Archimedean factor at an arbitrary complex point. -/
theorem norm_Gammaℝ (z : ℂ) :
    ‖Complex.Gammaℝ z‖ = Real.pi ^ (-z.re / 2) * ‖Complex.Gamma (z / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp

end GaloisForLFunctions.HTGeometry
