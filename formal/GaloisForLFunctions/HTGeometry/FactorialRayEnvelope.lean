import GaloisForLFunctions.HTGeometry.GammaRayRealEnvelope

/-!
# The factorial form of the ray envelope

The real factorial `Γ(1+rn)` is itself comparable, up to a polynomial factor, with `(n!)^r r^{rn}`:
the one-step ratio of the two sides is `1 + O(1/n)`, and the harmonic telescoping bound turns that
into a logarithmic defect.  Combining this with the ray envelope gives the form an endpoint
convolution estimate actually consumes,

`‖Γ(1+αn)‖ ≍ n^{±B} · (n!)^r · Λ^n`,   `Λ = e^{Re(α log α)}`, `r = Re α`,

in which the only transcendental ingredient left is the factorial itself.  The entropy inequality
for a product of factorials over a composition is elementary, so no Stirling series is needed
anywhere in the chain.

The telescoping step is isolated here as `exists_log_bound_of_step`, which converts a one-step bound
`|D(n+1) − D(n)| ≤ K/n` into `|D n| ≤ C + 2K log n`.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## Telescoping a one-step bound -/

/-- **Harmonic telescoping.**  A one-step defect of size `K/n` accumulates to `2K log n`. -/
theorem exists_log_bound_of_step {D : ℕ → ℝ} {K : ℝ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hK : 0 ≤ K)
    (hstep : ∀ n : ℕ, n₀ ≤ n → |D (n + 1) - D n| ≤ K / n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |D n| ≤ C + 2 * K * Real.log n := by
  classical
  have hmain : ∀ n : ℕ, n₀ ≤ n → |D n| ≤ |D n₀| + 2 * K * Real.log n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hone : (1 : ℝ) ≤ ((n₀ : ℕ) : ℝ) := by exact_mod_cast hn₀
        have hlog : 0 ≤ Real.log ((n₀ : ℕ) : ℝ) := Real.log_nonneg hone
        nlinarith
    | succ n hn ih =>
        have hn1 : 1 ≤ n := le_trans hn₀ hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hs := hstep n hn
        have hlogstep : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
          log_succ_lower_bound (n : ℝ) hnpos
        have hhalf : K / (n : ℝ) ≤ 2 * K * (1 / ((n : ℝ) + 1)) := by
          rw [div_le_iff₀ hnpos]
          have hfrac : (1 : ℝ) / ((n : ℝ) + 1) * (n : ℝ) ≥ 1 / 2 := by
            rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
            linarith
          nlinarith
        have htri : |D (n + 1)| ≤ |D n| + |D (n + 1) - D n| := by
          have := abs_add_le (D n) (D (n + 1) - D n)
          simpa using this
        have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith [htri, hs, hhalf, ih, hlogstep, hK]
  have hne : (Finset.range (n₀ + 1)).Nonempty := ⟨0, by simp⟩
  set C₂ : ℝ := (Finset.range (n₀ + 1)).sup' hne (fun m => |D m|) with hC₂
  have hC₂le : ∀ m : ℕ, m ≤ n₀ → |D m| ≤ C₂ := by
    intro m hm
    exact Finset.le_sup' (fun m => |D m|) (Finset.mem_range.mpr (by omega))
  have hC₂nonneg : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂le 0 (Nat.zero_le _))
  refine ⟨C₂, hC₂nonneg, ?_⟩
  intro n hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  rcases le_or_gt n₀ n with h | h
  · refine le_trans (hmain n h) ?_
    have := hC₂le n₀ le_rfl
    linarith
  · have hle := hC₂le n (le_of_lt h)
    nlinarith

/-! ## The real Gamma against the factorial -/

/-- The logarithmic defect of `Γ(1+rn)` against `(n!)^r r^{rn}`. -/
def factorialGammaDefect (r : ℝ) (n : ℕ) : ℝ :=
  Real.log (Real.Gamma (1 + r * n)) - r * Real.log (n.factorial) - n * (r * Real.log r)

theorem re_ofReal_mul_log_rayPoint_ofReal {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ((r : ℂ) * Complex.log (rayPoint (r : ℂ) n)).re = r * Real.log (1 + r * n) := by
  have hpos : (0 : ℝ) < 1 + r * n := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  rw [rayPoint_ofReal, log_ofReal_of_pos hpos, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- **The one-step defect of the factorial comparison.** -/
theorem factorialGammaDefect_succ_sub {r : ℝ} (hr : 0 < r) (n : ℕ) :
    factorialGammaDefect r (n + 1) - factorialGammaDefect r n
      = r * Real.log (1 + r * n) - r * Real.log ((n : ℝ) + 1) - r * Real.log r
        + (rayShiftExponent (r : ℂ) (r : ℂ) n).re := by
  have hβre : ((r : ℂ)).re = r := Complex.ofReal_re _
  have hβpos : 0 < ((r : ℂ)).re := by rw [hβre]; exact hr
  have hstep := log_norm_Gamma_rayPoint_succ_sub hβpos n
  simp only [norm_Gamma_rayPoint_ofReal hr] at hstep
  rw [re_ofReal_mul_log_rayPoint_ofReal hr] at hstep
  have hfac : Real.log (((n + 1).factorial : ℕ) : ℝ)
      = Real.log ((n.factorial : ℕ) : ℝ) + Real.log ((n : ℝ) + 1) := by
    have hval : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hval, Real.log_mul (by positivity) (by positivity)]
    ring
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [factorialGammaDefect, factorialGammaDefect, hfac, hcast]
  push_cast at hstep ⊢
  linarith [hstep]

/-- The one-step defect is `O(1/n)`. -/
theorem abs_factorialGammaDefect_succ_sub_le {r : ℝ} (hr : 0 < r) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * r + 4 ≤ 1 + n * r) (hsmall : 2 * |1 - r| ≤ r * n) :
    |factorialGammaDefect r (n + 1) - factorialGammaDefect r n|
      ≤ (2 * |1 - r| + (6 + 2 * r)) / n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hβre : ((r : ℂ)).re = r := Complex.ofReal_re _
  have hβpos : 0 < ((r : ℂ)).re := by rw [hβre]; exact hr
  have hβnorm : ‖((r : ℂ))‖ = r := norm_ofReal_of_pos hr
  have hRβ : (rayPoint ((r : ℝ) : ℂ) n).re = 1 + n * r := by rw [rayPoint_re, hβre]
  have hRpos : (0 : ℝ) < 1 + n * r := by linarith
  -- the logarithmic term
  have hden : (0 : ℝ) < r * ((n : ℝ) + 1) := by positivity
  have hlogterm : |r * Real.log (1 + r * n) - r * Real.log ((n : ℝ) + 1) - r * Real.log r|
      ≤ 2 * |1 - r| / n := by
    have hratio : (1 + r * n) / (r * ((n : ℝ) + 1)) = 1 + (1 - r) / (r * ((n : ℝ) + 1)) := by
      field_simp
      ring
    have hsplit : Real.log (1 + r * n) - Real.log ((n : ℝ) + 1) - Real.log r
        = Real.log ((1 + r * n) / (r * ((n : ℝ) + 1))) := by
      rw [Real.log_div (by linarith) (ne_of_gt hden), Real.log_mul (ne_of_gt hr) (by positivity)]
      ring
    have hu : |(1 - r) / (r * ((n : ℝ) + 1))| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by norm_num)]
      nlinarith
    have hulog : |Real.log (1 + (1 - r) / (r * ((n : ℝ) + 1)))|
        ≤ 2 * |(1 - r) / (r * ((n : ℝ) + 1))| := by
      set u : ℝ := (1 - r) / (r * ((n : ℝ) + 1)) with hudef
      have hu1 : |u| ≤ 1 / 2 := hu
      have hpos : (0 : ℝ) < 1 + u := by
        have := abs_le.mp hu1
        linarith [this.1]
      have hle : Real.log (1 + u) ≤ u := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      have hge : -(2 * |u|) ≤ Real.log (1 + u) := by
        have hinv : (0 : ℝ) < (1 + u)⁻¹ := by positivity
        have hlog2 : Real.log ((1 + u)⁻¹) ≤ (1 + u)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos hinv
        rw [Real.log_inv] at hlog2
        have hbound : (1 + u)⁻¹ - 1 ≤ 2 * |u| := by
          have habs := abs_le.mp hu1
          have hhalf : (1 : ℝ) / 2 ≤ 1 + u := by linarith [habs.1]
          have hid : (1 + u)⁻¹ - 1 = -u / (1 + u) := by
            field_simp
            ring
          rw [hid, div_le_iff₀ hpos]
          nlinarith [le_abs_self u, neg_abs_le u, abs_nonneg u]
        linarith
      have habsu : |u| ≥ 0 := abs_nonneg u
      rw [abs_le]
      constructor
      · linarith
      · linarith [le_abs_self u]
    have hfinal : r * Real.log (1 + r * n) - r * Real.log ((n : ℝ) + 1) - r * Real.log r
        = r * Real.log (1 + (1 - r) / (r * ((n : ℝ) + 1))) := by
      rw [← hratio, ← hsplit]
      ring
    rw [hfinal, abs_mul, abs_of_pos hr]
    refine le_trans (mul_le_mul_of_nonneg_left hulog (le_of_lt hr)) ?_
    have hLHS : r * (2 * |(1 - r) / (r * ((n : ℝ) + 1))|) = 2 * |1 - r| / ((n : ℝ) + 1) := by
      rw [abs_div, abs_of_pos hden]
      field_simp
    rw [hLHS]
    exact div_le_div_of_nonneg_left (by positivity) hnpos (by linarith)
  -- the shift exponent
  have hexpo : |(rayShiftExponent ((r : ℝ) : ℂ) ((r : ℝ) : ℂ) n).re| ≤ (6 + 2 * r) / (n : ℝ) := by
    have hbase := norm_rayShiftExponent_le (α := ((r : ℝ) : ℂ)) (w := ((r : ℝ) : ℂ))
      hβpos (n := n) (by rw [hRβ, hβnorm]; linarith)
    have habs : |(rayShiftExponent ((r : ℝ) : ℂ) ((r : ℝ) : ℂ) n).re|
        ≤ ‖rayShiftExponent ((r : ℝ) : ℂ) ((r : ℝ) : ℂ) n‖ := Complex.abs_re_le_norm _
    refine le_trans (le_trans habs hbase) ?_
    rw [hRβ, hβnorm]
    have hhalf : 3 / ((1 + n * r) - r) ≤ 6 / (1 + n * r) := by
      rw [div_le_div_iff₀ (by linarith) hRpos]
      nlinarith
    have hstep2 : r * (3 / ((1 + n * r) - r) + 2 * r / (1 + n * r))
        ≤ r * (6 / (1 + n * r) + 2 * r / (1 + n * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hr)
    refine le_trans hstep2 ?_
    have hcomb : r * (6 / (1 + n * r) + 2 * r / (1 + n * r)) = r * (6 + 2 * r) / (1 + n * r) := by
      field_simp
    rw [hcomb, div_le_div_iff₀ hRpos hnpos]
    nlinarith
  rw [factorialGammaDefect_succ_sub hr]
  have hadd := abs_add_le (r * Real.log (1 + r * n) - r * Real.log ((n : ℝ) + 1) - r * Real.log r)
    ((rayShiftExponent ((r : ℝ) : ℂ) ((r : ℝ) : ℂ) n).re)
  have hsum : 2 * |1 - r| / (n : ℝ) + (6 + 2 * r) / (n : ℝ)
      = (2 * |1 - r| + (6 + 2 * r)) / (n : ℝ) := by ring
  linarith [hadd, hlogterm, hexpo, hsum]

/-! ## The factorial envelope -/

/-- **`Γ(1+rn)` is `(n!)^r r^{rn}` up to a polynomial factor.** -/
theorem exists_factorialGammaEnvelope {r : ℝ} (hr : 0 < r) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Real.Gamma (1 + r * n)
          ≤ C * (n : ℝ) ^ B
            * ((n.factorial : ℝ) ^ r * Real.exp (n * (r * Real.log r)))
        ∧ (n.factorial : ℝ) ^ r * Real.exp (n * (r * Real.log r))
          ≤ C * (n : ℝ) ^ B * Real.Gamma (1 + r * n) := by
  classical
  set n₀ : ℕ := ⌈(2 * r + 3) / r⌉₊ + ⌈(2 * |1 - r|) / r⌉₊ + 1 with hn₀def
  have hn₀ : 1 ≤ n₀ := by omega
  have hK : (0 : ℝ) ≤ 2 * |1 - r| + (6 + 2 * r) := by
    have := abs_nonneg (1 - r)
    linarith
  have hstep : ∀ n : ℕ, n₀ ≤ n →
      |factorialGammaDefect r (n + 1) - factorialGammaDefect r n|
        ≤ (2 * |1 - r| + (6 + 2 * r)) / n := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hn₀ hn
    have hnR : ((n₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hc1 : (2 * r + 3) / r ≤ (⌈(2 * r + 3) / r⌉₊ : ℝ) := Nat.le_ceil _
    have hc2 : (2 * |1 - r|) / r ≤ (⌈(2 * |1 - r|) / r⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((n₀ : ℕ) : ℝ)
        = (⌈(2 * r + 3) / r⌉₊ : ℝ) + (⌈(2 * |1 - r|) / r⌉₊ : ℝ) + 1 := by
      rw [hn₀def]
      push_cast
      ring
    have hpos1 : (0 : ℝ) ≤ (⌈(2 * |1 - r|) / r⌉₊ : ℝ) := Nat.cast_nonneg _
    have hpos2 : (0 : ℝ) ≤ (⌈(2 * r + 3) / r⌉₊ : ℝ) := Nat.cast_nonneg _
    have hA : (2 * r + 3) / r ≤ (n : ℝ) := by
      rw [hcast] at hnR
      linarith
    have hB : (2 * |1 - r|) / r ≤ (n : ℝ) := by
      rw [hcast] at hnR
      linarith
    rw [div_le_iff₀ hr] at hA hB
    refine abs_factorialGammaDefect_succ_sub_le hr hn1 ?_ ?_
    · nlinarith
    · nlinarith
  obtain ⟨C₀, hC₀, hbound⟩ := exists_log_bound_of_step hn₀ hK hstep
  set K : ℝ := 2 * (2 * |1 - r| + (6 + 2 * r)) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  refine ⟨⌈K⌉₊, Real.exp C₀, Real.exp_pos _, ?_⟩
  intro n hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hrpos : (0 : ℝ) < 1 + r * n := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  have hGpos : 0 < Real.Gamma (1 + r * n) := Real.Gamma_pos_of_pos hrpos
  have hrpow : ((n.factorial : ℝ)) ^ r = Real.exp (r * Real.log (n.factorial : ℝ)) := by
    rw [Real.rpow_def_of_pos hfacpos]
    ring_nf
  have hexp : Real.Gamma (1 + r * n)
      = Real.exp (factorialGammaDefect r n)
        * ((n.factorial : ℝ) ^ r * Real.exp (n * (r * Real.log r))) := by
    rw [factorialGammaDefect, Real.exp_sub, Real.exp_sub, Real.exp_log hGpos, hrpow]
    field_simp
  have hpow : Real.exp (K * Real.log (n : ℝ)) ≤ (n : ℝ) ^ (⌈K⌉₊) := by
    have hKle : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have hmono : Real.exp (K * Real.log (n : ℝ)) ≤ Real.exp ((⌈K⌉₊ : ℝ) * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKle hlogn)
    refine le_trans hmono ?_
    rw [Real.exp_nat_mul, Real.exp_log hnpos]
  have hup : Real.exp (factorialGammaDefect r n) ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) := by
    have h1 : factorialGammaDefect r n ≤ C₀ + K * Real.log (n : ℝ) :=
      le_trans (le_abs_self _) (hbound n hn1)
    calc Real.exp (factorialGammaDefect r n) ≤ Real.exp (C₀ + K * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr h1
      _ = Real.exp C₀ * Real.exp (K * Real.log (n : ℝ)) := Real.exp_add _ _
      _ ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hdown : Real.exp (-(factorialGammaDefect r n)) ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) := by
    have h1 : -(factorialGammaDefect r n) ≤ C₀ + K * Real.log (n : ℝ) :=
      le_trans (neg_le_abs _) (hbound n hn1)
    calc Real.exp (-(factorialGammaDefect r n)) ≤ Real.exp (C₀ + K * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr h1
      _ = Real.exp C₀ * Real.exp (K * Real.log (n : ℝ)) := Real.exp_add _ _
      _ ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hprodpos : (0 : ℝ)
      < (n.factorial : ℝ) ^ r * Real.exp (n * (r * Real.log r)) := by positivity
  constructor
  · rw [hexp]
    exact mul_le_mul_of_nonneg_right hup (le_of_lt hprodpos)
  · have hrev : (n.factorial : ℝ) ^ r * Real.exp (n * (r * Real.log r))
        = Real.exp (-(factorialGammaDefect r n)) * Real.Gamma (1 + r * n) := by
      rw [hexp, Real.exp_neg]
      field_simp
    rw [hrev]
    exact mul_le_mul_of_nonneg_right hdown (le_of_lt hGpos)

/-- **The factorial form of the ray envelope.**  Up to a polynomial factor, the modulus of `Γ`
along the ray `1 + αn` is `(n!)^{Re α}` times the geometric factor `e^{n Re(α log α)}`. -/
theorem exists_factorialRayEnvelope {α : ℂ} (hre : 0 < α.re) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖Complex.Gamma (rayPoint α n)‖
          ≤ C * (n : ℝ) ^ B
            * ((n.factorial : ℝ) ^ α.re * Real.exp (n * (α * Complex.log α).re))
        ∧ (n.factorial : ℝ) ^ α.re * Real.exp (n * (α * Complex.log α).re)
          ≤ C * (n : ℝ) ^ B * ‖Complex.Gamma (rayPoint α n)‖ := by
  obtain ⟨B₁, C₁, hC₁, h₁⟩ := exists_rayEnvelope hre
  obtain ⟨B₂, C₂, hC₂, h₂⟩ := exists_factorialGammaEnvelope hre
  refine ⟨B₁ + B₂, C₁ * C₂, by positivity, ?_⟩
  intro n hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (B₁ + B₂) = (n : ℝ) ^ B₁ * (n : ℝ) ^ B₂ := pow_add _ _ _
  have hrpos : (0 : ℝ) < 1 + α.re * n := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  have hGpos : 0 < Real.Gamma (1 + α.re * n) := Real.Gamma_pos_of_pos hrpos
  have hΓpos : 0 < ‖Complex.Gamma (rayPoint α n)‖ := norm_Gamma_rayPoint_pos hre n
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hslope : (n : ℝ) * rayEnvelopeSlope α + (n : ℝ) * (α.re * Real.log α.re)
      = (n : ℝ) * (α * Complex.log α).re := by
    rw [rayEnvelopeSlope]
    ring
  have hsplit : Real.exp ((n : ℝ) * (α * Complex.log α).re)
      = Real.exp ((n : ℝ) * rayEnvelopeSlope α)
        * Real.exp ((n : ℝ) * (α.re * Real.log α.re)) := by
    rw [← Real.exp_add, hslope]
  obtain ⟨hup₁, hdown₁⟩ := h₁ n hn1
  obtain ⟨hup₂, hdown₂⟩ := h₂ n hn1
  constructor
  · calc ‖Complex.Gamma (rayPoint α n)‖
        ≤ C₁ * (n : ℝ) ^ B₁
          * (Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n)) := hup₁
      _ ≤ C₁ * (n : ℝ) ^ B₁
          * (Real.exp (n * rayEnvelopeSlope α)
            * (C₂ * (n : ℝ) ^ B₂
              * ((n.factorial : ℝ) ^ α.re * Real.exp (n * (α.re * Real.log α.re))))) := by
          have hfac : (0 : ℝ) ≤ C₁ * (n : ℝ) ^ B₁ * Real.exp (n * rayEnvelopeSlope α) := by
            positivity
          nlinarith [hup₂, Real.exp_pos ((n : ℝ) * rayEnvelopeSlope α), hC₁,
            pow_nonneg (le_of_lt hnpos) B₁]
      _ = C₁ * C₂ * (n : ℝ) ^ (B₁ + B₂)
          * ((n.factorial : ℝ) ^ α.re * Real.exp (n * (α * Complex.log α).re)) := by
          rw [hpow, hsplit]
          ring
  · calc (n.factorial : ℝ) ^ α.re * Real.exp (n * (α * Complex.log α).re)
        = (n.factorial : ℝ) ^ α.re * Real.exp (n * (α.re * Real.log α.re))
          * Real.exp (n * rayEnvelopeSlope α) := by
          rw [hsplit]
          ring
      _ ≤ C₂ * (n : ℝ) ^ B₂ * Real.Gamma (1 + α.re * n) * Real.exp (n * rayEnvelopeSlope α) := by
          have := Real.exp_pos ((n : ℝ) * rayEnvelopeSlope α)
          nlinarith [hdown₂]
      _ = C₂ * (n : ℝ) ^ B₂
          * (Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n)) := by ring
      _ ≤ C₂ * (n : ℝ) ^ B₂ * (C₁ * (n : ℝ) ^ B₁ * ‖Complex.Gamma (rayPoint α n)‖) := by
          have hfac : (0 : ℝ) ≤ C₂ * (n : ℝ) ^ B₂ := by positivity
          exact mul_le_mul_of_nonneg_left hdown₁ hfac
      _ = C₁ * C₂ * (n : ℝ) ^ (B₁ + B₂) * ‖Complex.Gamma (rayPoint α n)‖ := by
          rw [hpow]
          ring

end

end GaloisForLFunctions.HTGeometry
