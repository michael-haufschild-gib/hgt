import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The Bohr--Cesàro mean of a finite exponential sum

The primitive of `e^{-iθt}` is `e^{-iθt}/(-iθ)`, of modulus `1/|θ|`, so for a nonzero frequency the
whole integral over `[1, T]` stays bounded and its Cesàro mean vanishes.  The trivial frequency
contributes its coefficient.  Consequently the Cesàro mean of a finite exponential sum retains
exactly the coefficients at the zero frequencies:

`lim_{T→∞} (1/T) ∫_1^T ∑_j a_j e^{-iθ_j t} dt = ∑_{θ_j = 0} a_j`.

Applied to the two-replica form of the heat Turán defect on one off-line shell, this keeps exactly
the pairs with `B_j + B_k = 0`, whose contribution is a strictly negative sum of squares whenever
the shell is conjugation-symmetric with no zero transverse part.
-/

open Filter Topology Complex intervalIntegral

namespace RHTower

noncomputable section

/-! ## The mean of a single character -/

theorem hasDerivAt_charPrimitive {theta : ℝ} (h : theta ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (theta : ℂ) * (s : ℂ))
        / (-Complex.I * (theta : ℂ)))
      (Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))) t := by
  have hne : (-Complex.I * (theta : ℂ)) ≠ 0 := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hth : (theta : ℂ) ≠ 0 := by exact_mod_cast h
    simpa using mul_ne_zero (neg_ne_zero.2 hI) hth
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => -Complex.I * (theta : ℂ) * (s : ℂ))
      (-Complex.I * (theta : ℂ)) t := by
    simpa using h1.const_mul (-Complex.I * (theta : ℂ))
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (theta : ℂ) * (s : ℂ)))
      (Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ)) * (-Complex.I * (theta : ℂ))) t := h2.cexp
  have h4 := h3.div_const (-Complex.I * (theta : ℂ))
  refine h4.congr_deriv ?_
  field_simp
  exact div_self (by exact_mod_cast h : (theta : ℂ) ≠ 0)

theorem norm_char (theta t : ℝ) : ‖Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_integral_char_le {theta : ℝ} (h : theta ≠ 0) (T : ℝ) :
    ‖∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))‖ ≤ 2 / |theta| := by
  have hne : (-Complex.I * (theta : ℂ)) ≠ 0 := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hth : (theta : ℂ) ≠ 0 := by exact_mod_cast h
    simpa using mul_ne_zero (neg_ne_zero.2 hI) hth
  have hcont : Continuous fun t : ℝ => Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ)) := by
    fun_prop
  have hftc : ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))
      = Complex.exp (-Complex.I * (theta : ℂ) * (T : ℂ)) / (-Complex.I * (theta : ℂ))
        - Complex.exp (-Complex.I * (theta : ℂ) * ((1 : ℝ) : ℂ)) / (-Complex.I * (theta : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_charPrimitive h x)
      (hcont.intervalIntegrable _ _)
  have hden : ‖(-Complex.I * (theta : ℂ))‖ = |theta| := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hftc]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_div, norm_div, hden, norm_char, norm_char]
  exact le_of_eq (by ring)

/-- **The Cesàro mean of a nonzero character vanishes.** -/
theorem tendsto_cesaroChar {theta : ℝ} (h : theta ≠ 0) :
    Tendsto (fun T : ℝ => (1 / T) *
        ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ)))
      atTop (nhds 0) := by
  have habs : 0 < |theta| := abs_pos.2 h
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(1 / T) * ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))‖
        ≤ (2 / |theta|) / T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have hstep := norm_integral_char_le h T
    have hpos : (0 : ℝ) < 1 / T := by positivity
    calc 1 / T * ‖∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta : ℂ) * (t : ℂ))‖
        ≤ 1 / T * (2 / |theta|) := mul_le_mul_of_nonneg_left hstep hpos.le
      _ = (2 / |theta|) / T := by ring
  have hlim : Tendsto (fun T : ℝ => (2 / |theta|) / T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero_norm' hbound hlim

/-- **The Cesàro mean of the trivial character is one.** -/
theorem tendsto_cesaroChar_zero :
    Tendsto (fun T : ℝ => (1 / T) *
        ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * ((0 : ℝ) : ℂ) * (t : ℂ)))
      atTop (nhds 1) := by
  have hreal : Tendsto (fun T : ℝ => (1 : ℝ) / T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcplx : Tendsto (fun T : ℝ => ((1 / T : ℝ) : ℂ)) atTop (nhds 0) := by
    have hcomp := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa [Function.comp_def] using hcomp
  have hone : Tendsto (fun T : ℝ => (1 : ℂ) - ((1 / T : ℝ) : ℂ)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hcplx
  rw [sub_zero] at hone
  refine hone.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTne : (T : ℂ) ≠ 0 := by
    simpa using ne_of_gt hT
  have hint : (∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * ((0 : ℝ) : ℂ) * (t : ℂ)))
      = (T : ℂ) - 1 := by
    simp
  rw [hint]
  push_cast
  field_simp

/-! ## The mean of a finite exponential sum -/

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **(24.152) The Bohr--Cesàro mean of a finite exponential sum retains exactly the zero
frequencies.** -/
theorem tendsto_cesaro_expSum (s : Finset ι) (a : ι → ℂ) (theta : ι → ℝ) :
    Tendsto (fun T : ℝ => (1 / T) *
        ∫ t in (1 : ℝ)..T, ∑ j ∈ s, a j * Complex.exp (-Complex.I * (theta j : ℂ) * (t : ℂ)))
      atTop (nhds (∑ j ∈ s.filter (fun j => theta j = 0), a j)) := by
  classical
  have hsplit : ∀ T : ℝ, (1 / T) *
      ∫ t in (1 : ℝ)..T, ∑ j ∈ s, a j * Complex.exp (-Complex.I * (theta j : ℂ) * (t : ℂ))
      = ∑ j ∈ s, a j * ((1 / T) *
          ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta j : ℂ) * (t : ℂ))) := by
    intro T
    rw [intervalIntegral.integral_finsetSum (fun j _ => by
      exact ((Complex.continuous_exp.comp (by fun_prop)).const_mul (a j)).intervalIntegrable _ _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  have hterm : ∀ j ∈ s, Tendsto (fun T : ℝ => a j * ((1 / T) *
      ∫ t in (1 : ℝ)..T, Complex.exp (-Complex.I * (theta j : ℂ) * (t : ℂ))))
      atTop (nhds (if theta j = 0 then a j else 0)) := by
    intro j _
    by_cases hj : theta j = 0
    · rw [if_pos hj, hj]
      have := (tendsto_cesaroChar_zero).const_mul (a j)
      simpa using this
    · rw [if_neg hj]
      have := (tendsto_cesaroChar hj).const_mul (a j)
      simpa using this
  have hsum := tendsto_finsetSum s hterm
  have hval : ∑ j ∈ s, (if theta j = 0 then a j else 0)
      = ∑ j ∈ s.filter (fun j => theta j = 0), a j := by
    rw [Finset.sum_filter]
  rw [hval] at hsum
  refine hsum.congr fun T => ?_
  rw [hsplit T]

/-! ## The shell mean is strictly negative -/

omit [DecidableEq ι] in
/-- The pairs of a shell that survive the Cesàro mean. -/
theorem cesaro_shell_pairs_pos (s : Finset ι) (B : ι → ℝ) (sigma : ι → ι)
    (hsig : ∀ j ∈ s, sigma j ∈ s) (hB : ∀ j ∈ s, B (sigma j) = -B j)
    {j₀ : ι} (hj₀ : j₀ ∈ s) (hne : B j₀ ≠ 0) :
    0 < ∑ p ∈ (s ×ˢ s).filter (fun p => B p.1 + B p.2 = 0), (B p.1 - B p.2) ^ (2 : ℕ) := by
  classical
  refine Finset.sum_pos' (fun p _ => sq_nonneg _) ⟨(j₀, sigma j₀), ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hj₀, hsig j₀ hj₀⟩, by rw [hB j₀ hj₀]; ring⟩
  · have hval : B j₀ - B (sigma j₀) = 2 * B j₀ := by
      rw [hB j₀ hj₀]
      ring
    rw [hval]
    positivity

end

end RHTower
