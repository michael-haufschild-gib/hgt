/-
Oscillation bounds for first moments of modulated envelopes.

Integration by parts against the explicit antiderivative `exp(cu)/c` of a unimodular character
`u ↦ exp(−iλu)` converts a first moment `∫ A(u)·exp(−iλu) du` into boundary terms and a
derivative moment, each carrying the factor `1/|λ|`.  A `C¹` envelope with sup `M₀` and
derivative sup `M₁` therefore has first moment at most `(2M₀ + (β−α)M₁)/|λ|`: oscillation
converts envelope smoothness into cancellation at scale `1/|λ|`.  For the finite carrier the
relevant frequencies are `λ = log n`, so every term beyond `n = 1` gains a logarithm — the
mechanism that makes the first-moment cancellation face of the sign-bracket certificates a
theorem rather than an assumption.
-/
import GaloisForLFunctions.RHTower.HardyCarrier

open Complex Metric

namespace RHTower

/-- **Oscillation bound.**  A `C¹` envelope `A` with `‖A‖ ≤ M₀` and `‖A′‖ ≤ M₁` on `[α, β]` has
`‖∫ A(u)·exp(−iλu) du‖ ≤ (2M₀ + (β−α)M₁)/|λ|` for every nonzero frequency `λ`: integrating by
parts against the antiderivative `exp(−iλu)/(−iλ)` places the factor `1/|λ|` on both boundary
terms and on the derivative moment. -/
theorem norm_integral_mul_exp_le {A A' : ℝ → ℂ} {α β lam M₀ M₁ : ℝ}
    (hαβ : α ≤ β) (hlam : lam ≠ 0)
    (hA : ∀ u ∈ Set.uIcc α β, HasDerivAt A (A' u) u)
    (hA'c : ContinuousOn A' (Set.uIcc α β))
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖A u‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖A' u‖ ≤ M₁) :
    ‖∫ u in α..β, A u * Complex.exp (-(Complex.I * lam) * u)‖ ≤
      (2 * M₀ + (β - α) * M₁) / |lam| := by
  set c : ℂ := -(Complex.I * lam) with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    simp [Complex.ext_iff, hlam]
  have hnc : ‖c‖ = |lam| := by
    rw [hc_def]
    simp
  have hlam_abs : 0 < |lam| := abs_pos.mpr hlam
  have hEderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (c * u) / c)
      (Complex.exp (c * u)) u := by
    intro u
    have hlin : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul c
    have hexp := hlin.cexp
    have hdiv := hexp.div_const c
    simpa [mul_div_cancel_right₀ _ hc] using hdiv
  have hEnorm : ∀ u : ℝ, ‖Complex.exp (c * u) / c‖ = 1 / |lam| := by
    intro u
    rw [norm_div, hnc, Complex.norm_exp]
    have hre : (c * (u : ℂ)).re = 0 := by
      rw [hc_def]
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have hexp_cont : Continuous fun u : ℝ => Complex.exp (c * u) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := A) (u' := A') (v := fun u : ℝ => Complex.exp (c * u) / c)
    (v' := fun u : ℝ => Complex.exp (c * u))
    hA (fun x _ => hEderiv x)
    hA'c.intervalIntegrable
    (hexp_cont.intervalIntegrable α β)
  have hαmem : α ∈ Set.Icc α β := ⟨le_rfl, hαβ⟩
  have hβmem : β ∈ Set.Icc α β := ⟨hαβ, le_rfl⟩
  have hbound_tail : ‖∫ u in α..β, A' u * (Complex.exp (c * u) / c)‖ ≤
      M₁ / |lam| * |β - α| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc α β := by
      rw [Set.uIoc_of_le hαβ] at hx
      exact Set.Ioc_subset_Icc_self hx
    rw [norm_mul, hEnorm x]
    have h1 := hM₁ x hx'
    have h2 : (0 : ℝ) ≤ 1 / |lam| := by positivity
    calc ‖A' x‖ * (1 / |lam|) ≤ M₁ * (1 / |lam|) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = M₁ / |lam| := by ring
  have habs : |β - α| = β - α := abs_of_nonneg (by linarith)
  calc ‖∫ u in α..β, A u * Complex.exp (c * u)‖
      = ‖A β * (Complex.exp (c * β) / c) - A α * (Complex.exp (c * α) / c) -
          ∫ u in α..β, A' u * (Complex.exp (c * u) / c)‖ := by rw [hibp]
    _ ≤ ‖A β * (Complex.exp (c * β) / c)‖ + ‖A α * (Complex.exp (c * α) / c)‖ +
          ‖∫ u in α..β, A' u * (Complex.exp (c * u) / c)‖ := by
        exact le_trans (norm_sub_le _ _) (by gcongr; exact norm_sub_le _ _)
    _ ≤ M₀ * (1 / |lam|) + M₀ * (1 / |lam|) + M₁ / |lam| * |β - α| := by
        gcongr
        · rw [norm_mul, hEnorm β]
          exact mul_le_mul_of_nonneg_right (hM₀ β hβmem) (by positivity)
        · rw [norm_mul, hEnorm α]
          exact mul_le_mul_of_nonneg_right (hM₀ α hαmem) (by positivity)
    _ = (2 * M₀ + (β - α) * M₁) / |lam| := by
        rw [habs]
        field_simp
        ring

/-- Real-part form of the oscillation bound: the first moment of the real part of a modulated
`C¹` envelope obeys the same `(2M₀ + (β−α)M₁)/|λ|` bound. -/
theorem abs_integral_re_mul_exp_le {A A' : ℝ → ℂ} {α β lam M₀ M₁ : ℝ}
    (hαβ : α ≤ β) (hlam : lam ≠ 0)
    (hA : ∀ u ∈ Set.uIcc α β, HasDerivAt A (A' u) u)
    (hA'c : ContinuousOn A' (Set.uIcc α β))
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖A u‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖A' u‖ ≤ M₁) :
    |∫ u in α..β, (A u * Complex.exp (-(Complex.I * lam) * u)).re| ≤
      (2 * M₀ + (β - α) * M₁) / |lam| := by
  have hAc : ContinuousOn A (Set.uIcc α β) := fun x hx =>
    (hA x hx).continuousAt.continuousWithinAt
  have hexp_cont : Continuous fun u : ℝ => Complex.exp (-(Complex.I * lam) * u) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hInt : IntervalIntegrable
      (fun u : ℝ => A u * Complex.exp (-(Complex.I * lam) * u))
      MeasureTheory.volume α β :=
    (hAc.mul hexp_cont.continuousOn).intervalIntegrable
  have hre : (∫ u in α..β, (A u * Complex.exp (-(Complex.I * lam) * u)).re) =
      (∫ u in α..β, A u * Complex.exp (-(Complex.I * lam) * u)).re := by
    simpa using ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hInt
  rw [hre]
  exact le_trans (Complex.abs_re_le_norm _)
    (norm_integral_mul_exp_le hαβ hlam hA hA'c hM₀ hM₁)

end RHTower

namespace RHTower

/-- Critical-line form of a Dirichlet monomial: `n^{−s}` at `s = 1/2 + iu` is the real
coefficient `n^{−1/2}` times the unimodular character `exp(−i(log n)u)`. -/
theorem natCast_cpow_neg_linePt (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    (n : ℂ) ^ (-(linePt u)) =
      (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
  rw [hlog]
  have hexpand : ((Real.log n : ℝ) : ℂ) * (-(linePt u)) =
      ((Real.log n * (-(1/2 : ℝ)) : ℝ) : ℂ) +
        (-(Complex.I * (Real.log n : ℂ)) * u) := by
    unfold linePt
    push_cast
    ring
  rw [hexpand, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp, ← Real.rpow_def_of_pos hnpos]

/-- Reflected critical-line form: `n^{−(1−s)}` at `s = 1/2 + iu` is the same real coefficient
`n^{−1/2}` times the opposite-frequency character `exp(+i(log n)u)`. -/
theorem natCast_cpow_neg_one_sub_linePt (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    (n : ℂ) ^ (-(1 - linePt u)) =
      (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
  rw [hlog]
  have hexpand : ((Real.log n : ℝ) : ℂ) * (-(1 - linePt u)) =
      ((Real.log n * (-(1/2 : ℝ)) : ℝ) : ℂ) +
        (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) := by
    unfold linePt
    push_cast
    ring
  rw [hexpand, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp, ← Real.rpow_def_of_pos hnpos]

/-- The `n`-th critical-line term of the completed carrier: the real coefficient `n^{−1/2}`
times the two archimedean-envelope oscillations at frequencies `±log n`. -/
noncomputable def carrierLineTerm (n : ℕ) (u : ℝ) : ℂ :=
  (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
    (archFactor (linePt u) * Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) +
     archFactor (linePt u) * zetaChi (linePt u) *
       Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u))

/-- **Termwise decomposition of the completed carrier on the critical line.**  The completed
carrier is the finite sum of its critical-line terms: each Dirichlet monomial contributes the
direct oscillation `exp(−i(log n)u)` with envelope `archFactor` and the reflected oscillation
`exp(+i(log n)u)` with envelope `archFactor·χ`. -/
theorem completedGN_line_term_decomp (N : ℕ) (u : ℝ) :
    completedGN N (linePt u) = ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u := by
  have h1 : dirichletPoly N (linePt u) = ∑ n ∈ Finset.Icc 1 N,
      (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u) := by
    unfold dirichletPoly
    exact Finset.sum_congr rfl fun n hn =>
      natCast_cpow_neg_linePt n (Finset.mem_Icc.mp hn).1 u
  have h2 : dirichletPoly N (1 - linePt u) = ∑ n ∈ Finset.Icc 1 N,
      (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u) := by
    unfold dirichletPoly
    exact Finset.sum_congr rfl fun n hn =>
      natCast_cpow_neg_one_sub_linePt n (Finset.mem_Icc.mp hn).1 u
  show archFactor (linePt u) * gN N (linePt u) = _
  unfold gN chiSymmetrize carrierLineTerm
  rw [h1, h2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **First-moment bound for the completed carrier on the critical line.**  With `C¹` data for
the two archimedean envelopes (`archFactor` and `archFactor·χ` along the line) — a common sup
`M₀`, a common derivative sup `M₁` — and a bound `Cmain` on the non-oscillating `n = 1` moment,
the first moment of the completed carrier obeys
`|∫ Re Φ̃_N| ≤ Cmain + Σ_{2 ≤ n ≤ N} n^{−1/2}·2(2M₀+(β−α)M₁)/log n`: every term beyond the
first gains its frequency `log n` through integration by parts. -/
theorem abs_integral_re_completedGN_line_le {N : ℕ} (hN : 1 ≤ N) {α β : ℝ} (hαβ : α ≤ β)
    {Adir' Aref' : ℝ → ℂ} {M₀ M₁ Cmain : ℝ}
    (hAdir : ∀ u ∈ Set.uIcc α β,
      HasDerivAt (fun u : ℝ => archFactor (linePt u)) (Adir' u) u)
    (hAref : ∀ u ∈ Set.uIcc α β,
      HasDerivAt (fun u : ℝ => archFactor (linePt u) * zetaChi (linePt u)) (Aref' u) u)
    (hdirC : ContinuousOn Adir' (Set.uIcc α β))
    (hrefC : ContinuousOn Aref' (Set.uIcc α β))
    (hM₀dir : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀ref : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u) * zetaChi (linePt u)‖ ≤ M₀)
    (hM₁dir : ∀ u ∈ Set.Icc α β, ‖Adir' u‖ ≤ M₁)
    (hM₁ref : ∀ u ∈ Set.Icc α β, ‖Aref' u‖ ≤ M₁)
    (hCmain : ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (linePt u) * zetaChi (linePt u)‖ ≤ Cmain) :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      Cmain + ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(1/2 : ℝ)) *
        (2 * (2 * M₀ + (β - α) * M₁) / Real.log n) := by
  have hAdirC : ContinuousOn (fun u : ℝ => archFactor (linePt u)) (Set.uIcc α β) :=
    fun x hx => (hAdir x hx).continuousAt.continuousWithinAt
  have hArefC : ContinuousOn (fun u : ℝ => archFactor (linePt u) * zetaChi (linePt u))
      (Set.uIcc α β) := fun x hx => (hAref x hx).continuousAt.continuousWithinAt
  have hexpC : ∀ lam : ℝ, Continuous fun u : ℝ => Complex.exp (-(Complex.I * lam) * u) :=
    fun lam => Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint_dir : ∀ n : ℕ, IntervalIntegrable
      (fun u : ℝ => archFactor (linePt u) *
        Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u))
      MeasureTheory.volume α β :=
    fun n => (hAdirC.mul (hexpC (Real.log n)).continuousOn).intervalIntegrable
  have hint_ref : ∀ n : ℕ, IntervalIntegrable
      (fun u : ℝ => archFactor (linePt u) * zetaChi (linePt u) *
        Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u))
      MeasureTheory.volume α β :=
    fun n => (hArefC.mul (hexpC (-Real.log n)).continuousOn).intervalIntegrable
  have hterm_int : ∀ n : ℕ, IntervalIntegrable (fun u : ℝ => carrierLineTerm n u)
      MeasureTheory.volume α β := by
    intro n
    unfold carrierLineTerm
    exact (continuousOn_const.mul
      ((hAdirC.mul (hexpC (Real.log n)).continuousOn).add
       (hArefC.mul (hexpC (-Real.log n)).continuousOn))).intervalIntegrable
  have hint_all : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun u : ℝ => carrierLineTerm n u) MeasureTheory.volume α β :=
    fun n _ => hterm_int n
  have hfsum_int : IntervalIntegrable
      (fun u : ℝ => ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u)
      MeasureTheory.volume α β := by
    have h2 : (fun u : ℝ => ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u) =
        ∑ n ∈ Finset.Icc 1 N, fun u : ℝ => carrierLineTerm n u := by
      funext u
      simp
    rw [h2]
    exact IntervalIntegrable.sum _ hint_all
  have hre_int : (∫ u in α..β, (∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u).re) =
      (∫ u in α..β, ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u).re := by
    simpa using ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hfsum_int
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hG1EqOn : Set.EqOn (fun u : ℝ => carrierLineTerm 1 u)
      (fun u : ℝ => archFactor (linePt u) + archFactor (linePt u) * zetaChi (linePt u))
      (Set.uIcc α β) := by
    intro u _
    unfold carrierLineTerm
    simp [Real.log_one, Real.one_rpow]
  have hhead : ‖∫ u in α..β, carrierLineTerm 1 u‖ ≤ Cmain := by
    have hG1eq : (∫ u in α..β, carrierLineTerm 1 u) =
        (∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (linePt u) * zetaChi (linePt u) := by
      rw [intervalIntegral.integral_congr hG1EqOn,
        intervalIntegral.integral_add hAdirC.intervalIntegrable hArefC.intervalIntegrable]
    rw [hG1eq]
    exact hCmain
  have htail : ∀ n ∈ Finset.Ioc 1 N, ‖∫ u in α..β, carrierLineTerm n u‖ ≤
      (n : ℝ) ^ (-(1/2 : ℝ)) * (2 * (2 * M₀ + (β - α) * M₁) / Real.log n) := by
    intro n hn
    have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have heq : (∫ u in α..β, carrierLineTerm n u) =
        (((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        ((∫ u in α..β, archFactor (linePt u) *
            Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u)) +
         ∫ u in α..β, archFactor (linePt u) * zetaChi (linePt u) *
            Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u)) := by
      unfold carrierLineTerm
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hint_dir n) (hint_ref n)]
    have heng1 := norm_integral_mul_exp_le (M₀ := M₀) (M₁ := M₁)
      hαβ hlogpos.ne' hAdir hdirC hM₀dir hM₁dir
    have heng2 := norm_integral_mul_exp_le (M₀ := M₀) (M₁ := M₁)
      hαβ (neg_ne_zero.mpr hlogpos.ne') hAref hrefC hM₀ref hM₁ref
    rw [abs_of_pos hlogpos] at heng1
    rw [abs_neg, abs_of_pos hlogpos] at heng2
    have hsum := le_trans (norm_add_le _ _) (add_le_add heng1 heng2)
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    refine le_trans (mul_le_mul_of_nonneg_left hsum
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (le_of_eq (by ring))
  calc |∫ u in α..β, (completedGN N (linePt u)).re|
      = |∫ u in α..β, (∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u).re| := by
        congr 1
        exact intervalIntegral.integral_congr fun u _ => by
          rw [completedGN_line_term_decomp N u]
    _ = |(∫ u in α..β, ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u).re| := by rw [hre_int]
    _ ≤ ‖∫ u in α..β, ∑ n ∈ Finset.Icc 1 N, carrierLineTerm n u‖ :=
        Complex.abs_re_le_norm _
    _ = ‖∑ n ∈ Finset.Icc 1 N, ∫ u in α..β, carrierLineTerm n u‖ := by
        rw [intervalIntegral.integral_finsetSum hint_all]
    _ = ‖(∫ u in α..β, carrierLineTerm 1 u) +
          ∑ n ∈ Finset.Ioc 1 N, ∫ u in α..β, carrierLineTerm n u‖ := by
        rw [← Finset.add_sum_erase _ _ h1mem, Finset.Icc_erase_left]
    _ ≤ ‖∫ u in α..β, carrierLineTerm 1 u‖ +
          ‖∑ n ∈ Finset.Ioc 1 N, ∫ u in α..β, carrierLineTerm n u‖ := norm_add_le _ _
    _ ≤ Cmain + ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(1/2 : ℝ)) *
          (2 * (2 * M₀ + (β - α) * M₁) / Real.log n) :=
        add_le_add hhead (le_trans (norm_sum_le _ _) (Finset.sum_le_sum htail))

end RHTower

namespace RHTower

/-- **Van der Corput first-derivative engine.**  For a `C¹` amplitude `g` and a `C²` real phase
`φ` whose derivative stays away from zero, `|φ′| ≥ m > 0`, integration by parts against the
exact antiderivative structure `e^{iφ} = (e^{iφ})′/(iφ′)` bounds the oscillatory integral by
`‖∫ g·e^{iφ}‖ ≤ 2Mg/m + (β−α)·(Mg′/m + Mg·Mφ″/m²)`.  This subsumes the linear-frequency
oscillation bound and applies to phases like `u·log n ± 2θ(u)` whose derivative is the
Riemann–Siegel frequency shift: cancellation holds wherever the shifted frequency avoids its
stationary point. -/
theorem norm_integral_mul_exp_phase_le
    {g g' : ℝ → ℂ} {φ φ' φ'' : ℝ → ℝ} {α β m Mg Mg' Mp : ℝ}
    (hαβ : α ≤ β) (hm : 0 < m)
    (hg : ∀ u ∈ Set.uIcc α β, HasDerivAt g (g' u) u)
    (hφ : ∀ u ∈ Set.uIcc α β, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u ∈ Set.uIcc α β, HasDerivAt φ' (φ'' u) u)
    (hg'c : ContinuousOn g' (Set.uIcc α β))
    (hφ''c : ContinuousOn φ'' (Set.uIcc α β))
    (hmφ : ∀ u ∈ Set.uIcc α β, m ≤ |φ' u|)
    (hMg : ∀ u ∈ Set.Icc α β, ‖g u‖ ≤ Mg)
    (hMg' : ∀ u ∈ Set.Icc α β, ‖g' u‖ ≤ Mg')
    (hMp : ∀ u ∈ Set.Icc α β, |φ'' u| ≤ Mp) :
    ‖∫ u in α..β, g u * Complex.exp (Complex.I * (φ u : ℂ))‖ ≤
      2 * (Mg / m) + (β - α) * (Mg' / m + Mg * Mp / m ^ 2) := by
  have huI : Set.uIcc α β = Set.Icc α β := Set.uIcc_of_le hαβ
  have hαmem : α ∈ Set.Icc α β := ⟨le_rfl, hαβ⟩
  have hβmem : β ∈ Set.Icc α β := ⟨hαβ, le_rfl⟩
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg α hαmem)
  have hMg'0 : 0 ≤ Mg' := le_trans (norm_nonneg _) (hMg' α hαmem)
  have hMp0 : 0 ≤ Mp := le_trans (abs_nonneg _) (hMp α hαmem)
  have hφne : ∀ u ∈ Set.uIcc α β, (Complex.I * (φ' u : ℂ)) ≠ 0 := by
    intro u hu
    refine mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
    intro hz
    have h1 := hmφ u hu
    rw [hz] at h1
    simp only [abs_zero] at h1
    linarith
  have hden : ∀ u ∈ Set.uIcc α β, HasDerivAt (fun u : ℝ => Complex.I * (φ' u : ℂ))
      (Complex.I * (φ'' u : ℂ)) u :=
    fun u hu => ((hφ' u hu).ofReal_comp).const_mul Complex.I
  have hG : ∀ u ∈ Set.uIcc α β,
      HasDerivAt (fun u : ℝ => g u / (Complex.I * (φ' u : ℂ)))
        ((g' u * (Complex.I * (φ' u : ℂ)) - g u * (Complex.I * (φ'' u : ℂ))) /
          (Complex.I * (φ' u : ℂ)) ^ 2) u :=
    fun u hu => (hg u hu).div (hden u hu) (hφne u hu)
  have hV : ∀ u ∈ Set.uIcc α β,
      HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)))
        (Complex.exp (Complex.I * (φ u : ℂ)) * (Complex.I * (φ' u : ℂ))) u :=
    fun u hu => (((hφ u hu).ofReal_comp).const_mul Complex.I).cexp
  have hgc : ContinuousOn g (Set.uIcc α β) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hφ'cont : ContinuousOn (fun u : ℝ => (φ' u : ℂ)) (Set.uIcc α β) :=
    Complex.continuous_ofReal.comp_continuousOn
      (fun x hx => (hφ' x hx).continuousAt.continuousWithinAt)
  have hφcont : ContinuousOn (fun u : ℝ => (φ u : ℂ)) (Set.uIcc α β) :=
    Complex.continuous_ofReal.comp_continuousOn
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
  have hdenc : ContinuousOn (fun u : ℝ => Complex.I * (φ' u : ℂ)) (Set.uIcc α β) :=
    continuousOn_const.mul hφ'cont
  have hexpc : ContinuousOn (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)))
      (Set.uIcc α β) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hφcont)
  have hG'int : IntervalIntegrable
      (fun u : ℝ => (g' u * (Complex.I * (φ' u : ℂ)) - g u * (Complex.I * (φ'' u : ℂ))) /
        (Complex.I * (φ' u : ℂ)) ^ 2) MeasureTheory.volume α β := by
    apply ContinuousOn.intervalIntegrable
    exact ((hg'c.mul hdenc).sub (hgc.mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hφ''c)))).div
      (hdenc.pow 2) (fun u hu => pow_ne_zero 2 (hφne u hu))
  have hV'int : IntervalIntegrable
      (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)) * (Complex.I * (φ' u : ℂ)))
      MeasureTheory.volume α β :=
    (hexpc.mul hdenc).intervalIntegrable
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => g u / (Complex.I * (φ' u : ℂ)))
    (u' := fun u : ℝ => (g' u * (Complex.I * (φ' u : ℂ)) -
      g u * (Complex.I * (φ'' u : ℂ))) / (Complex.I * (φ' u : ℂ)) ^ 2)
    (v := fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)))
    (v' := fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)) * (Complex.I * (φ' u : ℂ)))
    hG hV hG'int hV'int
  have hcongr : (∫ u in α..β, g u * Complex.exp (Complex.I * (φ u : ℂ))) =
      ∫ u in α..β, (g u / (Complex.I * (φ' u : ℂ))) *
        (Complex.exp (Complex.I * (φ u : ℂ)) * (Complex.I * (φ' u : ℂ))) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ (hφne u hu)]
  have hnormden : ∀ u : ℝ, ‖Complex.I * (φ' u : ℂ)‖ = |φ' u| := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hEnorm1 : ∀ u : ℝ, ‖Complex.exp (Complex.I * (φ u : ℂ))‖ = 1 := by
    intro u
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hbdry : ∀ u ∈ Set.Icc α β, ‖g u / (Complex.I * (φ' u : ℂ))‖ ≤ Mg / m := by
    intro u hu
    rw [norm_div, hnormden u]
    exact div_le_div₀ hMg0 (hMg u hu) hm (hmφ u (by rw [huI]; exact hu))
  have htail : ‖∫ u in α..β, (g' u * (Complex.I * (φ' u : ℂ)) -
      g u * (Complex.I * (φ'' u : ℂ))) / (Complex.I * (φ' u : ℂ)) ^ 2 *
      Complex.exp (Complex.I * (φ u : ℂ))‖ ≤
      (Mg' / m + Mg * Mp / m ^ 2) * |β - α| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc α β := by
      rw [Set.uIoc_of_le hαβ] at hx
      exact Set.Ioc_subset_Icc_self hx
    have hmu : m ≤ |φ' x| := hmφ x (by rw [huI]; exact hx')
    have hpu : 0 < |φ' x| := lt_of_lt_of_le hm hmu
    rw [norm_mul, hEnorm1 x, mul_one, norm_div]
    have hnum : ‖g' x * (Complex.I * (φ' x : ℂ)) - g x * (Complex.I * (φ'' x : ℂ))‖ ≤
        Mg' * |φ' x| + Mg * Mp := by
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
      · rw [norm_mul, hnormden x]
        exact mul_le_mul_of_nonneg_right (hMg' x hx') (abs_nonneg _)
      · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
        exact mul_le_mul (hMg x hx') (hMp x hx') (abs_nonneg _) hMg0
    have hden2 : ‖(Complex.I * (φ' x : ℂ)) ^ 2‖ = |φ' x| ^ 2 := by
      rw [norm_pow, hnormden x]
    rw [hden2]
    calc ‖g' x * (Complex.I * (φ' x : ℂ)) - g x * (Complex.I * (φ'' x : ℂ))‖ / |φ' x| ^ 2
        ≤ (Mg' * |φ' x| + Mg * Mp) / |φ' x| ^ 2 :=
          div_le_div₀
            (add_nonneg (mul_nonneg hMg'0 (abs_nonneg _)) (mul_nonneg hMg0 hMp0))
            hnum (by positivity) le_rfl
      _ = Mg' / |φ' x| + Mg * Mp / |φ' x| ^ 2 := by
          field_simp
      _ ≤ Mg' / m + Mg * Mp / m ^ 2 := by
          refine add_le_add (div_le_div₀ hMg'0 le_rfl hm hmu)
            (div_le_div₀ (mul_nonneg hMg0 hMp0) le_rfl (by positivity) ?_)
          nlinarith
  have habs : |β - α| = β - α := abs_of_nonneg (by linarith)
  calc ‖∫ u in α..β, g u * Complex.exp (Complex.I * (φ u : ℂ))‖
      = ‖(g β / (Complex.I * (φ' β : ℂ))) * Complex.exp (Complex.I * (φ β : ℂ)) -
          (g α / (Complex.I * (φ' α : ℂ))) * Complex.exp (Complex.I * (φ α : ℂ)) -
          ∫ u in α..β, (g' u * (Complex.I * (φ' u : ℂ)) -
            g u * (Complex.I * (φ'' u : ℂ))) / (Complex.I * (φ' u : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (φ u : ℂ))‖ := by
        rw [hcongr, hibp]
    _ ≤ ‖(g β / (Complex.I * (φ' β : ℂ))) * Complex.exp (Complex.I * (φ β : ℂ))‖ +
          ‖(g α / (Complex.I * (φ' α : ℂ))) * Complex.exp (Complex.I * (φ α : ℂ))‖ +
          ‖∫ u in α..β, (g' u * (Complex.I * (φ' u : ℂ)) -
            g u * (Complex.I * (φ'' u : ℂ))) / (Complex.I * (φ' u : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (φ u : ℂ))‖ := by
        exact le_trans (norm_sub_le _ _) (by gcongr; exact norm_sub_le _ _)
    _ ≤ Mg / m + Mg / m + (Mg' / m + Mg * Mp / m ^ 2) * |β - α| := by
        gcongr
        · rw [norm_mul, hEnorm1 β, mul_one]
          exact hbdry β hβmem
        · rw [norm_mul, hEnorm1 α, mul_one]
          exact hbdry α hαmem
    _ = 2 * (Mg / m) + (β - α) * (Mg' / m + Mg * Mp / m ^ 2) := by
        rw [habs]
        ring

end RHTower
