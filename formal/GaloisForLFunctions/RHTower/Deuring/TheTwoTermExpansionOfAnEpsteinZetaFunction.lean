import GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPoincareAbsoluteConvergence

/-!
# The two-term expansion of an Epstein zeta function

For reals `α` and `k > 0` let `Q(y, x) = (x + α y)² + (k y)²` and
`E(s) = ∑_{(y,x) ∈ ℤ²} Q(y,x)^{-s}` (`Re s > 1`; the term at the origin is `0`).

Comparing each row `y ≠ 0` with its integral (first-order Euler–Maclaurin,
`|∑_n f(θ + n) − ∫ f| ≤ ∫ |f'|`) gives

`E(s) = 2 ζ(2s) + 2 k^{1-2s} C(s) ζ(2s-1) + R(s)`,  `C(s) = √π Γ(s - 1/2)/Γ(s)`,

where `R` is holomorphic on `Re s > 1/2` and `|R(s)| ≤ |s| C(σ) k^{-2σ} ∑_{n ∈ ℤ} |n|^{-2σ}`
(`epsteinZeta_eq_epsteinCont`, `differentiableOn_epsteinCont`, `norm_epsteinRem_le`).

Consequence (`four_mul_sq_le_deuringBound`): if the right-hand side vanishes at a point `ρ` with
`Re ρ > 1/2`, then `4k² ≤ D(ρ)` for an explicit `D(ρ)`, because `ζ(2ρ) ≠ 0` while the other two
terms are `O(k^{1-2 Re ρ})`.
-/

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower.Deuring

open GaloisForLFunctions.RHTower.SelbergPoincareKernel
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation
  GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
  GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry

noncomputable section

/-! ### First-order Euler–Maclaurin on `ℤ` -/

section EulerMaclaurin

variable {f f' : ℝ → ℂ}

/-- On a unit interval, `f(c)` differs from the mean of `f` by at most `∫ |f'|`. -/
theorem norm_sub_intervalIntegral_le (hf : ∀ u, HasDerivAt f (f' u) u) (hf' : Integrable f')
    (c : ℝ) : ‖f c - ∫ u in c..c + 1, f u‖ ≤ ∫ u in c..c + 1, ‖f' u‖ := by
  have hc : c ≤ c + 1 := by linarith
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hfi : IntervalIntegrable f volume c (c + 1) := hcont.intervalIntegrable _ _
  have hnn : IntervalIntegrable (fun u => ‖f' u‖) volume c (c + 1) := hf'.norm.intervalIntegrable
  have hpt : ∀ u ∈ Set.uIoc c (c + 1), ‖f c - f u‖ ≤ ∫ v in c..c + 1, ‖f' v‖ := by
    intro u hu
    rw [Set.uIoc_of_le hc] at hu
    have hFTC : ∫ v in c..u, f' v = f u - f c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hf v) hf'.intervalIntegrable
    rw [← norm_neg, neg_sub, ← hFTC]
    refine (intervalIntegral.norm_integral_le_integral_norm hu.1.le).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hu.1.le hu.2
      (Eventually.of_forall fun v => norm_nonneg _) hnn
  have hconst : f c - ∫ u in c..c + 1, f u = ∫ u in c..c + 1, (f c - f u) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi, intervalIntegral.integral_const]
    simp
  rw [hconst]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  simpa using h

/-- **Euler–Maclaurin, first order.** If `f` and `f'` are integrable, the shifted integer samples
of `f` are absolutely summable and their sum is within `∫ |f'|` of `∫ f`. -/
theorem summable_norm_shift_and_bound (hf : ∀ u, HasDerivAt f (f' u) u) (hfi : Integrable f)
    (hf' : Integrable f') (θ : ℝ) :
    Summable (fun n : ℤ => ‖f (θ + n)‖) ∧
      ‖∑' n : ℤ, f (θ + n) - ∫ u, f u‖ ≤ ∫ u, ‖f' u‖ := by
  have hA := hfi.hasSum_intervalIntegral θ
  have hB := hf'.norm.hasSum_intervalIntegral θ
  have hC := hfi.norm.hasSum_intervalIntegral θ
  have hstep : ∀ n : ℤ, ‖f (θ + n) - ∫ u in θ + n..θ + n + 1, f u‖ ≤
      ∫ u in θ + n..θ + n + 1, ‖f' u‖ := fun n => norm_sub_intervalIntegral_le hf hf' (θ + n)
  have hsum : Summable (fun n : ℤ => ‖f (θ + n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hC.summable.add hB.summable)
    have h1 : ‖∫ u in θ + n..θ + n + 1, f u‖ ≤ ∫ u in θ + n..θ + n + 1, ‖f u‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    have h2 := norm_sub_norm_le (f (θ + n)) (∫ u in θ + n..θ + n + 1, f u)
    linarith [hstep n]
  refine ⟨hsum, ?_⟩
  have hD : HasSum (fun n : ℤ => f (θ + n) - ∫ u in θ + n..θ + n + 1, f u)
      (∑' n : ℤ, f (θ + n) - ∫ u, f u) := hsum.of_norm.hasSum.sub hA
  rw [← hD.tsum_eq]
  exact tsum_of_norm_bounded hB hstep

end EulerMaclaurin

/-! ### Rows of the kernel `(T/(u² + T²))^s` -/

/-- For a real exponent the kernel has norm `(T/(u² + T²))^σ`. -/
theorem norm_ker_zero_ofReal {T : ℝ} (hT : 0 < T) (σ u : ℝ) :
    ‖ker 0 T (σ : ℂ) u‖ = wt T u ^ σ := by
  rw [ker0_eq T hT, Complex.norm_cpow_eq_rpow_re_of_pos (wt_pos hT u), Complex.ofReal_re]

theorem summable_norm_ker_shift {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 1 / 2 < s.re) (θ : ℝ) :
    Summable (fun n : ℤ => ‖ker 0 T s (θ + n)‖) :=
  (summable_norm_shift_and_bound (fun u => (hasDerivAt_ker hT u).differentiableAt.hasDerivAt)
    (integrable_ker le_rfl hT hs) (integrable_deriv_ker le_rfl hT hs) θ).1

/-- A row of the kernel is within `|s| T^{-σ} C(σ)` of its integral `T^{1-s} C(s)`. -/
theorem norm_tsum_ker_shift_sub_le {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 1 / 2 < s.re) (θ : ℝ) :
    ‖∑' n : ℤ, ker 0 T s (θ + n) - (T : ℂ) ^ (1 - s) * cBeta s‖ ≤
      ‖s‖ * T ^ (-s.re) * cst s.re := by
  have h := (summable_norm_shift_and_bound
    (fun u => (hasDerivAt_ker hT u).differentiableAt.hasDerivAt)
    (integrable_ker le_rfl hT hs) (integrable_deriv_ker le_rfl hT hs) θ).2
  rw [integral_ker0_scale hT, integral_ker01 hs] at h
  refine h.trans ?_
  have hb : ∀ u, ‖deriv (ker 0 T s) u‖ ≤ ‖s‖ / T * wt T u ^ s.re := fun u => by
    have h' := norm_deriv_ker_le (s := s) (le_refl (0 : ℝ)) hT u
    simpa using h'
  have hTσ : 0 < T ^ s.re := Real.rpow_pos_of_pos hT _
  calc ∫ u, ‖deriv (ker 0 T s) u‖ ≤ ∫ u, ‖s‖ / T * wt T u ^ s.re :=
        integral_mono (integrable_deriv_ker le_rfl hT hs).norm
          ((integrable_wt_rpow hT hs).const_mul _) hb
    _ = ‖s‖ / T * (T ^ (1 - s.re) * cst s.re) := by rw [integral_const_mul, integral_wt_rpow hT]
    _ = ‖s‖ * T ^ (-s.re) * cst s.re := by
        rw [Real.rpow_sub hT, Real.rpow_one, Real.rpow_neg hT.le]
        field_simp

/-- The row sum of the kernel is holomorphic in `s` on `Re s > 1/2`. -/
theorem differentiableAt_tsum_ker_shift {T : ℝ} (hT : 0 < T) (θ : ℝ) {s₀ : ℂ}
    (hs₀ : 1 / 2 < s₀.re) : DifferentiableAt ℂ (fun s => ∑' n : ℤ, ker 0 T s (θ + n)) s₀ := by
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = (1 / 2 + s₀.re) / 2 := ⟨_, rfl⟩
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : ℝ, σ₂ = s₀.re + 1 := ⟨_, rfl⟩
  have h1 : 1 / 2 < σ₁ := by rw [hσ₁]; linarith
  have h2 : 1 / 2 < σ₂ := by rw [hσ₂]; linarith
  have hU : IsOpen ({s : ℂ | σ₁ < s.re} ∩ {s : ℂ | s.re < σ₂}) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : s₀ ∈ {s : ℂ | σ₁ < s.re} ∩ {s : ℂ | s.re < σ₂} :=
    ⟨by show σ₁ < s₀.re; rw [hσ₁]; linarith, by show s₀.re < σ₂; rw [hσ₂]; linarith⟩
  have hu : Summable (fun n : ℤ => wt T (θ + n) ^ σ₁ + wt T (θ + n) ^ σ₂) := by
    have a1 := summable_norm_ker_shift hT (s := (σ₁ : ℂ)) (by rw [Complex.ofReal_re]; exact h1) θ
    have a2 := summable_norm_ker_shift hT (s := (σ₂ : ℂ)) (by rw [Complex.ofReal_re]; exact h2) θ
    simp only [norm_ker_zero_ofReal hT] at a1 a2
    exact a1.add a2
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℤ) (s : ℂ) => ker 0 T s (θ + n)) hu
    (fun n => (differentiable_ker 0 T (θ + n)).differentiableOn) hU
    (fun n s hs => (norm_ker_le le_rfl hT s _).trans
      (rpow_le_add (wt_pos hT _) (le_of_lt hs.1) (le_of_lt hs.2)))
  exact hd.differentiableAt (hU.mem_nhds hmem)

/-! ### The form and its rows -/

/-- The positive definite form `Q(y, x) = (x + α y)² + (k y)²` on `ℤ²`; the first coordinate
is `y`. -/
def epForm (α k : ℝ) (p : ℤ × ℤ) : ℝ := ((p.2 : ℝ) + α * p.1) ^ 2 + (k * p.1) ^ 2

/-- Complex powers of a positive real through the real logarithm. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = cexp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le, mul_comm]

/-- A term of row `y ≠ 0` is `T^{-s}` times the kernel at `α y + x`, `T = k|y|`. -/
theorem epForm_cpow_eq (α : ℝ) {k : ℝ} (hk : 0 < k) {y : ℤ} (hy : y ≠ 0) (x : ℤ) (s : ℂ) :
    ((epForm α k (y, x) : ℝ) : ℂ) ^ (-s) =
      ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (-s) * ker 0 (k * |(y : ℝ)|) s (α * y + x) := by
  have hT : 0 < k * |(y : ℝ)| := mul_pos hk (abs_pos.mpr (by exact_mod_cast hy))
  have hq : epForm α k (y, x) = (α * y + x) ^ 2 + (k * |(y : ℝ)|) ^ 2 := by
    simp only [epForm, mul_pow, sq_abs]; ring
  have hqpos : 0 < (α * y + x) ^ 2 + (k * |(y : ℝ)|) ^ 2 := by
    nlinarith [sq_nonneg (α * y + x), mul_pos hT hT]
  have hlog : Real.log (wt (k * |(y : ℝ)|) (α * y + x)) =
      Real.log (k * |(y : ℝ)|) - Real.log ((α * y + x) ^ 2 + (k * |(y : ℝ)|) ^ 2) := by
    unfold wt; rw [Real.log_div hT.ne' hqpos.ne']
  rw [hq, ker0_eq _ hT, ofReal_cpow_eq_exp hqpos, ofReal_cpow_eq_exp hT,
    ofReal_cpow_eq_exp (wt_pos hT _), ← Complex.exp_add, hlog]
  congr 1
  push_cast
  ring

/-- The remainder of row `y`: `T^{-s} (∑_x κ(α y + x) − T^{1-s} C(s))` with `T = k|y|`,
`κ(u) = (T/(u² + T²))^s`; zero for `y = 0`. -/
def rowRem (α k : ℝ) (y : ℤ) (s : ℂ) : ℂ :=
  if y = 0 then 0 else
    ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (-s) *
      (∑' x : ℤ, ker 0 (k * |(y : ℝ)|) s (α * y + x) -
        ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (1 - s) * cBeta s)

/-- Row `y ≠ 0` is `(k|y|)^{1-2s} C(s)` plus its remainder. -/
theorem tsum_row_eq (α : ℝ) {k : ℝ} (hk : 0 < k) {y : ℤ} (hy : y ≠ 0) (s : ℂ) :
    ∑' x : ℤ, ((epForm α k (y, x) : ℝ) : ℂ) ^ (-s) =
      ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (1 - 2 * s) * cBeta s + rowRem α k y s := by
  have hT : 0 < k * |(y : ℝ)| := mul_pos hk (abs_pos.mpr (by exact_mod_cast hy))
  have hT0 : ((k * |(y : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hexp : (1 : ℂ) - 2 * s = -s + (1 - s) := by ring
  simp_rw [epForm_cpow_eq α hk hy, tsum_mul_left]
  rw [rowRem, if_neg hy, mul_sub, ← mul_assoc, ← Complex.cpow_add _ _ hT0, ← hexp]
  ring

theorem norm_rowRem_le (α : ℝ) {k : ℝ} (hk : 0 < k) (y : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖rowRem α k y s‖ ≤ ‖s‖ * cst s.re * (k * |(y : ℝ)|) ^ (-(2 * s.re)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [rowRem, if_pos rfl, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (cst_nonneg _))
      (Real.rpow_nonneg (mul_nonneg hk.le (abs_nonneg _)) _)
  · have hT : 0 < k * |(y : ℝ)| := mul_pos hk (abs_pos.mpr (by exact_mod_cast hy))
    rw [rowRem, if_neg hy, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT, Complex.neg_re]
    refine (mul_le_mul_of_nonneg_left (norm_tsum_ker_shift_sub_le hT hs (α * y))
      (Real.rpow_nonneg hT.le _)).trans (le_of_eq ?_)
    rw [show -(2 * s.re) = -s.re + -s.re by ring, Real.rpow_add hT]
    ring

/-- `∑_{n ∈ ℤ} |n|^{-x}`; equals `2 ζ(x)` for `x > 1` (the term at `0` vanishes). -/
def intAbsZeta (x : ℝ) : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-x)

theorem intAbsZeta_nonneg (x : ℝ) : 0 ≤ intAbsZeta x :=
  tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _

theorem hasSum_rowMajorant {k : ℝ} (hk : 0 < k) {σ : ℝ} (hσ : 1 / 2 < σ) (c : ℝ) :
    HasSum (fun y : ℤ => c * (k * |(y : ℝ)|) ^ (-(2 * σ)))
      (c * (k ^ (-(2 * σ)) * intAbsZeta (2 * σ))) := by
  have h := (Real.summable_abs_int_rpow (b := 2 * σ) (by linarith)).hasSum
  have h2 := (h.mul_left (k ^ (-(2 * σ)))).mul_left c
  have hfun : (fun y : ℤ => c * (k * |(y : ℝ)|) ^ (-(2 * σ))) =
      fun y : ℤ => c * (k ^ (-(2 * σ)) * |(y : ℝ)| ^ (-(2 * σ))) := by
    funext y; rw [Real.mul_rpow hk.le (abs_nonneg _)]
  rw [hfun]
  exact h2

theorem summable_rowRem (α : ℝ) {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun y : ℤ => rowRem α k y s) :=
  Summable.of_norm_bounded (hasSum_rowMajorant hk hs (‖s‖ * cst s.re)).summable
    (fun y => norm_rowRem_le α hk y hs)

/-- The remainder `R(s) = ∑_y ρ_y(s)` of the two-term expansion. -/
def epsteinRem (α k : ℝ) (s : ℂ) : ℂ := ∑' y : ℤ, rowRem α k y s

/-- `|R(s)| ≤ |s| C(σ) k^{-2σ} ∑_n |n|^{-2σ}` on `Re s > 1/2`. -/
theorem norm_epsteinRem_le (α : ℝ) {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖epsteinRem α k s‖ ≤ ‖s‖ * cst s.re * (k ^ (-(2 * s.re)) * intAbsZeta (2 * s.re)) :=
  tsum_of_norm_bounded (hasSum_rowMajorant hk hs (‖s‖ * cst s.re))
    (fun y => norm_rowRem_le α hk y hs)

theorem differentiableAt_rowRem (α : ℝ) {k : ℝ} (hk : 0 < k) (y : ℤ) {s₀ : ℂ}
    (hs₀ : 1 / 2 < s₀.re) : DifferentiableAt ℂ (rowRem α k y) s₀ := by
  rcases eq_or_ne y 0 with rfl | hy
  · have h0 : rowRem α k 0 = fun _ => 0 := by funext s; rw [rowRem, if_pos rfl]
    rw [h0]
    exact differentiableAt_const _
  · have hT : 0 < k * |(y : ℝ)| := mul_pos hk (abs_pos.mpr (by exact_mod_cast hy))
    have hT0 : ((k * |(y : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hfun : rowRem α k y = fun s => ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (-s) *
        (∑' x : ℤ, ker 0 (k * |(y : ℝ)|) s (α * y + x) -
          ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (1 - s) * cBeta s) := by
      funext s; rw [rowRem, if_neg hy]
    rw [hfun]
    have d1 : DifferentiableAt ℂ (fun s : ℂ => ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (-s)) s₀ :=
      differentiableAt_id.neg.const_cpow (Or.inl hT0)
    have d2 : DifferentiableAt ℂ (fun s : ℂ => ((k * |(y : ℝ)| : ℝ) : ℂ) ^ (1 - s)) s₀ :=
      ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl hT0)
    exact d1.mul ((differentiableAt_tsum_ker_shift hT (α * y) hs₀).sub
      (d2.mul (differentiableAt_cBeta hs₀)))

/-- The remainder is holomorphic on `Re s > 1/2`. -/
theorem differentiableAt_epsteinRem (α : ℝ) {k : ℝ} (hk : 0 < k) {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) :
    DifferentiableAt ℂ (epsteinRem α k) s₀ := by
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = (1 / 2 + s₀.re) / 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖s₀‖ + 1 := ⟨_, rfl⟩
  have h1 : 1 / 2 < σ₁ := by rw [hσ₁]; linarith
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hre₀ : s₀.re ≤ ‖s₀‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s₀)
  have hσM : σ₁ < M := by rw [hσ₁, hM]; linarith
  have hcσ : 0 ≤ cst σ₁ := cst_nonneg σ₁
  have hU : IsOpen ({s : ℂ | σ₁ < s.re} ∩ Metric.ball (0 : ℂ) M) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s₀ ∈ {s : ℂ | σ₁ < s.re} ∩ Metric.ball (0 : ℂ) M :=
    ⟨by show σ₁ < s₀.re; rw [hσ₁]; linarith, by
      rw [Metric.mem_ball, dist_zero_right, hM]; linarith⟩
  have hu : Summable (fun y : ℤ => M * cst σ₁ * (k * |(y : ℝ)|) ^ (-(2 * σ₁)) +
      M * cst σ₁ * (k * |(y : ℝ)|) ^ (-(2 * M))) :=
    (hasSum_rowMajorant hk h1 (M * cst σ₁)).summable.add
      (hasSum_rowMajorant hk (h1.trans hσM) (M * cst σ₁)).summable
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (y : ℤ) (s : ℂ) => rowRem α k y s) hu
    (fun y s hs => (differentiableAt_rowRem α hk y (h1.trans hs.1)).differentiableWithinAt) hU
    (fun y s hs => by
      have hsσ : 1 / 2 < s.re := h1.trans hs.1
      have hsM : ‖s‖ ≤ M := by
        have := hs.2; rw [Metric.mem_ball, dist_zero_right] at this; exact this.le
      have hre : s.re ≤ M := ((le_abs_self _).trans (Complex.abs_re_le_norm s)).trans hsM
      have hc : cst s.re ≤ cst σ₁ := cst_anti h1 (le_of_lt hs.1)
      rcases eq_or_ne y 0 with rfl | hy
      · rw [rowRem, if_pos rfl, norm_zero]
        exact add_nonneg
          (mul_nonneg (mul_nonneg hM0 hcσ) (Real.rpow_nonneg (mul_nonneg hk.le (abs_nonneg _)) _))
          (mul_nonneg (mul_nonneg hM0 hcσ) (Real.rpow_nonneg (mul_nonneg hk.le (abs_nonneg _)) _))
      · have hT : 0 < k * |(y : ℝ)| := mul_pos hk (abs_pos.mpr (by exact_mod_cast hy))
        have hs1 : σ₁ < s.re := hs.1
        have hr := rpow_le_add hT (lo := -(2 * M)) (a := -(2 * s.re)) (hi := -(2 * σ₁))
          (by linarith) (by linarith)
        refine (norm_rowRem_le α hk y hsσ).trans ?_
        calc ‖s‖ * cst s.re * (k * |(y : ℝ)|) ^ (-(2 * s.re))
            ≤ M * cst σ₁ * (k * |(y : ℝ)|) ^ (-(2 * s.re)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul hsM hc (cst_nonneg _) hM0)
                (Real.rpow_nonneg hT.le _)
          _ ≤ M * cst σ₁ * ((k * |(y : ℝ)|) ^ (-(2 * M)) + (k * |(y : ℝ)|) ^ (-(2 * σ₁))) :=
              mul_le_mul_of_nonneg_left hr (mul_nonneg hM0 hcσ)
          _ = _ := by ring)
  exact hd.differentiableAt (hU.mem_nhds hmem)

/-! ### The row `y = 0` and the main terms -/

/-- `∑_{n ∈ ℤ} |n|^{-w} = 2 ζ(w)` for `Re w > 1`; the term at `0` is `0`. -/
theorem hasSum_int_abs_cpow {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℤ => ((|(n : ℝ)| : ℝ) : ℂ) ^ (-w)) (2 * riemannZeta w) := by
  have hw0 : -w ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, Complex.zero_re] at hw
    linarith
  have hsm : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hw)
    simpa using h
  have hnat : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) (riemannZeta w) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    exact hsm.hasSum
  have e1 : ∀ n : ℕ, ((|(((n : ℤ) + 1 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-w) = 1 / ((n : ℂ) + 1) ^ w := by
    intro n
    have habs : |(((n : ℤ) + 1 : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; exact abs_of_nonneg (by positivity)
    rw [habs, Complex.cpow_neg, one_div, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one]
  have e2 : ∀ n : ℕ, ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-w) = 1 / ((n : ℂ) + 1) ^ w := by
    intro n
    have habs : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
    rw [habs, Complex.cpow_neg, one_div, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one]
  have h1 : HasSum (fun n : ℕ => ((|(((n : ℤ) + 1 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-w))
      (riemannZeta w) := by
    simp only [e1]; exact hnat
  have h2 : HasSum (fun n : ℕ => ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-w))
      (riemannZeta w) := by
    simp only [e2]; exact hnat
  have h0 : ((|((0 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-w) = 0 := by
    rw [Int.cast_zero, abs_zero, Complex.ofReal_zero, Complex.zero_cpow hw0]
  have h := HasSum.of_add_one_of_neg_add_one
    (f := fun m : ℤ => ((|(m : ℝ)| : ℝ) : ℂ) ^ (-w)) h1 h2
  simp only [h0, add_zero] at h
  rwa [← two_mul] at h

/-- On the row `y = 0` the form is `x²`. -/
theorem epForm_zero_cpow (α k : ℝ) (x : ℤ) {s : ℂ} (hs : s ≠ 0) :
    ((epForm α k (0, x) : ℝ) : ℂ) ^ (-s) = ((|(x : ℝ)| : ℝ) : ℂ) ^ (-(2 * s)) := by
  have hq : epForm α k (0, x) = |(x : ℝ)| ^ 2 := by simp [epForm]
  rw [hq]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow (neg_ne_zero.mpr hs),
      Complex.zero_cpow (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hs))]
  · have hpos : 0 < |(x : ℝ)| := abs_pos.mpr (by exact_mod_cast hx)
    rw [ofReal_cpow_eq_exp (pow_pos hpos 2), ofReal_cpow_eq_exp hpos, Real.log_pow]
    congr 1
    push_cast
    ring

/-! ### The Epstein zeta function -/

/-- The Epstein zeta function `∑_{p ∈ ℤ²} Q(p)^{-s}`; the term at the origin is `0`. -/
def epsteinZeta (α k : ℝ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, ((epForm α k p : ℝ) : ℂ) ^ (-s)

theorem summable_epForm_cpow (α : ℝ) {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℤ × ℤ => ((epForm α k p : ℝ) : ℂ) ^ (-s)) := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, Complex.zero_re] at hs
    linarith
  have hQ : ∀ p : ℤ × ℤ, _root_.RHTower.d4BMPoincareQuadratic ⟨α, k, hk⟩ p = epForm α k p := by
    intro p
    simp only [_root_.RHTower.d4BMPoincareQuadratic, epForm]
    ring
  have hbase := _root_.RHTower.summable_d4BMPoincareQuadratic_cpow_norm ⟨α, k, hk⟩ ⟨s, hs⟩
  have hnorm : Summable (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} =>
      ‖((epForm α k p.1 : ℝ) : ℂ) ^ (-s)‖) := by
    refine hbase.congr fun p => ?_
    have hpos : 0 < epForm α k p.1 := by
      rw [← hQ]; exact _root_.RHTower.d4BMPoincareQuadratic_pos _ p.1 p.2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, hQ]
  refine (Function.Injective.summable_iff Subtype.val_injective (fun p hp => ?_)).mp hnorm.of_norm
  have hp0 : p = (0, 0) := by
    by_contra h
    exact hp ⟨⟨p, h⟩, rfl⟩
  rw [hp0]
  simp [epForm, Complex.zero_cpow hs0]

/-- The right-hand side of the two-term expansion. -/
def epsteinCont (α k : ℝ) (s : ℂ) : ℂ :=
  2 * riemannZeta (2 * s) + 2 * (k : ℂ) ^ (1 - 2 * s) * cBeta s * riemannZeta (2 * s - 1) +
    epsteinRem α k s

/-- **Two-term expansion of the Epstein zeta function**, `Re s > 1`:
`E(s) = 2ζ(2s) + 2 k^{1-2s} C(s) ζ(2s-1) + R(s)`. -/
theorem epsteinZeta_eq_epsteinCont (α : ℝ) {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta α k s = epsteinCont α k s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hw : 1 < (2 * s - 1).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero, Complex.one_re]
    linarith
  have hw2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hw0 : -(2 * s - 1) ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, Complex.zero_re] at hw
    linarith
  have hrow : ∀ y : ℤ, ∑' x : ℤ, ((epForm α k (y, x) : ℝ) : ℂ) ^ (-s) =
      (if y = 0 then 2 * riemannZeta (2 * s) else 0) +
        (((|(y : ℝ)| : ℝ) : ℂ) ^ (-(2 * s - 1)) * ((k : ℂ) ^ (1 - 2 * s) * cBeta s) +
          rowRem α k y s) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · have hz : ((|((0 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-(2 * s - 1)) = 0 := by
        rw [Int.cast_zero, abs_zero, Complex.ofReal_zero, Complex.zero_cpow hw0]
      rw [if_pos rfl, hz, zero_mul, rowRem, if_pos rfl, add_zero, add_zero]
      simp_rw [epForm_zero_cpow α k _ hs0]
      exact (hasSum_int_abs_cpow hw2).tsum_eq
    · rw [if_neg hy, zero_add, tsum_row_eq α hk hy, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hk.le (abs_nonneg _), neg_sub]
      ring
  have hA := (hasSum_int_abs_cpow hw).mul_right ((k : ℂ) ^ (1 - 2 * s) * cBeta s)
  have hR := (summable_rowRem α hk (s := s) (by linarith)).hasSum
  have h0 : HasSum (fun y : ℤ => if y = 0 then 2 * riemannZeta (2 * s) else 0)
      (2 * riemannZeta (2 * s)) := hasSum_ite_eq 0 _
  rw [epsteinZeta, (summable_epForm_cpow α hk hs).tsum_prod, tsum_congr hrow,
    (h0.add (hA.add hR)).tsum_eq, epsteinCont, epsteinRem]
  ring

/-- The expansion is holomorphic on the punctured half-plane `{Re s > 1/2, s ≠ 1}`. -/
theorem differentiableOn_epsteinCont (α : ℝ) {k : ℝ} (hk : 0 < k) :
    DifferentiableOn ℂ (epsteinCont α k) {s | 1 / 2 < s.re ∧ s ≠ 1} := by
  rintro s ⟨hre, hne⟩
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have d1 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s)) s := by
    have h21 : 2 * s ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
        Complex.one_re] at h'
      linarith
    exact (differentiableAt_riemannZeta h21).comp s (differentiableAt_id.const_mul 2)
  have d2 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s - 1)) s := by
    have h21 : 2 * s - 1 ≠ 1 := fun h => hne (by linear_combination h / 2)
    exact (differentiableAt_riemannZeta h21).comp s
      ((differentiableAt_id.const_mul 2).sub_const 1)
  have d3 : DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) ^ (1 - 2 * s)) s :=
    ((differentiableAt_const 1).sub (differentiableAt_id.const_mul 2)).const_cpow (Or.inl hk0)
  have d : DifferentiableAt ℂ (fun s : ℂ => 2 * riemannZeta (2 * s) +
      2 * (k : ℂ) ^ (1 - 2 * s) * cBeta s * riemannZeta (2 * s - 1) + epsteinRem α k s) s :=
    ((d1.const_mul 2).add (((d3.const_mul 2).mul (differentiableAt_cBeta hre)).mul d2)).add
      (differentiableAt_epsteinRem α hk hre)
  exact d.differentiableWithinAt

/-! ### A zero of the expansion bounds `k` -/

/-- `A(ρ) = |C(ρ)| |ζ(2ρ - 1)| + |ρ| C(Re ρ) (∑_n |n|^{-2 Re ρ}) / 2`. -/
def deuringConst (ρ : ℂ) : ℝ :=
  ‖cBeta ρ‖ * ‖riemannZeta (2 * ρ - 1)‖ + ‖ρ‖ * cst ρ.re * intAbsZeta (2 * ρ.re) / 2

/-- The explicit bound `D(ρ) = 4 max(1, A(ρ)/|ζ(2ρ)|)^{2/(2 Re ρ - 1)}`. -/
def deuringBound (ρ : ℂ) : ℝ :=
  4 * max 1 (deuringConst ρ / ‖riemannZeta (2 * ρ)‖) ^ (2 / (2 * ρ.re - 1))

/-- If the expansion vanishes at `ρ` and `k ≥ 1`, then `|ζ(2ρ)| ≤ k^{1 - 2 Re ρ} A(ρ)`. -/
theorem norm_zeta_two_mul_le (α : ℝ) {k : ℝ} (hk : 1 ≤ k) {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (h0 : epsteinCont α k ρ = 0) :
    ‖riemannZeta (2 * ρ)‖ ≤ k ^ (1 - 2 * ρ.re) * deuringConst ρ := by
  have hk0 : 0 < k := by linarith
  have hR := norm_epsteinRem_le α hk0 hρ
  have hkk : k ^ (-(2 * ρ.re)) ≤ k ^ (1 - 2 * ρ.re) :=
    Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  have hnk : ‖(k : ℂ) ^ (1 - 2 * ρ)‖ = k ^ (1 - 2 * ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0]
    simp
  have heq : 2 * riemannZeta (2 * ρ) =
      -(2 * (k : ℂ) ^ (1 - 2 * ρ) * cBeta ρ * riemannZeta (2 * ρ - 1) + epsteinRem α k ρ) := by
    unfold epsteinCont at h0
    linear_combination h0
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hn : 2 * ‖riemannZeta (2 * ρ)‖ ≤
      2 * k ^ (1 - 2 * ρ.re) * ‖cBeta ρ‖ * ‖riemannZeta (2 * ρ - 1)‖ + ‖epsteinRem α k ρ‖ := by
    have h' := congrArg norm heq
    rw [norm_mul, norm_neg, h2] at h'
    rw [h']
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_mul, hnk, h2]
  have hW : 0 ≤ ‖ρ‖ * cst ρ.re := mul_nonneg (norm_nonneg _) (cst_nonneg _)
  have hR' : ‖epsteinRem α k ρ‖ ≤
      ‖ρ‖ * cst ρ.re * (k ^ (1 - 2 * ρ.re) * intAbsZeta (2 * ρ.re)) :=
    hR.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hkk (intAbsZeta_nonneg _)) hW)
  unfold deuringConst
  linarith

/-- **A zero of the expansion right of the critical line bounds the scale of the form**:
`4 k² ≤ D(ρ)`. -/
theorem four_mul_sq_le_deuringBound (α : ℝ) {k : ℝ} (hk : 0 < k) {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (h0 : epsteinCont α k ρ = 0) : 4 * k ^ 2 ≤ deuringBound ρ := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max 1 (deuringConst ρ / ‖riemannZeta (2 * ρ)‖) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; exact le_max_left _ _
  have he : 0 < 2 * ρ.re - 1 := by linarith
  have hk2 : k ^ 2 ≤ m ^ (2 / (2 * ρ.re - 1)) := by
    rcases lt_or_ge k 1 with hlt | hge
    · exact (pow_le_one₀ hk.le hlt.le).trans (Real.one_le_rpow hm1 (div_pos two_pos he).le)
    · have hz : riemannZeta (2 * ρ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by
        simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
        linarith)
      have hzn : 0 < ‖riemannZeta (2 * ρ)‖ := norm_pos_iff.mpr hz
      have hb := norm_zeta_two_mul_le α hge hρ h0
      have hone : k ^ (2 * ρ.re - 1) * k ^ (1 - 2 * ρ.re) = 1 := by
        rw [← Real.rpow_add hk, show 2 * ρ.re - 1 + (1 - 2 * ρ.re) = 0 by ring, Real.rpow_zero]
      have hpow : k ^ (2 * ρ.re - 1) ≤ deuringConst ρ / ‖riemannZeta (2 * ρ)‖ := by
        rw [le_div_iff₀ hzn]
        calc k ^ (2 * ρ.re - 1) * ‖riemannZeta (2 * ρ)‖
            ≤ k ^ (2 * ρ.re - 1) * (k ^ (1 - 2 * ρ.re) * deuringConst ρ) :=
              mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hk.le _)
          _ = deuringConst ρ := by rw [← mul_assoc, hone, one_mul]
      have hkm : k ^ (2 * ρ.re - 1) ≤ m := by rw [hm]; exact hpow.trans (le_max_right _ _)
      have h := Real.rpow_le_rpow (Real.rpow_nonneg hk.le _) hkm (div_pos two_pos he).le
      rw [← Real.rpow_mul hk.le, show (2 * ρ.re - 1) * (2 / (2 * ρ.re - 1)) = 2 by field_simp,
        Real.rpow_two] at h
      exact h
  rw [deuringBound, ← hm]
  linarith

end

end GaloisForLFunctions.RHTower.Deuring
