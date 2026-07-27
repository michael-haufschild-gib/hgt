import GaloisForLFunctions.RHTower.DirichletLZeroHalfPlane
import GaloisForLFunctions.RHTower.EvenIndexHermitianOrderUpperBound
import GaloisForLFunctions.HTGeometry.LogOrderLimsupLower

/-!
# The twisted order law from below

A failure of the subpower bound at a single index upgrades to a recurring failure: a bound valid
outside a finite set can be globalized by enlarging the constant.  So whenever no subpower bound of
exponent below `θ` can hold, the twisted Hermitian mixed convolution coefficients exceed every
constant multiple of `(N+1)^α` infinitely often for each `α < θ`, and the logarithmic order exponent
`Ψ_{χ,k} = limsup log(1 + max(Re R_{χ,k}(N), 0)) / log(N+1)` is at least `θ`.

An `L`-zero at `ρ` supplies `θ = 2k·Re ρ - 1`, which is the lower half of the order law `(R3)`.
Since the zero divisor reaches the critical line, `θ = k - 1` is always available, giving the
omega-plus statement `(R5)`.  The upper half `Ψ_{χ,k} ≤ 2k - 1` is
`limsup_log_mixedAdditiveConvolutionPower_re_le`.
-/

open Complex Filter
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- A subpower bound valid outside a finite set holds globally after enlarging the constant. -/
theorem exists_global_subpower {f : ℕ → ℝ} {α C : ℝ} (hC : 0 ≤ C) (S : Finset ℕ)
    (h : ∀ M : ℕ, M ∉ S → f M ≤ C * ((M : ℝ) + 1) ^ α) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ M : ℕ, f M ≤ C' * ((M : ℝ) + 1) ^ α := by
  classical
  have hsum0 : 0 ≤ ∑ M ∈ S, max (f M / ((M : ℝ) + 1) ^ α) 0 :=
    Finset.sum_nonneg fun M _ => le_max_right _ _
  refine ⟨C + ∑ M ∈ S, max (f M / ((M : ℝ) + 1) ^ α) 0, by linarith, fun M => ?_⟩
  have hpow : (0 : ℝ) < ((M : ℝ) + 1) ^ α := by positivity
  by_cases hM : M ∈ S
  · have hterm : max (f M / ((M : ℝ) + 1) ^ α) 0
        ≤ ∑ K ∈ S, max (f K / ((K : ℝ) + 1) ^ α) 0 :=
      Finset.single_le_sum (f := fun K : ℕ => max (f K / ((K : ℝ) + 1) ^ α) 0)
        (fun K _ => le_max_right _ _) hM
    have hdiv : f M / ((M : ℝ) + 1) ^ α
        ≤ C + ∑ K ∈ S, max (f K / ((K : ℝ) + 1) ^ α) 0 := by
      have hmax := le_max_left (f M / ((M : ℝ) + 1) ^ α) 0
      linarith
    rwa [div_le_iff₀ hpow] at hdiv
  · have hb := h M hM
    nlinarith [hpow, hsum0]

/-- **Recurrence of large values.**  If no subpower bound of exponent `α` holds with any constant,
then every constant multiple of `(M+1)^α` is exceeded infinitely often. -/
theorem frequently_lt_of_no_subpower {a : ℕ → ℂ} {k : ℕ} {α : ℝ}
    (hno : ∀ C : ℝ, 0 ≤ C →
      ¬ (∀ M : ℕ, (mixedAdditiveConvolutionPower a k M).re ≤ C * ((M : ℝ) + 1) ^ α))
    (C : ℝ) :
    ∃ᶠ M : ℕ in atTop,
      C * ((M : ℝ) + 1) ^ α < (mixedAdditiveConvolutionPower a k M).re := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hcon
  have hout : ∀ M : ℕ, M ∉ Finset.range M₀ →
      (mixedAdditiveConvolutionPower a k M).re ≤ max C 0 * ((M : ℝ) + 1) ^ α := by
    intro M hM
    have hMle : M₀ ≤ M := by
      by_contra hlt'
      exact hM (Finset.mem_range.mpr (not_le.mp hlt'))
    have hb := not_lt.mp (hM₀ M hMle)
    have hpow : (0 : ℝ) < ((M : ℝ) + 1) ^ α := by positivity
    have hmax : C * ((M : ℝ) + 1) ^ α ≤ max C 0 * ((M : ℝ) + 1) ^ α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
    linarith
  obtain ⟨C', hC', hglob⟩ := exists_global_subpower (le_max_right C 0) (Finset.range M₀) hout
  exact hno C' hC' hglob

/-- **Logarithmic order from below.**  If no subpower bound of exponent below `θ` holds, the
logarithmic order exponent is at least `θ`. -/
theorem le_limsup_of_no_subpower_below {a : ℕ → ℂ} {k D : ℕ} {θ : ℝ}
    (hpoly : ∀ M : ℕ, (mixedAdditiveConvolutionPower a k M).re ≤ ((M : ℝ) + 1) ^ D)
    (hno : ∀ α C : ℝ, 0 ≤ α → 0 ≤ C → α < θ →
      ¬ (∀ M : ℕ, (mixedAdditiveConvolutionPower a k M).re
          ≤ C * ((M : ℝ) + 1) ^ α)) :
    θ ≤ Filter.limsup
      (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower a k M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  set F : ℕ → ℝ := fun M =>
    max (mixedAdditiveConvolutionPower a k M).re 0 with hF
  have hF0 : ∀ M, 0 ≤ F M := fun M => le_max_right _ _
  have hFb : ∀ M, F M ≤ 1 * ((M : ℝ) + 1) ^ D := by
    intro M
    refine max_le ?_ (by positivity)
    simpa using hpoly M
  have hbdd := GaloisForLFunctions.HTGeometry.isBoundedUnder_log_one_add_div_log
    (f := F) (C := 1) (d := D) one_pos hF0 hFb
  set Ψ : ℝ := Filter.limsup (fun M => Real.log (1 + F M) / Real.log ((M : ℝ) + 1)) atTop with hΨ
  have hstep : ∀ β : ℝ, 0 ≤ β → β < θ → β ≤ Ψ := by
    intro β hβ0 hβlt
    refine GaloisForLFunctions.HTGeometry.le_limsup_log_one_add_div_log hbdd ?_
    have hfreq := frequently_lt_of_no_subpower
      (fun C hC => hno β C hβ0 hC hβlt) 1
    refine hfreq.mono fun M hM => ?_
    have h1 : ((M : ℝ) + 1) ^ β
        ≤ (mixedAdditiveConvolutionPower a k M).re := by linarith [hM]
    exact h1.trans (le_max_left _ _)
  have hzero : (0 : ℝ) ≤ Ψ := by
    refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_) hbdd
    filter_upwards with M
    refine div_nonneg (Real.log_nonneg (by linarith [hF0 M])) (Real.log_nonneg ?_)
    have hMc := Nat.cast_nonneg (α := ℝ) M
    linarith
  rcases le_or_gt θ Ψ with h | h
  · exact h
  · exfalso
    have hmid : Ψ < (Ψ + θ) / 2 := by linarith
    have hmid2 : (Ψ + θ) / 2 < θ := by linarith
    have hmid0 : 0 ≤ (Ψ + θ) / 2 := by linarith
    exact absurd (hstep _ hmid0 hmid2) (not_le.mpr hmid)

/-- **The order law `(R3)` from below.**  An `L`-zero at `ρ` forces the logarithmic order exponent
of the twisted Hermitian mixed convolution power to be at least `2k·Re ρ - 1`. -/
theorem two_mul_re_sub_one_le_limsup_twistedMixedAdditiveConvolutionPower
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {j : ℕ} {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    2 * ((j : ℝ) + 1) * ρ.re - 1 ≤ Filter.limsup
      (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  refine le_limsup_of_no_subpower_below (D := 2 * j + 1) (fun M => ?_) fun α C hα hC hlt => ?_
  · have hb := norm_mixedAdditiveConvolutionPower_le_pow hcoeff j M
    have hre := Complex.re_le_norm (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M)
    exact hre.trans hb
  have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hρre : (α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) < ρ.re := by
    rw [div_lt_iff₀ hkR]
    push_cast at hlt ⊢
    linarith
  exact not_twistedMixedSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hα hC hzero hρre

/-- **The omega-plus law `(R5)`, twisted form.**  For every exponent below `k - 1` and every
constant, the twisted Hermitian mixed convolution coefficient exceeds `C (M+1)^α` infinitely
often. -/
theorem frequently_lt_re_twistedMixedAdditiveConvolutionPower
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {k : ℕ} (hk : 0 < k) {α : ℝ} (hα : 0 ≤ α) (hlt : α < (k : ℝ) - 1) (C : ℝ) :
    ∃ᶠ M : ℕ in atTop,
      C * ((M : ℝ) + 1) ^ α < (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re :=
  frequently_lt_of_no_subpower
    (fun _ hC' => not_twistedMixedSubpower_of_lt_sub_one hχ hprim hk hα hC' hlt) C

/-- **`Ψ_{χ,k} ≥ k - 1`.**  Specializing the order law at the critical line: the zero divisor of a
nontrivial primitive character reaches `Re ≥ 1/2`. -/
theorem sub_one_le_limsup_twistedMixedAdditiveConvolutionPower
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {j : ℕ} :
    (j : ℝ) ≤ Filter.limsup
      (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  obtain ⟨ρ, hρre, hzero⟩ := exists_LFunction_eq_zero_half_le_re hχ hprim
  refine le_trans ?_
    (two_mul_re_sub_one_le_limsup_twistedMixedAdditiveConvolutionPower hχ (j := j) hzero)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [hρre, hj]

end RHTower
