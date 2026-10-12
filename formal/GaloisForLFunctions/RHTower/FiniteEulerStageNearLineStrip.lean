import GaloisForLFunctions.RHTower.LogModulusHorizontal
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.RHTower.PrimeSmallDeviationArithmetic

/-!
# Finite Euler stages are zero-free near the critical line up to the critical height

The *finite Euler stage* of cutoff `X` is the functional-equation-symmetric function

  `Λ_X(s) = A_X(s) + A_X(1 − s)`,   `A_X(s) = Γ_ℝ(s) · exp(Σ_{n ≤ X} Λ(n) n^{−s} / log n)`,

built from the archimedean factor and the truncated Euler product written as an exponential (so
`A_X` has no zeros in `Re s > 0`).  It is real on the critical line and invariant under
`s ↦ 1 − s`.

**Theorem** (`eulerStage_ne_zero_near_line`).  Let `0 < u₀ < ½`.  At every height `|t| ≥ 4` with

  `log(|t| / 2π) > 6/|t| + W(X, u₀)`,   `W(X, u₀) = Σ_{n ≤ X} Λ(n) (n^{−½} + n^{u₀ − ½})`,

`Λ_X` has no zero with `0 < |Re s − ½| ≤ u₀`.

Mechanism: along `s = ½ + u + it` the function `g(u) = log|A_X(½+u+it)| − log|A_X(½−u−it)|`
vanishes at `u = 0` (conjugation symmetry), and its derivative is
`Re ψ_ℝ(½+u+it) + Re ψ_ℝ(½−u−it) − Re Σ Λ(n)(n^{−½−u−it} + n^{−½+u−it})`.  The digamma term is at
least `log(|t|/2π) − 6/|t|` and the prime term at most `W(X, u₀)`, so `g` increases.  Hence
`|A_X(s)| > |A_X(1 − s)|` and the two terms cannot cancel.

Since `W(X, 0⁺) = 2Σ_{n≤X} Λ(n)/√n ≈ 4√X`, the strip is guaranteed from height about `exp(4√X)`
on (`eulerStage_ne_zero_near_line_of_sqrt`).  The guarantee ends at the scale `X ≈ (log t)²`, where
the prime weight reaches the size `log(t/2π)` of the archimedean term.
-/

open Complex

namespace RHTower

noncomputable section

/-- The coefficient `Λ(n) / log n` of `log ζ`. -/
def eulerStageCoeff (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.log n

/-- The truncated logarithm of the Euler product, `Σ_{n ≤ X} Λ(n) n^{−s} / log n`. -/
def eulerStageLog (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1), (eulerStageCoeff n : ℂ) * (n : ℂ) ^ (-s)

/-- One half of the finite Euler stage: `Γ_ℝ(s) exp(Σ_{n ≤ X} Λ(n) n^{−s}/log n)`. -/
def eulerStageHalf (X : ℕ) (s : ℂ) : ℂ := Complex.Gammaℝ s * Complex.exp (eulerStageLog X s)

/-- The finite Euler stage `Λ_X(s) = A_X(s) + A_X(1 − s)`. -/
def eulerStage (X : ℕ) (s : ℂ) : ℂ := eulerStageHalf X s + eulerStageHalf X (1 - s)

/-- The prime weight `W(X, u₀) = Σ_{n ≤ X} Λ(n)(n^{−½} + n^{u₀−½})`. -/
def eulerStageWeight (X : ℕ) (u₀ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n *
    ((n : ℝ) ^ (-(1 / 2 : ℝ)) + (n : ℝ) ^ (u₀ - 1 / 2))

theorem eulerStage_one_sub (X : ℕ) (s : ℂ) : eulerStage X (1 - s) = eulerStage X s := by
  unfold eulerStage; rw [sub_sub_cancel]; ring

/-! ## Symmetry and nonvanishing of the half -/

theorem eulerStageLog_conj (X : ℕ) (s : ℂ) :
    eulerStageLog X (starRingEnd ℂ s) = starRingEnd ℂ (eulerStageLog X s) := by
  unfold eulerStageLog
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerStageCoeff]
  · congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Ne.symm Real.pi_ne_zero
    rw [← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem eulerStageHalf_conj (X : ℕ) (s : ℂ) :
    eulerStageHalf X (starRingEnd ℂ s) = starRingEnd ℂ (eulerStageHalf X s) := by
  unfold eulerStageHalf
  rw [Gammaℝ_conj, eulerStageLog_conj, Complex.exp_conj, map_mul]

theorem eulerStageHalf_ne_zero (X : ℕ) {s : ℂ} (hs : 0 < s.re) : eulerStageHalf X s ≠ 0 :=
  mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs) (Complex.exp_ne_zero _)

/-! ## The logarithmic derivative of the half -/

/-- `Λ(n) / log n · log n = Λ(n)`. -/
theorem eulerStageCoeff_mul_log (n : ℕ) :
    eulerStageCoeff n * Real.log n = ArithmeticFunction.vonMangoldt n := by
  unfold eulerStageCoeff
  rcases eq_or_ne (Real.log n) 0 with h | h
  · rw [h, div_zero, zero_mul]
    have hn : n = 0 ∨ n = 1 := by
      rcases Real.log_eq_zero.mp h with h' | h' | h'
      · left; exact_mod_cast h'
      · right; exact_mod_cast h'
      · exfalso; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    rcases hn with rfl | rfl <;> simp
  · field_simp

theorem hasDerivAt_eulerStageLog (X : ℕ) (s : ℂ) :
    HasDerivAt (eulerStageLog X)
      (-∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)) s := by
  unfold eulerStageLog
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro n _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eulerStageCoeff, CharP.cast_eq_zero, ArithmeticFunction.map_zero, zero_div,
      Complex.ofReal_zero, zero_mul, neg_zero]
    exact hasDerivAt_const _ _
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := ((hasDerivAt_neg s).const_cpow (c := (n : ℂ)) (Or.inl hn0)).const_mul
      (eulerStageCoeff n : ℂ)
    refine h.congr_deriv ?_
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hlog, ← eulerStageCoeff_mul_log n]
    push_cast
    ring

/-- `A_X′/A_X = ψ_ℝ − Σ_{n ≤ X} Λ(n) n^{−s}` on `Re s > 0`. -/
theorem hasDerivAt_eulerStageHalf (X : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (eulerStageHalf X)
      (eulerStageHalf X s * ((Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) -
        ∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s))) s := by
  have h := (hasDerivAt_Gammaℝ_of_re_pos hs).mul (hasDerivAt_eulerStageLog X s).cexp
  have hfun : eulerStageHalf X = fun y => Complex.Gammaℝ y * Complex.exp (eulerStageLog X y) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  ring

/-! ## Lower bound for the archimedean term -/

theorem re_digamma_half_ge {σ t : ℝ} (hσ : 0 < σ) (ht : 4 ≤ |t|) :
    Real.log (|t| / (2 * Real.pi)) - 6 / |t| ≤
      (Complex.digamma (((σ : ℂ) + t * I) / 2) - (Real.log Real.pi : ℂ)).re := by
  set z : ℂ := ((σ : ℂ) + t * I) / 2 with hz
  have hzre : 0 < z.re := by simp [hz]; linarith
  have hzim : z.im = t / 2 := by simp [hz]
  have hnorm : |t| / 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_div, abs_two] at this
    exact this
  have hz2 : 2 ≤ ‖z‖ := by linarith
  have hst := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2
  have hre : (Complex.log z).re - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
    have := (Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)).trans hst
    rw [Complex.sub_re] at this
    linarith [(abs_le.mp this).1]
  rw [Complex.log_re] at hre
  have hlog : Real.log (|t| / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by positivity) hnorm
  have hinv : 3 / ‖z‖ ≤ 6 / |t| := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hsplit : Real.log (|t| / (2 * Real.pi)) = Real.log (|t| / 2) - Real.log Real.pi := by
    rw [show |t| / (2 * Real.pi) = (|t| / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  rw [Complex.sub_re, Complex.ofReal_re, hsplit]
  linarith

/-! ## Dominance near the line -/

/-- The logarithmic derivative `ψ_ℝ(s) − Σ_{n ≤ X} Λ(n) n^{−s}` of the half. -/
def eulerStageLogDeriv (X : ℕ) (s : ℂ) : ℂ :=
  (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) -
    ∑ n ∈ Finset.range (X + 1), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)

theorem re_vonMangoldt_cpow_le (n : ℕ) (σ τ : ℝ) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + τ * I))).re ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    rw [Complex.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (le_of_eq ?_)) hΛ
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

/-- Lower bound for `Re` of the logarithmic derivative at height `|τ| ≥ 4`. -/
theorem re_eulerStageLogDeriv_ge (X : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 4 ≤ |τ|) :
    (Real.log (|τ| / (2 * Real.pi)) - 6 / |τ|) / 2 -
        ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) ≤
      (eulerStageLogDeriv X ((σ : ℂ) + τ * I)).re := by
  unfold eulerStageLogDeriv
  have hdig := re_digamma_half_ge hσ hτ
  rw [Complex.sub_re, Complex.re_sum]
  have harch : (Complex.digamma (((σ : ℂ) + τ * I) / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      (Complex.digamma (((σ : ℂ) + τ * I) / 2) - (Real.log Real.pi : ℂ)).re / 2 := by
    simp [Complex.sub_re]
    ring
  rw [harch]
  have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.range (X + 1)) =>
    re_vonMangoldt_cpow_le n σ τ
  linarith

theorem hasDerivAt_log_norm_eulerStageHalf_path (X : ℕ) {c v : ℂ} {u : ℝ}
    (hre : 0 < (c + u * v).re) :
    HasDerivAt (fun w : ℝ => Real.log ‖eulerStageHalf X (c + w * v)‖)
      ((v * eulerStageLogDeriv X (c + u * v)).re) u := by
  have hpath : HasDerivAt (fun w : ℝ => c + (w : ℂ) * v) v u := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const v).const_add c
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h
  have hA := (hasDerivAt_eulerStageHalf X hre).comp u hpath
  have hlog := hasDerivAt_log_norm_comp hA (eulerStageHalf_ne_zero X hre)
  refine hlog.congr_deriv ?_
  simp only [Function.comp_apply]
  unfold eulerStageLogDeriv
  congr 1
  field_simp [eulerStageHalf_ne_zero X hre]

/-- **Dominance.**  Under the height condition, `|A_X(½+u+it)| > |A_X(½−u−it)|` for
`0 < u ≤ u₀`. -/
theorem norm_eulerStageHalf_lt {X : ℕ} {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2) (ht : 4 ≤ |t|)
    (hcrit : 6 / |t| + eulerStageWeight X u₀ < Real.log (|t| / (2 * Real.pi)))
    {u : ℝ} (hu : 0 < u) (huu : u ≤ u₀) :
    ‖eulerStageHalf X (((1 / 2 - u : ℝ) : ℂ) + (-t : ℝ) * I)‖ <
      ‖eulerStageHalf X (((1 / 2 + u : ℝ) : ℂ) + t * I)‖ := by
  set cp : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hcp
  set cm : ℂ := ((1 / 2 : ℝ) : ℂ) + (-t : ℝ) * I with hcm
  have hpt : ∀ w : ℝ, cp + w * 1 = ((1 / 2 + w : ℝ) : ℂ) + t * I := fun w => by
    rw [hcp]; push_cast; ring
  have hmt : ∀ w : ℝ, cm + w * (-1) = ((1 / 2 - w : ℝ) : ℂ) + (-t : ℝ) * I := fun w => by
    rw [hcm]; push_cast; ring
  set g : ℝ → ℝ := fun w => Real.log ‖eulerStageHalf X (cp + w * 1)‖ -
    Real.log ‖eulerStageHalf X (cm + w * (-1))‖ with hg
  have hre_p : ∀ w : ℝ, 0 ≤ w → 0 < (cp + w * 1).re := fun w hw => by
    rw [hpt]; simp; linarith
  have hre_m : ∀ w : ℝ, w < 1 / 2 → 0 < (cm + w * (-1)).re := fun w hw => by
    rw [hmt]; simp; linarith
  have hderiv : ∀ w ∈ Set.Icc (0 : ℝ) u₀, HasDerivAt g
      ((1 * eulerStageLogDeriv X (cp + w * 1)).re -
        ((-1) * eulerStageLogDeriv X (cm + w * (-1))).re) w := fun w hw =>
    (hasDerivAt_log_norm_eulerStageHalf_path X (hre_p w hw.1)).sub
      (hasDerivAt_log_norm_eulerStageHalf_path X (hre_m w (by linarith [hw.2])))
  have hpos : ∀ w ∈ Set.Icc (0 : ℝ) u₀, 0 < (1 * eulerStageLogDeriv X (cp + w * 1)).re -
      ((-1) * eulerStageLogDeriv X (cm + w * (-1))).re := by
    intro w hw
    rw [one_mul, neg_one_mul, Complex.neg_re, sub_neg_eq_add, hpt, hmt]
    have h1 := re_eulerStageLogDeriv_ge X (σ := 1 / 2 + w) (τ := t) (by linarith [hw.1]) ht
    have h2 := re_eulerStageLogDeriv_ge X (σ := 1 / 2 - w) (τ := -t) (by linarith [hw.2])
      (by rwa [abs_neg])
    rw [abs_neg] at h2
    have hW : ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + w)) +
        ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 - w)) ≤
        eulerStageWeight X u₀ := by
      unfold eulerStageWeight
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hw.1]))
          (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hw.2]))
    linarith
  have hcont : ContinuousOn g (Set.Icc 0 u) := fun w hw =>
    (hderiv w ⟨hw.1, hw.2.trans huu⟩).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ hu hcont
    (fun w hw => hderiv w ⟨hw.1.le, hw.2.le.trans huu⟩)
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero, zero_mul, add_zero]
    have hconj : cm = starRingEnd ℂ cp := by
      rw [hcm, hcp]; apply Complex.ext <;> simp
    rw [hconj, eulerStageHalf_conj, Complex.norm_conj, sub_self]
  have hgu : 0 < g u := by
    have hp := hpos c ⟨hc.1.le, hc.2.le.trans huu⟩
    rw [hslope, hg0, sub_zero, sub_zero] at hp
    exact (div_pos_iff_of_pos_right hu).mp hp
  have hm := hre_m u (by linarith)
  have hp := hre_p u hu.le
  simp only [hg] at hgu
  rw [hmt] at hm hgu
  rw [hpt] at hp hgu
  exact (Real.log_lt_log_iff (norm_pos_iff.mpr (eulerStageHalf_ne_zero X hm))
    (norm_pos_iff.mpr (eulerStageHalf_ne_zero X hp))).mp (by linarith)

/-- **The finite Euler stage has no zero near the critical line above the critical height.**
For `0 < u₀ < ½`, `|t| ≥ 4` and `log(|t|/2π) > 6/|t| + W(X, u₀)`, no zero of `Λ_X` lies at height
`t` with `0 < |Re s − ½| ≤ u₀`. -/
theorem eulerStage_ne_zero_near_line {X : ℕ} {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2) (ht : 4 ≤ |t|)
    (hcrit : 6 / |t| + eulerStageWeight X u₀ < Real.log (|t| / (2 * Real.pi)))
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀) :
    eulerStage X ((σ : ℂ) + t * I) ≠ 0 := by
  have key : ∀ τ : ℝ, |τ| = |t| → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      eulerStage X (((1 / 2 + u : ℝ) : ℂ) + τ * I) ≠ 0 := by
    intro τ hτ u hu huu h
    have hlt := norm_eulerStageHalf_lt (X := X) (t := τ) hu₀ (hτ ▸ ht) (by rwa [hτ]) hu huu
    have hrefl : 1 - (((1 / 2 + u : ℝ) : ℂ) + τ * I) = ((1 / 2 - u : ℝ) : ℂ) + (-τ : ℝ) * I := by
      push_cast; ring
    unfold eulerStage at h
    rw [hrefl, add_eq_zero_iff_eq_neg] at h
    rw [h, norm_neg] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne (abs_pos.mp hσ) with hlt | hgt
  · rw [← eulerStage_one_sub]
    have hrefl : 1 - ((σ : ℂ) + t * I) = ((1 / 2 + (1 / 2 - σ) : ℝ) : ℂ) + (-t : ℝ) * I := by
      push_cast; ring
    rw [hrefl]
    rw [abs_of_neg (by linarith)] at hσu
    exact key (-t) (abs_neg t) (1 / 2 - σ) (by linarith) (by linarith)
  · rw [abs_of_pos (by linarith)] at hσu
    have h := key t rfl (σ - 1 / 2) (by linarith) hσu
    rwa [show ((1 / 2 + (σ - 1 / 2) : ℝ) : ℂ) = (σ : ℂ) by push_cast; ring] at h

/-- `W(X, u₀) ≤ (1 + X^{u₀}) (2 log 4 + 16) √X`. -/
theorem eulerStageWeight_le {X : ℕ} (hX : 1 ≤ X) {u₀ : ℝ} (hu₀ : 0 ≤ u₀) :
    eulerStageWeight X u₀ ≤
      (1 + (X : ℝ) ^ u₀) * ((2 * Real.log 4 + 16) * Real.sqrt X) := by
  have hcheb := PrimeSmallDeviation.sum_range_vonMangoldt_div_sqrt_le hX
  have hpt : ∀ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) + (n : ℝ) ^ (u₀ - 1 / 2)) ≤
      (1 + (X : ℝ) ^ u₀) * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hnX : (n : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hn1 : (0 : ℝ) < n := by exact_mod_cast hn0
      have hsq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hn1.le, one_div]
        norm_num
      have hsq' : (n : ℝ) ^ (u₀ - 1 / 2) = (n : ℝ) ^ u₀ / Real.sqrt n := by
        rw [Real.rpow_sub hn1, Real.sqrt_eq_rpow]
      have hpow : (n : ℝ) ^ u₀ ≤ (X : ℝ) ^ u₀ := Real.rpow_le_rpow hn1.le hnX hu₀
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      rw [hsq, hsq', ← add_div]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      calc ArithmeticFunction.vonMangoldt n * ((1 + (n : ℝ) ^ u₀) / Real.sqrt n)
          ≤ ArithmeticFunction.vonMangoldt n * ((1 + (X : ℝ) ^ u₀) / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hs.le) hΛ
        _ = (1 + (X : ℝ) ^ u₀) * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by ring
  calc eulerStageWeight X u₀ ≤ ∑ n ∈ Finset.range (X + 1),
        (1 + (X : ℝ) ^ u₀) * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) :=
        Finset.sum_le_sum hpt
    _ = (1 + (X : ℝ) ^ u₀) * ∑ n ∈ Finset.range (X + 1),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcheb (by positivity)

/-- **Explicit form.**  The strip `0 < |Re s − ½| ≤ u₀` carries no zero of `Λ_X` at heights with
`log(|t|/2π) > 6/|t| + (1 + X^{u₀})(2 log 4 + 16)√X`; for `u₀ = 1/log X` the threshold is
`log |t| ≍ √X`. -/
theorem eulerStage_ne_zero_near_line_of_sqrt {X : ℕ} (hX : 1 ≤ X) {u₀ t : ℝ} (hu₀0 : 0 ≤ u₀)
    (hu₀ : u₀ < 1 / 2) (ht : 4 ≤ |t|)
    (hcrit : 6 / |t| + (1 + (X : ℝ) ^ u₀) * ((2 * Real.log 4 + 16) * Real.sqrt X) <
      Real.log (|t| / (2 * Real.pi)))
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀) :
    eulerStage X ((σ : ℂ) + t * I) ≠ 0 :=
  eulerStage_ne_zero_near_line hu₀ ht
    (lt_of_le_of_lt (by linarith [eulerStageWeight_le hX hu₀0]) hcrit) hσ hσu

end

end RHTower
