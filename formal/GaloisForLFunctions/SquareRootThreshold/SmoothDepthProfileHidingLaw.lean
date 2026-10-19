import GaloisForLFunctions.SquareRootThreshold.DepthProfileFourierModeLaw
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Smooth depth profiles hide up to a logarithmic aperture

A run with a sharp edge is visible at aperture `O(1/δ)` (`OffLineRunEdgeVisibilityLaw`), while a
uniform depth hides up to the Nyquist ceiling `L/2` (`DepthProfileNyquistCeiling`). This module
quantifies the regime in between: **smooth** depth modulations.

Let `d` be a depth profile of period `P` with values in `[0, δ]` whose cyclic first and second
differences are at most `κ₁` and `κ₂`. Two periodic summations by parts
(`one_sub_mul_sum_pow`) give, for `1 ≤ m ≤ P/2` and `v = mL/P`,

`|D(m)| ≤ P³ (2vκ₂ sinh(vδ) + 4v²κ₁² cosh(vδ)) / (16 m²)`  (`norm_depthSymbol_le_of_smooth`),

because the second difference of `cosh(v·d)` is controlled by the mean value theorem
(`abs_second_diff_cosh_le`) and `|1 − e^{2πim/P}| ≥ 4m/P`. Summing the modes against the
Gershgorin criterion of `DepthProfileFourierModeLaw` gives (`profileConfig_weil_nonneg_of_smooth`):
the profile is invisible at every aperture `a ≤ L/4` with

`P L κ₂ sinh(2δa)(1 + log n)/8 + n L² κ₁² cosh(2δa)/4 ≤ 1`,  `n = ⌈2aP/L⌉`.

For a smooth profile of amplitude `δ` and period `P` (in lattice units) one has `κ₁ ≍ δ/P` and
`κ₂ ≍ δ/P²`, so the condition reads `e^{2δa} ≲ P/(δL log P)`: the profile hides up to aperture
`≈ (1/2δ) log(P/(δL))`, i.e. logarithmically in the modulation length `Λ = 2πP/L` measured in units
of the depth. Edges (`Λ → 0`) are seen at `O(1/δ)`, smooth modulations at `(1/2δ) log(Λ/δ)`, and the
uniform lattice (`Λ = ∞`) only at the ceiling `L/2`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Periodic summation by parts -/

/-- Along the cyclic rotation, a `(n+1)`-th root of unity picks up one factor `ω`. -/
theorem pow_finRotate {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (r : Fin (n + 1)) :
    ω ^ ((finRotate (n + 1) r : Fin (n + 1)) : ℕ) = ω * ω ^ (r : ℕ) := by
  by_cases h : r = Fin.last n
  · subst h
    rw [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last, ← pow_succ', hω]
  · rw [coe_finRotate_of_ne_last h, pow_succ']

/-- The cyclic backward difference `∇g(r) = g(r) − g(r − 1)`. -/
def backDiff {n : ℕ} (g : Fin (n + 1) → ℂ) (r : Fin (n + 1)) : ℂ :=
  g r - g ((finRotate (n + 1)).symm r)

/-- **Periodic summation by parts.** `(1 − ω) Σ_r g(r) ω^r = Σ_r ∇g(r) ω^r` for `ω^{n+1} = 1`. -/
theorem one_sub_mul_sum_pow {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (g : Fin (n + 1) → ℂ) :
    (1 - ω) * ∑ r, g r * ω ^ (r : ℕ) = ∑ r, backDiff g r * ω ^ (r : ℕ) := by
  have hshift : ∑ r, g ((finRotate (n + 1)).symm r) * ω ^ (r : ℕ) =
      ω * ∑ r, g r * ω ^ (r : ℕ) := by
    rw [← Equiv.sum_comp (finRotate (n + 1)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Equiv.symm_apply_apply, pow_finRotate hω]
    ring
  simp only [backDiff, sub_mul, Finset.sum_sub_distrib, hshift]
  ring

/-- Two summations by parts: `|Σ_r g(r) ω^r| ≤ Σ_r |∇²g(r)| / |1 − ω|²`. -/
theorem norm_sum_pow_le {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (hω1 : ω ≠ 1) (hωn : ‖ω‖ = 1)
    (g : Fin (n + 1) → ℂ) :
    ‖∑ r, g r * ω ^ (r : ℕ)‖ ≤ (∑ r, ‖backDiff (backDiff g) r‖) / ‖1 - ω‖ ^ 2 := by
  have h1 : (1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have h2 : (1 - ω) ^ 2 * ∑ r, g r * ω ^ (r : ℕ) = ∑ r, backDiff (backDiff g) r * ω ^ (r : ℕ) := by
    rw [sq, mul_assoc, one_sub_mul_sum_pow hω, one_sub_mul_sum_pow hω]
  have hpos : 0 < ‖1 - ω‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos, ← norm_pow, ← norm_mul, mul_comm, h2]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [norm_mul, norm_pow, hωn, one_pow, mul_one]

/-! ### The second difference of `cosh(v·d)` -/

/-- `|sinh x − sinh y| ≤ cosh M · |x − y|` for `|x|, |y| ≤ M`. -/
theorem abs_sinh_sub_sinh_le {x y M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |Real.sinh x - Real.sinh y| ≤ Real.cosh M * |x - y| := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
      Real.continuous_sinh.continuousOn fun z _ => Real.hasDerivAt_sinh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [abs_sub_comm, ← hcd, abs_mul, abs_sub_comm y x, abs_of_pos (Real.cosh_pos c)]
    gcongr
    rw [Real.cosh_le_cosh]
    exact (abs_le.mpr ⟨by linarith [(abs_le.mp hx).1, hc.1], by linarith [(abs_le.mp hy).2, hc.2]⟩).trans
      (le_abs_self M)
  · subst h; simp
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
      Real.continuous_sinh.continuousOn fun z _ => Real.hasDerivAt_sinh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [← hcd, abs_mul, abs_of_pos (Real.cosh_pos c)]
    gcongr
    rw [Real.cosh_le_cosh]
    exact (abs_le.mpr ⟨by linarith [(abs_le.mp hy).1, hc.1], by linarith [(abs_le.mp hx).2, hc.2]⟩).trans
      (le_abs_self M)


/-- **Second difference of `cosh(v·)`.** For `A, B, C ∈ [0, δ]`, `v ≥ 0`, `|A − B|, |C − B| ≤ κ₁`
and `|A − 2B + C| ≤ κ₂`: `|cosh(vA) − 2cosh(vB) + cosh(vC)| ≤ vκ₂ sinh(vδ) + 2v²κ₁² cosh(vδ)`.
Mean value theorem for `t ↦ cosh(v(B + t(A−B))) + cosh(v(B + t(C−B)))` on `[0, 1]`. -/
theorem abs_second_diff_cosh_le {v δ κ₁ κ₂ A B C : ℝ} (hv : 0 ≤ v) (hA : A ∈ Icc 0 δ)
    (hB : B ∈ Icc 0 δ) (hC : C ∈ Icc 0 δ) (h1 : |A - B| ≤ κ₁) (h2 : |C - B| ≤ κ₁)
    (h3 : |A - 2 * B + C| ≤ κ₂) :
    |Real.cosh (v * A) - 2 * Real.cosh (v * B) + Real.cosh (v * C)| ≤
      v * κ₂ * Real.sinh (v * δ) + 2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ) := by
  have hd : ∀ h t : ℝ, HasDerivAt (fun t => Real.cosh (v * (B + t * h)))
      (Real.sinh (v * (B + t * h)) * (v * h)) t := by
    intro h t
    have : HasDerivAt (fun t => v * (B + t * h)) (v * h) t := by
      simpa using (((hasDerivAt_id t).mul_const h).const_add B).const_mul v
    exact this.cosh
  set h₁ := A - B
  set h₂ := C - B
  obtain ⟨τ, hτ, hτd⟩ := exists_hasDerivAt_eq_slope
    (fun t => Real.cosh (v * (B + t * h₁)) + Real.cosh (v * (B + t * h₂)))
    (fun t => Real.sinh (v * (B + t * h₁)) * (v * h₁) + Real.sinh (v * (B + t * h₂)) * (v * h₂))
    zero_lt_one (by fun_prop) fun t _ => (hd h₁ t).add (hd h₂ t)
  simp only [zero_mul, add_zero, one_mul, sub_zero, div_one] at hτd
  have hA' : B + h₁ = A := by ring
  have hC' : B + h₂ = C := by ring
  rw [hA', hC'] at hτd
  have heq : Real.cosh (v * A) - 2 * Real.cosh (v * B) + Real.cosh (v * C) =
      v * Real.sinh (v * (B + τ * h₁)) * (h₁ + h₂) +
        v * (Real.sinh (v * (B + τ * h₂)) - Real.sinh (v * (B + τ * h₁))) * h₂ := by
    rw [show Real.cosh (v * A) - 2 * Real.cosh (v * B) + Real.cosh (v * C) =
      Real.cosh (v * A) + Real.cosh (v * C) - (Real.cosh (v * B) + Real.cosh (v * B)) by ring,
      ← hτd]
    ring
  -- the intermediate points stay in `[0, δ]`
  have hy : ∀ X ∈ Icc (0 : ℝ) δ, B + τ * (X - B) ∈ Icc 0 δ := by
    intro X hX
    have := hτ.1; have := hτ.2
    constructor <;> nlinarith [hX.1, hX.2, hB.1, hB.2]
  have hy₁ := hy A hA
  have hy₂ := hy C hC
  have hs₁ : |Real.sinh (v * (B + τ * h₁))| ≤ Real.sinh (v * δ) := by
    rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hv hy₁.1))]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hy₁.2 hv)
  have hlip : |Real.sinh (v * (B + τ * h₂)) - Real.sinh (v * (B + τ * h₁))| ≤
      Real.cosh (v * δ) * (v * (2 * κ₁)) := by
    refine (abs_sinh_sub_sinh_le (M := v * δ) ?_ ?_).trans ?_
    · rw [abs_of_nonneg (mul_nonneg hv hy₂.1)]; exact mul_le_mul_of_nonneg_left hy₂.2 hv
    · rw [abs_of_nonneg (mul_nonneg hv hy₁.1)]; exact mul_le_mul_of_nonneg_left hy₁.2 hv
    · gcongr
      rw [show v * (B + τ * h₂) - v * (B + τ * h₁) = v * (τ * (h₂ - h₁)) by ring, abs_mul,
        abs_of_nonneg hv, abs_mul, abs_of_pos hτ.1]
      refine mul_le_mul_of_nonneg_left ?_ hv
      calc τ * |h₂ - h₁| ≤ 1 * |h₂ - h₁| :=
            mul_le_mul_of_nonneg_right hτ.2.le (abs_nonneg _)
        _ ≤ 2 * κ₁ := by
          rw [one_mul]
          calc |h₂ - h₁| ≤ |h₂| + |h₁| := abs_sub _ _
            _ ≤ κ₁ + κ₁ := add_le_add h2 h1
            _ = 2 * κ₁ := by ring
  rw [heq]
  have hκ₁ : 0 ≤ κ₁ := (abs_nonneg _).trans h1
  calc |v * Real.sinh (v * (B + τ * h₁)) * (h₁ + h₂) +
        v * (Real.sinh (v * (B + τ * h₂)) - Real.sinh (v * (B + τ * h₁))) * h₂|
      ≤ |v * Real.sinh (v * (B + τ * h₁)) * (h₁ + h₂)| +
        |v * (Real.sinh (v * (B + τ * h₂)) - Real.sinh (v * (B + τ * h₁))) * h₂| :=
        abs_add_le _ _
    _ ≤ v * Real.sinh (v * δ) * κ₂ + v * (Real.cosh (v * δ) * (v * (2 * κ₁))) * κ₁ := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hv,
          show h₁ + h₂ = A - 2 * B + C by ring]
        have hδ0 : 0 ≤ δ := hB.1.trans hB.2
        have hsh : 0 ≤ Real.sinh (v * δ) := Real.sinh_nonneg_iff.mpr (mul_nonneg hv hδ0)
        exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hs₁ hv) h3 (abs_nonneg _)
          (mul_nonneg hv hsh)) (mul_le_mul (mul_le_mul_of_nonneg_left hlip hv) h2 (abs_nonneg _)
          (mul_nonneg hv (by positivity)))
    _ = v * κ₂ * Real.sinh (v * δ) + 2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ) := by ring

/-! ### The modes of a smooth profile -/

/-- **Mode bound for smooth profiles.** For `1 ≤ m`, `2m ≤ P = k + 1` and `v = mL/P`,
`|D(m)| ≤ P³ (2vκ₂ sinh(vδ) + 4v²κ₁² cosh(vδ)) / (16m²)`. -/
theorem norm_depthSymbol_le_of_smooth (L : ℝ) {k : ℕ} (d : Fin (k + 1) → ℝ) {δ κ₁ κ₂ : ℝ}
    (hd : ∀ r, d r ∈ Icc 0 δ) (h1 : ∀ s, |d (finRotate (k + 1) s) - d s| ≤ κ₁)
    (h2 : ∀ s, |d (finRotate (k + 1) s) - 2 * d s + d ((finRotate (k + 1)).symm s)| ≤ κ₂)
    (hL : 0 ≤ L) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : 2 * m ≤ k + 1) :
    ‖depthSymbol L d m‖ ≤ ((k + 1 : ℕ) : ℝ) ^ 3 *
      (2 * (m * L / (k + 1 : ℕ)) * κ₂ * Real.sinh (m * L / (k + 1 : ℕ) * δ) +
        4 * (m * L / (k + 1 : ℕ)) ^ 2 * κ₁ ^ 2 * Real.cosh (m * L / (k + 1 : ℕ) * δ)) /
          (16 * m ^ 2) := by
  have hP : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = m * L / ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hv]
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 2 * π * m / ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = cexp (I * θ) := ⟨_, rfl⟩
  have hωP : ω ^ (k + 1) = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    have hPc : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    rw [show ((k + 1 : ℕ) : ℂ) * (I * (θ : ℂ)) = (m : ℕ) * (2 * π * I) by
      rw [hθ]; push_cast; field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  have hωn : ‖ω‖ = 1 := by rw [hω, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hθπ : |θ| ≤ π := by
    rw [abs_of_nonneg (by rw [hθ]; positivity), hθ, div_le_iff₀ hP]
    have : (2 * m : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hm2
    nlinarith [Real.pi_pos]
  have hlow : 4 * m / ((k + 1 : ℕ) : ℝ) ≤ ‖1 - ω‖ := by
    have h := two_div_pi_mul_abs_le_norm_cexp_sub_one hθπ
    rw [norm_sub_rev, hω]
    rw [abs_of_nonneg (by rw [hθ]; positivity)] at h
    refine le_trans (le_of_eq ?_) h
    rw [hθ]
    field_simp
    norm_num
  have hlowpos : 0 < 4 * m / ((k + 1 : ℕ) : ℝ) := by positivity
  have hω1 : ω ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hlow; linarith
  -- the symbol as a sum of powers of `ω`
  obtain ⟨g, hg⟩ : ∃ g : Fin (k + 1) → ℂ, g = fun r => ((2 * Real.cosh (v * d r) : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hD : depthSymbol L d m = ∑ r, g r * ω ^ (r : ℕ) := by
    rw [depthSymbol]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hg, hω, ← Complex.exp_nat_mul]
    congr 1
    · congr 3
      rw [hv]; push_cast; ring
    · congr 1
      rw [hθ]
      push_cast
      ring
  rw [hD]
  refine (norm_sum_pow_le hωP hω1 hωn g).trans ?_
  -- the second differences
  set σ := finRotate (k + 1) with hσ
  have hdd : ∀ r, ‖backDiff (backDiff g) r‖ ≤
      2 * (v * κ₂ * Real.sinh (v * δ) + 2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ)) := by
    intro r
    obtain ⟨s, rfl⟩ : ∃ s, r = σ s := ⟨σ.symm r, (Equiv.apply_symm_apply σ r).symm⟩
    have hform : backDiff (backDiff g) (σ s) = ((2 * (Real.cosh (v * d (σ s)) -
        2 * Real.cosh (v * d s) + Real.cosh (v * d (σ.symm s))) : ℝ) : ℂ) := by
      simp only [backDiff, hg, ← hσ, Equiv.symm_apply_apply]
      push_cast
      ring
    rw [hform, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    gcongr
    refine abs_second_diff_cosh_le hv0 (hd _) (hd _) (hd _) (h1 s) ?_ (h2 s)
    have := h1 (σ.symm s)
    rw [Equiv.apply_symm_apply, abs_sub_comm] at this
    exact this
  have hsum : ∑ r, ‖backDiff (backDiff g) r‖ ≤ ((k + 1 : ℕ) : ℝ) *
      (2 * (v * κ₂ * Real.sinh (v * δ) + 2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ))) := by
    refine (Finset.sum_le_sum fun r _ => hdd r).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (4 * m / ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ ‖1 - ω‖ ^ 2 :=
    pow_le_pow_left₀ hlowpos.le hlow 2
  have hδ0 : 0 ≤ δ := (hd 0).1.trans (hd 0).2
  have hnum : 0 ≤ ((k + 1 : ℕ) : ℝ) *
      (2 * (v * κ₂ * Real.sinh (v * δ) + 2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ))) := by
    have hκ₂ : 0 ≤ κ₂ := (abs_nonneg _).trans (h2 0)
    have hsh : 0 ≤ Real.sinh (v * δ) := Real.sinh_nonneg_iff.mpr (mul_nonneg hv0 hδ0)
    positivity
  calc (∑ r, ‖backDiff (backDiff g) r‖) / ‖1 - ω‖ ^ 2
      ≤ (((k + 1 : ℕ) : ℝ) * (2 * (v * κ₂ * Real.sinh (v * δ) +
          2 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ)))) / (4 * m / ((k + 1 : ℕ) : ℝ)) ^ 2 :=
        div_le_div₀ hnum hsum (by positivity) hpow
    _ = ((k + 1 : ℕ) : ℝ) ^ 3 * (2 * v * κ₂ * Real.sinh (v * δ) +
          4 * v ^ 2 * κ₁ ^ 2 * Real.cosh (v * δ)) / (16 * m ^ 2) := by field_simp; ring

/-! ### Summing the modes -/

/-- `Σ_{1 ≤ j < n} 1/j ≤ 1 + log n`. -/
theorem sum_Ico_one_inv_le (n : ℕ) : ∑ j ∈ Finset.Ico 1 n, (1 / (j : ℝ)) ≤ 1 + Real.log n := by
  have h := _root_.harmonic_le_one_add_log n
  rw [_root_.harmonic_eq_sum_Icc] at h
  push_cast at h
  refine le_trans ?_ h
  have hsub : ∑ j ∈ Finset.Ico 1 n, (1 / (j : ℝ)) ≤ ∑ j ∈ Finset.Icc 1 n, (1 / (j : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => by positivity
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    omega
  refine hsub.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [one_div]

/-- A sum over the nonzero lags `0 < |m| < n` is at most twice the sum of a bound in `|m|`. -/
theorem sum_Ioo_erase_zero_le {n : ℕ} {F : ℤ → ℝ} {G : ℕ → ℝ}
    (hF : ∀ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, F m ≤ G m.natAbs) :
    ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, F m ≤ 2 * ∑ j ∈ Finset.Ico 1 n, G j := by
  refine (Finset.sum_le_sum hF).trans (le_of_eq ?_)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun m : ℤ => 0 < m), two_mul]
  congr 1
  · refine Finset.sum_nbij' (fun m => m.natAbs) (fun j => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo] at hm
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo]
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo] at hm
      omega
    · intro j _
      simp
    · intro m _
      rfl
  · refine Finset.sum_nbij' (fun m => m.natAbs) (fun j => -(j : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo] at hm
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo]
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioo] at hm
      omega
    · intro j _
      simp
    · intro m _
      rfl

/-- **Smooth profiles hide.** A depth profile of period `P = k + 1` with values in `[0, δ]`,
cyclic first differences `≤ κ₁` and second differences `≤ κ₂` is Weil-nonnegative at every
aperture `a ≤ L/4` satisfying
`P L κ₂ sinh(2δa)(1 + log n)/8 + n L² κ₁² cosh(2δa)/4 ≤ 1`, `n = ⌈2aP/L⌉`. -/
theorem profileConfig_weil_nonneg_of_smooth {L : ℝ} (hL : 0 < L) {k : ℕ}
    (d : Fin (k + 1) → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {δ κ₁ κ₂ a : ℝ}
    (hdδ : ∀ r, d r ≤ δ) (h1 : ∀ s, |d (finRotate (k + 1) s) - d s| ≤ κ₁)
    (h2 : ∀ s, |d (finRotate (k + 1) s) - 2 * d s + d ((finRotate (k + 1)).symm s)| ≤ κ₂)
    (ha : 0 < a) (haL : 4 * a ≤ L)
    (hcond : ((k + 1 : ℕ) : ℝ) * L * κ₂ * Real.sinh (2 * δ * a) *
        (1 + Real.log ⌈2 * a * ((k + 1 : ℕ) : ℝ) / L⌉₊) / 8 +
      ⌈2 * a * ((k + 1 : ℕ) : ℝ) / L⌉₊ * L ^ 2 * κ₁ ^ 2 * Real.cosh (2 * δ * a) / 4 ≤ 1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((profileConfig hL (Nat.succ_pos k) d hd0 hd1).W f f).re := by
  set P : ℝ := ((k + 1 : ℕ) : ℝ) with hPdef
  have hP : 0 < P := by positivity
  set n : ℕ := ⌈2 * a * P / L⌉₊ with hn
  have hδ0 : 0 ≤ δ := (hd0 0).trans (hdδ 0)
  have hκ₁ : 0 ≤ κ₁ := (abs_nonneg _).trans (h1 0)
  have hκ₂ : 0 ≤ κ₂ := (abs_nonneg _).trans (h2 0)
  set sh := Real.sinh (2 * δ * a) with hsh
  set ch := Real.cosh (2 * δ * a) with hch
  have hsh0 : 0 ≤ sh := Real.sinh_nonneg_iff.mpr (by positivity)
  -- the bound on one mode
  set G : ℕ → ℝ := fun j => P ^ 2 * L * κ₂ * sh / (8 * j) + P * L ^ 2 * κ₁ ^ 2 * ch / 4 with hG
  have hmode : ∀ j : ℕ, 1 ≤ j → j < n → ‖depthSymbol L d j‖ ≤ G j := by
    intro j hj1 hjn
    have hj : (j : ℝ) < 2 * a * P / L := Nat.lt_ceil.mp hjn
    have hv : (j : ℝ) * L / P < 2 * a := by
      rw [div_lt_iff₀ hP]; rw [lt_div_iff₀ hL] at hj; linarith
    have h2j : 2 * j ≤ k + 1 := by
      have : (2 * j : ℝ) < P := by
        have : 2 * a * P / L ≤ P / 2 := by
          rw [div_le_iff₀ hL]; nlinarith
        linarith
      have : 2 * j < k + 1 := by rw [hPdef] at this; exact_mod_cast this
      omega
    refine (norm_depthSymbol_le_of_smooth L d (fun r => ⟨hd0 r, hdδ r⟩) h1 h2 hL.le hj1 h2j).trans ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hv0 : 0 ≤ (j : ℝ) * L / P := by positivity
    have hs : Real.sinh ((j : ℝ) * L / P * δ) ≤ sh :=
      Real.sinh_le_sinh.mpr (by nlinarith)
    have hc : Real.cosh ((j : ℝ) * L / P * δ) ≤ ch := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      nlinarith
    calc P ^ 3 * (2 * ((j : ℝ) * L / P) * κ₂ * Real.sinh ((j : ℝ) * L / P * δ) +
          4 * ((j : ℝ) * L / P) ^ 2 * κ₁ ^ 2 * Real.cosh ((j : ℝ) * L / P * δ)) / (16 * j ^ 2)
        ≤ P ^ 3 * (2 * ((j : ℝ) * L / P) * κ₂ * sh + 4 * ((j : ℝ) * L / P) ^ 2 * κ₁ ^ 2 * ch) /
            (16 * j ^ 2) := by gcongr
      _ = G j := by rw [hG]; field_simp; ring
  -- sum over the nonzero lags
  have hmodes : ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖depthSymbol L d m‖ ≤
      2 * ∑ j ∈ Finset.Ico 1 n, G j := by
    refine sum_Ioo_erase_zero_le fun m hm => ?_
    simp only [Finset.mem_erase, Finset.mem_Ioo] at hm
    have hj1 : 1 ≤ m.natAbs := by omega
    have hjn : m.natAbs < n := by omega
    obtain ⟨j, hj⟩ : ∃ j : ℕ, j = m.natAbs := ⟨_, rfl⟩
    rw [← hj] at hj1 hjn ⊢
    rcases le_or_gt 0 m with hpos | hneg
    · rw [show m = (j : ℤ) by omega]
      exact hmode _ hj1 hjn
    · rw [show m = -(j : ℤ) by omega, depthSymbol_neg, Complex.norm_conj]
      exact hmode _ hj1 hjn
  have hsumG : ∑ j ∈ Finset.Ico 1 n, G j ≤
      P ^ 2 * L * κ₂ * sh / 8 * (1 + Real.log n) + n * (P * L ^ 2 * κ₁ ^ 2 * ch / 4) := by
    rw [hG, Finset.sum_add_distrib]
    gcongr
    · rw [show (fun j : ℕ => P ^ 2 * L * κ₂ * sh / (8 * j)) =
          fun j : ℕ => P ^ 2 * L * κ₂ * sh / 8 * (1 / (j : ℝ)) by funext j; field_simp,
        ← Finset.mul_sum]
      gcongr
      exact sum_Ico_one_inv_le n
    · rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hch0 : 0 ≤ ch := (Real.cosh_pos _).le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) (by positivity)
  refine profileConfig_weil_nonneg_of_modes hL (Nat.succ_pos k) d hd0 hd1 ha
    (hmodes.trans ?_) hf hfs
  have : 2 * (P ^ 2 * L * κ₂ * sh / 8 * (1 + Real.log n) + n * (P * L ^ 2 * κ₁ ^ 2 * ch / 4)) =
      2 * P * (P * L * κ₂ * sh * (1 + Real.log n) / 8 + n * L ^ 2 * κ₁ ^ 2 * ch / 4) := by ring
  calc 2 * ∑ j ∈ Finset.Ico 1 n, G j ≤ 2 * (P ^ 2 * L * κ₂ * sh / 8 * (1 + Real.log n) +
        n * (P * L ^ 2 * κ₁ ^ 2 * ch / 4)) := by gcongr
    _ = 2 * P * (P * L * κ₂ * sh * (1 + Real.log n) / 8 + n * L ^ 2 * κ₁ ^ 2 * ch / 4) := this
    _ ≤ 2 * P * 1 := by gcongr
    _ = 2 * P := by ring

end GaloisForLFunctions.SquareRootThreshold
