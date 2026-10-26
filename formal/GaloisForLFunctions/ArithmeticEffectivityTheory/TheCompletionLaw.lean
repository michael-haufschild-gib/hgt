import GaloisForLFunctions.ArithmeticEffectivityTheory.TheTorsionCharacteristics
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The completion law: incomplete sums from a count, with a logarithmic loss

At each finite level square-root cancellation of a complete character sum is a count
(`normSq_gaussSum_eq_card`). Completion transports it to incomplete sums: a character of a prime
modulus is its own finite Fourier transform up to the Gauss sum,
`χ(a) τ(χ̄) = Σ_x χ̄(x) e(ax/p)` (`mul_gaussSum_inv_eq_sum`), so an initial segment
`Σ_{n<N} χ(n)` becomes a combination of geometric sums of additive characters.

* **Pólya–Vinogradov** (`norm_sum_range_le_polyaVinogradov`). For a nontrivial character `χ`
  modulo a prime `p` and every `N`, `|Σ_{n<N} χ(n)| ≤ √p (1 + log p)`. The loss over the complete
  sum is the harmonic sum `Σ_{k<p} 1/sin(πk/p) ≤ p (1 + log p)` (`sum_inv_sin_le`), from
  `|e(k/p) − 1| = 2 sin(πk/p)` and Jordan's inequality.

The completion law is the mechanism by which counting reaches incomplete sums: it needs a period.
The arithmetic point — `Σ μ(n)`, `ψ(x) − x` — has none, so no finite group computes its sums, and
the square root it would need is RH (E4).
-/

noncomputable section

open Complex Finset Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Fourier inversion of a character**: `χ(a) τ(χ⁻¹, ψ) = Σ_x χ⁻¹(x) ψ(a x)`. -/
theorem mul_gaussSum_inv_eq_sum {χ : MulChar (ZMod p) ℂ} (hχ : χ ≠ 1) (ψ : AddChar (ZMod p) ℂ)
    (a : ZMod p) : χ a * gaussSum χ⁻¹ ψ = ∑ x, χ⁻¹ x * ψ (a * x) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [MulChar.sum_eq_zero_of_ne_one hinv, MulChar.map_nonunit χ not_isUnit_zero, zero_mul]
  · have hu := gaussSum_mulShift_eq χ⁻¹ ψ (Units.mk0 a ha)
    rw [inv_inv, Units.val_mk0] at hu
    rw [← hu, gaussSum]
    simp only [AddChar.mulShift_apply]

/-- A geometric sum of a unimodular `z ≠ 1` is at most `2 / |z − 1|`. -/
theorem norm_geom_sum_le {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hne : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
  rw [geom_sum_eq h1, norm_div, div_le_div_iff_of_pos_right (norm_pos_iff.mpr (sub_ne_zero.mpr h1))]
  calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

/-- `|e(k/p) − 1| = 2 sin(πk/p)` for `0 < k < p`. -/
theorem norm_stdAddChar_sub_one {x : ZMod p} (hx : x ≠ 0) :
    ‖ZMod.stdAddChar x - 1‖ = 2 * Real.sin (π * x.val / p) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hk0 : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
  have hkp : x.val < p := ZMod.val_lt x
  have harg : ZMod.stdAddChar x = Complex.exp (I * ((2 * π * x.val / p : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1; push_cast; ring
  rw [harg, norm_exp_I_mul_ofReal_sub_one, show 2 * π * x.val / p / 2 = π * x.val / p by ring,
    Real.norm_eq_abs, abs_of_nonneg]
  refine mul_nonneg two_pos.le (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
  rw [div_le_iff₀ hpos]
  have : (x.val : ℝ) ≤ p := by exact_mod_cast hkp.le
  nlinarith [Real.pi_pos]

/-- **Jordan's inequality on the circle**: `1/sin(πk/p) ≤ p/(2k) + p/(2(p − k))` for `0 < k < p`. -/
theorem inv_sin_le {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    1 / Real.sin (π * k / p) ≤ p / (2 * k) + p / (2 * (p - k)) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkp' : (k : ℝ) < p := by exact_mod_cast hkp
  have hpk : (0 : ℝ) < p - k := by linarith
  rcases le_total (2 * (k : ℝ)) p with h | h
  · have hs : 2 / π * (π * k / p) ≤ Real.sin (π * k / p) :=
      Real.mul_le_sin (by positivity) (by rw [div_le_iff₀ hpos]; nlinarith [Real.pi_pos])
    have hs' : 2 * k / p ≤ Real.sin (π * k / p) := by
      rwa [show 2 / π * (π * k / p) = 2 * k / p by field_simp] at hs
    have h1 : 1 / Real.sin (π * k / p) ≤ p / (2 * k) := by
      rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hs') (by positivity)]
      rw [div_le_iff₀ hpos] at hs'; linarith
    linarith [div_pos hpos (by positivity : (0 : ℝ) < 2 * (p - k))]
  · have hrefl : Real.sin (π * k / p) = Real.sin (π * (p - k) / p) := by
      rw [show π * (p - k) / p = π - π * k / p by field_simp, Real.sin_pi_sub]
    have hs : 2 / π * (π * (p - k) / p) ≤ Real.sin (π * (p - k) / p) :=
      Real.mul_le_sin (by positivity) (by rw [div_le_iff₀ hpos]; nlinarith [Real.pi_pos])
    have hs' : 2 * (p - k) / p ≤ Real.sin (π * k / p) := by
      rw [hrefl]; rwa [show 2 / π * (π * (p - k) / p) = 2 * (p - k) / p by field_simp] at hs
    have h1 : 1 / Real.sin (π * k / p) ≤ p / (2 * (p - k)) := by
      rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hs') (by positivity)]
      rw [div_le_iff₀ hpos] at hs'; linarith
    linarith [div_pos hpos (by positivity : (0 : ℝ) < 2 * k)]

/-- **The harmonic loss**: `Σ_{0<k<p} 1/sin(πk/p) ≤ p (1 + log p)`. -/
theorem sum_inv_sin_le :
    ∑ k ∈ Icc 1 (p - 1), 1 / Real.sin (π * k / p) ≤ p * (1 + Real.log p) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hrefl : ∑ k ∈ Icc 1 (p - 1), 1 / ((p : ℝ) - k) = ∑ k ∈ Icc 1 (p - 1), 1 / (k : ℝ) := by
    refine sum_nbij' (fun k : ℕ => p - k) (fun k : ℕ => p - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [mem_Icc] at hk; omega
    · intro k hk; simp only [mem_Icc] at hk; omega
    · intro k hk
      simp only [mem_Icc] at hk
      rw [Nat.cast_sub (by omega)]
  have hH := RHTower.Sieve.sum_Icc_one_div_le_one_add_log (p - 1)
  have hlog : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log p := by
    rcases Nat.eq_zero_or_pos (p - 1) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by exact_mod_cast hp1)
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.sub_le p 1)
  calc ∑ k ∈ Icc 1 (p - 1), 1 / Real.sin (π * k / p)
      ≤ ∑ k ∈ Icc 1 (p - 1), ((p : ℝ) / (2 * k) + p / (2 * (p - k))) :=
        sum_le_sum fun k hk => by
          simp only [mem_Icc] at hk
          exact inv_sin_le (by omega) (by omega)
    _ = (p / 2) * (∑ k ∈ Icc 1 (p - 1), 1 / (k : ℝ) + ∑ k ∈ Icc 1 (p - 1), 1 / ((p : ℝ) - k)) := by
        rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        field_simp
    _ = p * ∑ k ∈ Icc 1 (p - 1), 1 / (k : ℝ) := by rw [hrefl]; ring
    _ ≤ p * (1 + Real.log p) := mul_le_mul_of_nonneg_left (hH.trans (by linarith)) hpos.le

/-- Sums over `ℤ/pℤ` are sums over `0 ≤ k < p`. -/
theorem sum_zmod_eq_sum_range (f : ZMod p → ℝ) : ∑ x, f x = ∑ k ∈ range p, f (k : ZMod p) := by
  refine sum_nbij' (fun x : ZMod p => x.val) (fun k : ℕ => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x _; simpa using ZMod.val_lt x
  · intro k _; exact mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro k hk; exact ZMod.val_natCast_of_lt (mem_range.mp hk)
  · intro x _; rw [ZMod.natCast_zmod_val]

/-- **Pólya–Vinogradov.** For a nontrivial character `χ` modulo a prime `p`,
`|Σ_{n<N} χ(n)| ≤ √p (1 + log p)` for every `N`. -/
theorem norm_sum_range_le_polyaVinogradov {χ : MulChar (ZMod p) ℂ} (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ (n : ZMod p)‖ ≤ Real.sqrt p * (1 + Real.log p) := by
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hτ : ‖τ‖ = Real.sqrt p := by
    rw [norm_gaussSum_eq_sqrt_card hinv (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  -- `τ · S = Σ_x χ⁻¹(x) Σ_n ψ(x)^n`
  have hexp : τ * ∑ n ∈ range N, χ (n : ZMod p) =
      ∑ x, χ⁻¹ x * ∑ n ∈ range N, ψ x ^ n := by
    rw [mul_sum]
    have h : ∀ n ∈ range N, τ * χ (n : ZMod p) = ∑ x, χ⁻¹ x * ψ ((n : ZMod p) * x) :=
      fun n _ => by rw [mul_comm]; exact mul_gaussSum_inv_eq_sum hχ ψ _
    rw [sum_congr rfl h, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  -- each term is at most `1 / sin(π x.val / p)`, and `0` at `x = 0`
  have hterm : ∀ x : ZMod p, ‖χ⁻¹ x * ∑ n ∈ range N, ψ x ^ n‖ ≤
      if x = 0 then 0 else 1 / Real.sin (π * x.val / p) := by
    intro x
    split_ifs with hx
    · rw [hx, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, norm_zero]
    · have hψ1 : ψ x ≠ 1 := fun h => hx (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one ψ).symm))
      have hψn : ‖ψ x‖ = 1 := by simp [ψ, ZMod.stdAddChar_apply]
      rw [norm_mul]
      calc ‖χ⁻¹ x‖ * ‖∑ n ∈ range N, ψ x ^ n‖ ≤ 1 * (2 / ‖ψ x - 1‖) :=
            mul_le_mul (DirichletCharacter.norm_le_one (χ⁻¹ : DirichletCharacter ℂ p) x)
              (norm_geom_sum_le hψn hψ1 N) (norm_nonneg _)
              zero_le_one
        _ = 1 / Real.sin (π * x.val / p) := by
            rw [one_mul, norm_stdAddChar_sub_one hx]; field_simp
  have hsum : ∑ x : ZMod p, (if x = 0 then 0 else 1 / Real.sin (π * x.val / p)) ≤
      p * (1 + Real.log p) := by
    rw [sum_zmod_eq_sum_range]
    refine le_trans (le_of_eq ?_) sum_inv_sin_le
    have hcongr : ∀ k ∈ range p, (if (k : ZMod p) = 0 then (0 : ℝ) else
        1 / Real.sin (π * ((k : ZMod p).val : ℝ) / p)) =
          if k ≠ 0 then 1 / Real.sin (π * k / p) else 0 := by
      intro k hk
      have hkp := mem_range.mp hk
      have hz : (k : ZMod p) = 0 ↔ k = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hkp, fun h => h ▸ dvd_zero p⟩
      by_cases h0 : k = 0
      · simp [h0]
      · rw [if_neg (by rwa [hz]), if_pos h0, ZMod.val_natCast_of_lt hkp]
    rw [sum_congr rfl hcongr, ← sum_filter]
    congr 1
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    have := hp.out.one_lt
    omega
  have h1 : ‖τ‖ * ‖∑ n ∈ range N, χ (n : ZMod p)‖ ≤ p * (1 + Real.log p) := by
    rw [← norm_mul, hexp]
    exact (norm_sum_le _ _).trans ((sum_le_sum fun x _ => hterm x).trans hsum)
  rw [hτ] at h1
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpos
  have h2 : ‖∑ n ∈ range N, χ (n : ZMod p)‖ ≤ p * (1 + Real.log p) / Real.sqrt p := by
    rw [le_div_iff₀ hs]; linarith
  calc ‖∑ n ∈ range N, χ (n : ZMod p)‖ ≤ p * (1 + Real.log p) / Real.sqrt p := h2
    _ = (p / Real.sqrt p) * (1 + Real.log p) := by ring
    _ = Real.sqrt p * (1 + Real.log p) := by rw [Real.div_sqrt]

end GaloisForLFunctions.ArithmeticEffectivityTheory
