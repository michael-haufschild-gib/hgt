import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Complex.Basic

/-!
# Triangular solving and the exponential shift

Two elementary tools for jet interpolation by exponential polynomials: a lower triangular system
with invertible diagonal is solvable, and for every finite set of complex numbers there is a
positive real shift making the exponential `s ↦ e^{-δ s}` injective on that set — the only
obstruction is the imaginary period, which a small enough shift avoids.

* `deningerTriangular_solvable` : triangular solvability.
* `deningerExpShift_injOn` : the exponential shift is injective for small shifts.
-/

namespace RHTower

open Complex

section Triangular

/-- **Triangular systems are solvable.**  The unknowns are determined one at a time by the
invertible diagonal. -/
theorem deningerTriangular_solvable (M : ℕ → ℕ → ℂ) (hzero : ∀ k j, k < j → M k j = 0)
    (hdiag : ∀ k, M k k ≠ 0) (v : ℕ → ℂ) (m : ℕ) :
    ∃ a : ℕ → ℂ, ∀ k < m, ∑ j ∈ Finset.range m, a j * M k j = v k := by
  induction m with
  | zero => exact ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨Function.update a m
      ((v m - ∑ j ∈ Finset.range m, a j * M m j) / M m m), fun k hk => ?_⟩
    have hsum : ∀ r : ℕ, ∑ j ∈ Finset.range m,
        Function.update a m ((v m - ∑ j ∈ Finset.range m, a j * M m j) / M m m) j * M r j
        = ∑ j ∈ Finset.range m, a j * M r j := by
      intro r
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≠ m := by
        have := Finset.mem_range.mp hj
        omega
      rw [Function.update_of_ne hjm]
    rw [Finset.sum_range_succ, hsum, Function.update_self]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
    · rw [ha k hlt, hzero k m hlt, mul_zero, add_zero]
    · subst heq
      have hd := hdiag k
      field_simp
      ring

end Triangular

section ExpShift

/-- **The exponential shift is injective for small shifts.**  Two points of a finite set have the
same exponential only if their difference is an imaginary period, which a shift smaller than the
reciprocal of the imaginary spread cannot reach. -/
theorem deningerExpShift_injOn (T : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun s : ℂ => Complex.exp (-(δ : ℂ) * s)) T := by
  obtain ⟨B, hB⟩ := Finset.exists_le
    (((T ×ˢ T).image fun p : ℂ × ℂ => |(p.1 - p.2).im|))
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨min 1 (Real.pi / (B' + 1)), ?_, ?_⟩
  · refine lt_min one_pos ?_
    have : (0 : ℝ) < B' + 1 := by linarith
    positivity
  · set δ : ℝ := min 1 (Real.pi / (B' + 1)) with hδ
    have hδpos : 0 < δ := by
      refine lt_min one_pos ?_
      have : (0 : ℝ) < B' + 1 := by linarith
      positivity
    have hδB : δ * B' < Real.pi := by
      have h1 : δ ≤ Real.pi / (B' + 1) := min_le_right _ _
      have h2 : (0 : ℝ) < B' + 1 := by linarith
      have h3 : δ * B' ≤ (Real.pi / (B' + 1)) * B' :=
        mul_le_mul_of_nonneg_right h1 hB'0
      have h4 : (Real.pi / (B' + 1)) * B' < Real.pi := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
        nlinarith [Real.pi_pos]
      linarith
    intro a ha b hb hab
    have habound : |(b - a).im| ≤ B' := by
      refine le_trans (le_trans ?_ (le_max_left B 0)) (le_of_eq rfl)
      refine hB _ ?_
      exact Finset.mem_image.mpr ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, rfl⟩
    have hexp : Complex.exp (-(δ : ℂ) * a) = Complex.exp (-(δ : ℂ) * b) := hab
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hkey : (δ : ℂ) * (b - a) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      have : -(δ : ℂ) * a = -(δ : ℂ) * b + (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      linear_combination this
    have hre : δ * (b - a).re = 0 := by
      have := congrArg Complex.re hkey
      simpa [Complex.mul_re, Complex.mul_im] using this
    have him : δ * (b.im - a.im) = 2 * Real.pi * (n : ℝ) := by
      have h := congrArg Complex.im hkey
      simp [Complex.mul_re, Complex.mul_im, Complex.sub_im] at h
      linarith [h]
    have hnzero : n = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
          have hneg : (n : ℝ) < 0 := by linarith
          rw [abs_of_neg hneg]
          linarith
        · have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          rw [abs_of_pos (by linarith)]
          linarith
      have h2 : |δ * (b.im - a.im)| = 2 * Real.pi * |(n : ℝ)| := by
        rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h3 : |δ * (b.im - a.im)| ≤ δ * B' := by
        rw [abs_mul, abs_of_pos hδpos]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hδpos)
        simpa [Complex.sub_im] using habound
      have h4 : 2 * Real.pi ≤ 2 * Real.pi * |(n : ℝ)| := by
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
    rw [hnzero] at him
    have him0 : δ * (b.im - a.im) = 0 := by simpa using him
    have hre0 : δ * (b.re - a.re) = 0 := by simpa [Complex.sub_re] using hre
    have hbim : b.im = a.im := by
      rcases mul_eq_zero.mp him0 with h | h
      · exact absurd h (ne_of_gt hδpos)
      · linarith
    have hbre : b.re = a.re := by
      rcases mul_eq_zero.mp hre0 with h | h
      · exact absurd h (ne_of_gt hδpos)
      · linarith
    exact Complex.ext hbre.symm hbim.symm

end ExpShift

end RHTower
