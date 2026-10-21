import GaloisForLFunctions.HTGeometry.MontgomeryVaughanHilbertInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The Montgomery–Vaughan cosecant inequality

If `α_1, …, α_R` are `δ`-separated modulo one (`|α_r − α_s − m| ≥ δ` for `r ≠ s`, `m ∈ ℤ`), then

`|Σ_{r ≠ s} z_r z̄_s / sin(π(α_r − α_s))| ≤ δ⁻¹ Σ |z_r|²`.

This is the circle form of the Hilbert inequality, the input of the large sieve with constant
`N + δ⁻¹`. Proof: `π/sin(πx) = Σ_m (−1)^m/(x + m)`; the real-line Hilbert inequality applied to
`J` unit-spaced copies `α_r + j` with weights `(−1)^j z_r` has kernel
`G_J(x) = Σ_{j,k<J} (−1)^{j+k}/(x + j − k) = Σ_{K<J} S_K(x)` (Fejér identity, `S_K` the symmetric
alternating partial sums), so `G_J/J → π/sin(πx)` by Cesàro, and the copies are `δ`-separated.
The limit `S_K → π/sin(πx)` comes from the cotangent series at `x` and `x/2` through
`cot(θ/2) − cot θ = 1/sin θ`.
-/

open Finset Filter Topology Real
open scoped ComplexConjugate

namespace GaloisForLFunctions.HilbertInequality

/-! ### The alternating partial fractions of `π/sin(πx)` -/

/-- The symmetric pair `1/(x − (j+1)) + 1/(x + (j+1))` of the cotangent series. -/
noncomputable def cotPairTerm (x : ℝ) (j : ℕ) : ℝ := 1 / (x - (j + 1)) + 1 / (x + (j + 1))

theorem mem_integerComplement_ofReal {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  exact hx n (by exact_mod_cast hn.symm)

theorem tendsto_sum_cotPairTerm {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (fun n => ∑ j ∈ range n, cotPairTerm x j) atTop (𝓝 (π * Real.cot (π * x) - 1 / x)) := by
  have h := tendsto_logDeriv_euler_cot_sub (mem_integerComplement_ofReal hx)
  rw [← Filter.tendsto_ofReal_iff]
  convert h using 2 with n
  · push_cast [cotPairTerm, cotTerm]
    rfl
  · push_cast [Complex.ofReal_cot]
    rfl

theorem summable_cotPairTerm {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : Summable (cotPairTerm x) := by
  have h := summable_cotTerm (mem_integerComplement_ofReal hx)
  rw [← Complex.summable_ofReal]
  convert h using 2 with j
  push_cast [cotPairTerm, cotTerm]
  rfl

/-- The alternating partial sum `Σ_{|m| ≤ K} (−1)^m/(x + m)`. -/
noncomputable def altPartialFraction (x : ℝ) (K : ℕ) : ℝ :=
  1 / x + ∑ j ∈ range K, (-1) ^ (j + 1) * cotPairTerm x j

/-- Even alternating sums: the odd pairs at `x` are half the pairs at `x/2`. -/
theorem sum_range_two_mul_alt (x : ℝ) (n : ℕ) :
    ∑ j ∈ range (2 * n), (-1 : ℝ) ^ (j + 1) * cotPairTerm x j =
      ∑ i ∈ range n, cotPairTerm (x / 2) i - ∑ j ∈ range (2 * n), cotPairTerm x j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ, sum_range_succ]
    have hhalf : cotPairTerm (x / 2) n = 2 * cotPairTerm x (2 * n + 1) := by
      simp only [cotPairTerm]
      rw [show x / 2 - ((n : ℝ) + 1) = (x - (((2 * n + 1 : ℕ) : ℝ) + 1)) / 2 by push_cast; ring,
        show x / 2 + ((n : ℝ) + 1) = (x + (((2 * n + 1 : ℕ) : ℝ) + 1)) / 2 by push_cast; ring,
        one_div_div, one_div_div]
      ring
    rw [hhalf, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, show 2 * n + 1 = 2 * n + 1 by rfl]
    simp only [pow_succ, pow_mul]
    ring

theorem cot_half_sub_cot {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    Real.cot (θ / 2) - Real.cot θ = 1 / Real.sin θ := by
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs : Real.sin (θ / 2) ≠ 0 := fun h => hθ (by rw [h2, h]; ring)
  have hco : Real.cos (θ / 2) ≠ 0 := fun h => hθ (by rw [h2, h]; ring)
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, hc, h2]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

/-- **The alternating partial fractions converge to `π/sin(πx)`** off the integers. -/
theorem tendsto_altPartialFraction {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (altPartialFraction x) atTop (𝓝 (π / Real.sin (π * x))) := by
  have hx2 : ∀ n : ℤ, x / 2 ≠ n := fun n h => hx (2 * n) (by push_cast; linarith)
  have hsin : Real.sin (π * x) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    exact hx n (by nlinarith [Real.pi_pos])
  have hx0 : x ≠ 0 := by exact_mod_cast hx 0
  set a : ℕ → ℝ := fun j => (-1) ^ (j + 1) * cotPairTerm x j with ha
  have hsum : Summable a := by
    refine Summable.of_norm_bounded (summable_cotPairTerm hx).abs fun j => ?_
    simp [ha]
  have h1 := hsum.hasSum.tendsto_sum_nat
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
  have h2 : Tendsto (fun n => ∑ j ∈ range (2 * n), a j) atTop
      (𝓝 ((π * Real.cot (π * (x / 2)) - 1 / (x / 2)) - (π * Real.cot (π * x) - 1 / x))) := by
    simp only [ha, sum_range_two_mul_alt]
    exact (tendsto_sum_cotPairTerm hx2).sub ((tendsto_sum_cotPairTerm hx).comp htwo)
  have hlim := tendsto_nhds_unique (h1.comp htwo) h2
  have heq : (π * Real.cot (π * (x / 2)) - 1 / (x / 2)) - (π * Real.cot (π * x) - 1 / x) =
      π / Real.sin (π * x) - 1 / x := by
    rw [one_div_div, show π * (x / 2) = π * x / 2 by ring]
    linear_combination π * cot_half_sub_cot hsin
  rw [heq] at hlim
  have h3 := h1.const_add (1 / x)
  rw [hlim, add_sub_cancel] at h3
  exact h3


/-! ### Fejér means of the alternating kernel -/

/-- The kernel of `J` unit-spaced copies with alternating signs:
`G_J(x) = Σ_{j,k < J} (−1)^{j+k}/(x + j − k)`. -/
noncomputable def alternatingCopyKernel (J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range J, ∑ k ∈ range J, (-1 : ℝ) ^ (j + k) / (x + j - k)

private theorem neg_one_pow_reflect {J i : ℕ} (hi : i < J) :
    (-1 : ℝ) ^ (J + (J - 1 - i)) = (-1) ^ (i + 1) := by
  rw [show J + (J - 1 - i) = (i + 1) + 2 * (J - 1 - i) by omega, pow_add, pow_mul, neg_one_sq,
    one_pow, mul_one]

/-- **Fejér identity.** `G_J(x) = Σ_{K < J} S_K(x)`: adding a row and a column of copies adds the
alternating partial sum `S_J`. -/
theorem alternatingCopyKernel_eq_sum (J : ℕ) (x : ℝ) :
    alternatingCopyKernel J x = ∑ K ∈ range J, altPartialFraction x K := by
  induction J with
  | zero => simp [alternatingCopyKernel]
  | succ J ih =>
    rw [sum_range_succ, ← ih]
    simp only [alternatingCopyKernel, sum_range_succ, sum_add_distrib]
    have hrow : ∑ k ∈ range J, (-1 : ℝ) ^ (J + k) / (x + J - k) =
        ∑ i ∈ range J, (-1) ^ (i + 1) * (1 / (x + (i + 1))) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [neg_one_pow_reflect hi', Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring_nf
    have hcol : ∑ j ∈ range J, (-1 : ℝ) ^ (j + J) / (x + j - J) =
        ∑ i ∈ range J, (-1) ^ (i + 1) * (1 / (x - (i + 1))) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [add_comm (J - 1 - i), neg_one_pow_reflect hi', Nat.cast_sub (by omega),
        Nat.cast_sub (by omega)]
      push_cast
      ring_nf
    rw [hrow, hcol, altPartialFraction, ← add_assoc, add_assoc (∑ j ∈ range J, _)]
    simp only [cotPairTerm, mul_add, sum_add_distrib]
    rw [show (-1 : ℝ) ^ (J + J) / (x + J - J) = 1 / x by
      rw [← two_mul, pow_mul, neg_one_sq, one_pow, add_sub_cancel_right]]
    ring

/-- The alternating kernel vanishes at `x = 0` (it is odd under `j ↔ k`). -/
theorem alternatingCopyKernel_zero (J : ℕ) : alternatingCopyKernel J 0 = 0 := by
  have h : alternatingCopyKernel J 0 = -alternatingCopyKernel J 0 := by
    conv_rhs => rw [alternatingCopyKernel, sum_comm]
    rw [alternatingCopyKernel, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [add_comm k j, zero_add, zero_add, ← neg_sub, div_neg]
  linarith

/-- **Fejér means of the alternating kernel converge to `π/sin(πx)`** at `x = 0` (both sides
vanish) and off the integers. -/
theorem tendsto_alternatingCopyKernel_div {x : ℝ} (hx : x = 0 ∨ ∀ n : ℤ, x ≠ n) :
    Tendsto (fun J : ℕ => (J : ℝ)⁻¹ * alternatingCopyKernel J x) atTop
      (𝓝 (π / Real.sin (π * x))) := by
  rcases hx with rfl | hx
  · simp [alternatingCopyKernel_zero]
  · simp_rw [alternatingCopyKernel_eq_sum]
    exact (tendsto_altPartialFraction hx).cesaro


/-! ### The cosecant inequality -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The periodized Hilbert sum: `J` alternating copies of each point. -/
theorem sum_hilbertDifferenceKernel_copies (α : ι → ℝ) (z : ι → ℂ) (J : ℕ) :
    ∑ p : ι × Fin J, ∑ q : ι × Fin J,
        (-1 : ℂ) ^ (p.2 : ℕ) * z p.1 * conj ((-1 : ℂ) ^ (q.2 : ℕ) * z q.1) *
          (hilbertDifferenceKernel (fun p : ι × Fin J => α p.1 + p.2) p q : ℂ) =
      ∑ r, ∑ s, z r * conj (z s) * (alternatingCopyKernel J (α r - α s) : ℂ) := by
  simp only [Fintype.sum_prod_type, alternatingCopyKernel, hilbertDifferenceKernel, Finset.sum_range,
    Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one]
  push_cast
  rw [pow_add]
  ring_nf

/-- **The Montgomery–Vaughan cosecant inequality.** If the points `α_r` are `δ`-separated modulo
one, then `|Σ_{r ≠ s} z_r z̄_s / sin(π(α_r − α_s))| ≤ δ⁻¹ Σ |z_r|²` (the diagonal vanishes as
`1/sin 0 = 0`). Apply the Hilbert inequality to `J` alternating unit-spaced copies of each point
and let `J → ∞`: the Fejér means of `Σ_m (−1)^m/(x + m)` tend to `π/sin(πx)`. -/
theorem norm_sum_mul_conj_div_sin_le (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → ∀ m : ℤ, δ ≤ |α r - α s - m|) (z : ι → ℂ) :
    ‖∑ r, ∑ s, z r * conj (z s) * ((1 / Real.sin (π * (α r - α s)) : ℝ) : ℂ)‖ ≤
      δ⁻¹ * ∑ r, ‖z r‖ ^ 2 := by
  by_cases htriv : ∀ r s : ι, r = s
  · have h0 : ∑ r, ∑ s, z r * conj (z s) * ((1 / Real.sin (π * (α r - α s)) : ℝ) : ℂ) = 0 :=
      sum_eq_zero fun r _ => sum_eq_zero fun s _ => by
        rw [htriv r s, sub_self, mul_zero, Real.sin_zero, div_zero, Complex.ofReal_zero, mul_zero]
    rw [h0, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hδ.le) (sum_nonneg fun _ _ => sq_nonneg _)
  -- two distinct points force `δ ≤ 1/2`
  have hδ1 : δ ≤ 1 := by
    simp only [not_forall] at htriv
    obtain ⟨r, s, hrs⟩ := htriv
    have h := hsep r s hrs (round (α r - α s))
    linarith [abs_sub_round (α r - α s)]
  -- the Hilbert inequality for `J` copies
  have hJ : ∀ J : ℕ, 0 < J → ‖∑ r, ∑ s, z r * conj (z s) *
      (((J : ℝ)⁻¹ * alternatingCopyKernel J (α r - α s) : ℝ) : ℂ)‖ ≤ π / δ * ∑ r, ‖z r‖ ^ 2 := by
    intro J hJ0
    set l : ι × Fin J → ℝ := fun p => α p.1 + p.2
    have hsep' : ∀ p q : ι × Fin J, p ≠ q → δ ≤ |l p - l q| := by
      rintro ⟨r, j⟩ ⟨s, k⟩ hpq
      simp only [l]
      by_cases hrs : r = s
      · subst hrs
        have hjk : (j : ℕ) ≠ k := fun h => hpq (by rw [Fin.ext h])
        have : (1 : ℝ) ≤ |((j : ℕ) : ℝ) - (k : ℕ)| := by
          rcases lt_or_gt_of_ne hjk with h | h
          · have : ((j : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
          · have : ((k : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
            rw [abs_of_nonneg (by linarith)]
            linarith
        rw [show α r + ((j : ℕ) : ℝ) - (α r + (k : ℕ)) = ((j : ℕ) : ℝ) - (k : ℕ) by ring]
        linarith
      · have h := hsep r s hrs ((k : ℕ) - (j : ℕ) : ℤ)
        rw [show α r + ((j : ℕ) : ℝ) - (α s + (k : ℕ)) =
          α r - α s - (((k : ℕ) - (j : ℕ) : ℤ) : ℝ) by push_cast; ring]
        exact h
    have hH := norm_sum_mul_conj_hilbertDifferenceKernel_le l hδ hsep'
      (fun p => (-1 : ℂ) ^ (p.2 : ℕ) * z p.1)
    rw [sum_hilbertDifferenceKernel_copies] at hH
    have hnorm : ∑ p : ι × Fin J, ‖(-1 : ℂ) ^ (p.2 : ℕ) * z p.1‖ ^ 2 =
        J * ∑ r, ‖z r‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
    rw [hnorm] at hH
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ0
    have hfac : ∑ r, ∑ s, z r * conj (z s) *
        (((J : ℝ)⁻¹ * alternatingCopyKernel J (α r - α s) : ℝ) : ℂ) =
        (((J : ℝ)⁻¹ : ℝ) : ℂ) * ∑ r, ∑ s, z r * conj (z s) * (alternatingCopyKernel J (α r - α s) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [Complex.ofReal_mul]
      ring
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJR)]
    calc (J : ℝ)⁻¹ * _ ≤ (J : ℝ)⁻¹ * (π / δ * (J * ∑ r, ‖z r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hH (inv_pos.mpr hJR).le
      _ = π / δ * ∑ r, ‖z r‖ ^ 2 := by field_simp
  -- the limit `J → ∞`
  have hlim : Tendsto (fun J : ℕ => ∑ r, ∑ s, z r * conj (z s) *
      (((J : ℝ)⁻¹ * alternatingCopyKernel J (α r - α s) : ℝ) : ℂ)) atTop
      (𝓝 (∑ r, ∑ s, z r * conj (z s) * ((π / Real.sin (π * (α r - α s)) : ℝ) : ℂ))) := by
    refine tendsto_finsetSum _ fun r _ => tendsto_finsetSum _ fun s _ => ?_
    refine Tendsto.const_mul _ ((Complex.continuous_ofReal.tendsto _).comp ?_)
    refine tendsto_alternatingCopyKernel_div ?_
    by_cases hrs : r = s
    · exact Or.inl (by rw [hrs, sub_self])
    · refine Or.inr fun n hn => ?_
      have h := hsep r s hrs n
      rw [hn, sub_self, abs_zero] at h
      linarith
  have hle := le_of_tendsto (continuous_norm.tendsto _ |>.comp hlim)
    (eventually_atTop.mpr ⟨1, fun J hJ1 => hJ J hJ1⟩)
  have hpi : ∑ r, ∑ s, z r * conj (z s) * ((π / Real.sin (π * (α r - α s)) : ℝ) : ℂ) =
      (π : ℂ) * ∑ r, ∑ s, z r * conj (z s) * ((1 / Real.sin (π * (α r - α s)) : ℝ) : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    push_cast
    ring
  rw [hpi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hle
  rw [← mul_le_mul_iff_of_pos_left Real.pi_pos]
  calc π * _ ≤ π / δ * ∑ r, ‖z r‖ ^ 2 := hle
    _ = π * (δ⁻¹ * ∑ r, ‖z r‖ ^ 2) := by ring

end GaloisForLFunctions.HilbertInequality
