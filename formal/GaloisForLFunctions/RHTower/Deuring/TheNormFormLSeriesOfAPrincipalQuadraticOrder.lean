import GaloisForLFunctions.RHTower.Deuring.RepresentationNumbersOfAPrincipalQuadraticOrder

/-!
# The norm-form Dirichlet series of a principal quadratic order

Let `R = ℤ[ω]`, `ω² = a + bω`, be principal with `Δ = b² + 4a < 0`, let `r(n)` be the number of
elements of norm `n` and `χ` the completely multiplicative function with `χ(p) = ε_p` (the
splitting symbol).

* `LSeries_repCount`: `∑ r(n) n^{-s} = r(1) ζ(s) ∑ χ(n) n^{-s}` for `Re s > 1`, because
  `r = r(1) (1 ∗ χ)`.
* `one_sub_mul_LSeries_chiC`: `(1 − ε₂ 2^{-s}) ∑ χ(n) n^{-s} = ∑_{n odd} χ(n) n^{-s}`.
* `chiOdd_eq_jacobiFun`: on odd `n`, `χ(n)` is the Jacobi symbol `(Δ / n)`, which depends only on
  `n mod 4|Δ|`; so the odd part of `χ` is a function on `ℤ / 4|Δ|` and its Dirichlet series
  continues to `ℂ ∖ {1}`.
* `exists_LFunction_repCount`: there is `L`, holomorphic off `1`, with
  `(1 − ε₂ 2^{-s}) ∑ r(n) n^{-s} = r(1) ζ(s) L(s)` for `Re s > 1`.
-/

open Complex

namespace GaloisForLFunctions.RHTower.Deuring

variable {a b : ℤ}

noncomputable section

/-! ### The series of `r` is `r(1) ζ` times the series of `χ` -/

/-- `χ` as a complex-valued arithmetic function. -/
def chiC (a b : ℤ) (n : ℕ) : ℂ := ((chi a b n : ℤ) : ℂ)

theorem norm_chiC_le_one (a b : ℤ) (n : ℕ) : ‖chiC a b n‖ ≤ 1 := by
  rw [chiC, Complex.norm_intCast]
  exact_mod_cast abs_chi_le_one a b n

/-- `∑ r(n) n^{-s} = r(1) ζ(s) ∑ χ(n) n^{-s}` for `Re s > 1`. -/
theorem LSeries_repCount (hΔ : b ^ 2 + 4 * a < 0) [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (repCount a b n : ℂ)) s =
      (repCount a b 1 : ℂ) * (riemannZeta s * LSeries (chiC a b) s) := by
  have hconv : ∀ {n : ℕ}, n ≠ 0 → (repCount a b n : ℂ) =
      ((repCount a b 1 : ℂ) • LSeries.convolution 1 (chiC a b)) n := by
    intro n hn
    have h := repCount_eq hΔ (Nat.pos_of_ne_zero hn)
    have h' : (repCount a b n : ℂ) = (repCount a b 1 : ℂ) * ((divSum a b n : ℤ) : ℂ) := by
      exact_mod_cast h
    rw [h', Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
    congr 1
    have hd := Nat.sum_divisorsAntidiagonal' (fun x y => (1 : ℕ → ℂ) x * chiC a b y) (n := n)
    show _ = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chiC a b p.2
    rw [hd, divSum]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Pi.one_apply, one_mul, chiC]
  rw [LSeries_congr hconv, LSeries_smul, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_chiC_le_one a b n) hs),
    LSeries_one_eq_riemannZeta hs]

/-! ### The Euler factor at `2` -/

theorem chi_two_mul (n : ℕ) : chi a b (2 * n) = splitSym a b 2 * chi a b n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [mul_zero, chi_zero, mul_zero]
  · rw [chi_mul two_ne_zero hn, chi_prime Nat.prime_two]

/-- The odd part of `χ`. -/
def chiOdd (a b : ℤ) (n : ℕ) : ℂ := if Odd n then chiC a b n else 0

theorem norm_chiOdd_le_one (a b : ℤ) (n : ℕ) : ‖chiOdd a b n‖ ≤ 1 := by
  unfold chiOdd
  split_ifs
  · exact norm_chiC_le_one a b n
  · rw [norm_zero]
    exact zero_le_one

theorem term_chiC_two_mul (a b : ℤ) (s : ℂ) (k : ℕ) :
    LSeries.term (chiC a b) s (2 * k) =
      (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s) * LSeries.term (chiC a b) s k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [mul_zero, LSeries.term_zero, mul_zero]
  · have hcp : ((2 * k : ℕ) : ℂ) ^ s = (2 : ℂ) ^ s * (k : ℂ) ^ s := by
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_ofNat]
    have hchi : chiC a b (2 * k) = (splitSym a b 2 : ℂ) * chiC a b k := by
      rw [chiC, chiC, chi_two_mul, Int.cast_mul]
    rw [LSeries.term_of_ne_zero (mul_ne_zero two_ne_zero hk), LSeries.term_of_ne_zero hk, hcp,
      hchi, Complex.cpow_neg]
    ring

theorem term_chiOdd_even (a b : ℤ) (s : ℂ) (k : ℕ) :
    LSeries.term (chiOdd a b) s (2 * k) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [mul_zero, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero (mul_ne_zero two_ne_zero hk), chiOdd,
      if_neg (Nat.not_odd_iff_even.mpr (even_two_mul k)), zero_div]

theorem term_chiOdd_odd (a b : ℤ) (s : ℂ) (k : ℕ) :
    LSeries.term (chiOdd a b) s (2 * k + 1) = LSeries.term (chiC a b) s (2 * k + 1) := by
  rw [LSeries.term_of_ne_zero (by omega : 2 * k + 1 ≠ 0),
    LSeries.term_of_ne_zero (by omega : 2 * k + 1 ≠ 0), chiOdd, if_pos (odd_two_mul_add_one k)]

/-- Splitting off the even terms: `(1 − ε₂ 2^{-s}) ∑ χ(n) n^{-s} = ∑_{n odd} χ(n) n^{-s}`. -/
theorem one_sub_mul_LSeries_chiC (a b : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s)) * LSeries (chiC a b) s =
      LSeries (chiOdd a b) s := by
  have hf : Summable (LSeries.term (chiC a b) s) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_chiC_le_one a b n) hs
  have hg : Summable (LSeries.term (chiOdd a b) s) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_chiOdd_le_one a b n) hs
  have he : Function.Injective fun k : ℕ => 2 * k := mul_right_injective₀ two_ne_zero
  have ho : Function.Injective fun k : ℕ => 2 * k + 1 := fun x y h => by
    have h' : 2 * x + 1 = 2 * y + 1 := h
    omega
  have hfe : Summable fun k : ℕ => LSeries.term (chiC a b) s (2 * k) := hf.comp_injective he
  have hfo : Summable fun k : ℕ => LSeries.term (chiC a b) s (2 * k + 1) :=
    hf.comp_injective ho
  have hge : Summable fun k : ℕ => LSeries.term (chiOdd a b) s (2 * k) := hg.comp_injective he
  have hgo : Summable fun k : ℕ => LSeries.term (chiOdd a b) s (2 * k + 1) :=
    hg.comp_injective ho
  have h1 := tsum_even_add_odd hfe hfo
  have h2 := tsum_even_add_odd hge hgo
  have hE : ∑' k : ℕ, LSeries.term (chiC a b) s (2 * k) =
      (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s) * ∑' k : ℕ, LSeries.term (chiC a b) s k := by
    rw [← tsum_mul_left]
    exact tsum_congr (term_chiC_two_mul a b s)
  have hE' : ∑' k : ℕ, LSeries.term (chiOdd a b) s (2 * k) = 0 := by
    rw [tsum_congr (term_chiOdd_even a b s), tsum_zero]
  have hO : ∑' k : ℕ, LSeries.term (chiOdd a b) s (2 * k + 1) =
      ∑' k : ℕ, LSeries.term (chiC a b) s (2 * k + 1) := tsum_congr (term_chiOdd_odd a b s)
  rw [hE', zero_add, hO] at h2
  unfold LSeries
  rw [← h2]
  linear_combination (-1 : ℂ) * h1 + hE

/-! ### The odd part of `χ` is periodic -/

/-- On odd integers `χ` is the Jacobi symbol `(Δ / n)`. -/
theorem chi_eq_jacobiSym_of_odd (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] {n : ℕ} (hn : Odd n) :
    chi a b n = jacobiSym (b ^ 2 + 4 * a) n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd hn Nat.not_odd_zero
  | one => rw [chi_one, jacobiSym.one_right]
  | prime p hp =>
    haveI := Fact.mk hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact absurd hn (by decide)
    rw [chi_prime hp, splitSym_eq_legendreSym hΔ h2, jacobiSym.legendreSym.to_jacobiSym]
  | mul m n ihm ihn =>
    obtain ⟨hm, hn'⟩ := Nat.odd_mul.mp hn
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    haveI : NeZero n := ⟨hn'.pos.ne'⟩
    rw [chi_mul hm.pos.ne' hn'.pos.ne', ihm hm, ihn hn', jacobiSym.mul_right]

/-- The odd part of the Jacobi symbol `(Δ / ·)`, as a function on `ℤ / 4|Δ|`. -/
def jacobiFun (a b : ℤ) (j : ZMod (4 * (b ^ 2 + 4 * a).natAbs)) : ℂ :=
  if Odd j.val then ((jacobiSym (b ^ 2 + 4 * a) j.val : ℤ) : ℂ) else 0

/-- The odd part of `χ` factors through `ℤ / 4|Δ|`: the Jacobi symbol `(Δ / n)` of an odd `n`
depends only on `n mod 4|Δ|`. -/
theorem chiOdd_eq_jacobiFun (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] (n : ℕ) :
    chiOdd a b n = jacobiFun a b (n : ZMod (4 * (b ^ 2 + 4 * a).natAbs)) := by
  have hodd : Odd (n % (4 * (b ^ 2 + 4 * a).natAbs)) ↔ Odd n := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd n (Dvd.dvd.mul_right (by decide) _)]
  rw [chiOdd, jacobiFun, ZMod.val_natCast]
  by_cases hn : Odd n
  · rw [if_pos hn, if_pos (hodd.mpr hn), chiC, chi_eq_jacobiSym_of_odd hΔ hn,
      ← jacobiSym.mod_right _ hn]
  · rw [if_neg hn, if_neg fun h => hn (hodd.mp h)]

/-- **The norm-form Dirichlet series of a principal imaginary quadratic order.** There is a
function `L`, holomorphic on `ℂ ∖ {1}`, with
`(1 − ε₂ 2^{-s}) ∑ r(n) n^{-s} = r(1) ζ(s) L(s)` for `Re s > 1`; it is the continuation of
`∑_{n odd} (Δ / n) n^{-s}`. -/
theorem exists_LFunction_repCount (hΔ : b ^ 2 + 4 * a < 0)
    [IsPrincipalIdealRing (QuadraticAlgebra ℤ a b)] :
    ∃ L : ℂ → ℂ, (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ L s) ∧
      ∀ s : ℂ, 1 < s.re →
        (1 - (splitSym a b 2 : ℂ) * (2 : ℂ) ^ (-s)) * LSeries (fun n => (repCount a b n : ℂ)) s =
          (repCount a b 1 : ℂ) * (riemannZeta s * L s) := by
  haveI : NeZero (4 * (b ^ 2 + 4 * a).natAbs) :=
    ⟨mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hΔ.ne)⟩
  refine ⟨ZMod.LFunction (jacobiFun a b),
    fun s hs => ZMod.differentiableAt_LFunction _ s (Or.inl hs), fun s hs => ?_⟩
  have hL : ZMod.LFunction (jacobiFun a b) s = LSeries (chiOdd a b) s := by
    rw [ZMod.LFunction_eq_LSeries _ hs]
    exact LSeries_congr (fun {n} _ => (chiOdd_eq_jacobiFun hΔ n).symm) s
  rw [hL, ← one_sub_mul_LSeries_chiC a b hs, LSeries_repCount hΔ hs]
  ring

end

end GaloisForLFunctions.RHTower.Deuring
