/-
# The reflection cocycle is faithful on multiplicative integral Dirichlet data

The reflection cocycle of a carrier `f` is the intrinsic quotient `h_f(s) = f(1−s)/f(s)`.  It is
trivial exactly when `f` is *pointwise self-reflective*, `f(1−s) = f(s)` for every `s`.  This module
shows that, among carriers which are the everywhere-valid `L`-series of an integer-valued
multiplicative arithmetic function, the reflection constraint never fixes a nonconstant carrier: the
only self-reflective member is the constant `1`.  Equivalently, the reflection cocycle is a faithful
invariant — its kernel on this data is the single point `f ≡ 1`.

The mechanism is a growth dichotomy driven by integrality:

* **Infinite coefficient support collapses the carrier to zero.**  On `Re s ≤ 0` the term family
  `a n · n^{-s}` has norm `≥ 1` on the infinite support (a nonzero integer has modulus `≥ 1`, and
  `n^{−Re s} ≥ 1`), so it is not summable and the `tsum` junk value pins `f` to `0` there.  Exact
  symmetry `f s = f(1−s)` transports this to `Re s ≥ 1` (no conductor prefactor is needed), so `f`
  vanishes for all large real arguments; a converging `L`-series tends to its first coefficient
  `a 1 = 1`, so convergence is impossible and the junk value forces `f ≡ 0`.  Under any nonvanishing
  witness this branch is excluded.

* **Finite support forces a Dirichlet polynomial that cannot be symmetric unless constant.**  Writing
  `N₀` for the largest support point, if `N₀ ≥ 2` the two reflected frequency systems disagree:
  along the real axis `f(σ) → a 1 = 1` as `σ → +∞`, so `‖f(σ)‖` is bounded, whereas
  `f(1−σ) = ∑_n a_n n^{σ−1}` blows up — the dominant term has norm `≥ N₀^{σ−1}`, and
  `N₀^{σ−1} − (∑‖a_n‖)(N₀−1)^{σ−1} → ∞` because the ratio `N₀/(N₀−1) > 1`.  Exact symmetry equates a
  bounded quantity with an unbounded one, which is absurd; hence the support is `{1}` and
  `f ≡ a 1 = 1`.

Thus on integral multiplicative data the functional-equation constraint acts only through a
nontrivial cocycle class: trivial cocycle means constant carrier.
-/
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

noncomputable section

namespace RHTower

open Complex Filter

/-- **Infinite support under exact symmetry collapses the carrier to zero.**  If `f` is the
everywhere-valid `L`-series of an integer-valued arithmetic function `a` with infinite coefficient
support, and `f` is pointwise self-reflective `f(1−s) = f(s)`, then `f ≡ 0`.

On `Re s ≤ 0` the term norms are `≥ 1` on the infinite support, so the family is not summable and the
`tsum` junk value gives `f = 0`; symmetry carries this to `Re s ≥ 1`, so `f` vanishes for large real
arguments.  The eventually-zero dichotomy then either empties the support (contradicting infinitude)
or sends the abscissa of absolute convergence to `⊤`, whose junk value is identically `0`. -/
private theorem symmetric_infinite_support_zero {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hrep : ∀ s, f s = LSeries (fun n => a n) s)
    (hsym : ∀ s, f (1 - s) = f s)
    (hinf : (Function.support (fun n => a n)).Infinite) :
    ∀ s, f s = 0 := by
  have hge1 : ∀ z : ℂ, 1 ≤ z.re → f z = 0 := by
    intro z hz
    rw [← hsym z, hrep (1 - z)]
    exact LSeries_eq_zero_of_re_nonpos_of_int_of_infinite_support hint hinf
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
  exact eq_zero_of_int_of_infinite_support_of_eq_zero_of_one_le_re hrep hinf hge1

/-- **Finite support under exact symmetry forces the constant `1`.**  If `f` is the everywhere-valid
`L`-series of an integer-valued multiplicative arithmetic function `a` with finite coefficient
support and `f(1−s) = f(s)` for all `s`, then `f ≡ 1`.

The finite `L`-series is a Dirichlet polynomial `f(s) = ∑_{n ∈ supp} a_n n^{-s}` with `a 1 = 1`.  If
the support is `{1}` the polynomial is the single term `1`.  Otherwise let `N₀ ≥ 2` be the largest
support point.  Along the real axis `‖f(σ)‖ ≤ ∑‖a_n‖` for `σ ≥ 0`, so `‖f(σ+1)‖` is bounded by a
constant `B`; but `f(−m) = ∑_n a_n n^{m}` has norm at least
`N₀^{m} − (∑_{n≠N₀}‖a_n‖)(N₀−1)^{m}`, and since `N₀/(N₀−1) > 1` this exceeds `B` for large `m`.
Exact symmetry `f(−m) = f(m+1)` equates the two, which is impossible; hence the support is `{1}`. -/
private theorem symmetric_finite_support_eq_one {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hmul : a.IsMultiplicative) (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hrep : ∀ s, f s = LSeries (fun n => a n) s)
    (hsym : ∀ s, f (1 - s) = f s)
    (hfin : (Function.support (fun n => a n)).Finite) :
    ∀ s, f s = 1 := by
  set S : Finset ℕ := hfin.toFinset with hS
  have hmemS : ∀ n, n ∈ S ↔ a n ≠ 0 := by
    intro n; simp only [hS, Set.Finite.mem_toFinset, Function.mem_support]
  have ha1 : a 1 = 1 := hmul.map_one
  have h1S : (1 : ℕ) ∈ S := (hmemS 1).mpr (by rw [ha1]; norm_num)
  have h0S : (0 : ℕ) ∉ S := fun h => ((hmemS 0).mp h) a.map_zero
  have hterm_out : ∀ (s : ℂ) (n : ℕ), n ∉ S → LSeries.term (fun n => a n) s n = 0 := by
    intro s n hn
    rcases eq_or_ne n 0 with h0 | h0
    · rw [h0, LSeries.term_zero]
    · have han : a n = 0 := not_not.mp (mt (hmemS n).mpr hn)
      rw [LSeries.term_of_ne_zero h0 _ s, han, zero_div]
  have hFsum : ∀ s : ℂ, f s = ∑ n ∈ S, LSeries.term (fun n => a n) s n := by
    intro s
    rw [hrep s, show LSeries (fun n => a n) s = ∑' n, LSeries.term (fun n => a n) s n from rfl]
    exact tsum_eq_sum (fun n hn => hterm_out s n hn)
  have hnorm_ge : ∀ n ∈ S, (1 : ℝ) ≤ ‖a n‖ := by
    intro n hn
    have hane : a n ≠ 0 := (hmemS n).mp hn
    obtain ⟨k, hk⟩ := hint n
    have hk0 : k ≠ 0 := by rintro rfl; exact hane (by rw [hk]; norm_num)
    rw [hk, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hk0
  have hterm1 : ∀ s : ℂ, LSeries.term (fun n => a n) s 1 = 1 := by
    intro s
    rw [LSeries.term_of_ne_zero one_ne_zero (fun n => a n) s]
    show a 1 / ((1 : ℕ) : ℂ) ^ s = 1
    rw [ha1, Nat.cast_one, Complex.one_cpow, div_one]
  by_cases hbig : ∃ n ∈ S, 2 ≤ n
  · exfalso
    obtain ⟨n2, hn2S, hn2⟩ := hbig
    have hSne : S.Nonempty := ⟨1, h1S⟩
    set N₀ : ℕ := S.max' hSne with hN₀def
    have hN₀mem : N₀ ∈ S := S.max'_mem hSne
    have hle : ∀ n ∈ S, n ≤ N₀ := fun n hn => S.le_max' n hn
    have hN₀2 : 2 ≤ N₀ := le_trans hn2 (hle n2 hn2S)
    set B : ℝ := ∑ n ∈ S, ‖a n‖ with hB
    set D : ℝ := ∑ n ∈ S.erase N₀, ‖a n‖ with hD
    have hBnn : 0 ≤ B := Finset.sum_nonneg fun n _ => norm_nonneg _
    -- Uniform per-term bound on the closed right half-plane.
    have hterm_le : ∀ (s : ℂ), 0 ≤ s.re → ∀ n ∈ S,
        ‖LSeries.term (fun n => a n) s n‖ ≤ ‖a n‖ := by
      intro s hs n hn
      have hn0 : n ≠ 0 := fun h => h0S (h ▸ hn)
      rw [LSeries.norm_term_eq, if_neg hn0]
      exact div_le_self (norm_nonneg _)
        (Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) hs)
    -- Boundedness along the real axis to the right.
    have hUpper : ∀ m : ℕ, ‖f ((((m : ℝ) + 1 : ℝ)) : ℂ)‖ ≤ B := by
      intro m
      rw [hFsum ((((m : ℝ) + 1 : ℝ)) : ℂ)]
      refine le_trans (norm_sum_le _ _) ?_
      rw [hB]
      have hre_nn : (0 : ℝ) ≤ ((((m : ℝ) + 1 : ℝ)) : ℂ).re := by
        rw [Complex.ofReal_re]; positivity
      exact Finset.sum_le_sum (fun n hn => hterm_le _ hre_nn n hn)
    -- A blowing-up reflected lower bound via the dominant frequency `N₀`.
    have hrev : ∀ x y : ℂ, ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
      intro x y
      have h := norm_sub_le (x + y) y
      rw [add_sub_cancel_right] at h
      linarith
    have hLower : ∀ m : ℕ,
        (N₀ : ℝ) ^ m - D * ((N₀ : ℝ) - 1) ^ m ≤ ‖f ((((m : ℝ) + 1 : ℝ)) : ℂ)‖ := by
      intro m
      have hwcast : (1 : ℂ) - ((((m : ℝ) + 1 : ℝ)) : ℂ) = -((m : ℕ) : ℂ) := by push_cast; ring
      have hval : f ((((m : ℝ) + 1 : ℝ)) : ℂ) = ∑ n ∈ S, a n * ((n : ℂ) ^ m) := by
        rw [← hsym ((((m : ℝ) + 1 : ℝ)) : ℂ), hwcast, hFsum (-((m : ℕ) : ℂ))]
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := fun h => h0S (h ▸ hn)
        rw [LSeries.term_of_ne_zero hn0 (fun n => a n) (-((m : ℕ) : ℂ))]
        show a n / ((n : ℂ) ^ (-((m : ℕ) : ℂ))) = a n * (n : ℂ) ^ m
        rw [Complex.cpow_neg, Complex.cpow_natCast, div_eq_mul_inv, inv_inv]
      have hsplit : ∑ n ∈ S, a n * ((n : ℂ) ^ m)
          = a N₀ * ((N₀ : ℂ) ^ m) + ∑ n ∈ S.erase N₀, a n * ((n : ℂ) ^ m) :=
        (Finset.add_sum_erase S (fun n => a n * ((n : ℂ) ^ m)) hN₀mem).symm
      rw [hval, hsplit]
      have hbignorm : (N₀ : ℝ) ^ m ≤ ‖a N₀ * ((N₀ : ℂ) ^ m)‖ := by
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        calc (N₀ : ℝ) ^ m = 1 * (N₀ : ℝ) ^ m := (one_mul _).symm
          _ ≤ ‖a N₀‖ * (N₀ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_right (hnorm_ge N₀ hN₀mem) (by positivity)
      have hrestnorm : ‖∑ n ∈ S.erase N₀, a n * ((n : ℂ) ^ m)‖ ≤ D * ((N₀ : ℝ) - 1) ^ m := by
        refine le_trans (norm_sum_le _ _) ?_
        rw [hD, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro n hn
        have hnS : n ∈ S := Finset.mem_of_mem_erase hn
        have hnN₀ : n ≠ N₀ := Finset.ne_of_mem_erase hn
        have hnlt : n < N₀ := lt_of_le_of_ne (hle n hnS) hnN₀
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply pow_le_pow_left₀ (by positivity)
        have hle1 : n ≤ N₀ - 1 := by omega
        calc (n : ℝ) ≤ ((N₀ - 1 : ℕ) : ℝ) := by exact_mod_cast hle1
          _ = (N₀ : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      calc (N₀ : ℝ) ^ m - D * ((N₀ : ℝ) - 1) ^ m
          ≤ ‖a N₀ * ((N₀ : ℂ) ^ m)‖ - ‖∑ n ∈ S.erase N₀, a n * ((n : ℂ) ^ m)‖ := by linarith
        _ ≤ ‖a N₀ * ((N₀ : ℂ) ^ m) + ∑ n ∈ S.erase N₀, a n * ((n : ℂ) ^ m)‖ := hrev _ _
    -- Symmetry equates the bounded and the unbounded quantities: contradiction.
    have hcontra : ∀ m : ℕ, (N₀ : ℝ) ^ m ≤ B + D * ((N₀ : ℝ) - 1) ^ m := by
      intro m; have h1 := hLower m; have h2 := hUpper m; linarith
    have hN₀R : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀2
    have hden1 : (0 : ℝ) < (N₀ : ℝ) - 1 := by linarith
    have hden1' : (1 : ℝ) ≤ (N₀ : ℝ) - 1 := by linarith
    have hne : ((N₀ : ℝ) - 1) ≠ 0 := by linarith
    have hρ1 : (1 : ℝ) < (N₀ : ℝ) / ((N₀ : ℝ) - 1) := by rw [lt_div_iff₀ hden1]; linarith
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (B + D) hρ1
    have hident : ((N₀ : ℝ) / ((N₀ : ℝ) - 1)) ^ m * ((N₀ : ℝ) - 1) ^ m = (N₀ : ℝ) ^ m := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero m hne)]
    have hpowpos : (0 : ℝ) < ((N₀ : ℝ) - 1) ^ m := pow_pos hden1 m
    have hpow1 : (1 : ℝ) ≤ ((N₀ : ℝ) - 1) ^ m := one_le_pow₀ hden1'
    have hstep1 : (B + D) * ((N₀ : ℝ) - 1) ^ m < (N₀ : ℝ) ^ m := by
      rw [← hident]; exact mul_lt_mul_of_pos_right hm hpowpos
    have hstep2 : B + D * ((N₀ : ℝ) - 1) ^ m ≤ (B + D) * ((N₀ : ℝ) - 1) ^ m := by
      have hBle : B ≤ B * ((N₀ : ℝ) - 1) ^ m := le_mul_of_one_le_right hBnn hpow1
      have hexp : (B + D) * ((N₀ : ℝ) - 1) ^ m
          = B * ((N₀ : ℝ) - 1) ^ m + D * ((N₀ : ℝ) - 1) ^ m := by ring
      linarith
    have hc := hcontra m
    linarith
  · -- No support point `≥ 2`: the support is `{1}`, so `f ≡ 1`.
    have hSeq : S = {1} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨h1S, fun x hx => ?_⟩
      by_contra hx1
      rcases eq_or_ne x 0 with rfl | hx0
      · exact h0S hx
      · exact hbig ⟨x, hx, by omega⟩
    intro s
    rw [hFsum s, hSeq, Finset.sum_singleton, hterm1 s]

/-- **A self-reflective integral multiplicative carrier is the constant `1`.**  If `f` is the
everywhere-valid `L`-series of an integer-valued multiplicative arithmetic function `a`, is pointwise
self-reflective `f(1−s) = f(s)`, and is not identically zero, then `f ≡ 1`.

Case split on the finiteness of the coefficient support.  Infinite support collapses `f` to zero
under exact symmetry (contradicting the nonvanishing witness).  Finite support yields a Dirichlet
polynomial whose only symmetric member is the constant `1`: any support point `N₀ ≥ 2` makes the two
reflected frequency systems grow incompatibly along the real axis. -/
theorem symmetric_multiplicative_integral_eq_one {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hmul : a.IsMultiplicative) (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hrep : ∀ s, f s = LSeries (fun n => a n) s)
    (hsym : ∀ s, f (1 - s) = f s)
    (hne : ∃ s, f s ≠ 0) :
    ∀ s, f s = 1 := by
  by_cases hfin : (Function.support (fun n => a n)).Finite
  · exact symmetric_finite_support_eq_one hmul hint hrep hsym hfin
  · exfalso
    obtain ⟨s0, hs0⟩ := hne
    exact hs0 (symmetric_infinite_support_zero hint hrep hsym hfin s0)

/-- **The reflection cocycle is faithful on integral multiplicative data.**  For a carrier `f` that
is the everywhere-valid `L`-series of an integer-valued multiplicative arithmetic function, the
reflection cocycle `h_f(s) = f(1−s)/f(s)` is trivial (identically `1`) if and only if `f` is the
constant `1`. No nonvanishing premise is required: cocycle triviality itself forces `f s ≠ 0` at
every point, since division by zero is zero in the ambient field.

Forward: `h_f(s) = 1` first forces `f s ≠ 0`, then gives `f(1−s) = f(s)`, so `f` is
self-reflective and the structure theorem forces `f ≡ 1`. Backward: a constant carrier has
`f(1−s)/f(s) = 1/1 = 1`. -/
theorem reflCocycle_eq_one_iff_const {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hmul : a.IsMultiplicative) (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hrep : ∀ s, f s = LSeries (fun n => a n) s) :
    (∀ s, reflCocycle f s = 1) ↔ ∀ s, f s = 1 := by
  constructor
  · intro hcoc
    obtain ⟨hne, hsym⟩ :=
      (reflCocycle_eq_one_iff_reflectionInvariant f).mp hcoc
    exact symmetric_multiplicative_integral_eq_one hmul hint hrep hsym ⟨0, hne 0⟩
  · intro hconst s
    simp only [reflCocycle, hconst, div_one]

end RHTower
