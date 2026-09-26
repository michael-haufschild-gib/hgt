import GaloisForLFunctions.RHTower.CCMRestrictedWeilApertureMonotonicity

/-!
# Selberg-weighted von Mangoldt completions of the restricted Weil form

At aperture `a` the restricted Weil form sees the prime side only through `Λ(n)` for
`n ≤ X = ⌊e^{2a}⌋`.  Translations by `log n > 2a` have zero compressed matrix coefficient, so every
arithmetic weight that agrees with `Λ` below `X` defines the same level-`a` form.  Such a weight is a
Krein completion of the level-`a` Weil kernel: it fixes the kernel on `(-2a, 2a)` and chooses it
beyond the aperture.

Selberg's truncation gives a canonical family of these completions.  For a weight `w` with
`w(d) = 1` whenever `1 ≤ d ≤ X`, set

  `Λ_w(n) = ∑_{d ∣ n} μ(d) w(d) log(n/d)`.

This module proves:

* `selbergWeightedVonMangoldt_eq_vonMangoldt_of_le`: `Λ_w(n) = Λ(n)` for `n ≤ X`, so `Λ_w` is a
  completion;
* `selbergWeightedVonMangoldt_prime_pow`: `Λ_w(p^k) = log p · (k - (k-1) w(p))`, so
  `Λ_w(p) = log p` at every prime, including the invisible primes `p > X`;
* `ccmRestrictedWeilSourceQuadraticWith_selberg_eq`: for every prime-side cutoff `N ≥ X`, the
  Weil source quadratic built from `Λ_w` is the level-`a` Weil form;
* `LSeries_selbergWeightedVonMangoldt`: the Dirichlet series of `Λ_w` is
  `-(∑ μ(d) w(d) d^{-s}) · ζ'(s)`.  It has no factor `1/ζ`.

So the completion is exact at every prime.  Its only freedom sits at composite and
large-prime-power frequencies `n > X`, and it couples different primes through those composite
frequencies.  Its prime-side Dirichlet series is the mollified derivative `M_w ζ'`.  On the critical
line its Krein symbol is therefore `2θ' + 2 Re(ζ' M_w)` plus explicit polar terms, with `θ` the
Riemann–Siegel theta function.  A positive symbol would certify the level-`a` Hodge index.
-/

open ArithmeticFunction Complex Filter Topology

namespace RHTower

noncomputable section

/-- Selberg-weighted von Mangoldt function `Λ_w(n) = ∑_{d ∣ n} μ(d) w(d) log(n/d)`, written on the
divisor antidiagonal `(n/d, d)`. -/
def selbergWeightedVonMangoldt (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, Real.log x.1 * ((moebius x.2 : ℝ) * w x.2)

/-- `Λ = log ⋆ μ` on the divisor antidiagonal. -/
theorem vonMangoldt_eq_sum_divisorsAntidiagonal_log_mul_moebius (n : ℕ) :
    (Λ n : ℝ) = ∑ x ∈ n.divisorsAntidiagonal, Real.log x.1 * (moebius x.2 : ℝ) := by
  rw [← log_mul_moebius_eq_vonMangoldt, mul_apply]
  simp [log_apply, intCoe_apply]

/-- If the weight is one on every divisor of `n`, the Selberg weight at `n` is `Λ(n)`. -/
theorem selbergWeightedVonMangoldt_eq_vonMangoldt_of_forall_dvd {w : ℕ → ℝ} {n : ℕ}
    (hw : ∀ d, d ∣ n → w d = 1) : selbergWeightedVonMangoldt w n = Λ n := by
  rw [vonMangoldt_eq_sum_divisorsAntidiagonal_log_mul_moebius]
  unfold selbergWeightedVonMangoldt
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [hw x.2 (Dvd.intro_left _ hmul), mul_one]

/-- **Agreement below the aperture.**  A weight equal to one on `[1, X]` reproduces `Λ` on `[0, X]`. -/
theorem selbergWeightedVonMangoldt_eq_vonMangoldt_of_le {w : ℕ → ℝ} {X n : ℕ}
    (hw : ∀ d, 1 ≤ d → d ≤ X → w d = 1) (hn : n ≤ X) :
    selbergWeightedVonMangoldt w n = Λ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [selbergWeightedVonMangoldt]
  · refine selbergWeightedVonMangoldt_eq_vonMangoldt_of_forall_dvd fun d hd => hw d ?_ ?_
    · exact Nat.pos_of_dvd_of_pos hd hpos
    · exact (Nat.le_of_dvd hpos hd).trans hn

/-- **Prime powers.**  `Λ_w(p^k) = log p · (k - (k-1) w(p))` for `k ≥ 1`. -/
theorem selbergWeightedVonMangoldt_prime_pow {w : ℕ → ℝ} (hw1 : w 1 = 1) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    selbergWeightedVonMangoldt w (p ^ k) = Real.log p * ((k : ℝ) - ((k : ℝ) - 1) * w p) := by
  unfold selbergWeightedVonMangoldt
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => Real.log x * ((moebius y : ℝ) * w y)),
    Nat.sum_divisors_prime_pow hp]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp0 : 0 < p := hp.pos
  have hterm : ∀ j : ℕ, j ≤ m + 1 →
      Real.log ((p ^ (m + 1) / p ^ j : ℕ) : ℝ) = ((m + 1 - j : ℕ) : ℝ) * Real.log p := by
    intro j hj
    rw [Nat.pow_div hj hp0, Nat.cast_pow, Real.log_pow]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ j ∈ Finset.range m,
      Real.log ((p ^ (m + 1) / p ^ (j + 1 + 1) : ℕ) : ℝ) *
        ((moebius (p ^ (j + 1 + 1)) : ℝ) * w (p ^ (j + 1 + 1))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [hrest, zero_add, hterm 1 (by omega), hterm 0 (by omega),
    moebius_apply_prime_pow hp (by omega), if_pos rfl, pow_zero, moebius_apply_one, pow_one, hw1]
  push_cast
  ring

/-- **Exactness at every prime.**  Every Selberg completion keeps `Λ(p) = log p` at all primes,
visible or not. -/
theorem selbergWeightedVonMangoldt_prime {w : ℕ → ℝ} (hw1 : w 1 = 1) {p : ℕ} (hp : p.Prime) :
    selbergWeightedVonMangoldt w p = Real.log p := by
  have h := selbergWeightedVonMangoldt_prime_pow hw1 hp (le_refl 1)
  rw [pow_one] at h
  rw [h]
  push_cast
  ring

/-! ## The level-`a` Weil form is blind to the completion -/

/-- The restricted Weil source quadratic with an arbitrary prime-side weight `lam` and cutoff `N`. -/
def ccmRestrictedWeilSourceQuadraticWith (a : SuzukiPositiveAperture) (lam : ℕ → ℝ) (N : ℕ)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
      ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) +
    ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re -
    ∑ n ∈ Finset.Icc 2 N,
      lam n * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re

/-- **Krein completion invariance.**  Any weight equal to `Λ` on `[2, ⌊e^{2a}⌋]`, summed to any
cutoff `N ≥ ⌊e^{2a}⌋`, gives the level-`a` Weil form. -/
theorem ccmRestrictedWeilSourceQuadraticWith_eq (a : SuzukiPositiveAperture) (lam : ℕ → ℝ)
    {N : ℕ} (hN : Nat.floor (Real.exp (2 * a.1)) ≤ N)
    (hlam : ∀ n, 2 ≤ n → n ≤ Nat.floor (Real.exp (2 * a.1)) → lam n = Λ n)
    (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadraticWith a lam N u = ccmRestrictedWeilSourceQuadratic a u := by
  classical
  unfold ccmRestrictedWeilSourceQuadraticWith ccmRestrictedWeilSourceQuadratic
  dsimp only
  congr 1
  set f := ccmArchimedeanFormToAperture a u with hf
  have hvan : ∀ n ∈ Finset.Icc 2 N, n ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) →
      lam n * (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
          inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re = 0 := by
    intro n hnN hna
    rw [Finset.mem_Icc] at hnN
    have hfloor : Nat.floor (Real.exp (2 * a.1)) < n := by
      by_contra hnot
      exact hna (Finset.mem_Icc.mpr ⟨hnN.1, Nat.le_of_not_gt hnot⟩)
    have hexpN : Real.exp (2 * a.1) < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hnN.1)
    have hlog : 2 * a.1 < Real.log n := by
      have hstrict := Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (Real.exp_pos (2 * a.1))) (Set.mem_Ioi.mpr hnpos) hexpN
      rwa [Real.log_exp] at hstrict
    rw [inner_symmetric_logTranslations_eq_zero_of_aperture a f hlog]
    simp
  have hsub : Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) ⊆ Finset.Icc 2 N := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hN⟩
  rw [← Finset.sum_subset hsub hvan]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  rw [hlam n hn.1 hn.2]

/-- **Every Selberg completion reproduces the level-`a` Weil form.** -/
theorem ccmRestrictedWeilSourceQuadraticWith_selberg_eq (a : SuzukiPositiveAperture)
    {w : ℕ → ℝ} (hw : ∀ d, 1 ≤ d → d ≤ Nat.floor (Real.exp (2 * a.1)) → w d = 1)
    {N : ℕ} (hN : Nat.floor (Real.exp (2 * a.1)) ≤ N) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadraticWith a (selbergWeightedVonMangoldt w) N u =
      ccmRestrictedWeilSourceQuadratic a u :=
  ccmRestrictedWeilSourceQuadraticWith_eq a _ hN
    (fun _ _ hn => selbergWeightedVonMangoldt_eq_vonMangoldt_of_le hw hn) u

/-! ## The completion's Dirichlet series is the mollified derivative `-M_w ζ'` -/

/-- **Dirichlet series of the Selberg completion.**  For a bounded weight and `Re s > 1`,
`∑ Λ_w(n) n^{-s} = -(∑ μ(d) w(d) d^{-s}) ζ'(s)`. -/
theorem LSeries_selbergWeightedVonMangoldt {w : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |w n| ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (selbergWeightedVonMangoldt w n : ℂ)) s =
      -(LSeries (fun n => (((moebius n : ℝ) * w n : ℝ) : ℂ)) s * deriv riemannZeta s) := by
  set g : ℕ → ℂ := fun n => (((moebius n : ℝ) * w n : ℝ) : ℂ) with hg
  have hconv : (fun n => (selbergWeightedVonMangoldt w n : ℂ)) =
      LSeries.convolution (LSeries.logMul 1) g := by
    funext n
    rw [LSeries.convolution_def]
    simp only [selbergWeightedVonMangoldt, LSeries.logMul, Pi.one_apply, mul_one, hg]
    push_cast
    rfl
  have hab : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    refine lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_) ?_
    · exact LSeriesSummable_one_iff.mpr (by simpa using hy)
    · exact_mod_cast hs
  have hlog : LSeriesSummable (LSeries.logMul 1) s := LSeriesSummable_logMul_of_lt_re hab
  have hgs : LSeriesSummable g s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := C) (fun n _ => ?_) hs
    simp only [hg, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hμ : |(moebius n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    calc |(moebius n : ℝ)| * |w n| ≤ 1 * C :=
          mul_le_mul hμ (hC n) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hevent : LSeries (1 : ℕ → ℂ) =ᶠ[𝓝 s] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact LSeries_one_eq_riemannZeta hz
  have hderiv : LSeries (LSeries.logMul 1) s = -deriv riemannZeta s := by
    rw [← hevent.deriv_eq, LSeries_deriv hab, neg_neg]
  rw [hconv, LSeries_convolution' hlog hgs, hderiv]
  ring

end

end RHTower
