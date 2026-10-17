import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.LaguerreInequality

/-!
# The non-tempered countermodel `ζ(s − a) ζ(s + a)`

For real `a ≠ 0` the function `F_a(s) = ζ(s − a) ζ(s + a)` has every structural property that a
"Selberg-type" argument for the Riemann hypothesis might use, except the Ramanujan bound on its
coefficients, and its zeros lie on the two lines `Re s = ½ ± a`.  Any argument that proves
"zeros on the line" from the properties listed below alone is therefore wrong, because it would
prove a false statement for `F_a`.  This is the temperedness gate: a proof of RH must use the size
of the coefficients.

* **Dirichlet series with nonnegative coefficients.**  On `Re s > 1 + |a|`,
  `F_a(s) = Σ c_a(n) n^{−s}` with `c_a(n) = Σ_{de = n} d^{a} e^{−a} ≥ 0`, `c_a(1) = 1`
  (`lSeries_shiftedPairCoeff`, `shiftedPairCoeff_nonneg`, `shiftedPairCoeff_one`).
* **Euler product in logarithmic form.**  On `Re s > 1 + |a|`,
  `−F_a'(s)/F_a(s) = Σ Λ_a(n) n^{−s}` with `Λ_a(n) = Λ(n)(n^{a} + n^{−a}) = 2Λ(n) cosh(a log n) ≥ 0`
  supported on prime powers (`neg_deriv_shiftedZetaPair_div`, `shiftedPairVonMangoldt_nonneg`,
  `shiftedPairVonMangoldt_eq_zero_of_not_isPrimePow`).
* **Functional equation.**  The completed pair `Λ_a(s) = Λ(s − a) Λ(s + a)` (with Riemann's
  completed zeta `Λ`) satisfies `Λ_a(1 − s) = Λ_a(s)` for every `s` (`shiftedCompletedPair_one_sub`).
* **Polynomial growth** on vertical strips (`exists_norm_shiftedZetaPair_le`, from the convexity
  bound for `ζ`).
* **Off-line zeros.**  Every critical zero `½ + iγ` of `ζ` (Hardy's theorem supplies infinitely
  many) gives the zeros `½ ± a + iγ` of `F_a`, of real part `≠ ½`
  (`exists_offLine_zero_shiftedZetaPair`).
* **Ramanujan fails.**  `c_a(p) ≥ p^{|a|}` at every prime, so no bound `c_a(n) ≤ C n^{ε}` with
  `ε < |a|` holds (`not_ramanujan_shiftedPairCoeff`).

The function also has poles at `1 ± a` rather than at `1`; the point of the countermodel is the
list of positive properties above, all of which hold with the same proofs as for `ζ` itself.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The shifted pair `F_a(s) = ζ(s − a) ζ(s + a)`. -/
def shiftedZetaPair (a : ℝ) (s : ℂ) : ℂ := riemannZeta (s - a) * riemannZeta (s + a)

/-- The completed shifted pair `Λ(s − a) Λ(s + a)`. -/
def shiftedCompletedPair (a : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (s - a) * completedRiemannZeta (s + a)

/-- The Dirichlet coefficients `c_a(n) = Σ_{de = n} d^{a} e^{−a}`. -/
def shiftedPairCoeff (a : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal, (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ (-a)

/-- The von Mangoldt weights `Λ_a(n) = Λ(n)(n^{a} + n^{−a})` of the shifted pair. -/
def shiftedPairVonMangoldt (a : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ a + (n : ℝ) ^ (-a))

/-! ## Functional equation -/

/-- `Λ_a(1 − s) = Λ_a(s)`: the completed shifted pair is invariant under `s ↦ 1 − s`. -/
theorem shiftedCompletedPair_one_sub (a : ℝ) (s : ℂ) :
    shiftedCompletedPair a (1 - s) = shiftedCompletedPair a s := by
  unfold shiftedCompletedPair
  have h1 : (1 : ℂ) - s - a = 1 - (s + a) := by ring
  have h2 : (1 : ℂ) - s + a = 1 - (s - a) := by ring
  rw [h1, h2, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub, mul_comm]

/-! ## Coefficients -/

theorem shiftedPairCoeff_nonneg (a : ℝ) (n : ℕ) : 0 ≤ shiftedPairCoeff a n :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem shiftedPairCoeff_one (a : ℝ) : shiftedPairCoeff a 1 = 1 := by
  unfold shiftedPairCoeff
  rw [Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp

/-- At a prime, `c_a(p) ≥ p^{|a|}`. -/
theorem rpow_abs_le_shiftedPairCoeff_prime (a : ℝ) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ |a| ≤ shiftedPairCoeff a p := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hnn : ∀ q ∈ p.divisorsAntidiagonal, 0 ≤ (q.1 : ℝ) ^ a * (q.2 : ℝ) ^ (-a) := fun q _ =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  unfold shiftedPairCoeff
  rcases le_or_gt 0 a with ha | ha
  · have hmem : ((p, 1) : ℕ × ℕ) ∈ p.divisorsAntidiagonal := by
      rw [Nat.mem_divisorsAntidiagonal]; exact ⟨mul_one p, hp0⟩
    have := Finset.single_le_sum hnn hmem
    rw [abs_of_nonneg ha]
    simpa using this
  · have hmem : ((1, p) : ℕ × ℕ) ∈ p.divisorsAntidiagonal := by
      rw [Nat.mem_divisorsAntidiagonal]; exact ⟨one_mul p, hp0⟩
    have := Finset.single_le_sum hnn hmem
    rw [abs_of_neg ha]
    simpa using this

/-- **Ramanujan fails.**  No bound `c_a(n) ≤ C n^{ε}` with `ε < |a|` holds for all `n`. -/
theorem not_ramanujan_shiftedPairCoeff {a ε : ℝ} (hε : ε < |a|) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → shiftedPairCoeff a n ≤ C * (n : ℝ) ^ ε := by
  rintro ⟨C, hC⟩
  have hδ : 0 < |a| - ε := by linarith
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (C + 1)))
  obtain ⟨p, hpX, hp⟩ := Nat.exists_infinite_primes (⌈X⌉₊ + 2)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpX' : X ≤ (p : ℝ) :=
    le_trans (Nat.le_ceil X) (by exact_mod_cast (by omega : ⌈X⌉₊ ≤ p))
  have h1 := hX p hpX'
  have h2 := hC p hp.ne_zero
  have h3 := rpow_abs_le_shiftedPairCoeff_prime a hp
  have hpε : 0 < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp0 ε
  have hsplit : (p : ℝ) ^ |a| = (p : ℝ) ^ (|a| - ε) * (p : ℝ) ^ ε := by
    rw [← Real.rpow_add hp0, sub_add_cancel]
  have : (C + 1) * (p : ℝ) ^ ε ≤ C * (p : ℝ) ^ ε :=
    calc (C + 1) * (p : ℝ) ^ ε ≤ (p : ℝ) ^ (|a| - ε) * (p : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right h1 hpε.le
      _ = (p : ℝ) ^ |a| := hsplit.symm
      _ ≤ shiftedPairCoeff a p := h3
      _ ≤ C * (p : ℝ) ^ ε := h2
  nlinarith

/-! ## Dirichlet series -/

/-- Multiplying the coefficients by `n^{a}` shifts the Dirichlet series: termwise identity. -/
theorem term_natCast_cpow_mul (f : ℕ → ℂ) (a : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (n : ℂ) ^ (a : ℂ) * f n) s n = LSeries.term f (s - a) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hs : (n : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hn0 h.1
    have ha : (n : ℂ) ^ (a : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hn0 h.1
    rw [Complex.cpow_sub _ _ hn0]
    field_simp

theorem lSeriesSummable_natCast_cpow_mul_iff (f : ℕ → ℂ) (a : ℝ) (s : ℂ) :
    LSeriesSummable (fun n => (n : ℂ) ^ (a : ℂ) * f n) s ↔ LSeriesSummable f (s - a) := by
  unfold LSeriesSummable
  have : LSeries.term (fun n => (n : ℂ) ^ (a : ℂ) * f n) s = LSeries.term f (s - a) :=
    funext (term_natCast_cpow_mul f a s)
  rw [this]

theorem lSeries_natCast_cpow_mul (f : ℕ → ℂ) (a : ℝ) (s : ℂ) :
    LSeries (fun n => (n : ℂ) ^ (a : ℂ) * f n) s = LSeries f (s - a) := by
  unfold LSeries
  exact tsum_congr (term_natCast_cpow_mul f a s)

theorem re_sub_ofReal (s : ℂ) (a : ℝ) : (s - (a : ℂ)).re = s.re - a := by simp

/-- The convolution of the two shifted unit series is the coefficient sequence `c_a`. -/
theorem convolution_eq_shiftedPairCoeff (a : ℝ) (n : ℕ) :
    LSeries.convolution (fun n => (n : ℂ) ^ (a : ℂ) * (1 : ℕ → ℂ) n)
      (fun n => (n : ℂ) ^ ((-a : ℝ) : ℂ) * (1 : ℕ → ℂ) n) n = (shiftedPairCoeff a n : ℂ) := by
  rw [LSeries.convolution_def]
  unfold shiftedPairCoeff
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.one_apply, mul_one]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  ring

/-- **Dirichlet series of the shifted pair.**  On `Re s > 1 + |a|`,
`Σ c_a(n) n^{−s} = ζ(s − a) ζ(s + a)`. -/
theorem lSeries_shiftedPairCoeff {a : ℝ} {s : ℂ} (hs : 1 + |a| < s.re) :
    LSeries (fun n => (shiftedPairCoeff a n : ℂ)) s = shiftedZetaPair a s := by
  have hre1 : 1 < (s - (a : ℂ)).re := by rw [re_sub_ofReal]; linarith [le_abs_self a]
  have hre2 : 1 < (s - ((-a : ℝ) : ℂ)).re := by rw [re_sub_ofReal]; linarith [neg_abs_le a]
  have hfa : LSeriesSummable (fun n => (n : ℂ) ^ (a : ℂ) * (1 : ℕ → ℂ) n) s :=
    (lSeriesSummable_natCast_cpow_mul_iff _ _ _).2 (LSeriesSummable_one_iff.2 hre1)
  have hfb : LSeriesSummable (fun n => (n : ℂ) ^ ((-a : ℝ) : ℂ) * (1 : ℕ → ℂ) n) s :=
    (lSeriesSummable_natCast_cpow_mul_iff _ _ _).2 (LSeriesSummable_one_iff.2 hre2)
  rw [LSeries_congr (f := fun n => (shiftedPairCoeff a n : ℂ))
    (g := LSeries.convolution (fun n => (n : ℂ) ^ (a : ℂ) * (1 : ℕ → ℂ) n)
      (fun n => (n : ℂ) ^ ((-a : ℝ) : ℂ) * (1 : ℕ → ℂ) n))
    (fun {n} _ => (convolution_eq_shiftedPairCoeff a n).symm) s,
    LSeries_convolution' hfa hfb, lSeries_natCast_cpow_mul, lSeries_natCast_cpow_mul,
    LSeries_one_eq_riemannZeta hre1, LSeries_one_eq_riemannZeta hre2]
  unfold shiftedZetaPair
  rw [Complex.ofReal_neg, sub_neg_eq_add]

/-! ## Logarithmic Euler product -/

theorem shiftedPairVonMangoldt_nonneg (a : ℝ) (n : ℕ) : 0 ≤ shiftedPairVonMangoldt a n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem shiftedPairVonMangoldt_eq_zero_of_not_isPrimePow (a : ℝ) {n : ℕ} (h : ¬ IsPrimePow n) :
    shiftedPairVonMangoldt a n = 0 := by
  unfold shiftedPairVonMangoldt
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 h, zero_mul]

theorem hasDerivAt_shiftedZetaPair {a : ℝ} {s : ℂ} (h1 : s - a ≠ 1) (h2 : s + a ≠ 1) :
    HasDerivAt (shiftedZetaPair a)
      (deriv riemannZeta (s - a) * riemannZeta (s + a) +
        riemannZeta (s - a) * deriv riemannZeta (s + a)) s := by
  have hA : HasDerivAt (fun s : ℂ => riemannZeta (s - a)) (deriv riemannZeta (s - a) * 1) s :=
    (differentiableAt_riemannZeta h1).hasDerivAt.comp s ((hasDerivAt_id s).sub_const (a : ℂ))
  have hB : HasDerivAt (fun s : ℂ => riemannZeta (s + a)) (deriv riemannZeta (s + a) * 1) s :=
    (differentiableAt_riemannZeta h2).hasDerivAt.comp s ((hasDerivAt_id s).add_const (a : ℂ))
  have := hA.mul hB
  rw [mul_one, mul_one] at this
  exact this

/-- **Logarithmic Euler product.**  On `Re s > 1 + |a|`,
`−F_a'(s)/F_a(s) = Σ Λ(n)(n^{a} + n^{−a}) n^{−s}`. -/
theorem neg_deriv_shiftedZetaPair_div {a : ℝ} {s : ℂ} (hs : 1 + |a| < s.re) :
    -deriv (shiftedZetaPair a) s / shiftedZetaPair a s =
      LSeries (fun n => (shiftedPairVonMangoldt a n : ℂ)) s := by
  have hre1 : 1 < (s - (a : ℂ)).re := by rw [re_sub_ofReal]; linarith [le_abs_self a]
  have hre2' : 1 < (s - ((-a : ℝ) : ℂ)).re := by rw [re_sub_ofReal]; linarith [neg_abs_le a]
  have hre2 : 1 < (s + (a : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith [neg_abs_le a]
  have hz1 : riemannZeta (s - a) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1.le
  have hz2 : riemannZeta (s + a) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre2.le
  have hn1 : s - a ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hre1; exact lt_irrefl _ hre1
  have hn2 : s + a ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hre2; exact lt_irrefl _ hre2
  rw [(hasDerivAt_shiftedZetaPair hn1 hn2).deriv]
  have hcoef : (fun n : ℕ => (shiftedPairVonMangoldt a n : ℂ)) =
      (fun n : ℕ => ((n : ℕ) : ℂ) ^ (a : ℂ) *
        (fun m : ℕ => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) n) +
      (fun n : ℕ => ((n : ℕ) : ℂ) ^ ((-a : ℝ) : ℂ) *
        (fun m : ℕ => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) n) := by
    funext n
    simp only [shiftedPairVonMangoldt, Pi.add_apply]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    ring
  rw [hcoef, LSeries_add ((lSeriesSummable_natCast_cpow_mul_iff _ _ _).2
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hre1))
    ((lSeriesSummable_natCast_cpow_mul_iff _ _ _).2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre2')),
    lSeries_natCast_cpow_mul, lSeries_natCast_cpow_mul,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre1,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre2', Complex.ofReal_neg, sub_neg_eq_add]
  unfold shiftedZetaPair
  field_simp
  ring

/-! ## Off-line zeros -/

/-- **Off-line zeros.**  For `a ≠ 0` and every height `T`, `F_a` has a zero of real part `≠ ½`
above height `T`: the shift of a critical zero of `ζ` supplied by Hardy's theorem. -/
theorem exists_offLine_zero_shiftedZetaPair {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    ∃ s : ℂ, T < s.im ∧ s.re ≠ 1 / 2 ∧ shiftedZetaPair a s = 0 := by
  obtain ⟨t, hTt, hXi⟩ := exists_Xi_zero_gt T
  have hxi : xi (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
    rw [xiHalfLine_real, hXi]; simp
  have hζ : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.1 hxi).1
  have hre : (1 / 2 + (t : ℂ) * Complex.I + a).re = 1 / 2 + a := by simp
  refine ⟨1 / 2 + (t : ℂ) * Complex.I + a, by simpa using hTt, ?_, ?_⟩
  · rw [hre]; intro h; apply ha; linarith
  · unfold shiftedZetaPair
    rw [show (1 / 2 + (t : ℂ) * Complex.I + a) - a = 1 / 2 + (t : ℂ) * Complex.I by ring, hζ,
      zero_mul]

/-- The mirror zero `½ − a + iγ`. -/
theorem exists_offLine_zero_shiftedZetaPair' {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    ∃ s : ℂ, T < s.im ∧ s.re ≠ 1 / 2 ∧ shiftedZetaPair a s = 0 ∧ s.re = 1 / 2 - a := by
  obtain ⟨t, hTt, hXi⟩ := exists_Xi_zero_gt T
  have hxi : xi (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
    rw [xiHalfLine_real, hXi]; simp
  have hζ : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.1 hxi).1
  have hre : (1 / 2 + (t : ℂ) * Complex.I - a).re = 1 / 2 - a := by simp
  refine ⟨1 / 2 + (t : ℂ) * Complex.I - a, by simpa using hTt, ?_, ?_, ?_⟩
  · rw [hre]; intro h; apply ha; linarith
  · unfold shiftedZetaPair
    rw [show (1 / 2 + (t : ℂ) * Complex.I - a) + a = 1 / 2 + (t : ℂ) * Complex.I by ring, hζ,
      mul_zero]
  · exact hre

/-! ## Polynomial growth -/

/-- **Polynomial growth on a strip.**  For `|a| ≤ ¼`, `‖F_a(σ + it)‖ ≤ C t²` on
`−¼ ≤ σ ≤ 5/4`, `t ≥ 8`. -/
theorem exists_norm_shiftedZetaPair_le {a : ℝ} (ha : |a| ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 / 4 ≤ σ → σ ≤ 5 / 4 → 8 ≤ t →
      ‖shiftedZetaPair a ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_riemannZeta_le_convexity (η := 1 / 2) (by norm_num) le_rfl
  refine ⟨C * C, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have habs := abs_le.1 ha
  have e1 : (σ : ℂ) + (t : ℂ) * I - a = ((σ - a : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  have e2 : (σ : ℂ) + (t : ℂ) * I + a = ((σ + a : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  unfold shiftedZetaPair
  rw [e1, e2, norm_mul]
  have b1 := hbound (σ - a) t (by linarith) (by linarith) ht
  have b2 := hbound (σ + a) t (by linarith) (by linarith) ht
  have p1 : t ^ ((1 + 1 / 2 - (σ - a)) / 2) ≤ t ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have p2 : t ^ ((1 + 1 / 2 - (σ + a)) / 2) ≤ t ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hpow : t ^ (2 : ℝ) = t ^ (1 : ℝ) * t ^ (1 : ℝ) := by
    rw [← Real.rpow_add ht0]; norm_num
  calc ‖riemannZeta (((σ - a : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖riemannZeta (((σ + a : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (C * t ^ (1 : ℝ)) * (C * t ^ (1 : ℝ)) :=
        mul_le_mul (b1.trans (mul_le_mul_of_nonneg_left p1 hC.le))
          (b2.trans (mul_le_mul_of_nonneg_left p2 hC.le)) (norm_nonneg _) (by positivity)
    _ = C * C * t ^ (2 : ℝ) := by rw [hpow]; ring

end RHTower
