import GaloisForLFunctions.RHTower.PrimeDeletionSquareRootFloor

/-!
# The half-dimension floor is set by the atomic mass of the perturbation

Let an integer-supported Beurling system have masses `a` (`|a n| ≤ 1`, `a 1 = 1`) and generator
von Mangoldt function `Λ - e`, with every nonzero `e n` of size at least `log 2`.  Suppose the
perturbation's Chebyshev function `Σ_{n ≤ x} e n` has an expansion `Σ_{ρ ∈ J} c_ρ x^ρ + O(x^η)` over
finitely many exponents, and its **absolute** mass `Σ_{n ≤ N} |e n|` is at least `c₁ N^κ` for
infinitely many `N`.  If `Σ_{n ≤ x} a n = A x + O(x^θ)`, then `max(θ, η) ≥ κ/2`
(`IntegerBeurling.not_isBigO_count_of_frequently_abs_mass`).

No leading term and no sign condition enters: the floor is set by the `ℓ¹` mass of the integer
atoms, not by the size of their signed sum.  In particular sign cancellation cannot hide mass.  If
the signed Chebyshev function is `O(x^η)` with no main terms at all (`J = ∅`), a system whose count
error is `O(x^θ)` has perturbation mass of dimension at most `2 max(θ, η)`
(`IntegerBeurling.not_isBigO_count_of_frequently_abs_mass_of_isBigO`).

The proof is the one of `IntegerBeurling.not_isBigO_count_of_leading_chebyshev`, with the head mass
bounded from below through `Σ_{n ≤ N} e(n)² n^{-2σ} ≥ log 2 · N^{-2σ} Σ_{n ≤ N} |e n|`
(`head_mass_ge_log_two_mul_abs_mass`).
-/

open Filter Topology Complex Asymptotics

namespace RHTower

noncomputable section

namespace IntegerBeurling

variable {a e : ℕ → ℝ}

/-- `Σ_{n ≤ N} e(n)² n^{-2σ} ≥ log 2 · N^{-2σ} Σ_{n ≤ N} |e n|` for integer-size atoms. -/
theorem head_mass_ge_log_two_mul_abs_mass (hint : ∀ n, e n = 0 ∨ Real.log 2 ≤ |e n|) {σ : ℝ}
    (hσ : 0 ≤ σ) {N : ℕ} (hN1 : 1 ≤ N) :
    Real.log 2 * (N : ℝ) ^ (-2 * σ) * ∑ n ∈ Finset.Icc 1 N, |e n| ≤
      ∑ n ∈ Finset.Icc 1 N, (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hpow : (N : ℝ) ^ (-2 * σ) ≤ (n : ℝ) ^ (-2 * σ) :=
    Real.rpow_le_rpow_of_nonpos hn0 hnN (by linarith)
  have hsq : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  rw [mul_pow, hsq, ← sq_abs (e n)]
  rcases hint n with h0 | h2
  · rw [h0]; simp
  · have : Real.log 2 * |e n| ≤ |e n| ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    calc Real.log 2 * (N : ℝ) ^ (-2 * σ) * |e n|
        = (N : ℝ) ^ (-2 * σ) * (Real.log 2 * |e n|) := by ring
      _ ≤ (n : ℝ) ^ (-2 * σ) * |e n| ^ 2 :=
          mul_le_mul hpow this (by positivity) (Real.rpow_nonneg hn0.le _)
      _ = |e n| ^ 2 * (n : ℝ) ^ (-2 * σ) := by ring

/-- **The atomic-mass floor.**  Let a Beurling system of positive integers have masses `a`
(`|a n| ≤ 1`, `a 1 = 1`) and generator von Mangoldt function `Λ - e` (`(Λ - e) ⋆ a = a · log`,
`|e n| ≤ log n`), every nonzero `e n` of size at least `log 2`.  If
`Σ_{n ≤ x} e n = Σ_{ρ∈J} c_ρ x^ρ + O(x^η)` over finitely many exponents with `Re ρ < 2`, and
`Σ_{n ≤ N} |e n| ≥ c₁ N^κ` for infinitely many `N`, then `Σ_{n ≤ x} a n - A x ≠ O(x^θ)` whenever
`θ, η < κ/2`. -/
theorem not_isBigO_count_of_frequently_abs_mass (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((ArithmeticFunction.vonMangoldt n - e n : ℝ) : ℂ))
      (countSeq a) = LSeries.logMul (countSeq a))
    (hint : ∀ n, e n = 0 ∨ Real.log 2 ≤ |e n|) {A θ η κ c₁ : ℝ} {J : Finset ℂ} {c : ℂ → ℂ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ1 : κ ≤ 1)
    (hJ2 : ∀ ρ ∈ J, ρ.re < 2)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    (hc₁ : 0 < c₁) (hmass : ∃ᶠ N : ℕ in atTop, c₁ * (N : ℝ) ^ κ ≤ ∑ n ∈ Finset.Icc 1 N, |e n|) :
    ¬(fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ := by
  classical
  intro hN
  set B : ℝ := ∑ ρ ∈ J, |ρ.im| with hB
  have hJ' : ∀ ρ ∈ J, ρ.re < 2 ∧ |ρ.im| ≤ B := fun ρ hρ =>
    ⟨hJ2 ρ hρ, Finset.single_le_sum (f := fun ρ : ℂ => |ρ.im|) (fun _ _ => abs_nonneg _) hρ⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = (max θ η + κ / 2) / 2 := ⟨_, rfl⟩
  have hmax : max θ η < κ / 2 := max_lt hθκ hηκ
  have hσθ : θ < σ := by rw [hσdef]; linarith [le_max_left θ η]
  have hση : η < σ := by rw [hσdef]; linarith [le_max_right θ η]
  have hσκ : σ < κ / 2 := by rw [hσdef]; linarith
  have hσ0 : 0 < σ := by linarith
  obtain ⟨C, t₀, hC⟩ := exists_norm_pertLogDeriv_le_log ha ha1 he hconv hθ hN hψ hJ' hσθ hση
    (by linarith)
  obtain ⟨CR, hCR0, hCR⟩ := exists_forall_norm_remainder_le e he hη hψ
  set M : ℝ := Real.log 2 * c₁ with hM
  have hM0 : 0 < M := mul_pos (Real.log_pos (by norm_num)) hc₁
  have hδ0 : 0 < κ - 2 * σ := by linarith
  -- the head mass along the frequent cutoffs
  have hmassN : ∃ᶠ N : ℕ in atTop, M * (N : ℝ) ^ (κ - 2 * σ) ≤
      ∑ n ∈ Finset.Icc 1 N, (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
    refine (hmass.and_eventually (eventually_ge_atTop 1)).mono fun N ⟨hN', hN1⟩ => ?_
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    refine le_trans ?_ (head_mass_ge_log_two_mul_abs_mass hint hσ0.le hN1)
    calc M * (N : ℝ) ^ (κ - 2 * σ) = Real.log 2 * (N : ℝ) ^ (-2 * σ) * (c₁ * (N : ℝ) ^ κ) := by
          rw [hM, show κ - 2 * σ = -2 * σ + κ by ring, Real.rpow_add hN0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN'
          (mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg hN0.le _))
  have hmassu : ∃ᶠ u : ℝ in atTop, M * (⌊u⌋₊ : ℝ) ^ (κ - 2 * σ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (e n * (n : ℝ) ^ (-σ)) ^ 2 := by
    refine tendsto_natCast_atTop_atTop.frequently (hmassN.mono fun N hN' => ?_)
    rw [Nat.floor_natCast]; exact hN'
  have herr : ∀ᶠ u : ℝ in atTop, (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
      4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ))) *
        (u ^ 7 * Real.exp (-(u ^ 2 / 32))) ≤ Real.sqrt Real.pi / 2 := by
    have h := (tendsto_pow_mul_exp_neg_sq_div (k := 7) (c := 32) (by norm_num)).const_mul
      (30 * Real.exp 9 * (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)) +
        4 * Real.exp 9 * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) + 8 * (∑' m : ℕ, (m : ℝ) ^ (-1 - σ)))
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by positivity))
  have hdiag : ∀ᶠ u : ℝ in atTop, u ^ 4 * Real.exp (-(u ^ 2 / 4)) ≤ 1 :=
    (tendsto_pow_mul_exp_neg_sq_div (k := 4) (c := 4) (by norm_num)).eventually
      (ge_mem_nhds (by norm_num))
  have hlog := eventually_sq_log_add_lt (K := max C 0) hM0 hδ0
  have hu4 : Tendsto (fun u : ℝ => u ^ 4 / 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  obtain ⟨u, hum, hue, hud, hul, hut, huB, hu3⟩ :=
    (hmassu.and_eventually (herr.and (hdiag.and (hlog.and ((hu4.eventually_ge_atTop t₀).and
      ((hu4.eventually_ge_atTop (B + 1)).and (eventually_ge_atTop (3 : ℝ)))))))).exists
  have hcap := head_mass_le_of_log_bound he hψ hCR hCR0 hJ' hση hσ0 (by linarith) hC hu3 hut huB
    hue hud
  linarith

/-- **Sign cancellation cannot hide atomic mass.**  If the perturbation's signed Chebyshev function
is `O(x^η)` and the count error is `O(x^θ)`, then the absolute mass `Σ_{n ≤ N} |e n|` is not
`≥ c₁ N^κ` infinitely often for any `κ > 2 max(θ, η)`, `κ ≤ 1`. -/
theorem not_isBigO_count_of_frequently_abs_mass_of_isBigO (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((ArithmeticFunction.vonMangoldt n - e n : ℝ) : ℂ))
      (countSeq a) = LSeries.logMul (countSeq a))
    (hint : ∀ n, e n = 0 ∨ Real.log 2 ≤ |e n|) {A θ η κ c₁ : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθκ : θ < κ / 2) (hηκ : η < κ / 2) (hκ1 : κ ≤ 1)
    (hψ : (fun x : ℝ => pertChebyshev e x) =O[atTop] fun x : ℝ => x ^ η)
    (hc₁ : 0 < c₁) (hmass : ∃ᶠ N : ℕ in atTop, c₁ * (N : ℝ) ^ κ ≤ ∑ n ∈ Finset.Icc 1 N, |e n|) :
    ¬(fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ := by
  refine not_isBigO_count_of_frequently_abs_mass ha ha1 he hconv hint (J := ∅) (c := fun _ => 0)
    hθ hη hθκ hηκ hκ1 (fun ρ hρ => absurd hρ (Finset.notMem_empty ρ)) ?_ hc₁ hmass
  simp only [Finset.sum_empty, sub_zero]
  exact Complex.isBigO_ofReal_left.mpr hψ

end IntegerBeurling

end

end RHTower
