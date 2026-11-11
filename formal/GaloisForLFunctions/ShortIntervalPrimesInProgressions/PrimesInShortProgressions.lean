import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterWindows

/-!
# Primes in short intervals in every reduced residue class

For every modulus `q ≥ 1` and every unit `a` modulo `q`, with `θ = 1 − u₁/16 < 1`
(`u₁ = 1/(14·10⁷ + 12)`):

* `Σ_{x < n ≤ x + x^θ, n ≡ a (q)} Λ(n) ∼ x^θ/φ(q)`   (`tendsto_residueClass_window`);
* every interval `(x, x + x^θ]` with `x` large contains a prime `p ≡ a (mod q)`
  (`eventually_exists_prime_short_interval_mod`).

The residue class is the character average `φ(q)⁻¹ Σ_χ χ̄(a) ψ(·, χ)`
(`ArithmeticFunction.vonMangoldt.residueClass_apply`).  The principal window is `∼ x^θ`
(`tendsto_window_principal`) and every other window is `o(x^θ)` (`tendsto_window_character`).
Prime powers `p^k`, `k ≥ 2`, contribute at most `ψ(y) − θ(y) ≤ 2√y log y = o(x^θ)`.
-/

open Complex Filter Topology Finset ArithmeticFunction

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The window of the residue class as a character average. -/
theorem residueClass_window_eq {a : ZMod q} (ha : IsUnit a) {x y : ℝ} (hxy : x ≤ y) :
    ((∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, vonMangoldt.residueClass a n : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ y - psiChi χ x) := by
  push_cast
  rw [Finset.sum_congr rfl fun n _ => vonMangoldt.residueClass_apply ha n, ← Finset.mul_sum,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [psiChi_sub_eq_sum χ hxy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold twistedVM
  ring

/-- **The prime number theorem in short intervals of an arithmetic progression.**
`Σ_{x < n ≤ x + x^θ, n ≡ a} Λ(n) / x^θ → 1/φ(q)`. -/
theorem tendsto_residueClass_window {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ => (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + x ^ windowExponent⌋₊,
        vonMangoldt.residueClass a n) / x ^ windowExponent) atTop (𝓝 (1 / q.totient)) := by
  classical
  set θ := windowExponent with hθ
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero
    (NeZero.ne q))
  -- the complex character average
  set F : ℝ → ℂ := fun x => (q.totient : ℂ)⁻¹ *
    ((psiChi (1 : DirichletCharacter ℂ q) (x + x ^ θ) - psiChi (1 : DirichletCharacter ℂ q) x) /
        ((x ^ θ : ℝ) : ℂ) +
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ a⁻¹ * ((psiChi χ (x + x ^ θ) - psiChi χ x) / ((x ^ θ : ℝ) : ℂ))) with hF
  have hFlim : Tendsto F atTop (𝓝 ((q.totient : ℂ)⁻¹ * (1 + 0))) := by
    refine Tendsto.const_mul _ (tendsto_window_principal.add ?_)
    rw [show (0 : ℂ) = ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, (0 : ℂ)
      by simp]
    refine tendsto_finsetSum _ fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_window_character hχ1) (Eventually.of_forall fun x => norm_nonneg _) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hh0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx _
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
    calc ‖χ a⁻¹‖ * (‖psiChi χ (x + x ^ θ) - psiChi χ x‖ / x ^ θ)
        ≤ 1 * (‖psiChi χ (x + x ^ θ) - psiChi χ x‖ / x ^ θ) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
      _ = _ := one_mul _
  rw [add_zero, mul_one] at hFlim
  -- the real window is the real part of `F`
  have hre : Tendsto (fun x => (F x).re) atTop (𝓝 (((q.totient : ℂ)⁻¹).re)) :=
    (Complex.continuous_re.tendsto _).comp hFlim
  have hlim : ((q.totient : ℂ)⁻¹).re = 1 / q.totient := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hlim] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hh0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx _
  have hxy : x ≤ x + x ^ θ := by linarith
  have hunit : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 :=
    MulChar.one_apply (isUnit_of_mul_eq_one _ _ (ZMod.inv_mul_of_unit a ha))
  have hsum := residueClass_window_eq ha hxy
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), hunit, one_mul] at hsum
  have hhC : ((x ^ θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0.ne'
  have hF' : F x = ((∑ n ∈ Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊, vonMangoldt.residueClass a n : ℝ) : ℂ) /
      ((x ^ θ : ℝ) : ℂ) := by
    rw [hsum, hF]
    simp only
    rw [Finset.sum_div, mul_div_assoc, add_div]
    congr 2
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hF', ← Complex.ofReal_div, Complex.ofReal_re]

/-- The integers of a window which are not primes carry von Mangoldt mass at most `ψ(y) − θ(y)`. -/
theorem sum_window_not_prime_le {x y : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => ¬ n.Prime), vonMangoldt n ≤
      Chebyshev.psi y - Chebyshev.theta y := by
  classical
  have hpsi : Chebyshev.psi y - Chebyshev.theta y =
      ∑ n ∈ (Ioc 0 ⌊y⌋₊).filter (fun n => ¬ n.Prime), vonMangoldt n := by
    unfold Chebyshev.psi Chebyshev.theta
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 ⌊y⌋₊) (fun n => n.Prime)]
    rw [Finset.sum_congr rfl fun n hn => vonMangoldt_apply_prime (mem_filter.mp hn).2]
    ring
  rw [hpsi]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => vonMangoldt_nonneg
  intro n hn
  simp only [mem_filter, mem_Ioc] at hn ⊢
  exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩

/-- **Primes in short intervals in every reduced residue class.**  For every modulus `q ≥ 1` and
every unit `a` modulo `q`, every interval `(x, x + x^θ]`, `θ = 1 − 1/(16(14·10⁷ + 12)) < 1`, with
`x` large enough contains a prime `p ≡ a (mod q)`. -/
theorem eventually_exists_prime_short_interval_mod {a : ZMod q} (ha : IsUnit a) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ x < p ∧
      (p : ℝ) ≤ x + x ^ windowExponent := by
  classical
  set θ := windowExponent with hθ
  have hθ12 : 1 / 2 < θ := by linarith [seven_twelfths_lt_windowExponent]
  have hθ1 : θ < 1 := windowExponent_lt_one
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero
    (NeZero.ne q))
  have hlim := tendsto_residueClass_window ha
  have hlow : ∀ᶠ x : ℝ in atTop, 1 / (2 * q.totient) <
      (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊, vonMangoldt.residueClass a n) / x ^ θ :=
    hlim.eventually (lt_mem_nhds (by
      rw [one_div_lt_one_div (by positivity) hφ]; linarith))
  -- prime powers are `o(x^θ)`
  have hsmall : Tendsto (fun x : ℝ => Real.log x / x ^ (θ - 1 / 2)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by linarith)).tendsto_div_nhds_zero
  have hpp : ∀ᶠ x : ℝ in atTop, Real.log x / x ^ (θ - 1 / 2) < 1 / (16 * q.totient) :=
    hsmall.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hlow, hpp.comp_tendsto (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 2)),
    eventually_ge_atTop 2] with x hx hpx hx2
  simp only [Function.comp, id] at hpx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hhx : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hθ1.le
      _ = x := Real.rpow_one x
  by_contra hnone
  push Not at hnone
  set W := Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊ with hW
  -- without a prime the window is carried by prime powers
  have hprime0 : ∑ n ∈ W.filter (fun n => n.Prime), vonMangoldt.residueClass a n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    obtain ⟨hnW, hnp⟩ := mem_filter.mp hn
    rw [mem_Ioc] at hnW
    have hxn : x < n := Nat.lt_of_floor_lt hnW.1
    have hnx : (n : ℝ) ≤ x + x ^ θ := (Nat.cast_le.mpr hnW.2).trans (Nat.floor_le (by positivity))
    simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with hna
    · exact absurd hnx (not_le.mpr (hnone n hnp hna hxn))
    · rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not W (fun n => n.Prime)
    (fun n => vonMangoldt.residueClass a n)
  rw [hprime0, zero_add] at hsplit
  have hrest : ∑ n ∈ W.filter (fun n => ¬ n.Prime), vonMangoldt.residueClass a n ≤
      Chebyshev.psi (x + x ^ θ) - Chebyshev.theta (x + x ^ θ) :=
    (Finset.sum_le_sum fun n _ => vonMangoldt.residueClass_le a n).trans
      (sum_window_not_prime_le hx0.le)
  have hpt := Chebyshev.psi_sub_theta_le (x := x + x ^ θ) (by linarith)
  -- `2√(x + x^θ) log(x + x^θ) ≤ 4√2 √x log(2x)`, which is `o(x^θ)`
  have hy2 : x + x ^ θ ≤ 2 * x := by linarith
  have hsq : Real.sqrt (x + x ^ θ) ≤ 2 * x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc (x + x ^ θ) ^ (1 / 2 : ℝ) ≤ (4 * x) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = 2 * x ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hx0.le, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have hlog : Real.log (x + x ^ θ) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hy2
  have hlog0 : 0 ≤ Real.log (x + x ^ θ) := Real.log_nonneg (by linarith)
  have hsplitθ : x ^ θ = x ^ (1 / 2 : ℝ) * x ^ (θ - 1 / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hB : Real.log (2 * x) < x ^ (θ - 1 / 2) / (16 * q.totient) := by
    have h2x : (2 * x) ^ (θ - 1 / 2) ≤ 2 * x ^ (θ - 1 / 2) := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx0.le _)
      calc (2 : ℝ) ^ (θ - 1 / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hpos : 0 < (2 * x) ^ (θ - 1 / 2) := by positivity
    rw [div_lt_iff₀ hpos] at hpx
    have : 1 / (16 * (q.totient : ℝ)) * (2 * x) ^ (θ - 1 / 2) ≤
        1 / (16 * q.totient) * (2 * x ^ (θ - 1 / 2)) :=
      mul_le_mul_of_nonneg_left h2x (by positivity)
    have h16 : 1 / (16 * (q.totient : ℝ)) * (2 * x ^ (θ - 1 / 2)) =
        x ^ (θ - 1 / 2) / (16 * q.totient) * 2 := by ring
    nlinarith [Real.rpow_pos_of_pos hx0 (θ - 1 / 2)]
  rw [div_lt_iff₀ hh0, ← hsplit] at hx
  have hx12 : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hfinal : 2 * Real.sqrt (x + x ^ θ) * Real.log (x + x ^ θ) <
      1 / (2 * q.totient) * x ^ θ := by
    calc 2 * Real.sqrt (x + x ^ θ) * Real.log (x + x ^ θ)
        ≤ 2 * (2 * x ^ (1 / 2 : ℝ)) * Real.log (2 * x) := by
          gcongr
      _ < 2 * (2 * x ^ (1 / 2 : ℝ)) * (x ^ (θ - 1 / 2) / (16 * q.totient)) := by
          gcongr
      _ = 1 / (4 * q.totient) * (x ^ (1 / 2 : ℝ) * x ^ (θ - 1 / 2)) := by
          field_simp; ring
      _ ≤ 1 / (2 * q.totient) * x ^ θ := by
          rw [← hsplitθ]
          gcongr
          linarith
  linarith

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
