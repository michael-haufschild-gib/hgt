import GaloisForLFunctions.ArithmeticEffectivityTheory.TheStepanovMethodOverZ

/-!
# The integrality lattice of the horizon

The **Nair functional** sends an integer polynomial `P` to `∫₀¹ P`. For `deg P ≤ n` integrality
gives `lcm(1, …, n + 1) · ∫₀¹ P ∈ ℤ` (`ArithmeticEffectivityTheory`). This module proves the
converse: integrality is **exact**.

* **Bézout over a finite family** (`exists_int_sum_div_eq_inv_lcm`). For positive integers
  `b_i`, some integer combination of the `1/b_i` equals `1/lcm(b_i)`; every integer combination
  lies in `lcm(b_i)⁻¹ ℤ` (`exists_int_sum_div_eq_div_lcm`). The two-element step is
  `u/a + v/b = 1/lcm(a, b)` from Bézout for the coprime cofactors.
* **The integrality lattice** (`nairLattice_eq`):
  `{∫₀¹ P : P ∈ ℤ[X], deg P ≤ n} = lcm(1, …, n + 1)⁻¹ ℤ`.
* **The floor is attained** (`isLeast_positive_nairIntegral`): the least positive Nair integral in
  degree `≤ n` is exactly `1/lcm(1, …, n + 1)`, and
  `ψ(n + 1) = max_P log(1/∫₀¹ P)` over integer `P` of degree `≤ n` with positive integral
  (`isGreatest_log_inv_nairIntegral`).

So the Stepanov–Nair method over `ℤ` loses nothing at the integrality step: the log-torsion of the
horizon is exactly the best bound that the integrality floor can give. Whatever precision the
method lacks is lost in the analytic ceiling used to certify a small positive integral.
-/

noncomputable section

open Real Finset Polynomial intervalIntegral

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-! ### Bézout over a finite family -/

/-- **Two-element Bézout for reciprocals**: `u/a + v/b = 1/lcm(a, b)` for some integers `u, v`. -/
theorem exists_int_div_add_div_eq_inv_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ u v : ℤ, (u : ℝ) / a + v / b = 1 / (Nat.lcm a b : ℕ) := by
  set g := Nat.gcd a b with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha
  set a' := a / g
  set b' := b / g
  have hcop : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hg0
  have ha' : (a : ℝ) = g * a' := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)]
  have hb' : (b : ℝ) = g * b' := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
  have hl : ((Nat.lcm a b : ℕ) : ℝ) = g * a' * b' := by
    have h := Nat.gcd_mul_lcm a b
    have h' : (g : ℝ) * (Nat.lcm a b : ℕ) = a * b := by exact_mod_cast h
    rw [ha', hb'] at h'
    have : (0 : ℝ) < g := by exact_mod_cast hg0
    field_simp at h' ⊢
    nlinarith [h']
  have hbez := Nat.gcd_eq_gcd_ab a' b'
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨Nat.gcdB a' b', Nat.gcdA a' b', ?_⟩
  have ha0 : (0 : ℝ) < a' := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    rw [ha'] at this; exact pos_of_mul_pos_right this (by positivity)
  have hb0 : (0 : ℝ) < b' := by
    have : (0 : ℝ) < b := by exact_mod_cast hb
    rw [hb'] at this; exact pos_of_mul_pos_right this (by positivity)
  have hg0' : (0 : ℝ) < g := by exact_mod_cast hg0
  have hbez' : (1 : ℝ) = a' * (Nat.gcdA a' b' : ℝ) + b' * (Nat.gcdB a' b' : ℝ) := by
    exact_mod_cast hbez
  rw [ha', hb', hl]
  field_simp
  linarith

/-- The least common multiple of a finite family of positive integers is positive. -/
theorem lcm_pos {ι : Type*} (s : Finset ι) {f : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) :
    0 < s.lcm f := Nat.pos_of_ne_zero fun h => by
  obtain ⟨i, hi, h0⟩ := Finset.lcm_eq_zero_iff.mp h
  exact (hf i hi).ne' h0

/-- **Bézout over a finite family**: some integer combination of the `1/f i` is `1/lcm f`. -/
theorem exists_int_sum_div_eq_inv_lcm {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) {f : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) :
    ∃ c : ι → ℤ, ∑ i ∈ s, (c i : ℝ) / f i = 1 / (s.lcm f : ℕ) := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert b t hb ih =>
    rcases t.eq_empty_or_nonempty with ht | ht
    · subst ht
      refine ⟨fun _ => 1, ?_⟩
      simp [Finset.lcm_singleton]
    obtain ⟨c, hc⟩ := ih ht fun i hi => hf i (mem_insert_of_mem hi)
    obtain ⟨u, v, huv⟩ := exists_int_div_add_div_eq_inv_lcm (hf b (mem_insert_self b t))
      (lcm_pos t fun i hi => hf i (mem_insert_of_mem hi))
    refine ⟨fun i => if i = b then u else v * c i, ?_⟩
    have ht' : ∑ x ∈ t, ((if x = b then u else v * c x : ℤ) : ℝ) / f x =
        v / (t.lcm f : ℕ) := by
      rw [div_eq_mul_one_div (v : ℝ), ← hc, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [if_neg (ne_of_mem_of_not_mem hi hb), Int.cast_mul, mul_div_assoc]
    rw [sum_insert hb, Finset.lcm_insert, lcm_eq_nat_lcm]
    beta_reduce
    rw [if_pos rfl, ht']
    exact huv

/-- Every integer combination of the `1/f i` lies in `(lcm f)⁻¹ ℤ`. -/
theorem exists_int_sum_div_eq_div_lcm {ι : Type*} (s : Finset ι) {f : ι → ℕ}
    (hf : ∀ i ∈ s, 0 < f i) (c : ι → ℤ) :
    ∃ z : ℤ, ∑ i ∈ s, (c i : ℝ) / f i = z / (s.lcm f : ℕ) := by
  refine ⟨∑ i ∈ s, c i * ((s.lcm f / f i : ℕ) : ℤ), ?_⟩
  have hL : (0 : ℝ) < (s.lcm f : ℕ) := by exact_mod_cast lcm_pos s hf
  rw [Int.cast_sum, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hdvd : f i ∣ s.lcm f := Finset.dvd_lcm hi
  have hfi : (0 : ℝ) < f i := by exact_mod_cast hf i hi
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hfi.ne']
  field_simp

/-! ### The Nair functional -/

/-- The **Nair functional** `P ↦ ∫₀¹ P` on integer polynomials. -/
def nairIntegral (P : ℤ[X]) : ℝ := ∫ x in (0 : ℝ)..1, aeval x P

/-- The auxiliary polynomial `Σ_{1 ≤ k ≤ n+1} c_k X^{k−1}`. -/
def horizonPoly (n : ℕ) (c : ℕ → ℤ) : ℤ[X] := ∑ k ∈ Icc 1 (n + 1), C (c k) * X ^ (k - 1)

theorem horizonPoly_natDegree_le (n : ℕ) (c : ℕ → ℤ) : (horizonPoly n c).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := (mem_Icc.mp hk).2; omega)

/-- `∫₀¹ Σ c_k x^{k−1} = Σ c_k / k`. -/
theorem nairIntegral_horizonPoly (n : ℕ) (c : ℕ → ℤ) :
    nairIntegral (horizonPoly n c) = ∑ k ∈ Icc 1 (n + 1), (c k : ℝ) / (k : ℕ) := by
  unfold nairIntegral horizonPoly
  simp only [map_sum, map_mul, map_intCast, map_pow, aeval_X, eq_intCast]
  rw [integral_finsetSum (f := fun k x => (c k : ℝ) * x ^ (k - 1))
    fun k _ => ((continuous_const.mul (continuous_pow _))).intervalIntegrable _ _]
  refine sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  rw [integral_const_mul, integral_pow, one_pow, zero_pow (by omega), sub_zero,
    show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by rw [Nat.cast_sub hk1]; ring]
  ring

/-- **Some auxiliary polynomial of degree `≤ n` has `∫₀¹ P = 1/lcm(1, …, n + 1)`.** -/
theorem exists_nairIntegral_eq_inv_lcmUpto (n : ℕ) :
    ∃ P : ℤ[X], P.natDegree ≤ n ∧ nairIntegral P = 1 / (Nat.lcmUpto (n + 1) : ℕ) := by
  obtain ⟨c, hc⟩ := exists_int_sum_div_eq_inv_lcm (Icc 1 (n + 1)) ⟨1, by simp⟩
    (f := id) fun i hi => (mem_Icc.mp hi).1
  refine ⟨horizonPoly n c, horizonPoly_natDegree_le n c, ?_⟩
  rw [nairIntegral_horizonPoly]
  simpa [Nat.lcmUpto] using hc

/-- **The integrality lattice of the horizon**:
`{∫₀¹ P : P ∈ ℤ[X], deg P ≤ n} = lcm(1, …, n + 1)⁻¹ ℤ`. -/
theorem nairLattice_eq (n : ℕ) :
    {r : ℝ | ∃ P : ℤ[X], P.natDegree ≤ n ∧ nairIntegral P = r} =
      Set.range fun z : ℤ => (z : ℝ) / (Nat.lcmUpto (n + 1) : ℕ) := by
  have hd : (0 : ℝ) < (Nat.lcmUpto (n + 1) : ℕ) := by exact_mod_cast Nat.lcmUpto_pos _
  ext r
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨z, hz⟩ := ArithmeticEffectivityTheory.exists_int_eq_lcmUpto_mul_integral P hP
    refine ⟨z, ?_⟩
    show (z : ℝ) / _ = nairIntegral P
    rw [← hz, nairIntegral]; field_simp
  · rintro ⟨z, rfl⟩
    obtain ⟨P, hP, hP1⟩ := exists_nairIntegral_eq_inv_lcmUpto n
    refine ⟨C z * P, (natDegree_C_mul_le z P).trans hP, ?_⟩
    have : nairIntegral (C z * P) = z * nairIntegral P := by
      unfold nairIntegral
      simp only [map_mul, map_intCast, eq_intCast]
      exact integral_const_mul _ _
    rw [this, hP1]; ring

/-- **The floor is attained**: the least positive Nair integral in degree `≤ n` is
`1/lcm(1, …, n + 1)`. -/
theorem isLeast_positive_nairIntegral (n : ℕ) :
    IsLeast {r : ℝ | ∃ P : ℤ[X], P.natDegree ≤ n ∧ nairIntegral P = r ∧ 0 < r}
      (1 / (Nat.lcmUpto (n + 1) : ℕ)) := by
  have hd : (0 : ℝ) < (Nat.lcmUpto (n + 1) : ℕ) := by exact_mod_cast Nat.lcmUpto_pos _
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hP1⟩ := exists_nairIntegral_eq_inv_lcmUpto n
    exact ⟨P, hP, hP1, by positivity⟩
  · rintro r ⟨P, hP, rfl, hpos⟩
    have h1 := ArithmeticEffectivityTheory.one_le_lcmUpto_mul_integral P hP hpos
    rw [div_le_iff₀ hd]
    unfold nairIntegral
    linarith

/-- **The log-torsion is the best integrality bound**: `ψ(n + 1)` is the maximum of
`log (1 / ∫₀¹ P)` over integer `P` of degree `≤ n` with positive integral. -/
theorem isGreatest_log_inv_nairIntegral (n : ℕ) :
    IsGreatest {t : ℝ | ∃ P : ℤ[X], P.natDegree ≤ n ∧ 0 < nairIntegral P ∧
      t = Real.log (1 / nairIntegral P)} (Chebyshev.psi (n + 1 : ℕ)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hP1⟩ := exists_nairIntegral_eq_inv_lcmUpto n
    refine ⟨P, hP, by rw [hP1]; exact one_div_pos.mpr (by exact_mod_cast Nat.lcmUpto_pos _), ?_⟩
    rw [hP1, one_div_one_div, Chebyshev.psi_eq_log_lcmUpto]
  · rintro t ⟨P, hP, hpos, rfl⟩
    exact ArithmeticEffectivityTheory.log_inv_integral_le_psi P hP hpos

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
