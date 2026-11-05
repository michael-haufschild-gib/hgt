import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker

/-!
# Euler columns collide or repel at polynomial scale

The discreteness that an Euler product carries is Diophantine, not integral. A finite Euler
carrier `E_S(s) = ∏_{p ∈ S} (1 − p^{−s})` has integer Dirichlet coefficients, and its zeros are the
**Euler columns** `2πik/log p` on `Re s = 0` (`eulerCarrier_eq_zero_iff`). Two columns of different
primes interleave, and their near-coincidences are governed by the linear form `k log p' − k' log p`.

* **Collide or repel at polynomial scale** (`eulerCarrier_collide_or_repel`). There are `c, C > 0`
  such that distinct zeros of `E_S` of height at most `T ≥ 1` are at distance `≥ c T^{−C}`. Within a
  column the spacing is `2π/log p`; across columns the distance is
  `2π |k log p' − k' log p| / (log p log p')`, bounded below by the effective Baker bound
  `RHTower.Matveev.effectiveBakerBound_holds`. The only collision is `s = 0`, where all columns meet.
* **No uniform repulsion** (`eulerColumns_near_coincidence`). For two primes and every `n ≥ 1` there
  are distinct zeros of height `≤ 2πn/log p` at distance `≤ 2π/((n+1) log p')` (Dirichlet's
  approximation theorem applied to `log p'/log p`).

So for Euler carriers the collide-or-repel law of the function-field model holds exactly at
polynomial scale, with a polynomial loss that cannot be removed; the producer of the separation is
the transcendence of the frequency module `⊕ ℤ log p`, while integrality of the coefficients plays
no role.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The point `2πik/log p` of the Euler column of `p`. -/
def colPt (p : ℕ) (k : ℤ) : ℂ := ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) * I

theorem colPt_im (p : ℕ) (k : ℤ) : (colPt p k).im = 2 * Real.pi * k / Real.log p := by
  rw [colPt, mul_I_im, ofReal_re]

theorem colPt_zero (p : ℕ) : colPt p 0 = 0 := by simp [colPt]

/-- The zeros of a single Euler factor form its column. -/
theorem one_sub_cpow_neg_eq_zero_iff {p : ℕ} (hp : 1 < p) (s : ℂ) :
    1 - (p : ℂ) ^ (-s) = 0 ↔ ∃ k : ℤ, s = colPt p k := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hl : Complex.log (p : ℂ) ≠ 0 := by rw [← Complex.natCast_log]; exact_mod_cast hlog.ne'
  rw [sub_eq_zero, eq_comm, cpow_def_of_ne_zero hp0, exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    unfold colPt
    push_cast
    field_simp
    linear_combination -hn
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    unfold colPt
    push_cast
    field_simp

/-- The finite Euler carrier `∏_i (1 − p_i^{−s})`. -/
def eulerCarrier {d : ℕ} (p : Fin d → ℕ) (s : ℂ) : ℂ := ∏ i, (1 - (p i : ℂ) ^ (-s))

theorem eulerCarrier_eq_zero_iff {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, 1 < p i) (s : ℂ) :
    eulerCarrier p s = 0 ↔ ∃ i, ∃ k : ℤ, s = colPt (p i) k := by
  unfold eulerCarrier
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  exact exists_congr fun i => one_sub_cpow_neg_eq_zero_iff (hp i) s

theorem norm_colPt_sub (p p' : ℕ) (k k' : ℤ) :
    ‖colPt p k - colPt p' k'‖ = |2 * Real.pi * k / Real.log p - 2 * Real.pi * k' / Real.log p'| := by
  unfold colPt
  rw [← sub_mul, ← ofReal_sub, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]

/-- Across two columns the distance is the linear form in the two logarithms. -/
theorem colPt_sub_eq (p p' : ℕ) (k k' : ℤ) (hp : Real.log p ≠ 0) (hp' : Real.log p' ≠ 0) :
    2 * Real.pi * k / Real.log p - 2 * Real.pi * k' / Real.log p' =
      2 * Real.pi * (k * Real.log p' - k' * Real.log p) / (Real.log p * Real.log p') := by
  field_simp

/-- **Euler columns collide or repel at polynomial scale.** For distinct primes `p₁, …, p_d` there
are `c, C > 0` such that distinct zeros `ρ ≠ ρ'` of `∏_i (1 − p_i^{−s})` with `|Im ρ|, |Im ρ'| ≤ T`,
`T ≥ 1`, satisfy `‖ρ − ρ'‖ ≥ c T^{−C}`. -/
theorem eulerCarrier_collide_or_repel {d : ℕ} (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ ρ' : ℂ,
      eulerCarrier p ρ = 0 → eulerCarrier p ρ' = 0 → |ρ.im| ≤ T → |ρ'.im| ≤ T → ρ ≠ ρ' →
        c * T ^ (-C) ≤ ‖ρ - ρ'‖ := by
  classical
  obtain ⟨c₀, C₀, hc₀, hC₀, hB⟩ := RHTower.Matveev.effectiveBakerBound_holds p hp hprime
  have hp1 : ∀ i, 1 < p i := fun i => (hprime i).one_lt
  set P : ℝ := (RHTower.Matveev.primeBound p : ℝ) with hP
  have hP2 : (2 : ℝ) ≤ P := by rw [hP]; exact_mod_cast RHTower.Matveev.two_le_primeBound p
  set L : ℝ := Real.log P with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlogp : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast hp1 i)
  have hlogL : ∀ i, Real.log (p i) ≤ L := fun i =>
    Real.log_le_log (by exact_mod_cast (hprime i).pos)
      (by rw [hP]; exact_mod_cast RHTower.Matveev.le_primeBound p i)
  set A : ℝ := 2 + L / Real.pi with hA
  have hA0 : 0 < A := by positivity
  set c : ℝ := min (2 * Real.pi / L) (2 * Real.pi * c₀ / (L ^ 2 * A ^ C₀)) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, C₀, hc0, hC₀, fun T hT ρ ρ' hρ hρ' hT1 hT2 hne => ?_⟩
  obtain ⟨i, k, rfl⟩ := (eulerCarrier_eq_zero_iff p hp1 ρ).mp hρ
  obtain ⟨j, k', rfl⟩ := (eulerCarrier_eq_zero_iff p hp1 ρ').mp hρ'
  have hT0 : 0 < T := by linarith
  have hTC : T ^ (-C₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have hTC0 : 0 < T ^ (-C₀) := Real.rpow_pos_of_pos hT0 _
  -- heights bound the integers `k, k'`
  have hk : |(k : ℝ)| ≤ T * L / (2 * Real.pi) := by
    rw [colPt_im, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos (hlogp i), div_le_iff₀ (hlogp i)] at hT1
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hlogL i, abs_nonneg (k : ℝ)]
  have hk' : |(k' : ℝ)| ≤ T * L / (2 * Real.pi) := by
    rw [colPt_im, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos (hlogp j), div_le_iff₀ (hlogp j)] at hT2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hlogL j, abs_nonneg (k' : ℝ)]
  rw [norm_colPt_sub]
  by_cases hij : i = j
  · -- one column: spacing `2π/log p`
    subst hij
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
      have : (1 : ℤ) ≤ |k - k'| := Int.one_le_abs (sub_ne_zero.mpr hkk)
      exact_mod_cast this
    have heq : 2 * Real.pi * k / Real.log (p i) - 2 * Real.pi * k' / Real.log (p i) =
        2 * Real.pi * (k - k') / Real.log (p i) := by ring
    rw [heq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos (hlogp i)]
    calc c * T ^ (-C₀) ≤ c * 1 := mul_le_mul_of_nonneg_left hTC hc0.le
      _ ≤ 2 * Real.pi / L := by rw [mul_one]; exact min_le_left _ _
      _ ≤ 2 * Real.pi * 1 / Real.log (p i) := by
          rw [mul_one]; exact div_le_div_of_nonneg_left (by positivity) (hlogp i) (hlogL i)
      _ ≤ 2 * Real.pi * |(k : ℝ) - k'| / Real.log (p i) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (hlogp i).le
  · -- two columns: the linear form `k log p_j − k' log p_i`
    set ν : Fin d → ℤ := fun l => (if l = j then k else 0) - (if l = i then k' else 0) with hν
    have hji : j ≠ i := Ne.symm hij
    have hform : RHTower.Matveev.primeLogForm p ν = k * Real.log (p j) - k' * Real.log (p i) := by
      unfold RHTower.Matveev.primeLogForm
      simp only [hν, Int.cast_sub, Int.cast_ite, Int.cast_zero, sub_mul, ite_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hν0 : ν ≠ 0 := by
      intro h0
      have hj : ν j = 0 := congrFun h0 j
      have hi : ν i = 0 := congrFun h0 i
      simp [hν, hji, hij] at hj hi
      have hk0 : k = 0 := hj
      have hk'0 : k' = 0 := hi
      exact hne (by rw [hk0, hk'0, colPt_zero, colPt_zero])
    have hH : (RHTower.Matveev.coeffHeight ν : ℝ) ≤ |(k : ℝ)| + |(k' : ℝ)| := by
      have hnat : RHTower.Matveev.coeffHeight ν ≤ k.natAbs + k'.natAbs := by
        unfold RHTower.Matveev.coeffHeight
        calc ∑ l, (ν l).natAbs ≤ ∑ l, ((if l = j then k else 0).natAbs +
              (if l = i then k' else 0).natAbs) :=
              Finset.sum_le_sum fun l _ => Int.natAbs_sub_le _ _
          _ = k.natAbs + k'.natAbs := by
              rw [Finset.sum_add_distrib]
              simp only [apply_ite Int.natAbs, Int.natAbs_zero, Finset.sum_ite_eq',
                Finset.mem_univ, if_true]
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this
      simpa [Nat.cast_natAbs, Int.cast_abs] using this
    have hbaker := hB ν hν0
    rw [hform] at hbaker
    -- `2 + H ≤ A T`
    have hHT : 2 + (RHTower.Matveev.coeffHeight ν : ℝ) ≤ A * T := by
      have h1 : |(k : ℝ)| + |(k' : ℝ)| ≤ T * L / Real.pi := by
        have := add_le_add hk hk'
        calc |(k : ℝ)| + |(k' : ℝ)| ≤ T * L / (2 * Real.pi) + T * L / (2 * Real.pi) := this
          _ = T * L / Real.pi := by field_simp; ring
      rw [hA, add_mul]
      have : T * L / Real.pi = L / Real.pi * T := by ring
      nlinarith [div_nonneg hL.le Real.pi_pos.le]
    have hH0 : 0 < 2 + (RHTower.Matveev.coeffHeight ν : ℝ) := by positivity
    have hpow : (A * T) ^ (-C₀) ≤ (2 + (RHTower.Matveev.coeffHeight ν : ℝ)) ^ (-C₀) :=
      Real.rpow_le_rpow_of_nonpos hH0 hHT (by linarith)
    rw [Real.mul_rpow hA0.le hT0.le, Real.rpow_neg hA0.le] at hpow
    have hAC : 0 < A ^ C₀ := Real.rpow_pos_of_pos hA0 _
    -- the distance is `2π |form| / (log p_i log p_j)`
    rw [colPt_sub_eq _ _ _ _ (hlogp i).ne' (hlogp j).ne', abs_div, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos (mul_pos (hlogp i) (hlogp j))]
    have hden : Real.log (p i) * Real.log (p j) ≤ L ^ 2 := by
      rw [sq]; exact mul_le_mul (hlogL i) (hlogL j) (hlogp j).le hL.le
    have hform0 : 0 ≤ |(k : ℝ) * Real.log (p j) - k' * Real.log (p i)| := abs_nonneg _
    calc c * T ^ (-C₀) ≤ 2 * Real.pi * c₀ / (L ^ 2 * A ^ C₀) * T ^ (-C₀) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hTC0.le
      _ = 2 * Real.pi / L ^ 2 * (c₀ * ((A ^ C₀)⁻¹ * T ^ (-C₀))) := by field_simp
      _ ≤ 2 * Real.pi / L ^ 2 * (c₀ * (2 + (RHTower.Matveev.coeffHeight ν : ℝ)) ^ (-C₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hc₀.le) (by positivity)
      _ ≤ 2 * Real.pi / L ^ 2 * |(k : ℝ) * Real.log (p j) - k' * Real.log (p i)| :=
          mul_le_mul_of_nonneg_left hbaker (by positivity)
      _ = 2 * Real.pi * |(k : ℝ) * Real.log (p j) - k' * Real.log (p i)| / L ^ 2 := by ring
      _ ≤ 2 * Real.pi * |(k : ℝ) * Real.log (p j) - k' * Real.log (p i)| /
            (Real.log (p i) * Real.log (p j)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos (hlogp i) (hlogp j)) hden

/-- **No uniform repulsion.** For distinct primes `p ≠ p'` and every `n ≥ 1` there are distinct
column points `ρ = 2πik/log p`, `ρ' = 2πij/log p'` with `|Im ρ| ≤ 2πn/log p` and
`‖ρ − ρ'‖ ≤ 2π/((n+1) log p')`. -/
theorem eulerColumns_near_coincidence {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p')
    {n : ℕ} (hn : 0 < n) :
    ∃ k j : ℤ, colPt p k ≠ colPt p' j ∧ |(colPt p k).im| ≤ 2 * Real.pi * n / Real.log p ∧
      ‖colPt p k - colPt p' j‖ ≤ 2 * Real.pi / ((n + 1) * Real.log p') := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlp' : 0 < Real.log p' := Real.log_pos (by exact_mod_cast hp'.one_lt)
  obtain ⟨j, k, hk0, hkn, hdir⟩ := Real.exists_int_int_abs_mul_sub_le (Real.log p' / Real.log p) hn
  refine ⟨k, j, ?_, ?_, ?_⟩
  · -- distinct: `k log p' ≠ j log p` by the Baker bound for the pair `(p', p)`
    intro heq
    have hinj : Function.Injective ![p', p] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
    have hpr : ∀ i, (![p', p] i).Prime := by intro i; fin_cases i <;> simpa
    obtain ⟨c₀, C₀, hc₀, -, hB⟩ := RHTower.Matveev.effectiveBakerBound_holds ![p', p] hinj hpr
    have hν : (![k, -j] : Fin 2 → ℤ) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this; omega
    have hb := hB _ hν
    have hform : RHTower.Matveev.primeLogForm ![p', p] ![k, -j] =
        k * Real.log p' - j * Real.log p := by
      simp [RHTower.Matveev.primeLogForm, Fin.sum_univ_two]; ring
    have hzero : (k : ℝ) * Real.log p' - j * Real.log p = 0 := by
      have h := congrArg Complex.im heq
      rw [colPt_im, colPt_im] at h
      field_simp at h
      linarith
    rw [hform, hzero, abs_zero] at hb
    exact absurd hb (not_le.mpr (by positivity))
  · rw [colPt_im, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hlp]
    have : |(k : ℝ)| ≤ n := by rw [abs_of_pos (by exact_mod_cast hk0)]; exact_mod_cast hkn
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) hlp.le
  · rw [norm_colPt_sub]
    have hid : 2 * Real.pi * k / Real.log p - 2 * Real.pi * j / Real.log p' =
        2 * Real.pi * (k * (Real.log p' / Real.log p) - j) / Real.log p' := by
      field_simp
    rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hlp', div_le_div_iff₀ hlp' (by positivity)]
    calc 2 * Real.pi * |(k : ℝ) * (Real.log p' / Real.log p) - j| * ((n + 1) * Real.log p') ≤
          2 * Real.pi * (1 / (n + 1)) * ((n + 1) * Real.log p') := by
          gcongr
      _ = 2 * Real.pi * Real.log p' := by field_simp

end GaloisForLFunctions.ArithmeticDiscreteness
