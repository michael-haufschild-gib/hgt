import GaloisForLFunctions.ArtinMertens.TheTwistedVonMangoldtSeriesConvergesAtOne
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The Mertens constants in progressions exist

For `q ≥ 1` and `a` a unit mod `q`,

  `Σ_{n ≤ x, n ≡ a (q)} Λ(n)/n = log x/φ(q) + C(q, a) + o(1)`
  (`tendsto_sum_residueClass_div_sub_log`),

  `C(q, a) = φ(q)⁻¹ (−γ − Σ_{(n, q) > 1} Λ(n)/n + Re Σ_{χ ≠ 1} χ(a⁻¹) (−L'(1, χ)/L(1, χ)))`.

The characters separate the residue classes (`ArithmeticFunction.vonMangoldt.residueClass_apply`):
the principal character contributes Mertens' theorem with the Euler constant, `Σ_{n ≤ x} Λ(n)/n −
log x → −γ`, minus the convergent sum over the prime powers of the primes dividing `q`
(`summable_principalDefect`); every nontrivial character contributes `−L'(1, χ)/L(1, χ)`
(`tendsto_sum_twist_vonMangoldt_div`, via Newman's analytic theorem and `L(1 + it, χ) ≠ 0`).

Over the primes alone (`tendsto_sum_prime_log_div_residueClass_sub_log`):
`Σ_{p ≤ x, p ≡ a} log p/p = log x/φ(q) + C(q, a) − Σ_{n ≡ a, n = p^k, k ≥ 2} Λ(n)/n + o(1)`, the higher
prime powers forming a convergent series (Mertens' prime-power tail is bounded).
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.ArtinMertens

open ArithmeticFunction (vonMangoldt)

open scoped Classical in
/-- The defect of the principal character, `Λ(n)/n` on the `n` that are not units mod `q`. -/
def principalDefect (q n : ℕ) : ℝ := if IsUnit (n : ZMod q) then 0 else vonMangoldt n / n

theorem principalDefect_nonneg (q n : ℕ) : 0 ≤ principalDefect q n := by
  unfold principalDefect
  split_ifs
  · exact le_rfl
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

open scoped Classical in
/-- The powers `p^{k+1}` of a prime carry the summable weight `log p/p^{k+1}`. -/
def primePowerWeight (p n : ℕ) : ℝ :=
  if n ∈ Set.range (fun k : ℕ => p ^ (k + 1)) then Real.log p / n else 0

theorem summable_primePowerWeight {p : ℕ} (hp : p.Prime) : Summable (primePowerWeight p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun k l h =>
    Nat.succ_injective (Nat.pow_right_injective hp.two_le h)
  rw [← hinj.summable_iff (fun n hn => by unfold primePowerWeight; rw [if_neg hn])]
  have hgeo : Summable fun k : ℕ => Real.log p / p * (1 / (p : ℝ)) ^ k :=
    (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; exact hp1)).mul_left _
  refine hgeo.congr fun k => ?_
  simp only [Function.comp_apply]
  unfold primePowerWeight
  rw [if_pos (Set.mem_range_self k)]
  push_cast
  rw [pow_succ, one_div_pow]
  field_simp

/-- **The principal defect is summable**: it lives on the powers of the primes dividing `q`. -/
theorem summable_principalDefect {q : ℕ} [NeZero q] : Summable (principalDefect q) := by
  refine Summable.of_nonneg_of_le (f := fun n => ∑ p ∈ q.primeFactors, primePowerWeight p n)
    (principalDefect_nonneg q) (fun n => ?_)
    (summable_sum (s := q.primeFactors) fun p hp =>
      summable_primePowerWeight (Nat.prime_of_mem_primeFactors hp))
  have hw0 : ∀ p n, 0 ≤ primePowerWeight p n := fun p n => by
    unfold primePowerWeight; split_ifs <;> [positivity; exact le_rfl]
  unfold principalDefect
  split_ifs with hu
  · exact Finset.sum_nonneg fun p _ => hw0 p n
  by_cases hΛ : vonMangoldt n = 0
  · rw [hΛ, zero_div]; exact Finset.sum_nonneg fun p _ => hw0 p n
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpq : p ∈ q.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, NeZero.ne q⟩
    by_contra hdvd
    exact hu ((ZMod.isUnit_iff_coprime _ q).mpr (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)))
  have hval : vonMangoldt (p ^ k) / ((p ^ k : ℕ) : ℝ) = primePowerWeight p (p ^ k) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
    unfold primePowerWeight
    rw [if_pos ⟨k - 1, by show p ^ (k - 1 + 1) = p ^ k; rw [Nat.sub_add_cancel hk]⟩]
  rw [hval]
  exact Finset.single_le_sum (fun p' _ => hw0 p' (p ^ k)) hpq

/-- The principal character: `Σ_{n ≤ x} χ₀(n)Λ(n)/n − log x → −γ − Σ_n d(n)`. -/
theorem tendsto_sum_principal_vonMangoldt_div_sub_log {q : ℕ} [NeZero q] :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / n) - (Real.log x : ℂ)) atTop
      (𝓝 (((-Real.eulerMascheroniConstant - ∑' n, principalDefect q n : ℝ) : ℂ))) := by
  have hmert := RHTower.tendsto_real_sum_vonMangoldt_div_sub_log
  have hdef : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, principalDefect q n) atTop
      (𝓝 (∑' n, principalDefect q n)) := by
    have h := (summable_principalDefect (q := q)).hasSum.tendsto_sum_nat.comp
      ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
    refine h.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
    have hI : Finset.Ico (0 + 1) (⌊x⌋₊ + 1) = Finset.Icc 1 ⌊x⌋₊ := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI]
    simp [principalDefect]
  have hreal := (hmert.sub hdef).ofReal
  refine hreal.congr fun x => ?_
  have hsplit : ∀ n : ℕ, (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / n =
      ((vonMangoldt n / n - principalDefect q n : ℝ) : ℂ) := fun n => by
    unfold principalDefect
    by_cases hu : IsUnit (n : ZMod q)
    · rw [MulChar.one_apply hu, if_pos hu]; push_cast; ring
    · rw [MulChar.map_nonunit _ hu, if_neg hu]; push_cast; ring
  have h0 : ∀ N : ℕ, ∑ k ∈ Finset.Icc 0 N, vonMangoldt k / (k : ℝ) =
      ∑ k ∈ Finset.Icc 1 N, vonMangoldt k / (k : ℝ) := fun N => by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N)]
    have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    simp [hI]
  simp only [hsplit]
  rw [h0]
  push_cast
  rw [Finset.sum_sub_distrib]
  ring

/-- The Mertens constant of the class `a` mod `q`. -/
def mertensConstantAP (q : ℕ) [NeZero q] (a : ZMod q) : ℝ :=
  (q.totient : ℝ)⁻¹ * (-Real.eulerMascheroniConstant - ∑' n, principalDefect q n +
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, χ a⁻¹ *
      (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)).re)

/-- **The Mertens constants in progressions exist**: for `a` a unit mod `q`,
`Σ_{n ≤ x, n ≡ a} Λ(n)/n − log x/φ(q) → C(q, a)`. -/
theorem tendsto_sum_residueClass_div_sub_log {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass a n / n) - Real.log x / q.totient) atTop
      (𝓝 (mertensConstantAP q a)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hφR : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  -- the principal value `χ₀(a⁻¹) = 1`
  have hinv : IsUnit (a⁻¹ : ZMod q) := by
    obtain ⟨u, rfl⟩ := ha
    rw [ZMod.inv_coe_unit]; exact Units.isUnit _
  -- each nontrivial character
  have hnon : Tendsto (fun x : ℝ => ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ a⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (vonMangoldt n : ℂ) / n) atTop
      (𝓝 (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, χ a⁻¹ *
        (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))) :=
    tendsto_finsetSum _ fun χ hχ =>
      (tendsto_sum_twist_vonMangoldt_div χ (Finset.ne_of_mem_erase hχ)).const_mul _
  have hC := ((tendsto_sum_principal_vonMangoldt_div_sub_log (q := q)).add hnon).const_mul
    ((q.totient : ℂ)⁻¹)
  -- the complex identity
  have hres : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) / (n : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ n * (vonMangoldt n : ℂ) / n) :=
    fun n => by
      rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha n, Finset.mul_sum, Finset.sum_div,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
  have hsumres : ∀ x : ℝ, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) / (n : ℂ) =
      (q.totient : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / n +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          χ a⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (vonMangoldt n : ℂ) / n) := fun x => by
    rw [Finset.sum_congr rfl fun n _ => hres n, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    simp_rw [← Finset.mul_sum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), MulChar.one_apply hinv, one_mul]
  have hid : ∀ x : ℝ, ((((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass a n / n) - Real.log x / q.totient : ℝ)) : ℂ) =
      (q.totient : ℂ)⁻¹ * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / n) - (Real.log x : ℂ) +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          χ a⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (vonMangoldt n : ℂ) / n) := fun x => by
    push_cast
    rw [hsumres x]
    ring
  have hlim : Tendsto (fun x : ℝ => ((((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass a n / n) - Real.log x / q.totient : ℝ)) : ℂ))
      atTop (𝓝 ((q.totient : ℂ)⁻¹ * ((((-Real.eulerMascheroniConstant -
        ∑' n, principalDefect q n : ℝ)) : ℂ) +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, χ a⁻¹ *
          (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))) :=
    hC.congr fun x => (hid x).symm
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hCre : ((q.totient : ℂ)⁻¹ * ((((-Real.eulerMascheroniConstant -
      ∑' n, principalDefect q n : ℝ)) : ℂ) +
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, χ a⁻¹ *
        (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))).re =
      mertensConstantAP q a := by
    unfold mertensConstantAP
    rw [show ((q.totient : ℂ))⁻¹ = (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
  rw [← hCre]
  exact hre.congr fun x => Complex.ofReal_re _

/-! ### Over the primes -/

/-- The higher prime powers carry a convergent series `Σ_{n not prime} Λ(n)/n`. -/
theorem summable_notPrimeVonMangoldt_div :
    Summable fun n : ℕ => RHTower.Mertens.notPrimeVonMangoldt n / n := by
  have h0 : ∀ n : ℕ, 0 ≤ RHTower.Mertens.notPrimeVonMangoldt n / n := fun n => by
    unfold RHTower.Mertens.notPrimeVonMangoldt
    split_ifs
    · simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  refine summable_of_sum_range_le h0 (c := 8 + RHTower.Mertens.mertensTail) fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hT0 : 0 ≤ RHTower.Mertens.mertensTail := by
      unfold RHTower.Mertens.mertensTail; exact tsum_nonneg fun i => by positivity
    simp; linarith
  have h := RHTower.Mertens.tail_bounded (N - 1)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
  have hI : Finset.Ico (0 + 1) N = Finset.Icc 1 (N - 1) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [hI]
  simp only [CharP.cast_eq_zero, div_zero, zero_add]
  exact h

open scoped Classical in
/-- The higher prime powers of the class `a` mod `q`. -/
def classTail {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if (n : ZMod q) = a then RHTower.Mertens.notPrimeVonMangoldt n / n else 0

theorem notPrimeVonMangoldt_div_nonneg (n : ℕ) :
    0 ≤ RHTower.Mertens.notPrimeVonMangoldt n / n := by
  unfold RHTower.Mertens.notPrimeVonMangoldt
  split_ifs
  · simp
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

theorem summable_classTail {q : ℕ} (a : ZMod q) : Summable (classTail a) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_notPrimeVonMangoldt_div
  · unfold classTail
    split_ifs
    · exact notPrimeVonMangoldt_div_nonneg n
    · exact le_rfl
  · unfold classTail
    split_ifs
    · exact le_rfl
    · exact notPrimeVonMangoldt_div_nonneg n

/-- **The Mertens constants over the primes in progressions**: for `a` a unit mod `q`,
`Σ_{p ≤ x, p ≡ a} log p/p − log x/φ(q) → C(q, a) − Σ_{n ≡ a, n not prime} Λ(n)/n`. -/
theorem tendsto_sum_prime_log_div_residueClass_sub_log {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto (fun x : ℝ => (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), Real.log (p : ℝ) / (p : ℝ)) -
          Real.log x / q.totient) atTop
      (𝓝 (mertensConstantAP q a - ∑' n, classTail a n)) := by
  have htail : Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, classTail a n) atTop
      (𝓝 (∑' n, classTail a n)) := by
    have h := (summable_classTail a).hasSum.tendsto_sum_nat.comp
      ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
    refine h.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
    have hI : Finset.Ico (0 + 1) (⌊x⌋₊ + 1) = Finset.Icc 1 ⌊x⌋₊ := by
      ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI]
    simp [classTail]
  refine ((tendsto_sum_residueClass_div_sub_log ha).sub htail).congr fun x => ?_
  have hsplit : ∀ n : ℕ, ArithmeticFunction.vonMangoldt.residueClass a n / n =
      (if n.Prime ∧ (n : ZMod q) = a then Real.log n / n else 0) + classTail a n := fun n => by
    unfold classTail RHTower.Mertens.notPrimeVonMangoldt
    simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hna : (n : ZMod q) = a <;> by_cases hp : n.Prime <;>
      simp [hna, hp, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [Finset.sum_filter]
  simp only [hsplit, Finset.sum_add_distrib]
  ring

end GaloisForLFunctions.ArtinMertens
