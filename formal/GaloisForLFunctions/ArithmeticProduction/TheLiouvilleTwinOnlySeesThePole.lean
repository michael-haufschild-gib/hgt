import GaloisForLFunctions.ArithmeticProduction.TheLengthPrecisionLaw
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# The Liouville twin only sees the pole

The twin test of the deciding-input theorem separates `Λ` from `λΛ` through one number: the residue of the pole, `+1` against `−1`.  Correct the residue and nothing is left to separate.

The **pole-corrected twin** `Λ̂ = λΛ + 2` is the reflection `2 − Λ` of `Λ` around the count kernel, up to `𝒬`.  So

* **every error law is shared** (`errorLaw_poleCorrectedTwin_iff`): for every scale `E` above square root, `Λ̂` satisfies `ψ(x) − x ≪ E` exactly if `Λ` does;
* **the count is shared** (`count_poleCorrectedTwin_iff`): `Λ̂` satisfies the count exactly under RH, while `λΛ` never does;
* **the prime number theorem is shared** (`primeNumberLaw_poleCorrectedTwin`), while `λΛ` has the wrong residue (`tendsto_partialSum_liouvilleWeight_div`).

Being false for the twin is therefore cheap, and no square-root content is attached to it: the prime number theorem already passes.

**Prime polynomials do not see parity at any height `T`** (`exists_twist_polynomial_second_moment_le`, `twist_polynomial_second_moment_le`).  The polynomials of `λΛ` and `−Λ` differ only on even
powers of primes, so their difference has second moment `O(log N · (T + √N))`.  For `N ≤ T²` this is `O(T log T)`, which is below the diagonal `T log²N` of `P_Λ` as soon as `N` is a power of `T`.
So a mean value of a prime polynomial away from the pole cannot be the parity-breaking input.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Asymptotics
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision hiding powerWeight

/-- The reflection `2 − a` of a weight around the count kernel `1`. -/
def countReflection (a : ℕ → ℝ) (n : ℕ) : ℝ := 2 - a n

theorem countReflection_countReflection (a : ℕ → ℝ) : countReflection (countReflection a) = a := by
  funext n
  simp [countReflection]

theorem partialSum_countReflection (a : ℕ → ℝ) (x : ℝ) :
    partialSum (countReflection a) x = 2 * (⌊x⌋₊ : ℝ) - partialSum a x := by
  unfold partialSum countReflection
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  simp
  ring

/-- The defect of the kernel `1`: `2(⌊x⌋ − x) = O(1)`. -/
theorem floor_defect_isBigO : (fun x : ℝ => 2 * ((⌊x⌋₊ : ℝ) - x)) =O[atTop] sqrtScale := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have h1 := Nat.lt_floor_add_one x
  have h2 := Nat.floor_le hx0
  have h3 := one_le_sqrtScale hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqrtScale_nonneg x), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h4 : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

private theorem errorLaw_countReflection {E : ℝ → ℝ} (hE : sqrtScale =O[atTop] E) {a : ℕ → ℝ}
    (h : ErrorLaw E a) : ErrorLaw E (countReflection a) := by
  have h1 := (IsBigO.neg_left h).add (floor_defect_isBigO.trans hE)
  refine h1.congr_left fun x => ?_
  rw [partialSum_countReflection]
  ring

/-- **The reflection preserves every error law above square root.** -/
theorem errorLaw_countReflection_iff {E : ℝ → ℝ} (hE : sqrtScale =O[atTop] E) (a : ℕ → ℝ) :
    ErrorLaw E (countReflection a) ↔ ErrorLaw E a := by
  refine ⟨fun h => ?_, errorLaw_countReflection hE⟩
  have h1 := errorLaw_countReflection hE h
  rwa [countReflection_countReflection] at h1

/-- `λΛ + Λ` is supported on even powers of primes, and it lies in the square-root class. -/
theorem liouvilleWeight_add_mem_sqrtClass : liouvilleWeight + vonMangoldtWeight ∈ sqrtClass := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine IsBigO.of_bound (2 * |C|) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have h0 : partialSum (liouvilleWeight + vonMangoldtWeight) x =
      partialSum liouvilleWeight x + Chebyshev.psi x := by
    rw [partialSum_add, partialSum_vonMangoldt]
  obtain ⟨h1, h2⟩ := partialSum_liouvilleWeight_add_psi x
  rw [h0, Real.norm_of_nonneg h1, Real.norm_of_nonneg (sqrtScale_nonneg x)]
  have h3 := sqrt_le_sqrtScale hx
  have h4 : Chebyshev.psi x - Chebyshev.theta x ≤ |C| * √x :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg x))
  have h5 : |C| * √x ≤ |C| * sqrtScale x := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
  calc partialSum liouvilleWeight x + Chebyshev.psi x ≤ 2 * (Chebyshev.psi x - Chebyshev.theta x) := h2
    _ ≤ 2 * (|C| * sqrtScale x) := by linarith
    _ = _ := by ring

/-- The pole-corrected Liouville twin `λΛ + 2`. -/
def poleCorrectedTwin (n : ℕ) : ℝ := liouvilleWeight n + 2

theorem poleCorrectedTwin_eq :
    poleCorrectedTwin = countReflection vonMangoldtWeight + (liouvilleWeight + vonMangoldtWeight) := by
  funext n
  simp only [poleCorrectedTwin, countReflection, Pi.add_apply]
  ring

/-- **The corrected twin satisfies every error law that `Λ` satisfies, above square root.** -/
theorem errorLaw_poleCorrectedTwin_iff {E : ℝ → ℝ} (hE : sqrtScale =O[atTop] E) :
    ErrorLaw E poleCorrectedTwin ↔ ErrorLaw E vonMangoldtWeight := by
  have hδ : partialSum (liouvilleWeight + vonMangoldtWeight) =O[atTop] E :=
    IsBigO.trans liouvilleWeight_add_mem_sqrtClass hE
  rw [← errorLaw_countReflection_iff hE vonMangoldtWeight]
  constructor
  · intro h
    have h1 := IsBigO.sub h hδ
    refine h1.congr_left fun x => ?_
    rw [poleCorrectedTwin_eq, partialSum_add (countReflection vonMangoldtWeight)]
    ring
  · intro h
    have h1 := IsBigO.add h hδ
    refine h1.congr_left fun x => ?_
    rw [poleCorrectedTwin_eq, partialSum_add (countReflection vonMangoldtWeight)]
    ring

/-- **The corrected twin satisfies the count exactly under RH.** -/
theorem count_poleCorrectedTwin_iff : Count poleCorrectedTwin ↔ RiemannHypothesis :=
  (errorLaw_poleCorrectedTwin_iff (isBigO_refl _ _)).trans count_vonMangoldt_iff

/-- The twin has residue `−1`. -/
theorem tendsto_partialSum_liouvilleWeight_div :
    Tendsto (fun x => partialSum liouvilleWeight x / x) atTop (𝓝 (-1)) := by
  have h0 := (IsBigO.trans_isLittleO liouvilleWeight_add_mem_sqrtClass
    sqrtScale_isLittleO_id).tendsto_div_nhds_zero
  have h1 := h0.sub primeNumberLaw_vonMangoldt
  rw [zero_sub] at h1
  refine h1.congr fun x => ?_
  rw [partialSum_add]
  ring

/-- **The corrected twin has residue `+1`.** -/
theorem primeNumberLaw_poleCorrectedTwin : PrimeNumberLaw poleCorrectedTwin := by
  have h1 := tendsto_partialSum_liouvilleWeight_div
  have h2 : Tendsto (fun x : ℝ => 2 * ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 (2 * 1)) :=
    (tendsto_nat_floor_div_atTop (R := ℝ)).const_mul 2
  have h3 := h1.add h2
  have hval : (-1 : ℝ) + 2 * 1 = 1 := by norm_num
  rw [hval] at h3
  refine h3.congr fun x => ?_
  have h4 : partialSum poleCorrectedTwin x = partialSum liouvilleWeight x + 2 * (⌊x⌋₊ : ℝ) := by
    unfold partialSum poleCorrectedTwin
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    simp
    ring
  rw [h4]
  ring

/-! ### Prime polynomials do not see parity -/

/-- `P_{λΛ} + P_Λ` is the polynomial of `λΛ + Λ`. -/
theorem linePoly_liouville_add_vonMangoldt (N : ℕ) (t : ℝ) :
    linePoly (fun n => ((liouvilleWeight n : ℝ) : ℂ)) N t + linePoly (fun n => ((vonMangoldt n : ℝ) : ℂ)) N t =
      linePoly (fun n => ((liouvilleWeight n + vonMangoldt n : ℝ) : ℂ)) N t := by
  unfold linePoly _root_.RHTower.edPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- **The second moment of the difference of the two prime polynomials.** -/
theorem exists_twist_polynomial_second_moment_le :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (N : ℕ) (T₁ T₂ : ℝ), 1 ≤ N → T₁ ≤ T₂ →
      (∫ t in T₁..T₂, ‖linePoly (fun n => ((liouvilleWeight n + vonMangoldt n : ℝ) : ℂ)) N t‖ ^ 2) ≤
        Real.log N * (C₁ * (T₂ - T₁) + C₂ * √(N : ℝ)) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs := _root_.RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑' n : ℕ, if n.Prime then 0 else (vonMangoldt n : ℝ) / n := ⟨_, rfl⟩
  have hnn : ∀ n : ℕ, 0 ≤ if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n := by
    intro n
    split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact tsum_nonneg hnn
  refine ⟨4 * B, 208 * (4 * |C|), by positivity, by positivity, ?_⟩
  intro N T₁ T₂ hN hT
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun n => liouvilleWeight n + vonMangoldt n := ⟨_, rfl⟩
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    rw [he]
    exact (liouvilleWeight_add_vonMangoldt_le n).1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have heN : ∀ n ∈ Finset.Icc 1 N, e n ≤ 2 * Real.log N := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have h1 := (liouvilleWeight_add_vonMangoldt_le n).2
    have h2 : (if n.Prime then (0 : ℝ) else vonMangoldt n) ≤ vonMangoldt n := by
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
    have h3 : (vonMangoldt n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h4 : Real.log n ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn2)
    rw [he]
    show liouvilleWeight n + vonMangoldt n ≤ _
    linarith
  have hsq : ∀ n ∈ Finset.Icc 1 N, e n ^ 2 ≤ 2 * Real.log N * e n := by
    intro n hn
    rw [sq]
    exact mul_le_mul_of_nonneg_right (heN n hn) (he0 n)
  -- the diagonal
  have hS₁ : ∑ n ∈ Finset.Icc 1 N, e n ^ 2 / n ≤ Real.log N * (4 * B) := by
    calc ∑ n ∈ Finset.Icc 1 N, e n ^ 2 / n
        ≤ ∑ n ∈ Finset.Icc 1 N, (2 * Real.log N) *
            (2 * (if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h1 := div_le_div_of_nonneg_right (hsq n hn) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          refine h1.trans ?_
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h2 := (liouvilleWeight_add_vonMangoldt_le n).2
          have h3 := div_le_div_of_nonneg_right h2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          rw [he]
          refine h3.trans (le_of_eq ?_)
          split_ifs <;> ring
      _ = (2 * Real.log N) * (2 * ∑ n ∈ Finset.Icc 1 N,
            (if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (2 * Real.log N) * (2 * B) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by positivity)
          rw [hB]
          exact hs.sum_le_tsum _ fun n _ => hnn n
      _ = _ := by ring
  -- the off-diagonal
  have hS₂ : ∑ n ∈ Finset.Icc 1 N, e n ^ 2 ≤ Real.log N * (4 * |C| * √(N : ℝ)) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, e n ≤ 2 * (|C| * √(N : ℝ)) := by
      have h2 := (partialSum_liouvilleWeight_add_psi (N : ℝ)).2
      have h3 : partialSum liouvilleWeight (N : ℝ) + Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Icc 1 N, e n := by
        rw [← partialSum_vonMangoldt, ← partialSum_add]
        unfold partialSum
        rw [Nat.floor_natCast, show Finset.Icc 1 N = Finset.Ioc 0 N by ext; simp [Nat.succ_le_iff], he]
        rfl
      rw [h3] at h2
      refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact (hC N).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
    calc ∑ n ∈ Finset.Icc 1 N, e n ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, 2 * Real.log N * e n :=
          Finset.sum_le_sum hsq
      _ = 2 * Real.log N * ∑ n ∈ Finset.Icc 1 N, e n := by rw [Finset.mul_sum]
      _ ≤ 2 * Real.log N * (2 * (|C| * √(N : ℝ))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hmvt := (abs_le.mp (abs_integral_norm_sq_linePoly_sub_le
    (fun n => ((e n : ℝ) : ℂ)) N T₁ T₂)).2
  have hnorm : ∀ n, ‖((e n : ℝ) : ℂ)‖ = e n := fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (he0 n)]
  simp only [hnorm] at hmvt
  subst he
  have h3 := mul_le_mul_of_nonneg_left hS₁ (by linarith : 0 ≤ T₂ - T₁)
  have h4 := mul_le_mul_of_nonneg_left hS₂ (by norm_num : (0 : ℝ) ≤ 208)
  have hexp : Real.log N * (4 * B * (T₂ - T₁) + 208 * (4 * |C|) * √(N : ℝ)) =
      (T₂ - T₁) * (Real.log N * (4 * B)) + 208 * (Real.log N * (4 * |C| * √(N : ℝ))) := by ring
  rw [hexp]
  linarith

/-- **Through length `T²`, the prime polynomials of `λΛ` and `−Λ` agree in mean square, up to `O(T log T)`.** -/
theorem twist_polynomial_second_moment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ T ^ 2 →
      (∫ t in T..(2 * T), ‖linePoly (fun n => ((liouvilleWeight n + vonMangoldt n : ℝ) : ℂ)) N t‖ ^ 2) ≤
        C * (T * Real.log T) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := exists_twist_polynomial_second_moment_le
  refine ⟨2 * (C₁ + C₂), mul_nonneg (by norm_num) (add_nonneg hC₁ hC₂), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT N hN hNT
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hb := h N T (2 * T) hN (by linarith)
  have hN1 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : Real.log N ≤ 2 * Real.log T := by
    have h1 := Real.log_le_log hN1 hNT
    rw [Real.log_pow] at h1
    exact_mod_cast h1
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hsqrt : √(N : ℝ) ≤ T := Real.sqrt_le_iff.mpr ⟨hT0.le, hNT⟩
  have h2 : C₁ * (2 * T - T) + C₂ * √(N : ℝ) ≤ (C₁ + C₂) * T := by
    have h3 := mul_le_mul_of_nonneg_left hsqrt hC₂
    have h4 : C₁ * (2 * T - T) = C₁ * T := by ring
    rw [add_mul, h4]
    linarith
  refine hb.trans ?_
  calc Real.log N * (C₁ * (2 * T - T) + C₂ * √(N : ℝ))
      ≤ (2 * Real.log T) * ((C₁ + C₂) * T) :=
        mul_le_mul hlogN h2 (add_nonneg (mul_nonneg hC₁ (by linarith))
          (mul_nonneg hC₂ (Real.sqrt_nonneg _))) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticProduction
