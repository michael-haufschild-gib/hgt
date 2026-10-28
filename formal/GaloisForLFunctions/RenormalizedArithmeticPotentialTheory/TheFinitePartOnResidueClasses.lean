import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ClassHarmonicSumsHaveConstants
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremInResidueClassesWithItsConstant

/-!
# The finite part on residue classes

On the unit residue classes mod `q` the horizon divergence is the rank-one `(q/φ(q)) ℓ²`
(`exists_abs_residueGram_sub_le`). This file computes the finite part of the residue Gram.

* **The residue Gram as class Mertens sums** (`primeBilinear_residuePole_eq_classMertens`): for
  units `a, b` and `M ≤ M' ≤ N`,
  `⟨w_a^{(M)}, P w_b^{(M')}⟩ = Σ_{m ≤ M, m ≡ a} A(⌊M'/m⌋; a⁻¹b)/m + Σ_{n ≤ M, n ≡ b} A(⌊M/n⌋; b⁻¹a)/n`.
* **Floors** (`sum_log_floor_defect_le`): `0 ≤ Σ_{m ≤ M} (log(X/m) − log⌊X/m⌋)/m ≤ 2` for `M ≤ X`.
* **The logarithmic main term is exact to `O(1)`** (`exists_abs_residueLogGram_sub_le`): with the
  class constants `d_a` of `q S_a(M) = log M + d_a + O(1/M)`, the model Gram
  `φ(q)^{−1}(L_a(M) + log(M'/M) S_a(M) + L_b(M))` equals `(q/φ(q)) S_a(M) S_b(M') + O(1)`: the
  constants `d_a, d_b` cancel.
* **The residue finite-part law** (`exists_abs_residueGram_finitePart_le`): for every `η > 0`,
  `⟨w_a^{(M)}, P w_b^{(M')}⟩ = (q/φ(q)) S_a(M) S_b(M') + c_{a⁻¹b} S_a(M) + c_{b⁻¹a} S_b(M) +
  O(η H_M + C_η)`, with the class Mertens constants `c_r` (`classMertensConstant`).

So the finite part on residue classes is the convolution by the class Mertens constants: the pair
`(a, b)` carries `c_{a⁻¹b} + c_{b⁻¹a}` per unit of mass, the constant of the prime powers carrying
one class into the other, in both directions.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ}

/-- **The residue Gram as class Mertens sums**: for units `a, b` and `M ≤ M' ≤ N`. -/
theorem primeBilinear_residuePole_eq_classMertens {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b)
    {M M' N : ℕ} (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    primeBilinear N (residuePole q a M) (residuePole q b M') =
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then classMertensSum q (a⁻¹ * b) (M' / m) / m
        else 0) +
      ∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then classMertensSum q (b⁻¹ * a) (M / n) / n
        else 0) := by
  rw [primeBilinear_residuePole_eq a b (hMM'.trans hM'N) hM'N]
  congr 1
  · exact sum_congr rfl fun m _ => by
      split_ifs with hm
      · rw [classMertensRow_eq ha b hm]
      · rfl
  · -- the rows of `n > M` are empty
    have hsub : ∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) =
        ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) := by
      refine sum_subset (Icc_subset_Icc_right hMM') fun n hn hn' => ?_
      have hnM : M < n := by simp only [mem_Icc] at hn hn'; omega
      rw [classMertensRow, Nat.div_eq_of_lt hnM, Finset.Icc_eq_empty (by norm_num), sum_empty,
        zero_div, ite_self]
    rw [← hsub]
    exact sum_congr rfl fun n _ => by
      split_ifs with hn
      · rw [classMertensRow_eq hb a hn]
      · rfl

/-- **Floors cost at most `2`**: `0 ≤ Σ_{m ≤ M} (log X − log m − log⌊X/m⌋)/m ≤ 2` for `M ≤ X`,
because `X/m < ⌊X/m⌋ + 1 ≤ 2⌊X/m⌋`. -/
theorem sum_log_floor_defect_le {M X : ℕ} (hMX : M ≤ X) :
    0 ≤ ∑ m ∈ Icc 1 M, (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m ∧
      ∑ m ∈ Icc 1 M, (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m ≤ 2 := by
  have hterm : ∀ m ∈ Icc 1 M,
      0 ≤ (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m ∧
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m ≤ 2 / X := by
    intro m hm
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hmX : m ≤ X := (mem_Icc.mp hm).2.trans hMX
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hX' : (0 : ℝ) < X := by exact_mod_cast hm0.trans_le hmX
    set k := X / m with hk
    have hk1 : 1 ≤ k := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    -- `m k ≤ X < m (k + 1)`
    have hlo : m * k ≤ X := Nat.mul_div_le X m
    have hhi : X < m * (k + 1) := by
      rw [hk]
      exact Nat.lt_mul_div_succ X hm0
    have hlo' : (m : ℝ) * k ≤ X := by exact_mod_cast hlo
    have hhi' : (X : ℝ) < m * (k + 1) := by exact_mod_cast hhi
    have heq : Real.log X - Real.log m - Real.log k = Real.log (X / (m * k)) := by
      rw [Real.log_div hX'.ne' (by positivity), Real.log_mul hm'.ne' (by positivity)]
      ring
    rw [heq]
    have hratio : (1 : ℝ) ≤ X / (m * k) := by rw [le_div_iff₀ (by positivity)]; linarith
    refine ⟨div_nonneg (Real.log_nonneg hratio) hm'.le, ?_⟩
    -- `log(X/(mk)) ≤ X/(mk) − 1 < 1/k ≤ 2m/X`
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < X / (m * k) by positivity)
    have h2 : (X : ℝ) / (m * k) - 1 ≤ 2 * m / X := by
      rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hX']
      have ha : (X : ℝ) - m * k ≤ m := by linarith
      have hb : (X : ℝ) ≤ 2 * m * k := by nlinarith
      have ha0 : 0 ≤ (X : ℝ) - m * k := by linarith
      nlinarith [mul_le_mul ha hb hX'.le hm'.le]
    have h3 : 2 * (m : ℝ) / X * X = 2 * m := by field_simp
    rw [div_le_div_iff₀ hm' hX']
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) hX'.le]
  refine ⟨sum_nonneg fun m hm => (hterm m hm).1, ?_⟩
  calc ∑ m ∈ Icc 1 M, (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m
      ≤ ∑ _m ∈ Icc 1 M, 2 / (X : ℝ) := sum_le_sum fun m hm => (hterm m hm).2
    _ ≤ 2 := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos X with hX | hX
        · simp [hX]
        · have hX' : (0 : ℝ) < X := by exact_mod_cast hX
          have : ((M + 1 - 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast (by omega : M + 1 - 1 ≤ X)
          rw [mul_div_assoc', div_le_iff₀ hX']
          linarith

/-- **The logarithmic model Gram is exact to `O(1)`**: there is `K` with
`|L_a(M) + log(M'/M) S_a(M) + L_b(M) − q S_a(M) S_b(M')| ≤ K` for `1 ≤ M ≤ M'`. -/
theorem exists_abs_residueLogGram_sub_le [NeZero q] (a b : ZMod q) :
    ∃ K : ℝ, ∀ M M' : ℕ, 1 ≤ M → M ≤ M' →
      |classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
          classLogSum q b M - q * classHarmonic q a M * classHarmonic q b M'| ≤ K := by
  obtain ⟨da, hda⟩ := exists_classHarmonic_constant (q := q) a
  obtain ⟨db, hdb⟩ := exists_classHarmonic_constant (q := q) b
  set K₀ : ℝ := 1 + 2 * q ^ 2 with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  refine ⟨(2 * (2 * (K₀ + 1 / 2)) + 2 * K₀ + |da * db| + |da| * K₀ + K₀ * |db| + K₀ ^ 2) / q,
    fun M M' hM hMM' => ?_⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM'0 : (0 : ℝ) < M' := by exact_mod_cast hM.trans hMM'
  have hMM'r : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
  have hMne : (M : ℝ) ≠ 0 := hM0.ne'
  have hM'ne : (M' : ℝ) ≠ 0 := hM'0.ne'
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlogMle : Real.log M ≤ M := (Real.log_le_sub_one_of_pos hM0).trans (by linarith)
  -- the errors of the second-order asymptotics
  set σa := (q : ℝ) * classHarmonic q a M - Real.log M - da with hσa
  set σb := (q : ℝ) * classHarmonic q b M' - Real.log M' - db with hσb
  set la := (q : ℝ) * classLogSum q a M - Real.log M ^ 2 / 2 - da * Real.log M with hla
  set lb := (q : ℝ) * classLogSum q b M - Real.log M ^ 2 / 2 - db * Real.log M with hlb
  have hσa' : |σa| ≤ K₀ / M := hda M hM
  have hσb' : |σb| ≤ K₀ / M' := hdb M' (hM.trans hMM')
  have h1M : 0 ≤ 1 / (M : ℝ) := by positivity
  have hshrink : 2 * (K₀ + 1 / 2) * (1 - 1 / (M : ℝ)) ≤ 2 * (K₀ + 1 / 2) := by nlinarith
  have hla' : |la| ≤ 2 * (K₀ + 1 / 2) :=
    (abs_classLogSum_sub_le_const a hK₀0 hda hM).trans hshrink
  have hlb' : |lb| ≤ 2 * (K₀ + 1 / 2) :=
    (abs_classLogSum_sub_le_const b hK₀0 hdb hM).trans hshrink
  -- `q · (model − q S_a S_b') = λ_a + λ_b − σ_a log M − σ_b' log M − d_a d_b − d_a σ_b' − σ_a d_b −
  -- σ_a σ_b'`
  have hid : (q : ℝ) * (classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
      classLogSum q b M - q * classHarmonic q a M * classHarmonic q b M') =
      la + lb - σa * Real.log M - σb * Real.log M - da * db - da * σb - σa * db - σa * σb := by
    simp only [hσa, hσb, hla, hlb]
    ring
  -- each error term is bounded
  have e1 : |σa * Real.log M| ≤ K₀ := by
    rw [abs_mul, abs_of_nonneg hlogM]
    calc |σa| * Real.log M ≤ K₀ / M * M := mul_le_mul hσa' hlogMle hlogM (by positivity)
      _ = K₀ := by field_simp
  have e2 : |σb * Real.log M| ≤ K₀ := by
    rw [abs_mul, abs_of_nonneg hlogM]
    calc |σb| * Real.log M ≤ K₀ / M' * M' := mul_le_mul hσb' (hlogMle.trans hMM'r) hlogM
          (by positivity)
      _ = K₀ := by field_simp
  have hσa1 : |σa| ≤ K₀ := hσa'.trans (div_le_self hK₀0 (by exact_mod_cast hM))
  have hσb1 : |σb| ≤ K₀ := hσb'.trans (div_le_self hK₀0 (by exact_mod_cast hM.trans hMM'))
  have e3 : |da * σb| ≤ |da| * K₀ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hσb1 (abs_nonneg _)
  have e4 : |σa * db| ≤ K₀ * |db| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hσa1 (abs_nonneg _)
  have e5 : |σa * σb| ≤ K₀ ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hσa1 hσb1 (abs_nonneg _) hK₀0
  have htot : |(q : ℝ) * (classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
      classLogSum q b M - q * classHarmonic q a M * classHarmonic q b M')| ≤
      2 * (2 * (K₀ + 1 / 2)) + 2 * K₀ + |da * db| + |da| * K₀ + K₀ * |db| + K₀ ^ 2 := by
    rw [hid]
    have := abs_le.mp hla'
    have := abs_le.mp hlb'
    have := abs_le.mp e1
    have := abs_le.mp e2
    have := abs_le.mp e3
    have := abs_le.mp e4
    have := abs_le.mp e5
    have := neg_abs_le (da * db)
    have := le_abs_self (da * db)
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hq] at htot
  rw [le_div_iff₀ hq]
  linarith

/-- **The residue finite-part law**: for units `a, b` and every `η > 0` there is `C` with
`|⟨w_a^{(M)}, P w_b^{(M')}⟩ − (q/φ(q)) S_a(M) S_b(M') − c_{a⁻¹b} S_a(M) − c_{b⁻¹a} S_b(M)| ≤
η H_M + C` for `1 ≤ M ≤ M' ≤ N`. -/
theorem exists_abs_residueGram_finitePart_le [NeZero q] {a b : ZMod q} (ha : IsUnit a)
    (hb : IsUnit b) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M M' N : ℕ, 1 ≤ M → M ≤ M' → M' ≤ N →
      |primeBilinear N (residuePole q a M) (residuePole q b M') -
          (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M' -
          classMertensConstant q (a⁻¹ * b) * classHarmonic q a M -
          classMertensConstant q (b⁻¹ * a) * classHarmonic q b M| ≤ η * harmonicSum M + C := by
  have hainv : IsUnit a⁻¹ := IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  have hbinv : IsUnit b⁻¹ := IsUnit.of_mul_eq_one b (ZMod.inv_mul_of_unit b hb)
  set r₁ := a⁻¹ * b
  set r₂ := b⁻¹ * a
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  -- the Mertens remainders `D_r(y) = A(y; r) − log y/φ(q) − c_r` vanish at infinity
  set D₁ : ℕ → ℝ := fun y =>
    |classMertensSum q r₁ y - Real.log y / q.totient - classMertensConstant q r₁|
  set D₂ : ℕ → ℝ := fun y =>
    |classMertensSum q r₂ y - Real.log y / q.totient - classMertensConstant q r₂|
  have hD₁ : Tendsto D₁ atTop (𝓝 0) := by
    have h := (tendsto_classMertensSum_sub (hainv.mul hb)).sub_const (classMertensConstant q r₁)
    rw [sub_self] at h
    simpa using h.abs
  have hD₂ : Tendsto D₂ atTop (𝓝 0) := by
    have h := (tendsto_classMertensSum_sub (hbinv.mul ha)).sub_const (classMertensConstant q r₂)
    rw [sub_self] at h
    simpa using h.abs
  obtain ⟨C₁, hC₁⟩ := exists_abs_sum_div_sub_le_of_tendsto hD₁ (η := η / 2) (by positivity)
  obtain ⟨C₂, hC₂⟩ := exists_abs_sum_div_sub_le_of_tendsto hD₂ (η := η / 2) (by positivity)
  obtain ⟨K, hK⟩ := exists_abs_residueLogGram_sub_le (q := q) a b
  refine ⟨K / q.totient + 4 / q.totient + |C₁| + |C₂|, fun M M' N hM hMM' hM'N => ?_⟩
  rw [primeBilinear_residuePole_eq_classMertens ha hb hMM' hM'N]
  -- split each row into its logarithm, its constant and its remainder
  have hsplit : ∀ (c : ZMod q) (r : ZMod q) (X : ℕ), M ≤ X →
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then classMertensSum q r (X / m) / m else 0) =
        (classLogSum q c M + (Real.log X - Real.log M) * classHarmonic q c M) / q.totient -
          (∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then
            (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m else 0)) / q.totient +
          classMertensConstant q r * classHarmonic q c M +
          ∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then (classMertensSum q r (X / m) -
            Real.log ((X / m : ℕ) : ℝ) / q.totient - classMertensConstant q r) / m else 0) := by
    intro c r X _
    rw [← sum_classLog_div_eq c (q.totient : ℝ) M X, classHarmonic, mul_sum, sum_div,
      ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    split_ifs
    · ring
    · simp
  rw [hsplit a r₁ M' hMM', hsplit b r₂ M le_rfl]
  -- the floor defects
  have hF : ∀ (c : ZMod q) (X : ℕ), M ≤ X →
      0 ≤ ∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m else 0) ∧
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m else 0) ≤ 2 := by
    intro c X hX
    obtain ⟨h0, h2⟩ := sum_log_floor_defect_le hX
    have hle : ∀ m ∈ Icc 1 M, (if (m : ZMod q) = c then
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m else 0) ≤
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m := by
      intro m hm
      split_ifs
      · exact le_rfl
      · have hm0 := (mem_Icc.mp hm).1
        have hmX := (mem_Icc.mp hm).2.trans hX
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
        have h2' := log_div_add_log_le hm0 hmX
        exact div_nonneg (by linarith) hm'.le
    have hge : ∀ m ∈ Icc 1 M, 0 ≤ (if (m : ZMod q) = c then
        (Real.log X - Real.log m - Real.log ((X / m : ℕ) : ℝ)) / m else 0) := by
      intro m hm
      split_ifs
      · have hm0 := (mem_Icc.mp hm).1
        have hmX := (mem_Icc.mp hm).2.trans hX
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
        have h2' := log_div_add_log_le hm0 hmX
        exact div_nonneg (by linarith) hm'.le
      · exact le_rfl
    exact ⟨sum_nonneg hge, (sum_le_sum hle).trans h2⟩
  obtain ⟨hF₁0, hF₁2⟩ := hF a M' hMM'
  obtain ⟨hF₂0, hF₂2⟩ := hF b M le_rfl
  -- the remainders
  have hR : ∀ (c r : ZMod q) (X : ℕ) (D : ℕ → ℝ),
      (∀ y, D y = |classMertensSum q r y - Real.log y / q.totient - classMertensConstant q r|) →
      |∑ m ∈ Icc 1 M, (if (m : ZMod q) = c then (classMertensSum q r (X / m) -
          Real.log ((X / m : ℕ) : ℝ) / q.totient - classMertensConstant q r) / m else 0)| ≤
        ∑ m ∈ Icc 1 M, D (X / m) / m := by
    intro c r X D hDdef
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    have hm' : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    split_ifs
    · rw [abs_div, abs_of_pos hm', hDdef]
    · rw [abs_zero, hDdef]
      positivity
  have hC₁' := hC₁ M M' hMM'
  have hC₂' := hC₂ M M le_rfl
  rw [zero_mul, sub_zero] at hC₁' hC₂'
  have hR₁ := (hR a r₁ M' D₁ fun _ => rfl).trans ((le_abs_self _).trans hC₁')
  have hR₂ := (hR b r₂ M D₂ fun _ => rfl).trans ((le_abs_self _).trans hC₂')
  -- the logarithmic main terms
  have hlog := hK M M' hM hMM'
  have hlogφ : |(classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M) /
      q.totient + (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) /
      q.totient - (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M'| ≤
      K / q.totient := by
    have : (classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M) / q.totient +
        (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) / q.totient -
        (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M' =
        (classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
          classLogSum q b M - q * classHarmonic q a M * classHarmonic q b M') / q.totient := by
      field_simp
      ring
    rw [this, abs_div, abs_of_pos hφ0]
    exact div_le_div_of_nonneg_right hlog hφ0.le
  have hH0 := harmonicSum_nonneg M
  rw [abs_le] at hlogφ hR₁ hR₂ ⊢
  have hφinv : 0 ≤ 2 / (q.totient : ℝ) := by positivity
  have hf1 : (∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
      (Real.log M' - Real.log m - Real.log ((M' / m : ℕ) : ℝ)) / m else 0)) / q.totient ≤
      2 / q.totient := div_le_div_of_nonneg_right hF₁2 hφ0.le
  have hf2 : (∑ m ∈ Icc 1 M, (if (m : ZMod q) = b then
      (Real.log M - Real.log m - Real.log ((M / m : ℕ) : ℝ)) / m else 0)) / q.totient ≤
      2 / q.totient := div_le_div_of_nonneg_right hF₂2 hφ0.le
  have hf1' : 0 ≤ (∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
      (Real.log M' - Real.log m - Real.log ((M' / m : ℕ) : ℝ)) / m else 0)) / q.totient :=
    div_nonneg hF₁0 hφ0.le
  have hf2' : 0 ≤ (∑ m ∈ Icc 1 M, (if (m : ZMod q) = b then
      (Real.log M - Real.log m - Real.log ((M / m : ℕ) : ℝ)) / m else 0)) / q.totient :=
    div_nonneg hF₂0 hφ0.le
  have h4 : 4 / (q.totient : ℝ) = 2 / q.totient + 2 / q.totient := by ring
  have hC₁a := le_abs_self C₁
  have hC₂a := le_abs_self C₂
  constructor <;> linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
