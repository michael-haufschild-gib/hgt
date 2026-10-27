import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsPolar
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant

/-!
# The finite part is Euler's constant

At the horizon the divergence of Weil's prime form on uniform profiles is the square of the polar
functional (`TheHorizonCountertermIsPolar`). This file computes what remains after the counterterm
is removed: a scalar.

* **Mertens and Euler at the integers** (`tendsto_mertensSum_sub_log`,
  `tendsto_harmonicSum_sub_log`): `Σ_{t ≤ y} Λ(t)/t = log y − γ + o(1)` (RHTower, from the Laurent
  expansion `−ζ′/ζ(s) = 1/(s − 1) − γ + O(s − 1)` and the prime number theorem with error term), and
  `H_M = log M + γ + o(1)`.
* **The finite part of the pole Gram** (`exists_abs_primeBilinear_truncPole_finitePart_le`): for every
  `η > 0` there is `C` with
  `|⟨u^{(M)}, P u^{(M')}⟩ − H_M H_{M'} + 2γ H_{min(M, M')}| ≤ η H_{min(M, M')} + C`.
* **The finite part on step profiles** (`exists_abs_atomicWeilForm_stepProfile_finitePart_le`,
  `exists_abs_atomicWeilForm_stepProfile_add_le_of_polar`):
  `P_N(x) = ℓ(x)² − 2γ |x|² + o(|c|-mass)`, and on the polar hyperplane `P_N(x) = −2γ |x|² + o(|c|-mass)`.

So the renormalized limit of the prime place at the horizon is the **scalar** `−2γ` on the survival
cone: the constant term of `−ζ′/ζ` at its pole, once for each Hecke direction. In Weil's form the
prime place enters with a minus sign, so on polar-neutral uniform profiles it contributes `+2γ` per
unit mass: after renormalization the prime place is positive there. Positivity of the finite part
of the prime place on the survival cone is a theorem; the sign of Weil's form is decided by the
finite parts of the archimedean place and the pole.
-/

noncomputable section

open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Mertens and Euler at the integers -/

theorem tendsto_mertensSum_sub_log :
    Tendsto (fun y : ℕ => mertensSum y - Real.log y) atTop (𝓝 (-γ)) := by
  have h := RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.comp tendsto_natCast_atTop_atTop
  refine h.congr fun y => ?_
  simp only [Function.comp, Nat.floor_natCast, mertensSum]
  congr 1
  refine (sum_subset (Icc_subset_Icc (Nat.zero_le 1) le_rfl) fun x hx hx' => ?_).symm
  have hx0 : x = 0 := by
    simp only [mem_Icc] at hx hx'
    omega
  simp [hx0]

theorem tendsto_harmonicSum_sub_log :
    Tendsto (fun M : ℕ => harmonicSum M - Real.log M) atTop (𝓝 γ) := by
  refine Real.tendsto_harmonic_sub_log.congr fun M => ?_
  simp [harmonicSum, harmonic_eq_sum_Icc, one_div]

/-! ### The finite part of the pole Gram -/

/-- `0 ≤ log M' − log ⌊M'/m⌋ − log m ≤ 1/⌊M'/m⌋` for `m ≤ M'`. -/
theorem roundoff_le {m M' : ℕ} (hm : 0 < m) (hmM' : m ≤ M') :
    0 ≤ Real.log M' - Real.log ((M' / m : ℕ) : ℝ) - Real.log m ∧
      Real.log M' - Real.log ((M' / m : ℕ) : ℝ) - Real.log m ≤ 1 / ((M' / m : ℕ) : ℝ) := by
  have hq : 1 ≤ M' / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  have hq' : (1 : ℝ) ≤ ((M' / m : ℕ) : ℝ) := by exact_mod_cast hq
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨by linarith [log_div_add_log_le hm hmM'], ?_⟩
  have hlt := RHTower.Mertens.cast_div_lt M' m hm
  rw [div_lt_iff₀ hm'] at hlt
  have hpos : (0 : ℝ) < ((M' / m : ℕ) : ℝ) * m := by positivity
  have hM' : (0 : ℝ) < M' := by exact_mod_cast (hm.trans_le hmM')
  have hratio : Real.log M' - Real.log ((M' / m : ℕ) : ℝ) - Real.log m =
      Real.log ((M' : ℝ) / (((M' / m : ℕ) : ℝ) * m)) := by
    rw [Real.log_div hM'.ne' hpos.ne', Real.log_mul (by positivity) hm'.ne']; ring
  rw [hratio]
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (M' : ℝ) / (((M' / m : ℕ) : ℝ) * m) by
    positivity)
  have h2 : (M' : ℝ) / (((M' / m : ℕ) : ℝ) * m) - 1 ≤ 1 / ((M' / m : ℕ) : ℝ) := by
    rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos (by linarith)]
    nlinarith
  linarith

/-- **The finite part of the pole Gram.** For every `η > 0` there is `C` such that for
`1 ≤ M ≤ M' ≤ N`, `|⟨u^{(M)}, P u^{(M')}⟩ − H_M H_{M'} + 2γ H_M| ≤ η H_M + C`. -/
theorem exists_abs_primeBilinear_truncPole_finitePart_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M M' N : ℕ, 1 ≤ M → M ≤ M' → M' ≤ N →
      |primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
        2 * γ * harmonicSum M| ≤ η * harmonicSum M + C := by
  have hγ1 : γ < 1 := Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hγ0 : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  -- the two limits, at precision `η/4`
  obtain ⟨Y₁, hY₁⟩ := (Metric.tendsto_atTop.mp tendsto_mertensSum_sub_log) (η / 4) (by positivity)
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp tendsto_harmonicSum_sub_log) (η / 4) (by positivity)
  set Y : ℕ := max Y₁ (⌈4 / η⌉₊ + 1)
  set Ce : ℝ := Real.log 4 + 4 + 1
  refine ⟨(Ce + Real.log 2) * Y + 2 * (1 + Real.log M₀), fun M M' N hM hMM' hM'N => ?_⟩
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hHM := harmonicSum_nonneg M
  -- `B = (log M' − γ) H_M + Σ_m (e(⌊M'/m⌋) − r_m)/m`
  set e : ℕ → ℝ := fun y => mertensSum y - Real.log y + γ
  set r : ℕ → ℝ := fun m => Real.log M' - Real.log ((M' / m : ℕ) : ℝ) - Real.log m
  have hB : primeBilinear N (truncPole M) (truncPole M') =
      (Real.log M' - γ) * harmonicSum M + ∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m := by
    rw [primeBilinear_truncPole_eq hMM' hM'N, harmonicSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [e, r]
    ring
  -- the error term
  have herr : |∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m| ≤ η / 2 * harmonicSum M + (Ce + Real.log 2) * Y := by
    have hpt : ∀ m ∈ Icc 1 M, |(e (M' / m) - r m) / m| ≤
        η / 2 * (1 / (m : ℝ)) + (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0) := by
      intro m hm
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      have hmM' := (mem_Icc.mp hm).2.trans hMM'
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      have hq : 1 ≤ M' / m := (Nat.le_div_iff_mul_le hm0).mpr (by linarith)
      obtain ⟨hr0, hr1⟩ := roundoff_le hm0 hmM'
      have hmert := RHTower.Mertens.mertens_first (M' / m) hq
      rw [abs_div, abs_of_pos hm', div_eq_mul_one_div]
      by_cases hY : M' / m < Y
      · rw [if_pos hY]
        have hel : |e (M' / m) - r m| ≤ Ce + Real.log 2 := by
          have hr2 : r m ≤ Real.log 2 := by
            have := log_le_log_div_add_log hm0 hmM'; simp only [r]; linarith
          have hr0' : 0 ≤ r m := hr0
          have hmert' : |mertensSum (M' / m) - Real.log ((M' / m : ℕ) : ℝ)| ≤ Real.log 4 + 4 :=
            hmert
          have he' : e (M' / m) = mertensSum (M' / m) - Real.log ((M' / m : ℕ) : ℝ) + γ := rfl
          rw [he']
          simp only [Ce]
          rw [abs_le] at hmert' ⊢
          constructor <;> linarith
        have : 0 ≤ η / 2 * (1 / (m : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hel (by positivity : (0 : ℝ) ≤ 1 / m)]
      · rw [if_neg hY, add_zero]
        push Not at hY
        have hYq : Y₁ ≤ M' / m := (le_max_left _ _).trans hY
        have he : |e (M' / m)| ≤ η / 4 := by
          have := (hY₁ (M' / m) hYq).le
          rw [Real.dist_eq] at this
          simpa [e, sub_neg_eq_add, add_comm, add_left_comm, add_assoc] using this
        have hqY : (⌈4 / η⌉₊ + 1 : ℕ) ≤ M' / m := (le_max_right _ _).trans hY
        have hinv : 1 / ((M' / m : ℕ) : ℝ) ≤ η / 4 := by
          have h1 : (4 / η : ℝ) < ((M' / m : ℕ) : ℝ) := by
            have := Nat.le_ceil (4 / η)
            have h2 : ((⌈4 / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((M' / m : ℕ) : ℝ) := by exact_mod_cast hqY
            push_cast at h2
            linarith
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hη] at h1
          linarith
        have hel : |e (M' / m) - r m| ≤ η / 2 := by
          rw [abs_le] at he ⊢; constructor <;> linarith
        exact mul_le_mul_of_nonneg_right hel (by positivity)
    have hsmall : ∑ m ∈ Icc 1 M, (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0) ≤
        (Ce + Real.log 2) * Y := by
      -- each such `m` exceeds `M'/Y`, and there are at most `M ≤ M'` of them
      have hterm : ∀ m ∈ Icc 1 M, (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0) ≤
          (Ce + Real.log 2) * ((Y : ℝ) / M') := by
        intro m hm
        have hm0 : 0 < m := (mem_Icc.mp hm).1
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
        have hM' : (0 : ℝ) < M' := by exact_mod_cast (hm0.trans_le ((mem_Icc.mp hm).2.trans hMM'))
        split_ifs with hY
        · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          -- `M' < m (⌊M'/m⌋ + 1) ≤ m Y`
          have hlt := RHTower.Mertens.cast_div_lt M' m hm0
          have hYr : ((M' / m : ℕ) : ℝ) + 1 ≤ Y := by exact_mod_cast hY
          rw [div_lt_iff₀ hm'] at hlt
          rw [div_le_div_iff₀ hm' hM']
          nlinarith
        · positivity
      calc ∑ m ∈ Icc 1 M, (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0)
          ≤ ∑ m ∈ Icc 1 M, (Ce + Real.log 2) * ((Y : ℝ) / M') := sum_le_sum hterm
        _ = (Ce + Real.log 2) * (M * ((Y : ℝ) / M')) := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
        _ ≤ (Ce + Real.log 2) * Y := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hM' : (0 : ℝ) < M' := by exact_mod_cast (hM.trans hMM')
            rw [mul_div_assoc', div_le_iff₀ hM']
            have : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
            nlinarith [Nat.cast_nonneg (α := ℝ) Y]
    calc |∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m|
        ≤ ∑ m ∈ Icc 1 M, |(e (M' / m) - r m) / m| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Icc 1 M, (η / 2 * (1 / (m : ℝ)) +
            (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0)) := sum_le_sum hpt
      _ = η / 2 * harmonicSum M + ∑ m ∈ Icc 1 M,
            (if M' / m < Y then (Ce + Real.log 2) * (1 / (m : ℝ)) else 0) := by
          rw [sum_add_distrib, ← mul_sum]; rfl
      _ ≤ η / 2 * harmonicSum M + (Ce + Real.log 2) * Y := by linarith
  -- the Euler constant of `H_{M'}`
  have hEul : |harmonicSum M * (harmonicSum M' - Real.log M' - γ)| ≤
      η / 4 * harmonicSum M + 2 * (1 + Real.log M₀) := by
    rw [abs_mul, abs_of_nonneg hHM]
    by_cases hM'0 : M₀ ≤ M'
    · have := hM₀ M' hM'0
      rw [Real.dist_eq] at this
      have h : |harmonicSum M' - Real.log M' - γ| ≤ η / 4 := by
        rw [sub_sub]; rw [sub_sub] at this; exact this.le
      have : 0 ≤ 1 + Real.log M₀ := by
        have := Real.log_natCast_nonneg M₀; linarith
      nlinarith [mul_le_mul_of_nonneg_left h hHM]
    · push Not at hM'0
      have hb : |harmonicSum M' - Real.log M' - γ| ≤ 2 := by
        have h1 := log_le_harmonicSum M'
        have h2 := harmonicSum_le M'
        rw [abs_le]; constructor <;> linarith
      have hHM0 : harmonicSum M ≤ 1 + Real.log M₀ :=
        (harmonicSum_mono (hMM'.trans hM'0.le)).trans (harmonicSum_le M₀)
      nlinarith [mul_le_mul_of_nonneg_left hb hHM, abs_nonneg (harmonicSum M' - Real.log M' - γ)]
  have hident : primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M' +
      2 * γ * harmonicSum M = ∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m -
        harmonicSum M * (harmonicSum M' - Real.log M' - γ) := by
    rw [hB]; ring
  rw [hident]
  calc |∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m - harmonicSum M * (harmonicSum M' - Real.log M' - γ)|
      ≤ |∑ m ∈ Icc 1 M, (e (M' / m) - r m) / m| +
          |harmonicSum M * (harmonicSum M' - Real.log M' - γ)| := abs_sub _ _
    _ ≤ (η / 2 * harmonicSum M + (Ce + Real.log 2) * Y) +
          (η / 4 * harmonicSum M + 2 * (1 + Real.log M₀)) := add_le_add herr hEul
    _ ≤ η * harmonicSum M + ((Ce + Real.log 2) * Y + 2 * (1 + Real.log M₀)) := by nlinarith

/-! ### The finite part on step profiles -/

/-- **The finite part of the horizon renormalization is `−2γ`.** For every `η > 0` there is `C` such
that for every step profile on the orders `≤ N` with all `M_i ≥ 1`,
`|P_N(x) − ℓ(x)² + 2γ|x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)`. -/
theorem exists_abs_atomicWeilForm_stepProfile_finitePart_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (stepProfile c M) - polarFunctional N (stepProfile c M) ^ 2 +
          2 * γ * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C, hC⟩ := exists_abs_primeBilinear_truncPole_finitePart_le hη
  refine ⟨C, fun {k N} c M hM1 hM => ?_⟩
  have hpair : ∀ i j, |primeBilinear N (truncPole (M i)) (truncPole (M j)) -
      harmonicSum (M i) * harmonicSum (M j) + 2 * γ * harmonicSum (min (M i) (M j))| ≤
        η * harmonicSum (min (M i) (M j)) + C := by
    intro i j
    rcases le_total (M i) (M j) with h | h
    · rw [min_eq_left h]; exact hC _ _ _ (hM1 i) h (hM j)
    · rw [min_eq_right h, primeBilinear_comm, mul_comm (harmonicSum (M i))]
      exact hC _ _ _ (hM1 j) h (hM i)
  rw [atomicWeilForm_stepProfile, polarFunctional_stepProfile c M hM, sum_stepProfile_sq c M hM,
    sq, sum_mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  simp_rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hrw : c i * c j * primeBilinear N (truncPole (M i)) (truncPole (M j)) -
      c i * harmonicSum (M i) * (c j * harmonicSum (M j)) +
        2 * γ * (c i * c j * harmonicSum (min (M i) (M j))) =
      (c i * c j) * (primeBilinear N (truncPole (M i)) (truncPole (M j)) -
        harmonicSum (M i) * harmonicSum (M j) + 2 * γ * harmonicSum (min (M i) (M j))) := by ring
  rw [hrw, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hpair i j) (by positivity)

/-- **On the survival cone the finite part is the scalar `−2γ`**: for polar-neutral step profiles,
`|P_N(x) + 2γ|x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)`. -/
theorem exists_abs_atomicWeilForm_stepProfile_add_le_of_polar {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      polarFunctional N (stepProfile c M) = 0 →
      |atomicWeilForm N (stepProfile c M) + 2 * γ * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨C, fun {k N} c M hM1 hM hpolar => ?_⟩
  have h := hC c M hM1 hM
  rwa [hpolar, sq, mul_zero, sub_zero] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
