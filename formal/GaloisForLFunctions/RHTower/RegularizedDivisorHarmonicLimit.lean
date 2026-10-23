import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# The regularized divisor-harmonic limit

For a coefficient sequence `a : ℕ → ℝ` put `f = 1 * a` in the Dirichlet sense, i.e.
`f k = ∑_{d ∣ k} a d`.  This file proves the general regularization law

```text
∑_{k ≤ N} f(k)/k  −  (∑_d a_d/d) · log N
   →  γ · (∑_d a_d/d)  −  ∑_d (a_d/d) · log d
```

under two hypotheses that are easy to check in the arithmetic applications:

* `Summable (fun d => |a d| * (1 + log d) / d)` — absolute convergence with one logarithm to spare;
* `(∑_{d ≤ N} |a d|)/N → 0` — subliner growth of the coefficient mass.

The mechanism is the finite Dirichlet hyperbola `∑_{k ≤ N} f(k)/k = ∑_{d ≤ N} (a_d/d) H_{⌊N/d⌋}`
followed by the sharp floor-harmonic comparison
`|H_{⌊N/d⌋} − log(N/d) − γ| ≤ 4d/N` (`abs_harmonic_sub_log_div_le`).

This is a reusable regularization device.  It is the analytic engine behind the γ-affine structure
of the generalized Stieltjes structure constants: every finite-support multi-index lane is a
divisor-supported sum of exactly this shape.
-/

open Finset Filter Topology

namespace RHTower
namespace RegularizedDivisorHarmonic

noncomputable section

/-- Reindexing `Icc 1 N` as `range N` shifted by one. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, g i = ∑ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

lemma harmonic_cast_eq_sum (n : ℕ) : (harmonic n : ℝ) = ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  ring

/-- Sharp comparison of a floor-harmonic number with the real logarithm of the exact quotient. -/
theorem abs_harmonic_sub_log_div_le {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |(harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d) - Real.eulerMascheroniConstant|
      ≤ 4 * d / N := by
  set m := N / d with hm
  have hd0 : 0 < d := hd
  have hm1 : 1 ≤ m := (Nat.one_le_div_iff hd0).mpr hdN
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  -- the two floor inequalities
  have hlow : (m : ℝ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ hdR]
    have : m * d ≤ N := Nat.div_mul_le_self N d
    exact_mod_cast this
  have hhigh : (N : ℝ) / d < (m : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR]
    have h : N < (m + 1) * d := (Nat.div_lt_iff_lt_mul hd0).mp (Nat.lt_succ_self m)
    have : ((N : ℝ)) < ((m + 1 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  -- harmonic estimate
  have h1 : |(harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant| ≤ 1 / m :=
    HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hm1
  -- logarithm comparison
  have h2 : |Real.log ((N : ℝ) / d) - Real.log m| ≤ 1 / m := by
    have hge : Real.log (m : ℝ) ≤ Real.log ((N : ℝ) / d) :=
      Real.log_le_log hmpos hlow
    have hle : Real.log ((N : ℝ) / d) - Real.log m ≤ 1 / m := by
      have hratio : Real.log ((N : ℝ) / d) - Real.log m
          = Real.log (((N : ℝ) / d) / m) := by
        rw [Real.log_div (by positivity) (ne_of_gt hmpos)]
      rw [hratio]
      have hbound : ((N : ℝ) / d) / m ≤ 1 + 1 / m := by
        rw [div_le_iff₀ hmpos]
        have : (1 + 1 / (m:ℝ)) * m = m + 1 := by field_simp
        rw [this]
        linarith
      calc Real.log (((N : ℝ) / d) / m) ≤ Real.log (1 + 1 / m) :=
            Real.log_le_log (by positivity) hbound
        _ ≤ 1 / m := by
            have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (m:ℝ)) (by positivity)
            linarith
    rw [abs_le]
    constructor
    · linarith [hle]
    · exact hle
  -- combine
  have hsum : |(harmonic m : ℝ) - Real.log ((N : ℝ) / d) - Real.eulerMascheroniConstant|
      ≤ 2 / m := by
    have hsplit : (harmonic m : ℝ) - Real.log ((N : ℝ) / d) - Real.eulerMascheroniConstant
        = ((harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant)
          - (Real.log ((N : ℝ) / d) - Real.log m) := by ring
    rw [hsplit]
    have := abs_sub ((harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant)
      (Real.log ((N : ℝ) / d) - Real.log m)
    have hfinal : |((harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant)
        - (Real.log ((N : ℝ) / d) - Real.log m)| ≤ 1 / m + 1 / m :=
      le_trans (abs_sub _ _) (add_le_add h1 h2)
    calc _ ≤ 1 / (m:ℝ) + 1 / m := hfinal
      _ = 2 / m := by ring
  -- 1/m ≤ 2d/N
  have hinv : (1 : ℝ) / m ≤ 2 * d / N := by
    have hNlt : (N : ℝ) < ((m : ℝ) + 1) * d := by
      have h := hhigh
      rw [div_lt_iff₀ hdR] at h
      exact h
    have hbound : (N : ℝ) ≤ 2 * (m : ℝ) * d := by nlinarith
    rw [div_le_div_iff₀ hmpos hNR]
    nlinarith [hbound]
  calc |(harmonic m : ℝ) - Real.log ((N : ℝ) / d) - Real.eulerMascheroniConstant|
      ≤ 2 / (m:ℝ) := hsum
    _ = 2 * (1 / m) := by ring
    _ ≤ 2 * (2 * d / N) := by linarith
    _ = 4 * d / N := by ring

/-- Real form of the multiple-reindexing identity. -/
theorem sum_inv_multiples_eq_harmonic (N d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), ((n : ℝ))⁻¹) =
      ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) := by
  rw [harmonic_cast_eq_sum, Finset.mul_sum]
  refine (Finset.sum_bij' (fun k _ => d * k) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk ⊢
    refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega), Nat.div_le_div_right hnN⟩
  · intro k _hk
    exact Nat.mul_div_cancel_left k (by omega)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k _hk
    simp [Nat.cast_mul]
    ring

/-- **Finite Dirichlet hyperbola with the reciprocal kernel, real form.** -/
theorem divisorSummatory_reciprocal_harmonic (N : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ * ∑ d ∈ n.divisors, a d := by
  symm
  calc
    (∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ * ∑ d ∈ n.divisors, a d) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, ((n : ℝ))⁻¹ * a d := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), ((n : ℝ))⁻¹ * a d := by
      rw [Finset.sum_comm']
      intro n d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
        exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdn) hnN⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _⟩
        exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩
    _ = ∑ d ∈ Finset.Icc 1 N, a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      calc
        (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), ((n : ℝ))⁻¹ * a d) =
            (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), ((n : ℝ))⁻¹) * a d := by
              rw [Finset.sum_mul]
        _ = a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) := by
          rw [sum_inv_multiples_eq_harmonic N d hd1]
          ring

/-! ### The regularization law -/

/-- The logarithmically weighted absolute coefficient mass. -/
def logWeight (a : ℕ → ℝ) (d : ℕ) : ℝ := |a d| * (1 + Real.log d) / d

lemma logWeight_nonneg (a : ℕ → ℝ) (d : ℕ) : 0 ≤ logWeight a d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [logWeight, h]
  · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    have : 0 ≤ Real.log d := Real.log_nonneg h1
    unfold logWeight
    positivity

/-- The regularized coefficient density `∑_d a_d/d`. -/
def coeffDensity (a : ℕ → ℝ) : ℝ := ∑' d : ℕ, a d / d

/-- The regularized log-lane coefficient mass `∑_d (a_d/d)·log d`. -/
def coeffLogMass (a : ℕ → ℝ) : ℝ := ∑' d : ℕ, (a d / d) * Real.log d

variable {a : ℕ → ℝ}

lemma summable_coeffDensity (h1 : Summable (logWeight a)) : Summable (fun d : ℕ => a d / d) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_) h1
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h, logWeight]
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    have hlog : 0 ≤ Real.log d := Real.log_nonneg hd1
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (le_of_lt hdpos)]
    unfold logWeight
    rw [div_le_div_iff_of_pos_right hdpos]
    nlinarith [abs_nonneg (a d)]

lemma summable_coeffLogMass (h1 : Summable (logWeight a)) :
    Summable (fun d : ℕ => (a d / d) * Real.log d) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_) h1
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h, logWeight]
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    have hlog : 0 ≤ Real.log d := Real.log_nonneg hd1
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (le_of_lt hdpos),
      abs_of_nonneg hlog]
    unfold logWeight
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hdpos]
    nlinarith [abs_nonneg (a d)]

/-- The two-lane model summand at cutoff `N`. -/
def modelSummand (a : ℕ → ℝ) (N d : ℕ) : ℝ :=
  (a d / d) * (Real.log N + Real.eulerMascheroniConstant - Real.log d)

lemma modelSummand_zero (N : ℕ) : modelSummand a N 0 = 0 := by
  simp [modelSummand]

lemma summable_modelSummand (h1 : Summable (logWeight a)) (N : ℕ) :
    Summable (modelSummand a N) := by
  have hrep : ∀ d : ℕ, modelSummand a N d
      = (Real.log N + Real.eulerMascheroniConstant) * (a d / d)
        - (a d / d) * Real.log d := by
    intro d
    rw [modelSummand]
    ring
  rw [show modelSummand a N = fun d : ℕ =>
      (Real.log N + Real.eulerMascheroniConstant) * (a d / d) - (a d / d) * Real.log d
    from funext hrep]
  exact ((summable_coeffDensity h1).mul_left _).sub (summable_coeffLogMass h1)

lemma tsum_modelSummand (h1 : Summable (logWeight a)) (N : ℕ) :
    ∑' d, modelSummand a N d
      = coeffDensity a * (Real.log N + Real.eulerMascheroniConstant) - coeffLogMass a := by
  have hrep : ∀ d : ℕ, modelSummand a N d
      = (Real.log N + Real.eulerMascheroniConstant) * (a d / d)
        - (a d / d) * Real.log d := by
    intro d
    rw [modelSummand]
    ring
  rw [show modelSummand a N = fun d : ℕ =>
      (Real.log N + Real.eulerMascheroniConstant) * (a d / d) - (a d / d) * Real.log d
    from funext hrep]
  rw [Summable.tsum_sub ((summable_coeffDensity h1).mul_left _) (summable_coeffLogMass h1),
    tsum_mul_left]
  rw [coeffDensity, coeffLogMass]
  ring

/-- The explicit error majorant of the regularization. -/
def regError (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  4 * (∑ d ∈ Finset.Icc 1 N, |a d|) / N
    + (2 + |Real.eulerMascheroniConstant|) * ∑' i : ℕ, logWeight a (i + (N + 1))

lemma abs_regDefect_le (h1 : Summable (logWeight a)) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / k)
        - ∑' d, modelSummand a N d| ≤ regError a N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := hN
    exact_mod_cast this
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  -- hyperbola
  have hhyp : (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / k)
      = ∑ d ∈ Finset.Icc 1 N, a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) := by
    rw [divisorSummatory_reciprocal_harmonic N a]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_eq_inv_mul]
  -- split the model tsum
  have hsm := summable_modelSummand h1 N
  have hsplit : ∑' d, modelSummand a N d
      = (∑ d ∈ Finset.Icc 1 N, modelSummand a N d)
        + ∑' i : ℕ, modelSummand a N (i + (N + 1)) := by
    rw [← hsm.sum_add_tsum_nat_add (N + 1)]
    congr 1
    rw [Finset.sum_range_succ' (modelSummand a N) N, modelSummand_zero, add_zero]
    exact (sum_Icc_one_eq_sum_range (modelSummand a N) N).symm
  rw [hhyp, hsplit]
  have hmain : (∑ d ∈ Finset.Icc 1 N, a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ))
      - ((∑ d ∈ Finset.Icc 1 N, modelSummand a N d)
        + ∑' i : ℕ, modelSummand a N (i + (N + 1)))
      = (∑ d ∈ Finset.Icc 1 N,
          (a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) - modelSummand a N d))
        - ∑' i : ℕ, modelSummand a N (i + (N + 1)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hmain]
  refine le_trans (abs_sub _ _) ?_
  refine add_le_add ?_ ?_
  · -- the head
    have hterm : ∀ d ∈ Finset.Icc 1 N,
        |a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) - modelSummand a N d|
          ≤ 4 * |a d| / N := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        have : (0 : ℕ) < d := hd1
        exact_mod_cast this
      have hlogd : Real.log N - Real.log d = Real.log ((N : ℝ) / (d : ℝ)) := by
        rw [Real.log_div (ne_of_gt hNR) (ne_of_gt hdpos)]
      have hrw : a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) - modelSummand a N d
          = (a d / d) * ((harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
            - Real.eulerMascheroniConstant) := by
        rw [modelSummand, ← hlogd, div_eq_mul_inv]
        ring
      rw [hrw, abs_mul, abs_div, abs_of_nonneg (le_of_lt hdpos)]
      calc |a d| / (d : ℝ) *
            |(harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
              - Real.eulerMascheroniConstant|
          ≤ |a d| / (d : ℝ) * (4 * (d : ℝ) / N) :=
            mul_le_mul_of_nonneg_left (abs_harmonic_sub_log_div_le hd1 hdN) (by positivity)
        _ = 4 * |a d| / N := by field_simp
    calc |∑ d ∈ Finset.Icc 1 N,
            (a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) - modelSummand a N d)|
        ≤ ∑ d ∈ Finset.Icc 1 N,
            |a d * ((d : ℝ))⁻¹ * (harmonic (N / d) : ℝ) - modelSummand a N d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, 4 * |a d| / N := Finset.sum_le_sum hterm
      _ = 4 * (∑ d ∈ Finset.Icc 1 N, |a d|) / N := by
          rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
  · -- the tail
    have hsummableTail : Summable (fun i : ℕ => |modelSummand a N (i + (N + 1))|) :=
      (((summable_nat_add_iff (N + 1)).mpr hsm)).abs
    have hsummableBound : Summable
        (fun i : ℕ => (2 + |Real.eulerMascheroniConstant|) * logWeight a (i + (N + 1))) :=
      (((summable_nat_add_iff (N + 1)).mpr h1)).mul_left _
    have hterm : ∀ i : ℕ, |modelSummand a N (i + (N + 1))|
        ≤ (2 + |Real.eulerMascheroniConstant|) * logWeight a (i + (N + 1)) := by
      intro i
      set d := i + (N + 1) with hd
      have hd1 : 1 ≤ d := by omega
      have hdN : N ≤ d := by omega
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        have : (0 : ℕ) < d := hd1
        exact_mod_cast this
      have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1R
      have hlogle : Real.log N ≤ Real.log d := by
        refine Real.log_le_log hNR ?_
        exact_mod_cast hdN
      have hfactor : |Real.log N + Real.eulerMascheroniConstant - Real.log d|
          ≤ (2 + |Real.eulerMascheroniConstant|) * (1 + Real.log d) := by
        have hb1 : |Real.log N + Real.eulerMascheroniConstant - Real.log d|
            ≤ |Real.log N + Real.eulerMascheroniConstant| + |Real.log d| := abs_sub _ _
        have hb2 : |Real.log N + Real.eulerMascheroniConstant|
            ≤ Real.log N + |Real.eulerMascheroniConstant| := by
          calc |Real.log N + Real.eulerMascheroniConstant|
              ≤ |Real.log N| + |Real.eulerMascheroniConstant| := abs_add_le _ _
            _ = Real.log N + |Real.eulerMascheroniConstant| := by
                rw [abs_of_nonneg hlogN]
        have hb3 : |Real.log d| = Real.log d := abs_of_nonneg hlogd
        have hga : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
        linarith [mul_nonneg hga hlogd]
      rw [modelSummand, abs_mul, abs_div, abs_of_nonneg (le_of_lt hdpos), logWeight]
      calc |a d| / (d : ℝ) * |Real.log N + Real.eulerMascheroniConstant - Real.log d|
          ≤ |a d| / (d : ℝ) * ((2 + |Real.eulerMascheroniConstant|) * (1 + Real.log d)) :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = (2 + |Real.eulerMascheroniConstant|) * (|a d| * (1 + Real.log d) / (d : ℝ)) := by
            field_simp
    calc |∑' i : ℕ, modelSummand a N (i + (N + 1))|
        ≤ ∑' i : ℕ, |modelSummand a N (i + (N + 1))| := by
          have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => modelSummand a N (i + (N + 1)))
            (by simpa [Real.norm_eq_abs] using hsummableTail)
          simpa [Real.norm_eq_abs] using h
      _ ≤ ∑' i : ℕ, (2 + |Real.eulerMascheroniConstant|) * logWeight a (i + (N + 1)) :=
          Summable.tsum_le_tsum hterm hsummableTail hsummableBound
      _ = (2 + |Real.eulerMascheroniConstant|) * ∑' i : ℕ, logWeight a (i + (N + 1)) :=
          tsum_mul_left

lemma tendsto_regError (_h1 : Summable (logWeight a))
    (h2 : Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, |a d|) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => regError a N) atTop (𝓝 0) := by
  have hhead : Tendsto (fun N : ℕ => 4 * (∑ d ∈ Finset.Icc 1 N, |a d|) / N) atTop (𝓝 0) := by
    have := h2.const_mul (4 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun N => ?_
    rw [mul_div_assoc]
  have htailbase : Tendsto (fun M : ℕ => ∑' i : ℕ, logWeight a (i + M)) atTop (𝓝 0) :=
    tendsto_sum_nat_add (logWeight a)
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := Filter.tendsto_add_atTop_nat 1
  have htail : Tendsto (fun N : ℕ =>
      (2 + |Real.eulerMascheroniConstant|) * ∑' i : ℕ, logWeight a (i + (N + 1)))
      atTop (𝓝 0) := by
    have := (htailbase.comp hshift).const_mul (2 + |Real.eulerMascheroniConstant|)
    simpa using this
  simpa [regError] using hhead.add htail

/-- **The regularized divisor-harmonic limit.**  If the coefficient sequence has an absolutely
convergent logarithmically weighted mass and sublinear absolute mass, then the reciprocal sum of
its divisor transform is `(∑_d a_d/d) log N` plus a finite limit, and the finite part is exactly
`γ·(∑_d a_d/d) − ∑_d (a_d/d) log d`. -/
theorem tendsto_regularizedDivisorHarmonic (h1 : Summable (logWeight a))
    (h2 : Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, |a d|) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / k)
        - coeffDensity a * Real.log N)
      atTop (𝓝 (coeffDensity a * Real.eulerMascheroniConstant - coeffLogMass a)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_regError h1 h2)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hkey : (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / k)
      - coeffDensity a * Real.log N
      - (coeffDensity a * Real.eulerMascheroniConstant - coeffLogMass a)
      = (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / k)
        - ∑' d, modelSummand a N d := by
    rw [tsum_modelSummand h1 N]
    ring
  rw [Real.norm_eq_abs, hkey]
  exact abs_regDefect_le h1 hN

end

end RegularizedDivisorHarmonic
end RHTower
