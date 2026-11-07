import GaloisForLFunctions.PrimeTorusTheory.TheCornersOfTheOrbit
import GaloisForLFunctions.PrimeTorusTheory.UniqueFactorizationPaysForNonAlignment
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# The rank law and the test systems

Everything in this programme is about the rank of the steps. This module runs the test systems.

* **Rank one** (curves, Golden, commensurable steps). All steps are integer multiples of one `ℓ₀`.
  The orbit is periodic with period `τ = 2π/ℓ₀`, whatever the number of steps and the weights (`defect_period`), so exact returns
  have positive density and there is no saving against size at any height (`column_period_eq_size`). The oscillating energy at a period
  is the full positive count (`shiftedEnergy_period`), and the window of the finite-time Bohr isometry is one period
  (`exists_time_cos_eq_one`). Distinct products collide (`tupleStep_eq_of_coeff_sum_eq`), so `le_of_aligned` has no content.
* **Finite rank** (`exists_return_of_rank`). If the steps are integer combinations of `r` numbers, a return of precision `2πB/Q` occurs by
  time `Q^r`, independently of the number of steps. Time to reach depends on the rank, not on the size of the system.
* **The integers.** The steps `log p` have infinite rank (`not_isRankOne_log`, and `le_of_aligned`), and the first return of precision
  `t y^{−k}/2k` is not available before the pigeonhole.
* **Continuous systems** (`tendsto_continuousColumn`, `exists_defect_ge`). A Beurling system with a density has no torus: its column tends to `0`
  by Riemann–Lebesgue, so the defect tends to the size and the orbit never returns. Non-alignment is automatic there, and continuous systems
  with an off-line zero exist. So non-alignment alone never decides the critical line, and an argument must also use the amplitude.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- All steps are integer multiples of `ℓ₀`. -/
def IsRankOne (ℓ₀ : ℝ) : Prop := ∀ i, ∃ n : ℤ, S.step i = n * ℓ₀

variable {S}

/-- **The rank one orbit is periodic**: every multiple of `2π/ℓ₀` is an exact return. -/
theorem defect_period {ℓ₀ : ℝ} (h : S.IsRankOne ℓ₀) (hℓ₀ : ℓ₀ ≠ 0) (m : ℤ) :
    S.defect (m * (2 * Real.pi / ℓ₀)) = 0 := by
  rw [defect_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨n, hn⟩ := h i
  have e : (m : ℝ) * (2 * Real.pi / ℓ₀) * S.step i = ((m * n : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hn]
    push_cast
    field_simp
  rw [e, Real.cos_int_mul_two_pi]
  simp

/-- At rank one there is no saving against size at any height. -/
theorem column_period_eq_size {ℓ₀ : ℝ} (h : S.IsRankOne ℓ₀) (hℓ₀ : ℓ₀ ≠ 0) (m : ℤ) :
    S.column (m * (2 * Real.pi / ℓ₀)) = S.size := by
  have := defect_period h hℓ₀ m
  unfold defect at this
  linarith

/-- In every window of length one period there is an exact return. -/
theorem exists_exact_return {ℓ₀ : ℝ} (h : S.IsRankOne ℓ₀) (hℓ₀ : 0 < ℓ₀) (T : ℝ) :
    ∃ t ∈ Set.Icc T (T + 2 * Real.pi / ℓ₀), S.column t = S.size := by
  have hτ : 0 < 2 * Real.pi / ℓ₀ := by have := Real.pi_pos; positivity
  refine ⟨(⌈T / (2 * Real.pi / ℓ₀)⌉ : ℤ) * (2 * Real.pi / ℓ₀), ⟨?_, ?_⟩,
    column_period_eq_size h hℓ₀.ne' _⟩
  · have := Int.le_ceil (T / (2 * Real.pi / ℓ₀))
    rwa [div_le_iff₀ hτ] at this
  · have := Int.ceil_lt_add_one (T / (2 * Real.pi / ℓ₀))
    have h2 := mul_lt_mul_of_pos_right this hτ
    rw [add_mul, one_mul, div_mul_cancel₀ _ hτ.ne'] at h2
    linarith

/-- The step of a tuple on a rank one system is an integer multiple of `ℓ₀`. -/
theorem exists_tupleStep_eq {ℓ₀ : ℝ} (h : S.IsRankOne ℓ₀) {k : ℕ} (u : Fin k → ι) :
    ∃ n : ℤ, S.tupleStep u = n * ℓ₀ := by
  choose c hc using h
  refine ⟨∑ s, c (u s), ?_⟩
  unfold tupleStep
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => hc _

/-- **At rank one, products collide.** Tuples with the same coefficient sum have the same step. -/
theorem tupleStep_eq_of_coeff_sum_eq {ℓ₀ : ℝ} {c : ι → ℤ} (hc : ∀ i, S.step i = c i * ℓ₀) {k : ℕ}
    {u v : Fin k → ι} (h : ∑ s, c (u s) = ∑ s, c (v s)) : S.tupleStep u = S.tupleStep v := by
  unfold tupleStep
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  exact_mod_cast h

/-- **The oscillating energy at a period is the full positive count.** At rank one nothing cancels at a return. -/
theorem shiftedEnergy_period [DecidableEq ι] {ℓ₀ : ℝ} (h : S.IsRankOne ℓ₀) (hℓ₀ : ℓ₀ ≠ 0) (k : ℕ)
    (m : ℤ) (H : ℝ) : S.shiftedEnergy k (m * (2 * Real.pi / ℓ₀)) H = S.energy k H := by
  unfold shiftedEnergy energy
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  obtain ⟨a, ha⟩ := exists_tupleStep_eq h u
  obtain ⟨b, hb⟩ := exists_tupleStep_eq h v
  have e : (m : ℝ) * (2 * Real.pi / ℓ₀) * (S.tupleStep u - S.tupleStep v) =
      ((m * (a - b) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [ha, hb]
    push_cast
    field_simp
  rw [e, Real.cos_int_mul_two_pi, mul_one]

end PhaseSystem

/-- **Kronecker at rank one.** A single phase hits every target exactly within one period. -/
theorem exists_time_cos_eq_one {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (T θ : ℝ) :
    ∃ t ∈ Set.Icc T (T + 2 * Real.pi / ℓ₀), Real.cos (t * ℓ₀ - θ) = 1 := by
  have hpi := Real.pi_pos
  have hτ : 0 < 2 * Real.pi / ℓ₀ := by positivity
  set m : ℤ := ⌈(T * ℓ₀ - θ) / (2 * Real.pi)⌉ with hm
  refine ⟨(θ + m * (2 * Real.pi)) / ℓ₀, ⟨?_, ?_⟩, ?_⟩
  · rw [le_div_iff₀ hℓ₀]
    have := Int.le_ceil ((T * ℓ₀ - θ) / (2 * Real.pi))
    rw [div_le_iff₀ (by positivity)] at this
    rw [← hm] at this
    linarith
  · rw [div_le_iff₀ hℓ₀]
    have := Int.ceil_lt_add_one ((T * ℓ₀ - θ) / (2 * Real.pi))
    rw [← hm] at this
    have h2 := mul_lt_mul_of_pos_right this (by positivity : 0 < 2 * Real.pi)
    rw [add_mul, one_mul, div_mul_cancel₀ _ (by positivity)] at h2
    have e : (T + 2 * Real.pi / ℓ₀) * ℓ₀ = T * ℓ₀ + 2 * Real.pi := by
      field_simp
    rw [e]
    linarith
  · have e : (θ + m * (2 * Real.pi)) / ℓ₀ * ℓ₀ - θ = m * (2 * Real.pi) := by
      field_simp
      ring
    rw [e, Real.cos_int_mul_two_pi]

/-- **Finite rank.** If the steps are integer combinations of `r` numbers with coefficients of total size `≤ B`, a return of
precision `2πB/Q` occurs by time `Q^r`, whatever the number of steps. -/
theorem exists_return_of_rank {ι : Type*} {r : ℕ} (β : Fin r → ℝ) (c : ι → Fin r → ℤ) (ℓ : ι → ℝ)
    (hℓ : ∀ i, ℓ i = ∑ j, (c i j : ℝ) * β j) {B : ℝ} (hB : ∀ i, ∑ j, |(c i j : ℝ)| ≤ B) {Q : ℕ}
    (hQ : 0 < Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ r ∧ ∀ i, ∃ m : ℤ, |(q : ℝ) * ℓ i - 2 * Real.pi * m| ≤
      2 * Real.pi * B / Q := by
  have hpi := Real.pi_pos
  obtain ⟨q, hq1, hq2, hq⟩ := HTGeometry.exists_simultaneous_dirichlet
    (fun j => β j / (2 * Real.pi)) hQ
  refine ⟨q, hq1, hq2, fun i => ?_⟩
  choose p hp using hq
  refine ⟨∑ j, c i j * p j, ?_⟩
  have e : (q : ℝ) * ℓ i - 2 * Real.pi * ((∑ j, c i j * p j : ℤ) : ℝ) =
      ∑ j, (c i j : ℝ) * (2 * Real.pi) * ((q : ℝ) * (β j / (2 * Real.pi)) - p j) := by
    rw [hℓ i]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin r)),
      |(c i j : ℝ) * (2 * Real.pi) * ((q : ℝ) * (β j / (2 * Real.pi)) - p j)| ≤
        |(c i j : ℝ)| * (2 * Real.pi / Q) := by
    intro j _
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := (hp j).le
    calc
      2 * Real.pi * |(q : ℝ) * (β j / (2 * Real.pi)) - p j| ≤ 2 * Real.pi * (1 / Q) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Real.pi / Q := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  calc
    (∑ j, |(c i j : ℝ)|) * (2 * Real.pi / Q) ≤ B * (2 * Real.pi / Q) :=
      mul_le_mul_of_nonneg_right (hB i) (by positivity)
    _ = 2 * Real.pi * B / Q := by ring

/-- **The integers are not rank one.** The logarithms of two distinct primes are not integer multiples of a common number. -/
theorem not_isRankOne_log {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ℓ₀ : ℝ) :
    ¬ ((∃ a : ℤ, Real.log p = a * ℓ₀) ∧ ∃ b : ℤ, Real.log q = b * ℓ₀) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hℓ0 : ℓ₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ha
    linarith
  -- Both coefficients have the same sign; reduce to positive ones.
  have hrel : (b : ℝ) * Real.log p = a * Real.log q := by
    rw [ha, hb]
    ring
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at ha
    linarith
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at hb
    linarith
  have habs : (b.natAbs : ℝ) * Real.log p = a.natAbs * Real.log q := by
    have h1 := congrArg abs hrel
    rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at h1
    simpa [Nat.cast_natAbs] using h1
  have hpow : (p : ℝ) ^ b.natAbs = (q : ℝ) ^ a.natAbs := by
    have h1 : Real.log ((p : ℝ) ^ b.natAbs) = Real.log ((q : ℝ) ^ a.natAbs) := by
      rw [Real.log_pow, Real.log_pow]
      exact habs
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h1
  have hnat : p ^ b.natAbs = q ^ a.natAbs := by exact_mod_cast hpow
  have hdvd : p ∣ q ^ a.natAbs := by
    rw [← hnat]
    exact dvd_pow_self p (Int.natAbs_ne_zero.mpr hb0)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-! ### Continuous systems have no torus -/

/-- The column of a continuous system with density `w`. -/
def continuousColumn (w : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, w x * Real.cos (t * x)

/-- **No return.** The column of a continuous system tends to `0` at large height (Riemann–Lebesgue). -/
theorem tendsto_continuousColumn {w : ℝ → ℝ} (hw : MeasureTheory.Integrable w) :
    Tendsto (continuousColumn w) atTop (𝓝 0) := by
  have hpi := Real.pi_pos
  have hRL := Real.tendsto_integral_exp_smul_cocompact (fun x => (w x : ℂ))
  have hmap : Tendsto (fun t : ℝ => t / (2 * Real.pi)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have hcomp := Complex.continuous_re.tendsto _ |>.comp (hRL.comp hmap)
  rw [Complex.zero_re] at hcomp
  refine hcomp.congr fun t => ?_
  simp only [Function.comp]
  set y := t / (2 * Real.pi) with hy
  have e : ∀ v : ℝ, Real.fourierChar (-(v * y)) • (w v : ℂ) =
      Complex.exp (((2 * Real.pi * -(v * y) : ℝ) : ℂ) * Complex.I) * (w v : ℂ) := by
    intro v
    rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  simp_rw [e]
  have hint : MeasureTheory.Integrable fun v : ℝ =>
      Complex.exp (((2 * Real.pi * -(v * y) : ℝ) : ℂ) * Complex.I) * (w v : ℂ) := by
    refine MeasureTheory.Integrable.mono' hw.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ hw.ofReal.aestronglyMeasurable
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
  unfold continuousColumn
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Complex.reCLM_apply]
  rw [mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have e2 : 2 * Real.pi * -(v * y) = -(t * v) := by
    rw [hy]
    field_simp
  rw [e2, Real.cos_neg]

/-- A continuous system of positive mass stays away from alignment at all large heights. -/
theorem exists_defect_ge {w : ℝ → ℝ} (hw : MeasureTheory.Integrable w) (hS : 0 < ∫ x, w x) :
    ∃ T₀ : ℝ, ∀ t, T₀ ≤ t → (∫ x, w x) / 2 ≤ (∫ x, w x) - continuousColumn w t := by
  have hev := (tendsto_continuousColumn hw).eventually (gt_mem_nhds (half_pos hS))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨T₀, fun t ht => ?_⟩
  have := hT₀ t ht
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
