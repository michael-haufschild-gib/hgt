import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.HighBlockDualWeightVariation
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel

/-!
# The Mellin transform of a stencil

For a balanced stencil, with `D_c(s) = Σ c(k) k^{-s}`,

`D_c(s) ζ(s) = Σ_{r ≥ 1} g(r) (r^{-s} − (r + 1)^{-s})`,  `Re s > 0`, `s ≠ 1`.

The right side converges absolutely because `g` is bounded. The proof is elementary: partial sums
along multiples of a common period `L` are exact, since `g(qL) = 0` and `⌊qL/k⌋ = qL/k`, and the
polar parts `(qL/k)^{1-s}/(1-s)` cancel by balance.

**A producer is a mollifier on the line `Re s = 1`.** Subtract the window: the remainder has
nonnegative coefficients and total mass the excess `T`. So
`‖D_c(s) ζ(s) − m (1 − B^{-s})‖ ≤ ‖s‖ T` on `Re s = 1`, for free. This inverts `ζ` on `Re s = 1` by
a Dirichlet polynomial with integer coefficients, and proves `ζ(s) ≠ 0` as soon as `ε ‖s‖ < 1`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The Dirichlet polynomial `D_c(s) = Σ c(k) k^{-s}` of a stencil. -/
def dirichletPoly (c : ℕ →₀ ℤ) (s : ℂ) : ℂ :=
  ∑ k ∈ c.support, (c k : ℂ) * ((k : ℝ) : ℂ) ^ (-s)

/-- One step of the Abel kernel, `(j + 1)^{-s} − (j + 2)^{-s}`. -/
def abelStep (s : ℂ) (j : ℕ) : ℂ := (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((j : ℝ) + 2 : ℝ) : ℂ) ^ (-s)

/-- The real telescoping weight `(j + 1)^{-σ} − (j + 2)^{-σ}`. -/
def realStep (σ : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ (-σ) - ((j : ℝ) + 2) ^ (-σ)

theorem realStep_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (j : ℕ) : 0 ≤ realStep σ j := by
  have h : ((j : ℝ) + 2) ^ (-σ) ≤ ((j : ℝ) + 1) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [realStep]; linarith

/-- The partial sums of the real telescoping weight. -/
theorem sum_range_realStep (σ : ℝ) (n : ℕ) :
    ∑ j ∈ range n, realStep σ j = 1 - ((n : ℝ) + 1) ^ (-σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, realStep]
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    ring

theorem summable_realStep {σ : ℝ} (hσ : 0 ≤ σ) : Summable (realStep σ) := by
  refine summable_of_sum_range_le (c := 1) (realStep_nonneg hσ) fun n => ?_
  rw [sum_range_realStep]
  have : 0 ≤ ((n : ℝ) + 1) ^ (-σ) := by positivity
  linarith

/-- The Abel step in the telescoping form. -/
theorem norm_abelStep_le {s : ℂ} (hσ : 0 < s.re) (j : ℕ) :
    ‖abelStep s j‖ ≤ ‖s‖ * (realStep s.re j / s.re) := by
  have h := RHTower.norm_cpow_neg_sub_cpow_neg_le (w := s) hσ.ne' (A := (j : ℝ) + 1)
    (B := (j : ℝ) + 2) (by positivity) (by linarith)
  rw [abelStep, norm_sub_rev]
  exact h

/-- The Abel step in the pointwise form. -/
theorem norm_abelStep_le_rpow {s : ℂ} (hσ : 0 < s.re) (j : ℕ) :
    ‖abelStep s j‖ ≤ ‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1) := by
  have h := GaloisForLFunctions.RHTower.norm_cpow_unit_diff_le (w := s) hσ
    (x := (j : ℝ) + 1) (by positivity)
  rw [abelStep, show (j : ℝ) + 2 = (j : ℝ) + 1 + 1 by ring]
  exact h

/-- **Abel summation against the increment.** -/
theorem sum_range_mul_abelStep (c : ℕ →₀ ℤ) (s : ℂ) (N : ℕ) :
    ∑ j ∈ range N, (stepWeight c (j + 1) : ℂ) * abelStep s j =
      ∑ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
        (stepWeight c N : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, abelStep]
    have hs : (stepWeight c (N + 1) : ℂ) = stepWeight c N + increment c (N + 1) := by
      exact_mod_cast stepWeight_succ c N
    have hcast : (((N + 1 : ℕ) : ℝ) + 1 : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [hcast, hs]
    ring

/-- The sum over multiples of `k` factors through the partial sum at `N / k`. -/
theorem sum_range_dvd_cpow (s : ℂ) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∑ j ∈ range N, (if k ∣ j + 1 then (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) =
      ((k : ℝ) : ℂ) ^ (-s) * ∑ i ∈ Icc 1 (N / k), ((i : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_div]
    split_ifs with hd
    · rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      congr 1
      have hval : (N : ℝ) + 1 = (k : ℝ) * ((N / k + 1 : ℕ) : ℝ) := by
        obtain ⟨q, hq⟩ := hd
        have hq' : N / k + 1 = q := by
          have h1 : (N + 1) / k = q := by rw [hq]; exact Nat.mul_div_cancel_left q hk
          rw [Nat.succ_div, if_pos ⟨q, hq⟩] at h1
          exact h1
        rw [hq']
        exact_mod_cast hq
      rw [hval]
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (by positivity) _
    · simp

/-- **The increment sum in the partial sums of `ζ`.** -/
theorem sum_range_increment_mul_cpow (c : ℕ →₀ ℤ) (hc0 : c 0 = 0) (s : ℂ) (N : ℕ) :
    ∑ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
        ∑ i ∈ Icc 1 (N / k), ((i : ℝ) : ℂ) ^ (-s)) := by
  have hterm : ∀ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑ k ∈ c.support, (c k : ℂ) * (if k ∣ j + 1 then (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) := by
    intro j _
    rw [increment]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  rw [← mul_sum, sum_range_dvd_cpow s hk0 N]

/-- A common period, written for balanced stencils. -/
private lemma period_pos' {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) : 0 < IsProducer.period c :=
  prod_pos fun k hk => Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0

/-- `g(qL) = 0` on a common period. -/
private lemma stepWeight_mul_period {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (q : ℕ) :
    stepWeight c (q * IsProducer.period c) = 0 := by
  have h := stepWeight_periodic hc0 hbal (L := IsProducer.period c) IsProducer.dvd_period q 0
  rwa [add_zero, stepWeight_zero] at h

/-- The multiplicity of a balanced stencil is bounded by the coefficient mass. -/
theorem abs_stepWeight_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (r : ℕ) :
    |(stepWeight c r : ℝ)| ≤ coeffMass c := by
  rw [stepWeight_eq_sum_mod hc0 hbal, coeffMass]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hmod : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r hk0).le
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (r % k)), abs_div, abs_neg,
    abs_of_pos hkR, div_mul_eq_mul_div, div_le_iff₀ hkR]
  exact mul_le_mul_of_nonneg_left hmod (abs_nonneg _)

/-- The Mellin series converges absolutely for `Re s > 0`. -/
theorem summable_mellin {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {s : ℂ}
    (hσ : 0 < s.re) :
    Summable fun j : ℕ => (stepWeight c (j + 1) : ℂ) * abelStep s j := by
  refine Summable.of_norm_bounded
    (g := fun j => coeffMass c * (‖s‖ * (realStep s.re j / s.re))) ?_ fun j => ?_
  · exact (((summable_realStep hσ.le).div_const _).mul_left _).mul_left _
  · rw [norm_mul]
    have h1 : ‖(stepWeight c (j + 1) : ℂ)‖ ≤ coeffMass c := by
      rw [Complex.norm_intCast]
      exact abs_stepWeight_le hc0 hbal (j + 1)
    exact mul_le_mul h1 (norm_abelStep_le hσ j) (norm_nonneg _) (coeffMass_nonneg c)

/-- The polar parts of the partial sums cancel on multiples of the period. -/
private lemma sum_polar_eq_zero {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {s : ℂ}
    {N : ℕ} (hN : 0 < N) (hL : ∀ k ∈ c.support, k ∣ N) :
    ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
      (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s)) = 0 := by
  have hterm : ∀ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
      (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s)) =
      (((N : ℝ) : ℂ) ^ (1 - s)) * (((c k : ℝ) / k : ℝ) : ℂ) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hkC : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hkR.ne'
    have hNk : (N : ℝ) = (k : ℝ) * ((N / k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hL k hk)).symm
    have hmul : ((N : ℝ) : ℂ) ^ (1 - s) =
        ((k : ℝ) : ℂ) ^ (1 - s) * (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s) := by
      rw [hNk]
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) _
    have hpow : ((k : ℝ) : ℂ) ^ (1 - s) = ((k : ℝ) : ℂ) * ((k : ℝ) : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hkC, Complex.cpow_one]
    rw [hmul, hpow]
    push_cast
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  have hb : ∑ k ∈ c.support, (((c k : ℝ) / k : ℝ) : ℂ) = 0 := by
    have : ((∑ k ∈ c.support, (c k : ℝ) / k : ℝ) : ℂ) = 0 := by
      rw [show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hbal]; simp
    simpa using this
  rw [hb, mul_zero]

/-- **The Mellin transform of a stencil.** For a balanced stencil, `Re s > 0`, `s ≠ 1`,
`Σ_{r ≥ 1} g(r) (r^{-s} − (r + 1)^{-s}) = D_c(s) ζ(s)`. -/
theorem hasSum_mellin {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun j : ℕ => (stepWeight c (j + 1) : ℂ) * abelStep s j)
      (dirichletPoly c s * riemannZeta s) := by
  have hsum := summable_mellin hc0 hbal hσ
  have hL := period_pos' hc0
  set L := IsProducer.period c with hLdef
  have hdvd : ∀ k ∈ c.support, k ∣ L := IsProducer.dvd_period
  -- The partial sums along multiples of the period.
  have hpart : ∀ q : ℕ, 1 ≤ q →
      ∑ j ∈ range (q * L), (stepWeight c (j + 1) : ℂ) * abelStep s j =
        ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
          ((∑ i ∈ Icc 1 (q * L / k), ((i : ℝ) : ℂ) ^ (-s)) -
            (((q * L / k : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s))) := by
    intro q hq
    have hNpos : 0 < q * L := Nat.mul_pos hq hL
    rw [sum_range_mul_abelStep, stepWeight_mul_period hc0 hbal q, sum_range_increment_mul_cpow c hc0]
    have hpolar := sum_polar_eq_zero (s := s) hc0 hbal hNpos
      (fun k hk => (hdvd k hk).trans (Nat.dvd_mul_left L q))
    have hexp : ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
          ((∑ i ∈ Icc 1 (q * L / k), ((i : ℝ) : ℂ) ^ (-s)) -
            (((q * L / k : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s))) =
        ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
          ∑ i ∈ Icc 1 (q * L / k), ((i : ℝ) : ℂ) ^ (-s)) -
        (∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
          (((q * L / k : ℕ) : ℝ) : ℂ) ^ (1 - s))) / (1 - s) := by
      rw [sum_div, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [hexp, hpolar, zero_div, sub_zero]
    simp
  -- The limit of each column is `ζ(s)`.
  have hzeta := RHTower.tendsto_sum_cpow_sub_pow hσ hs1
  have hcol : ∀ k ∈ c.support, Tendsto (fun q : ℕ => (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
      ((∑ i ∈ Icc 1 (q * L / k), ((i : ℝ) : ℂ) ^ (-s)) -
        (((q * L / k : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s))))
      atTop (𝓝 ((c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) * riemannZeta s))) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hmono : Tendsto (fun q : ℕ => q * L / k) atTop atTop := by
      refine tendsto_atTop_mono (f := id) (fun q => ?_) tendsto_id
      obtain ⟨d, hd⟩ := hdvd k hk
      have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by
        rw [h, mul_zero] at hd; omega
      have : q * L / k = q * d := by
        rw [hd, show q * (k * d) = k * (q * d) by ring, Nat.mul_div_cancel_left _ hk0]
      rw [this]
      exact Nat.le_mul_of_pos_right q hd0
    exact ((hzeta.comp hmono).const_mul _).const_mul _
  have hlim : Tendsto (fun q : ℕ => ∑ j ∈ range (q * L), (stepWeight c (j + 1) : ℂ) * abelStep s j)
      atTop (𝓝 (dirichletPoly c s * riemannZeta s)) := by
    have hdp : dirichletPoly c s * riemannZeta s =
        ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) * riemannZeta s) := by
      rw [dirichletPoly, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [hdp]
    refine (tendsto_finset_sum _ hcol).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with q hq
    exact (hpart q hq).symm
  have hmul : Tendsto (fun q : ℕ => q * L) atTop atTop :=
    tendsto_id.atTop_mul_const' hL |> fun h => by simpa using h
  have htsum := (hsum.hasSum.tendsto_sum_nat).comp hmul
  have heq := tendsto_nhds_unique htsum hlim
  rw [← heq]
  exact hsum.hasSum

/-- The Abel kernel telescopes over the window. -/
theorem sum_range_abelStep (s : ℂ) (n : ℕ) :
    ∑ j ∈ range n, abelStep s j = 1 - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, abelStep]
    have hcast : (((n + 1 : ℕ) : ℝ) + 1 : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    ring

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- The multiplicity above the window, `g(r) − m 1_{r<B}`, as a real weight. -/
def tailWeight (c : ℕ →₀ ℤ) (m B j : ℕ) : ℝ :=
  (stepWeight c (j + 1) : ℝ) - (if j + 1 < B then (m : ℝ) else 0)

theorem tailWeight_eq (c : ℕ →₀ ℤ) (m B j : ℕ) :
    tailWeight c m B j = excessTerm m B c j * (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  rw [tailWeight, excessTerm, div_mul_cancel₀]
  positivity

theorem tailWeight_nonneg (hP : IsProducer c m B) (j : ℕ) : 0 ≤ tailWeight c m B j := by
  rw [tailWeight_eq]
  exact mul_nonneg (hP.excessTerm_nonneg j) (by positivity)

theorem tailWeight_le_peak (hP : IsProducer c m B) (j : ℕ) :
    tailWeight c m B j ≤ peak c := by
  have h : (stepWeight c (j + 1) : ℝ) ≤ peak c := by exact_mod_cast hP.stepWeight_le_peak (j + 1)
  have hm := hP.m_pos
  have hite : (0 : ℝ) ≤ if j + 1 < B then (m : ℝ) else 0 := by
    split_ifs
    · exact hm.le
    · exact le_rfl
  rw [tailWeight]
  linarith

/-- **The window split.** `D_c(s) ζ(s) − m (1 − B^{-s})` is the tail series. -/
theorem hasSum_tail (hP : IsProducer c m B) {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun j : ℕ => ((tailWeight c m B j : ℝ) : ℂ) * abelStep s j)
      (dirichletPoly c s * riemannZeta s - (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))) := by
  have hB := hP.two_le_B
  have hwin : HasSum (fun j : ℕ => (((if j + 1 < B then (m : ℝ) else 0 : ℝ)) : ℂ) * abelStep s j)
      ((m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))) := by
    have hfin : ∑ j ∈ range (B - 1), (((if j + 1 < B then (m : ℝ) else 0 : ℝ)) : ℂ) * abelStep s j =
        (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s)) := by
      have hcast : (((B - 1 : ℕ) : ℝ) + 1 : ℝ) = B := by
        have : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this]; ring
      rw [← hcast, ← sum_range_abelStep, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [if_pos (by have := mem_range.mp hj; omega)]
      simp
    rw [← hfin]
    refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
    rw [if_neg (by
      have := mem_range.not.mp hj
      omega)]
    simp
  have h := (hasSum_mellin hP.zero hP.balanced hσ hs1).sub hwin
  have hfun : (fun j : ℕ => ((tailWeight c m B j : ℝ) : ℂ) * abelStep s j) = fun j : ℕ =>
      (stepWeight c (j + 1) : ℂ) * abelStep s j -
        (((if j + 1 < B then (m : ℝ) else 0 : ℝ)) : ℂ) * abelStep s j := by
    funext j
    rw [tailWeight, ← sub_mul]
    push_cast
    rfl
  rw [hfun]
  exact h

/-- At `σ = 1` the real weight is the pronic weight. -/
theorem realStep_one (j : ℕ) : realStep 1 j = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  rw [realStep, Real.rpow_neg_one, Real.rpow_neg_one]
  field_simp
  ring

/-- **A producer is a mollifier on the line `Re s = 1`.** On that line, `s ≠ 1`,
`‖D_c(s) ζ(s) − m (1 − B^{-s})‖ ≤ ‖s‖ T`, `T` the excess of the slope. -/
theorem norm_mollifier_le (hP : IsProducer c m B) {s : ℂ} (hσ : s.re = 1) (hs1 : s ≠ 1) :
    ‖dirichletPoly c s * riemannZeta s - (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))‖ ≤
      ‖s‖ * excess c m B := by
  have hσ0 : 0 < s.re := by rw [hσ]; norm_num
  have htail := hP.hasSum_tail hσ0 hs1
  have hterm : ∀ j : ℕ, ‖((tailWeight c m B j : ℝ) : ℂ) * abelStep s j‖ ≤
      ‖s‖ * excessTerm m B c j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP.tailWeight_nonneg j)]
    have h := norm_abelStep_le hσ0 j
    rw [hσ, div_one, realStep_one] at h
    calc tailWeight c m B j * ‖abelStep s j‖
        ≤ tailWeight c m B j * (‖s‖ * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) :=
          mul_le_mul_of_nonneg_left h (hP.tailWeight_nonneg j)
      _ = ‖s‖ * excessTerm m B c j := by
          rw [tailWeight_eq]
          field_simp
  have hsum := (hP.hasSum_excess.mul_left ‖s‖)
  exact (norm_hasSum_le_of_le hterm htail hsum)

/-- The window factor stays away from zero: `‖1 − B^{-s}‖ ≥ 1 − B^{-σ}`. -/
theorem one_sub_rpow_le_norm (hP : IsProducer c m B) (s : ℂ) :
    1 - (B : ℝ) ^ (-s.re) ≤ ‖1 - ((B : ℝ) : ℂ) ^ (-s)‖ := by
  have hB : (0 : ℝ) < B := by have := hP.one_lt_B; linarith
  have h := norm_sub_norm_le (1 : ℂ) (((B : ℝ) : ℂ) ^ (-s))
  rw [norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hB, Complex.neg_re] at h
  exact h

/-- **Certified non-vanishing on `Re s = 1`.** If `ε ‖s‖ < 1`, then `ζ(s) ≠ 0`, and
`‖D_c(s)‖ ‖ζ(s)‖ ≥ m (1 − 1/B) (1 − ε ‖s‖)`. -/
theorem le_norm_dirichletPoly_mul_zeta (hP : IsProducer c m B) {s : ℂ} (hσ : s.re = 1)
    (hs1 : s ≠ 1) :
    (m : ℝ) * (1 - 1 / (B : ℝ)) * (1 - rate c m B * ‖s‖) ≤ ‖dirichletPoly c s‖ * ‖riemannZeta s‖ := by
  have hmol := hP.norm_mollifier_le hσ hs1
  have hwin := hP.one_sub_rpow_le_norm s
  rw [hσ, Real.rpow_neg_one, ← one_div] at hwin
  have hex := hP.excess_eq_rate
  have hm := hP.m_pos
  have hW : (m : ℝ) * (1 - 1 / (B : ℝ)) ≤ ‖(m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))‖ := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hwin hm.le
  have htri : ‖(m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))‖ ≤ ‖dirichletPoly c s * riemannZeta s‖ +
      ‖dirichletPoly c s * riemannZeta s - (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))‖ := by
    have := norm_sub_le (dirichletPoly c s * riemannZeta s)
      (dirichletPoly c s * riemannZeta s - (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s)))
    rwa [sub_sub_cancel] at this
  rw [← norm_mul]
  rw [hex] at hmol
  have hid : (m : ℝ) * (1 - 1 / (B : ℝ)) * (1 - rate c m B * ‖s‖) =
      (m : ℝ) * (1 - 1 / (B : ℝ)) - ‖s‖ * ((m : ℝ) * (1 - 1 / (B : ℝ)) * rate c m B) := by ring
  rw [hid]
  linarith

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
