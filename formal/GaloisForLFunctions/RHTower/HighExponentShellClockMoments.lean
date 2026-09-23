import GaloisForLFunctions.RHTower.HighExponentShellSourcePole
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Critical clock moments of a high-exponent shell

Under the Gibbs probability `P_{m,σ}(n) = a_m(n) n^{-σ} / S_m(σ)` the clock is `H = log n`.  Its
`k`-th moment is the `k`-th normalised derivative ratio of the shell source, so the pole structure
of `HighExponentShellSourcePole` computes the critical limits:

* `RHTower.tendsto_shellLogMoment_one` — `(σ-1)·E[H] → 1`;
* `RHTower.tendsto_shellLogMoment_two` — `(σ-1)²·E[H²] → 2`;
* `RHTower.tendsto_shellClockVariance` — the rescaled clock has asymptotic variance one;
* `RHTower.tendsto_shellProjectiveFisherEnergy` — the projective Fisher tangent of every
  high-exponent shell carries exactly four asymptotic energy units.

These are the unit-rate exponential moments, so the four-unit budget is the same for every shell
`m ≥ 12`, on pairwise disjoint arithmetic supports.
-/

noncomputable section

namespace RHTower

open Complex Filter LSeries
open scoped Topology LSeries.notation

/-! ## Summability and the abscissa of the shell coefficient -/

theorem LSeriesSummable_shellIndicator (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(shellIndicator m) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
  rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> simp

theorem abscissaOfAbsConv_shellIndicator_lt (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv ↗(shellIndicator m) < (s.re : EReal) := by
  have hr : 1 < (1 + s.re) / 2 := by linarith
  have hrs : (1 + s.re) / 2 < s.re := by linarith
  have hsum : LSeriesSummable ↗(shellIndicator m) (((1 + s.re) / 2 : ℝ) : ℂ) :=
    LSeriesSummable_shellIndicator m (by simpa using hr)
  refine lt_of_le_of_lt hsum.abscissaOfAbsConv_le ?_
  simpa using hrs

/-! ## The shell source is the L-series of the shell indicator -/

theorem ofReal_shellMellin {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    ((shellMellin m σ : ℝ) : ℂ) = shellSource m (σ : ℂ) := by
  have h1 : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
  have hcast : ((∑' n : ℕ, (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ : ℝ) : ℂ)
      = LSeries ↗(shellIndicator m) (σ : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.ofReal_natCast, div_eq_mul_inv]
      push_cast
      ring
  rw [shellMellin_eq_tsum hm hσ, hcast, LSeries_shellIndicator hm h1, shellSource]

theorem LSeries_shellIndicator_eventuallyEq_shellSource (m : ℕ) (hm : m ≠ 0) {s : ℂ}
    (hs : 1 < s.re) : LSeries ↗(shellIndicator m) =ᶠ[𝓝 s] shellSource m := by
  have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hopen] with z hz
  exact LSeries_shellIndicator hm hz

/-! ## The logarithmic moments -/

/-- The `k`-th logarithmic clock moment of the normalised shell mass. -/
def shellLogMoment (m k : ℕ) (σ : ℝ) : ℝ :=
  (∑' n : ℕ, (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ * (Real.log n) ^ k) / shellMellin m σ

private theorem iterate_logMul_shellIndicator (m k n : ℕ) :
    (logMul^[k] ↗(shellIndicator m)) n = Complex.log n ^ k * ((shellIndicator m n : ℤ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change Complex.log n * (logMul^[k] ↗(shellIndicator m)) n = _
      rw [ih]
      ring

private theorem term_iterate_logMul_shellIndicator (m k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] ↗(shellIndicator m)) (σ : ℂ) n
      = (((shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ * (Real.log n) ^ k : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term]
  · rw [term_of_ne_zero hn.ne', iterate_logMul_shellIndicator,
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.ofReal_natCast,
      Complex.ofReal_pow, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast,
      div_eq_mul_inv]
    push_cast
    ring

private theorem ofReal_shellLogMomentNumerator (m k : ℕ) (σ : ℝ) :
    ((∑' n : ℕ, (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ * (Real.log n) ^ k : ℝ) : ℂ)
      = LSeries (logMul^[k] ↗(shellIndicator m)) (σ : ℂ) := by
  rw [Complex.ofReal_tsum, LSeries]
  exact tsum_congr fun n => (term_iterate_logMul_shellIndicator m k σ n).symm

/-- Every logarithmic clock moment of the shell is the corresponding normalised derivative ratio
of the analytic shell source. -/
theorem ofReal_shellLogMoment {m : ℕ} (hm : m ≠ 0) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ((shellLogMoment m k σ : ℝ) : ℂ)
      = (-1 : ℂ) ^ k * iteratedDeriv k (shellSource m) (σ : ℂ) / shellSource m (σ : ℂ) := by
  have h1 : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
  have habs := abscissaOfAbsConv_shellIndicator_lt m h1
  have hiter := LSeries_iteratedDeriv (f := ↗(shellIndicator m)) k habs
  rw [(LSeries_shellIndicator_eventuallyEq_shellSource m hm h1).iteratedDeriv_eq k] at hiter
  rw [shellLogMoment, Complex.ofReal_div, ofReal_shellLogMomentNumerator,
    ofReal_shellMellin hm hσ]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  congr 1
  calc LSeries (logMul^[k] ↗(shellIndicator m)) (σ : ℂ)
      = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * LSeries (logMul^[k] ↗(shellIndicator m)) (σ : ℂ) := by
        rw [hsign, one_mul]
    _ = (-1 : ℂ) ^ k * iteratedDeriv k (shellSource m) (σ : ℂ) := by
        rw [hiter]; ring

/-! ## The critical limits -/

private theorem tendsto_ofReal_nhdsGT_one_nhdsNE :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  have hbase : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.continuousAt).tendsto
    rw [Complex.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨hbase, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have hre : σ = 1 := by
    have := congrArg Complex.re h
    simpa using this
  rw [hre] at hσ
  exact lt_irrefl 1 (Set.mem_Ioi.mp hσ)

private theorem tendsto_ofReal_of_tendsto_ofReal {f : ℝ → ℝ} {l : Filter ℝ} {c : ℝ}
    (h : Tendsto (fun σ : ℝ => ((f σ : ℝ) : ℂ)) l (𝓝 ((c : ℝ) : ℂ))) :
    Tendsto f l (𝓝 c) := by
  have hre := ((Complex.continuous_re.continuousAt).tendsto).comp h
  simpa using! hre

/-- **First critical clock moment of the shell.**  `(σ-1)·E[log n] → 1` as `σ ↓ 1`. -/
theorem tendsto_shellLogMoment_one {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun σ : ℝ => (σ - 1) * shellLogMoment m 1 σ) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hcomplex := (tendsto_shellSource_logDeriv hm).comp tendsto_ofReal_nhdsGT_one_nhdsNE
  refine tendsto_ofReal_of_tendsto_ofReal (c := 1) ?_
  rw [Complex.ofReal_one]
  refine hcomplex.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : 1 < σ := Set.mem_Ioi.mp hσ
  have hmom := ofReal_shellLogMoment (m := m) (by omega) 1 hσ1
  rw [pow_one, iteratedDeriv_one] at hmom
  simp only [Function.comp_apply]
  rw [Complex.ofReal_mul, hmom, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- **Second critical clock moment of the shell.**  `(σ-1)²·E[(log n)²] → 2` as `σ ↓ 1`. -/
theorem tendsto_shellLogMoment_two {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun σ : ℝ => (σ - 1) ^ (2 : ℕ) * shellLogMoment m 2 σ) (𝓝[>] (1 : ℝ)) (𝓝 2) := by
  have hcomplex := (tendsto_shellSource_secondDeriv hm).comp tendsto_ofReal_nhdsGT_one_nhdsNE
  refine tendsto_ofReal_of_tendsto_ofReal (c := 2) ?_
  rw [show (((2 : ℝ)) : ℂ) = 2 by norm_num]
  refine hcomplex.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : 1 < σ := Set.mem_Ioi.mp hσ
  have hmom := ofReal_shellLogMoment (m := m) (by omega) 2 hσ1
  have hiter2 : iteratedDeriv 2 (shellSource m) (σ : ℂ)
      = deriv (deriv (shellSource m)) (σ : ℂ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter2] at hmom
  simp only [Function.comp_apply]
  rw [Complex.ofReal_mul, Complex.ofReal_pow, hmom, Complex.ofReal_sub, Complex.ofReal_one]
  norm_num

/-- The variance of the rescaled shell clock. -/
def shellClockVariance (m : ℕ) (σ : ℝ) : ℝ :=
  (σ - 1) ^ (2 : ℕ) * shellLogMoment m 2 σ - ((σ - 1) * shellLogMoment m 1 σ) ^ (2 : ℕ)

/-- **The rescaled shell clock has asymptotic variance one** — the variance of `Exp(1)`. -/
theorem tendsto_shellClockVariance {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellClockVariance m) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have h := (tendsto_shellLogMoment_two hm).sub ((tendsto_shellLogMoment_one hm).pow 2)
  have hval : (2 : ℝ) - 1 ^ (2 : ℕ) = 1 := by norm_num
  rw [hval] at h
  exact h

/-- The projective Fisher energy of the shell source. -/
def shellProjectiveFisherEnergy (m : ℕ) (σ : ℝ) : ℝ := 4 * shellClockVariance m σ

/-- **Four units.**  The projective Fisher tangent of every high-exponent shell carries exactly
four asymptotic critical energy units — the same budget as the squarefree Möbius source, on a
disjoint arithmetic support. -/
theorem tendsto_shellProjectiveFisherEnergy {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellProjectiveFisherEnergy m) (𝓝[>] (1 : ℝ)) (𝓝 4) := by
  have h := (tendsto_shellClockVariance hm).const_mul (4 : ℝ)
  rw [mul_one] at h
  exact h

end RHTower
