import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower
import GaloisForLFunctions.RHTower.HighExponentShellClockMeasure

/-!
# The literal Euler-shell vertical mode

The pure-prime skeleton reporter `h ↦ (h_{p^m})_p` annihilates the mixed shell atom `2^m · 3`,
because that integer lies in the level-`m` shell and is not a prime power.  Nevertheless the
normalised Mellin phase response of the same atom is not identically zero in time.

The mechanism is elementary.  If the response vanished for all `t`, the shell characteristic
function would equal a single pure phase `e^{-i t log N}`; taking real parts of
`∑ P(n) e^{-i t (log n - log N)} = 1` against `∑ P(n) = 1` forces every occupied atom to satisfy
`log n = log N`, so the shell would be a single point.  It is not: `2^m` and `2^m · 3` are two
distinct occupied atoms.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## Occupied atoms of the shell law -/

theorem shellProbability_pos {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) {n : ℕ}
    (hn : shellIndicator m n = 1) : 0 < shellProbability m σ n := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp at hn
  rw [shellProbability, shellMass, hn]
  have hpos : (0 : ℝ) < ((n : ℝ) ^ σ)⁻¹ := by
    have : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    positivity
  have := shellMellin_pos hm hσ
  positivity

theorem shellIndicator_two_pow_mul_three_self {m : ℕ} (hm : m ≠ 0) :
    shellIndicator m (2 ^ m * 3) = 1 :=
  shellIndicator_two_pow_mul_three hm

/-- **The skeleton reporter kills the mixed atom.**  `2^m · 3` is not a prime power. -/
theorem two_pow_mul_three_ne_prime_pow {m : ℕ} (hm : 2 ≤ m) (p : ℕ) (hp : p.Prime) :
    (2 ^ m * 3 : ℕ) ≠ p ^ m := by
  intro h
  have h3 : (2 ^ m * 3 : ℕ).factorization 3 = 1 := by
    rw [factorization_two_pow_mul_three_apply]
    norm_num
  have hpow : (p ^ m).factorization 3 = m * p.factorization 3 := factorization_pow_apply p m 3
  rw [h, hpow] at h3
  have hm1 : m ≤ 1 := Nat.le_of_dvd one_pos ⟨p.factorization 3, h3.symm⟩
  omega

/-! ## The shell characteristic function and the normalised response -/

/-- The characteristic function of the shell clock law. -/
noncomputable def shellCharFun (m : ℕ) (σ t : ℝ) : ℂ :=
  ∑' n : ℕ, (shellProbability m σ n : ℂ) * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)

/-- The normalised Mellin phase response of a single shell atom. -/
noncomputable def normalizedResponse (m : ℕ) (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (shellProbability m σ N : ℂ) *
    (Complex.exp ((-(t * Real.log N) : ℝ) * Complex.I) - shellCharFun m σ t)

theorem summable_shellPhase {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable fun n : ℕ =>
      (shellProbability m σ n : ℂ) * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I) := by
  refine Summable.of_norm ?_
  have hnorm : ∀ n : ℕ,
      ‖(shellProbability m σ n : ℂ) * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)‖
        = shellProbability m σ n := by
    intro n
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (shellProbability_nonneg hm hσ n)]
  simpa [hnorm] using (hasSum_shellProbability hm hσ).summable

/-- If the response vanishes identically then the shell law is concentrated at one atom. -/
theorem support_singleton_of_response_zero {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) {N : ℕ}
    (hN : shellIndicator m N = 1) (hzero : ∀ t : ℝ, normalizedResponse m σ N t = 0)
    {n : ℕ} (hn : shellIndicator m n = 1) : Real.log n = Real.log N := by
  have hPN := shellProbability_pos hm hσ hN
  have hPn := shellProbability_pos hm hσ hn
  -- the characteristic function is a single pure phase
  have hphase : ∀ t : ℝ,
      shellCharFun m σ t = Complex.exp ((-(t * Real.log N) : ℝ) * Complex.I) := by
    intro t
    have h := hzero t
    rw [normalizedResponse, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (by exact_mod_cast h) hPN.ne'
    · linarith [sub_eq_zero.mp h] <;> skip
  -- take real parts of the normalised identity
  have hkey : ∀ t : ℝ, ∑' k : ℕ,
      shellProbability m σ k * (1 - Real.cos (t * (Real.log k - Real.log N))) = 0 := by
    intro t
    have hsum1 : ∑' k : ℕ, shellProbability m σ k = 1 := (hasSum_shellProbability hm hσ).tsum_eq
    have hcos : ∑' k : ℕ,
        shellProbability m σ k * Real.cos (t * (Real.log k - Real.log N)) = 1 := by
      have hc := hphase t
      have hre : ((shellCharFun m σ t) *
          Complex.exp ((t * Real.log N : ℝ) * Complex.I)).re = 1 := by
        rw [hc, ← Complex.exp_add]
        norm_num
      have hexpand : (shellCharFun m σ t) * Complex.exp ((t * Real.log N : ℝ) * Complex.I)
          = ∑' k : ℕ, (shellProbability m σ k : ℂ) *
              Complex.exp ((t * (Real.log k - Real.log N) : ℝ) * Complex.I) := by
        rw [shellCharFun, tsum_mul_right]
        refine tsum_congr fun k => ?_
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [hexpand] at hre
      have hsummable : Summable fun k : ℕ => (shellProbability m σ k : ℂ) *
          Complex.exp ((t * (Real.log k - Real.log N) : ℝ) * Complex.I) := by
        refine Summable.of_norm ?_
        have hnorm : ∀ k : ℕ, ‖(shellProbability m σ k : ℂ) *
            Complex.exp ((t * (Real.log k - Real.log N) : ℝ) * Complex.I)‖
              = shellProbability m σ k := by
          intro k
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (shellProbability_nonneg hm hσ k)]
        simpa [hnorm] using (hasSum_shellProbability hm hσ).summable
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.map_tsum hsummable] at hre
      rw [← hre]
      refine tsum_congr fun k => ?_
      simp [Complex.reCLM_apply, Complex.exp_ofReal_mul_I_re]
    have hsub : ∑' k : ℕ,
        shellProbability m σ k * (1 - Real.cos (t * (Real.log k - Real.log N)))
        = (∑' k : ℕ, shellProbability m σ k)
          - ∑' k : ℕ, shellProbability m σ k * Real.cos (t * (Real.log k - Real.log N)) := by
      rw [← tsum_sub (hasSum_shellProbability hm hσ).summable]
      · refine tsum_congr fun k => ?_
        ring
      · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
          (hasSum_shellProbability hm hσ).summable
        · positivity
        · sorry
    rw [hsub, hsum1, hcos, sub_self]
  sorry

end HTGeometry.ConstraintFrameRelativity
