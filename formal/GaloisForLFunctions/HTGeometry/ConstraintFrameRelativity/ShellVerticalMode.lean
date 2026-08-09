import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower
import GaloisForLFunctions.RHTower.HighExponentShellClockMeasure

/-!
# The literal Euler-shell vertical mode

The pure-prime skeleton reporter `h ↦ (h_{p^m})_p` annihilates the mixed shell atom `2^m · 3`,
because that integer lies in the level-`m` shell and is not a prime power.  Nevertheless the
normalised Mellin phase response of the same atom is not identically zero in time.

The mechanism is elementary.  If the response vanished for all `t`, the shell characteristic
function would be a single pure phase `e^{-i t log N}`; taking real parts of
`∑ P(n) e^{i t (log N - log n)} = 1` against `∑ P(n) = 1` forces every occupied atom to satisfy
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
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hZ := shellMellin_pos hm hσ
  rw [shellProbability, shellMass, hn]
  have hpos : (0 : ℝ) < ((n : ℝ) ^ σ)⁻¹ := by positivity
  positivity

/-- **The skeleton reporter kills the mixed atom.**  `2^m · 3` is not a prime power. -/
theorem two_pow_mul_three_ne_prime_pow {m : ℕ} (hm : 2 ≤ m) (p : ℕ) :
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

/-- A phase-weighted shell series is summable. -/
theorem summable_shellPhase {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (c : ℕ → ℝ) :
    Summable fun n : ℕ =>
      (shellProbability m σ n : ℂ) * Complex.exp ((c n : ℝ) * Complex.I) := by
  refine Summable.of_norm ?_
  have hnorm : ∀ n : ℕ,
      ‖(shellProbability m σ n : ℂ) * Complex.exp ((c n : ℝ) * Complex.I)‖
        = shellProbability m σ n := by
    intro n
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (shellProbability_nonneg hm hσ n)]
  exact (hasSum_shellProbability hm hσ).summable.congr fun n => (hnorm n).symm

/-- The characteristic function of the shell clock law. -/
noncomputable def shellCharFun (m : ℕ) (σ t : ℝ) : ℂ :=
  ∑' n : ℕ, (shellProbability m σ n : ℂ) * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)

/-- The normalised Mellin phase response of a single shell atom. -/
noncomputable def normalizedResponse (m : ℕ) (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (shellProbability m σ N : ℂ) *
    (Complex.exp ((-(t * Real.log N) : ℝ) * Complex.I) - shellCharFun m σ t)

theorem hasSum_shellCharFun {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasSum (fun n : ℕ => (shellProbability m σ n : ℂ) *
      Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) (shellCharFun m σ t) :=
  (summable_shellPhase hm hσ fun n => -(t * Real.log n)).hasSum

/-! ## The vanishing response forces a single atom -/

/-- If the normalised response of an occupied atom vanishes for all times, every occupied atom has
the same logarithm. -/
theorem log_eq_of_response_zero {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) {N : ℕ}
    (hN : shellIndicator m N = 1) (hzero : ∀ t : ℝ, normalizedResponse m σ N t = 0)
    {n : ℕ} (hn : shellIndicator m n = 1) : Real.log n = Real.log N := by
  have hPN := shellProbability_pos hm hσ hN
  have hPn := shellProbability_pos hm hσ hn
  have hphase : ∀ t : ℝ,
      shellCharFun m σ t = Complex.exp ((-(t * Real.log N) : ℝ) * Complex.I) := by
    intro t
    have h := hzero t
    rw [normalizedResponse, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (by exact_mod_cast h : shellProbability m σ N = 0) hPN.ne'
    · exact (sub_eq_zero.mp h).symm
  have hcos : ∀ t : ℝ, HasSum
      (fun k : ℕ => shellProbability m σ k * Real.cos (t * (Real.log N - Real.log k))) 1 := by
    intro t
    have hbase := (hasSum_shellCharFun hm hσ t).mul_right
      (Complex.exp ((t * Real.log N : ℝ) * Complex.I))
    rw [hphase t, ← Complex.exp_add] at hbase
    have hone : Complex.exp (((-(t * Real.log N) : ℝ) : ℂ) * Complex.I
        + ((t * Real.log N : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← add_mul]
      push_cast
      ring_nf
      simp
    rw [hone] at hbase
    have hfun : ∀ k : ℕ,
        (shellProbability m σ k : ℂ) * Complex.exp ((-(t * Real.log k) : ℝ) * Complex.I) *
            Complex.exp ((t * Real.log N : ℝ) * Complex.I)
          = (shellProbability m σ k : ℂ) *
            Complex.exp ((t * (Real.log N - Real.log k) : ℝ) * Complex.I) := by
      intro k
      rw [mul_assoc, ← Complex.exp_add, ← add_mul]
      congr 2
      push_cast
      ring
    rw [funext hfun] at hbase
    have hre := Complex.hasSum_re hbase
    have hre' : ∀ k : ℕ,
        ((shellProbability m σ k : ℂ) *
          Complex.exp ((t * (Real.log N - Real.log k) : ℝ) * Complex.I)).re
        = shellProbability m σ k * Real.cos (t * (Real.log N - Real.log k)) := by
      intro k
      rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    rw [funext hre'] at hre
    simpa using hre
  have hdiff : ∀ t : ℝ, HasSum
      (fun k : ℕ => shellProbability m σ k
        - shellProbability m σ k * Real.cos (t * (Real.log N - Real.log k))) 0 := by
    intro t
    have h := (hasSum_shellProbability hm hσ).sub (hcos t)
    simpa using h
  have hzero' : ∀ t : ℝ, ∀ k : ℕ,
      shellProbability m σ k
        - shellProbability m σ k * Real.cos (t * (Real.log N - Real.log k)) = 0 := by
    intro t
    have hnn : ∀ k : ℕ, (0 : ℝ) ≤ shellProbability m σ k
        - shellProbability m σ k * Real.cos (t * (Real.log N - Real.log k)) := by
      intro k
      have hc := Real.cos_le_one (t * (Real.log N - Real.log k))
      have hp := shellProbability_nonneg hm hσ k
      nlinarith
    have := (hasSum_zero_iff_of_nonneg hnn).mp (hdiff t)
    intro k
    exact congrFun this k
  by_contra hne
  set d : ℝ := Real.log N - Real.log n with hd
  have hd0 : d ≠ 0 := by
    intro h
    exact hne (by linarith [sub_eq_zero.mp h])
  have hc := hzero' (Real.pi / d) n
  have hval : Real.pi / d * (Real.log N - Real.log n) = Real.pi := by
    rw [← hd]
    field_simp
  rw [hval, Real.cos_pi] at hc
  nlinarith [hPn]

/-! ## The vertical mode -/

/-- **The prime skeleton does not predict the full-shell response.**  The mixed atom `2^m · 3` is
invisible to the pure-prime reporter, yet its normalised phase response is nonzero at some time. -/
theorem shell_vertical_mode {m : ℕ} (hm : 2 ≤ m) {σ : ℝ} (hσ : 1 < σ) :
    (∀ p : ℕ, (2 ^ m * 3 : ℕ) ≠ p ^ m)
      ∧ ∃ t : ℝ, normalizedResponse m σ (2 ^ m * 3) t ≠ 0 := by
  have hm0 : m ≠ 0 := by omega
  refine ⟨two_pow_mul_three_ne_prime_pow hm, ?_⟩
  by_contra hall
  have hall' : ∀ t : ℝ, normalizedResponse m σ (2 ^ m * 3) t = 0 := by
    intro t
    by_contra ht
    exact hall ⟨t, ht⟩
  have hN : shellIndicator m (2 ^ m * 3) = 1 := shellIndicator_two_pow_mul_three hm0
  have hn : shellIndicator m (2 ^ m) = 1 := shellIndicator_two_pow m
  have hlog := log_eq_of_response_zero hm0 hσ hN hall' hn
  have h2 : (0 : ℝ) < ((2 : ℕ) ^ m : ℕ) := by positivity
  have h3 : (0 : ℝ) < ((2 ^ m * 3 : ℕ) : ℝ) := by positivity
  have heq : ((2 ^ m : ℕ) : ℝ) = ((2 ^ m * 3 : ℕ) : ℝ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr h2) (Set.mem_Ioi.mpr h3) hlog
  push_cast at heq
  nlinarith [heq, pow_pos (show (0 : ℝ) < 2 by norm_num) m]

end HTGeometry.ConstraintFrameRelativity
