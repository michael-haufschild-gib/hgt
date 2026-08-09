import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower

/-!
# Boolean support of the ramification diagonal

Pulling the level-`m` shell back along `k ↦ k ^ m` returns the squarefree indicator: the
unitalised stream satisfies

`ã_m(k^m) = μ(k)²`.

Consequently the pulled-back support is the Boolean divisor lattice of a squarefree modulus and
repeated occupancy is inactive — a prime occurring twice in `k` produces exponent `2m`, where the
level-`m` stream vanishes.  The logarithmic coefficient operator recovers the clock
`E(k) = log k` from the same slice.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower ArithmeticFunction
open scoped Moebius

theorem shellIndicator_one {m : ℕ} (hm : m ≠ 0) : shellIndicator m 1 = 0 := by
  rcases shellIndicator_eq_zero_or_one m 1 with h | h
  · exact h
  · obtain ⟨-, hnot⟩ := (shellIndicator_eq_one_iff m 1).mp h
    exact absurd (mFree_one hm) hnot

/-- The unitalised shell stream. -/
noncomputable def unitalShellIndicator (m n : ℕ) : ℤ :=
  shellIndicator m n + (if n = 1 then 1 else 0)

theorem unitalShellIndicator_one {m : ℕ} (hm : m ≠ 0) : unitalShellIndicator m 1 = 1 := by
  rw [unitalShellIndicator, shellIndicator_one hm, if_pos rfl, zero_add]

theorem unitalShellIndicator_of_ne_one {m n : ℕ} (hn : n ≠ 1) :
    unitalShellIndicator m n = shellIndicator m n := by
  rw [unitalShellIndicator, if_neg hn, add_zero]

theorem one_lt_pow_of_one_lt {k m : ℕ} (hk : 1 < k) (hm : m ≠ 0) : 1 < k ^ m :=
  Nat.one_lt_pow hm hk

/-- **Exact squarefree pullback.**  `ã_m(k^m) = μ(k)²`. -/
theorem unitalShellIndicator_pow_self {m k : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) :
    unitalShellIndicator m (k ^ m) = (μ k) ^ 2 := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hk) with h1 | h1
  · have hk1 : k = 1 := h1.symm
    subst hk1
    rw [one_pow, unitalShellIndicator_one hm]
    simp
  · have hne : k ^ m ≠ 1 := (one_lt_pow_of_one_lt h1 hm).ne'
    rw [unitalShellIndicator_of_ne_one hne]
    by_cases hsq : Squarefree k
    · have h := (shellIndicator_pow_self_eq_one_iff hm hk).mpr ⟨hsq, h1.ne'⟩
      rw [h, moebius_apply_of_squarefree hsq]
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    · have h : shellIndicator m (k ^ m) = 0 := by
        rcases shellIndicator_eq_zero_or_one m (k ^ m) with h0 | h0
        · exact h0
        · exact absurd ((shellIndicator_pow_self_eq_one_iff hm hk).mp h0).1 hsq
      rw [h, moebius_eq_zero_of_not_squarefree hsq]
      simp

/-- **Hard-core exclusion.**  Repeated occupancy leaves the level-`m` shell. -/
theorem unitalShellIndicator_pow_self_eq_zero {m k p : ℕ} (hm : m ≠ 0) (hk : k ≠ 0)
    (hp : p.Prime) (hdvd : p ^ 2 ∣ k) : unitalShellIndicator m (k ^ m) = 0 := by
  have hsq : ¬ Squarefree k := by
    intro h
    have hpp : p * p ∣ k := by
      rw [← pow_two]
      exact hdvd
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (h p hpp))
  rw [unitalShellIndicator_pow_self hm hk, moebius_eq_zero_of_not_squarefree hsq]
  simp

theorem unitalShellIndicator_pow_self_eq_one_iff {m k : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) :
    unitalShellIndicator m (k ^ m) = 1 ↔ Squarefree k := by
  rw [unitalShellIndicator_pow_self hm hk]
  constructor
  · intro h
    by_contra hsq
    rw [moebius_eq_zero_of_not_squarefree hsq] at h
    simp at h
  · intro hsq
    rw [moebius_apply_of_squarefree hsq, ← pow_mul, mul_comm, pow_mul]
    simp

/-! ## The logarithmic coefficient clock -/

/-- The logarithmic coefficient operator `(L f)(n) = -(log n) f(n)`. -/
noncomputable def logCoeffOperator (f : ℕ → ℝ) (n : ℕ) : ℝ := -(Real.log n) * f n

/-- **Clock recovery.**  The source clock `E(k) = log k` is read off the ramification diagonal. -/
theorem logCoeffOperator_shell_clock {m k : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) (hsq : Squarefree k) :
    -(1 / (m : ℝ)) *
        logCoeffOperator (fun n => ((unitalShellIndicator m n : ℤ) : ℝ)) (k ^ m)
      = Real.log k := by
  have hval : ((unitalShellIndicator m (k ^ m) : ℤ) : ℝ) = 1 := by
    rw [(unitalShellIndicator_pow_self_eq_one_iff hm hk).mpr hsq]
    norm_num
  have hlog : Real.log ((k ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log k := by
    rw [Nat.cast_pow, Real.log_pow]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [logCoeffOperator, hval, hlog]
  field_simp

end HTGeometry.ConstraintFrameRelativity
