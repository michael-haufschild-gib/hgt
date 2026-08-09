import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity

/-!
# Phase-orbit invariance and lifted dilation under a ramification power event

For a finite prime aperture the shell of depth `m` carries the diagonal generator
`D_m e_p = m log p` and the unitary flow `U_m(t) e_p = e^{-i t m log p}`, with marked lift
`h_m(t) = -t m λ`.  A power event `m ↦ r m` dilates all three:

`D_{rm} = r D_m`,   `U_{rm}(t) = U_m(r t)`,   `h_{rm}(t) = r h_m(t)`,

so the observed orbit set is unchanged, `𝒪_{rm} = 𝒪_m`, while a fixed external clock sees an exact
dilation; compensating the clock by `t ↦ t/r` identifies the lifted paths.

At fixed clock the two representations are not conjugate: the generator traces differ, and the
centred spectral variance scales by `r²`.  The common orbit is dense in the torus by rational
independence of the prime logarithms, so there are arbitrarily large return times, while the
marked lift escapes linearly.

A positively `q`-homogeneous cost dilates by `r^q` at fixed clock and by `r^{q-1}` after clock
compensation.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset GaloisForLFunctions

variable {F : Finset Nat.Primes}

/-! ## Generator, flow and lift -/

/-- The prime clock of the aperture. -/
noncomputable def primeClockVec (F : Finset Nat.Primes) (p : F) : ℝ :=
  Real.log ((p : Nat.Primes) : ℕ)

/-- The diagonal generator at shell depth `m`. -/
noncomputable def shellGenerator (m : ℕ) (p : F) : ℝ := (m : ℝ) * primeClockVec F p

/-- The unitary phase flow at shell depth `m`. -/
noncomputable def shellFlow (m : ℕ) (t : ℝ) (p : F) : ℂ :=
  Complex.exp ((-(t * shellGenerator m p) : ℝ) * Complex.I)

/-- The marked universal-cover lift at shell depth `m`. -/
noncomputable def shellLift (m : ℕ) (t : ℝ) (p : F) : ℝ := -(t * shellGenerator m p)

theorem primeClockVec_pos (p : F) : 0 < primeClockVec F p := by
  have h : (1 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) := by
    exact_mod_cast (p : Nat.Primes).2.one_lt
  exact Real.log_pos h

/-- **Generator dilation.** -/
theorem shellGenerator_mul (m r : ℕ) (p : F) :
    shellGenerator (r * m) p = (r : ℝ) * shellGenerator m p := by
  simp only [shellGenerator]
  push_cast
  ring

/-- **Flow reparametrisation.** -/
theorem shellFlow_mul (m r : ℕ) (t : ℝ) (p : F) :
    shellFlow (r * m) t p = shellFlow m ((r : ℝ) * t) p := by
  simp only [shellFlow, shellGenerator_mul]
  congr 2
  push_cast
  ring

/-- **Lift dilation.** -/
theorem shellLift_mul (m r : ℕ) (t : ℝ) (p : F) :
    shellLift (r * m) t p = (r : ℝ) * shellLift m t p := by
  simp only [shellLift, shellGenerator_mul]
  ring

theorem shellFlow_div (m r : ℕ) (hr : r ≠ 0) (t : ℝ) (p : F) :
    shellFlow (r * m) (t / (r : ℝ)) p = shellFlow m t p := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  rw [shellFlow_mul]
  congr 1
  field_simp

/-- **Observed orbit invariance.** -/
theorem shellFlow_range_eq {m r : ℕ} (hr : r ≠ 0) :
    Set.range (fun t : ℝ => shellFlow (F := F) (r * m) t)
      = Set.range (fun t : ℝ => shellFlow (F := F) m t) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(r : ℝ) * t, by funext p; exact (shellFlow_mul m r t p).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t / (r : ℝ), by funext p; exact shellFlow_div m r hr t p⟩

/-- **Clock compensation identifies the lifted paths.** -/
theorem shellLift_div (m r : ℕ) (hr : r ≠ 0) (t : ℝ) (p : F) :
    shellLift (r * m) (t / (r : ℝ)) p = shellLift m t p := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  rw [shellLift_mul]
  simp only [shellLift, shellGenerator]
  field_simp

/-! ## Fixed-clock representation separation -/

/-- **Trace separation.**  The generator traces differ at fixed clock. -/
theorem sum_shellGenerator_ne {m r : ℕ} (hm : m ≠ 0) (hr : 2 ≤ r) (hF : F.Nonempty) :
    ∑ p : F, shellGenerator (r * m) p ≠ ∑ p : F, shellGenerator m p := by
  have hpos : 0 < ∑ p : F, shellGenerator m p := by
    obtain ⟨p₀, hp₀⟩ := hF
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    refine Finset.sum_pos (fun p _ => ?_) ⟨⟨p₀, hp₀⟩, Finset.mem_univ _⟩
    exact mul_pos hmpos (primeClockVec_pos p)
  have hsum : ∑ p : F, shellGenerator (r * m) p = (r : ℝ) * ∑ p : F, shellGenerator m p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => shellGenerator_mul m r p
  rw [hsum]
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- **Centred spectral variance scales by `r²`.** -/
theorem centeredVariance_mul (m r : ℕ) :
    ∑ p : F, (shellGenerator (r * m) p
        - (∑ q : F, shellGenerator (r * m) q) / (F.card : ℝ)) ^ 2
      = (r : ℝ) ^ 2 * ∑ p : F, (shellGenerator m p
        - (∑ q : F, shellGenerator m q) / (F.card : ℝ)) ^ 2 := by
  have hsum : ∑ q : F, shellGenerator (r * m) q = (r : ℝ) * ∑ q : F, shellGenerator m q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => shellGenerator_mul m r p
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [shellGenerator_mul, hsum, mul_div_assoc, ← mul_sub, mul_pow]

/-! ## Density and the escaping lift -/

/-- The prime clock vector is rationally independent. -/
theorem primeClockVec_linearIndependent (F : Finset Nat.Primes) :
    LinearIndependent ℚ (primeClockVec F) :=
  primeLogFiniteSlice_linearIndependent F

/-- The shell generator is rationally independent for a nonzero depth. -/
theorem shellGenerator_linearIndependent {m : ℕ} (hm : m ≠ 0) (F : Finset Nat.Primes) :
    LinearIndependent ℚ (shellGenerator (F := F) m) := by
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have h := (primeClockVec_linearIndependent F).units_smul
    (w := fun _ : F => Units.mk0 (m : ℚ) hm')
  have hfun : shellGenerator (F := F) m
      = fun p => (Units.mk0 (m : ℚ) hm' : ℚˣ) • primeClockVec F p := by
    funext p
    simp only [shellGenerator, Units.smul_def, Units.val_mk0, Rat.smul_def]
    push_cast
    ring
  rw [hfun]
  exact h

/-- **Density of the phase orbit.**  Every phase vector is approached by the flow. -/
theorem shellFlow_dense {m : ℕ} (hm : m ≠ 0) (F : Finset Nat.Primes) (θ : F → ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t : ℝ, ∀ p : F,
      ‖shellFlow (F := F) m t p - Complex.exp ((θ p : ℝ) * Complex.I)‖ < ε := by
  obtain ⟨t, ht⟩ :=
    kronecker_approx (shellGenerator_linearIndependent hm F) θ hε
  refine ⟨-t, fun p => ?_⟩
  have hrw : shellFlow (F := F) m (-t) p = expChar (shellGenerator m p) t := by
    simp only [shellFlow, expChar]
    congr 1
    push_cast
    ring
  rw [hrw]
  exact ht p

/-- **Arbitrarily large return times.**  The flow returns arbitrarily close to the identity at
arbitrarily late times. -/
theorem exists_large_return (m : ℕ) (F : Finset Nat.Primes) {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) :
    ∃ t : ℝ, T ≤ t ∧ ∀ p : F, ‖shellFlow (F := F) m t p - 1‖ < ε := by
  classical
  set x : ℕ → (F → ℂ) := fun n => shellFlow (F := F) m ((n : ℝ) * T) with hx
  have hnorm : ∀ n : ℕ, ∀ p : F, ‖x n p‖ = 1 := by
    intro n p
    simp [hx, shellFlow, Complex.norm_exp]
  have hbdd : ∀ n : ℕ, x n ∈ Metric.closedBall (0 : F → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    exact (hnorm n p).le
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    (isCompact_closedBall (0 : F → ℂ) 1).tendsto_subseq hbdd
  have hcauchy := hconv.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hcauchy ε hε
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  have hdist : dist (x (φ (N + 1))) (x (φ N)) < ε := hN (N + 1) (Nat.le_succ N)
  refine ⟨((φ (N + 1) - φ N : ℕ) : ℝ) * T, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((φ (N + 1) - φ N : ℕ) : ℝ) := by
      have : 1 ≤ φ (N + 1) - φ N := by omega
      exact_mod_cast this
    nlinarith
  · intro p
    have hsplit : shellFlow (F := F) m (((φ (N + 1) - φ N : ℕ) : ℝ) * T) p * x (φ N) p
        = x (φ (N + 1)) p := by
      simp only [hx, shellFlow, ← Complex.exp_add]
      congr 1
      have hle : φ N ≤ φ (N + 1) := hlt.le
      have hcast : ((φ (N + 1) - φ N : ℕ) : ℝ) = (φ (N + 1) : ℝ) - (φ N : ℝ) := by
        push_cast [hle]
        ring
      rw [hcast]
      push_cast
      ring
    have hxn : ‖x (φ N) p‖ = 1 := hnorm _ p
    have hxne : x (φ N) p ≠ 0 := by
      intro h
      rw [h] at hxn
      simp at hxn
    have hkey : shellFlow (F := F) m (((φ (N + 1) - φ N : ℕ) : ℝ) * T) p - 1
        = (x (φ (N + 1)) p - x (φ N) p) / x (φ N) p := by
      rw [eq_div_iff hxne, sub_mul, one_mul, hsplit]
    rw [hkey, norm_div, hxn, div_one]
    have hd : ‖x (φ (N + 1)) p - x (φ N) p‖ ≤ dist (x (φ (N + 1))) (x (φ N)) := by
      have := dist_le_pi_dist (x (φ (N + 1))) (x (φ N)) p
      simpa [dist_eq_norm] using this
    linarith [hdist]

/-- The marked lift escapes linearly. -/
theorem norm_shellLift {m : ℕ} (t : ℝ) :
    ∑ p : F, (shellLift (F := F) m t p) ^ 2
      = t ^ 2 * (m : ℝ) ^ 2 * ∑ p : F, (primeClockVec F p) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [shellLift, shellGenerator]
  ring

/-! ## Homogeneous cost dilation -/

/-- **Exact homogeneous cost dilation.**  A positively `q`-homogeneous cost dilates by `r^q` at
fixed clock. -/
theorem cost_dilation {Φ : (F → ℝ) → ℝ} {q : ℝ}
    (hΦ : ∀ (c : ℝ), 0 ≤ c → ∀ x, Φ (fun p => c * x p) = c ^ q * Φ x)
    (m r : ℕ) (t : ℝ) :
    Φ (shellLift (F := F) (r * m) t) = (r : ℝ) ^ q * Φ (shellLift (F := F) m t) := by
  have hrw : shellLift (F := F) (r * m) t = fun p => (r : ℝ) * shellLift (F := F) m t p := by
    funext p
    exact shellLift_mul m r t p
  rw [hrw, hΦ (r : ℝ) (Nat.cast_nonneg r)]

/-- **Fixed-clock action dilation.** -/
theorem action_dilation {Φ : (F → ℝ) → ℝ} {q : ℝ}
    (hΦ : ∀ (c : ℝ), 0 ≤ c → ∀ x, Φ (fun p => c * x p) = c ^ q * Φ x)
    (m r : ℕ) (T : ℝ) :
    T * Φ (fun p => -shellGenerator (F := F) (r * m) p)
      = (r : ℝ) ^ q * (T * Φ (fun p => -shellGenerator (F := F) m p)) := by
  have hrw : (fun p : F => -shellGenerator (r * m) p)
      = fun p => (r : ℝ) * (-shellGenerator (F := F) m p) := by
    funext p
    rw [shellGenerator_mul]
    ring
  rw [hrw, hΦ (r : ℝ) (Nat.cast_nonneg r)]
  ring

/-- **Reparametrised action.**  Traversing the same lifted path `r` times faster costs a factor
`r^{q-1}`. -/
theorem action_dilation_compensated {Φ : (F → ℝ) → ℝ} {q : ℝ}
    (hΦ : ∀ (c : ℝ), 0 ≤ c → ∀ x, Φ (fun p => c * x p) = c ^ q * Φ x)
    (m r : ℕ) (hr : r ≠ 0) (T : ℝ) :
    (T / (r : ℝ)) * Φ (fun p => -shellGenerator (F := F) (r * m) p)
      = (r : ℝ) ^ q / (r : ℝ) * (T * Φ (fun p => -shellGenerator (F := F) m p)) := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have h := action_dilation hΦ m r T
  field_simp
  linarith [h]

end HTGeometry.ConstraintFrameRelativity
