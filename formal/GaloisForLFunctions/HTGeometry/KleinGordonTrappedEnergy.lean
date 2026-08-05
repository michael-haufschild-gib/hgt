import GaloisForLFunctions.HTGeometry.KleinGordonEnergyTwoSided

/-!
# A clock in a weak static potential has its energy trapped

Statement 319 bounds the powers of the monodromy of a weak static real potential by
`K = √((1+b)/(1−b))`, uniformly. The evolution is invertible and its inverse obeys the same bound, so
the powers are bounded *below* as well: `‖Mⁿv‖ ≥ ‖v‖/K`, since `v = M⁻ⁿMⁿv`.

The energy of such a clock is therefore trapped in a band for all time,

`E(0)/K² ≤ E(nT) ≤ K²·E(0)`,

and its spectral radius is exactly one — every multiplier lies on the unit circle (statement 351) and
the spectrum is inhabited (341). A weak static potential neither drives a clock nor damps it: it can
only shift its energy by a fixed factor, once and for all.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a monoid, a right inverse telescopes through powers. -/
theorem pow_mul_pow_eq_one {M : Type*} [Monoid M] {a c : M} (h : a * c = 1) (n : ℕ) :
    a ^ n * c ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ' c n, mul_assoc, ← mul_assoc a c (c ^ n), h, one_mul, ih]

section StaticTrap

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **A clock in a weak static real potential has spectral radius exactly one.** -/
theorem spectralRadius_eq_one_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x) :
    spectralRadius ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T) = 1 := by
  have hall : ∀ k ∈ spectrum ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T), ‖k‖ = 1 :=
    fun _ hk => norm_eq_one_of_mem_spectrum_of_small_potential hb0 hb1 hW hsa hWb hWs hk
  have hle : spectralRadius ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T) ≤ 1 :=
    spectralRadius_le_one_of_forall fun k hk => le_of_eq (hall k hk)
  obtain ⟨k₀, hk₀⟩ := spectrum_kgMonodromy_nonempty (T := T) hb0 hWb hWs
  have hge : (1 : ℝ≥0∞) ≤ spectralRadius ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T) := by
    have hone : ((‖k₀‖₊ : ℝ≥0∞)) = 1 := by
      rw [enorm_eq_ofReal_norm, hall k₀ hk₀, ENNReal.ofReal_one]
    rw [← hone]
    exact norm_le_spectralRadius hk₀
  exact le_antisymm hle hge

set_option maxHeartbeats 1000000 in
/-- **The state of a clock in a weak static real potential is bounded below.** -/
theorem norm_kgFieldStateT_ge_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b))
      ≤ ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hKpos : 0 < Real.sqrt ((1 + b) / (1 - b)) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hab, hba⟩ := kgMonodromy_const_mul_inv (T := T) hb0 hWb hWs
  set M := kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T with hM
  set N := kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs (-T) with hN
  have hNM : N ^ n * M ^ n = 1 := pow_mul_pow_eq_one hba n
  have hstate : kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T) = (M ^ n) (kgPair E (g, h)) :=
    kgFieldStateT_monodromy_pow hb0 hWb hWs (periodic_const W₀ T) g h n
  have happ : (N ^ n) ((M ^ n) (kgPair E (g, h))) = kgPair E (g, h) := by
    have h1 : (N ^ n * M ^ n) (kgPair E (g, h)) = kgPair E (g, h) := by
      rw [hNM]
      rfl
    exact h1
  have hNbd : ‖N ^ n‖ ≤ Real.sqrt ((1 + b) / (1 - b)) :=
    norm_kgMonodromy_pow_le_of_small (T := -T) hb0 hb1 hW hsa hWb hWs n
  have hchain : ‖kgPair E (g, h)‖
      ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖(M ^ n) (kgPair E (g, h))‖ := by
    calc ‖kgPair E (g, h)‖ = ‖(N ^ n) ((M ^ n) (kgPair E (g, h)))‖ := by rw [happ]
      _ ≤ ‖N ^ n‖ * ‖(M ^ n) (kgPair E (g, h))‖ := (N ^ n).le_opNorm _
      _ ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖(M ^ n) (kgPair E (g, h))‖ :=
          mul_le_mul_of_nonneg_right hNbd (norm_nonneg _)
  rw [hstate, div_le_iff₀ hKpos]
  calc ‖kgPair E (g, h)‖ ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖(M ^ n) (kgPair E (g, h))‖ := hchain
    _ = ‖(M ^ n) (kgPair E (g, h))‖ * Real.sqrt ((1 + b) / (1 - b)) := by ring

set_option maxHeartbeats 1000000 in
/-- **The energy of a clock in a weak static real potential is trapped in a band, for all time.** -/
theorem kgFieldEnergy_trapped_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    (‖g‖ ^ 2 + ‖h‖ ^ 2) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGradT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2
          + ‖kgFieldVelT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2
      ∧ ‖kgFieldGradT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2
          + ‖kgFieldVelT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2
        ≤ (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK0 : (0 : ℝ) < (1 + b) / (1 - b) := by positivity
  have hKs : Real.sqrt ((1 + b) / (1 - b)) ^ 2 = (1 + b) / (1 - b) := Real.sq_sqrt hK0.le
  have hKpos : 0 < Real.sqrt ((1 + b) / (1 - b)) := Real.sqrt_pos.mpr hK0
  have hpair : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := norm_kgPair_sq g h
  have hlow := norm_kgFieldStateT_ge_of_small_potential (T := T) hb0 hb1 hW hsa hWb hWs g h n
  have hupp : ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖
      ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖ := by
    rw [kgFieldStateT_const]
    exact norm_kgFieldState_le_uniform hb0 hb1 hW hsa g h ((n : ℝ) * T)
  have hnn : (0 : ℝ) ≤ ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ := norm_nonneg _
  have hdiv0 : (0 : ℝ) ≤ ‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b)) := by positivity
  rw [kgFieldEnergyT_eq_norm_sq]
  constructor
  · have hsq := mul_self_le_mul_self hdiv0 hlow
    have hval : (‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b)))
        * (‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b)))
        = (‖g‖ ^ 2 + ‖h‖ ^ 2) / ((1 + b) / (1 - b)) := by
      rw [div_mul_div_comm, ← pow_two, ← pow_two, hKs, hpair]
    rw [hval] at hsq
    calc (‖g‖ ^ 2 + ‖h‖ ^ 2) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖
          * ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ := hsq
      _ = ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2 := by ring
  · have hsq := mul_self_le_mul_self hnn hupp
    have hval : (Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖)
        * (Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖)
        = (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
      rw [show (Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖)
          * (Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖)
          = Real.sqrt ((1 + b) / (1 - b)) ^ 2 * ‖kgPair E (g, h)‖ ^ 2 from by ring, hKs, hpair]
    rw [hval] at hsq
    calc ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ 2
        = ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖
          * ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ := by ring
      _ ≤ (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) := hsq

end StaticTrap

end GaloisForLFunctions.HTGeometry
