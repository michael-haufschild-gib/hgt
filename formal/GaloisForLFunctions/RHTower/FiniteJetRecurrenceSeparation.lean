import GaloisForLFunctions.RHTower.MixedStateQutritRecurrenceSeparation

/-!
# No finite survival jet determines quantum recurrence

For every prescribed finite order `N ≥ 2`, Lagrange interpolation constructs
two probability packets on one finite energy list. Their energy moments, and
therefore their formal survival-amplitude coefficients, agree through order
`N`. One packet is supported only on integer energies and returns at every
tick `2πn`; the other sees `√2`, never returns at a positive tick, and obeys
matching inverse-resolution lower and upper bounds.

The construction uses positive and negative parts of the Lagrange weights for
evaluation at `√2` on the integer nodes `0,...,N`. The weight at node zero is
strictly negative, so the irrational packet contains both irrational and
rational support with strictly positive mass.
-/

open scoped BigOperators

noncomputable section

namespace RHTower.FiniteJet

def node (N : ℕ) (i : Fin (N + 1)) : ℝ := (i : ℕ)

def weight (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  Polynomial.eval (Real.sqrt 2)
    (Lagrange.basis Finset.univ (node N) i)

theorem node_injective (N : ℕ) : Function.Injective (node N) := by
  intro i j h
  apply Fin.ext
  simpa [node] using h

theorem moment (N k : ℕ) (hk : k ≤ N) :
    (Real.sqrt 2) ^ k =
      ∑ i : Fin (N + 1), weight N i * (node N i) ^ k := by
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (N + 1))).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (v := node N)
    (f := (Polynomial.X ^ k : Polynomial ℝ))
    (by
      intro i _hi j _hj hij
      exact node_injective N hij) hdeg
  have he := congrArg (Polynomial.eval (Real.sqrt 2)) hp
  simpa [weight, Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow,
    mul_comm] using he

theorem weight_zero_neg (N : ℕ) (hN : 2 ≤ N) :
    weight N (0 : Fin (N + 1)) < 0 := by
  let s : Finset (Fin (N + 1)) :=
    Finset.univ.erase (0 : Fin (N + 1))
  let f : Fin (N + 1) → ℝ := fun j =>
    Polynomial.eval (Real.sqrt 2)
      (Lagrange.basisDivisor (node N 0) (node N j))
  have hcard : 1 < N + 1 := by omega
  let o : Fin (N + 1) := ⟨1, hcard⟩
  have h1mem : o ∈ s := by
    simp [s, o]
  have hf1 : f o < 0 := by
    simp [f, Lagrange.basisDivisor, node]
    have hs : 1 < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    linarith
  have hfpos : ∀ j ∈ s.erase o, 0 < f j := by
    intro j hj
    have hj1 : j ≠ o := (Finset.mem_erase.mp hj).1
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_erase.mp hj).2
      exact (Finset.mem_erase.mp this).1
    have hjval_ne0 : (j : ℕ) ≠ 0 := by
      intro hv
      apply hj0
      exact Fin.ext hv
    have hjval_ne1 : (j : ℕ) ≠ 1 := by
      intro hv
      apply hj1
      exact Fin.ext (by simpa [o] using hv)
    have hjtwo : 2 ≤ (j : ℕ) := by omega
    have hslt : Real.sqrt 2 < (j : ℕ) := by
      have hs : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg 2]
      exact lt_of_lt_of_le hs (by exact_mod_cast hjtwo)
    have hjpos : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (by omega : 0 < (j : ℕ))
    have hden : node N 0 - node N j < 0 := by
      simpa [node] using (sub_neg.mpr hjpos)
    have hnum : Real.sqrt 2 - node N j < 0 := by
      simpa [node] using (sub_neg.mpr hslt)
    have hmul :
        0 < (node N 0 - node N j)⁻¹ *
          (Real.sqrt 2 - node N j) :=
      mul_pos_of_neg_of_neg (inv_lt_zero.mpr hden) hnum
    simpa [f, Lagrange.basisDivisor] using hmul
  have hrest : 0 < ∏ j ∈ s.erase o, f j :=
    Finset.prod_pos hfpos
  rw [weight, Lagrange.basis, Polynomial.eval_prod]
  change (∏ j ∈ s, f j) < 0
  rw [← Finset.prod_erase_mul s f h1mem]
  exact mul_neg_of_pos_of_neg hrest hf1

def posWeight (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  max (weight N i) 0

def negWeight (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  max (-weight N i) 0

def mass (N : ℕ) : ℝ := ∑ i, posWeight N i

theorem signedWeight_eq_pos_sub_neg (N : ℕ) (i : Fin (N + 1)) :
    weight N i = posWeight N i - negWeight N i := by
  rw [posWeight, negWeight]
  exact (max_zero_sub_max_neg_zero_eq_self (weight N i)).symm

theorem sum_weight_eq_one (N : ℕ) :
    ∑ i, weight N i = 1 := by
  have h := moment N 0 (Nat.zero_le N)
  simpa using h.symm

theorem mass_eq_one_add_negMass (N : ℕ) :
    mass N = 1 + ∑ i, negWeight N i := by
  have hsum := sum_weight_eq_one N
  simp_rw [signedWeight_eq_pos_sub_neg] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  rw [mass]
  linarith

theorem negMass_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < ∑ i, negWeight N i := by
  have h0 : 0 < negWeight N (0 : Fin (N + 1)) := by
    rw [negWeight, max_eq_left]
    · linarith [weight_zero_neg N hN]
    · linarith [weight_zero_neg N hN]
  have hle :
      negWeight N (0 : Fin (N + 1)) ≤ ∑ i, negWeight N i := by
    apply Finset.single_le_sum
    · intro i _hi
      exact le_max_right _ _
    · simp
  linarith

theorem mass_gt_one (N : ℕ) (hN : 2 ≤ N) :
    1 < mass N := by
  rw [mass_eq_one_add_negMass]
  linarith [negMass_pos N hN]

theorem unnormalized_moment_eq (N k : ℕ) (hk : k ≤ N) :
    (Real.sqrt 2) ^ k +
        ∑ i, negWeight N i * (node N i) ^ k =
      ∑ i, posWeight N i * (node N i) ^ k := by
  have hm := moment N k hk
  calc
    (Real.sqrt 2) ^ k +
        ∑ i, negWeight N i * (node N i) ^ k =
        (∑ i, weight N i * (node N i) ^ k) +
          ∑ i, negWeight N i * (node N i) ^ k := by rw [hm]
    _ = ∑ i, (weight N i + negWeight N i) * (node N i) ^ k := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i, posWeight N i * (node N i) ^ k := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [signedWeight_eq_pos_sub_neg]
      ring

def energy (N : ℕ) : Option (Fin (N + 1)) → ℝ
  | none => Real.sqrt 2
  | some i => node N i

def periodicProbability (N : ℕ) : Option (Fin (N + 1)) → ℝ
  | none => 0
  | some i => posWeight N i / mass N

def aperiodicProbability (N : ℕ) : Option (Fin (N + 1)) → ℝ
  | none => 1 / mass N
  | some i => negWeight N i / mass N

theorem periodicProbability_nonneg (N : ℕ) (hN : 2 ≤ N) :
    ∀ x, 0 ≤ periodicProbability N x := by
  intro x
  cases x with
  | none => simp [periodicProbability]
  | some i =>
      rw [periodicProbability]
      exact div_nonneg (le_max_right _ _)
        (lt_trans zero_lt_one (mass_gt_one N hN)).le

theorem aperiodicProbability_nonneg (N : ℕ) (hN : 2 ≤ N) :
    ∀ x, 0 ≤ aperiodicProbability N x := by
  intro x
  cases x with
  | none =>
      rw [aperiodicProbability]
      exact (one_div_nonneg.mpr
        (lt_trans zero_lt_one (mass_gt_one N hN)).le)
  | some i =>
      rw [aperiodicProbability]
      exact div_nonneg (le_max_right _ _)
        (lt_trans zero_lt_one (mass_gt_one N hN)).le

theorem periodicProbability_sum (N : ℕ) (hN : 2 ≤ N) :
    ∑ x, periodicProbability N x = 1 := by
  rw [Fintype.sum_option]
  simp only [periodicProbability, zero_add, ← Finset.sum_div, mass]
  exact div_self (ne_of_gt
    (lt_trans zero_lt_one (mass_gt_one N hN)))

theorem aperiodicProbability_sum (N : ℕ) (hN : 2 ≤ N) :
    ∑ x, aperiodicProbability N x = 1 := by
  rw [Fintype.sum_option]
  simp only [aperiodicProbability, ← Finset.sum_div, ← add_div]
  rw [← mass_eq_one_add_negMass]
  exact div_self (ne_of_gt
    (lt_trans zero_lt_one (mass_gt_one N hN)))

theorem probability_moment_eq (N k : ℕ) (_hN : 2 ≤ N) (hk : k ≤ N) :
    (∑ x, periodicProbability N x * energy N x ^ k) =
      ∑ x, aperiodicProbability N x * energy N x ^ k := by
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [periodicProbability, aperiodicProbability, energy, zero_mul,
    zero_add]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
  simp only [one_mul]
  rw [unnormalized_moment_eq N k hk]

def survivalJetCoefficient (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (k : ℕ) : ℂ :=
  (-Complex.I) ^ k * (∑ x, (w x * energy N x ^ k : ℝ) : ℂ)

/-- Taylor coefficient for the opposite, equally conventional phase sign. -/
def forwardSurvivalJetCoefficient (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (k : ℕ) : ℂ :=
  Complex.I ^ k * (∑ x, (w x * energy N x ^ k : ℝ) : ℂ)

theorem survivalJetCoefficient_eq (N k : ℕ) (hN : 2 ≤ N) (hk : k ≤ N) :
    survivalJetCoefficient N (periodicProbability N) k =
      survivalJetCoefficient N (aperiodicProbability N) k := by
  rw [survivalJetCoefficient, survivalJetCoefficient]
  congr 1
  exact_mod_cast probability_moment_eq N k hN hk

theorem forwardSurvivalJetCoefficient_eq
    (N k : ℕ) (hN : 2 ≤ N) (hk : k ≤ N) :
    forwardSurvivalJetCoefficient N (periodicProbability N) k =
      forwardSurvivalJetCoefficient N (aperiodicProbability N) k := by
  rw [forwardSurvivalJetCoefficient, forwardSurvivalJetCoefficient]
  congr 1
  exact_mod_cast probability_moment_eq N k hN hk

/-- Pure quantum clock realizing the integer-supported packet. -/
def periodicClock (N : ℕ) :
    RHTower.FiniteIndexClockSpace (Option (Fin (N + 1))) :=
  RHTower.finiteIndexWeightKet (periodicProbability N)

/-- Pure quantum clock realizing the packet with irrational support. -/
def aperiodicClock (N : ℕ) :
    RHTower.FiniteIndexClockSpace (Option (Fin (N + 1))) :=
  RHTower.finiteIndexWeightKet (aperiodicProbability N)

/-- One self-adjoint diagonal Hamiltonian shared by both clocks. -/
def clockHamiltonian (N : ℕ) :
    RHTower.FiniteIndexClockSpace (Option (Fin (N + 1))) →L[ℂ]
      RHTower.FiniteIndexClockSpace (Option (Fin (N + 1))) :=
  RHTower.finiteIndexDiagonalHamiltonian (energy N)

theorem clockHamiltonian_selfAdjoint (N : ℕ) :
    ContinuousLinearMap.adjoint (clockHamiltonian N) =
      clockHamiltonian N :=
  RHTower.finiteIndexDiagonalHamiltonian_selfAdjoint (energy N)

theorem periodicClock_norm_eq_one (N : ℕ) (hN : 2 ≤ N) :
    ‖periodicClock N‖ = 1 :=
  RHTower.finiteIndexWeightKet_norm_eq_one
    (periodicProbability N) (periodicProbability_nonneg N hN)
    (periodicProbability_sum N hN)

theorem aperiodicClock_norm_eq_one (N : ℕ) (hN : 2 ≤ N) :
    ‖aperiodicClock N‖ = 1 :=
  RHTower.finiteIndexWeightKet_norm_eq_one
    (aperiodicProbability N) (aperiodicProbability_nonneg N hN)
    (aperiodicProbability_sum N hN)

/-- The two realized clocks have exactly the same energy variance. -/
theorem clock_variance_eq (N : ℕ) (hN : 2 ≤ N) :
    ‖clockHamiltonian N (periodicClock N)‖ ^ 2 -
        ‖inner ℂ (periodicClock N)
          (clockHamiltonian N (periodicClock N))‖ ^ 2 =
      ‖clockHamiltonian N (aperiodicClock N)‖ ^ 2 -
        ‖inner ℂ (aperiodicClock N)
          (clockHamiltonian N (aperiodicClock N))‖ ^ 2 := by
  have hfirst := probability_moment_eq N 1 hN (by omega)
  have hsecond := probability_moment_eq N 2 hN (by omega)
  simp only [pow_one] at hfirst
  simp only [clockHamiltonian, periodicClock, aperiodicClock]
  rw [RHTower.finiteIndexWeightKet_diagonal_variance
      (periodicProbability N) (energy N)
      (periodicProbability_nonneg N hN),
    RHTower.finiteIndexWeightKet_diagonal_variance
      (aperiodicProbability N) (energy N)
      (aperiodicProbability_nonneg N hN)]
  rw [hfirst, hsecond]

/-- Identical Hilbert--Schmidt initial speed for the two pure clock orbits. -/
theorem clock_hsSpeedSq_eq (N : ℕ) (hN : 2 ≤ N) :
    ContinuousLinearMap.hsNormSq
        (RHTower.mixedSpikeUnitaryTangent 1
          (clockHamiltonian N) (periodicClock N)) =
      ContinuousLinearMap.hsNormSq
        (RHTower.mixedSpikeUnitaryTangent 1
          (clockHamiltonian N) (aperiodicClock N)) := by
  rw [RHTower.mixedSpikeUnitaryTangent_hsNormSq 1
      (clockHamiltonian N) (clockHamiltonian_selfAdjoint N)
      (periodicClock N) (periodicClock_norm_eq_one N hN),
    RHTower.mixedSpikeUnitaryTangent_hsNormSq 1
      (clockHamiltonian N) (clockHamiltonian_selfAdjoint N)
      (aperiodicClock N) (aperiodicClock_norm_eq_one N hN)]
  rw [clock_variance_eq N hN]

/-- Identical symmetric-logarithmic-derivative time information. -/
theorem clock_quantumFisher_eq (N : ℕ) (hN : 2 ≤ N) :
    RHTower.mixedSpikeSLDQuantumFisher 0 1
        (clockHamiltonian N) (periodicClock N) =
      RHTower.mixedSpikeSLDQuantumFisher 0 1
        (clockHamiltonian N) (aperiodicClock N) := by
  rw [RHTower.mixedSpikeSLDQuantumFisher_eq 0 1 (by norm_num)
      (clockHamiltonian N) (clockHamiltonian_selfAdjoint N)
      (periodicClock N) (periodicClock_norm_eq_one N hN),
    RHTower.mixedSpikeSLDQuantumFisher_eq 0 1 (by norm_num)
      (clockHamiltonian N) (clockHamiltonian_selfAdjoint N)
      (aperiodicClock N) (aperiodicClock_norm_eq_one N hN)]
  rw [clock_variance_eq N hN]

def tickPhase (N n : ℕ) : Option (Fin (N + 1)) → ℂ
  | none => HTGeometry.ee ((n : ℝ) * Real.sqrt 2)
  | some _ => 1

def phaseAmplitude (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (n : ℕ) : ℂ :=
  ∑ x, (w x : ℂ) * tickPhase N n x

/-- Evolved clock ket at the stroboscopic tick `2πn`. -/
def tickClock (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (n : ℕ) :
    RHTower.FiniteIndexClockSpace (Option (Fin (N + 1))) :=
  RHTower.finiteIndexPhasedWeightKet w (tickPhase N n)

theorem tickPhase_norm (N n : ℕ) :
    ∀ x, ‖tickPhase N n x‖ = 1 := by
  intro x
  cases x with
  | none => exact HTGeometry.norm_ee _
  | some i => simp [tickPhase]

/-- The spectral phase sum is the actual Hilbert-space survival amplitude. -/
theorem clock_inner_tickClock
    (N n : ℕ) (w : Option (Fin (N + 1)) → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    inner ℂ (RHTower.finiteIndexWeightKet w) (tickClock N w n) =
      phaseAmplitude N w n := by
  exact RHTower.finiteIndexWeightKet_inner_phasedWeightKet
    w (tickPhase N n) hw

theorem periodic_phaseAmplitude_eq_one
    (N n : ℕ) (hN : 2 ≤ N) :
    phaseAmplitude N (periodicProbability N) n = 1 := by
  rw [phaseAmplitude, Fintype.sum_option]
  simp only [periodicProbability, tickPhase, Complex.ofReal_zero, zero_mul,
    zero_add, mul_one]
  have hreal : ∑ i, posWeight N i / mass N = 1 := by
    rw [← Finset.sum_div, mass]
    exact div_self (ne_of_gt
      (lt_trans zero_lt_one (mass_gt_one N hN)))
  exact_mod_cast hreal

theorem periodicClock_inner_tickClock_eq_one
    (N n : ℕ) (hN : 2 ≤ N) :
    inner ℂ (periodicClock N)
        (tickClock N (periodicProbability N) n) = 1 := by
  simp only [periodicClock]
  rw [clock_inner_tickClock N n (periodicProbability N)
      (periodicProbability_nonneg N hN),
    periodic_phaseAmplitude_eq_one N n hN]

theorem aperiodic_phaseAmplitude_eq_twoPoint
    (N n : ℕ) (hN : 2 ≤ N) :
    phaseAmplitude N (aperiodicProbability N) n =
      ((1 - 1 / mass N : ℝ) : ℂ) +
        ((1 / mass N : ℝ) : ℂ) *
          HTGeometry.ee ((n : ℝ) * Real.sqrt 2) := by
  rw [phaseAmplitude, Fintype.sum_option]
  simp only [aperiodicProbability, tickPhase, mul_one]
  have hneg : ∑ i, negWeight N i = mass N - 1 := by
    rw [mass_eq_one_add_negMass]
    ring
  have hmass0 : mass N ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one (mass_gt_one N hN))
  have hreal :
      ∑ i, negWeight N i / mass N = 1 - 1 / mass N := by
    rw [← Finset.sum_div, hneg]
    field_simp [hmass0]
  rw [← Complex.ofReal_sum, hreal]
  push_cast
  ring

theorem aperiodicClock_inner_tickClock_eq_twoPoint
    (N n : ℕ) (hN : 2 ≤ N) :
    inner ℂ (aperiodicClock N)
        (tickClock N (aperiodicProbability N) n) =
      ((1 - 1 / mass N : ℝ) : ℂ) +
        ((1 / mass N : ℝ) : ℂ) *
          HTGeometry.ee ((n : ℝ) * Real.sqrt 2) := by
  simp only [aperiodicClock]
  rw [clock_inner_tickClock N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN),
    aperiodic_phaseAmplitude_eq_twoPoint N n hN]

def irrationalMass (N : ℕ) : ℝ := 1 / mass N

theorem irrationalMass_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < irrationalMass N := by
  rw [irrationalMass]
  exact one_div_pos.mpr (lt_trans zero_lt_one (mass_gt_one N hN))

theorem irrationalMass_lt_one (N : ℕ) (hN : 2 ≤ N) :
    irrationalMass N < 1 := by
  rw [irrationalMass]
  exact (div_lt_one (lt_trans zero_lt_one (mass_gt_one N hN))).2
    (mass_gt_one N hN)

theorem twoPoint_fidelityDeficit
    (μ : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    1 - ‖((1 - μ : ℝ) : ℂ) + (μ : ℂ) * z‖ ^ 2 =
      μ * (1 - μ) * ‖z - 1‖ ^ 2 := by
  let w : Fin 2 → ℝ := ![1 - μ, μ]
  let phase : Fin 2 → ℂ := ![1, z]
  have hmass : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_two]
  have hphase : ∀ i, ‖phase i‖ = 1 := by
    intro i
    fin_cases i
    · simp [phase]
    · simp [phase, hz]
  have h := RHTower.projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    w phase hmass hphase
  have henergy :
      RHTower.projectiveWeightedPairwiseEnergy w phase =
        2 * μ * (1 - μ) * ‖z - 1‖ ^ 2 := by
    simp [RHTower.projectiveWeightedPairwiseEnergy, w, phase,
      Fin.sum_univ_two, norm_sub_rev]
    ring
  rw [henergy] at h
  simp [RHTower.projectiveWeightedPhaseAmplitude, w, phase,
    Fin.sum_univ_two] at h
  push_cast at h ⊢
  nlinarith

def recurrenceAmplitude (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (1 - ‖phaseAmplitude N w n‖ ^ 2)

/-- Operational recurrence amplitude from the actual clock-state overlap. -/
def clockRecurrenceAmplitude (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt
    (1 - ‖inner ℂ (RHTower.finiteIndexWeightKet w) (tickClock N w n)‖ ^ 2)

/-- Root survival deficit of the realized pure clock. -/
def rootSurvivalDeficit (N : ℕ)
    (w : Option (Fin (N + 1)) → ℝ) (n : ℕ) : ℝ :=
  2 * clockRecurrenceAmplitude N w n

theorem clockRecurrenceAmplitude_eq
    (N n : ℕ) (w : Option (Fin (N + 1)) → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    clockRecurrenceAmplitude N w n = recurrenceAmplitude N w n := by
  rw [clockRecurrenceAmplitude, recurrenceAmplitude,
    clock_inner_tickClock N n w hw]

theorem periodic_recurrenceAmplitude_eq_zero
    (N n : ℕ) (hN : 2 ≤ N) :
    recurrenceAmplitude N (periodicProbability N) n = 0 := by
  rw [recurrenceAmplitude, periodic_phaseAmplitude_eq_one N n hN]
  norm_num

theorem periodic_rootSurvivalDeficit_eq_zero
    (N n : ℕ) (hN : 2 ≤ N) :
    rootSurvivalDeficit N (periodicProbability N) n = 0 := by
  rw [rootSurvivalDeficit,
    clockRecurrenceAmplitude_eq N n (periodicProbability N)
      (periodicProbability_nonneg N hN),
    periodic_recurrenceAmplitude_eq_zero N n hN]
  ring

theorem aperiodic_recurrenceAmplitude_eq
    (N n : ℕ) (hN : 2 ≤ N) :
    recurrenceAmplitude N (aperiodicProbability N) n =
      (1 / 2 : ℝ) *
        Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
          ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
  rw [recurrenceAmplitude,
    aperiodic_phaseAmplitude_eq_twoPoint N n hN]
  have hfd := twoPoint_fidelityDeficit (irrationalMass N)
    (HTGeometry.ee ((n : ℝ) * Real.sqrt 2))
    (HTGeometry.norm_ee _)
  change (1 / 2 : ℝ) * Real.sqrt
      (1 - ‖(((1 - irrationalMass N : ℝ) : ℂ) +
        ((irrationalMass N : ℝ) : ℂ) *
          HTGeometry.ee ((n : ℝ) * Real.sqrt 2))‖ ^ 2) = _
  rw [hfd, Real.sqrt_mul
    (mul_nonneg (irrationalMass_pos N hN).le
      (by linarith [irrationalMass_lt_one N hN]))]
  rw [Real.sqrt_sq (norm_nonneg _)]
  ring

theorem aperiodic_rootSurvivalDeficit_eq
    (N n : ℕ) (hN : 2 ≤ N) :
    rootSurvivalDeficit N (aperiodicProbability N) n =
      Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
  rw [rootSurvivalDeficit,
    clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN),
    aperiodic_recurrenceAmplitude_eq N n hN]
  ring

theorem aperiodic_recurrenceAmplitude_lower
    (N n : ℕ) (hN : 2 ≤ N) (hn : 0 < n) :
    Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
        (2 * (n : ℝ)) ≤
      recurrenceAmplitude N (aperiodicProbability N) n := by
  rw [aperiodic_recurrenceAmplitude_eq N n hN]
  have hdist := RHTower.distToInt_nat_mul_sqrt_two_lower n hn
  have hchord :=
    HTGeometry.four_mul_distToInt_le_norm_ee_sub_one
      ((n : ℝ) * Real.sqrt 2)
  have hchordLower :
      1 / (n : ℝ) ≤
        ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
    calc
      1 / (n : ℝ) = 4 * (1 / (4 * (n : ℝ))) := by
        field_simp
      _ ≤ 4 * HTGeometry.distToInt ((n : ℝ) * Real.sqrt 2) := by
        gcongr
      _ ≤ ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := hchord
  have hsqrt :
      0 ≤ Real.sqrt (irrationalMass N * (1 - irrationalMass N)) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
        (2 * (n : ℝ)) =
        (1 / 2 : ℝ) *
          Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
            (1 / (n : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) *
        Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
          ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ := by
      gcongr

theorem aperiodic_recurrenceAmplitude_pos
    (N n : ℕ) (hN : 2 ≤ N) (hn : 0 < n) :
    0 < recurrenceAmplitude N (aperiodicProbability N) n := by
  have hlower :=
    aperiodic_recurrenceAmplitude_lower N n hN hn
  have hmassProduct :
      0 < irrationalMass N * (1 - irrationalMass N) :=
    mul_pos (irrationalMass_pos N hN)
      (sub_pos.mpr (irrationalMass_lt_one N hN))
  have hsqrt :
      0 < Real.sqrt (irrationalMass N * (1 - irrationalMass N)) :=
    Real.sqrt_pos.2 hmassProduct
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hleft :
      0 < Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
        (2 * (n : ℝ)) :=
    div_pos hsqrt (mul_pos (by norm_num) hnreal)
  exact lt_of_lt_of_le hleft hlower

theorem aperiodic_rootSurvivalDeficit_lower
    (N n : ℕ) (hN : 2 ≤ N) (hn : 0 < n) :
    Real.sqrt (irrationalMass N * (1 - irrationalMass N)) / (n : ℝ) ≤
      rootSurvivalDeficit N (aperiodicProbability N) n := by
  have h :=
    aperiodic_recurrenceAmplitude_lower N n hN hn
  rw [rootSurvivalDeficit,
    clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
  calc
    Real.sqrt (irrationalMass N * (1 - irrationalMass N)) / (n : ℝ) =
        2 * (Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
          (2 * (n : ℝ))) := by ring
    _ ≤ 2 * recurrenceAmplitude N (aperiodicProbability N) n := by
      gcongr

theorem aperiodic_rootSurvivalDeficit_pos
    (N n : ℕ) (hN : 2 ≤ N) (hn : 0 < n) :
    0 < rootSurvivalDeficit N (aperiodicProbability N) n := by
  rw [rootSurvivalDeficit,
    clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
  exact mul_pos (by norm_num)
    (aperiodic_recurrenceAmplitude_pos N n hN hn)

theorem exists_aperiodic_recurrenceAmplitude_upper
    (N Q : ℕ) (hN : 2 ≤ N) (hQ : 0 < Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
      recurrenceAmplitude N (aperiodicProbability N) n ≤
        Real.pi *
          Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
            (Q : ℝ) := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    RHTower.exists_fin_simultaneous_integer_approximation_anisotropic
      (fun _ : Fin 1 => Real.sqrt 2) (fun _ : Fin 1 => Q)
      (fun _ => hQ)
  have hnQ' : n ≤ Q := by
    simpa using hnQ
  have happrox :
      |(n : ℝ) * Real.sqrt 2 - (r 0 : ℝ)| ≤ 1 / (Q : ℝ) := by
    simpa using hr 0
  have hchord :
      ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ≤
        2 * Real.pi * (1 / (Q : ℝ)) :=
    RHTower.norm_ee_sub_one_le_two_pi_mul_of_integer_approximation
      (r 0) happrox
  refine ⟨n, hn, hnQ', ?_⟩
  rw [aperiodic_recurrenceAmplitude_eq N n hN]
  have hsqrt :
      0 ≤ Real.sqrt (irrationalMass N * (1 - irrationalMass N)) :=
    Real.sqrt_nonneg _
  calc
    (1 / 2 : ℝ) *
        Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
          ‖HTGeometry.ee ((n : ℝ) * Real.sqrt 2) - 1‖ ≤
        (1 / 2 : ℝ) *
          Real.sqrt (irrationalMass N * (1 - irrationalMass N)) *
            (2 * Real.pi * (1 / (Q : ℝ))) := by
      gcongr
    _ = Real.pi *
        Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
          (Q : ℝ) := by ring

theorem exists_aperiodic_rootSurvivalDeficit_upper
    (N Q : ℕ) (hN : 2 ≤ N) (hQ : 0 < Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
      rootSurvivalDeficit N (aperiodicProbability N) n ≤
        2 * Real.pi *
          Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
            (Q : ℝ) := by
  obtain ⟨n, hn, hnQ, hbound⟩ :=
    exists_aperiodic_recurrenceAmplitude_upper N Q hN hQ
  refine ⟨n, hn, hnQ, ?_⟩
  rw [rootSurvivalDeficit,
    clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
  calc
    2 * recurrenceAmplitude N (aperiodicProbability N) n ≤
        2 * (Real.pi *
          Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
            (Q : ℝ)) := by
      gcongr
    _ = 2 * Real.pi *
        Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
          (Q : ℝ) := by ring

theorem finiteJet_globalRecurrence_separation
    (N : ℕ) (hN : 2 ≤ N) :
    (∀ x, 0 ≤ periodicProbability N x) ∧
    (∀ x, 0 ≤ aperiodicProbability N x) ∧
    (∑ x, periodicProbability N x = 1) ∧
    (∑ x, aperiodicProbability N x = 1) ∧
    (∀ k : ℕ, k ≤ N →
      (∑ x, periodicProbability N x * energy N x ^ k) =
        ∑ x, aperiodicProbability N x * energy N x ^ k) ∧
    (∀ k : ℕ, k ≤ N →
      survivalJetCoefficient N (periodicProbability N) k =
        survivalJetCoefficient N (aperiodicProbability N) k) ∧
    (∀ n : ℕ,
      recurrenceAmplitude N (periodicProbability N) n = 0) ∧
    (∀ n : ℕ, 0 < n →
      Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
          (2 * (n : ℝ)) ≤
        recurrenceAmplitude N (aperiodicProbability N) n) ∧
    (∀ Q : ℕ, 0 < Q →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        recurrenceAmplitude N (aperiodicProbability N) n ≤
          Real.pi *
            Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
              (Q : ℝ)) := by
  refine ⟨periodicProbability_nonneg N hN,
    aperiodicProbability_nonneg N hN,
    periodicProbability_sum N hN,
    aperiodicProbability_sum N hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact probability_moment_eq N k hN hk
  · intro k hk
    exact survivalJetCoefficient_eq N k hN hk
  · intro n
    exact periodic_recurrenceAmplitude_eq_zero N n hN
  · intro n hn
    exact aperiodic_recurrenceAmplitude_lower N n hN hn
  · intro Q hQ
    exact exists_aperiodic_recurrenceAmplitude_upper N Q hN hQ

/--
Operator-level universal separation law.  For every finite order `N ≥ 2`,
two unit pure clocks evolving under one self-adjoint Hamiltonian agree in all
energy moments and survival coefficients through order `N`, including their
initial Hilbert--Schmidt speed and time quantum Fisher information.  One
returns exactly at every tick; the other never returns at a positive tick and
has matching inverse-horizon recurrence bounds.
-/
theorem finiteJet_quantumClock_separation
    (N : ℕ) (hN : 2 ≤ N) :
    ContinuousLinearMap.adjoint (clockHamiltonian N) =
        clockHamiltonian N ∧
    ‖periodicClock N‖ = 1 ∧
    ‖aperiodicClock N‖ = 1 ∧
    (∀ k : ℕ, k ≤ N →
      (∑ x, periodicProbability N x * energy N x ^ k) =
        ∑ x, aperiodicProbability N x * energy N x ^ k) ∧
    (∀ k : ℕ, k ≤ N →
      survivalJetCoefficient N (periodicProbability N) k =
        survivalJetCoefficient N (aperiodicProbability N) k) ∧
    ContinuousLinearMap.hsNormSq
        (RHTower.mixedSpikeUnitaryTangent 1
          (clockHamiltonian N) (periodicClock N)) =
      ContinuousLinearMap.hsNormSq
        (RHTower.mixedSpikeUnitaryTangent 1
          (clockHamiltonian N) (aperiodicClock N)) ∧
    RHTower.mixedSpikeSLDQuantumFisher 0 1
        (clockHamiltonian N) (periodicClock N) =
      RHTower.mixedSpikeSLDQuantumFisher 0 1
        (clockHamiltonian N) (aperiodicClock N) ∧
    (∀ n : ℕ,
      clockRecurrenceAmplitude N (periodicProbability N) n = 0) ∧
    (∀ n : ℕ, 0 < n →
      0 < clockRecurrenceAmplitude N (aperiodicProbability N) n) ∧
    (∀ n : ℕ, 0 < n →
      Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
          (2 * (n : ℝ)) ≤
        clockRecurrenceAmplitude N (aperiodicProbability N) n) ∧
    (∀ Q : ℕ, 0 < Q →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        clockRecurrenceAmplitude N (aperiodicProbability N) n ≤
          Real.pi *
            Real.sqrt (irrationalMass N * (1 - irrationalMass N)) /
              (Q : ℝ)) := by
  refine ⟨clockHamiltonian_selfAdjoint N,
    periodicClock_norm_eq_one N hN,
    aperiodicClock_norm_eq_one N hN, ?_, ?_,
    clock_hsSpeedSq_eq N hN, clock_quantumFisher_eq N hN,
    ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact probability_moment_eq N k hN hk
  · intro k hk
    exact survivalJetCoefficient_eq N k hN hk
  · intro n
    rw [clockRecurrenceAmplitude_eq N n (periodicProbability N)
      (periodicProbability_nonneg N hN)]
    exact periodic_recurrenceAmplitude_eq_zero N n hN
  · intro n hn
    rw [clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
    exact aperiodic_recurrenceAmplitude_pos N n hN hn
  · intro n hn
    rw [clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
    exact aperiodic_recurrenceAmplitude_lower N n hN hn
  · intro Q hQ
    obtain ⟨n, hn, hnQ, hbound⟩ :=
      exists_aperiodic_recurrenceAmplitude_upper N Q hN hQ
    refine ⟨n, hn, hnQ, ?_⟩
    rw [clockRecurrenceAmplitude_eq N n (aperiodicProbability N)
      (aperiodicProbability_nonneg N hN)]
    exact hbound

end RHTower.FiniteJet
