import GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw

/-!
# Polynomial-circuit same-draw growth, plateau, and recurrence

For every fixed finite gate alphabet and polynomial depth exponent, this module closes the
thermodynamic entropy condition in the nearest-neighbour same-draw law.  The exact Hilbert-space
dimension is `4 ^ L`; at fixed Choi error `1 / 100`, the complete circuit-tube entropy is bounded
by `10 * 4 ^ L * (2 / 5) ^ (4 ^ L)` and therefore vanishes.

Consequently, all sufficiently large path sizes admit one draw from the ordinary static Gaussian
nearest-neighbour ensemble with a robust laboratory-time complexity ramp, completed-time
polynomial-circuit plateau, and perpetual recurrence--hardness--recurrence alternation.  No Haar
draw or time-dependent drive is introduced.
-/

open Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

private lemma choiBase_le_one_tenth :
    Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) ≤ 1 / 10 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [mul_pow, hsqrt]
    nlinarith [Real.pi_lt_four]

private lemma exp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    congr 1
    norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_one_lt_three]

private lemma exp_nat_half_le_two_pow (D : ℕ) :
    Real.exp ((D : ℝ) / 2) ≤ (2 : ℝ) ^ D := by
  rw [show (D : ℝ) / 2 = (D : ℝ) * (1 / 2 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le exp_half_lt_two.le D

private lemma nat_le_two_pow (g : ℕ) : g ≤ 2 ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ g := one_le_pow₀ (by norm_num)
      omega

private lemma eventually_gatePolynomialExponent_le_fourPow (g k : ℕ) :
    ∀ᶠ L : ℕ in atTop, g * (L ^ k + 1) ≤ 4 ^ L := by
  by_cases hg : g = 0
  · simp [hg]
  have hgpos : (0 : ℝ) < 2 * g := by positivity
  have hlo := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
    (by norm_num : (1 : ℝ) < 4)).bound (one_div_pos.mpr hgpos)
  filter_upwards [hlo, Filter.eventually_ge_atTop 1] with L hL hLone
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hLone)
  have hraw : (L : ℝ) ^ k ≤ (1 / (2 * (g : ℝ))) * (4 : ℝ) ^ L := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ k),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ L)] using hL
  have hreal : (g : ℝ) * ((L : ℝ) ^ k + 1) ≤ (4 : ℝ) ^ L := by
    calc
      (g : ℝ) * ((L : ℝ) ^ k + 1) ≤ (g : ℝ) * (2 * (L : ℝ) ^ k) := by gcongr; linarith
      _ ≤ (g : ℝ) * (2 * ((1 / (2 * (g : ℝ))) * (4 : ℝ) ^ L)) := by gcongr
      _ = (4 : ℝ) ^ L := by field_simp
  exact_mod_cast hreal

private lemma eventually_gatePolynomialPower_le_twoPowFourPow (g k : ℕ) :
    ∀ᶠ L : ℕ in atTop, (g : ℝ) ^ (L ^ k + 1) ≤ (2 : ℝ) ^ (4 ^ L) := by
  filter_upwards [eventually_gatePolynomialExponent_le_fourPow g k] with L hL
  have hgpow : g ^ (L ^ k + 1) ≤ (2 ^ g) ^ (L ^ k + 1) :=
    Nat.pow_le_pow_left (nat_le_two_pow g) _
  have hrewrite : (2 ^ g) ^ (L ^ k + 1) = 2 ^ (g * (L ^ k + 1)) := by
    rw [← pow_mul]
  have hexp : 2 ^ (g * (L ^ k + 1)) ≤ 2 ^ (4 ^ L) :=
    Nat.pow_le_pow_right (by norm_num) hL
  exact_mod_cast hgpow.trans (hrewrite ▸ hexp)

/-- Complete fixed-error Choi circuit-tube entropy for alphabet size `g`, polynomial exponent `k`,
and nearest-neighbour path size `L`. -/
noncomputable def polynomialCircuitChoiEntropyCost (g k L : ℕ) : ℝ :=
  (g : ℝ) ^ (L ^ k + 1) *
    (((4 ^ L : ℕ) : ℝ) * Real.exp (((4 ^ L : ℕ) : ℝ) / 2) *
      Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) ^
        ((4 ^ L : ℕ) - 1))

private lemma twoPow_entropy_major_identity (D : ℕ) (hD : 1 ≤ D) :
    (2 : ℝ) ^ D *
        ((D : ℝ) * (2 : ℝ) ^ D * (1 / 10 : ℝ) ^ (D - 1)) =
      10 * (D : ℝ) * (2 / 5 : ℝ) ^ D := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
  simp only [Nat.succ_sub_one]
  rw [pow_succ]
  rw [show (2 / 5 : ℝ) = 4 * (1 / 10 : ℝ) by norm_num, mul_pow]
  ring_nf
  rw [show (2 : ℝ) ^ (m * 2) = (4 : ℝ) ^ m by
    calc
      (2 : ℝ) ^ (m * 2) = 2 ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num]
  rw [pow_succ]
  rw [pow_succ]
  ring

/-- Explicit eventual majorant for complete polynomial-circuit Choi entropy. -/
theorem eventually_polynomialCircuitChoiEntropyCost_le_major (g k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      polynomialCircuitChoiEntropyCost g k L ≤
        10 * ((4 ^ L : ℕ) : ℝ) * (2 / 5 : ℝ) ^ (4 ^ L) := by
  filter_upwards [eventually_gatePolynomialPower_le_twoPowFourPow g k] with L hgate
  let D : ℕ := 4 ^ L
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hexp := exp_nat_half_le_two_pow D
  have hbase := choiBase_le_one_tenth
  have hbase0 : 0 ≤ Real.sqrt
      (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) := Real.sqrt_nonneg _
  have hbasePow :
      Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) ^ (D - 1) ≤
        (1 / 10 : ℝ) ^ (D - 1) :=
    pow_le_pow_left₀ hbase0 hbase _
  calc
    polynomialCircuitChoiEntropyCost g k L ≤
        (2 : ℝ) ^ D * ((D : ℝ) * (2 : ℝ) ^ D * (1 / 10 : ℝ) ^ (D - 1)) := by
      unfold polynomialCircuitChoiEntropyCost
      dsimp [D] at hgate ⊢
      gcongr
    _ = 10 * (D : ℝ) * (2 / 5 : ℝ) ^ D :=
      twoPow_entropy_major_identity D hD
    _ = 10 * ((4 ^ L : ℕ) : ℝ) * (2 / 5 : ℝ) ^ (4 ^ L) := rfl

/-- Any fixed alphabet and fixed polynomial circuit-depth exponent lose to the full Choi-space
anti-concentration exponent. -/
theorem tendsto_polynomialCircuitChoiEntropyCost_atTop (g k : ℕ) :
    Tendsto (polynomialCircuitChoiEntropyCost g k) atTop (nhds 0) := by
  have hbase : Tendsto
      (fun D : ℕ => (D : ℝ) ^ 1 * (2 / 5 : ℝ) ^ D) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num) (by norm_num)
  have hD : Tendsto (fun L : ℕ => 4 ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hmajor : Tendsto
      (fun L : ℕ => 10 * ((4 ^ L : ℕ) : ℝ) * (2 / 5 : ℝ) ^ (4 ^ L))
      atTop (nhds 0) := by
    simpa [pow_one, mul_assoc] using (hbase.comp hD).const_mul 10
  refine squeeze_zero' (Filter.Eventually.of_forall fun L => ?_)
    (eventually_polynomialCircuitChoiEntropyCost_le_major g k) hmajor
  unfold polynomialCircuitChoiEntropyCost
  positivity

/-- Exact Hilbert-space dimension of the paired-qubit nearest-neighbour path. -/
theorem nearestNeighborPathProjectiveDimension_add_one (L : ℕ) :
    nearestNeighborPathProjectiveDimension L + 1 = 4 ^ L := by
  rw [nearestNeighborPathProjectiveDimension]
  simp only [Config, PairQubit, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_prod, Fintype.card_fin]
  rw [Nat.sub_add_cancel (one_le_pow₀ (by norm_num : 1 ≤ 2))]
  calc
    2 ^ (L * 2) = 2 ^ (2 * L) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ L := by rw [pow_mul]
    _ = 4 ^ L := by norm_num

/-- Complete polynomial-circuit Choi entropy vanishes for the nearest-neighbour path family. -/
theorem tendsto_nearestNeighborPolynomialCircuitChoiEntropyCost_atTop
    (gate : Type*) [Fintype gate] (k : ℕ) :
    Tendsto (fun L : ℕ =>
      (Fintype.card gate : ℝ) ^ (L ^ k + 1) *
        (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
          Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt
            (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)))
      atTop (nhds 0) := by
  convert tendsto_polynomialCircuitChoiEntropyCost_atTop
    (Fintype.card gate) k using 1
  funext L
  rw [nearestNeighborPathProjectiveDimension_add_one]
  rfl

/-- Eventually, polynomial circuit count times one fixed-error Choi tube volume is below one. -/
theorem eventually_nearestNeighborPolynomialCircuitChoiEntropy_lt_one
    (gate : Type*) [Fintype gate] (k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (Fintype.card gate : ℝ) ^ (L ^ k + 1) *
        (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
          Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt
            (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)) < 1 :=
  (tendsto_nearestNeighborPolynomialCircuitChoiEntropyCost_atTop gate k).eventually_lt_const
    (by norm_num)

private lemma explicit_growth_radius_pos {L : ℕ} (hL : 0 < L) :
    0 < 1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)) := by
  letI : NormedRing
      (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
    Matrix.instL2OpNormedRing
  have hmass : 0 ≤ nearestNeighborPathLocalGeneratorMass L := by
    unfold nearestNeighborPathLocalGeneratorMass
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  positivity

private lemma explicit_growth_radius_budget {L : ℕ} (hL : 0 < L) :
    (1 / 10000 : ℝ) * L *
        ((1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))) *
          nearestNeighborPathLocalGeneratorMass L) ≤
      1 / 10000 := by
  letI : NormedRing
      (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
    Matrix.instL2OpNormedRing
  let M := nearestNeighborPathLocalGeneratorMass L
  have hM : 0 ≤ M := by
    dsimp [M, nearestNeighborPathLocalGeneratorMass]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hM1 : 0 < M + 1 := by linarith
  have hratio : M / (M + 1) ≤ 1 := (div_le_one hM1).2 (by linarith)
  calc
    (1 / 10000 : ℝ) * L *
        ((1 / ((L : ℝ) * (M + 1))) * M) =
      (1 / 10000 : ℝ) * (M / (M + 1)) := by field_simp
    _ ≤ (1 / 10000 : ℝ) * 1 := by gcongr
    _ = 1 / 10000 := by ring

/-- For every fixed finite gate alphabet and every polynomial circuit-depth exponent, all
sufficiently large path sizes admit one ordinary static nearest-neighbour Gaussian draw with a
non-vacuous robust laboratory ramp, completed-time polynomial-circuit plateau, and perpetual
recurrence--hardness--recurrence alternation. -/
theorem eventually_exists_nearestNeighborPath_polynomial_sameDraw_growth_plateau_recurrence
    (gate : Type*) [Fintype gate] (k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      ∀ (target : PaddedCircuitWord gate (L ^ k) →
          EuclideanSpace ℂ
            (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
              Fin (nearestNeighborPathProjectiveDimension L + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ identityWord : PaddedCircuitWord gate (L ^ k),
          target identityWord =
            fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)) →
          ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
            p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L
              ((1 / 10000 : ℝ) * L) (1 / 10000 : ℝ) ∧
            NearestNeighborPathCompletedPlateau L (L ^ k) p target
              (Real.sqrt 2 * (1 / 100 : ℝ)) ∧
            NearestNeighborPathChoiRecurrenceHardAlternation L (L ^ k) p target
              (1 / 100 : ℝ) ∧
            ((⌊((1 / 10000 : ℝ) * L) /
                (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
              operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
                (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p)
                  ((1 / 10000 : ℝ) * L)) := by
  filter_upwards [eventually_nearestNeighborPolynomialCircuitChoiEntropy_lt_one gate k,
    Filter.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.pi)] with
      L hentropy hL hLlarge target htarget identityWord hidentity
  have hLpos : 0 < L := by omega
  have heventPos := measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
    hLpos
    (T := (1 / 10000 : ℝ) * L)
    (ε := (1 / 10000 : ℝ))
    (ρ := 1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))
    (by positivity) (by norm_num) (by norm_num)
    (explicit_growth_radius_pos hLpos)
    (explicit_growth_radius_budget hLpos)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (ne_of_gt heventPos)
  have hmaster := nearestNeighborPath_sameDraw_growth_plateau_recurrence
    hp (L ^ k) target htarget identityWord hidentity (by norm_num) hentropy
  have hend := hp.2 ((1 / 10000 : ℝ) * L)
    (by nlinarith : 2048 * Real.pi * (1 / 10000 : ℝ) ≤ (1 / 10000 : ℝ) * L)
    le_rfl le_rfl
  exact ⟨p, hp, hmaster.2.1, hmaster.2.2, hend⟩

end RHTower
