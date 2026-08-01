import GaloisForLFunctions.RHTower.GammaJacobiArtanhTransportCoupling

/-!
# Gamma--Jacobi tail/connection transgression

The singular diagonal normalization forced by the odd Gamma--Jacobi log incidence turns every
positive-source coefficient tail into a Szegő tail.  Its first surviving coordinate is exactly the
connection defect of the finite artanh head.  Consequently, removing one more absolute Jacobi mode
changes the normalized tail kernel by the rank-one tensor of the two connection defects.

At the source-selected prime capacities this boundary coordinate is literally the first nonzero
coordinate of the existing coherent residual.  Every common surviving adjacent coordinate pair
recovers the prime label projectively.  Generic Szegő/coherent-state facts are classical; the
content here is their exact weld to the actual `SR-38` residual and `SR-46` successor connection.

No Xi zero, RH premise, target moment, or computation is used.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Singular readout of the `K`-th actual odd Gamma--Jacobi coefficient. -/
def gammaOddJacobiTailBoundaryReadout (K : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ K * gammaOddJacobiCoefficient K t /
    (semilocalArchimedeanJacobiNormalization (2 * K + 1) *
      semilocalArchimedeanCharacteristic t * Real.tanh t)

/-- On the positive source half-line, the normalized first-tail readout is the exact finite-head
connection defect. -/
theorem gammaOddJacobiTailBoundaryReadout_eq
    (K : ℕ) {t : ℝ} (ht : 0 < t) :
    gammaOddJacobiTailBoundaryReadout K t = Real.tanh t ^ (2 * K) := by
  have hc := (semilocalArchimedeanJacobiNormalization_pos (2 * K + 1)).ne'
  have hphi := (semilocalArchimedeanCharacteristic_pos t).ne'
  have hx : Real.tanh t ≠ 0 := (tanh_pos_of_pos ht).ne'
  rw [gammaOddJacobiTailBoundaryReadout, gammaOddJacobiCoefficient]
  field_simp
  have hsign : ((-1 : ℝ) ^ K) ^ 2 = 1 := by
    rw [sq, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hsign]
  ring

/-- **Tail/connection transgression.**  The derivative missing from the `K`-mode artanh head is
exactly the singular readout of the first omitted actual Jacobi mode. -/
theorem gammaOddJacobiLogHead_connection_defect_eq_tailBoundary
    (K : ℕ) {t : ℝ} (ht : 0 < t) :
    1 - deriv (gammaOddJacobiLogHead K) t =
      gammaOddJacobiTailBoundaryReadout K t := by
  rw [(hasDerivAt_gammaOddJacobiLogHead K t).deriv,
    gammaOddJacobiTailBoundaryReadout_eq K ht]
  ring

/-- Projective node read from two consecutive actual odd Gamma--Jacobi tail coordinates. -/
def gammaOddJacobiTailProjectiveNode (K : ℕ) (t : ℝ) : ℝ :=
  -(semilocalArchimedeanJacobiNormalization (2 * K + 1) *
      gammaOddJacobiCoefficient (K + 1) t) /
    (semilocalArchimedeanJacobiNormalization (2 * (K + 1) + 1) *
      gammaOddJacobiCoefficient K t)

/-- Every consecutive tail pair reads the same squared hyperbolic source node. -/
theorem gammaOddJacobiTailProjectiveNode_eq
    (K : ℕ) {t : ℝ} (ht : 0 < t) :
    gammaOddJacobiTailProjectiveNode K t = Real.tanh t ^ 2 := by
  have hc0 := (semilocalArchimedeanJacobiNormalization_pos (2 * K + 1)).ne'
  have hc1 :=
    (semilocalArchimedeanJacobiNormalization_pos (2 * (K + 1) + 1)).ne'
  have hphi := (semilocalArchimedeanCharacteristic_pos t).ne'
  have hx : Real.tanh t ≠ 0 := (tanh_pos_of_pos ht).ne'
  rw [gammaOddJacobiTailProjectiveNode, gammaOddJacobiCoefficient,
    gammaOddJacobiCoefficient]
  rw [pow_succ]
  field_simp
  ring

/-- Two consecutive surviving tail modes determine every positive source point. -/
theorem gammaOddJacobiTailProjectiveNode_injectiveOn_pos
    (K : ℕ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaOddJacobiTailProjectiveNode K t =
        gammaOddJacobiTailProjectiveNode K u ↔
      t = u := by
  rw [gammaOddJacobiTailProjectiveNode_eq K ht,
    gammaOddJacobiTailProjectiveNode_eq K hu]
  constructor
  · intro h
    apply Real.tanh_injective
    nlinarith [tanh_pos_of_pos ht, tanh_pos_of_pos hu]
  · intro h
    subst u
    rfl

/-- Singular boundary readout of the first nonzero coordinate in the actual adaptive `SR-38`
residual. -/
def gammaOddJacobiPrimeResidualBoundaryReadout (p : Nat.Primes) : ℝ :=
  (-1 : ℝ) ^ gammaOddJacobiPrimeCapacity p *
      HTGeometry.adaptiveMercerResidualFeature
        gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p
          (gammaOddJacobiPrimeCapacity p) /
    (semilocalArchimedeanJacobiNormalization
        (2 * gammaOddJacobiPrimeCapacity p + 1) *
      semilocalArchimedeanCharacteristic (Real.log (p : ℝ)) *
      Real.tanh (Real.log (p : ℝ)))

/-- The first surviving adaptive residual coordinate is the exact prime-capacity connection
defect. -/
theorem gammaOddJacobiPrimeResidualBoundaryReadout_eq (p : Nat.Primes) :
    gammaOddJacobiPrimeResidualBoundaryReadout p =
      Real.tanh (Real.log (p : ℝ)) ^ (2 * gammaOddJacobiPrimeCapacity p) := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [gammaOddJacobiPrimeResidualBoundaryReadout]
  unfold HTGeometry.adaptiveMercerResidualFeature gammaOddJacobiPrimeFeature
  rw [if_neg (lt_irrefl _)]
  exact gammaOddJacobiTailBoundaryReadout_eq _ hpLog

/-- **Adaptive `SR-38`/`SR-46` weld.**  At each prime, the missing derivative of the source-selected
log head is the first surviving coherent-residual coordinate under the forced singular readout. -/
theorem gammaOddJacobiPrime_logHead_connection_defect_eq_residualBoundary
    (p : Nat.Primes) :
    1 - deriv
        (gammaOddJacobiLogHead (gammaOddJacobiPrimeCapacity p))
        (Real.log (p : ℝ)) =
      gammaOddJacobiPrimeResidualBoundaryReadout p := by
  rw [gammaOddJacobiPrimeResidualBoundaryReadout_eq p,
    (hasDerivAt_gammaOddJacobiLogHead
      (gammaOddJacobiPrimeCapacity p) (Real.log (p : ℝ))).deriv]
  ring

/-- Projective node read directly from the zero-padded coherent residual at an absolute tail
index. -/
def gammaOddJacobiPrimeResidualProjectiveNode
    (p : Nat.Primes) (K : ℕ) : ℝ :=
  -(semilocalArchimedeanJacobiNormalization (2 * K + 1) *
      HTGeometry.adaptiveMercerResidualFeature
        gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p (K + 1)) /
    (semilocalArchimedeanJacobiNormalization (2 * (K + 1) + 1) *
      HTGeometry.adaptiveMercerResidualFeature
        gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p K)

/-- Any adjacent pair beyond the adaptive cutoff reads the same source node. -/
theorem gammaOddJacobiPrimeResidualProjectiveNode_eq
    (p : Nat.Primes) {K : ℕ} (hK : gammaOddJacobiPrimeCapacity p ≤ K) :
    gammaOddJacobiPrimeResidualProjectiveNode p K =
      Real.tanh (Real.log (p : ℝ)) ^ 2 := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [gammaOddJacobiPrimeResidualProjectiveNode]
  unfold HTGeometry.adaptiveMercerResidualFeature gammaOddJacobiPrimeFeature
  rw [if_neg (by omega), if_neg (by omega)]
  exact gammaOddJacobiTailProjectiveNode_eq K hpLog

/-- Exact rational prime node carried by every surviving adjacent residual pair. -/
theorem gammaOddJacobiPrimeResidualProjectiveNode_eq_rational
    (p : Nat.Primes) {K : ℕ} (hK : gammaOddJacobiPrimeCapacity p ≤ K) :
    gammaOddJacobiPrimeResidualProjectiveNode p K =
      (((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 + 1)) ^ 2 := by
  rw [gammaOddJacobiPrimeResidualProjectiveNode_eq p hK, tanh_log_prime]

/-- **Cofinal projective faithfulness of `SR-38`.**  At every common absolute tail index, equality
of the two-coordinate projective residual nodes is equivalent to equality of prime labels. -/
theorem gammaOddJacobiPrimeResidualProjectiveNode_eq_iff
    (p q : Nat.Primes) {K : ℕ}
    (hpK : gammaOddJacobiPrimeCapacity p ≤ K)
    (hqK : gammaOddJacobiPrimeCapacity q ≤ K) :
    gammaOddJacobiPrimeResidualProjectiveNode p K =
        gammaOddJacobiPrimeResidualProjectiveNode q K ↔
      p = q := by
  rw [gammaOddJacobiPrimeResidualProjectiveNode_eq p hpK,
    gammaOddJacobiPrimeResidualProjectiveNode_eq q hqK]
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hqLog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.prop.one_lt)
  constructor
  · intro h
    have hlog : Real.log (p : ℝ) = Real.log (q : ℝ) :=
      (gammaOddJacobiTailProjectiveNode_injectiveOn_pos K hpLog hqLog).mp (by
        simpa [gammaOddJacobiTailProjectiveNode_eq K hpLog,
          gammaOddJacobiTailProjectiveNode_eq K hqLog] using h)
    apply Subtype.ext
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_log (by exact_mod_cast p.prop.pos : (0 : ℝ) < (p : ℝ)),
      Real.exp_log (by exact_mod_cast q.prop.pos : (0 : ℝ) < (q : ℝ))] at hexp
    exact_mod_cast hexp
  · intro h
    subst q
    rfl

/-- Szegő tail obtained by applying the forced singular Jacobi normalization to every surviving
coordinate. -/
def gammaOddJacobiHardyTailKernel (K : ℕ) (t u : ℝ) : ℝ :=
  ∑' j : ℕ,
    gammaOddJacobiTailBoundaryReadout (K + j) t *
      gammaOddJacobiTailBoundaryReadout (K + j) u

/-- Closed Szegő-kernel form of the normalized actual Gamma--Jacobi tail. -/
theorem gammaOddJacobiHardyTailKernel_eq
    (K : ℕ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaOddJacobiHardyTailKernel K t u =
      (Real.tanh t * Real.tanh u) ^ (2 * K) /
        (1 - (Real.tanh t * Real.tanh u) ^ 2) := by
  let q : ℝ := Real.tanh t * Real.tanh u
  have hxt0 : 0 < Real.tanh t := tanh_pos_of_pos ht
  have hxu0 : 0 < Real.tanh u := tanh_pos_of_pos hu
  have hq0 : 0 < q := mul_pos hxt0 hxu0
  have hq1 : q < 1 := by
    calc
      q < Real.tanh t * 1 := mul_lt_mul_of_pos_left (Real.tanh_lt_one u) hxt0
      _ < 1 := by simpa using Real.tanh_lt_one t
  have hr : ‖q ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    nlinarith
  have hgeom := (hasSum_geometric_of_norm_lt_one hr).mul_left (q ^ (2 * K))
  rw [gammaOddJacobiHardyTailKernel]
  calc
    (∑' j : ℕ,
        gammaOddJacobiTailBoundaryReadout (K + j) t *
          gammaOddJacobiTailBoundaryReadout (K + j) u) =
        ∑' j : ℕ, q ^ (2 * K) * (q ^ 2) ^ j := by
      apply tsum_congr
      intro j
      rw [gammaOddJacobiTailBoundaryReadout_eq _ ht,
        gammaOddJacobiTailBoundaryReadout_eq _ hu]
      dsimp [q]
      rw [show 2 * (K + j) = 2 * K + 2 * j by omega,
        pow_add, pow_add, ← pow_mul, mul_pow]
      ring
    _ = q ^ (2 * K) * (1 - q ^ 2)⁻¹ := hgeom.tsum_eq
    _ = (Real.tanh t * Real.tanh u) ^ (2 * K) /
        (1 - (Real.tanh t * Real.tanh u) ^ 2) := by
      dsimp [q]
      rw [div_eq_mul_inv]

/-- **Rank-one aperture transgression.**  Removing one more normalized absolute Jacobi mode changes
the tail kernel by the tensor product of the two finite-head connection defects. -/
theorem gammaOddJacobiHardyTailKernel_sub_succ
    (K : ℕ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaOddJacobiHardyTailKernel K t u -
        gammaOddJacobiHardyTailKernel (K + 1) t u =
      gammaOddJacobiTailBoundaryReadout K t *
        gammaOddJacobiTailBoundaryReadout K u := by
  rw [gammaOddJacobiHardyTailKernel_eq K ht hu,
    gammaOddJacobiHardyTailKernel_eq (K + 1) ht hu,
    gammaOddJacobiTailBoundaryReadout_eq K ht,
    gammaOddJacobiTailBoundaryReadout_eq K hu]
  let q : ℝ := Real.tanh t * Real.tanh u
  have hxt0 : 0 < Real.tanh t := tanh_pos_of_pos ht
  have hxu0 : 0 < Real.tanh u := tanh_pos_of_pos hu
  have hq0 : 0 < q := mul_pos hxt0 hxu0
  have hq1 : q < 1 := by
    calc
      q < Real.tanh t * 1 := mul_lt_mul_of_pos_left (Real.tanh_lt_one u) hxt0
      _ < 1 := by simpa using Real.tanh_lt_one t
  have hden : 1 - q ^ 2 ≠ 0 := by nlinarith [sq_nonneg q]
  change q ^ (2 * K) / (1 - q ^ 2) -
      q ^ (2 * (K + 1)) / (1 - q ^ 2) =
        Real.tanh t ^ (2 * K) * Real.tanh u ^ (2 * K)
  rw [show 2 * (K + 1) = 2 * K + 2 by omega, pow_add, mul_pow]
  field_simp

end

end RHTower
