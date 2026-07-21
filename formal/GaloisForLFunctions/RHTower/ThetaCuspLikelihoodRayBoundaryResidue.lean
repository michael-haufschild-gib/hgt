import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEisensteinMassShell

/-!
# The theta-likelihood ray is the modular boundary residue

The positive higher-likelihood measure is not finite.  Its Lebesgue-ray sector has an exact
simple-pole residue at the zero-likelihood boundary.  Atom by atom, that ray coefficient is the
desingularized value of the corresponding theta source atom where the first atom vanishes.

Thus modular completion is carried by the infinite ray sector: the atomic likelihood masses
disappear after boundary scaling, while the ray residue remains strictly positive.  All results
are exact and unconditional.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The positive coefficient left by the continuous likelihood rays at the zero-temperature
boundary. -/
def thetaCuspLikelihoodRayBoundaryResidue : ℝ :=
  ∑' k : ℕ, thetaCuspLikelihoodRayWeight (k + 2)

/-- The first theta atom divided by its simple zero in the likelihood coordinate. -/
def thetaCuspLikelihoodBoundaryDesingularizer (x : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (x / 2) * Real.exp x ^ 2 *
    Real.exp (-(Real.pi * Real.exp x ^ 2))

/-- A concrete logarithmic point at which the likelihood coordinate vanishes. -/
def thetaCuspLikelihoodBoundaryPoint : ℝ :=
  Real.log (Real.sqrt (3 / (2 * Real.pi)))

/-- Boundary-renormalized contribution of one likelihood atom-plus-ray channel. -/
def thetaCuspLikelihoodScaledBoundaryTerm (n : ℕ) (B : ℝ) : ℝ :=
  Real.exp (-B * thetaCuspLikelihoodGap n) *
    (B * thetaCuspLikelihoodAtomWeight n + thetaCuspLikelihoodRayWeight n)

/-- Boundary-renormalized response of the complete higher-likelihood measure. -/
def thetaCuspLikelihoodScaledBoundaryResponse (B : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspLikelihoodScaledBoundaryTerm (k + 2) B

/-- Product-shell phase after modular boundary scaling.  Its coefficients are precisely the
surviving ray residues on the two likelihood legs. -/
def thetaCuspLikelihoodRayBoundaryMassShellPhase (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodRayWeight (q.1 + 1) *
        thetaCuspLikelihoodRayWeight (q.2 + 1) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the ray-renormalized product-shell phase. -/
def thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative
    (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodRayWeight (q.1 + 1) *
        thetaCuspLikelihoodRayWeight (q.2 + 1) : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Full boundary-scaled shell before setting `B=0`. -/
def thetaCuspLikelihoodScaledMassShellPhase (k : ℕ) (B : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
        thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

/-- Spectral derivative of the full boundary-scaled shell. -/
def thetaCuspLikelihoodScaledMassShellPhaseDerivative
    (k : ℕ) (B : ℝ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
        thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B : ℝ) : ℂ) *
      (Complex.I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (Complex.I * (thetaFactorPairLogDisplacement q : ℂ) * z)

theorem thetaCuspLikelihoodBoundaryDesingularizer_pos (x : ℝ) :
    0 < thetaCuspLikelihoodBoundaryDesingularizer x := by
  unfold thetaCuspLikelihoodBoundaryDesingularizer
  positivity

/-- The first atom has exactly one factor of the intrinsic likelihood coordinate. -/
theorem thetaCuspSourceTerm_one_eq_likelihoodCoordinate_mul_desingularizer (x : ℝ) :
    thetaCuspSourceTerm x 1 =
      thetaCuspLikelihoodCoordinate x *
        thetaCuspLikelihoodBoundaryDesingularizer x := by
  unfold thetaCuspSourceTerm thetaCuspSeed thetaCuspLikelihoodCoordinate
    thetaCuspLikelihoodBoundaryDesingularizer
  norm_num
  ring

/-- The chosen boundary point has zero likelihood coordinate. -/
theorem thetaCuspLikelihoodCoordinate_boundaryPoint :
    thetaCuspLikelihoodCoordinate thetaCuspLikelihoodBoundaryPoint = 0 := by
  have hr : 0 < 3 / (2 * Real.pi) := by positivity
  have hs : 0 < Real.sqrt (3 / (2 * Real.pi)) := Real.sqrt_pos.2 hr
  unfold thetaCuspLikelihoodBoundaryPoint thetaCuspLikelihoodCoordinate
  rw [Real.exp_log hs, Real.sq_sqrt hr.le]
  field_simp [Real.pi_ne_zero]
  ring

/-- Polynomial-Gaussian normal form used at the zero-likelihood boundary. -/
private theorem thetaCuspSourceTerm_eq_boundaryScaleForm (x : ℝ) (n : ℕ) :
    thetaCuspSourceTerm x n =
      Real.exp (x / 2) * 2 * Real.pi * Real.exp x ^ 2 * (n : ℝ) ^ 2 *
        (2 * (Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2 - 3) *
        Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  ring

/-- **Atomwise modular boundary law.**  At the first-atom zero, each theta atom is exactly its
likelihood-ray coefficient times the common positive desingularizer. -/
theorem thetaCuspSourceTerm_eq_desingularizer_mul_likelihoodRayWeight
    {x : ℝ} (hx : thetaCuspLikelihoodCoordinate x = 0) (n : ℕ) :
    thetaCuspSourceTerm x n =
      thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodRayWeight n := by
  have hy : Real.pi * Real.exp x ^ 2 = 3 / 2 := by
    unfold thetaCuspLikelihoodCoordinate at hx
    linarith
  rw [thetaCuspSourceTerm_eq_boundaryScaleForm]
  unfold thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodRayWeight
    thetaCuspLikelihoodGap
  rw [hy]
  have hexp :
      Real.exp (-(3 / 2 : ℝ) * (n : ℝ) ^ 2) =
        Real.exp (-(3 / 2 : ℝ)) *
          Real.exp (-(3 / 2 : ℝ) * ((n : ℝ) ^ 2 - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem summable_thetaCuspLikelihoodAtomWeight_shift :
    Summable (fun k : ℕ => thetaCuspLikelihoodAtomWeight (k + 2)) := by
  have h4 : Summable (fun k : ℕ =>
      ((k + 2 : ℕ) : ℝ) ^ 4 *
        Real.exp (-(3 / 2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 2)) :=
    ((summable_pow_mul_exp_neg_nat_sq 4 (by norm_num : (0 : ℝ) < 3 / 2)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h))
  have hscaled := h4.mul_left (Real.exp (3 / 2 : ℝ))
  convert hscaled using 1
  funext k
  unfold thetaCuspLikelihoodAtomWeight thetaCuspLikelihoodGap
  rw [show -(3 / 2 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ 2 - 1) =
      3 / 2 + (-(3 / 2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 2) by ring,
    Real.exp_add]
  ring

theorem summable_thetaCuspLikelihoodRayWeight_shift :
    Summable (fun k : ℕ => thetaCuspLikelihoodRayWeight (k + 2)) := by
  have h4 : Summable (fun k : ℕ =>
      ((k + 2 : ℕ) : ℝ) ^ 4 *
        Real.exp (-(3 / 2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 2)) :=
    ((summable_pow_mul_exp_neg_nat_sq 4 (by norm_num : (0 : ℝ) < 3 / 2)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h))
  have h2 : Summable (fun k : ℕ =>
      ((k + 2 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(3 / 2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 2)) :=
    ((summable_pow_mul_exp_neg_nat_sq 2 (by norm_num : (0 : ℝ) < 3 / 2)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h))
  have hscaled := (h4.sub h2).mul_left
    (Real.exp (3 / 2 : ℝ) * (3 / 2 : ℝ))
  convert hscaled using 1
  funext k
  unfold thetaCuspLikelihoodRayWeight thetaCuspLikelihoodGap
  rw [show -(3 / 2 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ 2 - 1) =
      3 / 2 + (-(3 / 2 : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 2) by ring,
    Real.exp_add]
  ring

theorem thetaCuspLikelihoodRayBoundaryResidue_pos :
    0 < thetaCuspLikelihoodRayBoundaryResidue := by
  unfold thetaCuspLikelihoodRayBoundaryResidue
  exact summable_thetaCuspLikelihoodRayWeight_shift.tsum_pos
    (fun k => (thetaCuspLikelihoodRayWeight_pos (n := k + 2) (by omega)).le)
    0 (thetaCuspLikelihoodRayWeight_pos (n := 2) (by norm_num))

/-- On a prime arithmetic shell, every factor pair contains the ground index `1`; its likelihood
ray weight is zero. -/
theorem thetaCuspLikelihoodRayWeight_pair_mul_eq_zero_of_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) :
    thetaCuspLikelihoodRayWeight (q.1 + 1) *
      thetaCuspLikelihoodRayWeight (q.2 + 1) = 0 := by
  have hprod : (q.1 + 1) * (q.2 + 1) = k := (Finset.mem_filter.mp hq).2
  have hdiv : q.1 + 1 ∣ k := ⟨q.2 + 1, hprod.symm⟩
  rcases hk.eq_one_or_self_of_dvd (q.1 + 1) hdiv with ha | ha
  · have hq0 : q.1 = 0 := by omega
    simp [hq0, thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]
  · have hprod' := hprod
    rw [ha] at hprod'
    have hb : q.2 + 1 = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hk.pos
      calc
        k * (q.2 + 1) = k := hprod'
        _ = k * 1 := by ring
    have hq0 : q.2 = 0 := by omega
    simp [hq0, thetaCuspLikelihoodRayWeight, thetaCuspLikelihoodGap]

/-- A prime product fibre contains only its two ground/higher factorizations. -/
theorem thetaFactorPair_indices_of_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) :
    (q.1 + 1 = 1 ∧ q.2 + 1 = k) ∨
      (q.1 + 1 = k ∧ q.2 + 1 = 1) := by
  have hprod : (q.1 + 1) * (q.2 + 1) = k := (Finset.mem_filter.mp hq).2
  have hdiv : q.1 + 1 ∣ k := ⟨q.2 + 1, hprod.symm⟩
  rcases hk.eq_one_or_self_of_dvd (q.1 + 1) hdiv with ha | ha
  · exact Or.inl ⟨ha, by simpa [ha] using hprod⟩
  · have hprod' := hprod
    rw [ha] at hprod'
    have hb : q.2 + 1 = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hk.pos
      calc
        k * (q.2 + 1) = k := hprod'
        _ = k * 1 := by ring
    exact Or.inr ⟨ha, hb⟩

/-- The ground likelihood channel is exactly the boundary coordinate itself. -/
@[simp] theorem thetaCuspLikelihoodScaledBoundaryTerm_one (B : ℝ) :
    thetaCuspLikelihoodScaledBoundaryTerm 1 B = B := by
  simp [thetaCuspLikelihoodScaledBoundaryTerm, thetaCuspLikelihoodGap,
    thetaCuspLikelihoodAtomWeight, thetaCuspLikelihoodRayWeight]

/-- On a prime shell, both ordered factor pairs have one ground leg and the same higher leg. -/
theorem thetaCuspLikelihoodScaledBoundaryTerm_pair_mul_eq_prime
    {k : ℕ} (hk : k.Prime) {q : ℕ × ℕ}
    (hq : q ∈ thetaPositiveFactorPairs k) (B : ℝ) :
    thetaCuspLikelihoodScaledBoundaryTerm (q.1 + 1) B *
        thetaCuspLikelihoodScaledBoundaryTerm (q.2 + 1) B =
      B * thetaCuspLikelihoodScaledBoundaryTerm k B := by
  rcases thetaFactorPair_indices_of_prime hk hq with h | h
  · rw [h.1, h.2, thetaCuspLikelihoodScaledBoundaryTerm_one]
  · rw [h.1, h.2, thetaCuspLikelihoodScaledBoundaryTerm_one]
    ring

/-- **Exact prime first-boundary-layer factorization.**  The full scaled prime shell is the
strictly oriented atomic shell multiplied by `B` and one positive higher-channel amplitude. -/
theorem thetaCuspLikelihoodScaledMassShellPhase_eq_primeBoundaryLayer
    {k : ℕ} (hk : k.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodScaledMassShellPhase k B z =
      ((B * thetaCuspLikelihoodScaledBoundaryTerm k B : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  unfold thetaCuspLikelihoodScaledMassShellPhase thetaProductFiberCenteredPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodScaledBoundaryTerm_pair_mul_eq_prime hk hq]

/-- The same prime boundary-layer factorization holds for the spectral derivative. -/
theorem thetaCuspLikelihoodScaledMassShellPhaseDerivative_eq_primeBoundaryLayer
    {k : ℕ} (hk : k.Prime) (B : ℝ) (z : ℂ) :
    thetaCuspLikelihoodScaledMassShellPhaseDerivative k B z =
      ((B * thetaCuspLikelihoodScaledBoundaryTerm k B : ℝ) : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber]
  unfold thetaCuspLikelihoodScaledMassShellPhaseDerivative
    thetaProductFiberCenteredPhaseDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [thetaCuspLikelihoodScaledBoundaryTerm_pair_mul_eq_prime hk hq]
  push_cast
  ring

/-- Every scaled channel has the ray weight as its continuous boundary value. -/
@[simp] theorem thetaCuspLikelihoodScaledBoundaryTerm_zero (n : ℕ) :
    thetaCuspLikelihoodScaledBoundaryTerm n 0 =
      thetaCuspLikelihoodRayWeight n := by
  simp [thetaCuspLikelihoodScaledBoundaryTerm]

/-- Away from the endpoint, dividing a scaled prime shell by its forced simple zero leaves the
single higher-channel amplitude multiplying the original arithmetic shell. -/
theorem thetaCuspLikelihoodScaledPrimeMassShellPhase_div_boundaryCoordinate
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : 0 < B) (z : ℂ) :
    (B : ℂ)⁻¹ * thetaCuspLikelihoodScaledMassShellPhase k B z =
      (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z := by
  rw [thetaCuspLikelihoodScaledMassShellPhase_eq_primeBoundaryLayer hk]
  push_cast
  field_simp [hB.ne']

/-- The same exact cancellation holds for the differentiated shell. -/
theorem thetaCuspLikelihoodScaledPrimeMassShellPhaseDerivative_div_boundaryCoordinate
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : 0 < B) (z : ℂ) :
    (B : ℂ)⁻¹ * thetaCuspLikelihoodScaledMassShellPhaseDerivative k B z =
      (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z := by
  rw [thetaCuspLikelihoodScaledMassShellPhaseDerivative_eq_primeBoundaryLayer hk]
  push_cast
  field_simp [hB.ne']

/-- **Prime first-boundary-layer limit.**  Although the boundary-scaled prime shell vanishes,
division by its forced simple zero converges to the nonzero ray-weighted arithmetic shell. -/
theorem tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhase_div_nhdsGT_zero
    {k : ℕ} (hk : k.Prime) (z : ℂ) :
    Tendsto
      (fun B : ℝ => (B : ℂ)⁻¹ *
        thetaCuspLikelihoodScaledMassShellPhase k B z)
      (𝓝[>] 0)
      (𝓝 ((thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z)) := by
  have hcont : ContinuousAt
      (fun B : ℝ => (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z) 0 := by
    unfold thetaCuspLikelihoodScaledBoundaryTerm
    fun_prop
  have hlim : Tendsto
      (fun B : ℝ => (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z)
      (𝓝[>] 0)
      (𝓝 ((thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhase k z)) := by
    simpa using hcont.tendsto.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with B hB
  exact (thetaCuspLikelihoodScaledPrimeMassShellPhase_div_boundaryCoordinate
    hk hB z).symm

/-- The differentiated first boundary layer converges to the correspondingly ray-weighted
arithmetic derivative. -/
theorem tendsto_thetaCuspLikelihoodScaledPrimeMassShellPhaseDerivative_div_nhdsGT_zero
    {k : ℕ} (hk : k.Prime) (z : ℂ) :
    Tendsto
      (fun B : ℝ => (B : ℂ)⁻¹ *
        thetaCuspLikelihoodScaledMassShellPhaseDerivative k B z)
      (𝓝[>] 0)
      (𝓝 ((thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z)) := by
  have hcont : ContinuousAt
      (fun B : ℝ => (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z) 0 := by
    unfold thetaCuspLikelihoodScaledBoundaryTerm
    fun_prop
  have hlim : Tendsto
      (fun B : ℝ => (thetaCuspLikelihoodScaledBoundaryTerm k B : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z)
      (𝓝[>] 0)
      (𝓝 ((thetaCuspLikelihoodRayWeight k : ℂ) *
        thetaCuspLikelihoodMassShellPhaseDerivative k z)) := by
    simpa using hcont.tendsto.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with B hB
  exact (thetaCuspLikelihoodScaledPrimeMassShellPhaseDerivative_div_boundaryCoordinate
    hk hB z).symm

/-- Every prime boundary layer is strictly positive away from the endpoint. -/
theorem thetaCuspLikelihoodScaledBoundaryTerm_pos
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodScaledBoundaryTerm n B := by
  have hgap := thetaCuspLikelihoodGap_pos hn
  have hAtom := thetaCuspLikelihoodAtomWeight_pos
    (n := n) (lt_of_lt_of_le (by omega) hn)
  have hRay := thetaCuspLikelihoodRayWeight_pos hn
  unfold thetaCuspLikelihoodScaledBoundaryTerm
  exact mul_pos (Real.exp_pos _)
    (add_pos (mul_pos hB hAtom) hRay)

/-- **Prime orientation survives every positive likelihood temperature.**  Boundary scaling only
forces a first-order zero; after the positive scalar factor, the arithmetic current keeps its
strict upper-half-plane sign. -/
theorem thetaCuspLikelihoodScaledPrimeMassShellPhase_current_lt_zero
    {k : ℕ} (hk : k.Prime) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspLikelihoodScaledMassShellPhaseDerivative k B z *
      (starRingEnd ℂ) (thetaCuspLikelihoodScaledMassShellPhase k B z)).im < 0 := by
  rw [thetaCuspLikelihoodScaledMassShellPhaseDerivative_eq_primeBoundaryLayer hk,
    thetaCuspLikelihoodScaledMassShellPhase_eq_primeBoundaryLayer hk]
  let c : ℝ := B * thetaCuspLikelihoodScaledBoundaryTerm k B
  have hc : 0 < c := mul_pos hB
    (thetaCuspLikelihoodScaledBoundaryTerm_pos hk.two_le hB)
  have hbase := thetaCuspLikelihoodMassShellPhase_current_lt_zero hk.one_lt hz
  have heq :
      (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
        (starRingEnd ℂ) ((c : ℂ) * thetaCuspLikelihoodMassShellPhase k z)).im =
        c ^ 2 *
          (thetaCuspLikelihoodMassShellPhaseDerivative k z *
            (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im := by
    rw [map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  change (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
    (starRingEnd ℂ) ((c : ℂ) * thetaCuspLikelihoodMassShellPhase k z)).im < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hbase

/-- **The first boundary layer retains strict prime orientation.**  The zeroth-order prime shell
is annihilated, but the limiting phase and derivative after division by the boundary coordinate
still have strictly negative Hermitian current in the upper half-plane. -/
theorem thetaCuspLikelihoodPrimeFirstBoundaryLayer_current_lt_zero
    {k : ℕ} (hk : k.Prime) {z : ℂ} (hz : 0 < z.im) :
    (((thetaCuspLikelihoodRayWeight k : ℂ) *
          thetaCuspLikelihoodMassShellPhaseDerivative k z) *
        (starRingEnd ℂ) ((thetaCuspLikelihoodRayWeight k : ℂ) *
          thetaCuspLikelihoodMassShellPhase k z)).im < 0 := by
  let c : ℝ := thetaCuspLikelihoodRayWeight k
  have hc : 0 < c := thetaCuspLikelihoodRayWeight_pos hk.two_le
  have hbase := thetaCuspLikelihoodMassShellPhase_current_lt_zero hk.one_lt hz
  have heq :
      (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
        (starRingEnd ℂ) ((c : ℂ) * thetaCuspLikelihoodMassShellPhase k z)).im =
        c ^ 2 *
          (thetaCuspLikelihoodMassShellPhaseDerivative k z *
            (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im := by
    rw [map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  change (((c : ℂ) * thetaCuspLikelihoodMassShellPhaseDerivative k z) *
    (starRingEnd ℂ) ((c : ℂ) * thetaCuspLikelihoodMassShellPhase k z)).im < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hbase

/-- **Prime-shell boundary annihilation.**  Modular boundary renormalization removes every prime
likelihood mass-shell phase: only pairs with two genuinely higher indices survive. -/
theorem thetaCuspLikelihoodRayBoundaryMassShellPhase_eq_zero_of_prime
    {k : ℕ} (hk : k.Prime) (z : ℂ) :
    thetaCuspLikelihoodRayBoundaryMassShellPhase k z = 0 := by
  unfold thetaCuspLikelihoodRayBoundaryMassShellPhase
  apply Finset.sum_eq_zero
  intro q hq
  rw [thetaCuspLikelihoodRayWeight_pair_mul_eq_zero_of_prime hk hq]
  simp

/-- The derivative is annihilated on prime shells as well. -/
theorem thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative_eq_zero_of_prime
    {k : ℕ} (hk : k.Prime) (z : ℂ) :
    thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative k z = 0 := by
  unfold thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative
  apply Finset.sum_eq_zero
  intro q hq
  rw [thetaCuspLikelihoodRayWeight_pair_mul_eq_zero_of_prime hk hq]
  simp

/-- Atomic arithmetic orientation is strict on every prime shell in the upper half-plane, but its
entire ray-renormalized boundary image is zero.  This is the exact orientation-loss seam. -/
theorem thetaCuspLikelihood_primeMassShell_atomicOrientation_rayBoundaryCollapse
    {k : ℕ} (hk : k.Prime) {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspLikelihoodMassShellPhaseDerivative k z *
        (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im < 0 ∧
      thetaCuspLikelihoodRayBoundaryMassShellPhase k z = 0 ∧
      thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative k z = 0 := by
  exact ⟨thetaCuspLikelihoodMassShellPhase_current_lt_zero hk.one_lt hz,
    thetaCuspLikelihoodRayBoundaryMassShellPhase_eq_zero_of_prime hk z,
    thetaCuspLikelihoodRayBoundaryMassShellPhaseDerivative_eq_zero_of_prime hk z⟩

/-- The likelihood carrier has genuinely infinite total mass.  One positive Lebesgue ray already
forces this; exponential tilting, rather than finiteness, makes its interior response integrable.
-/
theorem thetaCuspHigherLikelihoodSpectralMeasure_univ_eq_top :
    thetaCuspHigherLikelihoodSpectralMeasure Set.univ = ⊤ := by
  unfold thetaCuspHigherLikelihoodSpectralMeasure
  have hle := Measure.le_sum
    (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  apply top_unique
  calc
    ⊤ = thetaCuspAtomLikelihoodSpectralMeasure 2 Set.univ := by
      symm
      unfold thetaCuspAtomLikelihoodSpectralMeasure
      simp [thetaCuspLikelihoodGap, thetaCuspLikelihoodRayWeight,
        thetaCuspLikelihoodAtomWeight]
      apply ENNReal.mul_top
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    _ ≤ (Measure.sum fun k : ℕ =>
        thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) Set.univ := hle Set.univ

/-- The complete theta source at the zero-likelihood boundary is precisely the positive ray
residue times the first-atom desingularizer. -/
theorem thetaCuspFullSource_eq_desingularizer_mul_likelihoodRayBoundaryResidue
    {x : ℝ} (hx : thetaCuspLikelihoodCoordinate x = 0) :
    thetaCuspFullSource x =
      thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodRayBoundaryResidue := by
  have hs := summable_thetaCuspSourceTerm x
  have hhead : (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add]
    rw [thetaCuspSourceTerm_one_eq_likelihoodCoordinate_mul_desingularizer, hx,
      zero_mul]
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  calc
    thetaCuspFullSource x = ∑' k : ℕ, thetaCuspSourceTerm x (k + 2) := by
      rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 2, hhead, zero_add]
    _ = ∑' k : ℕ, thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodRayWeight (k + 2) := by
      apply tsum_congr
      intro k
      exact thetaCuspSourceTerm_eq_desingularizer_mul_likelihoodRayWeight hx (k + 2)
    _ = thetaCuspLikelihoodBoundaryDesingularizer x *
        thetaCuspLikelihoodRayBoundaryResidue := by
      rw [tsum_mul_left]
      rfl

theorem thetaCuspFullSource_pos_of_likelihoodCoordinate_eq_zero
    {x : ℝ} (hx : thetaCuspLikelihoodCoordinate x = 0) :
    0 < thetaCuspFullSource x := by
  rw [thetaCuspFullSource_eq_desingularizer_mul_likelihoodRayBoundaryResidue hx]
  exact mul_pos (thetaCuspLikelihoodBoundaryDesingularizer_pos x)
    thetaCuspLikelihoodRayBoundaryResidue_pos

/-- At positive temperature, the desingularized term is exactly `B` times the original singular
atom-plus-ray response. -/
theorem thetaCuspLikelihoodScaledBoundaryTerm_eq_mul_spectralTerm
    {n : ℕ} {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodScaledBoundaryTerm n B =
      B * thetaCuspAtomLikelihoodSpectralTerm n B := by
  unfold thetaCuspLikelihoodScaledBoundaryTerm thetaCuspLikelihoodAtomWeight
    thetaCuspLikelihoodRayWeight thetaCuspAtomLikelihoodSpectralTerm
  field_simp [hB.ne']

/-- The scaled response extends the positive-temperature product `B L(B)`. -/
theorem thetaCuspLikelihoodScaledBoundaryResponse_eq_mul_response
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodScaledBoundaryResponse B =
      B * thetaCuspHigherLikelihoodSpectralResponse B := by
  unfold thetaCuspLikelihoodScaledBoundaryResponse
    thetaCuspHigherLikelihoodSpectralResponse
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  exact thetaCuspLikelihoodScaledBoundaryTerm_eq_mul_spectralTerm hB

/-- The continuous extension takes the exact ray-residue value at `B=0`. -/
@[simp] theorem thetaCuspLikelihoodScaledBoundaryResponse_zero :
    thetaCuspLikelihoodScaledBoundaryResponse 0 =
      thetaCuspLikelihoodRayBoundaryResidue := by
  unfold thetaCuspLikelihoodScaledBoundaryResponse
    thetaCuspLikelihoodRayBoundaryResidue thetaCuspLikelihoodScaledBoundaryTerm
  simp

/-- **Exact simple-pole boundary law.**  After multiplication by the likelihood coordinate, the
complete response converges to the strictly positive ray residue. -/
theorem tendsto_thetaCuspLikelihoodScaledBoundaryResponse_nhdsGT_zero :
    Tendsto thetaCuspLikelihoodScaledBoundaryResponse (𝓝[>] 0)
      (𝓝 thetaCuspLikelihoodRayBoundaryResidue) := by
  have hmajor : Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomWeight (k + 2) +
        thetaCuspLikelihoodRayWeight (k + 2)) :=
    summable_thetaCuspLikelihoodAtomWeight_shift.add
      summable_thetaCuspLikelihoodRayWeight_shift
  have hpoint (k : ℕ) : Tendsto
      (fun B : ℝ => thetaCuspLikelihoodScaledBoundaryTerm (k + 2) B)
      (𝓝[>] 0) (𝓝 (thetaCuspLikelihoodRayWeight (k + 2))) := by
    have hcont : ContinuousAt
        (fun B : ℝ => thetaCuspLikelihoodScaledBoundaryTerm (k + 2) B) 0 := by
      unfold thetaCuspLikelihoodScaledBoundaryTerm
      fun_prop
    simpa [thetaCuspLikelihoodScaledBoundaryTerm] using hcont.tendsto.mono_left inf_le_left
  have hupper : ∀ᶠ B : ℝ in 𝓝[>] 0, B < 1 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hbound : ∀ᶠ B : ℝ in 𝓝[>] 0, ∀ k : ℕ,
      ‖thetaCuspLikelihoodScaledBoundaryTerm (k + 2) B‖ ≤
        thetaCuspLikelihoodAtomWeight (k + 2) +
          thetaCuspLikelihoodRayWeight (k + 2) := by
    filter_upwards [self_mem_nhdsWithin, hupper] with B hB hB1
    intro k
    have hgap := thetaCuspLikelihoodGap_pos (n := k + 2) (by omega)
    have hAtom := thetaCuspLikelihoodAtomWeight_pos
      (n := k + 2) (by omega)
    have hRay := thetaCuspLikelihoodRayWeight_pos
      (n := k + 2) (by omega)
    have hExp : Real.exp (-B * thetaCuspLikelihoodGap (k + 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB.le) hgap.le
    have hinside0 :
        0 ≤ B * thetaCuspLikelihoodAtomWeight (k + 2) +
          thetaCuspLikelihoodRayWeight (k + 2) :=
      add_nonneg (mul_nonneg hB.le hAtom.le) hRay.le
    have hinside :
        B * thetaCuspLikelihoodAtomWeight (k + 2) +
            thetaCuspLikelihoodRayWeight (k + 2) ≤
          thetaCuspLikelihoodAtomWeight (k + 2) +
            thetaCuspLikelihoodRayWeight (k + 2) := by
      nlinarith
    unfold thetaCuspLikelihoodScaledBoundaryTerm
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · calc
        Real.exp (-B * thetaCuspLikelihoodGap (k + 2)) *
              (B * thetaCuspLikelihoodAtomWeight (k + 2) +
                thetaCuspLikelihoodRayWeight (k + 2)) ≤
            1 * (B * thetaCuspLikelihoodAtomWeight (k + 2) +
                thetaCuspLikelihoodRayWeight (k + 2)) :=
          mul_le_mul_of_nonneg_right hExp hinside0
        _ ≤ thetaCuspLikelihoodAtomWeight (k + 2) +
            thetaCuspLikelihoodRayWeight (k + 2) := by simpa using hinside
    · exact mul_nonneg (Real.exp_pos _).le hinside0
  simpa [thetaCuspLikelihoodScaledBoundaryResponse,
    thetaCuspLikelihoodRayBoundaryResidue] using
    tendsto_tsum_of_dominated_convergence hmajor hpoint hbound

/-- The unscaled likelihood response cannot have a finite right-boundary limit. -/
theorem not_exists_tendsto_thetaCuspHigherLikelihoodSpectralResponse_nhdsGT_zero :
    ¬ ∃ L : ℝ, Tendsto thetaCuspHigherLikelihoodSpectralResponse
      (𝓝[>] 0) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hB : Tendsto (fun B : ℝ => B) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hprod : Tendsto
      (fun B : ℝ => B * thetaCuspHigherLikelihoodSpectralResponse B)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hB.mul hL
  have heq :
      (fun B : ℝ => B * thetaCuspHigherLikelihoodSpectralResponse B) =ᶠ[𝓝[>] 0]
        thetaCuspLikelihoodScaledBoundaryResponse := by
    filter_upwards [self_mem_nhdsWithin] with B hBpos
    exact (thetaCuspLikelihoodScaledBoundaryResponse_eq_mul_response hBpos).symm
  have hres : Tendsto
      (fun B : ℝ => B * thetaCuspHigherLikelihoodSpectralResponse B)
      (𝓝[>] 0) (𝓝 thetaCuspLikelihoodRayBoundaryResidue) :=
    tendsto_thetaCuspLikelihoodScaledBoundaryResponse_nhdsGT_zero.congr' heq.symm
  have hz : thetaCuspLikelihoodRayBoundaryResidue = 0 :=
    tendsto_nhds_unique hres hprod
  exact thetaCuspLikelihoodRayBoundaryResidue_pos.ne' hz

end

end RHTower
