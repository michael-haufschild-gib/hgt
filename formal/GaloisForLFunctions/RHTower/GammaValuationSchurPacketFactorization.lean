import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw

/-!
# Coefficient-faithful Gamma–valuation Schur factorization

Corrected Gamma conductor coordinate is exactly vacuum coordinate of completed half-shifted
prime-valuation Szegő frame.  Consequently, after arbitrary finite coefficient interference,
completed prime energy minus exact Gamma charge square is all remaining valuation-depth energy.
This gives a same-aperture off-diagonal factorization, finite-depth sign preservation, cofinal
completion, and strict separation of every injectively labelled nonzero prime packet.

Construction is entirely source-defined and imports no Xi zero location.  It identifies literal
Gamma conductor Schur cancellation with valuation translation.  It does not identify this
intrinsic response with full CCM/prime–Gamma crossing flow; that coefficientwise transport remains
separate.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem hasSum_finset_sum_real_schur
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (a : ι → ℝ)
    (h : ∀ i ∈ s, HasSum (f i) (a i)) :
    HasSum (fun e => ∑ i ∈ s, f i e) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiSum := h i (Finset.mem_insert_self i s)
      have hsSum := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using hiSum.add hsSum

def gammaValuationSchurPacketResultant
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (e : ℕ) : ℝ :=
  ∑ i, c i * xiTransversePrimeHalfShiftedValuationCoordinate (p i) e

def gammaValuationSchurPacketPrimeEnergy
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j *
    xiTransverseGammaValuationSzegoKernel (p i) (p j)

def gammaValuationSchurPacketGammaCharge
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) : ℝ :=
  ∑ i, c i * (gammaValuationHardyRenormalizer (p i) *
    gammaConductorPrimeNormalizedCross (p i))

def gammaValuationSchurPacketSignedResidual
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) : ℝ :=
  gammaValuationSchurPacketPrimeEnergy p c -
    gammaValuationSchurPacketGammaCharge p c ^ 2 / (9 / 8 : ℝ)

def gammaValuationSchurPacketTailPrefix
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (D : ℕ) : ℝ :=
  ∑ e ∈ Finset.range D, gammaValuationSchurPacketResultant p c (e + 1) ^ 2

/-- Completed Hardy vector of one corrected Gamma–valuation prime source. -/
def gammaValuationSchurPrimeHardyVector (p : Nat.Primes) : PrimeHardy :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let hq : |q| < 1 := (abs_of_pos (xiTransversePrimeApertureDiskNode_pos 1 p)).symm ▸
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  arithmeticPrimeSchurBoundaryAmplitude p • hardyKernel q hq

@[simp] theorem gammaValuationSchurPrimeHardyVector_apply
    (p : Nat.Primes) (e : ℕ) :
    gammaValuationSchurPrimeHardyVector p e =
      xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  rw [← arithmeticSchurValuationCoordinate_prime_eq]
  simp [gammaValuationSchurPrimeHardyVector,
    arithmeticSchurValuationCoordinate]

/-- Finite coefficient synthesis inside intrinsic completed source Hardy space. -/
def gammaValuationSchurPacketHardyVector
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) : PrimeHardy :=
  ∑ i, c i • gammaValuationSchurPrimeHardyVector (p i)

@[simp] theorem gammaValuationSchurPacketHardyVector_apply
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (e : ℕ) :
    gammaValuationSchurPacketHardyVector p c e =
      gammaValuationSchurPacketResultant p c e := by
  classical
  unfold gammaValuationSchurPacketHardyVector
  let ev : PrimeHardy →+ ℝ :=
    { toFun := fun x => (x : ℕ → ℝ) e
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i, c i • gammaValuationSchurPrimeHardyVector (p i)) = _
  rw [map_sum]
  change (∑ i, c i * gammaValuationSchurPrimeHardyVector (p i) e) = _
  simp [gammaValuationSchurPacketResultant]

/-- Total energy of any vector in intrinsic infinite-dimensional source completion. -/
def gammaValuationSchurHardyEnergy (x : PrimeHardy) : ℝ :=
  ∑' e : ℕ, x e ^ 2

/-- Rank-one Gamma subtraction on entire source completion. -/
def gammaValuationSchurHardyResidual (x : PrimeHardy) : ℝ :=
  gammaValuationSchurHardyEnergy x - x 0 ^ 2

theorem summable_gammaValuationSchurHardy_sq (x : PrimeHardy) :
    Summable (fun e : ℕ => x e ^ 2) := by
  have h := (lp.memℓp x).summable (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- Global completion law: Gamma removes exactly vacuum line, leaving positive-depth energy. -/
theorem gammaValuationSchurHardyResidual_eq_tsum_tail (x : PrimeHardy) :
    gammaValuationSchurHardyResidual x = ∑' e : ℕ, x (e + 1) ^ 2 := by
  have hsplit := (summable_gammaValuationSchurHardy_sq x).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  unfold gammaValuationSchurHardyResidual gammaValuationSchurHardyEnergy
  rw [← hsplit]
  ring

theorem gammaValuationSchurHardyResidual_nonneg (x : PrimeHardy) :
    0 ≤ gammaValuationSchurHardyResidual x := by
  rw [gammaValuationSchurHardyResidual_eq_tsum_tail]
  exact tsum_nonneg fun e => sq_nonneg _

theorem hasSum_xiTransversePrimeHalfShiftedValuationCoordinate_mul
    (p q : Nat.Primes) :
    HasSum
      (fun e => xiTransversePrimeHalfShiftedValuationCoordinate p e *
        xiTransversePrimeHalfShiftedValuationCoordinate q e)
      (xiTransverseGammaValuationSzegoKernel p q) := by
  let x := xiTransversePrimeApertureDiskNode 1 p
  let y := xiTransversePrimeApertureDiskNode 1 q
  have hx0 : 0 < x := xiTransversePrimeApertureDiskNode_pos 1 p
  have hy0 : 0 < y := xiTransversePrimeApertureDiskNode_pos 1 q
  have hx1 : x < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hy1 : y < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) q
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0.le hy0.le
  have hxy1 : x * y < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hx0.le hx1 hy1.le
  have hgeom : HasSum (fun e : ℕ => (x * y) ^ e) (1 - x * y)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_pos hx0, abs_of_pos hy0] using hxy1)
  have hscaled := hgeom.mul_left
    (Real.sqrt x * Real.sqrt y * (1 - x) * (1 - y))
  change HasSum
    (fun e => (Real.sqrt x * ((1 - x) * x ^ e)) *
      (Real.sqrt y * ((1 - y) * y ^ e)))
    (Real.sqrt x * Real.sqrt y * (1 - x) * (1 - y) / (1 - x * y))
  rw [div_eq_mul_inv]
  apply hscaled.congr_fun
  intro e
  rw [mul_pow]
  ring

theorem hasSum_gammaValuationSchurPacketResultant_sq
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    HasSum (fun e => gammaValuationSchurPacketResultant p c e ^ 2)
      (gammaValuationSchurPacketPrimeEnergy p c) := by
  classical
  have hpairs : ∀ i : Fin N, HasSum
      (fun e => ∑ j, c i * c j *
        (xiTransversePrimeHalfShiftedValuationCoordinate (p i) e *
          xiTransversePrimeHalfShiftedValuationCoordinate (p j) e))
      (∑ j, c i * c j *
        xiTransverseGammaValuationSzegoKernel (p i) (p j)) := by
    intro i
    apply hasSum_finset_sum_real_schur Finset.univ
    intro j _
    simpa only using
      (hasSum_xiTransversePrimeHalfShiftedValuationCoordinate_mul (p i) (p j)).mul_left
        (c i * c j)
  have hall : HasSum
      (fun e => ∑ i, ∑ j, c i * c j *
        (xiTransversePrimeHalfShiftedValuationCoordinate (p i) e *
          xiTransversePrimeHalfShiftedValuationCoordinate (p j) e))
      (gammaValuationSchurPacketPrimeEnergy p c) := by
    unfold gammaValuationSchurPacketPrimeEnergy
    apply hasSum_finset_sum_real_schur Finset.univ
    intro i _
    exact hpairs i
  apply hall.congr_fun
  intro e
  unfold gammaValuationSchurPacketResultant
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gammaValuationSchurPacketGammaCharge_eq_resultant_zero
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    gammaValuationSchurPacketGammaCharge p c =
      -(3 * Real.sqrt 2 / 4) * gammaValuationSchurPacketResultant p c 0 := by
  classical
  unfold gammaValuationSchurPacketGammaCharge
    gammaValuationSchurPacketResultant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [gammaValuationHardyCorrectedCross_eq]
  change c i * (-(3 * Real.sqrt 2 / 4) *
      xiTransversePrimeHalfShiftedValuationCoordinate (p i) 0) = _
  ring

theorem gammaValuationSchurPacketSignedResidual_eq_tsum_tail
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    gammaValuationSchurPacketSignedResidual p c =
      ∑' e : ℕ, gammaValuationSchurPacketResultant p c (e + 1) ^ 2 := by
  have hs := hasSum_gammaValuationSchurPacketResultant_sq p c
  have hsplit := hs.summable.sum_add_tsum_nat_add 1
  have hconst : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold gammaValuationSchurPacketSignedResidual
  rw [gammaValuationSchurPacketGammaCharge_eq_resultant_zero,
    ← hs.tsum_eq]
  simp only [Finset.sum_range_one] at hsplit
  rw [← hsplit]
  have hcharge :
      (-(3 * Real.sqrt 2 / 4) * gammaValuationSchurPacketResultant p c 0) ^ 2 /
          (9 / 8 : ℝ) = gammaValuationSchurPacketResultant p c 0 ^ 2 := by
    rw [mul_pow, neg_sq, hconst]
    norm_num
  rw [hcharge]
  ring

/-- Finite prime quadratic form is exactly total energy of its vector in source completion. -/
theorem gammaValuationSchurPacketPrimeEnergy_eq_hardyEnergy
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    gammaValuationSchurPacketPrimeEnergy p c =
      gammaValuationSchurHardyEnergy (gammaValuationSchurPacketHardyVector p c) := by
  unfold gammaValuationSchurHardyEnergy
  rw [← (hasSum_gammaValuationSchurPacketResultant_sq p c).tsum_eq]
  apply tsum_congr
  intro e
  rw [gammaValuationSchurPacketHardyVector_apply]

/-- Gamma charge reads precisely vacuum coordinate of same completed source vector. -/
theorem gammaValuationSchurPacketGammaCharge_eq_hardyVacuum
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    gammaValuationSchurPacketGammaCharge p c =
      -(3 * Real.sqrt 2 / 4) * gammaValuationSchurPacketHardyVector p c 0 := by
  rw [gammaValuationSchurPacketGammaCharge_eq_resultant_zero,
    gammaValuationSchurPacketHardyVector_apply]

/-- Packet law is restriction of one rank-one subtraction on entire intrinsic completion. -/
theorem gammaValuationSchurPacketSignedResidual_eq_hardyResidual
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    gammaValuationSchurPacketSignedResidual p c =
      gammaValuationSchurHardyResidual (gammaValuationSchurPacketHardyVector p c) := by
  have hconst : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold gammaValuationSchurPacketSignedResidual
    gammaValuationSchurHardyResidual
  rw [gammaValuationSchurPacketPrimeEnergy_eq_hardyEnergy,
    gammaValuationSchurPacketGammaCharge_eq_hardyVacuum]
  have hcharge :
      (-(3 * Real.sqrt 2 / 4) * gammaValuationSchurPacketHardyVector p c 0) ^ 2 /
          (9 / 8 : ℝ) = gammaValuationSchurPacketHardyVector p c 0 ^ 2 := by
    rw [mul_pow, neg_sq, hconst]
    norm_num
  rw [hcharge]

theorem gammaValuationSchurPacketSignedResidual_nonneg
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    0 ≤ gammaValuationSchurPacketSignedResidual p c := by
  rw [gammaValuationSchurPacketSignedResidual_eq_tsum_tail]
  exact tsum_nonneg fun e => sq_nonneg _

/-- Distinct prime labels make the completed Schur residual faithful: its only null packet is the
zero coefficient packet. -/
theorem gammaValuationSchurPacketSignedResidual_eq_zero_iff
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p)
    (c : Fin N → ℝ) :
    gammaValuationSchurPacketSignedResidual p c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro hzero
    have hs := (hasSum_gammaValuationSchurPacketResultant_sq p c).summable
    have hinj : Function.Injective (fun e : ℕ => e + 1) := by
      intro e f h
      exact Nat.add_right_cancel h
    have htail : Summable
        (fun e : ℕ => gammaValuationSchurPacketResultant p c (e + 1) ^ 2) := by
      simpa [Function.comp_def] using hs.comp_injective hinj
    have hresultant : ∀ e : ℕ,
        gammaValuationSchurPacketResultant p c (e + 1) = 0 := by
      intro e
      have hle := htail.le_tsum e (fun j _ => sq_nonneg
        (gammaValuationSchurPacketResultant p c (j + 1)))
      rw [← gammaValuationSchurPacketSignedResidual_eq_tsum_tail p c, hzero] at hle
      have hsquare : gammaValuationSchurPacketResultant p c (e + 1) ^ 2 = 0 :=
        le_antisymm hle (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsquare
    let A := xiTransversePrimeHalfShiftedValuationSamplingMatrix p
    let d : Fin N → ℝ := fun i =>
      xiTransversePrimeApertureDiskNode 1 (p i) * c i
    have hAd : A.mulVec d = 0 := by
      funext e
      change ∑ i,
        xiTransversePrimeHalfShiftedValuationCoordinate (p i) e *
          (xiTransversePrimeApertureDiskNode 1 (p i) * c i) = 0
      rw [← hresultant e]
      unfold gammaValuationSchurPacketResultant
      apply Finset.sum_congr rfl
      intro i _
      rw [xiTransversePrimeHalfShiftedValuationCoordinate_succ]
      ring
    have hdet : A.det ≠ 0 := by
      exact xiTransversePrimeHalfShiftedValuationSamplingMatrix_det_ne_zero hp
    have hAinj : Function.Injective A.mulVec :=
      Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
    have hd : d = 0 := by
      apply hAinj
      simpa using hAd
    funext i
    have hdi := congrFun hd i
    change xiTransversePrimeApertureDiskNode 1 (p i) * c i = 0 at hdi
    exact (mul_eq_zero.mp hdi).resolve_left
      (xiTransversePrimeApertureDiskNode_pos 1 (p i)).ne'
  · rintro rfl
    simp [gammaValuationSchurPacketSignedResidual,
      gammaValuationSchurPacketPrimeEnergy,
      gammaValuationSchurPacketGammaCharge]

/-- Exact signed distinction on every nonzero finite injective prime packet. -/
theorem gammaValuationSchurPacketSignedResidual_pos
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p)
    {c : Fin N → ℝ} (hc : c ≠ 0) :
    0 < gammaValuationSchurPacketSignedResidual p c := by
  exact lt_of_le_of_ne
    (gammaValuationSchurPacketSignedResidual_nonneg p c)
    (fun h => hc ((gammaValuationSchurPacketSignedResidual_eq_zero_iff hp c).mp h.symm))

theorem gammaValuationSchurPacketTailPrefix_nonneg
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (D : ℕ) :
    0 ≤ gammaValuationSchurPacketTailPrefix p c D := by
  unfold gammaValuationSchurPacketTailPrefix
  exact Finset.sum_nonneg fun e _ => sq_nonneg _

theorem tendsto_gammaValuationSchurPacketTailPrefix
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    Tendsto (gammaValuationSchurPacketTailPrefix p c) atTop
      (nhds (gammaValuationSchurPacketSignedResidual p c)) := by
  have hinj : Function.Injective (fun e : ℕ => e + 1) := by
    intro e f h
    exact Nat.add_right_cancel h
  have htail : Summable
      (fun e : ℕ => gammaValuationSchurPacketResultant p c (e + 1) ^ 2) := by
    simpa [Function.comp_def] using
      (hasSum_gammaValuationSchurPacketResultant_sq p c).summable.comp_injective hinj
  have h := htail.hasSum.tendsto_sum_nat
  rw [gammaValuationSchurPacketSignedResidual_eq_tsum_tail]
  change Tendsto
    (fun D => ∑ e ∈ Finset.range D,
      gammaValuationSchurPacketResultant p c (e + 1) ^ 2)
    atTop
    (nhds (∑' e : ℕ, gammaValuationSchurPacketResultant p c (e + 1) ^ 2))
  exact h

end

end RHTower
