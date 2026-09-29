import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalPhysicalPluckerChiralityGain
import GaloisForLFunctions.RHTower.ThetaMellinSixIntegralNuclearFormation
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# The theta–Plücker formation-order index

Fix primes `p < q`, put `L = log p`, `M = log q`, `B_r = log r/(r+1)`, and let `a` be the critical
harmonic aperture.  The physical four-cell Plücker packet `(p,e),(p,e+1),(q,e),(q,e+1)` has rates
`(e+1/2)L, (e+3/2)L, (e+1/2)M, (e+3/2)M`, mass
`P_e = ∑_{i<j} [2a(λ_i-λ_j)/((λ_i²-a²)(λ_j²-a²))]² (B_i B_j)²`, total Fisher clock
`F = (4/3)(L² + M²)`, and depth weight `D_e = F P_e`.  The law `π_e = D_e/∑ D` is the conditional
depth law of the physical Plücker block weight on the edge `(p,q)`, and `w_e` is the theta
Mellin-six first-exit law `630/((2e+3)(2e+5)(2e+7)(2e+9))`.

* `e⁶ P_e → K = 16 a² (M-L)² B_p² B_q²/(L⁴M⁴) > 0`: both same-prime minors are `o(e⁻⁶)` and the
  four cross-prime minors share one limit.
* `e⁶ π_e → C = F K/∑ D > 0` and `e⁴ w_e → 315/8`.
* The unique positive half-density `s_e = √(w_e/π_e)` with `s_e² π_e = w_e` satisfies
  `s_e/e → √((315/8)/C) > 0`.
* `diag(s)` and `N+1` have the same maximal domain in `ℓ²` with equivalent graph norms, and
  `diag(s)` is unbounded.
* Every complex diagonal congruence `|g_e|² π_e = w_e` has `|g_e| = s_e`, so no bounded diagonal
  operator `G` satisfies `G diag(π) G* = diag(w)`.
-/

open Filter Topology Set Asymptotics
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## Asymptotics of one Cauchy–Plücker minor -/

/-- `e⁶ R = (2a (x-y)/e)² / ((x²-a²)/e² · (y²-a²)/e²)²` for the squared Cauchy–Plücker minor. -/
theorem pow_six_mul_twoBoundaryCauchyPairPluckerSq {a x y e : ℝ} (he : e ≠ 0) :
    e ^ 6 * twoBoundaryCauchyPairPluckerSq a x y =
      (2 * a * ((x - y) / e)) ^ 2 /
        (((x ^ 2 - a ^ 2) / e ^ 2) * ((y ^ 2 - a ^ 2) / e ^ 2)) ^ 2 := by
  unfold twoBoundaryCauchyPairPluckerSq twoBoundaryCauchyPairPlucker
  by_cases hx : x ^ 2 - a ^ 2 = 0
  · simp [hx]
  by_cases hy : y ^ 2 - a ^ 2 = 0
  · simp [hy]
  field_simp

/-- For the minor of the rates `(e+α)A` and `(e+β)B`,
`e⁶ R(e) → 4 a² (A-B)²/(A⁴B⁴)`. -/
theorem tendsto_pow_six_mul_twoBoundaryCauchyPairPluckerSq (a α β : ℝ) {A B : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 *
        twoBoundaryCauchyPairPluckerSq a ((e + α) * A) ((e + β) * B))
      atTop (𝓝 (4 * a ^ 2 * (A - B) ^ 2 / (A ^ 4 * B ^ 4))) := by
  have ht := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : Tendsto (fun e : ℕ => (A - B) + (α * A - β * B) * ((e : ℝ))⁻¹) atTop
      (𝓝 (A - B)) := by
    simpa using (tendsto_const_nhds (x := A - B)).add (ht.const_mul (α * A - β * B))
  have h2 : ∀ γ C : ℝ, Tendsto (fun e : ℕ =>
      (C + γ * C * ((e : ℝ))⁻¹) ^ 2 - a ^ 2 * ((e : ℝ))⁻¹ ^ 2) atTop (𝓝 (C ^ 2)) := by
    intro γ C
    simpa using (((tendsto_const_nhds (x := C)).add (ht.const_mul (γ * C))).pow 2).sub
      ((ht.pow 2).const_mul (a ^ 2))
  have hden : (A ^ 2 * B ^ 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB))
  have hlim := ((h1.const_mul (2 * a)).pow 2).div (((h2 α A).mul (h2 β B)).pow 2) hden
  have hval : (2 * a * (A - B)) ^ 2 / (A ^ 2 * B ^ 2) ^ 2 =
      4 * a ^ 2 * (A - B) ^ 2 / (A ^ 4 * B ^ 4) := by ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  have e1 : (A - B) + (α * A - β * B) * (e : ℝ)⁻¹ = ((e + α) * A - (e + β) * B) / e := by
    field_simp
    ring
  have e2 : ∀ γ C : ℝ, (C + γ * C * (e : ℝ)⁻¹) ^ 2 - a ^ 2 * (e : ℝ)⁻¹ ^ 2 =
      (((e + γ) * C) ^ 2 - a ^ 2) / (e : ℝ) ^ 2 := by
    intro γ C
    field_simp
  rw [Pi.div_apply, e1, e2 α A, e2 β B]
  exact (pow_six_mul_twoBoundaryCauchyPairPluckerSq he').symm

/-! ## The physical Plücker packet on a fixed prime edge -/

section Packet

variable (p q : Nat.Primes)

/-- The four-cell packet mass `P_e` written out over its six Plücker minors. -/
theorem gammaSewnCriticalPrimeDepthPacket_Partition_eq (e : ℕ) :
    gammaSewnCriticalPrimeDepthPacket_Partition e p q =
      twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 1 / 2) * Real.log p) ((e + 3 / 2) * Real.log p) *
          (gammaSewnMobiusApertureBoundaryAmplitude p *
            gammaSewnMobiusApertureBoundaryAmplitude p) ^ 2 +
        twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 1 / 2) * Real.log p) ((e + 1 / 2) * Real.log q) *
          (gammaSewnMobiusApertureBoundaryAmplitude p *
            gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
        twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 1 / 2) * Real.log p) ((e + 3 / 2) * Real.log q) *
          (gammaSewnMobiusApertureBoundaryAmplitude p *
            gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
        twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 3 / 2) * Real.log p) ((e + 1 / 2) * Real.log q) *
          (gammaSewnMobiusApertureBoundaryAmplitude p *
            gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
        twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 3 / 2) * Real.log p) ((e + 3 / 2) * Real.log q) *
          (gammaSewnMobiusApertureBoundaryAmplitude p *
            gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 +
        twoBoundaryCauchyPairPluckerSq gammaSewnCriticalFinitePacket_aperture
          ((e + 1 / 2) * Real.log q) ((e + 3 / 2) * Real.log q) *
          (gammaSewnMobiusApertureBoundaryAmplitude q *
            gammaSewnMobiusApertureBoundaryAmplitude q) ^ 2 := by
  have h32 : ((e + 1 : ℕ) : ℝ) + 1 / 2 = (e : ℝ) + 3 / 2 := by push_cast; ring
  simp only [gammaSewnCriticalPrimeDepthPacket_Partition, Fin.sum_univ_six,
    gammaSewnFourRateBoundaryPairRawWeight, fourRatePairLeft, fourRatePairRight,
    gammaSewnOrderedPrimeDepthPlucker_rate, gammaSewnOrderedPrimeDepthPlucker_cell,
    gammaSewnMobiusApertureCellMidHeight, Matrix.cons_val, h32]

/-- The total Fisher clock `F_{pq} = (4/3)(L² + M²)` of the packet. -/
def pluckerFisherClock : ℝ := 4 / 3 * (Real.log p ^ 2 + Real.log q ^ 2)

/-- Each prime occurs twice in the packet with boundary clock `(2/3)(log r)²`. -/
theorem gammaSewnCriticalPrimeDepthPacket_Total_eq (e : ℕ) :
    gammaSewnCriticalPrimeDepthPacket_Total e p q = pluckerFisherClock p q := by
  simp only [gammaSewnCriticalPrimeDepthPacket_Total, gammaSewnFourRateTotalFisher,
    fourRateTotalSum, gammaSewnOrderedPrimeDepthPlucker_cell, Matrix.cons_val,
    gammaSewnMobiusApertureBoundaryFisherClock, pluckerFisherClock]
  ring

theorem log_natPrimes_pos (r : Nat.Primes) : 0 < Real.log r :=
  Real.log_pos (by exact_mod_cast r.2.one_lt)

theorem pluckerFisherClock_pos : 0 < pluckerFisherClock p q := by
  have := log_natPrimes_pos p
  unfold pluckerFisherClock
  positivity

/-- The packet order constant `K_{pq} = 16 a² (M-L)² B_p² B_q²/(L⁴M⁴)`. -/
def pluckerOrderConstant : ℝ :=
  16 * gammaSewnCriticalFinitePacket_aperture ^ 2 * (Real.log q - Real.log p) ^ 2 *
    gammaSewnMobiusApertureBoundaryAmplitude p ^ 2 *
      gammaSewnMobiusApertureBoundaryAmplitude q ^ 2 / (Real.log p ^ 4 * Real.log q ^ 4)

theorem pluckerOrderConstant_pos {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    0 < pluckerOrderConstant p q := by
  have hL := log_natPrimes_pos p
  have hM := log_natPrimes_pos q
  have hLM : Real.log p < Real.log q :=
    Real.log_lt_log (by exact_mod_cast p.2.pos) (by exact_mod_cast hpq)
  have ha := gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
  have hBp : 0 < gammaSewnMobiusApertureBoundaryAmplitude p := by
    rw [gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
    positivity
  have hBq : 0 < gammaSewnMobiusApertureBoundaryAmplitude q := by
    rw [gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
    positivity
  have hsub : 0 < Real.log q - Real.log p := sub_pos.mpr hLM
  unfold pluckerOrderConstant gammaSewnCriticalFinitePacket_aperture
  positivity

/-- **(TPFOI, packet order).**  `e⁶ P_e → K_{pq}`: the same-prime minors vanish at order six and
the four cross-prime minors each contribute `4 a² (M-L)² B_p² B_q²/(L⁴M⁴)`. -/
theorem tendsto_pow_six_mul_gammaSewnCriticalPrimeDepthPacket_Partition :
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * gammaSewnCriticalPrimeDepthPacket_Partition e p q)
      atTop (𝓝 (pluckerOrderConstant p q)) := by
  have hL := (log_natPrimes_pos p).ne'
  have hM := (log_natPrimes_pos q).ne'
  set a := gammaSewnCriticalFinitePacket_aperture
  set Bp := gammaSewnMobiusApertureBoundaryAmplitude p
  set Bq := gammaSewnMobiusApertureBoundaryAmplitude q
  have t := fun (α β A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) =>
    tendsto_pow_six_mul_twoBoundaryCauchyPairPluckerSq a α β hA hB
  have h := (((((t (1 / 2) (3 / 2) _ _ hL hL).mul_const ((Bp * Bp) ^ 2)).add
    ((t (1 / 2) (1 / 2) _ _ hL hM).mul_const ((Bp * Bq) ^ 2))).add
    ((t (1 / 2) (3 / 2) _ _ hL hM).mul_const ((Bp * Bq) ^ 2))).add
    ((t (3 / 2) (1 / 2) _ _ hL hM).mul_const ((Bp * Bq) ^ 2))).add
    ((t (3 / 2) (3 / 2) _ _ hL hM).mul_const ((Bp * Bq) ^ 2)) |>.add
    ((t (1 / 2) (3 / 2) _ _ hM hM).mul_const ((Bq * Bq) ^ 2))
  have hK : pluckerOrderConstant p q =
      4 * a ^ 2 * (Real.log p - Real.log p) ^ 2 / (Real.log p ^ 4 * Real.log p ^ 4) *
          (Bp * Bp) ^ 2 +
        4 * a ^ 2 * (Real.log p - Real.log q) ^ 2 / (Real.log p ^ 4 * Real.log q ^ 4) *
          (Bp * Bq) ^ 2 +
        4 * a ^ 2 * (Real.log p - Real.log q) ^ 2 / (Real.log p ^ 4 * Real.log q ^ 4) *
          (Bp * Bq) ^ 2 +
        4 * a ^ 2 * (Real.log p - Real.log q) ^ 2 / (Real.log p ^ 4 * Real.log q ^ 4) *
          (Bp * Bq) ^ 2 +
        4 * a ^ 2 * (Real.log p - Real.log q) ^ 2 / (Real.log p ^ 4 * Real.log q ^ 4) *
          (Bp * Bq) ^ 2 +
        4 * a ^ 2 * (Real.log q - Real.log q) ^ 2 / (Real.log q ^ 4 * Real.log q ^ 4) *
          (Bq * Bq) ^ 2 := by
    unfold pluckerOrderConstant
    ring
  rw [hK]
  refine h.congr fun e => ?_
  rw [gammaSewnCriticalPrimeDepthPacket_Partition_eq]
  ring

/-! ## Depth weights and the conditional depth law -/

/-- The global Plücker block weight numerator `D_e = P_e F_{pq}` on the edge `(p,q)`. -/
def pluckerDepthWeight (e : ℕ) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_Partition e p q * gammaSewnCriticalPrimeDepthPacket_Total e p q

theorem pluckerDepthWeight_eq (e : ℕ) :
    pluckerDepthWeight p q e =
      pluckerFisherClock p q * gammaSewnCriticalPrimeDepthPacket_Partition e p q := by
  rw [pluckerDepthWeight, gammaSewnCriticalPrimeDepthPacket_Total_eq, mul_comm]

theorem pluckerDepthWeight_pos {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) (e : ℕ) :
    0 < pluckerDepthWeight p q e :=
  mul_pos (gammaSewnCriticalPrimeDepthPacket_Partition_pos hpq)
    (gammaSewnCriticalPrimeDepthPacket_Total_pos e p q)

/-- On adjacent primes the depth weight is the global adjacent-prime denominator term. -/
theorem pluckerDepthWeight_adjacentPrime (e n : ℕ) :
    pluckerDepthWeight (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) e =
      gammaSewnCriticalAdjacentPrime_DenominatorTerm (e, n) := rfl

/-- `e⁶ D_e → F_{pq} K_{pq}`. -/
theorem tendsto_pow_six_mul_pluckerDepthWeight :
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * pluckerDepthWeight p q e) atTop
      (𝓝 (pluckerFisherClock p q * pluckerOrderConstant p q)) := by
  refine ((tendsto_pow_six_mul_gammaSewnCriticalPrimeDepthPacket_Partition p q).const_mul
    (pluckerFisherClock p q)).congr fun e => ?_
  rw [pluckerDepthWeight_eq]
  ring

/-- The depth weights are summable: `D_e = O(e⁻⁶)`. -/
theorem summable_pluckerDepthWeight : Summable (pluckerDepthWeight p q) := by
  have hO : (fun e : ℕ => pluckerDepthWeight p q e) =O[atTop]
      (fun e : ℕ => (((e : ℝ)) ^ 6)⁻¹) := by
    have h := ((tendsto_pow_six_mul_pluckerDepthWeight p q).isBigO_one ℝ).mul
      (isBigO_refl (fun e : ℕ => (((e : ℝ)) ^ 6)⁻¹) atTop)
    refine h.congr' ?_ (Eventually.of_forall fun e => one_mul _)
    filter_upwards [eventually_ne_atTop 0] with e he
    have he' : ((e : ℝ)) ^ 6 ≠ 0 := pow_ne_zero 6 (Nat.cast_ne_zero.mpr he)
    field_simp
  exact summable_of_isBigO_nat (Real.summable_nat_pow_inv.mpr (by norm_num)) hO

/-- The total depth mass `Z_{pq} = ∑_e D_e`. -/
def pluckerDepthTotal : ℝ := ∑' e, pluckerDepthWeight p q e

theorem pluckerDepthTotal_pos {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    0 < pluckerDepthTotal p q :=
  (summable_pluckerDepthWeight p q).tsum_pos (fun e => (pluckerDepthWeight_pos hpq e).le) 0
    (pluckerDepthWeight_pos hpq 0)

/-- The conditional valuation-depth law `π_e = D_e/Z_{pq}`. -/
def pluckerDepthLaw (e : ℕ) : ℝ := pluckerDepthWeight p q e / pluckerDepthTotal p q

theorem pluckerDepthLaw_pos {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) (e : ℕ) :
    0 < pluckerDepthLaw p q e :=
  div_pos (pluckerDepthWeight_pos hpq e) (pluckerDepthTotal_pos hpq)

theorem hasSum_pluckerDepthLaw {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    HasSum (pluckerDepthLaw p q) 1 := by
  have h := (summable_pluckerDepthWeight p q).hasSum.div_const (pluckerDepthTotal p q)
  rwa [← pluckerDepthTotal, div_self (pluckerDepthTotal_pos hpq).ne'] at h

theorem pluckerDepthLaw_le_one {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) (e : ℕ) :
    pluckerDepthLaw p q e ≤ 1 := by
  rw [pluckerDepthLaw, div_le_one (pluckerDepthTotal_pos hpq)]
  exact (summable_pluckerDepthWeight p q).le_tsum e
    fun j _ => (pluckerDepthWeight_pos hpq j).le

/-- On adjacent primes `π` is the physical Plücker block weight conditioned on the prime edge. -/
theorem pluckerDepthLaw_adjacentPrime (e n : ℕ) :
    pluckerDepthLaw (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) e =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight (e, n) /
        ∑' k, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight (k, n) := by
  simp only [gammaSewnCriticalAdjacentPrime_PluckerBlockWeight, tsum_div_const]
  rw [div_div_div_cancel_right₀ gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos.ne']
  rfl

/-- The law constant `C_{pq} = F_{pq} K_{pq}/Z_{pq}`. -/
def pluckerDepthLawConstant : ℝ :=
  pluckerFisherClock p q * pluckerOrderConstant p q / pluckerDepthTotal p q

theorem pluckerDepthLawConstant_pos {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    0 < pluckerDepthLawConstant p q :=
  div_pos (mul_pos (pluckerFisherClock_pos p q) (pluckerOrderConstant_pos hpq))
    (pluckerDepthTotal_pos hpq)

/-- **(TPFOI, law order).**  `e⁶ π_e → C_{pq}`. -/
theorem tendsto_pow_six_mul_pluckerDepthLaw :
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * pluckerDepthLaw p q e) atTop
      (𝓝 (pluckerDepthLawConstant p q)) := by
  refine ((tendsto_pow_six_mul_pluckerDepthWeight p q).div_const
    (pluckerDepthTotal p q)).congr fun e => ?_
  rw [pluckerDepthLaw, mul_div_assoc]

end Packet

/-! ## The theta first-exit law -/

theorem thetaCuspMellinSixFlux_eq (e : ℕ) :
    thetaCuspMellinSixFlux e =
      630 / (((2 * e + 3 : ℕ) : ℝ) * ((2 * e + 5 : ℕ) : ℝ) * ((2 * e + 7 : ℕ) : ℝ) *
        ((2 * e + 9 : ℕ) : ℝ)) := by
  rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w, PrimeHodgeHistory.w_formula]

theorem thetaCuspMellinSixFlux_pos (e : ℕ) : 0 < thetaCuspMellinSixFlux e := by
  rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]
  exact PrimeHodgeHistory.w_pos e

theorem thetaCuspMellinSixFlux_le_one (e : ℕ) : thetaCuspMellinSixFlux e ≤ 1 := by
  rw [thetaCuspMellinSixFlux_eq, div_le_one (by positivity)]
  have h3 : (3 : ℝ) ≤ ((2 * e + 3 : ℕ) : ℝ) := by push_cast; linarith [e.cast_nonneg (α := ℝ)]
  have h5 : (5 : ℝ) ≤ ((2 * e + 5 : ℕ) : ℝ) := by push_cast; linarith [e.cast_nonneg (α := ℝ)]
  have h7 : (7 : ℝ) ≤ ((2 * e + 7 : ℕ) : ℝ) := by push_cast; linarith [e.cast_nonneg (α := ℝ)]
  have h9 : (9 : ℝ) ≤ ((2 * e + 9 : ℕ) : ℝ) := by push_cast; linarith [e.cast_nonneg (α := ℝ)]
  calc (630 : ℝ) ≤ 3 * 5 * 7 * 9 := by norm_num
    _ ≤ _ := by gcongr

/-- **(TPFOI.3).**  `e⁴ w_e → 630/2⁴ = 315/8`. -/
theorem tendsto_pow_four_mul_thetaCuspMellinSixFlux :
    Tendsto (fun e : ℕ => (e : ℝ) ^ 4 * thetaCuspMellinSixFlux e) atTop (𝓝 (315 / 8)) := by
  have ht := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlin : ∀ c : ℝ, Tendsto (fun e : ℕ => 2 + c * ((e : ℝ))⁻¹) atTop (𝓝 2) := fun c => by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (ht.const_mul c)
  have h := (tendsto_const_nhds (x := (630 : ℝ))).div
    ((((hlin 3).mul (hlin 5)).mul (hlin 7)).mul (hlin 9)) (by norm_num)
  have hval : (630 : ℝ) / (2 * 2 * 2 * 2) = 315 / 8 := by norm_num
  rw [← hval]
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  rw [Pi.div_apply, thetaCuspMellinSixFlux_eq]
  push_cast
  field_simp

/-! ## The formation half-density -/

section HalfDensity

variable (p q : Nat.Primes)

/-- The positive diagonal half-density `s_e = √(w_e/π_e)` taking `π` to `w`. -/
def formationHalfDensity (e : ℕ) : ℝ :=
  Real.sqrt (thetaCuspMellinSixFlux e / pluckerDepthLaw p q e)

variable {p q} (hpq : (p : ℕ) < (q : ℕ))
include hpq

theorem formationHalfDensity_pos (e : ℕ) : 0 < formationHalfDensity p q e :=
  Real.sqrt_pos.mpr (div_pos (thetaCuspMellinSixFlux_pos e) (pluckerDepthLaw_pos hpq e))

/-- `s_e² π_e = w_e`. -/
theorem formationHalfDensity_sq_mul (e : ℕ) :
    formationHalfDensity p q e ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e := by
  rw [formationHalfDensity, Real.sq_sqrt
    (div_pos (thetaCuspMellinSixFlux_pos e) (pluckerDepthLaw_pos hpq e)).le,
    div_mul_cancel₀ _ (pluckerDepthLaw_pos hpq e).ne']

/-- **Uniqueness.**  A nonnegative `x` satisfies `x² π_e = w_e` exactly when `x = s_e`. -/
theorem sq_mul_pluckerDepthLaw_eq_iff {x : ℝ} (hx : 0 ≤ x) (e : ℕ) :
    x ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e ↔ x = formationHalfDensity p q e := by
  constructor
  · intro h
    have hpi := (pluckerDepthLaw_pos hpq e).ne'
    rw [formationHalfDensity, ← h, mul_div_cancel_right₀ _ hpi, Real.sqrt_sq hx]
  · rintro rfl
    exact formationHalfDensity_sq_mul hpq e

omit hpq in
/-- The linear slope `√((315/8)/C_{pq})` of the half-density. -/
def formationOrderSlope (p q : Nat.Primes) : ℝ := Real.sqrt (315 / 8 / pluckerDepthLawConstant p q)

theorem formationOrderSlope_pos : 0 < formationOrderSlope p q :=
  Real.sqrt_pos.mpr (div_pos (by norm_num) (pluckerDepthLawConstant_pos hpq))

/-- **(TPFOI.1).**  `s_e/e → √((315/8)/C_{pq}) > 0`. -/
theorem tendsto_formationHalfDensity_div :
    Tendsto (fun e : ℕ => formationHalfDensity p q e / e) atTop
      (𝓝 (formationOrderSlope p q)) := by
  have h := ((tendsto_pow_four_mul_thetaCuspMellinSixFlux.div
    (tendsto_pow_six_mul_pluckerDepthLaw p q) (pluckerDepthLawConstant_pos hpq).ne').sqrt)
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hpi := (pluckerDepthLaw_pos hpq e).ne'
  rw [formationHalfDensity, ← Real.sqrt_sq he'.le, ← Real.sqrt_div' _ (sq_nonneg _),
    Pi.div_apply]
  congr 1
  field_simp

/-- `s_e/(e+1) → √((315/8)/C_{pq})`. -/
theorem tendsto_formationHalfDensity_div_succ :
    Tendsto (fun e : ℕ => formationHalfDensity p q e / ((e : ℝ) + 1)) atTop
      (𝓝 (formationOrderSlope p q)) := by
  have h := (tendsto_formationHalfDensity_div hpq).mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  field_simp

/-- **Two-sided linear bounds.**  There are `0 < c₁ ≤ c₂` with `c₁ (e+1) ≤ s_e ≤ c₂ (e+1)`. -/
theorem exists_formationHalfDensity_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ e : ℕ,
      c₁ * ((e : ℝ) + 1) ≤ formationHalfDensity p q e ∧
        formationHalfDensity p q e ≤ c₂ * ((e : ℝ) + 1) := by
  set r : ℕ → ℝ := fun e => formationHalfDensity p q e / ((e : ℝ) + 1)
  have hr : ∀ e, 0 < r e := fun e => div_pos (formationHalfDensity_pos hpq e) (by positivity)
  have hlim : Tendsto r atTop (𝓝 (formationOrderSlope p q)) :=
    tendsto_formationHalfDensity_div_succ hpq
  obtain ⟨c₂, hc₂⟩ := hlim.bddAbove_range
  obtain ⟨B, hB⟩ := (hlim.inv₀ (formationOrderSlope_pos hpq).ne').bddAbove_range
  have hru : ∀ e, r e ≤ c₂ := fun e => hc₂ ⟨e, rfl⟩
  have hrl : ∀ e, (r e)⁻¹ ≤ B := fun e => hB ⟨e, rfl⟩
  have hB0 : 0 < B := lt_of_lt_of_le (inv_pos.mpr (hr 0)) (hrl 0)
  refine ⟨B⁻¹, c₂, inv_pos.mpr hB0, lt_of_lt_of_le (hr 0) (hru 0), fun e => ⟨?_, ?_⟩⟩
  · have h1 := inv_le_of_inv_le₀ (hr e) (hrl e)
    have he : (0 : ℝ) < (e : ℝ) + 1 := by positivity
    calc B⁻¹ * ((e : ℝ) + 1) ≤ r e * ((e : ℝ) + 1) := by gcongr
      _ = formationHalfDensity p q e := div_mul_cancel₀ _ he.ne'
  · have he : (0 : ℝ) < (e : ℝ) + 1 := by positivity
    calc formationHalfDensity p q e = r e * ((e : ℝ) + 1) := (div_mul_cancel₀ _ he.ne').symm
      _ ≤ c₂ * ((e : ℝ) + 1) := by gcongr; exact hru e

/-- **Unboundedness.**  The half-density is not bounded. -/
theorem not_bddAbove_formationHalfDensity : ¬ BddAbove (range (formationHalfDensity p q)) := by
  rintro ⟨C, hC⟩
  obtain ⟨c₁, _, hc₁, _, hb⟩ := exists_formationHalfDensity_bounds hpq
  obtain ⟨e, he⟩ := exists_nat_gt (C / c₁)
  have h1 := (hb e).1
  have h2 : formationHalfDensity p q e ≤ C := hC ⟨e, rfl⟩
  have h3 : C < c₁ * ((e : ℝ) + 1) := by
    rw [div_lt_iff₀ hc₁] at he
    nlinarith
  linarith

end HalfDensity

/-! ## Domain and graph norm of `diag(s)` -/

section Domain

/-- Pointwise domination of coordinates gives domination of `ℓ²` norms. -/
theorem norm_le_of_forall_norm_apply_le {ι : Type*} {y z : lp (fun _ : ι => ℂ) 2} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ e, ‖y e‖ ≤ c * ‖z e‖) : ‖y‖ ≤ c * ‖z‖ := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (by positivity) ?_
  have hy := (lp.memℓp y).summable h2
  have hz := (lp.memℓp z).summable h2
  rw [Real.mul_rpow hc (norm_nonneg _), lp.norm_rpow_eq_tsum h2, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun e => ?_) hy (hz.mul_left _)
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h e) (by norm_num)

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
include hpq

/-- **Domain equality.**  `x ∈ Dom(diag s)` exactly when `x ∈ Dom(N+1)`. -/
theorem memℓp_formationHalfDensity_mul_iff (x : ℕ → ℂ) :
    Memℓp (fun e => (formationHalfDensity p q e : ℂ) * x e) 2 ↔
      Memℓp (fun e : ℕ => (((e : ℝ) + 1 : ℝ) : ℂ) * x e) 2 := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_formationHalfDensity_bounds hpq
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hs : ∀ e, ‖(formationHalfDensity p q e : ℂ) * x e‖ =
      formationHalfDensity p q e * ‖x e‖ := fun e => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (formationHalfDensity_pos hpq e).le]
  have hn : ∀ e : ℕ, ‖(((e : ℝ) + 1 : ℝ) : ℂ) * x e‖ = ((e : ℝ) + 1) * ‖x e‖ := fun e => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [memℓp_gen_iff h2, memℓp_gen_iff h2]
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) (h.mul_left (c₁⁻¹ ^ 2))
    rw [hs, hn, ENNReal.toReal_ofNat, Real.rpow_two, Real.rpow_two, ← mul_pow]
    have h1 : (e : ℝ) + 1 ≤ c₁⁻¹ * formationHalfDensity p q e := by
      rw [le_inv_mul_iff₀ hc₁]
      exact (hb e).1
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc ((e : ℝ) + 1) * ‖x e‖ ≤ c₁⁻¹ * formationHalfDensity p q e * ‖x e‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = c₁⁻¹ * (formationHalfDensity p q e * ‖x e‖) := by ring
  · intro h
    refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) (h.mul_left (c₂ ^ 2))
    rw [hs, hn, ENNReal.toReal_ofNat, Real.rpow_two, Real.rpow_two, ← mul_pow]
    refine pow_le_pow_left₀
      (mul_nonneg (formationHalfDensity_pos hpq e).le (norm_nonneg _)) ?_ 2
    calc formationHalfDensity p q e * ‖x e‖ ≤ c₂ * ((e : ℝ) + 1) * ‖x e‖ :=
          mul_le_mul_of_nonneg_right (hb e).2 (norm_nonneg _)
      _ = c₂ * (((e : ℝ) + 1) * ‖x e‖) := by ring

/-- **Graph-norm equivalence.**  For `x ∈ ℓ²` with `y = diag(s) x` and `z = (N+1) x` in `ℓ²`,
the graph norms `‖x‖ + ‖y‖` and `‖x‖ + ‖z‖` are uniformly equivalent. -/
theorem formationHalfDensity_graphNorm_equiv :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x y z : lp (fun _ : ℕ => ℂ) 2,
      (∀ e, y e = (formationHalfDensity p q e : ℂ) * x e) →
      (∀ e : ℕ, z e = (((e : ℝ) + 1 : ℝ) : ℂ) * x e) →
        c * (‖x‖ + ‖z‖) ≤ ‖x‖ + ‖y‖ ∧ ‖x‖ + ‖y‖ ≤ C * (‖x‖ + ‖z‖) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_formationHalfDensity_bounds hpq
  refine ⟨min 1 c₁, max 1 c₂, lt_min one_pos hc₁, lt_max_of_lt_left one_pos,
    fun x y z hy hz => ⟨?_, ?_⟩⟩
  · have hzy : ‖z‖ ≤ c₁⁻¹ * ‖y‖ := norm_le_of_forall_norm_apply_le (by positivity) fun e => by
      rw [hy, hz, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) + 1),
        Real.norm_of_nonneg (formationHalfDensity_pos hpq e).le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ((le_inv_mul_iff₀ hc₁).mpr (hb e).1) (norm_nonneg _)
    have hz' : c₁ * ‖z‖ ≤ ‖y‖ := by
      rw [le_inv_mul_iff₀ hc₁] at hzy
      exact hzy
    have hm1 : min 1 c₁ ≤ 1 := min_le_left _ _
    have hm2 : min 1 c₁ ≤ c₁ := min_le_right _ _
    have hx := norm_nonneg x
    have hzn := norm_nonneg z
    nlinarith
  · have hyz : ‖y‖ ≤ c₂ * ‖z‖ := norm_le_of_forall_norm_apply_le hc₂.le fun e => by
      rw [hy, hz, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) + 1),
        Real.norm_of_nonneg (formationHalfDensity_pos hpq e).le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hb e).2 (norm_nonneg _)
    have hm1 : 1 ≤ max 1 c₂ := le_max_left _ _
    have hm2 : c₂ ≤ max 1 c₂ := le_max_right _ _
    have hx := norm_nonneg x
    have hzn := norm_nonneg z
    nlinarith

end Domain

/-! ## No bounded diagonal congruence -/

section Congruence

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
include hpq

theorem norm_pluckerDepthLaw_le (e : ℕ) : ‖((pluckerDepthLaw p q e : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (pluckerDepthLaw_pos hpq e).le]
  exact pluckerDepthLaw_le_one hpq e

omit hpq in
theorem norm_thetaCuspMellinSixFlux_le (e : ℕ) : ‖((thetaCuspMellinSixFlux e : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (thetaCuspMellinSixFlux_pos e).le]
  exact thetaCuspMellinSixFlux_le_one e

/-- **Complex diagonal congruences.**  If `|g_e|² π_e = w_e` for all `e`, then `|g_e| = s_e`, and
`|g|` is unbounded. -/
theorem norm_eq_formationHalfDensity_of_congruence {g : ℕ → ℂ}
    (hg : ∀ e, ‖g e‖ ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e) (e : ℕ) :
    ‖g e‖ = formationHalfDensity p q e :=
  (sq_mul_pluckerDepthLaw_eq_iff hpq (norm_nonneg _) e).mp (hg e)

theorem not_bddAbove_norm_of_congruence {g : ℕ → ℂ}
    (hg : ∀ e, ‖g e‖ ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e) :
    ¬ BddAbove (range fun e => ‖g e‖) := by
  have : (fun e => ‖g e‖) = formationHalfDensity p q :=
    funext (norm_eq_formationHalfDensity_of_congruence hpq hg)
  rw [this]
  exact not_bddAbove_formationHalfDensity hpq

/-- **No bounded diagonal congruence.**  For every bounded diagonal operator `G = diag(g)` on
`ℓ²(ℕ)`, `G diag(π) G* ≠ diag(w)`. -/
theorem diagonal_congruence_ne (g : ℕ → ℂ) {C : ℝ} (hg : ∀ e, ‖g e‖ ≤ C) :
    _root_.HTGeometry.ellTwoDiagonal g hg ∘L
        _root_.HTGeometry.ellTwoDiagonal (fun e => ((pluckerDepthLaw p q e : ℝ) : ℂ))
          (norm_pluckerDepthLaw_le hpq) ∘L
        ContinuousLinearMap.adjoint (_root_.HTGeometry.ellTwoDiagonal g hg) ≠
      _root_.HTGeometry.ellTwoDiagonal (fun e => ((thetaCuspMellinSixFlux e : ℝ) : ℂ))
        norm_thetaCuspMellinSixFlux_le := by
  intro h
  have key : ∀ e, ‖g e‖ ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e := by
    intro e
    have he := congrArg (fun T => (T (lp.single 2 e (1 : ℂ)) : ℕ → ℂ) e) h
    simp only [ContinuousLinearMap.comp_apply, _root_.HTGeometry.adjoint_ellTwoDiagonal,
      _root_.HTGeometry.ellTwoDiagonal_apply, lp.single_apply_self, mul_one] at he
    have hc : (((‖g e‖ ^ 2 * pluckerDepthLaw p q e : ℝ)) : ℂ) =
        ((thetaCuspMellinSixFlux e : ℝ) : ℂ) := by
      rw [← he]
      push_cast
      rw [← Complex.mul_conj']
      ring
    exact_mod_cast hc
  exact not_bddAbove_norm_of_congruence hpq key ⟨C, by rintro _ ⟨e, rfl⟩; exact hg e⟩

end Congruence

/-! ## The formation-order index -/

/-- **Theorem TPFOI.**  For primes `p < q`: `K_{pq}, C_{pq} > 0`; `e⁶ P_e → K_{pq}`,
`e⁶ D_e → F_{pq} K_{pq}`, `e⁶ π_e → C_{pq}`, `e⁴ w_e → 315/8`; `π` is a probability law; `s_e` is
the unique nonnegative solution of `s² π_e = w_e` and `s_e/e → √((315/8)/C_{pq}) > 0`; `diag(s)`
and `N+1` have the same domain with equivalent graph norms; `s` is unbounded; and no bounded
diagonal `G` satisfies `G diag(π) G* = diag(w)`. -/
theorem theta_plucker_formation_order_index {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    0 < pluckerOrderConstant p q ∧ 0 < pluckerDepthLawConstant p q ∧
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * gammaSewnCriticalPrimeDepthPacket_Partition e p q)
      atTop (𝓝 (pluckerOrderConstant p q)) ∧
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * pluckerDepthWeight p q e) atTop
      (𝓝 (pluckerFisherClock p q * pluckerOrderConstant p q)) ∧
    Tendsto (fun e : ℕ => (e : ℝ) ^ 6 * pluckerDepthLaw p q e) atTop
      (𝓝 (pluckerDepthLawConstant p q)) ∧
    Tendsto (fun e : ℕ => (e : ℝ) ^ 4 * thetaCuspMellinSixFlux e) atTop (𝓝 (315 / 8)) ∧
    HasSum (pluckerDepthLaw p q) 1 ∧
    (∀ e (x : ℝ), 0 ≤ x →
      (x ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e ↔
        x = formationHalfDensity p q e)) ∧
    0 < formationOrderSlope p q ∧
    Tendsto (fun e : ℕ => formationHalfDensity p q e / e) atTop
      (𝓝 (formationOrderSlope p q)) ∧
    (∀ x : ℕ → ℂ, Memℓp (fun e => (formationHalfDensity p q e : ℂ) * x e) 2 ↔
      Memℓp (fun e : ℕ => (((e : ℝ) + 1 : ℝ) : ℂ) * x e) 2) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x y z : lp (fun _ : ℕ => ℂ) 2,
      (∀ e, y e = (formationHalfDensity p q e : ℂ) * x e) →
      (∀ e : ℕ, z e = (((e : ℝ) + 1 : ℝ) : ℂ) * x e) →
        c * (‖x‖ + ‖z‖) ≤ ‖x‖ + ‖y‖ ∧ ‖x‖ + ‖y‖ ≤ C * (‖x‖ + ‖z‖)) ∧
    ¬ BddAbove (range (formationHalfDensity p q)) ∧
    (∀ g : ℕ → ℂ, (∀ e, ‖g e‖ ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e) →
      ∀ e, ‖g e‖ = formationHalfDensity p q e) ∧
    ∀ (g : ℕ → ℂ) (C : ℝ) (hg : ∀ e, ‖g e‖ ≤ C),
      _root_.HTGeometry.ellTwoDiagonal g hg ∘L
          _root_.HTGeometry.ellTwoDiagonal (fun e => ((pluckerDepthLaw p q e : ℝ) : ℂ))
            (norm_pluckerDepthLaw_le hpq) ∘L
          ContinuousLinearMap.adjoint (_root_.HTGeometry.ellTwoDiagonal g hg) ≠
        _root_.HTGeometry.ellTwoDiagonal (fun e => ((thetaCuspMellinSixFlux e : ℝ) : ℂ))
          norm_thetaCuspMellinSixFlux_le :=
  ⟨pluckerOrderConstant_pos hpq, pluckerDepthLawConstant_pos hpq,
    tendsto_pow_six_mul_gammaSewnCriticalPrimeDepthPacket_Partition p q,
    tendsto_pow_six_mul_pluckerDepthWeight p q, tendsto_pow_six_mul_pluckerDepthLaw p q,
    tendsto_pow_four_mul_thetaCuspMellinSixFlux, hasSum_pluckerDepthLaw hpq,
    fun e _ hx => sq_mul_pluckerDepthLaw_eq_iff hpq hx e, formationOrderSlope_pos hpq,
    tendsto_formationHalfDensity_div hpq, memℓp_formationHalfDensity_mul_iff hpq,
    formationHalfDensity_graphNorm_equiv hpq, not_bddAbove_formationHalfDensity hpq,
    fun _ hg => norm_eq_formationHalfDensity_of_congruence hpq hg,
    fun g _ hg => diagonal_congruence_ne hpq g hg⟩

end GaloisForLFunctions.HTGeometry
