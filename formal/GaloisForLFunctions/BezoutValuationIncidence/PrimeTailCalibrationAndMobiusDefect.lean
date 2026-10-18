import GaloisForLFunctions.BezoutValuationIncidence.ChineseRemainderBezoutPeriodicityAndSawtoothDefect
import GaloisForLFunctions.BezoutValuationIncidence.FermiCellJumpReciprocityAndPronicTailBridge
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sharp prime-tail calibration and the literal Möbius defect

The prime band `N/2 < p ≤ N` has single-multiple Selberg coordinates and exact
successor eigenvalue `p`. Its actual divisor responses satisfy a sharp tradeoff
with the full pole-free successor energy. Explicit arithmetic weights attain
all supporting bounds.

For `N ≥ 2` and the literal Möbius coefficients, the combined signed LCM and
Bézout defect is exactly `M * sieveSuccessorReserve N moebiusReal - 1`
throughout `1 ≤ M ≤ N`.
At `M = N` it dominates the terminal-prime count minus one. The unconditional
prime-window theorem therefore excludes every eventual sublinear-power upper
bound for this unrenormalized defect. The scope includes the sieve horizon;
it does not exclude estimates retaining cancellation with the diagonal main
term. BVI cancellation and RH remain open.
-/


open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Primes whose next multiple lies beyond the sieve cutoff. -/
def sievePrimeTail (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun p => Nat.Prime p ∧ N < 2*p)

/-- Reciprocal-prime mass of the terminal sieve band. -/
def sievePrimeTailMass (N : ℕ) : ℝ :=
  ∑ p ∈ sievePrimeTail N, 1 / (p : ℝ)

/-- Actual divisor response observed on the terminal prime band. -/
def sievePrimeTailResponse (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ sievePrimeTail N, sieveSeq N c p ^ 2 / (p : ℝ)

/-- The part of the successor energy carried by terminal prime coordinates. -/
def sievePrimeTailReserve (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ sievePrimeTail N, c p ^ 2 / (p : ℝ)

/-- Pole-free diagonal energy; half the complete-period successor energy density. -/
def sieveSuccessorReserve (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c

private theorem primeTail_mem {N p : ℕ} (hp : p ∈ sievePrimeTail N) :
    2 ≤ p ∧ p ≤ N ∧ Nat.Prime p ∧ N < 2*p := by
  obtain ⟨hpI,hprime,hhalf⟩ := Finset.mem_filter.mp hp
  exact ⟨(Finset.mem_Icc.mp hpI).1,(Finset.mem_Icc.mp hpI).2,hprime,hhalf⟩

private theorem primeTail_subset (N : ℕ) : sievePrimeTail N ⊆ Finset.Icc 2 N :=
  Finset.filter_subset _ _

/-- A terminal prime has a single multiple in the coefficient support. -/
theorem selbergMultiplesCoord_primeTail {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (c : ℕ → ℝ) : selbergMultiplesCoord N c p = c p / (p : ℝ) := by
  obtain ⟨hp2,hpN,_,hhalf⟩ := primeTail_mem hp
  have hset : (Finset.Icc 1 N).filter (fun d => p ∣ d) = {p} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1,hdN⟩,hpd⟩
      obtain ⟨k,rfl⟩ := hpd
      have hpk : p*k < 2*p := lt_of_le_of_lt hdN hhalf
      have hk0 : k ≠ 0 := by rintro rfl; simp at hd1
      have hk1 : k = 1 := by nlinarith only [hpk,hp2,Nat.pos_of_ne_zero hk0]
      simp [hk1]
    · rintro rfl
      exact ⟨⟨by omega,hpN⟩,dvd_refl _⟩
  simp [selbergMultiplesCoord,hset]

/-- The literal prime response is the unit coefficient plus the prime coefficient. -/
theorem sieveSeq_prime_of_le {N p : ℕ} (hp : Nat.Prime p) (hpN : p ≤ N)
    (c : ℕ → ℝ) : sieveSeq N c p = c 1 + c p := by
  have hset : (Finset.Icc 1 N).filter (fun d => d ∣ p) = {1,p} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hd
      exact (Nat.dvd_prime hp).mp hd.2
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, (show 1 ≤ p from hp.pos).trans hpN⟩,one_dvd _⟩
      · exact ⟨⟨hp.pos,hpN⟩,dvd_refl _⟩
  simp [sieveSeq,hset,hp.ne_one.symm]

private theorem primeTail_diagonal_nonneg {e : ℕ} (he : 2 ≤ e) :
    0 ≤ (Nat.totient e : ℝ) - moebiusReal e := by
  have hphi : (1 : ℝ) ≤ Nat.totient e := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < e by omega))
  have hmu := moebiusReal_le_one e
  linarith only [hphi,hmu]

/-- Terminal prime observations give an unconditional lower bound for the full successor reserve. -/
theorem sievePrimeTailReserve_le_successorReserve {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℝ) : sievePrimeTailReserve N c ≤ sieveSuccessorReserve N c := by
  unfold sieveSuccessorReserve
  rw [selbergSubBezoutQuadraticForm_eq_Icc_two hN c]
  have hprime : (∑ p ∈ sievePrimeTail N,
      ((Nat.totient p : ℝ)-moebiusReal p)*(selbergMultiplesCoord N c p)^2) =
      sievePrimeTailReserve N c := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := primeTail_mem hp
    rw [totient_sub_moebiusReal_prime hp'.2.2.1,selbergMultiplesCoord_primeTail hp]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    field_simp
  rw [← hprime]
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeTail_subset N)
  intro e he _
  exact mul_nonneg (primeTail_diagonal_nonneg (Finset.mem_Icc.mp he).1) (sq_nonneg _)

/-- Exact completion of squares: the calibration price includes every non-prime mode. -/
theorem sievePrimeTail_calibration_identity (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (1-t)*sieveSuccessorReserve N c + t*sievePrimeTailResponse N c -
      t*(1-t)*(c 1)^2*sievePrimeTailMass N =
    (1-t)*(sieveSuccessorReserve N c-sievePrimeTailReserve N c) +
      ∑ p ∈ sievePrimeTail N, (c p+t*c 1)^2/(p : ℝ) := by
  have h : (∑ p ∈ sievePrimeTail N, (c p+t*c 1)^2/(p : ℝ)) =
      (1-t)*sievePrimeTailReserve N c + t*sievePrimeTailResponse N c -
        t*(1-t)*(c 1)^2*sievePrimeTailMass N := by
    unfold sievePrimeTailReserve sievePrimeTailResponse sievePrimeTailMass
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := primeTail_mem hp
    rw [sieveSeq_prime_of_le hp'.2.2.1 hp'.2.1]
    ring
  rw [h]
  ring

/-- Sharp source calibration inequality, without a sign or cancellation premise. -/
theorem sievePrimeTail_calibration_bound {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℝ) {t : ℝ} (ht1 : t ≤ 1) :
    t*(1-t)*(c 1)^2*sievePrimeTailMass N ≤
      (1-t)*sieveSuccessorReserve N c + t*sievePrimeTailResponse N c := by
  have hres := sievePrimeTailReserve_le_successorReserve hN c
  have hsq : 0 ≤ ∑ p ∈ sievePrimeTail N, (c p+t*c 1)^2/(p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg p)
  have hprod := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hres)
  have hid := sievePrimeTail_calibration_identity N c t
  linarith only [hid,hsq,hprod]

/-- Explicit attaining weights for every supporting calibration parameter. -/
def sievePrimeTailCalibrationWeight (N : ℕ) (a t : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then a else if d ∈ sievePrimeTail N then -t*a else 0

private theorem primeTail_weight_one (N : ℕ) (a t : ℝ) :
    sievePrimeTailCalibrationWeight N a t 1 = a := by
  simp [sievePrimeTailCalibrationWeight]

private theorem primeTail_weight_prime {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (a t : ℝ) : sievePrimeTailCalibrationWeight N a t p = -t*a := by
  have hp' := primeTail_mem hp
  simp [sievePrimeTailCalibrationWeight,hp,hp'.2.2.1.ne_one]

private theorem primeTail_weight_coordinate {N e : ℕ} (he : 2 ≤ e)
    (a t : ℝ) : selbergMultiplesCoord N (sievePrimeTailCalibrationWeight N a t) e =
      if e ∈ sievePrimeTail N then (-t*a)/(e : ℝ) else 0 := by
  by_cases heP : e ∈ sievePrimeTail N
  · rw [if_pos heP,selbergMultiplesCoord_primeTail heP,primeTail_weight_prime heP]
  · rw [if_neg heP]
    unfold selbergMultiplesCoord
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨_,hed⟩ := Finset.mem_filter.mp hd
    have hd1 : d ≠ 1 := by
      intro hd1
      subst d
      have hle := Nat.le_of_dvd (by omega : 0 < 1) hed
      omega
    have hdP : d ∉ sievePrimeTail N := by
      intro hdP
      have hdprime := (primeTail_mem hdP).2.2.1
      rcases (Nat.dvd_prime hdprime).mp hed with he1 | hed'
      · omega
      · exact heP (by simpa only [hed'] using hdP)
    simp [sievePrimeTailCalibrationWeight,hd1,hdP]

/-- The constructed coefficients attain both sides of the entire calibration curve. -/
theorem sievePrimeTailCalibrationWeight_reserves {N : ℕ} (hN : 1 ≤ N)
    (a t : ℝ) :
    sieveSuccessorReserve N (sievePrimeTailCalibrationWeight N a t) =
        t^2*a^2*sievePrimeTailMass N ∧
    sievePrimeTailResponse N (sievePrimeTailCalibrationWeight N a t) =
        (1-t)^2*a^2*sievePrimeTailMass N := by
  constructor
  · unfold sieveSuccessorReserve
    rw [selbergSubBezoutQuadraticForm_eq_Icc_two hN]
    have hterm (e : ℕ) (he : e ∈ Finset.Icc 2 N) :
        ((Nat.totient e : ℝ)-moebiusReal e)*
          (selbergMultiplesCoord N (sievePrimeTailCalibrationWeight N a t) e)^2 =
        if e ∈ sievePrimeTail N then t^2*a^2/(e : ℝ) else 0 := by
      rw [primeTail_weight_coordinate (Finset.mem_Icc.mp he).1]
      by_cases heP : e ∈ sievePrimeTail N
      · simp only [if_pos heP,totient_sub_moebiusReal_prime (primeTail_mem heP).2.2.1]
        have he0 : (e : ℝ) ≠ 0 := by
          exact_mod_cast (show e ≠ 0 by have := (Finset.mem_Icc.mp he).1; omega)
        field_simp
      · simp [heP]
    rw [Finset.sum_congr rfl hterm,← Finset.sum_filter]
    have hset : (Finset.Icc 2 N).filter (fun e => e ∈ sievePrimeTail N) =
        sievePrimeTail N := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨primeTail_subset N h,h⟩⟩
    rw [hset,sievePrimeTailMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  · unfold sievePrimeTailResponse sievePrimeTailMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := primeTail_mem hp
    rw [sieveSeq_prime_of_le hp'.2.2.1 hp'.2.1,
      primeTail_weight_one,primeTail_weight_prime hp]
    ring

/-- Every calibration bound is attained by explicit arithmetic coefficients. -/
theorem sievePrimeTail_calibration_attained {N : ℕ} (hN : 1 ≤ N)
    (a t : ℝ) :
    ∃ c : ℕ → ℝ, c 1 = a ∧
      (1-t)*sieveSuccessorReserve N c+t*sievePrimeTailResponse N c =
        t*(1-t)*a^2*sievePrimeTailMass N := by
  refine ⟨sievePrimeTailCalibrationWeight N a t,primeTail_weight_one N a t,?_⟩
  obtain ⟨hE,hR⟩ := sievePrimeTailCalibrationWeight_reserves hN a t
  rw [hE,hR]
  ring

/-- The actual Möbius coefficients force the full prime-tail reserve. -/
theorem sievePrimeTailMass_le_moebius_successorReserve {N : ℕ} (hN : 1 ≤ N) :
    sievePrimeTailMass N ≤ sieveSuccessorReserve N moebiusReal := by
  have h := sievePrimeTailReserve_le_successorReserve hN moebiusReal
  have heq : sievePrimeTailReserve N moebiusReal = sievePrimeTailMass N := by
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := (primeTail_mem hp).2.2.1
    simp [moebiusReal,ArithmeticFunction.moebius_apply_prime hprime]
  rwa [heq] at h

/-- The combined signed defect of the literal truncated Möbius source. -/
def moebiusCombinedPrefixDefect (N M : ℕ) : ℝ :=
  signedLcmFractDefect N M moebiusReal + bezoutSawtoothRemainderForm M N moebiusReal

/-- Exact arithmetic cancellation through the complete sieve horizon, including its endpoint. -/
theorem moebiusCombinedPrefixDefect_eq {N M : ℕ} (hN : 2 ≤ N)
    (hM : 1 ≤ M) (hMN : M ≤ N) :
    moebiusCombinedPrefixDefect N M = (M : ℝ)*sieveSuccessorReserve N moebiusReal-1 := by
  have hsquare : (∑ k ∈ Finset.Icc 1 M, (sieveSeq N moebiusReal k)^2) = 1 := by
    have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 M) :
        (sieveSeq N moebiusReal k)^2 = sieveSeq N moebiusReal k := by
      obtain ⟨hk1,hkM⟩ := Finset.mem_Icc.mp hk
      rw [sieveSeq_moebiusReal_eq_ite_of_le hk1 (hkM.trans hMN)]
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl hpoint,sum_sieveSeq_moebiusReal_eq_one_of_le hM hMN]
  have hsuccessor : (∑ k ∈ Finset.Icc 1 M,
      sieveSeq N moebiusReal k*sieveSeq N moebiusReal (k+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    obtain ⟨hk1,hkM⟩ := Finset.mem_Icc.mp hk
    by_cases hk : k = 1
    · subst k
      have htwo : sieveSeq N moebiusReal 2 = 0 := by
        simpa using sieveSeq_moebiusReal_eq_ite_of_le (by omega : 1 ≤ 2) hN
      simp [htwo]
    · rw [sieveSeq_moebiusReal_eq_ite_of_le hk1 (hkM.trans hMN),if_neg hk,zero_mul]
  have hsame := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N M moebiusReal
  have hsucc := sum_sieveSeq_mul_succ_eq_main_add_sawtooth M N moebiusReal
  rw [hsquare] at hsame
  rw [hsuccessor] at hsucc
  unfold moebiusCombinedPrefixDefect sieveSuccessorReserve
  linarith only [hsame,hsucc]

/-- A source-derived lower bound for the signed combined remainder, without absolute values. -/
theorem moebiusCombinedPrefixDefect_ge_primeTail {N M : ℕ} (hN : 2 ≤ N)
    (hM : 1 ≤ M) (hMN : M ≤ N) :
    (M : ℝ)*sievePrimeTailMass N-1 ≤ moebiusCombinedPrefixDefect N M := by
  rw [moebiusCombinedPrefixDefect_eq hN hM hMN]
  have h := sievePrimeTailMass_le_moebius_successorReserve (show 1 ≤ N by omega)
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg M)) 1

/-- At the sieve horizon the signed remainder pays at least one unit per terminal prime. -/
theorem moebiusCombinedPrefixDefect_ge_primeTailCard {N : ℕ} (hN : 2 ≤ N) :
    ((sievePrimeTail N).card : ℝ)-1 ≤ moebiusCombinedPrefixDefect N N := by
  have hmass : ((sievePrimeTail N).card : ℝ) ≤ (N : ℝ)*sievePrimeTailMass N := by
    unfold sievePrimeTailMass
    rw [Finset.mul_sum]
    have h : (∑ _p ∈ sievePrimeTail N, (1 : ℝ)) ≤
        ∑ p ∈ sievePrimeTail N, (N : ℝ)*(1/(p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := primeTail_mem hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.2.1
      have hdiv : 1 ≤ (N : ℝ)/(p : ℝ) := (le_div_iff₀ hp0).mpr (by simpa using hpN)
      simpa only [div_eq_mul_inv,one_mul] using hdiv
    simpa using h
  have h := moebiusCombinedPrefixDefect_ge_primeTail hN (show 1 ≤ N by omega) le_rfl
  linarith only [hmass,h]

end
end GaloisForLFunctions.BezoutValuationIncidence


open Finset Filter Topology
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- At an even cutoff the terminal primes are exactly the dyadic prime window. -/
theorem sievePrimeTail_two_mul (n : ℕ) :
    sievePrimeTail (2*n) = HTGeometry.primesInIoc n (2*n) := by
  ext p
  simp only [sievePrimeTail,HTGeometry.primesInIoc,Finset.mem_filter,
    Finset.mem_Icc,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_,hpN⟩,hprime,hhalf⟩
    exact ⟨⟨by omega,hpN⟩,hprime⟩
  · rintro ⟨⟨hlo,hhi⟩,hprime⟩
    exact ⟨⟨hprime.two_le,hhi⟩,hprime,by omega⟩

/-- An unconditional macroscopic lower bound for the actual combined signed defect. -/
theorem eventually_moebiusCombinedPrefixDefect_ge_div_log :
    ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ)*((n : ℝ)/Real.log n)-1 ≤
        moebiusCombinedPrefixDefect (2*n) (2*n) := by
  have hc := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (HTGeometry.eventually_primeCount_window_ge (K := 2) (by norm_num))
  filter_upwards [hc,eventually_ge_atTop (2 : ℕ)] with n hncount hn
  have hcast : (2 : ℝ)*(n : ℝ) = ((2*n : ℕ) : ℝ) := by push_cast; rfl
  simp only [hcast,Nat.floor_natCast] at hncount
  norm_num at hncount
  have h := moebiusCombinedPrefixDefect_ge_primeTailCard (show 2 ≤ 2*n by omega)
  rw [sievePrimeTail_two_mul,HTGeometry.card_primesInIoc (show n ≤ 2*n by omega)] at h
  linarith only [hncount,h]

/-- The unrenormalized Möbius defect exceeds every sublinear power budget along even cutoffs. -/
theorem eventually_moebiusCombinedPrefixDefect_gt_rpow
    {α : ℝ} (hα : α < 1) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C*((2*n : ℕ) : ℝ)^α < moebiusCombinedPrefixDefect (2*n) (2*n) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)^(1-α))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero.comp hcast
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have hlim : Tendsto (fun n : ℕ =>
      (C*((2*n : ℕ) : ℝ)^α+1)*Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    have h := (hpow.const_mul (C*(2 : ℝ)^α)).add hlog
    simp only [mul_zero,add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp0 : (n : ℝ)^α ≠ 0 := (Real.rpow_pos_of_pos hn0 α).ne'
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le,
      Real.rpow_sub hn0,Real.rpow_one]
    field_simp [hn0.ne',hp0]
  filter_upwards [eventually_moebiusCombinedPrefixDefect_ge_div_log,
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)),
    eventually_ge_atTop (2 : ℕ)] with n hdebt hsmall hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hlog0 : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hmul := (div_lt_iff₀ hn0).mp hsmall
  have hdiv := (lt_div_iff₀ hlog0).mpr hmul
  have hsmall' : C*((2*n : ℕ) : ℝ)^α+1 < (1/2 : ℝ)*((n : ℝ)/Real.log n) := by
    simpa only [div_eq_mul_inv,mul_assoc] using hdiv
  linarith only [hsmall',hdebt]

/-- A uniform sublinear power estimate for the raw combined remainder is false for the literal source. -/
theorem not_eventually_moebiusCombinedPrefixDefect_le_rpow
    {α : ℝ} (hα : α < 1) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      moebiusCombinedPrefixDefect N N ≤ C*(N : ℝ)^α := by
  rintro ⟨C,hC⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hC
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp
    (eventually_moebiusCombinedPrefixDefect_gt_rpow hα C)
  have hlower := hn₀ (N₀+n₀+1) (by omega)
  have hupper := hN₀ (2*(N₀+n₀+1)) (by omega)
  linarith only [hlower,hupper]

end
end GaloisForLFunctions.BezoutValuationIncidence
