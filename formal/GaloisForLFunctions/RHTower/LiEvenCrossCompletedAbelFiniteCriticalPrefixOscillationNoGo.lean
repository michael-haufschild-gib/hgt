import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero
import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusPoissonReserve
import GaloisForLFunctions.RHTower.PrimeArchShiftThirteenCircleCone
import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence


/-!
# Finite critical-prefix oscillation no-go for the even Li completed-Abel current

This module kills the atomwise and finite-prefix positivity producer for LI-CAB5.  For every
nonempty finite packet of critical-line Xi multiplicity copies and every squared mass
`0 < v ≤ 1/4`, its adjacent completed-Abel current has both signs cofinally in the Li mode.

Each critical atom is reduced exactly to

`(n+1) a_q(v) sin((n+1) omega_q(v))`,

where `a_q(v) > 0` and `0 < omega_q(v) < pi`.  A delayed simultaneous phase recurrence,
requiring no rational independence and allowing repeated atoms, returns arbitrarily late modes
near both the positive first mode and its negative.  Hardy's theorem supplies a critical-line
copy, so closed capstones refute all-mode atomwise positivity and universal nonempty finite-packet
positivity at the LI-CAB5 endpoint.

Exact RH proof strategy killed:

finite-prefix or termwise current nonnegativity
`=>` complete current nonnegativity by positive exhaustion
`=>` LI-CAB5
`=>` LI-CAB3
`=>` RH.

Positive survivor: any viable LI-CAB5 proof must use essential infinite, nonuniform tail
cancellation; no fixed nonempty finite critical prefix can carry the required all-mode sign.

All results are unconditional.  No numerical computation is used.
-/

open Polynomial Real Filter
open scoped BigOperators

namespace RHTower

noncomputable section

def liEvenCrossCriticalAtomMass (v : ℝ)
    (q : XiCriticalLineResolventCopy) : ℝ :=
  (xiShiftedReciprocalSquare v q.1).re

def liEvenCrossCriticalAtomNode (v : ℝ)
    (q : XiCriticalLineResolventCopy) : ℝ :=
  v * liEvenCrossCriticalAtomMass v q

def liEvenCrossCriticalAtomAngle (v : ℝ)
    (q : XiCriticalLineResolventCopy) : ℝ :=
  Real.arccos (2 * liEvenCrossCriticalAtomNode v q - 1)

def liEvenCrossCriticalAtomFrequency (v : ℝ)
    (q : XiCriticalLineResolventCopy) : ℝ :=
  2 * Real.pi - 2 * liEvenCrossCriticalAtomAngle v q

def liEvenCrossCriticalAtomAmplitude (v : ℝ)
    (q : XiCriticalLineResolventCopy) : ℝ :=
  liEvenCrossCriticalAtomMass v q *
    (1 - liEvenCrossCriticalAtomNode v q) /
      Real.sin (liEvenCrossCriticalAtomAngle v q)

theorem xiShiftedReciprocalSquare_criticalAtomMass
    {v : ℝ} (hv : 0 ≤ v) (q : XiCriticalLineResolventCopy) :
    xiShiftedReciprocalSquare v q.1 =
      (liEvenCrossCriticalAtomMass v q : ℂ) := by
  obtain ⟨x, hx, hshift⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hv q.1 q.2
  have hre : liEvenCrossCriticalAtomMass v q = x := by
    simp [liEvenCrossCriticalAtomMass, hshift]
  simpa [hre] using hshift

theorem liEvenCrossCriticalAtomMass_pos
    {v : ℝ} (hv : 0 ≤ v) (q : XiCriticalLineResolventCopy) :
    0 < liEvenCrossCriticalAtomMass v q := by
  obtain ⟨x, hx, hshift⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hv q.1 q.2
  simpa [liEvenCrossCriticalAtomMass, hshift] using hx

theorem liEvenCrossCriticalAtomMass_lt_two_over_fortyOne
    {v : ℝ} (hv : 0 ≤ v) (q : XiCriticalLineResolventCopy) :
    liEvenCrossCriticalAtomMass v q < 2 / 41 := by
  have hmass := liEvenCrossCriticalAtomMass_pos hv q
  have hshift := xiShiftedReciprocalSquare_criticalAtomMass hv q
  have hle := norm_xiShiftedReciprocalSquare_le hv q.1
  have hlt := norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q.1
  rw [hshift, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmass] at hle
  exact hle.trans_lt hlt

theorem liEvenCrossCriticalAtomNode_mem
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : XiCriticalLineResolventCopy) :
    0 < liEvenCrossCriticalAtomNode v q ∧
      liEvenCrossCriticalAtomNode v q < 1 / 2 := by
  have hmass := liEvenCrossCriticalAtomMass_pos hv0.le q
  have hmasslt := liEvenCrossCriticalAtomMass_lt_two_over_fortyOne hv0.le q
  dsimp [liEvenCrossCriticalAtomNode]
  constructor
  · exact mul_pos hv0 hmass
  · nlinarith

theorem liEvenCrossCriticalAtomAngle_mem
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : XiCriticalLineResolventCopy) :
    Real.pi / 2 < liEvenCrossCriticalAtomAngle v q ∧
      liEvenCrossCriticalAtomAngle v q < Real.pi := by
  obtain ⟨hy0, hy2⟩ := liEvenCrossCriticalAtomNode_mem hv0 hv4 q
  let c := 2 * liEvenCrossCriticalAtomNode v q - 1
  have hcneg : c < 0 := by dsimp [c]; linarith
  have hcm1 : -1 < c := by dsimp [c]; linarith
  have hθpi : Real.arccos c < Real.pi := Real.arccos_lt_pi.mpr hcm1
  have hθhalf : Real.pi / 2 < Real.arccos c := by
    have hnlt : ¬ Real.arccos c < Real.pi / 2 := by
      rw [Real.arccos_lt_pi_div_two]
      linarith
    have hle : Real.pi / 2 ≤ Real.arccos c := le_of_not_gt hnlt
    exact hle.lt_of_ne (by
      intro heq
      have hcos := Real.cos_arccos (show -1 ≤ c by linarith)
        (show c ≤ 1 by linarith)
      rw [← heq, Real.cos_pi_div_two] at hcos
      linarith)
  simpa [liEvenCrossCriticalAtomAngle, c] using And.intro hθhalf hθpi

theorem liEvenCrossCriticalAtomFrequency_mem
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : XiCriticalLineResolventCopy) :
    0 < liEvenCrossCriticalAtomFrequency v q ∧
      liEvenCrossCriticalAtomFrequency v q < Real.pi := by
  obtain ⟨hhalf, hpi⟩ := liEvenCrossCriticalAtomAngle_mem hv0 hv4 q
  dsimp [liEvenCrossCriticalAtomFrequency]
  constructor <;> linarith

theorem liEvenCrossCriticalAtomAmplitude_pos
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : XiCriticalLineResolventCopy) :
    0 < liEvenCrossCriticalAtomAmplitude v q := by
  obtain ⟨hy0, hy2⟩ := liEvenCrossCriticalAtomNode_mem hv0 hv4 q
  obtain ⟨hhalf, hpi⟩ := liEvenCrossCriticalAtomAngle_mem hv0 hv4 q
  exact div_pos
    (mul_pos (liEvenCrossCriticalAtomMass_pos hv0.le q) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) hpi)

theorem sin_mul_eval_chebyshevU_cos (θ : ℝ) (n : ℕ) :
    Real.sin θ * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ) =
      Real.sin (((n : ℝ) + 1) * θ) := by
  have hrec (k : ℕ)
      (hk : Real.sin θ * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) =
        Real.sin (((k : ℝ) + 1) * θ))
      (hks : Real.sin θ *
          (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) =
        Real.sin ((((k + 1 : ℕ) : ℝ) + 1) * θ)) :
      Real.sin θ *
          (Polynomial.Chebyshev.U ℝ ((k + 2 : ℕ) : ℤ)).eval (Real.cos θ) =
        Real.sin ((((k + 2 : ℕ) : ℝ) + 1) * θ) := by
    rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by omega,
      Polynomial.Chebyshev.U_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega]
    rw [mul_sub]
    calc
      _ = 2 * Real.cos θ *
              (Real.sin θ *
                (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) -
            Real.sin θ *
              (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) := by ring
      _ = 2 * Real.cos θ * Real.sin ((((k + 1 : ℕ) : ℝ) + 1) * θ) -
            Real.sin (((k : ℝ) + 1) * θ) := by rw [hks, hk]
      _ = Real.sin ((((k + 2 : ℕ) : ℝ) + 1) * θ) := by
        rw [show ((((k + 2 : ℕ) : ℝ) + 1) * θ) =
            ((((k + 1 : ℕ) : ℝ) + 1) * θ) + θ by push_cast; ring,
          show (((k : ℝ) + 1) * θ) =
            ((((k + 1 : ℕ) : ℝ) + 1) * θ) - θ by push_cast; ring,
          Real.sin_add, Real.sin_sub]
        ring
  have hp : ∀ k : ℕ,
      (Real.sin θ * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) =
        Real.sin (((k : ℝ) + 1) * θ)) ∧
      (Real.sin θ *
          (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) =
        Real.sin ((((k + 1 : ℕ) : ℝ) + 1) * θ)) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp [Polynomial.Chebyshev.U_zero]
        · norm_num [Polynomial.Chebyshev.U_one]
          rw [Real.sin_two_mul]
          ring
    | succ k ih =>
        exact ⟨ih.2, hrec k ih.1 ih.2⟩
  exact (hp n).1

theorem liEvenCrossCriticalAtomAngle_cos
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : XiCriticalLineResolventCopy) :
    Real.cos (liEvenCrossCriticalAtomAngle v q) =
      2 * liEvenCrossCriticalAtomNode v q - 1 := by
  obtain ⟨hy0, hy2⟩ := liEvenCrossCriticalAtomNode_mem hv0 hv4 q
  rw [liEvenCrossCriticalAtomAngle, Real.cos_arccos]
  · nlinarith
  · nlinarith

theorem liEvenCrossSquareMassAdjacentFlux_criticalAtom_sine
    {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (n : ℕ) (q : XiCriticalLineResolventCopy) :
    liEvenCrossSquareMassAdjacentFlux v n q.1 =
      (((n : ℝ) + 1) * liEvenCrossCriticalAtomAmplitude v q *
        Real.sin (((n : ℝ) + 1) * liEvenCrossCriticalAtomFrequency v q) : ℝ) := by
  let x := liEvenCrossCriticalAtomMass v q
  let y := liEvenCrossCriticalAtomNode v q
  let θ := liEvenCrossCriticalAtomAngle v q
  let ω := liEvenCrossCriticalAtomFrequency v q
  have hxy : v * x = y := by rfl
  have hcos : Real.cos θ = 2 * y - 1 := by
    simpa [θ, y] using liEvenCrossCriticalAtomAngle_cos hv0 hv4 q
  have hθ := liEvenCrossCriticalAtomAngle_mem hv0 hv4 q
  have hsinpos : 0 < Real.sin θ := by
    exact Real.sin_pos_of_pos_of_lt_pi (by simpa [θ] using hθ.1.trans' (by positivity))
      (by simpa [θ] using hθ.2)
  have heval : Polynomial.eval y (liEvenCrossUnitFluxQuotient n) =
      -((n : ℝ) + 1) * (1 - y) *
        (Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).eval (2 * y - 1) := by
    rw [liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
    simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_comp, liEvenCrossUnitAffine]
  have hU : Real.sin θ *
      (Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).eval (2 * y - 1) =
        Real.sin ((2 * ((n : ℝ) + 1)) * θ) := by
    rw [← hcos]
    convert sin_mul_eval_chebyshevU_cos θ (2 * n + 1) using 1
    all_goals
      push_cast
      ring
  have hfreq : Real.sin (((n : ℝ) + 1) * ω) =
      -Real.sin ((2 * ((n : ℝ) + 1)) * θ) := by
    rw [show ((n : ℝ) + 1) * ω =
        ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) -
          (2 * ((n : ℝ) + 1)) * θ by
            dsimp [ω, liEvenCrossCriticalAtomFrequency]
            push_cast
            ring,
      Real.sin_nat_mul_two_pi_sub]
  have hreal : x * Polynomial.eval y (liEvenCrossUnitFluxQuotient n) =
      ((n : ℝ) + 1) * liEvenCrossCriticalAtomAmplitude v q *
        Real.sin (((n : ℝ) + 1) * ω) := by
    rw [heval, hfreq]
    change x * (-((n : ℝ) + 1) * (1 - y) *
        (Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).eval (2 * y - 1)) =
      ((n : ℝ) + 1) * (x * (1 - y) / Real.sin θ) *
        -Real.sin ((2 * ((n : ℝ) + 1)) * θ)
    field_simp [hsinpos.ne']
    ring_nf at hU ⊢
    linear_combination (norm := ring_nf) x * (y - 1) * hU
  rw [liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient hv0,
    xiShiftedReciprocalSquare_criticalAtomMass hv0.le q,
    show (v : ℂ) * (liEvenCrossCriticalAtomMass v q : ℂ) = (y : ℂ) by
      exact_mod_cast hxy,
    evalRealPolynomial_ofReal]
  exact_mod_cast hreal

def finitePositiveSinePacket {d : ℕ} (a ω : Fin d → ℝ) (m : ℕ) : ℝ :=
  ∑ i, a i * Real.sin ((m : ℝ) * ω i)

theorem finitePositiveSinePacket_one_pos {d : ℕ} (hd : 0 < d)
    {a ω : Fin d → ℝ} (ha : ∀ i, 0 < a i)
    (hω0 : ∀ i, 0 < ω i) (hωπ : ∀ i, ω i < Real.pi) :
    0 < finitePositiveSinePacket a ω 1 := by
  simp only [finitePositiveSinePacket, Nat.cast_one, one_mul]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (ha i).le
      (Real.sin_pos_of_pos_of_lt_pi (hω0 i) (hωπ i)).le
  · let i : Fin d := ⟨0, hd⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (ha i) (Real.sin_pos_of_pos_of_lt_pi (hω0 i) (hωπ i))

theorem finitePositiveSinePacket_weightSum_pos {d : ℕ} (hd : 0 < d)
    {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) :
    0 < ∑ i, a i := by
  apply Finset.sum_pos'
  · intro i hi
    exact (ha i).le
  · let i : Fin d := ⟨0, hd⟩
    exact ⟨i, Finset.mem_univ i, ha i⟩

theorem finitePositiveSinePacket_phase_recurrence_close
    {d k : ℕ} {a ω : Fin d → ℝ} {r : Fin d → ℤ} {ε : ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (hphase : ∀ i, |(k : ℝ) * ω i - 2 * Real.pi * r i| ≤ ε) :
    |finitePositiveSinePacket a ω (k + 1) - finitePositiveSinePacket a ω 1| ≤
      (∑ i, a i) * ε := by
  have hpoint (i : Fin d) :
      |Real.sin (((k + 1 : ℕ) : ℝ) * ω i) - Real.sin (ω i)| ≤ ε := by
    let e : ℝ := (k : ℝ) * ω i - 2 * Real.pi * r i
    have hperiod : Real.sin (((k + 1 : ℕ) : ℝ) * ω i) =
        Real.sin (ω i + e) := by
      have hsin := Real.sin_add_int_mul_two_pi (ω i + e) (r i)
      rw [show (ω i + e) + (r i : ℝ) * (2 * Real.pi) =
        (((k + 1 : ℕ) : ℝ) * ω i) by dsimp [e]; push_cast; ring] at hsin
      exact hsin
    rw [hperiod]
    exact (Real.abs_sin_sub_sin_le _ _).trans (by
      simpa [e] using hphase i)
  rw [finitePositiveSinePacket, finitePositiveSinePacket]
  norm_num only [Nat.cast_one, one_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * Real.sin (((k + 1 : ℕ) : ℝ) * ω i) -
        a i * Real.sin (ω i))| ≤
        ∑ i, |a i * Real.sin (((k + 1 : ℕ) : ℝ) * ω i) -
          a i * Real.sin (ω i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, a i * |Real.sin (((k + 1 : ℕ) : ℝ) * ω i) -
          Real.sin (ω i)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (ha i)]
    _ ≤ ∑ i, a i * ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i) (ha i)
    _ = (∑ i, a i) * ε := by rw [Finset.sum_mul]

theorem finitePositiveSinePacket_phase_recurrence_close_neg
    {d k : ℕ} (hk : 1 ≤ k) {a ω : Fin d → ℝ} {r : Fin d → ℤ} {ε : ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (hphase : ∀ i, |(k : ℝ) * ω i - 2 * Real.pi * r i| ≤ ε) :
    |finitePositiveSinePacket a ω (k - 1) + finitePositiveSinePacket a ω 1| ≤
      (∑ i, a i) * ε := by
  have hpoint (i : Fin d) :
      |Real.sin (((k - 1 : ℕ) : ℝ) * ω i) + Real.sin (ω i)| ≤ ε := by
    let e : ℝ := (k : ℝ) * ω i - 2 * Real.pi * r i
    have hperiod : Real.sin (((k - 1 : ℕ) : ℝ) * ω i) =
        Real.sin (-ω i + e) := by
      have hsin := Real.sin_add_int_mul_two_pi (-ω i + e) (r i)
      rw [show (-ω i + e) + (r i : ℝ) * (2 * Real.pi) =
        (((k - 1 : ℕ) : ℝ) * ω i) by
          dsimp [e]
          rw [Nat.cast_sub hk]
          push_cast
          ring] at hsin
      exact hsin
    rw [hperiod]
    have hsinneg : Real.sin (-ω i) = -Real.sin (ω i) := Real.sin_neg _
    have h := Real.abs_sin_sub_sin_le (-ω i + e) (-ω i)
    rw [hsinneg] at h
    have h'' : |Real.sin (-ω i + e) + Real.sin (ω i)| ≤
        |-ω i + e + ω i| := by
      simpa only [sub_neg_eq_add] using h
    have h' : |Real.sin (-ω i + e) + Real.sin (ω i)| ≤ |e| := by
      calc
        |Real.sin (-ω i + e) + Real.sin (ω i)| ≤
            |-ω i + e + ω i| := h''
        _ = |e| := by ring_nf
    exact h'.trans (by simpa [e] using hphase i)
  rw [finitePositiveSinePacket, finitePositiveSinePacket]
  norm_num only [Nat.cast_one, one_mul]
  rw [← Finset.sum_add_distrib]
  calc
    |∑ i, (a i * Real.sin (((k - 1 : ℕ) : ℝ) * ω i) +
        a i * Real.sin (ω i))| ≤
        ∑ i, |a i * Real.sin (((k - 1 : ℕ) : ℝ) * ω i) +
          a i * Real.sin (ω i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, a i * |Real.sin (((k - 1 : ℕ) : ℝ) * ω i) +
          Real.sin (ω i)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, abs_mul, abs_of_nonneg (ha i)]
    _ ≤ ∑ i, a i * ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i) (ha i)
    _ = (∑ i, a i) * ε := by rw [Finset.sum_mul]

theorem cofinal_both_signs_finitePositiveSinePacket
    {d : ℕ} (hd : 0 < d) {a ω : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) (hω0 : ∀ i, 0 < ω i)
    (hωπ : ∀ i, ω i < Real.pi) (N : ℕ) :
    (∃ m : ℕ, N ≤ m ∧ 0 < finitePositiveSinePacket a ω m) ∧
      ∃ m : ℕ, N ≤ m ∧ finitePositiveSinePacket a ω m < 0 := by
  let δ := finitePositiveSinePacket a ω 1
  let A := ∑ i, a i
  have hδ : 0 < δ := finitePositiveSinePacket_one_pos hd ha hω0 hωπ
  have hA : 0 < A := finitePositiveSinePacket_weightSum_pos hd ha
  have hε : 0 < δ / (4 * Real.pi * A) := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hkL, hkU, r, hphase⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
      (d := d) (Q := Q) (L := N + 2) ω
  have hk1 : 1 ≤ k := by omega
  have hbudget : A * (2 * Real.pi / (Q + 1 : ℝ)) < δ / 2 := by
    have hmul := mul_lt_mul_of_pos_left hQ
      (show 0 < 4 * Real.pi * A by positivity)
    field_simp at hmul ⊢
    nlinarith [Real.pi_pos, hA]
  have hplus := finitePositiveSinePacket_phase_recurrence_close
    (a := a) (ω := ω) (r := r) (ε := 2 * Real.pi / (Q + 1 : ℝ))
    (fun i => (ha i).le) hphase
  have hminus := finitePositiveSinePacket_phase_recurrence_close_neg hk1
    (a := a) (ω := ω) (r := r) (ε := 2 * Real.pi / (Q + 1 : ℝ))
    (fun i => (ha i).le) hphase
  constructor
  · refine ⟨k + 1, by omega, ?_⟩
    have hlower := (abs_le.mp hplus).1
    dsimp [δ, A] at hbudget hlower ⊢
    linarith
  · refine ⟨k - 1, by omega, ?_⟩
    have hupper := (abs_le.mp hminus).2
    dsimp [δ, A] at hbudget hupper ⊢
    linarith

def liEvenCrossCriticalPacketCurrent {d : ℕ} (v : ℝ)
    (q : Fin d → XiCriticalLineResolventCopy) (n : ℕ) : ℝ :=
  ∑ i, (liEvenCrossSquareMassAdjacentFlux v n (q i).1).re

theorem liEvenCrossCriticalPacketCurrent_eq_sinePacket
    {d : ℕ} {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (n : ℕ) :
    liEvenCrossCriticalPacketCurrent v q n =
      ((n : ℝ) + 1) * finitePositiveSinePacket
        (fun i => liEvenCrossCriticalAtomAmplitude v (q i))
        (fun i => liEvenCrossCriticalAtomFrequency v (q i)) (n + 1) := by
  rw [liEvenCrossCriticalPacketCurrent, finitePositiveSinePacket,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hatom := congrArg Complex.re
    (liEvenCrossSquareMassAdjacentFlux_criticalAtom_sine hv0 hv4 n (q i))
  simpa only [Complex.ofReal_re, Nat.cast_add, Nat.cast_one, mul_assoc] using hatom

theorem cofinal_both_signs_liEvenCrossCriticalPacketCurrent
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (N : ℕ) :
    (∃ n : ℕ, N ≤ n ∧ 0 < liEvenCrossCriticalPacketCurrent v q n) ∧
      ∃ n : ℕ, N ≤ n ∧ liEvenCrossCriticalPacketCurrent v q n < 0 := by
  let a : Fin d → ℝ := fun i => liEvenCrossCriticalAtomAmplitude v (q i)
  let ω : Fin d → ℝ := fun i => liEvenCrossCriticalAtomFrequency v (q i)
  have ha : ∀ i, 0 < a i := fun i => liEvenCrossCriticalAtomAmplitude_pos hv0 hv4 (q i)
  have hω0 : ∀ i, 0 < ω i := fun i => (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).1
  have hωpi : ∀ i, ω i < Real.pi := fun i =>
    (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).2
  obtain ⟨⟨mpos, hmposN, hmpos⟩, ⟨mneg, hmnegN, hmneg⟩⟩ :=
    cofinal_both_signs_finitePositiveSinePacket hd ha hω0 hωpi (N + 1)
  have hmpos1 : 1 ≤ mpos := by omega
  have hmneg1 : 1 ≤ mneg := by omega
  constructor
  · refine ⟨mpos - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCurrent_eq_sinePacket hv0 hv4]
    have hindex : mpos - 1 + 1 = mpos := Nat.sub_add_cancel hmpos1
    rw [hindex]
    have hcast : (((mpos - 1 : ℕ) : ℝ) + 1) = (mpos : ℝ) := by
      rw [Nat.cast_sub hmpos1]
      push_cast
      ring
    rw [hcast]
    exact mul_pos (by exact_mod_cast hmpos1) (by simpa [a, ω] using hmpos)
  · refine ⟨mneg - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCurrent_eq_sinePacket hv0 hv4]
    have hindex : mneg - 1 + 1 = mneg := Nat.sub_add_cancel hmneg1
    rw [hindex]
    have hcast : (((mneg - 1 : ℕ) : ℝ) + 1) = (mneg : ℝ) := by
      rw [Nat.cast_sub hmneg1]
      push_cast
      ring
    rw [hcast]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hmneg1) (by simpa [a, ω] using hmneg)

theorem exists_hardyCritical_liEvenCrossAdjacentFlux_neg :
    ∃ n : ℕ, ∃ q : XiCriticalLineResolventCopy,
      (liEvenCrossSquareMassAdjacentFlux (1 / 4) n q.1).re < 0 := by
  let q0 : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  let packet : Fin 1 → XiCriticalLineResolventCopy := fun _ => q0
  obtain ⟨n, hn, hneg⟩ :=
    (cofinal_both_signs_liEvenCrossCriticalPacketCurrent (d := 1) (by norm_num)
      (v := 1 / 4) (by norm_num) (by norm_num) packet 0).2
  refine ⟨n, q0, ?_⟩
  simpa [liEvenCrossCriticalPacketCurrent, packet] using hneg

theorem not_all_hardyCritical_liEvenCrossAdjacentFlux_nonnegative :
    ¬ ∀ (n : ℕ) (q : XiCriticalLineResolventCopy),
      0 ≤ (liEvenCrossSquareMassAdjacentFlux (1 / 4) n q.1).re := by
  obtain ⟨n, q, hneg⟩ := exists_hardyCritical_liEvenCrossAdjacentFlux_neg
  intro hall
  linarith [hall n q]

theorem not_all_nonempty_finiteCriticalPacket_currents_nonnegative :
    ¬ ∀ (d : ℕ) (q : Fin d → XiCriticalLineResolventCopy),
      0 < d → ∀ n : ℕ, 0 ≤ liEvenCrossCriticalPacketCurrent (1 / 4) q n := by
  let q0 : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  let packet : Fin 1 → XiCriticalLineResolventCopy := fun _ => q0
  intro hall
  obtain ⟨n, hn, hneg⟩ :=
    (cofinal_both_signs_liEvenCrossCriticalPacketCurrent (d := 1) (by norm_num)
      (v := 1 / 4) (by norm_num) (by norm_num) packet 0).2
  linarith [hall 1 packet (by norm_num) n]

end
end RHTower

