import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimitivePrimePriceBeyondAMovingCofactorCut
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries
import GaloisForLFunctions.SquareRootThreshold.TheFiveSixthsFacesOfTheZeroAbscissa

/-!
# The independent-endpoint price of the first cofactor octave

Take `x = 4n`, the prime cut `Q = ⌊2√n⌋` and the octave cut `V = ⌊(4n)^{1/3}⌋`. On the first
surviving cofactor octave `V < v ≤ 2V` the projected coefficient is exactly `−μ(v)`, and the
ordinary prime row is

  `R(v) = θ-mass of (3n/v, 4n/v] − θ-mass of (2n/v, 3n/v]`,  primes `p > Q`, `p ∤ n`.

For `n ≥ 4096` the cut `Q` lies below both intervals, the two lengths cancel, and

  `|R(v)| ≤ log n + 2 + 4D (4n/v)^b`  whenever `|θ(a) − a| ≤ D a^b`.

Summing absolute values over the octave gives the reference price

  `|Σ_{V<v≤2V, (v,n)=1} μ(v) R(v)| ≤ C n^{1/3 + 2b/3}`  for every `b > Θ`
  (`abs_firstCofactorOctave_le`).

With the corpus strip this is every exponent above `32999/36000 ≈ 0.91664`
(`abs_firstCofactorOctave_le_unconditional`); under `Θ ≤ 5/6` every exponent above `8/9`
(`abs_firstCofactorOctave_le_of_fiveSixths`). Any genuine estimate of the octave must beat this
price, which uses no cancellation between different cofactors.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The octave cut `V = ⌊(4n)^{1/3}⌋`. -/
def firstOctaveCut (n : ℕ) : ℕ := ⌊(4*n:ℝ)^((1:ℝ)/3)⌋₊

/-- The prime cut `Q = ⌊2√n⌋`. -/
def octavePrimeCut (n : ℕ) : ℕ := ⌊2*Real.sqrt n⌋₊

/-- The first projected cofactor octave: Möbius-weighted ordinary prime rows on
`(V, 2V]`, restricted to cofactors coprime to `n`. -/
def firstCofactorOctave (n : ℕ) : ℝ :=
  ∑ v ∈ (Ioc (firstOctaveCut n) (2*firstOctaveCut n)).filter (n.Coprime ·),
    (μ v:ℝ) * primitiveOrdinaryCofactorRow n (octavePrimeCut n) v

/-- The weight of a prime in the row: `1` on `(a₃, a₄]`, `−1` on `(a₂, a₃]`, `0` elsewhere. -/
private def octaveWeight (a4 a3 a2 p : ℕ) : ℝ :=
  (if p ≤ a4 then 1 else 0) - 2*(if p ≤ a3 then 1 else 0) + (if p ≤ a2 then 1 else 0)

private theorem abs_octaveWeight_le {a4 a3 a2 : ℕ} (h32 : a2 ≤ a3) (h43 : a3 ≤ a4) (p : ℕ) :
    |octaveWeight a4 a3 a2 p| ≤ 1 := by
  unfold octaveWeight
  split_ifs <;> first | (exfalso; omega) | norm_num

private theorem octaveWeight_eq_zero {a4 a3 a2 p : ℕ} (h32 : a2 ≤ a3) (h43 : a3 ≤ a4)
    (hp : p ≤ a2) : octaveWeight a4 a3 a2 p = 0 := by
  unfold octaveWeight
  rw [if_pos (hp.trans (h32.trans h43)), if_pos (hp.trans h32), if_pos hp]
  ring

/-- The row as a weighted sum over its allowed primes. -/
private theorem row_eq_sum {n Q v : ℕ} (hv : 0 < v) :
    primitiveOrdinaryCofactorRow n Q v =
      ∑ p ∈ (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n),
        Real.log p * octaveWeight (4*n/v) (3*n/v) (2*n/v) p := by
  change (∑ p ∈ (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n),
      if v ≤ 4*n/p then Real.log p else 0) -
    2*(∑ p ∈ (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n),
      if v ≤ 3*n/p then Real.log p else 0) +
    (∑ p ∈ (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n),
      if v ≤ 2*n/p then Real.log p else 0) = _
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (mem_Icc.mp (mem_filter.mp hp).1).1
  have key (T : ℕ) : v ≤ T/p ↔ p ≤ T/v := by
    rw [Nat.le_div_iff_mul_le hp0, Nat.le_div_iff_mul_le hv, mul_comm]
  simp only [octaveWeight, key]
  split_ifs <;> ring

private theorem theta_nat_eq_sum {a N : ℕ} (h : a ≤ N) :
    Chebyshev.theta a = ∑ p ∈ Nat.primesLE N, Real.log p * (if p ≤ a then 1 else 0) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primesLE]
  exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1.trans h, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩⟩

private theorem thetaCombo_eq (n v : ℕ) :
    Chebyshev.theta (4*n/v:ℕ) - 2*Chebyshev.theta (3*n/v:ℕ) + Chebyshev.theta (2*n/v:ℕ) =
      ∑ p ∈ Nat.primesLE (4*n), Real.log p * octaveWeight (4*n/v) (3*n/v) (2*n/v) p := by
  have h4 : 4*n/v ≤ 4*n := Nat.div_le_self _ _
  have h3 : 3*n/v ≤ 4*n := (Nat.div_le_self _ _).trans (by omega)
  have h2 : 2*n/v ≤ 4*n := (Nat.div_le_self _ _).trans (by omega)
  rw [theta_nat_eq_sum h4, theta_nat_eq_sum h3, theta_nat_eq_sum h2, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  unfold octaveWeight
  ring

/-- Above the prime cut the row differs from the second difference of `θ` only by primes
dividing `n`. -/
private theorem abs_row_sub_thetaCombo_le {n Q v : ℕ} (hn : 0 < n) (hv : 0 < v)
    (hQ : Q ≤ 2*n/v) :
    |primitiveOrdinaryCofactorRow n Q v - (Chebyshev.theta (4*n/v:ℕ) -
      2*Chebyshev.theta (3*n/v:ℕ) + Chebyshev.theta (2*n/v:ℕ))| ≤ Real.log n := by
  rw [row_eq_sum hv, thetaCombo_eq]
  have h32 : 2*n/v ≤ 3*n/v := Nat.div_le_div_right (by omega)
  have h43 : 3*n/v ≤ 4*n/v := Nat.div_le_div_right (by omega)
  set w := octaveWeight (4*n/v) (3*n/v) (2*n/v)
  set A := (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n)
  have hsub : A ⊆ Nat.primesLE (4*n) := fun p hp => by
    obtain ⟨hI, -, hpr, -⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp hI).2, hpr⟩
  rw [← sum_sdiff hsub, show ∀ a c : ℝ, a - (c + a) = -c from fun a c => by ring, abs_neg]
  have hterm : ∀ p ∈ Nat.primesLE (4*n) \ A,
      |Real.log p * w p| ≤ if p ∣ n then Real.log p else 0 := by
    intro p hp
    obtain ⟨hpL, hpA⟩ := mem_sdiff.mp hp
    obtain ⟨hp4, hpr⟩ := Nat.mem_primesLE.mp hpL
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hd : p ∣ n
    · rw [if_pos hd, abs_mul, abs_of_nonneg hlog]
      exact mul_le_of_le_one_right hlog (abs_octaveWeight_le h32 h43 p)
    · rw [if_neg hd]
      have hpQ : p ≤ Q := by
        by_contra hlt
        exact hpA (mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.one_lt.le, hp4⟩, lt_of_not_ge hlt, hpr, hd⟩)
      rw [show w p = 0 from octaveWeight_eq_zero h32 h43 (hpQ.trans hQ), mul_zero, abs_zero]
  have hfac : ∑ p ∈ Nat.primesLE (4*n) \ A, (if p ∣ n then Real.log p else 0) ≤ Real.log n := by
    rw [← sum_filter]
    have hsubF : (Nat.primesLE (4*n) \ A).filter (· ∣ n) ⊆ n.primeFactors := fun p hp => by
      obtain ⟨hp1, hd⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp (mem_sdiff.mp hp1).1).2, hd, hn.ne'⟩
    have hprod : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    calc _ ≤ ∑ p ∈ n.primeFactors, Real.log p :=
          sum_le_sum_of_subset_of_nonneg hsubF (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod (fun p hp =>
            Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast hprod)
          (by exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans hfac)

/-- Above the abscissa the ordinary prime error has a power bound at every integer. -/
private theorem exists_abs_theta_sub_le {b : ℝ} (hb : _root_.RHTower.zeroReSup < b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a : ℕ, |Chebyshev.theta a - a| ≤ D * (a:ℝ)^b := by
  have half := _root_.RHTower.half_le_zeroReSup.trans_lt hb
  obtain ⟨A, hA, psi⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb
  obtain ⟨C, err⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨A + |C|, by positivity, fun a => ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.cast_zero, Chebyshev.theta_zero, sub_zero, abs_zero, Real.zero_rpow (by linarith),
      mul_zero]
  have nr : 1 ≤ (a:ℝ) := Nat.one_le_cast.mpr ha
  have root : Real.sqrt a ≤ (a:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le nr half.le
  have small := (err (a:ℝ)).trans
    (mul_le_mul (le_abs_self C) root (Real.sqrt_nonneg _) (abs_nonneg C))
  have h := abs_sub_le (Chebyshev.theta a) (Chebyshev.psi a) (a:ℝ)
  rw [abs_sub_comm (Chebyshev.theta a) (Chebyshev.psi a),
    abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))] at h
  have hp := psi a nr
  linarith only [small, h, hp, mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg a) b)]

/-- **One row.** Its two lengths cancel; each endpoint costs one power of the prime error. -/
private theorem abs_row_le {n Q v : ℕ} {b D : ℝ} (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hθ : ∀ a : ℕ, |Chebyshev.theta a - a| ≤ D * (a:ℝ)^b)
    (hn : 0 < n) (hv : 0 < v) (hQ : Q ≤ 2*n/v) :
    |primitiveOrdinaryCofactorRow n Q v| ≤ Real.log n + 2 + 4*D*((4*n:ℝ)/v)^b := by
  have hdiff := abs_row_sub_thetaCombo_le hn hv hQ
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have fl (T : ℕ) : ((T/v : ℕ):ℝ) ≤ (T:ℝ)/v ∧ (T:ℝ)/v < ((T/v : ℕ):ℝ) + 1 := by
    refine ⟨Nat.cast_div_le, ?_⟩
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact Nat.lt_floor_add_one _
  obtain ⟨u4, l4⟩ := fl (4*n)
  obtain ⟨u3, l3⟩ := fl (3*n)
  obtain ⟨u2, l2⟩ := fl (2*n)
  push_cast at u4 l4 u3 l3 u2 l2
  have hm : (0:ℝ) ≤ (n:ℝ)/v := by positivity
  have hX : (0:ℝ) ≤ 4*(n:ℝ)/v := by positivity
  have hcomb : |((4*n/v:ℕ):ℝ) - 2*((3*n/v:ℕ):ℝ) + ((2*n/v:ℕ):ℝ)| ≤ 2 := by
    have e4 : 4*(n:ℝ)/v = 4*((n:ℝ)/v) := by ring
    have e3 : 3*(n:ℝ)/v = 3*((n:ℝ)/v) := by ring
    have e2 : 2*(n:ℝ)/v = 2*((n:ℝ)/v) := by ring
    rw [e4] at u4 l4; rw [e3] at u3 l3; rw [e2] at u2 l2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have pw (T : ℕ) (hT : (T:ℝ)/v ≤ 4*(n:ℝ)/v) :
      |Chebyshev.theta (T/v:ℕ) - ((T/v:ℕ):ℝ)| ≤ D*((4*n:ℝ)/v)^b := by
    refine (hθ (T/v)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      ((Nat.cast_div_le).trans hT) hb) hD)
  have p4 := pw (4*n) (by push_cast; exact le_rfl)
  have p3 := pw (3*n) (by push_cast; exact div_le_div_of_nonneg_right (by linarith) hvR.le)
  have p2 := pw (2*n) (by push_cast; exact div_le_div_of_nonneg_right (by linarith) hvR.le)
  have e4 := abs_le.mp p4; have e3 := abs_le.mp p3; have e2 := abs_le.mp p2
  have ec := abs_le.mp hcomb; have ed := abs_le.mp hdiff
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `(2QV)⁶ ≤ (2n)⁶` once `n ≥ 1024`: the prime cut lies below every interval of the octave. -/
private theorem octave_cut_below {n : ℕ} (hn : 1024 ≤ n) :
    octavePrimeCut n * (2*firstOctaveCut n) ≤ 2*n := by
  set Q := octavePrimeCut n
  set V := firstOctaveCut n
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hQ : Q^2 ≤ 4*n := by
    have h : (Q:ℝ) ≤ 2*Real.sqrt n := Nat.floor_le (by positivity)
    have h2 : (Q:ℝ)^2 ≤ 4*n := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg Q) h 2
      rwa [mul_pow, Real.sq_sqrt hnR, show (2:ℝ)^2 = 4 by norm_num] at this
    exact_mod_cast h2
  have hV : V^3 ≤ 4*n := by
    have h : (V:ℝ) ≤ (4*n:ℝ)^((1:ℝ)/3) := Nat.floor_le (by positivity)
    have h3 : (V:ℝ)^3 ≤ 4*n := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg V) h 3
      have e : ((4*n:ℝ)^((1:ℝ)/3))^3 = 4*n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rwa [e] at this
    exact_mod_cast h3
  by_contra! hlt
  have hpow := Nat.pow_lt_pow_left hlt (show 6 ≠ 0 by norm_num)
  have hbig : (Q * (2*V))^6 = 64 * (Q^2)^3 * (V^3)^2 := by ring
  have hle : 64 * (Q^2)^3 * (V^3)^2 ≤ 64 * (4*n)^3 * (4*n)^2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ 3)) (Nat.pow_le_pow_left hV 2)
  have hfin : 64 * (4*n)^3 * (4*n)^2 ≤ (2*n)^6 := by
    have h5 : 64 * (4*n)^3 * (4*n)^2 = 64 * 1024 * n^5 := by ring
    have h6 : (2*n)^6 = 64 * n * n^5 := by ring
    rw [h5, h6]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hn)
  omega

/-- **The independent-endpoint price.** For every `b ∈ (Θ, 1]` the first projected cofactor
octave is at most `C n^{1/3 + 2b/3}` for `n ≥ 4096`. -/
theorem abs_firstCofactorOctave_le {b : ℝ} (hb : _root_.RHTower.zeroReSup < b) (hb1 : b ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4096 ≤ n →
      |firstCofactorOctave n| ≤ C * (n:ℝ)^(1/3 + 2*b/3) := by
  obtain ⟨D, hD, hθ⟩ := exists_abs_theta_sub_le hb
  have hbh : 1/2 < b := _root_.RHTower.half_le_zeroReSup.trans_lt hb
  have hb0 : 0 ≤ b := by linarith
  refine ⟨4*(5 + 4*D), by positivity, fun n hn => ?_⟩
  set V := firstOctaveCut n
  set Q := octavePrimeCut n
  have hn0 : 0 < n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  set X : ℝ := 4*n with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef]; linarith
  have hX0 : 0 < X := by linarith
  have hVX : (V:ℝ) ≤ X^((1:ℝ)/3) := Nat.floor_le (by positivity)
  have hV1 : 1 ≤ V := Nat.le_floor (by
    rw [Nat.cast_one]; exact Real.one_le_rpow hX1 (by norm_num))
  have hVR : (1:ℝ) ≤ V := by exact_mod_cast hV1
  have hcut := octave_cut_below (show 1024 ≤ n by omega)
  have hterm : ∀ v ∈ (Ioc V (2*V)).filter (n.Coprime ·),
      |(μ v:ℝ) * primitiveOrdinaryCofactorRow n Q v| ≤ Real.log n + 2 + 4*D*(X/V)^b := by
    intro v hv
    obtain ⟨hvI, -⟩ := mem_filter.mp hv
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hvI
    have hv0 : 0 < v := by omega
    have hQv : Q ≤ 2*n/v :=
      (Nat.le_div_iff_mul_le hv0).mpr ((Nat.mul_le_mul_left Q hhi).trans hcut)
    rw [abs_mul]
    have hmu : |(μ v:ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hrow := abs_row_le hb0 hD hθ hn0 hv0 hQv
    have hmono : ((4*n:ℝ)/v)^b ≤ (X/V)^b :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hX0.le (by linarith) (by exact_mod_cast hlo.le)) hb0
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    calc _ ≤ 1 * |primitiveOrdinaryCofactorRow n Q v| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          exact hrow.trans (by nlinarith [mul_le_mul_of_nonneg_left hmono hD])
  have hcard : (((Ioc V (2*V)).filter (n.Coprime ·)).card : ℝ) ≤ V := by
    have := card_filter_le (Ioc V (2*V)) (n.Coprime ·)
    rw [Nat.card_Ioc, show 2*V - V = V by omega] at this
    exact_mod_cast this
  have hbound := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  rw [sum_const, nsmul_eq_mul] at hbound
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hB : 0 ≤ Real.log n + 2 + 4*D*(X/V)^b := by positivity
  have htotal : |firstCofactorOctave n| ≤ V * (Real.log n + 2 + 4*D*(X/V)^b) :=
    hbound.trans (mul_le_mul_of_nonneg_right hcard hB)
  -- the power part: V (X/V)^b = V^{1-b} X^b ≤ X^{1/3 + 2b/3}
  have hVpos : (0:ℝ) < V := by linarith
  have hpow : (V:ℝ) * (X/V)^b ≤ X^(1/3 + 2*b/3) := by
    rw [Real.div_rpow hX0.le hVpos.le]
    have h1 : (V:ℝ) * (X^b / (V:ℝ)^b) = (V:ℝ)^(1-b) * X^b := by
      rw [Real.rpow_sub hVpos, Real.rpow_one]; ring
    rw [h1]
    have h2 : (V:ℝ)^(1-b) ≤ X^((1-b)/3) := by
      calc (V:ℝ)^(1-b) ≤ (X^((1:ℝ)/3))^(1-b) :=
            Real.rpow_le_rpow hVpos.le hVX (by linarith)
        _ = X^((1-b)/3) := by rw [← Real.rpow_mul hX0.le]; ring_nf
    calc (V:ℝ)^(1-b) * X^b ≤ X^((1-b)/3) * X^b :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hX0.le _)
      _ = X^(1/3 + 2*b/3) := by rw [← Real.rpow_add hX0]; ring_nf
  -- the logarithmic part: V (log n + 2) ≤ 5 X^{2/3} ≤ 5 X^{1/3 + 2b/3}
  have hlog : V * (Real.log n + 2) ≤ 5 * X^(1/3 + 2*b/3) := by
    have hl : Real.log n ≤ 3 * X^((1:ℝ)/3) := by
      have h := Real.log_le_rpow_div hX0.le (show (0:ℝ) < 1/3 by norm_num)
      have hmono : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) (by rw [hXdef]; linarith)
      calc Real.log n ≤ Real.log X := hmono
        _ ≤ X^((1:ℝ)/3) / (1/3) := h
        _ = 3 * X^((1:ℝ)/3) := by ring
    have h13 : 1 ≤ X^((1:ℝ)/3) := Real.one_le_rpow hX1 (by norm_num)
    have hsq : X^((1:ℝ)/3) * X^((1:ℝ)/3) = X^((2:ℝ)/3) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h23 : X^((2:ℝ)/3) ≤ X^(1/3 + 2*b/3) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    calc V * (Real.log n + 2) ≤ X^((1:ℝ)/3) * (5 * X^((1:ℝ)/3)) :=
          mul_le_mul hVX (by linarith) (by positivity) (by positivity)
      _ = 5 * X^((2:ℝ)/3) := by rw [← hsq]; ring
      _ ≤ _ := by linarith
  have hX : X^(1/3 + 2*b/3) ≤ 4 * (n:ℝ)^(1/3 + 2*b/3) := by
    rw [hXdef, Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
    have h4 : (4:ℝ)^(1/3 + 2*b/3) ≤ 4 := by
      calc (4:ℝ)^(1/3 + 2*b/3) ≤ (4:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := Real.rpow_one 4
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsplit : V * (Real.log n + 2 + 4*D*(X/V)^b) =
      V * (Real.log n + 2) + 4*D*((V:ℝ) * (X/V)^b) := by ring
  rw [hsplit] at htotal
  have hD4 := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*D by positivity)
  have hXn := Real.rpow_nonneg (Nat.cast_nonneg n) (1/3 + 2*b/3)
  nlinarith [mul_le_mul_of_nonneg_left hX (show 0 ≤ 5 + 4*D by positivity)]

/-- The price at any abscissa bound `Θ ≤ c`: every exponent above `1/3 + 2c/3`. -/
theorem abs_firstCofactorOctave_le_of_abscissa {c e : ℝ} (hc : 1/2 ≤ c)
    (hΘ : _root_.RHTower.zetaZeroAbscissa ≤ c) (he : 1/3 + 2*c/3 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4096 ≤ n → |firstCofactorOctave n| ≤ C * (n:ℝ)^e := by
  have hR := (SquareRootThreshold.zeroReSup_le_iff_zetaZeroAbscissa_le hc).mpr hΘ
  have h := abs_firstCofactorOctave_le (b := (3*e - 1)/2) (hR.trans_lt (by linarith))
    (by linarith)
  simpa only [show (1:ℝ)/3 + 2*((3*e - 1)/2)/3 = e by ring] using h

/-- **Unconditional reference price:** every exponent `e ∈ (32999/36000, 1]`. -/
theorem abs_firstCofactorOctave_le_unconditional {e : ℝ} (he : 32999/36000 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4096 ≤ n → |firstCofactorOctave n| ≤ C * (n:ℝ)^e :=
  abs_firstCofactorOctave_le_of_abscissa (c := 20999/24000) (by norm_num)
    ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths (by linarith) he1

/-- **The `5/6` price:** under `Θ ≤ 5/6`, every exponent `e ∈ (8/9, 1]`. -/
theorem abs_firstCofactorOctave_le_of_fiveSixths
    (hΘ : _root_.RHTower.zetaZeroAbscissa ≤ 5/6) {e : ℝ} (he : 8/9 < e) (he1 : e ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4096 ≤ n → |firstCofactorOctave n| ≤ C * (n:ℝ)^e :=
  abs_firstCofactorOctave_le_of_abscissa (by norm_num) hΘ (by linarith) he1

#print axioms abs_firstCofactorOctave_le
#print axioms abs_firstCofactorOctave_le_unconditional
#print axioms abs_firstCofactorOctave_le_of_fiveSixths

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
