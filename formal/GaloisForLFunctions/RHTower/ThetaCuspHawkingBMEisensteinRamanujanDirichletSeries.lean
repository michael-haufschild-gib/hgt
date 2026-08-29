import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCauchyPowerFourierBessel
import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier
import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier
import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatCyclicHaarPacket
import GaloisForLFunctions.RHTower.CCMRationalZModUnitInvariantMobius
import GaloisForLFunctions.RHTower.CCMRationalUnitInvariantMobiusPoissonCompression
import GaloisForLFunctions.RHTower.DeningerMobiusSuccessorAmplitude
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence
import GaloisForLFunctions.HTGeometry.RationalPadicResidue

/-!
# Exact Ramanujan divisor law and Dirichlet series for the BM Eisenstein coefficient

Corpus search isolated the missing arithmetic weld after exact Poincare unfolding and the
Gamma--Bessel evaluation: the literal CGL reduced-residue sum had no composite-modulus divisor
formula, and its denominator Dirichlet series had no exact zeta quotient.

This module proves both without prime-power casework. Möbius inversion expands the unit indicator;
an explicit equivalence identifies residues divisible by an arbitrary divisor with the quotient
cyclic group; finite-character orthogonality evaluates that subgroup exactly. The result is

`c_q(n) = sum_{d | gcd(n,q)} d * mu(q/d)`.

The coefficient stream is then the Dirichlet convolution of a finite divisor seed with Möbius.
Absolute L-series multiplication gives

`sum_{q >= 1} c_q(n) q^(-w) = (sum_{d | n} d^(1-w)) / zeta(w)`

for `Re(w)>1`, and a packaged specialization supplies `w=2s` for the actual BM Eisenstein
convergence parameter.

Full RH contribution chain:

`Ramanujan divisor law -> exact denominator Dirichlet series -> Poincare/Fourier coefficient
assembly -> Fourier uniqueness -> truncated modular Green/Stokes defects -> balanced BM
coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 clock defect -> RH`.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HB] [FZZ-P] [RBH] [PW-B]`
-/

open Complex Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower
noncomputable section

def d4BMMultiplesFinEquiv {N d : ℕ} [NeZero N] (hN : 0 < N) (hd : d ∈ N.divisors) :
    Fin (N / d) ≃ {a : ZMod N // d ∣ a.val} := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  refine
    { toFun := fun b => ⟨((d * b.val : ℕ) : ZMod N), ?_⟩
      invFun := fun a => ⟨a.1.val / d, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hlt : d * b.val < N := by
      calc
        d * b.val < d * (N / d) := (Nat.mul_lt_mul_left hdpos).2 b.isLt
        _ = N := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt]
    exact dvd_mul_right d b.val
  · apply (Nat.div_lt_iff_lt_mul hdpos).2
    rw [Nat.div_mul_cancel hdvd]
    exact ZMod.val_lt a.1
  · intro b
    apply Fin.ext
    simp only
    have hlt : d * b.val < N := by
      calc
        d * b.val < d * (N / d) := (Nat.mul_lt_mul_left hdpos).2 b.isLt
        _ = N := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt, mul_comm d b.val, Nat.mul_div_left _ hdpos]
  · intro a
    apply Subtype.ext
    have hmul : d * (a.1.val / d) = a.1.val := Nat.mul_div_cancel' a.property
    change ((d * (a.1.val / d) : ℕ) : ZMod N) = a.1
    rw [hmul]
    exact ZMod.natCast_zmod_val a.1

@[simp] lemma d4BMMultiplesFinEquiv_apply
    {N d : ℕ} [NeZero N] (hN : 0 < N) (hd : d ∈ N.divisors)
    (b : Fin (N / d)) :
    (d4BMMultiplesFinEquiv hN hd b).1 = ((d * b.val : ℕ) : ZMod N) := rfl

lemma d4BM_stdAddChar_divisorMultiple
    {N d : ℕ} [NeZero N] [NeZero (N / d)] (hN : 0 < N) (hd : d ∈ N.divisors)
    (m : ZMod N) (b : Fin (N / d)) :
    ZMod.stdAddChar (((d * b.val : ℕ) : ZMod N) * m) =
      ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d))) := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  have hleft :
      ((d * b.val : ℕ) : ZMod N) * m =
        ((d * b.val * m.val : ℕ) : ZMod N) := by
    calc
      ((d * b.val : ℕ) : ZMod N) * m =
          ((d * b.val : ℕ) : ZMod N) * (m.val : ZMod N) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((d * b.val * m.val : ℕ) : ZMod N) := by
        push_cast
        ring
  have hright :
      ((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d)) =
        ((b.val * m.val : ℕ) : ZMod (N / d)) := by
    push_cast
    ring
  rw [hleft, hright]
  change ZMod.stdAddChar ((d * b.val * m.val : ℕ) : ZMod N) =
    ZMod.stdAddChar ((b.val * m.val : ℕ) : ZMod (N / d))
  rw [show ((d * b.val * m.val : ℕ) : ZMod N) =
      ((d * b.val * m.val : ℤ) : ZMod N) by norm_num,
    show ((b.val * m.val : ℕ) : ZMod (N / d)) =
      ((b.val * m.val : ℤ) : ZMod (N / d)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  have hqC : ((N / d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hquotpos.ne'
  have hNC : (N : ℂ) = (d : ℂ) * (N / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  rw [hNC]
  field_simp

theorem d4BM_sum_stdAddChar_divisible
    {N d : ℕ} [NeZero N] (hN : 0 < N) (hd : d ∈ N.divisors) (m : ZMod N) :
    (∑ a : ZMod N, if d ∣ a.val then ZMod.stdAddChar (a * m) else 0) =
      if (N / d) ∣ m.val then ((N / d : ℕ) : ℂ) else 0 := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  letI : NeZero (N / d) := ⟨hquotpos.ne'⟩
  rw [← Finset.sum_filter]
  have hsub :
      (∑ a ∈ (Finset.univ : Finset (ZMod N)).filter (fun a => d ∣ a.val),
          ZMod.stdAddChar (a * m)) =
        ∑ a : {a : ZMod N // d ∣ a.val}, ZMod.stdAddChar (a.1 * m) := by
    exact Finset.sum_subtype _ (by simp) _
  rw [hsub]
  rw [← (d4BMMultiplesFinEquiv hN hd).sum_comp]
  simp_rw [d4BMMultiplesFinEquiv_apply]
  rw [show (∑ b : Fin (N / d),
      ZMod.stdAddChar ((((d * b.val : ℕ) : ZMod N)) * m)) =
      ∑ b : Fin (N / d),
        ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d))) by
    apply Finset.sum_congr rfl
    intro b hb
    exact d4BM_stdAddChar_divisorMultiple hN hd m b]
  rw [show (∑ b : Fin (N / d),
      ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d)))) =
      ∑ b : Fin (N / d),
        ZMod.stdAddChar ((ZMod.finEquiv (N / d) b) * (m.val : ZMod (N / d))) by
    apply Finset.sum_congr rfl
    intro b hb
    rw [show ZMod.finEquiv (N / d) b = (b.val : ZMod (N / d)) by
      apply ZMod.val_injective
      rw [GaloisForLFunctions.RHTower.ccmRationalZMod_finEquiv_val,
        ZMod.val_natCast_of_lt b.isLt]]]
  change (∑ b : Fin (N / d),
      (fun x : ZMod (N / d) => ZMod.stdAddChar (x * (m.val : ZMod (N / d))))
        ((ZMod.finEquiv (N / d)).toEquiv b)) = _
  calc
    _ = ∑ x : ZMod (N / d),
        ZMod.stdAddChar (x * (m.val : ZMod (N / d))) :=
      Equiv.sum_comp (ZMod.finEquiv (N / d)).toEquiv
        (fun x : ZMod (N / d) => ZMod.stdAddChar (x * (m.val : ZMod (N / d))))
    _ = _ := by
      rw [RHTower.Sieve.sum_stdAddChar_mul]
      have hz : ((m.val : ZMod (N / d)) = 0) ↔ (N / d) ∣ m.val :=
        GaloisForLFunctions.HTGeometry.natCast_zmod_eq_zero_iff
      by_cases hx : (m.val : ZMod (N / d)) = 0
      · rw [if_pos hx, if_pos (hz.mp hx)]
      · rw [if_neg hx, if_neg (fun hm => hx (hz.mpr hm))]
        norm_num

lemma cglUnitResidueIndicator_eq_mobiusCommonDivisorKernel
    (Q : CGLPositiveModulus) (a : ZMod Q.value) :
    cglUnitResidueIndicator Q a =
      ((mobiusCommonDivisorKernel a.val Q.value : ℤ) : ℂ) := by
  rw [mobiusCommonDivisorKernel_eq_coprimeIndicator]
  have hu : IsUnit a ↔ a.val.Coprime Q.value := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime a.val Q.value)
  unfold cglUnitResidueIndicator
  by_cases hcop : a.val.Coprime Q.value <;> simp [hcop, hu]

theorem cglRamanujanAdditiveSum_eq_mobiusDivisorFilter
    (Q : CGLPositiveModulus) (m : ZMod Q.value) :
    cglRamanujanAdditiveSum Q m =
      ∑ e ∈ Q.value.divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0) := by
  classical
  rw [cglRamanujanAdditiveSum_eq_indicator]
  unfold cglRamanujanAdditiveSumIndicator
  simp_rw [cglUnitResidueIndicator_eq_mobiusCommonDivisorKernel]
  unfold mobiusCommonDivisorKernel
  have hdivset (a : ZMod Q.value) :
      (a.val.gcd Q.value).divisors =
        Q.value.divisors.filter (fun e => e ∣ a.val) := by
    ext e
    have hg := GaloisForLFunctions.RHTower.ccmRational_mem_gcd_divisors_iff
      (d := e) Q.positive.ne' a
    rw [hg]
    simp [Nat.mem_divisors, Q.positive.ne', and_comm]
  simp_rw [hdivset, Int.cast_sum, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hfactor :
      (∑ a : ZMod Q.value,
          if e ∣ a.val then
            ZMod.stdAddChar (a * m) * ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          else 0) =
        (∑ a : ZMod Q.value,
          if e ∣ a.val then ZMod.stdAddChar (a * m) else 0) *
            ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hea : e ∣ a.val <;> simp [hea]
  rw [hfactor, d4BM_sum_stdAddChar_divisible Q.positive he m]
  by_cases hem : Q.value / e ∣ m.val <;> simp [hem]
  ring

theorem cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum
    (Q : CGLPositiveModulus) (m : ZMod Q.value) :
    cglRamanujanAdditiveSum Q m =
      ∑ d ∈ (m.val.gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) := by
  classical
  rw [cglRamanujanAdditiveSum_eq_mobiusDivisorFilter]
  have hdivset :
      (m.val.gcd Q.value).divisors =
        Q.value.divisors.filter (fun d => d ∣ m.val) := by
    ext d
    have hg := GaloisForLFunctions.RHTower.ccmRational_mem_gcd_divisors_iff
      (d := d) Q.positive.ne' m
    rw [hg]
    simp [Nat.mem_divisors, Q.positive.ne', and_comm]
  calc
    (∑ e ∈ Q.value.divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0)) =
        ∑ d ∈ Q.value.divisors,
          if d ∣ m.val then
            ((d : ℕ) : ℂ) *
              ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ)
          else 0 := by
      rw [← Nat.sum_div_divisors Q.value (fun e =>
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0))]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ Q.value := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hquotpos : 0 < Q.value / d :=
        Nat.div_pos (Nat.le_of_dvd Q.positive hdvd) hdpos
      have hquotquot : Q.value / (Q.value / d) = d :=
        Nat.div_eq_of_eq_mul_left hquotpos (Nat.mul_div_cancel' hdvd).symm
      rw [hquotquot]
      by_cases hdm : d ∣ m.val <;> simp [hdm]
      ring
    _ = ∑ d ∈ (m.val.gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) := by
      rw [hdivset, Finset.sum_filter]

theorem cglRamanujanAdditiveSum_natCast_eq_gcd_mobiusDivisorSum
    (Q : CGLPositiveModulus) (n : ℕ) :
    cglRamanujanAdditiveSum Q (n : ZMod Q.value) =
      ∑ d ∈ (n.gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) := by
  rw [cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum]
  have hfin :
      (((n : ZMod Q.value).val.gcd Q.value).divisors) =
        (n.gcd Q.value).divisors := by
    ext d
    rw [GaloisForLFunctions.RHTower.ccmRational_mem_gcd_divisors_iff
      (d := d) Q.positive.ne' (n : ZMod Q.value)]
    have hright :
        d ∈ (n.gcd Q.value).divisors ↔ d ∣ n ∧ d ∣ Q.value := by
      rw [Nat.mem_divisors]
      simp [Nat.dvd_gcd_iff, Nat.gcd_ne_zero_right Q.positive.ne']
    rw [hright]
    constructor
    · rintro ⟨hdres, hdQ⟩
      exact ⟨(GaloisForLFunctions.RHTower.ccmRational_dvd_zmodVal_natCast_iff
        hdQ).mp hdres, hdQ⟩
    · rintro ⟨hdn, hdQ⟩
      exact ⟨(GaloisForLFunctions.RHTower.ccmRational_dvd_zmodVal_natCast_iff
        hdQ).mpr hdn, hdQ⟩
  rw [hfin]

def d4BMRamanujanDivisorSeed (n : ℕ) : ArithmeticFunction ℂ where
  toFun d := if d = 0 then 0 else if d ∣ n then (d : ℂ) else 0
  map_zero' := by simp

def d4BMMoebiusArithmeticC : ArithmeticFunction ℂ :=
  ⟨moebiusCoeffC, moebiusCoeff_zero⟩

def d4BMRamanujanNaturalCoefficient (n q : ℕ) : ℂ :=
  if hq : 0 < q then
    cglRamanujanAdditiveSum ⟨q, hq⟩ (n : ZMod q)
  else 0

def d4BMRamanujanDivisorPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) * (d : ℂ) ^ (-w)

/-- A nonzero positive Fourier frequency, carried as data rather than as a theorem premise. -/
structure D4BMPositiveFourierFrequency where
  value : ℕ
  positive : 0 < value

def d4BMRamanujanPNatTerm
    (F : D4BMPositiveFourierFrequency)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) : ℂ :=
  d4BMRamanujanNaturalCoefficient F.value q *
    ((q : ℕ) : ℂ) ^ (-(2 * P.s))

theorem d4BMRamanujanNaturalCoefficient_eq_convolution
    {n : ℕ} (hn : 0 < n) (q : ℕ) :
    d4BMRamanujanNaturalCoefficient n q =
      (d4BMRamanujanDivisorSeed n * d4BMMoebiusArithmeticC) q := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [d4BMRamanujanNaturalCoefficient]
  · rw [d4BMRamanujanNaturalCoefficient, dif_pos hq,
      cglRamanujanAdditiveSum_natCast_eq_gcd_mobiusDivisorSum]
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
      (fun a b => d4BMRamanujanDivisorSeed n a * d4BMMoebiusArithmeticC b)]
    have hfin :
        (n.gcd q).divisors = q.divisors.filter (fun d => d ∣ n) := by
      ext d
      simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hn.ne', hq.ne', and_comm]
    rw [hfin, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    by_cases hdn : d ∣ n
    · simp [hdn, d4BMRamanujanDivisorSeed, d4BMMoebiusArithmeticC,
        moebiusCoeffC, hdpos.ne']
    · simp [hdn, d4BMRamanujanDivisorSeed]

theorem d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum
    {n q : ℕ} (hq : 0 < q) :
    d4BMRamanujanNaturalCoefficient n q =
      ∑ d ∈ (n.gcd q).divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
  rw [d4BMRamanujanNaturalCoefficient, dif_pos hq,
    cglRamanujanAdditiveSum_natCast_eq_gcd_mobiusDivisorSum]

theorem d4BMRamanujanDivisorSeed_LSeriesSummable
    {n : ℕ} (hn : 0 < n) (w : ℂ) :
    LSeriesSummable (d4BMRamanujanDivisorSeed n) w := by
  unfold LSeriesSummable
  apply summable_of_ne_finset_zero (s := n.divisors)
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [LSeries.term_zero]
  · have hndvd : ¬d ∣ n := by
      intro hdn
      exact hd (Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩)
    rw [LSeries.term_of_ne_zero hdpos.ne']
    simp [d4BMRamanujanDivisorSeed, hdpos.ne', hndvd]

theorem LSeries_d4BMRamanujanDivisorSeed_eq_polynomial
    {n : ℕ} (hn : 0 < n) (w : ℂ) :
    LSeries (d4BMRamanujanDivisorSeed n) w =
      d4BMRamanujanDivisorPolynomial n w := by
  unfold LSeries d4BMRamanujanDivisorPolynomial
  rw [tsum_eq_sum (s := n.divisors)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    rw [LSeries.term_of_ne_zero hdpos.ne']
    change (if d = 0 then 0 else if d ∣ n then (d : ℂ) else 0) /
        (d : ℂ) ^ w = (d : ℂ) * (d : ℂ) ^ (-w)
    rw [if_neg hdpos.ne', if_pos hdn]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
  · intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simp [LSeries.term_zero]
    · have hndvd : ¬d ∣ n := by
        intro hdn
        exact hd (Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩)
      rw [LSeries.term_of_ne_zero hdpos.ne']
      simp [d4BMRamanujanDivisorSeed, hdpos.ne', hndvd]

theorem d4BMMoebiusArithmeticC_LSeriesSummable
    {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable d4BMMoebiusArithmeticC w := by
  change LSeriesSummable moebiusCoeffC w
  change LSeriesSummable
    (fun q => ((ArithmeticFunction.moebius q : ℤ) : ℂ)) w
  exact lSeriesSummable_moebius_of_one_lt_re hw

theorem LSeries_d4BMRamanujanNaturalCoefficient_eq_mul
    {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : 1 < w.re) :
    LSeries (d4BMRamanujanNaturalCoefficient n) w =
      d4BMRamanujanDivisorPolynomial n w *
        LSeries d4BMMoebiusArithmeticC w := by
  have hseed := (d4BMRamanujanDivisorSeed_LSeriesSummable hn w).LSeriesHasSum
  rw [LSeries_d4BMRamanujanDivisorSeed_eq_polynomial hn w] at hseed
  have hmob := (d4BMMoebiusArithmeticC_LSeriesSummable hw).LSeriesHasSum
  have hmul := ArithmeticFunction.LSeriesHasSum_mul hseed hmob
  have hfun :
      d4BMRamanujanNaturalCoefficient n =
        fun q => (d4BMRamanujanDivisorSeed n * d4BMMoebiusArithmeticC) q := by
    funext q
    exact d4BMRamanujanNaturalCoefficient_eq_convolution hn q
  rw [hfun]
  exact hmul.LSeries_eq

theorem LSeries_d4BMRamanujanNaturalCoefficient_eq_div_riemannZeta
    {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : 1 < w.re) :
    LSeries (d4BMRamanujanNaturalCoefficient n) w =
      d4BMRamanujanDivisorPolynomial n w / riemannZeta w := by
  rw [LSeries_d4BMRamanujanNaturalCoefficient_eq_mul hn hw]
  have hinv := LSeries_moebiusCoeff_mul_riemannZeta hw
  have hzeta : riemannZeta w ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hinv
    exact zero_ne_one hinv
  have hM : LSeries d4BMMoebiusArithmeticC w = (riemannZeta w)⁻¹ := by
    have hseq : d4BMMoebiusArithmeticC = moebiusCoeffC := by
      funext q
      rfl
    rw [hseq]
    rw [show (riemannZeta w)⁻¹ = 1 / riemannZeta w by rw [one_div]]
    exact (eq_div_iff hzeta).2 hinv
  rw [hM, div_eq_mul_inv]

theorem tsum_d4BMRamanujanPNatTerm_eq_div_riemannZeta
    (F : D4BMPositiveFourierFrequency)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∑' q : ℕ+, d4BMRamanujanPNatTerm F P q) =
      d4BMRamanujanDivisorPolynomial F.value (2 * P.s) /
        riemannZeta (2 * P.s) := by
  have hw : 1 < (2 * P.s).re := by
    norm_num [Complex.mul_re]
    linarith [P.re_gt_one]
  rw [← LSeries_d4BMRamanujanNaturalCoefficient_eq_div_riemannZeta
    F.positive hw]
  unfold LSeries
  calc
    (∑' q : ℕ+, d4BMRamanujanPNatTerm F P q) =
        ∑' q : ℕ+,
          LSeries.term (d4BMRamanujanNaturalCoefficient F.value) (2 * P.s) q := by
      apply tsum_congr
      intro q
      rw [LSeries.term_of_ne_zero q.ne_zero]
      unfold d4BMRamanujanPNatTerm
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
    _ = ∑' q : ℕ,
        {q : ℕ | 0 < q}.indicator
          (LSeries.term (d4BMRamanujanNaturalCoefficient F.value) (2 * P.s)) q :=
      tsum_subtype {q : ℕ | 0 < q}
        (LSeries.term (d4BMRamanujanNaturalCoefficient F.value) (2 * P.s))
    _ = ∑' q : ℕ,
        LSeries.term (d4BMRamanujanNaturalCoefficient F.value) (2 * P.s) q := by
      apply tsum_congr
      intro q
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, lt_self_iff_false,
          if_false, LSeries.term_zero]
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hq]

end
end RHTower
