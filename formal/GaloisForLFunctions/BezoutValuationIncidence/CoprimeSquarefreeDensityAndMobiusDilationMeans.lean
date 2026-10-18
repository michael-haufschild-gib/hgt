import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit
import GaloisForLFunctions.RHTower.Sieve.BalancedPairsRescale
import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount

/-!
# Coprime squarefree densities and Möbius dilation means

For squarefree Q, the density of squarefree integers coprime to Q is
`(6 / pi^2) * product_{p | Q} p / (p + 1)`.
Prime deletion gives a plus recurrence for the normalized counting function.
Eliminating one scale turns it into a contracting minus recurrence, starting
from the square-root error for the unrestricted squarefree count.

Consequently, for coprime a and b, the mean of `mu(a*n) * mu(b*n)` is
`mu(a) * mu(b)` times the coprime-squarefree density for a*b. If a or b
is not squarefree, the product vanishes identically.
-/

open Finset Filter
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology ArithmeticFunction.Moebius


namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The indicator of squarefree integers coprime to Q, expressed through the Möbius square. -/
def coprimeSquarefreeIndicator (Q n : ℕ) : ℝ :=
  if Nat.Coprime Q n then ((μ n : ℤ) : ℝ) ^ 2 else 0

/-- The number of squarefree positive integers at most N that are coprime to Q. -/
def coprimeSquarefreeCount (Q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, coprimeSquarefreeIndicator Q n

/-- The coprime-squarefree count up to the natural floor of x, divided by x. -/
def coprimeSquarefreeMean (Q : ℕ) (x : ℝ) : ℝ :=
  coprimeSquarefreeCount Q ⌊x⌋₊ / x

/-- The coprime-squarefree indicator lies between zero and one. -/
theorem coprimeSquarefreeIndicator_bounds (Q n : ℕ) :
    0 ≤ coprimeSquarefreeIndicator Q n ∧ coprimeSquarefreeIndicator Q n ≤ 1 := by
  unfold coprimeSquarefreeIndicator
  split_ifs
  · have ha : |((μ n : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    refine ⟨sq_nonneg _, ?_⟩
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  · norm_num

/-- The coprime-squarefree count lies between zero and the length of the prefix. -/
theorem coprimeSquarefreeCount_bounds (Q N : ℕ) :
    0 ≤ coprimeSquarefreeCount Q N ∧ coprimeSquarefreeCount Q N ≤ (N : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun n _ => (coprimeSquarefreeIndicator_bounds Q n).1
  · calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => (coprimeSquarefreeIndicator_bounds Q n).2
      _ = _ := by simp

/-- The normalized coprime-squarefree count is bounded by one on the whole real line. -/
theorem abs_coprimeSquarefreeMean_le_one (Q : ℕ) (x : ℝ) :
    |coprimeSquarefreeMean Q x| ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [coprimeSquarefreeMean, Nat.floor_of_nonpos hx, coprimeSquarefreeCount]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [coprimeSquarefreeMean, abs_of_nonneg
      (div_nonneg (coprimeSquarefreeCount_bounds _ _).1 hx0.le)]
    exact (div_le_one hx0).mpr ((coprimeSquarefreeCount_bounds _ _).2.trans (Nat.floor_le hx0.le))

/-- Deleting a new prime partitions the indicator into a prime-free part and its dilation. -/
theorem coprimeSquarefreeIndicator_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (n : ℕ) :
    coprimeSquarefreeIndicator Q n = coprimeSquarefreeIndicator (p * Q) n +
      if p ∣ n then coprimeSquarefreeIndicator (p * Q) (n / p) else 0 := by
  have hQp : Nat.Coprime Q p := ((hp.coprime_iff_not_dvd).mpr hPQ).symm
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hQpm : Nat.Coprime Q (p * m) ↔ Nat.Coprime Q m := by
      exact ⟨fun h => (Nat.coprime_mul_iff_right.mp h).2,
        fun h => Nat.coprime_mul_iff_right.mpr ⟨hQp, h⟩⟩
    have hbad : ¬ Nat.Coprime (p * Q) (p * m) := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp h).1)
        (dvd_mul_right p m)
    have hpmul : p ∣ p * m := dvd_mul_right p m
    unfold coprimeSquarefreeIndicator
    rw [if_neg hbad, zero_add, if_pos hpmul, Nat.mul_div_cancel_left m hp.pos]
    by_cases hQm : Nat.Coprime Q m
    · rw [if_pos (hQpm.mpr hQm), moebius_sq_prime_mul hp]
      unfold coprimeSquarefreeWeight
      by_cases hpm : p ∣ m
      · have hbadm : ¬ Nat.Coprime (p * Q) m := fun h =>
          (hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp h).1) hpm
        rw [if_pos hpm, if_neg hbadm]
      · have hgoodm : Nat.Coprime (p * Q) m :=
          Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr hpm, hQm⟩
        rw [if_neg hpm, if_pos hgoodm]
    · rw [if_neg (fun h => hQm (hQpm.mp h)),
        if_neg (fun h => hQm (Nat.coprime_mul_iff_left.mp h).2)]
  · simp [coprimeSquarefreeIndicator, Nat.coprime_mul_iff_left,
      hp.coprime_iff_not_dvd, hpn]

/-- The exact prime-deletion recurrence for finite coprime-squarefree counts. -/
theorem coprimeSquarefreeCount_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (N : ℕ) :
    coprimeSquarefreeCount Q N = coprimeSquarefreeCount (p * Q) N +
      coprimeSquarefreeCount (p * Q) (N / p) := by
  classical
  unfold coprimeSquarefreeCount
  simp_rw [coprimeSquarefreeIndicator_prime_relation hp hPQ]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_Icc_div hp.pos]
  simp only [Nat.mul_div_cancel_left _ hp.pos]

/-- The normalized prime-deletion recurrence, valid also at nonpositive real cutoffs. -/
theorem coprimeSquarefreeMean_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (x : ℝ) :
    coprimeSquarefreeMean Q x = coprimeSquarefreeMean (p * Q) x +
      (1 / (p : ℝ)) * coprimeSquarefreeMean (p * Q) (x / p) := by
  unfold coprimeSquarefreeMean
  rw [Nat.floor_div_natCast, coprimeSquarefreeCount_prime_relation hp hPQ]
  by_cases hx : x = 0
  · simp [hx]
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp

private theorem tendsto_of_plus_div_contraction (p : ℝ) (hp : 1 < p)
    (f g : ℝ → ℝ) (L C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : ℝ, |f x| ≤ C) (hg : Tendsto g atTop (𝓝 L))
    (hrec : ∀ x : ℝ, g x = f x + (1 / p) * f (x / p)) :
    Tendsto f atTop (𝓝 ((p / (p + 1)) * L)) := by
  have hp0 : 0 < p := by linarith
  have hscale : Tendsto (fun x : ℝ => x / p) atTop atTop := by
    simpa only [div_eq_mul_inv, id_eq] using
      (tendsto_mul_const_atTop_of_pos (inv_pos.mpr hp0)).mpr
        (tendsto_id : Tendsto id atTop atTop)
  let g2 : ℝ → ℝ := fun x => g x - (1 / p) * g (x / p)
  have hg2 : Tendsto g2 atTop (𝓝 (L - (1 / p) * L)) :=
    hg.sub ((hg.comp hscale).const_mul (1 / p))
  have hrec2 (x : ℝ) : g2 x = f x - (1 / p ^ 2) * f (x / p ^ 2) := by
    dsimp only [g2]
    rw [hrec x, hrec (x / p)]
    have harg : x / p / p = x / p ^ 2 := by ring
    rw [harg]
    field_simp
    ring
  have h := tendsto_of_div_contraction (p ^ 2) (by nlinarith : 1 < p ^ 2)
    f g2 (L - (1 / p) * L) C hC hf hg2 hrec2
  have heq : (p ^ 2 / (p ^ 2 - 1)) * (L - (1 / p) * L) = (p / (p + 1)) * L := by
    have hpm : p ^ 2 - 1 ≠ 0 := by nlinarith
    have hpp : p + 1 ≠ 0 := by linarith
    field_simp
    ring
  rwa [heq] at h

/-- Deleting a new prime multiplies an existing coprime-squarefree density by p/(p+1). -/
theorem tendsto_coprimeSquarefreeMean_prime_step {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) {L : ℝ}
    (hlim : Tendsto (coprimeSquarefreeMean Q) atTop (𝓝 L)) :
    Tendsto (coprimeSquarefreeMean (p * Q)) atTop
      (𝓝 (((p : ℝ) / ((p : ℝ) + 1)) * L)) := by
  apply tendsto_of_plus_div_contraction (p : ℝ) (by exact_mod_cast hp.one_lt)
    (coprimeSquarefreeMean (p * Q)) (coprimeSquarefreeMean Q) L 1 (by norm_num)
  · exact abs_coprimeSquarefreeMean_le_one (p * Q)
  · exact hlim
  · exact coprimeSquarefreeMean_prime_relation hp hPQ


/-- The unrestricted squarefree density follows from the square-root counting error. -/
theorem tendsto_coprimeSquarefreeMean_one :
    Tendsto (coprimeSquarefreeMean 1) atTop (𝓝 squarefreeDensity) := by
  have hD : 0 ≤ squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hmaj : Tendsto (fun x : ℝ => 2 / Real.sqrt x + (1 + squarefreeDensity) / x)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 2 / Real.sqrt x) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul (2 : ℝ)
    have h2 : Tendsto (fun x : ℝ => (1 + squarefreeDensity) / x) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1 + squarefreeDensity)
    simpa only [zero_add] using h1.add h2
  have hkey : Tendsto (fun x : ℝ => |coprimeSquarefreeMean 1 x - squarefreeDensity|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hmaj
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hf1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hs := abs_sum_moebius_sq_Icc_sub_le ⌊x⌋₊
    have hcount : coprimeSquarefreeCount 1 ⌊x⌋₊ =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((μ n : ℤ) : ℝ) ^ 2 := by
      simp [coprimeSquarefreeCount, coprimeSquarefreeIndicator]
    rw [← hcount] at hs
    have hroot : Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hf
    have hfloor : |(⌊x⌋₊ : ℝ) * squarefreeDensity - x * squarefreeDensity| ≤
        squarefreeDensity := by
      rw [abs_le]
      constructor <;> nlinarith
    have htri := abs_sub_le (coprimeSquarefreeCount 1 ⌊x⌋₊)
      ((⌊x⌋₊ : ℝ) * squarefreeDensity) (x * squarefreeDensity)
    have hb : |coprimeSquarefreeCount 1 ⌊x⌋₊ - x * squarefreeDensity| ≤
        2 * Real.sqrt x + 1 + squarefreeDensity := by linarith
    have hid : Real.sqrt x / x = 1 / Real.sqrt x := by
      rw [div_eq_div_iff hx0.ne' hs0.ne', Real.mul_self_sqrt hx0.le]
      ring
    rw [coprimeSquarefreeMean,
      show coprimeSquarefreeCount 1 ⌊x⌋₊ / x - squarefreeDensity =
        (coprimeSquarefreeCount 1 ⌊x⌋₊ - x * squarefreeDensity) / x by field_simp,
      abs_div, abs_of_pos hx0]
    calc
      _ ≤ (2 * Real.sqrt x + 1 + squarefreeDensity) / x :=
        div_le_div_of_nonneg_right hb hx0.le
      _ = 2 * (Real.sqrt x / x) + (1 + squarefreeDensity) / x := by ring
      _ = _ := by rw [hid]; ring
  have hlim := (tendsto_const_nhds (x := squarefreeDensity) (f := atTop (α := ℝ))).add
    (tendsto_zero_iff_abs_tendsto_zero _ |>.2 hkey)
  simpa using hlim

/-- The squarefree density multiplied by the local coprimality factors for Q. -/
def coprimeSquarefreeDensity (Q : ℕ) : ℝ :=
  squarefreeDensity * ∏ p ∈ Q.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- The modulus-one coprimality factor is empty. -/
theorem coprimeSquarefreeDensity_one : coprimeSquarefreeDensity 1 = squarefreeDensity := by
  simp [coprimeSquarefreeDensity]

/-- A new prime contributes exactly its local factor p/(p+1). -/
theorem coprimeSquarefreeDensity_prime_mul {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (hQ : Q ≠ 0) :
    coprimeSquarefreeDensity (p * Q) =
      ((p : ℝ) / ((p : ℝ) + 1)) * coprimeSquarefreeDensity Q := by
  classical
  have hnot : p ∉ Q.primeFactors := fun h => hPQ (Nat.mem_primeFactors.mp h).2.1
  have hset : (p * Q).primeFactors = insert p Q.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hQ, hp.primeFactors]
    simp
  unfold coprimeSquarefreeDensity
  rw [hset, Finset.prod_insert hnot]
  ring

/-- Every fixed squarefree modulus has the stated finite Euler-product density. -/
theorem tendsto_coprimeSquarefreeMean_of_squarefree : ∀ Q : ℕ, Squarefree Q →
    Tendsto (coprimeSquarefreeMean Q) atTop (𝓝 (coprimeSquarefreeDensity Q)) := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | _ Q ih =>
    intro hQ
    rcases eq_or_ne Q 1 with rfl | hne
    · rw [coprimeSquarefreeDensity_one]
      exact tendsto_coprimeSquarefreeMean_one
    · have hQ0 : Q ≠ 0 := hQ.ne_zero
      let p := Q.minFac
      let R := Q / p
      have hp : p.Prime := Nat.minFac_prime hne
      have hpd : p ∣ Q := Nat.minFac_dvd Q
      have hmul : p * R = Q := Nat.mul_div_cancel' hpd
      have hpR : ¬ p ∣ R := by
        intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have hsq : p * p ∣ Q := by
          refine ⟨k, ?_⟩
          calc
            Q = p * R := hmul.symm
            _ = p * (p * k) := by rw [hk]
            _ = p * p * k := by ring
        have hunit := hQ _ hsq
        rw [Nat.isUnit_iff] at hunit
        exact hp.ne_one hunit
      have hRSf : Squarefree R := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd) hQ
      have hRlt : R < Q := Nat.div_lt_self (Nat.pos_of_ne_zero hQ0) hp.one_lt
      have hR0 : R ≠ 0 := hRSf.ne_zero
      have hstep := tendsto_coprimeSquarefreeMean_prime_step hp hpR (ih R hRlt hRSf)
      rw [← coprimeSquarefreeDensity_prime_mul hp hpR hR0, hmul] at hstep
      exact hstep

/-- A pair of Möbius dilations factors through one coprime-squarefree indicator. -/
theorem moebius_dilation_pair_eq_coprimeSquarefreeIndicator (a b n : ℕ) :
    ((μ (a * n) : ℤ) : ℝ) * ((μ (b * n) : ℤ) : ℝ) =
      ((μ a : ℤ) : ℝ) * ((μ b : ℤ) : ℝ) * coprimeSquarefreeIndicator (a * b) n := by
  by_cases hc : Nat.Coprime (a * b) n
  · obtain ⟨ha, hb⟩ := Nat.coprime_mul_iff_left.mp hc
    rw [coprimeSquarefreeIndicator, if_pos hc,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime ha,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hb]
    push_cast
    ring
  · by_cases ha : Nat.Coprime a n
    · have hb : ¬ Nat.Coprime b n := fun hb => hc (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩)
      have hz : μ (b * n) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h => hb (Nat.coprime_of_squarefree_mul h)
      simp [hz, coprimeSquarefreeIndicator, hc]
    · have hz : μ (a * n) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h => ha (Nat.coprime_of_squarefree_mul h)
      simp [hz, coprimeSquarefreeIndicator, hc]

/-- The arithmetic mean of two coprime Möbius dilations has an explicit Euler-product limit. -/
theorem tendsto_moebius_coprime_dilation_pair_mean {a b : ℕ} (hab : Nat.Coprime a b) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((μ (a * n) : ℤ) : ℝ) * ((μ (b * n) : ℤ) : ℝ)) / x)
      atTop (𝓝 (((μ a : ℤ) : ℝ) * ((μ b : ℤ) : ℝ) * coprimeSquarefreeDensity (a * b))) := by
  have heq (x : ℝ) :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((μ (a * n) : ℤ) : ℝ) * ((μ (b * n) : ℤ) : ℝ)) / x =
        (((μ a : ℤ) : ℝ) * ((μ b : ℤ) : ℝ)) * coprimeSquarefreeMean (a * b) x := by
    simp_rw [moebius_dilation_pair_eq_coprimeSquarefreeIndicator]
    rw [← Finset.mul_sum]
    unfold coprimeSquarefreeMean coprimeSquarefreeCount
    ring
  simp_rw [heq]
  by_cases hsf : Squarefree (a * b)
  · exact (tendsto_coprimeSquarefreeMean_of_squarefree (a * b) hsf).const_mul _
  · have hzero : ((μ a : ℤ) : ℝ) * ((μ b : ℤ) : ℝ) = 0 := by
      by_cases ha : Squarefree a
      · have hb : ¬ Squarefree b := fun hb => hsf ((Nat.squarefree_mul hab).mpr ⟨ha, hb⟩)
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]
      · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree ha]
    simp only [hzero, zero_mul]
    exact tendsto_const_nhds

end
end GaloisForLFunctions.BezoutValuationIncidence
