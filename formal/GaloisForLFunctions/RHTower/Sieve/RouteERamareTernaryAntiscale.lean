import GaloisForLFunctions.RHTower.RouteECriticalAntiscaleDissipationSaturation
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor
import GaloisForLFunctions.RHTower.Sieve.RamareSquareMultiple
import GaloisForLFunctions.RHTower.Sieve.MultiplicativeEulerBound

/-!
# Route E Ramaré ternary antiscale law

This module closes the exact finite ternary marker analysis exposed by Ramaré recombination.
For a finite prime packet `Q`, histories `Q → Fin 3` encode absence, left assignment, or right
assignment. Their logarithmic frequencies are injective by rational independence of prime logs and
are quantitatively separated by the sharp elementary scale `R_Q⁻²`, where `R_Q = ∏ p ∈ Q, p`.

The unweighted alternating reporter is proved equal to its full `3^|Q|` history expansion, retains
every finite Möbius sign, has exact coefficient energy `3^|Q|`, and satisfies the finite-height
mean-square bound

`∫[-W,W] |T_Q(t)|² ≤ (2W + 4R_Q²(1 + |Q| log 3)) 3^|Q|`.

Its local norm is at most three, with equality exactly at the antiscale phase. Prime-log recurrence
therefore gives arbitrarily late values approaching the exact global supremum `3^|Q|`.

The reciprocal Gibbs reporter keeps local weights `1, 1/p, 1/p`. Its coefficient energy is exactly

`V_Q = ∏ p ∈ Q, (1 + 2/p²)/(1 + 2/p)²`,

and the same separated-frequency theorem gives the weighted mean-square bound with factor `V_Q`.
The local norm is at most one, equality occurs exactly at antiscale, and modulus-one escape recurs
cofinally. Nevertheless

`V_Q ≤ exp (2 ∑ p⁻² - 2 ∑ p⁻¹)`,

and `V_Q → 0` unconditionally along canonical prime packets. Thus pointwise antiscale coherence is
the exact escape mode while finite-height Gibbs energy dissipates.

No computation, route premise, additional axiom, or asymptotic placeholder is used.
-/

namespace RHTower.Sieve

open scoped ArithmeticFunction.Moebius

noncomputable section

abbrev RouteETernaryHistory (Q : Finset Nat.Primes) := Q → Fin 3

def routeETernaryCharge (s : Fin 3) : ℚ :=
  if s = 0 then 0 else if s = 1 then 1 else -1

@[simp] theorem routeETernaryCharge_zero : routeETernaryCharge 0 = 0 := by
  simp [routeETernaryCharge]

@[simp] theorem routeETernaryCharge_one : routeETernaryCharge 1 = 1 := by
  simp [routeETernaryCharge]

@[simp] theorem routeETernaryCharge_two : routeETernaryCharge 2 = -1 := by
  simp [routeETernaryCharge]

theorem routeETernaryCharge_injective : Function.Injective routeETernaryCharge := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals norm_num [routeETernaryCharge] at hab

def routeETernaryHistoryFrequency {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : ℝ :=
  ∑ p : Q, (routeETernaryCharge (h p) : ℝ) * Real.log ((p : Nat.Primes) : ℕ)

theorem routeETernaryHistoryFrequency_injective (Q : Finset Nat.Primes) :
    Function.Injective (routeETernaryHistoryFrequency (Q := Q)) := by
  intro h k hhk
  have hli : LinearIndependent ℚ
      (fun p : Q => Real.log ((p : Nat.Primes) : ℕ)) :=
    GaloisForLFunctions.linearIndependent_log_primes.comp
      (fun p : Q => (p : Nat.Primes)) Subtype.val_injective
  have hzero : ∑ p : Q,
      (routeETernaryCharge (h p) - routeETernaryCharge (k p)) •
        Real.log ((p : Nat.Primes) : ℕ) = 0 := by
    calc
      ∑ p : Q, (routeETernaryCharge (h p) - routeETernaryCharge (k p)) •
          Real.log ((p : Nat.Primes) : ℕ) =
          routeETernaryHistoryFrequency h - routeETernaryHistoryFrequency k := by
            rw [routeETernaryHistoryFrequency, routeETernaryHistoryFrequency,
              ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            rw [Rat.smul_def]
            push_cast
            ring
      _ = 0 := sub_eq_zero.mpr hhk
  funext p
  apply routeETernaryCharge_injective
  exact sub_eq_zero.mp
    (Fintype.linearIndependent_iff.mp hli
      (fun q : Q => routeETernaryCharge (h q) - routeETernaryCharge (k q)) hzero p)

def routeETernaryPrimorial (Q : Finset Nat.Primes) : ℕ :=
  ∏ p : Q, ((p : Nat.Primes) : ℕ)

def routeETernaryLeftProduct {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : ℕ :=
  ∏ p : Q, if h p = 1 then ((p : Nat.Primes) : ℕ) else 1

def routeETernaryRightProduct {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : ℕ :=
  ∏ p : Q, if h p = 2 then ((p : Nat.Primes) : ℕ) else 1

theorem routeETernaryPrimorial_pos (Q : Finset Nat.Primes) :
    0 < routeETernaryPrimorial Q := by
  rw [routeETernaryPrimorial]
  exact Finset.prod_pos fun p _ => p.1.2.pos

theorem routeETernaryLeftProduct_pos {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : 0 < routeETernaryLeftProduct h := by
  rw [routeETernaryLeftProduct]
  exact Finset.prod_pos fun p _ => by
    by_cases hs : h p = 1
    · simpa [hs] using p.1.2.pos
    · simp [hs]

theorem routeETernaryRightProduct_pos {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : 0 < routeETernaryRightProduct h := by
  rw [routeETernaryRightProduct]
  exact Finset.prod_pos fun p _ => by
    by_cases hs : h p = 2
    · simpa [hs] using p.1.2.pos
    · simp [hs]

theorem routeETernaryLeftProduct_le_primorial {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) :
    routeETernaryLeftProduct h ≤ routeETernaryPrimorial Q := by
  rw [routeETernaryLeftProduct, routeETernaryPrimorial]
  apply Finset.prod_le_prod
  · intro p hp
    by_cases hs : h p = 1
    · simp [hs]
    · simp [hs]
  · intro p hp
    by_cases hs : h p = 1
    · simp [hs]
    · simpa [hs] using p.1.2.one_lt.le

theorem routeETernaryRightProduct_le_primorial {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) :
    routeETernaryRightProduct h ≤ routeETernaryPrimorial Q := by
  rw [routeETernaryRightProduct, routeETernaryPrimorial]
  apply Finset.prod_le_prod
  · intro p hp
    by_cases hs : h p = 2
    · simp [hs]
    · simp [hs]
  · intro p hp
    by_cases hs : h p = 2
    · simp [hs]
    · simpa [hs] using p.1.2.one_lt.le

private theorem routeETernaryCharge_log_eq
    (s : Fin 3) (p : Nat.Primes) :
    (routeETernaryCharge s : ℝ) * Real.log (p : ℕ) =
      Real.log ((if s = 1 then (p : ℕ) else 1 : ℕ) : ℝ) -
        Real.log ((if s = 2 then (p : ℕ) else 1 : ℕ) : ℝ) := by
  fin_cases s <;> simp [routeETernaryCharge]

theorem routeETernaryHistoryFrequency_eq_log_products
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    routeETernaryHistoryFrequency h =
      Real.log (routeETernaryLeftProduct h : ℝ) -
        Real.log (routeETernaryRightProduct h : ℝ) := by
  have hleft : Real.log (routeETernaryLeftProduct h : ℝ) =
      ∑ p : Q, Real.log ((if h p = 1 then (p : ℕ) else 1 : ℕ) : ℝ) := by
    rw [routeETernaryLeftProduct, Nat.cast_prod]
    exact Real.log_prod fun p _ => by
      by_cases hs : h p = 1
      · simp [hs, p.1.2.ne_zero]
      · simp [hs]
  have hright : Real.log (routeETernaryRightProduct h : ℝ) =
      ∑ p : Q, Real.log ((if h p = 2 then (p : ℕ) else 1 : ℕ) : ℝ) := by
    rw [routeETernaryRightProduct, Nat.cast_prod]
    exact Real.log_prod fun p _ => by
      by_cases hs : h p = 2
      · simp [hs, p.1.2.ne_zero]
      · simp [hs]
  rw [routeETernaryHistoryFrequency, hleft, hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact routeETernaryCharge_log_eq (h p) p

theorem routeETernaryHistoryFrequency_separated
    (Q : Finset Nat.Primes) (h k : RouteETernaryHistory Q) (hhk : h ≠ k) :
    1 / ((routeETernaryPrimorial Q : ℝ) ^ 2) ≤
      |routeETernaryHistoryFrequency h - routeETernaryHistoryFrequency k| := by
  let A := routeETernaryLeftProduct h
  let B := routeETernaryRightProduct h
  let C := routeETernaryLeftProduct k
  let D := routeETernaryRightProduct k
  let R := routeETernaryPrimorial Q
  have hA : 0 < A := routeETernaryLeftProduct_pos h
  have hB : 0 < B := routeETernaryRightProduct_pos h
  have hC : 0 < C := routeETernaryLeftProduct_pos k
  have hD : 0 < D := routeETernaryRightProduct_pos k
  have hAR : A ≤ R := routeETernaryLeftProduct_le_primorial h
  have hBR : B ≤ R := routeETernaryRightProduct_le_primorial h
  have hCR : C ≤ R := routeETernaryLeftProduct_le_primorial k
  have hDR : D ≤ R := routeETernaryRightProduct_le_primorial k
  have hAD : 0 < A * D := Nat.mul_pos hA hD
  have hCB : 0 < C * B := Nat.mul_pos hC hB
  have hADR : A * D ≤ R ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hAR hDR
  have hCBR : C * B ≤ R ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hCR hBR
  have hcross : A * D ≠ C * B := by
    intro hcross
    apply hhk
    apply routeETernaryHistoryFrequency_injective Q
    rw [routeETernaryHistoryFrequency_eq_log_products,
      routeETernaryHistoryFrequency_eq_log_products]
    have hlog := congrArg (fun n : ℕ => Real.log (n : ℝ)) hcross
    rw [Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hA.ne') (Nat.cast_ne_zero.mpr hD.ne'),
      Real.log_mul (Nat.cast_ne_zero.mpr hC.ne') (Nat.cast_ne_zero.mpr hB.ne')] at hlog
    linarith
  have hbase := RHTower.Sieve.one_div_nat_upper_le_abs_log_sub
    hAD hCB hADR hCBR hcross
  have hfreq : routeETernaryHistoryFrequency h - routeETernaryHistoryFrequency k =
      Real.log ((A * D : ℕ) : ℝ) - Real.log ((C * B : ℕ) : ℝ) := by
    rw [routeETernaryHistoryFrequency_eq_log_products,
      routeETernaryHistoryFrequency_eq_log_products]
    rw [Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hA.ne') (Nat.cast_ne_zero.mpr hD.ne'),
      Real.log_mul (Nat.cast_ne_zero.mpr hC.ne') (Nat.cast_ne_zero.mpr hB.ne')]
    ring
  have hcast : (((R ^ 2 : ℕ) : ℝ)) = (R : ℝ) ^ 2 := by norm_num
  rw [hcast] at hbase
  rw [hfreq]
  simpa [R] using hbase

open HTGeometry.ConstraintMotiveRelativity

def routeETernaryLocalCoefficient (s : Fin 3) : ℂ :=
  if s = 0 then 1 else -1

def routeETernaryLocalPhase (p : Nat.Primes) (s : Fin 3) (t : ℝ) : ℂ :=
  if s = 0 then 1 else if s = 1 then
    (starRingEnd ℂ) (phaseCovec t p) else phaseCovec t p

def routeETernaryHistoryCoefficient {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : ℂ :=
  ∏ p : Q, routeETernaryLocalCoefficient (h p)

def routeETernaryReporter (Q : Finset Nat.Primes) (t : ℝ) : ℂ :=
  ∏ p : Q,
    (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)

theorem routeETernaryLocalPhase_eq_exp (p : Nat.Primes) (s : Fin 3) (t : ℝ) :
    routeETernaryLocalPhase p s t =
      Complex.exp
        (((t * (routeETernaryCharge s : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ) *
          Complex.I) := by
  fin_cases s
  · simp [routeETernaryLocalPhase, routeETernaryCharge]
  · simp [routeETernaryLocalPhase, routeETernaryCharge]
    rw [phaseCovec_eq, ← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [← Complex.natCast_log]
    push_cast
    ring
  · simp [routeETernaryLocalPhase, routeETernaryCharge]
    rw [phaseCovec_eq]
    congr 1
    push_cast
    ring

theorem routeETernaryLocalSum_eq_factor (p : Nat.Primes) (t : ℝ) :
    (∑ s : Fin 3,
      routeETernaryLocalCoefficient s * routeETernaryLocalPhase p s t) =
      1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p := by
  simp [Fin.sum_univ_succ, routeETernaryLocalCoefficient, routeETernaryLocalPhase]
  ring

theorem routeETernaryHistoryPhaseProduct_eq_exp
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) (t : ℝ) :
    (∏ p : Q, routeETernaryLocalPhase p (h p) t) =
      Complex.exp
        (((t * routeETernaryHistoryFrequency h : ℝ) : ℂ) * Complex.I) := by
  simp_rw [routeETernaryLocalPhase_eq_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  have hsum :
      (∑ p : Q,
        t * (routeETernaryCharge (h p) : ℝ) * Real.log ((p : Nat.Primes) : ℕ)) =
        t * routeETernaryHistoryFrequency h := by
    rw [routeETernaryHistoryFrequency, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [← Complex.ofReal_sum, hsum]

theorem routeETernaryReporter_eq_frequencyPolynomial
    (Q : Finset Nat.Primes) (t : ℝ) :
    routeETernaryReporter Q t =
      RHTower.routeEFintypeFrequencyPolynomial
        (routeETernaryHistoryFrequency (Q := Q))
        routeETernaryHistoryCoefficient t := by
  classical
  rw [routeETernaryReporter, RHTower.routeEFintypeFrequencyPolynomial]
  simp_rw [← routeETernaryLocalSum_eq_factor]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [routeETernaryHistoryCoefficient, Finset.prod_mul_distrib,
    routeETernaryHistoryPhaseProduct_eq_exp]

@[simp] theorem norm_routeETernaryLocalCoefficient (s : Fin 3) :
    ‖routeETernaryLocalCoefficient s‖ = 1 := by
  fin_cases s <;> simp [routeETernaryLocalCoefficient]

@[simp] theorem norm_routeETernaryHistoryCoefficient
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    ‖routeETernaryHistoryCoefficient h‖ = 1 := by
  rw [routeETernaryHistoryCoefficient, norm_prod]
  simp

theorem routeETernaryHistoryCoefficient_energy
    (Q : Finset Nat.Primes) :
    (∑ h : RouteETernaryHistory Q, ‖routeETernaryHistoryCoefficient h‖ ^ 2) =
      (3 : ℝ) ^ Q.card := by
  simp

theorem routeETernaryHistory_card (Q : Finset Nat.Primes) :
    Fintype.card (RouteETernaryHistory Q) = 3 ^ Q.card := by
  simp

theorem routeETernaryReporter_meanValue_le
    (Q : Finset Nat.Primes) (W : ℝ) :
    (∫ t in (-W)..W, ‖routeETernaryReporter Q t‖ ^ 2) ≤
      (2 * W + 4 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
        (1 + (Q.card : ℝ) * Real.log 3)) * (3 : ℝ) ^ Q.card := by
  classical
  let emptyHistory : RouteETernaryHistory Q := fun _ => 0
  letI : Nonempty (RouteETernaryHistory Q) := ⟨emptyHistory⟩
  let delta : ℝ := 1 / (routeETernaryPrimorial Q : ℝ) ^ 2
  have hR : (0 : ℝ) < (routeETernaryPrimorial Q : ℝ) := by
    exact_mod_cast routeETernaryPrimorial_pos Q
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase := RHTower.routeEFintypeFrequency_meanValue_le
    (routeETernaryHistoryFrequency (Q := Q)) routeETernaryHistoryCoefficient
    (routeETernaryHistoryFrequency_injective Q) hdelta
    (routeETernaryHistoryFrequency_separated Q) W
  have hpoly : ∀ t,
      RHTower.routeEFintypeFrequencyPolynomial
          (routeETernaryHistoryFrequency (Q := Q))
          routeETernaryHistoryCoefficient t = routeETernaryReporter Q t :=
    fun t => (routeETernaryReporter_eq_frequencyPolynomial Q t).symm
  simp_rw [hpoly] at hbase
  rw [routeETernaryHistoryCoefficient_energy, routeETernaryHistory_card] at hbase
  have hlog : Real.log (((3 ^ Q.card : ℕ) : ℝ)) =
      (Q.card : ℝ) * Real.log 3 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlog] at hbase
  have hconstant :
      4 / (1 / (routeETernaryPrimorial Q : ℝ) ^ 2) =
        4 * (routeETernaryPrimorial Q : ℝ) ^ 2 := by
    field_simp [hR.ne']
  dsimp [delta] at hbase
  rw [hconstant] at hbase
  exact hbase

theorem routeETernaryLocalFactor_normSq_deficit
    (p : Nat.Primes) (t : ℝ) :
    9 - Complex.normSq
        (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p) =
      4 * (1 + (phaseCovec t p).re) * (2 - (phaseCovec t p).re) := by
  rw [Complex.normSq_apply]
  simp only [Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.sub_re, Complex.sub_im]
  ring

theorem routeETernaryLocalFactor_norm_le_three
    (p : Nat.Primes) (t : ℝ) :
    ‖1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p‖ ≤ 3 := by
  have hreabs : |(phaseCovec t p).re| ≤ 1 := by
    calc
      |(phaseCovec t p).re| ≤ ‖phaseCovec t p‖ := Complex.abs_re_le_norm _
      _ = 1 := norm_phaseCovec t p
  have hdef := routeETernaryLocalFactor_normSq_deficit p t
  have hnonneg :
      0 ≤ 4 * (1 + (phaseCovec t p).re) * (2 - (phaseCovec t p).re) := by
    have hlo : -1 ≤ (phaseCovec t p).re := (abs_le.mp hreabs).1
    have hhi : (phaseCovec t p).re ≤ 1 := (abs_le.mp hreabs).2
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  rw [Complex.normSq_eq_norm_sq] at hdef
  nlinarith [norm_nonneg
    (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)]

theorem routeETernaryLocalFactor_norm_eq_three_iff
    (p : Nat.Primes) (t : ℝ) :
    ‖1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p‖ = 3 ↔
      phaseCovec t p = -1 := by
  let z := phaseCovec t p
  have hzNorm : ‖z‖ = 1 := norm_phaseCovec t p
  have hreabs : |z.re| ≤ 1 := by
    calc |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm _
      _ = 1 := hzNorm
  constructor
  · intro hnorm
    have hdef := routeETernaryLocalFactor_normSq_deficit p t
    have hsq : Complex.normSq
        (1 - (starRingEnd ℂ) z - z) = 9 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hre : z.re = -1 := by
      change 9 - Complex.normSq
          (1 - (starRingEnd ℂ) z - z) =
        4 * (1 + z.re) * (2 - z.re) at hdef
      rw [hsq] at hdef
      have hlo : -1 ≤ z.re := (abs_le.mp hreabs).1
      have hhi : z.re ≤ 1 := (abs_le.mp hreabs).2
      nlinarith
    have hzsq : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hzNorm]
      norm_num
    rw [Complex.normSq_apply] at hzsq
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply Complex.ext
    · simpa [hre]
    · simpa [him]
  · intro hz
    rw [hz]
    norm_num

theorem routeETernaryReporter_norm_le_pow
    (Q : Finset Nat.Primes) (t : ℝ) :
    ‖routeETernaryReporter Q t‖ ≤ (3 : ℝ) ^ Q.card := by
  rw [routeETernaryReporter, norm_prod]
  calc
    (∏ p : Q,
        ‖1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p‖) ≤
        ∏ _p : Q, (3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact routeETernaryLocalFactor_norm_le_three p t
    _ = (3 : ℝ) ^ Q.card := by simp

theorem routeETernaryLocalFactor_sub_three_norm_le
    (p : Nat.Primes) (t : ℝ) :
    ‖(1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p) - 3‖ ≤
      2 * ‖phaseCovec t p + 1‖ := by
  let z := phaseCovec t p
  have heq : (1 - (starRingEnd ℂ) z - z) - 3 =
      -((starRingEnd ℂ) (z + 1)) - (z + 1) := by
    simp only [map_add, map_one]
    ring
  rw [heq]
  calc
    ‖-((starRingEnd ℂ) (z + 1)) - (z + 1)‖ ≤
        ‖-((starRingEnd ℂ) (z + 1))‖ + ‖z + 1‖ := norm_sub_le _ _
    _ = 2 * ‖z + 1‖ := by
      rw [norm_neg, RCLike.norm_conj]
      ring

theorem exists_gt_routeETernaryReporter_norm_gt_pow_sub
    (Q : Finset Nat.Primes) (T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, T < t ∧
      (3 : ℝ) ^ Q.card - epsilon < ‖routeETernaryReporter Q t‖ := by
  classical
  let eta : ℝ := epsilon /
    (4 * ((Q.card : ℝ) + 1) * (3 : ℝ) ^ Q.card)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨t, ht, hphase⟩ :=
    RHTower.exists_gt_phaseCovec_near_antiscale Q T heta
  refine ⟨t, ht, ?_⟩
  have hfactor : ∀ p ∈ Q,
      ‖(1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p) - 3‖ ≤
        2 * eta := by
    intro p hp
    exact (routeETernaryLocalFactor_sub_three_norm_le p t).trans
      (mul_le_mul_of_nonneg_left (hphase ⟨p, hp⟩).le (by norm_num))
  have hprod := GaloisForLFunctions.norm_prod_sub_prod_le
    (fun p : Nat.Primes =>
      1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)
    (fun _ : Nat.Primes => (3 : ℂ))
    (C := 3) (δ := 2 * eta) (by norm_num) (by positivity) Q
    (fun p hp => routeETernaryLocalFactor_norm_le_three p t)
    (by simp) hfactor
  have hreport :
      (∏ p ∈ Q,
        (1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)) =
        routeETernaryReporter Q t := by
    rw [routeETernaryReporter]
    simpa using (Finset.prod_attach Q
      (fun p : Nat.Primes =>
        1 - (starRingEnd ℂ) (phaseCovec t p) - phaseCovec t p)).symm
  rw [hreport] at hprod
  simp only [Finset.prod_const] at hprod
  have hsmall :
      (Q.card : ℝ) * 3 ^ Q.card * (2 * eta) < epsilon := by
    have hratio : (Q.card : ℝ) / (2 * ((Q.card : ℝ) + 1)) < 1 := by
      have hcard : (0 : ℝ) ≤ Q.card := by positivity
      rw [div_lt_one (by positivity)]
      linarith
    calc
      (Q.card : ℝ) * 3 ^ Q.card * (2 * eta) =
          epsilon * ((Q.card : ℝ) / (2 * ((Q.card : ℝ) + 1))) := by
            dsimp [eta]
            field_simp
            ring
      _ < epsilon * 1 := mul_lt_mul_of_pos_left hratio hepsilon
      _ = epsilon := mul_one _
  have hreverse :
      (3 : ℝ) ^ Q.card - ‖routeETernaryReporter Q t‖ ≤
        ‖routeETernaryReporter Q t - (3 : ℂ) ^ Q.card‖ := by
    calc
      (3 : ℝ) ^ Q.card - ‖routeETernaryReporter Q t‖ ≤
          ‖(3 : ℂ) ^ Q.card - routeETernaryReporter Q t‖ := by
            simpa using
              norm_sub_norm_le ((3 : ℂ) ^ Q.card) (routeETernaryReporter Q t)
      _ = ‖routeETernaryReporter Q t - (3 : ℂ) ^ Q.card‖ := norm_sub_rev _ _
  linarith

def routeETernaryReciprocalRadius (p : Nat.Primes) : ℝ :=
  1 / (((p : ℕ) : ℝ))

theorem routeETernaryReciprocalRadius_pos (p : Nat.Primes) :
    0 < routeETernaryReciprocalRadius p := by
  rw [routeETernaryReciprocalRadius]
  exact one_div_pos.mpr (by exact_mod_cast p.2.pos)

theorem routeETernaryReciprocalRadius_le_half (p : Nat.Primes) :
    routeETernaryReciprocalRadius p ≤ 1 / 2 := by
  rw [routeETernaryReciprocalRadius]
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast p.2.two_le)

def routeETernaryWeightedLocalCoefficient (p : Nat.Primes) (s : Fin 3) : ℂ :=
  let u := routeETernaryReciprocalRadius p
  if s = 0 then (((1 / (1 + 2 * u) : ℝ)) : ℂ)
  else -(((u / (1 + 2 * u) : ℝ)) : ℂ)

def routeETernaryWeightedHistoryCoefficient {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : ℂ :=
  ∏ p : Q, routeETernaryWeightedLocalCoefficient p (h p)

def routeETernaryWeightedReporter (Q : Finset Nat.Primes) (t : ℝ) : ℂ :=
  ∏ p : Q,
    let u := routeETernaryReciprocalRadius p
    (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
      (u : ℂ) * phaseCovec t p) / (1 + 2 * u)

def routeETernaryWeightedMeanSquareMass (Q : Finset Nat.Primes) : ℝ :=
  ∏ p : Q,
    let u := routeETernaryReciprocalRadius p
    (1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2

theorem routeETernaryWeightedLocalSum_eq_factor
    (p : Nat.Primes) (t : ℝ) :
    (∑ s : Fin 3,
      routeETernaryWeightedLocalCoefficient p s * routeETernaryLocalPhase p s t) =
      let u := routeETernaryReciprocalRadius p
      (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
        (u : ℂ) * phaseCovec t p) / (1 + 2 * u) := by
  let u := routeETernaryReciprocalRadius p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hdenR : (1 + 2 * u : ℝ) ≠ 0 := by positivity
  have hdenC : (1 + (2 : ℂ) * (u : ℂ)) ≠ 0 := by exact_mod_cast hdenR
  simp [Fin.sum_univ_succ, routeETernaryWeightedLocalCoefficient,
    routeETernaryLocalPhase]
  field_simp [hdenC]
  ring

theorem routeETernaryWeightedReporter_eq_frequencyPolynomial
    (Q : Finset Nat.Primes) (t : ℝ) :
    routeETernaryWeightedReporter Q t =
      RHTower.routeEFintypeFrequencyPolynomial
        (routeETernaryHistoryFrequency (Q := Q))
        routeETernaryWeightedHistoryCoefficient t := by
  classical
  rw [routeETernaryWeightedReporter, RHTower.routeEFintypeFrequencyPolynomial]
  simp_rw [← routeETernaryWeightedLocalSum_eq_factor]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [routeETernaryWeightedHistoryCoefficient, Finset.prod_mul_distrib,
    routeETernaryHistoryPhaseProduct_eq_exp]

theorem norm_routeETernaryWeightedLocalCoefficient
    (p : Nat.Primes) (s : Fin 3) :
    ‖routeETernaryWeightedLocalCoefficient p s‖ =
      let u := routeETernaryReciprocalRadius p
      if s = 0 then 1 / (1 + 2 * u) else u / (1 + 2 * u) := by
  let u := routeETernaryReciprocalRadius p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hden : 0 < 1 + 2 * u := by positivity
  have hdenNorm : ‖(1 + (2 : ℂ) * (u : ℂ))‖ = 1 + 2 * u := by
    rw [show (1 + (2 : ℂ) * (u : ℂ)) = (((1 + 2 * u : ℝ)) : ℂ) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  fin_cases s <;>
    simp [routeETernaryWeightedLocalCoefficient, u, hdenNorm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.le]

theorem routeETernaryWeightedLocalCoefficient_energy
    (p : Nat.Primes) :
    (∑ s : Fin 3, ‖routeETernaryWeightedLocalCoefficient p s‖ ^ 2) =
      let u := routeETernaryReciprocalRadius p
      (1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2 := by
  let u := routeETernaryReciprocalRadius p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hden : (1 + 2 * u : ℝ) ≠ 0 := by positivity
  simp_rw [norm_routeETernaryWeightedLocalCoefficient]
  simp [Fin.sum_univ_succ]
  field_simp [hden]

theorem routeETernaryWeightedHistoryCoefficient_energy
    (Q : Finset Nat.Primes) :
    (∑ h : RouteETernaryHistory Q,
      ‖routeETernaryWeightedHistoryCoefficient h‖ ^ 2) =
      routeETernaryWeightedMeanSquareMass Q := by
  classical
  calc
    (∑ h : RouteETernaryHistory Q,
        ‖routeETernaryWeightedHistoryCoefficient h‖ ^ 2) =
        ∑ h : RouteETernaryHistory Q,
          ∏ p : Q, ‖routeETernaryWeightedLocalCoefficient p (h p)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [routeETernaryWeightedHistoryCoefficient, norm_prod, Finset.prod_pow]
    _ = ∏ p : Q,
        ∑ s : Fin 3, ‖routeETernaryWeightedLocalCoefficient p s‖ ^ 2 :=
      (Fintype.prod_sum fun (p : Q) (s : Fin 3) =>
        ‖routeETernaryWeightedLocalCoefficient p s‖ ^ 2).symm
    _ = routeETernaryWeightedMeanSquareMass Q := by
      rw [routeETernaryWeightedMeanSquareMass]
      apply Finset.prod_congr rfl
      intro p hp
      exact routeETernaryWeightedLocalCoefficient_energy p

theorem routeETernaryWeightedReporter_meanValue_le
    (Q : Finset Nat.Primes) (W : ℝ) :
    (∫ t in (-W)..W, ‖routeETernaryWeightedReporter Q t‖ ^ 2) ≤
      (2 * W + 4 * (routeETernaryPrimorial Q : ℝ) ^ 2 *
        (1 + (Q.card : ℝ) * Real.log 3)) *
          routeETernaryWeightedMeanSquareMass Q := by
  classical
  let emptyHistory : RouteETernaryHistory Q := fun _ => 0
  letI : Nonempty (RouteETernaryHistory Q) := ⟨emptyHistory⟩
  let delta : ℝ := 1 / (routeETernaryPrimorial Q : ℝ) ^ 2
  have hR : (0 : ℝ) < (routeETernaryPrimorial Q : ℝ) := by
    exact_mod_cast routeETernaryPrimorial_pos Q
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase := RHTower.routeEFintypeFrequency_meanValue_le
    (routeETernaryHistoryFrequency (Q := Q))
    routeETernaryWeightedHistoryCoefficient
    (routeETernaryHistoryFrequency_injective Q) hdelta
    (routeETernaryHistoryFrequency_separated Q) W
  have hpoly : ∀ t,
      RHTower.routeEFintypeFrequencyPolynomial
          (routeETernaryHistoryFrequency (Q := Q))
          routeETernaryWeightedHistoryCoefficient t =
        routeETernaryWeightedReporter Q t :=
    fun t => (routeETernaryWeightedReporter_eq_frequencyPolynomial Q t).symm
  simp_rw [hpoly] at hbase
  rw [routeETernaryWeightedHistoryCoefficient_energy,
    routeETernaryHistory_card] at hbase
  have hlog : Real.log (((3 ^ Q.card : ℕ) : ℝ)) =
      (Q.card : ℝ) * Real.log 3 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlog] at hbase
  have hconstant :
      4 / (1 / (routeETernaryPrimorial Q : ℝ) ^ 2) =
        4 * (routeETernaryPrimorial Q : ℝ) ^ 2 := by
    field_simp [hR.ne']
  dsimp [delta] at hbase
  rw [hconstant] at hbase
  exact hbase

theorem routeETernaryWeightedMeanSquareMass_nonneg
    (Q : Finset Nat.Primes) :
    0 ≤ routeETernaryWeightedMeanSquareMass Q := by
  rw [routeETernaryWeightedMeanSquareMass]
  apply Finset.prod_nonneg
  intro p hp
  exact div_nonneg (by positivity) (sq_nonneg _)

private theorem routeETernary_log_one_add_two_mul_ge
    {u : ℝ} (hu0 : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    u ≤ Real.log (1 + 2 * u) := by
  have hden : 0 < 1 + 2 * u := by linarith
  have hbase := log_sub_ge (by norm_num : (0 : ℝ) < 1)
    (by linarith : (1 : ℝ) ≤ 1 + 2 * u)
  have hfrac : u ≤ (2 * u) / (1 + 2 * u) := by
    rw [le_div_iff₀ hden]
    nlinarith
  rw [Real.log_one, sub_zero] at hbase
  have hbase' : (2 * u) / (1 + 2 * u) ≤ Real.log (1 + 2 * u) := by
    convert hbase using 1
    all_goals ring
  exact hfrac.trans hbase'

theorem routeETernaryWeightedLocalMass_le_exp
    (p : Nat.Primes) :
    let u := routeETernaryReciprocalRadius p
    (1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2 ≤
      Real.exp (2 * u ^ 2 - 2 * u) := by
  let u := routeETernaryReciprocalRadius p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have huHalf : u ≤ 1 / 2 := routeETernaryReciprocalRadius_le_half p
  have hnum : 0 < 1 + 2 * u ^ 2 := by positivity
  have hden : 0 < 1 + 2 * u := by positivity
  have hlogNum : Real.log (1 + 2 * u ^ 2) ≤ 2 * u ^ 2 := by
    have := Real.log_le_sub_one_of_pos hnum
    linarith
  have hlogDen : u ≤ Real.log (1 + 2 * u) :=
    routeETernary_log_one_add_two_mul_ge hu.le huHalf
  have hmassPos : 0 < (1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2 :=
    div_pos hnum (sq_pos_of_pos hden)
  have hlogMass :
      Real.log ((1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2) ≤
        2 * u ^ 2 - 2 * u := by
    rw [Real.log_div hnum.ne' (pow_ne_zero 2 hden.ne'), Real.log_pow]
    norm_num
    linarith
  calc
    (1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2 =
        Real.exp (Real.log ((1 + 2 * u ^ 2) / (1 + 2 * u) ^ 2)) :=
      (Real.exp_log hmassPos).symm
    _ ≤ Real.exp (2 * u ^ 2 - 2 * u) := Real.exp_le_exp.mpr hlogMass

theorem routeETernaryWeightedMeanSquareMass_le_exp
    (Q : Finset Nat.Primes) :
    routeETernaryWeightedMeanSquareMass Q ≤
      Real.exp
        (2 * ∑ p : Q, routeETernaryReciprocalRadius p ^ 2 -
          2 * ∑ p : Q, routeETernaryReciprocalRadius p) := by
  rw [routeETernaryWeightedMeanSquareMass]
  calc
    (∏ p : Q,
      (1 + 2 * routeETernaryReciprocalRadius p ^ 2) /
        (1 + 2 * routeETernaryReciprocalRadius p) ^ 2) ≤
        ∏ p : Q, Real.exp
          (2 * routeETernaryReciprocalRadius p ^ 2 -
            2 * routeETernaryReciprocalRadius p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact div_nonneg (by positivity) (sq_nonneg _)
      · intro p hp
        exact routeETernaryWeightedLocalMass_le_exp p
    _ = Real.exp
        (∑ p : Q,
          (2 * routeETernaryReciprocalRadius p ^ 2 -
            2 * routeETernaryReciprocalRadius p)) := by
      rw [Real.exp_sum]
    _ = Real.exp
        (2 * ∑ p : Q, routeETernaryReciprocalRadius p ^ 2 -
          2 * ∑ p : Q, routeETernaryReciprocalRadius p) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem routeETernaryWeightedLocalFactor_norm_le_one
    (p : Nat.Primes) (t : ℝ) :
    let u := routeETernaryReciprocalRadius p
    ‖(1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
      (u : ℂ) * phaseCovec t p) / (1 + 2 * u)‖ ≤ 1 := by
  let u := routeETernaryReciprocalRadius p
  let z := phaseCovec t p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hzNorm : ‖z‖ = 1 := norm_phaseCovec t p
  have hden : 0 < 1 + 2 * u := by positivity
  have hnum : ‖1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z‖ ≤
      1 + 2 * u := by
    calc
      ‖1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z‖ ≤
          ‖1 - (u : ℂ) * (starRingEnd ℂ) z‖ + ‖(u : ℂ) * z‖ :=
        norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(u : ℂ) * (starRingEnd ℂ) z‖) +
          ‖(u : ℂ) * z‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ = 1 + 2 * u := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hu, RCLike.norm_conj, hzNorm]
        norm_num
        ring
  have hdenNorm : ‖(1 + (2 : ℂ) * (u : ℂ))‖ = 1 + 2 * u := by
    rw [show (1 + (2 : ℂ) * (u : ℂ)) = (((1 + 2 * u : ℝ)) : ℂ) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  change ‖(1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) /
      (1 + 2 * u)‖ ≤ 1
  rw [norm_div, hdenNorm, div_le_one hden]
  exact hnum

theorem routeETernaryWeightedLocalNumerator_normSq_deficit
    (p : Nat.Primes) (t : ℝ) :
    let u := routeETernaryReciprocalRadius p
    (1 + 2 * u) ^ 2 - Complex.normSq
        (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
          (u : ℂ) * phaseCovec t p) =
      4 * u * (1 + (phaseCovec t p).re) *
        (1 + u * (1 - (phaseCovec t p).re)) := by
  let u := routeETernaryReciprocalRadius p
  let z := phaseCovec t p
  change (1 + 2 * u) ^ 2 - Complex.normSq
      (1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) =
    4 * u * (1 + z.re) * (1 + u * (1 - z.re))
  rw [Complex.normSq_apply]
  simp only [Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, add_zero, sub_zero]
  ring

theorem routeETernaryWeightedLocalFactor_norm_eq_one_iff
    (p : Nat.Primes) (t : ℝ) :
    let u := routeETernaryReciprocalRadius p
    ‖(1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
      (u : ℂ) * phaseCovec t p) / (1 + 2 * u)‖ = 1 ↔
        phaseCovec t p = -1 := by
  let u := routeETernaryReciprocalRadius p
  let z := phaseCovec t p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hzNorm : ‖z‖ = 1 := norm_phaseCovec t p
  have hden : 0 < 1 + 2 * u := by positivity
  have hdenNorm : ‖(1 + (2 : ℂ) * (u : ℂ))‖ = 1 + 2 * u := by
    rw [show (1 + (2 : ℂ) * (u : ℂ)) = (((1 + 2 * u : ℝ)) : ℂ) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  have hreabs : |z.re| ≤ 1 := by
    calc |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm _
      _ = 1 := hzNorm
  change ‖(1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) /
      (1 + 2 * u)‖ = 1 ↔ z = -1
  constructor
  · intro hnorm
    rw [norm_div, hdenNorm] at hnorm
    have hnumNorm :
        ‖1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z‖ =
          1 + 2 * u := by
      have hcross := (div_eq_iff hden.ne').mp hnorm
      simpa using hcross
    have hsq : Complex.normSq
        (1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) =
          (1 + 2 * u) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hnumNorm]
    have hdef := routeETernaryWeightedLocalNumerator_normSq_deficit p t
    change (1 + 2 * u) ^ 2 - Complex.normSq
        (1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) =
      4 * u * (1 + z.re) * (1 + u * (1 - z.re)) at hdef
    rw [hsq] at hdef
    have hlo : -1 ≤ z.re := (abs_le.mp hreabs).1
    have hhi : z.re ≤ 1 := (abs_le.mp hreabs).2
    have hother : 0 < 1 + u * (1 - z.re) := by positivity
    have hre : z.re = -1 := by
      by_contra hne
      have hgt : -1 < z.re := lt_of_le_of_ne hlo (Ne.symm hne)
      have hone : 0 < 1 + z.re := by linarith
      have hpos : 0 < 4 * u * (1 + z.re) * (1 + u * (1 - z.re)) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hu) hone) hother
      nlinarith
    have hzsq : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hzNorm]
      norm_num
    rw [Complex.normSq_apply] at hzsq
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply Complex.ext
    · simp [hre]
    · simp [him]
  · intro hz
    have hdenC : (1 + (2 : ℂ) * (u : ℂ)) ≠ 0 := by
      exact_mod_cast hden.ne'
    have hdenC' : (1 + (u : ℂ) * (2 : ℂ)) ≠ 0 := by
      simpa [mul_comm] using hdenC
    have hfactor :
        (1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) /
          (1 + 2 * u) = 1 := by
      rw [hz]
      simp only [map_neg, map_one]
      field_simp [hdenC, hdenC']
      ring
    rw [hfactor, norm_one]

theorem routeETernaryWeightedReporter_norm_le_one
    (Q : Finset Nat.Primes) (t : ℝ) :
    ‖routeETernaryWeightedReporter Q t‖ ≤ 1 := by
  rw [routeETernaryWeightedReporter, norm_prod]
  calc
    (∏ p : Q,
      ‖(let u := routeETernaryReciprocalRadius p
        (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
          (u : ℂ) * phaseCovec t p) / (1 + 2 * u))‖) ≤
        ∏ _p : Q, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact routeETernaryWeightedLocalFactor_norm_le_one p t
    _ = 1 := by simp

theorem routeETernaryWeightedLocalFactor_sub_one_norm_le_phase
    (p : Nat.Primes) (t : ℝ) :
    let u := routeETernaryReciprocalRadius p
    ‖(1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
      (u : ℂ) * phaseCovec t p) / (1 + 2 * u) - 1‖ ≤
        ‖phaseCovec t p + 1‖ := by
  let u := routeETernaryReciprocalRadius p
  let z := phaseCovec t p
  have hu : 0 < u := routeETernaryReciprocalRadius_pos p
  have hden : 0 < 1 + 2 * u := by positivity
  have hdenC : (1 + (2 : ℂ) * (u : ℂ)) ≠ 0 := by
    exact_mod_cast hden.ne'
  have hdenC' : (1 + (u : ℂ) * (2 : ℂ)) ≠ 0 := by
    simpa [mul_comm] using hdenC
  have hcast : (((u / (1 + 2 * u) : ℝ)) : ℂ) =
      (u : ℂ) / (1 + (2 : ℂ) * (u : ℂ)) := by
    push_cast
    rfl
  have heq :
      (1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) /
          (1 + 2 * u) - 1 =
        -((u / (1 + 2 * u) : ℝ) : ℂ) *
          ((starRingEnd ℂ) (z + 1) + (z + 1)) := by
    simp only [map_add, map_one]
    rw [hcast]
    field_simp [hdenC, hdenC']
    ring
  change ‖(1 - (u : ℂ) * (starRingEnd ℂ) z - (u : ℂ) * z) /
      (1 + 2 * u) - 1‖ ≤ ‖z + 1‖
  rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hu.le hden.le)]
  have hsum : ‖(starRingEnd ℂ) (z + 1) + (z + 1)‖ ≤
      2 * ‖z + 1‖ := by
    calc
      ‖(starRingEnd ℂ) (z + 1) + (z + 1)‖ ≤
          ‖(starRingEnd ℂ) (z + 1)‖ + ‖z + 1‖ := norm_add_le _ _
      _ = 2 * ‖z + 1‖ := by rw [RCLike.norm_conj]; ring
  have hcoef : 2 * u / (1 + 2 * u) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  calc
    u / (1 + 2 * u) *
        ‖(starRingEnd ℂ) (z + 1) + (z + 1)‖ ≤
        u / (1 + 2 * u) * (2 * ‖z + 1‖) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hu.le hden.le)
    _ = (2 * u / (1 + 2 * u)) * ‖z + 1‖ := by ring
    _ ≤ 1 * ‖z + 1‖ :=
      mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = ‖z + 1‖ := one_mul _

theorem exists_gt_routeETernaryWeightedReporter_norm_gt_one_sub
    (Q : Finset Nat.Primes) (T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, T < t ∧
      1 - epsilon < ‖routeETernaryWeightedReporter Q t‖ := by
  classical
  let eta : ℝ := epsilon / (2 * ((Q.card : ℝ) + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨t, ht, hphase⟩ :=
    RHTower.exists_gt_phaseCovec_near_antiscale Q T heta
  refine ⟨t, ht, ?_⟩
  have hfactor : ∀ p ∈ Q,
      ‖(let u := routeETernaryReciprocalRadius p
        (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
          (u : ℂ) * phaseCovec t p) / (1 + 2 * u)) - 1‖ ≤ eta := by
    intro p hp
    exact (routeETernaryWeightedLocalFactor_sub_one_norm_le_phase p t).trans
      (hphase ⟨p, hp⟩).le
  have hprod := GaloisForLFunctions.norm_prod_sub_prod_le
    (fun p : Nat.Primes =>
      let u := routeETernaryReciprocalRadius p
      (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
        (u : ℂ) * phaseCovec t p) / (1 + 2 * u))
    (fun _ : Nat.Primes => (1 : ℂ))
    (C := 1) (δ := eta) (by norm_num) heta.le Q
    (fun p hp => routeETernaryWeightedLocalFactor_norm_le_one p t)
    (by simp) hfactor
  have hreport :
      (∏ p ∈ Q,
        (let u := routeETernaryReciprocalRadius p
        (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
          (u : ℂ) * phaseCovec t p) / (1 + 2 * u))) =
        routeETernaryWeightedReporter Q t := by
    rw [routeETernaryWeightedReporter]
    simpa using (Finset.prod_attach Q
      (fun p : Nat.Primes =>
        let u := routeETernaryReciprocalRadius p
        (1 - (u : ℂ) * (starRingEnd ℂ) (phaseCovec t p) -
          (u : ℂ) * phaseCovec t p) / (1 + 2 * u))).symm
  rw [hreport] at hprod
  simp only [one_pow, mul_one, Finset.prod_const_one] at hprod
  have hsmall : (Q.card : ℝ) * eta < epsilon := by
    dsimp [eta]
    have hcard : (0 : ℝ) ≤ Q.card := by positivity
    have hden : (0 : ℝ) < 2 * ((Q.card : ℝ) + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hreverse : 1 - ‖routeETernaryWeightedReporter Q t‖ ≤
      ‖routeETernaryWeightedReporter Q t - 1‖ := by
    calc
      1 - ‖routeETernaryWeightedReporter Q t‖ ≤
          ‖(1 : ℂ) - routeETernaryWeightedReporter Q t‖ := by
        simpa only [norm_one] using
          norm_sub_norm_le (1 : ℂ) (routeETernaryWeightedReporter Q t)
      _ = ‖routeETernaryWeightedReporter Q t - 1‖ := norm_sub_rev _ _
  linarith

theorem routeETernaryReciprocalRadius_sq_sum_le
    (Q : Finset Nat.Primes) :
    (∑ p : Q, routeETernaryReciprocalRadius p ^ 2) ≤ 49 / 100 := by
  have hpartial := Summable.sum_le_tsum Q
    (fun p hp => by positivity)
    RHTower.Sieve.summable_primes_inv_sq
  calc
    (∑ p : Q, routeETernaryReciprocalRadius p ^ 2) =
        ∑ p ∈ Q, routeETernaryReciprocalRadius p ^ 2 := by
      simpa using (Finset.sum_attach Q
        (fun p : Nat.Primes => routeETernaryReciprocalRadius p ^ 2))
    _ =
        ∑ p ∈ Q, (1 : ℝ) / (((p : ℕ) : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [routeETernaryReciprocalRadius]
      field_simp
    _ ≤ ∑' p : Nat.Primes, (1 : ℝ) / (((p : ℕ) : ℝ)) ^ 2 := hpartial
    _ ≤ 49 / 100 := RHTower.Sieve.tsum_primes_inv_sq_le

theorem routeETernaryCriticalPrimePacket_radiusMass_eq (N : ℕ) :
    (∑ p : RHTower.routeECriticalPrimesBelow N,
      routeETernaryReciprocalRadius p) =
      RHTower.routeECriticalPrimeRadiusMass N 1 := by
  calc
    (∑ p : RHTower.routeECriticalPrimesBelow N,
        routeETernaryReciprocalRadius p) =
        ∑ p ∈ RHTower.routeECriticalPrimesBelow N,
          routeETernaryReciprocalRadius p := by
      simpa using (Finset.sum_attach (RHTower.routeECriticalPrimesBelow N)
        routeETernaryReciprocalRadius)
    _ = ∑ n ∈ Nat.primesBelow N, (1 : ℝ) / (n : ℝ) := by
      simpa [RHTower.routeECriticalPrimesBelow, routeETernaryReciprocalRadius]
        using (Finset.sum_attach (Nat.primesBelow N)
          (fun n : ℕ => (1 : ℝ) / (n : ℝ)))
    _ = RHTower.routeECriticalPrimeRadiusMass N 1 := by
      rw [RHTower.routeECriticalPrimeRadiusMass]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.rpow_neg_one]
      rw [one_div]

theorem tendsto_routeETernaryWeightedMeanSquareMass_criticalPrimePacket_zero :
    Filter.Tendsto
      (fun N => routeETernaryWeightedMeanSquareMass
        (RHTower.routeECriticalPrimesBelow N))
      Filter.atTop (nhds 0) := by
  have hsum : Filter.Tendsto
      (fun N => ∑ p : RHTower.routeECriticalPrimesBelow N,
        routeETernaryReciprocalRadius p)
      Filter.atTop Filter.atTop := by
    simpa only [routeETernaryCriticalPrimePacket_radiusMass_eq] using
      (RHTower.tendsto_routeECriticalPrimeRadiusMass_atTop
        (r := 1) (by norm_num))
  have hdouble : Filter.Tendsto
      (fun N => 2 * ∑ p : RHTower.routeECriticalPrimesBelow N,
        routeETernaryReciprocalRadius p)
      Filter.atTop Filter.atTop := hsum.const_mul_atTop (by norm_num)
  have hneg : Filter.Tendsto
      (fun N => -(2 * ∑ p : RHTower.routeECriticalPrimesBelow N,
        routeETernaryReciprocalRadius p))
      Filter.atTop Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp hdouble
  have hexponent : Filter.Tendsto
      (fun N => 1 - 2 * ∑ p : RHTower.routeECriticalPrimesBelow N,
        routeETernaryReciprocalRadius p)
      Filter.atTop Filter.atBot := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atBot_add_const_left Filter.atTop (1 : ℝ) hneg
  have hexp : Filter.Tendsto
      (fun N => Real.exp
        (1 - 2 * ∑ p : RHTower.routeECriticalPrimesBelow N,
          routeETernaryReciprocalRadius p))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hexponent
  exact squeeze_zero
    (fun N => routeETernaryWeightedMeanSquareMass_nonneg _)
    (fun N =>
      (routeETernaryWeightedMeanSquareMass_le_exp
        (RHTower.routeECriticalPrimesBelow N)).trans
        (Real.exp_le_exp.mpr (by
          have hsq := routeETernaryReciprocalRadius_sq_sum_le
            (RHTower.routeECriticalPrimesBelow N)
          linarith)))
    hexp

def routeETernaryPrimeEmbedding (Q : Finset Nat.Primes) : Q ↪ ℕ where
  toFun p := ((p : Q) : Nat.Primes)
  inj' := by
    intro p q hpq
    exact Subtype.ext (Subtype.ext hpq)

def routeETernaryLeftSupport {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : Finset ℕ :=
  (Finset.univ.filter (fun p : Q => h p = 1)).map
    (routeETernaryPrimeEmbedding Q)

def routeETernaryRightSupport {Q : Finset Nat.Primes}
    (h : RouteETernaryHistory Q) : Finset ℕ :=
  (Finset.univ.filter (fun p : Q => h p = 2)).map
    (routeETernaryPrimeEmbedding Q)

theorem routeETernaryLeftProduct_eq_supportProduct
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    routeETernaryLeftProduct h = ∏ p ∈ routeETernaryLeftSupport h, p := by
  simp [routeETernaryLeftProduct, routeETernaryLeftSupport,
    routeETernaryPrimeEmbedding, Finset.prod_ite]

theorem routeETernaryRightProduct_eq_supportProduct
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    routeETernaryRightProduct h = ∏ p ∈ routeETernaryRightSupport h, p := by
  simp [routeETernaryRightProduct, routeETernaryRightSupport,
    routeETernaryPrimeEmbedding, Finset.prod_ite]

theorem routeETernaryLeftSupport_prime
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    ∀ p ∈ routeETernaryLeftSupport h, p.Prime := by
  intro p hp
  rw [routeETernaryLeftSupport, Finset.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact q.1.2

theorem routeETernaryRightSupport_prime
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    ∀ p ∈ routeETernaryRightSupport h, p.Prime := by
  intro p hp
  rw [routeETernaryRightSupport, Finset.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact q.1.2

theorem routeETernaryLeftProduct_squarefree
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    Squarefree (routeETernaryLeftProduct h) := by
  rw [routeETernaryLeftProduct_eq_supportProduct]
  exact RHTower.GibbsGas.squarefree_prod_primes
    (routeETernaryLeftSupport_prime h)

theorem routeETernaryRightProduct_squarefree
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    Squarefree (routeETernaryRightProduct h) := by
  rw [routeETernaryRightProduct_eq_supportProduct]
  exact RHTower.GibbsGas.squarefree_prod_primes
    (routeETernaryRightSupport_prime h)

theorem routeETernarySupports_disjoint
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    Disjoint (routeETernaryLeftSupport h) (routeETernaryRightSupport h) := by
  rw [Finset.disjoint_left]
  intro p hpL hpR
  rw [routeETernaryLeftSupport, Finset.mem_map] at hpL
  rw [routeETernaryRightSupport, Finset.mem_map] at hpR
  obtain ⟨q, hq, hqp⟩ := hpL
  obtain ⟨r, hr, hrp⟩ := hpR
  have hqr : q = r := by
    apply Subtype.ext
    apply Subtype.ext
    exact hqp.trans hrp.symm
  subst r
  rw [Finset.mem_filter] at hq hr
  omega

theorem routeETernaryProducts_coprime
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    Nat.Coprime (routeETernaryLeftProduct h) (routeETernaryRightProduct h) := by
  rw [routeETernaryLeftProduct_eq_supportProduct,
    routeETernaryRightProduct_eq_supportProduct]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  apply (Nat.coprime_primes
    (routeETernaryLeftSupport_prime h p hp)
    (routeETernaryRightSupport_prime h q hq)).mpr
  intro hpq
  exact (Finset.disjoint_left.mp (routeETernarySupports_disjoint h)) hp (hpq ▸ hq)

private theorem routeETernaryLocalCoefficient_split (s : Fin 3) :
    routeETernaryLocalCoefficient s =
      (if s = 1 then (-1 : ℂ) else 1) *
        (if s = 2 then (-1 : ℂ) else 1) := by
  fin_cases s <;> simp [routeETernaryLocalCoefficient]

theorem routeETernaryHistoryCoefficient_eq_moebiusProducts
    {Q : Finset Nat.Primes} (h : RouteETernaryHistory Q) :
    routeETernaryHistoryCoefficient h =
      (((μ (routeETernaryLeftProduct h) : ℤ) : ℂ)) *
        (((μ (routeETernaryRightProduct h) : ℤ) : ℂ)) := by
  have hmuL := RHTower.GibbsGas.moebius_prod_primes
    (routeETernaryLeftSupport_prime h)
  have hmuR := RHTower.GibbsGas.moebius_prod_primes
    (routeETernaryRightSupport_prime h)
  rw [← routeETernaryLeftProduct_eq_supportProduct] at hmuL
  rw [← routeETernaryRightProduct_eq_supportProduct] at hmuR
  have hmuLC : (((μ (routeETernaryLeftProduct h) : ℤ) : ℂ)) =
      (-1 : ℂ) ^ (routeETernaryLeftSupport h).card := by
    exact_mod_cast hmuL
  have hmuRC : (((μ (routeETernaryRightProduct h) : ℤ) : ℂ)) =
      (-1 : ℂ) ^ (routeETernaryRightSupport h).card := by
    exact_mod_cast hmuR
  rw [hmuLC, hmuRC, routeETernaryHistoryCoefficient]
  simp_rw [routeETernaryLocalCoefficient_split]
  rw [Finset.prod_mul_distrib]
  simp [routeETernaryLeftSupport, routeETernaryRightSupport,
    Finset.prod_ite, Finset.card_map]

end

end RHTower.Sieve
