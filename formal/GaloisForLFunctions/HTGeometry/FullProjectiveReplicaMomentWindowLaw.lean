import GaloisForLFunctions.HTGeometry.FullProjectiveChoiAffineTensorWindowLaw
import GaloisForLFunctions.HTGeometry.SubprobabilityPhaseTwistedReplicaShortcutActionLaw
import GaloisForLFunctions.HTGeometry.FiniteGridCoherenceMoment

open scoped BigOperators Interval
open Real intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

abbrev FullProjectiveReplicaLayer (n r : ℕ) :=
  {p : Fin (n + 2) → ℕ // p ∈ Finset.univ.piAntidiag r}

/-- Zero-energy anchor followed by the complete projective clock-ratio packet. -/
def anchoredFullProjectiveFrequency (y : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.cons 0 (fullProjectiveFrequency y)

def fullProjectiveReplicaPairCoefficient
    (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ) (r : ℕ)
    (x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r) : ℂ :=
  if x.1.1 = x.2.1 then 0 else
    (fidelityReplicaMultiplicityWeight weight x.1.1 x.2.1 : ℂ) *
      replicaMultiplicityTwist twist x.1.1 x.2.1

def fullProjectiveReplicaPairClockCharacter
    (x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r) : ℤ :=
  if x.1.1 = x.2.1 then 1 else replicaMultiplicityCharacter x.1.1 x.2.1 1

def fullProjectiveReplicaPairRatioCharacter
    (x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r) : Fin n → ℤ :=
  if x.1.1 = x.2.1 then 0 else
    fun j => replicaMultiplicityCharacter x.1.1 x.2.1 j.succ.succ

def fullProjectiveReplicaTwistedDiagonal
    (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ) (r : ℕ) : ℂ :=
  ∑ p : FullProjectiveReplicaLayer n r,
    (fidelityReplicaMultiplicityWeight weight p.1 p.1 : ℂ) *
      replicaMultiplicityTwist twist p.1 p.1

theorem fullProjectiveReplicaPairCharacter_nonconstant
    (x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r) :
    fullProjectiveReplicaPairClockCharacter x ≠ 0 ∨
      fullProjectiveReplicaPairRatioCharacter x ≠ 0 := by
  by_cases h : x.1.1 = x.2.1
  · left
    simp [fullProjectiveReplicaPairClockCharacter, h]
  · have hc : replicaMultiplicityCharacter x.1.1 x.2.1 ≠ 0 :=
      (replicaMultiplicityCharacter_eq_zero_iff x.1.1 x.2.1).not.mpr h
    by_contra hz
    push Not at hz
    apply hc
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hrest :
          (∑ j : Fin (n + 1), x.1.1 j.succ) =
            ∑ j : Fin (n + 1), x.2.1 j.succ := by
        apply Finset.sum_congr rfl
        intro j hj
        refine Fin.cases ?_ (fun k => ?_) j
        · have hc0 : replicaMultiplicityCharacter x.1.1 x.2.1 1 = 0 := by
            simpa [fullProjectiveReplicaPairClockCharacter, h] using hz.1
          have hc0' : (x.1.1 1 : ℤ) = (x.2.1 1 : ℤ) := by
            exact sub_eq_zero.mp hc0
          exact_mod_cast hc0'
        · have hk :
              replicaMultiplicityCharacter x.1.1 x.2.1 k.succ.succ = 0 := by
            simpa [fullProjectiveReplicaPairRatioCharacter, h] using congrFun hz.2 k
          have hk' : (x.1.1 k.succ.succ : ℤ) =
              (x.2.1 k.succ.succ : ℤ) := by
            exact sub_eq_zero.mp hk
          exact_mod_cast hk'
      have hpSum := (Finset.mem_piAntidiag.mp x.1.2).1
      have hqSum := (Finset.mem_piAntidiag.mp x.2.2).1
      rw [Fin.sum_univ_succ] at hpSum hqSum
      have hanchor : x.1.1 0 = x.2.1 0 := by omega
      simp [replicaMultiplicityCharacter, hanchor]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [fullProjectiveReplicaPairClockCharacter, h] using hz.1
      · simpa [fullProjectiveReplicaPairRatioCharacter, h] using congrFun hz.2 k

theorem replicaMultiplicityEnergy_fullProjectiveFrequency_sub
    (y : Fin n → ℝ) (p q : Fin (n + 2) → ℕ) :
    replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) p -
        replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) q =
      KleinbockMargulis.dotProd
          (fun j => replicaMultiplicityCharacter p q j.succ.succ) y +
        (replicaMultiplicityCharacter p q 1 : ℝ) := by
  rw [← finiteTorusCharacterDetuning_replicaMultiplicityCharacter]
  unfold finiteTorusCharacterDetuning KleinbockMargulis.dotProd
    replicaMultiplicityCharacter anchoredFullProjectiveFrequency
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
  rw [Fin.sum_univ_succ]
  simp only [fullProjectiveFrequency, Fin.cons_zero, Fin.cons_succ, mul_one]
  rw [show (Fin.succ 0 : Fin (n + 2)) = 1 by rfl]
  ring

theorem twistedFiniteSpectralFidelity_fullProjective_eq_diagonal_add_packet
    (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ)
    (r : ℕ) (y : Fin n → ℝ) (t : ℝ) :
    twistedFiniteSpectralFidelity weight (anchoredFullProjectiveFrequency y) twist t ^ r =
      fullProjectiveReplicaTwistedDiagonal weight twist r +
        ∑ x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r,
          fullProjectiveReplicaPairCoefficient weight twist r x *
            Complex.exp ((t : ℂ) *
              ((KleinbockMargulis.dotProd
                    (fullProjectiveReplicaPairRatioCharacter x) y +
                  (fullProjectiveReplicaPairClockCharacter x : ℝ) : ℝ) : ℂ) *
                Complex.I) := by
  classical
  rw [twistedFiniteSpectralFidelity_pow_expansion]
  have houter :
      (∑ p ∈ Finset.univ.piAntidiag r,
        ∑ q ∈ Finset.univ.piAntidiag r,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            Complex.exp
              (((t * (replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) p -
                replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) q) : ℝ) : ℂ) *
                Complex.I)) =
      ∑ p : FullProjectiveReplicaLayer n r,
        ∑ q : FullProjectiveReplicaLayer n r,
          (fidelityReplicaMultiplicityWeight weight p.1 q.1 : ℂ) *
            replicaMultiplicityTwist twist p.1 q.1 *
            Complex.exp
              (((t * (replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) p.1 -
                replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) q.1) : ℝ) : ℂ) *
                Complex.I) := by
    rw [Finset.sum_subtype (Finset.univ.piAntidiag r) (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro p hp
    exact Finset.sum_subtype (Finset.univ.piAntidiag r)
      (fun _ => Iff.rfl) _
  rw [houter, Fintype.sum_prod_type]
  unfold fullProjectiveReplicaTwistedDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hdiag :
      (fidelityReplicaMultiplicityWeight weight p.1 p.1 : ℂ) *
          replicaMultiplicityTwist twist p.1 p.1 =
        ∑ q : FullProjectiveReplicaLayer n r,
          if p.1 = q.1 then
            (fidelityReplicaMultiplicityWeight weight p.1 q.1 : ℂ) *
              replicaMultiplicityTwist twist p.1 q.1 *
              Complex.exp
                (((t * (replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) p.1 -
                  replicaMultiplicityEnergy (anchoredFullProjectiveFrequency y) q.1) : ℝ) : ℂ) *
                  Complex.I)
          else 0 := by
    simp
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpq : p.1 = q.1
  · simp [hpq, fullProjectiveReplicaPairCoefficient]
  · simp only [hpq, if_false, fullProjectiveReplicaPairCoefficient,
      fullProjectiveReplicaPairClockCharacter,
      fullProjectiveReplicaPairRatioCharacter]
    rw [replicaMultiplicityEnergy_fullProjectiveFrequency_sub]
    push_cast
    ring

def fullProjectiveReplicaAffineMultiplicativeCost
    (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ)
    (r : ℕ) (eps : ℝ) : ℝ :=
  KleinbockMargulis.indexedMultiplicativeFourierL1Cost
    (fun x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r =>
      fullProjectiveReplicaPairCoefficient weight twist r x)
    fullProjectiveReplicaPairRatioCharacter eps

theorem norm_fullProjectiveReplicaTwistedDiagonal_le_floor
    {weight : Fin (n + 2) → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    {twist : Fin (n + 2) → ℂ} (htwist : ∀ i, ‖twist i‖ = 1)
    (r : ℕ) :
    ‖fullProjectiveReplicaTwistedDiagonal weight twist r‖ ≤
      fidelityReplicaPermutationFloor weight r := by
  classical
  unfold fullProjectiveReplicaTwistedDiagonal
  calc
    ‖∑ p : FullProjectiveReplicaLayer n r,
        (fidelityReplicaMultiplicityWeight weight p.1 p.1 : ℂ) *
          replicaMultiplicityTwist twist p.1 p.1‖ ≤
      ∑ p : FullProjectiveReplicaLayer n r,
        ‖(fidelityReplicaMultiplicityWeight weight p.1 p.1 : ℂ) *
          replicaMultiplicityTwist twist p.1 p.1‖ := norm_sum_le _ _
    _ = ∑ p : FullProjectiveReplicaLayer n r,
        fidelityReplicaMultiplicityWeight weight p.1 p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hweight p.1 p.1),
        norm_replicaMultiplicityTwist htwist, mul_one]
    _ = fidelityReplicaPermutationFloor weight r := by
      unfold fidelityReplicaPermutationFloor
      symm
      exact Finset.sum_subtype (Finset.univ.piAntidiag r)
        (fun _ => Iff.rfl) _

private theorem nat_le_two_pow_self (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m + 1 ≤ 2 ^ m + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ (m + 1) := by rw [pow_succ]; omega

/-- Replica-mass height law: a ratio character assembled from two order-`r`
sheets has multiplicative height at most `4^r`, independently of ambient
spectral dimension. -/
theorem fullProjectiveReplicaPairRatioCharacter_piPlus_le_four_pow
    (x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r) :
    KleinbockMargulis.PiPlus (fullProjectiveReplicaPairRatioCharacter x) ≤
      (4 : ℝ) ^ r := by
  classical
  by_cases hpq : x.1.1 = x.2.1
  · simp only [fullProjectiveReplicaPairRatioCharacter, hpq, if_pos,
      KleinbockMargulis.PiPlus, Pi.zero_apply, Int.cast_zero, abs_zero,
      max_eq_right zero_le_one, Finset.prod_const_one]
    simpa using (pow_le_pow_right₀ (a := (4 : ℝ)) (by norm_num) (Nat.zero_le r))
  · let p := x.1.1
    let q := x.2.1
    have hpoint : ∀ j : Fin n,
        max |(fullProjectiveReplicaPairRatioCharacter x j : ℝ)| 1 ≤
          (2 : ℝ) ^ (p j.succ.succ + q j.succ.succ) := by
      intro j
      have hlocalR :
          |(replicaMultiplicityCharacter p q j.succ.succ : ℝ)| ≤
            (p j.succ.succ + q j.succ.succ : ℝ) := by
        simp only [replicaMultiplicityCharacter]
        rw [abs_le]
        have hp0 : (0 : ℝ) ≤ p j.succ.succ := Nat.cast_nonneg _
        have hq0 : (0 : ℝ) ≤ q j.succ.succ := Nat.cast_nonneg _
        constructor <;> push_cast <;> linarith
      have hpowR :
          (p j.succ.succ + q j.succ.succ : ℝ) ≤
            (2 : ℝ) ^ (p j.succ.succ + q j.succ.succ) := by
        exact_mod_cast nat_le_two_pow_self
          (p j.succ.succ + q j.succ.succ)
      apply max_le
      · simpa [fullProjectiveReplicaPairRatioCharacter, hpq, p, q] using
          hlocalR.trans hpowR
      · exact_mod_cast Nat.one_le_two_pow
          (n := p j.succ.succ + q j.succ.succ)
    have hpSum := (Finset.mem_piAntidiag.mp x.1.2).1
    have hqSum := (Finset.mem_piAntidiag.mp x.2.2).1
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hpSum hqSum
    have htail :
        (∑ j : Fin n, (p j.succ.succ + q j.succ.succ)) ≤ 2 * r := by
      rw [Finset.sum_add_distrib]
      dsimp [p, q]
      omega
    rw [KleinbockMargulis.PiPlus]
    calc
      (∏ j, max |(fullProjectiveReplicaPairRatioCharacter x j : ℝ)| 1) ≤
          ∏ j : Fin n, (2 : ℝ) ^ ((p j.succ.succ) + (q j.succ.succ)) := by
        exact Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hpoint j)
      _ = (2 : ℝ) ^
          (∑ j : Fin n, (p j.succ.succ + q j.succ.succ)) := by
        simp only [Finset.prod_pow_eq_pow_sum]
      _ ≤ (2 : ℝ) ^ (2 * r) := pow_le_pow_right₀ (by norm_num) htail
      _ = (4 : ℝ) ^ r := by
        rw [show 2 * r = r + r by omega, pow_add, ← mul_pow]
        norm_num

theorem fullProjectiveReplicaAffineMultiplicativeCost_le
    {weight : Fin (n + 2) → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    {twist : Fin (n + 2) → ℂ} (htwist : ∀ i, ‖twist i‖ = 1)
    (r : ℕ) {eps : ℝ} (heps : 0 ≤ eps) :
    fullProjectiveReplicaAffineMultiplicativeCost weight twist r eps ≤
      (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
  classical
  let B : ℝ := 4
  let W : ℝ := B ^ ((r : ℝ) * (1 + eps))
  have hB : 0 < B := by dsimp [B]; positivity
  have hW : 0 ≤ W := Real.rpow_nonneg hB.le _
  have hratio : ∀ x : FullProjectiveReplicaLayer n r ×
      FullProjectiveReplicaLayer n r,
      KleinbockMargulis.PiPlus
          (fullProjectiveReplicaPairRatioCharacter x) /
        KleinbockMargulis.PiPlus
            (fullProjectiveReplicaPairRatioCharacter x) ^ (-eps) ≤ W := by
    intro x
    let P := KleinbockMargulis.PiPlus
      (fullProjectiveReplicaPairRatioCharacter x)
    have hPpos : 0 < P := KleinbockMargulis.PiPlus_pos _
    have hPle : P ≤ B ^ r := by
      simpa [P, B] using fullProjectiveReplicaPairRatioCharacter_piPlus_le_four_pow x
    rw [div_rpow_neg_eq_rpow_one_add hPpos]
    calc
      P ^ (1 + eps) ≤ (B ^ r) ^ (1 + eps) :=
        Real.rpow_le_rpow hPpos.le hPle (by linarith)
      _ = W := by
        dsimp [W]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
  have hcoefficient :
      (∑ x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r,
          ‖fullProjectiveReplicaPairCoefficient weight twist r x‖) ≤ 1 := by
    calc
      (∑ x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r,
          ‖fullProjectiveReplicaPairCoefficient weight twist r x‖) ≤
        ∑ x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r,
          fidelityReplicaMultiplicityWeight weight x.1.1 x.2.1 := by
            refine Finset.sum_le_sum fun x _ => ?_
            by_cases hpq : x.1.1 = x.2.1
            · simp [fullProjectiveReplicaPairCoefficient, hpq,
                fidelityReplicaMultiplicityWeight_nonneg hweight]
            · rw [fullProjectiveReplicaPairCoefficient, if_neg hpq,
                norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg
                  (fidelityReplicaMultiplicityWeight_nonneg hweight x.1.1 x.2.1),
                norm_replicaMultiplicityTwist htwist, mul_one]
      _ = (∑ p ∈ Finset.univ.piAntidiag r,
          ∑ q ∈ Finset.univ.piAntidiag r,
            fidelityReplicaMultiplicityWeight weight p q) := by
            rw [Fintype.sum_prod_type]
            symm
            rw [Finset.sum_subtype (Finset.univ.piAntidiag r) (fun _ => Iff.rfl)]
            apply Finset.sum_congr rfl
            intro p hp
            exact Finset.sum_subtype (Finset.univ.piAntidiag r)
              (fun _ => Iff.rfl) _
      _ = (∑ i, weight i) ^ (2 * r) :=
        sum_fidelityReplicaMultiplicityWeight_eq_sum_pow weight r
      _ ≤ 1 := by
        have hsumNonneg : 0 ≤ ∑ i, weight i :=
          Finset.sum_nonneg fun i hi => hweight i
        exact pow_le_one₀ hsumNonneg hweightSum
  unfold fullProjectiveReplicaAffineMultiplicativeCost
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost
  calc
    (∑ x, ‖fullProjectiveReplicaPairCoefficient weight twist r x‖ *
        (KleinbockMargulis.PiPlus
              (fullProjectiveReplicaPairRatioCharacter x) /
          KleinbockMargulis.PiPlus
              (fullProjectiveReplicaPairRatioCharacter x) ^ (-eps))) ≤
      ∑ x, ‖fullProjectiveReplicaPairCoefficient weight twist r x‖ * W := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (hratio x) (norm_nonneg _)
    _ = (∑ x, ‖fullProjectiveReplicaPairCoefficient weight twist r x‖) * W := by
      rw [Finset.sum_mul]
    _ ≤ 1 * W := mul_le_mul_of_nonneg_right hcoefficient hW
    _ = (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
      simp [W, B]

/-- One affine-character constant controls every finite indexed packet,
independently of packet cardinality and hence independently of replica order. -/
theorem indexedAffineFourierPacketHaarDiscrepancy_of_characterSuppression
    {ι : Type*} [Fintype ι] {y : Fin n → ℝ} {eps C : ℝ}
    (hchar : ∀ (p : ℤ) (q : Fin n → ℤ),
      (p ≠ 0 ∨ q ≠ 0) → ∀ u T : ℝ, 0 < T →
        ‖(1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              Complex.exp ((t : ℂ) *
                ((KleinbockMargulis.dotProd q y + (p : ℝ) : ℝ) : ℂ) *
                  Complex.I)‖ *
            KleinbockMargulis.PiPlus q ^ (-eps) ≤
          2 * C * KleinbockMargulis.PiPlus q / T)
    (a0 : ℂ) (c : ι → ℂ) (p : ι → ℤ) (q : ι → Fin n → ℤ)
    (hpq : ∀ i, p i ≠ 0 ∨ q i ≠ 0) (u T : ℝ) (hT : 0 < T) :
    ‖((1 / (T : ℂ)) *
        ∫ t in u..(u + T),
          (a0 + ∑ i, c i * Complex.exp
            ((t : ℂ) *
              ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                Complex.I))) - a0‖ ≤
      (2 * C / T) *
        KleinbockMargulis.indexedMultiplicativeFourierL1Cost c q eps := by
  classical
  have hsplit :
      (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                  Complex.I) =
        ∑ i, c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                Complex.I)) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [intervalIntegral.integral_const_mul]
        ring
    · intro i hi
      exact (intervalIntegrable_exp_mode
        (KleinbockMargulis.dotProd (q i) y + (p i : ℝ)) u T).const_mul (c i)
  have hosc :
      ‖(1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                  Complex.I)‖ ≤
        (2 * C / T) *
          KleinbockMargulis.indexedMultiplicativeFourierL1Cost c q eps := by
    rw [hsplit]
    calc
      ‖∑ i, c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                Complex.I))‖ ≤
        ∑ i, ‖c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                Complex.I))‖ := norm_sum_le _ _
      _ ≤ ∑ i, (2 * C / T) *
          (‖c i‖ * (KleinbockMargulis.PiPlus (q i) /
            KleinbockMargulis.PiPlus (q i) ^ (-eps))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw : 0 < KleinbockMargulis.PiPlus (q i) ^ (-eps) :=
          Real.rpow_pos_of_pos (KleinbockMargulis.PiPlus_pos (q i)) _
        have hi := hchar (p i) (q i) (hpq i) u T hT
        have hmean :
            ‖(1 / (T : ℂ)) *
                ∫ t in u..(u + T),
                  Complex.exp ((t : ℂ) *
                    ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                      Complex.I)‖ ≤
              (2 * C * KleinbockMargulis.PiPlus (q i) / T) /
                KleinbockMargulis.PiPlus (q i) ^ (-eps) :=
          (le_div_iff₀ hw).2 hi
        rw [norm_mul]
        calc
          ‖c i‖ *
              ‖(1 / (T : ℂ)) *
                ∫ t in u..(u + T),
                  Complex.exp ((t : ℂ) *
                    ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                      Complex.I)‖ ≤
            ‖c i‖ * ((2 * C * KleinbockMargulis.PiPlus (q i) / T) /
              KleinbockMargulis.PiPlus (q i) ^ (-eps)) :=
            mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
          _ = (2 * C / T) *
              (‖c i‖ * (KleinbockMargulis.PiPlus (q i) /
                KleinbockMargulis.PiPlus (q i) ^ (-eps))) := by ring
      _ = (2 * C / T) *
          KleinbockMargulis.indexedMultiplicativeFourierL1Cost c q eps := by
        rw [KleinbockMargulis.indexedMultiplicativeFourierL1Cost,
          Finset.mul_sum]
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) *
          ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
            Complex.I)) MeasureTheory.volume u (u + T) := by
    have hcont : Continuous fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) *
          ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
            Complex.I) := by
      refine continuous_finsetSum _ fun i _ => ?_
      fun_prop
    exact hcont.intervalIntegrable u (u + T)
  have hcenter :
      ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a0 + ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                  Complex.I))) - a0 =
        (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                  Complex.I) := by
    let J : ℂ := ∫ t in u..(u + T),
      ∑ i, c i * Complex.exp
        ((t : ℂ) *
          ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
            Complex.I)
    have hadd :
        (∫ t in u..(u + T),
          (a0 + ∑ i, c i * Complex.exp
            ((t : ℂ) *
              ((KleinbockMargulis.dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) *
                Complex.I))) = (T : ℂ) * a0 + J := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
    rw [hadd]
    change (1 / (T : ℂ)) * ((T : ℂ) * a0 + J) - a0 =
      (1 / (T : ℂ)) * J
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
    field_simp
    ring
  rw [hcenter]
  exact hosc

theorem exists_uniform_windowMean_twistedFidelity_fullProjective_le
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ)
        (r : ℕ),
        (∀ i, 0 ≤ weight i) → (∑ i, weight i ≤ 1) →
        (∀ i, ‖twist i‖ = 1) →
        ∀ u T : ℝ, 0 < T →
          ‖(1 / (T : ℂ)) * ∫ t in u..(u + T),
              twistedFiniteSpectralFidelity weight
                (anchoredFullProjectiveFrequency y) twist t ^ r‖ ≤
            (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r +
              (2 * C / T) *
                (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
  classical
  obtain ⟨C, hC, hchar⟩ :=
    KleinbockMargulis.exists_global_affineCharacterWindowSuppression hy heps
  refine ⟨C, hC, ?_⟩
  intro weight twist r hweight hweightSum htwist u T hT
  have hdisc := indexedAffineFourierPacketHaarDiscrepancy_of_characterSuppression
    (n := n) (y := y) (eps := eps) (C := C) hchar
    (fullProjectiveReplicaTwistedDiagonal weight twist r)
    (fun x => fullProjectiveReplicaPairCoefficient weight twist r x)
    fullProjectiveReplicaPairClockCharacter
    fullProjectiveReplicaPairRatioCharacter
    fullProjectiveReplicaPairCharacter_nonconstant u T hT
  have hInt :
      (∫ t in u..(u + T),
          twistedFiniteSpectralFidelity weight
            (anchoredFullProjectiveFrequency y) twist t ^ r) =
        ∫ t in u..(u + T),
          (fullProjectiveReplicaTwistedDiagonal weight twist r +
            ∑ x : FullProjectiveReplicaLayer n r × FullProjectiveReplicaLayer n r,
              fullProjectiveReplicaPairCoefficient weight twist r x *
                Complex.exp ((t : ℂ) *
                  ((KleinbockMargulis.dotProd
                        (fullProjectiveReplicaPairRatioCharacter x) y +
                      (fullProjectiveReplicaPairClockCharacter x : ℝ) : ℝ) : ℂ) *
                    Complex.I)) :=
    intervalIntegral.integral_congr fun t _ =>
      twistedFiniteSpectralFidelity_fullProjective_eq_diagonal_add_packet
        weight twist r y t
  rw [← hInt] at hdisc
  have hcost := fullProjectiveReplicaAffineMultiplicativeCost_le
    hweight hweightSum htwist r heps.le
  have hfactor : 0 ≤ 2 * C / T := by
    have : 0 ≤ C := le_trans zero_le_one hC
    positivity
  have herr :
      (2 * C / T) *
          fullProjectiveReplicaAffineMultiplicativeCost weight twist r eps ≤
        (2 * C / T) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) :=
    mul_le_mul_of_nonneg_left hcost hfactor
  have hdiag :
      ‖fullProjectiveReplicaTwistedDiagonal weight twist r‖ ≤
        (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r :=
    (norm_fullProjectiveReplicaTwistedDiagonal_le_floor hweight htwist r).trans
      (fidelityReplicaPermutationFloor_le_factorial_mul_sqMoment hweight r)
  let M : ℂ :=
    (1 / (T : ℂ)) * ∫ t in u..(u + T),
      twistedFiniteSpectralFidelity weight
        (anchoredFullProjectiveFrequency y) twist t ^ r
  have htriangle :
      ‖M‖ ≤
        ‖M - fullProjectiveReplicaTwistedDiagonal weight twist r‖ +
          ‖fullProjectiveReplicaTwistedDiagonal weight twist r‖ := by
    calc
      ‖M‖ = ‖(M - fullProjectiveReplicaTwistedDiagonal weight twist r) +
          fullProjectiveReplicaTwistedDiagonal weight twist r‖ := by
        congr 1
        ring
      _ ≤ ‖M - fullProjectiveReplicaTwistedDiagonal weight twist r‖ +
          ‖fullProjectiveReplicaTwistedDiagonal weight twist r‖ :=
        norm_add_le _ _
  change ‖M‖ ≤ _
  calc
    ‖M‖ ≤
        ‖M - fullProjectiveReplicaTwistedDiagonal weight twist r‖ +
          ‖fullProjectiveReplicaTwistedDiagonal weight twist r‖ := htriangle
    _ ≤ (2 * C / T) *
          fullProjectiveReplicaAffineMultiplicativeCost weight twist r eps +
        (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r :=
      add_le_add hdisc hdiag
    _ ≤ (2 * C / T) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) +
        (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r :=
      add_le_add herr (le_refl _)
    _ = (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r +
        (2 * C / T) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by ring

theorem twistedFiniteSpectralFidelity_scaledAnchoredFullProjective
    (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ)
    (g t : ℝ) (y : Fin n → ℝ) :
    twistedFiniteSpectralFidelity weight
        (fun i => g * anchoredFullProjectiveFrequency y i) twist t =
      twistedFiniteSpectralFidelity weight
        (anchoredFullProjectiveFrequency y) twist (g * t) := by
  unfold twistedFiniteSpectralFidelity twistedFiniteSpectralAmplitude
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  congr 1
  push_cast
  ring

/-- Physical clock scaling costs exactly inverse elapsed clock time `1/(gT)`;
the Diophantine constant remains uniform in target and replica order. -/
theorem exists_uniform_windowMean_twistedFidelity_clockScaledFullProjective_le
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) {g : ℝ} (hg : 0 < g) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (weight : Fin (n + 2) → ℝ) (twist : Fin (n + 2) → ℂ)
        (r : ℕ),
        (∀ i, 0 ≤ weight i) → (∑ i, weight i ≤ 1) →
        (∀ i, ‖twist i‖ = 1) →
        ∀ u T : ℝ, 0 < T →
          ‖(1 / (T : ℂ)) * ∫ t in u..(u + T),
              twistedFiniteSpectralFidelity weight
                (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r‖ ≤
            (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r +
              (2 * C / (g * T)) *
                (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_windowMean_twistedFidelity_fullProjective_le hy heps
  refine ⟨C, hC, ?_⟩
  intro weight twist r hweight hweightSum htwist u T hT
  have hmain := hbase weight twist r hweight hweightSum htwist
    (g * u) (g * T) (mul_pos hg hT)
  have hpoint : ∀ t : ℝ,
      twistedFiniteSpectralFidelity weight
          (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r =
        twistedFiniteSpectralFidelity weight
          (anchoredFullProjectiveFrequency y) twist (g * t) ^ r := by
    intro t
    rw [twistedFiniteSpectralFidelity_scaledAnchoredFullProjective]
  have hscale := intervalIntegral.integral_comp_mul_left
    (fun s : ℝ => twistedFiniteSpectralFidelity weight
      (anchoredFullProjectiveFrequency y) twist s ^ r) hg.ne'
    (a := u) (b := u + T)
  have hmean :
      (1 / (T : ℂ)) * ∫ t in u..(u + T),
          twistedFiniteSpectralFidelity weight
            (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r =
        (1 / ((g * T : ℝ) : ℂ)) * ∫ s in (g * u)..(g * u + g * T),
          twistedFiniteSpectralFidelity weight
            (anchoredFullProjectiveFrequency y) twist s ^ r := by
    rw [intervalIntegral.integral_congr fun t _ => hpoint t, hscale]
    rw [show g * (u + T) = g * u + g * T by ring]
    rw [Complex.real_smul]
    push_cast
    field_simp [hg.ne']
  rw [hmean]
  simpa only [mul_assoc] using hmain

end

end GaloisForLFunctions.HTGeometry
