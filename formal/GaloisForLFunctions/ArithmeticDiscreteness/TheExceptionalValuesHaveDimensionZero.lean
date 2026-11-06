import GaloisForLFunctions.ArithmeticDiscreteness.HigherTaylorPolynomialsCoverNearCoincidences
import GaloisForLFunctions.ArithmeticDiscreteness.TheExceptionalValuesHaveSmallHausdorffDimension

/-!+# Nonrepelling values have Hausdorff dimension zero

For a holomorphic function of polynomial strip growth, values with no polynomial separation
law for their distinct preimages form a set of Hausdorff dimension zero. Higher Taylor
polynomials replace a quadratic image cover by covers of arbitrary order.
-/

open Complex Metric Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- Critical-value centres of degree-`k` Taylor polynomials on the dyadic strip mesh. -/
def higherValueCentres (F : ℂ → ℂ) (α β : ℝ) (k D n : ℕ) : Finset ℂ := by
  classical
  exact (gridIdx α β D n).biUnion fun p =>
    polynomialCriticalCentres
      (originTaylorPolynomial (fun z => F (gridPt α D n p + z)) k) 0

/-- The common image radius supplied by polynomial strip growth. -/
def higherValueRadius (A : ℝ) (B k D n : ℕ) : ℝ :=
  nearCoincidenceCoverConstant k * A * (4 + (heightCap D n : ℝ)) ^ B *
    (1 / (2 : ℝ) ^ n) ^ (k + 1)

/-- A finite cover of the common values of sufficiently close pairs. -/
def higherBadValues (F : ℂ → ℂ) (α β A : ℝ) (B k D n : ℕ) : Set ℂ :=
  ⋃ a ∈ higherValueCentres F α β k D n, closedBall a (higherValueRadius A B k D n)

theorem higherValueCentres_card_le (F : ℂ → ℂ) (α β : ℝ) (k D n : ℕ) :
    (higherValueCentres F α β k D n).card ≤ (gridIdx α β D n).card * (k + 1) := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  calc
    (∑ p ∈ gridIdx α β D n,
        (polynomialCriticalCentres
          (originTaylorPolynomial (fun z => F (gridPt α D n p + z)) k) 0).card)
        ≤ ∑ _p ∈ gridIdx α β D n, (k + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (polynomialCriticalCentres_card_le _ _).trans
        (Nat.add_le_add_right (originTaylorPolynomial_natDegree_le _ _) 1)
    _ = _ := by simp

/-- Each close pair belongs to the higher-order cover at its scale and height cap. -/
theorem mem_higherBadValues {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {α β A : ℝ} {B k D n : ℕ}
    (hA : 0 ≤ A) (hk : 1 ≤ k) (hn : 6 ≤ n)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧
        ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {a s s' : ℂ} (hs : F s = a) (hs' : F s' = a) (hne : s ≠ s')
    (hre0 : α ≤ s.re) (hre1 : s.re ≤ β) (him0 : 3 ≤ |s.im|)
    (him1 : |s.im| ≤ heightCap D n)
    (hd : ‖s' - s‖ ≤ (1 / (2 : ℝ) ^ n) ^ k) :
    a ∈ higherBadValues F α β A B k D n := by
  classical
  let h : ℝ := 1 / (2 : ℝ) ^ n
  have hh0 : 0 < h := by dsimp [h]; positivity
  have hh : h ≤ 1 / 64 := by
    have hp : (2 : ℝ) ^ 6 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    exact one_div_le_one_div_of_le (by norm_num) (by norm_num at hp ⊢; exact hp)
  obtain ⟨p, hp, hsp⟩ := exists_gridPt_near (β := β) D n
    (by linarith : α - 1 ≤ s.re) (by linarith : s.re ≤ β + 1) him1
  let q := gridPt α D n p
  have hsq : ‖s - q‖ ≤ 2 * h := by
    simpa only [q, h, div_eq_mul_inv, one_mul] using hsp
  have hqr := (abs_re_le_norm (s - q)).trans hsq
  have hqi := (abs_im_le_norm (s - q)).trans hsq
  rw [sub_re] at hqr
  rw [sub_im] at hqi
  have hqi1 := abs_sub_abs_le_abs_sub s.im q.im
  have hqi2 := abs_sub_abs_le_abs_sub q.im s.im
  rw [abs_sub_comm] at hqi2
  have hqre0 : α - 1 ≤ q.re := by linarith [(abs_le.mp hqr).2]
  have hqre1 : q.re ≤ β + 1 := by linarith [(abs_le.mp hqr).1]
  have hqim0 : 2 ≤ |q.im| := by linarith only [hqi1, hqi, him0, hh]
  have hqim1 : |q.im| ≤ (heightCap D n : ℝ) + 1 := by
    linarith only [hqi2, hqi, him1, hh]
  obtain ⟨hqU, hqM⟩ := hM q hqre0 hqre1 hqim0
  let g : ℂ → ℂ := fun z => F (q + z)
  let M : ℝ := A * (4 + (heightCap D n : ℝ)) ^ B
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have htranslate : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), q + z ∈ closedBall q (1 / 2) := by
    intro z hz
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hg : DifferentiableOn ℂ g (ball 0 (1 / 2)) := by
    intro z hz
    exact ((hF.differentiableAt (hU.mem_nhds (hqU
      (htranslate z (ball_subset_closedBall hz))))).comp z
        ((hasDerivAt_id z).const_add q).differentiableAt).differentiableWithinAt
  have hgM : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖g z‖ ≤ M := by
    intro z hz
    refine (hqM (q + z) (htranslate z hz)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hqim1]) B
  have hgs : g (s - q) = a := by
    dsimp [g]
    rwa [show q + (s - q) = s by ring]
  have hgs' : g (s' - q) = a := by
    dsimp [g]
    rwa [show q + (s' - q) = s' by ring]
  obtain ⟨v, hv, hval⟩ := close_pair_value_near_taylorCriticalCentre hg hM0 hgM hh0 hh hk
    hsq (hgs.trans hgs'.symm) (by
      intro he
      apply hne
      simpa only [sub_add_cancel] using congrArg (fun w : ℂ => w + q) he)
    (show ‖(s' - q) - (s - q)‖ ≤ h ^ k by
      rw [show (s' - q) - (s - q) = s' - s by ring]
      exact hd)
  apply mem_iUnion₂.mpr
  refine ⟨v, Finset.mem_biUnion.mpr ⟨p, hp, hv⟩, ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  simpa only [hgs, higherValueRadius, M, h, mul_assoc] using hval

/-- Avoiding the higher-order covers gives a polynomial separation exponent `kD`. -/
theorem polynomialValueRepulsion_of_eventually_notMem_higherBadValues
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B k D : ℕ} (hA : 0 ≤ A) (hk : 1 ≤ k) (hD : 0 < D)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧
        ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {a : ℂ} (ha : ∀ᶠ n in atTop, a ∉ higherBadValues F α β A B k D n) :
    PolynomialValueRepulsion F α β a := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ha
  let N := max n₀ 6
  have hN6 : 6 ≤ N := le_max_right _ _
  have havoid : ∀ n, N ≤ n → a ∉ higherBadValues F α β A B k D n :=
    fun n hn => hn₀ n ((le_max_left _ _).trans hn)
  let κ : ℝ := min (1 / 64) (min (1 / (2 : ℝ) ^ (k * N)) (1 / (2 : ℝ) ^ (k * D)))
  refine ⟨k * D, κ, by dsimp [κ]; positivity, ?_⟩
  intro s s' hs hs' hne hre0 hre1 him
  let d := ‖s' - s‖
  have hd0 : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hX1 : 1 ≤ (2 + |s.im|) ^ (k * D) := one_le_pow₀ (by linarith [abs_nonneg s.im])
  have hX0 : 0 < (2 + |s.im|) ^ (k * D) := by positivity
  have hκX : κ / (2 + |s.im|) ^ (k * D) ≤ κ := div_le_self (by dsimp [κ]; positivity) hX1
  by_cases hfar : 1 / 64 < d
  · exact hκX.trans ((min_le_left _ _).trans hfar.le)
  push Not at hfar
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := 1 / d) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hd0]; linarith only [hfar]) (by norm_num)
  have hdj1 : d ≤ 1 / (2 : ℝ) ^ j := by
    rw [le_div_iff₀ hd0] at hj1
    rw [le_div_iff₀ (by positivity)]
    linarith only [hj1, mul_comm d ((2 : ℝ) ^ j)]
  have hdj0 : 1 / (2 : ℝ) ^ (j + 1) < d := by
    rw [div_lt_iff₀ hd0] at hj2
    rw [div_lt_iff₀ (by positivity)]
    linarith only [hj2, mul_comm d ((2 : ℝ) ^ (j + 1))]
  let n := j / k
  have hkn : k * n ≤ j := by
    simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self j k
  have hjn : j + 1 ≤ k * (n + 1) := by
    apply Nat.succ_le_iff.mpr
    simpa only [n, Nat.mul_add, Nat.mul_one, Nat.mul_comm] using
      Nat.lt_div_mul_add (a := j) (b := k) (by omega : 0 < k)
  have hdn : d ≤ (1 / (2 : ℝ) ^ n) ^ k := by
    calc d ≤ 1 / (2 : ℝ) ^ j := hdj1
      _ ≤ 1 / (2 : ℝ) ^ (k * n) := one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hkn)
      _ = (1 / (2 : ℝ) ^ n) ^ k := by
        simp only [div_pow, one_pow, ← pow_mul, Nat.mul_comm]
  by_cases hcap : |s.im| ≤ heightCap D n
  · have hnN : n < N := by
      by_contra hnot
      have hNn : N ≤ n := le_of_not_gt hnot
      exact havoid n hNn (mem_higherBadValues hU hF hA hk (hN6.trans hNn) hM
        hs hs' hne hre0 hre1 him hcap hdn)
    have hjN : j + 1 ≤ k * N := hjn.trans (Nat.mul_le_mul_left k (Nat.succ_le_of_lt hnN))
    have hscale : 1 / (2 : ℝ) ^ (k * N) ≤ 1 / (2 : ℝ) ^ (j + 1) :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hjN)
    exact hκX.trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (hscale.trans hdj0.le)))
  · push Not at hcap
    have hnD : n + 1 ≤ D * (n / D) + D := by
      have ht := Nat.lt_div_mul_add (a := n) (b := D) hD
      linarith only [ht, Nat.mul_comm (n / D) D]
    have hjD : j + 1 ≤ (k * D) * (n / D) + k * D := by
      calc j + 1 ≤ k * (n + 1) := hjn
        _ ≤ k * (D * (n / D) + D) := Nat.mul_le_mul_left k hnD
        _ = _ := by ring
    have hcapD : (heightCap D n : ℝ) ^ (k * D) =
        (2 : ℝ) ^ ((k * D) * (n / D)) := by
      rw [heightCap]
      push_cast
      rw [← pow_mul, Nat.mul_comm]
    have hcapX : (heightCap D n : ℝ) ≤ 2 + |s.im| := by linarith only [hcap]
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (k * D) * (2 + |s.im|) ^ (k * D) := by
      calc (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ ((k * D) * (n / D) + k * D) :=
          pow_le_pow_right₀ (by norm_num) hjD
        _ = (2 : ℝ) ^ (k * D) * (heightCap D n : ℝ) ^ (k * D) := by
          rw [hcapD, pow_add, mul_comm]
        _ ≤ (2 : ℝ) ^ (k * D) * (2 + |s.im|) ^ (k * D) := by
          gcongr
    calc
      κ / (2 + |s.im|) ^ (k * D)
          ≤ (1 / (2 : ℝ) ^ (k * D)) / (2 + |s.im|) ^ (k * D) :=
        div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hX0.le
      _ = 1 / ((2 : ℝ) ^ (k * D) * (2 + |s.im|) ^ (k * D)) := by rw [div_div]
      _ ≤ 1 / (2 : ℝ) ^ (j + 1) := one_div_le_one_div_of_le (by positivity) hpow
      _ ≤ d := hdj0.le

/-- Higher Taylor order increases the exponential decay of the image radii. -/
theorem higherValueRadius_le_exp {A : ℝ} (hA : 0 ≤ A) (B k D n : ℕ) :
    higherValueRadius A B k D n ≤
      (nearCoincidenceCoverConstant k * A * 5 ^ B) *
        Real.exp (-(((k : ℝ) + 1) * Real.log 2 - B * (Real.log 2 / D)) * n) := by
  have hY1 : (1 : ℝ) ≤ heightCap D n := by
    rw [heightCap]
    push_cast
    exact one_le_pow₀ (by norm_num)
  have hY : (4 + (heightCap D n : ℝ)) ^ B ≤
      5 ^ B * Real.exp (Real.log 2 / D * n) ^ B := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hy := heightCap_le_exp D n
    linarith only [hY1, hy]
  have hmesh : (1 / (2 : ℝ) ^ n) ^ (k + 1) =
      Real.exp (-(((k : ℝ) + 1) * Real.log 2) * n) := by
    have hp : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hp, one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hC0 := (nearCoincidenceCoverConstant_pos k).le
  rw [higherValueRadius, hmesh]
  calc
    nearCoincidenceCoverConstant k * A * (4 + (heightCap D n : ℝ)) ^ B *
        Real.exp (-(((k : ℝ) + 1) * Real.log 2) * n)
        ≤ nearCoincidenceCoverConstant k * A *
          (5 ^ B * Real.exp (Real.log 2 / D * n) ^ B) *
            Real.exp (-(((k : ℝ) + 1) * Real.log 2) * n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY (mul_nonneg hC0 hA))
        (Real.exp_pos _).le
    _ = (nearCoincidenceCoverConstant k * A * 5 ^ B) *
        (Real.exp ((B : ℝ) * (Real.log 2 / D * n)) *
          Real.exp (-(((k : ℝ) + 1) * Real.log 2) * n)) := by
      rw [← Real.exp_nat_mul]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Nonrepelling values of a holomorphic function of polynomial strip growth have zero
Hausdorff measure in every positive dimension. -/
theorem hausdorffMeasure_nonrepellingValues_eq_zero_of_pos
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {α β A : ℝ} {B : ℕ} (hαβ : α ≤ β) (hA : 0 ≤ A)
    (hM : ∀ c : ℂ, α - 1 ≤ c.re → c.re ≤ β + 1 → 2 ≤ |c.im| →
      closedBall c (1 / 2) ⊆ U ∧
        ∀ z ∈ closedBall c (1 / 2), ‖F z‖ ≤ A * (2 + |c.im|) ^ B)
    {s : ℝ} (hs : 0 < s) :
    μH[s] {a | ¬ PolynomialValueRepulsion F α β a} = 0 := by
  classical
  obtain ⟨k, hklarge⟩ := exists_nat_gt (max 1 (2 / s))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hklarge
  have hk : 1 ≤ k := by exact_mod_cast hk1.le
  have hks : 2 < ((k : ℝ) + 1) * s := by
    have ht := (le_max_right _ _).trans_lt hklarge
    rw [div_lt_iff₀ hs] at ht
    nlinarith only [ht, hs]
  obtain ⟨D, hDlarge⟩ := exists_nat_gt
    (max 0 ((s * B + 1) / (((k : ℝ) + 1) * s - 2)))
  have hDpos : (0 : ℝ) < D := (le_max_left _ _).trans_lt hDlarge
  have hD : 0 < D := by exact_mod_cast hDpos
  have hchoose : s * B + 1 < (((k : ℝ) + 1) * s - 2) * D := by
    have ht := (le_max_right _ _).trans_lt hDlarge
    rw [div_lt_iff₀ (by linarith only [hks])] at ht
    nlinarith only [ht]
  let ell := Real.log 2
  let e := ell / D
  let a := 2 * ell + e
  let b := ((k : ℝ) + 1) * ell - B * e
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have he : 0 < e := div_pos hell hDpos
  have hDe : (D : ℝ) * e = ell := by dsimp [e]; field_simp
  have hab : a < b * s := by
    have ht := mul_lt_mul_of_pos_right hchoose he
    rw [mul_assoc (((k : ℝ) + 1) * s - 2), hDe] at ht
    dsimp [a, b]
    nlinarith only [ht]
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by nlinarith only [hab, ha, hs]
  let C := (3 * (β - α + 4)) * ((k : ℝ) + 1)
  let R := nearCoincidenceCoverConstant k * A * 5 ^ B
  let r : ℕ → ℝ := fun n => R * Real.exp (-b * n)
  let w : ℕ → ℝ := fun n => (C * (2 * R) ^ s) * Real.exp ((a - b * s) * n)
  have hC : 0 ≤ C := by
    have hβα : 0 ≤ β - α := sub_nonneg.mpr hαβ
    dsimp [C]
    positivity
  have hR : 0 ≤ R := by
    have hc := (nearCoincidenceCoverConstant_pos k).le
    dsimp [R]
    positivity
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_pos (-b)).le (Real.exp_lt_one_iff.mpr (by linarith only [hb]))
    simpa only [r, mul_comm (-b), Real.exp_nat_mul, mul_zero] using hp.const_mul R
  have hsum : Summable w := by
    have ht := (summable_geometric_of_lt_one (Real.exp_pos (a - b * s)).le
      (Real.exp_lt_one_iff.mpr (sub_neg.mpr hab))).mul_left (C * (2 * R) ^ s)
    simpa only [w, mul_comm (a - b * s), Real.exp_nat_mul] using ht
  have hcard : ∀ n, ((higherValueCentres F α β k D n).card : ℝ) ≤ C * Real.exp (a * n) := by
    intro n
    have hc : ((higherValueCentres F α β k D n).card : ℝ) ≤
        ((gridIdx α β D n).card : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast higherValueCentres_card_le F α β k D n
    calc ((higherValueCentres F α β k D n).card : ℝ)
        ≤ ((gridIdx α β D n).card : ℝ) * ((k : ℝ) + 1) := hc
      _ ≤ (3 * (β - α + 4) * Real.exp (a * n)) * ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (gridIdx_card_le_exp hαβ D n) (by positivity)
      _ = C * Real.exp (a * n) := by dsimp [C]; ring
  refine hausdorffMeasure_eq_zero_of_tail_covers _ (higherValueCentres F α β k D)
    (fun _ v => v) r w s hs (fun n => mul_nonneg hR (Real.exp_pos _).le)
    ?_ hrlim (fun n => by dsimp [w]; positivity) hsum ?_ ?_
  · intro n m hnm
    apply mul_le_mul_of_nonneg_left _ hR
    apply Real.exp_le_exp.mpr
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith only [hnm', hb]
  · intro n
    calc ((higherValueCentres F α β k D n).card : ℝ) * (2 * r n) ^ s
        ≤ (C * Real.exp (a * n)) * (2 * r n) ^ s :=
          mul_le_mul_of_nonneg_right (hcard n) (Real.rpow_nonneg (by dsimp [r]; positivity) _)
      _ = w n := by
        dsimp [r, w]
        rw [show 2 * (R * Real.exp (-b * (n : ℝ))) = (2 * R) * Real.exp (-b * n) by ring,
          Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
        rw [show C * Real.exp (a * (n : ℝ)) * ((2 * R) ^ s * Real.exp (-b * n * s)) =
          (C * (2 * R) ^ s) * (Real.exp (a * n) * Real.exp (-b * n * s)) by ring,
          ← Real.exp_add, show a * (n : ℝ) + -b * n * s = (a - b * s) * n by ring]
  · intro N z hz
    obtain ⟨n, hn, hzn⟩ : ∃ n, N ≤ n ∧ z ∈ higherBadValues F α β A B k D n := by
      by_contra hnone
      apply hz
      apply polynomialValueRepulsion_of_eventually_notMem_higherBadValues hU hF hA hk hD hM
      filter_upwards [eventually_ge_atTop N] with n hn
      exact fun hzn => hnone ⟨n, hn, hzn⟩
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzn
    refine mem_iUnion₂.mpr ⟨n, hn, mem_iUnion₂.mpr ⟨v, hv, ?_⟩⟩
    exact (closedBall_subset_closedBall (higherValueRadius_le_exp hA B k D n)) hzv

/-- The complete set of ζ-values with no polynomial separation law has Hausdorff dimension
zero. This does not decide whether the particular value zero belongs to that set. -/
theorem dimH_zetaNonrepellingValues_eq_zero : dimH zetaNonrepellingValues = 0 := by
  obtain ⟨A, B, hA, hM⟩ := exists_riemannZeta_repulsion_strip_bound
  have hfU : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  apply le_antisymm ?_ bot_le
  apply dimH_le
  intro d hd
  by_contra hle
  have hd0 : (0 : ℝ) < d := by
    have ht : (0 : ℝ≥0∞) < (d : ℝ≥0∞) := lt_of_not_ge hle
    exact_mod_cast ht
  have hzero := hausdorffMeasure_nonrepellingValues_eq_zero_of_pos isOpen_ne hfU
    (by norm_num : (0 : ℝ) ≤ 1) hA hM hd0
  exact ENNReal.zero_ne_top (hzero.symm.trans hd)

/-- The dense residual set of ζ-values with exponentially close pairs has Hausdorff
dimension zero. -/
theorem dimH_exceptional_values_of_riemannZeta_eq_zero :
    dimH (⋂ n, exceptionalSet n) = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    dimH (⋂ n, exceptionalSet n) ≤ dimH zetaNonrepellingValues := by
      apply dimH_mono
      intro a ha
      rintro ⟨D, κ, hκ, hrep⟩
      obtain ⟨s, s', hs, hs', hne, hre0, hre1, him, hd⟩ :=
        exists_superpolynomial_pair ha hκ D
      exact (not_le.mpr hd) (hrep s s' hs hs' hne hre0 hre1 him)
    _ = 0 := dimH_zetaNonrepellingValues_eq_zero

end GaloisForLFunctions.ArithmeticDiscreteness
