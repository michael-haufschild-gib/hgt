import GaloisForLFunctions.RHTower.PrimeArchBernsteinRpowPacketGrowth
import GaloisForLFunctions.RHTower.AtomicBernsteinMaximalPacketAsymptotic

/-!
# Positive-power transfer from a square half-order law

For a triangular packet of length `n + 1`, a positive square half-order asymptotic and a common
`l1` exponential ceiling determine the exact nth-root growth of every positive real-power energy.
No distinguished transform phase is required.  The only loss between different powers is a
polynomial factor in the packet length, hence it disappears at nth-root scale.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- The real-power energy at exponent two is the ordinary complex square energy. -/
theorem finitePacketRpowEnergy_two_eq_squareEnergy
    (a : ℕ → ℕ → ℂ) (n : ℕ) :
    finitePacketRpowEnergy a 2 n =
      finiteComplexPacketSquareEnergy (a n) (n + 1) := by
  rw [finitePacketRpowEnergy, finiteComplexPacketSquareEnergy]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.rpow_two ‖a n i‖

/-- Subadditivity of a nonnegative real power at exponent at most one, for finite sums. -/
lemma finset_rpow_sum_le_sum_rpow_of_nonneg
    {J : Type*} (s : Finset J) (f : J → ℝ) {q : ℝ}
    (hf : ∀ j ∈ s, 0 ≤ f j) (hqpos : 0 < q) (hq1 : q ≤ 1) :
    (∑ j ∈ s, f j) ^ q ≤ ∑ j ∈ s, f j ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hqpos.ne']
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (Real.rpow_add_le_add_rpow
        (hf j (Finset.mem_insert_self j s))
        (Finset.sum_nonneg fun k hk => hf k (Finset.mem_insert_of_mem hk))
        hqpos.le hq1).trans
        (add_le_add le_rfl
          (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))))

/-- Every positive-power energy is bounded by packet cardinality times the corresponding power
of the packet `l1` norm.  This remains valid below exponent one. -/
theorem finitePacketRpowEnergy_le_card_mul_l1_rpow
    (a : ℕ → ℕ → ℂ) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    finitePacketRpowEnergy a p n ≤
      (n + 1 : ℝ) * finitePacketL1 a n ^ p := by
  have hl10 : 0 ≤ finitePacketL1 a n :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoord : ∀ i ∈ Finset.range (n + 1), ‖a n i‖ ≤ finitePacketL1 a n := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => norm_nonneg (a n j)) hi
  rw [finitePacketRpowEnergy]
  calc
    (∑ i ∈ Finset.range (n + 1), ‖a n i‖ ^ p) ≤
        ∑ _i ∈ Finset.range (n + 1), finitePacketL1 a n ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow (norm_nonneg _) (hcoord i hi) hp.le
    _ = (n + 1 : ℝ) * finitePacketL1 a n ^ p := by
      simp [Nat.cast_add, Nat.cast_one]

/-- Uniform finite-dimensional comparison with the square energy.  The deliberately coarse
factor `(n+1)^(p/2)` works on both sides of exponent two and is sufficient at exponential scale. -/
theorem finitePacketSquareEnergy_rpow_le_card_mul_rpowEnergy
    (a : ℕ → ℕ → ℂ) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    (finitePacketRpowEnergy a 2 n) ^ (p / 2) ≤
      (n + 1 : ℝ) ^ (p / 2) * finitePacketRpowEnergy a p n := by
  let q : ℝ := p / 2
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  have hqpos : 0 < q := by dsimp only [q]; linarith
  have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hterm (i : ℕ) : (‖a n i‖ ^ 2) ^ q = ‖a n i‖ ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    dsimp only [q]
    ring
  have hrewrite :
      (∑ i ∈ Finset.range (n + 1), (‖a n i‖ ^ 2) ^ q) =
        finitePacketRpowEnergy a p n := by
    rw [finitePacketRpowEnergy]
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  rw [finitePacketRpowEnergy]
  change (∑ i ∈ Finset.range (n + 1), ‖a n i‖ ^ (2 : ℝ)) ^ q ≤
    (n + 1 : ℝ) ^ q * finitePacketRpowEnergy a p n
  simp_rw [Real.rpow_two]
  by_cases hq1 : q ≤ 1
  · have hsub := finset_rpow_sum_le_sum_rpow_of_nonneg
      (Finset.range (n + 1)) (fun i => ‖a n i‖ ^ 2)
      (fun _ _ => sq_nonneg _) hqpos hq1
    calc
      (∑ i ∈ Finset.range (n + 1), ‖a n i‖ ^ 2) ^ q ≤
          ∑ i ∈ Finset.range (n + 1), (‖a n i‖ ^ 2) ^ q := hsub
      _ = finitePacketRpowEnergy a p n := hrewrite
      _ ≤ (n + 1 : ℝ) ^ q * finitePacketRpowEnergy a p n := by
        rw [← one_mul (finitePacketRpowEnergy a p n)]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (Real.one_le_rpow hbase hq0)
          (finitePacketRpowEnergy_nonneg a p n)
  · have hqge : 1 ≤ q := le_of_lt (lt_of_not_ge hq1)
    have hmean := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.range (n + 1)) (f := fun i => ‖a n i‖ ^ 2)
      hqge (fun _ _ => sq_nonneg _)
    have hcard : (n + 1 : ℝ) ^ (q - 1) ≤ (n + 1 : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    calc
      (∑ i ∈ Finset.range (n + 1), ‖a n i‖ ^ 2) ^ q ≤
          (n + 1 : ℝ) ^ (q - 1) *
            ∑ i ∈ Finset.range (n + 1), (‖a n i‖ ^ 2) ^ q := by
        simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hmean
      _ = (n + 1 : ℝ) ^ (q - 1) * finitePacketRpowEnergy a p n := by
        rw [hrewrite]
      _ ≤ (n + 1 : ℝ) ^ q * finitePacketRpowEnergy a p n :=
        mul_le_mul_of_nonneg_right hcard (finitePacketRpowEnergy_nonneg a p n)

/-- A positive square half-order law supplies a polynomially weakened square-energy lower
envelope. -/
lemma eventually_squareEnergy_ge_of_positive_halfOrder
    (a : ℕ → ℕ → ℂ) {B L : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hhalf : Tendsto
      (fun n : ℕ => Real.sqrt n * finitePacketRpowEnergy a 2 n / (B ^ 2) ^ n)
      atTop (nhds L)) :
    ∀ᶠ n : ℕ in atTop,
      (L / 2) * (B ^ 2) ^ n / (n + 1 : ℝ) ≤
        finitePacketRpowEnergy a 2 n := by
  have hlower : ∀ᶠ n : ℕ in atTop,
      L / 2 < Real.sqrt n * finitePacketRpowEnergy a 2 n / (B ^ 2) ^ n :=
    hhalf.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hlower, eventually_ge_atTop 1] with n hn hn1
  have hbase : 0 < (B ^ 2) ^ n := pow_pos (sq_pos_of_pos hB) n
  have hcard : 0 < (n + 1 : ℝ) := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ≤ n + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
      nlinarith
  have hscaled : (L / 2) * (B ^ 2) ^ n ≤
      Real.sqrt n * finitePacketRpowEnergy a 2 n := by
    exact (lt_div_iff₀ hbase).mp hn |>.le
  apply (div_le_iff₀ hcard).2
  calc
    (L / 2) * (B ^ 2) ^ n ≤
        Real.sqrt n * finitePacketRpowEnergy a 2 n := hscaled
    _ ≤ (n + 1 : ℝ) * finitePacketRpowEnergy a 2 n :=
      mul_le_mul_of_nonneg_right hsqrt (finitePacketRpowEnergy_nonneg a 2 n)
    _ = finitePacketRpowEnergy a 2 n * (n + 1 : ℝ) := mul_comm _ _

/-- **Positive-power half-order transfer.**  A square half-order asymptotic and a common `l1`
exponential ceiling determine the exact exponential exponent of every positive real-power energy. -/
theorem finitePacketRpowEnergy_exactExponent_of_positive_square_halfOrder
    (a : ℕ → ℕ → ℂ) {p A B L : ℝ}
    (hp : 0 < p) (hA : 0 ≤ A) (hB : 0 < B) (hL : 0 < L)
    (hupper : ∀ n : ℕ, finitePacketL1 a n ≤ A * B ^ n)
    (hhalf : Tendsto
      (fun n : ℕ => Real.sqrt n * finitePacketRpowEnergy a 2 n / (B ^ 2) ^ n)
      atTop (nhds L)) :
    ExactExponentialExponentAtNatInfinity (finitePacketRpowEnergy a p) (B ^ p) := by
  let q : ℝ := p / 2
  have hp0 : 0 ≤ p := hp.le
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith
  have hqpos : 0 < q := by dsimp only [q]; linarith
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hB p
  have heta : 0 < (L / 2) ^ q := Real.rpow_pos_of_pos (by linarith) q
  obtain ⟨k, hk⟩ := exists_nat_ge p
  have hsquare := eventually_squareEnergy_ge_of_positive_halfOrder a hB hL hhalf
  refine ⟨hBp, ?_, ?_⟩
  · intro r hBr
    have hr : 0 < r := hBp.trans hBr
    let theta : ℝ := B ^ p / r
    have htheta0 : 0 ≤ theta := div_nonneg hBp.le hr.le
    have htheta1 : theta < 1 := (div_lt_one hr).2 hBr
    have hgeom := tendsto_natCast_add_one_mul_pow_nhds_zero htheta0 htheta1
    have hmajor : Tendsto
        (fun n : ℕ => A ^ p * ((n + 1 : ℝ) * theta ^ n))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hgeom
    apply squeeze_zero
      (fun n => div_nonneg (finitePacketRpowEnergy_nonneg a p n)
        (pow_nonneg hr.le n))
      (fun n => ?_) hmajor
    calc
      finitePacketRpowEnergy a p n / r ^ n ≤
          ((n + 1 : ℝ) * finitePacketL1 a n ^ p) / r ^ n :=
        div_le_div_of_nonneg_right
          (finitePacketRpowEnergy_le_card_mul_l1_rpow a hp n)
          (pow_nonneg hr.le n)
      _ ≤ ((n + 1 : ℝ) * (A * B ^ n) ^ p) / r ^ n := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le n)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow
            (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hupper n) hp0)
          (by positivity)
      _ = A ^ p * ((n + 1 : ℝ) * theta ^ n) := by
        dsimp only [theta]
        rw [Real.mul_rpow hA (pow_nonneg hB.le n),
          ← Real.rpow_pow_comm hB.le p n, div_pow]
        ring
  · intro r hr hrB
    have hratio : 1 < B ^ p / r := (one_lt_div hr).2 hrB
    have hdiverge := tendsto_const_mul_pow_div_nat_add_one_pow_atTop
      k hratio heta
    have hlower : ∀ᶠ n : ℕ in atTop,
        (L / 2) ^ q * (B ^ p / r) ^ n / (n + 1 : ℝ) ^ k ≤
          finitePacketRpowEnergy a p n / r ^ n := by
      filter_upwards [hsquare] with n hn
      let card : ℝ := n + 1
      have hcard : 0 < card := by dsimp only [card]; positivity
      have hcardOne : 1 ≤ card := by
        dsimp only [card]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hsqLower :
          ((L / 2) * (B ^ 2) ^ n / card) ^ q ≤
            (finitePacketRpowEnergy a 2 n) ^ q :=
        Real.rpow_le_rpow
          (div_nonneg (mul_nonneg (by linarith) (pow_nonneg (sq_nonneg B) n)) hcard.le)
          (by simpa only [card] using hn) hq0
      have hcompare := finitePacketSquareEnergy_rpow_le_card_mul_rpowEnergy a hp n
      have hcore :
          (L / 2) ^ q * (B ^ p) ^ n / card ^ p ≤
            finitePacketRpowEnergy a p n := by
        have hcombined :
            ((L / 2) * (B ^ 2) ^ n / card) ^ q ≤
              card ^ q * finitePacketRpowEnergy a p n :=
          hsqLower.trans (by simpa only [card, q] using hcompare)
        have hcardq : 0 < card ^ q := Real.rpow_pos_of_pos hcard q
        calc
          (L / 2) ^ q * (B ^ p) ^ n / card ^ p =
              (((L / 2) * (B ^ 2) ^ n / card) ^ q) / card ^ q := by
            rw [Real.div_rpow (mul_nonneg (by linarith) (pow_nonneg (sq_nonneg B) n))
                hcard.le,
              Real.mul_rpow (by linarith) (pow_nonneg (sq_nonneg B) n),
              ← Real.rpow_pow_comm (sq_nonneg B) q n]
            have hBpower : (B ^ 2) ^ q = B ^ p := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
              congr 1
              dsimp only [q]
              ring
            rw [hBpower]
            have hcardPower : card ^ p = card ^ q * card ^ q := by
              rw [← Real.rpow_add hcard]
              congr 1
              dsimp only [q]
              ring
            rw [hcardPower, div_div]
          _ ≤ (card ^ q * finitePacketRpowEnergy a p n) / card ^ q :=
            div_le_div_of_nonneg_right hcombined hcardq.le
          _ = finitePacketRpowEnergy a p n := by field_simp [hcardq.ne']
      have hcardPow : card ^ p ≤ card ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hcardOne hk
      have hweakened :
          (L / 2) ^ q * (B ^ p) ^ n / card ^ k ≤
            finitePacketRpowEnergy a p n := by
        calc
          (L / 2) ^ q * (B ^ p) ^ n / card ^ k =
              (L / 2) ^ q * (B ^ p) ^ n / card ^ (k : ℝ) := by
            rw [Real.rpow_natCast]
          _ ≤ (L / 2) ^ q * (B ^ p) ^ n / card ^ p :=
            div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg (by linarith) q)
                (pow_nonneg hBp.le n))
              (Real.rpow_pos_of_pos hcard p) hcardPow
          _ ≤ finitePacketRpowEnergy a p n := hcore
      have hden : 0 < r ^ n := pow_pos hr n
      calc
        (L / 2) ^ q * (B ^ p / r) ^ n / (n + 1 : ℝ) ^ k =
            ((L / 2) ^ q * (B ^ p) ^ n / card ^ k) / r ^ n := by
          dsimp only [card]
          rw [div_pow]
          simp only [div_eq_mul_inv]
          ring
        _ ≤ finitePacketRpowEnergy a p n / r ^ n :=
          div_le_div_of_nonneg_right hweakened hden.le
    exact tendsto_atTop_mono' atTop hlower hdiverge

/-- The ordinary nth root of every positive-power packet energy has the corresponding powered
base. -/
theorem tendsto_finitePacketRpowEnergy_of_positive_square_halfOrder
    (a : ℕ → ℕ → ℂ) {p A B L : ℝ}
    (hp : 0 < p) (hA : 0 ≤ A) (hB : 0 < B) (hL : 0 < L)
    (hupper : ∀ n : ℕ, finitePacketL1 a n ≤ A * B ^ n)
    (hhalf : Tendsto
      (fun n : ℕ => Real.sqrt n * finitePacketRpowEnergy a 2 n / (B ^ 2) ^ n)
      atTop (nhds L)) :
    Tendsto
      (fun n : ℕ => finitePacketRpowEnergy a p n ^ ((n : ℝ)⁻¹))
      atTop (nhds (B ^ p)) := by
  exact tendsto_rpow_inv_natCast_of_exactExponentialExponentAtNatInfinity
    (finitePacketRpowEnergy_nonneg a p)
    (finitePacketRpowEnergy_exactExponent_of_positive_square_halfOrder
      a hp hA hB hL hupper hhalf)

end

end RHTower
