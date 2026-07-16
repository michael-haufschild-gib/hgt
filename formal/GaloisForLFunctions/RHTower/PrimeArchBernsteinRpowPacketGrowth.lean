import GaloisForLFunctions.RHTower.PrimeArchBernsteinClosedAbelBoundary
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Real-p growth of finite coefficient packets

This file isolates the norm argument behind the Bernstein purity construction.  A degree-`n`
packet has a finite `l1` norm, a unit-disk transform, and a real-`p` energy.  If its `l1` norm has
an exponential ceiling `B^n` while one unit-disk transform survives at scale `B^n`, then every
finite real `p >= 1` energy has exact exponential exponent `B^p` and ordinary nth-root limit
`B^p`.

The theorem is independent of the arithmetic origin of the packet.  The only analytic loss in
passing from a transform value to the `p`-energy is the subexponential cardinality factor
`(n+1)^(p-1)`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `l1` norm of a triangular complex coefficient packet. -/
def finitePacketL1 (a : ℕ → ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ‖a n i‖

/-- The real-`p` energy of a triangular complex coefficient packet. -/
def finitePacketRpowEnergy (a : ℕ → ℕ → ℂ) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ‖a n i‖ ^ p

/-- The degree-`n` coefficient transform of a triangular packet. -/
def finitePacketTransform (a : ℕ → ℕ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), a n i * w ^ i

/-- A finite sum of nonnegative real `p`-powers is bounded by the `p`-power of the sum when
`p >= 1`. -/
lemma finset_sum_rpow_le_rpow_sum_of_nonneg
    {I : Type*} (s : Finset I) (f : I → ℝ) {p : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hp : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add_left
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (f i ^ p)).trans
        (Real.add_rpow_le_rpow_add
          (hf i (Finset.mem_insert_self i s))
          (Finset.sum_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)) hp)

/-- Real-`p` packet energy is nonnegative. -/
lemma finitePacketRpowEnergy_nonneg
    (a : ℕ → ℕ → ℂ) (p : ℝ) (n : ℕ) :
    0 ≤ finitePacketRpowEnergy a p n := by
  exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

/-- For `p >= 1`, the packet `p`-energy is at most the `p`-power of its `l1` norm. -/
theorem finitePacketRpowEnergy_le_l1_rpow
    (a : ℕ → ℕ → ℂ) {p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    finitePacketRpowEnergy a p n ≤ finitePacketL1 a n ^ p := by
  exact finset_sum_rpow_le_rpow_sum_of_nonneg
    (Finset.range (n + 1)) (fun i => ‖a n i‖) (fun _ _ => norm_nonneg _) hp

/-- The packet transform on the closed unit disk is bounded by the packet `l1` norm. -/
theorem norm_finitePacketTransform_le_l1
    (a : ℕ → ℕ → ℂ) (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖finitePacketTransform a n w‖ ≤ finitePacketL1 a n := by
  rw [finitePacketTransform, finitePacketL1]
  calc
    ‖∑ i ∈ Finset.range (n + 1), a n i * w ^ i‖ ≤
        ∑ i ∈ Finset.range (n + 1), ‖a n i * w ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), ‖a n i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg (a n i))
        (pow_le_one₀ (norm_nonneg w) hw)

/-- Holder's finite-cardinality loss from a unit-disk transform value to packet `p`-energy. -/
theorem norm_finitePacketTransform_rpow_le_card_mul_energy
    (a : ℕ → ℕ → ℂ) {p : ℝ} (hp : 1 ≤ p)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖finitePacketTransform a n w‖ ^ p ≤
      (n + 1 : ℝ) ^ (p - 1) * finitePacketRpowEnergy a p n := by
  have htransform := norm_finitePacketTransform_le_l1 a n hw
  have hmean := Real.rpow_sum_le_const_mul_sum_rpow
    (s := Finset.range (n + 1)) (f := fun i => ‖a n i‖) hp
  simp only [abs_of_nonneg (norm_nonneg _), Finset.card_range] at hmean
  exact (Real.rpow_le_rpow (norm_nonneg _) htransform (by linarith)).trans hmean

/-- A positive exponential dominates every fixed natural power of the packet cardinality. -/
lemma tendsto_const_mul_pow_div_nat_add_one_pow_atTop
    {rho eta : ℝ} (k : ℕ) (hrho : 1 < rho) (heta : 0 < eta) :
    Tendsto (fun n : ℕ => eta * rho ^ n / (n + 1 : ℝ) ^ k) atTop atTop := by
  have hbase := tendsto_pow_const_div_const_pow_of_one_lt k hrho
  have hupper : Tendsto
      (fun n : ℕ => (2 : ℝ) ^ k * ((n : ℝ) ^ k / rho ^ n))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbase
  have hpoly : Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ k / rho ^ n)
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => div_nonneg (pow_nonneg (by positivity) k)
        (pow_nonneg (lt_trans zero_lt_one hrho).le n))
      (fun n => ?_) hupper
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hcast : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
        exact_mod_cast (show n + 1 ≤ 2 * n by omega)
      have hpow : (n + 1 : ℝ) ^ k ≤ (2 * (n : ℝ)) ^ k :=
        pow_le_pow_left₀ (by positivity) hcast k
      calc
        (n + 1 : ℝ) ^ k / rho ^ n ≤
            (2 * (n : ℝ)) ^ k / rho ^ n :=
          div_le_div_of_nonneg_right hpow (pow_nonneg (lt_trans zero_lt_one hrho).le n)
        _ = (2 : ℝ) ^ k * ((n : ℝ) ^ k / rho ^ n) := by
          rw [mul_pow]
          ring
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n + 1 : ℝ) ^ k / rho ^ n :=
    Eventually.of_forall fun n => div_pos (pow_pos (by positivity) k)
      (pow_pos (lt_trans zero_lt_one hrho) n)
  have hright : Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ k / rho ^ n)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpoly, hpos⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  have hmul := hinv.atTop_mul_pos heta tendsto_const_nhds
  convert hmul using 1
  funext n
  change eta * rho ^ n / (n + 1 : ℝ) ^ k =
    (((n + 1 : ℝ) ^ k / rho ^ n)⁻¹) * eta
  rw [inv_div]
  ring

/-- **Abstract finite-packet real-`p` growth theorem.**  A common exponential `l1` ceiling and
one nonvanishing unit-disk transform mode determine the exact exponent of every finite
real-`p` packet energy. -/
theorem finitePacketRpowEnergy_exactExponent
    (a : ℕ → ℕ → ℂ) {p A B delta : ℝ} {w : ℂ}
    (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 < B) (hdelta : 0 < delta)
    (hw : ‖w‖ ≤ 1)
    (hupper : ∀ n : ℕ, finitePacketL1 a n ≤ A * B ^ n)
    (hlower : ∀ᶠ n : ℕ in atTop,
      delta * B ^ n ≤ ‖finitePacketTransform a n w‖) :
    ExactExponentialExponentAtNatInfinity (finitePacketRpowEnergy a p) (B ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hB p
  refine ⟨hBp, ?_, ?_⟩
  · intro r hBr
    have hr : 0 < r := hBp.trans hBr
    let q : ℝ := B ^ p / r
    have hq0 : 0 ≤ q := div_nonneg hBp.le hr.le
    have hq1 : q < 1 := (div_lt_one hr).2 hBr
    have hqpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hmajor : Tendsto (fun n : ℕ => A ^ p * q ^ n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hqpow
    apply squeeze_zero
      (fun n => div_nonneg (finitePacketRpowEnergy_nonneg a p n)
        (pow_nonneg hr.le n))
      (fun n => ?_) hmajor
    calc
      finitePacketRpowEnergy a p n / r ^ n ≤
          finitePacketL1 a n ^ p / r ^ n :=
        div_le_div_of_nonneg_right (finitePacketRpowEnergy_le_l1_rpow a hp n)
          (pow_nonneg hr.le n)
      _ ≤ (A * B ^ n) ^ p / r ^ n :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (hupper n) hp0)
          (pow_nonneg hr.le n)
      _ = A ^ p * q ^ n := by
        dsimp only [q]
        rw [Real.mul_rpow hA (pow_nonneg hB.le n),
          ← Real.rpow_pow_comm hB.le p n, div_pow]
        ring
  · intro r hr hrB
    have hratio : 1 < B ^ p / r := (one_lt_div hr).2 hrB
    obtain ⟨k, hk⟩ := exists_nat_ge (p - 1)
    have hbase := tendsto_const_mul_pow_div_nat_add_one_pow_atTop
      k hratio (Real.rpow_pos_of_pos hdelta p)
    have hbound : ∀ᶠ n : ℕ in atTop,
        delta ^ p * (B ^ p / r) ^ n / (n + 1 : ℝ) ^ k ≤
          finitePacketRpowEnergy a p n / r ^ n := by
      filter_upwards [hlower] with n hn
      have htransform := norm_finitePacketTransform_rpow_le_card_mul_energy a hp n hw
      have hdeltaPow :
          (delta * B ^ n) ^ p ≤ ‖finitePacketTransform a n w‖ ^ p :=
        Real.rpow_le_rpow
          (mul_nonneg hdelta.le (pow_nonneg hB.le n)) hn hp0
      have hcard : (n + 1 : ℝ) ^ (p - 1) ≤ (n + 1 : ℝ) ^ k := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by positivity) hk
      have hsource :
          delta ^ p * (B ^ p) ^ n ≤
            (n + 1 : ℝ) ^ k * finitePacketRpowEnergy a p n := by
        calc
          delta ^ p * (B ^ p) ^ n = (delta * B ^ n) ^ p := by
            rw [Real.mul_rpow hdelta.le (pow_nonneg hB.le n),
              ← Real.rpow_pow_comm hB.le p n]
          _ ≤ ‖finitePacketTransform a n w‖ ^ p := hdeltaPow
          _ ≤ (n + 1 : ℝ) ^ (p - 1) * finitePacketRpowEnergy a p n :=
            htransform
          _ ≤ (n + 1 : ℝ) ^ k * finitePacketRpowEnergy a p n :=
            mul_le_mul_of_nonneg_right hcard (finitePacketRpowEnergy_nonneg a p n)
      have hden : 0 < (n + 1 : ℝ) ^ k * r ^ n := by positivity
      calc
        delta ^ p * (B ^ p / r) ^ n / (n + 1 : ℝ) ^ k =
            (delta ^ p * (B ^ p) ^ n) /
              ((n + 1 : ℝ) ^ k * r ^ n) := by
          rw [div_pow]
          field_simp [hr.ne']
        _ ≤ ((n + 1 : ℝ) ^ k * finitePacketRpowEnergy a p n) /
              ((n + 1 : ℝ) ^ k * r ^ n) :=
          div_le_div_of_nonneg_right hsource hden.le
        _ = finitePacketRpowEnergy a p n / r ^ n := by
          field_simp [hr.ne']
    exact tendsto_atTop_mono' atTop hbound hbase

/-- Under the same hypotheses, the ordinary nth root of the packet `p`-energy converges to
`B^p`. -/
theorem tendsto_finitePacketRpowEnergy_rpow_inv_natCast
    (a : ℕ → ℕ → ℂ) {p A B delta : ℝ} {w : ℂ}
    (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 < B) (hdelta : 0 < delta)
    (hw : ‖w‖ ≤ 1)
    (hupper : ∀ n : ℕ, finitePacketL1 a n ≤ A * B ^ n)
    (hlower : ∀ᶠ n : ℕ in atTop,
      delta * B ^ n ≤ ‖finitePacketTransform a n w‖) :
    Tendsto
      (fun n : ℕ => finitePacketRpowEnergy a p n ^ ((n : ℝ)⁻¹))
      atTop (nhds (B ^ p)) := by
  exact tendsto_rpow_inv_natCast_of_exactExponentialExponentAtNatInfinity
    (finitePacketRpowEnergy_nonneg a p)
    (finitePacketRpowEnergy_exactExponent a hp hA hB hdelta hw hupper hlower)

end

end RHTower
