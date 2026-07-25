import GaloisForLFunctions.HTGeometry.FisherHeightReplicaCoareaInvariance
import GaloisForLFunctions.RHTower.MobiusCofinalReplicaOneCorner

/-!
# Singular clock-split evacuation of an atomic Fisher collision

Height-preserving replicas cannot cross a physical cutoff separately.  This
module gives the exact complementary law.  Split the `k` copies of every atom
by the positive clock offsets

`eta * r / k`, `r : Fin k`,

while leaving their probability, Fisher score, and damping coordinate
unchanged.  The strict physical order among copies then recovers the fraction
`1 - 1/k` of the same-atom collision.  At the same time, the signed clock
holonomy created inside those replica fibres is bounded by `|eta|` times the
unsplit diagonal energy.

Consequently the joint singular limit `k -> infinity`, `eta = 1/k` recovers
the complete same-atom codiagonal while the added holonomy energy tends to
zero.  The theorem is countable and requires only the summability needed for
the two displayed source quantities.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Physical height of one normalized clock-split replica. -/
def normalizedClockSplitReplicaHeight
    {ι : Type*} (k : ℕ) (eta : ℝ) (h : ι → ℝ)
    (q : Fin k × ι) : ℝ :=
  h q.2 + eta * ((q.1 : ℝ) / k)

/-- Positive clock splitting turns physical order inside one replica fibre
into the strict order of replica labels. -/
theorem normalizedClockSplitReplicaHeight_sameAtom_lt_iff
    {ι : Type*} {k : ℕ} (hk : 0 < k) {eta : ℝ} (heta : 0 < eta)
    (h : ι → ℝ) (r s : Fin k) (i : ι) :
    normalizedClockSplitReplicaHeight k eta h (s, i) <
        normalizedClockSplitReplicaHeight k eta h (r, i) ↔
      s < r := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  change h i + eta * ((s : ℝ) / k) <
      h i + eta * ((r : ℝ) / k) ↔ s < r
  constructor
  · intro hrs
    have hmul :
        eta * ((s : ℝ) / k) < eta * ((r : ℝ) / k) := by
      linarith
    have hdiv : (s : ℝ) / k < (r : ℝ) / k :=
      lt_of_mul_lt_mul_left hmul heta.le
    have hsrR : (s : ℝ) < r :=
      (div_lt_div_iff_of_pos_right hkR).mp hdiv
    exact_mod_cast hsrR
  · intro hsr
    have hsrR : (s : ℝ) < r := by exact_mod_cast hsr
    have hdiv : (s : ℝ) / k < (r : ℝ) / k :=
      (div_lt_div_iff_of_pos_right hkR).2 hsrR
    have hmul :
        eta * ((s : ℝ) / k) < eta * ((r : ℝ) / k) :=
      mul_lt_mul_of_pos_left hdiv heta
    linarith

/-- Same-atom part of the strict-lower codiagonal after `k` normalized
replicas have been installed over every atom. -/
def splitSameAtomCodiagonalOn
    {ι : Type*}
    (k : ℕ) (p a d : ι → ℝ) : ℝ :=
  ∑' i, strictLowerOneCornerCodiagonalOn
    (fun _q : Fin k × Fin k =>
      (p i / k) ^ 2 * (a i + a i) * d i)

/-- The normalized replica fibre recovers exactly the fraction `1 - 1/k`
of twice the atomic collision. -/
theorem splitSameAtomCodiagonalOn_eq
    {ι : Type*}
    {k : ℕ} (hk : 0 < k) (p a d : ι → ℝ)
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i)) :
    splitSameAtomCodiagonalOn k p a d =
      2 * (1 - (k : ℝ)⁻¹) * ∑' i, p i ^ 2 * a i * d i := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpair (i : ι) :
      strictLowerOneCornerCodiagonalOn
          (fun _q : Fin k × Fin k =>
            (p i / k) ^ 2 * (a i + a i) * d i) =
        2 * (1 - (k : ℝ)⁻¹) * (p i ^ 2 * a i * d i) := by
    rw [strictLowerOneCornerCodiagonalOn_eq_orderedOffDiagonal]
    · rw [orderedOffDiagonalCodiagonalOn, tsum_fintype]
      have hcard (r : Fin k) :
          (Finset.univ.filter fun s : Fin k => s ≠ r).card = k - 1 := by
        rw [show (Finset.univ.filter fun s : Fin k => s ≠ r) =
            Finset.univ.erase r by ext s; simp]
        simp
      have hinner (r : Fin k) :
          (∑ s : Fin k, if r ≠ s then
              (p i / k) ^ 2 * (a i + a i) * d i else 0) =
            (k - 1 : ℕ) *
              ((p i / k) ^ 2 * (a i + a i) * d i) := by
        rw [← Finset.sum_filter, Finset.sum_const]
        have hc :
            (Finset.univ.filter fun s : Fin k => r ≠ s).card = k - 1 := by
          simpa [ne_comm] using hcard r
        rw [hc]
        simp only [nsmul_eq_mul]
      rw [show (∑ q : Fin k × Fin k,
          if q.1 ≠ q.2 then
            (p i / k) ^ 2 * (a i + a i) * d i else 0) =
          ∑ r : Fin k, ∑ s : Fin k,
            if r ≠ s then
              (p i / k) ^ 2 * (a i + a i) * d i else 0 by
        rw [Fintype.sum_prod_type]]
      simp_rw [hinner]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hkCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have hnat : k - 1 + 1 = k := Nat.sub_add_cancel hk
        have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
        norm_num at hcast
        linarith
      rw [hkCast]
      field_simp [hkR]
      ring
    · exact (hasSum_fintype _).summable
  rw [splitSameAtomCodiagonalOn]
  simp_rw [hpair]
  exact hcollision.tsum_mul_left _

/-- Same-atom codiagonal defined by the literal split physical heights. -/
def physicalSplitSameAtomCodiagonalOn
    {ι : Type*}
    (k : ℕ) (eta : ℝ) (p a d h : ι → ℝ) : ℝ :=
  ∑' i, ∑ q : Fin k × Fin k,
    if normalizedClockSplitReplicaHeight k eta h (q.2, i) <
        normalizedClockSplitReplicaHeight k eta h (q.1, i) then
      (p i / k) ^ 2 * (a i + a i) * d i +
        (p i / k) ^ 2 * (a i + a i) * d i
    else 0

/-- The algebraic same-atom replica codiagonal is the codiagonal selected by
the literal split physical clock. -/
theorem physicalSplitSameAtomCodiagonalOn_eq
    {ι : Type*}
    {k : ℕ} (hk : 0 < k) {eta : ℝ} (heta : 0 < eta)
    (p a d h : ι → ℝ) :
    physicalSplitSameAtomCodiagonalOn k eta p a d h =
      splitSameAtomCodiagonalOn k p a d := by
  rw [physicalSplitSameAtomCodiagonalOn, splitSameAtomCodiagonalOn]
  apply tsum_congr
  intro i
  rw [strictLowerOneCornerCodiagonalOn, tsum_fintype]
  apply Finset.sum_congr rfl
  intro q hq
  have hiff :=
    normalizedClockSplitReplicaHeight_sameAtom_lt_iff
      hk heta h q.1 q.2 i
  by_cases hlt : q.2 < q.1
  · rw [if_pos (hiff.mpr hlt), if_pos hlt]
  · rw [if_neg (fun hs => hlt (hiff.mp hs)), if_neg hlt]

/-- Average normalized clock distance inside one `k`-replica fibre. -/
def normalizedReplicaClockSpread (k : ℕ) : ℝ :=
  (∑ r : Fin k, ∑ s : Fin k,
      |(r : ℝ) / k - (s : ℝ) / k|) / (k : ℝ) ^ 2

theorem normalizedReplicaClockSpread_nonneg (k : ℕ) :
    0 ≤ normalizedReplicaClockSpread k := by
  rw [normalizedReplicaClockSpread]
  positivity

theorem normalizedReplicaClockSpread_le_one
    {k : ℕ} (hk : 0 < k) :
    normalizedReplicaClockSpread k ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [normalizedReplicaClockSpread, div_le_one (sq_pos_of_pos hkR)]
  calc
    (∑ r : Fin k, ∑ s : Fin k,
        |(r : ℝ) / k - (s : ℝ) / k|) ≤
        ∑ _r : Fin k, ∑ _s : Fin k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_le]
      constructor
      · have hr0 : 0 ≤ (r : ℝ) / k := by positivity
        have hs1 : (s : ℝ) / k ≤ 1 := by
          rw [div_le_one hkR]
          exact_mod_cast s.isLt.le
        linarith
      · have hs0 : 0 ≤ (s : ℝ) / k := by positivity
        have hr1 : (r : ℝ) / k ≤ 1 := by
          rw [div_le_one hkR]
          exact_mod_cast r.isLt.le
        linarith
    _ = (k : ℝ) ^ 2 := by
      simp [pow_two]

/-- Signed holonomy energy added inside the split replica fibres.  The
amplitude coordinate `a` is unchanged; only the physical clock is split. -/
def splitSameAtomHolonomyEnergyOn
    {ι : Type*}
    (k : ℕ) (eta : ℝ) (p a : ι → ℝ) (m : ℝ) : ℝ :=
  ∑' i, ∑ r : Fin k, ∑ s : Fin k,
    (p i / k) ^ 2 *
      |eta * ((r : ℝ) / k - (s : ℝ) / k)| *
      (2 * a i - 2 * m) ^ 2

/-- Exact factorization of the clock-split same-atom holonomy energy. -/
theorem splitSameAtomHolonomyEnergyOn_eq
    {ι : Type*}
    {k : ℕ} (hk : 0 < k) (eta : ℝ) (p a : ι → ℝ) (m : ℝ)
    (henergy : Summable (fun i => p i ^ 2 * (2 * a i - 2 * m) ^ 2)) :
    splitSameAtomHolonomyEnergyOn k eta p a m =
      |eta| * normalizedReplicaClockSpread k *
        ∑' i, p i ^ 2 * (2 * a i - 2 * m) ^ 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  let C : ℝ := |eta| * normalizedReplicaClockSpread k
  have hterm (i : ι) :
      (∑ r : Fin k, ∑ s : Fin k,
        (p i / k) ^ 2 *
          |eta * ((r : ℝ) / k - (s : ℝ) / k)| *
          (2 * a i - 2 * m) ^ 2) =
        C * (p i ^ 2 * (2 * a i - 2 * m) ^ 2) := by
    let D : ℝ := (p i / k) ^ 2 * |eta| *
      (2 * a i - 2 * m) ^ 2
    let S : ℝ := ∑ r : Fin k, ∑ s : Fin k,
      |(r : ℝ) / k - (s : ℝ) / k|
    calc
      (∑ r : Fin k, ∑ s : Fin k,
          (p i / k) ^ 2 *
            |eta * ((r : ℝ) / k - (s : ℝ) / k)| *
            (2 * a i - 2 * m) ^ 2) =
          ∑ r : Fin k, ∑ s : Fin k,
            D * |(r : ℝ) / k - (s : ℝ) / k| := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [abs_mul]
        simp only [D]
        ring
      _ = D * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
      _ = C * (p i ^ 2 * (2 * a i - 2 * m) ^ 2) := by
        simp only [C, D, S, normalizedReplicaClockSpread]
        field_simp [hkR]
  rw [splitSameAtomHolonomyEnergyOn]
  simp_rw [hterm]
  exact henergy.tsum_mul_left _

/-- Cofinal physical clock splitting recovers twice the complete countable
same-atom collision. -/
theorem tendsto_physicalSplitSameAtomCodiagonalOn
    {ι : Type*}
    (p a d h : ι → ℝ)
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i)) :
    Filter.Tendsto
      (fun n : ℕ =>
        physicalSplitSameAtomCodiagonalOn
          (n + 1) (((n + 1 : ℕ) : ℝ)⁻¹) p a d h)
      Filter.atTop
      (nhds (2 * ∑' i, p i ^ 2 * a i * d i)) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
        Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hfactor :
      Filter.Tendsto
        (fun n : ℕ => 2 * (1 - (((n + 1 : ℕ) : ℝ)⁻¹)))
        Filter.atTop (nhds 2) := by
    have hone :
        Filter.Tendsto (fun _n : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hinv).const_mul 2
  have hvalue (n : ℕ) :
      physicalSplitSameAtomCodiagonalOn
          (n + 1) (((n + 1 : ℕ) : ℝ)⁻¹) p a d h =
        2 * (1 - (((n + 1 : ℕ) : ℝ)⁻¹)) *
          ∑' i, p i ^ 2 * a i * d i := by
    rw [physicalSplitSameAtomCodiagonalOn_eq
        (Nat.succ_pos n) (inv_pos.mpr (by positivity))]
    exact splitSameAtomCodiagonalOn_eq
      (Nat.succ_pos n) p a d hcollision
  simp_rw [hvalue]
  simpa using hfactor.mul_const (∑' i, p i ^ 2 * a i * d i)

/-- Along the same cofinal path the added clock holonomy energy vanishes. -/
theorem tendsto_splitSameAtomHolonomyEnergyOn_zero
    {ι : Type*}
    (p a : ι → ℝ) (m : ℝ)
    (henergy : Summable (fun i => p i ^ 2 * (2 * a i - 2 * m) ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ =>
        splitSameAtomHolonomyEnergyOn
          (n + 1) (((n + 1 : ℕ) : ℝ)⁻¹) p a m)
      Filter.atTop (nhds 0) := by
  let E : ℝ := ∑' i, p i ^ 2 * (2 * a i - 2 * m) ^ 2
  have hE : 0 ≤ E := by
    exact tsum_nonneg fun i =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hinv :
      Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
        Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hupper :
      Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹) * E)
        Filter.atTop (nhds 0) := by
    simpa using hinv.mul_const E
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards
    intro n
    rw [splitSameAtomHolonomyEnergyOn_eq
      (Nat.succ_pos n) _ p a m henergy]
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (normalizedReplicaClockSpread_nonneg _)) hE
  · filter_upwards
    intro n
    rw [splitSameAtomHolonomyEnergyOn_eq
      (Nat.succ_pos n) _ p a m henergy,
      abs_of_pos (inv_pos.mpr (by positivity))]
    have hinvnonneg : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) :=
      inv_nonneg.mpr (by positivity)
    calc
      (((n + 1 : ℕ) : ℝ)⁻¹ *
          normalizedReplicaClockSpread (n + 1) * E) ≤
          (((n + 1 : ℕ) : ℝ)⁻¹ * 1 * E) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (normalizedReplicaClockSpread_le_one (Nat.succ_pos n))
            hinvnonneg)
          hE
      _ = (((n + 1 : ℕ) : ℝ)⁻¹) * E := by ring

/-- **Singular clock-splitting law.**  For every countable summable source,
cofinal physical clock splitting recovers the full same-atom collision
codiagonal while the added signed-holonomy energy vanishes. -/
theorem tendsto_clockSplitCollisionRecoveryAndVanishingEnergy
    {ι : Type*}
    (p a d h : ι → ℝ) (m : ℝ)
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i))
    (henergy : Summable (fun i => p i ^ 2 * (2 * a i - 2 * m) ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (physicalSplitSameAtomCodiagonalOn
            (n + 1) (((n + 1 : ℕ) : ℝ)⁻¹) p a d h,
          splitSameAtomHolonomyEnergyOn
            (n + 1) (((n + 1 : ℕ) : ℝ)⁻¹) p a m))
      Filter.atTop
      (nhds
        (2 * ∑' i, p i ^ 2 * a i * d i, 0)) :=
  (tendsto_physicalSplitSameAtomCodiagonalOn
    p a d h hcollision).prodMk_nhds
      (tendsto_splitSameAtomHolonomyEnergyOn_zero p a m henergy)

/-! ## Graph-scale-safe clock splitting

The singular Gamma graph divides a codiagonal by one power of its normal
scale, so source energy is exposed to the square of that division.  Linear
replica growth is therefore insufficient for a norm statement.  Cubic
replica growth is the first integer schedule with a full spare power:

`kₙ = (n+1)³`, `ηₙ = kₙ⁻¹`, `εₙ = (n+1)⁻¹`.

The collision recovery still tends to one, while the added clock holonomy
after division by `εₙ²` is bounded by `E/(n+1)` and vanishes. -/

/-- Cubic number of clock-split replicas at cofinal depth `n`. -/
def cubicClockSplitReplicaCount (n : ℕ) : ℕ :=
  (n + 1) ^ 3

theorem cubicClockSplitReplicaCount_pos (n : ℕ) :
    0 < cubicClockSplitReplicaCount n := by
  simp [cubicClockSplitReplicaCount]

/-- Normal aperture scale paired with cubic clock splitting. -/
def cubicClockSplitNormalScale (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ))⁻¹

/-- Physical replica offset chosen at the inverse cubic scale. -/
def cubicClockSplitOffset (n : ℕ) : ℝ :=
  ((cubicClockSplitReplicaCount n : ℕ) : ℝ)⁻¹

theorem cubicClockSplitOffset_pos (n : ℕ) :
    0 < cubicClockSplitOffset n := by
  rw [cubicClockSplitOffset]
  exact inv_pos.mpr (by
    exact_mod_cast cubicClockSplitReplicaCount_pos n)

private theorem cubicClockSplitOffset_eq_normalScale_pow (n : ℕ) :
    cubicClockSplitOffset n = cubicClockSplitNormalScale n ^ 3 := by
  rw [cubicClockSplitOffset, cubicClockSplitNormalScale,
    cubicClockSplitReplicaCount]
  push_cast
  rw [inv_pow]

private theorem tendsto_cubicClockSplitNormalScale_zero :
    Filter.Tendsto cubicClockSplitNormalScale Filter.atTop (nhds 0) := by
  have heq :
      cubicClockSplitNormalScale =
        fun n : ℕ => (((n : ℝ) + 1))⁻¹ := by
    funext n
    rw [cubicClockSplitNormalScale]
    norm_num
  rw [heq]
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0))

/-- Cubic splitting still recovers the complete same-atom codiagonal. -/
theorem tendsto_cubicClockSplitSameAtomCodiagonal
    {ι : Type*}
    (p a d h : ι → ℝ)
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i)) :
    Filter.Tendsto
      (fun n : ℕ =>
        physicalSplitSameAtomCodiagonalOn
          (cubicClockSplitReplicaCount n)
          (cubicClockSplitOffset n) p a d h)
      Filter.atTop
      (nhds (2 * ∑' i, p i ^ 2 * a i * d i)) := by
  let C : ℝ := ∑' i, p i ^ 2 * a i * d i
  have hoffset :
      Filter.Tendsto cubicClockSplitOffset Filter.atTop (nhds 0) := by
    have h := tendsto_cubicClockSplitNormalScale_zero.pow 3
    convert h using 1
    · funext n
      exact cubicClockSplitOffset_eq_normalScale_pow n
    · norm_num
  have hfactor :
      Filter.Tendsto
        (fun n : ℕ => 2 * (1 - cubicClockSplitOffset n))
        Filter.atTop (nhds 2) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1)).sub hoffset).const_mul 2
  have hvalue (n : ℕ) :
      physicalSplitSameAtomCodiagonalOn
          (cubicClockSplitReplicaCount n)
          (cubicClockSplitOffset n) p a d h =
        2 * (1 - cubicClockSplitOffset n) * C := by
    rw [physicalSplitSameAtomCodiagonalOn_eq
        (cubicClockSplitReplicaCount_pos n)
        (cubicClockSplitOffset_pos n)]
    rw [splitSameAtomCodiagonalOn_eq
      (cubicClockSplitReplicaCount_pos n) p a d hcollision]
    rfl
  simp_rw [hvalue]
  simpa only [C] using hfactor.mul_const C

/-- **Graph-scale-safe singular clock splitting.**  After the one-corner
Gamma graph's squared normal amplification, the holonomy energy created by
cubic clock splitting still vanishes.  This is the norm-compatible
counterpart of collision evacuation; no relation between the source
coefficients and the cofinal schedule is assumed. -/
theorem
    tendsto_cubicClockSplitSameAtomHolonomyEnergy_div_normalScale_sq_zero
    {ι : Type*}
    (p a : ι → ℝ) (m : ℝ)
    (henergy : Summable (fun i => p i ^ 2 * (2 * a i - 2 * m) ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ =>
        splitSameAtomHolonomyEnergyOn
            (cubicClockSplitReplicaCount n)
            (cubicClockSplitOffset n) p a m /
          cubicClockSplitNormalScale n ^ 2)
      Filter.atTop (nhds 0) := by
  let E : ℝ := ∑' i, p i ^ 2 * (2 * a i - 2 * m) ^ 2
  have hE : 0 ≤ E := by
    exact tsum_nonneg fun i =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnormalPos (n : ℕ) : 0 < cubicClockSplitNormalScale n := by
    rw [cubicClockSplitNormalScale]
    positivity
  have hupper :
      Filter.Tendsto
        (fun n : ℕ => cubicClockSplitNormalScale n * E)
        Filter.atTop (nhds 0) := by
    simpa using tendsto_cubicClockSplitNormalScale_zero.mul_const E
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards
    intro n
    rw [splitSameAtomHolonomyEnergyOn_eq
      (cubicClockSplitReplicaCount_pos n)
      (cubicClockSplitOffset n) p a m henergy]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _)
          (normalizedReplicaClockSpread_nonneg _)) hE)
      (sq_nonneg _)
  · filter_upwards
    intro n
    rw [splitSameAtomHolonomyEnergyOn_eq
      (cubicClockSplitReplicaCount_pos n)
      (cubicClockSplitOffset n) p a m henergy,
      abs_of_pos (cubicClockSplitOffset_pos n),
      cubicClockSplitOffset_eq_normalScale_pow]
    have hnormal0 : cubicClockSplitNormalScale n ≠ 0 :=
      (hnormalPos n).ne'
    have hspread :=
      normalizedReplicaClockSpread_le_one
        (cubicClockSplitReplicaCount_pos n)
    calc
      (cubicClockSplitNormalScale n ^ 3 *
            normalizedReplicaClockSpread
              (cubicClockSplitReplicaCount n) * E) /
          cubicClockSplitNormalScale n ^ 2 ≤
        (cubicClockSplitNormalScale n ^ 3 * 1 * E) /
          cubicClockSplitNormalScale n ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hspread
                  (pow_nonneg (hnormalPos n).le 3)) hE)
              (sq_nonneg _)
      _ = cubicClockSplitNormalScale n * E := by
        field_simp [hnormal0]

/-- Joint form: the full atomic codiagonal is recovered while graph-amplified
added holonomy vanishes along the same cubic schedule. -/
theorem tendsto_cubicClockSplitCollisionRecoveryAndGraphSafeEnergy
    {ι : Type*}
    (p a d h : ι → ℝ) (m : ℝ)
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i))
    (henergy : Summable (fun i => p i ^ 2 * (2 * a i - 2 * m) ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (physicalSplitSameAtomCodiagonalOn
            (cubicClockSplitReplicaCount n)
            (cubicClockSplitOffset n) p a d h,
          splitSameAtomHolonomyEnergyOn
              (cubicClockSplitReplicaCount n)
              (cubicClockSplitOffset n) p a m /
            cubicClockSplitNormalScale n ^ 2))
      Filter.atTop
      (nhds (2 * ∑' i, p i ^ 2 * a i * d i, 0)) :=
  (tendsto_cubicClockSplitSameAtomCodiagonal
    p a d h hcollision).prodMk_nhds
      (tendsto_cubicClockSplitSameAtomHolonomyEnergy_div_normalScale_sq_zero
        p a m henergy)

end RHTower
