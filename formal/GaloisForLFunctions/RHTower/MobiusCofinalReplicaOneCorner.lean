import GaloisForLFunctions.RHTower.MobiusCoMovingDiffuseCodiagonal
import Mathlib.Data.Prod.Lex

/-!
# Cofinal replica evacuation of the Fisher diagonal

A countable atomic source loses a literal diagonal collision when only a non-diagonal
one-corner kernel is retained.  Replicating every atom `k` times with mass divided by `k`
preserves every linear source observable and divides the collision by `k`.  Hence the
strict-lower one-corner codiagonal converges to the complete score at every fixed Euler point,
not only in the critical boundary layer.

This is a source dilation: the copied coordinates carry the same Fisher and damping values,
while their amplitudes are spread over orthogonal replica channels.
-/

open Complex Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

/-! ## Universal one-corner law on an ordered countable source -/

def diffuseFisherOffDiagonalCodiagonalOn
    {ι : Type*} [DecidableEq ι] (p a d : ι → ℝ) : ℝ :=
  ∑' i : ι, ∑' j : ι,
    if j = i then 0 else p i * p j * (a i + a j) * d i

def diffuseFisherCollisionResidualOn
    {ι : Type*} (p a d : ι → ℝ) : ℝ :=
  ∑' i : ι, p i ^ 2 * a i * d i

private theorem tsum_ite_eq_zero_of_eq_sub_on
    {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    (hf : Summable f) (i : ι) :
    (∑' j : ι, if j = i then 0 else f j) =
      (∑' j : ι, f j) - f i := by
  rw [show (fun j : ι => if j = i then 0 else f j) =
      fun j => f j - if j = i then f i else 0 by
    funext j
    split_ifs with h
    · subst j
      simp
    · simp]
  rw [Summable.tsum_sub hf (hasSum_ite_eq i (f i)).summable,
    tsum_ite_eq]

theorem diffuseFisherOffDiagonalCodiagonalOn_eq_score_sub_collision
    {ι : Type*} [DecidableEq ι] {p a d : ι → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun i => p i * a i))
    (hpad : Summable (fun i => p i * a i * d i))
    (hcollision : Summable (fun i => p i ^ 2 * a i * d i))
    (hp_one : ∑' i, p i = 1)
    (hpa_zero : ∑' i, p i * a i = 0) :
    diffuseFisherOffDiagonalCodiagonalOn p a d =
      (∑' i, p i * a i * d i) -
        2 * diffuseFisherCollisionResidualOn p a d := by
  have hinner (i : ι) :
      Summable (fun j : ι => p i * p j * (a i + a j) * d i) := by
    have h₁ := hp.mul_left (p i * a i * d i)
    have h₂ := hpa.mul_left (p i * d i)
    exact (h₁.add h₂).congr (fun j => by ring)
  have hinnerValue (i : ι) :
      (∑' j : ι, p i * p j * (a i + a j) * d i) =
        p i * a i * d i := by
    rw [show (fun j : ι => p i * p j * (a i + a j) * d i) =
        fun j => (p i * a i * d i) * p j +
          (p i * d i) * (p j * a j) by
      funext j
      ring]
    rw [Summable.tsum_add (hp.mul_left _) (hpa.mul_left _),
      tsum_mul_left, tsum_mul_left, hp_one, hpa_zero]
    ring
  rw [diffuseFisherOffDiagonalCodiagonalOn]
  simp_rw [tsum_ite_eq_zero_of_eq_sub_on (hinner _) _, hinnerValue]
  rw [show (fun i : ι =>
      p i * a i * d i - p i * p i * (a i + a i) * d i) =
      fun i => p i * a i * d i - 2 * (p i ^ 2 * a i * d i) by
    funext i
    ring]
  rw [Summable.tsum_sub hpad (hcollision.mul_left 2),
    tsum_mul_left, diffuseFisherCollisionResidualOn]

def strictLowerOneCornerCodiagonalOn
    {ι : Type*} [LT ι] [DecidableRel ((· < ·) : ι → ι → Prop)]
    (F : ι × ι → ℝ) : ℝ :=
  ∑' q : ι × ι,
    if q.2 < q.1 then F q + F q.swap else 0

def orderedOffDiagonalCodiagonalOn
    {ι : Type*} [DecidableEq ι] (F : ι × ι → ℝ) : ℝ :=
  ∑' q : ι × ι, if q.1 ≠ q.2 then F q else 0

private theorem summable_strictLower_on
    {ι : Type*} [LT ι]
    [DecidableRel ((· < ·) : ι → ι → Prop)]
    (F : ι × ι → ℝ) (hF : Summable F) :
    Summable (fun q : ι × ι => if q.2 < q.1 then F q else 0) := by
  let A : Set (ι × ι) := {q | q.2 < q.1}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_strictLower_swap_on
    {ι : Type*} [LT ι]
    [DecidableRel ((· < ·) : ι → ι → Prop)]
    (F : ι × ι → ℝ) (hF : Summable F) :
    Summable (fun q : ι × ι => if q.2 < q.1 then F q.swap else 0) := by
  have hs : Summable (fun q : ι × ι => F q.swap) :=
    hF.prod_symm
  let A : Set (ι × ι) := {q | q.2 < q.1}
  exact (hs.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_strictUpper_on
    {ι : Type*} [LT ι]
    [DecidableRel ((· < ·) : ι → ι → Prop)]
    (F : ι × ι → ℝ) (hF : Summable F) :
    Summable (fun q : ι × ι => if q.1 < q.2 then F q else 0) := by
  let A : Set (ι × ι) := {q | q.1 < q.2}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

private theorem summable_orderedOffDiagonal_on
    {ι : Type*} [DecidableEq ι]
    (F : ι × ι → ℝ) (hF : Summable F) :
    Summable (fun q : ι × ι => if q.1 ≠ q.2 then F q else 0) := by
  let A : Set (ι × ι) := {q | q.1 ≠ q.2}
  exact (hF.indicator A).congr
    (fun q => by simp [A, Set.indicator])

theorem strictLowerOneCornerCodiagonalOn_eq_orderedOffDiagonal
    {ι : Type*} [LinearOrder ι] (F : ι × ι → ℝ)
    (hF : Summable F) :
    strictLowerOneCornerCodiagonalOn F =
      orderedOffDiagonalCodiagonalOn F := by
  have hL := summable_strictLower_on (ι := ι) F hF
  have hLS := summable_strictLower_swap_on (ι := ι) F hF
  have hU := summable_strictUpper_on (ι := ι) F hF
  rw [strictLowerOneCornerCodiagonalOn,
    show (fun q : ι × ι =>
      if q.2 < q.1 then F q + F q.swap else 0) =
      (fun q =>
        (if q.2 < q.1 then F q else 0) +
          (if q.2 < q.1 then F q.swap else 0)) by
      funext q
      split_ifs <;> simp_all]
  rw [hL.tsum_add hLS]
  have hswap :
      (∑' q : ι × ι, if q.2 < q.1 then F q.swap else 0) =
        ∑' q : ι × ι, if q.1 < q.2 then F q else 0 := by
    simpa using (Equiv.prodComm ι ι).tsum_eq
      (fun q : ι × ι => if q.1 < q.2 then F q else 0)
  rw [hswap, ← hL.tsum_add hU,
    orderedOffDiagonalCodiagonalOn]
  apply tsum_congr
  intro q
  rcases lt_trichotomy q.1 q.2 with h | h | h
  · have hn : ¬ q.2 < q.1 := not_lt_of_ge h.le
    simp [h, h.ne, hn]
  · simp [h]
  · have hn : ¬ q.1 < q.2 := not_lt_of_ge h.le
    simp [h, h.ne', hn]

def diffuseFisherOrderedKernelOn
    {ι : Type*} (p a d : ι → ℝ) (q : ι × ι) : ℝ :=
  p q.1 * p q.2 * (a q.1 + a q.2) * d q.1

def diffuseFisherOneCornerCodiagonalOn
    {ι : Type*} [LinearOrder ι] (p a d : ι → ℝ) : ℝ :=
  strictLowerOneCornerCodiagonalOn
    (diffuseFisherOrderedKernelOn p a d)

private theorem summable_diffuseFisherOrderedKernelOn
    {ι : Type*} {p a d : ι → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun i => p i * a i))
    (hpd : Summable (fun i => p i * d i))
    (hpad : Summable (fun i => p i * a i * d i)) :
    Summable (diffuseFisherOrderedKernelOn p a d) := by
  have hleft :
      Summable (fun q : ι × ι =>
        (p q.1 * a q.1 * d q.1) * p q.2) :=
    summable_mul_of_summable_norm hpad.norm hp.norm
  have hright :
      Summable (fun q : ι × ι =>
        (p q.1 * d q.1) * (p q.2 * a q.2)) :=
    summable_mul_of_summable_norm hpd.norm hpa.norm
  convert hleft.add hright using 1
  funext q
  simp only [diffuseFisherOrderedKernelOn]
  ring

theorem diffuseFisherOneCornerCodiagonalOn_eq_offDiagonal
    {ι : Type*} [LinearOrder ι] {p a d : ι → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun i => p i * a i))
    (hpd : Summable (fun i => p i * d i))
    (hpad : Summable (fun i => p i * a i * d i)) :
    diffuseFisherOneCornerCodiagonalOn p a d =
      diffuseFisherOffDiagonalCodiagonalOn p a d := by
  rw [diffuseFisherOneCornerCodiagonalOn,
    strictLowerOneCornerCodiagonalOn_eq_orderedOffDiagonal
      (diffuseFisherOrderedKernelOn p a d)
      (summable_diffuseFisherOrderedKernelOn hp hpa hpd hpad),
    orderedOffDiagonalCodiagonalOn,
    diffuseFisherOffDiagonalCodiagonalOn]
  have hF :=
    summable_diffuseFisherOrderedKernelOn hp hpa hpd hpad
  have hO :=
    summable_orderedOffDiagonal_on
      (diffuseFisherOrderedKernelOn p a d) hF
  rw [hO.tsum_prod]
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · have hij : i ≠ j := Ne.symm hji
    simp [hji, hij, diffuseFisherOrderedKernelOn]

/-! ## Cofinal orthogonal replication -/

def cofinalReplicaProbability
    (k : ℕ) (p : ℕ → ℝ) (q : Fin k × ℕ) : ℝ :=
  p q.2 / k

def cofinalReplicaCoordinate
    (a : ℕ → ℝ) (q : Fin k × ℕ) : ℝ :=
  a q.2

local instance cofinalReplicaIndexLinearOrder (k : ℕ) :
    LinearOrder (Fin k × ℕ) :=
  inferInstanceAs (LinearOrder (Fin k ×ₗ ℕ))

def cofinalReplicaFisherOneCornerCodiagonal
    (k : ℕ) (p a d : ℕ → ℝ) : ℝ :=
  diffuseFisherOneCornerCodiagonalOn
    (cofinalReplicaProbability k p)
    (cofinalReplicaCoordinate a)
    (cofinalReplicaCoordinate d)

private theorem summable_cofinalReplica
    {k : ℕ} {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun q : Fin k × ℕ => f q.2 / k) := by
  have hfin : Summable (fun _ : Fin k => (1 : ℝ)) :=
    (hasSum_fintype (fun _ : Fin k => (1 : ℝ))).summable
  have hprod :=
    summable_mul_of_summable_norm hfin.norm (hf.div_const k).norm
  exact hprod.congr (fun q => by simp)

private theorem tsum_cofinalReplica
    {k : ℕ} (hk : 0 < k) {f : ℕ → ℝ} (hf : Summable f) :
    (∑' q : Fin k × ℕ, f q.2 / k) = ∑' n, f n := by
  have hrep := summable_cofinalReplica (k := k) hf
  rw [hrep.tsum_prod]
  simp only [tsum_div_const]
  rw [tsum_fintype]
  simp [hk.ne']

private theorem collision_cofinalReplica
    {k : ℕ} (hk : 0 < k) {p a d : ℕ → ℝ}
    (hcollision : Summable (fun n => p n ^ 2 * a n * d n)) :
    diffuseFisherCollisionResidualOn
        (cofinalReplicaProbability k p)
        (cofinalReplicaCoordinate a)
        (cofinalReplicaCoordinate d) =
      (diffuseFisherCollisionResidual p a d) / k := by
  rw [diffuseFisherCollisionResidualOn,
    diffuseFisherCollisionResidual]
  have hrep :
      Summable (fun q : Fin k × ℕ =>
        (p q.2 ^ 2 * a q.2 * d q.2) / (k : ℝ) ^ 2) := by
    convert summable_cofinalReplica
      (k := k) (hcollision.div_const k) using 1
    funext q
    ring
  rw [show (fun q : Fin k × ℕ =>
      cofinalReplicaProbability k p q ^ 2 *
        cofinalReplicaCoordinate a q *
          cofinalReplicaCoordinate d q) =
      fun q => (p q.2 ^ 2 * a q.2 * d q.2) / (k : ℝ) ^ 2 by
    funext q
    simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
    ring]
  rw [hrep.tsum_prod]
  simp only [tsum_div_const]
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [hk.ne']

/-- **Cofinal replica evacuation law.**  Orthogonally replicating each source atom `k` times
preserves the complete damped score and divides the omitted diagonal collision by `k`.
One strict lower corner therefore contains the full source observable in the cofinal limit. -/
theorem cofinalReplicaFisherOneCornerCodiagonal_eq_score_sub_collision
    {k : ℕ} (hk : 0 < k) {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpd : Summable (fun n => p n * d n))
    (hpad : Summable (fun n => p n * a n * d n))
    (hcollision : Summable (fun n => p n ^ 2 * a n * d n))
    (hp_one : ∑' n, p n = 1)
    (hpa_zero : ∑' n, p n * a n = 0) :
    cofinalReplicaFisherOneCornerCodiagonal k p a d =
      (∑' n, p n * a n * d n) -
        (2 / k) * diffuseFisherCollisionResidual p a d := by
  have hpR :
      Summable (cofinalReplicaProbability k p) := by
    exact (summable_cofinalReplica (k := k) hp).congr (fun q => rfl)
  have hpaR :
      Summable (fun q : Fin k × ℕ =>
        cofinalReplicaProbability k p q *
          cofinalReplicaCoordinate a q) := by
    convert summable_cofinalReplica
      (k := k) hpa using 1
    funext q
    simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
    ring
  have hpdR :
      Summable (fun q : Fin k × ℕ =>
        cofinalReplicaProbability k p q *
          cofinalReplicaCoordinate d q) := by
    convert summable_cofinalReplica
      (k := k) hpd using 1
    funext q
    simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
    ring
  have hpadR :
      Summable (fun q : Fin k × ℕ =>
        cofinalReplicaProbability k p q *
          cofinalReplicaCoordinate a q *
            cofinalReplicaCoordinate d q) := by
    convert summable_cofinalReplica
      (k := k) hpad using 1
    funext q
    simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
    ring
  have hcollisionR :
      Summable (fun q : Fin k × ℕ =>
        cofinalReplicaProbability k p q ^ 2 *
          cofinalReplicaCoordinate a q *
            cofinalReplicaCoordinate d q) := by
    have hbase :
        Summable (fun q : Fin k × ℕ =>
          (p q.2 ^ 2 * a q.2 * d q.2) / (k : ℝ) ^ 2) := by
      convert summable_cofinalReplica
        (k := k) (hcollision.div_const k) using 1
      funext q
      ring
    convert hbase using 1
    funext q
    simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
    ring
  have hpRone :
      (∑' q : Fin k × ℕ, cofinalReplicaProbability k p q) = 1 := by
    rw [show (fun q : Fin k × ℕ =>
      cofinalReplicaProbability k p q) =
      fun q => p q.2 / k by rfl,
      tsum_cofinalReplica hk hp,
      hp_one]
  have hpaRzero :
      (∑' q : Fin k × ℕ,
        cofinalReplicaProbability k p q *
          cofinalReplicaCoordinate a q) = 0 := by
    rw [show (fun q : Fin k × ℕ =>
      cofinalReplicaProbability k p q *
        cofinalReplicaCoordinate a q) =
      fun q => (p q.2 * a q.2) / k by
      funext q
      simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
      ring,
      tsum_cofinalReplica hk hpa,
      hpa_zero]
  have hscoreR :
      (∑' q : Fin k × ℕ,
        cofinalReplicaProbability k p q *
          cofinalReplicaCoordinate a q *
            cofinalReplicaCoordinate d q) =
        ∑' n, p n * a n * d n := by
    rw [show (fun q : Fin k × ℕ =>
      cofinalReplicaProbability k p q *
        cofinalReplicaCoordinate a q *
          cofinalReplicaCoordinate d q) =
      fun q => (p q.2 * a q.2 * d q.2) / k by
      funext q
      simp only [cofinalReplicaProbability, cofinalReplicaCoordinate]
      ring,
      tsum_cofinalReplica hk hpad]
  have hcollisionEq :
      diffuseFisherCollisionResidualOn
          (cofinalReplicaProbability k p)
          (cofinalReplicaCoordinate a)
          (cofinalReplicaCoordinate d) =
        diffuseFisherCollisionResidual p a d / k :=
    collision_cofinalReplica hk hcollision
  rw [cofinalReplicaFisherOneCornerCodiagonal,
    diffuseFisherOneCornerCodiagonalOn_eq_offDiagonal
      hpR hpaR hpdR hpadR,
    diffuseFisherOffDiagonalCodiagonalOn_eq_score_sub_collision
      hpR hpaR hpadR hcollisionR hpRone hpaRzero,
    hscoreR, hcollisionEq]
  ring

theorem tendsto_cofinalReplicaFisherOneCornerCodiagonal
    {p a d : ℕ → ℝ}
    (hp : Summable p)
    (hpa : Summable (fun n => p n * a n))
    (hpd : Summable (fun n => p n * d n))
    (hpad : Summable (fun n => p n * a n * d n))
    (hcollision : Summable (fun n => p n ^ 2 * a n * d n))
    (hp_one : ∑' n, p n = 1)
    (hpa_zero : ∑' n, p n * a n = 0) :
    Tendsto
      (fun k : ℕ =>
        cofinalReplicaFisherOneCornerCodiagonal (k + 1) p a d)
      atTop (𝓝 (∑' n, p n * a n * d n)) := by
  have hinv :
      Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0))
  have hcollisionLimit :
      Tendsto (fun k : ℕ =>
        (2 / ((k + 1 : ℕ) : ℝ)) *
          diffuseFisherCollisionResidual p a d)
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv).mul tendsto_const_nhds
  have hmain : Tendsto
      (fun k : ℕ =>
        (∑' n, p n * a n * d n) -
          (2 / ((k + 1 : ℕ) : ℝ)) *
            diffuseFisherCollisionResidual p a d)
      atTop (𝓝 (∑' n, p n * a n * d n)) := by
    simpa using
      (tendsto_const_nhds.sub hcollisionLimit)
  apply hmain.congr'
  filter_upwards with k
  rw [cofinalReplicaFisherOneCornerCodiagonal_eq_score_sub_collision
    (Nat.succ_pos k) hp hpa hpd hpad hcollision hp_one hpa_zero]

/-! ## Möbius–Gamma–Xi instantiation at every Euler point -/

def mobiusCofinalReplicaFisherOneCornerCodiagonal
    (k : ℕ) (sigma u : ℝ) : ℝ :=
  cofinalReplicaFisherOneCornerCodiagonal k
    (squarefreeMobiusProbability sigma)
    (mobiusCriticalFisherCoordinate sigma)
    (mobiusCriticalDampingCoordinate sigma u)

/-- Exact physical replica law.  The Möbius score is unchanged while the collision coefficient
is reduced from `2` to `2 / k`. -/
theorem ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal_eq
    {k : ℕ} (hk : 0 < k) {sigma u : ℝ}
    (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (mobiusCofinalReplicaFisherOneCornerCodiagonal k sigma u : ℂ) =
      GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) -
        (2 / (k : ℂ)) * mobiusDiffuseCollisionResidual sigma u := by
  have hreal :=
    cofinalReplicaFisherOneCornerCodiagonal_eq_score_sub_collision
      hk
      (summable_squarefreeMobiusProbability hsigma)
      (summable_mobius_probability_mul_fisherCoordinate hsigma)
      (summable_mobius_probability_mul_damping hsigma hu)
      (summable_mobius_probability_mul_fisherCoordinate_mul_damping
        hsigma hu)
      (summable_mobius_collision hsigma hu)
      (tsum_squarefreeMobiusProbability hsigma)
      (tsum_mobius_probability_mul_fisherCoordinate_zero hsigma)
  have hscore :=
    ofReal_tsum_mobius_probability_mul_fisherCoordinate_mul_damping_eq_coefficient
      hsigma hu
  have hcollision :=
    ofReal_diffuseFisherCollisionResidual_eq_mobiusDiffuseCollisionResidual
      hsigma hu
  have hcoefficient :
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
    calc
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
          inner ℂ
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalDampedSignedWeightLp
              sigma u hsigma hu) :=
        (inner_fisherTangent_damped_eq_coefficient hsigma hu).symm
      _ = _ :=
        inner_fisherTangent_damped_eq_squarefreeFisherScore hsigma hu
  calc
    (mobiusCofinalReplicaFisherOneCornerCodiagonal k sigma u : ℂ) =
        (((∑' n : ℕ,
          squarefreeMobiusProbability sigma n *
            mobiusCriticalFisherCoordinate sigma n *
              mobiusCriticalDampingCoordinate sigma u n) -
          (2 / k) *
            diffuseFisherCollisionResidual
              (squarefreeMobiusProbability sigma)
              (mobiusCriticalFisherCoordinate sigma)
              (mobiusCriticalDampingCoordinate sigma u) : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hreal
    _ = (((∑' n : ℕ,
          squarefreeMobiusProbability sigma n *
            mobiusCriticalFisherCoordinate sigma n *
              mobiusCriticalDampingCoordinate sigma u n : ℝ) : ℂ)) -
        ((2 / k : ℝ) : ℂ) *
          ((diffuseFisherCollisionResidual
            (squarefreeMobiusProbability sigma)
            (mobiusCriticalFisherCoordinate sigma)
            (mobiusCriticalDampingCoordinate sigma u) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by
      rw [hscore, hcollision, hcoefficient]
      push_cast
      ring

/-- At each fixed safe Euler point, the strict-lower replicated source converges to the exact
division-free Fisher numerator.  No critical boundary limit is taken. -/
theorem tendsto_ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Tendsto
      (fun k : ℕ =>
        (mobiusCofinalReplicaFisherOneCornerCodiagonal
          (k + 1) sigma u : ℂ))
      atTop
      (𝓝 (GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ))) := by
  have hreal :=
    tendsto_cofinalReplicaFisherOneCornerCodiagonal
      (summable_squarefreeMobiusProbability hsigma)
      (summable_mobius_probability_mul_fisherCoordinate hsigma)
      (summable_mobius_probability_mul_damping hsigma hu)
      (summable_mobius_probability_mul_fisherCoordinate_mul_damping
        hsigma hu)
      (summable_mobius_collision hsigma hu)
      (tsum_squarefreeMobiusProbability hsigma)
      (tsum_mobius_probability_mul_fisherCoordinate_zero hsigma)
  have hcast :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hscore :=
    ofReal_tsum_mobius_probability_mul_fisherCoordinate_mul_damping_eq_coefficient
      hsigma hu
  have hcoefficient :
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
    calc
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u =
          inner ℂ
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalDampedSignedWeightLp
              sigma u hsigma hu) :=
        (inner_fisherTangent_damped_eq_coefficient hsigma hu).symm
      _ = _ :=
        inner_fisherTangent_damped_eq_squarefreeFisherScore hsigma hu
  rw [hscore, hcoefficient] at hcast
  exact hcast.congr' (Filter.Eventually.of_forall (fun k => rfl))

/-- Singular Gamma graph fed by the replicated strict-lower source. -/
def squarefreeMobiusCofinalReplicaGammaCurrentTransportV
    (k : ℕ) (sigma u : ℝ) : ℂ :=
  2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
    (mobiusCofinalReplicaFisherOneCornerCodiagonal k sigma u : ℂ) /
      (((sigma - 1 : ℝ) : ℂ) *
        squarefreeMobiusBoundaryLayerLaplace sigma u) -
    2 * logDeriv archFactor
      (mobiusCriticalBoundaryParameter sigma u)

/-- Exact finite-replica Gamma error. -/
theorem squarefreeMobiusCofinalReplicaGammaCurrentTransportV_eq_completed_add_collision
    {k : ℕ} (hk : 0 < k) {sigma u : ℝ}
    (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusCofinalReplicaGammaCurrentTransportV k sigma u =
      GaloisForLFunctions.completedSquarefreeFixedCurrent
          (mobiusCriticalBoundaryParameter sigma u : ℂ) +
        ((2 / (k : ℂ)) * mobiusDiffuseCollisionResidual sigma u) /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) := by
  have hfull :=
    squarefreeMobiusGammaCurrentTransportV_actualTangent
      hsigma hu
  have hoverlap :=
    squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      hsigma hu
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  calc
    squarefreeMobiusCofinalReplicaGammaCurrentTransportV k sigma u =
        squarefreeMobiusGammaCurrentTransportV
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
          (u : ℂ) +
        ((2 / (k : ℂ)) * mobiusDiffuseCollisionResidual sigma u) /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) := by
      rw [squarefreeMobiusCofinalReplicaGammaCurrentTransportV,
        squarefreeMobiusGammaCurrentTransportV, ← hoverlap,
        hcoord,
        ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal_eq
          hk hsigma hu]
      ring
    _ = _ := by rw [hfull]

/-- Cofinal replication commutes with the singular Gamma graph at every fixed safe Euler point. -/
theorem tendsto_squarefreeMobiusCofinalReplicaGammaCurrentTransportV
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Tendsto
      (fun k : ℕ =>
        squarefreeMobiusCofinalReplicaGammaCurrentTransportV
          (k + 1) sigma u)
      atTop
      (𝓝 (GaloisForLFunctions.completedSquarefreeFixedCurrent
        (mobiusCriticalBoundaryParameter sigma u : ℂ))) := by
  have hscore :=
    tendsto_ofReal_mobiusCofinalReplicaFisherOneCornerCodiagonal
      hsigma hu
  have htransport : Tendsto
      (fun k : ℕ =>
        2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
          (mobiusCofinalReplicaFisherOneCornerCodiagonal
            (k + 1) sigma u : ℂ) /
            (((sigma - 1 : ℝ) : ℂ) *
              squarefreeMobiusBoundaryLayerLaplace sigma u) -
          2 * logDeriv archFactor
            (mobiusCriticalBoundaryParameter sigma u))
      atTop
      (𝓝 (2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
        GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) /
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u) -
        2 * logDeriv archFactor
          (mobiusCriticalBoundaryParameter sigma u))) := by
    exact
      (tendsto_const_nhds.sub
        (hscore.div_const
          (((sigma - 1 : ℝ) : ℂ) *
            squarefreeMobiusBoundaryLayerLaplace sigma u))).sub
        tendsto_const_nhds
  have hfull :=
    squarefreeMobiusGammaCurrentTransportV_actualTangent hsigma hu
  have hoverlap :=
    squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      hsigma hu
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  rw [← hfull]
  simpa only [squarefreeMobiusCofinalReplicaGammaCurrentTransportV,
    squarefreeMobiusGammaCurrentTransportV, hcoord, hoverlap] using
    htransport

/-- Replicated one-corner source with the exact doubled-prime Xi correction. -/
def squarefreeMobiusCofinalReplicaGammaXiWardTransportV
    (k : ℕ) (sigma u : ℝ) : ℂ :=
  let s : ℂ := (mobiusCriticalBoundaryParameter sigma u : ℂ)
  (-I / 2) *
    (squarefreeMobiusCofinalReplicaGammaCurrentTransportV k sigma u +
      4 * infinitePrimeFlux (2 * s))

/-- **Global Euler cofinal source recovery.**  At every fixed safe Euler point, a genuinely
non-diagonal strict-lower replicated source converges to the continued completed Xi trace. -/
theorem tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Tendsto
      (fun k : ℕ =>
        squarefreeMobiusCofinalReplicaGammaXiWardTransportV
          (k + 1) sigma u)
      atTop
      (𝓝 (continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (mobiusCriticalBoundaryParameter sigma u : ℂ)))) := by
  have hcurrent :=
    tendsto_squarefreeMobiusCofinalReplicaGammaCurrentTransportV
      hsigma hu
  let correction : ℂ :=
    4 * infinitePrimeFlux
      (2 * (mobiusCriticalBoundaryParameter sigma u : ℂ))
  have hcorrection : Tendsto (fun _ : ℕ => correction)
      atTop (𝓝 correction) :=
    tendsto_const_nhds
  have h : Tendsto
      (fun k : ℕ =>
        (-I / 2) *
          (squarefreeMobiusCofinalReplicaGammaCurrentTransportV
            (k + 1) sigma u + correction))
      atTop
      (𝓝 ((-I / 2) *
        (GaloisForLFunctions.completedSquarefreeFixedCurrent
            (mobiusCriticalBoundaryParameter sigma u : ℂ) +
          correction))) :=
    (hcurrent.add hcorrection).const_mul (-I / 2)
  have hsource :=
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction
      (xiWardCenteredCoordinate
        (mobiusCriticalBoundaryParameter sigma u : ℂ))
  rw [xiWardCenteredCoordinate_source] at hsource
  simpa only [squarefreeMobiusCofinalReplicaGammaXiWardTransportV,
    correction, hsource] using h

end RHTower
