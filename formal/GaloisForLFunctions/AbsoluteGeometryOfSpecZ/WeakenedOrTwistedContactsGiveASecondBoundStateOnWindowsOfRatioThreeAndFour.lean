import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize

/-!
# Weakened or twisted contacts give a second bound state on windows of ratio three and four

Weil's form of a packet carries the contact `Λ(k)/√k` at the displacement `log k`. Replace it by
`ω(k) Λ(k)/√k` (`reweightedPacketForm`): `ω ≡ 1` is Weil's form, `ω ≡ 0` the form without primes,
`ω(p^m) = (−1)^m` the Liouville twist.

* **One floor map.** The contact of `k` is the difference of Weil's forms of the cutoffs `k − 1`
  and `k` (`packetForm_pred_sub`); on step packets it is the graph of the floor map of `k` between
  the blocks, with the weight `Λ(k)/k` (`contact_stepPacket_eq_sum_floorGraph`).
* **The tower.** Hence every reweighted form is a combination of Weil's forms of different
  cutoffs: on step packets it is the form of the reweighted block matrix
  (`reweightedPacketForm_stepPacket`), and the reweighted block matrix and its neutral part are
  invariant under refinement, as the true ones are (`sum_reweightedBlock_refine`,
  `sum_reweightedNeutral_refine`). A statement on the first blocks holds at every block size.
* **The halves of `(R, 4R]`.** On the packets with the values `s/√R` on `(R, 2R]` and `t/√R` on
  `(2R, 4R]` the reweighted neutral part is

    `−(D s² + 2 (J + K_ω) s t + 2 D t²)`,

  with the depth `D = γ + log 2π + 3 log 2 − 3 log 3` of a dyadic window, the jets
  `J = 6 log 3 − 2 log 2 − (5/2) log 5` and the contacts `K_ω = ω(2) log 2 + ω(3) (log 3)/3`
  between the halves (`bilin_reweightedNeutral_halves`). The halves hold two bound states as soon
  as `(J + K_ω)² < 2 D²` (`two_le_hermNegIndex_reweighted_lowered_ratio_four`): the jets alone do
  not bind them. At the true weights `(J + K)² > 2 D²` and the plane holds a positive direction
  (`bilin_neutralWindow_halves_pos`).

Consequences, at every block size `R ≥ 1`:

* if the contact of `2` has a weight in `[−4, 0]`, every window `(R, R + J]` with `J ≥ 2R` holds
  at least two bound states, whatever the other weights
  (`two_le_hermNegIndex_reweighted_of_ratio_three`); in particular for the Liouville twist
  (`two_le_hermNegIndex_liouville`);
* if the contacts of `2` and `3` have weights in `[−5/2, 19/40]`, every window with `J ≥ 3R` holds
  at least two bound states (`two_le_hermNegIndex_weakened_contacts`);
* with the true contacts and the constant `γ + log 2π` raised by `δ ≥ 2/5`, the window `(R, 4R]`
  holds at least two bound states (`two_le_hermNegIndex_raised_constant`);
* Weil's form with the contacts of `2` and `3` weighted by at most `7/12`, or by at least `9/8`,
  is negative on a packet constant on the halves of `(R, 4R]`
  (`exists_reweightedPacketForm_neg`): there it equals
  `A s² + 2 (3 log 2 − J − K_ω) s t + 2 A t²` with `A = 2 log 2 − D`
  (`reweightedPacketForm_halves`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The graph of one floor map -/

/-- The graph of the floor map of `k` between two blocks, with the weight `Λ(k)/k`. -/
def floorGraph (k a b : ℕ) : ℝ := if max a b / k = min a b then (Λ k : ℝ) / k else 0

theorem floorGraph_comm (k a b : ℕ) : floorGraph k a b = floorGraph k b a := by
  rw [floorGraph, floorGraph, max_comm, min_comm]

theorem floorGraph_of_le (k : ℕ) {a b : ℕ} (hab : a ≤ b) :
    floorGraph k a b = if b / k = a then (Λ k : ℝ) / k else 0 := by
  rw [floorGraph, max_eq_right hab, min_eq_left hab]

/-- No floor map joins two blocks of ratio below two. -/
theorem floorGraph_eq_zero {k a b : ℕ} (hk : 2 ≤ k) (hab : a ≤ b) (hb : b < 2 * a) :
    floorGraph k a b = 0 := by
  rw [floorGraph_of_le k hab]
  refine if_neg fun h => ?_
  have h1 : b / k * k ≤ b := Nat.div_mul_le_self b k
  rw [h] at h1
  have h2 : a * 2 ≤ a * k := Nat.mul_le_mul_left a hk
  omega

/-- A floor map of `k > b` does not send the block `b` to the first block. -/
theorem floorGraph_one_eq_zero {k b : ℕ} (hb : 1 ≤ b) (hbk : b < k) : floorGraph k 1 b = 0 := by
  rw [floorGraph_of_le k hb, Nat.div_eq_of_lt hbk]
  exact if_neg (by norm_num)

/-- The contacts between two blocks are the graphs of the floor maps. -/
theorem floorContact_eq_sum_floorGraph (Q : ℕ) {a b : ℕ} (hab : a ≤ b) :
    floorContact Q a b = ∑ k ∈ Icc 2 Q, floorGraph k a b := by
  unfold floorContact
  exact Finset.sum_congr rfl fun k _ => (floorGraph_of_le k hab).symm

/-- **The graph of one floor map is the difference of the block matrices of two cutoffs.** -/
theorem blockMatrix_pred_sub {k : ℕ} (hk : 2 ≤ k) (a b : ℕ) :
    blockMatrix (k - 1) a b - blockMatrix k a b = floorGraph k a b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, blockMatrix, blockMatrix, floorContact, floorContact,
    Finset.sum_Icc_succ_top (by omega), floorGraph]
  ring

theorem neutralBlock_pred_sub {k : ℕ} (hk : 2 ≤ k) (a b : ℕ) :
    neutralBlock (k - 1) a b - neutralBlock k a b = floorGraph k a b := by
  rw [neutralBlock, neutralBlock, ← blockMatrix_pred_sub hk]
  ring

/-- **The contact of `k` in Weil's form is the difference of the forms of two cutoffs.** -/
theorem packetForm_pred_sub {k : ℕ} (hk : 2 ≤ k) (g : ℝ → ℝ) :
    packetForm (k - 1) g - packetForm k g =
      2 * (contactWeight k * packetAutocorr g (Real.log k)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, packetForm, packetForm, Finset.sum_Icc_succ_top (by omega)]
  ring

/-- **The contact of `k` on a step packet is the graph of the floor map of `k`.** -/
theorem contact_stepPacket_eq_sum_floorGraph {R : ℕ} (hR : 1 ≤ R) {k : ℕ} (hk : 2 ≤ k) (J : ℕ)
    (σ : ℕ → ℝ) :
    2 * (contactWeight k * packetAutocorr (stepPacket R J σ) (Real.log k)) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph k (R + j) (R + l) := by
  rw [← packetForm_pred_sub hk, packetForm_stepPacket_eq_sum_blockMatrix hR,
    packetForm_stepPacket_eq_sum_blockMatrix hR, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← blockMatrix_pred_sub hk, mul_sub]

/-- **The graph of a floor map is invariant under refinement.** -/
theorem sum_floorGraph_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : 2 ≤ k)
    (J : ℕ) (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), ∑ l ∈ range (m * J),
        refineStep m σ i * refineStep m σ l * floorGraph k (m * R + i) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph k (R + j) (R + l) := by
  simp only [← neutralBlock_pred_sub hk, mul_sub, Finset.sum_sub_distrib]
  rw [sum_neutralBlock_refine hR hm, sum_neutralBlock_refine hR hm]

/-! ### Reweighted contacts -/

/-- The neutral part of the block matrix with the contact of the floor map of `k` weighted by
`ω k`. -/
def reweightedNeutral (ω : ℕ → ℝ) (Q a b : ℕ) : ℝ :=
  neutralBlock Q a b + ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a b

/-- The block matrix with the contact of the floor map of `k` weighted by `ω k`. -/
def reweightedBlock (ω : ℕ → ℝ) (Q a b : ℕ) : ℝ :=
  blockMatrix Q a b + ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a b

/-- Weil's form of a packet with the contact of `k` weighted by `ω k`. -/
def reweightedPacketForm (ω : ℕ → ℝ) (Q : ℕ) (g : ℝ → ℝ) : ℝ :=
  packetForm Q g +
    2 * ∑ k ∈ Icc 2 Q, (1 - ω k) * (contactWeight k * packetAutocorr g (Real.log k))

/-- The reweighted form is the form without contacts minus the contacts `ω(k) Λ(k)/√k`. -/
theorem reweightedPacketForm_eq (ω : ℕ → ℝ) (Q : ℕ) (g : ℝ → ℝ) :
    reweightedPacketForm ω Q g = packetForm 1 g -
      2 * ∑ k ∈ Icc 2 Q, ω k * (contactWeight k * packetAutocorr g (Real.log k)) := by
  have h1 : packetForm 1 g = packetForm Q g +
      2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k) := by
    unfold packetForm
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : 1 < 2), Finset.sum_empty]
    ring
  have h2 : ∑ k ∈ Icc 2 Q, (1 - ω k) * (contactWeight k * packetAutocorr g (Real.log k)) =
      ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k) -
        ∑ k ∈ Icc 2 Q, ω k * (contactWeight k * packetAutocorr g (Real.log k)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [reweightedPacketForm, h1, h2]
  ring

theorem reweightedNeutral_one (Q a b : ℕ) :
    reweightedNeutral (fun _ => 1) Q a b = neutralBlock Q a b := by
  simp [reweightedNeutral]

theorem reweightedPacketForm_one (Q : ℕ) (g : ℝ → ℝ) :
    reweightedPacketForm (fun _ => 1) Q g = packetForm Q g := by
  simp [reweightedPacketForm]

theorem reweightedNeutral_comm (ω : ℕ → ℝ) (Q a b : ℕ) :
    reweightedNeutral ω Q a b = reweightedNeutral ω Q b a := by
  rw [reweightedNeutral, reweightedNeutral, neutralBlock_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [floorGraph_comm]

/-- Between different blocks: minus the jets, minus the weighted graphs of the floor maps. -/
theorem reweightedNeutral_of_lt (ω : ℕ → ℝ) (Q : ℕ) {a b : ℕ} (hab : a < b) :
    reweightedNeutral ω Q a b = -blockJet a b - ∑ k ∈ Icc 2 Q, ω k * floorGraph k a b := by
  have h : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a b =
      ∑ k ∈ Icc 2 Q, floorGraph k a b - ∑ k ∈ Icc 2 Q, ω k * floorGraph k a b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [reweightedNeutral, neutralBlock_of_lt hab, floorContact_eq_sum_floorGraph Q hab.le, h]
  ring

/-- Between blocks of ratio below two the weights do not enter. -/
theorem reweightedNeutral_eq_neutralBlock (ω : ℕ → ℝ) (Q : ℕ) {a b : ℕ} (hab : a ≤ b)
    (hb : b < 2 * a) : reweightedNeutral ω Q a b = neutralBlock Q a b := by
  have h : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a b = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 hab hb, mul_zero]
  rw [reweightedNeutral, h, add_zero]

/-- A form is linear in its kernel. -/
theorem sum_form_add_sum (J : ℕ) (x : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (B : ℕ → ℕ → ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * (A j l + ∑ k ∈ S, c k * B k j l) =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * A j l +
        ∑ k ∈ S, c k * ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * B k j l := by
  have hin : ∀ j ∈ range J, ∑ l ∈ range J, x j * x l * (A j l + ∑ k ∈ S, c k * B k j l) =
      ∑ l ∈ range J, x j * x l * A j l +
        ∑ k ∈ S, c k * ∑ l ∈ range J, x j * x l * B k j l := by
    intro j _
    have h : ∀ l ∈ range J, x j * x l * (A j l + ∑ k ∈ S, c k * B k j l) =
        x j * x l * A j l + ∑ k ∈ S, c k * (x j * x l * B k j l) := fun l _ => by
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_comm (t := S)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, Finset.sum_comm (t := S)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

theorem sum_reweightedNeutral_eq (ω : ℕ → ℝ) (Q c J : ℕ) (x : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * reweightedNeutral ω Q (c + j) (c + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * neutralBlock Q (c + j) (c + l) +
        ∑ k ∈ Icc 2 Q, (1 - ω k) *
          ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * floorGraph k (c + j) (c + l) :=
  sum_form_add_sum J x (Icc 2 Q) (fun k => 1 - ω k) (fun j l => neutralBlock Q (c + j) (c + l))
    fun k j l => floorGraph k (c + j) (c + l)

theorem sum_reweightedBlock_eq (ω : ℕ → ℝ) (Q c J : ℕ) (x : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * reweightedBlock ω Q (c + j) (c + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * blockMatrix Q (c + j) (c + l) +
        ∑ k ∈ Icc 2 Q, (1 - ω k) *
          ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * floorGraph k (c + j) (c + l) :=
  sum_form_add_sum J x (Icc 2 Q) (fun k => 1 - ω k) (fun j l => blockMatrix Q (c + j) (c + l))
    fun k j l => floorGraph k (c + j) (c + l)

/-- The reweighted block matrix is the product of the charges plus its neutral part. -/
theorem sum_reweightedBlock_eq_charges_add_neutral (ω : ℕ → ℝ) (Q R J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedBlock ω Q (R + j) (R + l) =
      2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) +
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedNeutral ω Q (R + j) (R + l) := by
  rw [sum_reweightedNeutral_eq, sum_reweightedBlock_eq, sum_blockMatrix_eq_charges_add_neutral]
  ring

/-- **On step packets the reweighted form is the form of the reweighted block matrix.** -/
theorem reweightedPacketForm_stepPacket {R : ℕ} (hR : 1 ≤ R) (ω : ℕ → ℝ) (Q J : ℕ)
    (σ : ℕ → ℝ) :
    reweightedPacketForm ω Q (stepPacket R J σ) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedBlock ω Q (R + j) (R + l) := by
  have h : 2 * ∑ k ∈ Icc 2 Q,
      (1 - ω k) * (contactWeight k * packetAutocorr (stepPacket R J σ) (Real.log k)) =
      ∑ k ∈ Icc 2 Q, (1 - ω k) *
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph k (R + j) (R + l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← contact_stepPacket_eq_sum_floorGraph hR (Finset.mem_Icc.mp hk).1]
    ring
  rw [reweightedPacketForm, h, packetForm_stepPacket_eq_sum_blockMatrix hR,
    sum_reweightedBlock_eq]

/-- **The reweighted neutral part is invariant under refinement.** -/
theorem sum_reweightedNeutral_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (ω : ℕ → ℝ)
    (Q J : ℕ) (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), ∑ l ∈ range (m * J),
        refineStep m σ i * refineStep m σ l * reweightedNeutral ω Q (m * R + i) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedNeutral ω Q (R + j) (R + l) := by
  rw [sum_reweightedNeutral_eq, sum_reweightedNeutral_eq, sum_neutralBlock_refine hR hm]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    rw [sum_floorGraph_refine hR hm (Finset.mem_Icc.mp hk).1]

/-- **The reweighted block matrix is invariant under refinement.** -/
theorem sum_reweightedBlock_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (ω : ℕ → ℝ)
    (Q J : ℕ) (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), ∑ l ∈ range (m * J),
        refineStep m σ i * refineStep m σ l * reweightedBlock ω Q (m * R + i) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedBlock ω Q (R + j) (R + l) := by
  rw [sum_reweightedBlock_eq, sum_reweightedBlock_eq, sum_blockMatrix_refine hR hm]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    rw [sum_floorGraph_refine hR hm (Finset.mem_Icc.mp hk).1]

/-- **The reweighted forms of the step packets form a tower under refinement.** -/
theorem reweightedPacketForm_stepPacket_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (ω : ℕ → ℝ) (Q J : ℕ) (σ : ℕ → ℝ) :
    reweightedPacketForm ω Q (stepPacket (m * R) (m * J) (refineStep m σ)) =
      reweightedPacketForm ω Q (stepPacket R J σ) := by
  rw [reweightedPacketForm_stepPacket (Nat.mul_pos hm hR), reweightedPacketForm_stepPacket hR,
    sum_reweightedBlock_refine hR hm]

/-- The negative index of the matrix of a kernel does not decrease when the window grows. -/
theorem hermNegIndex_windowMatrix_mono (K : ℕ → ℕ → ℝ) (R : ℕ) {J J' : ℕ} (hJ : J ≤ J') :
    hermNegIndex ((windowMatrix K R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((windowMatrix K R J').map (↑) : Matrix (Fin J') (Fin J') ℂ) :=
  HeckeKreinToeplitz.hermNegIndex_submatrix_le
    ((windowMatrix K R J').map (↑) : Matrix (Fin J') (Fin J') ℂ) (Fin.castLE hJ)

/-! ### The first blocks -/

/-- The depth of a dyadic window: minus the neutral part of the first block. -/
def dyadicDepth : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi) + 3 * Real.log 2 - 3 * Real.log 3

/-- The depth of the block `(2, 3]`. -/
def thirdDepth : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi) + 9 * Real.log 2 - 5 * Real.log 5

/-- The jets between the first block and the blocks `(2, 3]`, `(3, 4]`. -/
def halvesJet : ℝ := 6 * Real.log 3 - 2 * Real.log 2 - 5 / 2 * Real.log 5

/-- The contacts between the first block and the blocks `(2, 3]`, `(3, 4]`, with the weights
`ω 2` and `ω 3` on the floor maps of `2` and `3`. -/
def halvesContact (ω : ℕ → ℝ) : ℝ := ω 2 * Real.log 2 + ω 3 * (Real.log 3 / 3)

/-- Weil's form on the unit packet of the first block. -/
def dyadicMargin : ℝ := 2 * Real.log 2 - dyadicDepth

theorem neutralBlock_one_one (Q : ℕ) : neutralBlock Q 1 1 = -dyadicDepth := by
  have h4 := log_four
  rw [neutralBlock, blockMatrix_self le_rfl, dyadicDepth]
  simp only [blockDensity, blockJet, xLogXDiff, xLogX]
  norm_num
  linarith

theorem neutralBlock_two_two (Q : ℕ) : neutralBlock Q 2 2 = -thirdDepth := by
  have h4 := log_four
  have h6 := log_six
  rw [neutralBlock, blockMatrix_self (by norm_num), thirdDepth]
  simp only [blockDensity, blockJet, xLogXDiff, xLogX]
  norm_num
  linarith

theorem blockJet_one_two :
    blockJet 1 2 = (5 * Real.log 5 - 14 * Real.log 2 + 3 * Real.log 3) / 2 := by
  have h4 := log_four
  simp only [blockJet, xLogXDiff, xLogX]
  norm_num
  linarith

/-- The neutral part on the constant packet of the blocks `(2, 3]`, `(3, 4]`. -/
theorem neutralBlock_upper_blocks (Q : ℕ) :
    neutralBlock Q 2 2 + 2 * neutralBlock Q 2 3 + neutralBlock Q 3 3 = -(2 * dyadicDepth) := by
  have h := sum_neutralBlock_ratio_two Q (H := 1) le_rfl
  have hc := neutralBlock_comm Q 3 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  rw [dyadicDepth]
  linarith

/-- The jets between the first block and the blocks `(2, 3]`, `(3, 4]`. -/
theorem blockJet_one_two_add_one_three : blockJet 1 2 + blockJet 1 3 = halvesJet := by
  have h4 := log_four
  have h6 := log_six
  have h := sum_range_blockJet_eq (a := 1) (L := 2) (by norm_num) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num [xLogXStep, xLogX] at h
  rw [halvesJet]
  linarith

theorem floorGraph_two_one_two : floorGraph 2 1 2 = Real.log 2 / 2 := by
  rw [floorGraph_of_le 2 (by norm_num), if_pos (by norm_num), vonMangoldt_two]
  norm_num

theorem floorGraph_two_one_three : floorGraph 2 1 3 = Real.log 2 / 2 := by
  rw [floorGraph_of_le 2 (by norm_num), if_pos (by norm_num), vonMangoldt_two]
  norm_num

theorem floorGraph_three_one_three : floorGraph 3 1 3 = Real.log 3 / 3 := by
  rw [floorGraph_of_le 3 (by norm_num), if_pos (by norm_num), vonMangoldt_three]
  norm_num

/-- Only the floor map of `2` joins the blocks `(1, 2]` and `(2, 3]`. -/
theorem sum_weighted_floorGraph_one_two (ω : ℕ → ℝ) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ k ∈ Icc 2 Q, ω k * floorGraph k 1 2 = ω 2 * (Real.log 2 / 2) := by
  rw [Finset.sum_eq_single 2, floorGraph_two_one_two]
  · intro k hk hne
    have hk2 := (Finset.mem_Icc.mp hk).1
    rw [floorGraph_one_eq_zero (by norm_num) (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) h

/-- Only the floor maps of `2` and `3` join the blocks `(1, 2]` and `(3, 4]`. -/
theorem sum_weighted_floorGraph_one_three (ω : ℕ → ℝ) {Q : ℕ} (hQ : 3 ≤ Q) :
    ∑ k ∈ Icc 2 Q, ω k * floorGraph k 1 3 =
      ω 2 * (Real.log 2 / 2) + ω 3 * (Real.log 3 / 3) := by
  have hk : ∀ k ∈ Icc 2 Q, ω k * floorGraph k 1 3 =
      (if k = 2 then ω 2 * (Real.log 2 / 2) else 0) +
        (if k = 3 then ω 3 * (Real.log 3 / 3) else 0) := by
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · interval_cases k
      · rw [floorGraph_two_one_three]
        norm_num
      · rw [floorGraph_three_one_three]
        norm_num
    · rw [floorGraph_one_eq_zero (by norm_num) (by omega), mul_zero, if_neg (by omega),
        if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩),
    if_pos (Finset.mem_Icc.mpr ⟨by norm_num, hQ⟩)]

theorem reweightedNeutral_one_one (ω : ℕ → ℝ) (Q : ℕ) :
    reweightedNeutral ω Q 1 1 = -dyadicDepth := by
  rw [reweightedNeutral_eq_neutralBlock ω Q le_rfl (by norm_num), neutralBlock_one_one]

theorem reweightedNeutral_one_two (ω : ℕ → ℝ) {Q : ℕ} (hQ : 2 ≤ Q) :
    reweightedNeutral ω Q 1 2 = -(blockJet 1 2 + ω 2 * (Real.log 2 / 2)) := by
  rw [reweightedNeutral_of_lt ω Q (by norm_num), sum_weighted_floorGraph_one_two ω hQ]
  ring

/-- The reweighted neutral part between the first block and the blocks `(2, 3]`, `(3, 4]`. -/
theorem reweightedNeutral_first_cross (ω : ℕ → ℝ) {Q : ℕ} (hQ : 3 ≤ Q) :
    reweightedNeutral ω Q 1 2 + reweightedNeutral ω Q 1 3 = -(halvesJet + halvesContact ω) := by
  rw [reweightedNeutral_one_two ω (by omega), reweightedNeutral_of_lt ω Q (by norm_num),
    sum_weighted_floorGraph_one_three ω hQ, halvesContact, ← blockJet_one_two_add_one_three]
  ring

theorem reweightedNeutral_upper_blocks (ω : ℕ → ℝ) (Q : ℕ) :
    reweightedNeutral ω Q 2 2 + 2 * reweightedNeutral ω Q 2 3 + reweightedNeutral ω Q 3 3 =
      -(2 * dyadicDepth) := by
  rw [reweightedNeutral_eq_neutralBlock ω Q le_rfl (by norm_num),
    reweightedNeutral_eq_neutralBlock ω Q (by norm_num) (by norm_num),
    reweightedNeutral_eq_neutralBlock ω Q le_rfl (by norm_num), neutralBlock_upper_blocks]

/-- A symmetric form on the step functions of two blocks. -/
theorem sum_two_blocks_form (N : ℕ → ℕ → ℝ) (hN : ∀ a b, N a b = N b a) (s t : ℝ) :
    ∑ j ∈ range 2, ∑ l ∈ range 2,
        (if j = 0 then s else t) * (if l = 0 then s else t) * N (1 + j) (1 + l) =
      N 1 1 * s ^ 2 + 2 * N 1 2 * s * t + N 2 2 * t ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  rw [hN 2 1]
  ring

/-- A symmetric form on the functions of three blocks that are constant on the last two. -/
theorem sum_three_blocks_form (N : ℕ → ℕ → ℝ) (hN : ∀ a b, N a b = N b a) (s t : ℝ) :
    ∑ j ∈ range 3, ∑ l ∈ range 3,
        (if j = 0 then s else t) * (if l = 0 then s else t) * N (1 + j) (1 + l) =
      N 1 1 * s ^ 2 + 2 * (N 1 2 + N 1 3) * s * t + (N 2 2 + 2 * N 2 3 + N 3 3) * t ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  rw [hN 2 1, hN 3 1, hN 3 2]
  ring

/-- **The reweighted neutral part on the first block and the next one.** -/
theorem sum_reweightedNeutral_two_blocks (ω : ℕ → ℝ) {Q : ℕ} (hQ : 2 ≤ Q) (s t : ℝ) :
    ∑ j ∈ range 2, ∑ l ∈ range 2,
        (if j = 0 then s else t) * (if l = 0 then s else t) *
          reweightedNeutral ω Q (1 + j) (1 + l) =
      -(dyadicDepth * s ^ 2 + 2 * (blockJet 1 2 + ω 2 * (Real.log 2 / 2)) * s * t +
        thirdDepth * t ^ 2) := by
  rw [sum_two_blocks_form _ (reweightedNeutral_comm ω Q), reweightedNeutral_one_one,
    reweightedNeutral_one_two ω hQ,
    reweightedNeutral_eq_neutralBlock ω Q le_rfl (by norm_num), neutralBlock_two_two]
  ring

/-- **The reweighted neutral part on the first block and the two next ones.** -/
theorem sum_reweightedNeutral_three_blocks (ω : ℕ → ℝ) {Q : ℕ} (hQ : 3 ≤ Q) (s t : ℝ) :
    ∑ j ∈ range 3, ∑ l ∈ range 3,
        (if j = 0 then s else t) * (if l = 0 then s else t) *
          reweightedNeutral ω Q (1 + j) (1 + l) =
      -(dyadicDepth * s ^ 2 + 2 * (halvesJet + halvesContact ω) * s * t +
        2 * dyadicDepth * t ^ 2) := by
  rw [sum_three_blocks_form _ (reweightedNeutral_comm ω Q), reweightedNeutral_one_one,
    reweightedNeutral_first_cross ω hQ, reweightedNeutral_upper_blocks]
  ring

/-! ### The halves of a window at every block size -/

/-- The plane of the packets constant on the first block and on the next ones. -/
theorem refineStep_two_steps (m : ℕ) (s t : ℝ) (i : ℕ) :
    s * refineStep m (fun j => if j = 0 then 1 else 0) i +
        t * refineStep m (fun j => if j = 0 then 0 else 1) i =
      refineStep m (fun j => if j = 0 then s else t) i := by
  simp only [refineStep]
  split_ifs <;> ring

/-- **The reweighted neutral part on the packets constant on `(R, 2R]` and on `(2R, 3R]`.** -/
theorem bilin_reweightedNeutral_ratio_three {R Q : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q) (ω : ℕ → ℝ)
    (s t : ℝ) :
    bilin (windowMatrix (reweightedNeutral ω Q) R (R * 2))
        (fun i => refineStep R (fun j => if j = 0 then s else t) i)
        (fun i => refineStep R (fun j => if j = 0 then s else t) i) =
      -(dyadicDepth * s ^ 2 + 2 * (blockJet 1 2 + ω 2 * (Real.log 2 / 2)) * s * t +
        thirdDepth * t ^ 2) := by
  have h := sum_reweightedNeutral_refine (R := 1) le_rfl hR ω Q 2
    (fun j => if j = 0 then s else t)
  rw [Nat.mul_one, sum_reweightedNeutral_two_blocks ω hQ] at h
  exact (sum_fin_windowMatrix_coe (reweightedNeutral ω Q) R (R * 2)
    (refineStep R fun j => if j = 0 then s else t)).trans h

/-- **The reweighted neutral part on the packets constant on the halves of `(R, 4R]`.** -/
theorem bilin_reweightedNeutral_halves {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) (ω : ℕ → ℝ)
    (s t : ℝ) :
    bilin (windowMatrix (reweightedNeutral ω Q) R (R * 3))
        (fun i => refineStep R (fun j => if j = 0 then s else t) i)
        (fun i => refineStep R (fun j => if j = 0 then s else t) i) =
      -(dyadicDepth * s ^ 2 + 2 * (halvesJet + halvesContact ω) * s * t +
        2 * dyadicDepth * t ^ 2) := by
  have h := sum_reweightedNeutral_refine (R := 1) le_rfl hR ω Q 3
    (fun j => if j = 0 then s else t)
  rw [Nat.mul_one, sum_reweightedNeutral_three_blocks ω hQ] at h
  exact (sum_fin_windowMatrix_coe (reweightedNeutral ω Q) R (R * 3)
    (refineStep R fun j => if j = 0 then s else t)).trans h

/-- The mass of a packet constant on the halves of `(R, 4R]`. -/
theorem sum_fin_refineStep_sq {R : ℕ} (hR : 1 ≤ R) (s t : ℝ) :
    ∑ i : Fin (R * 3), refineStep R (fun j => if j = 0 then s else t) i ^ 2 =
      s ^ 2 + 2 * t ^ 2 := by
  refine (Fin.sum_univ_eq_sum_range
    (fun i => refineStep R (fun j => if j = 0 then s else t) i ^ 2) (R * 3)).trans ?_
  rw [sum_refineStep_sq hR]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- **Two bound states at ratio three.** If the pairing of the first two blocks is small
against their depths, the reweighted neutral part of `(R, 3R]` has two negative squares. -/
theorem two_le_hermNegIndex_reweighted_ratio_three {R Q : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (ω : ℕ → ℝ) (hD : 0 < dyadicDepth)
    (hω : (blockJet 1 2 + ω 2 * (Real.log 2 / 2)) ^ 2 < dyadicDepth * thirdDepth) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (R * 2)).map (↑) :
      Matrix (Fin (R * 2)) (Fin (R * 2)) ℂ) := by
  refine two_le_hermNegIndex_of_two_vectors _
    (fun i : Fin (R * 2) => refineStep R (fun j => if j = 0 then 1 else 0) i)
    (fun i : Fin (R * 2) => refineStep R (fun j => if j = 0 then 0 else 1) i)
    (α := -dyadicDepth) (γ := -thirdDepth)
    (c := -(blockJet 1 2 + ω 2 * (Real.log 2 / 2))) (fun s t => ?_) (by linarith) ?_
  · simp only [refineStep_two_steps]
    rw [bilin_reweightedNeutral_ratio_three hR hQ]
    exact le_of_eq (by ring)
  · rw [neg_sq, neg_mul_neg]
    exact hω

/-- **Two bound states at ratio four.** With the contacts weighted by `ω` and the density of
every block lowered by `δ`, the halves of `(R, 4R]` hold two bound states as soon as
`(J + K_ω)² < 2 (D + δ)²`. -/
theorem two_le_hermNegIndex_reweighted_lowered_ratio_four {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q)
    (ω : ℕ → ℝ) {δ : ℝ} (hD : 0 < dyadicDepth + δ)
    (hω : (halvesJet + halvesContact ω) ^ 2 < 2 * (dyadicDepth + δ) ^ 2) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (R * 3) -
      diagonal fun _ => δ).map (↑) : Matrix (Fin (R * 3)) (Fin (R * 3)) ℂ) := by
  refine two_le_hermNegIndex_of_two_vectors _
    (fun i : Fin (R * 3) => refineStep R (fun j => if j = 0 then 1 else 0) i)
    (fun i : Fin (R * 3) => refineStep R (fun j => if j = 0 then 0 else 1) i)
    (α := -(dyadicDepth + δ)) (γ := -(2 * (dyadicDepth + δ)))
    (c := -(halvesJet + halvesContact ω)) (fun s t => ?_) (by linarith) ?_
  · simp only [refineStep_two_steps]
    rw [bilin_sub_diagonal, bilin_reweightedNeutral_halves hR hQ, ← Finset.mul_sum,
      sum_fin_refineStep_sq hR]
    exact le_of_eq (by ring)
  · rw [neg_sq, neg_mul_neg]
    linarith

/-! ### Numbers -/

theorem dyadicDepth_mem : (1.195 : ℝ) < dyadicDepth ∧ dyadicDepth < 1.2 := by
  have hγ1 := RenormalizedArithmeticPotentialTheory.eulerMascheroniConstant_gt_d4
  have hγ2 := RenormalizedArithmeticPotentialTheory.eulerMascheroniConstant_lt_d4
  have hπ1 := log_three_add_lt_log_pi
  have hπ2 := log_pi_lt
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  rw [dyadicDepth, log_two_pi]
  constructor <;> linarith [l3.1, l3.2]

theorem thirdDepth_gt : (0.6027 : ℝ) < thirdDepth := by
  have hγ1 := RenormalizedArithmeticPotentialTheory.eulerMascheroniConstant_gt_d4
  have hπ1 := log_three_add_lt_log_pi
  have l2a := Real.log_two_gt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  rw [thirdDepth, log_two_pi]
  linarith [l3.1, l5.2]

theorem halvesJet_mem : (1.1817 : ℝ) < halvesJet ∧ halvesJet < 1.1818 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  rw [halvesJet]
  constructor <;> linarith [l3.1, l3.2, l5.1, l5.2]

theorem blockJet_one_two_mem : (0.8194 : ℝ) < blockJet 1 2 ∧ blockJet 1 2 < 0.8195 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  have l5 := log_five_mem
  rw [blockJet_one_two]
  constructor <;> linarith [l3.1, l3.2, l5.1, l5.2]

/-- The true contacts between the halves. -/
theorem log_two_add_log_three_div_mem :
    (1.0593 : ℝ) < Real.log 2 + Real.log 3 / 3 ∧ Real.log 2 + Real.log 3 / 3 < 1.0594 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l3 := log_three_mem
  constructor <;> linarith [l3.1, l3.2]

theorem dyadicMargin_mem : (0.186 : ℝ) < dyadicMargin ∧ dyadicMargin < 0.1913 := by
  have hD := dyadicDepth_mem
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  rw [dyadicMargin]
  constructor <;> linarith [hD.1, hD.2]

/-- The contacts between the halves are monotone in the weights of `2` and `3`. -/
theorem halvesContact_le {ω : ℕ → ℝ} {b : ℝ} (h2 : ω 2 ≤ b) (h3 : ω 3 ≤ b) :
    halvesContact ω ≤ b * (Real.log 2 + Real.log 3 / 3) := by
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have l3 : 0 ≤ Real.log 3 / 3 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have e2 := mul_le_mul_of_nonneg_right h2 l2
  have e3 := mul_le_mul_of_nonneg_right h3 l3
  rw [halvesContact]
  linarith

theorem le_halvesContact {ω : ℕ → ℝ} {a : ℝ} (h2 : a ≤ ω 2) (h3 : a ≤ ω 3) :
    a * (Real.log 2 + Real.log 3 / 3) ≤ halvesContact ω := by
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have l3 : 0 ≤ Real.log 3 / 3 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have e2 := mul_le_mul_of_nonneg_right h2 l2
  have e3 := mul_le_mul_of_nonneg_right h3 l3
  rw [halvesContact]
  linarith

/-- A pairing in `(−b, b)` against two depths above `d₀`, `e₀` with `b² ≤ d₀ e₀`. -/
theorem sq_lt_mul_of_abs_lt {x b d e d₀ e₀ : ℝ} (h1 : -b < x) (h2 : x < b) (hd₀ : 0 ≤ d₀)
    (he₀ : 0 ≤ e₀) (hd : d₀ < d) (he : e₀ < e) (hb : b ^ 2 ≤ d₀ * e₀) : x ^ 2 < d * e := by
  have hx : x ^ 2 < b ^ 2 := sq_lt_sq' h1 h2
  have hde : d₀ * e₀ < d * e := mul_lt_mul'' hd he hd₀ he₀
  linarith

/-- A pairing outside `[−b₀, b₀]` against a margin below `a₀` with `2 a₀² ≤ b₀²`. -/
theorem two_mul_sq_lt_sq_of_bounds {A B a₀ b₀ : ℝ} (hA0 : 0 ≤ A) (hA : A < a₀) (hb₀ : 0 ≤ b₀)
    (hB : b₀ < B ∨ B < -b₀) (h : 2 * a₀ ^ 2 ≤ b₀ ^ 2) : 2 * A ^ 2 < B ^ 2 := by
  have hA2 : A ^ 2 < a₀ ^ 2 := sq_lt_sq' (by linarith) hA
  have hB2 : b₀ ^ 2 < B ^ 2 := by
    rcases hB with hB | hB
    · exact sq_lt_sq' (by linarith) hB
    · have h' : b₀ ^ 2 < (-B) ^ 2 := sq_lt_sq' (by linarith) (by linarith)
      rwa [neg_sq] at h'
  linarith

/-! ### Bound states -/

/-- **Without the contact of `2` every window of ratio at least three holds two bound states.**
If the floor map of `2` has a weight in `[−4, 0]`, the reweighted neutral part of `(R, R + J]`,
`J ≥ 2R`, has at least two negative squares, whatever the other weights. -/
theorem two_le_hermNegIndex_reweighted_of_ratio_three {R Q J : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (hJ : 2 * R ≤ J) (ω : ℕ → ℝ) (h1 : -4 ≤ ω 2) (h2 : ω 2 ≤ 0) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) := by
  have hD := dyadicDepth_mem
  have hT := thirdDepth_gt
  have hB := blockJet_one_two_mem
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l2 : 0 ≤ Real.log 2 / 2 := by linarith
  have e1 := mul_le_mul_of_nonneg_right h1 l2
  have e2 := mul_le_mul_of_nonneg_right h2 l2
  have hcrit : (blockJet 1 2 + ω 2 * (Real.log 2 / 2)) ^ 2 < dyadicDepth * thirdDepth :=
    sq_lt_mul_of_abs_lt (b := 0.8195) (d₀ := 1.195) (e₀ := 0.6027) (by linarith) (by linarith)
      (by norm_num) (by norm_num) hD.1 hT (by norm_num)
  exact (two_le_hermNegIndex_reweighted_ratio_three hR hQ ω (by linarith) hcrit).trans
    (hermNegIndex_windowMatrix_mono _ R (by omega))

/-- **The Liouville twist gives a second bound state on every window of ratio at least
three**, at every block size. -/
theorem two_le_hermNegIndex_liouville {R Q J : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q) (hJ : 2 * R ≤ J) :
    2 ≤ hermNegIndex ((windowMatrix
      (reweightedNeutral (fun k => (-1 : ℝ) ^ ArithmeticFunction.cardFactors k) Q) R J).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) := by
  have h : (-1 : ℝ) ^ ArithmeticFunction.cardFactors 2 = -1 := by
    rw [ArithmeticFunction.cardFactors_apply_prime Nat.prime_two, pow_one]
  exact two_le_hermNegIndex_reweighted_of_ratio_three hR hQ hJ _ (by rw [h]; norm_num)
    (by rw [h]; norm_num)

/-- **Weakened contacts give a second bound state at ratio four.** If the floor maps of `2` and
`3` have weights in `[−5/2, 19/40]`, the reweighted neutral part of `(R, R + J]`, `J ≥ 3R`, has
at least two negative squares. -/
theorem two_le_hermNegIndex_weakened_contacts {R Q J : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q)
    (hJ : 3 * R ≤ J) (ω : ℕ → ℝ) (h2 : -(5 / 2) ≤ ω 2 ∧ ω 2 ≤ 19 / 40)
    (h3 : -(5 / 2) ≤ ω 3 ∧ ω 3 ≤ 19 / 40) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) := by
  have hD := dyadicDepth_mem
  have hJt := halvesJet_mem
  have hK := log_two_add_log_three_div_mem
  have hK1 := halvesContact_le h2.2 h3.2
  have hK2 := le_halvesContact h2.1 h3.1
  have hprod : (halvesJet + halvesContact ω) ^ 2 < (dyadicDepth + 0) * (2 * (dyadicDepth + 0)) :=
    sq_lt_mul_of_abs_lt (b := 1.6855) (d₀ := 1.195) (e₀ := 2.39) (by linarith) (by linarith)
      (by norm_num) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have h := two_le_hermNegIndex_reweighted_lowered_ratio_four hR hQ ω (δ := 0) (by linarith)
    (by linarith)
  rw [show (diagonal fun _ : Fin (R * 3) => (0 : ℝ)) = 0 from Matrix.diagonal_zero, sub_zero]
    at h
  exact h.trans (hermNegIndex_windowMatrix_mono _ R (by omega))

/-- **A raised constant gives a second bound state at ratio four.** With the true contacts and
the density of every block lowered by `δ ≥ 2/5`, the neutral part of `(R, 4R]` has at least two
negative squares. -/
theorem two_le_hermNegIndex_raised_constant {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) {δ : ℝ}
    (hδ : 2 / 5 ≤ δ) :
    2 ≤ hermNegIndex ((neutralWindow Q R (R * 3) - diagonal fun _ => δ).map (↑) :
      Matrix (Fin (R * 3)) (Fin (R * 3)) ℂ) := by
  have hD := dyadicDepth_mem
  have hJt := halvesJet_mem
  have hK := log_two_add_log_three_div_mem
  have hK1 : halvesContact (fun _ => 1) = Real.log 2 + Real.log 3 / 3 := by
    rw [halvesContact]
    ring
  have hprod : (halvesJet + halvesContact (fun _ => 1)) ^ 2 <
      (dyadicDepth + δ) * (2 * (dyadicDepth + δ)) :=
    sq_lt_mul_of_abs_lt (b := 2.2412) (d₀ := 1.595) (e₀ := 3.19) (by linarith) (by linarith)
      (by norm_num) (by norm_num) (by linarith) (by linarith) (by norm_num)
  have h := two_le_hermNegIndex_reweighted_lowered_ratio_four hR hQ (fun _ => 1) (δ := δ)
    (by linarith) (by linarith)
  have e : reweightedNeutral (fun _ => 1) Q = neutralBlock Q :=
    funext fun a => funext fun b => reweightedNeutral_one Q a b
  rw [e] at h
  exact h

/-- **At the true weights the plane of the halves holds a positive direction**: the neutral
part of `(R, 4R]` is positive on the difference of the constant packets of its halves. -/
theorem bilin_neutralWindow_halves_pos {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) :
    0 < bilin (neutralWindow Q R (R * 3))
      (fun i => refineStep R (fun j => if j = 0 then 1 else -1) i)
      (fun i => refineStep R (fun j => if j = 0 then 1 else -1) i) := by
  have hD := dyadicDepth_mem
  have hJt := halvesJet_mem
  have hK := log_two_add_log_three_div_mem
  have h := bilin_reweightedNeutral_halves hR hQ (fun _ => 1) 1 (-1)
  have e : reweightedNeutral (fun _ => 1) Q = neutralBlock Q :=
    funext fun a => funext fun b => reweightedNeutral_one Q a b
  rw [e, halvesContact] at h
  rw [neutralWindow, h]
  linarith

/-! ### Weil's form with reweighted contacts -/

/-- **The reweighted form on the packets constant on the halves of `(R, 4R]`.** -/
theorem reweightedPacketForm_halves {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) (ω : ℕ → ℝ) (s t : ℝ) :
    reweightedPacketForm ω Q
        (stepPacket R (R * 3) (refineStep R fun j => if j = 0 then s else t)) =
      dyadicMargin * s ^ 2 + 2 * (3 * Real.log 2 - halvesJet - halvesContact ω) * s * t +
        2 * dyadicMargin * t ^ 2 := by
  have h4 := log_four
  have h := reweightedPacketForm_stepPacket_refine (R := 1) le_rfl hR ω Q 3
    (fun j => if j = 0 then s else t)
  rw [Nat.mul_one] at h
  have h1 : ∑ j ∈ range 3, (if j = 0 then s else t) = s + 2 * t := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    ring
  have hd : blockDegree 1 = Real.log 2 ∧ blockDegree 2 + blockDegree 3 = Real.log 2 := by
    simp only [blockDegree]
    norm_num
    linarith
  have h2 : ∑ j ∈ range 3, (if j = 0 then s else t) * blockDegree (1 + j) =
      (s + t) * Real.log 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    rw [hd.1]
    linear_combination t * hd.2
  rw [h, reweightedPacketForm_stepPacket le_rfl, sum_reweightedBlock_eq_charges_add_neutral,
    sum_reweightedNeutral_three_blocks ω hQ, h1, h2, dyadicMargin]
  ring

/-- Weil's form with reweighted contacts is negative on a packet constant on the halves of
`(R, 4R]` as soon as `2 A² < (3 log 2 − J − K_ω)²`. -/
theorem exists_reweightedPacketForm_neg_of_sq_lt {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q)
    (ω : ℕ → ℝ)
    (h : 2 * dyadicMargin ^ 2 < (3 * Real.log 2 - halvesJet - halvesContact ω) ^ 2) :
    ∃ s t : ℝ, reweightedPacketForm ω Q
      (stepPacket R (R * 3) (refineStep R fun j => if j = 0 then s else t)) < 0 := by
  have hA := dyadicMargin_mem.1
  refine ⟨-(3 * Real.log 2 - halvesJet - halvesContact ω), dyadicMargin, ?_⟩
  rw [reweightedPacketForm_halves hR hQ]
  have hpos := mul_pos (show (0 : ℝ) < dyadicMargin by linarith) (sub_pos.mpr h)
  linarith

/-- **Weil's form with wrong contact weights is negative at ratio four**, at every block size:
if the floor maps of `2` and `3` both have weights at most `7/12`, or both at least `9/8`, the
reweighted form is negative on a packet constant on the halves of `(R, 4R]`. -/
theorem exists_reweightedPacketForm_neg {R Q : ℕ} (hR : 1 ≤ R) (hQ : 3 ≤ Q) (ω : ℕ → ℝ)
    (h : (ω 2 ≤ 7 / 12 ∧ ω 3 ≤ 7 / 12) ∨ (9 / 8 ≤ ω 2 ∧ 9 / 8 ≤ ω 3)) :
    ∃ s t : ℝ, reweightedPacketForm ω Q
      (stepPacket R (R * 3) (refineStep R fun j => if j = 0 then s else t)) < 0 := by
  have hA := dyadicMargin_mem
  have hJt := halvesJet_mem
  have hK := log_two_add_log_three_div_mem
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  refine exists_reweightedPacketForm_neg_of_sq_lt hR hQ ω
    (two_mul_sq_lt_sq_of_bounds (a₀ := 0.1913) (b₀ := 0.2796) (by linarith) hA.2 (by norm_num)
      ?_ (by norm_num))
  rcases h with h | h
  · have hK1 := halvesContact_le h.1 h.2
    exact Or.inl (by linarith)
  · have hK2 := le_halvesContact h.1 h.2
    exact Or.inr (by linarith)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
