import GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.RHTower.EHKoszulDuality
import GaloisForLFunctions.RHTower.AdamsOperations

/-!
# Witt formation mechanics

This module certifies the finite mechanism in
`witt-ghost-formation-conservation-reconstruction-and-adams-memory-law.md`.

One marked mode packet has three generated shadows: complete-homogeneous formation, exterior
formation, and ghost/power-sum response.  Exterior and complete formation obey exact inverse
conservation, the first `r` ghosts reconstruct an `r`-mode multiset, and Adams intervention
subsamples the ghost sequence.

The fourth-organ prediction is encoded by a surjective bucket from original modes to distinct
post-Adams modes.  Bucket cardinalities are the nonzero aggregate weights.  Their Hankel rank is
exactly the number of buckets, and every nonzero constant recurrence has at least that order.
Thus Adams collision count is exact finite process-memory loss.
-/

open scoped BigOperators Matrix
open Finset Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r s : ℕ}

private def natAntidiagonal (k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.HasAntidiagonal.antidiagonal k

/-- Ghost/power-sum response of a finite marked mode packet. -/
def wittGhost (x : Fin r → ℂ) (n : ℕ) : ℂ :=
  (Finset.univ.val.map fun i => x i ^ n).sum

/-- Exterior/hard-core formation response. -/
def wittExterior (x : Fin r → ℂ) (k : ℕ) : ℂ :=
  (Finset.univ.val.map x).esymm k

/-- Complete-homogeneous/unrestricted formation response. -/
def wittComplete (x : Fin r → ℂ) (k : ℕ) : ℂ :=
  (MvPolynomial.aeval x) (MvPolynomial.hsymm (Fin r) ℂ k)

/-- **Exact formation conservation.**  The signed exterior and complete-homogeneous packets are
coefficientwise inverse: every positive-degree coefficient of `E(-t) H(t)` vanishes. -/
theorem witt_formation_conservation (x : Fin r → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ natAntidiagonal k,
      (-1) ^ p.1 * wittExterior x p.1 * wittComplete x p.2 = 0 := by
  simpa [natAntidiagonal, wittExterior, wittComplete] using
    GaloisForLFunctions.eh_koszul_duality x hk

/-- **Ghost/exterior generation.**  Newton's identity ties primitive ghost response to hard-core
formation response in every positive degree. -/
theorem wittGhost_exterior_newton (x : Fin r → ℂ) (k : ℕ) (hk : 0 < k) :
    wittGhost x k =
      (-1) ^ (k + 1) * k * wittExterior x k -
        ∑ a ∈ {a ∈ natAntidiagonal k | a.1 ∈ Set.Ioo 0 k},
          (-1) ^ a.1 * wittExterior x a.1 * wittGhost x a.2 := by
  simpa [natAntidiagonal, wittGhost, wittExterior] using
    GaloisForLFunctions.multiset_newton x k hk

/-- **Joint reconstruction.**  Equality of the first `r` ghost responses reconstructs the entire
unordered `r`-mode packet.  Consequently it reconstructs every symmetric formation response. -/
theorem wittGhost_reconstructs_modes (x y : Fin r → ℂ)
    (h : ∀ k, k ≤ r → wittGhost x k = wittGhost y k) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  apply GaloisForLFunctions.powerSum_torelli_finite x y
  intro k hk
  exact h k hk

/-- Adams intervention raises every marked mode to the same power. -/
def adamsModes (x : Fin r → ℂ) (q : ℕ) : Fin r → ℂ := fun i => x i ^ q

/-- **Adams ghost law.**  Adams intervention by `q` extracts the `q`-spaced ghost subsequence. -/
theorem wittGhost_adams (x : Fin r → ℂ) (q n : ℕ) :
    wittGhost (adamsModes x q) n = wittGhost x (q * n) := by
  simp [wittGhost, adamsModes, pow_mul]

/-- Multiplicity of one post-Adams mode bucket. -/
noncomputable def bucketMultiplicity (bucket : Fin r → Fin s) (a : Fin s) : ℂ :=
  ((Finset.univ.filter fun i => bucket i = a).card : ℂ)

/-- Every bucket of a surjective collision quotient has nonzero multiplicity. -/
theorem bucketMultiplicity_ne_zero (bucket : Fin r → Fin s)
    (hsurj : Function.Surjective bucket) (a : Fin s) : bucketMultiplicity bucket a ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hsurj a
  have hmem : i ∈ Finset.univ.filter (fun j => bucket j = a) := by simp [hi]
  have hcard : 0 < (Finset.univ.filter (fun j => bucket j = a)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  unfold bucketMultiplicity
  exact_mod_cast hcard.ne'

/-- **Collision aggregation.**  If `bucket` labels equal powered modes, then the post-Adams ghost
is exactly the weighted response of the distinct bucket modes. -/
theorem packetMoment_bucket_eq_adamsGhost (x : Fin r → ℂ) (q : ℕ)
    (y : Fin s → ℂ) (bucket : Fin r → Fin s)
    (hpow : ∀ i, x i ^ q = y (bucket i)) (n : ℕ) :
    packetMoment y (bucketMultiplicity bucket) n = wittGhost x (q * n) := by
  classical
  calc
    packetMoment y (bucketMultiplicity bucket) n
        = ∑ a : Fin s, ∑ i ∈ Finset.univ with bucket i = a, y a ^ n := by
            apply Finset.sum_congr rfl
            intro a _
            simp [bucketMultiplicity, nsmul_eq_mul]
    _ = ∑ i : Fin r, y (bucket i) ^ n := Finset.sum_fiberwise' Finset.univ bucket _
    _ = ∑ i : Fin r, (x i ^ q) ^ n := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hpow]
    _ = wittGhost x (q * n) := by
          rw [wittGhost]
          change (Finset.univ.val.map fun i => (x i ^ q) ^ n).sum = _
          simp [pow_mul]

/-- **Fourth-organ prediction, recurrence.**  The distinct powered modes generate the exact
characteristic-polynomial recurrence of the post-Adams ghost sequence. -/
theorem adamsGhost_recurrence_of_bucket (x : Fin r → ℂ) (q : ℕ)
    (y : Fin s → ℂ) (bucket : Fin r → Fin s)
    (hpow : ∀ i, x i ^ q = y (bucket i)) (n : ℕ) :
    ∑ k ∈ Finset.range (s + 1), (spectrumPoly y).coeff k *
      wittGhost x (q * (n + k)) = 0 := by
  simpa only [packetMoment_bucket_eq_adamsGhost x q y bucket hpow] using
    packetMoment_recurrence y (bucketMultiplicity bucket) n

/-- **Fourth-organ prediction, exact memory rank.**  Once the Hankel window is saturated, its rank
is exactly the number of distinct post-Adams buckets. -/
theorem adamsGhost_hankel_rank_of_bucket (x : Fin r → ℂ) (q : ℕ)
    (y : Fin s → ℂ) (bucket : Fin r → Fin s)
    (hpow : ∀ i, x i ^ q = y (bucket i))
    (hsurj : Function.Surjective bucket) (hinj : Function.Injective y)
    {N : ℕ} (hN : s ≤ N + 1) :
    (seqHankel (fun n => wittGhost x (q * n)) N).rank = s := by
  have heq : seqHankel (fun n => wittGhost x (q * n)) N =
      packetHankel y (bucketMultiplicity bucket) N := by
    ext i j
    exact (packetMoment_bucket_eq_adamsGhost x q y bucket hpow
      ((i : ℕ) + (j : ℕ))).symm
  rw [heq]
  exact rank_packetHankel_of_le y (bucketMultiplicity bucket) hinj
    (bucketMultiplicity_ne_zero bucket hsurj) hN

/-- **Adams collision equals minimal process memory.**  Every nonzero constant recurrence for the
post-Adams ghost sequence has order at least the number of distinct powered-mode buckets. -/
theorem adamsGhost_minimal_recurrence_order (x : Fin r → ℂ) (q : ℕ)
    (y : Fin s → ℂ) (bucket : Fin r → Fin s)
    (hpow : ∀ i, x i ^ q = y (bucket i))
    (hsurj : Function.Surjective bucket) (hinj : Function.Injective y)
    (hs : 0 < s) {p : Polynomial ℂ} (hp : p ≠ 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * wittGhost x (q * (n + k)) = 0) :
    s ≤ p.natDegree := by
  have hrank := adamsGhost_hankel_rank_of_bucket x q y bucket hpow hsurj hinj
    (N := s - 1) (by omega)
  have hle : (seqHankel (fun n => wittGhost x (q * n)) (s - 1)).rank ≤ p.natDegree :=
    rank_seqHankel_le_of_recurrence (m := fun n => wittGhost x (q * n)) hp hrec (s - 1)
  rw [hrank] at hle
  exact hle

/-- Positive real modes cannot collide under a positive Adams power. -/
theorem positiveReal_adamsModes_injective (x : Fin r → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hinj : Function.Injective x)
    {q : ℕ} (hq : q ≠ 0) :
    Function.Injective (fun i => ((x i : ℂ) ^ q)) := by
  intro i j hij
  apply hinj
  have hreal : x i ^ q = x j ^ q := by
    apply Complex.ofReal_injective
    simpa using hij
  exact (pow_left_strictMonoOn₀ hq).injOn (hx i) (hx j) hreal

/-- **Positive chamber.**  Distinct nonnegative real modes preserve full memory under every
positive Adams intervention. -/
theorem positiveReal_adamsGhost_hankel_rank (x : Fin r → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hinj : Function.Injective x)
    {q : ℕ} (hq : q ≠ 0) {N : ℕ} (hN : r ≤ N + 1) :
    (seqHankel (fun n => wittGhost (fun i => (x i : ℂ)) (q * n)) N).rank = r := by
  exact adamsGhost_hankel_rank_of_bucket (fun i => (x i : ℂ)) q
    (fun i => ((x i : ℂ) ^ q)) id (fun _ => rfl) Function.surjective_id
    (positiveReal_adamsModes_injective x hx hinj hq) hN

end


end GaloisForLFunctions.HTGeometry
