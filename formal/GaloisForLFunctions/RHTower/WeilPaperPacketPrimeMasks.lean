import GaloisForLFunctions.RHTower.WeilPaperPacketDivisibility
import Mathlib.Data.Nat.PrimeFin

/-!
# Prime-subset masks for actual Weil packets

The proven disjoint-support inclusion-exclusion in OpenAI/math,
`QuadraticSieve/CrossSeparation.lean`, splits packet coefficients into two
positive Gram families. Their difference retains exactly coprime label pairs.
Removing label one makes this difference invisible to every integer diagonal.
-/

open Matrix Complex GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The actual finite prime support of the packet labels. -/
def paperPacketPrimeSet (N : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun m : PacketIndex N => (m : ℕ).primeFactors

abbrev PaperPacketPrimeIndex (N : ℕ) := ↥(paperPacketPrimeSet N).powerset

theorem paperPacket_primeFactors_subset {N : ℕ} (m : PacketIndex N) :
    (m : ℕ).primeFactors ⊆ paperPacketPrimeSet N := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hp⟩

/-- Delete the sole unit label, with no restriction on the supplied coefficients. -/
def paperPacketNonunitCoeff {N : ℕ} (c : PacketIndex N → ℂ) (m : PacketIndex N) : ℂ :=
  if (m : ℕ) = 1 then 0 else c m

/-- One column for every subset of the actual prime support. -/
def paperPacketPrimeMask {N : ℕ} (c : PacketIndex N → ℂ) :
    Matrix (PacketIndex N) (PaperPacketPrimeIndex N) ℂ := fun m D =>
  if D.1 ⊆ (m : ℕ).primeFactors then paperPacketNonunitCoeff c m else 0

def paperPacketEvenPrimeColumns {N : ℕ} (c : PacketIndex N → ℂ) :
    Matrix (PacketIndex N) (PaperPacketPrimeIndex N) ℂ := fun m D =>
  if Even D.1.card then paperPacketPrimeMask c m D else 0

def paperPacketOddPrimeColumns {N : ℕ} (c : PacketIndex N → ℂ) :
    Matrix (PacketIndex N) (PaperPacketPrimeIndex N) ℂ := fun m D =>
  if Even D.1.card then 0 else paperPacketPrimeMask c m D

/-- The primitive part of the packet covariance. -/
def paperPacketCoprimeCovariance {N : ℕ} (c : PacketIndex N → ℂ) :
    Matrix (PacketIndex N) (PacketIndex N) ℂ := fun m k =>
  if Nat.Coprime (m : ℕ) (k : ℕ) then
    paperPacketNonunitCoeff c m * conj (paperPacketNonunitCoeff c k) else 0

private theorem subset_sign_sum (S : Finset ℕ) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ℕ => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

private theorem support_indicator (B S T : Finset ℕ) (hS : S ⊆ B) :
    (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      if Disjoint S T then 1 else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  calc
    _ = ∑ D ∈ (S ∩ T).powerset,
        if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro D _ hnot
      have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
        simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
      simp [hn]
    _ = ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
      apply Finset.sum_congr rfl
      intro D hD
      have hh : D ⊆ S ∧ D ⊆ T := by
        simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
      simp [hh]
    _ = _ := by rw [subset_sign_sum]; simp only [Finset.disjoint_iff_inter_eq_empty]

/-- The source's exact indicator identity at the actual positive integer labels. -/
theorem paperPacketPrimeMask_indicator {N : ℕ} (m k : PacketIndex N) :
    (∑ D : PaperPacketPrimeIndex N,
      if D.1 ⊆ (m : ℕ).primeFactors ∧ D.1 ⊆ (k : ℕ).primeFactors then
        (-1 : ℂ) ^ D.1.card else 0) = if Nat.Coprime (m : ℕ) (k : ℕ) then 1 else 0 := by
  have h := support_indicator (paperPacketPrimeSet N) (m : ℕ).primeFactors
    (k : ℕ).primeFactors (paperPacket_primeFactors_subset m)
  rw [Finset.sum_subtype (p := fun D : Finset ℕ => D ∈ (paperPacketPrimeSet N).powerset)
    (paperPacketPrimeSet N).powerset (fun _ => Iff.rfl)] at h
  simpa only [Nat.disjoint_primeFactors
    (by have := (Finset.mem_Icc.mp m.property).1; omega : (m : ℕ) ≠ 0)
    (by have := (Finset.mem_Icc.mp k.property).1; omega : (k : ℕ) ≠ 0)] using h

private theorem parity_entry {N : ℕ} (c : PacketIndex N → ℂ)
    (m k : PacketIndex N) (D : PaperPacketPrimeIndex N) :
    paperPacketEvenPrimeColumns c m D * conj (paperPacketEvenPrimeColumns c k D) -
      paperPacketOddPrimeColumns c m D * conj (paperPacketOddPrimeColumns c k D) =
      (if D.1 ⊆ (m : ℕ).primeFactors ∧ D.1 ⊆ (k : ℕ).primeFactors then
        (-1 : ℂ) ^ D.1.card else 0) *
          (paperPacketNonunitCoeff c m * conj (paperPacketNonunitCoeff c k)) := by
  by_cases hD : Even D.1.card <;>
    by_cases hm : D.1 ⊆ (m : ℕ).primeFactors <;>
    by_cases hk : D.1 ⊆ (k : ℕ).primeFactors <;>
    simp [paperPacketEvenPrimeColumns, paperPacketOddPrimeColumns,
      paperPacketPrimeMask, neg_one_pow_eq_ite, hD, hm, hk]

/-- Difference of two genuine positive Gram covariances is exactly the coprime part. -/
theorem paperPacket_prime_covariance_difference {N : ℕ} (c : PacketIndex N → ℂ) :
    paperPacketEvenPrimeColumns c * (paperPacketEvenPrimeColumns c)ᴴ -
      paperPacketOddPrimeColumns c * (paperPacketOddPrimeColumns c)ᴴ =
        paperPacketCoprimeCovariance c := by
  ext m k
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Finset.sum_sub_distrib]
  simp_rw [parity_entry]
  rw [← Finset.sum_mul, paperPacketPrimeMask_indicator]
  simp only [paperPacketCoprimeCovariance]
  split_ifs <;> simp

/-- Every integer multiplicative diagonal vanishes, including the diagonal at one. -/
theorem divisibilityTrace_paperPacketCoprimeCovariance {N : ℕ}
    (c : PacketIndex N → ℂ) (n : ℕ) :
    divisibilityTrace (paperPacketCoprimeCovariance c) n = 0 := by
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro k _
  by_cases hmk : n * (k : ℕ) = (m : ℕ)
  · rw [if_pos hmk]
    unfold paperPacketCoprimeCovariance
    by_cases hc : Nat.Coprime (m : ℕ) (k : ℕ)
    · have hc' : Nat.Coprime (n * (k : ℕ)) (k : ℕ) := by simpa only [hmk] using hc
      have hk : (k : ℕ) = 1 :=
        (Nat.coprime_self (k : ℕ)).mp (Nat.coprime_mul_iff_left.mp hc').2
      simp [paperPacketNonunitCoeff, hk]
    · simp [hc]
  · exact if_neg hmk

/-- The two positive Gram families have identical integer observations. -/
theorem divisibilityTrace_paperPacket_prime_parity {N : ℕ}
    (c : PacketIndex N → ℂ) (n : ℕ) :
    divisibilityTrace (paperPacketEvenPrimeColumns c * (paperPacketEvenPrimeColumns c)ᴴ) n =
      divisibilityTrace (paperPacketOddPrimeColumns c * (paperPacketOddPrimeColumns c)ᴴ) n := by
  apply sub_eq_zero.mp
  rw [← divisibilityTrace_sub, paperPacket_prime_covariance_difference,
    divisibilityTrace_paperPacketCoprimeCovariance]

/-- Exact cost of all prime-subset masks, weighted by the number of prime factors. -/
theorem paperPacketPrimeMask_total_coefficient_energy {N : ℕ} (c : PacketIndex N → ℂ) :
    (∑ D : PaperPacketPrimeIndex N, ∑ m : PacketIndex N, ‖paperPacketPrimeMask c m D‖ ^ 2) =
      ∑ m : PacketIndex N, (2 : ℝ) ^ (m : ℕ).primeFactors.card *
        ‖paperPacketNonunitCoeff c m‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  have heq : (paperPacketPrimeSet N).powerset.filter (fun D => D ⊆ (m : ℕ).primeFactors) =
      (m : ℕ).primeFactors.powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.trans (paperPacket_primeFactors_subset m), h⟩⟩
  have hite (D : Finset ℕ) :
      ‖if D ⊆ (m : ℕ).primeFactors then paperPacketNonunitCoeff c m else 0‖ ^ 2 =
        if D ⊆ (m : ℕ).primeFactors then ‖paperPacketNonunitCoeff c m‖ ^ 2 else 0 := by
    split_ifs <;> simp
  change (∑ D : PaperPacketPrimeIndex N,
    ‖if D.1 ⊆ (m : ℕ).primeFactors then paperPacketNonunitCoeff c m else 0‖ ^ 2) = _
  rw [← Finset.sum_subtype (p := fun D : Finset ℕ => D ∈ (paperPacketPrimeSet N).powerset)
    (paperPacketPrimeSet N).powerset (fun _ => Iff.rfl)
    (fun D => ‖if D ⊆ (m : ℕ).primeFactors then paperPacketNonunitCoeff c m else 0‖ ^ 2)]
  simp_rw [hite]
  rw [← Finset.sum_filter, heq]
  simp

/-- Both positive families together spend exactly the source's prime-support energy. -/
theorem paperPacket_prime_parity_total_energy {N : ℕ} (c : PacketIndex N → ℂ) :
    finiteMatrixHilbertSchmidtSq (paperPacketEvenPrimeColumns c) +
      finiteMatrixHilbertSchmidtSq (paperPacketOddPrimeColumns c) =
        ∑ m : PacketIndex N, (2 : ℝ) ^ (m : ℕ).primeFactors.card *
          ‖paperPacketNonunitCoeff c m‖ ^ 2 := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ m : PacketIndex N, ∑ D : PaperPacketPrimeIndex N, ‖paperPacketPrimeMask c m D‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro D _
      by_cases hD : Even D.1.card <;>
        simp [paperPacketEvenPrimeColumns, paperPacketOddPrimeColumns, hD]
    _ = _ := by rw [Finset.sum_comm, paperPacketPrimeMask_total_coefficient_energy]

/-- Exact coefficient energy retained by the coprime projection. -/
def paperPacketCoprimeCoefficientEnergy {N : ℕ} (c : PacketIndex N → ℂ) : ℝ :=
  ∑ m : PacketIndex N, ∑ k : PacketIndex N,
    if Nat.Coprime (m : ℕ) (k : ℕ) then
      ‖paperPacketNonunitCoeff c m‖ ^ 2 * ‖paperPacketNonunitCoeff c k‖ ^ 2 else 0

theorem paperPacketCoprimeCovariance_energy {N : ℕ} (c : PacketIndex N → ℂ) :
    finiteMatrixHilbertSchmidtSq (paperPacketCoprimeCovariance c) =
      paperPacketCoprimeCoefficientEnergy c := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  change ‖(if Nat.Coprime (m : ℕ) (k : ℕ) then
    paperPacketNonunitCoeff c m * conj (paperPacketNonunitCoeff c k) else 0 : ℂ)‖ ^ 2 =
      if Nat.Coprime (m : ℕ) (k : ℕ) then
        ‖paperPacketNonunitCoeff c m‖ ^ 2 * ‖paperPacketNonunitCoeff c k‖ ^ 2 else 0
  by_cases h : Nat.Coprime (m : ℕ) (k : ℕ)
  · rw [if_pos h, if_pos h]
    simp only [norm_mul, ← Complex.star_def, norm_star, mul_pow]
  · rw [if_neg h, if_neg h]
    simp

end RHTower.WeilWorkPBAP
