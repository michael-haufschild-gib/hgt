import GaloisForLFunctions.RHTower.SlabGermResidueTransport
import GaloisForLFunctions.HTGeometry.HermiteBiehlerPairRankCensus
import GaloisForLFunctions.HTGeometry.FiniteMomentDivisorReconstruction

/-!
# The Hedenmalm value reads the distinct Xi-zero census

The finite Weierstrass polynomial of a Xi packet carries the divisor with its analytic
multiplicities.  Multiplication by the de Branges value `E = F + i F'` on the resulting finite local
algebra has rank the number of *distinct* zeros and nullity the multiplicity excess, so the census
is a rank of one canonical finite operator built from the entire pair.

The boundary reader is unconditional: the contour power moments of the packet are its
multiplicity-weighted divisor moments, and finitely many of them already determine the divisor and
hence the Weierstrass polynomial.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The analytic multiplicity of a centered Xi zero. -/
def xiMult (w : ℂ) : ℕ := (analyticOrderAt XiC w).toNat

theorem xiMult_pos {w : ℂ} (hw : XiC w = 0) : 0 < xiMult w := by
  have h := SlabGermResidueTransport.xiPacketMass_pos hw
  simpa [SlabGermResidueTransport.xiPacketMass, xiMult] using h

/-- The Xi divisor of a finite packet, as a multiset with analytic multiplicities. -/
def xiPacketDivisor (P : Finset ℂ) : Multiset ℂ :=
  P.val.bind (fun w => Multiset.replicate (xiMult w) w)

/-- The monic Weierstrass polynomial carrying the Xi divisor of a finite packet. -/
def xiPacketWeierstrass (P : Finset ℂ) : ℂ[X] :=
  ∏ w ∈ P, (X - C w) ^ xiMult w

theorem xiPacketWeierstrass_monic (P : Finset ℂ) : (xiPacketWeierstrass P).Monic :=
  monic_prod_of_monic _ _ fun w _ => (monic_X_sub_C w).pow _

theorem xiPacketWeierstrass_ne_zero (P : Finset ℂ) : xiPacketWeierstrass P ≠ 0 :=
  (xiPacketWeierstrass_monic P).ne_zero

theorem natDegree_xiPacketWeierstrass (P : Finset ℂ) :
    (xiPacketWeierstrass P).natDegree = ∑ w ∈ P, xiMult w := by
  classical
  rw [xiPacketWeierstrass, natDegree_prod _ _ (fun w _ => pow_ne_zero _ (X_sub_C_ne_zero w))]
  exact Finset.sum_congr rfl fun w _ => by rw [natDegree_pow, natDegree_X_sub_C, mul_one]

theorem roots_xiPacketWeierstrass (P : Finset ℂ) :
    (xiPacketWeierstrass P).roots = xiPacketDivisor P := by
  classical
  rw [xiPacketWeierstrass, roots_prod _ _ (xiPacketWeierstrass_ne_zero P), xiPacketDivisor]
  refine congrArg (Multiset.bind P.val) (funext fun w => ?_)
  rw [roots_pow, roots_X_sub_C, Multiset.nsmul_singleton]

theorem roots_toFinset_xiPacketWeierstrass {P : Finset ℂ}
    (hP : ∀ w ∈ P, XiC w = 0) :
    (xiPacketWeierstrass P).roots.toFinset = P := by
  classical
  ext w
  rw [Multiset.mem_toFinset, roots_xiPacketWeierstrass, xiPacketDivisor,
    Multiset.mem_bind]
  constructor
  · rintro ⟨v, hv, hmem⟩
    rw [Multiset.eq_of_mem_replicate hmem]
    exact hv
  · intro hw
    exact ⟨w, hw, Multiset.mem_replicate.2 ⟨(xiMult_pos (hP w hw)).ne', rfl⟩⟩

/-- The `k`-th power moment of the packet divisor is its multiplicity-weighted divisor moment. -/
theorem powerSum_xiPacketDivisor (P : Finset ℂ) (k : ℕ) :
    ((xiPacketDivisor P).map (fun x => x ^ k)).sum =
      SlabGermResidueTransport.packetDivisorMoment P k := by
  classical
  rw [xiPacketDivisor, Multiset.map_bind, Multiset.sum_bind,
    SlabGermResidueTransport.packetDivisorMoment, ← Finset.sum_map_val]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun w _ => ?_)
  rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul, xiMult]

/-- **Boundary reader.**  The Xi divisor of a packet is determined by finitely many
multiplicity-weighted moments, hence so is its Weierstrass polynomial and the distinct-zero
census. -/
theorem xiPacketDivisor_eq_of_moments {P : Finset ℂ} {N : Multiset ℂ}
    (hcard : Multiset.card N = ∑ w ∈ P, xiMult w)
    (hmom : ∀ k ≤ ∑ w ∈ P, xiMult w,
      (N.map (fun x => x ^ k)).sum = SlabGermResidueTransport.packetDivisorMoment P k) :
    N = xiPacketDivisor P := by
  classical
  have hsplit : (xiPacketWeierstrass P).Splits := IsAlgClosed.splits _
  have hcardD : Multiset.card (xiPacketDivisor P) = ∑ w ∈ P, xiMult w := by
    rw [← roots_xiPacketWeierstrass, ← hsplit.natDegree_eq_card_roots,
      natDegree_xiPacketWeierstrass]
  refine GaloisForLFunctions.multiset_eq_of_powerSum_eq_le (by omega) ?_
  intro k hk
  rw [powerSum_xiPacketDivisor]
  exact hmom k (by omega)

/-- **Rank census.**  Multiplication by the de Branges value of the packet source on the finite
local algebra of the Weierstrass polynomial has rank exactly the number of distinct Xi zeros in the
packet. -/
theorem finrank_range_xiPacketDeBrangesMul {P : Finset ℂ} (hP : ∀ w ∈ P, XiC w = 0)
    (H : ℂ[X]) (hcop : IsCoprime (xiPacketWeierstrass P) H) :
    Module.finrank ℂ (LinearMap.range
        (GaloisForLFunctions.HTGeometry.polyQuotMul (xiPacketWeierstrass P)
          (GaloisForLFunctions.HTGeometry.deBrangesValue (xiPacketWeierstrass P * H)))) =
      P.card := by
  rw [GaloisForLFunctions.HTGeometry.finrank_range_polyQuotMul_deBrangesValue
      _ H (xiPacketWeierstrass_ne_zero P) hcop,
    roots_toFinset_xiPacketWeierstrass hP]

/-- **Nullity census.**  The kernel dimension is the multiplicity excess. -/
theorem finrank_ker_xiPacketDeBrangesMul {P : Finset ℂ} (hP : ∀ w ∈ P, XiC w = 0)
    (H : ℂ[X]) (hcop : IsCoprime (xiPacketWeierstrass P) H) :
    Module.finrank ℂ (LinearMap.ker
        (GaloisForLFunctions.HTGeometry.polyQuotMul (xiPacketWeierstrass P)
          (GaloisForLFunctions.HTGeometry.deBrangesValue (xiPacketWeierstrass P * H)))) =
      (∑ w ∈ P, xiMult w) - P.card := by
  rw [GaloisForLFunctions.HTGeometry.finrank_ker_polyQuotMul_deBrangesValue
      _ H (xiPacketWeierstrass_ne_zero P) hcop,
    roots_toFinset_xiPacketWeierstrass hP, natDegree_xiPacketWeierstrass]

/-- **Total dimension.**  The finite local algebra has dimension the total multiplicity. -/
theorem finrank_xiPacketQuot (P : Finset ℂ) :
    Module.finrank ℂ (GaloisForLFunctions.HTGeometry.polyQuot (xiPacketWeierstrass P)) =
      ∑ w ∈ P, xiMult w := by
  rw [GaloisForLFunctions.HTGeometry.finrank_polyQuot _ (xiPacketWeierstrass_ne_zero P),
    natDegree_xiPacketWeierstrass]

/-- The census congruence is exactly divisibility of the distinct-zero count. -/
theorem census_congruence_iff_dvd {P : Finset ℂ} (hP : ∀ w ∈ P, XiC w = 0) (k : ℕ) :
    Nat.ModEq (2 ^ k) (∑ w ∈ P, xiMult w) ((∑ w ∈ P, xiMult w) - P.card) ↔
      2 ^ k ∣ P.card := by
  classical
  have hle : P.card ≤ ∑ w ∈ P, xiMult w := by
    calc P.card = ∑ _w ∈ P, 1 := by simp
      _ ≤ ∑ w ∈ P, xiMult w := Finset.sum_le_sum fun w hw => xiMult_pos (hP w hw)
  constructor
  · intro h
    have h2 := (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).mp h.symm
    rwa [Nat.sub_sub_self hle] at h2
  · intro h
    refine Nat.ModEq.symm ((Nat.modEq_iff_dvd' (Nat.sub_le _ _)).mpr ?_)
    rwa [Nat.sub_sub_self hle]

/-- **Height-adaptive census collapse.**  A distinct-zero census divisible by a power of two above
the packet envelope forces the packet to be empty. -/
theorem xiPacket_eq_empty_of_census_congruence {P : Finset ℂ} {k N : ℕ}
    (hbound : P.card ≤ N) (hlt : N < 2 ^ k) (hcong : 2 ^ k ∣ P.card) : P = ∅ :=
  Finset.card_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hcong (by omega))

end

end RHTower
