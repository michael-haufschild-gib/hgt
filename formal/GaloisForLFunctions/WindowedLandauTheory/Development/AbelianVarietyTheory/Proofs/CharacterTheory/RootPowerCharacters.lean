import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdamsCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.BrauerLift
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.BrauerRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.NilpotentPrimeComplement
import GaloisForLFunctions.RHTower.Artin.ArtinBrauerInductionTheorem

/-! The power sums of lifted characteristic roots on a finite general linear group are virtual. -/

open GaloisForLFunctions Polynomial

namespace GlobalTheory.CuspGL

private theorem power_sum_mem_virtual_of_nonmodular {k G : Type} [Field k] [IsAlgClosed k]
    [Group G] [Finite G] [Group.IsNilpotent G] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (hc : (Nat.card G : k) ≠ 0) {n : ℕ} (ρ : G →* GL (Fin n) k) (r : ℕ) :
    (fun g => (Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots)).sum) ∈
      virtualCharacterGroup G := by
  obtain ⟨m, L, hL⟩ := exists_matrix_brauer_lift k θ hθ G hc n ρ
  convert complex_root_power_sum_mem_virtual L r using 1
  funext g
  have hm : Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots) =
      Multiset.map θ ((ρ (g ^ r) : Matrix (Fin n) (Fin n) k).charpoly.roots) := by
    rw [map_pow, Units.val_pow_eq_pow_val, GlobalTheory.CharpolyPow.roots_charpoly_pow, Multiset.map_map]
    simp [map_pow]
  rw [hm, hL (g ^ r), map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
    GlobalTheory.CharpolyPow.roots_charpoly_pow]

private theorem power_sum_mem_virtual_of_nilpotent {k G : Type} [Field k] [IsAlgClosed k]
    [Group G] [Finite G] [Group.IsNilpotent G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (θ : k →* ℂ) (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {n : ℕ} (ρ : G →* GL (Fin n) k) (r : ℕ) :
    (fun g => (Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots)).sum) ∈
      virtualCharacterGroup G := by
  obtain ⟨H, π, hH, hsplit⟩ := exists_primeComplement G p
  have hc : (Nat.card H : k) ≠ 0 := (CharP.cast_eq_zero_iff k p _).not.mpr hH
  have hvirt := power_sum_mem_virtual_of_nonmodular θ hθ hc (ρ.comp H.subtype) r
  have hcomp := (VirtualCharacter.restrict H π ⟨_, hvirt⟩).property
  convert hcomp using 1
  funext g
  obtain ⟨s, m, hg, hcomm, hs⟩ := hsplit g
  change ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots.map (fun α => θ α ^ r)).sum =
    ((ρ (π g : G) : Matrix (Fin n) (Fin n) k).charpoly.roots.map (fun α => θ α ^ r)).sum
  congr 2
  conv_lhs => rw [hg, map_mul, Units.val_mul]
  have hinj : Function.Injective (fun x : k => x ^ p ^ m) := iterateFrobenius_inj k p m
  apply Multiset.map_injective hinj
  rw [← GlobalTheory.CharpolyPow.roots_charpoly_pow, ← GlobalTheory.CharpolyPow.roots_charpoly_pow]
  have hm := (hcomm.map ρ).units_val
  rw [hm.mul_pow, ← Units.val_pow_eq_pow_val (ρ s), ← map_pow, hs, map_one, Units.val_one, mul_one]

/-- Brauer induction reduces the root sum to its restrictions to finite nilpotent subgroups. -/
theorem rootSum_charpoly_mem_virtual (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n r : ℕ) :
    (fun x : GL (Fin n) F => rootSum θ r (x : Matrix (Fin n) (Fin n) F).charpoly) ∈
      virtualCharacterGroup (GL (Fin n) F) := by
  classical
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  refine virtual_of_brauer_restrictions _ ?_ ?_
  · intro x g
    congr 1
    simpa [Units.val_mul] using
      Matrix.charpoly_units_conj x (g : Matrix (Fin n) (Fin n) F)
  · rintro _ ⟨E, rfl⟩
    letI := E.isNilpotent
    obtain ⟨p, hp⟩ := CharP.exists F
    letI : CharP F p := hp
    letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    letI : CharP (AlgebraicClosure F) p :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
    let ρ : E.subgroup →* GL (Fin n) (AlgebraicClosure F) :=
      (Units.map (algebraMap F (AlgebraicClosure F)).mapMatrix.toMonoidHom).comp E.subgroup.subtype
    convert power_sum_mem_virtual_of_nilpotent p θ hθ ρ r using 1
    funext x
    unfold rootSum
    congr 3
    simp [ρ, Matrix.charpoly_map]

end GlobalTheory.CuspGL
