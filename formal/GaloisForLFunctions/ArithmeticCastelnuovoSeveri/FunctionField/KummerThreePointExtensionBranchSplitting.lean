import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionBranchResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionSplitting

/-!
# The normalized branch fiber over extended constants

A constant residue of the balanced radical bounds the decomposition
group by `M / gcd(M,a)`. Radical-order divisibility gives the opposite
bound on ramification, so every residue degree is one. The fundamental
degree identity gives exactly `gcd(M,a)` primes above one. Inverse-power
coefficients supply the required residue root for every exponent,
including zero.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "N" => M - 1 + 1
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "F" => FractionRing E[X]

/-- The balanced residue bounds every decomposition character by the reduced covering degree. -/
theorem primePowerThreePointExtension_branch_character_pow
    (β : E) (hβ : β ≠ 0) (hpow : β ^ Nat.gcd N a = (c : E))
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})]
    (g : (w.valuation L).valuationSubring.decompositionSubgroup F) :
    (((primePowerThreePointExtensionAutEquiv p d n E c a).symm g : Eˣ) : E) ^
      (N / Nat.gcd N a) = 1 := by
  let σ : L ≃ₐ[F] L := g
  let ζ := (primePowerThreePointExtensionAutEquiv p d n E c a).symm σ
  let u := primePowerThreePointExtensionBranchUnit p d n E c a w
  let f := heightOnePolynomialConstantHom (K := E) («L» := L) w
  obtain ⟨t, ht⟩ := primePowerThreePointExtension_branchUnit_residue_constant
    p d n E c a β hβ hpow w
  have hfix : g • f t = f t := by
    apply Subtype.ext
    change σ (f t : L) = (f t : L)
    rw [heightOnePolynomialConstantHom_coe, IsScalarTower.algebraMap_apply E F L, σ.commutes]
  have hunit : w.valuation L (u : L) = 1 :=
    primePowerThreePointExtension_branchUnit_valuation_one p d n E c a w
  have hzσ := primePowerThreePointExtensionAutEquiv_root p d n E c a ζ
  rw [MulEquiv.apply_symm_apply] at hzσ
  have htσ : σ (algebraMap E[X] L (1 - X ^ (0 + 1))) =
      algebraMap E[X] L (1 - X ^ (0 + 1)) := by
    rw [IsScalarTower.algebraMap_apply E[X] F L, σ.commutes]
  apply decomposition_unit_character_eq_one (w.valuation L) f
    (fun x hx => by rw [heightOnePolynomialConstantHom_coe]; exact heightOne_valuation_constant w x hx)
    g hunit ht.symm hfix
  apply Subtype.ext
  change σ (kummerBranchUnitRoot c 0 a (M - 1)) =
    (f (((ζ : Eˣ) : E) ^ (N / Nat.gcd N a)) : L) * kummerBranchUnitRoot c 0 a (M - 1)
  rw [heightOnePolynomialConstantHom_coe, kummerBranchUnitRoot, map_div₀, map_pow, map_pow,
    hzσ, htσ, mul_pow, ← map_pow, mul_div_assoc]

/-- The full decomposition group has at most the reduced covering degree many elements. -/
theorem primePowerThreePointExtension_branch_decomposition_card_le
    (β : E) (hβ : β ≠ 0) (hpow : β ^ Nat.gcd N a = (c : E))
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    Nat.card ((w.valuation L).valuationSubring.decompositionSubgroup F) ≤ N / Nat.gcd N a := by
  classical
  letI := primePowerThreePointExtension_isGalois p d n E c a
  let G := (w.valuation L).valuationSubring.decompositionSubgroup F
  let D := N / Nat.gcd N a
  have hD : 0 < D := Nat.div_pos
    (Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left N a))
    (Nat.gcd_pos_of_pos_left a (Nat.succ_pos _))
  let j : G → E := fun g => (((primePowerThreePointExtensionAutEquiv p d n E c a).symm g : Eˣ) : E)
  have hj : Function.Injective j := by
    intro g h hgh
    apply Subtype.ext
    apply (primePowerThreePointExtensionAutEquiv p d n E c a).symm.injective
    apply Subtype.ext
    exact Units.ext hgh
  have hmem : ∀ g : G, j g ∈ (Polynomial.nthRoots D (1 : E)).toFinset := by
    intro g
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hD]
    exact primePowerThreePointExtension_branch_character_pow p d n E c a β hβ hpow w g
  have hcard : Nat.card G ≤ Nat.card {x // x ∈ (Polynomial.nthRoots D (1 : E)).toFinset} :=
    Nat.card_le_card_of_injective (fun g : G => ⟨j g, hmem g⟩)
      (fun g h hgh => hj (congrArg Subtype.val hgh))
  rw [Nat.card_eq_finsetCard] at hcard
  exact hcard.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots D 1))

/-- Opposing order bounds force exact ramification and residue degree one at the branch. -/
theorem primePowerThreePointExtension_branch_indices
    (β : E) (hβ : β ≠ 0) (hpow : β ^ Nat.gcd N a = (c : E))
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal = M / Nat.gcd M a ∧
      (Ideal.span {X - C (1 : E)}).inertiaDeg' w.asIdeal = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (1 : E))
  letI : (Ideal.span {X - C (1 : E)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hN := primePowerThreePointExtension_branch_decomposition_card_le p d n E c a β hβ hpow w
  rw [primePowerThreePointExtension_decomposition_card p d n E c a 1 w] at hN
  have h : (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal *
      (Ideal.span {X - C (1 : E)}).inertiaDeg' w.asIdeal ≤ M / Nat.gcd M a :=
    hN.trans_eq (congrArg (fun k : ℕ => k / Nat.gcd k a)
      (primePowerThreePointExtension_index p d n))
  have hD : 0 < M / Nat.gcd M a := Nat.div_pos
    (Nat.le_of_dvd (primePowerKummerCyclicDegree_pos p d n) (Nat.gcd_dvd_left M a))
    (Nat.gcd_pos_of_pos_left a (primePowerKummerCyclicDegree_pos p d n))
  have hfpos := Nat.pos_of_ne_zero
    (Ideal.inertiaDeg'_ne_zero (Ideal.span {X - C (1 : E)}) w.asIdeal)
  have he : (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal = M / Nat.gcd M a :=
    Nat.le_antisymm ((Nat.le_mul_of_pos_right _ hfpos).trans h)
      (Nat.le_of_dvd (primePowerThreePointExtension_ramification_pos p d n E c a 1 w)
        (primePowerThreePointExtension_one_ramification_gcd_dvd p d n E c a w))
  refine ⟨he, Nat.le_antisymm ?_ hfpos⟩
  rw [he] at h
  exact le_of_mul_le_mul_left (a := M / Nat.gcd M a)
    (by simpa only [mul_one] using h) hD

/-- The complete normalized branch fiber has exactly the branch gcd many primes. -/
theorem primePowerThreePointExtension_branch_primes_card
    (β : E) (hβ : β ≠ 0) (hpow : β ^ Nat.gcd N a = (c : E)) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C (1 : E)}) B).card = Nat.gcd M a := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (1 : E))
  let T := IsDedekindDomain.primesOverFinset (Ideal.span {X - C (1 : E)}) B
  let D := M / Nat.gcd M a
  letI : (Ideal.span {X - C (1 : E)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C (1 : E)}) ≠ ⊥ := v.ne_bot
  have hD : 0 < D := Nat.div_pos
    (Nat.le_of_dvd (primePowerKummerCyclicDegree_pos p d n) (Nat.gcd_dvd_left M a))
    (Nat.gcd_pos_of_pos_left a (primePowerKummerCyclicDegree_pos p d n))
  have hterm : ∀ P ∈ T, (Ideal.span {X - C (1 : E)}).ramificationIdx' P *
      (Ideal.span {X - C (1 : E)}).inertiaDeg' P = D := by
    intro P hP
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
    letI := hprime
    letI := hover
    let w : HeightOneSpectrum B := ⟨P, hprime, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
    obtain ⟨he, hf⟩ := primePowerThreePointExtension_branch_indices p d n E c a β hβ hpow w
    change (Ideal.span {X - C (1 : E)}).ramificationIdx' P = D at he
    change (Ideal.span {X - C (1 : E)}).inertiaDeg' P = 1 at hf
    rw [he, hf, mul_one]
  have hsum := Ideal.sum_ramification_inertia B F L hv0
  rw [primePowerThreePointExtension_finrank] at hsum
  have hcount : T.card * D = M := by
    calc
      T.card * D = ∑ P ∈ T, D := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ = ∑ P ∈ T, (Ideal.span {X - C (1 : E)}).ramificationIdx' P *
          (Ideal.span {X - C (1 : E)}).inertiaDeg' P :=
        Finset.sum_congr rfl (fun P hP => (hterm P hP).symm)
      _ = M := hsum
  apply Nat.eq_of_mul_eq_mul_left hD
  exact (Nat.mul_comm D T.card).trans
    (hcount.trans (Nat.div_mul_cancel (Nat.gcd_dvd_left M a)).symm)

/-- Inverse-power coefficients make every prime above one rational with exact reduced ramification. -/
theorem primePowerThreePointExtension_inversePower_branch_indices (η : Eˣ)
    (w : HeightOneSpectrum (PrimePowerThreePointExtensionNormalization p d n E ((η⁻¹) ^ a) a))
    [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal = M / Nat.gcd M a ∧
      (Ideal.span {X - C (1 : E)}).inertiaDeg' w.asIdeal = 1 := by
  obtain ⟨β, hβ, hpow⟩ := primePowerThreePointExtension_inversePower_residue_root p d n E a η
  exact primePowerThreePointExtension_branch_indices p d n E ((η⁻¹) ^ a) a β hβ hpow w

/-- For every exponent, the inverse-power family has exactly the branch gcd many rational primes above one. -/
theorem primePowerThreePointExtension_inversePower_branch_primes_card (η : Eˣ) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C (1 : E)})
      (PrimePowerThreePointExtensionNormalization p d n E ((η⁻¹) ^ a) a)).card = Nat.gcd M a := by
  obtain ⟨β, hβ, hpow⟩ := primePowerThreePointExtension_inversePower_residue_root p d n E a η
  exact primePowerThreePointExtension_branch_primes_card p d n E ((η⁻¹) ^ a) a β hβ hpow

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
