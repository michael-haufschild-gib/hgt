import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerParabolicCrossing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerOpenCellWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PatternCharacterGroups

/-! The open-cell calculation for Whittaker traces applies to all class
functions. This permits its use on twisted mirabolic means. -/

noncomputable section
open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- The Whittaker trace is the pairing with the Whittaker character on the unipotent subgroup. -/
theorem wh_eq_restricted_pairing_of_function (ψ : AddChar (ZMod g) ℂ) {n : ℕ}
    (f : Gn g n → ℂ) :
    wh ψ f =
      characterPairing (upperUnitriangular g n)
        (fun u => (whittakerCharacter ψ n u : ℂ)) (fun u => f u.val) := by
  unfold wh eU
  rw [tr_eDat_of_subgroup _ _ ψ (upperUnitriangular g n) (fun _ => mem_upperUnitriangular.symm),
    characterPairing]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_inv (whittakerCharacter ψ n), Units.val_inv_eq_inv_val, mul_comm]
  rfl

/-- The Whittaker trace in rank zero is evaluation at the identity. -/
theorem wh_rank_zero (ψ : AddChar (ZMod g) ℂ) (f : Gn g 0 → ℂ) : wh ψ f = f 1 := by
  letI : Unique (upperUnitriangular g 0) :=
    ⟨⟨1⟩, fun u => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have hcard : Nat.card (upperUnitriangular g 0) = 1 := Nat.card_unique
  rw [wh_eq_restricted_pairing_of_function, characterPairing,
    Fintype.sum_subsingleton _ (1 : upperUnitriangular g 0), hcard]
  simp

private theorem whittaker_overlap_openCell_function (ψ : AddChar (ZMod g) ℂ)
    (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    doubleCosetPairing (upperUnitriangular g (a + b)) (twoBlockParabolic g a b)
      (fun u => (whittakerCharacter ψ (a + b) u : ℂ))
      (fun p => α (twoBlockLevi p).1 * β (twoBlockLevi p).2)
      (permutationUnit (openCellPermutation a b)) = wh ψ α * wh ψ β := by
  let O := openCellOverlap g a b
  letI : Fintype O := Fintype.ofFinite O
  let A := upperUnitriangular g a
  let B := upperUnitriangular g b
  let e : O ≃* A × B := openCellOverlapEquiv
  let f (x : A) := α x.val * (whittakerCharacter ψ a x⁻¹ : ℂ)
  let h (y : B) := β y.val * (whittakerCharacter ψ b y⁻¹ : ℂ)
  let c : ℂ := Nat.card A
  let d : ℂ := Nat.card B
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hCard : (Nat.card O : ℂ) = c * d := by
    change _ = (Nat.card A : ℂ) * Nat.card B
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.cast_mul]
  have hSum : (∑ u : O, α (e u).1.val * β (e u).2.val *
      (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ)) = (∑ x : A, f x) * ∑ y : B, h y := by
    calc
      _ = ∑ z : A × B, f z.1 * h z.2 := by
        refine Fintype.sum_equiv e.toEquiv _ _ fun u => ?_
        change α (e u).1.val * β (e u).2.val * (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ) =
          f (e u).1 * h (e u).2
        rw [whittakerCharacter_openCell ψ (u⁻¹ : O),
          show openCellProjection (u⁻¹ : O) = (e u)⁻¹ from map_inv e u]
        dsimp only [f, h]
        let x := (e u).1
        let y := (e u).2
        let s : ℂ := whittakerCharacter ψ a x⁻¹
        let t : ℂ := whittakerCharacter ψ b y⁻¹
        change α x.val * β y.val * (s * t) = (α x.val * s) * (β y.val * t)
        ring
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul]; simp only [Finset.mul_sum]
  rw [doubleCosetPairing_eq_pairing, wh_eq_restricted_pairing_of_function ψ α,
    wh_eq_restricted_pairing_of_function ψ β]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O, α (e u).1.val * β (e u).2.val *
      (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ)) =
    (c⁻¹ * ∑ x : A, f x) * (d⁻¹ * ∑ y : B, h y)
  rw [hCard, hSum]
  field_simp [hc, hd]

/-- The Whittaker trace of a Harish–Chandra product factors for class functions. -/
theorem wh_hc_mul_of_isClass (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {α : Gn g a → ℂ} {β : Gn g b → ℂ} (hα : IsClass α) (hβ : IsClass β) :
    wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  let θ := whittakerCharacter ψ (a + b)
  let F (u : U) : ℂ := θ u
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  let B (p : P) : ℂ := α (π p).1 * β (π p).2
  let Q := DoubleCoset.Quotient (U : Set (Gn g (a + b))) P
  letI : Fintype Q := mixedDoubleCosetFintype U P
  let w : Gn g (a + b) := permutationUnit (openCellPermutation a b)
  let q₀ := DoubleCoset.mk U P w
  have hF (u v : U) : F (v * u * v⁻¹) = F u := by
    have h : θ (v * u * v⁻¹) = θ u := by
      simp only [map_mul, map_inv]
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    exact congrArg (fun t : ℂˣ => (t : ℂ)) h
  have hB (u v : P) : B (v * u * v⁻¹) = B u := by
    change α (π (v * u * v⁻¹)).1 * β (π (v * u * v⁻¹)).2 = α (π u).1 * β (π u).2
    rw [map_mul, map_mul, map_inv]
    exact congrArg₂ (· * ·) (hα (π u).1 (π v).1) (hβ (π u).2 (π v).2)
  have hz (q : Q) (hq : q ≠ q₀) : doubleCosetPairing U P F B q.out = 0 := by
    obtain ⟨σ, hσ⟩ := exists_parabolic_permutation_rep (g := g) (a := a) (b := b) q.out
    have hne : firstBlockImage σ ≠ firstBlockImage (openCellPermutation a b) := by
      intro h
      apply hq
      exact ((DoubleCoset.out_eq' U P q).symm.trans hσ.symm).trans
        (parabolic_coset_eq_of_firstBlockImage_eq (g := g) σ (openCellPermutation a b) h).symm
    exact (doubleCosetPairing_eq_of_mk_eq U P F B hF hB hσ.symm).trans
      (whittaker_overlap_eq_zero_of_crossing ψ hψ σ hne α β)
  calc
    wh ψ (hc a b α β (a + b)) =
        characterPairing U F (fun u => inducedFunction P B u.val) := by
      rw [wh_eq_restricted_pairing_of_function, hc_eq_inducedFunction]
    _ = ∑ q : Q, doubleCosetPairing U P F B q.out :=
      characterPairing_restrict_induced_doubleCosets U P F B hF hB
    _ = doubleCosetPairing U P F B q₀.out :=
      Finset.sum_eq_single_of_mem q₀ (Finset.mem_univ q₀) (fun q _ h => hz q h)
    _ = doubleCosetPairing U P F B w :=
      doubleCosetPairing_eq_of_mk_eq U P F B hF hB (DoubleCoset.out_eq' U P q₀)
    _ = _ := whittaker_overlap_openCell_function ψ α β

end GlobalTheory.GLq
