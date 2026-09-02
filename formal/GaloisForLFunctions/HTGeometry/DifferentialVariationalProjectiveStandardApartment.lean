import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveBuildingCarrier

/-!
# Standard apartment in the correctly oriented projective carrier

The first lattice carrier used right homothety, which is not compatible with arbitrary left-linear
maps over a noncommutative skew field.  The projective carrier corrects this to left homothety.
This leaf proves that the same integral coweight apartment embeds in that corrected carrier.

Although left multiplication by a uniformizer power is not coordinatewise right multiplication,
the two descriptions give the same coweight translation.  Conjugation by a completed-skew unit
preserves the valuation ring; this supplies the exact noncommutative argument.  Consequently two
diagonal coweight lattices are left-homothetic exactly when their coweights differ by one common
integer.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- Two integer powers of the same completed pseudodifferential uniformizer commute. -/
theorem completedPseudoDiffOpUniformizerUnit_zpow_comm (a b : ℤ) :
    completedPseudoDiffOpUniformizerUnit (K := K) ^ a *
      completedPseudoDiffOpUniformizerUnit (K := K) ^ b =
    completedPseudoDiffOpUniformizerUnit (K := K) ^ b *
      completedPseudoDiffOpUniformizerUnit (K := K) ^ a :=
  ((Commute.refl (completedPseudoDiffOpUniformizerUnit (K := K))).zpow_zpow a b).eq

/-- Inverting a sum-power of the uniformizer splits in coweight order. -/
theorem completedPseudoDiffOpUniformizerUnit_zpow_add_inv (a b : ℤ) :
    (completedPseudoDiffOpUniformizerUnit (K := K) ^ (a + b))⁻¹ =
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ a)⁻¹ *
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ b)⁻¹ := by
  rw [zpow_add, mul_inv_rev]
  simpa only [zpow_neg] using
    completedPseudoDiffOpUniformizerUnit_zpow_comm (K := K) (-b) (-a)

/-- Left multiplication by a uniformizer power adds the same integer to every coweight. -/
theorem leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const
    (m : ι → ℤ) (c : ℤ) :
    leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ c)
        (standardCompletedPseudoDiffOpLatticeAtCoweight m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (m + fun _ => c) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff,
    mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hx
    intro i
    have hi := innerCompletedPseudoDiffOp_mem_integer
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ c)
      ⟨x i * ((completedPseudoDiffOpUniformizerCoweight m i)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ), hx i⟩
    have hinv := congrArg
      (fun q : (CompletedPseudoDiffOp K)ˣ => (q : CompletedPseudoDiffOp K))
      (completedPseudoDiffOpUniformizerUnit_zpow_add_inv (K := K) (m i) c)
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ c :
      (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * x i *
        (((completedPseudoDiffOpUniformizerUnit (K := K) ^ (m i + c))⁻¹ :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) ∈
      CompletedPseudoDiffOpInteger (K := K)
    rw [hinv]
    simpa [completedPseudoDiffOpUniformizerCoweight, mul_assoc] using hi
  · intro hy
    let a : (CompletedPseudoDiffOp K)ˣ :=
      completedPseudoDiffOpUniformizerUnit (K := K) ^ c
    let x : ι → CompletedPseudoDiffOp K := fun i => (a⁻¹ : CompletedPseudoDiffOp K) * y i
    refine ⟨x, ?_, ?_⟩
    · rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
      intro i
      have hi := innerCompletedPseudoDiffOp_mem_integer a⁻¹
        ⟨y i * ((completedPseudoDiffOpUniformizerCoweight (m + fun _ => c) i)⁻¹ :
          (CompletedPseudoDiffOp K)ˣ), hy i⟩
      have hinv := congrArg
        (fun q : (CompletedPseudoDiffOp K)ˣ => (q : CompletedPseudoDiffOp K))
        (completedPseudoDiffOpUniformizerUnit_zpow_add_inv (K := K) (m i) c)
      let ac : CompletedPseudoDiffOp K :=
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ c :
          (CompletedPseudoDiffOp K)ˣ)
      have hac : ac ≠ 0 := Units.ne_zero _
      have hcancel : ac⁻¹ * ac = 1 := inv_mul_cancel₀ hac
      change (((a⁻¹ : (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
          (y i * ((completedPseudoDiffOpUniformizerCoweight (m + fun _ => c) i)⁻¹ :
            (CompletedPseudoDiffOp K)ˣ)) *
            (((a⁻¹)⁻¹ : (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)) ∈
        CompletedPseudoDiffOpInteger (K := K) at hi
      simp only [inv_inv] at hi
      dsimp [a, completedPseudoDiffOpUniformizerCoweight] at hi
      rw [hinv] at hi
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hi
      simp only [mul_assoc] at hi
      change ac⁻¹ * (y i *
        ((((completedPseudoDiffOpUniformizerUnit (K := K) ^ m i :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)⁻¹) * (ac⁻¹ * ac))) ∈
        CompletedPseudoDiffOpInteger (K := K) at hi
      rw [hcancel, mul_one] at hi
      simpa [x, a, completedPseudoDiffOpUniformizerCoweight, ac, mul_assoc] using hi
    · funext i
      change (a : CompletedPseudoDiffOp K) * ((a⁻¹ : CompletedPseudoDiffOp K) * y i) = y i
      rw [← mul_assoc]
      simp

/-- A left homothety from coweight `m` to `n` gives the coordinatewise valuation inequality. -/
theorem coweight_le_add_unit_of_leftScale_eq (m n : ι → ℤ)
    (a : (CompletedPseudoDiffOp K)ˣ)
    (hscale : leftScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLatticeAtCoweight m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight n) (i : ι) :
    n i ≤ m i + completedPseudoDiffOpUnitAddValue a := by
  classical
  let v := completedPseudoDiffOpCoweightBasisVector (K := K) m i
  have hv : v ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight m).carrier :=
    completedPseudoDiffOpCoweightBasisVector_mem m i
  have hva : leftMulCompletedPseudoIntegerVecSemilinearMap a v ∈
      (leftScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLatticeAtCoweight m)).carrier :=
    (mem_leftScaleCompletedPseudoDiffOpLattice_iff a _ _).2 ⟨v, hv, rfl⟩
  rw [hscale] at hva
  have hi := (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n _).1 hva i
  change (a : CompletedPseudoDiffOp K) * v i *
    ((completedPseudoDiffOpUniformizerCoweight n i)⁻¹ :
      (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K) at hi
  let u : (CompletedPseudoDiffOp K)ˣ := a *
    completedPseudoDiffOpUniformizerUnit (K := K) ^ m i *
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹
  have hu : (u : CompletedPseudoDiffOp K) ∈ CompletedPseudoDiffOpInteger (K := K) := by
    simpa [u, v, completedPseudoDiffOpCoweightBasisVector,
      leftMulCompletedPseudoIntegerVecSemilinearMap,
      diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
      completedPseudoDiffOpUniformizerCoweight, mul_assoc] using hi
  rw [coe_unit_mem_completedPseudoDiffOpInteger_iff] at hu
  dsimp [u] at hu
  rw [completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hu
  omega

/-- Exact corrected-orientation classification: two diagonal coweight lattices are left-homothetic
precisely when their weights differ by one common integer. -/
theorem standardCompletedPseudoDiffOpLattices_leftHomothetic_iff_coweightDiffersByConstant
    (m n : ι → ℤ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).LeftHomothetic
        (standardCompletedPseudoDiffOpLatticeAtCoweight n) ↔
      CoweightDiffersByConstant m n := by
  constructor
  · rintro ⟨a, hscale⟩
    let c := completedPseudoDiffOpUnitAddValue a
    have hle : ∀ i, n i ≤ m i + c :=
      fun i => coweight_le_add_unit_of_leftScale_eq m n a hscale i
    have hinv : leftScaleCompletedPseudoDiffOpLattice a⁻¹
        (standardCompletedPseudoDiffOpLatticeAtCoweight n) =
          standardCompletedPseudoDiffOpLatticeAtCoweight m := by
      calc
        leftScaleCompletedPseudoDiffOpLattice a⁻¹
            (standardCompletedPseudoDiffOpLatticeAtCoweight n) =
          leftScaleCompletedPseudoDiffOpLattice a⁻¹
            (leftScaleCompletedPseudoDiffOpLattice a
              (standardCompletedPseudoDiffOpLatticeAtCoweight m)) := by rw [hscale]
        _ = leftScaleCompletedPseudoDiffOpLattice (a⁻¹ * a)
              (standardCompletedPseudoDiffOpLatticeAtCoweight m) :=
          leftScaleCompletedPseudoDiffOpLattice_mul a a⁻¹ _
        _ = standardCompletedPseudoDiffOpLatticeAtCoweight m := by
          rw [show a⁻¹ * a = 1 by simp, leftScaleCompletedPseudoDiffOpLattice_one]
    have hge : ∀ i, m i ≤ n i - c := by
      intro i
      have h := coweight_le_add_unit_of_leftScale_eq n m a⁻¹ hinv i
      rw [completedPseudoDiffOpUnitAddValue_inv] at h
      exact h
    refine ⟨c, ?_⟩
    funext i
    dsimp
    have h1 := hle i
    have h2 := hge i
    omega
  · rintro ⟨c, rfl⟩
    exact ⟨completedPseudoDiffOpUniformizerUnit (K := K) ^ c,
      leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const m c⟩

/-- Canonical standard-apartment map into the correctly oriented projective carrier. -/
def differentialVariationalProjectiveStandardApartmentMap :
    DifferentialVariationalStandardApartmentCarrier ι →
      DifferentialVariationalProjectiveBuildingCarrier K ι :=
  Quotient.map (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)) (by
    intro m n h
    change CoweightDiffersByConstant m n at h
    apply
      (standardCompletedPseudoDiffOpLattices_leftHomothetic_iff_coweightDiffersByConstant
        (K := K) m n).2
    exact h)

/-- Correctly oriented standard-apartment map is injective. -/
theorem differentialVariationalProjectiveStandardApartmentMap_injective :
    Function.Injective
      (differentialVariationalProjectiveStandardApartmentMap (K := K) (ι := ι)) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ m =>
      induction y using Quotient.inductionOn with
      | _ n =>
          apply Quotient.sound
          change CoweightDiffersByConstant m n
          apply
            (standardCompletedPseudoDiffOpLattices_leftHomothetic_iff_coweightDiffersByConstant
              (K := K) m n).mp
          exact Quotient.exact hxy

/-- Rank two contains a non-base balanced point in the correctly oriented projective carrier. -/
theorem rankTwoBalancedProjectiveBuildingPoint_ne_base :
    differentialVariationalProjectiveStandardApartmentMap (K := K)
        (Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) rankTwoBalancedCoweight) ≠
      differentialVariationalProjectiveStandardApartmentMap
        (Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) (fun _ => 0)) := by
  intro h
  exact rankTwoBalancedApartmentPoint_ne_base
    (differentialVariationalProjectiveStandardApartmentMap_injective h)

/-- Differential coefficient automorphisms fix the corrected standard apartment pointwise. -/
theorem map_differentialVariationalProjectiveStandardApartmentMap
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x : DifferentialVariationalStandardApartmentCarrier ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ
        (differentialVariationalProjectiveStandardApartmentMap (K := K) x) =
      differentialVariationalProjectiveStandardApartmentMap x := by
  induction x using Quotient.inductionOn with
  | _ m =>
      apply Quotient.sound
      rw [map_standardCompletedPseudoDiffOpLatticeAtCoweight]

end
end GaloisForLFunctions.HTGeometry.DiffOp
