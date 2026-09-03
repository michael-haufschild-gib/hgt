import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCoweightLatticeLength

/-!
# Exact lengths of intervals between completed coweight lattices

Integral coordinates are constructed at every integer coweight, not only at the standard origin.
Increasing a coweight by a natural vector corresponds exactly to imposing the associated product
of uniformizer-power ideals.  Hence every such lattice interval has length equal to the sum of its
coordinate increments.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- Integral coordinates on the completed diagonal lattice at an arbitrary integer coweight. -/
def standardCompletedPseudoDiffOpLatticeAtCoweightIntegerEquiv (m : ι → ℤ) :
    (ι → CompletedPseudoDiffOpInteger (K := K)) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier where
  toFun x := ⟨fun i => (x i : CompletedPseudoDiffOp K) *
      (completedPseudoDiffOpUniformizerCoweight (K := K) m i :
        (CompletedPseudoDiffOp K)ˣ), by
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
    intro i
    simp⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    exact add_mul (x i : CompletedPseudoDiffOp K) (y i) _
  map_smul' c x := by
    apply Subtype.ext
    funext i
    exact mul_assoc (c : CompletedPseudoDiffOp K) (x i) _
  invFun y i := ⟨y.1 i *
      ((completedPseudoDiffOpUniformizerCoweight (K := K) m i)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ),
    (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff m y.1).1 y.2 i⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    funext i
    simp

/-- The lattice at `m` viewed inside the lattice at `n`. -/
def standardCompletedPseudoDiffOpCoweightIntervalInside (m n : ι → ℤ) :
    Submodule (CompletedPseudoDiffOpInteger (K := K))
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n).carrier :=
  Submodule.comap
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n).carrier.subtype
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier

/-- A natural uniformizer increment cancels the inverse power at the incremented weight. -/
theorem completedPseudoDiffOpUniformizer_interval_cancel (n : ℤ) (d : ℕ) :
    ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      (((completedPseudoDiffOpUniformizerUnit (K := K) ^ n :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      (((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n + (d : ℤ)))⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)) = 1 := by
  have hu : completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) *
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n *
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n + (d : ℤ)))⁻¹) = 1 := by
    rw [← mul_assoc, ← zpow_add]
    simp [add_comm]
  exact congrArg Units.val hu

/-- Removing a natural increment from an inverse uniformizer power recovers the base inverse. -/
theorem completedPseudoDiffOpUniformizer_interval_shift (n : ℤ) (d : ℕ) :
    (((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n + (d : ℤ)))⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) =
      (((completedPseudoDiffOpUniformizerUnit (K := K) ^ n)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) := by
  have hu : (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n + (d : ℤ)))⁻¹ *
      completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) =
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n)⁻¹ := by
    rw [← zpow_neg, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  exact congrArg Units.val hu

/-- A coerced integer uniformizer power cancels its inverse in the completed skew field. -/
theorem completedPseudoDiffOpUniformizer_zpow_inv_mul (n : ℤ) :
    (((completedPseudoDiffOpUniformizerUnit (K := K) ^ n)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ n :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) = 1 := by
  have hu : (completedPseudoDiffOpUniformizerUnit (K := K) ^ n)⁻¹ *
      completedPseudoDiffOpUniformizerUnit (K := K) ^ n = 1 := by simp
  exact congrArg Units.val hu

/-- Coordinates identify product power ideals with actual completed coweight-lattice intervals. -/
theorem map_uniformizerPowerPi_eq_coweightInterval
    (n : ι → ℤ) (d : ι → ℕ) :
    Submodule.map (standardCompletedPseudoDiffOpLatticeAtCoweightIntegerEquiv (K := K) n).toLinearMap
        (completedPseudoDiffOpUniformizerPowerPi (K := K) d) =
      standardCompletedPseudoDiffOpCoweightIntervalInside (K := K) (fun i => n i + d i) n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (fun i => (x i : CompletedPseudoDiffOp K) *
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i :
        (CompletedPseudoDiffOp K)ˣ)) ∈
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => n i + d i)).carrier
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
    intro i
    have hxi := hx i (Set.mem_univ i)
    change x i ∈ (CompletedPseudoDiffOpInteger (K := K)) ∙
      (completedPseudoDiffOpUniformizerInteger (K := K) ^ d i) at hxi
    rw [Submodule.mem_span_singleton] at hxi
    obtain ⟨c, hc⟩ := hxi
    rw [← hc]
    change (((c : CompletedPseudoDiffOpInteger (K := K)) * completedPseudoDiffOpUniformizerInteger (K := K) ^ d i : CompletedPseudoDiffOpInteger (K := K)) :
        CompletedPseudoDiffOp K) *
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i :
            (CompletedPseudoDiffOp K)ˣ) *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i + (d i : ℤ)))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K)
    change ((c : CompletedPseudoDiffOp K) *
        (((completedPseudoDiffOpUniformizerInteger (K := K) ^ d i : CompletedPseudoDiffOpInteger (K := K)) :
          CompletedPseudoDiffOp K))) *
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i :
            (CompletedPseudoDiffOp K)ˣ) *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i + (d i : ℤ)))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K)
    rw [completedPseudoDiffOpUniformizerInteger_pow_coe]
    simpa only [mul_assoc, completedPseudoDiffOpUniformizer_interval_cancel, mul_one] using c.property
  · intro hy
    change (y.1 : ι → CompletedPseudoDiffOp K) ∈
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => n i + d i)).carrier at hy
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hy
    let x : ι → CompletedPseudoDiffOpInteger (K := K) := fun i => ⟨y.1 i *
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ),
      (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n y.1).1 y.2 i⟩
    refine ⟨x, ?_, ?_⟩
    · intro i _
      change x i ∈ (CompletedPseudoDiffOpInteger (K := K)) ∙
        (completedPseudoDiffOpUniformizerInteger (K := K) ^ d i)
      rw [Submodule.mem_span_singleton]
      let c : CompletedPseudoDiffOpInteger (K := K) := ⟨y.1 i *
        ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i + (d i : ℤ)))⁻¹ :
          (CompletedPseudoDiffOp K)ˣ), hy i⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change (c : CompletedPseudoDiffOp K) *
          (((completedPseudoDiffOpUniformizerInteger (K := K) ^ d i : CompletedPseudoDiffOpInteger (K := K)) :
            CompletedPseudoDiffOp K)) = x i
      rw [completedPseudoDiffOpUniformizerInteger_pow_coe]
      change (y.1 i *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i + (d i : ℤ)))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ)) *
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (d i : ℤ) :
            (CompletedPseudoDiffOp K)ˣ) =
        y.1 i * ((completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹ :
          (CompletedPseudoDiffOp K)ˣ)
      rw [mul_assoc, completedPseudoDiffOpUniformizer_interval_shift]
    · apply Subtype.ext
      funext i
      change (y.1 i *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹ :
            (CompletedPseudoDiffOp K)ˣ)) *
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i :
            (CompletedPseudoDiffOp K)ˣ) = y.1 i
      rw [mul_assoc, completedPseudoDiffOpUniformizer_zpow_inv_mul, mul_one]

/-- A coweight interval quotient is the coordinatewise uniformizer-power quotient. -/
def standardCompletedPseudoDiffOpCoweightIntervalQuotientEquiv (n : ι → ℤ) (d : ι → ℕ) :
    ((ι → CompletedPseudoDiffOpInteger (K := K)) ⧸ completedPseudoDiffOpUniformizerPowerPi (K := K) d) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      ((standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n).carrier ⧸
        standardCompletedPseudoDiffOpCoweightIntervalInside (K := K) (fun i => n i + d i) n) :=
  Submodule.Quotient.equiv _ _ (standardCompletedPseudoDiffOpLatticeAtCoweightIntegerEquiv (K := K) n)
    (map_uniformizerPowerPi_eq_coweightInterval (K := K) n d)

/-- Coweight interval length is exactly the sum of the nonnegative coordinate increments. -/
theorem standardCompletedPseudoDiffOpCoweightIntervalQuotient_length (n : ι → ℤ) (d : ι → ℕ) :
    Module.length (CompletedPseudoDiffOpInteger (K := K))
      ((standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n).carrier ⧸
        standardCompletedPseudoDiffOpCoweightIntervalInside (K := K) (fun i => n i + d i) n) =
      ∑ i, d i := by
  rw [← (standardCompletedPseudoDiffOpCoweightIntervalQuotientEquiv (K := K) n d).length_eq]
  exact completedPseudoDiffOpUniformizerPowerPiQuotient_length (K := K) d

end

end GaloisForLFunctions.HTGeometry.DiffOp
