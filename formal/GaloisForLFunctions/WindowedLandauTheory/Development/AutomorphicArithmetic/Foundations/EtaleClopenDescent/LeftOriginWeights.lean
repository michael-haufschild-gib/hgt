import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential

/-! The left coordinate weights cut out the affine origin in the
first chart. Their normalized weights are the affine coordinates. -/

noncomputable section

namespace GlobalTheory.WH.WeightedChartSystem

variable {k R E : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup E] [Module k E]
  {d : ℕ} (T : WeightedChartSystem k d R E)

abbrev leftOriginWeights (l : Fin d) : R := T.X l.succ

theorem normalizedWeight_leftOriginWeights (i j : Fin (d + 1)) (l : Fin d) :
    T.normalizedWeight (fun _ => (1, 0)) T.leftOriginWeights i j l =
      ((T.X l.succ * (T.X i)⁻¹ : Rˣ) : R) := by
  simp only [normalizedWeight, weightUnit, leftOriginWeights, pow_one, pow_zero, mul_one, Units.val_mul]

theorem leftOriginWeights_admitted (hT : T.Good) :
    T.Admitted (fun _ => (1, 0)) T.leftOriginWeights := by
  intro i j l
  rw [T.normalizedWeight_leftOriginWeights]
  exact hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) l.succ

/-- Away from the first chart, one normalized origin equation is a unit. -/
theorem exists_normalizedWeight_leftOriginWeights_eq_one {i : Fin (d + 1)} (hi : i ≠ 0) (j : Fin (d + 1)) :
    ∃ l : Fin d, T.normalizedWeight (fun _ => (1, 0)) T.leftOriginWeights i j l = 1 := by
  obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hi
  exact ⟨l, by rw [T.normalizedWeight_leftOriginWeights, mul_inv_cancel, Units.val_one]⟩

end GlobalTheory.WH.WeightedChartSystem
