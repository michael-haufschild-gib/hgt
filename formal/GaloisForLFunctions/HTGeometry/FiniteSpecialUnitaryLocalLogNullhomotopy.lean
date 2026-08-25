import GaloisForLFunctions.HTGeometry.FiniteUnitaryDeterminantExponential
import GaloisForLFunctions.HTGeometry.ContinuousIntegerLatticeRigidity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product

/-!
# Local logarithm nullhomotopy in finite special-unitary groups

For a based `SU(n)` loop contained in the principal radius-two logarithm chart, determinant one
forces the continuously varying principal-log trace to remain in `2πℤ`. Connectedness of the
parameter interval forces that trace to stay zero. Radially scaling the logarithm therefore gives
an explicit endpoint-fixed nullhomotopy entirely inside `SU(n)`.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

noncomputable local instance : CStarAlgebra (Matrix iota iota ℂ) :=
  CStarAlgebra.mk

def localSpecialUnitaryToUnitary
    (S : Matrix.specialUnitaryGroup iota ℂ) :
    Matrix.unitaryGroup iota ℂ :=
  ⟨S, Matrix.specialUnitaryGroup_le_unitaryGroup S.2⟩

theorem continuous_localSpecialUnitaryToUnitary :
    Continuous (localSpecialUnitaryToUnitary :
      Matrix.specialUnitaryGroup iota ℂ → Matrix.unitaryGroup iota ℂ) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val

theorem principalLogTrace_eq_zero_of_specialUnitaryPath
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((localSpecialUnitaryToUnitary (p t) : Matrix iota iota ℂ) - 1)‖ < 2) :
    ∀ t, Matrix.trace
      (Unitary.argSelfAdjoint (localSpecialUnitaryToUnitary (p t)) :
        Matrix iota iota ℂ) = 0 := by
  let u : unitInterval → Matrix.unitaryGroup iota ℂ :=
    fun t ↦ localSpecialUnitaryToUnitary (p t)
  have hu : Continuous u := continuous_localSpecialUnitaryToUnitary.comp p.continuous
  have harg : Continuous (fun t ↦ Unitary.argSelfAdjoint (u t)) := by
    apply Unitary.continuousOn_argSelfAdjoint.comp_continuous hu
    intro t
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, u] using hp t
  let f : unitInterval → ℝ := fun t ↦
    (Matrix.trace (Unitary.argSelfAdjoint (u t) : Matrix iota iota ℂ)).re
  have hf : Continuous f := by
    unfold f
    apply Complex.continuous_re.comp
    unfold Matrix.trace
    apply continuous_finsetSum
    intro i hi
    exact (continuous_apply i).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp harg))
  have hzero : f 0 = 0 := by
    simp [f, u, localSpecialUnitaryToUnitary]
  have hdisc : ∀ t, ∃ n : ℤ, f t = (n : ℝ) * (2 * Real.pi) := by
    intro t
    let H : selfAdjoint (Matrix iota iota ℂ) :=
      Unitary.argSelfAdjoint (u t)
    have hHerm : (H : Matrix iota iota ℂ).IsHermitian := H.2
    have him : (Matrix.trace (H : Matrix iota iota ℂ)).im = 0 := by
      rw [isHermitian_trace_eq_sum_eigenvalues hHerm]
      simp
    have hdet : ((u t : Matrix iota iota ℂ).det) = 1 := by
      exact (Matrix.mem_specialUnitaryGroup_iff.mp (p t).2).2
    have hexpOne : Complex.exp
        (Complex.I * Matrix.trace (H : Matrix iota iota ℂ)) = 1 := by
      rw [← det_expUnitary_eq_exp_I_mul_trace H]
      rw [show selfAdjoint.expUnitary H = u t from
        expUnitary_argSelfAdjoint (hp t)]
      exact hdet
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexpOne
    refine ⟨n, ?_⟩
    have hnim := congrArg Complex.im hn
    change (Matrix.trace (H : Matrix iota iota ℂ)).re =
      (n : ℝ) * (2 * Real.pi)
    simpa [him] using hnim
  have hreal : ∀ t, f t = 0 :=
    continuous_eq_zero_of_eq_int_mul 0 f hf hzero (2 * Real.pi)
      (mul_pos (by norm_num) Real.pi_pos) hdisc
  intro t
  let H : selfAdjoint (Matrix iota iota ℂ) :=
    Unitary.argSelfAdjoint (u t)
  have hHerm : (H : Matrix iota iota ℂ).IsHermitian := H.2
  have him : (Matrix.trace (H : Matrix iota iota ℂ)).im = 0 := by
    rw [isHermitian_trace_eq_sum_eigenvalues hHerm]
    simp
  change Matrix.trace (H : Matrix iota iota ℂ) = 0
  apply Complex.ext
  · simpa [f, H, u] using hreal t
  · exact him

/-- Principal-log contraction of a special-unitary loop contained in the radius-two chart,
with the determinant-one condition certified by trace quantization. -/
def finiteSpecialUnitaryLocalLogHomotopy
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((localSpecialUnitaryToUnitary (p t) : Matrix iota iota ℂ) - 1)‖ < 2) :
    p.Homotopy (Path.refl 1) := by
  have htrace := principalLogTrace_eq_zero_of_specialUnitaryPath p hp
  let u : unitInterval → Matrix.unitaryGroup iota ℂ :=
    fun t ↦ localSpecialUnitaryToUnitary (p t)
  have hu : Continuous u := continuous_localSpecialUnitaryToUnitary.comp p.continuous
  have harg : Continuous (fun t ↦ Unitary.argSelfAdjoint (u t)) := by
    apply Unitary.continuousOn_argSelfAdjoint.comp_continuous hu
    intro t
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, u] using hp t
  let Hmap : C(unitInterval × unitInterval,
      Matrix.specialUnitaryGroup iota ℂ) :=
    ⟨fun st ↦
      ⟨selfAdjoint.expUnitary
          ((1 - (st.1 : ℝ)) • Unitary.argSelfAdjoint (u st.2)), by
        rw [Matrix.mem_specialUnitaryGroup_iff]
        constructor
        · exact (selfAdjoint.expUnitary _).2
        · rw [det_expUnitary_eq_exp_I_mul_trace]
          have hz : Matrix.trace
              (((1 - (st.1 : ℝ)) • Unitary.argSelfAdjoint (u st.2) :
                selfAdjoint (Matrix iota iota ℂ)) : Matrix iota iota ℂ) = 0 := by
            have ht : Matrix.trace
                (Unitary.argSelfAdjoint (u st.2) : Matrix iota iota ℂ) = 0 := by
              simpa only [u] using htrace st.2
            rw [selfAdjoint.val_smul, Matrix.trace_smul]
            rw [ht, smul_zero]
          rw [hz]
          simp⟩, by
      apply continuous_induced_rng.2
      change Continuous (fun st : unitInterval × unitInterval ↦
        (selfAdjoint.expUnitary
          ((1 - (st.1 : ℝ)) • Unitary.argSelfAdjoint (u st.2)) :
            Matrix iota iota ℂ))
      apply continuous_subtype_val.comp
      apply selfAdjoint.continuous_expUnitary.comp
      exact (by fun_prop : Continuous (fun st : unitInterval × unitInterval ↦
        (1 - (st.1 : ℝ)))).smul (harg.comp continuous_snd)⟩
  refine
    { toContinuousMap := Hmap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    apply Subtype.ext
    dsimp [Hmap]
    change (selfAdjoint.expUnitary
      ((1 - (0 : ℝ)) • Unitary.argSelfAdjoint (u t)) :
        Matrix iota iota ℂ) = (u t : Matrix iota iota ℂ)
    exact congrArg Subtype.val (by
      simpa using expUnitary_argSelfAdjoint (hp t))
  · intro t
    apply Subtype.ext
    simp [Hmap]
  · intro t x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> apply Subtype.ext <;>
      simp [Hmap, u, localSpecialUnitaryToUnitary]

theorem finiteSpecialUnitaryLocalLog_nullhomotopic
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((localSpecialUnitaryToUnitary (p t) : Matrix iota iota ℂ) - 1)‖ < 2) :
    p.Homotopic (Path.refl 1) :=
  ⟨finiteSpecialUnitaryLocalLogHomotopy p hp⟩

end

end GaloisForLFunctions.HTGeometry
