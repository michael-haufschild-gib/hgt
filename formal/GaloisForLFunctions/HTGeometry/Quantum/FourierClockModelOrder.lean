import GaloisForLFunctions.HTGeometry.FiniteAdditiveFiberEnergy
import GaloisForLFunctions.RHTower.UnitaryEulerFactorRigidity

/-!
# Spectral model order witnessed by a Fourier clock

At consecutive clock ticks an equally spaced spectrum traverses orthogonal
unitary matrices. A competitor may choose its eigenbasis arbitrarily and
adjust its phases at every tick. A fixed partition into k spectral sectors
can capture at most k units of normalized squared trace overlap in total.
-/

open scoped BigOperators
open Matrix
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Diagonal of a spectral projection in the clock basis. -/
private def sectorWeight {D k : ℕ} [NeZero D]
    (V : Matrix.unitaryGroup (ZMod D) ℂ) (g : ZMod D → Fin k)
    (a : Fin k) (x : ZMod D) : ℝ :=
  ∑ y : {y // g y = a}, Complex.normSq ((V : Matrix (ZMod D) (ZMod D) ℂ) x y.val)

private theorem sum_sectorWeight {D k : ℕ} [NeZero D]
    (V : Matrix.unitaryGroup (ZMod D) ℂ) (g : ZMod D → Fin k) (x : ZMod D) :
    ∑ a, sectorWeight V g a x = 1 := by
  rw [← RHTower.sum_normSq_row_of_mem_unitary V.2 x]
  exact Fintype.sum_fiberwise g (fun y => Complex.normSq ((V : Matrix (ZMod D) (ZMod D) ℂ) x y))

/-- The clock and its competitor can have unrelated eigenbases. Sector phases
may change independently at each sample. -/
def clockSectorTrace {D k : ℕ} [NeZero D]
    (V : Matrix.unitaryGroup (ZMod D) ℂ) (g : ZMod D → Fin k)
    (angle : ZMod D → Fin k → ℝ) (s : ZMod D) : ℂ :=
  Matrix.trace (Matrix.diagonal (fun x => (ZMod.stdAddChar (s*x) : ℂ)) *
    ((V : Matrix (ZMod D) (ZMod D) ℂ) * Matrix.diagonal (fun y =>
      Complex.exp (((angle s (g y) : ℝ) : ℂ) * Complex.I)) * star (V : Matrix (ZMod D) (ZMod D) ℂ)))

private theorem clockSectorTrace_expansion {D k : ℕ} [NeZero D]
    (V : Matrix.unitaryGroup (ZMod D) ℂ) (g : ZMod D → Fin k)
    (angle : ZMod D → Fin k → ℝ) (s : ZMod D) :
    clockSectorTrace V g angle s =
      ∑ a, Complex.exp ((angle s a : ℂ) * Complex.I) *
        ∑ x, (sectorWeight V g a x : ℂ) * ZMod.stdAddChar (s*x) := by
  classical
  unfold clockSectorTrace
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hd (x : ZMod D) : ((V : Matrix (ZMod D) (ZMod D) ℂ) * Matrix.diagonal (fun y =>
      Complex.exp ((angle s (g y) : ℂ) * Complex.I)) * star (V : Matrix (ZMod D) (ZMod D) ℂ)) x x =
      ∑ y, ((V : Matrix (ZMod D) (ZMod D) ℂ) x y * Complex.exp ((angle s (g y) : ℂ) * Complex.I)) *
        (starRingEnd ℂ) ((V : Matrix (ZMod D) (ZMod D) ℂ) x y) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def]
  simp_rw [hd, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin k)) (t := Finset.univ (α := ZMod D))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fintype.sum_fiberwise g]
  apply Finset.sum_congr rfl
  intro a _
  simp only [sectorWeight, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [y.property, Complex.normSq_eq_conj_mul_self]
  ring

/-- Any set of clock samples has total normalized Choi fidelity at most the
number of simulator sectors. The trace is unnormalized on the left. -/
theorem fourierClock_sectorTrace_energy_le
    {D k : ℕ} [NeZero D] (V : Matrix.unitaryGroup (ZMod D) ℂ)
    (g : ZMod D → Fin k) (angle : ZMod D → Fin k → ℝ) (samples : Finset (ZMod D)) :
    ∑ s ∈ samples, ‖clockSectorTrace V g angle s‖ ^ 2 ≤ (k : ℝ) * (D : ℝ)^2 := by
  classical
  let F (a : Fin k) (s : ZMod D) :=
    ∑ x, (sectorWeight V g a x : ℂ) * ZMod.stdAddChar (s*x)
  have hFourier (a : Fin k) : ∑ s, ‖F a s‖ ^ 2 =
      (D : ℝ) * ∑ x, (sectorWeight V g a x)^2 := by
    have h := RHTower.Sieve.sum_normSq_weighted_stdAddChar_mul_of_injective
      D id Function.injective_id (fun x => (sectorWeight V g a x : ℂ))
    simpa only [F, id_eq, Complex.normSq_eq_norm_sq, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] using h
  have hn (a : Fin k) (x : ZMod D) : 0 ≤ sectorWeight V g a x := by
    unfold sectorWeight
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hrow (x : ZMod D) : ∑ a, (sectorWeight V g a x)^2 ≤ 1 := by
    rw [← sum_sectorWeight V g x]
    apply Finset.sum_le_sum
    intro a _
    have hu : sectorWeight V g a x ≤ 1 := by
      rw [← sum_sectorWeight V g x]
      exact Finset.single_le_sum (fun i _ => hn i x) (Finset.mem_univ a)
    simpa only [sq, mul_one] using mul_le_mul_of_nonneg_left hu (hn a x)
  have ht (s : ZMod D) : ‖clockSectorTrace V g angle s‖^2 ≤
      (k : ℝ) * ∑ a, ‖F a s‖^2 := by
    rw [clockSectorTrace_expansion]
    have h := norm_sum_smul_sq_le_mass Finset.univ
      (fun a => Complex.exp ((angle s a : ℂ) * Complex.I)) (fun a => F a s)
    simpa only [smul_eq_mul, Complex.norm_exp_ofReal_mul_I, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_mul, F] using h
  calc
    _ ≤ ∑ s : ZMod D, ‖clockSectorTrace V g angle s‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ s : ZMod D, (k : ℝ) * ∑ a, ‖F a s‖^2 := Finset.sum_le_sum fun s _ => ht s
    _ = (k : ℝ) * ((D : ℝ) * ∑ x, ∑ a, (sectorWeight V g a x)^2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [hFourier]
      rw [← Finset.mul_sum, Finset.sum_comm (s := Finset.univ (α := Fin k))]
    _ ≤ (k : ℝ) * ((D : ℝ) * ∑ _x : ZMod D, (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ => hrow x) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by simp [sq]

#print axioms fourierClock_sectorTrace_energy_le

end
end GaloisForLFunctions.HTGeometry
