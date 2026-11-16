import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Topological nilpotence of integral p-adic matrices

Powers of an integral p-adic matrix converge to zero exactly when its
residue matrix is nilpotent. An exponent `m` killing the residue gives
an exponent `m*k` killing reduction modulo `p^k`, hence a quantitative
entrywise norm bound. This is weaker than algebraic nilpotence: the
nonzero scalar matrix `p` supplies a counterexample in every positive
dimension.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open Filter
open scoped Topology

variable (p : ℕ) [Fact p.Prime]

/-- A vanishing finite residue is exactly a closed p-adic norm bound. -/
theorem padicProjection_eq_zero_iff_norm_le (x : ℤ_[p]) (k : ℕ) :
    PadicInt.toZModPow k x = 0 ↔ ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]

/-- Convergence to zero is detected by eventual vanishing at every finite residue level. -/
theorem padic_tendsto_zero_iff {α : Type*} {l : Filter α} (f : α → ℤ_[p]) :
    Tendsto f l (𝓝 0) ↔ ∀ k : ℕ, ∀ᶠ x in l, PadicInt.toZModPow k (f x) = 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor
  · intro h k
    have he := Metric.tendsto_nhds.mp h ((p : ℝ) ^ (-(k : ℤ))) (zpow_pos hp _)
    filter_upwards [he] with x hx
    exact (padicProjection_eq_zero_iff_norm_le p (f x) k).mpr
      (by simpa only [dist_zero_right] using hx.le)
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    filter_upwards [h k] with x hx
    rw [dist_zero_right]
    exact lt_of_le_of_lt ((padicProjection_eq_zero_iff_norm_le p (f x) k).mp hx) hk

/-- Entrywise reduction of an integral p-adic matrix modulo `p^k`. -/
def padicMatrixProjection (k : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℤ_[p] →+* Matrix ι ι (ZMod (p ^ k)) :=
  (PadicInt.toZModPow k).mapMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix powers converge to zero exactly when every finite reduction is nilpotent. -/
theorem padicMatrix_topNil_iff_all_reductions (A : Matrix ι ι ℤ_[p]) :
    IsTopologicallyNilpotent A ↔ ∀ k : ℕ, IsNilpotent (padicMatrixProjection p k ι A) := by
  constructor
  · intro h k
    change Tendsto (fun m : ℕ => A ^ m) atTop (𝓝 0) at h
    have he (i j : ι) : ∀ᶠ m : ℕ in atTop, PadicInt.toZModPow k ((A ^ m) i j) = 0 :=
      (padic_tendsto_zero_iff p (fun m : ℕ => (A ^ m) i j)).mp
        ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i)) j) k
    have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : ι, PadicInt.toZModPow k ((A ^ m) i j) = 0 :=
      eventually_all.mpr fun i => eventually_all.mpr fun j => he i j
    obtain ⟨m, hm⟩ := hall.exists
    refine ⟨m, ?_⟩
    rw [← map_pow]
    ext i j
    exact hm i j
  · intro h
    change Tendsto (fun m : ℕ => A ^ m) atTop (𝓝 0)
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply (padic_tendsto_zero_iff p (fun m : ℕ => (A ^ m) i j)).mpr
    intro k
    obtain ⟨m, hm⟩ := h k
    filter_upwards [eventually_ge_atTop m] with t ht
    have hz : padicMatrixProjection p k ι (A ^ t) = 0 := by
      rw [map_pow, ← Nat.add_sub_of_le ht, pow_add, hm, zero_mul]
    exact congrFun (congrFun hz i) j

/-- A matrix with zero residue has an integral scalar factor `p`. -/
theorem padicMatrix_zero_residue_factor (A : Matrix ι ι ℤ_[p])
    (hA : padicMatrixProjection p 1 ι A = 0) :
    ∃ B : Matrix ι ι ℤ_[p], A = (p : ℤ_[p]) • B := by
  have he (i j : ι) : ∃ b : ℤ_[p], A i j = (p : ℤ_[p]) * b := by
    have h := congrFun (congrFun hA i) j
    change PadicInt.toZModPow 1 (A i j) = 0 at h
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at h
    exact h
  choose B hB using he
  refine ⟨B, ?_⟩
  ext i j
  exact hB i j

/-- A residue nilpotence exponent `m` kills level `k` after `m*k` powers. -/
theorem padicMatrix_projection_pow_eq_zero (A : Matrix ι ι ℤ_[p]) (m : ℕ)
    (hm : (padicMatrixProjection p 1 ι A) ^ m = 0) (k : ℕ) :
    padicMatrixProjection p k ι (A ^ (m * k)) = 0 := by
  have hz : padicMatrixProjection p 1 ι (A ^ m) = 0 := by rw [map_pow, hm]
  obtain ⟨B, hB⟩ := padicMatrix_zero_residue_factor p (A ^ m) hz
  rw [pow_mul, hB, smul_pow]
  ext i j
  change PadicInt.toZModPow k ((p : ℤ_[p]) ^ k * (B ^ k) i j) = 0
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  exact ⟨(B ^ k) i j, rfl⟩

/-- Every residue nilpotence exponent gives a quantitative p-adic decay bound. -/
theorem padicMatrix_pow_norm_le (A : Matrix ι ι ℤ_[p]) (m : ℕ)
    (hm : (padicMatrixProjection p 1 ι A) ^ m = 0) (k : ℕ) (i j : ι) :
    ‖(A ^ (m * k)) i j‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
  (padicProjection_eq_zero_iff_norm_le p _ k).mp
    (congrFun (congrFun (padicMatrix_projection_pow_eq_zero p A m hm k) i) j)

/-- Topological nilpotence is completely determined by the matrix modulo `p`. -/
theorem padicMatrix_topNil_iff_residue_nil (A : Matrix ι ι ℤ_[p]) :
    IsTopologicallyNilpotent A ↔ IsNilpotent (padicMatrixProjection p 1 ι A) := by
  rw [padicMatrix_topNil_iff_all_reductions]
  constructor
  · exact fun h => h 1
  · rintro ⟨m, hm⟩ k
    refine ⟨m * k, ?_⟩
    rw [← map_pow]
    exact padicMatrix_projection_pow_eq_zero p A m hm k

/-- The scalar matrix `p` separates topological from algebraic nilpotence in every positive dimension. -/
theorem padicScalar_topNil_not_nilpotent (n : ℕ) :
    IsTopologicallyNilpotent (p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) ∧
      ¬ IsNilpotent (p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) := by
  constructor
  · apply (padicMatrix_topNil_iff_residue_nil p _).mpr
    refine ⟨1, ?_⟩
    rw [pow_one (padicMatrixProjection p 1 (Fin (n + 1))
      (p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p])), map_natCast]
    ext i j
    rw [Matrix.natCast_apply]
    split_ifs
    · simpa only [pow_one] using (CharP.cast_eq_zero (ZMod (p ^ 1)) (p ^ 1))
    · exact Nat.cast_zero
  · rintro ⟨m, hm⟩
    rw [← Nat.cast_pow] at hm
    have he := congrFun (congrFun hm (0 : Fin (n + 1))) (0 : Fin (n + 1))
    have hz : ((p ^ m : ℕ) : ℤ_[p]) = 0 := by simpa [Matrix.natCast_apply] using he
    exact (Nat.cast_ne_zero.mpr (pow_ne_zero m (Fact.out : p.Prime).ne_zero)) hz

#print axioms padicMatrix_topNil_iff_all_reductions
#print axioms padicMatrix_pow_norm_le
#print axioms padicMatrix_topNil_iff_residue_nil
#print axioms padicScalar_topNil_not_nilpotent

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
