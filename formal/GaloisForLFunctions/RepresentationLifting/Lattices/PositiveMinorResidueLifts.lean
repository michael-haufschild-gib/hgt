import GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Strictly totally positive lifts of arbitrary residue matrices

Choi–Jang choose integral representatives with nonzero facet determinants.
Sampling the exponential kernel on integer grids produces an integral
direction along which all ordered minors eventually become positive at
once. Multiplying this direction by the modulus preserves every entry's
prescribed residue.
-/

namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry Matrix Filter Topology
noncomputable section

variable {n m : ℕ}

/-- An integral exponential kernel, including its constant first row and column. -/
def dyadicKernel (n m : ℕ) : Matrix (Fin n) (Fin m) ℤ :=
  of fun i j => 2 ^ (i.val * j.val)

private theorem dyadic_exp (i j : ℕ) :
    (((2 : ℤ) ^ (i*j) : ℤ) : ℝ) = Real.exp ((i * Real.log 2) * j) := by
  push_cast
  rw [show (i:ℝ) * Real.log 2 * j = ((i*j:ℕ):ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]

/-- Every ordered minor of the integral dyadic matrix is strictly positive. -/
theorem dyadicKernel_minor_pos {k : ℕ} (r : Fin k ↪o Fin n) (c : Fin k ↪o Fin m) :
    0 < ((dyadicKernel n m).submatrix r c).det := by
  have hr : StrictMono (fun i => ((r i).val : ℝ) * Real.log 2) :=
    fun _ _ h => mul_lt_mul_of_pos_right (Nat.cast_lt.mpr (r.strictMono h))
      (Real.log_pos (by norm_num))
  have hc : StrictMono (fun j => ((c j).val : ℝ)) :=
    fun _ _ h => Nat.cast_lt.mpr (c.strictMono h)
  have he : (Int.castRingHom ℝ).mapMatrix ((dyadicKernel n m).submatrix r c) =
      expNodeMatrix (fun i => ((r i).val : ℝ) * Real.log 2) (fun j => ((c j).val : ℝ)) :=
    Matrix.ext fun i j => dyadic_exp _ _
  have h := det_expKernel_pos hr hc
  rw [← he, ← RingHom.map_det] at h
  exact Int.cast_pos.mp h

/-- Integral perturbations preserving the modulus `d+1`. -/
def residueRay (A : Matrix (Fin n) (Fin m) ℤ) (d t : ℕ) : Matrix (Fin n) (Fin m) ℤ :=
  of fun i j => A i j + (d+1:ℕ) * (t:ℤ) * dyadicKernel n m i j

/-- The direction is fixed independently of the residue representatives. -/
theorem residueRay_entry (A : Matrix (Fin n) (Fin m) ℤ) (d t : ℕ) (i : Fin n) (j : Fin m) :
    ((d+1:ℕ) : ℤ) ∣ residueRay A d t i j - A i j :=
  ⟨(t:ℤ) * dyadicKernel n m i j, by dsimp [residueRay]; ring⟩

private theorem eventually_minor_pos (A : Matrix (Fin n) (Fin m) ℤ) (d : ℕ)
    {k : ℕ} (r : Fin k ↪o Fin n) (c : Fin k ↪o Fin m) :
    ∀ᶠ t : ℕ in atTop, 0 < ((residueRay A d t).submatrix r c).det := by
  let B := (Int.castRingHom ℝ).mapMatrix (A.submatrix r c)
  let D := (Int.castRingHom ℝ).mapMatrix ((dyadicKernel n m).submatrix r c)
  let f := fun z : ℝ => (((d+1:ℕ):ℝ) • D + z • B).det
  have hD : 0 < D.det := by
    change 0 < ((Int.castRingHom ℝ).mapMatrix ((dyadicKernel n m).submatrix r c)).det
    rw [← RingHom.map_det]
    exact Int.cast_pos.mpr (dyadicKernel_minor_pos r c)
  have hzero : 0 < f 0 := by
    simpa [f, det_smul] using mul_pos (pow_pos (by positivity : 0 < ((d+1:ℕ):ℝ)) k) hD
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have ht : Tendsto (fun t : ℕ => (t:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [((hcont.tendsto 0).comp ht).eventually (lt_mem_nhds hzero),
    eventually_gt_atTop 0] with t h htpos
  have htp : 0 < (t:ℝ) := by exact_mod_cast htpos
  have he : (Int.castRingHom ℝ).mapMatrix ((residueRay A d t).submatrix r c) =
      (t:ℝ) • (((d+1:ℕ):ℝ) • D + (t:ℝ)⁻¹ • B) := by
    ext i j
    change ((A (r i) (c j) + ((d+1:ℕ):ℤ) * (t:ℤ) * dyadicKernel n m (r i) (c j) : ℤ) : ℝ) =
      (t:ℝ) * (((d+1:ℕ):ℝ) * (dyadicKernel n m (r i) (c j) : ℝ) +
        (t:ℝ)⁻¹ * (A (r i) (c j) : ℝ))
    push_cast
    field_simp [htp.ne']
    ring
  have hd := congrArg Matrix.det he
  rw [← RingHom.map_det, det_smul] at hd
  have hp : 0 < (Int.castRingHom ℝ) ((residueRay A d t).submatrix r c).det := by
    rw [hd]
    exact mul_pos (pow_pos htp _) h
  exact Int.cast_pos.mp hp

/-- Beyond one common threshold, every ordered square minor of every size
is positive while all entry residues stay fixed. -/
theorem residueRay_eventually_totallyPositive (A : Matrix (Fin n) (Fin m) ℤ) (d : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ (k : ℕ) (r : Fin k ↪o Fin n) (c : Fin k ↪o Fin m),
      0 < ((residueRay A d t).submatrix r c).det := by
  classical
  have hall : ∀ᶠ t : ℕ in atTop, ∀ (k : Fin (n+1)) (r : Fin k.val ↪o Fin n)
      (c : Fin k.val ↪o Fin m), 0 < ((residueRay A d t).submatrix r c).det :=
    eventually_all.mpr fun _ => eventually_all.mpr fun r =>
      eventually_all.mpr fun c => eventually_minor_pos A d r c
  filter_upwards [hall] with t h k r c
  have hk : k ≤ n := by simpa using Fintype.card_le_of_injective _ r.injective
  exact h ⟨k, by omega⟩ r c

/-- Every residue class of rectangular integer matrices has a representative
in the strictly totally positive locus. -/
theorem exists_totallyPositive_lift (A : Matrix (Fin n) (Fin m) ℤ) (d : ℕ) :
    ∃ B : Matrix (Fin n) (Fin m) ℤ,
      (∀ i j, ((d+1:ℕ):ℤ) ∣ B i j - A i j) ∧
      ∀ (k : ℕ) (r : Fin k ↪o Fin n) (c : Fin k ↪o Fin m), 0 < (B.submatrix r c).det := by
  obtain ⟨t,ht⟩ := (residueRay_eventually_totallyPositive A d).exists
  exact ⟨_, residueRay_entry A d t, ht⟩

private theorem cast_eq_of_dvd_sub (q : ℕ) (z w : ℤ) (h : (q:ℤ) ∣ z-w) :
    (z : ZMod q) = (w : ZMod q) := by
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (z-w) q).mpr h
  rw [Int.cast_sub] at he
  exact sub_eq_zero.mp he

/-- Two independently specified residue matrices at coprime positive moduli
have a common integral lift with all ordered minors positive. This applies
directly to the binary and ternary matrices of the chart obstruction. -/
theorem exists_simultaneous_totallyPositive_lift (p q : ℕ+) (hpq : (p:ℕ).Coprime (q:ℕ))
    (U : Matrix (Fin n) (Fin m) (ZMod (p:ℕ))) (V : Matrix (Fin n) (Fin m) (ZMod (q:ℕ))) :
    ∃ B : Matrix (Fin n) (Fin m) ℤ,
      (B.map (Int.castRingHom (ZMod (p:ℕ))) = U ∧
       B.map (Int.castRingHom (ZMod (q:ℕ))) = V) ∧
      ∀ (k : ℕ) (r : Fin k ↪o Fin n) (c : Fin k ↪o Fin m), 0 < (B.submatrix r c).det := by
  let a (i : Fin n) (j : Fin m) := Nat.chineseRemainder hpq (U i j).val (V i j).val
  let A : Matrix (Fin n) (Fin m) ℤ := of fun i j => ((a i j).val:ℤ)
  let d := (p:ℕ)*(q:ℕ)-1
  have hd : d+1 = (p:ℕ)*(q:ℕ) := Nat.sub_add_cancel (Nat.mul_pos p.property q.property)
  obtain ⟨B,hB,hpos⟩ := exists_totallyPositive_lift A d
  have hres (i j) : ((p:ℤ)*(q:ℤ)) ∣ B i j-A i j := by
    simpa only [hd,Nat.cast_mul] using hB i j
  refine ⟨B,⟨?_,?_⟩,hpos⟩
  · ext i j
    change (B i j : ZMod (p:ℕ)) = U i j
    rw [cast_eq_of_dvd_sub _ _ (A i j) ((dvd_mul_right (p:ℤ) (q:ℤ)).trans (hres i j))]
    change (((((a i j).val:ℕ):ℤ):ZMod (p:ℕ))) = U i j
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (a i j).property.1
  · ext i j
    change (B i j : ZMod (q:ℕ)) = V i j
    rw [cast_eq_of_dvd_sub _ _ (A i j) ((dvd_mul_left (q:ℤ) (p:ℤ)).trans (hres i j))]
    change (((((a i j).val:ℕ):ℤ):ZMod (q:ℕ))) = V i j
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (a i j).property.2

#print axioms dyadicKernel_minor_pos
#print axioms residueRay_eventually_totallyPositive
#print axioms exists_totallyPositive_lift
#print axioms exists_simultaneous_totallyPositive_lift

end
end GaloisForLFunctions.RepresentationLifting
