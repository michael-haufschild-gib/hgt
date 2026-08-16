import GaloisForLFunctions.HTGeometry.LocalSpectralExtensionRelationRigidity

/-!
# Residues of an affine multiple of a simple-pole packet

A quadratic-rate spectral identity, differentiated twice along a perturbation, produces an
identity of the shape

`L(w) * ∑ᵢ cᵢ / (zᵢ - w) = constant`,

with `L` affine.  The right side has no pole, so every residue of the left side vanishes: at each
node `zᵢ` one gets `cᵢ · L(zᵢ) = 0`.  A nonzero affine function has at most one root, so at most
one coefficient of the packet can survive.

Clearing denominators keeps everything polynomial, so no meromorphic continuation is used.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cleared numerator of `L(w)·∑ cᵢ/(zᵢ - w) - cst` for the affine multiplier `L(w) = p + q w`. -/
def affinePolePacketNumerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (p q cst : ℂ) : ℂ[X] :=
  (Polynomial.C p + Polynomial.C q * Polynomial.X) * distinctNodePacketNumerator z c
    - Polynomial.C cst * ∏ i, (Polynomial.C (z i) - Polynomial.X)

/-- An affine-multiplier simple-pole identity on any infinite pole-free set clears to the zero
numerator. -/
theorem affinePolePacketNumerator_eq_zero_of_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (z c : ι → ℂ) (p q cst : ℂ)
    (S : Set ℂ) (hS : S.Infinite) (havoid : ∀ w ∈ S, ∀ i, w ≠ z i)
    (hidentity : ∀ w ∈ S, (p + q * w) * ∑ i, c i / (z i - w) = cst) :
    affinePolePacketNumerator z c p q cst = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply hS.mono
  intro w hw
  have hne : ∀ i : ι, z i - w ≠ 0 := fun i => sub_ne_zero.mpr (havoid w hw i).symm
  have hpacket : (distinctNodePacketNumerator z c).eval w
      = (∑ i, c i / (z i - w)) * ∏ j, (z j - w) := by
    rw [distinctNodePacketNumerator]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j => z j - w) (Finset.mem_univ i)]
    field_simp [hne i]
  have heval : (affinePolePacketNumerator z c p q cst).eval w = 0 := by
    rw [affinePolePacketNumerator]
    simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_prod]
    rw [hpacket]
    have hprod : ∏ i, ((z i) - w) = ∏ i, ((z i) - w) := rfl
    calc (p + q * w) * ((∑ i, c i / (z i - w)) * ∏ j, (z j - w))
          - cst * ∏ i, ((z i) - w)
        = ((p + q * w) * ∑ i, c i / (z i - w) - cst) * ∏ i, ((z i) - w) := by ring
      _ = 0 := by rw [hidentity w hw, sub_self, zero_mul]
  exact heval

/-- **The residue law.**  At every node of the packet the coefficient is killed by the affine
multiplier. -/
theorem affinePoleResidue_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z c : ι → ℂ} {p q cst : ℂ}
    (hz : Function.Injective z) (hnum : affinePolePacketNumerator z c p q cst = 0) (i : ι) :
    c i * (p + q * z i) = 0 := by
  have heval := congrArg (fun P : ℂ[X] => P.eval (z i)) hnum
  simp only [affinePolePacketNumerator, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_prod,
    eval_zero] at heval
  rw [distinctNodePacketNumerator_eval_node z c i] at heval
  have hzero : ∏ j, ((z j) - z i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  rw [hzero, mul_zero, sub_zero] at heval
  have hprod : ∏ j ∈ Finset.univ.erase i, (z j - z i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hz h)
  have hfac : (p + q * z i) * (c i * ∏ j ∈ Finset.univ.erase i, (z j - z i)) = 0 := heval
  rcases mul_eq_zero.mp hfac with h | h
  · rw [mul_comm]
    exact mul_eq_zero_of_left h _
  · rcases mul_eq_zero.mp h with h' | h'
    · exact mul_eq_zero_of_left h' _
    · exact absurd h' hprod

/-- A coefficient not annihilated by the affine multiplier must vanish. -/
theorem affinePoleCoefficient_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z c : ι → ℂ} {p q cst : ℂ}
    (hz : Function.Injective z) (hnum : affinePolePacketNumerator z c p q cst = 0) {i : ι}
    (hL : p + q * z i ≠ 0) : c i = 0 :=
  (mul_eq_zero.mp (affinePoleResidue_eq_zero hz hnum i)).resolve_right hL

/-- **At most one surviving residue.**  A nonzero affine multiplier has at most one root, so at
most one node of the packet can carry a nonzero coefficient. -/
theorem affinePole_support_subsingleton
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z c : ι → ℂ} {p q cst : ℂ}
    (hz : Function.Injective z) (hL : p ≠ 0 ∨ q ≠ 0)
    (hnum : affinePolePacketNumerator z c p q cst = 0) :
    ∀ i j : ι, c i ≠ 0 → c j ≠ 0 → i = j := by
  intro i j hi hj
  have hzi : p + q * z i = 0 := (mul_eq_zero.mp (affinePoleResidue_eq_zero hz hnum i)).resolve_left hi
  have hzj : p + q * z j = 0 := (mul_eq_zero.mp (affinePoleResidue_eq_zero hz hnum j)).resolve_left hj
  have hq : q ≠ 0 := by
    rcases hL with hp | hq
    · intro hq0
      rw [hq0, zero_mul, add_zero] at hzi
      exact hp hzi
    · exact hq
  have : q * z i = q * z j := by
    have h1 : q * z i = -p := by linear_combination hzi
    have h2 : q * z j = -p := by linear_combination hzj
    rw [h1, h2]
  exact hz (mul_left_cancel₀ hq this)

/-- **The residue law in the form used by the extension induction.**  If the affine multiplier is
nonzero, all but at most one coefficient of the packet vanish. -/
theorem affinePole_eq_zero_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z c : ι → ℂ} {p q cst : ℂ}
    (hz : Function.Injective z) (hL : p ≠ 0 ∨ q ≠ 0)
    (hnum : affinePolePacketNumerator z c p q cst = 0) {i j : ι} (hij : i ≠ j) (hi : c i ≠ 0) :
    c j = 0 := by
  by_contra hj
  exact hij (affinePole_support_subsingleton hz hL hnum i j hi hj)

/-- A vanishing affine multiplier forces the constant to vanish. -/
theorem affinePole_const_eq_zero_of_multiplier_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z c : ι → ℂ} {cst : ℂ}
    (S : Set ℂ) (hS : S.Nonempty)
    (hidentity : ∀ w ∈ S, ((0 : ℂ) + 0 * w) * ∑ i, c i / (z i - w) = cst) : cst = 0 := by
  obtain ⟨w, hw⟩ := hS
  have h := hidentity w hw
  simpa using h.symm

end

end GaloisForLFunctions.HTGeometry
