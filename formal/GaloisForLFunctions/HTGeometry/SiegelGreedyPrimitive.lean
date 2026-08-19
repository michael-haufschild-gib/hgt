import GaloisForLFunctions.HTGeometry.SiegelProjectedNorm

/-!
# A minimiser of the projected norm has primitive tail

The projected norm at level `i` depends only on the coordinates from `i` on, and scales
quadratically.  So if every tail coordinate of a lattice vector were divisible by `k ≥ 2`, dividing
by `k` would leave the projection nonzero while dividing the projected norm by `k²` — impossible for
a minimiser.

This is the step that makes the greedy construction produce a *basis*: the vector realising the
minimum at level `i` is primitive modulo the earlier ones, hence extends the partial basis.

* `JacobiData.projNorm_smul` : the projected norm is quadratically homogeneous.
* `JacobiData.projNorm_congr_tail` : it depends only on the tail coordinates.
* `JacobiData.not_dvd_of_projNorm_min` : **a minimiser has primitive tail.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The projected norm is quadratically homogeneous.** -/
theorem JacobiData.projNorm_smul (J : JacobiData n) (i : Fin n) (c : ℝ) (v : Fin n → ℝ) :
    J.projNorm i (c • v) = c ^ 2 * J.projNorm i v := by
  classical
  rw [JacobiData.projNorm, JacobiData.projNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul]
  show J.d m * ((c • (J.U *ᵥ v)) m) ^ 2 = c ^ 2 * (J.d m * ((J.U *ᵥ v) m) ^ 2)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The projected norm depends only on the tail coordinates.** -/
theorem JacobiData.projNorm_congr_tail (J : JacobiData n) (i : Fin n) {v w : Fin n → ℝ}
    (h : ∀ m : Fin n, i ≤ m → v m = w m) : J.projNorm i v = J.projNorm i w := by
  classical
  rw [JacobiData.projNorm, JacobiData.projNorm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  have hval : (J.U *ᵥ v) m = (J.U *ᵥ w) m := by
    show ∑ p, J.U m p * v p = ∑ p, J.U m p * w p
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases lt_or_ge p m with hpm | hpm
    · rw [J.upper m p hpm, zero_mul, zero_mul]
    · rw [h p (le_trans hm.2 hpm)]
  rw [hval]

/-- **A minimiser of the projected norm has primitive tail.**  If every coordinate from `i` on were
divisible by `k ≥ 2`, dividing by `k` would produce a lattice vector with nonzero projection and
projected norm `dᵢ / k² < dᵢ`. -/
theorem JacobiData.not_dvd_of_projNorm_min (J : JacobiData n) (i : Fin n)
    (hmin : ∀ v : Fin n → ℤ, (∃ m : Fin n, i ≤ m ∧ v m ≠ 0) →
      J.d i ≤ J.projNorm i (intVec v))
    {v : Fin n → ℤ} (hv : ∃ m : Fin n, i ≤ m ∧ v m ≠ 0)
    (hvmin : J.projNorm i (intVec v) = J.d i)
    {k : ℤ} (hk : 2 ≤ k) : ¬ (∀ m : Fin n, i ≤ m → k ∣ v m) := by
  classical
  intro hdvd
  set w : Fin n → ℤ := fun m => if i ≤ m then v m / k else 0 with hw
  have hk0 : k ≠ 0 := by omega
  have htail : ∀ m : Fin n, i ≤ m → v m = k * w m := by
    intro m hm
    rw [hw]
    simp only [if_pos hm]
    exact (Int.ediv_mul_cancel (hdvd m hm)).symm ▸ (Int.mul_ediv_cancel' (hdvd m hm)).symm
  have hwne : ∃ m : Fin n, i ≤ m ∧ w m ≠ 0 := by
    obtain ⟨m, hm, hvm⟩ := hv
    refine ⟨m, hm, ?_⟩
    intro hcon
    apply hvm
    rw [htail m hm, hcon, mul_zero]
  have hagree : ∀ m : Fin n, i ≤ m → intVec v m = ((k : ℝ) • intVec w) m := by
    intro m hm
    show ((v m : ℤ) : ℝ) = (k : ℝ) * ((w m : ℤ) : ℝ)
    rw [htail m hm]
    push_cast
    ring
  have hscale : J.projNorm i (intVec v) = (k : ℝ) ^ 2 * J.projNorm i (intVec w) := by
    rw [J.projNorm_congr_tail i hagree, J.projNorm_smul]
  have hlow : J.d i ≤ J.projNorm i (intVec w) := hmin w hwne
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hdi : (0 : ℝ) < J.d i := J.pos i
  rw [hvmin] at hscale
  have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hP : 0 ≤ J.projNorm i (intVec w) := J.projNorm_nonneg i _
  have h4 : 4 * J.projNorm i (intVec w) ≤ (k : ℝ) ^ 2 * J.projNorm i (intVec w) :=
    mul_le_mul_of_nonneg_right hk2 hP
  linarith [hscale, hlow, hdi, h4]

end GaloisForLFunctions.HTGeometry
