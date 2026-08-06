import GaloisForLFunctions.HTGeometry.NonTorusLevelSet

/-!
# The annihilator of a character set

`m ↦ h^m` is a homomorphism from the integer characters to the nonzero
complex numbers, so the characters annihilated by a fixed scaling form a
subgroup: annihilating a set annihilates the lattice it generates.

Taking absolute values turns annihilation into a linear condition on the
logarithms of the coordinate moduli.  A character set whose real span is
everything therefore forces every coordinate of an annihilating scaling to have
unit modulus: an annihilating scaling lies on the torus.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The character homomorphism -/

omit [DecidableEq d] in
theorem charPow_zero (h : d → ℂ) : charPow h (0 : d → ℤ) = 1 := by
  rw [charPow]
  exact Finset.prod_eq_one fun j _ => by simp

omit [DecidableEq d] in
theorem charPow_add {h : d → ℂ} (hne : ∀ j, h j ≠ 0) (m m' : d → ℤ) :
    charPow h (m + m') = charPow h m * charPow h m' := by
  rw [charPow, charPow, charPow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hne j) (m j) (m' j)

omit [DecidableEq d] in
theorem charPow_zsmul (h : d → ℂ) (n : ℤ) (m : d → ℤ) :
    charPow h (n • m) = (charPow h m) ^ n := by
  rw [charPow, charPow, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← zpow_mul, mul_comm]

omit [DecidableEq d] in
/-- **Annihilating a set annihilates the lattice it generates.** -/
theorem charPow_eq_one_of_mem_span {h : d → ℂ} (hne : ∀ j, h j ≠ 0)
    {S : Set (d → ℤ)} (hann : ∀ m ∈ S, charPow h m = 1) {m : d → ℤ}
    (hm : m ∈ Submodule.span ℤ S) : charPow h m = 1 := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact hann x hx
  | zero => exact charPow_zero h
  | add x y _ _ hx hy => rw [charPow_add hne, hx, hy, one_mul]
  | smul n x _ hx => rw [charPow_zsmul, hx, one_zpow]

/-! ### Annihilation forces unit modulus -/

omit [DecidableEq d] in
theorem sum_mul_log_norm_eq_zero {h : d → ℂ} (hne : ∀ j, h j ≠ 0) {m : d → ℤ}
    (hm : charPow h m = 1) :
    ∑ j, (m j : ℝ) * Real.log ‖h j‖ = 0 := by
  have hprod : ∏ j, ‖h j‖ ^ (m j) = 1 := norm_eq_one_of_charPow_eq_one hm
  have hnz : ∀ j ∈ (Finset.univ : Finset d), ‖h j‖ ^ (m j) ≠ 0 := by
    intro j _
    exact zpow_ne_zero _ (norm_ne_zero_iff.2 (hne j))
  have hlog : Real.log (∏ j, ‖h j‖ ^ (m j))
      = ∑ j, Real.log (‖h j‖ ^ (m j)) := Real.log_prod hnz
  rw [hprod, Real.log_one] at hlog
  have hsum : ∑ j, (m j : ℝ) * Real.log ‖h j‖
      = ∑ j, Real.log (‖h j‖ ^ (m j)) :=
    Finset.sum_congr rfl fun j _ => (Real.log_zpow _ _).symm
  rw [hsum, ← hlog]

omit [DecidableEq d] in
/-- **An annihilating scaling lies on the torus.**  If the annihilated
characters span the real coordinate space, every coordinate of the scaling has
unit modulus. -/
theorem norm_eq_one_of_annihilates {h : d → ℂ} (hne : ∀ j, h j ≠ 0)
    {S : Set (d → ℤ)}
    (hfull : ∀ c : d → ℝ, (∀ m ∈ S, ∑ j, (m j : ℝ) * c j = 0) → c = 0)
    (hann : ∀ m ∈ S, charPow h m = 1) (j : d) : ‖h j‖ = 1 := by
  have hc : (fun j => Real.log ‖h j‖) = 0 :=
    hfull _ fun m hm => sum_mul_log_norm_eq_zero hne (hann m hm)
  have hj : Real.log ‖h j‖ = 0 := congrFun hc j
  have hpos : 0 < ‖h j‖ := norm_pos_iff.2 (hne j)
  have := Real.exp_log hpos
  rw [hj, Real.exp_zero] at this
  exact this.symm

omit [DecidableEq d] in
/-- **The annihilator of a spanning character set lies on the unit torus.** -/
theorem mem_unitTorus_of_annihilates {h : d → ℂ} (hne : ∀ j, h j ≠ 0)
    {S : Set (d → ℤ)}
    (hfull : ∀ c : d → ℝ, (∀ m ∈ S, ∑ j, (m j : ℝ) * c j = 0) → c = 0)
    (hann : ∀ m ∈ S, charPow h m = 1) : h ∈ unitTorus d :=
  fun j => norm_eq_one_of_annihilates hne hfull hann j

end

end GaloisForLFunctions.HTGeometry
