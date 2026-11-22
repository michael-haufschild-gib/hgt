import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Nat.Totient

/-!
# Finite cyclic-order measurements with arbitrary shell mixing

Every conserving propagator is the inverse square root of the shell count
followed on the right by a unitary. Positivity selects a unique propagator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open scoped Matrix MatrixOrder ComplexOrder

abbrev Block (M : ℕ) := Matrix (Fin M) (Fin M) ℂ

def size {M : ℕ} (i : Fin M) := i.val+1

def radius {M : ℕ} (i : Fin M) : ℝ := Real.sqrt (size i)

private theorem radius_pos {M : ℕ} (i : Fin M) : 0 < radius i :=
  Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos i.val)

private theorem radius_sq {M : ℕ} (i : Fin M) : (radius i:ℂ)^2 = (size i:ℂ) := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (size i))

def root (M : ℕ) : Block M := Matrix.diagonal fun i => (radius i:ℂ)

def critical (M : ℕ) : Block M := Matrix.diagonal fun i => ((radius i)⁻¹:ℝ)

theorem critical_positive (M : ℕ) : (critical M).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (radius_pos i).le)

private theorem root_critical (M : ℕ) : root M * critical M = 1 := by
  rw [root,critical,Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
  congr 1
  funext i
  change (radius i:ℂ)*↑((radius i)⁻¹) = 1
  rw [Complex.ofReal_inv,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (radius_pos i).ne')]

private theorem critical_root (M : ℕ) : critical M * root M = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin M))).mp (root_critical M)

abbrev OrderRow (M : ℕ) := (i : Fin M) × (size i).divisors

/-- The output records both the propagated shell and the measured cyclic order. -/
def orderSplit {M : ℕ} (G : Block M) : Matrix (OrderRow M) (Fin M) ℂ :=
  fun x j => (Real.sqrt x.2.val.totient:ℂ)*G x.1 j

private theorem weight_product (a : ℝ) (x y : ℂ) :
    star ((a:ℂ)*x)*((a:ℂ)*y) = (a:ℂ)^2*(star x*y) := by
  rw [star_mul',Complex.star_def,Complex.conj_ofReal]
  ring

/-- Summing the order multiplicities recovers the full count of each intermediate shell. -/
theorem order_gram {M : ℕ} (G : Block M) :
    (orderSplit G)ᴴ * orderSplit G = (root M*G)ᴴ*(root M*G) := by
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hterm (d : (size n).divisors) :
      (orderSplit G)ᴴ i ⟨n,d⟩ * orderSplit G ⟨n,d⟩ j =
        (d.val.totient:ℂ)*(star (G n i)*G n j) := by
    change star ((Real.sqrt d.val.totient:ℂ)*G n i)*((Real.sqrt d.val.totient:ℂ)*G n j) = _
    rw [weight_product,show (Real.sqrt d.val.totient:ℂ)^2 = (d.val.totient:ℂ) by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d.val.totient)]
  simp_rw [hterm]
  rw [← Finset.sum_mul,← Nat.cast_sum,Finset.univ_eq_attach,
    (size n).divisors.sum_attach Nat.totient,Nat.sum_totient,Matrix.conjTranspose_apply,
    root,Matrix.diagonal_mul,Matrix.diagonal_mul,weight_product,radius_sq]

/-- All possible mixing at a single cutoff consists of a unitary on the input. -/
theorem order_isometry_iff_unitary {M : ℕ} (G : Block M) :
    (orderSplit G)ᴴ*orderSplit G = 1 ↔
      ∃ U : Matrix.unitaryGroup (Fin M) ℂ, G = critical M*U.val := by
  rw [order_gram]
  constructor
  · intro h
    let U := root M*G
    have hu : U ∈ Matrix.unitaryGroup (Fin M) ℂ := Matrix.mem_unitaryGroup_iff.mpr
      ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin M))).mp h)
    refine ⟨⟨U,hu⟩,?_⟩
    change G = critical M*(root M*G)
    rw [← mul_assoc,critical_root,one_mul]
  · rintro ⟨U,rfl⟩
    rw [← mul_assoc (root M) (critical M) U.val,root_critical,one_mul]
    exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin M))).mpr
      (Matrix.mem_unitaryGroup_iff.mp U.property)

/-- Conservation fixes the output Gram matrix even for arbitrary complex mixing. -/
theorem output_gram {M : ℕ} {G : Block M} (h : (orderSplit G)ᴴ*orderSplit G = 1) :
    G*Gᴴ = critical M^2 := by
  obtain ⟨U,rfl⟩ := (order_isometry_iff_unitary G).mp h
  have hu : U.val*U.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [Matrix.conjTranspose_mul,(critical_positive M).isHermitian.eq,mul_assoc,
    ← mul_assoc U.val,hu,one_mul,pow_two]

/-- A positive conserving propagator is diagonal in the occupation basis at the critical amplitude. -/
theorem positive_order_isometry_iff {M : ℕ} (G : Block M) :
    G.PosSemidef ∧ (orderSplit G)ᴴ*orderSplit G = 1 ↔ G = critical M := by
  constructor
  · rintro ⟨hp,hi⟩
    have hs := output_gram hi
    rw [hp.isHermitian.eq,← pow_two] at hs
    exact (CFC.sqrt_sq G (Matrix.nonneg_iff_posSemidef.mpr hp)).symm.trans
      ((congrArg CFC.sqrt hs).trans (CFC.sqrt_sq _ (Matrix.nonneg_iff_posSemidef.mpr (critical_positive M))))
  · rintro rfl
    exact ⟨critical_positive M,(order_isometry_iff_unitary _).mpr ⟨1,(mul_one _).symm⟩⟩

#print axioms order_gram
#print axioms order_isometry_iff_unitary
#print axioms positive_order_isometry_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
