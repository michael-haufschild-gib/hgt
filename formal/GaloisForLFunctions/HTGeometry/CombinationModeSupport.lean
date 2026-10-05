import GaloisForLFunctions.HTGeometry.HankelDetTotalDegree

/-!
# Combination-mode support of polynomials in axis modes

A Laurent polynomial on the torus `𝕋^ι` is an element of `R[ι →₀ ℤ]`; its modes are the exponent
vectors `m : ι →₀ ℤ` with nonzero coefficient, and the support size `|supp m|` counts the
coordinates a mode combines.  An element is *axis-mode* when every mode has support size at most
one.

Mode support sizes are subadditive under multiplication, so a polynomial of total degree `d` in
axis-mode elements has all its modes of support size at most `d`.  In particular, if the power
sums `P_k` are axis-mode, the Hankel determinant `det (P_{i+j})_{i,j<d}` carries only combination
modes of support at most `d`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {R ι : Type*} [CommRing R]

/-- Every mode of `x` combines at most `d` coordinates. -/
def ModeSupportLE (d : ℕ) (x : AddMonoidAlgebra R (ι →₀ ℤ)) : Prop :=
  ∀ m ∈ x.coeff.support, #m.support ≤ d

theorem ModeSupportLE.mono {d e : ℕ} {x : AddMonoidAlgebra R (ι →₀ ℤ)} (h : ModeSupportLE d x)
    (hde : d ≤ e) : ModeSupportLE e x :=
  fun m hm => (h m hm).trans hde

theorem ModeSupportLE.add {d : ℕ} {x y : AddMonoidAlgebra R (ι →₀ ℤ)} (hx : ModeSupportLE d x)
    (hy : ModeSupportLE d y) : ModeSupportLE d (x + y) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coeff_add] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
  · exact hx m h
  · exact hy m h

theorem ModeSupportLE.zero (d : ℕ) : ModeSupportLE d (0 : AddMonoidAlgebra R (ι →₀ ℤ)) := by
  intro m hm
  simp at hm

theorem card_support_add_le [DecidableEq ι] (m₁ m₂ : ι →₀ ℤ) :
    #(m₁ + m₂).support ≤ #m₁.support + #m₂.support :=
  (card_le_card Finsupp.support_add).trans (card_union_le _ _)

theorem ModeSupportLE.mul {d e : ℕ} {x y : AddMonoidAlgebra R (ι →₀ ℤ)} (hx : ModeSupportLE d x)
    (hy : ModeSupportLE e y) : ModeSupportLE (d + e) (x * y) := by
  classical
  intro m hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset x y hm)
  exact (card_support_add_le m₁ m₂).trans (Nat.add_le_add (hx m₁ hm₁) (hy m₂ hm₂))

theorem ModeSupportLE.algebraMap (r : R) :
    ModeSupportLE 0 (algebraMap R (AddMonoidAlgebra R (ι →₀ ℤ)) r) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hm
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hm)]
  simp

theorem ModeSupportLE.one : ModeSupportLE 0 (1 : AddMonoidAlgebra R (ι →₀ ℤ)) := by
  have := ModeSupportLE.algebraMap (R := R) (ι := ι) 1
  rwa [map_one] at this

theorem ModeSupportLE.pow {d : ℕ} {x : AddMonoidAlgebra R (ι →₀ ℤ)} (hx : ModeSupportLE d x)
    (k : ℕ) : ModeSupportLE (d * k) (x ^ k) := by
  induction k with
  | zero => simpa using ModeSupportLE.one (R := R) (ι := ι)
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

/-- **A polynomial of total degree `d` in axis-mode elements has mode support at most `d`.** -/
theorem modeSupportLE_aeval {d : ℕ} (P : ℕ → AddMonoidAlgebra R (ι →₀ ℤ))
    (hP : ∀ k, ModeSupportLE 1 (P k)) (Q : MvPolynomial ℕ R) (hQ : Q.totalDegree ≤ d) :
    ModeSupportLE d (MvPolynomial.aeval P Q) := by
  classical
  rw [MvPolynomial.as_sum Q, map_sum]
  refine Finset.sum_induction _ (ModeSupportLE d) (fun a b ha hb => ha.add hb)
    (ModeSupportLE.zero d) fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  have hdeg : (s.sum fun _ e => e) ≤ d := (MvPolynomial.le_totalDegree hs).trans hQ
  have hprod : ModeSupportLE (s.sum fun _ e => e) (s.prod fun i k => P i ^ k) := by
    unfold Finsupp.prod Finsupp.sum
    induction s.support using Finset.induction_on with
    | empty => simpa using ModeSupportLE.one (R := R) (ι := ι)
    | insert a t ha ih =>
        rw [prod_insert ha, sum_insert ha]
        have := ((hP a).pow (s a)).mul ih
        simpa [one_mul] using this
  have := (ModeSupportLE.algebraMap (ι := ι) (MvPolynomial.coeff s Q)).mul hprod
  rw [zero_add] at this
  exact this.mono hdeg

/-- **Axis-mode power sums give a Hankel determinant of combination-mode support at most `d`.** -/
theorem modeSupportLE_det_hankel [Nontrivial R] (d : ℕ) (P : ℕ → AddMonoidAlgebra R (ι →₀ ℤ))
    (hP : ∀ k, ModeSupportLE 1 (P k)) :
    ModeSupportLE d (Matrix.det (fun i j : Fin d => P (i.val + j.val))) := by
  classical
  have hmap : Matrix.det (fun i j : Fin d => P (i.val + j.val)) =
      MvPolynomial.aeval P (Matrix.det (fun i j : Fin d =>
        (MvPolynomial.X (i.val + j.val) : MvPolynomial ℕ R))) := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [AlgHom.mapMatrix_apply]
  rw [hmap]
  exact modeSupportLE_aeval P hP _ (totalDegree_hankelDet_le d)

end GaloisForLFunctions.HTGeometry
