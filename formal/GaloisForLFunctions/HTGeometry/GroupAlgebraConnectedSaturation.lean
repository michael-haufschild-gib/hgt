import GaloisForLFunctions.HTGeometry.CharacterLatticeSaturation
import GaloisForLFunctions.HTGeometry.ConnectedPrimeSpectrumIdempotent

/-!
# Connected group algebras have torsion-free character groups

If a character has finite positive order, its normalized cyclic-orbit sum is a nontrivial
idempotent in the group algebra.  A preconnected prime spectrum excludes that idempotent, so the
character group is torsion-free.  Applied to a quotient character group, this proves saturation of
the defining relation lattice.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry
namespace GroupAlgebraConnectedSaturation

noncomputable section

open ConnectedPrimeSpectrumIdempotent CharacterLatticeSaturation

variable {k M : Type*} [Field k] [CharZero k] [AddCommGroup M]

/-- Group-algebra element attached to a character. -/
def cyclicGenerator (q : M) : AddMonoidAlgebra k M :=
  AddMonoidAlgebra.single q 1

/-- Sum of the first `d` powers of the group-algebra element attached to a character. -/
def cyclicSum (q : M) (d : ℕ) : AddMonoidAlgebra k M :=
  ∑ i ∈ Finset.range d, cyclicGenerator q ^ i

/-- Normalized cyclic-orbit sum. -/
def cyclicAverage (q : M) (d : ℕ) : AddMonoidAlgebra k M :=
  (d : k)⁻¹ • cyclicSum q d

omit [CharZero k] in
@[simp] theorem cyclicGenerator_pow (q : M) (i : ℕ) :
    cyclicGenerator (k := k) q ^ i = AddMonoidAlgebra.single (i • q) 1 := by
  induction i with
  | zero => simp [cyclicGenerator, AddMonoidAlgebra.one_def]
  | succ i hi =>
      rw [pow_succ, hi, cyclicGenerator, AddMonoidAlgebra.single_mul_single]
      simp [add_nsmul]

omit [CharZero k] in
theorem cyclicGenerator_pow_eq_one {q : M} {d : ℕ} (hdq : d • q = 0) :
    cyclicGenerator (k := k) q ^ d = 1 := by
  rw [cyclicGenerator_pow, hdq]
  simp [AddMonoidAlgebra.one_def]

omit [CharZero k] in
theorem cyclicGenerator_mul_cyclicSum {q : M} {d : ℕ}
    (hd : 0 < d) (hdq : d • q = 0) :
    cyclicGenerator (k := k) q * cyclicSum q d = cyclicSum q d := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  simp only [cyclicSum, Finset.mul_sum]
  have hpow : cyclicGenerator (k := k) q ^ (r + 1) = 1 :=
    cyclicGenerator_pow_eq_one hdq
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [pow_zero]
  have hterm : ∀ i : ℕ,
      cyclicGenerator (k := k) q * cyclicGenerator q ^ i =
        cyclicGenerator q ^ (i + 1) := by
    intro i
    rw [pow_succ']
  simp_rw [hterm]
  rw [hpow]

omit [CharZero k] in
theorem cyclicGenerator_pow_mul_cyclicSum {q : M} {d : ℕ}
    (hd : 0 < d) (hdq : d • q = 0) (i : ℕ) :
    cyclicGenerator (k := k) q ^ i * cyclicSum q d = cyclicSum q d := by
  induction i with
  | zero => simp
  | succ i hi =>
      rw [pow_succ, mul_assoc, cyclicGenerator_mul_cyclicSum hd hdq, hi]

omit [CharZero k] in
theorem cyclicSum_mul_self {q : M} {d : ℕ}
    (hd : 0 < d) (hdq : d • q = 0) :
    cyclicSum (k := k) q d * cyclicSum q d = (d : k) • cyclicSum q d := by
  change (∑ i ∈ Finset.range d, cyclicGenerator (k := k) q ^ i) * cyclicSum q d =
    (d : k) • cyclicSum q d
  rw [Finset.sum_mul]
  calc
    (∑ i ∈ Finset.range d, cyclicGenerator (k := k) q ^ i * cyclicSum q d) =
        ∑ _i ∈ Finset.range d, cyclicSum q d := by
          apply Finset.sum_congr rfl
          intro i hi
          exact cyclicGenerator_pow_mul_cyclicSum hd hdq i
    _ = (d : ℕ) • cyclicSum q d := by rw [Finset.sum_const, Finset.card_range]
    _ = (d : k) • cyclicSum q d := (Nat.cast_smul_eq_nsmul k d _).symm

/-- A finite-order character produces an idempotent normalized cyclic average. -/
theorem cyclicAverage_isIdempotentElem {q : M} {d : ℕ}
    (hd : 0 < d) (hdq : d • q = 0) :
    IsIdempotentElem (cyclicAverage (k := k) q d) := by
  rw [isIdempotentElem_iff, cyclicAverage]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul, cyclicSum_mul_self hd hdq, smul_smul]
  have hd0 : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  simp [hd0]

omit [CharZero k] in
theorem cyclicSum_coeff_zero {q : M} {d : ℕ}
    (hd : 0 < d)
    (hmin : ∀ i : ℕ, 0 < i → i < d → i • q ≠ 0) :
    (cyclicSum (k := k) q d).coeff 0 = 1 := by
  classical
  simp only [cyclicSum, cyclicGenerator_pow, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  change Finsupp.applyAddHom 0
    (∑ i ∈ Finset.range d, Finsupp.single (i • q) (1 : k)) = 1
  rw [map_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    change (Finsupp.single (i • q) (1 : k) : M →₀ k) 0 = 0
    rw [Finsupp.single_eq_of_ne]
    exact (hmin i (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)).symm
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hd)).elim

omit [CharZero k] in
theorem cyclicAverage_coeff_zero {q : M} {d : ℕ}
    (hd : 0 < d)
    (hmin : ∀ i : ℕ, 0 < i → i < d → i • q ≠ 0) :
    (cyclicAverage (k := k) q d).coeff 0 = (d : k)⁻¹ := by
  simp [cyclicAverage, AddMonoidAlgebra.coeff_smul,
    cyclicSum_coeff_zero hd hmin]

theorem cyclicAverage_ne_zero {q : M} {d : ℕ}
    (hd : 0 < d)
    (hmin : ∀ i : ℕ, 0 < i → i < d → i • q ≠ 0) :
    cyclicAverage (k := k) q d ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun x : AddMonoidAlgebra k M => x.coeff 0) hzero
  rw [cyclicAverage_coeff_zero hd hmin] at hcoeff
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)) hcoeff

theorem cyclicAverage_ne_one {q : M} {d : ℕ}
    (hd1 : 1 < d)
    (hmin : ∀ i : ℕ, 0 < i → i < d → i • q ≠ 0) :
    cyclicAverage (k := k) q d ≠ 1 := by
  intro hone
  have hcoeffRaw := congrArg (fun x : AddMonoidAlgebra k M => x.coeff 0) hone
  have hcoeff : (d : k)⁻¹ = 1 := by
    rw [cyclicAverage_coeff_zero (by omega) hmin] at hcoeffRaw
    simpa [AddMonoidAlgebra.one_def] using hcoeffRaw
  have hdne : (d : k) ≠ 1 := by
    exact_mod_cast (Nat.ne_of_gt hd1)
  exact hdne (inv_eq_one.mp hcoeff)

/-- If a group algebra has only trivial idempotents, its character group is torsion-free. -/
theorem eq_zero_of_nsmul_eq_zero_of_groupAlgebra_idempotents_trivial
    (htriv : ∀ e : AddMonoidAlgebra k M, IsIdempotentElem e → e = 0 ∨ e = 1)
    {q : M} {n : ℕ} (hn : 0 < n) (hnq : n • q = 0) :
    q = 0 := by
  classical
  by_contra hq
  let P : ℕ → Prop := fun d => 0 < d ∧ d • q = 0
  have hex : ∃ d, P d := ⟨n, hn, hnq⟩
  let d := Nat.find hex
  have hdspec : 0 < d ∧ d • q = 0 := Nat.find_spec hex
  have hmin : ∀ i : ℕ, 0 < i → i < d → i • q ≠ 0 := by
    intro i hi hid hiq
    exact (Nat.find_min hex hid) ⟨hi, hiq⟩
  have hd1 : 1 < d := by
    have hdne1 : d ≠ 1 := by
      intro hdEq
      apply hq
      have hq0 : 1 • q = 0 := by simpa [hdEq] using hdspec.2
      simpa using hq0
    omega
  let e := cyclicAverage (k := k) q d
  have he : IsIdempotentElem e :=
    cyclicAverage_isIdempotentElem hdspec.1 hdspec.2
  have he0 : e ≠ 0 := cyclicAverage_ne_zero hdspec.1 hmin
  have he1 : e ≠ 1 := cyclicAverage_ne_one hd1 hmin
  rcases htriv e he with hzero | hone
  · exact he0 hzero
  · exact he1 hone

/-- A character group whose group algebra has preconnected prime spectrum is torsion-free. -/
theorem eq_zero_of_nsmul_eq_zero_of_preconnected_groupAlgebra_primeSpectrum
    {q : M} {n : ℕ} (hn : 0 < n) (hnq : n • q = 0)
    [PreconnectedSpace (PrimeSpectrum (AddMonoidAlgebra k M))] :
    q = 0 :=
  eq_zero_of_nsmul_eq_zero_of_groupAlgebra_idempotents_trivial
    (k := k) (M := M)
    (fun _ he => isIdempotentElem_eq_zero_or_one_of_preconnected_primeSpectrum he)
    hn hnq

/-- Preconnectedness of the quotient group algebra proves integral saturation of the relation
subgroup. -/
theorem integerSaturated_of_preconnected_groupAlgebra_primeSpectrum
    (L : AddSubgroup M)
    [PreconnectedSpace (PrimeSpectrum (AddMonoidAlgebra k (M ⧸ L)))] :
    IntegerSaturated L.toIntSubmodule := by
  rw [integerSaturated_toIntSubmodule_iff_quotient_nsmul_eq_zero]
  intro n q hn hnq
  exact
    eq_zero_of_nsmul_eq_zero_of_preconnected_groupAlgebra_primeSpectrum
      (k := k) (M := M ⧸ L) hn hnq

open AffineExponentialGroup AffineExponentialProjectionClassification

/-- Connectedness of the group algebra classified by the torus projection's character quotient
forces saturation of the mixed subgroup's torus-relation lattice. -/
theorem torusRelationLattice_integerSaturated_of_preconnected_groupAlgebra_primeSpectrum
    (k : Type*) [Field k] [CharZero k] {n : ℕ}
    (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]
    [PreconnectedSpace
      (PrimeSpectrum
        (AddMonoidAlgebra k
          ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I)))] :
    IntegerSaturated (torusRelationLattice k I).toIntSubmodule :=
  integerSaturated_of_preconnected_groupAlgebra_primeSpectrum
    (k := k) (torusRelationLattice k I)

end
end GroupAlgebraConnectedSaturation
end GaloisForLFunctions.HTGeometry
