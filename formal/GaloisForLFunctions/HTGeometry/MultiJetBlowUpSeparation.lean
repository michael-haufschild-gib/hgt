import GaloisForLFunctions.HTGeometry.MultiJetBlowUpIndependence
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Universal separation of finite exponent families

Every injectively indexed finite family of finitely supported exponent vectors can be separated by
one nonnegative integral weight vector.  Choose a radix strictly larger than every coordinate and
use its powers as weights.  Equality of weighted sums is then equality of fixed-length base-radix
expansions.

Combined with the multi-jet blow-up theorem, this removes its combinatorial rate premise and gives
an unconditional full-rank row packet for every finite family of distinct monomials, realized by
powers of the periodic pole model.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A radix strictly larger than every coordinate of every exponent in a finite family. -/
noncomputable def finiteExponentDigitBase {κ : Type*} [Fintype κ] {n : ℕ}
    (exponent : κ → Fin n →₀ ℕ) : ℕ :=
  2 + ∑ a : κ, (exponent a).sum fun _ m => m

/-- Mixed-radix rates encoding a finite exponent vector as one blow-up order. -/
noncomputable def mixedRadixBlowUpRate {κ : Type*} [Fintype κ] {n : ℕ}
    (exponent : κ → Fin n →₀ ℕ) (k : Fin n) : ℕ :=
  finiteExponentDigitBase exponent ^ (k : ℕ)

private theorem exponent_coordinate_lt_finiteExponentDigitBase {κ : Type*} [Fintype κ]
    {n : ℕ} (exponent : κ → Fin n →₀ ℕ) (a : κ) (k : Fin n) :
    exponent a k < finiteExponentDigitBase exponent := by
  classical
  have hcoordinate :
      exponent a k ≤ (exponent a).sum fun _ m => m := by
    rw [Finsupp.sum_fintype]
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    · simp
  have hfamily :
      (exponent a).sum (fun _ m => m) ≤
        ∑ b : κ, (exponent b).sum fun _ m => m := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun b : κ => (exponent b).sum fun _ m => m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  unfold finiteExponentDigitBase
  omega

private theorem finiteExponentDigitBase_gt_one {κ : Type*} [Fintype κ] {n : ℕ}
    (exponent : κ → Fin n →₀ ℕ) : 1 < finiteExponentDigitBase exponent := by
  classical
  unfold finiteExponentDigitBase
  omega

/-- Mixed-radix weighting separates every injectively indexed finite exponent family. -/
theorem blowUpOrder_mixedRadix_injective {κ : Type*} [Fintype κ] {n : ℕ}
    (exponent : κ → Fin n →₀ ℕ) (hexponent : Function.Injective exponent) :
    Function.Injective fun a => blowUpOrder (mixedRadixBlowUpRate exponent) (exponent a) := by
  classical
  intro a b hab
  have hab' :
      (∑ k : Fin n,
          exponent a k * finiteExponentDigitBase exponent ^ (k : ℕ)) =
        ∑ k : Fin n,
          exponent b k * finiteExponentDigitBase exponent ^ (k : ℕ) := by
    unfold blowUpOrder at hab
    change (exponent a).sum
        (fun k m => m * mixedRadixBlowUpRate exponent k) =
      (exponent b).sum (fun k m => m * mixedRadixBlowUpRate exponent k) at hab
    simp only [mixedRadixBlowUpRate] at hab
    rw [Finsupp.sum_fintype (exponent a)
        (fun k m => m * finiteExponentDigitBase exponent ^ (k : ℕ)) (by simp),
      Finsupp.sum_fintype (exponent b)
        (fun k m => m * finiteExponentDigitBase exponent ^ (k : ℕ)) (by simp)] at hab
    exact hab
  apply hexponent
  apply Finsupp.ext
  apply congrFun
  apply List.ofFn_inj.mp
  apply Nat.ofDigits_inj_of_len_eq (finiteExponentDigitBase_gt_one exponent)
  · simp
  · intro digit hdigit
    rw [List.mem_ofFn'] at hdigit
    obtain ⟨k, rfl⟩ := hdigit
    exact exponent_coordinate_lt_finiteExponentDigitBase exponent a k
  · intro digit hdigit
    rw [List.mem_ofFn'] at hdigit
    obtain ⟨k, rfl⟩ := hdigit
    exact exponent_coordinate_lt_finiteExponentDigitBase exponent b k
  · simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
      List.length_ofFn, Fin.val_cast, Nat.mul_comm, List.sum_ofFn] using! hab'

/-- Every injectively indexed finite exponent family admits a separating blow-up-rate vector. -/
theorem exists_blowUpRate_injective {κ : Type*} [Fintype κ] {n : ℕ}
    (exponent : κ → Fin n →₀ ℕ) (hexponent : Function.Injective exponent) :
    ∃ d : Fin n → ℕ, Function.Injective fun a => blowUpOrder d (exponent a) := by
  exact ⟨mixedRadixBlowUpRate exponent, blowUpOrder_mixedRadix_injective exponent hexponent⟩

/-- Universal finite-monomial full-rank law for periodic pole powers. -/
theorem exists_periodicPolePower_row_packet {κ row : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype row] {n q : ℕ} (exponent : κ → Fin n →₀ ℕ)
    (hexponent : Function.Injective exponent) (f : κ × Fin (q + 1) → row)
    (hf : Function.Injective f) :
    ∃ (d : Fin n → ℕ) (z : row → ℂ),
      (∀ b, z b ∈ upperHalfPlane) ∧ Function.Injective z ∧
        Function.Injective
          (expandedDifferentialEvaluationMatrix q n z exponent
            (fun p => periodicPoleModel (z p.1) ^ d p.2)).mulVec := by
  let d := mixedRadixBlowUpRate exponent
  obtain ⟨z, hzmem, hzinj, hzrank⟩ :=
    exists_row_packet_upperHalfPlane_of_multiBlowUp
      infinite_upperHalfPlane (multiBlowUpData_periodicPolePowers d)
      (blowUpOrder_mixedRadix_injective exponent hexponent) f hf
  exact ⟨d, z, hzmem, hzinj, hzrank⟩

end GaloisForLFunctions.HTGeometry
