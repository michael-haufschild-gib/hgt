import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticMatrixFibres
import GaloisForLFunctions.RepresentationLifting.Probability.PadicMatrixHaar
import Mathlib.Data.Nat.Totient

/-!
# Two spectral coefficients of a Haar p-adic matrix

The trace–determinant chart of Lapid and Shusterman (Lemma C.1) gives
uniform joint coefficients on the invertible-entry event at every finite
precision. At precision one the triangular complement supplies a correction
equal to the number of ground-field roots.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Matrix MeasureTheory OperatorKernels
open scoped Matrix
noncomputable section

/-- Free parameters in a fixed fibre on the invertible-entry chart over an
arbitrary commutative ring, including rings of higher residue precision. -/
def unitEntryTraceDetEquiv {R : Type*} [CommRing R] (t d : R) :
    {A : Matrix (Fin 2) (Fin 2) R // IsUnit (A 0 1) ∧ A.trace=t ∧ A.det=d} ≃ R × Rˣ where
  toFun M := (M.val 0 0,M.property.1.unit)
  invFun q :=
    let row := (traceDetChart q.1 q.2).symm (t,d)
    ⟨!![q.1,(q.2:R);row.1,row.2],q.2.isUnit,by
      have he := (traceDetChart q.1 q.2).apply_symm_apply (t,d)
      exact ⟨(trace_fin_two_of ..).trans (congrArg Prod.fst he),
        (det_fin_two_of ..).trans (congrArg Prod.snd he)⟩⟩
  left_inv M := by
    let y := M.property.1.unit
    have hval : (y:R) = M.val 0 1 := M.property.1.unit_spec
    have he : traceDetChart (M.val 0 0) y (M.val 1 0,M.val 1 1) = (t,d) := by
      apply Prod.ext
      · exact (trace_fin_two M.val).symm.trans M.property.2.1
      · change M.val 0 0*M.val 1 1 - (y:R)*M.val 1 0 = d
        rw [hval,← det_fin_two,M.property.2.2]
    have hr := (traceDetChart (M.val 0 0) y).symm_apply_apply (M.val 1 0,M.val 1 1)
    rw [he] at hr
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hval
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  right_inv q := Prod.ext rfl (Units.ext (IsUnit.unit_spec _))

private theorem card_residue_matrices (q : ℕ) [NeZero q] :
    Nat.card (Matrix (Fin 2) (Fin 2) (ZMod q)) = q^4 := by
  simp only [Matrix,Nat.card_fun,Nat.card_fin,Nat.card_zmod,← pow_mul]

variable (p : ℕ) [Fact p.Prime]

/-- Uniform joint trace and determinant on the unit chart. Its Haar mass
per fibre is φ(q)/q³ for q=p^h, with no tame-characteristic restriction. -/
theorem padicMatrixHaar_unitEntry_traceDet (h : ℕ) (t d : ZMod (p^h)) :
    (padicMatrixHaar p 2).real {M | let A := padicMatrixProjection p h (Fin 2) M
      IsUnit (A 0 1) ∧ A.trace=t ∧ A.det=d} =
      ((p^h).totient : ℝ) / ((p^h : ℕ) : ℝ)^3 := by
  let q := p^h
  have hq : q ≠ 0 := pow_ne_zero h (Fact.out : p.Prime).ne_zero
  letI : NeZero q := ⟨hq⟩
  have hqR : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  rw [padicMatrixHaar_residue_probability p h 2 (fun A => IsUnit (A 0 1) ∧ A.trace=t ∧ A.det=d),
    Nat.card_congr (unitEntryTraceDetEquiv t d), Nat.card_prod]
  have hu : Nat.card (ZMod q)ˣ = q.totient := by
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  change (Nat.card (ZMod q)*Nat.card (ZMod q)ˣ : ℕ) / (Nat.card (Matrix (Fin 2) (Fin 2) (ZMod q)) : ℝ) = _
  rw [hu,card_residue_matrices,Nat.card_zmod,Nat.cast_mul,Nat.cast_pow]
  change (q:ℝ)*q.totient/(q:ℝ)^4 = q.totient/(q:ℝ)^3
  field_simp [hqR] <;> ring

/-- Full joint residue law. Ground-field root count changes the density by
exactly one over p³ per distinct root. -/
theorem padicMatrixHaar_traceDet_mod_prime (t d : ZMod (p^1)) :
    (padicMatrixHaar p 2).real {M | let A := padicMatrixProjection p 1 (Fin 2) M
      A.trace=t ∧ A.det=d} =
      ((p:ℝ)-1 + Nat.card (traceDetRoot t d)) / (p:ℝ)^3 := by
  letI : Fact (p^1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  have hp := (Fact.out : p.Prime).one_le
  have hpR : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicMatrixHaar_residue_probability p 1 2 (fun A => A.trace=t ∧ A.det=d),card_traceDetFibre]
  rw [card_residue_matrices,Nat.card_zmod,Nat.cast_mul,Nat.cast_add]
  have he : (p^1 : ℕ)=p := pow_one _
  simp only [he,Nat.cast_sub hp,Nat.cast_one,Nat.cast_pow]
  field_simp [hpR] <;> ring

#print axioms unitEntryTraceDetEquiv
#print axioms padicMatrixHaar_unitEntry_traceDet
#print axioms padicMatrixHaar_traceDet_mod_prime

end
end GaloisForLFunctions.RepresentationLifting
