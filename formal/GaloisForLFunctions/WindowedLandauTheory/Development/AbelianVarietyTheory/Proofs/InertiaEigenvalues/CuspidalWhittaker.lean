import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalWhittakerStep
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperBlockWhittaker
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerVectors

/-! A cuspidal representation of the finite general linear group has a
nonzero standard Whittaker vector. -/

noncomputable section
open scoped Classical

open CategoryTheory WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private def HasLeadingWhittakerVector (V : FDRep ℂ (Gn g n)) (k : ℕ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ u : upperUnitriangular g n, FixLeadingColumns k u.val.val →
    V.ρ u.val v = (whittakerCharacter ZMod.stdAddChar n u : ℂ) • v

private theorem extend_leading_whittaker (V : FDRep ℂ (Gn g n)) {k : ℕ}
    (hk : 0 < k) (hkn : k < n) (h0 : res k (n - k) V.character 1 1 = 0)
    (h : HasLeadingWhittakerVector V (k + 1)) : HasLeadingWhittakerVector V k := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hkn).ne'
  have hn : n = a + 1 + (b + 1) :=
    (Nat.add_sub_of_le hkn.le).symm.trans (congrArg ((a + 1) + ·) hb)
  subst n
  rw [hb] at h0
  obtain ⟨v, hv, hf⟩ := h
  have hvTail (X : Matrix (Fin (a + 1)) (Fin (b + 1)) (ZMod g))
      (D : upperUnitriangular g (b + 1)) (hX : ∀ i, X i 0 = 0) :
      V.ρ (upperBlockUnit 1 X D.val) v = (whittakerCharacter ZMod.stdAddChar (b + 1) D : ℂ) • v := by
    let u : upperUnitriangular g (a + 1 + (b + 1)) :=
      ⟨upperBlockUnit 1 X D.val, isUniUp_upperBlockMatrix X D.property⟩
    have hp : FixLeadingColumns (a + 1 + 1) u.val.val :=
      (fixLeadingColumns_succ_iff D.property).mpr hX
    have he : (whittakerCharacter ZMod.stdAddChar (a + 1 + (b + 1)) u : ℂ) =
        (whittakerCharacter ZMod.stdAddChar (b + 1) D : ℂ) := by
      simpa [hX] using whittakerCharacter_upperBlock ZMod.stdAddChar X D
    exact (hf u hp).trans (congrArg (· • v) he)
  obtain ⟨z, hz, hZ⟩ := exists_extended_whittaker_vector V h0 v hv hvTail
  refine ⟨z, hz, fun u hu => ?_⟩
  obtain ⟨X, D, he⟩ := exists_upperBlockUnit_of_fixLeadingColumns u hu
  let u' : upperUnitriangular g (a + 1 + (b + 1)) :=
    ⟨upperBlockUnit 1 X D.val, isUniUp_upperBlockMatrix X D.property⟩
  have hU : u = u' := Subtype.ext he
  rw [hU, show (whittakerCharacter ZMod.stdAddChar (a + 1 + (b + 1)) u' : ℂ) = _ from
    whittakerCharacter_upperBlock ZMod.stdAddChar X D]
  exact hZ X D

private theorem exists_nonzero_vector_of_simple (V : FDRep ℂ (Gn g n)) [Simple V] :
    ∃ v : V, v ≠ 0 := by
  letI := invertibleOfNonzero (NeZero.ne (Nat.card (Gn g n) : ℂ))
  by_contra! h
  letI : Subsingleton V := ⟨fun x y => (h x).trans (h y).symm⟩
  have hz (x : Gn g n) : V.character x = 0 :=
    (congrArg (LinearMap.trace ℂ V) (Subsingleton.elim (V.ρ x) 0)).trans (map_zero _)
  have hIso : Nonempty (V ≅ V) := ⟨Iso.refl V⟩
  simpa [hz, hIso] using FDRep.char_orthonormal V V

/-- The standard Whittaker projection has nonzero trace on every cuspidal character. -/
theorem wh_std_ne_zero_of_cuspidal {χ : Gn g n → ℂ} (hχ : IsCusp χ) :
    wh ZMod.stdAddChar χ ≠ 0 := by
  obtain ⟨hn, ⟨V, hV, hχV⟩, hRes⟩ := hχ
  letI : Simple V := hV
  have he : V.character = χ := funext hχV
  rw [← he] at hRes ⊢
  have hGood (t : ℕ) (ht : t < n) : HasLeadingWhittakerVector V (n - t) := by
    induction t with
    | zero =>
      rw [Nat.sub_zero]
      obtain ⟨v, hv⟩ := exists_nonzero_vector_of_simple V
      refine ⟨v, hv, fun u hu => ?_⟩
      have e : u = 1 := Subtype.ext (Units.ext (Matrix.ext fun i j => hu i j j.isLt))
      rw [e]
      simp
    | succ t ih =>
      have h := ih (by omega)
      have e : n - t = (n - (t + 1)) + 1 := by omega
      rw [e] at h
      exact extend_leading_whittaker V (by omega) (by omega)
        (hRes (n - (t + 1)) (by omega) (by omega)) h
  have h := hGood (n - 1) (by omega)
  rw [show n - (n - 1) = 1 by omega] at h
  obtain ⟨v, hv, h⟩ := h
  exact wh_ne_zero_of_vector ZMod.stdAddChar V v hv
    (fun u => h u (fixLeadingColumns_one u.property))

end GlobalTheory.GLq
