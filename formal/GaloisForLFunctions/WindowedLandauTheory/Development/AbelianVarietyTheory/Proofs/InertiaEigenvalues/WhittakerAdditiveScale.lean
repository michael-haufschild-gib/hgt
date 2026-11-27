import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PatternCharacterGroups
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularMonomialCosets
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-! Conjugation by a diagonal of successive powers transports the standard
Whittaker character to any nontrivial additive character of the prime field. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- A nontrivial additive character of the prime field is the standard character
after multiplication by a unit. -/
theorem exists_addChar_scale (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∃ c : (ZMod g)ˣ, ∀ x, ψ x = ZMod.stdAddChar ((c : ZMod g) * x) := by
  let A (k : ZMod g) := ∑ x : ZMod g, ψ x * ZMod.stdAddChar (-(k * x))
  have hsum : ∑ k : ZMod g, A k = (g : ℂ) := by
    unfold A
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← mul_neg, RHTower.Sieve.sum_stdAddChar_mul, neg_eq_zero]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
    · simp
    · intro x _ hx
      simp only [if_neg hx, Nat.cast_zero, mul_zero]
  obtain ⟨k, hk⟩ : ∃ k, A k ≠ 0 := by
    by_contra! h
    rw [Finset.sum_eq_zero (fun k _ => h k)] at hsum
    exact (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero) hsum.symm
  have hscale (x : ZMod g) : ψ x = ZMod.stdAddChar (k * x) := by
    have htranslate : A k = (ψ x * ZMod.stdAddChar (-(k * x))) * A k := calc
      A k = ∑ y : ZMod g, ψ (x + y) * ZMod.stdAddChar (-(k * (x + y))) :=
        (Equiv.sum_comp (Equiv.addLeft x)
          (fun y => ψ y * ZMod.stdAddChar (-(k * y)))).symm
      _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [mul_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
        ring
    have he : ψ x * ZMod.stdAddChar (-(k * x)) = 1 :=
      mul_right_cancel₀ hk (htranslate.symm.trans (one_mul _).symm)
    have hcancel : ZMod.stdAddChar (-(k * x)) * ZMod.stdAddChar (k * x) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    simpa only [mul_assoc, hcancel, mul_one, one_mul] using
      congrArg (· * ZMod.stdAddChar (k * x)) he
  have hk0 : k ≠ 0 := by
    intro h
    apply hψ
    ext x
    simp [hscale x, h]
  exact ⟨Units.mk0 k hk0, hscale⟩

/-- All nontrivial Whittaker characters of the prime field give the same
projection trace on a class function. -/
theorem wh_eq_standard (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (χ : Gn g n → ℂ) (hχ : IsClass χ) : wh ψ χ = wh ZMod.stdAddChar χ := by
  obtain ⟨c, hc⟩ := exists_addChar_scale ψ hψ
  let d (j : Fin n) := c ^ j.val
  let w : Gn g n := monomialUnit (Equiv.refl _) d
  let e : Gn g n ≃ Gn g n := (MulAut.conj w⁻¹).toEquiv
  have hw (u : Gn g n) : e u = w⁻¹ * u * w := by simp [e]
  have hval (u : Gn g n) (i j : Fin n) :
      (e u).val i j = (d i : ZMod g)⁻¹ * u.val i j * d j := by
    rw [hw]
    exact monomialConj_apply (Equiv.refl _) d u i j
  have hU (u : Gn g n) : IsUniUp u.val ↔ IsUniUp (e u).val := by
    constructor
    · intro hu i j
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hval, (hu i j).1 h, mul_zero, zero_mul]
      · subst j
        rw [hval, (hu i i).2 rfl, mul_one, inv_mul_cancel₀ (Units.ne_zero (d i))]
    · intro hu i j
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have he := (hval u i j).symm.trans ((hu i j).1 h)
        exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (Units.ne_zero (d j)))).resolve_left
          (inv_ne_zero (Units.ne_zero (d i)))
      · subst j
        have he := (hval u i i).symm.trans ((hu i i).2 rfl)
        rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero (d i)), one_mul] at he
        exact he
  let sup (u : Gn g n) := ∑ i ∈ Finset.range (n - 1), entN u.val i (i + 1)
  have hs (u : Gn g n) : sup (e u) = (c : ZMod g) * sup u := by
    unfold sup
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hn : i < n ∧ i + 1 < n := by omega
    rw [entN, dif_pos hn, entN, dif_pos hn, hval]
    have hd : (d ⟨i + 1, hn.2⟩ : ZMod g) = (d ⟨i, hn.1⟩ : ZMod g) * c := by
      change ((c ^ (i + 1) : (ZMod g)ˣ) : ZMod g) = _
      rw [pow_succ, Units.val_mul]
    rw [hd, ← mul_assoc, mul_right_comm ((d _ : ZMod g)⁻¹),
      inv_mul_cancel₀ (Units.ne_zero (d ⟨i, hn.1⟩)), one_mul, mul_comm]
  unfold wh eU
  rw [tr_eDat, tr_eDat]
  congr 1
  refine Finset.sum_equiv e (fun u => by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hU u) fun u _ => ?_
  have hχe : χ (e u) = χ u := by
    rw [hw]
    simpa only [inv_inv] using hχ u w⁻¹
  change (ψ (sup u))⁻¹ * χ u = (ZMod.stdAddChar (sup (e u)))⁻¹ * χ (e u)
  rw [hs, hc, hχe]

end GlobalTheory.GLq
