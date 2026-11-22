import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicHostInertia
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.QuadraticResidueLift
import GaloisForLFunctions.WindowedLandauTheory.SizeWindowBrackets.ChainSlopeWindows.PrimitiveValues

/-! The host sign on the discriminant residue class. -/

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace WindowedLandauTheory.HC.Der

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

theorem exists_unit_crt {A B : ℕ} [NeZero (A * B)] (hAB : A.Coprime B) (x y : ℕ)
    (hx : x.Coprime A) (hy : y.Coprime B) :
    ∃ u : (ZMod (A * B))ˣ, (u : ZMod (A * B)).val ≡ x [MOD A] ∧ (u : ZMod (A * B)).val ≡ y [MOD B] := by
  obtain ⟨u, h₁, h₂⟩ := WindowedLandauTheory.LFunctionChainParameters.LHost.exists_unit_crt rfl hAB
    (dvd_mul_right A B) (dvd_mul_left B A) (ZMod.unitOfCoprime x hx) (ZMod.unitOfCoprime y hy)
  refine ⟨u, (val_modEq_iff (dvd_mul_right A B) u x).mpr ?_,
    (val_modEq_iff (dvd_mul_left B A) u y).mpr ?_⟩
  · rw [h₁, ZMod.coe_unitOfCoprime]
  · rw [h₂, ZMod.coe_unitOfCoprime]

private theorem ordCompl_eq {l m : ℕ} (hl : l.Prime) (k : ℕ) (hm : ¬ l ∣ m) : ordCompl[l] (l ^ k * m) = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  have hf : (l ^ k * m).factorization l = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ hl.ne_zero) hm0, Finsupp.add_apply,
      hl.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  rw [hf, Nat.mul_div_cancel_left _ (pow_pos hl.pos _)]

theorem exists_prime_liesOver {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (span {(p : ℤ)}) := by
  have hne : Ideal.comap (algebraMap ℤ (𝓞 M)) P ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.comap (algebraMap ℤ (𝓞 M)) P = Ideal.span {g} :=
    (Submodule.IsPrincipal.principal (Ideal.comap (algebraMap ℤ (𝓞 M)) P))
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [hg, Ideal.span_singleton_eq_bot]
  have hpr : (Ideal.span {g}).IsPrime := by rw [← hg]; infer_instance
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp hpr
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ⟨?_⟩⟩
  rw [Int.span_natAbs]
  exact hg.symm

variable {φ : Frame} (H : HostRaw φ)

theorem tower_dvd_QSq : 2 ^ (φ.e + 2) ∣ H.QS * H.q := H.tower_dvd.trans (dvd_mul_right _ _)

theorem QSq_dvd : H.QS * H.q ∣ H.condN := dvd_mul_right _ _

theorem split_QSq (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (h : l ∣ H.QS * H.q) : jacobiSym (-(H.d : ℤ)) l = 1 := by
  rcases (Nat.Prime.dvd_mul hl).mp h with h1 | h1
  · exact H.QS_split l hl hl2 h1
  · have hlq : l = H.q := (Nat.prime_dvd_prime_iff_eq hl H.hyp.1).mp h1
    rw [hlq]
    exact H.hyp.2.2.2.2

theorem ordCompl_d : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hd : H.d.Prime := H.hyp.2.1
  have hnd : ¬ H.d ∣ H.QS * H.q := fun h => hd.one_lt.ne' (H.coprime_QSq_d.symm.eq_one_of_dvd h)
  show ordCompl[H.d] (H.QS * H.q * H.d) = H.QS * H.q
  rw [show H.QS * H.q * H.d = H.d ^ 1 * (H.QS * H.q) by ring]
  exact ordCompl_eq hd 1 hnd

theorem ps_congr (u w : (ZMod H.condN)ˣ) (h : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) w) :
    (H.art u).1.1 = (H.art w).1.1 := by
  haveI : NeZero H.condN := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos)⟩
  have h1 : ZMod.unitsMap (QSq_dvd H) (u * w⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := H.art_d (u * w⁻¹) ((val_modEq_one_iff (QSq_dvd H) _).mpr h1)
  have h3 : (H.art (u * w⁻¹)).1.1 = 1 := by
    rcases h2 with h2 | h2 <;> rw [h2] <;> rfl
  have h4 : H.art u = H.art (u * w⁻¹) * H.art w := by rw [← map_mul, inv_mul_cancel_right]
  rw [h4, Prod.fst_mul, Prod.fst_mul, h3, one_mul]

theorem ps_d : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1 := by
  intro u hu
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  haveI : NeZero (H.QS * H.q) := ⟨hM0⟩
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have hs' : ((s : ZMod (H.QS * H.q))) ^ 2 = -((H.d : ℕ) : ZMod (H.QS * H.q)) := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hs
    push_cast at h0
    linear_combination h0
  have hdu : IsUnit ((H.d : ℕ) : ZMod (H.QS * H.q)) :=
    (ZMod.unitOfCoprime H.d H.coprime_QSq_d.symm).isUnit
  have hsu : IsUnit ((s : ZMod (H.QS * H.q))) := by
    have h0 : IsUnit ((s : ZMod (H.QS * H.q)) ^ 2) := by rw [hs']; exact hdu.neg
    exact (isUnit_pow_iff two_ne_zero).mp h0
  obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective (QSq_dvd H) hsu.unit
  have hneg : ((ZMod.unitsMap (QSq_dvd H) (-1) : (ZMod (H.QS * H.q))ˣ) : ZMod (H.QS * H.q)) = -1 := by
    simp [ZMod.unitsMap]
  have key : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) (-1 * w ^ 2) := by
    apply Units.ext
    rw [(val_modEq_iff (QSq_dvd H) u H.d).mp hu, map_mul, map_pow, hw, Units.val_mul,
      Units.val_pow_eq_pow_val, IsUnit.unit_spec, hs', hneg]
    ring
  have h1 := ps_congr H u (-1 * w ^ 2) key
  rw [h1, map_mul, map_pow, H.art_neg_one, Prod.fst_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_fst,
    Int.units_sq, mul_one]
  rfl

end WindowedLandauTheory.HC.Der

end
