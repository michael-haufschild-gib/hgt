import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteFieldFrobeniusPeriods

/-! Irreducible polynomial labels are Frobenius orbits of roots in the algebraic closure. -/

open Polynomial WindowedLandauTheory.CyclotomicNorms

namespace GlobalTheory.GLq

variable {g : ℕ} [hg : Fact g.Prime]

theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) (w : Fbar g)
    (hw : L.teich w ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d w (L.gen d ^ n) = L.teich w ^ n := by
  have hex : ∃ n' : ℕ, L.gen d ^ n = L.gen d ^ n' := ⟨n, rfl⟩
  unfold thetaOf
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have hgd := Nat.one_lt_pow hd.ne' hg.out.one_lt
  have hfo : IsOfFinOrder (L.gen d) := orderOf_pos_iff.mp (by rw [L.gen_order d hd]; omega)
  rw [hfo.pow_eq_pow_iff_modEq, L.gen_order d hd] at hs
  rw [← pow_mod_eq hw n, ← pow_mod_eq hw hex.choose]
  exact congrArg _ hs.symm

end GlobalTheory.GLq

namespace GlobalTheory.GreenExists

variable {g : ℕ} [hg : Fact g.Prime]

theorem mem_rootsBar_iff {P : (ZMod g)[X]} (hP : P ≠ 0) {x : Fbar g} :
    x ∈ rootsBar P ↔ aeval x P = 0 := by
  rw [rootsBar, mem_roots (Polynomial.map_ne_zero hP), IsRoot, eval_map, aeval_def]

theorem root_pow {P : (ZMod g)[X]} {x : Fbar g} (hx : aeval x P = 0) (i : ℕ) :
    aeval (x ^ g ^ i) P = 0 := by
  have h := aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) x P
  rw [hx, map_zero] at h
  rw [← h]
  congr 1
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]

theorem pow_eq_self_iff {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g}
    (hz : aeval z f = 0) (n : ℕ) :
    z ^ g ^ n = z ↔ f.natDegree ∣ n := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have has : Associated (minpoly (ZMod g) z) f :=
    (minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)
  have hdeg : (minpoly (ZMod g) z).natDegree = f.natDegree :=
    le_antisymm (natDegree_le_of_dvd has.dvd hf.ne_zero)
      (natDegree_le_of_dvd has.symm.dvd (minpoly.ne_zero hx))
  rw [← hdeg, CuspGL.minpoly_natDegree_dvd_iff_pow, Nat.card_zmod]

theorem pow_inj_lt {P : (ZMod g)[X]} (hP : Irreducible P) {x : Fbar g} (hx : aeval x P = 0)
    {i j : ℕ} (hij : i < j) (hj : j < P.natDegree) : x ^ g ^ i ≠ x ^ g ^ j := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have h₂ : (x ^ g ^ i) ^ g ^ (m + 1) = x ^ g ^ i := by
    rw [← pow_mul, ← pow_add, ← add_assoc, ← h]
  have hle := Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hP (root_pow hx i) _).mp h₂)
  omega

theorem rootsBar_eq {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g}
    (hz : aeval z f = 0) :
    rootsBar f = (Finset.range f.natDegree).val.map fun i => z ^ g ^ i := by
  have hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup := by
    refine Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup
    rw [← Finset.mem_def, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h₁ | h₁ | h₁
    · exact absurd h (pow_inj_lt hf hz h₁ hj)
    · exact h₁
    · exact absurd h.symm (pow_inj_lt hf hz h₁ hi)
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).mpr fun w hw => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hw
    exact (mem_rootsBar_iff hf.ne_zero).mpr (root_pow hz i)
  · have h := card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))
    simpa [rootsBar] using h

end GlobalTheory.GreenExists
