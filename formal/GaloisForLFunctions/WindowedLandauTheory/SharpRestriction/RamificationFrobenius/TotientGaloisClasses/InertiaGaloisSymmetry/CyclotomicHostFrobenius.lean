import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicSignAction

/-! The unramified Artin signs and the inertia at the quadratic discriminant. -/

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace WindowedLandauTheory.HC.Der

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

theorem val_one_modEq (M N : ℕ) [NeZero N] (h : M ∣ N) : (((1 : (ZMod N)ˣ) : ZMod N)).val ≡ 1 [MOD M] := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod]
  exact (Nat.mod_modEq 1 N).of_dvd h

variable {φ : Frame} (H : HostRaw φ)

theorem frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
  intro p _ hpN P _ _
  have hp : p.Prime := Fact.out
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hcop : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hfact : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, Nat.div_one]
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, hF⟩ := exists_over (emb H) p P
  have hval : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p →
      (u : ZMod H.condN).val ≡ p [MOD ordCompl[p] H.condN] := by
    intro u hu
    rw [hfact, hu, ZMod.val_natCast]
    exact Nat.mod_modEq p _
  have hfu : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p → ∀ σ : H.E ≃ₐ[ℚ] H.E,
      H.gal σ = H.art u → IsArithFrobAt ℤ σ P := fun u hu σ hσ =>
    hF σ (tauN H.condN u) ((gal_eq_art_iff H σ u).mp hσ) (tauN_frob H.condN p Q u (hval u hu))
  have hinert : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
    intro σ
    constructor
    · intro h
      obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
      obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
      have h1 := (tauN_inertia_iff H.condN p Q w).mp hτ2
      rw [hfact] at h1
      have hw1 : w = 1 := by
        apply Units.ext
        rw [Units.val_one, ← ZMod.natCast_zmod_val (w : ZMod H.condN), ← Nat.cast_one,
          ZMod.natCast_eq_natCast_iff]
        exact h1
      subst hw1
      apply AlgEquiv.ext
      intro x
      apply (emb H).toRingHom.injective
      show emb H (σ x) = emb H x
      rw [hτ1 x, map_one, AlgEquiv.one_apply]
    · rintro rfl x
      simp
  have hiff : ∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
      (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u) := by
    intro σ u hu
    constructor
    · intro hσ
      have hσ' := hfu u hu (H.gal.symm (H.art u)) (H.gal.apply_symm_apply _)
      have h1 := (hinert _).mp ((frob_iff_inertia P _ σ hσ').mp hσ)
      rw [mul_inv_eq_one] at h1
      rw [h1, MulEquiv.apply_symm_apply]
    · exact hfu u hu σ
  have hu0 : ((ZMod.unitOfCoprime p hcop : (ZMod H.condN)ˣ) : ZMod H.condN) = p :=
    ZMod.coe_unitOfCoprime _ _
  refine ⟨⟨H.gal.symm (H.art (ZMod.unitOfCoprime p hcop)),
    hfu _ hu0 _ (H.gal.apply_symm_apply _)⟩, hiff, fun σ hσ => ?_, hinert⟩
  have hg := (hiff σ _ hu0).mp hσ
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN (H.two_dvd_QS.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    unfold HostRaw.psAt
    rw [dif_pos hcop]
  · rw [hg, art_ch H, hu0, ZMod.val_natCast, jacobi_neg_recip hd4 hpodd,
      jacobiSym.mod_left ((p % H.condN : ℕ) : ℤ), jacobiSym.mod_left (p : ℤ)]
    congr 1
    push_cast
    exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
  · have h2 : 2 ^ (φ.e + 2) ∣ H.condN := (tower_dvd_QSq H).trans (QSq_dvd H)
    have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    refine ⟨ZMod.unitOfCoprime p hc2, ZMod.coe_unitOfCoprime _ _, ?_⟩
    rw [hg]
    apply H.art_h
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq p H.condN).of_dvd h2).symm

theorem exists_art_iod : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hd1 : 1 ≤ H.d := H.hyp.2.1.one_lt.le
  have hcop : Nat.Coprime (H.d - 1) H.d :=
    ((Nat.Prime.coprime_iff_not_dvd H.hyp.2.1).mpr
      (Nat.not_dvd_of_pos_of_lt (by have := H.hyp.2.1.two_le; omega) (by omega))).symm
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt H.coprime_QSq_d 1 (H.d - 1) (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hdv : H.d ∣ (u : ZMod H.condN).val + 1 := by
    have h0 : ((u : ZMod H.condN).val + 1) % H.d = (H.d - 1 + 1) % H.d := hu2.add_right 1
    rw [Nat.sub_add_cancel hd1, Nat.mod_self] at h0
    exact Nat.dvd_of_mod_eq_zero h0
  have hv : ((u : ZMod H.condN).val : ℤ) % (H.d : ℤ) = (-1 : ℤ) % (H.d : ℤ) := by
    have h0 : (H.d : ℤ) ∣ ((u : ZMod H.condN).val : ℤ) + 1 := by exact_mod_cast hdv
    have h1 : Int.ModEq (H.d : ℤ) ((u : ZMod H.condN).val : ℤ) (-1) := by
      apply Int.modEq_iff_dvd.mpr
      rw [show (-1 : ℤ) - ((u : ZMod H.condN).val : ℤ) = -(((u : ZMod H.condN).val : ℤ) + 1) by ring]
      exact h0.neg_right
    exact h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = -1 := by
    rw [jacobiSym.mod_left, hv, ← jacobiSym.mod_left,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hd4]
  rcases H.art_d u hu1 with h | h
  · exfalso
    have h0 := art_ch H u
    rw [h, hJ] at h0
    norm_num at h0
  · exact h

theorem inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod) := by
  intro P _ _ σ
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, -⟩ := exists_over (emb H) H.d P
  constructor
  · intro h
    obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
    obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
    have h1 := (tauN_inertia_iff H.condN H.d Q w).mp hτ2
    rw [ordCompl_d H] at h1
    have hg : H.gal σ = H.art w := (gal_eq_art_iff H σ w).mpr hτ1
    rw [hg]
    exact H.art_d w h1
  · intro h
    have key : ∀ w : (ZMod H.condN)ˣ, (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] →
        H.gal σ = H.art w → ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
      intro w hw1 hg
      apply (hI σ).mpr
      refine ⟨tauN H.condN w, (gal_eq_art_iff H σ w).mp hg, ?_⟩
      apply (tauN_inertia_iff H.condN H.d Q w).mpr
      rw [ordCompl_d H]
      exact hw1
    rcases h with h | h
    · exact key 1 (val_one_modEq _ _ (QSq_dvd H)) (h.trans (map_one _).symm)
    · obtain ⟨u, hu1, hu2⟩ := exists_art_iod H
      exact key u hu1 (h.trans hu2.symm)

end WindowedLandauTheory.HC.Der

end
