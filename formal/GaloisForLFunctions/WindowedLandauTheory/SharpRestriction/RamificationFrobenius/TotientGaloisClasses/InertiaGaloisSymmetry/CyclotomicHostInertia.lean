import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicPrimeResidues

/-! Transfer cyclotomic inertia and Frobenius congruences to the host field. -/

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace WindowedLandauTheory.HC.Der

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  have := cyc_isGalois H.condN
  obtain ⟨Q, _, _, h1, -⟩ := exists_over (emb H) l P
  rw [h1]
  constructor
  · rintro ⟨τ, h2, h3⟩
    obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
    exact ⟨u, (tauN_inertia_iff _ l Q u).mp h3, (gal_eq_art_iff H σ u).mpr h2⟩
  · rintro ⟨u, h2, h3⟩
    exact ⟨_, (gal_eq_art_iff H σ u).mp h3, (tauN_inertia_iff _ l Q u).mpr h2⟩

private lemma lift_lemma' (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ Q : Ideal (𝓞 (Cond.Cyc H.condN)), Q.IsPrime ∧ Q.LiesOver (span {(l : ℤ)}) ∧
      Q.comap (RingOfIntegers.mapRingHom (emb H).toRingHom) = P := by
  classical
  letI : Algebra (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := (RingOfIntegers.mapRingHom (emb H).toRingHom).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩
  have hinj : Function.Injective (RingOfIntegers.mapRingHom (emb H).toRingHom) := by
    intro x y hxy
    apply RingOfIntegers.ext
    have h1 := congrArg (fun z : 𝓞 (Cond.Cyc H.condN) => (z : Cond.Cyc H.condN)) hxy
    exact (emb H).toRingHom.injective h1
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 (Cond.Cyc H.condN))) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hinj (hx.trans (map_zero _).symm)
    rw [hx0]
    exact P.zero_mem)
  refine ⟨Q, hQp, ⟨?_⟩, hQ⟩
  have hP : span {(l : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [hP, ← hQ]
  show Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.comap (algebraMap (𝓞 H.E) (𝓞 (Cond.Cyc H.condN))) Q) =
    Ideal.comap (algebraMap ℤ (𝓞 (Cond.Cyc H.condN))) Q
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext_int _ _

theorem frob_of_modEq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN])
    (h : H.gal σ = H.art u) : IsArithFrobAt ℤ σ P := by
  obtain ⟨Q, hQp, hQl, hQ⟩ := lift_lemma' H l P
  haveI := hQp
  haveI := hQl
  have hτ := tauN_frob H.condN l Q u hu
  have hact : ∀ x : 𝓞 H.E, RingOfIntegers.mapRingHom (emb H).toRingHom (σ • x) =
      tauN H.condN u • RingOfIntegers.mapRingHom (emb H).toRingHom x := by
    intro x
    apply RingOfIntegers.ext
    exact (gal_eq_art_iff H σ u).1 h x
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ) := by
    rw [← Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)}), ← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})]
  unfold IsArithFrobAt at hτ ⊢
  intro x
  rw [hcard, ← hQ, Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply] at hτ ⊢
  rw [map_sub, map_pow, hact]
  exact hτ _

theorem exists_frob (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (F : H.E ≃ₐ[ℚ] H.E) (w : (ZMod H.condN)ˣ), IsArithFrobAt ℤ F P ∧
      (w : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal F = H.art w := by
  have hl : l.Prime := Fact.out
  have hcop : l.Coprime (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl (NeZero.ne _)
  obtain ⟨w, hw⟩ := exists_unit_modEq (Nat.ordCompl_dvd H.condN l) l hcop
  exact ⟨H.gal.symm (H.art w), w, frob_of_modEq H l P _ w hw (by simp), hw, by simp⟩

theorem frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  refine ⟨fun hσ => ?_, fun ⟨u, h1, h2⟩ => frob_of_modEq H l P σ u h1 h2⟩
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [frob_iff_inertia P F σ hF, inertia H l P, map_mul, map_inv, hFw] at hσ
  obtain ⟨u, hu, h1⟩ := hσ
  refine ⟨u * w, ?_, by rw [map_mul, ← h1, inv_mul_cancel_right]⟩
  rw [val_modEq_one_iff hM] at hu
  rw [val_modEq_iff hM] at hw ⊢
  rw [map_mul, hu, one_mul, hw]

theorem decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [val_modEq_iff hM] at hw
  constructor
  · intro hσ
    obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul l P F σ hF hσ
    obtain ⟨u, hu, h1⟩ := (inertia H l P ρ).mp hρ
    refine ⟨u * w ^ k, k, ?_, by rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]⟩
    rw [val_modEq_one_iff hM] at hu
    rw [val_modEq_iff hM, map_mul, hu, one_mul, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow]
  · rintro ⟨u, k, hu, h1⟩
    have h2 : ∀ x : 𝓞 H.E, (σ * (F ^ k)⁻¹) • x - x ∈ P := by
      rw [inertia H l P]
      refine ⟨u * (w ^ k)⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]⟩
      rw [val_modEq_iff hM] at hu
      have h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k) :=
        Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])
      rw [val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]
    have h4 := Subgroup.mul_mem _ (Decomp.mem_stab_of _ P (smul_mem_of_inertia _ P h2))
      (Subgroup.pow_mem _ hF.mem_stabilizer k)
    rwa [inv_mul_cancel_right] at h4

end WindowedLandauTheory.HC.Der

end
