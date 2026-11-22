import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicHostFrobenius
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

/-! Decomposition at ramified host primes and unramifiedness over the real subfield. -/

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace WindowedLandauTheory.HC.Der

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem decomp_typeI : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi := by
  intro l hl hlN P _ _ σ hσ
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  show (H.gal σ).1.2 = 1
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with hε | hε
  · exact hε
  exfalso
  have hσX : σ H.sqd = -H.sqd := by rw [H.gal_sqd σ, hε]; simp
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have h16 : 2 ^ 4 ∣ H.QS * H.q :=
    ((pow_dvd_pow 2 (by have := H.two_le_e; omega)).trans H.tower_dvd).trans (dvd_mul_right _ _)
  obtain ⟨R, hR⟩ := h16
  obtain ⟨c, hc⟩ := hs
  have hc' : s ^ 2 + (H.d : ℤ) = 16 * ((R : ℤ) * c) := by rw [hc, hR]; push_cast; ring
  obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := by
    rcases Int.even_or_odd s with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exfalso
      have h0 : (H.d : ℤ) = 2 * (8 * ((R : ℤ) * c) - 2 * a ^ 2) := by linear_combination hc'
      generalize 8 * ((R : ℤ) * c) - 2 * a ^ 2 = z at h0
      have := H.hyp.2.2.2.1
      omega
    · exact ⟨a, rfl⟩
  have hlP : ((l : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 : (l : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (span {(l : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under] using h0
  have hlR : l ∣ 4 * R := by
    rcases hl.eq_two_or_odd with rfl | hlo
    · exact Dvd.intro (2 * R) (by ring)
    · have h0 : l ∣ 2 ^ 4 * R := hR ▸ hlN
      have hco : Nat.Coprime l (2 ^ 4) :=
        Nat.Coprime.pow_right 4 ((Nat.coprime_primes hl Nat.prime_two).mpr (by omega))
      exact (hco.dvd_of_dvd_mul_left h0).mul_left 4
  obtain ⟨k, hk⟩ := hlR
  obtain ⟨ω, hωc⟩ : ∃ ω : 𝓞 H.E, (ω : H.E) = (1 + H.sqd) / 2 :=
    ⟨⟨(1 + H.sqd) / 2, WindowedLandauTheory.FrobeniusOrbits.Decomp.omega_integral hd4 H.sqd_sq⟩, rfl⟩
  have hσω : σ • ω = 1 - ω := by
    apply NumberField.RingOfIntegers.ext
    show σ (ω : H.E) = 1 - (ω : H.E)
    rw [hωc, map_div₀, map_add, map_one, hσX, show σ (2 : H.E) = 2 from map_ofNat σ 2]
    ring
  have hprod : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) =
      -((l : ℤ) : 𝓞 H.E) * ((k * c : ℤ) : 𝓞 H.E) := by
    apply NumberField.RingOfIntegers.ext
    show ((ω : H.E) - ((a + 1 : ℤ) : H.E)) * ((ω : H.E) - (1 - ((a + 1 : ℤ) : H.E))) =
      -((l : ℤ) : H.E) * ((k * c : ℤ) : H.E)
    rw [hωc]
    push_cast
    have hcE : (((2 * a + 1) ^ 2 + (H.d : ℤ) : ℤ) : H.E) = ((16 * ((R : ℤ) * c) : ℤ) : H.E) := by
      rw [hc']
    push_cast at hcE
    have hkE : (4 * (R : H.E)) = (l : H.E) * (k : H.E) := by exact_mod_cast hk
    linear_combination (1 / 4 : H.E) * H.sqd_sq - (1 / 4 : H.E) * hcE - (c : H.E) * hkE
  have hprodP : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) ∈ P := by
    rw [hprod]
    exact Ideal.mul_mem_right _ _ (neg_mem hlP)
  have hσt : σ • ((a + 1 : ℤ) : 𝓞 H.E) = ((a + 1 : ℤ) : 𝓞 H.E) :=
    map_intCast (MulSemiringAction.toRingHom (H.E ≃ₐ[ℚ] H.E) (𝓞 H.E) σ) (a + 1)
  have hA : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P → ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    intro h
    have h1 := (WindowedLandauTheory.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, hσω, hσt] at h1
    have h2 : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) = -(1 - ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by ring
    rw [h2]
    exact neg_mem h1
  have hB : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P → ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    intro h
    have h1 := (WindowedLandauTheory.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, smul_sub, hσω, hσt, smul_one] at h1
    have h2 : ω - ((a + 1 : ℤ) : 𝓞 H.E) = -(1 - ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) := by ring
    rw [h2]
    exact neg_mem h1
  have hboth : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P ∧ ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h | h
    · exact ⟨h, hA h⟩
    · exact ⟨hB h, h⟩
  have hsP : ((2 * a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 := P.sub_mem hboth.2 hboth.1
    have h1 : ((2 * a + 1 : ℤ) : 𝓞 H.E) =
        ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) - (ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by
      push_cast
      ring
    rw [h1]
    exact h0
  have hls : (l : ℤ) ∣ 2 * a + 1 := by
    have h0 : (2 * a + 1 : ℤ) ∈ P.under ℤ := by simpa [Ideal.under] using hsP
    rw [← Ideal.over_def P (span {(l : ℤ)}), Ideal.mem_span_singleton] at h0
    exact h0
  have hlsd : (l : ℤ) ∣ (2 * a + 1) ^ 2 + H.d := by
    rw [hc]
    exact Dvd.dvd.mul_right (by exact_mod_cast hlN) c
  have hld : (l : ℤ) ∣ H.d := (dvd_add_right (dvd_pow hls two_ne_zero)).mp hlsd
  have hld' : l ∣ H.d := by exact_mod_cast hld
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hlN H.coprime_QSq_d) hld')

theorem decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P := by
  intro l hl hlN P _ _ hσ
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  by_cases hlq : l ∣ H.QS * H.q
  · have h3 := decomp_typeI H l hl hlq P H.conj hσ
    rw [h2] at h3
    exact φ.cc_notMem_Psi h3
  have hld : l = H.d := by
    rcases (Nat.Prime.dvd_mul hl).mp hlN with h | h
    · exact absurd h hlq
    · exact (Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI hPd : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hld]; infer_instance
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, -, hF⟩ := exists_over (emb H) H.d P
  have hcd : Nat.Coprime H.d (H.QS * H.q) := H.coprime_QSq_d.symm
  obtain ⟨uF, huF1, -⟩ := exists_unit_crt H.coprime_QSq_d H.d 1 hcd (Nat.coprime_one_left _)
  have hFrob : IsArithFrobAt ℤ (H.gal.symm (H.art uF)) P := by
    apply hF _ (tauN H.condN uF) ((gal_eq_art_iff H _ uF).mp (H.gal.apply_symm_apply _))
    apply tauN_frob H.condN H.d Q uF
    rw [ordCompl_d H]
    exact huF1
  obtain ⟨k, ρ, hρ, hconj⟩ := WindowedLandauTheory.FrobeniusOrbits.Decomp.stab_eq_inertia_mul H.d P _ H.conj hFrob hσ
  have hg : φ.cc = H.gal ρ * H.art uF ^ k := by
    rw [← h2, hconj, map_mul, map_pow, MulEquiv.apply_symm_apply]
  have hρ1 : (H.gal ρ).1.1 = 1 ∧ (H.gal ρ).2 = 1 := by
    rcases (inertia_d H P ρ).mp hρ with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  have hps := ps_d H uF huF1
  have h2N : 2 ^ (φ.e + 2) ∣ H.QS * H.q := tower_dvd_QSq H
  have hc2 : Nat.Coprime H.d (2 ^ (φ.e + 2)) := Nat.Coprime.coprime_dvd_right h2N hcd
  have hhv : φ.hH (H.art uF).2 = hcl φ.e (ZMod.unitOfCoprime H.d hc2) := by
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff]
    exact (huF1.of_dvd h2N).symm
  have hk2 : (H.art uF).2 ^ k = 1 := by
    have h0 := congrArg Prod.snd hg
    rw [Prod.snd_mul, Prod.pow_snd, hρ1.2, one_mul] at h0
    rw [← h0]
    rfl
  have hvk : ((ZMod.unitOfCoprime H.d hc2 ^ k : (ZMod (2 ^ (φ.e + 2)))ˣ) : HGrp φ.e) = 1 := by
    rw [QuotientGroup.mk_pow]
    show hcl φ.e (ZMod.unitOfCoprime H.d hc2) ^ k = 1
    rw [← hhv, ← map_pow, hk2, map_one]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_one_iff _ |>.mp hvk)
  have h16 : 16 ∣ 2 ^ (φ.e + 2) := by
    have h0 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h0]
    exact pow_dvd_pow 2 (by have := H.two_le_e; omega)
  have hfv : ZMod.castHom h16 (ZMod 16) ((ZMod.unitOfCoprime H.d hc2 : (ZMod (2 ^ (φ.e + 2)))ˣ) :
      ZMod (2 ^ (φ.e + 2))) = 7 := by
    rw [ZMod.coe_unitOfCoprime, map_natCast, ← ZMod.natCast_mod H.d 16, H.hyp.2.2.2.1]
    rfl
  have hpm : (7 : ZMod 16) ^ k = 1 ∨ (7 : ZMod 16) ^ k = -1 := by
    have h0 := congrArg (fun x : (ZMod (2 ^ (φ.e + 2)))ˣ =>
      ZMod.castHom h16 (ZMod 16) (x : ZMod (2 ^ (φ.e + 2)))) hn
    simp only [Units.val_pow_eq_pow_val, map_pow, hfv] at h0
    rcases Int.even_or_odd n with he | ho
    · left
      rw [he.neg_one_zpow, Units.val_one, map_one] at h0
      exact h0.symm
    · right
      rw [ho.neg_one_zpow, Units.val_neg, Units.val_one, map_neg, map_one] at h0
      exact h0.symm
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h0 := congrArg (fun g : φ.GG => g.1.1) hg
    simp only [Prod.fst_mul, Prod.pow_fst] at h0
    rw [hρ1.1, hps, one_mul, hj, ← two_mul, pow_mul, Int.units_sq, one_pow] at h0
    have h1 : (-1 : ℤˣ) = 1 := h0
    exact absurd (congrArg Units.val h1) (by norm_num)
  · have h7 : (7 : ZMod 16) ^ k = 7 := by
      rw [hj, pow_succ, pow_mul, (by decide : (7 : ZMod 16) ^ 2 = 1), one_pow, one_mul]
    rw [h7] at hpm
    revert hpm
    decide

theorem unramEF : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P := by
  intro P hP hP0 h
  obtain ⟨p, hp, hpl⟩ := exists_prime_liesOver P hP0
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  have hcs : H.conj H.sqd = -H.sqd := by
    rw [H.gal_sqd H.conj, h2]
    simp [Frame.cc, c0]
  by_cases hpd : p = H.d
  · haveI : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hpd]; exact hpl
    have h3 := (inertia_d H P H.conj).mp h
    rw [h2] at h3
    rcases h3 with h3 | h3
    · exact φ.cc_ne_one h3
    · have h4 := congrArg (fun g : φ.GG => ((g.1.1 : ℤˣ) : ℤ)) h3
      simp [Frame.cc, Frame.iod, c0] at h4
  · haveI := hpl
    have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
    exact WindowedLandauTheory.FrobeniusOrbits.Inertia.sqrt_fixed H.hyp.2.1 hd4 hp hpd P H.conj H.sqd_sq hcs h

end WindowedLandauTheory.HC.Der

end
