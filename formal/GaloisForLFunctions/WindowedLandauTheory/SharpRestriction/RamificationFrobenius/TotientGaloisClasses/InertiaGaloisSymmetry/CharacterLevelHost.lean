import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CharacterConductor
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CharacterHost
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

/-! The host at the least level retains the designated primitive Dirichlet characters. -/

noncomputable section

namespace WindowedLandauTheory.HC

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

theorem HostRaw.art_eq_of_prim_eq {φ : Frame} (H : HostRaw φ) {θ θ' : φ.Char} (h : H.prim θ = H.prim θ')
    (u : (ZMod H.condN)ˣ) : θ (H.art u) = θ' (H.art u) := by
  have h1 := (H.isPrimOf_prim θ).2 _ (ZMod.val_coe_unit_coprime u)
  have h2 := ((H.isPrimOf_iff θ' _).mpr h).2 _ (ZMod.val_coe_unit_coprime u)
  have h3 := h1.symm.trans h2
  rw [HostRaw.dirAt, HostRaw.dirAt, ZMod.natCast_zmod_val, H.dir_unit, H.dir_unit] at h3
  exact Units.ext h3

namespace AnyGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def thetaA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).MA →* ℂˣ := (thetaB Ξ χ hχ).comp (data Ξ e).xiA

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e).Char :=
  (thetaA Ξ e χ hχ).comp (MonoidHom.snd G0 (frame Ξ e).MA * (data Ξ e).w.comp (frame Ξ e).chQ)

theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e χ hχ ∈ (frame Ξ e).Xp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have h1 : (frame Ξ e).iota s * (data Ξ e).w 1 = (frame Ξ e).iota s :=
      (congrArg ((frame Ξ e).iota s * ·) (map_one (data Ξ e).w)).trans (mul_one _)
    exact (congrArg (thetaA Ξ e χ hχ) h1).trans
      ((congrArg (thetaB Ξ χ hχ) (((data Ξ e).mem_A0_iff_xiA_eq_one s).mp hs)).trans (map_one _))
  · exact (congrArg (thetaA Ξ e χ hχ) ((one_mul _).trans (map_one (data Ξ e).w))).trans (map_one _)

theorem thetaA_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) :=
  congrArg (thetaB Ξ χ hχ) (((data Ξ e).xiA_toA _).trans (xi_unitsMap Ξ e u))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

include hH hc in
theorem coprime_QS : Nat.Coprime (QS Ξ e) (q * d) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  have h2 : Nat.Coprime 2 (q * d) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ h2) hc)

def host : HostRaw (frame Ξ e) :=
  (data Ξ e).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem host_q : (host Ξ e hH hc he hs).q = q := rfl
theorem host_d : (host Ξ e hH hc he hs).d = d := rfl
theorem host_QS : (host Ξ e hH hc he hs).QS = QS Ξ e := rfl

theorem psQ : (host Ξ e hH hc he hs).PsQ := by
  unfold host
  apply ModData.psQ

theorem exact : (host Ξ e hH hc he hs).Exact := by
  unfold host
  apply ModData.exact
  intro l hl hd
  exact exact_data Ξ e (by omega) l hl hd

theorem exists_sqq : ∃ s : (host Ξ e hH hc he hs).E, s ^ 2 = -((host Ξ e hH hc he hs).q : (host Ξ e hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hH hc he hs).E,
      σ s = (((((host Ξ e hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hH hc he hs).E) * s := by
  unfold host
  apply ModData.exists_sqq

theorem theta_art (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (u : (ZMod (QS Ξ e * q * d))ˣ) :
    theta Ξ e χ hχ ((host Ξ e hH hc he hs).art u) =
      thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) :=
  congrArg (thetaA Ξ e χ hχ) ((mul_assoc _ _ _).trans
    ((congrArg (_ * ·) ((data Ξ e).w_mul_self ((data Ξ e).art hH u).1.1)).trans (mul_one _)))

theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hH hc he hs).prim (theta Ξ e χ hχ) := by
  set H := host Ξ e hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := thetaA_toA Ξ e χ hχ (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  exact (theta_art Ξ e hH hc he hs χ hχ _).trans ((congrArg (fun v => thetaA Ξ e χ hχ ((data Ξ e).toA v))
    (unitsMap_unitOfCoprime ((data Ξ e).m_dvd q d) a haN)).trans h1)

theorem keptInXp : (host Ξ e hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := fun ψ hψ => by
  obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
  exact ⟨_, theta_mem Ξ e χ hχ, (HostRaw.isPrimOf_iff _ _ _).mpr (prim_theta Ξ e hH hc he hs χ hχ)⟩

theorem exceptional_character_condition : (host Ξ e hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hH hc he hs χ hχ] at h1
  have hco := coprime_QS Ξ e hH hc
  obtain ⟨u, hu, hsign⟩ := (data Ξ e).exists_art_ps_neg_one hH hco
  have h2 := (theta_art Ξ e hH hc he hs χ hχ u).symm.trans (HostRaw.art_eq_of_prim_eq _ h1 u)
  have h3 : thetaA Ξ e χ hχ ((data Ξ e).toA (ZMod.unitsMap ((data Ξ e).m_dvd q d) u)) = 1 := by
    rw [hu, map_one, map_one]
  have h4 : ((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) = -1 := hsign
  have h5 : (1 : ℂ) = (((((data Ξ e).art hH u).1.1 : ℤˣ) : ℤ) : ℂ) := congrArg Units.val (h3.symm.trans h2)
  rw [h4] at h5
  norm_num at h5

theorem o_eq_level : (frame Ξ e).o = (Level.ofSub Ξ).o := by
  rw [o_eq]
  rfl

end Host

end AnyGrp

end WindowedLandauTheory.HC
