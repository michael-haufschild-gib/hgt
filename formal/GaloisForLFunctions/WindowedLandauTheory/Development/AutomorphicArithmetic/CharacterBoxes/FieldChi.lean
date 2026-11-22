import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.OrdAny
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.TwistAny
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.HostFieldData
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.ConstructHostAxioms

/-! Construct the CM host for a primitive Dirichlet character and identify its fixed field. -/

open WindowedLandauTheory.HC WindowedLandauTheory.FrobeniusOrbits UpperTheory.Top HostParam.Seam

theorem HostParam.Seam.conductor_divisor_bounds {M : ℕ} [NeZero M] {Q e b : ℕ} (hQ : Q ∣ Nat.lcm (2 ^ (e + 2)) M) (hb : 4 * M ≤ b) :
    (∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Q → 4 * l ≤ b) ∧ Q ≤ 4 * M * 2 ^ e := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 := hQ.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl h2 h => ?_, (Nat.le_of_dvd (by positivity) h1).trans (le_of_eq (by ring))⟩
  have h3 : l ∣ M := (hl.dvd_mul.1 (h.trans h1)).resolve_left fun h4 =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h4))
  have := Nat.le_of_dvd hM h3
  omega

theorem UpperTheory.Top.fieldChi :
    ∀ ψ : PChar, ∃ c e0 : ℕ, 1 ≤ c ∧ ∀ e ≥ e0, ∀ q d b : ℕ, HostHyp q d → q ≠ 3 → Nat.Coprime ψ.N (q * d) → 4 * ψ.N ≤ b →
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(d : ℤ)) p = 1) →
      ∃ (φ : Frame) (H : HostAx φ), φ.e = e ∧ φ.ord = c * 2 ^ e ∧ H.q = q ∧ H.d = d ∧ φ.o = (Level.cyc ψ).o ∧ FieldRows H.toHostRaw b ∧
        H.QS ∣ Nat.lcm (2 ^ (e + 2)) ψ.N ∧ H.QS ≤ 4 * ψ.N * φ.ord ∧
        H.KeptInXp (Level.cyc ψ).KEPT ∧ H.ExceptionalCharacterKept (Level.cyc ψ).KEPT (Level.cyc ψ).psK ∧
        KerChi ψ H.toHostRaw ∧ TwistForm ψ H.toHostRaw := by
  intro ψ
  obtain ⟨c, e1, hc1, -, hord⟩ := ordAny ψ.N (Subgroup.zpowers ψ.χ)
  refine ⟨c, max e1 (max 2 (max (4 * ψ.N) (64 * Nat.card (Subgroup.zpowers ψ.χ)))), hc1,
    fun e he q d b hH hq3 hcop hb hsplit => ?_⟩
  simp only [ge_iff_le, max_le_iff] at he
  obtain ⟨he1, he2, heN, heK⟩ := he
  have hNpos : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ ψ.N → jacobiSym (-(d : ℤ)) l = 1 := by
    intro l hl hl2 hlN
    have := Nat.le_of_dvd hNpos hlN
    exact hsplit l hl hl2 (by omega)
  have hQdvd : (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hcop he2 hs).QS ∣ Nat.lcm (2 ^ (e + 2)) ψ.N :=
    AnyGrp.QS_dvd _ e
  obtain ⟨hsmall, hQle⟩ := conductor_divisor_bounds hQdvd hb
  have h2e : 2 ^ e ≤ (AnyGrp.frame (Subgroup.zpowers ψ.χ) e).ord :=
    Frame.two_pow_le_ord (AnyGrp.frame (Subgroup.zpowers ψ.χ) e)
  have h4M : 4 * ψ.N ≤ 2 ^ e := by
    have : e < 2 ^ e := Nat.lt_two_pow_self
    omega
  have hopow : (AnyGrp.frame (Subgroup.zpowers ψ.χ) e).o ^ 64 ≤ 2 ^ (AnyGrp.frame (Subgroup.zpowers ψ.χ) e).e := by
    rw [AnyGrp.o_eq]
    show Nat.card (Subgroup.zpowers ψ.χ) ^ 64 ≤ 2 ^ e
    calc Nat.card (Subgroup.zpowers ψ.χ) ^ 64 ≤ (2 ^ Nat.card (Subgroup.zpowers ψ.χ)) ^ 64 :=
          Nat.pow_le_pow_left Nat.lt_two_pow_self.le 64
      _ = 2 ^ (64 * Nat.card (Subgroup.zpowers ψ.χ)) := by ring
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) heK
  refine ⟨AnyGrp.frame (Subgroup.zpowers ψ.χ) e,
    HostAx.ofRaw (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hcop he2 hs), rfl, hord e he1, rfl, rfl,
    AnyGrp.o_eq _ e, ?_, hQdvd, ?_, AnyGrp.keptInXp _ e hH hcop he2 hs, AnyGrp.exceptional_character_condition _ e hH hcop he2 hs,
    kerChiAny ψ e q d hH hcop he2 hs, twistAny ψ e q d hH hcop he2 hs⟩
  · exact ⟨AnyGrp.psQ _ e hH hcop he2 hs, AnyGrp.exists_sqq _ e hH hcop he2 hs, AnyGrp.exact _ e hH hcop he2 hs,
      AnyGrp.QS_le _ e h4M, hopow, hq3, hsplit, hsmall⟩
  · exact hQle.trans (Nat.mul_le_mul_left _ h2e)

/-- The Artin kernel identifies the host as the designated cyclotomic subfield. -/
theorem UpperTheory.Top.isChiField :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ), KerChi ψ H → IsChiField ψ φ.e H.q H.d H.E := by
  intro ψ φ H h
  obtain ⟨hψ, hart⟩ := h
  have hyp := H.hyp
  unfold WindowedLandauTheory.FrobeniusOrbits.HostHyp at hyp
  have hq := hyp.1.pos
  have hd := hyp.2.1.pos
  have hQS := H.QS_pos
  have hNpos : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos hQS hq) hd
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩
  have hζ := H.cycZeta_prim
  refine ⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩
  · exact dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  · exact dvd_mul_left _ _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d) := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime (H.QS * H.q * H.d) := (hζ.pow_iff_coprime hNpos a).mp hprim
    have hcop' : a.Coprime H.condN := hcop
    rw [← hart a hcop']
    set u := ZMod.unitOfCoprime a hcop' with hu
    have hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val := by
      rw [hτ]
      have hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d) := by
        rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hv]
      conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hspec := H.art_spec u τ hτu
    constructor
    · intro hfix
      have hg : H.gal.symm (H.art u) = 1 := by
        ext x
        apply H.cycEmb.injective
        exact (hspec x).trans (hfix x)
      have h1 := congrArg H.gal hg
      rw [MulEquiv.apply_symm_apply, map_one] at h1
      exact h1
    · intro h1 x
      have h2 := hspec x
      rw [h1, map_one] at h2
      rw [← h2]
      rfl
