import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CharacterFrame
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicPrimeResidues
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.RealSubfieldLeCompositum

/-! The least level supporting the character quotient and the dyadic tower. -/

noncomputable section

namespace WindowedLandauTheory.HC

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

theorem unitsMap_unitOfCoprime {M N : ℕ} (h : M ∣ N) (a : ℕ) (ha : Nat.Coprime a N) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a ha) = ZMod.unitOfCoprime a (ha.coprime_dvd_right h) := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

private theorem unitsMap_val_modEq {M N : ℕ} [NeZero M] [NeZero N]
    (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M).val [MOD M] := by
  apply (Der.val_modEq_iff h u _).mpr
  rw [ZMod.natCast_zmod_val]

namespace AnyGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

/-- The common kernel of the characters in the subgroup. -/
def ann : Subgroup (ZMod M)ˣ := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).symm (OrderDual.toDual Ξ)

theorem mem_ann (u : (ZMod M)ˣ) : u ∈ ann Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  simp [ann]

theorem mem_iff (χ : DirichletCharacter ℂ M) : χ ∈ Ξ ↔ ∀ u ∈ ann Ξ, χ u = 1 := by
  have h1 := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).apply_symm_apply (OrderDual.toDual Ξ)
  have h2 : χ ∈ Ξ ↔ χ ∈ OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ) (ann Ξ)) := by
    simp only [ann, h1, OrderDual.ofDual_toDual]
  rw [h2]
  generalize ann Ξ = S
  simp

abbrev B : Type := (ZMod M)ˣ ⧸ ann Ξ

theorem card_B : Nat.card (B Ξ) = Nat.card Ξ := by
  rw [← MulChar.card_subgroupOrderIsoSubgroupMulChar (R := ℂ), ann, OrderIso.apply_symm_apply]
  rfl

instance neZero_lcm : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩

def xiW : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* B Ξ := (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem xiW_surj : Function.Surjective (xiW Ξ e) := by
  intro b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ann Ξ) b
  obtain ⟨c, rfl⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_right (2 ^ (e + 2)) M) a
  exact ⟨c, rfl⟩

def Good (m : ℕ) : Prop := m ∣ Nat.lcm (2 ^ (e + 2)) M ∧ 2 ^ (e + 2) ∣ m ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ, (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD m] → xiW Ξ e u = 1

theorem exists_good : ∃ m, Good Ξ e m := by
  refine ⟨Nat.lcm (2 ^ (e + 2)) M, dvd_rfl, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have h1 : ((u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val : ZMod (Nat.lcm (2 ^ (e + 2)) M)) =
      ((1 : ℕ) : ZMod (Nat.lcm (2 ^ (e + 2)) M)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : u = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, map_one]

open Classical in

/-- The smallest quotient level through which the characters and the dyadic projection factor. -/
def QS : ℕ := Nat.find (exists_good Ξ e)

open Classical in
theorem good_QS : Good Ξ e (QS Ξ e) := Nat.find_spec (exists_good Ξ e)

open Classical in
theorem not_good {m : ℕ} (h : m < QS Ξ e) : ¬ Good Ξ e m := Nat.find_min (exists_good Ξ e) h

theorem QS_dvd : QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (good_QS Ξ e).1

theorem QS_dvd_mul : QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd Ξ e).trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))

theorem QS_pos : 0 < QS Ξ e := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := QS_dvd Ξ e
  rw [h, zero_dvd_iff] at h1
  exact (NeZero.ne _) h1

instance neZero_QS : NeZero (QS Ξ e) := ⟨(QS_pos Ξ e).ne'⟩

def xi : (ZMod (QS Ξ e))ˣ →* B Ξ :=
  (ZMod.unitsMap (QS_dvd Ξ e)).liftOfSurjective (ZMod.unitsMap_surjective _)
    ⟨xiW Ξ e, fun u hu => (good_QS Ξ e).2.2 u ((Der.val_modEq_one_iff _ u).mpr hu)⟩

theorem xi_unitsMap (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) : xi Ξ e (ZMod.unitsMap (QS_dvd Ξ e) u) = xiW Ξ e u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem xi_surj : Function.Surjective (xi Ξ e) := by
  intro b
  obtain ⟨u, rfl⟩ := xiW_surj Ξ e b
  exact ⟨_, xi_unitsMap Ξ e u⟩

theorem dvd_of_dvd_QS {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ QS Ξ e) : l ∣ M := by
  rcases (Nat.Prime.dvd_mul hl).mp (h.trans (QS_dvd_mul Ξ e)) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1)) h2
  · exact h1

def thetaB (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : B Ξ →* ℂˣ :=
  QuotientGroup.lift (ann Ξ) χ.toUnitHom fun u hu =>
    Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_ann Ξ u).mp hu χ hχ))

def data : ModData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e

abbrev frame : Frame := (data Ξ e).frame

theorem frame_e : (frame Ξ e).e = e := rfl

theorem o_eq : (frame Ξ e).o = Nat.card Ξ := by
  show (data Ξ e).frame.o = _
  rw [ModData.o_eq]
  show Nat.card (xi Ξ e).range = _
  rw [MonoidHom.range_eq_top.mpr (xi_surj Ξ e), Subgroup.card_top]
  exact card_B Ξ

theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e).ord := (frame Ξ e).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2

/-- Removing a prime factor changes either the character quotient or the dyadic projection. -/
theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

end AnyGrp

end WindowedLandauTheory.HC
