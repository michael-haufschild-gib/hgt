import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CharacterFrame
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CharacterFixedField
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CyclotomicSignAction

/-! Adjoin the two quadratic signs to the frame via the Chinese remainder theorem. -/

noncomputable section

namespace WindowedLandauTheory.HC

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

namespace D7

variable {q d : ℕ}

private theorem exists_sign {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ) :
    ∃ b : ℕ, Nat.Coprime b p ∧ jacobiSym (b : ℤ) p = (s : ℤ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, Nat.coprime_one_left _, by simp [jacobiSym.one_left]⟩
  · have h1 : 1 ≤ p := hp.one_lt.le
    refine ⟨p - 1, ?_, ?_⟩
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (by have := hp.two_le; omega) h
      omega
    · have hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) * 1 := by push_cast [h1]; ring
      rw [hcast, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left (-1) p,
        jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hp4]
      simp

private theorem cop_qd : Nat.Coprime q d := by
  rw [Nat.coprime_primes hH.1 hH.2.1]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega
private theorem q4 : q % 4 = 3 := by
  have := hH.2.2.1
  omega
private theorem d4 : d % 4 = 3 := by
  have := hH.2.2.2.1
  omega

end D7

namespace ModData

private theorem exists_unit_crt_three {a b c : ℕ} [NeZero (a * b * c)]
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c)
    (x y z : ℕ) (hx : x.Coprime a) (hy : y.Coprime b) (hz : z.Coprime c) :
    ∃ u : (ZMod (a * b * c))ˣ, (u : ZMod (a * b * c)).val ≡ x [MOD a] ∧
      (u : ZMod (a * b * c)).val ≡ y [MOD b] ∧ (u : ZMod (a * b * c)).val ≡ z [MOD c] := by
  haveI : NeZero (a * b) := ⟨left_ne_zero_of_mul (NeZero.ne (a * b * c))⟩
  obtain ⟨v, hva, hvb⟩ := Der.exists_unit_crt hab x y hx hy
  obtain ⟨u, huv, huc⟩ := Der.exists_unit_crt (hac.mul hbc) (v : ZMod (a * b)).val z
    (ZMod.val_coe_unit_coprime v) hz
  exact ⟨u, (huv.of_mul_right b).trans hva, (huv.of_mul_left a).trans hvb, huc⟩

variable (D : ModData)

def w : ℤˣ →* D.frame.MA := D.toA.comp (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom)

theorem w_neg_one : D.w (-1) = D.toA (-1) := by
  show D.toA (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom (-1)) = _
  congr 1
  ext
  simp

theorem w_mul_self (s : ℤˣ) : D.w s * D.w s = 1 := by
  rw [← map_mul, Int.units_mul_self, map_one]

theorem hH_w (s : ℤˣ) : D.frame.hH (D.w s) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, map_one]
  · rw [w_neg_one, hH_toA, cl_neg_one]
    rfl

section Host

variable {q d : ℕ} (hH : HostHyp q d)

theorem m_dvd (q d : ℕ) : D.m ∣ D.m * q * d := ⟨q * d, by ring⟩
theorem q_dvd (q d : ℕ) : q ∣ D.m * q * d := ⟨D.m * d, by ring⟩
theorem d_dvd (q d : ℕ) : d ∣ D.m * q * d := ⟨D.m * q, by ring⟩

include hH in
theorem neZeroN : NeZero (D.m * q * d) := by
  have h1 := hH.1.pos
  have h2 := hH.2.1.pos
  have h3 := D.m_pos
  exact ⟨by positivity⟩

def art : (ZMod (D.m * q * d))ˣ →* D.frame.GG :=
  ((D7.sgnN hH.1 (D.q_dvd q d)).prod (D7.sgnN hH.2.1 (D.d_dvd q d))).prod
    (D.toA.comp (ZMod.unitsMap (D.m_dvd q d)) * D.w.comp (D7.sgnN hH.1 (D.q_dvd q d)))

theorem art_snd (u : (ZMod (D.m * q * d))ˣ) :
    (D.art hH u).2 = D.toA (ZMod.unitsMap (D.m_dvd q d) u) * D.w (D.art hH u).1.1 := rfl

theorem art_ps (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.1 (D.q_dvd q d) u

theorem art_ch (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.2.1 (D.d_dvd q d) u

theorem art_ps_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD q])
    (hy : jacobiSym (y : ℤ) q = 1) : (D.art hH u).1.1 = 1 := by
  have h := D.art_ps hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q = jacobiSym (y : ℤ) q := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % q = y % q from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_ch_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD d])
    (hy : jacobiSym (y : ℤ) d = 1) : (D.art hH u).1.2 = 1 := by
  have h := D.art_ch hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d = jacobiSym (y : ℤ) d := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % d = y % d from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_snd_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    (D.art hH u).2 = D.w (D.art hH u).1.1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [art_snd, h1, map_one, one_mul]

theorem art_eq_one (u : (ZMod (D.m * q * d))ˣ) (h1 : (D.art hH u).1.1 = 1) (h2 : (D.art hH u).1.2 = 1)
    (h3 : D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1) : D.art hH u = 1 := by
  refine Prod.ext (Prod.ext h1 h2) ?_
  rw [art_snd, h1, map_one, mul_one]
  exact (D.toA_eq_one_iff _).mpr h3

include hH in
theorem eta_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [h1, map_one]

variable (hc : Nat.Coprime D.m (q * d))

include hc in
theorem art_surj : Function.Surjective (D.art hH) := by
  have := D.neZeroN hH
  intro g
  obtain ⟨v, hv⟩ := D.toA_surj (g.2 * D.w g.1.1)
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) g.1.1
  obtain ⟨z, cz, hz⟩ := D7.exists_sign hH.2.1 (D7.d4 hH) g.1.2
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_crt_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val y z (ZMod.val_coe_unit_coprime v) cy cz
  have h4 : (D.art hH u).1.1 = g.1.1 := Units.ext (by rw [art_ps, jacobi_congr h2, hy])
  refine ⟨u, Prod.ext (Prod.ext h4 (Units.ext ?_)) ?_⟩
  · rw [art_ch, jacobi_congr h3, hz]
  · rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, hv, h4, mul_assoc, w_mul_self, mul_one]

theorem exists_art_ps_neg_one :
    ∃ u : (ZMod (D.m * q * d))ˣ, ZMod.unitsMap (D.m_dvd q d) u = 1 ∧
      (((D.art hH u).1.1 : ℤˣ) : ℤ) = -1 := by
  haveI := D.neZeroN hH
  obtain ⟨y, hy, hj⟩ := D7.exists_sign hH.1 (D7.q4 hH) (-1)
  obtain ⟨u, hm, hq, -⟩ := exists_unit_crt_three hc.coprime_mul_right_right
    hc.coprime_mul_left_right (D7.cop_qd hH) 1 y 1 (Nat.coprime_one_left _) hy
    (Nat.coprime_one_left _)
  refine ⟨u, (Der.val_modEq_one_iff (D.m_dvd q d) u).mp hm, ?_⟩
  exact (D.art_ps hH u).trans ((jacobi_congr hq).trans hj)

variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)

def charData : CharData D.frame where
  q := q
  d := d
  QS := D.m
  hyp := hH
  two_le_e := he
  QS_pos := D.m_pos
  tower_dvd := D.tower
  QS_coprime := hc
  QS_split := hs
  art := D.art hH
  art_surj := D.art_surj hH hc
  art_neg_one := by
    have h1 : (D.art hH (-1)).1.1 = -1 := D7.sgnN_neg_one hH.1 (D7.q4 hH) _
    refine Prod.ext (Prod.ext h1 (D7.sgnN_neg_one hH.2.1 (D7.d4 hH) _)) ?_
    rw [art_snd, D7.unitsMap_neg_one, h1, ← w_neg_one]
    exact D.w_mul_self _
  art_h := fun u v hv => by
    have := D.neZeroN hH
    rw [art_snd, map_mul, hH_w, mul_one, hH_toA, cl_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact congrArg (hcl D.e) (Units.ext ((D7.unitsMap_val _ u).trans hv.symm))
  art_d := fun u hu => by
    have h1 := D.art_ps_one hH u (hu.of_dvd (dvd_mul_left _ _)) (by simp)
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    rw [h1, map_one] at h2
    rcases Int.units_eq_one_or (D.art hH u).1.2 with h3 | h3
    · exact Or.inl (Prod.ext (Prod.ext h1 h3) h2)
    · exact Or.inr (Prod.ext (Prod.ext h1 h3) h2)
  art_q := fun u hu => by
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (D.art hH u).2 ^ 2 = 1
    rw [h2, sq, w_mul_self]
  art_ch := D.art_ch hH

def host : HostRaw D.frame := (D.charData hH hc he hs).toHostRaw

theorem host_q : (D.host hH hc he hs).q = q := rfl
theorem host_d : (D.host hH hc he hs).d = d := rfl
theorem host_QS : (D.host hH hc he hs).QS = D.m := rfl
theorem host_art : (D.host hH hc he hs).art = D.art hH := rfl

theorem psQ : (D.host hH hc he hs).PsQ := D.art_ps hH

theorem exists_sqq : ∃ s : (D.host hH hc he hs).E, s ^ 2 = -((D.host hH hc he hs).q : (D.host hH hc he hs).E) ∧
    ∀ σ : (D.host hH hc he hs).E ≃ₐ[ℚ] (D.host hH hc he hs).E,
      σ s = (((((D.host hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (D.host hH hc he hs).E) * s :=
  (D.charData hH hc he hs).exists_sqq (D.psQ hH hc he hs)

theorem exact (h : ∀ l : ℕ, l.Prime → l ∣ D.m → ∃ v : (ZMod D.m)ˣ, (v : ZMod D.m).val ≡ 1 [MOD D.m / l] ∧ D.eta v ≠ 1) :
    (D.host hH hc he hs).Exact := by
  have := D.neZeroN hH
  intro l hl (hlm : l ∣ D.m)
  obtain ⟨v, hv, hv1⟩ := h l hl hlm
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_crt_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime v) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  refine ⟨u, ?_, fun h4 => hv1 ?_⟩
  · show (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m * q * d / l]
    have h5 : D.m * q * d / l = D.m / l * (q * d) := by rw [mul_assoc, Nat.div_mul_right_comm hlm]
    have h6 : D.m / l ∣ D.m := Nat.div_dvd_of_dvd hlm
    rw [h5]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (hc.coprime_dvd_left h6)).mp
      ⟨(h1.of_dvd h6).trans hv, (Nat.modEq_and_modEq_iff_modEq_mul (D7.cop_qd hH)).mp ⟨h2, h3⟩⟩
  · have h5 : (D.art hH u).2 = 1 := congrArg Prod.snd h4
    rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, D.art_ps_one hH u h2 (by simp), map_one, mul_one] at h5
    exact (D.toA_eq_one_iff v).mp h5

end Host

end ModData

end WindowedLandauTheory.HC
