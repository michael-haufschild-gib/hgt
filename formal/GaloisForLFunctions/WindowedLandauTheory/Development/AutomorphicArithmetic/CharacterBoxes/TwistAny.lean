import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.KerChiAny

/-! A frame character trivial on the cyclic subgroup factors into a kept character and two quadratic signs. -/

open WindowedLandauTheory.HC WindowedLandauTheory.FrobeniusOrbits
open WindowedLandauTheory.TwoAdicCyclotomicDecomposition UpperTheory.Top

private theorem exA {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
    (θ : (AnyGrp.frame Ξ e).Char) (h1 : Frame.TrivialOnFirstFactor θ) :
    ∃ χ ∈ Ξ, ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ,
      θ (1, (AnyGrp.data Ξ e).toA (ZMod.unitsMap (AnyGrp.QS_dvd Ξ e) u)) =
        χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  set D := AnyGrp.data Ξ e with hD
  let g : (ZMod (AnyGrp.QS Ξ e))ˣ →* ℂˣ := (θ.comp (MonoidHom.inr G0 D.frame.MA)).comp D.toA
  have hk : (AnyGrp.xi Ξ e).ker ≤ g.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    change g u = 1
    have h0 : Multiplicative.toAdd (D.toA u) ∈ D.frame.A0 := by
      rw [D.mem_A0_iff_xiA_eq_one]
      exact (D.xiA_toA u).trans hu
    exact h1 _ h0
  let ρ := MonoidHom.liftOfSurjective (AnyGrp.xi Ξ e) (AnyGrp.xi_surj Ξ e) ⟨g, hk⟩
  have hρ : ∀ u, ρ (AnyGrp.xi Ξ e u) = g u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  let cu : (ZMod M)ˣ →* ℂˣ := ρ.comp (QuotientGroup.mk' (AnyGrp.ann Ξ))
  refine ⟨MulChar.ofUnitHom cu, ?_, fun u => ?_⟩
  · rw [AnyGrp.mem_iff]
    intro v hv
    rw [MulChar.ofUnitHom_coe]
    have hv1 : QuotientGroup.mk' (AnyGrp.ann Ξ) v = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hv
    change ((ρ (QuotientGroup.mk' (AnyGrp.ann Ξ) v) : ℂˣ) : ℂ) = 1
    rw [hv1, map_one, Units.val_one]
  · apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe]
    have hx : AnyGrp.xi Ξ e (ZMod.unitsMap (AnyGrp.QS_dvd Ξ e) u) =
        QuotientGroup.mk' (AnyGrp.ann Ξ) (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u) :=
      AnyGrp.xi_unitsMap Ξ e u
    change ((θ (1, D.toA (ZMod.unitsMap (AnyGrp.QS_dvd Ξ e) u)) : ℂˣ) : ℂ) =
      ((ρ (QuotientGroup.mk' (AnyGrp.ann Ξ) (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u)) : ℂˣ) : ℂ)
    rw [← hx, hρ]
    rfl

private theorem exSign (f : ℤˣ →* ℂˣ) : ∃ i : Fin 2, f (-1) = (-1) ^ (i : ℕ) ∧
    ∀ s : ℤˣ, ((f s : ℂˣ) : ℂ) = (((s : ℤ) : ℤ) : ℂ) ^ (i : ℕ) := by
  have hm : (-1 : ℤˣ) * -1 = 1 := by simp
  have hsq : ((f (-1) : ℂˣ) : ℂ) * ((f (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hm, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · refine ⟨0, Units.ext (by simpa using h), fun s => ?_⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simp [h]
  · refine ⟨1, Units.ext (by simpa using h), fun s => ?_⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simp [h]

theorem UpperTheory.Top.twistAny :
    ∀ (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) (hc : Nat.Coprime ψ.N (q * d)) (he : 2 ≤ e)
      (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ ψ.N → jacobiSym (-(d : ℤ)) l = 1),
      TwistForm ψ (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs) := by
  intro ψ e q d hH hc he hs θ hθ
  haveI := ψ.ne
  set D := AnyGrp.data (Subgroup.zpowers ψ.χ) e with hD
  obtain ⟨χ, hχ, hχθ⟩ := exA (Subgroup.zpowers ψ.χ) e θ hθ
  let f1 : ℤˣ →* ℂˣ := θ.comp (MonoidHom.prod (MonoidHom.inl ℤˣ ℤˣ) D.w)
  let f2 : ℤˣ →* ℂˣ := θ.comp ((MonoidHom.inl G0 D.frame.MA).comp (MonoidHom.inr ℤˣ ℤˣ))
  obtain ⟨i, -, hi⟩ := exSign f1
  obtain ⟨j, hj1, hj⟩ := exSign f2
  refine ⟨χ, hχ, i, j, ?_, fun a h => ?_⟩
  · exact hj1
  have hM : ψ.N ∣ D.m := AnyGrp.primitive_level_dvd_QS ψ.χ ψ.prim e
  haveI := D.neZeroN hH
  have h' : a.Coprime (D.m * q * d) := h
  have h1 : a.Coprime D.m := h'.coprime_dvd_right (D.m_dvd q d)
  have hT : 2 ^ (e + 2) ∣ D.m := D.tower
  have hL : (2 ^ (e + 2)).lcm ψ.N ∣ D.m := Nat.lcm_dvd hT hM
  have hcL : a.Coprime ((2 ^ (e + 2)).lcm ψ.N) := h1.coprime_dvd_right hL
  have hv : ((ZMod.unitOfCoprime a h' : ZMod (D.m * q * d)).val) ≡ a [MOD D.m * q * d] := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq a _
  have hdir : (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs).dirAt θ a =
      ((θ (D.art hH (ZMod.unitOfCoprime a h')) : ℂˣ) : ℂ) := by
    rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a h, HostRaw.dir_unit]
    rfl
  set x := D.art hH (ZMod.unitOfCoprime a h') with hx
  have hsplit : x = ((x.1.1, 1), D.w x.1.1) * ((1, x.1.2), 1) *
      ((1, 1), D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change x.1.1 = x.1.1 * 1 * 1
      rw [mul_one, mul_one]
    · change x.1.2 = 1 * x.1.2 * 1
      rw [one_mul, mul_one]
    · change x.2 = D.w x.1.1 * 1 * D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))
      rw [mul_one, hx, D.art_snd, mul_comm]
  have e1 : ((θ ((x.1.1, 1), D.w x.1.1) : ℂˣ) : ℂ) = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) := by
    rw [show θ ((x.1.1, 1), D.w x.1.1) = f1 x.1.1 from rfl, hi, hx, D.art_ps,
      jacobi_congr (hv.of_dvd (D.q_dvd q d))]
  have e2 : ((θ ((1, x.1.2), 1) : ℂˣ) : ℂ) = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ) := by
    rw [show θ ((1, x.1.2), 1) = f2 x.1.2 from rfl, hj, hx, D.art_ch,
      jacobi_congr (hv.of_dvd (D.d_dvd q d))]
  have e3 : ((θ ((1, 1), D.toA (ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h'))) : ℂˣ) : ℂ) =
      χ (a : ZMod ψ.N) := by
    have hw := hχθ (ZMod.unitOfCoprime a hcL)
    rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at hw
    rw [unitsMap_unitOfCoprime]
    have hw' := congrArg (fun z : ℂˣ => (z : ℂ)) hw
    simp only [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] at hw'
    exact hw'
  rw [hdir, hsplit, map_mul, map_mul, Units.val_mul, Units.val_mul, e1, e2, e3]
  change _ = χ (a : ZMod ψ.N) * ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) *
    ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)
  ring
