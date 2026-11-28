import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionCentralCharacterClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionDepthZeroClass

/-! In rank one, determinant identifies first congruence with
first principal units and gives all the cuspidal classes.
The central character detects equivalence and twisting. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.Reciprocity

namespace GlobalTheory.GLp.IrrGL

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "L" => HeightOneSpectrum.adicCompletion F v

private theorem det_mem_firstUnits_iff (g : GL (Fin 1) L) :
    g.det ∈ unitsLevel v 1 ↔ g ∈ completionPrincipalCongruenceOne v (Fin 1) := by
  let e := unitsLevelZeroEquivIntegerUnits v
  have he (a : unitsLevel (K := F) v 0) :
      finiteCompletionUnitReduction v a = 1 ↔ a.val ∈ unitsLevel v 1 :=
    (finiteCompletionUnitReduction_eq_one_iff v a).trans (mem_unitsLevel_one_iff_lt_one v a.val).symm
  constructor
  · intro h
    let a : unitsLevel (K := F) v 0 := ⟨g.det, unitsLevel_antitone v (by omega : 0 ≤ 1) h⟩
    have ha : Units.map (completionReduction v).toMonoidHom (e a) = 1 := (he a).mpr h
    let u := GeneralLinearGroup.scalar (Fin 1) (e a)
    refine ⟨u, ?_, ?_⟩
    · change GeneralLinearGroup.map (completionReduction v) u = 1
      rw [show u = GeneralLinearGroup.scalar (Fin 1) (e a) from rfl, GeneralLinearGroup.map_scalar]
      exact (congrArg (GeneralLinearGroup.scalar (Fin 1)) ha).trans (map_one _)
    · have hv : Units.map (algebraMap (CompletedIntegers v) L).toMonoidHom (e a) = g.det :=
        Units.ext (unitsLevelZeroEquivIntegerUnits_val v a)
      rw [show u = GeneralLinearGroup.scalar (Fin 1) (e a) from rfl, GeneralLinearGroup.map_scalar]
      exact (congrArg (GeneralLinearGroup.scalar (Fin 1)) hv).trans (scalar_det_fin_one g)
  · rintro ⟨u, hu, rfl⟩
    let a := e.symm u.det
    have ha : e a = u.det := e.apply_symm_apply u.det
    have hdet : (GeneralLinearGroup.map (algebraMap (CompletedIntegers v) L) u).det = a.val := by
      rw [GeneralLinearGroup.map_det, ← ha]
      exact Units.ext (unitsLevelZeroEquivIntegerUnits_val v a)
    have hr : finiteCompletionUnitReduction v a = 1 := by
      change Units.map (completionReduction v).toMonoidHom (e a) = 1
      exact (congrArg (Units.map (completionReduction v).toMonoidHom) ha).trans
        ((GeneralLinearGroup.map_det (completionReduction v) u).symm.trans
          ((congrArg GeneralLinearGroup.det (show GeneralLinearGroup.map (completionReduction v) u = 1 from hu)).trans
            (map_one _)))
    rw [hdet]
    exact (he a).mp hr

theorem isCusp_ofCharacter (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) :
    (ofCharacter v χ hχ).IsCusp :=
  (isCusp_mk_iff (rankOneIrrRep χ hχ)).mpr ⟨Nat.one_pos, rankOneIrrRep_cuspidal χ hχ⟩

@[simp] theorem centralCharacter_ofCharacter (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) :
    (ofCharacter v χ hχ).centralCharacter v = χ := by
  apply centralCharacter_eq_of_act v (rankOneIrrRep χ hχ)
  intro z x
  let w : ℂ := x
  change rankOneCharacter χ (GeneralLinearGroup.scalar (Fin 1) z) w = (χ z : ℂ) * w
  simp [GeneralLinearGroup.det_scalar]

theorem eq_of_rankOne_centralCharacter_eq {x y : IrrGL L} (hx : x.1 = 1) (hy : y.1 = 1)
    (h : x.centralCharacter v = y.centralCharacter v) : x = y := by
  obtain ⟨χ, hχ, rfl⟩ := exists_ofCharacter_of_rank_one v x hx
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofCharacter_of_rank_one v y hy
  simp only [centralCharacter_ofCharacter] at h
  subst ψ
  rfl

theorem ofCharacter_detTwist (χ ψ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ))
    (hψ : IsOpen (ψ.ker : Set Lˣ)) :
    (ofCharacter v χ hχ).detTwist ψ hψ = ofCharacter v (χ * ψ) (isOpen_ker_mul _ _ hχ hψ) := by
  refine eq_of_rankOne_centralCharacter_eq v rfl rfl ?_
  rw [centralCharacter_detTwist, centralCharacter_ofCharacter, centralCharacter_ofCharacter]
  change χ * ψ ^ (1 : ℕ) = χ * ψ
  exact congrArg (χ * ·) (pow_one ψ)

theorem depthZero_ofCharacter_iff (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) :
    (ofCharacter v χ hχ).DepthZero v ↔ ∀ z : Lˣ, z ∈ unitsLevel v 1 → χ z = 1 := by
  rw [ofCharacter, depthZero_mk_iff]
  let H := completionPrincipalCongruenceOne v (Fin 1)
  constructor
  · intro hn z hz
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    let g := GeneralLinearGroup.scalar (Fin 1) z
    have hd : g.det = z := by simp [g, GeneralLinearGroup.det_scalar]
    have hg : g ∈ H := (det_mem_firstUnits_iff v g).mp (hd.symm ▸ hz)
    have he := hx ⟨g, hg⟩
    change (rankOneCharacter χ g) x = x at he
    rw [rankOneCharacter_apply, hd] at he
    let w : ℂ := x
    have hw : w ≠ 0 := hx0
    have he' : (χ z : ℂ) * w = w := he
    exact Units.ext (mul_right_cancel₀ hw (he'.trans (one_mul w).symm))
  · intro h
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨(1 : ℂ), ?_, (show (1 : ℂ) ≠ 0 from one_ne_zero)⟩
    intro g
    change (rankOneCharacter χ g.val) (1 : ℂ) = 1
    rw [rankOneCharacter_apply, h _ ((det_mem_firstUnits_iff v g.val).mpr g.2), Units.val_one, one_mul]

end GlobalTheory.GLp.IrrGL

#print axioms GlobalTheory.GLp.IrrGL.ofCharacter_detTwist
#print axioms GlobalTheory.GLp.IrrGL.depthZero_ofCharacter_iff
