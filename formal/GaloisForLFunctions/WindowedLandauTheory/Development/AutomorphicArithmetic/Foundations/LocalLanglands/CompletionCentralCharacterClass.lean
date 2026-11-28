import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalGLIrreducibleClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalGLRankOne

/-! Scalar matrices determine the central character on an
irreducible class. A determinant twist multiplies it by the
rank-th power of the twisting character. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.PRep

namespace GlobalTheory.GLp.IrrGL

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "L" => HeightOneSpectrum.adicCompletion F v

private theorem exists_centralCharacter (x : IrrGL L) :
    ∃ ω : Lˣ →* ℂˣ, IsOpen (ω.ker : Set Lˣ) ∧
      ∀ z a, x.2.rep.ρ (GeneralLinearGroup.scalar (Fin x.1) z) a = (ω z : ℂ) • a := by
  letI := x.2.rep.irr
  obtain ⟨ω, ho, hw, -⟩ := exists_unique_smoothGLCentralCharacter v x.2.rep.ρ x.2.rep.smooth
  exact ⟨ω, ho, hw⟩

def centralCharacter (x : IrrGL L) : Lˣ →* ℂˣ := (exists_centralCharacter v x).choose

theorem isOpen_ker_centralCharacter (x : IrrGL L) :
    IsOpen ((x.centralCharacter v).ker : Set Lˣ) :=
  (exists_centralCharacter v x).choose_spec.1

theorem centralCharacter_act {n : ℕ} (a : IrrRep (GL (Fin n) L)) (z : Lˣ) (w : a.V) :
    a.ρ (GeneralLinearGroup.scalar (Fin n) z) w =
      ((centralCharacter v (⟨n, a.cl⟩ : IrrGL L)) z : ℂ) • w := by
  let x : IrrGL L := ⟨n, a.cl⟩
  obtain ⟨e⟩ := IrrRep.cl_eq_iff.mp a.cl.cl_rep
  have hr := (exists_centralCharacter v x).choose_spec.2 z (e.toLinearEquiv.symm w)
  apply e.toLinearEquiv.symm.injective
  exact (IntertwiningMap.isIntertwining a.ρ x.2.rep.ρ e.symm.toIntertwiningMap
    (GeneralLinearGroup.scalar (Fin n) z) w).trans
    (hr.trans (map_smul e.toLinearEquiv.symm _ w).symm)

theorem centralCharacter_eq_of_act {n : ℕ} (a : IrrRep (GL (Fin n) L)) {ω : Lˣ →* ℂˣ}
    (hw : ∀ z w, a.ρ (GeneralLinearGroup.scalar (Fin n) z) w = (ω z : ℂ) • w) :
    centralCharacter v (⟨n, a.cl⟩ : IrrGL L) = ω := by
  letI := a.irr
  obtain ⟨θ, -, -, he⟩ := exists_unique_smoothGLCentralCharacter v a.ρ a.smooth
  exact (he _ (centralCharacter_act v a)).trans (he _ hw).symm

theorem centralCharacter_detTwist (x : IrrGL L) (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) :
    (x.detTwist χ hχ).centralCharacter v = x.centralCharacter v * χ ^ x.1 := by
  let a := x.2.rep
  let b := a.twist (χ.comp GeneralLinearGroup.det) (hχ.preimage GeneralLinearGroup.continuous_det)
  have hx : (⟨x.1, a.cl⟩ : IrrGL L) = x := congrArg (Sigma.mk x.1) x.2.cl_rep
  have hb : (⟨x.1, b.cl⟩ : IrrGL L) = x.detTwist χ hχ := by
    apply congrArg (Sigma.mk x.1)
    simp only [b, a, IrrRep.cl_twist, IrrCl.cl_rep]
  rw [← hb]
  apply centralCharacter_eq_of_act v b
  intro z w
  have hsc (z : Lˣ) (w : a.V) := centralCharacter_act v a z w
  simp only [hx] at hsc
  exact determinantTwist_centralCharacter a.ρ (x.centralCharacter v) χ hsc z w

def ofCharacter (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) : IrrGL L :=
  ⟨1, (rankOneIrrRep χ hχ).cl⟩

theorem exists_ofCharacter_of_rank_one (x : IrrGL L) (hx : x.1 = 1) :
    ∃ (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)), x = ofCharacter v χ hχ := by
  obtain ⟨n, c⟩ := x
  change n = 1 at hx
  subst n
  obtain ⟨χ, hχ, he⟩ := exists_rankOneIrrRep_equiv v c.rep
  exact ⟨χ, hχ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.mpr he))⟩

end GlobalTheory.GLp.IrrGL

#print axioms GlobalTheory.GLp.IrrGL.centralCharacter_detTwist
#print axioms GlobalTheory.GLp.IrrGL.exists_ofCharacter_of_rank_one
