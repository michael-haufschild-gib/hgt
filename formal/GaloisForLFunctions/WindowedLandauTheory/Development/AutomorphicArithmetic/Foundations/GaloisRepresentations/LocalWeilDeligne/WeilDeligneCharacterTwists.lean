import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! The determinant reads the rank-one character of a Weil–Deligne
parameter. Twisting by that character respects sums and composition. -/

noncomputable section

open Module
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace WDRep

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def detChar (a : WDRep h V) : Weil h →* ℂˣ :=
  Units.map (LinearMap.det : End ℂ V →* ℂ) |>.comp a.ρ.toHomUnits

omit [IsAlgClosure E Ω] in
theorem smooth_detChar (a : WDRep h V) : IsSmooth a.detChar :=
  a.smooth.of_le fun σ hσ => Units.ext (by change LinearMap.det (a.ρ σ) = 1; rw [hσ, map_one])

omit [IsAlgClosure E Ω] in
theorem Iso.detChar_eq {a : WDRep h V} {b : WDRep h V'} (h : a.Iso b) :
    a.detChar = b.detChar := by
  obtain ⟨e, he, -⟩ := h
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  change LinearMap.det (a.ρ σ) = LinearMap.det (b.ρ σ)
  have h : (e : V →ₗ[ℂ] V') ∘ₗ a.ρ σ ∘ₗ (e.symm : V' →ₗ[ℂ] V) = b.ρ σ := by
    ext v
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply] using he σ (e.symm v)
  rw [← h, LinearMap.det_conj]

end WDRep

namespace WD

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def detChar (x : WD h) : Weil h →* ℂˣ :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.detChar)
    (fun _ _ hab => WDRep.Iso.detChar_eq hab) x

@[simp] theorem detChar_mk (a : WDRep h V) : (mk a).detChar = a.detChar :=
  (iso_std a).detChar_eq.symm

theorem smooth_detChar (x : WD h) : IsSmooth x.detChar := by
  refine WD.ind (fun n a => ?_) x
  rw [detChar_mk]
  exact a.smooth_detChar

/-- Twist by the determinant character. In rank one this is the character
of the parameter itself. -/
def lpChar (x y : WD h) : WD h := lpTwist x y.detChar y.smooth_detChar

theorem lpDim_char (x y : WD h) : (x.lpChar y).lpDim = x.lpDim :=
  lpDim_twist x _ _

theorem lpChar_sum (x y z : WD h) : (lpSum x y).lpChar z = lpSum (x.lpChar z) (y.lpChar z) := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpChar, lpSum_mk, lpTwist_mk]
  apply sound
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

/-- A scalar twist multiplies the determinant by the twisting character to the rank. -/
theorem detChar_twist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (σ : Weil h) : ((lpTwist x χ hχ).detChar σ : ℂ) =
      (χ σ : ℂ) ^ x.lpDim * (x.detChar σ : ℂ) := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpTwist_mk, detChar_mk, lpDim_mk]
  change LinearMap.det ((χ σ : ℂ) • a.ρ σ) = _
  rw [LinearMap.det_smul]
  rfl

-- The one-dimensional unramified parameter with eigenvalue one is the trivial character.
theorem lpChar_unit (x : WD h) : x.lpChar (lpUnr fun _ : Fin 1 => 1) = x := by
  let u := WDRep.diag (h := h) (fun _ : Fin 1 => 1)
  have ht : (mk u).detChar = 1 := by
    rw [detChar_mk]
    apply MonoidHom.ext
    intro σ
    apply Units.ext
    change LinearMap.det (u.ρ σ) = 1
    rw [show u.ρ σ = 1 from LinearMap.ext fun v => funext fun i => by
      simp [u, WDRep.diag_ρ_apply]]
    exact map_one _
  refine WD.ind (fun n a => ?_) x
  change lpChar (mk a) (mk u) = mk a
  simp only [lpChar, lpTwist_mk]
  refine sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  change (((mk u).detChar σ : ℂ) • a.ρ σ v) = _
  simp [ht]

theorem lpChar_zero (x : WD h) :
    (lpUnr fun _ : Fin 0 => 1).lpChar x = lpUnr fun _ : Fin 0 => 1 := by
  simp only [lpChar, lpUnr, lpTwist_mk]
  exact sound ⟨LinearEquiv.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => rfl⟩

/-- Twisting twice amounts to multiplying the two rank-one characters. -/
theorem lpChar_assoc (x y z : WD h) (hy : y.lpDim = 1) :
    (x.lpChar y).lpChar z = x.lpChar (y.lpChar z) := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpChar, lpTwist_mk]
  apply sound
  refine ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  change (z.detChar σ : ℂ) • ((y.detChar σ : ℂ) • a.ρ σ v) =
    ((lpTwist y z.detChar z.smooth_detChar).detChar σ : ℂ) • a.ρ σ v
  rw [detChar_twist, hy, pow_one, smul_smul]

end WD
end GlobalTheory.WeilDeligne
