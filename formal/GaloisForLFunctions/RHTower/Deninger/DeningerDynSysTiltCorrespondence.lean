import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTiltSurjective
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysFontaineTheta
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTiltInjective

/-!
# The tilting correspondence for pointed multiplicative maps

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.13
(`t1110`).

A homomorphism of tilts `χ♭ : A♭ → 𝒪♭` gives the pointed multiplicative map `χ = ♯ ∘ χ♭` out of
`A♭ ≅ lim_{()^p} A`, and `χ♭` is recovered from `χ`: the zeroth coefficient of `χ♭ x` is the
reduction of `χ x` modulo `p`, and a homomorphism into a perfection is determined by its zeroth
coefficient.  So the assignment `χ♭ ↦ χ` is injective.  Conversely a pointed multiplicative map
whose reduction modulo `p` is additive is `♯ ∘ χ♭` for the perfection lift of that reduction:
comparing the two sides coefficientwise gives `p ∣ ♯(Frob^{-n} χ♭ x) - χ (Frob^{-n} x)`, and
raising to the `pⁿ`-th power turns this into a congruence modulo `p^{n+1}`, so the two sides agree
in the `p`-adically complete ring `𝒪`.  Together these give the correspondence.
-/

namespace RHTower

open Perfection PreTilt

universe u

variable {A O : Type u} [CommRing A] [CommRing O] {p : ℕ} [Fact p.Prime]
variable [Fact (¬ IsUnit (p : A))] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- **Deninger, Proposition 14.13 (`t1110`).**  The pointed multiplicative map `χ = ♯ ∘ χ♭`
attached to a homomorphism of tilts. -/
noncomputable def deningerTiltChar (χ : PreTilt A p →+* PreTilt O p) : PreTilt A p →* O :=
  PreTilt.untilt.comp χ.toMonoidHom

@[simp] theorem deningerTiltChar_apply (χ : PreTilt A p →+* PreTilt O p) (x : PreTilt A p) :
    deningerTiltChar χ x = (χ x).untilt := rfl

/-- **Deninger, Proposition 14.13 (`t1110`).**  A homomorphism of tilts is determined by the
pointed multiplicative map it induces, because a homomorphism into a perfection is determined by
its zeroth coefficient and that coefficient is the reduction of the untilt. -/
theorem deningerTiltHom_ext {χ ψ : PreTilt A p →+* PreTilt O p}
    (h : ∀ x, (χ x).untilt = (ψ x).untilt) : χ = ψ := by
  refine Perfection.hom_ext p (S := ModP O p) fun x => ?_
  have h1 : PreTilt.coeff 0 (χ x) = PreTilt.coeff 0 (ψ x) := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  rw [PreTilt.coeff_def, PreTilt.coeff_def] at h1
  exact h1

theorem deningerTiltChar_injective :
    Function.Injective (deningerTiltChar (A := A) (O := O) (p := p)) := by
  intro χ ψ h
  exact deningerTiltHom_ext fun x => DFunLike.congr_fun h x

/-- **Deninger, Proposition 14.13 (`t1110`), the existence half of the correspondence.**  A pointed
multiplicative map whose reduction modulo `p` is a ring homomorphism is `♯ ∘ χ♭` for the lift `χ♭`
of that reduction. -/
theorem deningerTiltChar_exists (χ : PreTilt A p →* O) (χbar : PreTilt A p →+* ModP O p)
    (hχ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x) = χbar x) :
    deningerTiltChar (Perfection.lift p (PreTilt A p) (ModP O p) χbar) = χ := by
  set χb := Perfection.lift p (PreTilt A p) (ModP O p) χbar with hχb
  refine MonoidHom.ext fun x => ?_
  show PreTilt.untilt (χb x) = χ x
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]
  intro k
  refine deningerSMod_of_dvd ?_
  rcases k with _ | n
  · simp
  · have hx : (((frobeniusEquiv (PreTilt A p) p).symm)^[n] x) ^ p ^ n = x := by simp
    set y : PreTilt O p := χb x with hydef
    have hiter : ((frobenius (PreTilt O p) p)^[n])
        (((frobeniusEquiv (PreTilt O p) p).symm)^[n] y) = y := by
      rw [← coe_frobeniusEquiv]
      exact Function.LeftInverse.iterate
        (fun z => (frobeniusEquiv (PreTilt O p) p).apply_symm_apply z) n y
    have hc0 : PreTilt.coeff 0 (((frobeniusEquiv (PreTilt O p) p).symm)^[n] y)
        = PreTilt.coeff n y := by
      have hstep := PreTilt.coeff_iterate_frobenius 0 n
        (((frobeniusEquiv (PreTilt O p) p).symm)^[n] y)
      rw [hiter, zero_add] at hstep
      exact hstep.symm
    have hcn : PreTilt.coeff n y
        = χbar (((frobeniusEquiv (PreTilt A p) p).symm)^[n] x) := rfl
    have hdvd : (p : O) ∣ PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm)^[n] y)
        - χ (((frobeniusEquiv (PreTilt A p) p).symm)^[n] x) := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
        PreTilt.mk_untilt_eq_coeff_zero, hc0, hcn, ← hχ]
    have hpow := dvd_sub_pow_of_dvd_sub hdvd n
    rw [PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, ← map_pow, hx] at hpow
    exact hpow

/-- The reduction modulo `p` of the pointed multiplicative map attached to a homomorphism of tilts
is the ring homomorphism given by the zeroth coefficient. -/
theorem deningerTiltChar_reduction (χ : PreTilt A p →+* PreTilt O p) (x : PreTilt A p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (deningerTiltChar χ x)
      = ((PreTilt.coeff 0).comp χ) x := by
  rw [deningerTiltChar_apply, PreTilt.mk_untilt_eq_coeff_zero]
  rfl

/-- **Deninger, Proposition 14.13 (`t1110`).**  A pointed multiplicative map `A♭ → 𝒪` comes from a
homomorphism of tilts exactly when its reduction modulo `p` is additive. -/
theorem deningerTiltChar_exists_iff (χ : PreTilt A p →* O) :
    (∃ χflat : PreTilt A p →+* PreTilt O p, deningerTiltChar χflat = χ)
      ↔ ∃ χbar : PreTilt A p →+* ModP O p,
          ∀ x, Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x) = χbar x := by
  constructor
  · rintro ⟨χflat, rfl⟩
    exact ⟨(PreTilt.coeff 0).comp χflat, fun x => deningerTiltChar_reduction χflat x⟩
  · rintro ⟨χbar, hχ⟩
    exact ⟨_, deningerTiltChar_exists χ χbar hχ⟩

/-- **Deninger, Proposition 14.13 (`t1110`), the correspondence.**  A pointed multiplicative map
`A♭ → 𝒪` whose reduction modulo `p` is additive comes from a unique homomorphism of tilts. -/
theorem deningerTiltChar_existsUnique (χ : PreTilt A p →* O) (χbar : PreTilt A p →+* ModP O p)
    (hχ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x) = χbar x) :
    ∃! χflat : PreTilt A p →+* PreTilt O p, deningerTiltChar χflat = χ :=
  ⟨_, deningerTiltChar_exists χ χbar hχ, fun _ hψ =>
    deningerTiltChar_injective (hψ.trans (deningerTiltChar_exists χ χbar hχ).symm)⟩

variable [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- **Deninger, Proposition 14.13 (`t1110`).**  The pointed multiplicative map on
`lim_{()^p} A` attached to a homomorphism of tilts, through the identification
`lim_{()^p} A ≅ A♭`. -/
noncomputable def deningerLimChar (χ : PreTilt A p →+* PreTilt O p) : Perfection A p →* O :=
  (deningerTiltChar χ).comp (deningerTiltEquiv (A := A) (p := p)).toMonoidHom

@[simp] theorem deningerLimChar_apply (χ : PreTilt A p →+* PreTilt O p) (x : Perfection A p) :
    deningerLimChar χ x = (χ (deningerTiltComparison x)).untilt := rfl

/-- **Deninger, Proposition 14.13 (`t1110`), the uniqueness half of the correspondence.**  A
homomorphism of tilts is determined by the pointed multiplicative map it induces on
`lim_{()^p} A`. -/
theorem deningerLimChar_injective :
    Function.Injective (deningerLimChar (A := A) (O := O) (p := p)) := by
  intro χ ψ h
  refine deningerTiltHom_ext fun y => ?_
  obtain ⟨x, rfl⟩ := deningerTiltComparison_surjective (A := A) (p := p) y
  exact DFunLike.congr_fun h x

/-- **Deninger, Proposition 14.13 (`t1110`), the correspondence on `lim_{()^p} A`.**  A pointed
multiplicative map `lim_{()^p} A → 𝒪` whose reduction modulo `p` is additive on the tilt comes
from a unique homomorphism of tilts. -/
theorem deningerLimChar_existsUnique (χ : Perfection A p →* O)
    (χbar : PreTilt A p →+* ModP O p)
    (hχ : ∀ x : Perfection A p,
      Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x) = χbar (deningerTiltComparison x)) :
    ∃! χflat : PreTilt A p →+* PreTilt O p, deningerLimChar χflat = χ := by
  set e := deningerTiltEquiv (A := A) (p := p) with he
  set χ' : PreTilt A p →* O := χ.comp e.symm.toMonoidHom with hχ'
  have hbar : ∀ y : PreTilt A p,
      Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ' y) = χbar y := by
    intro y
    have h1 := hχ (e.symm y)
    have h2 : deningerTiltComparison (e.symm y) = y := e.apply_symm_apply y
    rw [h2] at h1
    exact h1
  obtain ⟨χflat, hflat, huniq⟩ := deningerTiltChar_existsUnique χ' χbar hbar
  have hval : ∀ (ψ : PreTilt A p →+* PreTilt O p) (z : Perfection A p),
      deningerLimChar ψ z = PreTilt.untilt (ψ (e z)) := fun _ _ => rfl
  refine ⟨χflat, MonoidHom.ext fun x => ?_, fun ψ hψ => huniq ψ (MonoidHom.ext fun y => ?_)⟩
  · have h1 := DFunLike.congr_fun hflat (e x)
    have h2 : χ' (e x) = χ x := by
      show χ (e.symm (e x)) = χ x
      rw [e.symm_apply_apply]
    rw [hval χflat x]
    exact h1.trans h2
  · have h1 := DFunLike.congr_fun hψ (e.symm y)
    rw [hval ψ (e.symm y), e.apply_symm_apply] at h1
    exact h1

end RHTower
