import GaloisForLFunctions.HTGeometry.TranscendentalTranslateObstruction
import GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple
import GaloisForLFunctions.HTGeometry.DifferenceSolutionSpace

/-!
# No new constants in a Picard--Vessiot ring

A constant of a `σ`-simple, finitely generated extension of a difference field is algebraic over
the constants of the base, and lies in them when those constants are algebraically closed.

The argument has two halves.  The geometric half is that a transcendental element of a finite-type
algebra cannot have all of its translates by an infinite set of scalars invertible — Chevalley's
theorem, in `TranscendentalTranslateObstruction`.  Since a nonzero constant of a `σ`-simple ring is
a unit, a transcendental constant would violate exactly that, so every constant is algebraic over
the base.  The algebraic half is that the annihilator ideal of a constant is stable under the shift
acting on coefficients, so its monic generator is fixed, so its coefficients are constants of the
base.

This is the statement that makes the difference Galois group a group over a *fixed* field of
constants.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- The shift of a polynomial expression in a constant is the expression in the shifted
coefficients. -/
theorem sigma_aeval_eq (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    {e : R} (he : σR e = e) (p : K[X]) :
    σR (aeval e p) = aeval e (p.map (σK : K →+* K)) := by
  have h : (σR : R →+* R).comp ((aeval e : K[X] →ₐ[K] R) : K[X] →+* R)
      = ((aeval e : K[X] →ₐ[K] R) : K[X] →+* R).comp
        (Polynomial.mapRingHom (σK : K →+* K)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, hcompat]
    · simp [RingHom.comp_apply, he]
  exact DFunLike.congr_fun h p

/-- **No new constants, algebraic form.**  Every constant of a `σ`-simple finitely generated
extension is killed by a monic polynomial whose coefficients are constants of the base. -/
theorem exists_monic_constantCoeff_annihilator
    [Nontrivial R] [Algebra.FiniteType K R]
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hsimple : IsSigmaSimple σR)
    (hinf : ((differenceConstants σK : Subfield K) : Set K).Infinite)
    {e : R} (he : σR e = e) :
    ∃ g : K[X], g.Monic ∧ g.map (σK : K →+* K) = g ∧ aeval e g = 0 := by
  classical
  -- the constant is algebraic over the base
  have halg : IsAlgebraic K e := by
    by_contra hcon
    have htr : Transcendental K e := hcon
    obtain ⟨a, haC, hnu⟩ := exists_notMem_isUnit_sub_algebraMap htr hinf
    have haC' : σK a = a := haC
    have hconstElt : σR (e - algebraMap K R a) = e - algebraMap K R a := by
      rw [map_sub, he, hcompat, haC']
    rcases eq_or_ne (e - algebraMap K R a) 0 with hz | hnz
    · refine htr ⟨X - C a, X_sub_C_ne_zero a, ?_⟩
      have hea : e = algebraMap K R a := by
        have := sub_eq_zero.mp hz
        exact this
      simp [hea]
    · exact hnu (isUnit_of_isSigmaSimple_of_fixed hsimple hconstElt hnz)
  -- the annihilator ideal
  set I : Ideal K[X] := RingHom.ker ((aeval e : K[X] →ₐ[K] R) : K[X] →+* R) with hIdef
  have hmemI : ∀ p : K[X], p ∈ I ↔ aeval e p = 0 := fun p => Iff.rfl
  have hIne : I ≠ ⊥ := by
    obtain ⟨p, hp0, hpe⟩ := halg
    intro hbot
    apply hp0
    have : p ∈ I := (hmemI p).mpr hpe
    rw [hbot] at this
    simpa using this
  set g0 : K[X] := Submodule.IsPrincipal.generator I with hg0def
  have hspan : Ideal.span {g0} = I := Submodule.IsPrincipal.span_singleton_generator I
  have hg0ne : g0 ≠ 0 := by
    intro h
    apply hIne
    rw [← hspan, h]
    simp
  set g : K[X] := g0 * C (g0.leadingCoeff)⁻¹ with hgdef
  have hgmonic : g.Monic := monic_mul_leadingCoeff_inv hg0ne
  have hgspan : Ideal.span {g} = I := by
    rw [hgdef, Ideal.span_singleton_mul_right_unit ?_ g0, hspan]
    exact (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0ne))))
  have hgI : g ∈ I := by
    rw [← hgspan]
    exact Ideal.mem_span_singleton_self g
  -- the ideal is stable under the shift acting on coefficients
  have hstab : ∀ p ∈ I, p.map (σK : K →+* K) ∈ I := by
    intro p hp
    have hp0 : aeval e p = 0 := (hmemI p).mp hp
    have hshift := sigma_aeval_eq σK σR hcompat he p
    rw [hp0, map_zero] at hshift
    exact (hmemI _).mpr hshift.symm
  -- the monic generator is fixed
  have hdvd : g ∣ g.map (σK : K →+* K) := by
    have hmem : g.map (σK : K →+* K) ∈ I := hstab g hgI
    rw [← hgspan, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hmapmonic : (g.map (σK : K →+* K)).Monic := hgmonic.map _
  have hdeg : (g.map (σK : K →+* K)).degree = g.degree :=
    degree_map_eq_of_injective (σK : K →+* K).injective g
  have hfix : g.map (σK : K →+* K) = g := by
    obtain ⟨q, hq⟩ := hdvd
    have hgne : g ≠ 0 := hgmonic.ne_zero
    have hqne : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hq
      exact hmapmonic.ne_zero hq
    have hnat : (g.map (σK : K →+* K)).natDegree = g.natDegree :=
      natDegree_map_eq_of_injective (σK : K →+* K).injective g
    have hnatmul : (g * q).natDegree = g.natDegree + q.natDegree := natDegree_mul hgne hqne
    have hq0 : q.natDegree = 0 := by
      have hcong := congrArg Polynomial.natDegree hq
      rw [hnat, hnatmul] at hcong
      omega
    have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq0
    have hlead : q.coeff 0 = 1 := by
      have h2 := congrArg Polynomial.leadingCoeff hq
      rw [hmapmonic.leadingCoeff, leadingCoeff_mul, hgmonic.leadingCoeff, one_mul] at h2
      rw [hqC] at h2
      simpa using h2.symm
    rw [hq, hqC, hlead, map_one, mul_one]
  exact ⟨g, hgmonic, hfix, (hmemI g).mp hgI⟩

/-- **No new constants.**  If the constants of the base are algebraically closed, then every
constant of a `σ`-simple finitely generated extension already lies in the base.

Algebraic closedness is used in the form in which it is needed: a monic polynomial of positive
degree fixed by the shift has a root fixed by the shift. -/
theorem exists_eq_algebraMap_of_isSigmaSimple
    [Nontrivial R] [Algebra.FiniteType K R]
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hsimple : IsSigmaSimple σR)
    (hinf : ((differenceConstants σK : Subfield K) : Set K).Infinite)
    (hclosed : ∀ g : K[X], g.Monic → 0 < g.natDegree → g.map (σK : K →+* K) = g →
      ∃ a : K, σK a = a ∧ g.IsRoot a)
    {e : R} (he : σR e = e) :
    ∃ a : K, σK a = a ∧ e = algebraMap K R a := by
  classical
  obtain ⟨g₀, hg₀monic, hg₀fix, hg₀ann⟩ :=
    exists_monic_constantCoeff_annihilator σK σR hcompat hsimple hinf he
  suffices haux : ∀ (n : ℕ) (g : K[X]), g.natDegree = n → g.Monic →
      g.map (σK : K →+* K) = g → aeval e g = 0 →
      ∃ a : K, σK a = a ∧ e = algebraMap K R a from
    haux g₀.natDegree g₀ rfl hg₀monic hg₀fix hg₀ann
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hgn hgmonic hgfix hgann
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exfalso
      have hd : g.natDegree = 0 := hgn.trans hn0
      have hc0 : g.coeff 0 = 1 := by
        have hl : g.leadingCoeff = 1 := hgmonic
        simpa [Polynomial.leadingCoeff, hd] using hl
      have hg1 : g = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hd, hc0, map_one]
      rw [hg1, map_one] at hgann
      exact one_ne_zero hgann
    · obtain ⟨a, haC, hroot⟩ := hclosed g hgmonic (by omega) hgfix
      set h : K[X] := g /ₘ (X - C a) with hhdef
      have hfact : (X - C a) * h = g := mul_divByMonic_eq_iff_isRoot.mpr hroot
      have hXne : (X - C a : K[X]) ≠ 0 := X_sub_C_ne_zero a
      have hhmonic : h.Monic := by
        have h1 := congrArg Polynomial.leadingCoeff hfact
        rw [leadingCoeff_mul, (monic_X_sub_C a).leadingCoeff, one_mul,
          hgmonic.leadingCoeff] at h1
        exact h1
      have hhne : h ≠ 0 := hhmonic.ne_zero
      have hhdeg : h.natDegree = n - 1 := by
        have h2 := congrArg Polynomial.natDegree hfact
        rw [natDegree_mul hXne hhne, natDegree_X_sub_C, hgn] at h2
        omega
      have hhfix : h.map (σK : K →+* K) = h := by
        have hXfix : (X - C a : K[X]).map (σK : K →+* K) = X - C a := by
          simp [Polynomial.map_sub, haC]
        have h3 : (X - C a) * h.map (σK : K →+* K) = (X - C a) * h := by
          rw [← hXfix, ← Polynomial.map_mul, hfact, hgfix, ← hfact, hXfix]
        exact mul_left_cancel₀ hXne h3
      have hprod : (e - algebraMap K R a) * aeval e h = 0 := by
        rw [← hgann, ← hfact]
        simp
      have hconst : σR (e - algebraMap K R a) = e - algebraMap K R a := by
        rw [map_sub, he, hcompat, haC]
      rcases eq_or_ne (e - algebraMap K R a) 0 with hz | hnz
      · exact ⟨a, haC, sub_eq_zero.mp hz⟩
      · have hunit := isUnit_of_isSigmaSimple_of_fixed hsimple hconst hnz
        have hzero : aeval e h = 0 := (hunit.mul_right_eq_zero).mp hprod
        exact ih (n - 1) (by omega) h hhdeg hhmonic hhfix hzero


end

end GaloisForLFunctions.HTGeometry
