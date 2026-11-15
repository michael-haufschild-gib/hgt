import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheRationalsContainsZeta
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaWeightsArePrincipalIdealCharacters
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# The Hecke family of the rationals carries the seed

E6 asks for the Hecke characters of a second field. Over `ℚ` a ray class character `ψ` modulo
`𝔪 = (N)·𝔪∞` takes on a positive integer `n` the value of its finite residue character at
`n mod N`, because `n` is positive at the real place (`heckeValue_span_natCast`). The residue ring
`𝓞_ℚ/(N)` is `ℤ/N` (`ratResidueEquiv`), so `ψ` restricted to the positive integers is a Dirichlet
character `χ_ψ` modulo `N` (`ratDirichlet`), and the global continuation of `L(s, ψ)` is `L(s, χ_ψ)`
off `s = 1` (`heckeLFunction_rat_eq_LFunction`).

* **The Hecke family of `ℚ` has the half-plane `7/8`** (`heckeHalfPlane_rat_seven_eighths`): no ray
  class `L`-function of `ℚ`, of any modulus and any signs at infinity, vanishes at `ρ ≠ 1` with
  `Re ρ > 7/8`. The seed of the Dirichlet `L`-functions is the seed of `ℚ(ω)` read through the base
  change `L(s, χ ∘ N) = L(s, χ) L(s, χ χ₋₃)` (MMD), so `ℚ ⊂ ℚ(ω)` are two fields whose whole
  Hecke family carries the seed (with `heckeHalfPlane_seven_eighths`).
-/

noncomputable section

open NumberField Complex Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open HeckeLFunctions FamilyContinuationTheory MetaplecticMobiusDescent.CubicEisenstein

variable (𝔪 : Modulus ℚ) (ψ : HeckeCharacter 𝔪)

/-- The norm `N` of the finite part of a modulus of `ℚ`. -/
abbrev ratLevel : ℕ := Ideal.absNorm 𝔪.fin

instance : NeZero (ratLevel 𝔪) := ⟨fun h => 𝔪.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)⟩

theorem natCast_ratLevel_eq_zero : ((ratLevel 𝔪 : ℕ) : 𝓞 ℚ ⧸ 𝔪.fin) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk 𝔪.fin), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem 𝔪.fin

/-- The residue map `ℤ/N → 𝓞_ℚ/𝔪₀`. -/
def ratResidueHom : ZMod (ratLevel 𝔪) →+* 𝓞 ℚ ⧸ 𝔪.fin :=
  ZMod.castHom (ringChar.dvd (natCast_ratLevel_eq_zero 𝔪)) _

theorem ratResidueHom_surjective : Function.Surjective (ratResidueHom 𝔪) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(Rat.ringOfIntegersEquiv a : ZMod (ratLevel 𝔪)), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk 𝔪.fin),
    ← eq_intCast Rat.ringOfIntegersEquiv.symm, RingEquiv.symm_apply_apply]

/-- `ℤ/N` and `𝓞_ℚ/𝔪₀` have the same `N` elements, so the residue map is a bijection. -/
theorem ratResidueHom_bijective : Function.Bijective (ratResidueHom 𝔪) := by
  have h : Nat.card (𝓞 ℚ ⧸ 𝔪.fin) = ratLevel 𝔪 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (ratResidueHom_surjective 𝔪).bijective_of_nat_card_le ((Nat.card_zmod _).le.trans h.ge)

/-- `ℤ/N ≅ 𝓞_ℚ/𝔪₀`. -/
def ratResidueEquiv : ZMod (ratLevel 𝔪) ≃+* 𝓞 ℚ ⧸ 𝔪.fin :=
  RingEquiv.ofBijective (ratResidueHom 𝔪) (ratResidueHom_bijective 𝔪)

/-- **The Dirichlet character of `ψ`**: its finite residue character read on `ℤ/N`. -/
def ratDirichlet : DirichletCharacter ℂ (ratLevel 𝔪) :=
  MulChar.ofUnitHom ((finiteResidueCharacter 𝔪 ψ).comp (Units.map (ratResidueHom 𝔪).toMonoidHom))

theorem ratDirichlet_apply (x : ZMod (ratLevel 𝔪)) :
    ratDirichlet 𝔪 ψ x = finiteHeckeWeight 𝔪 ψ (ratResidueHom 𝔪 x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h : ratResidueHom 𝔪 (u : ZMod (ratLevel 𝔪)) =
        ((Units.map (ratResidueHom 𝔪).toMonoidHom u : (𝓞 ℚ ⧸ 𝔪.fin)ˣ) : 𝓞 ℚ ⧸ 𝔪.fin) := rfl
    rw [ratDirichlet, MulChar.ofUnitHom_coe, h, finiteHeckeWeight_unit, MonoidHom.comp_apply]
  · refine (MulChar.map_nonunit _ hx).trans (MulChar.map_nonunit _ fun hu => hx ?_).symm
    have h := hu.map (ratResidueEquiv 𝔪).symm
    rwa [show ratResidueHom 𝔪 x = ratResidueEquiv 𝔪 x from rfl, RingEquiv.symm_apply_apply] at h

/-- On a positive integer `n` a ray class character of `ℚ` is its finite residue character at
`n mod N`: the sign of `n` at the real place is `+1`. -/
theorem heckeValue_span_natCast {n : ℕ} (hn : n ≠ 0) :
    heckeValue 𝔪 ψ (Ideal.span {(n : 𝓞 ℚ)}) = ratDirichlet 𝔪 ψ n := by
  have ha : algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hn
  have hsign : signAtInf 𝔪 (Units.mk0 _ ha) = 1 := by
    funext w
    have hpos : 0 < InfinitePlace.embedding_of_isReal w.1.2 ((Units.mk0 _ ha : ℚˣ) : ℚ) := by
      rw [Units.val_mk0, map_natCast, map_natCast]
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [signAtInf_apply, if_pos hpos, Pi.one_apply]
  rw [← integralHeckeWeight_mul_infiniteSign_eq_heckeValue 𝔪 ψ _ ha, hsign, map_one,
    Units.val_one, mul_one, ratDirichlet_apply, integralHeckeWeight,
    map_natCast (Ideal.Quotient.mk 𝔪.fin) n, map_natCast (ratResidueHom 𝔪) n]

/-- The ring of integers of `ℚ` has the one ideal `(n)` of norm `n`. -/
theorem idealsOfNorm_rat {n : ℕ} : idealsOfNorm ℚ n = {Ideal.span {(n : 𝓞 ℚ)}} := by
  have hmem : Ideal.span {(n : 𝓞 ℚ)} ∈ idealsOfNorm ℚ n := by
    rw [mem_idealsOfNorm, Ideal.absNorm_span_singleton, norm_ringOfIntegers_rat, map_natCast,
      Int.natAbs_natCast]
  have hsub : Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    (Nat.card_eq_one_iff_unique.mp (card_ideals_rat_absNorm n)).1
  ext I
  rw [Finset.mem_singleton]
  refine ⟨fun hI => ?_, fun hI => hI ▸ hmem⟩
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨I, mem_idealsOfNorm.mp hI⟩ : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n})
    ⟨_, mem_idealsOfNorm.mp hmem⟩)

theorem heckeCoeff_rat {n : ℕ} (hn : n ≠ 0) : heckeCoeff 𝔪 ψ n = ratDirichlet 𝔪 ψ n := by
  rw [heckeCoeff, idealsOfNorm_rat, Finset.sum_singleton, heckeValue_span_natCast 𝔪 ψ hn]

theorem heckeL_rat_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = (ratDirichlet 𝔪 ψ).LFunction s := by
  rw [heckeL, DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun {n} hn => heckeCoeff_rat 𝔪 ψ hn) s

/-- **A ray class `L`-function of `ℚ` is a Dirichlet `L`-function**: off `s = 1` the global
continuation of `L(s, ψ)` is `L(s, χ_ψ)`; both are holomorphic on `ℂ ∖ {1}` and agree on
`Re s > 1`. -/
theorem heckeLFunction_rat_eq_LFunction {s : ℂ} (hs : s ≠ 1) :
    heckeLFunction 𝔪 ψ s = (ratDirichlet 𝔪 ψ).LFunction s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hf : AnalyticOnNhd ℂ (heckeLFunction 𝔪 ψ) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_heckeLFunction 𝔪 ψ hz).differentiableWithinAt) hU
  have hg : AnalyticOnNhd ℂ (ratDirichlet 𝔪 ψ).LFunction ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt) hU
  have hev : heckeLFunction 𝔪 ψ =ᶠ[nhds (2 : ℂ)] (ratDirichlet 𝔪 ψ).LFunction := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [heckeLFunction_eq_heckeL 𝔪 ψ hz, heckeL_rat_eq_LFunction 𝔪 ψ hz]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn (by simp) hev hs

/-- **The Hecke family of `ℚ` has the half-plane `7/8`.** -/
theorem heckeHalfPlane_rat_seven_eighths : HeckeHalfPlane ℚ (7 / 8) := by
  intro 𝔫 φ ρ hρ hρ1
  rw [heckeLFunction_rat_eq_LFunction 𝔫 φ hρ1]
  exact ProbeFinalAssemblyUnconditional.dirichlet_nonzero _ (NeZero.ne _) _ ρ hρ
    fun h => hρ1 h.2

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
