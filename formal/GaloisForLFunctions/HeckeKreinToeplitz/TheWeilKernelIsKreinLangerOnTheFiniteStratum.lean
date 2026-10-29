import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw

/-!
# The Weil kernel is Krein–Langer on the finite stratum

The structure theorem of the finite-support stratum. A kernel is **Krein–Langer**
(`IsKreinLanger`) when it is a positive-definite kernel plus finitely many hyperbolic pairs.

**Decomposition** (`orbitKernel_eq_onLine_add_pairs`). On a tempered configuration with finitely
many zeros right of the line, the Hecke orbit kernel of a real test `f` is
`K = K_{on} + Σ_{ρ right} h_{χ_{ρ̄}, ω̄_ρ}`, `χ_{ρ̄}(u) = u^{ρ̄−1/2}`, `ω_ρ = W_ρ(f, f)`:

* `K_{on}` is the orbit kernel of the on-line zeros (`onLineConfig`), positive definite because that
  configuration has no zero right of the line (`isPosDefKernel_orbitKernel_onLine`);
* each right zero `ρ` and its reflection `1 − ρ̄` give one hyperbolic pair, because the summand at
  `1 − ρ̄` is the conjugate of the summand at `ρ` (`Wsummand_reflect_cx`).

**Krein–Langer class** (`isKreinLanger_orbitKernel_iff`, `isKreinLanger_zetaKernel_iff`). The
orbit kernel is Krein–Langer iff `f` sees finitely many right zeros; for `ζ`, iff finitely many
zeros lie off the line. The finite-support stratum is the Krein–Langer class of the Weil kernel, and
its spectral data are the on-line zeros (positive part) and the right zeros (pairs).
-/

open Complex Finset
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests rightZeros gammaOf_reflect
  summable_Wsummand cx_contDiff cx_hasCompactSupport translate_contDiff translate_hasCompactSupport
  rightZeros_zeta_eq_empty_iff)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros seenConfig
  temperedConfig_seenConfig rightZeros_seenConfig W_translate_seenConfig seenRightZeros_cubicSpline
  rightZeros_zeta_finite_iff_finiteOffLine)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open RHTower.BacklundConverse

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### The Krein–Langer class -/

/-- A **Krein–Langer kernel**: a positive-definite kernel plus finitely many hyperbolic pairs. -/
def IsKreinLanger {G : Type*} [Group G] (k : G → ℂ) : Prop :=
  ∃ p : G → ℂ, IsPosDefKernel p ∧ ∃ (κ : ℕ) (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ),
    k = fun g => p g + ∑ j, pairKernel (χ j) (ω j) g

/-- A Krein–Langer kernel has finite index. -/
theorem IsKreinLanger.negIndex_lt_top {G : Type*} [Group G] {k : G → ℂ} (hk : IsKreinLanger k) :
    negIndex k < ⊤ := by
  obtain ⟨p, hp, κ, χ, ω, rfl⟩ := hk
  exact (negIndex_add_sum_pairKernel_le hp χ ω).trans_lt (ENat.coe_lt_top _)

/-- A finite sum of pairs indexed by a finset is a Krein–Langer kernel plus `p`. -/
theorem isKreinLanger_of_finset {G : Type*} [Group G] {p : G → ℂ} (hp : IsPosDefKernel p)
    {ι : Type*} (R : Finset ι) (χ : ι → G →* ℂ) (ω : ι → ℂ) :
    IsKreinLanger fun g => p g + ∑ i ∈ R, pairKernel (χ i) (ω i) g := by
  refine ⟨p, hp, R.card, fun j => χ (R.equivFin.symm j), fun j => ω (R.equivFin.symm j), ?_⟩
  funext g
  rw [← R.sum_coe_sort, ← R.equivFin.symm.sum_comp]

/-! ### The on-line part of a configuration -/

/-- The configuration of the zeros on the critical line. -/
def onLineConfig (Z : ZeroConfig) : ZeroConfig where
  carrier := {ρ ∈ Z.carrier | ρ.re = 1 / 2}
  mult := Z.mult
  one_le_mult ρ hρ := Z.one_le_mult ρ hρ.1
  strip ρ hρ := Z.strip ρ hρ.1
  reflect_mem ρ hρ := ⟨Z.reflect_mem ρ hρ.1, by
    rw [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hρ.2]; norm_num⟩
  mult_reflect ρ hρ := Z.mult_reflect ρ hρ.1
  finite_window T₁ T₂ := (Z.finite_window T₁ T₂).subset fun _ hρ => ⟨hρ.1.1, hρ.2⟩

theorem temperedConfig_onLineConfig {Z : ZeroConfig} (hZ : TemperedConfig Z) :
    TemperedConfig (onLineConfig Z) :=
  (hZ.comp_injective (Set.inclusion_injective (fun _ h => h.1 :
    (onLineConfig Z).carrier ⊆ Z.carrier))).congr fun _ => rfl

/-- **The on-line part is positive definite**: it has no zero right of the line. -/
theorem isPosDefKernel_orbitKernel_onLine {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : IsPosDefKernel (orbitKernel (onLineConfig Z) f) := by
  refine (isPosDefKernel_iff (isHermKernel_orbitKernel _ _)).mpr ?_
  rw [negIndex_orbitKernel _ (temperedConfig_onLineConfig hZ) hf, Set.encard_eq_zero]
  ext ρ
  simp only [seenRightZeros, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hρ, hre, -⟩
  exact absurd hρ.2 (ne_of_gt hre)

/-! ### The zero sum of the orbit kernel -/

/-- The summand at the reflected zero is the conjugate summand. -/
theorem Wsummand_reflect_cx (Z : ZeroConfig) (f : ℝ → ℝ) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    Z.Wsummand (cx f) (cx f) (reflect ρ) = conj (Z.Wsummand (cx f) (cx f) ρ) := by
  simp only [ZeroConfig.Wsummand, gammaOf_reflect, Z.mult_reflect ρ hρ, map_mul, conj_conj,
    Complex.conj_natCast]
  ring

/-- The summand of the orbit kernel at a zero `ρ`. -/
def orbitTerm (Z : ZeroConfig) (f : ℝ → ℝ) (u : HeckeLattice) (ρ : ℂ) : ℂ :=
  logChar heckeLogScale (1 / 2 - ρ) u * Z.Wsummand (cx f) (cx f) ρ

theorem orbitKernel_eq_tsum (Z : ZeroConfig) (f : ℝ → ℝ) (u : HeckeLattice) :
    orbitKernel Z f u = ∑' ρ : Z.carrier, orbitTerm Z f u ρ := by
  rw [orbitKernel_eq, W_shiftTest_shiftTest]
  refine tsum_congr fun ρ => ?_
  rw [orbitTerm, logChar_apply]
  congr 2
  simp only [Complex.ofReal_zero]
  ring

theorem summable_orbitTerm {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (u : HeckeLattice) :
    Summable fun ρ : Z.carrier => orbitTerm Z f u ρ := by
  have hs := summable_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (translate_contDiff (cx_contDiff hf.1) (scale heckeLogScale u))
    (translate_hasCompactSupport (cx_hasCompactSupport hf.2) (scale heckeLogScale u))
  refine hs.congr fun ρ => ?_
  have h := W_shiftTest_shiftTest Z f 0 (scale heckeLogScale u)
  rw [orbitTerm, logChar_apply, ← ArithmeticOrientationGeometry.cx_scaleShift_eq_translate,
    show cx f = cx (ArithmeticCastelnuovoSeveri.scaleShift 0 f) by
      rw [ArithmeticCastelnuovoSeveri.scaleShift_zero], ArithmeticOrientationGeometry.Wsummand_scaleShift,
    ArithmeticCastelnuovoSeveri.scaleShift_zero]
  congr 2
  simp only [Complex.ofReal_zero]
  ring

/-- A right zero and its reflection give one hyperbolic pair. -/
theorem orbitTerm_add_reflect (Z : ZeroConfig) (f : ℝ → ℝ) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (u : HeckeLattice) :
    orbitTerm Z f u ρ + orbitTerm Z f u (reflect ρ) =
      pairKernel (zeroChar (conj ρ)) (conj (Z.Wsummand (cx f) (cx f) ρ)) u := by
  rw [← pairKernel_reflectChar, reflectChar_logChar, conj_conj, orbitTerm, orbitTerm,
    Wsummand_reflect_cx Z f hρ, pairKernel, reflectChar_logChar]
  have e1 : -conj (conj ρ - 1 / 2) = 1 / 2 - ρ := by
    rw [map_sub, conj_conj, map_div₀, map_one, map_ofNat]; ring
  have e2 : 1 / 2 - reflect ρ = -conj (1 / 2 - ρ) := by
    rw [reflect, map_sub, map_div₀, map_one, map_ofNat]; ring
  rw [e1, e2]
  ring

/-! ### The decomposition -/

/-- **Decomposition of the orbit kernel on the finite stratum.** -/
theorem orbitKernel_eq_onLine_add_pairs {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (hR : (rightZeros Z).Finite) (u : HeckeLattice) :
    orbitKernel Z f u = orbitKernel (onLineConfig Z) f u +
      ∑ ρ ∈ hR.toFinset, pairKernel (zeroChar (conj ρ)) (conj (Z.Wsummand (cx f) (cx f) ρ)) u := by
  classical
  set R := hR.toFinset
  have hRmem : ∀ ρ, ρ ∈ R ↔ ρ ∈ Z.carrier ∧ 1 / 2 < ρ.re := fun ρ => by
    simp [R, rightZeros]
  have hre_reflect : ∀ ρ : ℂ, (reflect ρ).re = 1 - ρ.re := fun ρ => by
    simp [reflect]
  set T := R ∪ R.image reflect
  have hdisjR : Disjoint R (R.image reflect) := by
    rw [disjoint_left]
    intro ρ hρ hρ'
    obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ'
    have h1 := ((hRmem _).mp hρ).2
    have h2 := ((hRmem _).mp hσ).2
    rw [hre_reflect] at h1
    linarith
  -- the pieces of the carrier
  have hsplit : ∀ ρ : ℂ, Z.carrier.indicator (orbitTerm Z f u) ρ =
      (onLineConfig Z).carrier.indicator (orbitTerm Z f u) ρ +
        (T : Set ℂ).indicator (orbitTerm Z f u) ρ := fun ρ => by
    by_cases hc : ρ ∈ Z.carrier
    · rw [Set.indicator_of_mem hc]
      rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
      · have hT : ρ ∈ T := mem_union_right _ (mem_image.mpr ⟨reflect ρ, (hRmem _).mpr
          ⟨Z.reflect_mem ρ hc, by rw [hre_reflect]; linarith⟩, by simp [reflect]⟩)
        rw [Set.indicator_of_notMem (fun h' => absurd h'.2 h.ne),
          Set.indicator_of_mem (by exact_mod_cast hT), zero_add]
      · have hT : ρ ∉ T := by
          intro hT
          rcases mem_union.mp hT with h' | h'
          · exact absurd ((hRmem _).mp h').2 (by rw [h]; exact lt_irrefl _)
          · obtain ⟨σ, hσ, rfl⟩ := mem_image.mp h'
            have := ((hRmem _).mp hσ).2
            rw [hre_reflect] at h
            linarith
        rw [Set.indicator_of_mem (show ρ ∈ (onLineConfig Z).carrier from ⟨hc, h⟩),
          Set.indicator_of_notMem (by exact_mod_cast hT), add_zero]
      · have hT : ρ ∈ T := mem_union_left _ ((hRmem _).mpr ⟨hc, h⟩)
        rw [Set.indicator_of_notMem (fun h' => absurd h'.2 h.ne'),
          Set.indicator_of_mem (by exact_mod_cast hT), zero_add]
    · have hT : ρ ∉ T := by
        intro hT
        rcases mem_union.mp hT with h' | h'
        · exact hc ((hRmem _).mp h').1
        · obtain ⟨σ, hσ, rfl⟩ := mem_image.mp h'
          exact hc (Z.reflect_mem _ ((hRmem _).mp hσ).1)
      rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h' => hc h'.1),
        Set.indicator_of_notMem (by exact_mod_cast hT), add_zero]
  have hsumm : Summable (Z.carrier.indicator (orbitTerm Z f u)) :=
    (summable_subtype_iff_indicator).mp (summable_orbitTerm hZ hf u)
  have hsumm_on : Summable ((onLineConfig Z).carrier.indicator (orbitTerm Z f u)) := by
    have := hsumm.indicator (onLineConfig Z).carrier
    rwa [Set.indicator_indicator, Set.inter_eq_left.mpr (fun _ h => h.1)] at this
  have hsumm_T : Summable ((T : Set ℂ).indicator (orbitTerm Z f u)) :=
    summable_of_ne_finset_zero (s := T) fun ρ hρ => Set.indicator_of_notMem hρ _
  have hterm : orbitTerm (onLineConfig Z) f u = orbitTerm Z f u := rfl
  rw [orbitKernel_eq_tsum, orbitKernel_eq_tsum, hterm, _root_.tsum_subtype, _root_.tsum_subtype,
    tsum_congr hsplit, Summable.tsum_add hsumm_on hsumm_T]
  congr 1
  rw [← _root_.tsum_subtype, Finset.tsum_subtype', sum_union hdisjR,
    sum_image fun _ _ _ _ h => by simpa [reflect] using congrArg conj h, ← sum_add_distrib]
  exact sum_congr rfl fun ρ hρ => orbitTerm_add_reflect Z f ((hRmem ρ).mp hρ).1 u

/-! ### The Krein–Langer class of the orbit kernel -/

/-- **The orbit kernel is Krein–Langer iff the test sees finitely many right zeros.** -/
theorem isKreinLanger_orbitKernel_iff {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : IsKreinLanger (orbitKernel Z f) ↔ (seenRightZeros Z f).Finite := by
  constructor
  · intro h
    have := h.negIndex_lt_top
    rwa [negIndex_orbitKernel Z hZ hf, Set.encard_lt_top_iff] at this
  · intro hfin
    -- pass to the zeros the test sees
    have hseen : orbitKernel Z f = orbitKernel (seenConfig Z f) f := by
      funext u
      rw [orbitKernel_eq, orbitKernel_eq, W_translate_seenConfig]
    have hR : (rightZeros (seenConfig Z f)).Finite := by rwa [rightZeros_seenConfig]
    have hZs := temperedConfig_seenConfig hZ f
    rw [hseen, show orbitKernel (seenConfig Z f) f = fun u => orbitKernel (onLineConfig
      (seenConfig Z f)) f u + ∑ ρ ∈ hR.toFinset, pairKernel (zeroChar (conj ρ))
        (conj ((seenConfig Z f).Wsummand (cx f) (cx f) ρ)) u from
      funext (orbitKernel_eq_onLine_add_pairs hZs hf hR)]
    exact isKreinLanger_of_finset (isPosDefKernel_orbitKernel_onLine hZs hf) _ _ _

/-- **The finite-support stratum of `ζ` is the Krein–Langer class of its Weil kernel.** -/
theorem isKreinLanger_zetaKernel_iff : IsKreinLanger zetaKernel ↔ FiniteOffLine := by
  rw [zetaKernel, isKreinLanger_orbitKernel_iff temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests, seenRightZeros_cubicSpline]
  exact rightZeros_zeta_finite_iff_finiteOffLine

end GaloisForLFunctions.HeckeKreinToeplitz
