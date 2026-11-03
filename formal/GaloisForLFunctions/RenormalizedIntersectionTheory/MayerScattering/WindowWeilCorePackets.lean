import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWindowMellinBridge
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerKreinLaxPhillipsRealization
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowRealizations
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle

/-!
# Window Weil coordinates in the actual scattering-core basis

Finite sums of the actual Mayer cores realize the reflection-paired upper-zero sums of the
complete Weil form. Their coefficients are the existing window zero map, equivalently the
normalized source-period evaluations. Window reflection includes conjugation and an exponential
twist. The source Hecke action transports coefficients through the expanded window.
-/

noncomputable section
open Complex Set Filter Topology Zeta23
open scoped ComplexConjugate lp
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The nontrivial zeta zero corresponding to an upper Mayer resonance. -/
def upperMayerZero (s : upperMayerResonances) : zetaZeroConfig.carrier :=
  ⟨2 * s.1, by
    change IsNontrivialZero (2 * s.1)
    refine ⟨(isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2, ?_, ?_⟩
    · simp
      linarith only [s.2.2.1]
    · simp
      linarith only [s.2.2.2.1]⟩

theorem upperMayerZero_injective : Function.Injective upperMayerZero := by
  intro s t h
  apply Subtype.ext
  have he := congrArg (fun z : zetaZeroConfig.carrier => (z : ℂ)) h
  change 2 * s.1 = 2 * t.1 at he
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he

theorem upperMayerZero_reflect (s : upperMayerResonances) :
    upperMayerZero (reflectUpperResonance s) = reflectCarrier zetaZeroConfig (upperMayerZero s) := by
  apply Subtype.ext
  change 2 * riemannMayerReflect s.1 = reflect (2 * s.1)
  simp only [riemannMayerReflect, reflect, map_mul, map_ofNat]
  ring

/-- The existing zero coordinate is evaluation of the actual normalized Lewis period. -/
theorem windowZeroMap_upperMayerZero {A : ℝ} (H : windowTests A) (s : upperMayerResonances) :
    windowZeroMap A H (upperMayerZero s) =
      (Real.sqrt (zetaZeroConfig.mult (2 * s.1)) : ℂ) * windowMellinPeriod H s.1 1 := by
  rw [windowMellinPeriod_one H s.2.2.1 s.2.2.2.1]
  rfl

/-- Close a finite set of resonances under the Riemann–Mayer reflection. -/
def pairedMayerResonances (S : Finset upperMayerResonances) : Finset upperMayerResonances :=
  S ∪ S.image reflectUpperResonance

private theorem mem_pairedMayerResonances_reflect {S : Finset upperMayerResonances}
    {s : upperMayerResonances} (hs : s ∈ pairedMayerResonances S) :
    reflectUpperResonance s ∈ pairedMayerResonances S := by
  classical
  rcases Finset.mem_union.mp hs with hs | hs
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hs
    rw [← he, reflectUpperResonance_involutive]
    exact Finset.mem_union_left _ ht

private theorem mem_pairedMayerResonances_reflect_iff (S : Finset upperMayerResonances)
    (s : upperMayerResonances) :
    reflectUpperResonance s ∈ pairedMayerResonances S ↔ s ∈ pairedMayerResonances S :=
  ⟨fun h => by simpa only [reflectUpperResonance_involutive] using
    mem_pairedMayerResonances_reflect h, mem_pairedMayerResonances_reflect⟩

/-- A finite sum of actual scattering cores with the window's zero coordinates. -/
def windowWeilCorePacket {A : ℝ} (S : Finset upperMayerResonances) (H : windowTests A) :
    mayerPeriodKreinSpace :=
  ∑ s ∈ pairedMayerResonances S, windowZeroMap A H (upperMayerZero s) • mayerPeriodBasis s

theorem repr_windowWeilCorePacket {A : ℝ} (S : Finset upperMayerResonances)
    (H : windowTests A) (s : upperMayerResonances) :
    mayerPeriodBasis.repr (windowWeilCorePacket S H) s =
      if s ∈ pairedMayerResonances S then windowZeroMap A H (upperMayerZero s) else 0 := by
  classical
  rw [windowWeilCorePacket, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply, mul_ite, mul_one, mul_zero]
  simpa only [eq_comm] using Finset.sum_ite_eq (pairedMayerResonances S) s
    (fun t => windowZeroMap A H (upperMayerZero t))

private theorem windowZeroMap_reflected_product {A : ℝ} (H : windowTests A)
    (ρ : zetaZeroConfig.carrier) :
    windowZeroMap A H ρ * conj (windowZeroMap A H (reflectCarrier zetaZeroConfig ρ)) =
      zetaZeroConfig.Wsummand (cx H) (cx H) ρ := by
  have hm := zetaZeroConfig.mult_reflect (ρ : ℂ) ρ.2
  have hsq : (Real.sqrt (zetaZeroConfig.mult ρ) : ℂ) *
      (Real.sqrt (zetaZeroConfig.mult ρ) : ℂ) = (zetaZeroConfig.mult ρ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  change zeroCoord zetaZeroConfig (cx H) ρ *
    conj (zeroCoord zetaZeroConfig (cx H) (reflectCarrier zetaZeroConfig ρ)) = _
  simp only [zeroCoord, reflectCarrier, hm, gammaOf_reflect, map_mul,
    Complex.conj_ofReal, ZeroConfig.Wsummand]
  linear_combination (paperFT (cx H) (gammaOf ρ) *
    conj (paperFT (cx H) (conj (gammaOf ρ)))) * hsq

/-- The PM Krein square is exactly the upper-zero Weil partial sum, with multiplicities.
The vectors consist of actual period cores; the form is the existing PM coefficient form. -/
theorem mayerKreinForm_windowWeilCorePacket {A : ℝ} (S : Finset upperMayerResonances)
    (H : windowTests A) :
    mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H) =
      ∑ s ∈ pairedMayerResonances S, zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1) := by
  classical
  have hsupp : (mayerPeriodBasis.repr (windowWeilCorePacket S H)).support ⊆
      pairedMayerResonances S := by
    intro s hs
    by_contra hn
    rw [Finsupp.mem_support_iff, repr_windowWeilCorePacket, if_neg hn] at hs
    exact hs rfl
  rw [mayerKreinForm, mayerKreinPosInner_eq_sum_of_subset hsupp]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [repr_mayerKreinReflection, repr_windowWeilCorePacket, if_pos hs,
    repr_windowWeilCorePacket, if_pos (mem_pairedMayerResonances_reflect hs),
    upperMayerZero_reflect]
  exact windowZeroMap_reflected_product H (upperMayerZero s)

/-- On the actual core coordinates, window reflection is the conjugate-linear twisted PM
reflection, rather than the linear PM reflection alone. -/
theorem repr_windowWeilCorePacket_reflection {A : ℝ} (S : Finset upperMayerResonances)
    (H : windowTests A) (s : upperMayerResonances) :
    mayerPeriodBasis.repr (windowWeilCorePacket S
      ⟨windowInvolution A H, H.2.windowInvolution⟩) s =
      Complex.exp (-(A : ℂ) * (2 * s.1 - 1 / 2)) *
        conj (mayerPeriodBasis.repr (mayerKreinReflection (windowWeilCorePacket S H)) s) := by
  classical
  rw [repr_mayerKreinReflection, repr_windowWeilCorePacket, repr_windowWeilCorePacket]
  by_cases hs : s ∈ pairedMayerResonances S
  · rw [if_pos hs, if_pos (mem_pairedMayerResonances_reflect hs),
      windowZeroMap_upperMayerZero, windowZeroMap_upperMayerZero,
      windowMellinPeriod_krein_reflection_one A H s.2.2.1 s.2.2.2.1]
    have hm : zetaZeroConfig.mult (2 * (reflectUpperResonance s).1) =
        zetaZeroConfig.mult (2 * s.1) := by
      change zetaZeroConfig.mult (upperMayerZero (reflectUpperResonance s)) =
        zetaZeroConfig.mult (upperMayerZero s)
      rw [upperMayerZero_reflect]
      exact zetaZeroConfig.mult_reflect _ (upperMayerZero s).2
    rw [hm, map_mul, Complex.conj_ofReal, reflectUpperResonance_coe]
    ring
  · rw [if_neg hs, if_neg (fun h => hs ((mem_pairedMayerResonances_reflect_iff S s).mp h)),
      map_zero, mul_zero]

/-- The expanded-window pull multiplies each core coefficient by the source Hecke eigenvalue
minus one. The actual period equation is `lewisHeckeT2_windowMellinPeriod`. -/
theorem repr_windowWeilCorePacket_hecke {A : ℝ} (S : Finset upperMayerResonances)
    (H : windowTests A) (s : upperMayerResonances) :
    mayerPeriodBasis.repr (windowWeilCorePacket S
      ⟨heckeWindowPull H, heckeWindowPull_mem H.2⟩) s =
      (2 * (2 : ℂ) ^ (-(2 * s.1))) * mayerPeriodBasis.repr (windowWeilCorePacket S H) s := by
  classical
  rw [repr_windowWeilCorePacket, repr_windowWeilCorePacket]
  by_cases hs : s ∈ pairedMayerResonances S
  · rw [if_pos hs, if_pos hs, windowZeroMap_upperMayerZero, windowZeroMap_upperMayerZero,
      windowMellinPeriod_one _ s.2.2.1 s.2.2.2.1,
      windowMellinPeriod_one _ s.2.2.1 s.2.2.2.1]
    change (Real.sqrt (zetaZeroConfig.mult (2 * s.1)) : ℂ) *
      tr (fun u => (heckeWindowPull H u : ℂ)) (2 * s.1) = _
    rw [tr_heckeWindowPull]
    ring
  · rw [if_neg hs, if_neg hs, mul_zero]

private def upperMayerOfZero (ρ : zetaZeroConfig.carrier) (hρ : 0 < (ρ : ℂ).im) :
    upperMayerResonances :=
  ⟨(ρ : ℂ) / 2, by
    have h0 : 0 < ((ρ : ℂ) / 2).re := by simp; linarith [ρ.2.2.1]
    have h1 : ((ρ : ℂ) / 2).re < 1 / 2 := by simp; linarith [ρ.2.2.2]
    refine ⟨by simp; linarith, (isMayerScatteringResonance_iff_zeta_zero h0 h1).mpr ?_⟩
    rw [show 2 * ((ρ : ℂ) / 2) = ρ by ring]
    exact ρ.2.1⟩

private theorem upperMayerZero_ofZero (ρ : zetaZeroConfig.carrier) (hρ : 0 < (ρ : ℂ).im) :
    upperMayerZero (upperMayerOfZero ρ hρ) = ρ := by
  apply Subtype.ext
  change 2 * ((ρ : ℂ) / 2) = ρ
  ring

private theorem upperMayerZero_im_pos (s : upperMayerResonances) :
    0 < (upperMayerZero s : ℂ).im := by
  change 0 < (2 * s.1).im
  simp
  linarith only [s.2.1]

private def signedMayerZero : upperMayerResonances ⊕ upperMayerResonances → zetaZeroConfig.carrier
  | Sum.inl s => upperMayerZero s
  | Sum.inr s => conjEquiv fesSymmetric_zetaZeroConfig (upperMayerZero s)

private theorem signedMayerZero_bijective : Function.Bijective signedMayerZero := by
  constructor
  · intro x y h
    cases x with
    | inl s =>
      cases y with
      | inl t => exact congrArg Sum.inl (upperMayerZero_injective h)
      | inr t =>
        have he := congrArg (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) h
        change (upperMayerZero s : ℂ).im =
          (conjEquiv fesSymmetric_zetaZeroConfig (upperMayerZero t) : ℂ).im at he
        rw [conjEquiv_apply, Complex.conj_im] at he
        linarith [upperMayerZero_im_pos s, upperMayerZero_im_pos t]
    | inr s =>
      cases y with
      | inl t =>
        have he := congrArg (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) h
        change (conjEquiv fesSymmetric_zetaZeroConfig (upperMayerZero s) : ℂ).im =
          (upperMayerZero t : ℂ).im at he
        rw [conjEquiv_apply, Complex.conj_im] at he
        linarith [upperMayerZero_im_pos s, upperMayerZero_im_pos t]
      | inr t =>
        exact congrArg Sum.inr
          (upperMayerZero_injective ((conjEquiv fesSymmetric_zetaZeroConfig).injective h))
  · intro ρ
    by_cases hp : 0 < (ρ : ℂ).im
    · exact ⟨Sum.inl (upperMayerOfZero ρ hp), upperMayerZero_ofZero ρ hp⟩
    · have hn : (ρ : ℂ).im < 0 :=
        (lt_or_eq_of_le (le_of_not_gt hp)).resolve_right (zetaZeroConfig_im_ne_zero' ρ ρ.2)
      have hc : 0 < (conjEquiv fesSymmetric_zetaZeroConfig ρ : ℂ).im := by
        rw [conjEquiv_apply, Complex.conj_im]
        linarith
      refine ⟨Sum.inr (upperMayerOfZero (conjEquiv fesSymmetric_zetaZeroConfig ρ) hc), ?_⟩
      change conjEquiv fesSymmetric_zetaZeroConfig
        (upperMayerZero (upperMayerOfZero (conjEquiv fesSymmetric_zetaZeroConfig ρ) hc)) = ρ
      rw [upperMayerZero_ofZero]
      apply Subtype.ext
      rw [conjEquiv_apply, conjEquiv_apply, Complex.conj_conj]

private def signedMayerZeroEquiv :
    upperMayerResonances ⊕ upperMayerResonances ≃ zetaZeroConfig.carrier :=
  Equiv.ofBijective signedMayerZero signedMayerZero_bijective

private theorem window_upperMayer_sum_summable {A : ℝ} (H : windowTests A) :
    Summable (fun s : upperMayerResonances =>
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) := by
  have h : Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand (cx H) (cx H) ρ) :=
    summable_Wsummand zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
  exact h.comp_injective (i := upperMayerZero) upperMayerZero_injective

/-- The complete real Weil form is twice the real part of the upper-resonance sum.
Conjugation pairs the two half planes; the zeta configuration has no real zeros. -/
theorem weilQuad_eq_twice_upperMayer_sum {A : ℝ} (H : windowTests A) :
    weilQuad H = 2 * (∑' s : upperMayerResonances,
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)).re := by
  let f : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand (cx H) (cx H) ρ
  have hall : Summable f := summable_Wsummand zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
  have hu : Summable (fun s => f (signedMayerZero (Sum.inl s))) :=
    hall.comp_injective upperMayerZero_injective
  have hl : Summable (fun s => f (signedMayerZero (Sum.inr s))) :=
    hall.comp_injective ((conjEquiv fesSymmetric_zetaZeroConfig).injective.comp
      upperMayerZero_injective)
  have hsplit : zetaZeroConfig.W (cx H) (cx H) =
      (∑' s : upperMayerResonances, f (upperMayerZero s)) +
        conj (∑' s : upperMayerResonances, f (upperMayerZero s)) := by
    calc
      zetaZeroConfig.W (cx H) (cx H) = ∑' x, f (signedMayerZero x) :=
        (signedMayerZeroEquiv.tsum_eq f).symm
      _ = (∑' s, f (upperMayerZero s)) +
          ∑' s, f (conjEquiv fesSymmetric_zetaZeroConfig (upperMayerZero s)) :=
        Summable.tsum_sum hu hl
      _ = _ := by
        rw [Complex.conj_tsum]
        congr 1
        refine tsum_congr fun s => ?_
        change zetaZeroConfig.Wsummand (cx H) (cx H)
          (conjEquiv fesSymmetric_zetaZeroConfig (upperMayerZero s)) = _
        rw [conjEquiv_apply]
        exact (conj_Wsummand_ofReal zetaZeroConfig fesSymmetric_zetaZeroConfig
          H H (upperMayerZero s).2).symm
  rw [LogCells.weilQuad_eq_zetaW H.2.contDiff H.2.hasCompactSupport]
  change (zetaZeroConfig.W (cx H) (cx H)).re = _
  rw [hsplit, Complex.add_re, Complex.conj_re]
  exact (two_mul _).symm

/-- The complete Weil energy is the limit of twice the actual finite-core Krein squares.
Reflection-closed finite sets exhaust the upper resonances, and absolute summability controls
the limit. No positivity assertion enters this identification. -/
theorem tendsto_mayerKreinForm_windowWeilCorePacket {A : ℝ} (H : windowTests A) :
    Tendsto (fun S : Finset upperMayerResonances =>
      2 * (mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H)).re)
      atTop (𝓝 (weilQuad H)) := by
  classical
  have hcofinal : Tendsto pairedMayerResonances atTop atTop := by
    refine tendsto_atTop.mpr fun S => eventually_atTop.mpr ⟨S, fun T hT => ?_⟩
    exact hT.trans Finset.subset_union_left
  have hsum : Tendsto (fun S : Finset upperMayerResonances =>
      ∑ s ∈ S, zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) atTop
      (𝓝 (∑' s : upperMayerResonances, zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1))) :=
    (window_upperMayer_sum_summable H).hasSum
  have hre := (Complex.continuous_re.tendsto _).comp (hsum.comp hcofinal)
  have hout : Tendsto (fun S : Finset upperMayerResonances =>
      2 * (∑ s ∈ pairedMayerResonances S,
        zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)).re) atTop
      (𝓝 (2 * (∑' s : upperMayerResonances,
        zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)).re)) :=
    tendsto_const_nhds.mul hre
  simpa only [mayerKreinForm_windowWeilCorePacket, weilQuad_eq_twice_upperMayer_sum] using hout

#print axioms mayerKreinForm_windowWeilCorePacket
#print axioms repr_windowWeilCorePacket_reflection
#print axioms repr_windowWeilCorePacket_hecke
#print axioms weilQuad_eq_twice_upperMayer_sum
#print axioms tendsto_mayerKreinForm_windowWeilCorePacket

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
