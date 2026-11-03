import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.WindowWeilCorePackets
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros

/-!
# Finite core projections and their omitted Weil tail

Real tests in any positive-length window prescribe arbitrary finite upper-resonance
coordinates. This follows from interpolation in an arbitrarily short interval, with conjugate
data at the reflected Fourier nodes `-conj γ`. Thus finite core projections retain every negative PM
direction even when the complete short-window Weil form is coercive.
-/

noncomputable section
open Complex Set MeasureTheory Zeta23
open scoped ComplexConjugate lp
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri
open ArithmeticPolarization SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem paperFT_conj_function (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun u => conj (f u)) z = conj (paperFT f (-conj z)) := by
  unfold paperFT
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

private theorem paperFT_realPart {f : ℝ → ℂ} (hc : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    paperFT (cx (fun u => (f u).re)) z =
      (paperFT f z + conj (paperFT f (-conj z))) / 2 := by
  have he : cx (fun u => (f u).re) = (1 / 2 : ℂ) • (f + fun u => conj (f u)) := by
    funext u
    apply Complex.ext <;>
      simp [cx, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [he, paperFT_smul, paperFT_add (f := f) (g := fun u => conj (f u)) hc hfc (by fun_prop)
    (hfc.comp_left (map_zero (starRingEnd ℂ))), paperFT_conj_function]
  ring

/-- Every finite family of upper-resonance zero coordinates can be prescribed by a real
test in any positive-length window. No critical-line condition is imposed. -/
theorem exists_windowZeroMap_prescribed {A : ℝ} (hA : 0 < A)
    (S : Finset upperMayerResonances) (c : upperMayerResonances → ℂ) :
    ∃ H : windowTests A, ∀ s ∈ S, windowZeroMap A H (upperMayerZero s) = c s := by
  classical
  let q : S → ℂ := fun s => gammaOf (2 * s.1.1)
  have hq : Function.Injective q := by
    intro s t h
    apply Subtype.ext
    apply upperMayerZero_injective
    exact Subtype.ext (gammaOf_injective h)
  have hqpos (s : S) : 0 < (q s).re := by
    have he : (q s).re = 2 * s.1.1.im := by simp [q, gammaOf, Complex.div_I]
    rw [he]
    linarith [s.1.2.1]
  let z : S ⊕ S → ℂ := Sum.elim q (fun s => -conj (q s))
  have hz : Function.Injective z := by
    rintro (s | s) (t | t) h <;> simp only [z, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (hq h)
    · have he := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.conj_re] at he
      linarith [hqpos s, hqpos t]
    · have he := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.conj_re] at he
      linarith [hqpos s, hqpos t]
    · apply congrArg Sum.inr
      apply hq
      have he := congrArg (fun w : ℂ => -conj w) h
      simpa only [map_neg, Complex.conj_conj, neg_neg] using he
  let b : S → ℂ := fun s =>
    Complex.exp ((2 * s.1.1 - 1 / 2) * ((A / 2 : ℝ) : ℂ)) *
      (c s.1 / (Real.sqrt (zetaZeroConfig.mult (2 * s.1.1)) : ℂ))
  let d : S ⊕ S → ℂ := Sum.elim b (fun s => conj (b s))
  let e := Fintype.equivFin (S ⊕ S)
  obtain ⟨f, hf, hsupp, hval⟩ := exists_test_interpolating_Icc
    (a₀ := A / 2) (by linarith) (z ∘ e.symm) (hz.comp e.symm.injective) (d ∘ e.symm)
  have hfc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hsupp
  have hvals (i : S ⊕ S) : paperFT f (z i) = d i := by
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hval (e i)
  let F : ℝ → ℝ := fun u => (f u).re
  have hF : ContDiff ℝ 2 F := Complex.reCLM.contDiff.comp hf
  have hvalues (s : S) : tr (cx F) (2 * s.1.1) = b s := by
    change paperFT (cx (fun u => (f u).re)) (q s) = b s
    rw [paperFT_realPart hf.continuous hfc,
      show paperFT f (q s) = b s from hvals (Sum.inl s),
      show paperFT f (-conj (q s)) = conj (b s) from hvals (Sum.inr s),
      Complex.conj_conj]
    ring
  let H : ℝ → ℝ := fun u => F (u + A / 2)
  have hH : IsWindowTest A H := by
    refine ⟨hF.comp (contDiff_id.add contDiff_const), fun u hu => ?_⟩
    have hn : u + A / 2 ∉ Icc (-(A / 2)) (A / 2) := fun hm =>
      hu ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have hz : f (u + A / 2) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm => hn (hsupp hm))
    simpa only [H, F, Complex.zero_re] using congrArg Complex.re hz
  have hcx : cx H = ArithmeticPolarization.translate (-(A / 2)) (cx F) := by
    funext u
    simp only [cx, H, ArithmeticPolarization.translate, sub_neg_eq_add]
  refine ⟨⟨H, hH⟩, fun s hs => ?_⟩
  let t : S := ⟨s, hs⟩
  have hm : (0 : ℝ) < zetaZeroConfig.mult (2 * s.1) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ (upperMayerZero s).2
  have hw : (Real.sqrt (zetaZeroConfig.mult (2 * s.1)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne'
  rw [windowZeroMap_upperMayerZero, windowMellinPeriod_one _ s.2.2.1 s.2.2.2.1]
  change (Real.sqrt (zetaZeroConfig.mult (2 * s.1)) : ℂ) * tr (cx H) (2 * s.1) = c s
  rw [hcx, tr_translate, show tr (cx F) (2 * s.1) = b t from hvalues t]
  dsimp only [b, t]
  rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  field_simp [hw, Complex.exp_ne_zero]

/-- Every core vector with support in a finite reflection-closed resonance set is the
projection of a real test from any prescribed positive window. -/
theorem exists_windowWeilCorePacket_eq {A : ℝ} (hA : 0 < A)
    (S : Finset upperMayerResonances) (v : mayerPeriodKreinSpace)
    (hv : (mayerPeriodBasis.repr v).support ⊆ pairedMayerResonances S) :
    ∃ H : windowTests A, windowWeilCorePacket S H = v := by
  classical
  obtain ⟨H, hH⟩ := exists_windowZeroMap_prescribed hA (pairedMayerResonances S)
    (mayerPeriodBasis.repr v)
  refine ⟨H, mayerPeriodBasis.repr.injective ?_⟩
  ext s
  rw [repr_windowWeilCorePacket]
  by_cases hs : s ∈ pairedMayerResonances S
  · rw [if_pos hs, hH s hs]
  · rw [if_neg hs]
    symm
    by_contra hn
    exact hs (hv (Finsupp.mem_support_iff.mpr hn))

#print axioms exists_windowZeroMap_prescribed
#print axioms exists_windowWeilCorePacket_eq

/-- Every off-line resonance included in the projection gives an exactly normalized negative
core square, realized by a real test in an arbitrarily short positive window. -/
theorem exists_windowWeilCorePacket_neg_two {A : ℝ} (hA : 0 < A)
    (S : Finset upperMayerResonances) {s : upperMayerResonances} (hs : s ∈ S)
    (hne : s.1.re ≠ 1 / 4) :
    ∃ H : windowTests A,
      mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H) = -2 := by
  classical
  have hsP : s ∈ pairedMayerResonances S := Finset.mem_union_left _ hs
  have hrP : reflectUpperResonance s ∈ pairedMayerResonances S :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hsupport : (mayerPeriodBasis.repr (mayerOffLineNegativeState s)).support ⊆
      pairedMayerResonances S := by
    intro t ht
    by_contra hn
    have hst : s ≠ t := fun h => hn (h ▸ hsP)
    have hrt : reflectUpperResonance s ≠ t := fun h => hn (h ▸ hrP)
    rw [Finsupp.mem_support_iff, mayerOffLineNegativeState, map_sub, Finsupp.sub_apply,
      Module.Basis.repr_self_apply, Module.Basis.repr_self_apply,
      if_neg hst, if_neg hrt, sub_self] at ht
    exact ht rfl
  obtain ⟨H, hH⟩ := exists_windowWeilCorePacket_eq hA S (mayerOffLineNegativeState s) hsupport
  exact ⟨H, by rw [hH, mayerKreinForm_offLineNegativeState_self hne]⟩

/-- Finite core positivity at any positive window is exactly critical-line confinement of
the included resonances. The complete short-window coercivity theorem concerns the full sum. -/
theorem windowWeilCorePacket_nonneg_iff {A : ℝ} (hA : 0 < A)
    (S : Finset upperMayerResonances) :
    (∀ H : windowTests A,
      0 ≤ (mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H)).re) ↔
      ∀ s ∈ S, s.1.re = 1 / 4 := by
  classical
  constructor
  · intro hpos s hs
    by_contra hn
    obtain ⟨H, hH⟩ := exists_windowWeilCorePacket_neg_two hA S hs hn
    have hp := hpos H
    rw [hH] at hp
    norm_num at hp
  · intro hline H
    have hfixed : ∀ s ∈ pairedMayerResonances S, reflectUpperResonance s = s := by
      intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact (reflectUpperResonance_eq_self_iff s).mpr (hline s hs)
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        rw [reflectUpperResonance_involutive,
          (reflectUpperResonance_eq_self_iff t).mpr (hline t ht)]
    have hreflect : mayerKreinReflection (windowWeilCorePacket S H) = windowWeilCorePacket S H := by
      rw [windowWeilCorePacket, map_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [map_smul, mayerKreinReflection_basis, hfixed s hs]
    rw [mayerKreinForm, hreflect]
    exact mayerKreinPosInner_self_re_nonneg _

/-- In a coercive short window the omitted Weil tail must pay for every normalized negative
finite core square. The lower bound includes the native square-mass margin. -/
theorem exists_short_window_core_tail_compensation {A : ℝ} (hA : 0 < A)
    (hshort : A ≤ 1 / 1000) (S : Finset upperMayerResonances)
    {s : upperMayerResonances} (hs : s ∈ S) (hne : s.1.re ≠ 1 / 4) :
    ∃ H : windowTests A,
      mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H) = -2 ∧
        4 + (∫ u : ℝ, ((H : ℝ → ℝ) u) ^ 2) / 4 ≤ weilQuad H -
          2 * (mayerKreinForm (windowWeilCorePacket S H) (windowWeilCorePacket S H)).re := by
  obtain ⟨H, hH⟩ := exists_windowWeilCorePacket_neg_two hA S hs hne
  refine ⟨H, hH, ?_⟩
  have hq := weilQuad_ge_of_short H.2 hA hshort
  rw [hH]
  norm_num
  linarith only [hq]

#print axioms windowWeilCorePacket_nonneg_iff
#print axioms exists_short_window_core_tail_compensation

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
