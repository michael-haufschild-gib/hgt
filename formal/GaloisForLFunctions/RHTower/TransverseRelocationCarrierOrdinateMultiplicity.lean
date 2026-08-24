import GaloisForLFunctions.RHTower.ReflectedGammaQuartetMultiplicity
import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification
import GaloisForLFunctions.RHTower.DeckChargeInvariant
import GaloisForLFunctions.RHTower.TransverseRelocationCarrierAnalyticCompletion
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Exact ordinate-multiplicity measure and positive-density relocation

This leaf defines the analytic zero-divisor mass on one ordinate and in a finite height band,
proves product additivity, transports it under horizontal translation, and applies it to the
reflected-Gamma/Cosh carrier. It also classifies and counts the complete off-critical lattice,
with a uniform `O(1)` error from its `4 T / π` main term.
-/

open Complex Set

namespace RHTower

noncomputable section

def analyticZeroOrdinateFiber (f : ℂ → ℂ) (y : ℝ) : Set ℂ :=
  {z | f z = 0 ∧ z.im = y}

def analyticZeroOrdinateMass (f : ℂ → ℂ) (y : ℝ)
    (hfin : (analyticZeroOrdinateFiber f y).Finite) : ENat :=
  ∑ z ∈ hfin.toFinset, analyticOrderAt f z

theorem analyticZeroOrdinateMass_congr
    {f g : ℂ → ℂ} (hfg : f = g) (y : ℝ)
    (hf : (analyticZeroOrdinateFiber f y).Finite)
    (hg : (analyticZeroOrdinateFiber g y).Finite) :
    analyticZeroOrdinateMass f y hf = analyticZeroOrdinateMass g y hg := by
  subst g
  rfl

theorem analyticZeroOrdinateFiber_mul (f g : ℂ → ℂ) (y : ℝ) :
    analyticZeroOrdinateFiber (f * g) y =
      analyticZeroOrdinateFiber f y ∪ analyticZeroOrdinateFiber g y := by
  ext z
  simp only [analyticZeroOrdinateFiber, Set.mem_setOf_eq, Pi.mul_apply,
    mul_eq_zero, Set.mem_union]
  aesop

theorem analyticZeroOrdinateFiber_mul_finite
    {f g : ℂ → ℂ} {y : ℝ}
    (hf : (analyticZeroOrdinateFiber f y).Finite)
    (hg : (analyticZeroOrdinateFiber g y).Finite) :
    (analyticZeroOrdinateFiber (f * g) y).Finite := by
  rw [analyticZeroOrdinateFiber_mul]
  exact hf.union hg

theorem analyticZeroOrdinateMass_mul
    {f g : ℂ → ℂ} {y : ℝ}
    (hfAnalytic : ∀ z, AnalyticAt ℂ f z)
    (hgAnalytic : ∀ z, AnalyticAt ℂ g z)
    (hf : (analyticZeroOrdinateFiber f y).Finite)
    (hg : (analyticZeroOrdinateFiber g y).Finite) :
    analyticZeroOrdinateMass (f * g) y
        (analyticZeroOrdinateFiber_mul_finite hf hg) =
      analyticZeroOrdinateMass f y hf + analyticZeroOrdinateMass g y hg := by
  classical
  unfold analyticZeroOrdinateMass
  have hfinset :
      (analyticZeroOrdinateFiber_mul_finite hf hg).toFinset =
        hf.toFinset ∪ hg.toFinset := by
    ext z
    constructor
    · intro hz
      have hzSet : z ∈ analyticZeroOrdinateFiber (f * g) y :=
        (analyticZeroOrdinateFiber_mul_finite hf hg).mem_toFinset.mp hz
      have hzUnion : z ∈ analyticZeroOrdinateFiber f y ∪
          analyticZeroOrdinateFiber g y := by
        rw [← analyticZeroOrdinateFiber_mul]
        exact hzSet
      exact Finset.mem_union.mpr (hzUnion.elim
        (fun h ↦ Or.inl (hf.mem_toFinset.mpr h))
        (fun h ↦ Or.inr (hg.mem_toFinset.mpr h)))
    · intro hz
      have hzUnion : z ∈ analyticZeroOrdinateFiber f y ∪
          analyticZeroOrdinateFiber g y :=
        (Finset.mem_union.mp hz).elim
          (fun h ↦ Or.inl (hf.mem_toFinset.mp h))
          (fun h ↦ Or.inr (hg.mem_toFinset.mp h))
      apply (analyticZeroOrdinateFiber_mul_finite hf hg).mem_toFinset.mpr
      rw [analyticZeroOrdinateFiber_mul]
      exact hzUnion
  rw [hfinset]
  have horder : ∀ z, analyticOrderAt (f * g) z =
      analyticOrderAt f z + analyticOrderAt g z := by
    intro z
    exact analyticOrderAt_mul (hfAnalytic z) (hgAnalytic z)
  simp_rw [horder, Finset.sum_add_distrib]
  congr 1
  · symm
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzUnion hzNot
    have hnotzero : f z ≠ 0 := by
      intro hz
      apply hzNot
      rw [hf.mem_toFinset]
      exact ⟨hz, (Finset.mem_union.mp hzUnion).elim
        (fun h ↦ (hf.mem_toFinset.mp h).2)
        (fun h ↦ (hg.mem_toFinset.mp h).2)⟩
    exact (hfAnalytic z).analyticOrderAt_eq_zero.mpr hnotzero
  · symm
    apply Finset.sum_subset Finset.subset_union_right
    intro z hzUnion hzNot
    have hnotzero : g z ≠ 0 := by
      intro hz
      apply hzNot
      rw [hg.mem_toFinset]
      exact ⟨hz, (Finset.mem_union.mp hzUnion).elim
        (fun h ↦ (hf.mem_toFinset.mp h).2)
        (fun h ↦ (hg.mem_toFinset.mp h).2)⟩
    exact (hgAnalytic z).analyticOrderAt_eq_zero.mpr hnotzero

theorem reflectedGammaCarrier_zeroOrdinateFiber_finite (beta y : ℝ) :
    (analyticZeroOrdinateFiber (reflectedGammaCarrier beta) y).Finite := by
  refine (Set.finite_singleton (Complex.I * (y : ℂ))).subset ?_
  intro z hz
  rw [Set.mem_singleton_iff]
  apply Complex.ext
  · have hre := reflectedGammaCarrier_zero_re_eq_zero hz.1
    simpa using hre
  · simpa using hz.2

theorem coshQuartetEnvelope_zeroOrdinateFiber_finite (a y : ℝ) :
    (analyticZeroOrdinateFiber (coshQuartetEnvelope a) y).Finite := by
  let p : ℂ := (a : ℂ) + Complex.I * (y : ℂ)
  let q : ℂ := -(a : ℂ) + Complex.I * (y : ℂ)
  refine (Set.finite_singleton q).insert p |>.subset ?_
  intro z hz
  have hreSq := coshQuartetEnvelope_zero_re_sq hz.1
  have hre : z.re = a ∨ z.re = -a :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hreSq
  rcases hre with hre | hre
  · have hzEq : z = p := by
      apply Complex.ext
      · simpa [p] using hre
      · simpa [p] using hz.2
    simp [hzEq]
  · have hzEq : z = q := by
      apply Complex.ext
      · simpa [q] using hre
      · simpa [q] using hz.2
    simp [hzEq]

theorem reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite
    (beta a y : ℝ) :
    (analyticZeroOrdinateFiber (reflectedGammaQuartetCarrier beta a) y).Finite := by
  exact analyticZeroOrdinateFiber_mul_finite
    (reflectedGammaCarrier_zeroOrdinateFiber_finite beta y)
    (coshQuartetEnvelope_zeroOrdinateFiber_finite a y)

def reflectedGammaQuartetCarrier_zeroOrdinateMass
    (beta a y : ℝ) : ENat :=
  analyticZeroOrdinateMass (reflectedGammaQuartetCarrier beta a) y
    (reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite beta a y)

def coshQuartetEnvelope_zeroOrdinateMass (a y : ℝ) : ENat :=
  analyticZeroOrdinateMass (coshQuartetEnvelope a) y
    (coshQuartetEnvelope_zeroOrdinateFiber_finite a y)

theorem coshQuartetEnvelope_zeroOrdinateFiber_zero_eq_singleton
    {y : ℝ} (hy : coshQuartetEnvelope 0 (Complex.I * (y : ℂ)) = 0) :
    analyticZeroOrdinateFiber (coshQuartetEnvelope 0) y =
      {Complex.I * (y : ℂ)} := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_singleton_iff]
    apply Complex.ext
    · simpa using coshQuartetEnvelope_zero_re_eq_zero_of_eq_zero hz.1
    · simpa using hz.2
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hy, by simp⟩

theorem coshQuartetEnvelope_zeroOrdinateFiber_zero_eq_empty
    {y : ℝ} (hy : coshQuartetEnvelope 0 (Complex.I * (y : ℂ)) ≠ 0) :
    analyticZeroOrdinateFiber (coshQuartetEnvelope 0) y = ∅ := by
  ext z
  constructor
  · intro hz
    exfalso
    apply hy
    have hzEq : z = Complex.I * (y : ℂ) := by
      apply Complex.ext
      · simpa using coshQuartetEnvelope_zero_re_eq_zero_of_eq_zero hz.1
      · simpa using hz.2
    simpa [hzEq] using hz.1
  · intro hz
    exact hz.elim

theorem coshQuartetEnvelope_zeroOrdinateFiber_eq_pair
    {a y : ℝ}
    (hy : coshQuartetEnvelope 0 (Complex.I * (y : ℂ)) = 0) :
    analyticZeroOrdinateFiber (coshQuartetEnvelope a) y =
      {(a : ℂ) + Complex.I * (y : ℂ),
        -(a : ℂ) + Complex.I * (y : ℂ)} := by
  let p : ℂ := (a : ℂ) + Complex.I * (y : ℂ)
  let q : ℂ := -(a : ℂ) + Complex.I * (y : ℂ)
  have hcosh : Complex.cosh (Complex.I * (y : ℂ)) = 0 := by
    have hsq : Complex.cosh (Complex.I * (y : ℂ)) *
        Complex.cosh (Complex.I * (y : ℂ)) = 0 := by
      simpa [coshQuartetEnvelope] using hy
    exact (mul_eq_zero.mp hsq).elim id id
  have hp : coshQuartetEnvelope a p = 0 := by
    unfold coshQuartetEnvelope
    have hpSub : p - (a : ℂ) = Complex.I * (y : ℂ) := by
      simp [p]
    rw [hpSub, hcosh, zero_mul]
  have hq : coshQuartetEnvelope a q = 0 := by
    unfold coshQuartetEnvelope
    have hqAdd : q + (a : ℂ) = Complex.I * (y : ℂ) := by
      simp [q]
    rw [hqAdd, hcosh, mul_zero]
  ext z
  constructor
  · intro hz
    have hreSq := coshQuartetEnvelope_zero_re_sq hz.1
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hreSq with hre | hre
    · left
      apply Complex.ext
      · simpa [p] using hre
      · simpa [p] using hz.2
    · right
      rw [Set.mem_singleton_iff]
      apply Complex.ext
      · simpa [q] using hre
      · simpa [q] using hz.2
  · intro hz
    rcases hz with hz | hz
    · subst z
      exact ⟨hp, by simp⟩
    · rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hq, by simp⟩

theorem coshQuartetEnvelope_zeroOrdinateFiber_eq_empty
    {a y : ℝ}
    (hy : coshQuartetEnvelope 0 (Complex.I * (y : ℂ)) ≠ 0) :
    analyticZeroOrdinateFiber (coshQuartetEnvelope a) y = ∅ := by
  ext z
  constructor
  · intro hz
    exfalso
    obtain ⟨w, hw, hwIm⟩ :=
      (coshQuartetEnvelope_zero_im_iff_zero_im_zero a y).mp ⟨z, hz.1, hz.2⟩
    apply hy
    have hwEq : w = Complex.I * (y : ℂ) := by
      apply Complex.ext
      · simpa using coshQuartetEnvelope_zero_re_eq_zero_of_eq_zero hw
      · simpa using hwIm
    simpa [hwEq] using hw
  · intro hz
    exact hz.elim

theorem coshQuartetEnvelope_zeroOrdinateMass_eq
    {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    coshQuartetEnvelope_zeroOrdinateMass a y =
      coshQuartetEnvelope_zeroOrdinateMass 0 y := by
  classical
  let p : ℂ := (a : ℂ) + Complex.I * (y : ℂ)
  let q : ℂ := -(a : ℂ) + Complex.I * (y : ℂ)
  by_cases hy : coshQuartetEnvelope 0 (Complex.I * (y : ℂ)) = 0
  · have hpair := coshQuartetEnvelope_zeroOrdinateFiber_eq_pair (a := a) hy
    have hsingle := coshQuartetEnvelope_zeroOrdinateFiber_zero_eq_singleton hy
    unfold coshQuartetEnvelope_zeroOrdinateMass analyticZeroOrdinateMass
    have haFinset :
        (coshQuartetEnvelope_zeroOrdinateFiber_finite a y).toFinset = {p, q} := by
      ext z
      rw [(coshQuartetEnvelope_zeroOrdinateFiber_finite a y).mem_toFinset]
      simpa [p, q] using Set.ext_iff.mp hpair z
    have hzeroFinset :
        (coshQuartetEnvelope_zeroOrdinateFiber_finite 0 y).toFinset =
          {Complex.I * (y : ℂ)} := by
      ext z
      rw [(coshQuartetEnvelope_zeroOrdinateFiber_finite 0 y).mem_toFinset]
      simpa using Set.ext_iff.mp hsingle z
    have hp : coshQuartetEnvelope a p = 0 := by
      have hpMem : p ∈ analyticZeroOrdinateFiber (coshQuartetEnvelope a) y := by
        rw [hpair]
        simp [p]
      exact hpMem.1
    have hq : coshQuartetEnvelope a q = 0 := by
      have hqMem : q ∈ analyticZeroOrdinateFiber (coshQuartetEnvelope a) y := by
        rw [hpair]
        simp [q]
      exact hqMem.1
    have hpq : p ≠ q := by
      intro hpq
      have hre := congrArg Complex.re hpq
      simp [p, q] at hre
      exact ha (by linarith)
    rw [haFinset, hzeroFinset]
    simp [hpq, analyticOrderAt_coshQuartetEnvelope_eq_one_of_eq_zero ha hp,
      analyticOrderAt_coshQuartetEnvelope_eq_one_of_eq_zero ha hq,
      analyticOrderAt_coshQuartetEnvelope_zero_eq_two hy]
    norm_num
  · have haEmpty := coshQuartetEnvelope_zeroOrdinateFiber_eq_empty (a := a) hy
    have hzeroEmpty := coshQuartetEnvelope_zeroOrdinateFiber_zero_eq_empty hy
    unfold coshQuartetEnvelope_zeroOrdinateMass analyticZeroOrdinateMass
    have haFinset :
        (coshQuartetEnvelope_zeroOrdinateFiber_finite a y).toFinset = ∅ := by
      ext z
      rw [(coshQuartetEnvelope_zeroOrdinateFiber_finite a y).mem_toFinset]
      simpa using Set.ext_iff.mp haEmpty z
    have hzeroFinset :
        (coshQuartetEnvelope_zeroOrdinateFiber_finite 0 y).toFinset = ∅ := by
      ext z
      rw [(coshQuartetEnvelope_zeroOrdinateFiber_finite 0 y).mem_toFinset]
      simpa using Set.ext_iff.mp hzeroEmpty z
    rw [haFinset, hzeroFinset]
    simp

theorem reflectedGammaQuartetCarrier_zeroOrdinateMass_eq_gamma_add_cosh
    (beta a y : ℝ) :
    reflectedGammaQuartetCarrier_zeroOrdinateMass beta a y =
      analyticZeroOrdinateMass (reflectedGammaCarrier beta) y
          (reflectedGammaCarrier_zeroOrdinateFiber_finite beta y) +
        coshQuartetEnvelope_zeroOrdinateMass a y := by
  unfold reflectedGammaQuartetCarrier_zeroOrdinateMass
    coshQuartetEnvelope_zeroOrdinateMass
  change analyticZeroOrdinateMass
      (reflectedGammaCarrier beta * coshQuartetEnvelope a) y _ = _
  exact analyticZeroOrdinateMass_mul
    (fun z ↦ reflectedGammaCarrier_analyticOnNhd beta z (by simp))
    (fun z ↦ coshQuartetEnvelope_analyticAt a z)
    (reflectedGammaCarrier_zeroOrdinateFiber_finite beta y)
    (coshQuartetEnvelope_zeroOrdinateFiber_finite a y)

theorem reflectedGammaQuartetCarrier_zeroOrdinateMass_eq
    (beta : ℝ) {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    reflectedGammaQuartetCarrier_zeroOrdinateMass beta a y =
      reflectedGammaQuartetCarrier_zeroOrdinateMass beta 0 y := by
  rw [reflectedGammaQuartetCarrier_zeroOrdinateMass_eq_gamma_add_cosh,
    reflectedGammaQuartetCarrier_zeroOrdinateMass_eq_gamma_add_cosh,
    coshQuartetEnvelope_zeroOrdinateMass_eq ha y]

def realHorizontalTranslate (f : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  f (z - (c : ℂ))

theorem analyticZeroOrdinateFiber_realHorizontalTranslate
    (f : ℂ → ℂ) (c y : ℝ) :
    analyticZeroOrdinateFiber (realHorizontalTranslate f c) y =
      (fun z : ℂ ↦ z + (c : ℂ)) '' analyticZeroOrdinateFiber f y := by
  ext z
  constructor
  · intro hz
    refine ⟨z - (c : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact hz.1
    · simpa using hz.2
    · ring
  · rintro ⟨w, hw, rfl⟩
    constructor
    · simpa [realHorizontalTranslate] using hw.1
    · simpa using hw.2

theorem analyticZeroOrdinateFiber_realHorizontalTranslate_finite
    {f : ℂ → ℂ} {c y : ℝ}
    (hf : (analyticZeroOrdinateFiber f y).Finite) :
    (analyticZeroOrdinateFiber (realHorizontalTranslate f c) y).Finite := by
  rw [analyticZeroOrdinateFiber_realHorizontalTranslate]
  exact hf.image _

theorem analyticZeroOrdinateMass_realHorizontalTranslate
    {f : ℂ → ℂ} {c y : ℝ}
    (hf : (analyticZeroOrdinateFiber f y).Finite) :
    analyticZeroOrdinateMass (realHorizontalTranslate f c) y
        (analyticZeroOrdinateFiber_realHorizontalTranslate_finite (c := c) hf) =
      analyticZeroOrdinateMass f y hf := by
  classical
  unfold analyticZeroOrdinateMass
  have hfinset :
      (analyticZeroOrdinateFiber_realHorizontalTranslate_finite (c := c) hf).toFinset =
        hf.toFinset.image (fun z : ℂ ↦ z + (c : ℂ)) := by
    ext z
    rw [(analyticZeroOrdinateFiber_realHorizontalTranslate_finite (c := c) hf).mem_toFinset,
      Finset.mem_image]
    rw [analyticZeroOrdinateFiber_realHorizontalTranslate]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hf.mem_toFinset.mpr hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hf.mem_toFinset.mp hw, rfl⟩
  rw [hfinset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [show realHorizontalTranslate f c =
        fun w : ℂ ↦ f (w + -(c : ℂ)) by
      funext w
      rw [realHorizontalTranslate, sub_eq_add_neg]]
    simpa using analyticOrderAt_comp_add f (-(c : ℂ)) (z + (c : ℂ))
  · intro z _ w _ hzw
    apply add_right_cancel hzw

theorem transverseRelocationCarrier_eq_realHorizontalTranslate (beta a : ℝ) :
    transverseRelocationCarrier beta a =
      realHorizontalTranslate (reflectedGammaQuartetCarrier beta a) (1 / 2) := by
  funext z
  simp [transverseRelocationCarrier, realHorizontalTranslate]

theorem transverseRelocationCarrier_zeroOrdinateFiber_finite
    (beta a y : ℝ) :
    (analyticZeroOrdinateFiber (transverseRelocationCarrier beta a) y).Finite := by
  rw [transverseRelocationCarrier_eq_realHorizontalTranslate]
  exact analyticZeroOrdinateFiber_realHorizontalTranslate_finite (c := (1 / 2 : ℝ))
    (reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite beta a y)

def transverseRelocationCarrier_zeroOrdinateMass (beta a y : ℝ) : ENat :=
  analyticZeroOrdinateMass (transverseRelocationCarrier beta a) y
    (transverseRelocationCarrier_zeroOrdinateFiber_finite beta a y)

theorem transverseRelocationCarrier_zeroOrdinateMass_eq_centered
    (beta a y : ℝ) :
    transverseRelocationCarrier_zeroOrdinateMass beta a y =
      reflectedGammaQuartetCarrier_zeroOrdinateMass beta a y := by
  unfold transverseRelocationCarrier_zeroOrdinateMass
    reflectedGammaQuartetCarrier_zeroOrdinateMass
  calc
    analyticZeroOrdinateMass (transverseRelocationCarrier beta a) y
        (transverseRelocationCarrier_zeroOrdinateFiber_finite beta a y) =
      analyticZeroOrdinateMass
          (realHorizontalTranslate (reflectedGammaQuartetCarrier beta a) (1 / 2)) y
          (analyticZeroOrdinateFiber_realHorizontalTranslate_finite
            (c := (1 / 2 : ℝ))
            (reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite beta a y)) :=
        analyticZeroOrdinateMass_congr
          (transverseRelocationCarrier_eq_realHorizontalTranslate beta a) y _ _
    _ = analyticZeroOrdinateMass (reflectedGammaQuartetCarrier beta a) y
          (reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite beta a y) :=
      analyticZeroOrdinateMass_realHorizontalTranslate
        (c := (1 / 2 : ℝ))
        (reflectedGammaQuartetCarrier_zeroOrdinateFiber_finite beta a y)

theorem transverseRelocationCarrier_zeroOrdinateMass_eq
    (beta : ℝ) {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    transverseRelocationCarrier_zeroOrdinateMass beta a y =
      transverseRelocationCarrier_zeroOrdinateMass beta 0 y := by
  rw [transverseRelocationCarrier_zeroOrdinateMass_eq_centered,
    transverseRelocationCarrier_zeroOrdinateMass_eq_centered,
    reflectedGammaQuartetCarrier_zeroOrdinateMass_eq beta ha y]

def analyticZeroHeightBand (f : ℂ → ℂ) (T : ℝ) : Set ℂ :=
  {z | f z = 0 ∧ |z.im| ≤ T}

def analyticZeroHeightBandMass (f : ℂ → ℂ) (T : ℝ)
    (hfin : (analyticZeroHeightBand f T).Finite) : ENat :=
  ∑ z ∈ hfin.toFinset, analyticOrderAt f z

theorem transverseRelocationCarrier_zero_abs_re_le
    {beta a : ℝ} {s : ℂ} (hs : transverseRelocationCarrier beta a s = 0) :
    |s.re| ≤ |a| + 1 := by
  change reflectedGammaCarrier beta (s - (1 / 2 : ℂ)) *
      coshQuartetEnvelope a (s - (1 / 2 : ℂ)) = 0 at hs
  rcases mul_eq_zero.mp hs with hgamma | hcosh
  · have hre := reflectedGammaCarrier_zero_re_eq_zero hgamma
    have hsRe : s.re = 1 / 2 := by
      have hre' : s.re - 1 / 2 = 0 := by simpa using hre
      linarith
    rw [hsRe]
    have haNonneg : 0 ≤ |a| := abs_nonneg a
    norm_num
    linarith
  · have hreSq := coshQuartetEnvelope_zero_re_sq hcosh
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hreSq with hre | hre
    · have hsRe : s.re = a + 1 / 2 := by
        have hre' : s.re - 1 / 2 = a := by simpa using hre
        linarith
      rw [hsRe]
      calc
        |a + 1 / 2| ≤ |a| + |(1 / 2 : ℝ)| := by
          simpa only [Real.norm_eq_abs] using norm_add_le a (1 / 2 : ℝ)
        _ ≤ |a| + 1 := by norm_num
    · have hsRe : s.re = -a + 1 / 2 := by
        have hre' : s.re - 1 / 2 = -a := by simpa using hre
        linarith
      rw [hsRe]
      calc
        |-a + 1 / 2| ≤ |-a| + |(1 / 2 : ℝ)| := by
          simpa only [Real.norm_eq_abs] using norm_add_le (-a) (1 / 2 : ℝ)
        _ ≤ |a| + 1 := by norm_num

theorem transverseRelocationCarrier_zero_norm_le
    {beta a T : ℝ} {s : ℂ} (hs : transverseRelocationCarrier beta a s = 0)
    (hT : |s.im| ≤ T) :
    ‖s‖ ≤ |a| + 1 + T := by
  have hsSplit : s = (s.re : ℂ) + Complex.I * (s.im : ℂ) := by
    apply Complex.ext <;> simp
  calc
    ‖s‖ = ‖(s.re : ℂ) + Complex.I * (s.im : ℂ)‖ := congrArg norm hsSplit
    _ ≤ ‖(s.re : ℂ)‖ + ‖Complex.I * (s.im : ℂ)‖ := norm_add_le _ _
    _ = |s.re| + |s.im| := by simp
    _ ≤ (|a| + 1) + T :=
      add_le_add (transverseRelocationCarrier_zero_abs_re_le hs) hT

theorem transverseRelocationCarrier_zeroHeightBand_finite
    {beta a T : ℝ} (hbeta : 0 < beta) (hT : 0 ≤ T) :
    (analyticZeroHeightBand (transverseRelocationCarrier beta a) T).Finite := by
  let R : ℝ := |a| + 1 + T
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hanalytic := transverseRelocationCarrier_analyticOnNhd beta a
  have hdiff : DifferentiableOn ℂ (transverseRelocationCarrier beta a) Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hanalytic).differentiableOn
  have hiso : ∀ z ∈ (Set.univ : Set ℂ),
      ¬ (∀ᶠ w in nhds z, transverseRelocationCarrier beta a w = 0) := by
    intro z _ hzero
    have hEq : Set.EqOn (transverseRelocationCarrier beta a) 0 Set.univ :=
      hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (by simp) hzero
    exact transverseRelocationCarrier_ne_zero_half hbeta a (hEq (by simp))
  have hcompactFinite :
      (Metric.closedBall (0 : ℂ) R ∩
        {z | transverseRelocationCarrier beta a z = 0}).Finite :=
    GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact
      isOpen_univ hdiff hiso (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)
  refine hcompactFinite.subset ?_
  intro z hz
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact transverseRelocationCarrier_zero_norm_le hz.1 hz.2
  · exact hz.1

def transverseRelocationCarrier_zeroHeightBandMass
    (beta a T : ℝ) (hbeta : 0 < beta) (hT : 0 ≤ T) : ENat :=
  analyticZeroHeightBandMass (transverseRelocationCarrier beta a) T
    (transverseRelocationCarrier_zeroHeightBand_finite hbeta hT)

def coshOddIndexHeightBand (T : ℝ) : Finset ℤ :=
  let N : ℕ := ⌈T / Real.pi + 1⌉₊
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter fun k ↦
    |((2 * (k : ℝ) + 1) * Real.pi / 2)| ≤ T

theorem mem_coshOddIndexHeightBand_iff
    {T : ℝ} (hT : 0 ≤ T) (k : ℤ) :
    k ∈ coshOddIndexHeightBand T ↔
      |((2 * (k : ℝ) + 1) * Real.pi / 2)| ≤ T := by
  classical
  let x : ℝ := T / Real.pi
  let N : ℕ := ⌈x + 1⌉₊
  have hx : 0 ≤ x := div_nonneg hT Real.pi_pos.le
  have hx1 : 0 ≤ x + 1 := by positivity
  have hN : x + 1 ≤ (N : ℝ) := Nat.le_ceil _
  change k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter _ ↔ _
  rw [Finset.mem_filter]
  constructor
  · exact fun hk ↦ hk.2
  · intro hk
    refine ⟨Finset.mem_Icc.mpr ?_, hk⟩
    have hscale :
        |((2 * (k : ℝ) + 1) * Real.pi / 2)| =
          |2 * (k : ℝ) + 1| * Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [hscale] at hk
    have habs : |2 * (k : ℝ) + 1| ≤ 2 * x := by
      rw [show 2 * x = (2 * T) / Real.pi by
        dsimp [x]
        ring]
      apply (le_div_iff₀ Real.pi_pos).2
      nlinarith
    have hkBounds := abs_le.mp habs
    have hkLower : -(N : ℝ) ≤ (k : ℝ) := by
      nlinarith
    have hkUpper : (k : ℝ) ≤ (N : ℝ) := by
      nlinarith
    constructor
    · exact_mod_cast hkLower
    · exact_mod_cast hkUpper

def coshQuartetLatticePoint (a : ℝ) (positiveLine : Bool) (k : ℤ) : ℂ :=
  (if positiveLine then (a : ℂ) else -(a : ℂ)) -
    ((2 * (k : ℂ) + 1) * Real.pi / 2) * Complex.I

def transverseOffCriticalLatticePoint
    (a : ℝ) (positiveLine : Bool) (k : ℤ) : ℂ :=
  coshQuartetLatticePoint a positiveLine k + (1 / 2 : ℂ)

theorem coshQuartetEnvelope_coshQuartetLatticePoint_zero
    (a : ℝ) (positiveLine : Bool) (k : ℤ) :
    coshQuartetEnvelope a (coshQuartetLatticePoint a positiveLine k) = 0 := by
  cases positiveLine
  · apply coshQuartetEnvelope_eq_zero_iff.mpr
    right
    exact ⟨k, by simp [coshQuartetLatticePoint]⟩
  · apply coshQuartetEnvelope_eq_zero_iff.mpr
    left
    exact ⟨k, by simp [coshQuartetLatticePoint]⟩

theorem transverseRelocationCarrier_offCriticalLatticePoint_zero
    (beta a : ℝ) (positiveLine : Bool) (k : ℤ) :
    transverseRelocationCarrier beta a
      (transverseOffCriticalLatticePoint a positiveLine k) = 0 := by
  unfold transverseRelocationCarrier transverseOffCriticalLatticePoint
  have harg : coshQuartetLatticePoint a positiveLine k + (1 / 2 : ℂ) - 1 / 2 =
      coshQuartetLatticePoint a positiveLine k := by ring
  rw [harg]
  unfold reflectedGammaQuartetCarrier
  rw [coshQuartetEnvelope_coshQuartetLatticePoint_zero, mul_zero]

theorem transverseOffCriticalLatticePoint_re
    (a : ℝ) (positiveLine : Bool) (k : ℤ) :
    (transverseOffCriticalLatticePoint a positiveLine k).re =
      1 / 2 + if positiveLine then a else -a := by
  cases positiveLine <;> simp [transverseOffCriticalLatticePoint,
    coshQuartetLatticePoint] <;> ring

theorem transverseOffCriticalLatticePoint_im
    (a : ℝ) (positiveLine : Bool) (k : ℤ) :
    (transverseOffCriticalLatticePoint a positiveLine k).im =
      -((2 * (k : ℝ) + 1) * Real.pi / 2) := by
  cases positiveLine <;> simp [transverseOffCriticalLatticePoint,
    coshQuartetLatticePoint]

theorem transverseOffCriticalLatticePoint_injective
    {a : ℝ} (ha : a ≠ 0) :
    Function.Injective
      (fun p : Bool × ℤ ↦ transverseOffCriticalLatticePoint a p.1 p.2) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  cases b <;> cases c
  · have hklReal : (k : ℝ) = (l : ℝ) := by
      simp only [transverseOffCriticalLatticePoint_im] at him
      nlinarith [Real.pi_pos]
    have hkl : k = l := by exact_mod_cast hklReal
    simp [hkl]
  · simp only [transverseOffCriticalLatticePoint_re] at hre
    simp at hre
    exact (ha (by linarith)).elim
  · simp only [transverseOffCriticalLatticePoint_re] at hre
    simp at hre
    exact (ha (by linarith)).elim
  · have hklReal : (k : ℝ) = (l : ℝ) := by
      simp only [transverseOffCriticalLatticePoint_im] at him
      nlinarith [Real.pi_pos]
    have hkl : k = l := by exact_mod_cast hklReal
    simp [hkl]

def transverseOffCriticalLatticeFinset (a T : ℝ) : Finset ℂ :=
  (Finset.univ.product (coshOddIndexHeightBand T)).image
    (fun p : Bool × ℤ ↦ transverseOffCriticalLatticePoint a p.1 p.2)

def transverseOffCriticalZeroHeightBand
    (beta a T : ℝ) : Set ℂ :=
  {s | transverseRelocationCarrier beta a s = 0 ∧
    s.re ≠ 1 / 2 ∧ |s.im| ≤ T}

theorem transverseOffCriticalZeroHeightBand_finite
    {beta a T : ℝ} (hbeta : 0 < beta) (hT : 0 ≤ T) :
    (transverseOffCriticalZeroHeightBand beta a T).Finite := by
  refine (transverseRelocationCarrier_zeroHeightBand_finite
    (a := a) hbeta hT).subset ?_
  intro s hs
  exact ⟨hs.1, hs.2.2⟩

theorem transverseOffCriticalZeroHeightBand_toFinset_eq_lattice
    (beta : ℝ) {a T : ℝ} (ha : a ≠ 0) (hbeta : 0 < beta) (hT : 0 ≤ T) :
    (transverseOffCriticalZeroHeightBand_finite
        (a := a) hbeta hT).toFinset =
      transverseOffCriticalLatticeFinset a T := by
  classical
  ext s
  rw [(transverseOffCriticalZeroHeightBand_finite
    (a := a) hbeta hT).mem_toFinset]
  constructor
  · intro hs
    let z : ℂ := s - (1 / 2 : ℂ)
    have hzRe : z.re ≠ 0 := by
      intro hz
      apply hs.2.1
      have : s.re - 1 / 2 = 0 := by simpa [z] using hz
      linarith
    have hzZero : reflectedGammaQuartetCarrier beta a z = 0 := by
      simpa [z, transverseRelocationCarrier] using hs.1
    have hcosh : coshQuartetEnvelope a z = 0 :=
      (reflectedGammaQuartetCarrier_offCentral_zero_iff hzRe).mp hzZero
    rcases coshQuartetEnvelope_eq_zero_iff.mp hcosh with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hsPoint : s = transverseOffCriticalLatticePoint a true k := by
        unfold transverseOffCriticalLatticePoint coshQuartetLatticePoint
        rw [if_pos rfl]
        dsimp [z] at hk
        linear_combination hk
      rw [transverseOffCriticalLatticeFinset, Finset.mem_image]
      refine ⟨(true, k), ?_, hsPoint.symm⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, (mem_coshOddIndexHeightBand_iff hT k).mpr ?_⟩
      simpa [hsPoint, transverseOffCriticalLatticePoint_im] using hs.2.2
    · have hsPoint : s = transverseOffCriticalLatticePoint a false k := by
        unfold transverseOffCriticalLatticePoint coshQuartetLatticePoint
        rw [if_neg Bool.false_ne_true]
        dsimp [z] at hk
        linear_combination hk
      rw [transverseOffCriticalLatticeFinset, Finset.mem_image]
      refine ⟨(false, k), ?_, hsPoint.symm⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, (mem_coshOddIndexHeightBand_iff hT k).mpr ?_⟩
      simpa [hsPoint, transverseOffCriticalLatticePoint_im] using hs.2.2
  · intro hs
    rw [transverseOffCriticalLatticeFinset, Finset.mem_image] at hs
    rcases hs with ⟨⟨b, k⟩, hk, rfl⟩
    have hkBand := (mem_coshOddIndexHeightBand_iff hT k).mp
      (Finset.mem_product.mp hk).2
    constructor
    · exact transverseRelocationCarrier_offCriticalLatticePoint_zero beta a b k
    · constructor
      · rw [transverseOffCriticalLatticePoint_re]
        cases b <;> simp [ha]
      · rw [transverseOffCriticalLatticePoint_im]
        simpa only [abs_neg] using hkBand

def transverseOffCriticalZeroHeightCount
    (beta a T : ℝ) (hbeta : 0 < beta) (hT : 0 ≤ T) : ℕ :=
  (transverseOffCriticalZeroHeightBand_finite
    (a := a) hbeta hT).toFinset.card

theorem transverseOffCriticalZeroHeightCount_eq_two_mul_indexCard
    (beta : ℝ) {a T : ℝ} (ha : a ≠ 0) (hbeta : 0 < beta) (hT : 0 ≤ T) :
    transverseOffCriticalZeroHeightCount beta a T hbeta hT =
      2 * (coshOddIndexHeightBand T).card := by
  unfold transverseOffCriticalZeroHeightCount
  rw [transverseOffCriticalZeroHeightBand_toFinset_eq_lattice beta ha hbeta hT,
    transverseOffCriticalLatticeFinset,
    (Finset.card_image_iff.mpr
      (transverseOffCriticalLatticePoint_injective ha).injOn)]
  simp

theorem coshOddIndexHeightBand_card_le
    {T : ℝ} (hT : 0 ≤ T) :
    ((coshOddIndexHeightBand T).card : ℝ) ≤
      2 * (T / Real.pi) + 5 := by
  let x : ℝ := T / Real.pi
  let N : ℕ := ⌈x + 1⌉₊
  have hx : 0 ≤ x := div_nonneg hT Real.pi_pos.le
  have hx1 : 0 ≤ x + 1 := by positivity
  have hsubset : coshOddIndexHeightBand T ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hcard := Finset.card_le_card hsubset
  have hIccCard :
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    have htoNat : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    exact htoNat
  rw [hIccCard] at hcard
  have hNlt : (N : ℝ) < x + 2 := by
    have hceil := Nat.ceil_lt_add_one hx1
    change (N : ℝ) < (x + 1) + 1 at hceil
    linarith
  have hcardReal : ((coshOddIndexHeightBand T).card : ℝ) ≤
      ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  dsimp [x] at hNlt ⊢
  norm_num at hcardReal ⊢
  linarith

theorem coshOddIndexHeightBand_card_ge
    {T : ℝ} (hT : Real.pi ≤ T) :
    2 * (T / Real.pi) - 2 ≤
      ((coshOddIndexHeightBand T).card : ℝ) := by
  let x : ℝ := T / Real.pi
  let M : ℕ := ⌊x⌋₊
  have hx : 0 ≤ x := by
    exact div_nonneg (le_trans Real.pi_pos.le hT) Real.pi_pos.le
  have hxOne : 1 ≤ x := by
    rw [le_div_iff₀ Real.pi_pos]
    simpa using hT
  have hMpos : 1 ≤ M := by
    apply Nat.le_floor
    exact_mod_cast hxOne
  have hMle : (M : ℝ) ≤ x := Nat.floor_le hx
  have hsubset : Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1) ⊆
      coshOddIndexHeightBand T := by
    intro k hk
    apply (mem_coshOddIndexHeightBand_iff
      (le_trans Real.pi_pos.le hT) k).mpr
    have hkIcc := Finset.mem_Icc.mp hk
    have hkLower : -(M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkIcc.1
    have hkUpper : (k : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast hkIcc.2
    have habs : |2 * (k : ℝ) + 1| ≤ 2 * x := by
      rw [abs_le]
      constructor <;> nlinarith
    have hscale :
        |((2 * (k : ℝ) + 1) * Real.pi / 2)| =
          |2 * (k : ℝ) + 1| * Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [hscale]
    have hxT : x * Real.pi = T := by
      dsimp [x]
      field_simp [Real.pi_ne_zero]
    nlinarith [Real.pi_pos]
  have hcard := Finset.card_le_card hsubset
  have hIccCard :
      (Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1)).card = 2 * M := by
    rw [Int.card_Icc]
    have htoNat : (((M : ℤ) - 1) + 1 - -(M : ℤ)).toNat = 2 * M := by
      omega
    exact htoNat
  rw [hIccCard] at hcard
  have hxLt : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcardReal : ((2 * M : ℕ) : ℝ) ≤
      ((coshOddIndexHeightBand T).card : ℝ) := by
    exact_mod_cast hcard
  dsimp [x] at hxLt ⊢
  norm_num at hcardReal ⊢
  linarith

theorem transverseOffCriticalZeroHeightCount_error_le_ten
    (beta : ℝ) {a T : ℝ} (ha : a ≠ 0) (hbeta : 0 < beta)
    (hT : Real.pi ≤ T) :
    |↑(transverseOffCriticalZeroHeightCount beta a T hbeta
          (le_trans Real.pi_pos.le hT)) - 4 * T / Real.pi| ≤ 10 := by
  have hcount := transverseOffCriticalZeroHeightCount_eq_two_mul_indexCard
    beta ha hbeta (le_trans Real.pi_pos.le hT)
  have hlower := coshOddIndexHeightBand_card_ge hT
  have hupper := coshOddIndexHeightBand_card_le (le_trans Real.pi_pos.le hT)
  have hcountReal :
      (↑(transverseOffCriticalZeroHeightCount beta a T hbeta
        (le_trans Real.pi_pos.le hT)) : ℝ) =
        2 * ((coshOddIndexHeightBand T).card : ℝ) := by
    exact_mod_cast hcount
  rw [show 4 * T / Real.pi = 4 * (T / Real.pi) by ring]
  rw [abs_le]
  constructor
  · rw [hcountReal]
    nlinarith
  · rw [hcountReal]
    nlinarith

theorem transverseOffCriticalZeroHeightCount_positiveDensity
    (beta : ℝ) {a T : ℝ} (ha : a ≠ 0) (hbeta : 0 < beta)
    (hT : 2 * Real.pi ≤ T) :
    (2 / Real.pi) * T ≤
      ↑(transverseOffCriticalZeroHeightCount beta a T hbeta
        (le_trans (by positivity) hT)) := by
  have hpiT : Real.pi ≤ T := le_trans (by linarith [Real.pi_pos]) hT
  have hcount := transverseOffCriticalZeroHeightCount_eq_two_mul_indexCard
    beta ha hbeta (le_trans Real.pi_pos.le hpiT)
  have hlower := coshOddIndexHeightBand_card_ge hpiT
  have hTdiv : 2 ≤ T / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    simpa [mul_comm] using hT
  have hcountReal :
      (↑(transverseOffCriticalZeroHeightCount beta a T hbeta
        (le_trans (by positivity) hT)) : ℝ) =
        2 * ((coshOddIndexHeightBand T).card : ℝ) := by
    exact_mod_cast hcount
  rw [show (2 / Real.pi) * T = 2 * (T / Real.pi) by ring, hcountReal]
  nlinarith

theorem analyticZeroHeightBandMass_eq_sum_ordinate
    {f : ℂ → ℂ} {T : ℝ}
    (hband : (analyticZeroHeightBand f T).Finite)
    (hfiber : ∀ y, (analyticZeroOrdinateFiber f y).Finite) :
    analyticZeroHeightBandMass f T hband =
      ∑ y ∈ hband.toFinset.image Complex.im,
        analyticZeroOrdinateMass f y (hfiber y) := by
  classical
  unfold analyticZeroHeightBandMass
  calc
    (∑ z ∈ hband.toFinset, analyticOrderAt f z) =
        ∑ y ∈ hband.toFinset.image Complex.im,
          ∑ z ∈ hband.toFinset.filter (fun z ↦ z.im = y), analyticOrderAt f z := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun z hz ↦ Finset.mem_image_of_mem Complex.im hz) _
    _ = ∑ y ∈ hband.toFinset.image Complex.im,
        analyticZeroOrdinateMass f y (hfiber y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨z₀, hz₀, rfl⟩
      have hz₀Band := hband.mem_toFinset.mp hz₀
      unfold analyticZeroOrdinateMass
      apply Finset.sum_congr
      · ext z
        rw [Finset.mem_filter, (hfiber z₀.im).mem_toFinset]
        constructor
        · rintro ⟨hz, him⟩
          exact ⟨(hband.mem_toFinset.mp hz).1, him⟩
        · rintro ⟨hz, him⟩
          apply And.intro
          · apply hband.mem_toFinset.mpr
            exact ⟨hz, by simpa [him] using hz₀Band.2⟩
          · exact him
      · intro z hz
        rfl

theorem transverseRelocationCarrier_zeroHeightBand_ordinateFinset_eq
    (beta : ℝ) {a T : ℝ} (hbeta : 0 < beta) (hT : 0 ≤ T) :
    (transverseRelocationCarrier_zeroHeightBand_finite
        (a := a) hbeta hT).toFinset.image Complex.im =
      (transverseRelocationCarrier_zeroHeightBand_finite
        (a := 0) hbeta hT).toFinset.image Complex.im := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    have hzBand := (transverseRelocationCarrier_zeroHeightBand_finite
      (a := a) hbeta hT).mem_toFinset.mp hz
    obtain ⟨w, hw, hwIm⟩ :=
      (transverseRelocationCarrier_zero_im_iff_zero_im beta a 0 z.im).mp
        ⟨z, hzBand.1, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, hwIm⟩
    apply (transverseRelocationCarrier_zeroHeightBand_finite
      (a := 0) hbeta hT).mem_toFinset.mpr
    exact ⟨hw, by simpa [hwIm] using hzBand.2⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    have hzBand := (transverseRelocationCarrier_zeroHeightBand_finite
      (a := 0) hbeta hT).mem_toFinset.mp hz
    obtain ⟨w, hw, hwIm⟩ :=
      (transverseRelocationCarrier_zero_im_iff_zero_im beta 0 a z.im).mp
        ⟨z, hzBand.1, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, hwIm⟩
    apply (transverseRelocationCarrier_zeroHeightBand_finite
      (a := a) hbeta hT).mem_toFinset.mpr
    exact ⟨hw, by simpa [hwIm] using hzBand.2⟩

theorem transverseRelocationCarrier_zeroHeightBandMass_eq
    (beta : ℝ) {a T : ℝ} (ha : a ≠ 0) (hbeta : 0 < beta) (hT : 0 ≤ T) :
    transverseRelocationCarrier_zeroHeightBandMass beta a T hbeta hT =
      transverseRelocationCarrier_zeroHeightBandMass beta 0 T hbeta hT := by
  classical
  unfold transverseRelocationCarrier_zeroHeightBandMass
  rw [analyticZeroHeightBandMass_eq_sum_ordinate,
    analyticZeroHeightBandMass_eq_sum_ordinate,
    transverseRelocationCarrier_zeroHeightBand_ordinateFinset_eq beta hbeta hT]
  apply Finset.sum_congr rfl
  intro y hy
  simpa [transverseRelocationCarrier_zeroOrdinateMass] using
    transverseRelocationCarrier_zeroOrdinateMass_eq beta ha y

end
end RHTower
