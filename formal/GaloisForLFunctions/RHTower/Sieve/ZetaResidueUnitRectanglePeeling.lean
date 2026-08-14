import GaloisForLFunctions.RHTower.FinitePeeling
import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegular
import GaloisForLFunctions.HTGeometry.SmoothWeightInversion
import Mathlib.Order.Interval.Set.Infinite

/-!
# Exact zeta-residue-unit zero extraction on a rectangle

The entire residue unit `G(s) = (s - 1) * ζ(s)` has only finitely many zeros in any closed
rectangle.  Peeling exactly that finite packet gives a cofactor nonzero on the rectangle.  The
local weighted argument principle then extracts the exact analytic-multiplicity-weighted zero sum
for any weight analytic near the rectangle.

This removes the zero-free-rectangle premise from the regular `-ζ'/ζ` contour: crossing zeros costs
the explicit finite residue sum and nothing else.  No infinite zero sum is used.
-/

open Complex Filter intervalIntegral Set Topology

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The regularized residue unit is analytic on the whole complex plane. -/
theorem zetaResidueUnit_analyticOnNhd_univ :
    AnalyticOnNhd ℂ zetaResidueUnit Set.univ :=
  fun z _ => analyticAt_zetaResidueUnit z

/-- The residue unit has finite analytic order at every point because it is entire and takes the
nonzero value `1` at `s = 1`. -/
theorem zetaResidueUnit_order_ne_top (z : ℂ) :
    analyticOrderAt zetaResidueUnit z ≠ ⊤ := by
  intro htop
  have hevent : zetaResidueUnit =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
  have heq : Set.EqOn zetaResidueUnit 0 (Set.univ : Set ℂ) :=
    zetaResidueUnit_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hevent
  have hone := heq (Set.mem_univ (1 : ℂ))
  rw [zetaResidueUnit_one] at hone
  norm_num at hone

/-- The zeros of the residue unit in any closed coordinate rectangle form a finite set. -/
theorem zetaResidueUnit_zeros_closedRectangle_finite (z₁ z₂ : ℂ) :
    {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) |
      zetaResidueUnit z = 0}.Finite := by
  have hcod : (zetaResidueUnit ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    zetaResidueUnit_analyticOnNhd_univ.preimage_zero_mem_codiscreteWithin
      (x := 1) (by rw [zetaResidueUnit_one]; norm_num) (Set.mem_univ 1) isConnected_univ
  have hcodK : (zetaResidueUnit ⁻¹' {0}ᶜ) ∈ codiscreteWithin
      (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_sdiff_of_mem_codiscreteWithin
    hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- The finite set of distinct residue-unit zeros in a closed coordinate rectangle. -/
def zetaResidueUnitClosedRectangleZeros (z₁ z₂ : ℂ) : Finset ℂ :=
  (zetaResidueUnit_zeros_closedRectangle_finite z₁ z₂).toFinset

@[simp] theorem mem_zetaResidueUnitClosedRectangleZeros {z₁ z₂ z : ℂ} :
    z ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂ ↔
      z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ∧
        zetaResidueUnit z = 0 := by
  rw [zetaResidueUnitClosedRectangleZeros, Set.Finite.mem_toFinset, Set.mem_sep_iff]

/-- **Exact closed-rectangle residue-unit factorization.**  Peeling every distinct zero in the
rectangle produces its exact analytic multiplicity and an entire cofactor nonvanishing throughout
the closed rectangle. -/
theorem exists_zetaResidueUnit_closedRectangle_factorization (z₁ z₂ : ℂ) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h Set.univ ∧
      (∀ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        m w = (analyticOrderAt zetaResidueUnit w).toNat) ∧
      (∀ z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im), h z ≠ 0) ∧
      ∀ z : ℂ, zetaResidueUnit z =
        (∏ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂, (z - w) ^ m w) * h z := by
  obtain ⟨m, h, hhan, hm, hh0, hfact⟩ := exists_finite_peel isOpen_univ
    zetaResidueUnit_analyticOnNhd_univ (zetaResidueUnitClosedRectangleZeros z₁ z₂)
      (by simp) (fun w _ => zetaResidueUnit_order_ne_top w)
  refine ⟨m, h, hhan, hm, ?_, fun z => hfact z (Set.mem_univ z)⟩
  intro z hzK hhzero
  have hG0 : zetaResidueUnit z = 0 := by
    rw [hfact z (Set.mem_univ z), hhzero, mul_zero]
  exact hh0 z (mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨hzK, hG0⟩) hhzero

/-- **Multiplicity-exact weighted argument principle for the residue unit.**  If the residue unit
is nonzero on the boundary of a positively oriented rectangle, integrating any locally analytic
weight against `G'/G` extracts precisely all enclosed zeros with analytic multiplicity. -/
theorem rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum
    {g : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => g z * logDeriv zetaResidueUnit z) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w := by
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_zetaResidueUnit_closedRectangle_factorization z₁ z₂
  let V : Set ℂ := U ∩ {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hVopen : IsOpen V := by
    apply hUopen.inter
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hsubV : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ V :=
    fun z hz => ⟨hsub hz, hhK z hz⟩
  have hin : ∀ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_zetaResidueUnitClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hre.le] at hwre
    rw [uIcc_of_le him.le] at hwim
    have hrel : z₁.re < w.re := by
      have hne : z₁.re ≠ w.re := by
        intro heq
        have hedge : (z₁.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneG := hleft w.im hwimU
        rw [hedge] at hneG
        exact hneG hwzero
      exact lt_of_le_of_ne hwre.1 hne
    have hrer : w.re < z₂.re := by
      have hne : w.re ≠ z₂.re := by
        intro heq
        have hedge : (z₂.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneG := hright w.im hwimU
        rw [hedge] at hneG
        exact hneG hwzero
      exact lt_of_le_of_ne hwre.2 hne
    have himl : z₁.im < w.im := by
      have hne : z₁.im ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₁.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneG := hbot w.re hwreU
        rw [hedge] at hneG
        exact hneG hwzero
      exact lt_of_le_of_ne hwim.1 hne
    have himr : w.im < z₂.im := by
      have hne : w.im ≠ z₂.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₂.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneG := htop w.re hwreU
        rw [hedge] at hneG
        exact hneG hwzero
      exact lt_of_le_of_ne hwim.2 hne
    exact ⟨hrel, hrer, himl, himr⟩
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    (zetaResidueUnitClosedRectangleZeros z₁ z₂) (fun w => w) m
      (f := zetaResidueUnit) (g := g) (h := h) (z₁ := z₁) (z₂ := z₂) (U := V)
      hVopen (hg.mono (fun _ hz => hz.1)) hin hsubV
      (hhan.mono (fun _ _ => Set.mem_univ _)) (fun _ hz => hz.2)
      (fun z _ => hfact z)
  calc
    rectIntegral (fun z => g z * logDeriv zetaResidueUnit z) z₁ z₂ =
        2 * Real.pi * I * ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
          (m w : ℂ) * g w := by
      simpa only using hres
    _ = 2 * Real.pi * I * ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hm w hw]

/-- **The regular `-ζ'/ζ` rectangle identity.**  Crossing the zeros of the entire residue unit
contributes the negative analytic-multiplicity-weighted zero sum. -/
theorem rectIntegral_mul_zetaLogDerivReg_eq_neg_closedRectangleZeroSum
    {g : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => g z * zetaLogDerivReg z) z₁ z₂ =
      -(2 * Real.pi * I * ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) := by
  have hpos := rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum
    hUopen hg hsub hre him hbot htop hright hleft
  have hfun : (fun z => g z * zetaLogDerivReg z) =
      fun z => (-1 : ℂ) * (g z * logDeriv zetaResidueUnit z) := by
    funext z
    rw [zetaLogDerivReg]
    ring
  rw [hfun, rectIntegral_const_mul, hpos]
  ring

/-- The Mellin transform of the Route T smooth cutoff is analytic on the full open right half-plane.
This is the maximal domain needed by a contour whose left edge remains to the right of zero. -/
theorem analyticOnNhd_mellin_smoothWeight_re_pos {N H : ℝ} (hH : 0 < H) :
    AnalyticOnNhd ℂ
      (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)))
      {s : ℂ | 0 < s.re} := by
  have hdiff : DifferentiableOn ℂ
      (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)))
      {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (differentiableAt_mellin_smoothWeight hH hs).differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- **Multiplicity-exact smoothed Chebyshev zero-crossing formula.**  On any positive-real-part
rectangle avoiding residue-unit zeros on its boundary, the regular part of `-ζ'/ζ` weighted by the
actual Route T cutoff Mellin transform is exactly the negative finite zero packet. -/
theorem rectIntegral_mellin_smoothWeight_mul_zetaLogDerivReg_eq_neg_zeroSum
    {N H : ℝ} (hH : 0 < H) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.re) (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral
        (fun z => mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) z *
          zetaLogDerivReg z) z₁ z₂ =
      -(2 * Real.pi * I * ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) w) := by
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      {s : ℂ | 0 < s.re} := by
    intro z hz
    obtain ⟨hzre, _⟩ := Complex.mem_reProdIm.mp hz
    rw [uIcc_of_le hre.le] at hzre
    exact lt_of_lt_of_le hz₁ hzre.1
  exact rectIntegral_mul_zetaLogDerivReg_eq_neg_closedRectangleZeroSum
    (isOpen_lt continuous_const Complex.continuous_re)
    (analyticOnNhd_mellin_smoothWeight_re_pos hH) hsub hre him
    hbot htop hright hleft

/-- **Contour-shift form of the smoothed zero-crossing identity.**  This is the exact replacement
for `integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_rect`: without a zero-free rectangle, its
right side is the negative finite multiplicity-weighted zeta-zero packet. -/
theorem integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_sub_zeroSum
    {N H : ℝ} (hH : 0 < H) {c d T : ℝ}
    (hc : 0 < c) (hcd : c < d) (hT : 0 < T)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + (y : ℝ) * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * I) ≠ 0) :
    I • (∫ y : ℝ in (-T)..T,
          zetaLogDerivReg ((d : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * I))
      - I • (∫ y : ℝ in (-T)..T,
          zetaLogDerivReg ((c : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * I))
      - ((∫ x : ℝ in c..d,
          zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * I) *
            mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        - ∫ x : ℝ in c..d,
          zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
            mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      -(2 * Real.pi * I *
        ∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + ((-T : ℝ) : ℂ) * I)
            ((d : ℂ) + ((T : ℝ) : ℂ) * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) w) := by
  have hrect := rectIntegral_mellin_smoothWeight_mul_zetaLogDerivReg_eq_neg_zeroSum
    (N := N) (H := H)
    (z₁ := (c : ℂ) + ((-T : ℝ) : ℂ) * I)
    (z₂ := (d : ℂ) + ((T : ℝ) : ℂ) * I)
    hH (by simpa using hc) (by simpa using hcd) (by simp; linarith)
    (by simpa using hbot) (by simpa using htop)
    (by simpa using hright) (by simpa using hleft)
  simp [rectIntegral, smul_eq_mul, mul_comm] at hrect ⊢
  linear_combination hrect

private theorem exists_Ioo_not_mem_finset_zeta {a b : ℝ} (hab : a < b) (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F := by
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hdiff : (Set.Ioo a b \ (F : Set ℝ)).Infinite := hinf.sdiff F.finite_toSet
  obtain ⟨x, hxI, hxF⟩ := hdiff.nonempty
  exact ⟨x, hxI, by simpa using hxF⟩

/-- **Unconditional finite contour selection.**  Inside any prescribed positive left-abscissa
interval, right-abscissa interval, and positive height interval with separated horizontal ranges,
there is a rectangle whose entire boundary avoids the zeros of the residue unit.  Only finite
avoidance in one larger compact rectangle is used. -/
theorem exists_zetaResidueUnit_zeroFreeBoundary_rectangle
    {a b d₀ d₁ T₀ T₁ : ℝ}
    (ha : 0 < a) (hab : a < b) (hsep : b < d₀) (hdd : d₀ < d₁)
    (hT₀ : 0 < T₀) (hTT : T₀ < T₁) :
    ∃ c d T : ℝ,
      c ∈ Set.Ioo a b ∧ d ∈ Set.Ioo d₀ d₁ ∧ T ∈ Set.Ioo T₀ T₁ ∧
      (∀ x ∈ uIcc c d,
        zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ uIcc c d,
        zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ uIcc (-T) T,
        zetaResidueUnit ((d : ℂ) + (y : ℝ) * I) ≠ 0) ∧
      ∀ y ∈ uIcc (-T) T,
        zetaResidueUnit ((c : ℂ) + (y : ℝ) * I) ≠ 0 := by
  classical
  let raw₁ : ℂ := (a : ℂ) + ((-T₁ : ℝ) : ℂ) * I
  let raw₂ : ℂ := (d₁ : ℂ) + ((T₁ : ℝ) : ℂ) * I
  let Z : Finset ℂ := zetaResidueUnitClosedRectangleZeros raw₁ raw₂
  let Fre : Finset ℝ := Z.image Complex.re
  let Fheight : Finset ℝ := Z.image (fun z => |z.im|)
  obtain ⟨c, hcI, hcavoid⟩ := exists_Ioo_not_mem_finset_zeta hab Fre
  obtain ⟨d, hdI, hdavoid⟩ := exists_Ioo_not_mem_finset_zeta hdd Fre
  obtain ⟨T, hTI, hTavoid⟩ := exists_Ioo_not_mem_finset_zeta hTT Fheight
  have hc0 : 0 < c := ha.trans hcI.1
  have hcd : c < d := lt_trans hcI.2 (hsep.trans hdI.1)
  have hT0 : 0 < T := hT₀.trans hTI.1
  have hraw_mem {z : ℂ} (hre₁ : a ≤ z.re) (hre₂ : z.re ≤ d₁)
      (him₁ : -T₁ ≤ z.im) (him₂ : z.im ≤ T₁) :
      z ∈ (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
    apply Complex.mem_reProdIm.mpr
    have hrraw : raw₁.re ≤ raw₂.re := by
      simp [raw₁, raw₂]
      linarith
    have hiraw : raw₁.im ≤ raw₂.im := by
      simp [raw₁, raw₂]
      linarith
    rw [uIcc_of_le hrraw, uIcc_of_le hiraw]
    constructor
    · simpa [raw₁, raw₂] using And.intro hre₁ hre₂
    · simpa [raw₁, raw₂] using And.intro him₁ him₂
  have hzero_mem_Z {z : ℂ}
      (hraw : z ∈ (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im))
      (hz : zetaResidueUnit z = 0) : z ∈ Z :=
    mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨hraw, hz⟩
  have hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : c ≤ x ∧ x ≤ d := by
      rw [uIcc_of_le hcd.le] at hx
      exact hx
    have hraw : ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp <;>
        linarith [hcI.1, hdI.2, hTI.2]
    have hzZ := hzero_mem_Z hraw hzero
    apply hTavoid
    exact Finset.mem_image.mpr
      ⟨(x : ℂ) + ((-T : ℝ) : ℂ) * I, hzZ, by simp [abs_of_pos hT0]⟩
  have htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : c ≤ x ∧ x ≤ d := by
      rw [uIcc_of_le hcd.le] at hx
      exact hx
    have hraw : ((x : ℂ) + ((T : ℝ) : ℂ) * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp <;>
        linarith [hcI.1, hdI.2, hTI.2]
    have hzZ := hzero_mem_Z hraw hzero
    apply hTavoid
    exact Finset.mem_image.mpr
      ⟨(x : ℂ) + ((T : ℝ) : ℂ) * I, hzZ, by simp [abs_of_pos hT0]⟩
  have hright : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + (y : ℝ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -T ≤ y ∧ y ≤ T := by
      rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
      exact hy
    have hraw : ((d : ℂ) + (y : ℝ) * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp <;>
        linarith [hdI.1, hdI.2, hTI.2]
    have hzZ := hzero_mem_Z hraw hzero
    apply hdavoid
    exact Finset.mem_image.mpr ⟨(d : ℂ) + (y : ℝ) * I, hzZ, by simp⟩
  have hleft : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -T ≤ y ∧ y ≤ T := by
      rw [uIcc_of_le (by linarith : -T ≤ T)] at hy
      exact hy
    have hraw : ((c : ℂ) + (y : ℝ) * I) ∈
        (uIcc raw₁.re raw₂.re ×ℂ uIcc raw₁.im raw₂.im) := by
      apply hraw_mem <;> simp <;>
        linarith [hcI.1, hcI.2, hTI.2]
    have hzZ := hzero_mem_Z hraw hzero
    apply hcavoid
    exact Finset.mem_image.mpr ⟨(c : ℂ) + (y : ℝ) * I, hzZ, by simp⟩
  exact ⟨c, d, T, hcI, hdI, hTI, hbot, htop, hright, hleft⟩

/-- Four-edge boundary functional of the smooth Mellin weight times the regular part of
`-ζ'/ζ`. -/
noncomputable def zetaRegularMellinBoundary
    (N H c d T : ℝ) : ℂ :=
  I • (∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * I))
    - I • (∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((c : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * I))
    - ((∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * I) *
          mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * I))
      - ∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
          mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))

/-- Exact analytic-multiplicity-weighted zero packet crossed by the same rectangle. -/
noncomputable def zetaRegularMellinZeroPacket
    (N H c d T : ℝ) : ℂ :=
  2 * Real.pi * I *
    ∑ w ∈ zetaResidueUnitClosedRectangleZeros
        ((c : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((d : ℂ) + ((T : ℝ) : ℂ) * I),
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) w

/-- **Unconditional exact smoothed zero-crossing contour.**  In every prescribed separated box of
positive abscissae and positive heights, one can select a contour for which the regular Chebyshev
boundary functional is exactly the negative multiplicity-weighted zeta-zero packet.  No boundary
avoidance premise remains in the conclusion. -/
theorem exists_zetaRegularMellinBoundary_eq_neg_zeroPacket
    {N H a b d₀ d₁ T₀ T₁ : ℝ} (hH : 0 < H)
    (ha : 0 < a) (hab : a < b) (hsep : b < d₀) (hdd : d₀ < d₁)
    (hT₀ : 0 < T₀) (hTT : T₀ < T₁) :
    ∃ c d T : ℝ,
      c ∈ Set.Ioo a b ∧ d ∈ Set.Ioo d₀ d₁ ∧ T ∈ Set.Ioo T₀ T₁ ∧
      zetaRegularMellinBoundary N H c d T =
        -zetaRegularMellinZeroPacket N H c d T := by
  obtain ⟨c, d, T, hcI, hdI, hTI, hbot, htop, hright, hleft⟩ :=
    exists_zetaResidueUnit_zeroFreeBoundary_rectangle
      ha hab hsep hdd hT₀ hTT
  have hc0 : 0 < c := ha.trans hcI.1
  have hcd : c < d := lt_trans hcI.2 (hsep.trans hdI.1)
  have hT0 : 0 < T := hT₀.trans hTI.1
  refine ⟨c, d, T, hcI, hdI, hTI, ?_⟩
  simpa [zetaRegularMellinBoundary, zetaRegularMellinZeroPacket] using
    (integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_sub_zeroSum
      (N := N) (H := H) hH hc0 hcd hT0 hbot htop hright hleft)

end

end RHTower.Sieve
