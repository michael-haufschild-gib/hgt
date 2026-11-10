import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfTheSquareOfAQuadraticRing
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.BezoutDeterminesTheConstantOfTheCounterterm
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer
import GaloisForLFunctions.RHTower.DirichletLUniformRvM
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw
import GaloisForLFunctions.WindowVisibilityLaw.TheUniversalVisibilityThreshold
import GaloisForLFunctions.ExceptionalLayerTheory.TheDeuringHeilbronnRepulsionLaw

/-!
# The trivial aperture and the exceptional square on the twisted comb

For a primitive Dirichlet character `χ` of conductor `q > 1`, the pairing of the twisted part of
the comb on a packet `f` — jets, the counterterm `log(qn/2π)` and twice the contacts `Λ Re χ` —
has the limit `−Z_χ(f)`, where `Z_χ(f) = twistedZeroSum hq hprim f` is the sum over the zeros of
`L(s, χ)` in the critical strip. This module establishes the unconditional laws governing `Z_χ`
across apertures:

* **Real-to-complex splitting and the onset-aperture dictionary**
  (`re_dirichletZeros_W_split`, `windowPositiveAt_dirichletZeros_iff_twistedZeroSum_nonneg`,
  `twistedZeroSum_nonneg_iff_le_onsetAperture`, `grh_dirichlet_iff_forall_twistedZeroSum_nonneg`):
  for a real primitive character `χ`, `Re W_{L(·,χ)}(F, F) = Z_χ(Re F) + Z_χ(Im F)` for every
  complex `C²` test `F`. Consequently, `Z_χ(f) ≥ 0` on real packets of aperture `a` is equivalent
  to `WindowPositiveAt (dirichletZeros hq hprim) a`, to `(a : EReal) ≤ onsetAperture`, and to the
  vanishing of the Hodge defect at `a`. Holding for all `C` at aperture `log log q + C` for a
  fixed `χ` is equivalent to the Generalized Riemann Hypothesis for `L(s, χ)`.
* **The trivial aperture and the disjoint-half-window `log 2` improvement**
  (`twistedZeroSum_ge_of_aperture`, `two_mul_abs_packetAutocorr_le_of_aperture`,
  `twistedZeroSum_ge_of_aperture_sharpened`, `tendsto_sharpened_primeMass_div_exp`):
  bounding every contact by `|packetAutocorr f (log k)| ≤ ∫ f²` gives the unconditional floor
  `Z_χ(f) ≥ (log q − C_χ − 2 primeMass a) ∫ f²`, which is nonnegative up to aperture
  `log log q − log 4 − o(1)`. Moreover, for every lag `log k ≥ a` (`k > e^a`) on a packet of
  aperture `a`, the factors `f(u)` and `f(u + log k)` are supported in disjoint half-lines
  `u ≤ c` and `u + log k ≥ c`, so `2 |packetAutocorr f (log k)| ≤ ∫ f²`. This halves the prime
  sum on `(e^a, e^{2a}]` without using any sign of `χ`, yielding the sharper unconditional floor
  `Z_χ(f) ≥ (log q − C_χ − primeMass a − primeMass (a / 2)) ∫ f²` with
  `(primeMass a + primeMass (a / 2)) / e^a → 2`, and extending unconditional positivity of `Z_χ`
  to aperture `log log q − log 2 − o(1)`.
* **The one-square law and removal of the exceptional square on even and nonnegative packets**
  (`re_Wsummand_real_zero_eq_cosh_sq_sub_sinh_sq`, `re_Wsummand_real_zero_nonneg_of_even`,
  `re_Wsummand_real_zero_nonneg_of_nonneg`, `re_Wsummand_real_zero_pair_ge_neg_two_pairEnergy`):
  a real zero `β = ½ + δ ∈ (½, 1)` of `L(s, χ)` and its reflection `1 − β = ½ − δ` contribute
  `2 m_β ((∫ f cosh(δu))² − (∫ f sinh(δu))²)` to `Z_χ(f)`. On every even packet, every
  nonnegative packet, and every packet orthogonal to `sinh(δu)`, every real zero pair contributes
  nonnegatively; on packets supported in `[−a, a]` its contribution is bounded below by the sharp
  rank-one square `−(sinh(2δa)/δ − 2a) ∫ f² = −2 pairEnergy(δ, a) ∫ f²`.
* **Deuring–Heilbronn on the twisted comb and repulsion at logarithmic aperture**
  (`exceptional_zero_unique_and_simple`, `twistedZeroSum_odd_le_of_deuring_heilbronn`,
  `exceptional_zero_repelled_of_twistedZeroSum_nonneg`):
  in the exceptional region `1 − β < 1 / (e C (1 + log q + log 3))`, `L(s, χ)` has at most one
  real zero `β`, and it is simple (`mult β = 1`). When `C (1 − β) log(q(R + 3)) < (q(R + 3))^{-C/2}`,
  every other zero `ρ ≠ β, 1 − β` with `|Im ρ| ≤ R` lies on the critical line `Re ρ = ½`,
  isolating the negative odd hyperbolic square of `{β, 1 − β}` on `sinhTest a (β − ½)` and
  forcing `Z_χ < 0` once the pair energy exceeds the critical-line sea; contrapositively,
  `Z_χ ≥ 0` on odd packets at aperture `a` forces the explicit repulsion bound on `1 − β`.
-/

open Finset Filter Topology MeasureTheory Complex Set
open scoped ComplexConjugate ArithmeticFunction.vonMangoldt Real
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {q : ℕ}

/-! ### 1. Real-to-complex splitting and the onset-aperture dictionary for `Z_χ` -/

/-- **Real-to-complex splitting of the pole term**: for any continuous compactly supported test
`F : ℝ → ℂ`, the real part of the pole term of `F ⋆ F̃` is the sum of the pole terms of its real
and imaginary parts. -/
theorem weilPoleTerm_split {F : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    (_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re =
      2 * ((∫ u, (F u).re * Real.exp (-u / 2)) * ∫ u, (F u).re * Real.exp (u / 2)) +
        2 * ((∫ u, (F u).im * Real.exp (-u / 2)) * ∫ u, (F u).im * Real.exp (u / 2)) := by
  rw [_root_.RHTower.WeilOneSided.weilPoleTerm_re_eq_two_re hF hFc]
  have hi1 : Integrable fun u : ℝ => F u * (Real.exp (-u / 2) : ℂ) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hi2 : Integrable fun u : ℝ => F u * (Real.exp (u / 2) : ℂ) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hre : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r := fun z r => by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have him : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).im = z.im * r := fun z r => by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hr1 : ∫ u, (F u * (Real.exp (-u / 2) : ℂ)).re =
      (∫ u, F u * (Real.exp (-u / 2) : ℂ)).re :=
    Complex.reCLM.integral_comp_comm hi1
  have hi1' : ∫ u, (F u * (Real.exp (-u / 2) : ℂ)).im =
      (∫ u, F u * (Real.exp (-u / 2) : ℂ)).im :=
    Complex.imCLM.integral_comp_comm hi1
  have hr2 : ∫ u, (F u * (Real.exp (u / 2) : ℂ)).re =
      (∫ u, F u * (Real.exp (u / 2) : ℂ)).re :=
    Complex.reCLM.integral_comp_comm hi2
  have hi2' : ∫ u, (F u * (Real.exp (u / 2) : ℂ)).im =
      (∫ u, F u * (Real.exp (u / 2) : ℂ)).im :=
    Complex.imCLM.integral_comp_comm hi2
  have r1 : (paperFT F (Complex.I / 2)).re = ∫ u, (F u).re * Real.exp (-u / 2) := by
    rw [_root_.RHTower.LebesgueAtomWeil.paperFT_I_div_two, ← hr1]
    exact integral_congr_ae (Eventually.of_forall fun u => hre _ _)
  have i1 : (paperFT F (Complex.I / 2)).im = ∫ u, (F u).im * Real.exp (-u / 2) := by
    rw [_root_.RHTower.LebesgueAtomWeil.paperFT_I_div_two, ← hi1']
    exact integral_congr_ae (Eventually.of_forall fun u => him _ _)
  have r2 : (paperFT F (-Complex.I / 2)).re = ∫ u, (F u).re * Real.exp (u / 2) := by
    rw [_root_.RHTower.LebesgueAtomWeil.paperFT_neg_I_div_two, ← hr2]
    exact integral_congr_ae (Eventually.of_forall fun u => hre _ _)
  have i2 : (paperFT F (-Complex.I / 2)).im = ∫ u, (F u).im * Real.exp (u / 2) := by
    rw [_root_.RHTower.LebesgueAtomWeil.paperFT_neg_I_div_two, ← hi2']
    exact integral_congr_ae (Eventually.of_forall fun u => him _ _)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add,
    r1, i1, r2, i2]
  ring

/-- **Real-to-complex splitting of the zero sum of `L(s, χ)`**: for a real primitive character
`χ` of conductor `q > 1` and any complex `C²` test `F` of compact support, the real part of Weil's
zero form `W_{L(·,χ)}(F, F)` is the sum of `Z_χ` on the real and imaginary parts of `F`. -/
theorem re_dirichletZeros_W_split [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    ((_root_.RHTower.dirichletZeros hq hprim).W F F).re =
      twistedZeroSum hq hprim (fun x => (F x).re) +
        twistedZeroSum hq hprim (fun x => (F x).im) := by
  obtain ⟨A, hA⟩ := hFc.isCompact.isBounded.subset_closedBall 0
  have ha : 0 ≤ |A| := abs_nonneg A
  have hFs : tsupport F ⊆ Set.Icc (-|A|) |A| := fun x hx => by
    have := hA hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp (this.trans (le_abs_self A))
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hF
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hF
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have hχ := re_weilFullFunctional_twist hq hprim hreal ha hF hFs
  rw [integral_norm_sq_split hF.continuous hFc, mul_add] at hχ
  have hχs := re_weilFullFunctional_split (twistWeight χ) hF hFc
  have hp := weilPoleTerm_split hF.continuous hFc
  have hpe := placeEnergy_split χ hF hFs
  have hχu := re_weilFullFunctional_twist_packet hq hprim hu huc
  have hχv := re_weilFullFunctional_twist_packet hq hprim hv hvc
  linarith

/-- If a complex test `F` has `tsupport F ⊆ [−a, a]`, then the packet embeddings of its real and
imaginary parts also have `tsupport ⊆ [−a, a]`. -/
theorem tsupport_ofReal_re_im_subset {F : ℝ → ℂ} {a : ℝ} (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    tsupport (fun u => (((F u).re : ℝ) : ℂ)) ⊆ Set.Icc (-a) a ∧
      tsupport (fun u => (((F u).im : ℝ) : ℂ)) ⊆ Set.Icc (-a) a :=
  ⟨(tsupport_comp_subset (g := fun z : ℂ => (z.re : ℂ)) (by simp) F).trans hFs,
    (tsupport_comp_subset (g := fun z : ℂ => (z.im : ℂ)) (by simp) F).trans hFs⟩

/-- **Complex window positivity of `L(s, χ)` is equivalent to `Z_χ ≥ 0` on real packets.** -/
theorem windowPositiveAt_dirichletZeros_iff_twistedZeroSum_nonneg [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (a : ℝ) :
    WindowVisibilityLaw.WindowPositiveAt (_root_.RHTower.dirichletZeros hq hprim) a ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a → 0 ≤ twistedZeroSum hq hprim f := by
  constructor
  · intro hpos f hf hfs
    exact hpos (fun u => (f u : ℂ)) (contDiff_ofReal_packet hf) hfs
  · intro hreal_pos F hF hFs
    have hFc : HasCompactSupport F :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport F) hFs
    obtain ⟨hre_s, him_s⟩ := tsupport_ofReal_re_im_subset hFs
    rw [re_dirichletZeros_W_split hq hprim hreal hF hFc]
    exact add_nonneg
      (hreal_pos (fun u => (F u).re) (Complex.reCLM.contDiff.comp hF) hre_s)
      (hreal_pos (fun u => (F u).im) (Complex.imCLM.contDiff.comp hF) him_s)

/-- **Translation-invariant window positivity equivalence**: `WindowPositiveAt` at half-width `a`
is equivalent to `Z_χ(f) ≥ 0` on all packets supported in any window `[c − a, c + a]` of half-width
`a`. -/
theorem windowPositiveAt_dirichletZeros_iff_forall_window [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (_ha : 0 ≤ a) :
    WindowVisibilityLaw.WindowPositiveAt (_root_.RHTower.dirichletZeros hq hprim) a ↔
      ∀ (f : ℝ → ℝ) (c : ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
        (∀ u, a < |u - c| → f u = 0) → 0 ≤ twistedZeroSum hq hprim f := by
  rw [windowPositiveAt_dirichletZeros_iff_twistedZeroSum_nonneg hq hprim hreal a]
  constructor
  · intro hpos f c hf hfc hshort
    have hg : ContDiff ℝ 2 fun u => f (u - -c) := hf.comp (contDiff_id.sub contDiff_const)
    have hts : tsupport (fun x => ((f (x - -c) : ℝ) : ℂ)) ⊆ Set.Icc (-a) a := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      by_contra hxI
      have hx' : a < |x - -c - c| := by
        rw [sub_neg_eq_add, add_sub_cancel_right]
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
        rcases hxI with h | h
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl h)
      exact hx (by
        show ((f (x - -c) : ℝ) : ℂ) = 0
        rw [hshort _ hx', Complex.ofReal_zero])
    rw [← twistedZeroSum_translate hq hprim hf hfc (-c)]
    exact hpos _ hg hts
  · intro hwin f hf hfs
    have hfc : HasCompactSupport f := by
      have hFc : HasCompactSupport fun u => (f u : ℂ) :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
      exact hFc.comp_left (g := Complex.re) (by simp)
    refine hwin f 0 hf hfc fun u hu => ?_
    rw [sub_zero] at hu
    have hnot : u ∉ Set.Icc (-a) a := fun hm => by
      have := abs_le.mpr ⟨hm.1, hm.2⟩
      linarith
    have hF0 : ((f u : ℝ) : ℂ) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun u => (f u : ℂ)) fun hm => hnot (hfs hm)
    exact Complex.ofReal_eq_zero.mp hF0

/-- **Onset-aperture characterization of `Z_χ ≥ 0`**: for `a ≥ 0` and a real primitive character
`χ`, `Z_χ(f) ≥ 0` on all packets of half-width `a` iff `(a : EReal) ≤ onsetAperture`. -/
theorem twistedZeroSum_nonneg_iff_le_onsetAperture [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a → 0 ≤ twistedZeroSum hq hprim f) ↔
      (a : EReal) ≤ WindowVisibilityLaw.onsetAperture (_root_.RHTower.dirichletZeros hq hprim) := by
  rw [← windowPositiveAt_dirichletZeros_iff_twistedZeroSum_nonneg hq hprim hreal a,
    WindowVisibilityLaw.windowPositiveAt_iff_le_onsetAperture
      (temperedConfig_dirichletZeros hq hprim) ha]

/-- **Equivalence with the Generalized Riemann Hypothesis for `L(s, χ)`**: for a fixed real
primitive character `χ` of conductor `q > 1`, `Z_χ(f) ≥ 0` holds at aperture `log log q + C` for
every `C : ℝ` if and only if every nontrivial zero of `L(s, χ)` lies on the critical line
`Re ρ = 1 / 2`. -/
theorem grh_dirichlet_iff_forall_twistedZeroSum_nonneg [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier, ρ.re = 1 / 2) ↔
      ∀ (C : ℝ) (f : ℝ → ℝ), ContDiff ℝ 2 f →
        tsupport (fun u => (f u : ℂ)) ⊆
          Set.Icc (-(Real.log (Real.log q) + C)) (Real.log (Real.log q) + C) →
        0 ≤ twistedZeroSum hq hprim f := by
  rw [← WindowVisibilityLaw.onsetAperture_eq_top_iff_onLine
    (temperedConfig_dirichletZeros hq hprim)]
  constructor
  · intro htop C f hf hfs
    set a := Real.log (Real.log q) + C
    rcases lt_or_ge a 0 with ha | ha
    · have hpos := WindowVisibilityLaw.windowPositiveAt_of_neg
        (_root_.RHTower.dirichletZeros hq hprim) ha
      exact (windowPositiveAt_dirichletZeros_iff_twistedZeroSum_nonneg hq hprim hreal a).mp
        hpos f hf hfs
    · have hle : (a : EReal) ≤
          WindowVisibilityLaw.onsetAperture (_root_.RHTower.dirichletZeros hq hprim) :=
        htop ▸ le_top
      exact (twistedZeroSum_nonneg_iff_le_onsetAperture hq hprim hreal ha).mpr hle f hf hfs
  · intro hall
    cases h : WindowVisibilityLaw.onsetAperture (_root_.RHTower.dirichletZeros hq hprim) with
    | bot =>
      exfalso
      have h0 := WindowVisibilityLaw.zero_le_onsetAperture (_root_.RHTower.dirichletZeros hq hprim)
      rw [h] at h0
      exact absurd h0 (by decide)
    | top => rfl
    | coe b =>
      exfalso
      set a := max b 0 + 1
      have ha0 : 0 ≤ a := by dsimp [a]; linarith [le_max_right b 0]
      have hba : b < a := by dsimp [a]; linarith [le_max_left b 0]
      set C := a - Real.log (Real.log q)
      have haC : Real.log (Real.log q) + C = a := by dsimp [C]; ring
      have hpos : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
          tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a → 0 ≤ twistedZeroSum hq hprim f := by
        intro f hf hfs
        exact hall C f hf (by rwa [haC])
      have hle := (twistedZeroSum_nonneg_iff_le_onsetAperture hq hprim hreal ha0).mp hpos
      rw [h, EReal.coe_le_coe_iff] at hle
      linarith

/-! ### 2. The trivial aperture theorem and the disjoint-half-window `log 2` improvement -/

open Classical in
/-- The archimedean constant `C_χ` of a Dirichlet character `χ`: `log(4π)` when `χ` is odd and
`log(128π)` when `χ` is even. -/
def archConstant (χ : DirichletCharacter ℂ q) : ℝ :=
  if χ.Odd then Real.log (4 * π) else Real.log (128 * π)

theorem archConstant_of_odd {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) :
    archConstant χ = Real.log (4 * π) := by
  simp only [archConstant, if_pos hodd]

theorem archConstant_of_even {χ : DirichletCharacter ℂ q} (heven : χ.Even) :
    archConstant χ = Real.log (128 * π) := by
  have hno : ¬ χ.Odd := by
    intro hodd
    have h1 : χ (-1) = 1 := heven
    have h2 : χ (-1) = -1 := hodd
    have : (1 : ℂ) = -1 := h1.symm.trans h2
    exact absurd (congrArg Complex.re this) (by norm_num)
  simp only [archConstant, if_neg hno]

/-- **Archimedean lower bound on `Z_χ(g)` at arbitrary aperture `a ≥ 0`**: for every primitive
character `χ` of conductor `q > 1` and every `C²` packet `g` supported in `[−a, a]`,
`Z_χ(g) ≥ (log q − archConstant χ) ∫ g² − 2 ∑_{2 ≤ k ≤ ⌊e^{2a}⌋} (twistWeight χ k / √k) packetAutocorr g (log k)`. -/
theorem twistedZeroSum_ge_sub_sum_twistWeight [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {a : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hGs : tsupport (fun u => (g u : ℂ)) ⊆ Set.Icc (-a) a) :
    (Real.log q - archConstant χ) * (∫ u, g u ^ 2) -
        2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k) ≤
      twistedZeroSum hq hprim g := by
  have hG := contDiff_ofReal_packet hg
  have hπ : 0 < π := Real.pi_pos
  have hπ0 : (π : ℝ) ≠ 0 := hπ.ne'
  have hh : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
    _root_.RHTower.integrable_normSq_paperFT hG hGs
  have hA : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
      _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) :=
    _root_.RHTower.integrable_normSq_paperFT_mul_arch hG hGs
  have hform := integral_weilAtomSymbol_twist_packet hq hprim hg hGs
  have hk : ∀ y : ℝ, EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) y =
      ((packetAutocorr g y : ℝ) : ℂ) := fun y => weilTest_packet g y
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n / Real.sqrt n *
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (Real.log n) +
          EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (-Real.log n)).re =
      2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        twistWeight χ n / Real.sqrt n * packetAutocorr g (Real.log n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hk, hk, packetAutocorr_neg, ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  rw [_root_.RHTower.integral_weilAtomSymbol_eq_arch_sub hG hGs (twistWeight χ), hsum] at hform
  have hPlanch : ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 = 2 * π * ∫ u, g u ^ 2 := by
    rw [_root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_ofReal_sq]
  have hsymb0 : ∀ ξ : ℝ, _root_.RHTower.weilAtomSymbol (fun _ => 0) 0 ξ =
      _root_.RHTower.archimedeanWeilSymbol ξ := fun ξ => by
    simp [_root_.RHTower.weilAtomSymbol]
  rcases χ.even_or_odd with heven | hodd
  · rw [archConstant_of_even heven]
    rw [placeEnergy_of_even heven, mul_zero, sub_zero] at hform
    have hpos := _root_.RHTower.integral_evenDirichletArchSymbol_nonneg (le_rfl : 128 * π ≤ 128 * π)
      (fun u => (g u : ℂ))
    have hB : Integrable fun τ : ℝ => Real.log (128 * π) * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
      hh.const_mul _
    have hsplit : ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log (128 * π)) =
        (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) +
          Real.log (128 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_add hA hB]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      show ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log (128 * π)) =
        ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) +
          Real.log (128 * π) * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2
      rw [hsymb0]
      ring
    rw [hsplit] at hpos
    rw [hPlanch] at hpos hform
    have h1 : 0 ≤ 2 * π * (twistedZeroSum hq hprim g -
        (Real.log q - Real.log (128 * π)) * (∫ u, g u ^ 2) +
        2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k)) := by
      linarith
    have h2 := nonneg_of_mul_nonneg_right h1 (by positivity : (0 : ℝ) < 2 * π)
    linarith
  · rw [archConstant_of_odd hodd]
    rw [placeEnergy_of_odd hodd] at hform
    have hpos := _root_.RHTower.integral_oddDirichletArchSymbol_nonneg (le_rfl : 4 * π ≤ 4 * π)
      (fun u => (g u : ℂ))
    have hB : Integrable fun τ : ℝ => Real.log (4 * π) * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
      hh.const_mul _
    have hAB : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) +
          Real.log (4 * π) * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 := hA.add hB
    have hC : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
        (π / Real.cosh (π * τ)) := by
      have hGc : HasCompactSupport fun u => (g u : ℂ) :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hGs
      have hhc : Continuous fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
        _root_.RHTower.BlindPrimePowerSlack.continuous_normSq_paperFT ⟨_, hG, hGc⟩
      refine (hh.const_mul π).mono' (hhc.mul (continuous_const.div
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
        fun τ => (Real.cosh_pos _).ne')).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
      show ‖‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ))‖ ≤
        π * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2
      have hc : 1 ≤ Real.cosh (π * τ) := Real.one_le_cosh _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (div_nonneg hπ.le (by linarith))), mul_comm]
      exact mul_le_mul_of_nonneg_right (div_le_self hπ.le hc) (sq_nonneg _)
    have hsplit : ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log (4 * π) +
            π / Real.cosh (π * τ)) =
        (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) +
          Real.log (4 * π) * (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2) +
          ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ)) := by
      rw [← integral_const_mul, ← integral_add hA hB, ← integral_add hAB hC]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      show ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log (4 * π) +
            π / Real.cosh (π * τ)) =
        ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) +
          Real.log (4 * π) * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 +
          ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ))
      rw [hsymb0]
      ring
    have hcancel : 2 * π * (1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (π / Real.cosh (π * τ))) =
        ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ)) := by
      field_simp
    rw [hsplit] at hpos
    rw [hcancel, hPlanch] at hform
    rw [hPlanch] at hpos
    have h1 : 0 ≤ 2 * π * (twistedZeroSum hq hprim g -
        (Real.log q - Real.log (4 * π)) * (∫ u, g u ^ 2) +
        2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k)) := by
      linarith
    have h2 := nonneg_of_mul_nonneg_right h1 (by positivity : (0 : ℝ) < 2 * π)
    linarith

/-- The twisted weight is bounded in absolute value by the von Mangoldt function:
`|Λ(n) Re χ(n)| ≤ Λ(n)`. -/
theorem abs_twistWeight_le_vonMangoldt [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    |twistWeight χ n| ≤ Λ n := by
  unfold twistWeight
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have h1 : |(χ (n : ZMod q)).re| ≤ 1 :=
    (Complex.abs_re_le_norm (χ (n : ZMod q))).trans (_root_.RHTower.norm_dirichletCharacter_le_one χ _)
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg h1

/-- **Global Cauchy–Schwarz bound on the autocorrelation**: for every continuous compactly supported
packet `g : ℝ → ℝ` and every lag `y : ℝ`, `|packetAutocorr g y| ≤ ∫ u, g u ^ 2`. -/
theorem abs_packetAutocorr_le_integral_sq {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (y : ℝ) :
    |packetAutocorr g y| ≤ ∫ u, g u ^ 2 := by
  have hgsq : Integrable fun u => g u ^ 2 := by
    refine ((hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show g u * g u = g u ^ 2
    ring
  have hgy : Integrable fun u => g (u + y) ^ 2 := hgsq.comp_add_right y
  have hprod : Integrable fun u => |g u * g (u + y)| :=
    ((hg.mul (hg.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hgc.mul_right).abs
  have hpt : ∀ u : ℝ, 2 * |g u * g (u + y)| ≤ g u ^ 2 + g (u + y) ^ 2 := fun u => by
    rw [abs_mul, ← mul_assoc]
    have := two_mul_le_add_sq |g u| |g (u + y)|
    rwa [sq_abs, sq_abs] at this
  have hint : ∫ u, 2 * |g u * g (u + y)| ≤ ∫ u, (g u ^ 2 + g (u + y) ^ 2) :=
    integral_mono (hprod.const_mul 2) (hgsq.add hgy) hpt
  rw [integral_const_mul, integral_add hgsq hgy, integral_add_right_eq_self (fun u => g u ^ 2) y] at hint
  have habs : |packetAutocorr g y| ≤ ∫ u, |g u * g (u + y)| :=
    abs_integral_le_integral_abs
  linarith

/-- **Disjoint-half-window autocorrelation bound (`log 2` improvement)**: if `g` vanishes outside
`[c − a, c + a]` and `y ≥ a`, then for every `u ≠ c − y` where `g(u) g(u + y) ≠ 0`, `u` lies in
`(−∞, c]` while `u + y` lies in `(c, ∞)`. Because `(−∞, c]` and `(c, ∞)` are disjoint, AM–GM on the
two halves gives `2 |packetAutocorr g y| ≤ ∫ u, g u ^ 2` — a factor of `2` sharper than the global
bound. -/
theorem two_mul_abs_packetAutocorr_le_of_aperture {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {c a y : ℝ} (hay : a ≤ y)
    (hshort : ∀ u, a < |u - c| → g u = 0) :
    2 * |packetAutocorr g y| ≤ ∫ u, g u ^ 2 := by
  have hgsq : Integrable fun u => g u ^ 2 := by
    refine ((hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show g u * g u = g u ^ 2
    ring
  have hIic : Integrable (Set.indicator (Set.Iic c) (fun u => g u ^ 2)) :=
    hgsq.indicator measurableSet_Iic
  have hIoi : Integrable (Set.indicator (Set.Ioi c) (fun u => g u ^ 2)) :=
    hgsq.indicator measurableSet_Ioi
  have hIoi_shift : Integrable (fun u => Set.indicator (Set.Ioi c) (fun x => g x ^ 2) (u + y)) :=
    hIoi.comp_add_right y
  have hprod : Integrable fun u => 2 * |g u * g (u + y)| :=
    (((hg.mul (hg.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hgc.mul_right).abs).const_mul 2
  have hae : ∀ᵐ u ∂volume, 2 * |g u * g (u + y)| ≤
      Set.indicator (Set.Iic c) (fun x => g x ^ 2) u +
        Set.indicator (Set.Ioi c) (fun x => g x ^ 2) (u + y) := by
    have hcompl : ({c - y}ᶜ : Set ℝ) ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl, measure_singleton])
    filter_upwards [hcompl] with u hu
    have hne : u ≠ c - y := hu
    by_cases huc : u ≤ c
    · by_cases huy : c < u + y
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr huc),
          Set.indicator_of_mem (Set.mem_Ioi.mpr huy), abs_mul, ← mul_assoc]
        have := two_mul_le_add_sq |g u| |g (u + y)|
        rwa [sq_abs, sq_abs] at this
      · push Not at huy
        have hlt : u + y < c := lt_of_le_of_ne huy (fun h => hne (by linarith))
        have hgu : g u = 0 := hshort u (lt_abs.mpr (Or.inr (by linarith)))
        rw [hgu, zero_mul, abs_zero, mul_zero]
        exact add_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
          (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    · push Not at huc
      have hguy : g (u + y) = 0 := hshort (u + y) (lt_abs.mpr (Or.inl (by linarith)))
      rw [hguy, mul_zero, abs_zero, mul_zero]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  have hint : ∫ u, 2 * |g u * g (u + y)| ≤ ∫ u, (Set.indicator (Set.Iic c) (fun x => g x ^ 2) u +
      Set.indicator (Set.Ioi c) (fun x => g x ^ 2) (u + y)) :=
    integral_mono_ae hprod (hIic.add hIoi_shift) hae
  have hpart : ∀ x : ℝ, Set.indicator (Set.Iic c) (fun t => g t ^ 2) x +
      Set.indicator (Set.Ioi c) (fun t => g t ^ 2) x = g x ^ 2 := fun x => by
    by_cases hx : x ≤ c
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx),
        Set.indicator_of_notMem (show x ∉ Set.Ioi c from not_lt.mpr hx), add_zero]
    · push Not at hx
      rw [Set.indicator_of_notMem (show x ∉ Set.Iic c from not_le.mpr hx),
        Set.indicator_of_mem (Set.mem_Ioi.mpr hx), zero_add]
  have hsum_int : (∫ u, Set.indicator (Set.Iic c) (fun x => g x ^ 2) u) +
      (∫ u, Set.indicator (Set.Ioi c) (fun x => g x ^ 2) u) = ∫ u, g u ^ 2 := by
    rw [← integral_add hIic hIoi]
    exact integral_congr_ae (Eventually.of_forall hpart)
  rw [integral_const_mul, integral_add hIic hIoi_shift,
    integral_add_right_eq_self (Set.indicator (Set.Ioi c) (fun x => g x ^ 2)) y, hsum_int] at hint
  have habs : |packetAutocorr g y| ≤ ∫ u, |g u * g (u + y)| :=
    abs_integral_le_integral_abs
  linarith

/-- **The trivial aperture bound on `Z_χ(f)` (`A100` Part 1)**: for every primitive character `χ`
of conductor `q > 1` and every packet `f` supported in a window `[c − a, c + a]` of half-width
`a ≥ 0`,
`Z_χ(f) ≥ (log q − archConstant χ − 2 primeMass a) ∫ f²`. -/
theorem twistedZeroSum_ge_of_aperture [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {c a : ℝ} (hshort : ∀ u, a < |u - c| → f u = 0) :
    (Real.log q - archConstant χ - 2 * _root_.RHTower.FreeLagTrace.primeMass a) * (∫ u, f u ^ 2) ≤
      twistedZeroSum hq hprim f := by
  set g : ℝ → ℝ := fun u => f (u - -c)
  have hg : ContDiff ℝ 2 g := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g := hfc.comp_homeomorph (Homeomorph.subRight (-c))
  have hg0 : ∀ x : ℝ, a < |x| → g x = 0 := fun x hx => by
    change f (x - -c) = 0
    exact hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
  have hts : tsupport (fun x => (g x : ℂ)) ⊆ Set.Icc (-a) a := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra hxI
    have hx' : a < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
      rcases hxI with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hx (by show ((g x : ℝ) : ℂ) = 0; rw [hg0 x hx', Complex.ofReal_zero])
  have harch := twistedZeroSum_ge_sub_sum_twistWeight hq hprim hg hts
  have hmass : ∫ u, g u ^ 2 = ∫ u, f u ^ 2 :=
    integral_sub_right_eq_self (fun u => f u ^ 2) (-c)
  have hZ : twistedZeroSum hq hprim g = twistedZeroSum hq hprim f :=
    twistedZeroSum_translate hq hprim hf hfc (-c)
  have hsum_le : ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k) ≤
      _root_.RHTower.FreeLagTrace.primeMass a * ∫ u, g u ^ 2 := by
    unfold _root_.RHTower.FreeLagTrace.primeMass
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := le_abs_self (twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k))
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg k)] at h1
    have h2 : |twistWeight χ k| / Real.sqrt k * |packetAutocorr g (Real.log k)| ≤
        (Λ k : ℝ) / Real.sqrt k * ∫ u, g u ^ 2 :=
      mul_le_mul
        (div_le_div_of_nonneg_right (abs_twistWeight_le_vonMangoldt χ k) (Real.sqrt_nonneg k))
        (abs_packetAutocorr_le_integral_sq hg.continuous hgc (Real.log k))
        (abs_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
    exact h1.trans h2
  rw [hmass, hZ] at harch
  rw [hmass] at hsum_le
  linarith

/-- **The sharpened sign-blind trivial aperture bound (`log 2` improvement)**: splitting the prime
sum at `⌊e^a⌋ = ⌊e^{2(a/2)}⌋` and using `two_mul_abs_packetAutocorr_le_of_aperture` on `(e^a, e^{2a}]`
gives the strictly stronger unconditional bound
`Z_χ(f) ≥ (log q − archConstant χ − primeMass a − primeMass (a / 2)) ∫ f²`
without using any sign of `χ`. -/
theorem twistedZeroSum_ge_of_aperture_sharpened [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {c a : ℝ}
    (hshort : ∀ u, a < |u - c| → f u = 0) :
    (Real.log q - archConstant χ -
        (_root_.RHTower.FreeLagTrace.primeMass a +
          _root_.RHTower.FreeLagTrace.primeMass (a / 2))) * (∫ u, f u ^ 2) ≤
      twistedZeroSum hq hprim f := by
  set g : ℝ → ℝ := fun u => f (u - -c)
  have hg : ContDiff ℝ 2 g := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g := hfc.comp_homeomorph (Homeomorph.subRight (-c))
  have hg0 : ∀ x : ℝ, a < |x - 0| → g x = 0 := fun x hx => by
    change f (x - -c) = 0
    rw [sub_zero] at hx
    exact hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
  have hts : tsupport (fun x => (g x : ℂ)) ⊆ Set.Icc (-a) a := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra hxI
    have hx' : a < |x - 0| := by
      rw [sub_zero]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
      rcases hxI with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hx (by show ((g x : ℝ) : ℂ) = 0; rw [hg0 x hx', Complex.ofReal_zero])
  have harch := twistedZeroSum_ge_sub_sum_twistWeight hq hprim hg hts
  have hmass : ∫ u, g u ^ 2 = ∫ u, f u ^ 2 :=
    integral_sub_right_eq_self (fun u => f u ^ 2) (-c)
  have hZ : twistedZeroSum hq hprim g = twistedZeroSum hq hprim f :=
    twistedZeroSum_translate hq hprim hf hfc (-c)
  by_cases ha0 : 0 ≤ a
  · have hsub : Finset.Icc 2 ⌊Real.exp (2 * (a / 2))⌋₊ ⊆ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ :=
      Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))
    have hpm_split : _root_.RHTower.FreeLagTrace.primeMass a +
          _root_.RHTower.FreeLagTrace.primeMass (a / 2) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          (if k ≤ ⌊Real.exp (2 * (a / 2))⌋₊ then 2 else 1) * ((Λ k : ℝ) / Real.sqrt k) := by
      unfold _root_.RHTower.FreeLagTrace.primeMass _root_.RHTower.FreeLagTrace.primeCutoff
      have h1 : (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a / 2))⌋₊, (Λ k : ℝ) / Real.sqrt k) =
          ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
            if k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a / 2))⌋₊ then (Λ k : ℝ) / Real.sqrt k else 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      by_cases hle : k ≤ ⌊Real.exp (2 * (a / 2))⌋₊
      · rw [if_pos (Finset.mem_Icc.mpr ⟨hk2, hle⟩), if_pos hle]; ring
      · rw [if_neg (fun hm => hle (Finset.mem_Icc.mp hm).2), if_neg hle]; ring
    have hsum_le : 2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k) ≤
        (_root_.RHTower.FreeLagTrace.primeMass a +
          _root_.RHTower.FreeLagTrace.primeMass (a / 2)) * ∫ u, g u ^ 2 := by
      rw [Finset.mul_sum, hpm_split, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have h1 : 2 * (twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k)) ≤
          |twistWeight χ k| / Real.sqrt k * (2 * |packetAutocorr g (Real.log k)|) := by
        have := le_abs_self (twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k))
        rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg k)] at this
        linarith
      have htw : |twistWeight χ k| / Real.sqrt k ≤ (Λ k : ℝ) / Real.sqrt k :=
        div_le_div_of_nonneg_right (abs_twistWeight_le_vonMangoldt χ k) (Real.sqrt_nonneg k)
      have hΛ0 : 0 ≤ (Λ k : ℝ) / Real.sqrt k :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)
      by_cases hle : k ≤ ⌊Real.exp (2 * (a / 2))⌋₊
      · rw [if_pos hle]
        have hauto : 2 * |packetAutocorr g (Real.log k)| ≤ 2 * ∫ u, g u ^ 2 := by
          linarith [abs_packetAutocorr_le_integral_sq hg.continuous hgc (Real.log k)]
        calc 2 * (twistWeight χ k / Real.sqrt k * packetAutocorr g (Real.log k))
            ≤ |twistWeight χ k| / Real.sqrt k * (2 * |packetAutocorr g (Real.log k)|) := h1
          _ ≤ (Λ k : ℝ) / Real.sqrt k * (2 * ∫ u, g u ^ 2) :=
              mul_le_mul htw hauto (by positivity) hΛ0
          _ = 2 * ((Λ k : ℝ) / Real.sqrt k) * ∫ u, g u ^ 2 := by ring
      · rw [if_neg hle, one_mul]
        push Not at hle
        have hexp : Real.exp a < k := by
          have : Real.exp (2 * (a / 2)) < k := (Nat.floor_lt (Real.exp_pos _).le).mp hle
          rwa [show 2 * (a / 2) = a by ring] at this
        have hlog : a ≤ Real.log k := by
          rw [← Real.log_exp a]
          exact (Real.log_lt_log (Real.exp_pos _) hexp).le
        have hauto := two_mul_abs_packetAutocorr_le_of_aperture hg.continuous hgc hlog hg0
        exact h1.trans (mul_le_mul htw hauto (by positivity) hΛ0)
    rw [hmass, hZ] at harch
    rw [hmass] at hsum_le
    linarith
  · push Not at ha0
    have hf0 : ∀ u, f u = 0 := fun u => hshort u (lt_of_lt_of_le ha0 (abs_nonneg _))
    have hint0 : (∫ u, f u ^ 2) = 0 := by simp [hf0]
    have hZ0 : twistedZeroSum hq hprim f = 0 := by
      unfold twistedZeroSum
      have hF0 : (fun u : ℝ => (f u : ℂ)) = 0 := by funext u; simp [hf0]
      have hp0 : paperFT (0 : ℝ → ℂ) = 0 := by funext z; simp [paperFT_def]
      simp [ZeroConfig.W, ZeroConfig.Wsummand, hF0, hp0]
    rw [hint0, hZ0, mul_zero]

/-- **Asymptotic coefficient `2` (rather than `4`) of the sharpened sign-blind prime mass**:
`(primeMass a + primeMass (a / 2)) / e^a → 2` as `a → ∞`. -/
theorem tendsto_sharpened_primeMass_div_exp :
    Tendsto (fun a : ℝ =>
      (_root_.RHTower.FreeLagTrace.primeMass a +
        _root_.RHTower.FreeLagTrace.primeMass (a / 2)) / Real.exp a)
      atTop (𝓝 2) := by
  have h1 : Tendsto (fun a : ℝ => _root_.RHTower.FreeLagTrace.primeMass a / Real.exp a) atTop (𝓝 2) :=
    _root_.RHTower.FreeLagTrace.tendsto_primeMass_div_exp
  have h2a : Tendsto (fun a : ℝ => a / 2) atTop atTop :=
    (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)).congr fun a => by dsimp; ring
  have h2 : Tendsto (fun a : ℝ =>
      _root_.RHTower.FreeLagTrace.primeMass (a / 2) / Real.exp (a / 2)) atTop (𝓝 2) :=
    _root_.RHTower.FreeLagTrace.tendsto_primeMass_div_exp.comp h2a
  have h3 : Tendsto (fun a : ℝ => Real.exp (-(a / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2a)
  have h4 : Tendsto (fun a : ℝ =>
      _root_.RHTower.FreeLagTrace.primeMass (a / 2) / Real.exp a) atTop (𝓝 0) := by
    have hmul := h2.mul h3
    rw [mul_zero] at hmul
    refine hmul.congr fun a => ?_
    rw [Real.exp_neg]
    have hexp : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
      rw [← Real.exp_add, add_halves]
    calc _root_.RHTower.FreeLagTrace.primeMass (a / 2) / Real.exp (a / 2) * (Real.exp (a / 2))⁻¹
        = _root_.RHTower.FreeLagTrace.primeMass (a / 2) /
            (Real.exp (a / 2) * Real.exp (a / 2)) := by
          rw [div_mul_eq_div_mul_one_div, one_div]
      _ = _root_.RHTower.FreeLagTrace.primeMass (a / 2) / Real.exp a := by rw [hexp]
  have hsum := h1.add h4
  rw [add_zero] at hsum
  exact hsum.congr fun a => (add_div _ _ _).symm

/-- **Unconditional nonnegativity of `Z_χ` up to the sharpened trivial aperture**: whenever
`primeMass a + primeMass (a / 2) + archConstant χ ≤ log q`, `Z_χ(f) ≥ 0` holds on every packet `f`
of aperture `a`, and for real `χ` this gives `WindowPositiveAt (dirichletZeros hq hprim) a`. -/
theorem twistedZeroSum_nonneg_of_sharpened_trivial_aperture [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {c a : ℝ}
    (hle : _root_.RHTower.FreeLagTrace.primeMass a +
      _root_.RHTower.FreeLagTrace.primeMass (a / 2) + archConstant χ ≤ Real.log q)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hshort : ∀ u, a < |u - c| → f u = 0) :
    0 ≤ twistedZeroSum hq hprim f := by
  have h := twistedZeroSum_ge_of_aperture_sharpened hq hprim hf hfc hshort
  have h0 : 0 ≤ (Real.log q - archConstant χ -
      (_root_.RHTower.FreeLagTrace.primeMass a +
        _root_.RHTower.FreeLagTrace.primeMass (a / 2))) * ∫ u, f u ^ 2 :=
    mul_nonneg (by linarith) (integral_nonneg fun _ => sq_nonneg _)
  linarith

theorem windowPositiveAt_dirichletZeros_of_sharpened_trivial_aperture [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a)
    (hle : _root_.RHTower.FreeLagTrace.primeMass a +
      _root_.RHTower.FreeLagTrace.primeMass (a / 2) + archConstant χ ≤ Real.log q) :
    WindowVisibilityLaw.WindowPositiveAt (_root_.RHTower.dirichletZeros hq hprim) a := by
  rw [windowPositiveAt_dirichletZeros_iff_forall_window hq hprim hreal ha]
  intro f c hf hfc hshort
  exact twistedZeroSum_nonneg_of_sharpened_trivial_aperture hq hprim hle hf hfc hshort

/-- **Castelnuovo–Severi on the quadratic ring at the sharpened trivial aperture**: if `ζ` has a
certificate with margin `c₀` at half-width `a` and
`primeMass a + primeMass (a / 2) + archConstant χ ≤ log q`, then the quadratic ring pairing on a
packet of half-width `a` is at most `2 d₁ d₂ − c₀ ∫ f²`. -/
theorem tendsto_quadraticForm_le_degrees_of_sharpened_trivial_aperture [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {a c₀ : ℝ}
    (hcert : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-a) a →
      c₀ * (∫ x, ‖g x‖ ^ 2) ≤ (zetaZeroConfig.W g g).re)
    (hle : _root_.RHTower.FreeLagTrace.primeMass a +
      _root_.RHTower.FreeLagTrace.primeMass (a / 2) + archConstant χ ≤ Real.log q)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {c : ℝ}
    (hshort : ∀ u, a < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => quadraticForm χ f (3 * K) N +
          2 * weightedContact (idealWeight χ) f (3 * K) N) atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        c₀ * ∫ u, f u ^ 2 := by
  refine ⟨_, tendsto_quadraticForm_add_idealContact hq hprim hf hfc hK hsupp, ?_⟩
  have h1 := zeroSum_ge_of_certificate hcert hf hfc hshort
  have h2 := twistedZeroSum_nonneg_of_sharpened_trivial_aperture hq hprim hle hf hfc hshort
  linarith

/-! ### 3. The one-square theorem and removal of the exceptional square on even and nonnegative packets -/

/-- For a real zero `ρ ∈ Z.carrier` (`ρ.im = 0`) with offset `δ = ρ.re − 1/2`, the real part of its
Weil summand on a real packet `f` is `m_ρ (∫ f(u) e^{δu} du)(∫ f(u) e^{−δu} du)`, which equals the
hyperbolic difference of squares `m_ρ ((∫ f(u) cosh(δu) du)² − (∫ f(u) sinh(δu) du)²)`. -/
theorem re_Wsummand_real_zero_eq_cosh_sq_sub_sinh_sq (Z : ZeroConfig) {ρ : ℂ}
    (_hρ : ρ ∈ Z.carrier) (him : ρ.im = 0) {δ : ℝ} (hδ : ρ.re = 1 / 2 + δ)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re =
        (Z.mult ρ : ℝ) * ((∫ u, f u * Real.exp (δ * u)) * ∫ u, f u * Real.exp (-(δ * u))) ∧
      (Z.mult ρ : ℝ) * ((∫ u, f u * Real.exp (δ * u)) * ∫ u, f u * Real.exp (-(δ * u))) =
        (Z.mult ρ : ℝ) *
          ((∫ u, f u * Real.cosh (δ * u)) ^ 2 - (∫ u, f u * Real.sinh (δ * u)) ^ 2) := by
  have hγ : gammaOf ρ = ((0 : ℝ) : ℂ) - Complex.I * δ := by
    apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hδ, him]
  have hγc : conj (gammaOf ρ) = ((0 : ℝ) : ℂ) + Complex.I * δ := by
    rw [hγ]; apply Complex.ext <;> simp
  have hFpos : paperFT (fun u => (f u : ℂ)) (((0 : ℝ) : ℂ) - Complex.I * δ) =
      ((∫ u, f u * Real.exp (δ * u) : ℝ) : ℂ) := by
    rw [_root_.RHTower.paperFT_sub_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp
  have hFneg : paperFT (fun u => (f u : ℂ)) (((0 : ℝ) : ℂ) + Complex.I * δ) =
      ((∫ u, f u * Real.exp (-(δ * u)) : ℝ) : ℂ) := by
    rw [_root_.RHTower.paperFT_add_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp [neg_mul]
  constructor
  · rw [ZeroConfig.Wsummand, hγc, hγ, hFpos, hFneg, Complex.conj_ofReal]
    simp
    ring
  · have hcosh : Integrable fun u => f u * Real.cosh (δ * u) :=
      (hf.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hfc.mul_right
    have hsinh : Integrable fun u => f u * Real.sinh (δ * u) :=
      (hf.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hfc.mul_right
    have hexp_pos : (∫ u, f u * Real.exp (δ * u)) =
        (∫ u, f u * Real.cosh (δ * u)) + ∫ u, f u * Real.sinh (δ * u) := by
      rw [← integral_add hcosh hsinh]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show f u * Real.exp (δ * u) = f u * Real.cosh (δ * u) + f u * Real.sinh (δ * u)
      rw [← mul_add, Real.cosh_add_sinh]
    have hexp_neg : (∫ u, f u * Real.exp (-(δ * u))) =
        (∫ u, f u * Real.cosh (δ * u)) - ∫ u, f u * Real.sinh (δ * u) := by
      rw [← integral_sub hcosh hsinh]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show f u * Real.exp (-(δ * u)) = f u * Real.cosh (δ * u) - f u * Real.sinh (δ * u)
      rw [← mul_sub, Real.cosh_sub_sinh]
    rw [hexp_pos, hexp_neg]
    ring

/-- **Removal of the exceptional square on hyperbolic-orthogonal, even, and nonnegative packets**:
for any real zero `ρ ∈ Z.carrier` (`ρ.im = 0`), its contribution to `Re W_Z(f, f)` is nonnegative
whenever:
1. `∫ f(u) sinh((ρ.re − ½) u) du = 0`, or
2. `f` is even (`∀ u, f(−u) = f(u)`), or
3. `f` is nonnegative (`∀ u, 0 ≤ f(u)`). -/
theorem re_Wsummand_real_zero_nonneg (Z : ZeroConfig) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (him : ρ.im = 0) {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ((∫ u, f u * Real.sinh ((ρ.re - 1 / 2) * u)) = 0 →
        0 ≤ (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re) ∧
      ((∀ u, f (-u) = f u) →
        0 ≤ (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re) ∧
      ((∀ u, 0 ≤ f u) →
        0 ≤ (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re) := by
  obtain ⟨h1, h2⟩ := re_Wsummand_real_zero_eq_cosh_sq_sub_sinh_sq Z hρ him
    (show ρ.re = 1 / 2 + (ρ.re - 1 / 2) by ring) hf hfc
  refine ⟨fun horth => ?_, fun heven => ?_, fun hnn => ?_⟩
  · rw [h1, h2, horth, zero_pow two_ne_zero, sub_zero]
    positivity
  · have horth : (∫ u, f u * Real.sinh ((ρ.re - 1 / 2) * u)) = 0 := by
      have h := integral_neg_eq_self (fun u => f u * Real.sinh ((ρ.re - 1 / 2) * u)) volume
      simp only [heven, mul_neg, Real.sinh_neg] at h
      rw [integral_neg] at h
      linarith
    rw [h1, h2, horth, zero_pow two_ne_zero, sub_zero]
    positivity
  · rw [h1]
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (integral_nonneg fun u => mul_nonneg (hnn u) (Real.exp_pos _).le)
      (integral_nonneg fun u => mul_nonneg (hnn u) (Real.exp_pos _).le))

/-- **The one-square lower bound for a real zero pair (`A100` Part 2)**: for any real zero
`ρ ∈ Z.carrier` (`ρ.im = 0`) with `δ = ρ.re − 1/2 > 0` and any packet `f` supported in `[−a, a]`
(`a ≥ 0`), the pair `{ρ, 1 − conj ρ}` contributes at least
`−2 m_ρ pairEnergy(δ, a) ∫ f² = −m_ρ (sinh(2δa)/δ − 2a) ∫ f²`. -/
theorem re_Wsummand_real_zero_pair_ge_neg_two_pairEnergy (Z : ZeroConfig) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (him : ρ.im = 0) {δ : ℝ} (hδ : 0 < δ) (hre : ρ.re = 1 / 2 + δ)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a) :
    -2 * (Z.mult ρ : ℝ) * SquareRootThreshold.pairEnergy δ a * (∫ u, f u ^ 2) ≤
      (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ +
        Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (reflect ρ)).re ∧
      2 * SquareRootThreshold.pairEnergy δ a = Real.sinh (2 * δ * a) / δ - 2 * a := by
  constructor
  · have hF : Continuous fun u => (f u : ℂ) := Complex.continuous_ofReal.comp hf
    have hγ : gammaOf ρ = (0 : ℂ) - Complex.I * δ := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hre, him]
    have hγc : conj (gammaOf ρ) = (0 : ℂ) + Complex.I * δ := by
      rw [hγ]; apply Complex.ext <;> simp
    have hrefl : gammaOf (reflect ρ) = conj (gammaOf ρ) := by
      apply Complex.ext <;> simp [gammaOf, reflect] <;> ring
    have hpair_re := SquareRootThreshold.neg_half_normSq_sub_le_re_pair
      (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) - Complex.I * δ))
      (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) + Complex.I * δ))
    have hpair_norm := SquareRootThreshold.norm_sub_sq_le_pairEnergy hδ ha 0 hF hfs
    simp only [Complex.ofReal_zero] at hpair_norm
    rw [integral_norm_ofReal_sq] at hpair_norm
    have hsum : (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ +
          Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (reflect ρ)).re =
        (Z.mult ρ : ℝ) *
          (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) - Complex.I * δ) *
              conj (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) + Complex.I * δ)) +
            paperFT (fun u => (f u : ℂ)) ((0 : ℂ) + Complex.I * δ) *
              conj (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) - Complex.I * δ))).re := by
      rw [ZeroConfig.Wsummand, ZeroConfig.Wsummand,
        hrefl, Complex.conj_conj, Z.mult_reflect ρ hρ, hγc, hγ, ← Complex.re_ofReal_mul]
      push_cast
      congr 1
      ring
    rw [hsum]
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have hcomb : -(2 * SquareRootThreshold.pairEnergy δ a * ∫ u, f u ^ 2) ≤
        (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) - Complex.I * δ) *
            conj (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) + Complex.I * δ)) +
          paperFT (fun u => (f u : ℂ)) ((0 : ℂ) + Complex.I * δ) *
            conj (paperFT (fun u => (f u : ℂ)) ((0 : ℂ) - Complex.I * δ))).re := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hcomb hm0
    linarith
  · unfold SquareRootThreshold.pairEnergy
    have hδ0 : δ ≠ 0 := hδ.ne'
    field_simp

/-! ### 4. Deuring–Heilbronn on the twisted comb (`A101`) and resolution at logarithmic aperture (`B154`) -/

/-- Every Dirichlet character whose values have zero imaginary part is quadratic
(`χ(a) ∈ {0, 1, −1}`). -/
theorem isQuadratic_of_im_eq_zero [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · have hnorm := _root_.RHTower.norm_dirichletCharacter_apply χ ha
    have heq : χ a = ((χ a).re : ℂ) := Complex.ext rfl (by simp [hreal a])
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at hnorm
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hnorm with h1 | h1
    · exact Or.inr (Or.inl (by rw [heq, h1, Complex.ofReal_one]))
    · exact Or.inr (Or.inr (by rw [heq, h1, Complex.ofReal_neg, Complex.ofReal_one]))
  · exact Or.inl (χ.map_nonunit ha)

/-- **Unconditional uniform local zero count of `L(s, χ)` in `ZeroConfig.N` form.** -/
theorem exists_dirichletZeros_local_count :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (q : ℕ) [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
      (hprim : χ.IsPrimitive) (t : ℝ),
      ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ) ≤
        A₀ * (Real.log q + 1) * Real.log (|t| + 3) := by
  obtain ⟨A, hloc⟩ : ∃ A : ℝ, ∀ (q : ℕ) [NeZero q] (hq : 1 < q)
      {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (t : ℝ),
      ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ) ≤
        A * (Real.log q + Real.log (|t| + 3)) := by
    refine ⟨2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84), fun q _ hq χ hprim t => ?_⟩
    have hN := Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of hq hprim) t (t + 1)
    have h := _root_.RHTower.localCountChi_uniform' hq hprim t
    rw [← hN] at h
    exact h
  refine ⟨max 1 A, le_max_left 1 A, fun q _ hq χ hprim t => ?_⟩
  have h1 : ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ) ≤
      A * (Real.log q + Real.log (|t| + 3)) := hloc q hq hprim t
  have hA' : A ≤ max 1 A := le_max_right 1 A
  have hlog3 : 1 ≤ Real.log (|t| + 3) := _root_.RHTower.one_le_log_abs_add_three t
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have h2 : Real.log q + Real.log (|t| + 3) ≤ (Real.log q + 1) * Real.log (|t| + 3) := by
    nlinarith
  have h3 : 0 ≤ Real.log q + Real.log (|t| + 3) := by linarith
  calc ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ)
      ≤ A * (Real.log q + Real.log (|t| + 3)) := h1
    _ ≤ max 1 A * (Real.log q + Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_right hA' h3
    _ ≤ max 1 A * ((Real.log q + 1) * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (le_max_left 1 A))
    _ = max 1 A * (Real.log q + 1) * Real.log (|t| + 3) := by ring

/-- **Simplicity and uniqueness of the exceptional zero on the twisted comb (`A101` Part 1)**:
there exists an absolute constant `C > 0` such that for every real primitive character `χ (mod q)`
(`q > 1`) and every real zero `β ∈ [1/2, 1)` of `L(s, χ)` in the exceptional region
`1 − 1 / (e C (1 + log q + log 3)) < β < 1`:
1. Any two multiplicity copies `i₁, j : ExceptionalZeroCopy χ` in `[1/2, 1)` with
   `1 − 1 / (e C (1 + log q + log 3)) < Re(exceptionalZero χ j)` at real points coincide (`j = i₁`),
   so `(β : ℂ)` is a simple zero of the completed divisor `exceptionalCompletion χ`.
2. Any real zero `β' ∈ [1/2, 1)` of `L(s, χ)` satisfying
   `1 − 1 / (e C log(3q)) < β'` coincides with `β` (`β' = β`). -/
theorem exceptional_zero_unique_and_simple :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
        (hprim : χ.IsPrimitive), (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, (β : ℂ) ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier →
        (∀ (i₁ j : ExceptionalLayerTheory.ExceptionalZeroCopy χ) (β' : ℝ),
          ExceptionalLayerTheory.exceptionalZero χ i₁ = (β : ℂ) →
          ExceptionalLayerTheory.exceptionalZero χ j = (β' : ℂ) →
          1 / 2 ≤ β' →
          1 - 1 / (Real.exp 1 * C * (1 + Real.log q + Real.log 3)) < β →
          1 - 1 / (Real.exp 1 * C * (1 + Real.log q + Real.log 3)) < β' →
          j = i₁) ∧
        (∀ β' : ℝ, (β' : ℂ) ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier →
          1 / 2 ≤ β' →
          1 - 1 / (Real.exp 1 * C * Real.log ((q : ℝ) * 3)) < β →
          1 - 1 / (Real.exp 1 * C * Real.log ((q : ℝ) * 3)) < β' →
          β' = β) := by
  obtain ⟨C₁, hC₁, hDH₁⟩ := ExceptionalLayerTheory.exists_dirichlet_exceptional_zero_repulsion
  obtain ⟨C₂, hC₂, hDH₂⟩ := ExceptionalLayerTheory.exists_deuring_heilbronn_repulsion
  set C := max C₁ C₂
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left C₁ C₂)
  refine ⟨C, hC, fun q inst hq χ hprim hreal β hβ_mem => ?_⟩
  haveI := inst
  have hχ : χ ≠ 1 := _root_.RHTower.ne_one_of_isPrimitive hq hprim
  have hquad : χ.IsQuadratic := isQuadratic_of_im_eq_zero hreal
  have hβ_zero : Zeta23.ThmE.IsNontrivialZeroL χ (β : ℂ) := by
    rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hβ_mem
  have hβ0 : 0 < β := by simpa using hβ_zero.2.1
  have hβ1 : β < 1 := by simpa using hβ_zero.2.2
  have hη : 0 < 1 - β := by linarith
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hexp1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  constructor
  · intro i₁ j β' hi₁ hj hβ'12 hclose hclose'
    by_contra hne
    have hrep := hDH₁ χ hχ hprim hquad i₁ j β hi₁ hne (by rw [hj, Complex.ofReal_re]; exact hβ'12)
    rw [hj, Complex.ofReal_re, Complex.ofReal_im] at hrep
    set L := ExceptionalLayerTheory.exceptionalHeightLog q 0
    have hL_eq : L = 1 + Real.log q + Real.log 3 := by
      dsimp [L, ExceptionalLayerTheory.exceptionalHeightLog]; rw [abs_zero, zero_add]
    have hL0 : 0 < L := by
      rw [hL_eq]
      have : 0 < Real.log q := Real.log_pos hq1
      have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
      linarith
    have hC₁_le : C₁ ≤ C := le_max_left C₁ C₂
    have hprod_lt : C₁ * (1 - β) * L < (Real.exp 1)⁻¹ := by
      have h1 : 1 - β < 1 / (Real.exp 1 * C * L) := by rw [← hL_eq] at hclose; linarith
      have h2 : C₁ * (1 - β) * L ≤ C * (1 - β) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁_le hη.le) hL0.le
      have h3 : C * (1 - β) * L < 1 / Real.exp 1 := by
        have := (lt_div_iff₀ (mul_pos (mul_pos (Real.exp_pos 1) hC) hL0)).mp h1
        rw [lt_div_iff₀ (Real.exp_pos 1)]
        linarith
      rw [← one_div]
      exact h2.trans_lt h3
    have hexp_lt : Real.exp 1 < 1 / (C₁ * (1 - β) * L) := by
      have := one_div_lt_one_div_of_lt (mul_pos (mul_pos hC₁ hη) hL0) hprod_lt
      rwa [one_div, inv_inv] at this
    have hlog_gt : 1 < Real.log (1 / (C₁ * (1 - β) * L)) := by
      have := Real.log_lt_log (Real.exp_pos 1) hexp_lt
      rwa [Real.log_exp] at this
    have hdiv1 : 1 / (C₁ * L) < Real.log (1 / (C₁ * (1 - β) * L)) / (C₁ * L) :=
      div_lt_div_of_pos_right hlog_gt (mul_pos hC₁ hL0)
    have hdiv2 : 1 / (Real.exp 1 * C * L) ≤ 1 / (C₁ * L) := by
      refine one_div_le_one_div_of_le (mul_pos hC₁ hL0) ?_
      have : C₁ * 1 ≤ Real.exp 1 * C := by nlinarith
      nlinarith
    rw [← hL_eq] at hclose'
    linarith
  · intro β' hβ'_mem hβ'12 hclose hclose'
    by_contra hne
    have hβ'_zero : Zeta23.ThmE.IsNontrivialZeroL χ (β' : ℂ) := by
      rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hβ'_mem
    have hβ'1 : β' < 1 := by simpa using hβ'_zero.2.2
    have hne_c : (β' : ℂ) ≠ (β : ℂ) := by exact_mod_cast hne
    have hβ'_ne1 : (β' : ℂ) ≠ 1 := by exact_mod_cast hβ'1.ne
    have hrep := hDH₂ χ hχ hprim hquad β (β' : ℂ) hβ0 hβ_zero.1
      (by simpa using hβ'12) hβ'_ne1 (Or.inr hβ'_zero.1) hne_c
    simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re] at hrep
    set Q := Real.log ((q : ℝ) * 3)
    have hQ0 : 0 < Q := Real.log_pos (by nlinarith)
    have hC₂_le : C₂ ≤ C := le_max_right C₁ C₂
    have hprod_lt : C₂ * (1 - β) * Q < (Real.exp 1)⁻¹ := by
      have h1 : 1 - β < 1 / (Real.exp 1 * C * Q) := by linarith
      have h2 : C₂ * (1 - β) * Q ≤ C * (1 - β) * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂_le hη.le) hQ0.le
      have h3 : C * (1 - β) * Q < 1 / Real.exp 1 := by
        have := (lt_div_iff₀ (mul_pos (mul_pos (Real.exp_pos 1) hC) hQ0)).mp h1
        rw [lt_div_iff₀ (Real.exp_pos 1)]
        linarith
      rw [← one_div]
      exact h2.trans_lt h3
    have hexp_lt : Real.exp 1 < 1 / (C₂ * (1 - β) * Q) := by
      have := one_div_lt_one_div_of_lt (mul_pos (mul_pos hC₂ hη) hQ0) hprod_lt
      rwa [one_div, inv_inv] at this
    have hlog_gt : 1 < Real.log (1 / (C₂ * (1 - β) * Q)) := by
      have := Real.log_lt_log (Real.exp_pos 1) hexp_lt
      rwa [Real.log_exp] at this
    have hdiv1 : 1 / (C₂ * Q) < Real.log (1 / (C₂ * (1 - β) * Q)) / (C₂ * Q) :=
      div_lt_div_of_pos_right hlog_gt (mul_pos hC₂ hQ0)
    have hdiv2 : 1 / (Real.exp 1 * C * Q) ≤ 1 / (C₂ * Q) := by
      refine one_div_le_one_div_of_le (mul_pos hC₂ hQ0) ?_
      have : C₂ * 1 ≤ Real.exp 1 * C := by nlinarith
      nlinarith
    linarith

/-- At ordinate `γ₀ = 0`, `_root_.RHTower.modulatedTest 0 s` is the packet embedding
`fun u => (s u : ℂ)`. -/
theorem modulatedTest_zero_eq_ofReal (s : ℝ → ℝ) :
    _root_.RHTower.modulatedTest 0 s = fun u => (s u : ℂ) := by
  funext u
  simp [_root_.RHTower.modulatedTest]

/-- **Deuring–Heilbronn on the twisted comb and repulsion from window positivity (`A101` & `B154`)**:
there exist absolute constants `C > 0` and `A₀ ≥ 1` such that for every real primitive character
`χ` of conductor `q > 1` and every real zero `β = ½ + δ ∈ (½, 1)` of `L(s, χ)`:
1. **Critical-line clearing of the strip**: if
   `C (1 − β) log(q(R + 3)) < (q(R + 3))^{-C/2}` (`R ≥ 0`), then every other zero `ρ ≠ β, 1 − β`
   of `L(s, χ)` with `|Im ρ| ≤ R` lies on the critical line `Re ρ = 1 / 2`.
2. **Isolation of the exceptional square on odd packets**: under the same condition, for every
   aperture `a ≥ 0` and every odd `C²` packet `s` supported in `[−a, a]`,
   `Z_χ(s) ≤ −2 m_β (∫ s(u) sinh(δu) du)² + 384 A₀ (log 3)(log q + 1) testNorm(s)² (1 + e^a / (1 + R))`.
3. **Repulsion from `Z_χ ≥ 0` at aperture `a`**: if `Z_χ(f) ≥ 0` holds on smooth odd packets
   supported in `[−a, a]` and, for some `0 < w ≤ a / 4` and `R ≥ 0`,
   `384 A₀ (log 3)(log q + 1) N_b(a, δ)² (1 + e^a / (1 + R)) < 2 (w (wa)^{5/2} sinh²(δ(a − 2w)))²`,
   then `1 − β` satisfies the unconditional lower bound
   `(q(R + 3))^{-C/2} / (C log(q(R + 3))) ≤ 1 − β`. -/
theorem deuring_heilbronn_on_twisted_comb :
    ∃ (C A₀ : ℝ), 0 < C ∧ 1 ≤ A₀ ∧
      ∀ (q : ℕ) [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
        (hprim : χ.IsPrimitive), (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β δ : ℝ, 0 < δ → β = 1 / 2 + δ →
        (β : ℂ) ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier →
        ∀ R : ℝ, 0 ≤ R →
        (C * (1 - β) * Real.log ((q : ℝ) * (R + 3)) < ((q : ℝ) * (R + 3)) ^ (-C / 2) →
          (∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
            ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) → |ρ.im| ≤ R → ρ.re = 1 / 2) ∧
          (∀ (a : ℝ), 0 ≤ a → ∀ (s : ℝ → ℝ), ContDiff ℝ 2 s →
            (∀ u, s (-u) = -s u) → (∀ u, s u ≠ 0 → |u| ≤ a) →
            twistedZeroSum hq hprim s ≤
              -2 * ((_root_.RHTower.dirichletZeros hq hprim).mult (β : ℂ) : ℝ) *
                  (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
                384 * (A₀ * (Real.log q + 1)) * Real.log 3 *
                  _root_.RHTower.testNorm s ^ 2 * (1 + Real.exp a / (1 + R)))) ∧
        (∀ (a w : ℝ), 0 < w → w ≤ a / 4 →
          (∀ s : ℝ → ℝ, ContDiff ℝ 2 s → (∀ u, s (-u) = -s u) →
            tsupport (fun u => (s u : ℂ)) ⊆ Set.Icc (-a) a →
            0 ≤ twistedZeroSum hq hprim s) →
          384 * (A₀ * (Real.log q + 1)) * Real.log 3 *
              (2 * a * Real.cosh (δ * a) *
                (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
              (1 + Real.exp a / (1 + R)) <
            2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
          ((q : ℝ) * (R + 3)) ^ (-C / 2) / (C * Real.log ((q : ℝ) * (R + 3))) ≤ 1 - β) := by
  obtain ⟨C, hC, hDH⟩ := ExceptionalLayerTheory.exists_deuring_heilbronn_repulsion
  obtain ⟨A₀, hA₀, hloc⟩ := exists_dirichletZeros_local_count
  refine ⟨C, A₀, hC, hA₀, fun q inst hq χ hprim hreal β δ hδ hre hβ_mem R hR => ?_⟩
  haveI := inst
  have hχ : χ ≠ 1 := _root_.RHTower.ne_one_of_isPrimitive hq hprim
  have hquad : χ.IsQuadratic := isQuadratic_of_im_eq_zero hreal
  have hβ_zero : Zeta23.ThmE.IsNontrivialZeroL χ (β : ℂ) := by
    rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hβ_mem
  have hβ0 : 0 < β := by simpa using hβ_zero.2.1
  have hβ12 : 1 / 2 < β := by linarith
  have hβ1 : β < 1 := by simpa using hβ_zero.2.2
  have hη0 : 0 < 1 - β := by linarith
  have hA_ge : 1 ≤ A₀ * (Real.log q + 1) := by
    have : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    nlinarith
  have hno_half : ∀ (ρ : ℂ), 1 / 2 ≤ ρ.re → ρ.re < 1 → ρ ≠ (β : ℂ) → χ.LFunction ρ = 0 →
      C * (1 - β) * Real.log ((q : ℝ) * (|ρ.im| + 3)) <
        ((q : ℝ) * (|ρ.im| + 3)) ^ (-C / 2) → False := by
    intro ρ hre_ge hre_lt1 hne hLρ hlt_ρ
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hre_lt1; exact lt_irrefl 1 hre_lt1
    have hrep := hDH χ hχ hprim hquad β ρ hβ0 hβ_zero.1 hre_ge hρ1 (Or.inr hLρ) hne
    set B := (q : ℝ) * (|ρ.im| + 3)
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
    have hB3 : 3 < B := by
      have : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
      dsimp [B]; nlinarith
    have hB0 : 0 < B := by linarith
    set Q := Real.log B
    have hQ0 : 0 < Q := Real.log_pos (by linarith)
    have hrpow : B ^ (-C / 2) = (Real.exp (C * Q / 2))⁻¹ := by
      rw [Real.rpow_def_of_pos hB0, ← Real.exp_neg]
      congr 1; dsimp [Q]; ring
    rw [hrpow, ← one_div] at hlt_ρ
    have hexp_lt : Real.exp (C * Q / 2) < 1 / (C * (1 - β) * Q) := by
      have := one_div_lt_one_div_of_lt (mul_pos (mul_pos hC hη0) hQ0) hlt_ρ
      rwa [one_div_one_div] at this
    have hlog_gt : C * Q / 2 < Real.log (1 / (C * (1 - β) * Q)) := by
      have := Real.log_lt_log (Real.exp_pos _) hexp_lt
      rwa [Real.log_exp] at this
    have hdiv_gt : 1 / 2 < Real.log (1 / (C * (1 - β) * Q)) / (C * Q) := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (mul_pos hC hQ0)]
      linarith
    linarith
  have hiso_of_lt : C * (1 - β) * Real.log ((q : ℝ) * (R + 3)) < ((q : ℝ) * (R + 3)) ^ (-C / 2) →
      ∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
        ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) → |ρ.im| ≤ R → ρ.re = 1 / 2 := by
    intro hlt ρ hρ hne1 hne2 him
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
    have hbase_le : (q : ℝ) * (|ρ.im| + 3) ≤ (q : ℝ) * (R + 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hbase_gt1 : 1 < (q : ℝ) * (|ρ.im| + 3) := by
      have : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
      nlinarith
    have hlog_le : Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ Real.log ((q : ℝ) * (R + 3)) :=
      Real.log_le_log (by positivity) hbase_le
    have hpow_le : ((q : ℝ) * (R + 3)) ^ (-C / 2) ≤ ((q : ℝ) * (|ρ.im| + 3)) ^ (-C / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase_le (by linarith)
    have hlt_ρ : C * (1 - β) * Real.log ((q : ℝ) * (|ρ.im| + 3)) <
        ((q : ℝ) * (|ρ.im| + 3)) ^ (-C / 2) := by
      have h1 : C * (1 - β) * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤
          C * (1 - β) * Real.log ((q : ℝ) * (R + 3)) :=
        mul_le_mul_of_nonneg_left hlog_le (by positivity)
      linarith
    rcases lt_or_ge ρ.re (1 / 2) with hre_lt | hre_ge
    · have hrefl_mem : reflect ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier :=
        (_root_.RHTower.dirichletZeros hq hprim).reflect_mem ρ hρ
      have hrefl_zero : Zeta23.ThmE.IsNontrivialZeroL χ (reflect ρ) := by
        rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hrefl_mem
      have hrefl_re12 : 1 / 2 ≤ (reflect ρ).re := by
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      have hrefl_ne : reflect ρ ≠ (β : ℂ) := by
        intro h
        apply hne2
        have h1 := congrArg reflect h
        have h2 : reflect (reflect ρ) = ρ := by
          apply Complex.ext <;> simp [reflect]
        rw [h2] at h1
        exact h1
      have hrefl_im : |(reflect ρ).im| = |ρ.im| := by simp [reflect]
      have hlt_refl : C * (1 - β) * Real.log ((q : ℝ) * (|(reflect ρ).im| + 3)) <
          ((q : ℝ) * (|(reflect ρ).im| + 3)) ^ (-C / 2) := by
        rwa [hrefl_im]
      exact False.elim (hno_half (reflect ρ) hrefl_re12 hrefl_zero.2.2 hrefl_ne hrefl_zero.1 hlt_refl)
    · have hρ_zero : Zeta23.ThmE.IsNontrivialZeroL χ ρ := by
        rwa [_root_.RHTower.dirichletZeros, Zeta23.ThmE.LZeros_carrier] at hρ
      exact False.elim (hno_half ρ hre_ge hρ_zero.2.2 hne1 hρ_zero.1 hlt_ρ)
  refine ⟨fun hlt => ⟨hiso_of_lt hlt, fun a ha s hs hodd hsupp => ?_⟩,
    fun a w hw hwa hpos hbig => ?_⟩
  · have hiso := hiso_of_lt hlt
    have hiso' : ∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
        ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) → |ρ.im - (β : ℂ).im| ≤ R → ρ.re = 1 / 2 := by
      intro ρ hρ hne1 hne2 him
      rw [Complex.ofReal_im, sub_zero] at him
      exact hiso ρ hρ hne1 hne2 him
    have hre' : (β : ℂ).re = 1 / 2 + δ := by simp [hre]
    have hmod := _root_.RHTower.re_W_modulatedTest_le_of_isolated
      (_root_.RHTower.dirichletZeros hq hprim) hA_ge (hloc q hq hprim) hβ_mem hδ hre' ha hR
      hiso' hs hodd hsupp
    simpa [Complex.ofReal_im, modulatedTest_zero_eq_ofReal, twistedZeroSum] using hmod
  · by_contra hnot
    push Not at hnot
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
    have hR0 : 0 ≤ R := hR
    have hlog_pos : 0 < C * Real.log ((q : ℝ) * (R + 3)) :=
      mul_pos hC (Real.log_pos (by nlinarith))
    have hlt : C * (1 - β) * Real.log ((q : ℝ) * (R + 3)) < ((q : ℝ) * (R + 3)) ^ (-C / 2) := by
      have := (lt_div_iff₀ hlog_pos).mp hnot
      linarith
    have hiso := hiso_of_lt hlt
    have hiso' : ∀ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
        ρ ≠ (β : ℂ) → ρ ≠ reflect (β : ℂ) → |ρ.im - (β : ℂ).im| ≤ R → ρ.re = 1 / 2 := by
      intro ρ hρ hne1 hne2 him
      rw [Complex.ofReal_im, sub_zero] at him
      exact hiso ρ hρ hne1 hne2 him
    have ha : 0 < a := by linarith
    have hre' : (β : ℂ).re = 1 / 2 + δ := by simp [hre]
    have hmaster := _root_.RHTower.re_W_modulatedTest_le_of_isolated
      (_root_.RHTower.dirichletZeros hq hprim) hA_ge (hloc q hq hprim) hβ_mem hδ hre' ha.le hR
      hiso' (_root_.RHTower.sinhTest_contDiff a δ) (_root_.RHTower.sinhTest_odd a δ)
      (_root_.RHTower.sinhTest_supp ha.le)
    rw [Complex.ofReal_im, modulatedTest_zero_eq_ofReal, abs_zero, zero_add] at hmaster
    have hP := _root_.RHTower.sinhTest_energy_ge (a := a) hδ hw hwa
    have hN := _root_.RHTower.testNorm_sinhTest_le ha.le hδ.le
    have hN0 := _root_.RHTower.testNorm_nonneg (_root_.RHTower.sinhTest a δ)
    have hm : (1 : ℝ) ≤ (_root_.RHTower.dirichletZeros hq hprim).mult (β : ℂ) := by
      exact_mod_cast (_root_.RHTower.dirichletZeros hq hprim).one_le_mult (β : ℂ) hβ_mem
    have hPl0 : 0 ≤ w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 := by positivity
    have hP2 := pow_le_pow_left₀ hPl0 hP 2
    have hN2 := pow_le_pow_left₀ hN0 hN 2
    have h1 : (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 ≤
        ((_root_.RHTower.dirichletZeros hq hprim).mult (β : ℂ) : ℝ) *
          (∫ u, _root_.RHTower.sinhTest a δ u * Real.sinh (δ * u)) ^ 2 :=
      calc (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2
          ≤ 1 * (∫ u, _root_.RHTower.sinhTest a δ u * Real.sinh (δ * u)) ^ 2 := by linarith
        _ ≤ ((_root_.RHTower.dirichletZeros hq hprim).mult (β : ℂ) : ℝ) *
              (∫ u, _root_.RHTower.sinhTest a δ u * Real.sinh (δ * u)) ^ 2 :=
            mul_le_mul_of_nonneg_right hm (sq_nonneg _)
    have h2 : 384 * (A₀ * (Real.log q + 1)) * Real.log 3 *
          _root_.RHTower.testNorm (_root_.RHTower.sinhTest a δ) ^ 2 *
          (1 + Real.exp a / (1 + R)) ≤
        384 * (A₀ * (Real.log q + 1)) * Real.log 3 *
          (2 * a * Real.cosh (δ * a) *
            (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
          (1 + Real.exp a / (1 + R)) := by
      have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
      gcongr
    have hneg : twistedZeroSum hq hprim (_root_.RHTower.sinhTest a δ) < 0 := by
      unfold twistedZeroSum
      linarith
    have hts : tsupport (fun u => (_root_.RHTower.sinhTest a δ u : ℂ)) ⊆ Set.Icc (-a) a := by
      simpa [modulatedTest_zero_eq_ofReal] using
        _root_.RHTower.tsupport_modulatedTest_subset 0 (_root_.RHTower.sinhTest_supp ha.le)
    have hnonneg := hpos (_root_.RHTower.sinhTest a δ)
      (_root_.RHTower.sinhTest_contDiff a δ) (_root_.RHTower.sinhTest_odd a δ) hts
    linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
