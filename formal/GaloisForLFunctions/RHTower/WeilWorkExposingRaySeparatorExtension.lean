import GaloisForLFunctions.RHTower.WeilWorkExposingRayFibreTransfer
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction

/-!
# Bounded spectral separators extend from polar to full sources

For every real arithmetic coefficient sequence and bounded real linear
functional on spectral L1, its lower bound on all actual compact complex C2
polar sources is equivalent to its lower bound on every compact complex C2
source. There are no growth, positivity, RH or recovery premises.

The functional norm gives a constant polar mass bound. The preceding
FibreTransfer theorem transfers that bound to full sources. Its mass-deficit
translation kernel is positive definite, so the exact far-polar correction
converges in the arithmetic form, with error at most (2*c+c^2)*Q(f).
The same factor bounds spectral L1 error. Both polar zeros are proved for
the actual corrected source, and the arithmetic limit is established before
passing the separator inequality to the full source.

This proves section4 of the all-fibre paper argument. Far polarization alone
does not preserve the integer trace; the exact-fibre separation step remains
separate. No archimedean-energy bound or WP02 lower inequality is asserted.

Paper: docs/reports/weil-work/results/02-exposing-ray/POLAR-FIBRE-DENSITY-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral

/-- The mass minus raw integer-atom functional; compact support makes its sum finite. -/
def atomicForm (b : ℕ → ℝ) (C : ℝ) (k : ℝ → ℂ) : ℂ :=
  (C : ℂ) * k 0 - ∑' n : ℕ, ((if 2 ≤ n then b n else 0 : ℝ) : ℂ) *
    (k (Real.log n) + k (-Real.log n))

theorem atomicForm_add (b : ℕ → ℝ) (C : ℝ) {k l : ℝ → ℂ}
    (hk : HasCompactSupport k) (hl : HasCompactSupport l) :
    atomicForm b C (k+l) = atomicForm b C k + atomicForm b C l := by
  have ht := (summable_primeAtoms (fun n => if 2 ≤ n then b n else 0) hk).tsum_add
    (summable_primeAtoms (fun n => if 2 ≤ n then b n else 0) hl)
  unfold atomicForm
  simp only [Pi.add_apply]
  have he : (∑' n : ℕ, ((if 2 ≤ n then b n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + l (Real.log n) + (k (-Real.log n) + l (-Real.log n)))) =
      (∑' n : ℕ, ((if 2 ≤ n then b n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) +
      ∑' n : ℕ, ((if 2 ≤ n then b n else 0 : ℝ) : ℂ) *
        (l (Real.log n) + l (-Real.log n)) := by
    rw [← ht]
    apply tsum_congr; intro n; ring
  rw [he]; ring

theorem atomicForm_smul (b : ℕ → ℝ) (C : ℝ) (a : ℂ) (k : ℝ → ℂ) :
    atomicForm b C (a • k) = a * atomicForm b C k := by
  unfold atomicForm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, ← tsum_mul_left]
  congr 1
  · ring
  · apply tsum_congr; intro n; ring

theorem atomicForm_zero (b : ℕ → ℝ) (C : ℝ) : atomicForm b C 0 = 0 := by
  simp [atomicForm]

theorem atomicForm_sum (b : ℕ → ℝ) (C : ℝ) {ι : Type*}
    (s : Finset ι) {k : ι → ℝ → ℂ} (hk : ∀ i ∈ s, HasCompactSupport (k i)) :
    atomicForm b C (∑ i ∈ s, k i) = ∑ i ∈ s, atomicForm b C (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [atomicForm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      atomicForm_add b C (hk a (Finset.mem_insert_self a s))
        (HasCompactSupport.finset_sum fun i hi => hk i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hk i (Finset.mem_insert_of_mem hi)]

private theorem atomicForm_tilde (b : ℕ → ℝ) (C : ℝ) (k : ℝ → ℂ) :
    atomicForm b C (EF.tilde k) = conj (atomicForm b C k) := by
  unfold atomicForm
  rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_tsum]
  simp only [EF.tilde, neg_zero, neg_neg]
  congr 1
  apply tsum_congr; intro n
  simp only [map_mul, map_add, Complex.conj_ofReal]
  ring

private theorem atomicForm_corr_im (b : ℕ → ℝ) (C : ℝ) (f : ℝ → ℂ) :
    (atomicForm b C (EF.weilTest f f)).im = 0 := by
  have h := atomicForm_tilde b C (EF.weilTest f f)
  rw [tilde_weilTest_self] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

private theorem corr_zero (f : ℝ → ℂ) :
    EF.weilTest f f 0 = ((∫ x : ℝ, ‖f x‖^2 : ℝ) : ℂ) := by
  rw [WeilSpectral.weilTest_apply]
  simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact integral_ofReal

/-- The infinite notation is exactly the finite raw-atom form on each aperture. -/
theorem atomicForm_corr_re (b : ℕ → ℝ) (C : ℝ) {f : ℝ → ℂ} {a : ℝ}
    (hfs : tsupport f ⊆ Icc (-a) a) :
    (atomicForm b C (EF.weilTest f f)).re =
      C * (∫ x : ℝ, ‖f x‖^2) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n * atomCoeff f n := by
  have hs : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
  have hsum := summable_primeAtoms (fun n => if 2 ≤ n then b n else 0)
    (EF.weilTest_hasCompactSupport hs hs)
  unfold atomicForm
  rw [Complex.sub_re, corr_zero, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.re_tsum hsum]
  congr 1
  rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2*a)⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [if_pos (Finset.mem_Icc.mp hn).1, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, atomCoeff]
  · intro n hn
    by_cases hn2 : 2 ≤ n
    · have hlarge : ⌊Real.exp (2*a)⌋₊ < n := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      simp only [if_pos hn2, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      change b n * atomCoeff f n = 0
      rw [atomCoeff_eq_zero_of_floor_lt hfs hlarge, mul_zero]
    · simp [hn2]

private theorem atomicForm_nonneg {b : ℕ → ℝ} {C : ℝ} (h : FullMassBound b C)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    0 ≤ (atomicForm b C (EF.weilTest f f)).re := by
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hs
  have hfs : tsupport f ⊆ Icc (-a) a := by
    apply closure_minimal
    · intro x hx; exact abs_le.mp (ha x hx)
    · exact isClosed_Icc
  rw [atomicForm_corr_re b C hfs]
  exact sub_nonneg.mpr (h a f hf hfs)

/-- The translation kernel of the mass deficit. -/
def atomicKernel (b : ℕ → ℝ) (C : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  atomicForm b C (WeilSpectral.transl y (EF.weilTest f f))

theorem atomicForm_packet (b : ℕ → ℝ) (C : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) {N : ℕ}
    (t : Fin N → ℝ) (c : Fin N → ℂ) :
    atomicForm b C (EF.weilTest (∑ j, c j • WeilSpectral.transl (t j) f) (∑ j, c j • WeilSpectral.transl (t j) f)) =
      ∑ i, ∑ j, star (c i) * atomicKernel b C f (t j-t i) * c j := by
  have hcorr := EF.weilTest_hasCompactSupport hs hs
  have ht (y : ℝ) : HasCompactSupport (WeilSpectral.transl y (EF.weilTest f f)) :=
    hcorr.comp_homeomorph (Homeomorph.subRight y)
  have hterms (i j : Fin N) : HasCompactSupport
      ((star (c i)*c j) • WeilSpectral.transl (t j-t i) (EF.weilTest f f)) := (ht _).smul_left
  rw [weilTest_sum_transl hf hs,
    atomicForm_sum b C Finset.univ (fun i _ =>
      HasCompactSupport.finset_sum (fun j _ => hterms i j))]
  apply Finset.sum_congr rfl; intro i _
  rw [atomicForm_sum b C Finset.univ (fun j _ => hterms i j)]
  apply Finset.sum_congr rfl; intro j _
  rw [atomicForm_smul, atomicKernel]
  ring

/-- A polar mass bound already controls the full translation kernel. -/
theorem positiveDefinite_atomicKernel {b : ℕ → ℝ} {C : ℝ} (h : PolarMassBound b C)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal (atomicKernel b C f) := by
  have hfull := (polarMassBound_iff_fullMassBound b C).mp h
  intro N t c
  let g : ℝ → ℂ := ∑ j, c j • WeilSpectral.transl (t j) f
  have hgc : ContDiff ℝ 2 g := by
    have he : g = fun x => ∑ j, c j * f (x-t j) := by
      funext x; simp [g, Finset.sum_apply, WeilSpectral.transl]
    rw [he]
    exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))
  have hgs : HasCompactSupport g :=
    HasCompactSupport.finset_sum fun j _ =>
      (hs.comp_homeomorph (Homeomorph.subRight (t j))).smul_left
  refine ⟨(atomicForm b C (EF.weilTest g g)).re, atomicForm_nonneg hfull hgc hgs, ?_⟩
  rw [← atomicForm_packet b C hf.continuous hs]
  exact Complex.ext rfl (by simpa using atomicForm_corr_im b C g)


/-- Exact characterization by all positive translation kernels. -/
theorem polarMassBound_iff_positiveDefinite_atomicKernel (b : ℕ → ℝ) (C : ℝ) :
    PolarMassBound b C ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal (atomicKernel b C f) := by
  constructor
  · intro h f hf hs; exact positiveDefinite_atomicKernel h hf hs
  · intro h a f hp
    have hs : HasCompactSupport f :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hp.2.2.1
    have hz := (h f hp.2.1 hs).zero.1
    have he : atomicKernel b C f 0 = atomicForm b C (EF.weilTest f f) := by
      change atomicForm b C (fun x => EF.weilTest f f (x-0)) = _
      simp only [sub_zero]
    rw [he, atomicForm_corr_re b C hp.2.2.1] at hz
    linarith

/-- Generic far polarization, with the two translates kept in the actual source. -/
def farSource (X : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  f - ((farPolarCoeff X : ℂ) / 2) • (WeilSpectral.transl X f + WeilSpectral.transl (-X) f)

theorem farSource_packet (X : ℝ) (f : ℝ → ℂ) :
    farSource X f = ∑ j : Fin 3,
      (![1, -(farPolarCoeff X : ℂ)/2, -(farPolarCoeff X : ℂ)/2] j) •
        WeilSpectral.transl (![0, X, -X] j) f := by
  funext x
  simp [farSource, Fin.sum_univ_succ, WeilSpectral.transl, sub_eq_add_neg]
  ring

theorem atomicForm_farSource (b : ℕ → ℝ) (C : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (X : ℝ) :
    atomicForm b C (EF.weilTest (farSource X f) (farSource X f)) =
      atomicKernel b C f 0 - (farPolarCoeff X : ℂ) *
        (atomicKernel b C f X + atomicKernel b C f (-X)) +
      (farPolarCoeff X : ℂ)^2/4 *
        (2*atomicKernel b C f 0 + atomicKernel b C f (2*X) + atomicKernel b C f (-(2*X))) := by
  rw [farSource_packet, atomicForm_packet b C hf hs]
  simp [Fin.sum_univ_succ]
  rw [show -X-X = -(2*X) by ring, show X+X = 2*X by ring]
  norm_num [map_ofNat]
  ring

/-- Quantitative continuity in the actual positive atomic form, independent of translation size. -/
theorem norm_atomicForm_farSource_sub_le {b : ℕ → ℝ} {C : ℝ} (h : PolarMassBound b C)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (X : ℝ) :
    ‖atomicForm b C (EF.weilTest (farSource X f) (farSource X f)) -
      atomicForm b C (EF.weilTest f f)‖ ≤
      (2*farPolarCoeff X + farPolarCoeff X^2) * (atomicForm b C (EF.weilTest f f)).re := by
  let K := atomicKernel b C f
  have hp := positiveDefinite_atomicKernel h hf hs
  have hK (y : ℝ) : ‖K y‖ ≤ (K 0).re := hp.norm_le y
  have h0 : K 0 = atomicForm b C (EF.weilTest f f) := by
    change atomicForm b C (fun x => EF.weilTest f f (x-0)) = _
    simp only [sub_zero]
  have hr := farPolarCoeff_nonneg X
  have hn : ‖(farPolarCoeff X : ℂ)‖ = farPolarCoeff X := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have h1 : ‖(farPolarCoeff X : ℂ)*(K X+K (-X))‖ ≤
      2*farPolarCoeff X*(K 0).re := by
    rw [norm_mul, hn]
    calc farPolarCoeff X * ‖K X+K (-X)‖
        ≤ farPolarCoeff X * (‖K X‖+‖K (-X)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hr
      _ ≤ 2*farPolarCoeff X*(K 0).re := by nlinarith [hK X, hK (-X)]
  have h2 : ‖(farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X)))‖ ≤
      farPolarCoeff X^2*(K 0).re := by
    have hb : ‖2*K 0+K (2*X)+K (-(2*X))‖ ≤ 4*(K 0).re := by
      calc ‖2*K 0+K (2*X)+K (-(2*X))‖
          ≤ ‖2*K 0‖+‖K (2*X)‖+‖K (-(2*X))‖  := by
            linarith [norm_add_le (2*K 0) (K (2*X)),
              norm_add_le (2*K 0+K (2*X)) (K (-(2*X)))]
        _ ≤ 4*(K 0).re := by rw [norm_mul, norm_ofNat]; nlinarith [hK 0, hK (2*X), hK (-(2*X))]
    rw [norm_mul, norm_div, norm_pow, hn, norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (farPolarCoeff X))]
  rw [atomicForm_farSource b C hf.continuous hs X]
  change ‖K 0 - (farPolarCoeff X : ℂ)*(K X+K (-X)) +
    (farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X))) - _‖ ≤ _
  rw [← h0]
  have he (a u v : ℂ) : a-u+v-a = -u+v := by ring
  rw [he]
  calc ‖-((farPolarCoeff X : ℂ)*(K X+K (-X))) +
      (farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X)))‖
      ≤ ‖-((farPolarCoeff X : ℂ)*(K X+K (-X)))‖ +
        ‖(farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X)))‖ := norm_add_le _ _
    _ ≤ (2*farPolarCoeff X+farPolarCoeff X^2)*(K 0).re := by rw [norm_neg]; nlinarith

/-- Far polarization preserves the value of every polar-mass-bounded atomic form in the limit. -/
theorem tendsto_atomicForm_farSource {b : ℕ → ℝ} {C : ℝ} (h : PolarMassBound b C)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun X : ℝ => atomicForm b C (EF.weilTest (farSource X f) (farSource X f)))
      atTop (𝓝 (atomicForm b C (EF.weilTest f f))) := by
  have he : Tendsto (fun X : ℝ => (2*farPolarCoeff X+farPolarCoeff X^2)*
      (atomicForm b C (EF.weilTest f f)).re) atTop (𝓝 0) := by
    simpa using ((tendsto_farPolarCoeff.const_mul 2).add (tendsto_farPolarCoeff.pow 2)).mul_const
      (atomicForm b C (EF.weilTest f f)).re
  have hd := squeeze_zero_norm (norm_atomicForm_farSource_sub_le h hf hs) he
  simpa using hd.add_const (atomicForm b C (EF.weilTest f f))


private theorem exists_aperture {f : ℝ → ℂ} (hs : HasCompactSupport f) :
    ∃ a : ℝ, 0 ≤ a ∧ tsupport f ⊆ Icc (-a) a := by
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hs
  refine ⟨|a|, abs_nonneg _, closure_minimal (fun x hx => ?_) isClosed_Icc⟩
  exact abs_le.mp ((ha x hx).trans (le_abs_self a))

private theorem contDiff_farSource {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (X : ℝ) :
    ContDiff ℝ 2 (farSource X f) :=
  hf.sub (contDiff_const.smul ((hf.comp (contDiff_id.sub contDiff_const)).add
    (hf.comp (contDiff_id.sub contDiff_const))))

private theorem compact_farSource {f : ℝ → ℂ} (hs : HasCompactSupport f) (X : ℝ) :
    HasCompactSupport (farSource X f) :=
  hs.sub (((hs.comp_homeomorph (Homeomorph.subRight X)).add
    (hs.comp_homeomorph (Homeomorph.subRight (-X)))).smul_left)

/-- The far correction cancels both pole evaluations for every compact source. -/
theorem paperFT_farSource {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (X : ℝ) (z : ℂ) :
    paperFT (farSource X f) z =
      paperFT f z * (1-(farPolarCoeff X : ℂ)*Complex.cos (X*z)) := by
  have hi (s : ℝ) : Integrable (fun y : ℝ => f (y-s)*cexp (I*z*y)) := by
    exact ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hs.comp_homeomorph (Homeomorph.subRight s)).mul_right
  have i0 : Integrable (fun y : ℝ => f y*cexp (I*z*y)) := by simpa using hi 0
  have e : (fun y : ℝ => farSource X f y*cexp (I*z*y)) =
      fun y => f y*cexp (I*z*y) - (farPolarCoeff X : ℂ)/2 *
        (f (y-X)*cexp (I*z*y)+f (y- -X)*cexp (I*z*y)) := by
    funext y; simp only [farSource, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, WeilSpectral.transl]; ring
  have i12 : Integrable (fun y : ℝ => (farPolarCoeff X : ℂ)/2 *
      (f (y-X)*cexp (I*z*y)+f (y- -X)*cexp (I*z*y))) :=
    ((hi X).add (hi (-X))).const_mul _
  rw [paperFT, e, integral_sub i0 i12,
    integral_const_mul, integral_add (hi X) (hi (-X))]
  change paperFT f z - (farPolarCoeff X : ℂ)/2 *
    (paperFT (WeilSpectral.transl X f) z + paperFT (WeilSpectral.transl (-X) f) z) = _
  rw [paperFT_transl, paperFT_transl, Complex.cos]
  have e1 : I*z*(X : ℂ) = (X : ℂ)*z*I := by ring
  have e2 : I*z*((-X : ℝ) : ℂ) = -((X : ℂ)*z)*I := by push_cast; ring
  rw [e1, e2]; ring

/-- Both polar zeros are literal zeros of the actual compact C2 source. -/
theorem isPolarTest_farSource {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) (X : ℝ) : ∃ a, IsPolarTest a (farSource X f) := by
  obtain ⟨a, ha, hsup⟩ := exists_aperture (compact_farSource hs X)
  refine ⟨a, ha, contDiff_farSource hf X, hsup, ?_, ?_⟩
  · rw [paperFT_farSource hf.continuous hs, cos_mul_half_I, farPolarCoeff_mul_cosh,
      sub_self, mul_zero]
  · rw [paperFT_farSource hf.continuous hs, mul_neg, Complex.cos_neg, cos_mul_half_I,
      farPolarCoeff_mul_cosh, sub_self, mul_zero]

private theorem normSq_farSource {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (X τ : ℝ) : ‖paperFT (farSource X f) τ‖^2 =
      ‖paperFT f τ‖^2*(1-farPolarCoeff X*Real.cos (X*τ))^2 := by
  rw [paperFT_farSource hf hs, norm_mul, mul_pow]
  congr 1
  have he : 1-(farPolarCoeff X : ℂ)*Complex.cos ((X : ℂ)*τ) =
      ((1-farPolarCoeff X*Real.cos (X*τ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos]; push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem density_error_le {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (X τ : ℝ) : |‖paperFT (farSource X f) τ‖^2-‖paperFT f τ‖^2| ≤
      (2*farPolarCoeff X+farPolarCoeff X^2)*‖paperFT f τ‖^2 := by
  rw [normSq_farSource hf hs]
  have hr := farPolarCoeff_nonneg X
  let z := farPolarCoeff X*Real.cos (X*τ)
  have hz : |z| ≤ farPolarCoeff X := by
    dsimp [z]; rw [abs_mul, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hr).trans_eq (mul_one _)
  have hz' := abs_le.mp hz
  have hzz : z^2 ≤ farPolarCoeff X^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz'.2) (show 0 ≤ farPolarCoeff X+z by linarith)]
  have he : |(1-z)^2-1| ≤ 2*farPolarCoeff X+farPolarCoeff X^2 := by
    apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg z]
  change |‖paperFT f τ‖^2*(1-z)^2-‖paperFT f τ‖^2| ≤ _
  rw [show ‖paperFT f τ‖^2*(1-z)^2-‖paperFT f τ‖^2 =
    ‖paperFT f τ‖^2*((1-z)^2-1) by ring, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖paperFT f τ‖)

/-- Quantitative spectral L1 convergence of the generic far-polar source. -/
theorem integral_density_error_farSource_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) (X : ℝ) :
    (∫ τ : ℝ, |‖paperFT (farSource X f) τ‖^2-‖paperFT f τ‖^2|) ≤
      (2*farPolarCoeff X+farPolarCoeff X^2)*(∫ τ : ℝ, ‖paperFT f τ‖^2) := by
  obtain ⟨a, _, hsup⟩ := exists_aperture hs
  obtain ⟨d, _, hdsup⟩ := exists_aperture (compact_farSource hs X)
  have hi := integrable_normSq_paperFT hf hsup
  have hj := integrable_normSq_paperFT (contDiff_farSource hf X) hdsup
  rw [← integral_const_mul]
  exact integral_mono (hj.sub hi).abs (hi.const_mul _)
    (density_error_le hf.continuous hs X)

/-- Actual compact C2 polar sources approximate every full source in spectral L1. -/
theorem tendsto_integral_density_error_farSource {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) :
    Tendsto (fun X : ℝ => ∫ τ : ℝ, |‖paperFT (farSource X f) τ‖^2-‖paperFT f τ‖^2|)
      atTop (𝓝 0) := by
  have he : Tendsto (fun X : ℝ => (2*farPolarCoeff X+farPolarCoeff X^2)*
      (∫ τ : ℝ, ‖paperFT f τ‖^2)) atTop (𝓝 0) := by
    simpa using ((tendsto_farPolarCoeff.const_mul 2).add (tendsto_farPolarCoeff.pow 2)).mul_const
      (∫ τ : ℝ, ‖paperFT f τ‖^2)
  exact squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (integral_density_error_farSource_le hf hs) he


open WeilOneSided

theorem density_integrable (f : WeilTestFn) :
    Integrable (fun τ : ℝ => ‖paperFT f.1 τ‖^2) := by
  obtain ⟨a, _, ha⟩ := exists_aperture f.2.2
  exact integrable_normSq_paperFT f.2.1 ha

/-- The actual spectral density as a real L1 element. -/
def densityL1 (f : WeilTestFn) : Lp ℝ 1 (volume : Measure ℝ) :=
  (density_integrable f).toL1 (fun τ : ℝ => ‖paperFT f.1 τ‖^2)

/-- The finite raw arithmetic pairing, expressed without choosing an aperture. -/
def atomValue (b : ℕ → ℝ) (f : ℝ → ℂ) : ℝ :=
  -(atomicForm b 0 (EF.weilTest f f)).re

theorem atomValue_eq_sum (b : ℕ → ℝ) {f : ℝ → ℂ} {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) :
    atomValue b f = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, b n*atomCoeff f n := by
  simp [atomValue, atomicForm_corr_re b 0 hs]

private theorem norm_densityL1 (f : WeilTestFn) :
    ‖densityL1 f‖ = 2*Real.pi*(∫ x : ℝ, ‖f.1 x‖^2) := by
  rw [densityL1, L1.norm_of_fun_eq_integral_norm]
  simp only [Real.norm_eq_abs, abs_sq]
  obtain ⟨a, _, ha⟩ := exists_aperture f.2.2
  have he := integral_normSq_paperFT_mul_cos_eq f.2.1 ha 0
  simp only [mul_zero, Real.cos_zero, mul_one, neg_zero, corr_zero,
    Complex.add_re, Complex.ofReal_re] at he
  rw [he]; ring

/-- The far-polar source packaged with its actual regularity. -/
def farTest (X : ℝ) (f : WeilTestFn) : WeilTestFn :=
  ⟨farSource X f.1, contDiff_farSource f.2.1 X, compact_farSource f.2.2 X⟩

private theorem norm_densityL1_sub (f g : WeilTestFn) :
    ‖densityL1 f-densityL1 g‖ =
      ∫ τ : ℝ, |‖paperFT f.1 τ‖^2-‖paperFT g.1 τ‖^2| := by
  rw [densityL1, densityL1, ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

private theorem tendsto_densityL1_farTest (f : WeilTestFn) :
    Tendsto (fun X : ℝ => densityL1 (farTest X f)) atTop (𝓝 (densityL1 f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_densityL1_sub, farTest] using tendsto_integral_density_error_farSource f.2.1 f.2.2

private theorem atomicForm_sub_mass (b : ℕ → ℝ) (C : ℝ) (k : ℝ → ℂ) :
    atomicForm b 0 k = atomicForm b C k-(C : ℂ)*atomicForm (fun _ => 0) 1 k := by
  simp only [atomicForm, Complex.ofReal_zero, zero_mul, ite_self, tsum_zero,
    Complex.ofReal_one, one_mul, sub_zero]
  ring

private theorem tendsto_atomValue_farSource {b : ℕ → ℝ} {C : ℝ} (h : PolarMassBound b C)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun X : ℝ => atomValue b (farSource X f)) atTop (𝓝 (atomValue b f)) := by
  have hz : PolarMassBound (fun _ => 0) 1 := by
    intro a g hg
    simp only [zero_mul, Finset.sum_const_zero, one_mul]
    exact integral_nonneg fun _ => sq_nonneg _
  have he := (tendsto_atomicForm_farSource h hf hs).sub
    ((tendsto_atomicForm_farSource hz hf hs).const_mul (C : ℂ))
  simp only [← atomicForm_sub_mass] at he
  exact (Complex.continuous_re.tendsto _ |>.comp he).neg

/-- Polar inequalities against bounded spectral functionals. -/
def PolarSpectralBound (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) → atomValue b f.1 ≤ ell (densityL1 f)

/-- Full-source inequalities against the same bounded spectral functional. -/
def FullSpectralBound (b : ℕ → ℝ) (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : WeilTestFn, atomValue b f.1 ≤ ell (densityL1 f)

/-- A bounded spectral separator valid on all polar sources is valid on every full source.
The arithmetic coefficients are arbitrary; their required continuity is proved from the bound. -/
theorem polarSpectralBound_iff_fullSpectralBound (b : ℕ → ℝ)
    (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) :
    PolarSpectralBound b ell ↔ FullSpectralBound b ell := by
  constructor
  · intro h
    have hb : PolarMassBound b (‖ell‖*(2*Real.pi)) := by
      intro a f hp
      have hs : HasCompactSupport f :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hp.2.2.1
      let F : WeilTestFn := ⟨f, hp.2.1, hs⟩
      have ha := h F ⟨a, hp⟩
      rw [atomValue_eq_sum b hp.2.2.1] at ha
      have hn := ell.le_opNorm (densityL1 F)
      rw [norm_densityL1] at hn
      have hlo := le_abs_self (ell (densityL1 F))
      rw [← Real.norm_eq_abs] at hlo
      dsimp only [F] at hn
      nlinarith
    intro f
    have hl := tendsto_atomValue_farSource hb f.2.1 f.2.2
    have hr := ell.continuous.tendsto (densityL1 f) |>.comp (tendsto_densityL1_farTest f)
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun X =>
      h (farTest X f) (isPolarTest_farSource f.2.1 f.2.2 X))
  · intro h f _; exact h f

end RHTower.ExposingRayTransfer
