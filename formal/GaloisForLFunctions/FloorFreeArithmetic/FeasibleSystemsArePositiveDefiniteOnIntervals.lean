import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.FiniteAperturePositivityCannotDecide
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Feasible systems are positive definite on intervals

The spectral kernel of a test `f` for a weight system `λ` is `K_f(y) = W_λ(τ_y(f ⋆ f̃))`. For
a combination `g = Σ c_j τ_{t_j} f` of translates one has the identity
`W_λ(g ⋆ g̃) = Σ_{i,j} c̄_i K_f(t_j − t_i) c_j`, for every weight system.

A system feasible on all tests has positive definite kernels on the line. A system feasible at
an aperture `A` sees only combinations that stay inside `[−A, A]`: for a test supported in
`[−A', A']` the nodes `t_j` may range over `[−(A − A'), A − A']`. So feasibility at an aperture
is positive definiteness of the kernels on intervals, the hypothesis of Krein's extension
theorem: each kernel is then the Fourier transform, on its interval of differences, of a
positive measure, not unique in general. The extension theorem itself is not used here.

* `PositiveDefiniteOnNodes K r`: positive definiteness of `K` on node sets in `[−r, r]`.
* `sum_spectralKernel_eq_weilFullFunctional`: the identity above.
* `aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes`: the description of the feasible
  set of an aperture.
* `eq_zero_of_positiveDefiniteOnNodes_of_zero`, `spectralKernel_eq_zero_of_null`: a kernel
  positive definite on an interval that vanishes at `0` vanishes on the whole interval of
  differences. So a feasible
  system is strictly positive on a test, unless the Weil functional vanishes on every translate
  of its autocorrelation that the aperture admits: a null vector annihilates the system on an
  interval.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open ArithmeticOfSquareRootPrecision
open _root_.RHTower _root_.RHTower.WeilSpectral

/-- Positive definiteness of a kernel on the node sets contained in `[−r, r]`: the Gram forms
`Σ c̄_i K(t_j − t_i) c_j` with `|t_j| ≤ r` are nonnegative reals. -/
def PositiveDefiniteOnNodes (K : ℝ → ℂ) (r : ℝ) : Prop :=
  ∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ), (∀ j, |t j| ≤ r) →
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∑ i, ∑ j, star (c i) * K (t j - t i) * c j = (ρ : ℂ)

/-- **The Gram form of translates is the Weil functional of the combination**, for every
weight system. -/
theorem sum_spectralKernel_eq_weilFullFunctional (lam : ℕ → ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) :
    ∑ i, ∑ j, star (c i) * spectralKernel lam f (t j - t i) * c j =
      weilFullFunctional lam
        (EF.weilTest (∑ j, c j • transl (t j) f) (∑ j, c j • transl (t j) f)) := by
  have hadm := admissible_weilTest hf hfc
  rw [weilTest_sum_transl hf.continuous hfc,
    weilFullFunctional_sum lam _ fun i _ => Admissible.sum _ fun j _ => (hadm.transl _).smul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weilFullFunctional_sum lam _ fun j _ => (hadm.transl _).smul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilFullFunctional_smul, spectralKernel]
  ring

/-- A combination of translates by at most `A − A'` of a test supported in `[−A', A']` is
supported in `[−A, A]`. -/
theorem tsupport_sum_transl_subset {f : ℝ → ℂ} {A A' : ℝ} (hfs : tsupport f ⊆ Icc (-A') A')
    {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) (ht : ∀ j, |t j| ≤ A - A') :
    tsupport (∑ j, c j • transl (t j) f) ⊆ Icc (-A) A := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hout
  apply hx
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hzero : f (x - t j) = 0 := by
    by_contra hne
    have hmem := hfs (subset_tsupport f hne)
    obtain ⟨h1, h2⟩ := abs_le.mp (ht j)
    exact hout ⟨by linarith only [hmem.1, h1], by linarith only [hmem.2, h2]⟩
  simp only [Pi.smul_apply, transl, hzero, smul_zero]

/-- **Feasibility at an aperture is positive definiteness on intervals.** A weight system is
feasible at the aperture `A` if and only if, for every `A' ≤ A` and every test supported in
`[−A', A']`, its spectral kernel is positive definite on the nodes of `[−(A − A'), A − A']`. -/
theorem aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes (A : ℝ) (lam : ℕ → ℝ) :
    AperturePositive A lam ↔
      ∀ A' : ℝ, A' ≤ A → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A') A' →
        PositiveDefiniteOnNodes (spectralKernel lam f) (A - A') := by
  constructor
  · intro hpos A' _ f hf hfs N t c ht
    have hfc : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs)
    have hg : ContDiff ℝ 2 (∑ j, c j • transl (t j) f) := by
      have hfun : (∑ j, c j • transl (t j) f) = fun x => ∑ j, c j * f (x - t j) := by
        funext x
        simp [Finset.sum_apply, transl]
      rw [hfun]
      exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))
    refine ⟨(weilFullFunctional lam
      (EF.weilTest (∑ j, c j • transl (t j) f) (∑ j, c j • transl (t j) f))).re,
      hpos _ hg (tsupport_sum_transl_subset hfs t c ht), ?_⟩
    rw [sum_spectralKernel_eq_weilFullFunctional lam hf hfc t c]
    exact Complex.ext rfl (by simpa using im_weilFullFunctional_weilTest_self lam _)
  · intro h f hf hfs
    obtain ⟨ρ, hρ, hsum⟩ := h A le_rfl f hf hfs 1 (fun _ => 0) (fun _ => 1) (fun _ => by simp)
    simp at hsum
    have h0 : spectralKernel lam f 0 = weilFullFunctional lam (EF.weilTest f f) := by
      rw [spectralKernel]
      congr 1
      funext x
      simp [transl]
    rw [← h0, hsum, Complex.ofReal_re]
    exact hρ

/-! ### Null vectors -/

/-- **A positive definite kernel on an interval that vanishes at `0` vanishes on the interval
of differences.** The Gram form on the two nodes `−y/2, y/2` is `K(y) c + K(−y) c̄` for the
vector `(1, c)`; it is nonnegative for `c = ±1, ±i`. -/
theorem eq_zero_of_positiveDefiniteOnNodes_of_zero {K : ℝ → ℂ} {r : ℝ}
    (hK : PositiveDefiniteOnNodes K r) (h0 : K 0 = 0) {y : ℝ} (hy : |y| ≤ 2 * r) :
    K y = 0 := by
  have hhalf : |y / 2| ≤ r := by
    rw [abs_div, abs_two]
    linarith only [hy]
  have hnodes : ∀ j : Fin 2, |(![-(y / 2), y / 2] : Fin 2 → ℝ) j| ≤ r := by
    intro j
    fin_cases j
    · simpa using hhalf
    · simpa using hhalf
  have e1 : y / 2 - -(y / 2) = y := by ring
  have e2 : -(y / 2) - y / 2 = -y := by ring
  -- the Gram form of `(1, c)` on the nodes `−y/2, y/2`
  have hform : ∀ c : ℂ, ∃ ρ : ℝ, 0 ≤ ρ ∧ K y * c + star c * K (-y) = (ρ : ℂ) := by
    intro c
    obtain ⟨ρ, hρ, hsum⟩ := hK 2 ![-(y / 2), y / 2] ![1, c] hnodes
    refine ⟨ρ, hρ, ?_⟩
    simpa [Fin.sum_univ_two, h0, e1, e2] using hsum
  obtain ⟨ρ₁, h1, e1⟩ := hform 1
  obtain ⟨ρ₂, h2, e2⟩ := hform (-1)
  obtain ⟨ρ₃, h3, e3⟩ := hform I
  obtain ⟨ρ₄, h4, e4⟩ := hform (-I)
  -- opposite vectors give opposite values, so all four values vanish
  have hsum12 : ((ρ₁ + ρ₂ : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_add, ← e1, ← e2]
    simp only [star_one, star_neg, mul_one, one_mul]
    ring
  have hsum34 : ((ρ₃ + ρ₄ : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_add, ← e3, ← e4]
    simp only [star_neg]
    ring
  have hρ1 : ρ₁ = 0 := by
    have := Complex.ofReal_eq_zero.mp hsum12
    linarith only [this, h1, h2]
  have hρ3 : ρ₃ = 0 := by
    have := Complex.ofReal_eq_zero.mp hsum34
    linarith only [this, h3, h4]
  rw [hρ1, Complex.ofReal_zero] at e1
  rw [hρ3, Complex.ofReal_zero] at e3
  -- `K(y) + K(−y) = 0` and `i K(y) − i K(−y) = 0`
  have ea : K y + K (-y) = 0 := by simpa using e1
  have eb : K y * I - I * K (-y) = 0 := by simpa [sub_eq_add_neg] using e3
  have h2K : 2 * (K y * I) = 0 := by linear_combination I * ea + eb
  have hKI : K y * I = 0 := by
    rcases mul_eq_zero.mp h2K with h | h
    · norm_num at h
    · exact h
  exact (mul_eq_zero.mp hKI).resolve_right Complex.I_ne_zero

/-- **A null vector annihilates a feasible system on an interval.** If the Weil form of a
system feasible at the aperture `A` vanishes on a test supported in `[−A', A']`, then its
spectral kernel vanishes on `[−2(A − A'), 2(A − A')]`, the whole interval of differences. -/
theorem spectralKernel_eq_zero_of_null {A A' : ℝ} {lam : ℕ → ℝ} (hpos : AperturePositive A lam)
    (hA : A' ≤ A) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A') A')
    (hnull : (weilFullFunctional lam (EF.weilTest f f)).re = 0) {y : ℝ}
    (hy : |y| ≤ 2 * (A - A')) : spectralKernel lam f y = 0 := by
  have hK := (aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes A lam).mp hpos A' hA
    f hf hfs
  have h0 : spectralKernel lam f 0 = 0 := by
    have e : spectralKernel lam f 0 = weilFullFunctional lam (EF.weilTest f f) := by
      rw [spectralKernel]
      congr 1
      funext x
      simp [transl]
    rw [e]
    exact Complex.ext hnull (by simpa using im_weilFullFunctional_weilTest_self lam f)
  exact eq_zero_of_positiveDefiniteOnNodes_of_zero hK h0 hy

end GaloisForLFunctions.FloorFreeArithmetic
