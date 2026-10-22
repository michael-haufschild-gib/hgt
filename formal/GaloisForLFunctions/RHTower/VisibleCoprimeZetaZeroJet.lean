import GaloisForLFunctions.RHTower.VisibleCoprimeMellinSymbol
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.RHTower.ZetaRealSignature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Visible-coprime zeta zero jets

The continued primitive-lattice Mellin symbol is

`ζ(s) ζ(t) invZeta(s+t)`.

At an actual Xi divisor `rho`, differentiating once in each variable at the full analytic
multiplicity leaves exactly the squared norm of the leading zeta jet times the regular reciprocal
at `2 Re rho`.  The regular reciprocal is negative to the left of the critical line, zero on it,
and positive to its right.  This gives the exact unconditional orientation and zero-locus laws
`(V7)`--`(V9)` from the visible-coprime card.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- If every lower jet of the first factor vanishes, only its top Leibniz term survives. -/
theorem complex_iteratedDeriv_mul_of_vanishing_below
    (m : ℕ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ m f z) (hg : ContDiffAt ℂ m g z)
    (hvanish : ∀ j < m, iteratedDeriv j f z = 0) :
    iteratedDeriv m (fun w => f w * g w) z = iteratedDeriv m f z * g z := by
  have hprod : (fun w => f w * g w) = f * g := rfl
  rw [hprod, iteratedDeriv_mul hf hg]
  rw [Finset.sum_eq_single m]
  · simp [iteratedDeriv_zero]
  · intro i hi him
    have hi' : i < m := by
      rw [Finset.mem_range] at hi
      omega
    rw [hvanish i hi']
    simp
  · simp

/-- Two-variable top-jet extraction for a product whose third factor depends on the sum. -/
theorem complex_mixedAddProductJet_of_vanishing_below
    (m : ℕ) {f g h : ℂ → ℂ} {a b : ℂ}
    (hf : ContDiffAt ℂ m f a) (hg : ContDiffAt ℂ m g b)
    (hh : ContDiffAt ℂ m h (a + b))
    (hfvanish : ∀ j < m, iteratedDeriv j f a = 0)
    (hgvanish : ∀ j < m, iteratedDeriv j g b = 0) :
    iteratedDeriv m
        (fun s => iteratedDeriv m (fun t => f s * g t * h (s + t)) b) a =
      iteratedDeriv m f a * iteratedDeriv m g b * h (a + b) := by
  have hnear : ∀ᶠ s in 𝓝 a, ContDiffAt ℂ m h (s + b) := by
    have htend : Tendsto (fun s : ℂ => s + b) (𝓝 a) (𝓝 (a + b)) :=
      continuousAt_id.add continuousAt_const
    exact htend (hh.eventually (by simp))
  have hinner :
      (fun s => iteratedDeriv m (fun t => f s * g t * h (s + t)) b) =ᶠ[𝓝 a]
        (fun s => iteratedDeriv m g b * (f s * h (s + b))) := by
    filter_upwards [hnear] with s hhs
    have hadd : ContDiffAt ℂ m (fun t : ℂ => s + t) b :=
      contDiffAt_const.add contDiffAt_id
    have hhcomp : ContDiffAt ℂ m (fun t : ℂ => h (s + t)) b := by
      simpa [Function.comp_def] using hhs.comp b hadd
    have hrest : ContDiffAt ℂ m (fun t : ℂ => f s * h (s + t)) b :=
      contDiffAt_const.mul hhcomp
    rw [show (fun t : ℂ => f s * g t * h (s + t)) =
        fun t : ℂ => g t * (f s * h (s + t)) by funext t; ring]
    exact complex_iteratedDeriv_mul_of_vanishing_below m hg hrest hgvanish
  rw [hinner.iteratedDeriv_eq m]
  have hadd : ContDiffAt ℂ m (fun s : ℂ => s + b) a :=
    contDiffAt_id.add contDiffAt_const
  have hhcomp : ContDiffAt ℂ m (fun s : ℂ => h (s + b)) a := by
    simpa [Function.comp_def] using hh.comp a hadd
  have hrest : ContDiffAt ℂ m
      (fun s : ℂ => iteratedDeriv m g b * h (s + b)) a :=
    contDiffAt_const.mul hhcomp
  rw [show (fun s : ℂ => iteratedDeriv m g b * (f s * h (s + b))) =
      fun s : ℂ => f s * (iteratedDeriv m g b * h (s + b)) by funext s; ring]
  rw [complex_iteratedDeriv_mul_of_vanishing_below m hf hrest hfvanish]
  ring

/-- The regular reciprocal is analytic wherever the entire zeta residue unit is nonzero. -/
theorem analyticAt_invZeta_of_residueUnit_ne_zero {s : ℂ}
    (hs : zetaResidueUnit s ≠ 0) :
    AnalyticAt ℂ Sieve.invZeta s := by
  exact (analyticAt_id.sub analyticAt_const).mul
    ((analyticAt_zetaResidueUnit s).inv hs)

/-- The entire zeta residue unit has no zero anywhere on the positive real axis. -/
theorem zetaResidueUnit_ne_zero_of_ofReal_pos {u : ℝ} (hu : 0 < u) :
    zetaResidueUnit (u : ℂ) ≠ 0 := by
  rcases lt_trichotomy u 1 with hu1 | hu1 | hu1
  · have hne : (u : ℂ) ≠ 1 := by exact_mod_cast ne_of_lt hu1
    exact (Sieve.zetaResidueUnit_ne_zero_iff hne).2
      (riemannZeta_ne_zero_of_ofReal_mem_Ioo hu hu1)
  · subst u
    simp
  · have hne : (u : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hu1
    exact (Sieve.zetaResidueUnit_ne_zero_iff hne).2
      (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))

/-- A point plus its Schwarz conjugate is the real point `2 Re z`. -/
theorem add_conj_eq_ofReal_two_re (z : ℂ) :
    z + (starRingEnd ℂ) z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
    ring
  · simp

/-- Every iterated zeta jet is Schwarz equivariant. -/
theorem iteratedDeriv_riemannZeta_conj (m : ℕ) (z : ℂ) :
    iteratedDeriv m riemannZeta ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (iteratedDeriv m riemannZeta z) := by
  have hfun : (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) = riemannZeta := by
    funext w
    simp [Function.comp_def, riemannZeta_conj]
  have h := congrFun (iteratedDeriv_conj_conj riemannZeta m) ((starRingEnd ℂ) z)
  rw [hfun] at h
  simpa [Function.comp_def] using h

/-- Holomorphically continued primitive-coprime zeta symbol. -/
def visibleCoprimeZetaKernel (s t : ℂ) : ℂ :=
  riemannZeta s * riemannZeta t * Sieve.invZeta (s + t)

/-- Hermitian mixed jet at one actual Xi divisor and its Schwarz conjugate. -/
def visibleCoprimeZetaMixedJet (rho : XiDivisorSupport) : ℂ :=
  let m := xiSupportMultiplicity rho
  iteratedDeriv m
    (fun s => iteratedDeriv m (fun t => visibleCoprimeZetaKernel s t)
      ((starRingEnd ℂ) (rho : ℂ))) (rho : ℂ)

/-- The two Leibniz expansions leave only the two top zeta jets. -/
theorem visibleCoprimeZetaMixedJet_eq_raw (rho : XiDivisorSupport) :
    visibleCoprimeZetaMixedJet rho =
      iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho) riemannZeta
          ((starRingEnd ℂ) (rho : ℂ)) *
        Sieve.invZeta ((rho : ℂ) + (starRingEnd ℂ) (rho : ℂ)) := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrho1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hconj1 : (starRingEnd ℂ) (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hsum :
      (rho : ℂ) + (starRingEnd ℂ) (rho : ℂ) =
        ((2 * (rho : ℂ).re : ℝ) : ℂ) :=
    add_conj_eq_ofReal_two_re (rho : ℂ)
  have hpos : 0 < 2 * (rho : ℂ).re := by linarith
  have hf : ContDiffAt ℂ (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hrho1).contDiffAt
  have hg : ContDiffAt ℂ (xiSupportMultiplicity rho) riemannZeta
      ((starRingEnd ℂ) (rho : ℂ)) :=
    (analyticOn_riemannZeta ((starRingEnd ℂ) (rho : ℂ)) hconj1).contDiffAt
  have hh : ContDiffAt ℂ (xiSupportMultiplicity rho) Sieve.invZeta
      ((rho : ℂ) + (starRingEnd ℂ) (rho : ℂ)) := by
    rw [hsum]
    exact (analyticAt_invZeta_of_residueUnit_ne_zero
      (zetaResidueUnit_ne_zero_of_ofReal_pos hpos)).contDiffAt
  have hfzero : ∀ j < xiSupportMultiplicity rho,
      iteratedDeriv j riemannZeta (rho : ℂ) = 0 := by
    intro j hj
    exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho hj
  have hgzero : ∀ j < xiSupportMultiplicity rho,
      iteratedDeriv j riemannZeta ((starRingEnd ℂ) (rho : ℂ)) = 0 := by
    intro j hj
    rw [← xiSupportConj_coe rho]
    exact iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity
      (xiSupportConj rho) (by simpa [xiSupportMultiplicity_conj] using hj)
  unfold visibleCoprimeZetaMixedJet visibleCoprimeZetaKernel
  exact complex_mixedAddProductJet_of_vanishing_below
    (xiSupportMultiplicity rho) hf hg hh hfzero hgzero

/-- Raw Hermitian form of the visible-coprime mixed jet. -/
theorem visibleCoprimeZetaMixedJet_eq_conj (rho : XiDivisorSupport) :
    visibleCoprimeZetaMixedJet rho =
      iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) *
        (starRingEnd ℂ)
          (iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ)) *
        Sieve.invZeta (((2 * (rho : ℂ).re : ℝ) : ℂ)) := by
  rw [visibleCoprimeZetaMixedJet_eq_raw,
    iteratedDeriv_riemannZeta_conj, add_conj_eq_ofReal_two_re]

/-- Exact visible-coprime zero-jet law `(V7)`, with the reciprocal regularized at the pole. -/
theorem visibleCoprimeZetaMixedJet_eq (rho : XiDivisorSupport) :
    visibleCoprimeZetaMixedJet rho =
      ((Complex.normSq
        (iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ)) : ℝ) : ℂ) *
        Sieve.invZeta (((2 * (rho : ℂ).re : ℝ) : ℂ)) := by
  rw [visibleCoprimeZetaMixedJet_eq_conj, Complex.mul_conj]

/-- The zeta conormal order and the canonical Xi support multiplicity coincide. -/
theorem xiSupportMultiplicity_eq_burnolCoPoissonXiConormalOrder
    (rho : XiDivisorSupport) :
    xiSupportMultiplicity rho = burnolCoPoissonXiConormalOrder rho := by
  rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    burnolCoPoissonXiConormalOrder_eq_xi_analyticOrder_toNat]

/-- The zeta jet at the exact Xi support multiplicity is nonzero. -/
theorem iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity
    (rho : XiDivisorSupport) :
    iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) ≠ 0 := by
  rw [xiSupportMultiplicity_eq_burnolCoPoissonXiConormalOrder]
  exact iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho

/-- The regular reciprocal on `2 sigma` is negative left of the critical line. -/
theorem re_invZeta_two_mul_neg {sigma : ℝ}
    (h0 : 0 < sigma) (hhalf : sigma < 1 / 2) :
    (Sieve.invZeta (((2 * sigma : ℝ) : ℂ))).re < 0 := by
  obtain ⟨z, hz, hzeta⟩ := riemannZeta_two_mul_neg h0 hhalf
  have hne : (((2 * sigma : ℝ) : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [Sieve.invZeta_eq_inv hne, hzeta, ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_lt_zero.mpr hz

/-- The regular reciprocal on `2 sigma` is positive right of the critical line. -/
theorem re_invZeta_two_mul_pos {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    0 < (Sieve.invZeta (((2 * sigma : ℝ) : ℂ))).re := by
  have hne : (((2 * sigma : ℝ) : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [Sieve.invZeta_eq_inv hne, riemannZeta_two_mul_eq_ofReal hhalf,
    ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr (eulerPositiveTotal_two_mul_pos hhalf)

/-- The Hermitian mixed jet is real. -/
theorem visibleCoprimeZetaMixedJet_im_eq_zero (rho : XiDivisorSupport) :
    (visibleCoprimeZetaMixedJet rho).im = 0 := by
  rw [visibleCoprimeZetaMixedJet_eq]
  rcases lt_trichotomy (rho : ℂ).re (1 / 2) with hlt | heq | hgt
  · obtain ⟨z, _, hzeta⟩ := riemannZeta_two_mul_neg
      (xi_divisor_support_re_mem_open_unit rho).1 hlt
    have hne : (((2 * (rho : ℂ).re : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    rw [Sieve.invZeta_eq_inv hne, hzeta, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul]
    simp
  · rw [heq]
    norm_num [Sieve.invZeta_one]
  · have hne : (((2 * (rho : ℂ).re : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    rw [Sieve.invZeta_eq_inv hne, riemannZeta_two_mul_eq_ofReal hgt,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    simp

/-- Left of the critical line the visible-coprime zero jet is strictly negative. -/
theorem visibleCoprimeZetaMixedJet_re_neg_of_re_lt_half
    (rho : XiDivisorSupport) (hhalf : (rho : ℂ).re < 1 / 2) :
    (visibleCoprimeZetaMixedJet rho).re < 0 := by
  rw [visibleCoprimeZetaMixedJet_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg
    ((Complex.normSq_pos).2
      (iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity rho))
    (re_invZeta_two_mul_neg
      (xi_divisor_support_re_mem_open_unit rho).1 hhalf)

/-- Right of the critical line the visible-coprime zero jet is strictly positive. -/
theorem visibleCoprimeZetaMixedJet_re_pos_of_half_lt_re
    (rho : XiDivisorSupport) (hhalf : 1 / 2 < (rho : ℂ).re) :
    0 < (visibleCoprimeZetaMixedJet rho).re := by
  rw [visibleCoprimeZetaMixedJet_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos
    ((Complex.normSq_pos).2
      (iteratedDeriv_riemannZeta_ne_zero_at_xiSupportMultiplicity rho))
    (re_invZeta_two_mul_pos hhalf)

/-- Exact critical-line vanishing certificate `(V9)`. -/
theorem visibleCoprimeZetaMixedJet_eq_zero_iff (rho : XiDivisorSupport) :
    visibleCoprimeZetaMixedJet rho = 0 ↔ (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy (rho : ℂ).re (1 / 2) with hlt | heq | hgt
    · have hneg := visibleCoprimeZetaMixedJet_re_neg_of_re_lt_half rho hlt
      rw [hzero] at hneg
      norm_num at hneg
    · exact heq
    · have hpos := visibleCoprimeZetaMixedJet_re_pos_of_half_lt_re rho hgt
      rw [hzero] at hpos
      norm_num at hpos
  · intro hhalf
    rw [visibleCoprimeZetaMixedJet_eq, hhalf]
    norm_num [Sieve.invZeta_one]

/-- Negative chamber equivalence in the pointwise orientation law `(V8)`. -/
theorem visibleCoprimeZetaMixedJet_re_neg_iff (rho : XiDivisorSupport) :
    (visibleCoprimeZetaMixedJet rho).re < 0 ↔ (rho : ℂ).re < 1 / 2 := by
  constructor
  · intro hneg
    rcases lt_trichotomy (rho : ℂ).re (1 / 2) with hlt | heq | hgt
    · exact hlt
    · have hzero := (visibleCoprimeZetaMixedJet_eq_zero_iff rho).2 heq
      rw [hzero] at hneg
      norm_num at hneg
    · have hpos := visibleCoprimeZetaMixedJet_re_pos_of_half_lt_re rho hgt
      linarith
  · exact visibleCoprimeZetaMixedJet_re_neg_of_re_lt_half rho

/-- Positive chamber equivalence in the pointwise orientation law `(V8)`. -/
theorem visibleCoprimeZetaMixedJet_re_pos_iff (rho : XiDivisorSupport) :
    0 < (visibleCoprimeZetaMixedJet rho).re ↔ 1 / 2 < (rho : ℂ).re := by
  constructor
  · intro hpos
    rcases lt_trichotomy (rho : ℂ).re (1 / 2) with hlt | heq | hgt
    · have hneg := visibleCoprimeZetaMixedJet_re_neg_of_re_lt_half rho hlt
      linarith
    · have hzero := (visibleCoprimeZetaMixedJet_eq_zero_iff rho).2 heq
      rw [hzero] at hpos
      norm_num at hpos
    · exact hgt
  · exact visibleCoprimeZetaMixedJet_re_pos_of_half_lt_re rho

end

end RHTower
