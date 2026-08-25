import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedDerivativeTruncation

/-!
# Finite classical truncation of the differentiated displaced zeta AFE

The exact differentiated source is truncated on both Dirichlet edges.  The
finite reflected weighted head is then replaced by its classical main head,
with the conductor-localization correction kept explicitly.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaDisplacedFiniteWeightedHeightDerivative
    (d x tau : ℝ) (L : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n) +
    (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n) -
    smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau

def smoothAFEZetaDisplacedFiniteClassicalHeightDerivative
    (d x tau : ℝ) (L : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n) +
    (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n) -
    smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau

/-- Both exact differentiated Dirichlet edges admit a simultaneous finite
truncation. -/
theorem exists_norm_smoothAFEZetaDisplacedHeightDerivativeSourceField_sub_finiteWeighted_le
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ tau : ℝ, ∀ L : ℕ, 1 ≤ L →
      ‖smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteWeightedHeightDerivative d x tau L‖ ≤
        K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  obtain ⟨C, hC, hdirect⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectHeightDerivativeSourceField_sub_sum_le
      hdhalf hx
  obtain ⟨R, hR, hreflected⟩ :=
    exists_norm_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField_sub_sum_le
      hd hdquarter heta hetaquarter hx
  let K : ℝ := C + R
  have hK : 0 ≤ K := add_nonneg hC hR
  refine ⟨K, hK, fun tau L hL => ?_⟩
  let a : ℝ := (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ)
  let b : ℝ := (1 + |tau|) ^ 3 *
    ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hdecomp :
      smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteWeightedHeightDerivative d x tau L =
        (smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n) +
        (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
            d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n) := by
    unfold smoothAFEZetaDisplacedHeightDerivativeSourceField
      smoothAFEZetaDisplacedFiniteWeightedHeightDerivative
    ring
  rw [hdecomp]
  calc
    ‖(smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n) +
        (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
            d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n)‖
      ≤ ‖smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n‖ +
        ‖smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
            d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n‖ := norm_add_le _ _
    _ ≤ C * a + R * b := by
      dsimp only [a, b]
      gcongr
      · simpa only [mul_div_assoc] using hdirect tau L hL
      · simpa only [mul_assoc] using hreflected tau L hL
    _ ≤ K * (a + b) := by
      dsimp only [K]
      nlinarith [mul_nonneg hC hb, mul_nonneg hR ha]
    _ = K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) := by
      rfl

/-- Quantitative differentiated classical two-head AFE. -/
theorem exists_norm_smoothAFEZetaDisplacedHeightDerivativeSourceField_sub_finiteClassical_le
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ {tau : ℝ}, 4 ≤ tau → ∀ L : ℕ, 1 ≤ L →
      ‖smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L‖ ≤
        K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
        E * x ^ (d + eta) / tau ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log L + 1 / tau) := by
  obtain ⟨K, hK, htail⟩ :=
    exists_norm_smoothAFEZetaDisplacedHeightDerivativeSourceField_sub_finiteWeighted_le
      hd hdquarter heta hetaquarter hx
  obtain ⟨E, hE, hcorrection⟩ :=
    exists_norm_sum_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_sub_main_le
      hd.le hdquarter heta hetaquarter
  refine ⟨K, E, hK, hE, fun {tau} htau L hL => ?_⟩
  have hdecomp :
      smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L =
        (smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteWeightedHeightDerivative d x tau L) +
        ∑ n ∈ Finset.range L,
          (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n -
            smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
              d tau n) := by
    unfold smoothAFEZetaDisplacedFiniteWeightedHeightDerivative
      smoothAFEZetaDisplacedFiniteClassicalHeightDerivative
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  calc
    ‖(smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteWeightedHeightDerivative d x tau L) +
        ∑ n ∈ Finset.range L,
          (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n -
            smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
              d tau n)‖
      ≤ ‖smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau -
          smoothAFEZetaDisplacedFiniteWeightedHeightDerivative d x tau L‖ +
        ‖∑ n ∈ Finset.range L,
          (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n -
            smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
              d tau n)‖ := norm_add_le _ _
    _ ≤ K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
        E * x ^ (d + eta) / tau ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log L + 1 / tau) := by
      gcongr
      · exact htail tau L hL
      · exact hcorrection d hd le_rfl htau hx L hL

/-- Analytic derivative form of the differentiated classical two-head AFE. -/
theorem exists_norm_deriv_riemannZeta_mul_I_displaced_sub_finiteClassical_le
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧
      ∀ {tau : ℝ}, 4 ≤ tau → ∀ L : ℕ, 1 ≤ L →
      ‖deriv riemannZeta (displacedLinePt d tau) * I -
          smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L‖ ≤
        K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
        E * x ^ (d + eta) / tau ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log L + 1 / tau) := by
  obtain ⟨K, E, hK, hE, hsource⟩ :=
    exists_norm_smoothAFEZetaDisplacedHeightDerivativeSourceField_sub_finiteClassical_le
      hd hdquarter heta hetaquarter hx
  refine ⟨K, E, hK, hE, fun {tau} htau L hL => ?_⟩
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hsneq : displacedLinePt d tau ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [displacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hzeta := (differentiableAt_riemannZeta hsneq).hasDerivAt.comp
    tau (hasDerivAt_displacedLinePt d tau)
  have hafe := hasDerivAt_riemannZeta_displaced_eq_smoothAFE
    hd hdquarter heta hetaquarter hx tau
  have hderiv : deriv riemannZeta (displacedLinePt d tau) * I =
      smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau :=
    hzeta.unique hafe
  rw [hderiv]
  exact hsource htau L hL

end RHTower
