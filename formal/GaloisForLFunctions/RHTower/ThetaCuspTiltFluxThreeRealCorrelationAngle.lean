import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxThreeRealDeterminant
import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationAngle
import GaloisForLFunctions.RHTower.ThetaSourceGlobalStrictLogConvexity

/-!
# Lorentz correlation-angle classification of three-real theta flux

The complete Xi Euler-response kernel is normalized to a correlation in `(0,1)` on every pair
of distinct positive nodes. Its three-point determinant is nonnegative exactly when the three
associated correlation angles satisfy all triangle inequalities. Transport through the literal
theta-source congruence makes failure of this metric law exactly a negative three-mode real-ray
theta tilt flux.

A second normal form exposes physics behind the endpoint. The normalized correlation is a ratio
of multiplicative Lorentz coshes: response boost over aperture boost. Global strict log-convexity
of centered Xi and strict radial decrease place response boost strictly inside aperture future
cone, while both boosts compose exactly across ordered nodes. Thus remaining cubic sign is a
causal-angle globalization problem, not a pairwise positivity problem.

No zero-location hypothesis is used.

Claim labels: `[LEAN-PROVED] [BRIDGE/REDUCTION] [NOVELTY UNVERIFIED]`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Diagonally normalized full Xi Euler-response correlation. -/
def xiSquaredEulerFullCorrelation (x y : ℝ) : ℝ :=
  xiSquaredEulerFullKernel x y /
    (Real.sqrt (xiSquaredEulerFullKernel x x) *
      Real.sqrt (xiSquaredEulerFullKernel y y))

/-- Correlation angle of two positive Euler nodes. -/
def xiSquaredEulerFullCorrelationAngle (x y : ℝ) : ℝ :=
  Real.arccos (xiSquaredEulerFullCorrelation x y)

/-- All three metric triangle inequalities for one Euler-node triple. -/
def XiSquaredEulerFullCorrelationTriangleLaw (x y z : ℝ) : Prop :=
  xiSquaredEulerFullCorrelationAngle x z ≤ xiSquaredEulerFullCorrelationAngle x y + xiSquaredEulerFullCorrelationAngle y z ∧
  xiSquaredEulerFullCorrelationAngle x y ≤ xiSquaredEulerFullCorrelationAngle x z + xiSquaredEulerFullCorrelationAngle y z ∧
  xiSquaredEulerFullCorrelationAngle y z ≤ xiSquaredEulerFullCorrelationAngle x y + xiSquaredEulerFullCorrelationAngle x z

private theorem xiSquaredEulerFullKernel_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < xiSquaredEulerFullKernel x y := by
  unfold xiSquaredEulerFullKernel eulerRayResponseKernel xiSquaredEulerFullQ
  exact div_pos
    (add_pos
      (mul_pos hx (xiSquaredEulerFullResponse_pos (sq_nonneg x)))
      (mul_pos hy (xiSquaredEulerFullResponse_pos (sq_nonneg y))))
    (add_pos hx hy)

/-- Full Euler correlation is strictly positive on positive nodes. -/
theorem xiSquaredEulerFullCorrelation_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < xiSquaredEulerFullCorrelation x y := by
  unfold xiSquaredEulerFullCorrelation
  exact div_pos (xiSquaredEulerFullKernel_pos hx hy)
    (mul_pos
      (Real.sqrt_pos.2 (xiSquaredEulerFullKernel_diag_pos hx))
      (Real.sqrt_pos.2 (xiSquaredEulerFullKernel_diag_pos hy)))

/-- Distinct ordered nodes have correlation strictly below one. -/
theorem xiSquaredEulerFullCorrelation_lt_one {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    xiSquaredEulerFullCorrelation x y < 1 := by
  have hy : 0 < y := hx.trans hxy
  let A := xiSquaredEulerFullKernel x x
  let B := xiSquaredEulerFullKernel y y
  let P := xiSquaredEulerFullKernel x y
  let S := Real.sqrt A * Real.sqrt B
  have hA : 0 < A := xiSquaredEulerFullKernel_diag_pos hx
  have hB : 0 < B := xiSquaredEulerFullKernel_diag_pos hy
  have hP : 0 < P := xiSquaredEulerFullKernel_pos hx hy
  have hminor : 0 < A * B - P ^ 2 :=
    xiSquaredEulerFullKernel_twoPoint_det_pos hx hxy
  have hS : 0 < S := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hSsq : S ^ 2 = A * B := by
    dsimp only [S]
    rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
  have hPS : P < S := by nlinarith [sq_nonneg (P + S)]
  change P / S < 1
  exact (div_lt_one hS).2 hPS

private theorem symmetricThreePointDet_eq_diag_mul_correlationDeterminant
    {K : ℝ → ℝ → ℝ} {x y z : ℝ}
    (hx : 0 < K x x) (hy : 0 < K y y) (hz : 0 < K z z) :
    symmetricThreePointDet K x y z =
      (K x x * K y y * K z z) *
        HilbertMetric.threePointCorrelationDeterminant 1
          (K x y / (Real.sqrt (K x x) * Real.sqrt (K y y)))
          (K y z / (Real.sqrt (K y y) * Real.sqrt (K z z)))
          (K x z / (Real.sqrt (K x x) * Real.sqrt (K z z))) := by
  have hsx : Real.sqrt (K x x) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsy : Real.sqrt (K y y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hsz : Real.sqrt (K z z) ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  have hsx2 : Real.sqrt (K x x) ^ 2 = K x x := Real.sq_sqrt hx.le
  have hsy2 : Real.sqrt (K y y) ^ 2 = K y y := Real.sq_sqrt hy.le
  have hsz2 : Real.sqrt (K z z) ^ 2 = K z z := Real.sq_sqrt hz.le
  unfold symmetricThreePointDet HilbertMetric.threePointCorrelationDeterminant
  field_simp [hsx, hsy, hsz]
  rw [hsx2, hsy2, hsz2]
  ring

private theorem arccos_triangle_of_correlationDet_nonneg
    {p q r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hdet : 0 ≤ HilbertMetric.threePointCorrelationDeterminant 1 p q r) :
    Real.arccos r ≤ Real.arccos p + Real.arccos q := by
  let alpha := Real.arccos p
  let beta := Real.arccos q
  let gamma := Real.arccos r
  have halpha0 : 0 ≤ alpha := Real.arccos_nonneg p
  have hbeta0 : 0 ≤ beta := Real.arccos_nonneg q
  have hgammaPi : gamma ≤ Real.pi := Real.arccos_le_pi r
  have hcosa : Real.cos alpha = p := Real.cos_arccos (by linarith) hp1
  have hcosb : Real.cos beta = q := Real.cos_arccos (by linarith) hq1
  have hcosg : Real.cos gamma = r := Real.cos_arccos (by linarith) hr1
  have hsina0 : 0 ≤ Real.sin alpha :=
    Real.sin_nonneg_of_nonneg_of_le_pi halpha0 (Real.arccos_le_pi p)
  have hsinb0 : 0 ≤ Real.sin beta :=
    Real.sin_nonneg_of_nonneg_of_le_pi hbeta0 (Real.arccos_le_pi q)
  have hsinaSq : Real.sin alpha ^ 2 = 1 - p ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hsinbSq : Real.sin beta ^ 2 = 1 - q ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq beta]
  have hdet' :
      (r - p * q) ^ 2 ≤
        (Real.sin alpha * Real.sin beta) ^ 2 := by
    rw [mul_pow, hsinaSq, hsinbSq]
    unfold HilbertMetric.threePointCorrelationDeterminant at hdet
    nlinarith
  have hlower :
      -(Real.sin alpha * Real.sin beta) ≤ r - p * q := by
    by_contra h
    have hsumNeg :
        r - p * q + Real.sin alpha * Real.sin beta < 0 := by linarith
    have hdiffNeg :
        r - p * q - Real.sin alpha * Real.sin beta < 0 := by
      have hsinProd : 0 ≤ Real.sin alpha * Real.sin beta :=
        mul_nonneg hsina0 hsinb0
      linarith
    have hprod : 0 <
        (r - p * q - Real.sin alpha * Real.sin beta) *
          (r - p * q + Real.sin alpha * Real.sin beta) :=
      mul_pos_of_neg_of_neg hdiffNeg hsumNeg
    nlinarith
  have hcos : Real.cos (alpha + beta) ≤ Real.cos gamma := by
    rw [Real.cos_add, hcosa, hcosb, hcosg]
    linarith
  by_contra htriangle
  have hlt : alpha + beta < gamma := lt_of_not_ge htriangle
  have hstrict : Real.cos gamma < Real.cos (alpha + beta) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (add_nonneg halpha0 hbeta0) hgammaPi hlt
  exact (not_lt_of_ge hcos) hstrict

private theorem correlationDet_nonneg_iff_all_arccos_triangles
    {p q r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ HilbertMetric.threePointCorrelationDeterminant 1 p q r ↔
      Real.arccos r ≤ Real.arccos p + Real.arccos q ∧
      Real.arccos p ≤ Real.arccos r + Real.arccos q ∧
      Real.arccos q ≤ Real.arccos p + Real.arccos r := by
  constructor
  · intro hdet
    refine ⟨arccos_triangle_of_correlationDet_nonneg hp0 hp1.le hq0 hq1.le
      hr0 hr1.le hdet, ?_, ?_⟩
    · apply arccos_triangle_of_correlationDet_nonneg hr0 hr1.le hq0 hq1.le
        hp0 hp1.le
      unfold HilbertMetric.threePointCorrelationDeterminant at hdet ⊢
      nlinarith
    · apply arccos_triangle_of_correlationDet_nonneg hp0 hp1.le hr0 hr1.le
        hq0 hq1.le
      unfold HilbertMetric.threePointCorrelationDeterminant at hdet ⊢
      nlinarith
  · rintro ⟨hR, hP, hQ⟩
    by_cases hrp : r ≤ p
    · by_cases hrq : r ≤ q
      · have hpsd :=
          HilbertMetric.threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
            hp0 hp1.le hq0 hq1.le hr0 hrp hrq hR
        exact (HilbertMetric.threePointCorrelationMatrix_posSemidef_iff
          (by norm_num) hp0 hp1).1 hpsd
      · have hqr : q ≤ r := le_of_not_ge hrq
        have hqp : q ≤ p := hqr.trans hrp
        have hpsd :=
          HilbertMetric.threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
            hr0 hr1.le hp0 hp1.le hq0 hqr hqp (by simpa [add_comm] using hQ)
        have hdet' := (HilbertMetric.threePointCorrelationMatrix_posSemidef_iff
          (by norm_num) hr0 hr1).1 hpsd
        unfold HilbertMetric.threePointCorrelationDeterminant at hdet' ⊢
        nlinarith
    · have hpr : p ≤ r := le_of_not_ge hrp
      by_cases hpq : p ≤ q
      · have hpsd :=
          HilbertMetric.threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
            hr0 hr1.le hq0 hq1.le hp0 hpr hpq hP
        have hdet' := (HilbertMetric.threePointCorrelationMatrix_posSemidef_iff
          (by norm_num) hr0 hr1).1 hpsd
        unfold HilbertMetric.threePointCorrelationDeterminant at hdet' ⊢
        nlinarith
      · have hqp : q ≤ p := le_of_not_ge hpq
        have hqr : q ≤ r := hqp.trans hpr
        have hpsd :=
          HilbertMetric.threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
            hp0 hp1.le hr0 hr1.le hq0 hqp hqr hQ
        have hdet' := (HilbertMetric.threePointCorrelationMatrix_posSemidef_iff
          (by norm_num) hp0 hp1).1 hpsd
        unfold HilbertMetric.threePointCorrelationDeterminant at hdet' ⊢
        nlinarith

/-- **Exact angular determinant wall.** Full Xi Euler cubic is nonnegative exactly when its three normalized correlation angles obey all triangle inequalities. -/
theorem symmetricThreePointDet_xiSquaredEulerFullKernel_nonneg_iff_correlationTriangleLaw
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    0 ≤ symmetricThreePointDet xiSquaredEulerFullKernel x y z ↔
      XiSquaredEulerFullCorrelationTriangleLaw x y z := by
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  let p := xiSquaredEulerFullCorrelation x y
  let q := xiSquaredEulerFullCorrelation y z
  let r := xiSquaredEulerFullCorrelation x z
  have hp0 : 0 ≤ p := (xiSquaredEulerFullCorrelation_pos hx hy).le
  have hq0 : 0 ≤ q := (xiSquaredEulerFullCorrelation_pos hy hz).le
  have hr0 : 0 ≤ r := (xiSquaredEulerFullCorrelation_pos hx hz).le
  have hp1 : p < 1 := xiSquaredEulerFullCorrelation_lt_one hx hxy
  have hq1 : q < 1 := xiSquaredEulerFullCorrelation_lt_one hy hyz
  have hr1 : r < 1 := xiSquaredEulerFullCorrelation_lt_one hx (hxy.trans hyz)
  have hscale := symmetricThreePointDet_eq_diag_mul_correlationDeterminant
    (K := xiSquaredEulerFullKernel) (x := x) (y := y) (z := z)
    (xiSquaredEulerFullKernel_diag_pos hx)
    (xiSquaredEulerFullKernel_diag_pos hy)
    (xiSquaredEulerFullKernel_diag_pos hz)
  have hdiag : 0 <
      xiSquaredEulerFullKernel x x * xiSquaredEulerFullKernel y y *
        xiSquaredEulerFullKernel z z :=
    mul_pos
      (mul_pos (xiSquaredEulerFullKernel_diag_pos hx)
        (xiSquaredEulerFullKernel_diag_pos hy))
      (xiSquaredEulerFullKernel_diag_pos hz)
  rw [hscale, mul_nonneg_iff_of_pos_left hdiag]
  simpa only [p, q, r, xiSquaredEulerFullCorrelationAngle, XiSquaredEulerFullCorrelationTriangleLaw, xiSquaredEulerFullCorrelation] using
    correlationDet_nonneg_iff_all_arccos_triangles hp0 hp1 hq0 hq1 hr0 hr1

/-- Multiplicative-coordinate Lorentz cosine `(r + r⁻¹) / 2`. -/
def multiplicativeLorentzCosh (r : ℝ) : ℝ := (r + r⁻¹) / 2

/-- Multiplicative aperture boost between two positive nodes. -/
def xiSquaredEulerApertureBoost (x y : ℝ) : ℝ := Real.sqrt y / Real.sqrt x

/-- Multiplicative boost of the real centered-Xi logarithmic derivative. -/
def xiSquaredEulerResponseBoost (x y : ℝ) : ℝ :=
  Real.sqrt (xiSquaredEulerFullQ y) / Real.sqrt (xiSquaredEulerFullQ x)

private theorem xiSquaredEulerFullQ_pos {x : ℝ} (hx : 0 < x) :
    0 < xiSquaredEulerFullQ x := by
  unfold xiSquaredEulerFullQ
  exact mul_pos hx (xiSquaredEulerFullResponse_pos (sq_nonneg x))

/-- **Lorentz normal form.** Euler correlation is response-boost cosh divided by aperture-boost cosh. -/
theorem xiSquaredEulerFullCorrelation_eq_lorentzCosh_ratio
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    xiSquaredEulerFullCorrelation x y =
      multiplicativeLorentzCosh (xiSquaredEulerResponseBoost x y) /
        multiplicativeLorentzCosh (xiSquaredEulerApertureBoost x y) := by
  have hQx : 0 < xiSquaredEulerFullQ x := xiSquaredEulerFullQ_pos hx
  have hQy : 0 < xiSquaredEulerFullQ y := xiSquaredEulerFullQ_pos hy
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsy : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hsqx : Real.sqrt (xiSquaredEulerFullQ x) ≠ 0 :=
    (Real.sqrt_pos.2 hQx).ne'
  have hsqy : Real.sqrt (xiSquaredEulerFullQ y) ≠ 0 :=
    (Real.sqrt_pos.2 hQy).ne'
  have hdiagX : xiSquaredEulerFullKernel x x = xiSquaredEulerFullQ x / x := by
    unfold xiSquaredEulerFullKernel eulerRayResponseKernel
    field_simp [hx.ne']
  have hdiagY : xiSquaredEulerFullKernel y y = xiSquaredEulerFullQ y / y := by
    unfold xiSquaredEulerFullKernel eulerRayResponseKernel
    field_simp [hy.ne']
  have hdiagXpos : 0 < xiSquaredEulerFullQ x / x := div_pos hQx hx
  have hdiagYpos : 0 < xiSquaredEulerFullQ y / y := div_pos hQy hy
  have hsqrtDiagX :
      Real.sqrt (xiSquaredEulerFullQ x / x) =
        Real.sqrt (xiSquaredEulerFullQ x) / Real.sqrt x := by
    rw [Real.sqrt_div hQx.le]
  have hsqrtDiagY :
      Real.sqrt (xiSquaredEulerFullQ y / y) =
        Real.sqrt (xiSquaredEulerFullQ y) / Real.sqrt y := by
    rw [Real.sqrt_div hQy.le]
  rw [xiSquaredEulerFullCorrelation, hdiagX, hdiagY, hsqrtDiagX, hsqrtDiagY]
  unfold multiplicativeLorentzCosh xiSquaredEulerApertureBoost xiSquaredEulerResponseBoost
  unfold xiSquaredEulerFullKernel eulerRayResponseKernel
  field_simp [hx.ne', hy.ne', hsx, hsy, hsqx, hsqy]
  rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le,
    Real.sq_sqrt hQx.le, Real.sq_sqrt hQy.le]
  ring

/-- Multiplicative Lorentz cosine is ordinary hyperbolic cosine in logarithmic rapidity. -/
theorem multiplicativeLorentzCosh_eq_cosh_log {r : ℝ} (hr : 0 < r) :
    multiplicativeLorentzCosh r = Real.cosh (Real.log r) := by
  rw [Real.cosh_log hr]
  rfl

private theorem xiSquaredEulerFullQ_eq_xiRealLogDeriv {x : ℝ} (hx : 0 < x) :
    xiSquaredEulerFullQ x = xiRealLogDeriv x := by
  simpa only [xiRealLogDeriv] using xiSquaredEulerFullQ_eq_logDeriv_re hx

/-- **Strict causal chamber.** Ordered positive nodes place response boost strictly inside aperture boost. -/
theorem xiSquaredEulerResponseBoost_mem_futureCone
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    1 < xiSquaredEulerResponseBoost x y ∧
      xiSquaredEulerResponseBoost x y < xiSquaredEulerApertureBoost x y := by
  have hy : 0 < y := hx.trans hxy
  have hQx : 0 < xiSquaredEulerFullQ x := xiSquaredEulerFullQ_pos hx
  have hQy : 0 < xiSquaredEulerFullQ y := xiSquaredEulerFullQ_pos hy
  have hQxy : xiSquaredEulerFullQ x < xiSquaredEulerFullQ y := by
    rw [xiSquaredEulerFullQ_eq_xiRealLogDeriv hx, xiSquaredEulerFullQ_eq_xiRealLogDeriv hy]
    exact strictMono_xiRealLogDeriv hxy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hsQx : 0 < Real.sqrt (xiSquaredEulerFullQ x) := Real.sqrt_pos.2 hQx
  have hsQy : 0 < Real.sqrt (xiSquaredEulerFullQ y) := Real.sqrt_pos.2 hQy
  have hsQxy :
      Real.sqrt (xiSquaredEulerFullQ x) <
        Real.sqrt (xiSquaredEulerFullQ y) :=
    Real.sqrt_lt_sqrt hQx.le hQxy
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hresponseDecrease :=
    strictAntiOn_xiSquaredEulerFullResponse (sq_nonneg x) (sq_nonneg y) hsq
  have hcrossRaw :
      x * xiSquaredEulerFullQ y < y * xiSquaredEulerFullQ x := by
    calc
      x * xiSquaredEulerFullQ y =
          (x * y) * xiSquaredEulerFullResponse (y ^ 2) := by
            unfold xiSquaredEulerFullQ
            ring
      _ < (x * y) * xiSquaredEulerFullResponse (x ^ 2) :=
        mul_lt_mul_of_pos_left hresponseDecrease (mul_pos hx hy)
      _ = y * xiSquaredEulerFullQ x := by
        unfold xiSquaredEulerFullQ
        ring
  have hcross :
      Real.sqrt (xiSquaredEulerFullQ y) * Real.sqrt x <
        Real.sqrt y * Real.sqrt (xiSquaredEulerFullQ x) := by
    have hleft0 : 0 ≤ Real.sqrt (xiSquaredEulerFullQ y) * Real.sqrt x := by positivity
    have hright0 : 0 ≤ Real.sqrt y * Real.sqrt (xiSquaredEulerFullQ x) := by positivity
    nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le,
      Real.sq_sqrt hQx.le, Real.sq_sqrt hQy.le,
      sq_nonneg
        (Real.sqrt (xiSquaredEulerFullQ y) * Real.sqrt x +
          Real.sqrt y * Real.sqrt (xiSquaredEulerFullQ x))]
  constructor
  · unfold xiSquaredEulerResponseBoost
    exact (one_lt_div hsQx).2 hsQxy
  · unfold xiSquaredEulerResponseBoost xiSquaredEulerApertureBoost
    exact (div_lt_div_iff₀ hsQx hsx).2 hcross

/-- Aperture boosts compose exactly across an intermediate positive node. -/
theorem xiSquaredEulerApertureBoost_comp
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) :
    xiSquaredEulerApertureBoost x z =
      xiSquaredEulerApertureBoost x y * xiSquaredEulerApertureBoost y z := by
  unfold xiSquaredEulerApertureBoost
  field_simp [(Real.sqrt_pos.2 hx).ne', (Real.sqrt_pos.2 hy).ne']

/-- Response boosts compose exactly across an intermediate positive node. -/
theorem xiSquaredEulerResponseBoost_comp
    {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) :
    xiSquaredEulerResponseBoost x z =
      xiSquaredEulerResponseBoost x y * xiSquaredEulerResponseBoost y z := by
  have hQx := xiSquaredEulerFullQ_pos hx
  have hQy := xiSquaredEulerFullQ_pos hy
  unfold xiSquaredEulerResponseBoost
  field_simp [(Real.sqrt_pos.2 hQx).ne', (Real.sqrt_pos.2 hQy).ne']

/-- Product of future-null defects associated with aperture and response boosts.
It is the squared tangent-half-angle coordinate of their Lorentz-cosh correlation ratio. -/
def multiplicativeLorentzNullDefect (A U : ℝ) : ℝ :=
  ((A - U) * (A * U - 1)) / ((A + U) * (A * U + 1))

/-- Exact Cayley factorization of a Lorentz-cosh correlation ratio into its two null channels. -/
theorem one_sub_lorentzCoshRatio_div_one_add_eq_nullDefect
    {A U : ℝ} (hA : 0 < A) (hU : 0 < U) :
    (1 - multiplicativeLorentzCosh U / multiplicativeLorentzCosh A) /
        (1 + multiplicativeLorentzCosh U / multiplicativeLorentzCosh A) =
      multiplicativeLorentzNullDefect A U := by
  have hA0 : A ≠ 0 := hA.ne'
  have hU0 : U ≠ 0 := hU.ne'
  have hAsq : A ^ 2 + 1 ≠ 0 := by positivity
  have hUsq : U ^ 2 + 1 ≠ 0 := by positivity
  have hsum : A + U ≠ 0 := (add_pos hA hU).ne'
  have hprodSum : A * U + 1 ≠ 0 := by positivity
  unfold multiplicativeLorentzCosh multiplicativeLorentzNullDefect
  field_simp [hA0, hU0, hAsq, hUsq, hsum, hprodSum]
  ring

/-- Strict future-cone order makes both null factors, hence angular Cayley defect, positive. -/
theorem multiplicativeLorentzNullDefect_pos_of_futureCone
    {A U : ℝ} (hU : 1 < U) (hUA : U < A) :
    0 < multiplicativeLorentzNullDefect A U := by
  unfold multiplicativeLorentzNullDefect
  have hA : 0 < A := zero_lt_one.trans (hU.trans hUA)
  exact div_pos
    (mul_pos (sub_pos.mpr hUA)
      (sub_pos.mpr (one_lt_mul (hU.trans hUA).le hU)))
    (mul_pos (add_pos hA (zero_lt_one.trans hU))
      (add_pos (mul_pos hA (zero_lt_one.trans hU)) zero_lt_one))

/-- Full Xi Euler angular Cayley defect is exactly product of its two Lorentz null channels. -/
theorem xiSquaredEulerFullCorrelation_cayleyDefect_eq_lorentzNullDefect
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 - xiSquaredEulerFullCorrelation x y) /
        (1 + xiSquaredEulerFullCorrelation x y) =
      multiplicativeLorentzNullDefect
        (xiSquaredEulerApertureBoost x y)
        (xiSquaredEulerResponseBoost x y) := by
  rw [xiSquaredEulerFullCorrelation_eq_lorentzCosh_ratio hx hy]
  apply one_sub_lorentzCoshRatio_div_one_add_eq_nullDefect
  · unfold xiSquaredEulerApertureBoost
    exact div_pos (Real.sqrt_pos.2 hy) (Real.sqrt_pos.2 hx)
  · unfold xiSquaredEulerResponseBoost
    exact div_pos
      (Real.sqrt_pos.2 (xiSquaredEulerFullQ_pos hy))
      (Real.sqrt_pos.2 (xiSquaredEulerFullQ_pos hx))

/-- **Strict causal-order no-go.** Strict response-within-aperture boost order, even together
with exact multiplicative composition, does not force the three-point correlation determinant
nonnegative. This exact rational packet falsifies that tempting universal Lorentz-cone producer. -/
theorem strictFutureConeBoostComposition_correlationDet_neg :
    let A₁ : ℝ := 4
    let A₂ : ℝ := 4
    let U₁ : ℝ := 39 / 10
    let U₂ : ℝ := 40 / 39
    let p := multiplicativeLorentzCosh U₁ / multiplicativeLorentzCosh A₁
    let q := multiplicativeLorentzCosh U₂ / multiplicativeLorentzCosh A₂
    let r := multiplicativeLorentzCosh (U₁ * U₂) /
      multiplicativeLorentzCosh (A₁ * A₂)
    1 < U₁ ∧ U₁ < A₁ ∧ 1 < U₂ ∧ U₂ < A₂ ∧
      HilbertMetric.threePointCorrelationDeterminant 1 p q r < 0 := by
  norm_num [multiplicativeLorentzCosh,
    HilbertMetric.threePointCorrelationDeterminant]

/-- Every complex three-real Euler energy is nonnegative exactly when correlation angles form a metric triangle. -/
theorem threeRealEulerResponseEnergy_nonneg_iff_correlationTriangleLaw
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    (∀ c : Fin 3 → ℂ, 0 ≤ threeRealEulerResponseEnergy x y z c) ↔
      XiSquaredEulerFullCorrelationTriangleLaw x y z :=
  (threeRealEulerResponseEnergy_nonneg_iff_det_nonneg hx hxy hyz).trans
    (symmetricThreePointDet_xiSquaredEulerFullKernel_nonneg_iff_correlationTriangleLaw hx hxy hyz)

/-- Negative literal three-mode real theta flux exists exactly when Euler correlation angles fail triangle geometry. -/
theorem exists_threeMode_realRay_thetaCuspTiltFlux_neg_iff_correlationTriangleFailure
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z) :
    (∃ (c : Fin 3 → ℂ) (D : ℝ),
        HasDerivAt
          (tiltCorrelation thetaCuspTiltSource c (threeRealNodes x y z)) D 0 ∧
        D < 0) ↔
      ¬ XiSquaredEulerFullCorrelationTriangleLaw x y z := by
  rw [exists_threeMode_realRay_thetaCuspTiltFlux_neg_iff_det_neg hx hxy hyz]
  have hcriterion := symmetricThreePointDet_xiSquaredEulerFullKernel_nonneg_iff_correlationTriangleLaw (x := x) (y := y) (z := z)
    (by linarith) hxy hyz
  constructor
  · intro hneg htriangle
    exact (not_lt_of_ge (hcriterion.2 htriangle)) hneg
  · intro hfailure
    exact lt_of_not_ge (fun hnonneg => hfailure (hcriterion.1 hnonneg))

/-- Explicit classification: negative literal theta flux is exactly one of three strict angular triangle violations. -/
theorem exists_threeMode_realRay_thetaCuspTiltFlux_neg_iff_correlationAngleViolation
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z) :
    (∃ (c : Fin 3 → ℂ) (D : ℝ),
        HasDerivAt
          (tiltCorrelation thetaCuspTiltSource c (threeRealNodes x y z)) D 0 ∧
        D < 0) ↔
      xiSquaredEulerFullCorrelationAngle x z > xiSquaredEulerFullCorrelationAngle x y + xiSquaredEulerFullCorrelationAngle y z ∨
      xiSquaredEulerFullCorrelationAngle x y > xiSquaredEulerFullCorrelationAngle x z + xiSquaredEulerFullCorrelationAngle y z ∨
      xiSquaredEulerFullCorrelationAngle y z > xiSquaredEulerFullCorrelationAngle x y + xiSquaredEulerFullCorrelationAngle x z := by
  rw [exists_threeMode_realRay_thetaCuspTiltFlux_neg_iff_correlationTriangleFailure hx hxy hyz]
  simp only [XiSquaredEulerFullCorrelationTriangleLaw, not_and_or, not_le]

end

end RHTower
