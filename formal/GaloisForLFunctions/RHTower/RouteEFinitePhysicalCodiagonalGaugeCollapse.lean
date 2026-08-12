import GaloisForLFunctions.HTGeometry.InfiniteFisherOneCornerCodiagonalContraction
import GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation
import GaloisForLFunctions.RHTower.RouteEEntropyComplementBreadthMixture

/-!
# Route E finite physical codiagonal and sharp Fisher gauge collapse

This module closes two exact finite faces of the critical antiscale/codiagonal transfer law.

First, it sharpens the universal one-corner geometry.  A lower corner of a pointed Fisher
connection has at most half of the tangent energy.  Pairing it with any contractive joined
reporter therefore costs at most one quarter of the tangent energy.  This improves the coarse
`sqrt 2` gauge-collapse constant to `1` for every all-order squarefree Euler packet.

Second, it identifies the physical centered likelihood-ratio energy for arbitrary finite pushed
and target masses.  Total Pearson chi-square is exactly centered column energy plus scalar signed
mass discrepancy, including the empty finite type without an extra nonemptiness premise.

Third, it proves literal finite complex codiagonal recovery and the full
mean/off-diagonal/collision trichotomy for arbitrary state-dependent cofactors, including exact
maximum-atom collision control.

All statements are finite and unconditional.  No Route E incidence, capacity, seam, or recurrence
estimate is assumed.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Sharp pointed-Fisher lower-corner law.**  Every orthogonal cutoff retains at most half of
the tangent energy in one oriented corner.  State--tangent orthogonality is not needed. -/
theorem hsNormSq_cutoffLowerBoundary_pointedFisherConnection_le_half
    (e : H →L[ℂ] H) (psi chi : H)
    (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hpsi : ‖psi‖ = 1) :
    hsNormSq (cutoffLowerBoundary e (pointedFisherConnection psi chi)) ≤
      (1 / 2 : ℝ) * ‖chi‖ ^ 2 := by
  by_cases hchi : chi = 0
  · subst chi
    have hzero : hsNormSq (0 : H →L[ℂ] H) = 0 :=
      (hsNormSq_eq_zero_iff isHilbertSchmidt_zero).2 rfl
    simp [cutoffLowerBoundary, pointedFisherConnection, hzero]
  · let chiUnit : H := ((‖chi‖ : ℂ)⁻¹) • chi
    let D : H →L[ℂ] H := rankOne ℂ chiUnit psi
    have hchiNorm : ‖chi‖ ≠ 0 := norm_ne_zero_iff.mpr hchi
    have hchiUnit : ‖chiUnit‖ = 1 := by
      simp only [chiUnit, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg chi), inv_mul_cancel₀ hchiNorm]
    have hDpsi : D psi = chiUnit := by
      simp only [D, rankOne_apply, inner_self_eq_norm_sq_to_K, hpsi]
      norm_num
    have hDnorm : ‖D‖ ≤ 1 := by
      simp only [D, InnerProductSpace.norm_rankOne, hchiUnit, hpsi]
      norm_num
    have hchiScale : ((‖chi‖ : ℂ) • chiUnit) = chi := by
      simp only [chiUnit, smul_smul]
      simp [hchiNorm]
    have hconnectionScaleGeneral (r : ℝ) (v : H) :
        pointedFisherConnection psi ((r : ℂ) • v) =
          (r : ℂ) • pointedFisherConnection psi v := by
      ext z
      simp only [pointedFisherConnection, smul_apply, add_apply, rankOne_apply,
        inner_smul_left, map_smul, smul_add, smul_smul, Complex.conj_ofReal]
      module
    have hconnectionScale :
        pointedFisherConnection psi chi =
          (‖chi‖ : ℂ) • pointedFisherConnection psi chiUnit := by
      calc
        pointedFisherConnection psi chi =
            pointedFisherConnection psi ((‖chi‖ : ℂ) • chiUnit) := by rw [hchiScale]
        _ = _ := hconnectionScaleGeneral ‖chi‖ chiUnit
    have hboundaryScale :
        cutoffLowerBoundary e (pointedFisherConnection psi chi) =
          (‖chi‖ : ℂ) • infiniteFisherOneCornerJoinedReporter e D psi := by
      rw [hconnectionScale, infiniteFisherOneCornerJoinedReporter, hDpsi]
      ext z
      simp [cutoffLowerBoundary]
    have hreporterHS :
        IsHilbertSchmidt (infiniteFisherOneCornerJoinedReporter e D psi) := by
      exact ((pointedFisherConnection_isHilbertSchmidt psi (D psi)).comp_right e)
        |>.comp_left (1 - e)
    have hreporter :=
      hsNormSq_infiniteFisherOneCornerJoinedReporter_le_half
        e D psi he heAdj hpsi hDnorm
    rw [hboundaryScale, hsNormSq_smul hreporterHS,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg chi)]
    nlinarith [sq_nonneg ‖chi‖]

/-- A one-corner Fisher source paired with any joined contractive reporter has at most one
quarter of the total pointed-connection energy. -/
theorem norm_sq_hsInner_cutoffLowerBoundary_joinedReporter_le_quarter
    (e D : H →L[ℂ] H) (psi chi : H)
    (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hpsi : ‖psi‖ = 1) (hD : ‖D‖ ≤ 1) :
    ‖hsInner
        (cutoffLowerBoundary e (pointedFisherConnection psi chi))
        (infiniteFisherOneCornerJoinedReporter e D psi)‖ ^ 2 ≤
      (1 / 4 : ℝ) * ‖chi‖ ^ 2 := by
  have hsource : IsHilbertSchmidt
      (cutoffLowerBoundary e (pointedFisherConnection psi chi)) := by
    exact ((pointedFisherConnection_isHilbertSchmidt psi chi).comp_right e)
      |>.comp_left (1 - e)
  have hpair :=
    norm_sq_hsInner_infiniteFisherOneCornerJoinedReporter_le_half
      (cutoffLowerBoundary e (pointedFisherConnection psi chi))
      e D psi hsource he heAdj hpsi hD
  have hlower := hsNormSq_cutoffLowerBoundary_pointedFisherConnection_le_half e psi chi he heAdj hpsi
  calc
    ‖hsInner
        (cutoffLowerBoundary e (pointedFisherConnection psi chi))
        (infiniteFisherOneCornerJoinedReporter e D psi)‖ ^ 2 ≤
        (1 / 2 : ℝ) * hsNormSq
          (cutoffLowerBoundary e (pointedFisherConnection psi chi)) := hpair
    _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * ‖chi‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ = (1 / 4 : ℝ) * ‖chi‖ ^ 2 := by ring

end GaloisForLFunctions.HTGeometry

namespace RHTower

open ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry

/-! ## Literal finite complex codiagonal -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Target-weighted complex score. -/
def routeEFiniteCodiagonalScore (w : Ω → ℝ) (A d : Ω → ℂ) : ℂ :=
  ∑ s, (w s : ℂ) * A s * d s

/-- Atomic diagonal collision omitted by the off-diagonal codiagonal. -/
def routeEFiniteCodiagonalCollision (w : Ω → ℝ) (A d : Ω → ℂ) : ℂ :=
  ∑ s, ((w s ^ 2 : ℝ) : ℂ) * A s * d s

/-- Literal ordered-pair codiagonal with equal-state pairs removed. -/
def routeEFiniteOffDiagonalCodiagonal (w : Ω → ℝ) (A d : Ω → ℂ) : ℂ :=
  ∑ s, ∑ q, if q = s then 0 else
    (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s)

/-- Weighted centered-state energy controlling atomic collision. -/
def routeEFiniteCodiagonalEnergy (w : Ω → ℝ) (A : Ω → ℂ) : ℝ :=
  ∑ s, w s * ‖A s‖ ^ 2

/-- **Exact finite complex codiagonal recovery.**  A centered score equals literal off-diagonal
codiagonal plus twice its atomic collision. -/
theorem routeEFiniteOffDiagonalCodiagonal_eq_score_sub_collision
    (w : Ω → ℝ) (A d : Ω → ℂ)
    (hw : ∑ s, w s = 1)
    (hcenter : ∑ s, (w s : ℂ) * A s = 0) :
    routeEFiniteOffDiagonalCodiagonal w A d =
      routeEFiniteCodiagonalScore w A d -
        2 * routeEFiniteCodiagonalCollision w A d := by
  classical
  have hwC : ∑ s, (w s : ℂ) = 1 := by
    exact_mod_cast hw
  have hcomplete :
      (∑ s, ∑ q, (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s)) =
        routeEFiniteCodiagonalScore w A d := by
    calc
      _ = ∑ s,
          ((w s : ℂ) * A s * d s * (∑ q, (w q : ℂ)) +
            (w s : ℂ) * d s * (∑ q, (w q : ℂ) * A q)) := by
              apply Finset.sum_congr rfl
              intro s _hs
              rw [Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro q _hq
              push_cast
              ring
      _ = routeEFiniteCodiagonalScore w A d := by
        simp_rw [hwC, hcenter, mul_one, mul_zero, add_zero]
        rfl
  have hdiag :
      (∑ s, ∑ q, if q = s then
          (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s) else 0) =
        2 * routeEFiniteCodiagonalCollision w A d := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [routeEFiniteCodiagonalCollision, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    push_cast
    ring
  rw [routeEFiniteOffDiagonalCodiagonal]
  calc
    (∑ s, ∑ q, if q = s then 0 else
        (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s)) =
      (∑ s, ∑ q, (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s)) -
      (∑ s, ∑ q, if q = s then
        (((w s * w q : ℝ) : ℂ) * (A s + A q) * d s) else 0) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s _hs
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro q _hq
          split_ifs <;> ring
    _ = routeEFiniteCodiagonalScore w A d -
        2 * routeEFiniteCodiagonalCollision w A d := by
      rw [hcomplete, hdiag]

omit [DecidableEq Ω] in
private theorem weighted_norm_sum_le_sqrt_routeEFiniteCodiagonalEnergy
    (w : Ω → ℝ) (A : Ω → ℂ)
    (hw_nonneg : ∀ s, 0 ≤ w s) (hw : ∑ s, w s = 1) :
    (∑ s, w s * ‖A s‖) ≤ Real.sqrt (routeEFiniteCodiagonalEnergy w A) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset Ω)
    (fun s => Real.sqrt (w s))
    (fun s => Real.sqrt (w s) * ‖A s‖)
  have hleft :
      (∑ s, Real.sqrt (w s) * (Real.sqrt (w s) * ‖A s‖)) =
        ∑ s, w s * ‖A s‖ := by
    apply Finset.sum_congr rfl
    intro s _hs
    rw [← mul_assoc, Real.mul_self_sqrt (hw_nonneg s)]
  have hfirst : (∑ s, Real.sqrt (w s) ^ 2) = 1 := by
    simpa only [Real.sq_sqrt (hw_nonneg _)] using hw
  have hsecond :
      (∑ s, (Real.sqrt (w s) * ‖A s‖) ^ 2) =
        routeEFiniteCodiagonalEnergy w A := by
    unfold routeEFiniteCodiagonalEnergy
    apply Finset.sum_congr rfl
    intro s _hs
    rw [mul_pow, Real.sq_sqrt (hw_nonneg s)]
  rw [hleft, hfirst, hsecond, one_mul] at hcs
  have henergy : 0 ≤ routeEFiniteCodiagonalEnergy w A := by
    unfold routeEFiniteCodiagonalEnergy
    exact Finset.sum_nonneg fun s _hs => mul_nonneg (hw_nonneg s) (sq_nonneg _)
  have hsqrt := Real.sq_sqrt henergy
  have hsum : 0 ≤ ∑ s, w s * ‖A s‖ :=
    Finset.sum_nonneg fun s _hs => mul_nonneg (hw_nonneg s) (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg (routeEFiniteCodiagonalEnergy w A)]

/-- **Diffuse finite complex collision bound.**  Maximum atom weight controls exact defect
between centered score and literal off-diagonal codiagonal. -/
theorem norm_routeEFiniteCodiagonalScore_sub_offDiagonal_le
    (w : Ω → ℝ) (A d : Ω → ℂ) (wMax : ℝ)
    (hw_nonneg : ∀ s, 0 ≤ w s)
    (hw_le : ∀ s, w s ≤ wMax)
    (hw : ∑ s, w s = 1)
    (hcenter : ∑ s, (w s : ℂ) * A s = 0)
    (hd : ∀ s, ‖d s‖ ≤ 1) :
    ‖routeEFiniteCodiagonalScore w A d -
        routeEFiniteOffDiagonalCodiagonal w A d‖ ≤
      2 * wMax * Real.sqrt (routeEFiniteCodiagonalEnergy w A) := by
  have huniv : (Finset.univ : Finset Ω).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hw
    simp at hw
  obtain ⟨s0, _hs0⟩ := huniv
  have hwMax_nonneg : 0 ≤ wMax := (hw_nonneg s0).trans (hw_le s0)
  have hcollision :
      ‖routeEFiniteCodiagonalCollision w A d‖ ≤
        wMax * Real.sqrt (routeEFiniteCodiagonalEnergy w A) := by
    calc
      ‖routeEFiniteCodiagonalCollision w A d‖ ≤
          ∑ s, ‖(((w s ^ 2 : ℝ) : ℂ) * A s * d s)‖ := by
            unfold routeEFiniteCodiagonalCollision
            exact norm_sum_le _ _
      _ ≤ ∑ s, wMax * (w s * ‖A s‖) := by
        apply Finset.sum_le_sum
        intro s _hs
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg (w s))]
        calc
          w s ^ 2 * ‖A s‖ * ‖d s‖ ≤ w s ^ 2 * ‖A s‖ * 1 :=
            mul_le_mul_of_nonneg_left (hd s)
              (mul_nonneg (sq_nonneg _) (norm_nonneg _))
          _ ≤ wMax * (w s * ‖A s‖) := by
            have hbase : 0 ≤ w s * ‖A s‖ :=
              mul_nonneg (hw_nonneg s) (norm_nonneg _)
            calc
              w s ^ 2 * ‖A s‖ * 1 = (w s * ‖A s‖) * w s := by ring
              _ ≤ (w s * ‖A s‖) * wMax :=
                mul_le_mul_of_nonneg_left (hw_le s) hbase
              _ = wMax * (w s * ‖A s‖) := by ring
      _ = wMax * (∑ s, w s * ‖A s‖) := by rw [Finset.mul_sum]
      _ ≤ wMax * Real.sqrt (routeEFiniteCodiagonalEnergy w A) :=
        mul_le_mul_of_nonneg_left
          (weighted_norm_sum_le_sqrt_routeEFiniteCodiagonalEnergy
            w A hw_nonneg hw) hwMax_nonneg
  have hid := routeEFiniteOffDiagonalCodiagonal_eq_score_sub_collision
    w A d hw hcenter
  calc
    ‖routeEFiniteCodiagonalScore w A d -
        routeEFiniteOffDiagonalCodiagonal w A d‖ =
        ‖(2 : ℂ) * routeEFiniteCodiagonalCollision w A d‖ := by
          rw [hid]
          congr 1
          ring
    _ = 2 * ‖routeEFiniteCodiagonalCollision w A d‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * (wMax * Real.sqrt (routeEFiniteCodiagonalEnergy w A)) :=
      mul_le_mul_of_nonneg_left hcollision (by norm_num)
    _ = 2 * wMax * Real.sqrt (routeEFiniteCodiagonalEnergy w A) := by ring

/-- Weighted state mean for arbitrary complex cofactor blocks. -/
def routeEFiniteCodiagonalMean (w : Ω → ℝ) (G : Ω → ℂ) : ℂ :=
  ∑ s, (w s : ℂ) * G s

/-- State cofactor centered at its physical weighted mean. -/
def routeEFiniteCenteredCofactor (w : Ω → ℝ) (G : Ω → ℂ) (s : Ω) : ℂ :=
  G s - routeEFiniteCodiagonalMean w G

omit [DecidableEq Ω] in
/-- Centering is exact for every normalized real weight law. -/
theorem routeEFiniteCenteredCofactor_mean_zero
    (w : Ω → ℝ) (G : Ω → ℂ) (hw : ∑ s, w s = 1) :
    ∑ s, (w s : ℂ) * routeEFiniteCenteredCofactor w G s = 0 := by
  have hwC : ∑ s, (w s : ℂ) = 1 := by
    exact_mod_cast hw
  unfold routeEFiniteCenteredCofactor routeEFiniteCodiagonalMean
  calc
    (∑ s, (w s : ℂ) * (G s - ∑ q, (w q : ℂ) * G q)) =
        ∑ s, ((w s : ℂ) * G s -
          (∑ q, (w q : ℂ) * G q) * (w s : ℂ)) := by
            apply Finset.sum_congr rfl
            intro s _hs
            ring
    _ = (∑ s, (w s : ℂ) * G s) -
          (∑ q, (w q : ℂ) * G q) * (∑ s, (w s : ℂ)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 0 := by rw [hwC]; ring

/-- **Mean/codiagonal/collision trichotomy.**  Arbitrary state-dependent complex cofactors split
exactly into weighted mean, one centered off-diagonal reporter, and atomic collision. -/
theorem routeEFinite_mean_offDiagonal_collision_decomposition
    (w : Ω → ℝ) (G d : Ω → ℂ) (hw : ∑ s, w s = 1) :
    (∑ s, (w s : ℂ) * d s * G s) =
      routeEFiniteCodiagonalMean w G * (∑ s, (w s : ℂ) * d s) +
        routeEFiniteOffDiagonalCodiagonal w (routeEFiniteCenteredCofactor w G) d +
          2 * routeEFiniteCodiagonalCollision w (routeEFiniteCenteredCofactor w G) d := by
  have hcenter := routeEFiniteCenteredCofactor_mean_zero w G hw
  have hoff := routeEFiniteOffDiagonalCodiagonal_eq_score_sub_collision
    w (routeEFiniteCenteredCofactor w G) d hw hcenter
  have hsplit :
      (∑ s, (w s : ℂ) * d s * G s) =
        routeEFiniteCodiagonalMean w G * (∑ s, (w s : ℂ) * d s) +
          routeEFiniteCodiagonalScore w (routeEFiniteCenteredCofactor w G) d := by
    unfold routeEFiniteCodiagonalMean routeEFiniteCodiagonalScore
      routeEFiniteCenteredCofactor
    simp only [routeEFiniteCodiagonalMean]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  rw [hsplit, hoff]
  ring

/-- Atomic collision in the mean/codiagonal decomposition obeys exact maximum-weight decay. -/
theorem norm_two_mul_routeEFiniteCenteredCofactor_collision_le
    (w : Ω → ℝ) (G d : Ω → ℂ) (wMax : ℝ)
    (hw_nonneg : ∀ s, 0 ≤ w s)
    (hw_le : ∀ s, w s ≤ wMax)
    (hw : ∑ s, w s = 1)
    (hd : ∀ s, ‖d s‖ ≤ 1) :
    ‖2 * routeEFiniteCodiagonalCollision w (routeEFiniteCenteredCofactor w G) d‖ ≤
      2 * wMax * Real.sqrt
        (routeEFiniteCodiagonalEnergy w (routeEFiniteCenteredCofactor w G)) := by
  have hbound := norm_routeEFiniteCodiagonalScore_sub_offDiagonal_le
    w (routeEFiniteCenteredCofactor w G) d wMax hw_nonneg hw_le hw
      (routeEFiniteCenteredCofactor_mean_zero w G hw) hd
  have hoff := routeEFiniteOffDiagonalCodiagonal_eq_score_sub_collision
    w (routeEFiniteCenteredCofactor w G) d hw
      (routeEFiniteCenteredCofactor_mean_zero w G hw)
  rw [hoff] at hbound
  convert hbound using 1
  ring

/-- Finite squarefree Fisher connection over every occupied-subset history of `S`. -/
def routeEFiniteSquarefreeFisherConnection (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) →L[ℂ]
      EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  pointedFisherConnection
    (finiteSquarefreeSource S sigma) (finiteSquarefreeTangent S sigma)

theorem routeEFiniteSquarefreeFisherConnection_energy
    (S : Finset Nat.Primes) (sigma : ℝ) :
    hsNormSq (routeEFiniteSquarefreeFisherConnection S sigma) =
      4 * (sigma - 1) ^ 2 * finiteSquarefreeCurvature S sigma := by
  rw [routeEFiniteSquarefreeFisherConnection,
    hsNormSq_pointedFisherConnection_of_unit_of_orthogonal
      (finiteSquarefreeSource S sigma) (finiteSquarefreeTangent S sigma)
      (norm_finiteSquarefreeSource S sigma)
      (inner_finiteSquarefreeSource_tangent_eq_zero S sigma),
    norm_finiteSquarefreeTangent_sq]

/-- Finite squarefree curvature is nonnegative for every real Euler parameter. -/
theorem finiteSquarefreeCurvature_nonneg (S : Finset Nat.Primes) (sigma : ℝ) :
    0 ≤ finiteSquarefreeCurvature S sigma := by
  rw [← finiteSquarefreeCurvature_eq_variance]
  apply Finset.sum_nonneg
  intro x _hx
  apply mul_nonneg
  · unfold finiteSquarefreeBornWeight squarefreeBitWeight
    apply Finset.prod_nonneg
    intro p _hp
    split_ifs
    · linarith [squarefreePrimeOccupation_lt_one sigma p]
    · exact (squarefreePrimeOccupation_pos sigma p).le
  · exact sq_nonneg _

/-- **Sharp finite Fisher gauge-collapse law, squared form.** -/
theorem norm_sq_hsInner_routeEFiniteSquarefreeFisherLowerBoundary_joinedReporter_le
    (S : Finset Nat.Primes) (sigma : ℝ)
    (e D : EuclideanSpace ℂ (SquarefreeBitConfig S) →L[ℂ]
      EuclideanSpace ℂ (SquarefreeBitConfig S))
    (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hD : ‖D‖ ≤ 1) :
    ‖hsInner
        (cutoffLowerBoundary e (routeEFiniteSquarefreeFisherConnection S sigma))
        (infiniteFisherOneCornerJoinedReporter e D
          (finiteSquarefreeSource S sigma))‖ ^ 2 ≤
      (sigma - 1) ^ 2 * finiteSquarefreeCurvature S sigma := by
  have hpair := norm_sq_hsInner_cutoffLowerBoundary_joinedReporter_le_quarter e D
    (finiteSquarefreeSource S sigma) (finiteSquarefreeTangent S sigma)
    he heAdj (norm_finiteSquarefreeSource S sigma)
    hD
  rw [routeEFiniteSquarefreeFisherConnection]
  rw [norm_finiteSquarefreeTangent_sq] at hpair
  nlinarith

/-- **Sharp finite Fisher gauge-collapse law.**  The constant is `1`, improving the direct
compression-plus-half-unit estimate by `sqrt 2`. -/
theorem norm_hsInner_routeEFiniteSquarefreeFisherLowerBoundary_joinedReporter_le
    (S : Finset Nat.Primes) (sigma : ℝ)
    (e D : EuclideanSpace ℂ (SquarefreeBitConfig S) →L[ℂ]
      EuclideanSpace ℂ (SquarefreeBitConfig S))
    (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hD : ‖D‖ ≤ 1) :
    ‖hsInner
        (cutoffLowerBoundary e (routeEFiniteSquarefreeFisherConnection S sigma))
        (infiniteFisherOneCornerJoinedReporter e D
          (finiteSquarefreeSource S sigma))‖ ≤
      |sigma - 1| * Real.sqrt (finiteSquarefreeCurvature S sigma) := by
  have hsq := norm_sq_hsInner_routeEFiniteSquarefreeFisherLowerBoundary_joinedReporter_le S sigma e D he heAdj hD
  have hcurv := finiteSquarefreeCurvature_nonneg S sigma
  have hsqrt := Real.sq_sqrt hcurv
  have hrhs : 0 ≤ |sigma - 1| * Real.sqrt (finiteSquarefreeCurvature S sigma) :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hrhsSq :
      (|sigma - 1| * Real.sqrt (finiteSquarefreeCurvature S sigma)) ^ 2 =
        (sigma - 1) ^ 2 * finiteSquarefreeCurvature S sigma := by
    rw [mul_pow, sq_abs, hsqrt]
  nlinarith [norm_nonneg
    (hsInner
      (cutoffLowerBoundary e (routeEFiniteSquarefreeFisherConnection S sigma))
      (infiniteFisherOneCornerJoinedReporter e D
        (finiteSquarefreeSource S sigma)))]

/-- Division-free gauge-neutral tangent.  This is the physical centered logarithmic direction
before multiplication by the Euler coordinate `sigma - 1`. -/
def routeEFiniteSquarefreeGaugeNeutralTangent (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  WithLp.toLp 2 fun x =>
    ((-2 * (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x

theorem finiteSquarefreeTangent_eq_gauge_smul_neutral
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finiteSquarefreeTangent S sigma =
      ((sigma - 1 : ℝ) : ℂ) • routeEFiniteSquarefreeGaugeNeutralTangent S sigma := by
  apply (WithLp.equiv 2 _).injective
  funext x
  change
    (((-2 * (sigma - 1) *
      (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x) =
    (((sigma - 1 : ℝ) : ℂ) *
      (((-2 *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
        finiteSquarefreeSourceCoefficient S sigma x))
  push_cast
  ring

theorem norm_routeEFiniteSquarefreeGaugeNeutralTangent_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ‖routeEFiniteSquarefreeGaugeNeutralTangent S sigma‖ ^ 2 =
      4 * finiteSquarefreeCurvature S sigma := by
  rw [routeEFiniteSquarefreeGaugeNeutralTangent, EuclideanSpace.norm_sq_eq]
  change (∑ x : SquarefreeBitConfig S,
    ‖(((-2 *
      (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
      finiteSquarefreeSourceCoefficient S sigma x)‖ ^ 2) = _
  rw [← finiteSquarefreeCurvature_eq_variance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [norm_mul, mul_pow, norm_finiteSquarefreeSourceCoefficient_sq,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow]
  norm_num
  ring

theorem inner_source_routeEFiniteSquarefreeGaugeNeutralTangent_eq_zero
    (S : Finset Nat.Primes) (sigma : ℝ) :
    inner ℂ (finiteSquarefreeSource S sigma)
      (routeEFiniteSquarefreeGaugeNeutralTangent S sigma) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [finiteSquarefreeSource, routeEFiniteSquarefreeGaugeNeutralTangent, PiLp.toLp_apply,
    Pi.star_apply]
  rw [show (∑ x : SquarefreeBitConfig S,
      (((-2 *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) *
          finiteSquarefreeSourceCoefficient S sigma x) *
        star (finiteSquarefreeSourceCoefficient S sigma x)) =
      ((-2 : ℝ) : ℂ) *
        ∑ x : SquarefreeBitConfig S,
          ((finiteSquarefreeBornWeight S sigma x *
            (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma) : ℝ) : ℂ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    have hnorm :
        finiteSquarefreeSourceCoefficient S sigma x *
            star (finiteSquarefreeSourceCoefficient S sigma x) =
          (finiteSquarefreeBornWeight S sigma x : ℂ) := by
      rw [← starRingEnd_apply]
      calc
        _ = ((‖finiteSquarefreeSourceCoefficient S sigma x‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (finiteSquarefreeSourceCoefficient S sigma x)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_finiteSquarefreeSourceCoefficient_sq]
    rw [mul_assoc, hnorm]
    push_cast
    ring]
  rw [← Complex.ofReal_sum]
  have hcentered : (∑ x : SquarefreeBitConfig S,
      finiteSquarefreeBornWeight S sigma x *
        (finiteSquarefreeHamiltonian S x - finiteSquarefreeCurrent S sigma)) = 0 := by
    exact sum_squarefreeBitWeight_mul_centeredEnergy S
      (squarefreePrimeOccupation sigma) squarefreePrimeEnergy
  rw [hcentered]
  simp

/-- Gauge-neutralized finite Fisher connection without singular division. -/
def routeEFiniteSquarefreeGaugeNeutralConnection (S : Finset Nat.Primes) (sigma : ℝ) :
    EuclideanSpace ℂ (SquarefreeBitConfig S) →L[ℂ]
      EuclideanSpace ℂ (SquarefreeBitConfig S) :=
  pointedFisherConnection
    (finiteSquarefreeSource S sigma) (routeEFiniteSquarefreeGaugeNeutralTangent S sigma)

theorem routeEFiniteSquarefreeGaugeNeutralConnection_energy
    (S : Finset Nat.Primes) (sigma : ℝ) :
    hsNormSq (routeEFiniteSquarefreeGaugeNeutralConnection S sigma) =
      4 * finiteSquarefreeCurvature S sigma := by
  rw [routeEFiniteSquarefreeGaugeNeutralConnection,
    hsNormSq_pointedFisherConnection_of_unit_of_orthogonal
      (finiteSquarefreeSource S sigma) (routeEFiniteSquarefreeGaugeNeutralTangent S sigma)
      (norm_finiteSquarefreeSource S sigma)
      (inner_source_routeEFiniteSquarefreeGaugeNeutralTangent_eq_zero S sigma),
    norm_routeEFiniteSquarefreeGaugeNeutralTangent_sq]

/-- **Gauge-neutral sharp contraction.**  Removing the Euler coordinate leaves the exact
division-free budget `sqrt V`, not `sqrt (2 V)`. -/
theorem norm_hsInner_routeEFiniteSquarefreeGaugeNeutralLowerBoundary_joinedReporter_le
    (S : Finset Nat.Primes) (sigma : ℝ)
    (e D : EuclideanSpace ℂ (SquarefreeBitConfig S) →L[ℂ]
      EuclideanSpace ℂ (SquarefreeBitConfig S))
    (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (hD : ‖D‖ ≤ 1) :
    ‖hsInner
        (cutoffLowerBoundary e (routeEFiniteSquarefreeGaugeNeutralConnection S sigma))
        (infiniteFisherOneCornerJoinedReporter e D
          (finiteSquarefreeSource S sigma))‖ ≤
      Real.sqrt (finiteSquarefreeCurvature S sigma) := by
  have hsq := norm_sq_hsInner_cutoffLowerBoundary_joinedReporter_le_quarter e D
    (finiteSquarefreeSource S sigma) (routeEFiniteSquarefreeGaugeNeutralTangent S sigma)
    he heAdj (norm_finiteSquarefreeSource S sigma)
    hD
  rw [routeEFiniteSquarefreeGaugeNeutralConnection]
  rw [norm_routeEFiniteSquarefreeGaugeNeutralTangent_sq] at hsq
  have hcurv := finiteSquarefreeCurvature_nonneg S sigma
  have hsqrt := Real.sq_sqrt hcurv
  nlinarith [Real.sqrt_nonneg (finiteSquarefreeCurvature S sigma),
    norm_nonneg
      (hsInner
        (cutoffLowerBoundary e (routeEFiniteSquarefreeGaugeNeutralConnection S sigma))
        (infiniteFisherOneCornerJoinedReporter e D
          (finiteSquarefreeSource S sigma)))]

end RHTower

namespace RHTower.RouteEFiniteColumnData

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Literal pushed-to-target likelihood ratio on a finite physical column family. -/
noncomputable def likelihoodRatio (d : RouteEFiniteColumnData ι) (i : ι) : ℝ :=
  d.pushedMass i / d.targetMass i

/-- Likelihood ratio with its physical target-mass mean removed. -/
noncomputable def centeredLikelihoodRatio
    (d : RouteEFiniteColumnData ι) (i : ι) : ℝ :=
  d.likelihoodRatio i - d.pushedTotal / d.targetTotal

/-- Target-weighted non-scalar likelihood-ratio energy. -/
noncomputable def centeredEnergy (d : RouteEFiniteColumnData ι) : ℝ :=
  ∑ i, d.targetMass i * d.centeredLikelihoodRatio i ^ 2

private theorem target_mul_likelihoodRatio
    (d : RouteEFiniteColumnData ι) (i : ι) :
    d.targetMass i * d.likelihoodRatio i = d.pushedMass i := by
  rw [likelihoodRatio, mul_div_cancel₀ _ (ne_of_gt (d.targetMass_pos i))]

private theorem targetTotal_pos [Nonempty ι]
    (d : RouteEFiniteColumnData ι) : 0 < d.targetTotal := by
  unfold targetTotal
  exact Finset.sum_pos (fun i _hi => d.targetMass_pos i) Finset.univ_nonempty

theorem centeredLikelihoodRatio_mean_zero
    (d : RouteEFiniteColumnData ι) :
    ∑ i, d.targetMass i * d.centeredLikelihoodRatio i = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      simp
  | inr hι =>
      letI := hι
      have hN : d.targetTotal ≠ 0 := ne_of_gt d.targetTotal_pos
      calc
        (∑ i, d.targetMass i * d.centeredLikelihoodRatio i) =
            ∑ i, (d.pushedMass i -
              (d.pushedTotal / d.targetTotal) * d.targetMass i) := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [centeredLikelihoodRatio]
                calc
                  d.targetMass i *
                      (d.likelihoodRatio i - d.pushedTotal / d.targetTotal) =
                      d.targetMass i * d.likelihoodRatio i -
                        (d.pushedTotal / d.targetTotal) * d.targetMass i := by ring
                  _ = _ := by rw [d.target_mul_likelihoodRatio]
        _ =
            (∑ i, d.pushedMass i) -
              (d.pushedTotal / d.targetTotal) * (∑ i, d.targetMass i) := by
                rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = 0 := by
          change d.pushedTotal -
            (d.pushedTotal / d.targetTotal) * d.targetTotal = 0
          field_simp [hN]
          ring

/-- Exact physical ANOVA: total Pearson energy is centered column energy plus scalar mass defect. -/
theorem chiSquare_eq_centeredEnergy_add_massDefect
    (d : RouteEFiniteColumnData ι) :
    d.chiSquare = d.centeredEnergy +
      (d.pushedTotal - d.targetTotal) ^ 2 / d.targetTotal := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      simp [RouteEFiniteColumnData.chiSquare, centeredEnergy,
        pushedTotal, targetTotal]
  | inr hι =>
      letI := hι
      have hN : d.targetTotal ≠ 0 := ne_of_gt d.targetTotal_pos
      have hpoint (i : ι) :
          (d.pushedMass i - d.targetMass i) ^ 2 / d.targetMass i =
            d.targetMass i * (d.likelihoodRatio i - 1) ^ 2 := by
        rw [likelihoodRatio]
        field_simp [ne_of_gt (d.targetMass_pos i)]
      have hcross := d.centeredLikelihoodRatio_mean_zero
      unfold RouteEFiniteColumnData.chiSquare centeredEnergy
      simp_rw [hpoint]
      calc
        (∑ i, d.targetMass i * (d.likelihoodRatio i - 1) ^ 2) =
            ∑ i, d.targetMass i *
              (d.centeredLikelihoodRatio i +
                (d.pushedTotal / d.targetTotal - 1)) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [centeredLikelihoodRatio]
                  ring
        _ = (∑ i, d.targetMass i * d.centeredLikelihoodRatio i ^ 2) +
            2 * (d.pushedTotal / d.targetTotal - 1) *
              (∑ i, d.targetMass i * d.centeredLikelihoodRatio i) +
            (d.pushedTotal / d.targetTotal - 1) ^ 2 *
              (∑ i, d.targetMass i) := by
                calc
                  _ = ∑ i,
                      (d.targetMass i * d.centeredLikelihoodRatio i ^ 2 +
                        2 * (d.pushedTotal / d.targetTotal - 1) *
                          (d.targetMass i * d.centeredLikelihoodRatio i) +
                        (d.pushedTotal / d.targetTotal - 1) ^ 2 *
                          d.targetMass i) := by
                            apply Finset.sum_congr rfl
                            intro i _hi
                            ring
                  _ = _ := by
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                    rw [Finset.mul_sum, Finset.mul_sum]
        _ = (∑ i, d.targetMass i * d.centeredLikelihoodRatio i ^ 2) +
            (d.pushedTotal - d.targetTotal) ^ 2 / d.targetTotal := by
              rw [hcross]
              change _ + 2 * _ * 0 + _ ^ 2 * d.targetTotal = _
              field_simp [hN]
              ring

end RHTower.RouteEFiniteColumnData
