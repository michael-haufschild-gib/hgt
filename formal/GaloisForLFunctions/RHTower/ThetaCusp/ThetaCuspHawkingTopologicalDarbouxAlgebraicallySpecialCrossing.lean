import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow

/-!
# Theta-paired algebraically-special Teukolsky crossings

For the exact `d = 4` topological gravitational Darboux pair, every theta
mediator QNM has one positive mass where its forward Starobinsky factor
vanishes.  Functional reflection produces a second crossing.  The crossings
coincide exactly on the critical line; otherwise their product is negative at
the positive midpoint mass.

The horizon incidence is oriented: the vector-to-scalar Darboux multiplier has
a zero and the reverse multiplier has a pole.  The associated AdS boundary
trace map kills a Robin line, while nonzero Dirichlet data survives.  Thus the
local horizon zero is not asserted to be a full Dirichlet Jost zero.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Positive mass where the theta-mediator forward Starobinsky factor vanishes. -/
def d4BMXiThetaMirrorAlgebraicallySpecialMass (n : ℕ) (q : XiZeroCopy) : ℝ :=
  let a := (q.1 : ℂ).re
  a * (1 - a) * (2 - a) * (3 - a) /
    (12 * (4 * n + 3 - a))

lemma d4BMXiThetaMirrorDampingRate_pos (n : ℕ) (q : XiZeroCopy) :
    0 < (4 : ℝ) * n + 3 - (q.1 : ℂ).re := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

lemma d4BMXiThetaMirrorAlgebraicallySpecialMass_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiThetaMirrorAlgebraicallySpecialMass n q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have h1 : 0 < 1 - (q.1 : ℂ).re := by linarith
  have h2 : 0 < 2 - (q.1 : ℂ).re := by linarith
  have h3 : 0 < 3 - (q.1 : ℂ).re := by linarith
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMass
  exact div_pos (mul_pos (mul_pos (mul_pos hstrip.1 h1) h2) h3)
    (mul_pos (by norm_num) (d4BMXiThetaMirrorDampingRate_pos n q))

lemma d4BMXiThetaMirrorAngularPolynomial_eq (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q *
        (d4BMXiReflectedRealPairMediatorAngularQ q + 2) =
      -(q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
        (2 - (q.1 : ℂ).re) * (3 - (q.1 : ℂ).re) := by
  unfold d4BMXiReflectedRealPairMediatorAngularQ
  ring

/-- The forward Starobinsky factor is affine in mass with positive slope. -/
lemma d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_slope_mul_sub_asMass
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorTopologicalStarobinskyWeight n M q =
      12 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
        (M - d4BMXiThetaMirrorAlgebraicallySpecialMass n q) := by
  rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight]
  rw [d4BMXiThetaMirrorAngularPolynomial_eq]
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMass
  have hne : (4 : ℝ) * n + 3 - (q.1 : ℂ).re ≠ 0 :=
    ne_of_gt (d4BMXiThetaMirrorDampingRate_pos n q)
  field_simp [hne]
  ring

theorem d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_zero_iff
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorTopologicalStarobinskyWeight n M q = 0 ↔
      M = d4BMXiThetaMirrorAlgebraicallySpecialMass n q := by
  rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_slope_mul_sub_asMass]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hrate | hmass
    · have hpos := d4BMXiThetaMirrorDampingRate_pos n q
      norm_num at hrate
      exact (ne_of_gt hpos hrate).elim
    · exact sub_eq_zero.mp hmass
  · intro h
    rw [h]
    ring

lemma d4BMXiThetaMirrorAlgebraicallySpecialMass_reflect_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorAlgebraicallySpecialMass n
        (xiZeroCopyReflectEquiv q) =
      (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
          ((q.1 : ℂ).re + 1) * ((q.1 : ℂ).re + 2) /
        (12 * ((4 : ℝ) * n + 2 + (q.1 : ℂ).re)) := by
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMass
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  ring

lemma d4BMXiThetaMirrorReflectedDampingRate_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < (4 : ℝ) * n + 2 + (q.1 : ℂ).re := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- Exact separation of the two reflected algebraically-special masses. -/
lemma d4BMXiThetaMirrorAlgebraicallySpecialMass_sub_reflect_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorAlgebraicallySpecialMass n q -
        d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q) =
      ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
          (1 - 2 * (q.1 : ℂ).re) *
          (16 * (n : ℝ) +
            (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re))) /
        (12 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
          ((4 : ℝ) * n + 2 + (q.1 : ℂ).re)) := by
  rw [d4BMXiThetaMirrorAlgebraicallySpecialMass_reflect_eq]
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMass
  have hq := ne_of_gt (d4BMXiThetaMirrorDampingRate_pos n q)
  have hr := ne_of_gt (d4BMXiThetaMirrorReflectedDampingRate_pos n q)
  field_simp [hq, hr]
  ring

/-- Reflected algebraically-special crossings synchronize exactly on the critical line. -/
theorem d4BMXiThetaMirrorAlgebraicallySpecialMass_eq_reflect_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorAlgebraicallySpecialMass n q =
        d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have h1 : 0 < 1 - (q.1 : ℂ).re := by linarith
  have htail :
      0 < 16 * (n : ℝ) +
        (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : 0 < 3 - (q.1 : ℂ).re := by linarith
    have h2 : 0 < 2 + (q.1 : ℂ).re := by linarith
    positivity
  constructor
  · intro h
    have hd : d4BMXiThetaMirrorAlgebraicallySpecialMass n q -
        d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q) = 0 := sub_eq_zero.mpr h
    rw [d4BMXiThetaMirrorAlgebraicallySpecialMass_sub_reflect_eq] at hd
    have hden : 12 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
        ((4 : ℝ) * n + 2 + (q.1 : ℂ).re) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (ne_of_gt (d4BMXiThetaMirrorDampingRate_pos n q)))
        (ne_of_gt (d4BMXiThetaMirrorReflectedDampingRate_pos n q))
    have hnum := (div_eq_zero_iff).mp hd
    rcases hnum with hnum | hbad
    · have hcoef :
          0 < (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
            (16 * (n : ℝ) +
              (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re)) := by
          exact mul_pos (mul_pos hstrip.1 h1) htail
      have hreassoc :
          (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
              (1 - 2 * (q.1 : ℂ).re) *
              (16 * (n : ℝ) +
                (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re)) =
            ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
              (16 * (n : ℝ) +
                (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re))) *
              (1 - 2 * (q.1 : ℂ).re) := by ring
      rw [hreassoc] at hnum
      rcases mul_eq_zero.mp hnum with hzero | hcenter
      · exact (ne_of_gt hcoef hzero).elim
      · linarith
    · exact (hden hbad).elim
  · intro hline
    rw [← sub_eq_zero,
      d4BMXiThetaMirrorAlgebraicallySpecialMass_sub_reflect_eq, hline]
    norm_num

/-- Product of forward Starobinsky factors for a theta-reflected pair. -/
def d4BMXiThetaMirrorStarobinskyCrossingProduct
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorTopologicalStarobinskyWeight n M q *
    d4BMXiThetaMirrorTopologicalStarobinskyWeight n M
      (xiZeroCopyReflectEquiv q)

def d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  (d4BMXiThetaMirrorAlgebraicallySpecialMass n q +
    d4BMXiThetaMirrorAlgebraicallySpecialMass n
      (xiZeroCopyReflectEquiv q)) / 2

lemma d4BMXiThetaMirrorStarobinskyCrossingProduct_factorization
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorStarobinskyCrossingProduct n M q =
      144 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
        ((4 : ℝ) * n + 2 + (q.1 : ℂ).re) *
        (M - d4BMXiThetaMirrorAlgebraicallySpecialMass n q) *
        (M - d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q)) := by
  unfold d4BMXiThetaMirrorStarobinskyCrossingProduct
  rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_slope_mul_sub_asMass,
    d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_slope_mul_sub_asMass]
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  ring

lemma d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorStarobinskyCrossingProduct n
        (d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q) q =
      -36 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
        ((4 : ℝ) * n + 2 + (q.1 : ℂ).re) *
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q -
          d4BMXiThetaMirrorAlgebraicallySpecialMass n
            (xiZeroCopyReflectEquiv q)) ^ (2 : ℕ) := by
  rw [d4BMXiThetaMirrorStarobinskyCrossingProduct_factorization]
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint
  ring

theorem d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q := by
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint
  have hq := d4BMXiThetaMirrorAlgebraicallySpecialMass_pos n q
  have hr := d4BMXiThetaMirrorAlgebraicallySpecialMass_pos n
    (xiZeroCopyReflectEquiv q)
  linarith

/-- Every tilted theta pair has a negative gravitational crossing chamber at positive mass. -/
theorem d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_neg_of_tilted
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorStarobinskyCrossingProduct n
        (d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q) q < 0 := by
  rw [d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_eq]
  have hm : d4BMXiThetaMirrorAlgebraicallySpecialMass n q ≠
      d4BMXiThetaMirrorAlgebraicallySpecialMass n
        (xiZeroCopyReflectEquiv q) := by
    intro h
    exact htilt
      ((d4BMXiThetaMirrorAlgebraicallySpecialMass_eq_reflect_iff n q).mp h)
  have hs : 0 < (d4BMXiThetaMirrorAlgebraicallySpecialMass n q -
      d4BMXiThetaMirrorAlgebraicallySpecialMass n
        (xiZeroCopyReflectEquiv q)) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hm)
  have hq := d4BMXiThetaMirrorDampingRate_pos n q
  have hr := d4BMXiThetaMirrorReflectedDampingRate_pos n q
  have hp : 0 < 36 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
      ((4 : ℝ) * n + 2 + (q.1 : ℂ).re) *
      (d4BMXiThetaMirrorAlgebraicallySpecialMass n q -
        d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q)) ^ (2 : ℕ) := by
    positivity
  nlinarith

/-- Global mass-chamber nonnegativity of one theta fibre is exactly critical-line placement. -/
theorem d4BMXiThetaMirrorStarobinskyCrossingProduct_nonnegative_all_mass_iff
    (n : ℕ) (q : XiZeroCopy) :
    (∀ M : ℝ, 0 ≤ d4BMXiThetaMirrorStarobinskyCrossingProduct n M q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    by_contra htilt
    have hnonneg := h (d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q)
    have hneg :=
      d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_neg_of_tilted
        n q htilt
    linarith
  · intro hline M
    rw [d4BMXiThetaMirrorStarobinskyCrossingProduct_factorization]
    have hm :=
      (d4BMXiThetaMirrorAlgebraicallySpecialMass_eq_reflect_iff n q).2 hline
    rw [hm]
    have hq := d4BMXiThetaMirrorDampingRate_pos n q
    have hr := d4BMXiThetaMirrorReflectedDampingRate_pos n q
    have hp : 0 ≤ 144 * ((4 : ℝ) * n + 3 - (q.1 : ℂ).re) *
        ((4 : ℝ) * n + 2 + (q.1 : ℂ).re) *
        (M - d4BMXiThetaMirrorAlgebraicallySpecialMass n
          (xiZeroCopyReflectEquiv q)) ^ (2 : ℕ) := by
      positivity
    convert hp using 1
    ring

/-- Opposite Darboux orientation of the topological Starobinsky factor. -/
def d4TopologicalDarbouxReverseStarobinskyConstant (M Q omega : ℂ) : ℂ :=
  Q * (Q + 2) - 12 * Complex.I * M * omega

/-- Exact finite-mass vector-to-scalar horizon Darboux multiplier. -/
def d4TopologicalDarbouxHorizonForwardSMatrix (M Q omega : ℂ) : ℂ :=
  d4TopologicalTeukolskyStarobinskyConstant M Q omega /
    d4TopologicalDarbouxReverseStarobinskyConstant M Q omega

lemma d4TopologicalDarbouxReverseStarobinskyConstant_eq_star
    (M Q omega : ℝ) :
    d4TopologicalDarbouxReverseStarobinskyConstant
        (M : ℂ) (Q : ℂ) (omega : ℂ) =
      star (d4TopologicalTeukolskyStarobinskyConstant
        (M : ℂ) (Q : ℂ) (omega : ℂ)) := by
  unfold d4TopologicalDarbouxReverseStarobinskyConstant
    d4TopologicalTeukolskyStarobinskyConstant
  apply Complex.ext <;> simp

/-- The physical real-frequency horizon multiplier is unitary. -/
theorem d4TopologicalDarbouxHorizonForwardSMatrix_norm_eq_one
    (M Q omega : ℝ)
    (hden : d4TopologicalDarbouxReverseStarobinskyConstant
      (M : ℂ) (Q : ℂ) (omega : ℂ) ≠ 0) :
    ‖d4TopologicalDarbouxHorizonForwardSMatrix
      (M : ℂ) (Q : ℂ) (omega : ℂ)‖ = 1 := by
  unfold d4TopologicalDarbouxHorizonForwardSMatrix
  rw [norm_div, d4TopologicalDarbouxReverseStarobinskyConstant_eq_star,
    norm_star]
  exact div_self (norm_ne_zero_iff.mpr (by
    intro hplus
    apply hden
    rw [d4TopologicalDarbouxReverseStarobinskyConstant_eq_star, hplus]
    simp))

lemma d4BMXiThetaMirrorForwardStarobinskyFactor_at_asMass
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalTeukolskyStarobinskyConstant
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) = 0 := by
  rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_complex]
  exact_mod_cast (by
    rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_slope_mul_sub_asMass]
    ring : d4BMXiThetaMirrorTopologicalStarobinskyWeight n
      (d4BMXiThetaMirrorAlgebraicallySpecialMass n q) q = 0)

/-- The analytically continued theta QNM has one simple forward horizon zero in mass. -/
theorem d4BMXiThetaMirrorForwardStarobinskyFactor_eq_zero_iff
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4TopologicalTeukolskyStarobinskyConstant (M : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) = 0 ↔
      M = d4BMXiThetaMirrorAlgebraicallySpecialMass n q := by
  rw [d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_complex]
  exact_mod_cast
    d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_zero_iff n M q

lemma d4BMXiThetaMirrorAngularPolynomial_neg (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q *
        (d4BMXiReflectedRealPairMediatorAngularQ q + 2) < 0 := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  exact mul_neg_of_neg_of_pos hQ.2 (by linarith [hQ.1])

lemma d4BMXiThetaMirrorReverseStarobinskyFactor_at_asMass
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalDarbouxReverseStarobinskyConstant
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) =
      2 * ((d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) *
        ((d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) + 2)) := by
  have hzero := d4BMXiThetaMirrorForwardStarobinskyFactor_at_asMass n q
  unfold d4TopologicalDarbouxReverseStarobinskyConstant
    d4TopologicalTeukolskyStarobinskyConstant at *
  linear_combination -hzero

lemma d4BMXiThetaMirrorReverseStarobinskyFactor_at_asMass_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalDarbouxReverseStarobinskyConstant
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) ≠ 0 := by
  rw [d4BMXiThetaMirrorReverseStarobinskyFactor_at_asMass]
  exact mul_ne_zero (by norm_num) (by
    exact_mod_cast ne_of_lt (d4BMXiThetaMirrorAngularPolynomial_neg q))

/-- Forward orientation has a zero; the reverse orientation has the corresponding pole. -/
theorem d4BMXiThetaMirrorHorizonForwardSMatrix_at_asMass
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalDarbouxHorizonForwardSMatrix
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) = 0 := by
  unfold d4TopologicalDarbouxHorizonForwardSMatrix
  rw [d4BMXiThetaMirrorForwardStarobinskyFactor_at_asMass]
  exact zero_div _

/-- Darboux action on boundary value and outward derivative. -/
def d4TopologicalDarbouxBoundaryTraceMap
    (W nu omega : ℂ) (b : ℂ × ℂ) : ℂ × ℂ :=
  (W * b.1 + b.2,
    (W ^ (2 : ℕ) - nu ^ (2 : ℕ) - omega ^ (2 : ℕ)) * b.1 + W * b.2)

lemma d4TopologicalDarbouxBoundaryTraceDeterminant
    (W nu omega : ℂ) :
    W * W - (W ^ (2 : ℕ) - nu ^ (2 : ℕ) - omega ^ (2 : ℕ)) = nu ^ (2 : ℕ) + omega ^ (2 : ℕ) := by
  ring

/-- Darboux sends Dirichlet trace to a transverse Robin trace. -/
lemma d4TopologicalDarbouxBoundaryTraceMap_dirichlet
    (W nu omega d : ℂ) :
    d4TopologicalDarbouxBoundaryTraceMap W nu omega (0, d) =
      (d, W * d) := by
  simp [d4TopologicalDarbouxBoundaryTraceMap]

lemma d4TopologicalDarbouxBoundaryTraceMap_dirichlet_ne_zero
    (W nu omega d : ℂ) (hd : d ≠ 0) :
    d4TopologicalDarbouxBoundaryTraceMap W nu omega (0, d) ≠ (0, 0) := by
  rw [d4TopologicalDarbouxBoundaryTraceMap_dirichlet]
  intro h
  have hfirst := congrArg Prod.fst h
  simp only at hfirst
  exact hd hfirst

/-- At Darboux degeneracy the boundary kernel is the Robin line `(1, -W)`. -/
lemma d4TopologicalDarbouxBoundaryTraceMap_robin
    (W nu omega : ℂ) (hdeg : nu ^ (2 : ℕ) + omega ^ (2 : ℕ) = 0) :
    d4TopologicalDarbouxBoundaryTraceMap W nu omega (1, -W) = (0, 0) := by
  apply Prod.ext <;> simp [d4TopologicalDarbouxBoundaryTraceMap]
  linear_combination -hdeg

def d4TopologicalDarbouxPhysicalAlgebraicConstant (M Q : ℂ) : ℂ :=
  Q * (Q + 2) / (12 * M)

lemma d4BMXiThetaMirrorPhysicalAlgebraicConstant_add_iomega_at_asMass
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalDarbouxPhysicalAlgebraicConstant
        (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) +
        Complex.I * d4BMXiReflectedRealPairFrequency n q = 0 := by
  have hzero := d4BMXiThetaMirrorForwardStarobinskyFactor_at_asMass n q
  have hM : (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (d4BMXiThetaMirrorAlgebraicallySpecialMass_pos n q)
  unfold d4TopologicalDarbouxPhysicalAlgebraicConstant
  unfold d4TopologicalTeukolskyStarobinskyConstant at hzero
  field_simp [hM]
  linear_combination hzero

lemma d4BMXiThetaMirrorPhysicalBoundaryDegeneracy_at_asMass
    (n : ℕ) (q : XiZeroCopy) :
    d4TopologicalDarbouxPhysicalAlgebraicConstant
          (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
          (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) ^ (2 : ℕ) +
        d4BMXiReflectedRealPairFrequency n q ^ (2 : ℕ) = 0 := by
  have h :=
    d4BMXiThetaMirrorPhysicalAlgebraicConstant_add_iomega_at_asMass n q
  have hnu : d4TopologicalDarbouxPhysicalAlgebraicConstant
      (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
      (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) =
        -Complex.I * d4BMXiReflectedRealPairFrequency n q := by
    linear_combination h
  rw [hnu, mul_pow, neg_sq, Complex.I_sq]
  ring

/-- The algebraically-special boundary kernel is Robin, independently of its finite boundary value `W`. -/
theorem d4BMXiThetaMirrorBoundaryTraceMap_robin_at_asMass
    (n : ℕ) (q : XiZeroCopy) (W : ℂ) :
    d4TopologicalDarbouxBoundaryTraceMap W
        (d4TopologicalDarbouxPhysicalAlgebraicConstant
          (d4BMXiThetaMirrorAlgebraicallySpecialMass n q : ℂ)
          (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ))
        (d4BMXiReflectedRealPairFrequency n q) (1, -W) = (0, 0) :=
  d4TopologicalDarbouxBoundaryTraceMap_robin W _ _
    (d4BMXiThetaMirrorPhysicalBoundaryDegeneracy_at_asMass n q)

end

end RHTower
