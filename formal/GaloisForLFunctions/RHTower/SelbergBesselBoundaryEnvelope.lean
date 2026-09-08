import GaloisForLFunctions.RHTower.SelbergBesselBoundarySlope

/-!
# Inverse-frequency correction of the actual critical cusp boundary response

The source Bessel Riccati equation and positivity give
`exp(t) < Q(t) < exp(t) + 1/2`, and then
`0 < exp(t) + 1/2 - Q(t) < exp(-t)/8`.
Both upper bounds follow from explicit integrating factors and contradiction
with reciprocal positivity on a sufficiently long future interval.
No Bessel asymptotic expansion or numerical bound is assumed.

For actual frequency `k=exp(a)` and height `Y=exp(T)`, the outgoing coefficient
therefore satisfies `0 < k-B(k,Y) < 1/(8*k*Y^2)`.
This identifies an inverse-frequency boundary correction; no assertion about
the compact core or the global congruence Maass spectrum is made.
-/

open Set
namespace GaloisForLFunctions.RHTower.SelbergBesselEnvelope
open SelbergBesselSlope
noncomputable section

/-- Excess of the actual dimensionless Bessel slope over its argument. -/
def excess (t : ℝ) : ℝ := logSlope t - Real.exp t

/-- The source integral comparison gives strict positive excess. -/
theorem excess_pos (t : ℝ) : 0 < excess t :=
  sub_pos.mpr (argument_lt_slope (Real.exp_pos t))

/-- Exact Riccati equation for the positive excess. -/
theorem excess_hasDerivAt (t : ℝ) :
    HasDerivAt excess (2 * Real.exp t * excess t + excess t ^ 2 - Real.exp t) t := by
  convert (logSlope_hasDerivAt t).sub (Real.hasDerivAt_exp t) using 1 <;> try rfl
  unfold excess
  ring

/-- Integrating factor for comparison with the half-unit excess. -/
def barrier (t : ℝ) : ℝ := Real.exp (-2 * Real.exp t) * (excess t - 1 / 2)

/-- Its derivative is a strictly positive weighted square. -/
theorem barrier_hasDerivAt (t : ℝ) :
    HasDerivAt barrier (Real.exp (-2 * Real.exp t) * excess t ^ 2) t := by
  have he := ((Real.hasDerivAt_exp t).const_mul (-2)).exp
  convert he.mul ((excess_hasDerivAt t).sub_const (1 / 2)) using 1 <;> try rfl
  ring

/-- The half-unit comparison factor is strictly increasing. -/
theorem barrier_strictMono : StrictMono barrier := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(barrier_hasDerivAt t).deriv]
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos (excess_pos t))

/-- Global positivity rules out touching or crossing the half-unit upper barrier. -/
theorem excess_lt_half (T : ℝ) : excess T < 1 / 2 := by
  by_contra hn
  have hT : 1 / 2 ≤ excess T := le_of_not_gt hn
  have hnonneg : 0 ≤ barrier T :=
    mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hT)
  have hpersist : ∀ t ∈ Ici T, 1 / 2 ≤ excess t := by
    intro t ht
    have h := hnonneg.trans (barrier_strictMono.monotone ht)
    unfold barrier at h
    have hz := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h
    linarith
  let F : ℝ → ℝ := fun t => 1 / excess t + t
  have hF (t : ℝ) : HasDerivAt F
      (-(2 * Real.exp t * excess t + excess t ^ 2 - Real.exp t) / excess t ^ 2 + 1) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).div (excess_hasDerivAt t)
      (excess_pos t).ne').add (hasDerivAt_id t) using 1 <;>
      try rfl
    ring
  have hanti : AntitoneOn F (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici T)
    · intro t _
      exact (hF t).continuousAt.continuousWithinAt
    · intro t _
      exact (hF t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t).deriv]
      have htT : t ∈ Ici T := interior_subset ht
      have hv := hpersist t htT
      have hnum : excess t ^ 2 ≤ 2 * Real.exp t * excess t + excess t ^ 2 - Real.exp t := by
        nlinarith [Real.exp_pos t]
      have hdiv : 1 ≤ (2 * Real.exp t * excess t + excess t ^ 2 - Real.exp t) / excess t ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos (excess_pos t)), one_mul]
        exact hnum
      rw [neg_div]
      linarith
  let t := T + 1 / excess T + 1
  have ht : T ≤ t := by dsimp only [t]; linarith [one_div_pos.mpr (excess_pos T)]
  have hcompare := hanti (le_refl T) ht ht
  have hpos := one_div_pos.mpr (excess_pos t)
  dsimp only [F, t] at hcompare hpos
  linarith

/-- The actual dimensionless slope lies strictly between its argument and argument plus one half. -/
theorem logSlope_bounds (t : ℝ) : Real.exp t < logSlope t ∧ logSlope t < Real.exp t + 1 / 2 := by
  have hl := excess_pos t
  have hu := excess_lt_half t
  unfold excess at hl hu
  constructor <;> linarith

/-- The actual outgoing response lies between the elementary Robin coefficient and the frequency. -/
theorem outgoing_bounds (a T : ℝ) :
    Real.exp a - 1 / (2 * Real.exp T) < outgoing a T ∧ outgoing a T < Real.exp a := by
  obtain ⟨hl, hu⟩ := logSlope_bounds (a + T)
  rw [outgoing_eq]
  have he := Real.exp_add a T
  constructor
  · apply (lt_div_iff₀ (Real.exp_pos T)).mpr
    have hc : (Real.exp a - 1 / (2 * Real.exp T)) * Real.exp T = Real.exp a * Real.exp T - 1 / 2 := by
      field_simp
    rw [hc]
    linarith
  · apply (div_lt_iff₀ (Real.exp_pos T)).mpr
    linarith

/-- Positive deficit from the first upper envelope. -/
def deficit (t : ℝ) : ℝ := 1 / 2 - excess t

/-- The source deficit lies strictly between zero and one half. -/
theorem deficit_bounds (t : ℝ) : 0 < deficit t ∧ deficit t < 1 / 2 := by
  have hl := excess_pos t
  have hu := excess_lt_half t
  unfold deficit
  constructor <;> linarith

/-- Exact differential equation for the positive deficit. -/
theorem deficit_hasDerivAt (t : ℝ) :
    HasDerivAt deficit (2 * Real.exp t * deficit t - excess t ^ 2) t := by
  convert (excess_hasDerivAt t).const_sub (1 / 2) using 1 <;> try rfl
  unfold deficit
  ring

/-- Integrating factor for the inverse-argument deficit bound. -/
def refinedBarrier (t : ℝ) : ℝ :=
  Real.exp (-2 * Real.exp t) * (deficit t - Real.exp (-t) / 8)

/-- The refined comparison derivative retains its explicit positive source. -/
theorem refinedBarrier_hasDerivAt (t : ℝ) :
    HasDerivAt refinedBarrier
      (Real.exp (-2 * Real.exp t) * (1 / 4 - excess t ^ 2 + Real.exp (-t) / 8)) t := by
  have he := ((Real.hasDerivAt_exp t).const_mul (-2)).exp
  have hr := ((hasDerivAt_id t).neg.exp).div_const 8
  convert he.mul ((deficit_hasDerivAt t).sub hr) using 1 <;> try rfl
  simp only [Pi.neg_apply, Pi.sub_apply, id_eq]
  rw [Real.exp_neg]
  field_simp
  ring

/-- The inverse-argument comparison factor is strictly increasing. -/
theorem refinedBarrier_strictMono : StrictMono refinedBarrier := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(refinedBarrier_hasDerivAt t).deriv]
  apply mul_pos (Real.exp_pos _)
  nlinarith [excess_pos t, excess_lt_half t, Real.exp_pos (-t)]

/-- The deficit is strictly less than one eighth of the inverse argument. -/
theorem deficit_lt_inverse_argument (T : ℝ) : deficit T < Real.exp (-T) / 8 := by
  by_contra hn
  have hT : Real.exp (-T) / 8 ≤ deficit T := le_of_not_gt hn
  have hnonneg : 0 ≤ refinedBarrier T :=
    mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hT)
  have hpersist : ∀ t ∈ Ici T, Real.exp (-t) / 8 ≤ deficit t := by
    intro t ht
    have h := hnonneg.trans (refinedBarrier_strictMono.monotone ht)
    unfold refinedBarrier at h
    have hz := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h
    linarith
  let F : ℝ → ℝ := fun t => 1 / deficit t + t
  have hF (t : ℝ) : HasDerivAt F
      (-(2 * Real.exp t * deficit t - excess t ^ 2) / deficit t ^ 2 + 1) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).div (deficit_hasDerivAt t)
      (deficit_bounds t).1.ne').add (hasDerivAt_id t) using 1 <;> try rfl
    ring
  have hanti : AntitoneOn F (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici T)
    · intro t _
      exact (hF t).continuousAt.continuousWithinAt
    · intro t _
      exact (hF t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t).deriv]
      have htT : t ∈ Ici T := interior_subset ht
      have hv := hpersist t htT
      have he : 2 * Real.exp t * (Real.exp (-t) / 8) = 1 / 4 := by
        rw [Real.exp_neg]
        field_simp
        ring
      have hvp := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * Real.exp t)
      rw [he] at hvp
      have hnum : deficit t ^ 2 ≤ 2 * Real.exp t * deficit t - excess t ^ 2 := by
        have hd : deficit t + excess t = 1 / 2 := by unfold deficit; ring
        obtain ⟨hp, hu⟩ := deficit_bounds t
        nlinarith
      have hdiv : 1 ≤ (2 * Real.exp t * deficit t - excess t ^ 2) / deficit t ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos (deficit_bounds t).1), one_mul]
        exact hnum
      rw [neg_div]
      linarith
  let t := T + 1 / deficit T + 1
  have ht : T ≤ t := by dsimp only [t]; linarith [one_div_pos.mpr (deficit_bounds T).1]
  have hcompare := hanti (le_refl T) ht ht
  have hpos := one_div_pos.mpr (deficit_bounds t).1
  dsimp only [F, t] at hcompare hpos
  linarith

/-- Difference between the Fourier frequency and the actual outgoing Bessel response. -/
def correction (a T : ℝ) : ℝ := Real.exp a - outgoing a T

/-- The physical boundary correction is the dimensionless deficit divided by height. -/
theorem correction_eq (a T : ℝ) : correction a T = deficit (a + T) / Real.exp T := by
  rw [correction, outgoing_eq]
  unfold deficit excess
  rw [Real.exp_add]
  field_simp
  ring

/-- The actual correction is positive and bounded by the inverse frequency times inverse squared height. -/
theorem correction_inverse_frequency_bound (a T : ℝ) :
    0 < correction a T ∧ correction a T < 1 / (8 * Real.exp a * Real.exp T ^ 2) := by
  rw [correction_eq]
  refine ⟨div_pos (deficit_bounds _).1 (Real.exp_pos _), ?_⟩
  calc
    _ < (Real.exp (-(a + T)) / 8) / Real.exp T :=
      div_lt_div_of_pos_right (deficit_lt_inverse_argument _) (Real.exp_pos _)
    _ = _ := by
      rw [Real.exp_neg, Real.exp_add]
      field_simp

/-- Refined two-sided envelope for the actual critical cusp boundary coefficient. -/
theorem outgoing_refined_bounds (a T : ℝ) :
    Real.exp a - 1 / (8 * Real.exp a * Real.exp T ^ 2) < outgoing a T ∧
      outgoing a T < Real.exp a := by
  have h := correction_inverse_frequency_bound a T
  unfold correction at h
  constructor <;> linarith [h.1, h.2]

end
end GaloisForLFunctions.RHTower.SelbergBesselEnvelope
