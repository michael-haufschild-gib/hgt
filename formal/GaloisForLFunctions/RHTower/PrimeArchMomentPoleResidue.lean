import GaloisForLFunctions.RHTower.PrimeArchBernsteinMobiusPullbackSource
import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase

/-!
# The prime--archimedean moment pole--residue pinch law

The endpoint-normalized ordinary moment germ

```
M_R(v) = ∑_n (normalizedPrimeArchMoment n / R^n) v^n
```

is, near the origin, the reciprocal-coordinate resolvent `∑_q c_q/(1 - u_q v)` of the
multiplicity-indexed Xi divisor, with `c_q = xiZeroCopyReciprocalSquare q` and `u_q = c_q / R`.

Grouping the copies by their common normalized coordinate `u` gives `C_u = R u m_u` with `m_u` the
exact fibre multiplicity, so the poles are the simple points `p_u = 1/u` and the residue is exactly
`-R m_u`: no cancellation between multiplicity copies or reflection partners is possible.

The reflected Bernstein amplitude of the pole is `B(p) = (1+|p-1|)/|p|`, and triangle equality
gives `B(p) = 1` exactly on the ray `[1, ∞)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The endpoint-normalized moment sequence `m_n = normalizedPrimeArchMoment(n)/R^n`. -/
def endpointMoment : ℕ → ℝ :=
  radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment

theorem xiEndpointNormalizedReciprocalSquare_mul (q : XiZeroCopy) :
    (primeArchEndpointHausdorffRadius : ℂ) * xiEndpointNormalizedReciprocalSquare q
      = xiZeroCopyReciprocalSquare q := by
  have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 := by
    exact_mod_cast primeArchEndpointHausdorffRadius_pos.ne'
  rw [xiEndpointNormalizedReciprocalSquare]
  field_simp

/-- **(11)** The endpoint-normalized moments are the reciprocal-coordinate power sums. -/
theorem endpointMoment_eq_tsum (n : ℕ) :
    ((endpointMoment n : ℝ) : ℂ)
      = ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q
          * (xiEndpointNormalizedReciprocalSquare q) ^ n := by
  have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 := by
    exact_mod_cast primeArchEndpointHausdorffRadius_pos.ne'
  have hterm : ∀ q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q * (xiEndpointNormalizedReciprocalSquare q) ^ n
        = xiZeroCopyReciprocalSquare q ^ (n + 1) / (primeArchEndpointHausdorffRadius : ℂ) ^ n := by
    intro q
    rw [xiEndpointNormalizedReciprocalSquare, div_pow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_div_const, tsum_xiZeroCopyReciprocalSquare_pow n]
  rw [endpointMoment, radiusNormalizedMoment]
  push_cast
  rw [← primeArchSourceMoment_eq_xiCentralReciprocalMoment n]
  rw [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm]

/-- The reciprocal-coordinate resolvent `∑_q c_q / (1 - u_q v)`. -/
def endpointResolvent (v : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q
    / (1 - xiEndpointNormalizedReciprocalSquare q * v)

theorem exists_endpointNormalized_norm_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ M := by
  obtain ⟨M, hM1, hM⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hR := primeArchEndpointHausdorffRadius_pos
  refine ⟨M / primeArchEndpointHausdorffRadius, by positivity, fun q => ?_⟩
  rw [xiEndpointNormalizedReciprocalSquare, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hM q) hR

/-- **(2)** Near the origin the endpoint moment germ is the reciprocal-coordinate resolvent. -/
theorem bernsteinMomentGerm_endpoint_eq_resolvent {v : ℂ} {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ M)
    (hv : M * ‖v‖ < 1) :
    bernsteinMomentGerm endpointMoment v = endpointResolvent v := by
  set F : XiZeroCopy × ℕ → ℂ := fun p =>
    xiZeroCopyReciprocalSquare p.1 * (xiEndpointNormalizedReciprocalSquare p.1 * v) ^ p.2 with hF
  have hMv0 : 0 ≤ M * ‖v‖ := by positivity
  have hqv : ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q * v‖ < 1 := by
    intro q
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hM q) (norm_nonneg v)) hv
  have hsum : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : XiZeroCopy × ℕ =>
      ‖xiZeroCopyReciprocalSquare p.1‖ * (M * ‖v‖) ^ p.2) ?_ ?_
    · exact Summable.mul_of_nonneg summable_xiZeroCopyReciprocalSquare.norm
        (summable_geometric_of_lt_one hMv0 hv) (fun _ => norm_nonneg _)
        (fun n => by positivity)
    · intro p
      rw [hF]
      simp only [norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM p.1) (norm_nonneg v)
  have hrow : ∀ q : XiZeroCopy, ∑' n : ℕ, F (q, n)
      = xiZeroCopyReciprocalSquare q
        / (1 - xiEndpointNormalizedReciprocalSquare q * v) := by
    intro q
    rw [hF]
    simp only
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hqv q), div_eq_mul_inv]
  have hcol : ∀ n : ℕ, ∑' q : XiZeroCopy, F (q, n)
      = ((endpointMoment n : ℝ) : ℂ) * v ^ n := by
    intro n
    rw [hF]
    simp only
    rw [endpointMoment_eq_tsum n, ← tsum_mul_right]
    exact tsum_congr fun q => by rw [mul_pow]; ring
  have h1 : ∑' p : XiZeroCopy × ℕ, F p = endpointResolvent v := by
    rw [hsum.tsum_prod, endpointResolvent]
    exact tsum_congr hrow
  have hswap : Summable (fun p : ℕ × XiZeroCopy => F (p.2, p.1)) := by
    refine (((Equiv.prodComm ℕ XiZeroCopy).summable_iff (f := F)).mpr hsum).congr fun p => rfl
  have h2 : ∑' p : XiZeroCopy × ℕ, F p = bernsteinMomentGerm endpointMoment v := by
    have heq : ∑' p : XiZeroCopy × ℕ, F p = ∑' p : ℕ × XiZeroCopy, F (p.2, p.1) :=
      ((Equiv.prodComm ℕ XiZeroCopy).tsum_eq F).symm
    rw [heq, hswap.tsum_prod, bernsteinMomentGerm]
    exact tsum_congr hcol
  rw [← h2, h1]

end

end RHTower
