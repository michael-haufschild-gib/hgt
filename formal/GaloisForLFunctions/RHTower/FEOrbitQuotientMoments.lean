import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniSource

/-!
# FE orbit quotient half-trace moments

Passing from the even completed function `Ξ(w)` to the quotient `Φ(z)` with `Φ(w²) = Ξ(w)` removes
the functional-equation sign duplication: the orbit `[w] = {w, −w}` carries total multiplicity `2m`
while the quotient carries `m`.  Any route through the quotient must restore the factor `2` before
comparing with the bridge reciprocal moments.

* `analyticOrderAt_xiSquaredSeamEntireQuotient` — the quotient divisor of the corpus's entire
  square-root quotient `xiSquaredSeamEntireQuotient` has multiplicity `m`, **not** `2m`, at the
  squared coordinate of a nonzero Xi zero;
* `analyticOrderAt_XiC_neg` — the two members of an orbit carry the same multiplicity, so the orbit
  total is `2m`;
* `orbitLog`, `exp_orbitLog`, `hasSum_orbitLog` — the canonical logarithm of the orbit product and
  its Taylor coefficients `ℓ_k = −(1/k) Σ m_j z_j^{−k}`;
* `traceMoment_eq` — **the dictionary** `T_k = −2k(−1)^k ℓ_k`.

The logarithm is *defined* as `Σ m_j log(1 − z/z_j)` and proved to exponentiate to the orbit
product (`exp_orbitLog`), which is exactly the branch the card's expansion uses and avoids any
branch-cut bookkeeping.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower.FEOrbitQuotient

open RHTower

variable {ι : Type*}

/-! ## The orbit quotient divisor -/

/-- Squaring has a simple zero of the shifted coordinate away from the origin. -/
theorem analyticOrderAt_sq_sub {w₀ : ℂ} (hw : w₀ ≠ 0) :
    analyticOrderAt (fun w : ℂ => w ^ (2 : ℕ) - w₀ ^ (2 : ℕ)) w₀ = 1 := by
  have han : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ) - w₀ ^ (2 : ℕ)) w₀ := by
    exact (analyticAt_id.pow 2).sub analyticAt_const
  have hval : (fun w : ℂ => w ^ (2 : ℕ) - w₀ ^ (2 : ℕ)) w₀ = 0 := by simp
  have hderiv : deriv (fun w : ℂ => w ^ (2 : ℕ) - w₀ ^ (2 : ℕ)) w₀ = 2 * w₀ := by
    have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) - w₀ ^ (2 : ℕ)) (2 * w₀ ^ (2 - 1) * 1) w₀ := by
      have hb : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ)) (2 * w₀ ^ (2 - 1) * 1) w₀ :=
        (hasDerivAt_id w₀).pow 2
      simpa using hb.sub_const (w₀ ^ (2 : ℕ))
    rw [h.deriv]
    norm_num
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hval ?_
  rw [hderiv]
  exact mul_ne_zero two_ne_zero hw

/-- **The quotient divisor carries `m`, not `2m`.**  The entire square-root quotient of the centered
Xi function has, at the squared coordinate of a nonzero zero, exactly the multiplicity of that
zero — one copy per functional-equation orbit. -/
theorem analyticOrderAt_xiSquaredSeamEntireQuotient {w₀ : ℂ} (hw : w₀ ≠ 0) :
    analyticOrderAt xiSquaredSeamEntireQuotient (w₀ ^ (2 : ℕ)) = analyticOrderAt XiC w₀ := by
  have hQ : AnalyticAt ℂ xiSquaredSeamEntireQuotient ((fun w : ℂ => w ^ (2 : ℕ)) w₀) :=
    (differentiable_xiSquaredSeamEntireQuotient.differentiableOn.analyticOnNhd isOpen_univ) _
      (Set.mem_univ _)
  have hg : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ)) w₀ := analyticAt_id.pow 2
  have hcomp := hQ.analyticOrderAt_comp hg
  have hfun : (xiSquaredSeamEntireQuotient ∘ fun w : ℂ => w ^ (2 : ℕ)) = XiC := by
    funext w
    exact xiSquaredSeamEntireQuotient_sq w
  rw [hfun, analyticOrderAt_sq_sub hw, mul_one] at hcomp
  exact hcomp.symm

/-- The two members of a functional-equation orbit carry the same multiplicity, so the orbit total
is `2m` while the quotient carries `m`. -/
theorem analyticOrderAt_XiC_neg (w₀ : ℂ) :
    analyticOrderAt XiC (-w₀) = analyticOrderAt XiC w₀ := by
  have hcomp : (XiC ∘ fun w : ℂ => -w) = XiC := by
    funext w
    exact XiC_even w
  have hQ : AnalyticAt ℂ XiC ((fun w : ℂ => -w) w₀) :=
    (XiC_differentiable.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have hg : AnalyticAt ℂ (fun w : ℂ => -w) w₀ := analyticAt_id.neg
  have hord := hQ.analyticOrderAt_comp hg
  rw [hcomp] at hord
  have hone : analyticOrderAt (fun w : ℂ => -w - -w₀) w₀ = 1 := by
    have han : AnalyticAt ℂ (fun w : ℂ => -w - -w₀) w₀ := (analyticAt_id.neg).sub analyticAt_const
    refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) ?_
    have h : HasDerivAt (fun w : ℂ => -w - -w₀) (-1) w₀ := by
      simpa using ((hasDerivAt_id w₀).neg).sub_const (-w₀)
    rw [h.deriv]
    norm_num
  rw [hone, mul_one] at hord
  exact hord.symm

/-! ## Half-trace moments of the quotient divisor -/

/-- The normalized orbit product `∏ (1 − z/z_j)^{m_j}` in the quotient coordinate. -/
def orbitProduct (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) (z : ℂ) : ℂ :=
  ∏ j ∈ s, (1 - z / zr j) ^ (m j)

/-- Its canonical logarithm, normalized to vanish at the origin. -/
def orbitLog (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) (z : ℂ) : ℂ :=
  ∑ j ∈ s, (m j : ℂ) * Complex.log (1 - z / zr j)

theorem orbitLog_zero (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) :
    orbitLog m zr s 0 = 0 := by
  rw [orbitLog]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp

/-- `orbitLog` really is a logarithm of the orbit product. -/
theorem exp_orbitLog (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) {z : ℂ}
    (hz : ∀ j ∈ s, 1 - z / zr j ≠ 0) :
    Complex.exp (orbitLog m zr s z) = orbitProduct m zr s z := by
  rw [orbitLog, Complex.exp_sum, orbitProduct]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Complex.exp_nat_mul, Complex.exp_log (hz j hj)]

/-- The half-trace log coefficients `ℓ_k` of the quotient divisor. -/
def ell (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) (k : ℕ) : ℂ :=
  -(1 / (k : ℂ)) * ∑ j ∈ s, (m j : ℂ) * (zr j)⁻¹ ^ k

/-- The bridge reciprocal trace moments: each orbit carries the doubled weight `2m`. -/
def traceMoment (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) (k : ℕ) : ℂ :=
  ∑ j ∈ s, 2 * (m j : ℂ) * (-(zr j)⁻¹) ^ k

/-- **The log coefficients are the half-trace moments.** -/
theorem hasSum_orbitLog (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) {z : ℂ}
    (hz : ∀ j ∈ s, ‖z / zr j‖ < 1) :
    HasSum (fun k : ℕ => ell m zr s k * z ^ k) (orbitLog m zr s z) := by
  classical
  have hterm : ∀ j ∈ s, HasSum
      (fun k : ℕ => (m j : ℂ) * ((-1) ^ (k + 1) * (-(z / zr j)) ^ k / k))
      ((m j : ℂ) * Complex.log (1 - z / zr j)) := by
    intro j hj
    have hnorm : ‖-(z / zr j)‖ < 1 := by
      rw [norm_neg]
      exact hz j hj
    have h := (Complex.hasSum_taylorSeries_log hnorm).mul_left ((m j : ℂ))
    have hrw : (1 : ℂ) + -(z / zr j) = 1 - z / zr j := by ring
    rw [hrw] at h
    exact h
  have hsum := hasSum_sum hterm
  rw [← orbitLog] at hsum
  have hfun : (fun k : ℕ => ∑ j ∈ s, (m j : ℂ) * ((-1) ^ (k + 1) * (-(z / zr j)) ^ k / k))
      = fun k : ℕ => ell m zr s k * z ^ k := by
    funext k
    have hsign : ((-1 : ℂ) ^ (k + 1)) * ((-1 : ℂ) ^ k) = -1 := by
      rw [← pow_add, show k + 1 + k = 2 * k + 1 by omega, pow_succ, pow_mul]
      norm_num
    have hrhs : ell m zr s k * z ^ k
        = ∑ j ∈ s, (-(1 / (k : ℂ)) * ((m j : ℂ) * (zr j)⁻¹ ^ k) * z ^ k) := by
      rw [ell, Finset.mul_sum, Finset.sum_mul]
    rw [hrhs]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hneg : (-(z / zr j)) ^ k = (-1 : ℂ) ^ k * (z ^ k * (zr j)⁻¹ ^ k) := by
      rw [neg_pow, div_pow, div_eq_mul_inv, ← inv_pow]
    rw [hneg]
    have hcore : ((-1 : ℂ) ^ (k + 1) * ((-1 : ℂ) ^ k * (z ^ k * (zr j)⁻¹ ^ k)) / (k : ℂ))
        = -(1 / (k : ℂ)) * (z ^ k * (zr j)⁻¹ ^ k) := by
      calc ((-1 : ℂ) ^ (k + 1) * ((-1 : ℂ) ^ k * (z ^ k * (zr j)⁻¹ ^ k)) / (k : ℂ))
          = (((-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ k) * (z ^ k * (zr j)⁻¹ ^ k)) / (k : ℂ) := by ring
        _ = (-1 * (z ^ k * (zr j)⁻¹ ^ k)) / (k : ℂ) := by rw [hsign]
        _ = -(1 / (k : ℂ)) * (z ^ k * (zr j)⁻¹ ^ k) := by ring
    rw [hcore]
    ring
  rw [hfun] at hsum
  exact hsum

/-- **The half-trace dictionary.**  The bridge reciprocal trace moments are the quotient log
coefficients multiplied by the functional-equation trace factor. -/
theorem traceMoment_eq (m : ι → ℕ) (zr : ι → ℂ) (s : Finset ι) {k : ℕ} (hk : k ≠ 0) :
    traceMoment m zr s k = -2 * (k : ℂ) * (-1) ^ k * ell m zr s k := by
  have hkC : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [traceMoment, ell]
  have hcollapse : (-2 : ℂ) * (k : ℂ) * (-1) ^ k
        * (-(1 / (k : ℂ)) * ∑ j ∈ s, (m j : ℂ) * (zr j)⁻¹ ^ k)
      = (2 * (-1) ^ k) * ∑ j ∈ s, (m j : ℂ) * (zr j)⁻¹ ^ k := by
    field_simp
  rw [hcollapse, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [neg_pow]
  ring

end RHTower.FEOrbitQuotient
