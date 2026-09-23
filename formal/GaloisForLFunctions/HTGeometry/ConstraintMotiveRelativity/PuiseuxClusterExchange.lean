import Mathlib

/-!
# Cluster-split Lorentz exchange of a coefficient coarea form

Activating one higher Puiseux coefficient between two coefficient clusters raises every cross
contact from `ℓ` to `k` and leaves every within-cluster contact fixed.  Since the contact pairing
enters the coefficient Cartan form subtractively, the form changes by exactly

`Q₁(x) - Q₀(x) = -2Δ X_U X_V = (Δ/2)((X_U - X_V)² - M²)`,  `Δ = k - ℓ`,

so `Δ/2` units of quadratic coupling move from the common rank port `M = X_U + X_V` into the
centered cluster contrast `X_U - X_V`, and on `M = 0` the change is the positive square
`2Δ X_U²`.  The rank port, and hence the determinant character `λ ↦ λ^{M(x)}`, is untouched.

The two-branch model `Q_j = 2x₁² + 2x₂² + 2(1-j)x₁x₂` exhibits the inertia jump explicitly, and the
projective score of a blockwise scalar twist is a Kullback–Leibler divergence whose Hessian is a
difference Laplacian; a common central twist leaves it identically zero.
-/

open Finset

namespace HTGeometry.ConstraintMotiveRelativity

/-! ## The cluster-split exchange -/

section ClusterSplit

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The contact pairing of a symmetric contact function against a dimension vector. -/
def contactPairing (contact : A → A → ℝ) (x : A → ℝ) : ℝ :=
  ∑ a, ∑ b, contact a b * (x a * x b)

/-- The coefficient Cartan/coarea form: a base term minus the contact pairing. -/
def cartanForm (base : (A → ℝ) → ℝ) (contact : A → A → ℝ) (x : A → ℝ) : ℝ :=
  base x - contactPairing contact x

/-- The cluster sums and the common rank port. -/
def clusterSum (U : Finset A) (x : A → ℝ) : ℝ := ∑ a ∈ U, x a

theorem clusterSum_add_compl (U : Finset A) (x : A → ℝ) :
    clusterSum U x + clusterSum Uᶜ x = ∑ a, x a := by
  rw [clusterSum, clusterSum, Finset.sum_add_sum_compl]

/-- **Theorem 2.1, the exact Lorentz exchange.**  Raising every cross contact by `Δ` and leaving
every within-cluster contact fixed changes the coefficient Cartan form by `-2Δ X_U X_V`. -/
theorem cartanForm_sub (base : (A → ℝ) → ℝ) (U : Finset A) (Δ : ℝ)
    (contact₀ contact₁ : A → A → ℝ)
    (hin : ∀ a b, (a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b)
    (hcross : ∀ a b, ¬(a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b + Δ)
    (x : A → ℝ) :
    cartanForm base contact₁ x - cartanForm base contact₀ x
      = -2 * Δ * (clusterSum U x * clusterSum Uᶜ x) := by
  classical
  set g : A → A → ℝ := fun a b => (if (a ∈ U ↔ b ∈ U) then (0:ℝ) else Δ) * (x a * x b) with hg
  have hdiff : contactPairing contact₁ x - contactPairing contact₀ x = ∑ a, ∑ b, g a b := by
    rw [contactPairing, contactPairing, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : (a ∈ U ↔ b ∈ U)
    · rw [hin a b h, hg]
      simp [h]
    · rw [hcross a b h, hg]
      simp [h]
      ring
  have hinnerU : ∀ a ∈ U, ∑ b, g a b = Δ * x a * clusterSum Uᶜ x := by
    intro a ha
    rw [← Finset.sum_add_sum_compl U fun b => g a b]
    have h1 : ∑ b ∈ U, g a b = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [hg]; simp [ha, hb]
    have h2 : ∑ b ∈ Uᶜ, g a b = Δ * x a * clusterSum Uᶜ x := by
      rw [clusterSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbU : b ∉ U := Finset.mem_compl.1 hb
      rw [hg]
      simp [ha, hbU]
      ring
    rw [h1, h2, zero_add]
  have hinnerV : ∀ a ∈ Uᶜ, ∑ b, g a b = Δ * x a * clusterSum U x := by
    intro a ha
    have haU : a ∉ U := Finset.mem_compl.1 ha
    rw [← Finset.sum_add_sum_compl U fun b => g a b]
    have h1 : ∑ b ∈ U, g a b = Δ * x a * clusterSum U x := by
      rw [clusterSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [hg]
      simp [haU, hb]
      ring
    have h2 : ∑ b ∈ Uᶜ, g a b = 0 :=
      Finset.sum_eq_zero fun b hb => by
        have hbU : b ∉ U := Finset.mem_compl.1 hb
        rw [hg]; simp [haU, hbU]
    rw [h1, h2, add_zero]
  have hsplit : ∑ a, ∑ b, g a b = 2 * Δ * (clusterSum U x * clusterSum Uᶜ x) := by
    rw [← Finset.sum_add_sum_compl U fun a => ∑ b, g a b]
    rw [Finset.sum_congr rfl hinnerU, Finset.sum_congr rfl hinnerV]
    have e1 : ∑ a ∈ U, Δ * x a * clusterSum Uᶜ x
        = Δ * clusterSum U x * clusterSum Uᶜ x := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rfl
    have e2 : ∑ a ∈ Uᶜ, Δ * x a * clusterSum U x
        = Δ * clusterSum Uᶜ x * clusterSum U x := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rfl
    rw [e1, e2]
    ring
  rw [cartanForm, cartanForm]
  have hrew : base x - contactPairing contact₁ x - (base x - contactPairing contact₀ x)
      = -(contactPairing contact₁ x - contactPairing contact₀ x) := by ring
  rw [hrew, hdiff, hsplit]
  ring

/-- The Lorentzian form of the exchange: `Δ/2` units move from the rank port into the centered
cluster contrast. -/
theorem cartanForm_sub_lorentz (base : (A → ℝ) → ℝ) (U : Finset A) (Δ : ℝ)
    (contact₀ contact₁ : A → A → ℝ)
    (hin : ∀ a b, (a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b)
    (hcross : ∀ a b, ¬(a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b + Δ)
    (x : A → ℝ) :
    cartanForm base contact₁ x - cartanForm base contact₀ x
      = Δ / 2 * ((clusterSum U x - clusterSum Uᶜ x) ^ (2 : ℕ) - (∑ a, x a) ^ (2 : ℕ)) := by
  rw [cartanForm_sub base U Δ contact₀ contact₁ hin hcross x,
    ← clusterSum_add_compl U x]
  ring

/-- **On the kernel of the rank port the exchange is a positive square.** -/
theorem cartanForm_sub_on_ker (base : (A → ℝ) → ℝ) (U : Finset A) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (contact₀ contact₁ : A → A → ℝ)
    (hin : ∀ a b, (a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b)
    (hcross : ∀ a b, ¬(a ∈ U ↔ b ∈ U) → contact₁ a b = contact₀ a b + Δ)
    (x : A → ℝ) (hx : ∑ a, x a = 0) :
    cartanForm base contact₁ x - cartanForm base contact₀ x
      = 2 * Δ * clusterSum U x ^ (2 : ℕ) ∧
      0 ≤ cartanForm base contact₁ x - cartanForm base contact₀ x := by
  have hV : clusterSum Uᶜ x = -clusterSum U x := by
    have h := clusterSum_add_compl U x
    rw [hx] at h
    linarith
  constructor
  · rw [cartanForm_sub base U Δ contact₀ contact₁ hin hcross x, hV]
    ring
  · rw [cartanForm_sub base U Δ contact₀ contact₁ hin hcross x, hV]
    nlinarith [sq_nonneg (clusterSum U x), hΔ]

end ClusterSplit

/-! ## The sharp two-branch wall -/

section TwoBranch

/-- The two-branch coefficient form `(10)` at common contact `j`. -/
def branchForm (j x₁ x₂ : ℝ) : ℝ := 2 * x₁ ^ (2 : ℕ) + 2 * x₂ ^ (2 : ℕ) + 2 * (1 - j) * (x₁ * x₂)

/-- Its diagonalization in the contrast and port coordinates. -/
theorem branchForm_diag (j x₁ x₂ : ℝ) :
    branchForm j x₁ x₂ = (1 + j) / 2 * (x₁ - x₂) ^ (2 : ℕ) + (3 - j) / 2 * (x₁ + x₂) ^ (2 : ℕ) := by
  rw [branchForm]; ring

/-- The port gap `(11)`. -/
noncomputable def branchGap (j : ℝ) : ℝ := (3 - j) / 2

/-- The coefficient determinant `(11)`. -/
def branchDet (j : ℝ) : ℝ := (1 + j) * (3 - j)

theorem branchDet_eq (j : ℝ) : branchDet j = 4 - (1 - j) ^ (2 : ℕ) := by
  rw [branchDet]; ring

/-- Below the wall the form is positive definite. -/
theorem branchForm_pos {j : ℝ} (h1 : -1 < j) (h2 : j < 3) (x₁ x₂ : ℝ)
    (hne : ¬(x₁ = 0 ∧ x₂ = 0)) : 0 < branchForm j x₁ x₂ := by
  rw [branchForm_diag]
  rcases eq_or_ne x₁ x₂ with h | h
  · have hx : x₁ + x₂ ≠ 0 := by
      intro hsum
      exact hne ⟨by linarith [h, hsum], by linarith [h, hsum]⟩
    have hsq : 0 < (x₁ + x₂) ^ (2 : ℕ) := by positivity
    have : (0:ℝ) < (3 - j) / 2 := by linarith
    nlinarith [sq_nonneg (x₁ - x₂), h1]
  · have hsq : 0 < (x₁ - x₂) ^ (2 : ℕ) := by
      have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 h
      positivity
    nlinarith [sq_nonneg (x₁ + x₂), h2]

/-- At the wall the form is positive semidefinite with a one-dimensional radical. -/
theorem branchForm_at_three (x₁ x₂ : ℝ) :
    branchForm 3 x₁ x₂ = 2 * (x₁ - x₂) ^ (2 : ℕ) := by
  rw [branchForm_diag]; ring

theorem branchForm_three_null (t : ℝ) : branchForm 3 t t = 0 := by
  rw [branchForm_at_three]; ring

/-- Above the wall the form has a negative direction. -/
theorem branchForm_neg_above {j : ℝ} (h : 3 < j) : branchForm j 1 1 < 0 := by
  rw [branchForm_diag]
  norm_num
  linarith

/-- **The two-branch endpoints `(13)`–`(14)`.** -/
theorem branch_endpoints :
    branchGap 1 = 1 ∧ branchDet 1 = 4 ∧ branchGap 4 = -(1 / 2) ∧ branchDet 4 = -5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [branchGap, branchDet] <;> norm_num

end TwoBranch

/-! ## The projective score and the common central twist -/

section ProjectiveScore

variable {ι : Type*} [Fintype ι]

/-- The partition function `(27)`. -/
noncomputable def partitionZ (q a : ι → ℝ) : ℝ := ∑ i, q i * Real.exp (a i)

/-- The Gibbs weights `(27)`. -/
noncomputable def gibbsWeight (q a : ι → ℝ) (i : ι) : ℝ := q i * Real.exp (a i) / partitionZ q a

/-- The projective score `(27)`. -/
noncomputable def projectiveScore (q a : ι → ℝ) : ℝ :=
  Real.log (partitionZ q a) - ∑ i, q i * a i

theorem partitionZ_pos {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (a : ι → ℝ) :
    0 < partitionZ q a := by
  classical
  rw [partitionZ]
  obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, 0 < q j := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, q i ≤ 0 :=
      Finset.sum_nonpos fun i _ => hcon i (Finset.mem_univ i)
    rw [hq1] at this
    linarith
  refine Finset.sum_pos'
    (fun i _ => mul_nonneg (hq i) (Real.exp_pos _).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩

/-- **The projective score is a Kullback–Leibler divergence, hence nonnegative** `(28)`. -/
theorem projectiveScore_nonneg {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (a : ι → ℝ) : 0 ≤ projectiveScore q a := by
  have hZ : 0 < partitionZ q a := partitionZ_pos hq hq1 a
  have hjensen : Real.exp (∑ i, q i * a i) ≤ partitionZ q a := by
    have hconv := convexOn_exp.map_sum_le (t := (Finset.univ : Finset ι)) (w := q) (p := a)
      (fun i _ => hq i) (by simpa using hq1) (fun i _ => Set.mem_univ _)
    simpa [partitionZ, smul_eq_mul] using hconv
  have hlog : ∑ i, q i * a i ≤ Real.log (partitionZ q a) := by
    have := Real.log_le_log (Real.exp_pos _) hjensen
    rwa [Real.log_exp] at this
  rw [projectiveScore]
  linarith

/-- **The Hessian of the score is a difference Laplacian** `(29)`. -/
theorem gibbs_hessian_identity (p v : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * v i ^ (2 : ℕ) - (∑ i, p i * v i) ^ (2 : ℕ)
      = 1 / 2 * ∑ i, ∑ j, p i * p j * (v i - v j) ^ (2 : ℕ) := by
  set S0 : ℝ := ∑ j, p j with hS0
  set S1 : ℝ := ∑ j, p j * v j with hS1
  set S2 : ℝ := ∑ j, p j * v j ^ (2 : ℕ) with hS2
  have h1 : ∀ i, ∑ j, p i * p j * (v i - v j) ^ (2 : ℕ)
      = p i * v i ^ (2 : ℕ) * S0 - p i * v i * (2 * S1) + p i * S2 := by
    intro i
    rw [hS0, hS1, hS2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, p i * p j * (v i - v j) ^ (2 : ℕ) = S2 * S0 - S1 * (2 * S1) + S0 * S2 := by
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [h2, hp]
  ring

/-- **A common central twist has zero relative score and unchanged Gibbs weights.** -/
theorem projectiveScore_const {q : ι → ℝ} (hq1 : ∑ i, q i = 1) (c : ℝ) :
    projectiveScore q (fun _ => c) = 0 ∧ ∀ i, gibbsWeight q (fun _ => c) i = q i := by
  have hZ : partitionZ q (fun _ => c) = Real.exp c := by
    rw [partitionZ, ← Finset.sum_mul, hq1, one_mul]
  constructor
  · rw [projectiveScore, hZ, Real.log_exp, ← Finset.sum_mul, hq1, one_mul, sub_self]
  · intro i
    rw [gibbsWeight, hZ]
    field_simp

end ProjectiveScore

/-! ## Smooth phase versus constructible law event -/

section PhaseJump

open Complex

/-- The polar model `r e^{iθ}` of a nonvanishing coefficient path. -/
noncomputable def polarCurve (r θ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (r t : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))

theorem hasDerivAt_polarCurve {r θ : ℝ → ℝ} {r' θ' t : ℝ}
    (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (polarCurve r θ)
      ((r' : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))
        + (r t : ℂ) * (Complex.exp (Complex.I * (θ t : ℂ)) * (Complex.I * (θ' : ℂ)))) t := by
  have hrc : HasDerivAt (fun t : ℝ => (r t : ℂ)) (r' : ℂ) t := hr.ofReal_comp
  have hθc : HasDerivAt (fun t : ℝ => (θ t : ℂ)) (θ' : ℂ) t := hθ.ofReal_comp
  exact hrc.mul ((hθc.const_mul Complex.I).cexp)

/-- **`(17)`.**  Along a differentiable nonvanishing path the logarithmic derivative separates the
two smooth receivers: its imaginary part is the phase rate and its real part is the logarithmic
rate of the modulus. -/
theorem logDeriv_polarCurve {r θ : ℝ → ℝ} {r' θ' t : ℝ}
    (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) (hrne : r t ≠ 0) :
    ∃ w : ℂ, HasDerivAt (polarCurve r θ) w t ∧ polarCurve r θ t ≠ 0 ∧
      w / polarCurve r θ t = (r' / r t : ℝ) + Complex.I * (θ' : ℂ) := by
  refine ⟨_, hasDerivAt_polarCurve hr hθ, ?_, ?_⟩
  · have h1 : (r t : ℂ) ≠ 0 := by exact_mod_cast hrne
    exact mul_ne_zero h1 (Complex.exp_ne_zero _)
  · have h1 : (r t : ℂ) ≠ 0 := by exact_mod_cast hrne
    have h2 : Complex.exp (Complex.I * (θ t : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    rw [polarCurve, div_eq_iff (mul_ne_zero h1 h2)]
    push_cast
    field_simp
    try ring

/-- The pure phase rotation: constant modulus, unit phase rate. -/
noncomputable def rotPath (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

/-- The spiral: the same unit phase rate, but a growing modulus. -/
noncomputable def spiralPath (t : ℝ) : ℂ := Complex.exp ((1 + Complex.I) * (t : ℂ))

theorem hasDerivAt_rotPath : HasDerivAt rotPath Complex.I 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0:ℝ)).ofReal_comp
  have h2 := (h1.const_mul Complex.I).cexp
  norm_num at h2
  exact h2

theorem hasDerivAt_spiralPath : HasDerivAt spiralPath (1 + Complex.I) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0:ℝ)).ofReal_comp
  have h2 := (h1.const_mul (1 + Complex.I)).cexp
  norm_num at h2
  exact h2

theorem norm_rotPath (t : ℝ) : ‖rotPath t‖ = 1 := by
  rw [rotPath, Complex.norm_exp]; simp

theorem norm_spiralPath (t : ℝ) : ‖spiralPath t‖ = Real.exp t := by
  rw [spiralPath, Complex.norm_exp]; simp

/-- **No universal phase-to-modulus response law.**  Two paths with the same phase rate at the
origin have different modulus rates there, so no function of the phase rate `Im (u̇/u)` can
predict the response of any rotation-invariant receiver. -/
theorem no_universal_phase_response :
    ¬ ∃ Φ : ℝ → ℝ, ∀ (u : ℝ → ℂ) (w : ℂ) (g' : ℝ), HasDerivAt u w 0 → u 0 ≠ 0 →
      HasDerivAt (fun t => ‖u t‖) g' 0 → g' = Φ ((w / u 0).im) := by
  rintro ⟨Φ, hΦ⟩
  have hrot0 : rotPath 0 = 1 := by simp [rotPath]
  have hsp0 : spiralPath 0 = 1 := by simp [spiralPath]
  have h1 : (0 : ℝ) = Φ 1 := by
    have hg : HasDerivAt (fun t => ‖rotPath t‖) 0 0 := by
      simpa [norm_rotPath] using (hasDerivAt_const (0:ℝ) (1:ℝ))
    have := hΦ rotPath Complex.I 0 hasDerivAt_rotPath (by rw [hrot0]; exact one_ne_zero) hg
    simpa [hrot0] using this
  have h2 : (1 : ℝ) = Φ 1 := by
    have hg : HasDerivAt (fun t => ‖spiralPath t‖) 1 0 := by
      simpa [norm_spiralPath] using (Real.hasDerivAt_exp 0)
    have := hΦ spiralPath (1 + Complex.I) 1 hasDerivAt_spiralPath
      (by rw [hsp0]; exact one_ne_zero) hg
    simpa [hsp0] using this
  rw [← h2] at h1
  norm_num at h1

end PhaseJump

/-! ## The general rank-one crossing form -/

section RankOneCrossing

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one operator `x ↦ ⟪r, x⟫ r`. -/
noncomputable def rankOneCL (r : E) : E →L[ℝ] E := (innerSL ℝ r).smulRight r

@[simp] theorem rankOneCL_apply (r x : E) : rankOneCL r x = ⟪r, x⟫ • r := rfl

/-- The rank-one crossing family `(18)`. -/
noncomputable def crossQ (P : E →L[ℝ] E) (lam : ℝ) (r : E) : E →L[ℝ] E :=
  P - lam • rankOneCL r

theorem crossQ_apply (P : E →L[ℝ] E) (lam : ℝ) (r x : E) :
    crossQ P lam r x = P x - (lam * ⟪r, x⟫) • r := by
  simp [crossQ, smul_smul]

/-- On the candidate kernel vector `u = P⁻¹ r` the family is a multiple of `r`. -/
theorem crossQ_apply_inv (P Pinv : E →L[ℝ] E) (hPP : ∀ x, P (Pinv x) = x) (lam : ℝ) (r : E) :
    crossQ P lam r (Pinv r) = (1 - lam * ⟪r, Pinv r⟫) • r := by
  rw [crossQ_apply, hPP, sub_smul, one_smul]

/-- **`Ω₀ = 0` puts `u₀ = P⁻¹ r` in the kernel.** -/
theorem crossQ_inv_eq_zero (P Pinv : E →L[ℝ] E) (hPP : ∀ x, P (Pinv x) = x) (lam : ℝ) (r : E)
    (hc : ⟪r, Pinv r⟫ ≠ 0) (hΩ : (⟪r, Pinv r⟫)⁻¹ - lam = 0) :
    crossQ P lam r (Pinv r) = 0 := by
  rw [crossQ_apply_inv P Pinv hPP lam r]
  have hlam : lam = (⟪r, Pinv r⟫)⁻¹ := by linarith
  rw [hlam, inv_mul_cancel₀ hc, sub_self, zero_smul]

/-- **The kernel is contained in the line `ℝ u₀`.** -/
theorem crossQ_ker_le (P Pinv : E →L[ℝ] E) (hPinv : ∀ x, Pinv (P x) = x) (lam : ℝ) (r x : E)
    (hx : crossQ P lam r x = 0) : x = (lam * ⟪r, x⟫) • Pinv r := by
  have hP : P x = (lam * ⟪r, x⟫) • r := by
    have h := crossQ_apply P lam r x
    rw [hx] at h
    exact sub_eq_zero.1 h.symm
  have h2 := congrArg Pinv hP
  rwa [hPinv, map_smul] at h2

/-- **`(21)`.**  The value of the family on `u₀` is `c - λ c²`. -/
theorem crossQ_quadratic (P Pinv : E →L[ℝ] E) (hPP : ∀ x, P (Pinv x) = x) (lam : ℝ) (r : E) :
    ⟪Pinv r, crossQ P lam r (Pinv r)⟫ = ⟪r, Pinv r⟫ - lam * ⟪r, Pinv r⟫ ^ (2 : ℕ) := by
  rw [crossQ_apply_inv P Pinv hPP lam r, real_inner_smul_right, real_inner_comm]
  ring

/-- The same value read through the port gap `Ω = c⁻¹ - λ`. -/
theorem crossQ_quadratic_gap (P Pinv : E →L[ℝ] E) (hPP : ∀ x, P (Pinv x) = x) (lam : ℝ) (r : E)
    (hc : ⟪r, Pinv r⟫ ≠ 0) :
    ⟪Pinv r, crossQ P lam r (Pinv r)⟫
      = ⟪r, Pinv r⟫ ^ (2 : ℕ) * ((⟪r, Pinv r⟫)⁻¹ - lam) := by
  rw [crossQ_quadratic P Pinv hPP lam r]
  field_simp
  try ring

/-- **`(20)`, the crossing form.**  At a zero of the port gap the second-order terms drop out and
the derivative of the family, evaluated on the kernel line, is `c₀² Ω̇₀`. -/
theorem crossing_form (Q : ℝ → E →L[ℝ] E) (Q' : E →L[ℝ] E) (u : ℝ → E) (u' : E)
    (c Ω : ℝ → ℝ) (c' Ω' : ℝ)
    (hQ : HasDerivAt Q Q' 0) (hu : HasDerivAt u u' 0)
    (hc : HasDerivAt c c' 0) (hΩ : HasDerivAt Ω Ω' 0)
    (hsymm : ∀ x y, ⟪Q 0 x, y⟫ = ⟪x, Q 0 y⟫)
    (hval : ∀ t, ⟪u t, Q t (u t)⟫ = c t ^ (2 : ℕ) * Ω t)
    (hker : Q 0 (u 0) = 0) (hΩ0 : Ω 0 = 0) :
    ⟪u 0, Q' (u 0)⟫ = c 0 ^ (2 : ℕ) * Ω' := by
  have hL : HasDerivAt (fun t => ⟪u t, Q t (u t)⟫)
      (⟪u 0, Q' (u 0) + Q 0 u'⟫ + ⟪u', Q 0 (u 0)⟫) 0 := hu.inner ℝ (hQ.clm_apply hu)
  have hL' : HasDerivAt (fun t => c t ^ (2 : ℕ) * Ω t)
      (⟪u 0, Q' (u 0) + Q 0 u'⟫ + ⟪u', Q 0 (u 0)⟫) 0 := by
    refine hL.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun t => (hval t).symm
  have hR : HasDerivAt (fun t => c t ^ (2 : ℕ) * Ω t)
      ((2 : ℕ) * c 0 ^ (2 - 1) * c' * Ω 0 + c 0 ^ (2 : ℕ) * Ω') 0 := (hc.pow 2).mul hΩ
  have huniq := hL'.unique hR
  have hz1 : ⟪u', Q 0 (u 0)⟫ = (0 : ℝ) := by rw [hker, inner_zero_right]
  have hz2 : ⟪u 0, Q 0 u'⟫ = (0 : ℝ) := by
    rw [← hsymm, hker, inner_zero_left]
  rw [inner_add_right, hz1, hz2, hΩ0] at huniq
  simpa using huniq

/-- The local spectral-flow orientation: at a simple crossing the value of the family on the fixed
kernel line changes sign through zero with the sign of `Ω̇₀`. -/
theorem crossing_sign (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0)
    (hpos : 0 < f') : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, 0 < f t / t := by
  have hslope : Filter.Tendsto (slope f 0) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds f') :=
    hasDerivAt_iff_tendsto_slope.1 hf
  have := hslope.eventually (eventually_gt_nhds hpos)
  refine this.mono fun t ht => ?_
  rw [slope_def_field, hf0, sub_zero, sub_zero, div_eq_inv_mul] at ht
  rwa [div_eq_inv_mul]

end RankOneCrossing

/-! ## The common central twist -/

section CentralTwist

variable {A : Type*} [Fintype A]

/-- **A common central shift of every contact only rescales the rank port.** -/
theorem cartanForm_central_shift (base : (A → ℝ) → ℝ) (δ : ℝ) (contact₀ contact₁ : A → A → ℝ)
    (hall : ∀ a b, contact₁ a b = contact₀ a b + δ) (x : A → ℝ) :
    cartanForm base contact₁ x - cartanForm base contact₀ x = -δ * (∑ a, x a) ^ (2 : ℕ) := by
  have hdiff : contactPairing contact₁ x - contactPairing contact₀ x = δ * (∑ a, x a) ^ (2 : ℕ) := by
    rw [contactPairing, contactPairing, ← Finset.sum_sub_distrib]
    have h1 : ∀ a, (∑ b, contact₁ a b * (x a * x b)) - ∑ b, contact₀ a b * (x a * x b)
        = δ * x a * ∑ b, x b := by
      intro a
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hall a b]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [cartanForm, cartanForm]
  have hrew : base x - contactPairing contact₁ x - (base x - contactPairing contact₀ x)
      = -(contactPairing contact₁ x - contactPairing contact₀ x) := by ring
  rw [hrew, hdiff]
  ring

/-- **`(24)`.**  On the kernel of the rank port a common central twist changes nothing, so it can
create no crossing there. -/
theorem central_twist_no_crossing (base : (A → ℝ) → ℝ) (δ : ℝ) (contact₀ contact₁ : A → A → ℝ)
    (hall : ∀ a b, contact₁ a b = contact₀ a b + δ) (x : A → ℝ) (hx : ∑ a, x a = 0) :
    cartanForm base contact₁ x = cartanForm base contact₀ x := by
  have := cartanForm_central_shift base δ contact₀ contact₁ hall x
  rw [hx] at this
  simp at this
  linarith

/-- The determinant holonomy `(25)` of a common central twist. -/
noncomputable def detHolonomy (δ : ℝ) (M : ℕ) : ℝ := δ ^ M

/-- The holonomy is not constant in the central parameter as soon as the rank port is nonzero. -/
theorem detHolonomy_nonconstant {M : ℕ} (hM : M ≠ 0) :
    detHolonomy 1 M ≠ detHolonomy 2 M := by
  rw [detHolonomy, detHolonomy, one_pow]
  have : (1 : ℝ) < 2 ^ M := one_lt_pow₀ (by norm_num) hM
  linarith

/-- **The separation.**  On the rank-port kernel the cluster split moves the coefficient Cartan
form by a positive square while the common central twist moves it not at all, yet the central
twist does move the determinant holonomy. -/
theorem central_vs_cluster (base : (Fin 2 → ℝ) → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (contact₀ contactCl contactCe : Fin 2 → Fin 2 → ℝ)
    (hin : ∀ a b, (a ∈ ({0} : Finset (Fin 2)) ↔ b ∈ ({0} : Finset (Fin 2))) →
      contactCl a b = contact₀ a b)
    (hcross : ∀ a b, ¬(a ∈ ({0} : Finset (Fin 2)) ↔ b ∈ ({0} : Finset (Fin 2))) →
      contactCl a b = contact₀ a b + Δ)
    (δ : ℝ) (hall : ∀ a b, contactCe a b = contact₀ a b + δ) {M : ℕ} (hM : M ≠ 0) :
    cartanForm base contactCl ![1, -1] - cartanForm base contact₀ ![1, -1] = 2 * Δ ∧
    cartanForm base contactCe ![1, -1] = cartanForm base contact₀ ![1, -1] ∧
    detHolonomy 1 M ≠ detHolonomy 2 M := by
  have hx : ∑ a, (![1, -1] : Fin 2 → ℝ) a = 0 := by
    simp [Fin.sum_univ_two]
  refine ⟨?_, central_twist_no_crossing base δ contact₀ contactCe hall _ hx,
    detHolonomy_nonconstant hM⟩
  have h := (cartanForm_sub_on_ker base ({0} : Finset (Fin 2)) hΔ.le contact₀ contactCl hin hcross
    ![1, -1] hx).1
  rw [h, clusterSum]
  simp

end CentralTwist

end HTGeometry.ConstraintMotiveRelativity
