/-
# What the Riesz projection does to eigenvectors and generalized eigenvectors

Evaluating the contour integral on a vector reduces the Riesz projection to explicit scalar circle
integrals.  On a generalized eigenvector for an eigenvalue inside the contour the resolvent is a
finite Laurent polynomial, and only its simple pole contributes, so the projection acts as the
identity.  On an eigenvector for an eigenvalue outside the closed disc the resolvent is a single
holomorphic Cauchy kernel, so the projection annihilates it.

Main results:
* `circleIntegral_apply` — an operator-valued circle integral evaluates termwise.
* `resolvent_apply_of_pow_eq_zero` — the finite Laurent expansion of the resolvent on a
  generalized eigenvector.
* `rieszProjection_apply_eq_self` — **generalized eigenvectors inside the contour are fixed**.
* `rieszProjection_apply_eq_zero_of_eigenvector`,
  `rieszProjection_apply_eq_zero_of_pow_eq_zero` — **(generalized) eigenvectors outside the closed
  disc are annihilated**.
-/
import GaloisForLFunctions.HTGeometry.RieszProjection

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- An operator-valued circle integral may be evaluated at a vector inside the integral. -/
theorem circleIntegral_apply {f : ℂ → (H →L[ℂ] H)} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (x : H) :
    (∮ lam in C(c, r), f lam) x = ∮ lam in C(c, r), f lam x := by
  have key := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.apply ℂ H x) hf.out
  simp only [ContinuousLinearMap.apply_apply] at key
  simp only [circleIntegral]
  rw [← key]
  exact intervalIntegral.integral_congr fun θ _ => by
    simp only [smul_apply]

/-- The evaluation of the Riesz projection at a vector. -/
theorem rieszProjection_apply (a : H →L[ℂ] H) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) (x : H) :
    rieszProjection a c r x
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(c, r), resolvent a lam x := by
  rw [rieszProjection, smul_apply,
    circleIntegral_apply (circleIntegrable_resolvent hr h) x]

omit [CompleteSpace H] in
/-- The telescoping identity behind the finite Laurent expansion of the resolvent. -/
theorem sub_smul_pow_sum {N : H →L[ℂ] H} {d : ℂ} (hd : d ≠ 0) {n : ℕ} {x : H}
    (hx : (N ^ n) x = 0) :
    (d • (1 : H →L[ℂ] H) - N) (∑ k ∈ Finset.range n, (d⁻¹ ^ (k + 1)) • ((N ^ k) x)) = x := by
  have hstep : ∀ k : ℕ,
      (d • (1 : H →L[ℂ] H) - N) ((d⁻¹ ^ (k + 1)) • ((N ^ k) x))
        = d⁻¹ ^ k • ((N ^ k) x) - d⁻¹ ^ (k + 1) • ((N ^ (k + 1)) x) := by
    intro k
    have hcoef : d * d⁻¹ ^ (k + 1) = d⁻¹ ^ k := by
      rw [pow_succ, mul_comm (d⁻¹ ^ k) d⁻¹, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    have hpow : (N ^ (k + 1)) x = N ((N ^ k) x) := by
      rw [pow_succ']
      rfl
    simp only [sub_apply, smul_apply,
      one_apply_eq_self, ContinuousLinearMap.map_smul, smul_smul, hcoef, hpow]
  rw [map_sum, Finset.sum_congr rfl (fun k _ => hstep k),
    Finset.sum_range_sub' (fun k => d⁻¹ ^ k • ((N ^ k) x)) n]
  simp [hx]

omit [CompleteSpace H] in
/-- **The finite Laurent expansion of the resolvent on a generalized eigenvector.** -/
theorem resolvent_apply_of_pow_eq_zero {T : H →L[ℂ] H} {lam0 lam : ℂ} {n : ℕ} {x : H}
    (hlam : lam ∈ resolventSet ℂ T) (hne : lam ≠ lam0)
    (hx : ((T - lam0 • (1 : H →L[ℂ] H)) ^ n) x = 0) :
    resolvent T lam x
      = ∑ k ∈ Finset.range n,
          ((lam - lam0)⁻¹ ^ (k + 1)) • (((T - lam0 • (1 : H →L[ℂ] H)) ^ k) x) := by
  set N : H →L[ℂ] H := T - lam0 • (1 : H →L[ℂ] H) with hNdef
  set y : H := ∑ k ∈ Finset.range n, ((lam - lam0)⁻¹ ^ (k + 1)) • ((N ^ k) x) with hydef
  have hop : algebraMap ℂ (H →L[ℂ] H) lam - T = (lam - lam0) • (1 : H →L[ℂ] H) - N := by
    rw [hNdef, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  have h1 : (algebraMap ℂ (H →L[ℂ] H) lam - T) y = x := by
    rw [hop]
    exact sub_smul_pow_sum (sub_ne_zero.mpr hne) hx
  have h2 : resolvent T lam ((algebraMap ℂ (H →L[ℂ] H) lam - T) y) = y := by
    have hres : resolvent T lam * (algebraMap ℂ (H →L[ℂ] H) lam - T) = 1 :=
      resolvent_mul_sub hlam
    calc resolvent T lam ((algebraMap ℂ (H →L[ℂ] H) lam - T) y)
        = (resolvent T lam * (algebraMap ℂ (H →L[ℂ] H) lam - T)) y := rfl
      _ = y := by rw [hres]; rfl
  rw [← h1, h2]

/-- The scalar circle integrals of the finite Laurent expansion. -/
theorem circleIntegral_inv_pow (c lam0 : ℂ) (r : ℝ) (hlam0 : lam0 ∈ ball c r) (k : ℕ) :
    (∮ lam in C(c, r), ((lam - lam0)⁻¹ ^ (k + 1)))
      = if k = 0 then 2 * Real.pi * Complex.I else 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using circleIntegral.integral_sub_inv_of_mem_ball hlam0
  · rw [if_neg hk.ne']
    have hrw : ∀ lam : ℂ, (lam - lam0)⁻¹ ^ (k + 1) = (lam - lam0) ^ (-((k + 1 : ℕ) : ℤ)) := by
      intro lam
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [hrw]
    exact circleIntegral.integral_sub_zpow_of_ne (by omega) c lam0 r

/-- **A generalized eigenvector for an eigenvalue inside the contour is fixed by the Riesz
projection.** -/
theorem rieszProjection_apply_eq_self {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {lam0 : ℂ} {n : ℕ} {x : H}
    (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T) (hlam0 : lam0 ∈ ball c r)
    (hx : ((T - lam0 • (1 : H →L[ℂ] H)) ^ n) x = 0) :
    rieszProjection T c r x = x := by
  set N : H →L[ℂ] H := T - lam0 • (1 : H →L[ℂ] H) with hNdef
  have hsphne : ∀ lam ∈ sphere c r, lam ≠ lam0 := by
    intro lam hlam hcon
    have h1 : dist lam c = r := hlam
    have h2 : dist lam0 c < r := hlam0
    rw [hcon] at h1
    linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
  have hci : ∀ k : ℕ, CircleIntegrable
      (fun lam => ((lam - lam0)⁻¹ ^ (k + 1)) • ((N ^ k) x)) c r := by
    intro k
    refine ContinuousOn.circleIntegrable hr (ContinuousOn.smul ?_ continuousOn_const)
    exact ContinuousOn.pow (ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn)
      (fun lam hlam => sub_ne_zero.mpr (hsphne lam hlam))) _
  have hexp : (∮ lam in C(c, r), resolvent T lam x)
      = ∑ k ∈ Finset.range n, (if k = 0 then 2 * Real.pi * Complex.I else 0) • ((N ^ k) x) := by
    rw [circleIntegral.integral_congr hr (fun lam hlam =>
      resolvent_apply_of_pow_eq_zero (h lam hlam) (hsphne lam hlam) hx)]
    rw [circleIntegral.integral_fun_sum (fun k _ => hci k)]
    exact Finset.sum_congr rfl fun k _ => by
      rw [circleIntegral.integral_smul_const, circleIntegral_inv_pow c lam0 r hlam0 k]
  have hsum : (∑ k ∈ Finset.range n,
      (if k = 0 then 2 * Real.pi * Complex.I else 0) • ((N ^ k) x))
      = (2 * Real.pi * Complex.I : ℂ) • x := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk0
      simp [hk0]
    · intro hcon
      exact absurd (Finset.mem_range.mpr hn) hcon
  rw [rieszProjection_apply T hr h x, hexp, hsum, smul_smul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

/-- **An eigenvector for an eigenvalue outside the closed disc is annihilated by the Riesz
projection.** -/
theorem rieszProjection_apply_eq_zero_of_eigenvector {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {mu : ℂ}
    {v : H} (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T)
    (hmu : mu ∉ closedBall c r) (hv : T v = mu • v) :
    rieszProjection T c r v = 0 := by
  have hsphne : ∀ lam ∈ sphere c r, lam ≠ mu := by
    intro lam hlam hcon
    exact hmu (hcon ▸ sphere_subset_closedBall hlam)
  have hres : ∀ lam ∈ sphere c r, resolvent T lam v = (lam - mu)⁻¹ • v := by
    intro lam hlam
    have hd : lam - mu ≠ 0 := sub_ne_zero.mpr (hsphne lam hlam)
    have h1 : (algebraMap ℂ (H →L[ℂ] H) lam - T) ((lam - mu)⁻¹ • v) = v := by
      simp only [sub_apply, ContinuousLinearMap.map_smul,
        Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hv, smul_smul, ← sub_smul]
      rw [show lam * (lam - mu)⁻¹ - (lam - mu)⁻¹ * mu = 1 from by field_simp, one_smul]
    have h2 : resolvent T lam ((algebraMap ℂ (H →L[ℂ] H) lam - T) ((lam - mu)⁻¹ • v))
        = (lam - mu)⁻¹ • v := by
      calc resolvent T lam ((algebraMap ℂ (H →L[ℂ] H) lam - T) ((lam - mu)⁻¹ • v))
          = (resolvent T lam * (algebraMap ℂ (H →L[ℂ] H) lam - T)) ((lam - mu)⁻¹ • v) := rfl
        _ = (lam - mu)⁻¹ • v := by rw [resolvent_mul_sub (h lam hlam)]; rfl
    calc resolvent T lam v
        = resolvent T lam ((algebraMap ℂ (H →L[ℂ] H) lam - T) ((lam - mu)⁻¹ • v)) := by rw [h1]
      _ = (lam - mu)⁻¹ • v := h2
  have hzero : (∮ lam in C(c, r), (lam - mu)⁻¹) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
      Set.countable_empty ?_ (fun lam hlam => ?_)
    · exact ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn)
        (fun lam hlam => sub_ne_zero.mpr (fun hcon => hmu (hcon ▸ hlam)))
    · refine DifferentiableAt.inv (by fun_prop) (sub_ne_zero.mpr ?_)
      exact fun hcon => hmu (hcon ▸ ball_subset_closedBall hlam.1)
  rw [rieszProjection_apply T hr h v, circleIntegral.integral_congr hr hres,
    circleIntegral.integral_smul_const, hzero, zero_smul, smul_zero]

/-- Every negative power of a Cauchy kernel centred outside the closed disc integrates to zero. -/
theorem circleIntegral_inv_pow_outside (c mu : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hmu : mu ∉ closedBall c r) (k : ℕ) :
    (∮ lam in C(c, r), ((lam - mu)⁻¹ ^ (k + 1))) = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [zero_add, pow_one]
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
      Set.countable_empty ?_ (fun lam hlam => ?_)
    · exact ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn)
        (fun lam hlam => sub_ne_zero.mpr (fun hcon => hmu (hcon ▸ hlam)))
    · refine DifferentiableAt.inv (by fun_prop) (sub_ne_zero.mpr ?_)
      exact fun hcon => hmu (hcon ▸ ball_subset_closedBall hlam.1)
  · have hrw : ∀ lam : ℂ, (lam - mu)⁻¹ ^ (k + 1) = (lam - mu) ^ (-((k + 1 : ℕ) : ℤ)) := by
      intro lam
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [hrw]
    exact circleIntegral.integral_sub_zpow_of_ne (by omega) c mu r

/-- **A generalized eigenvector for an eigenvalue outside the closed disc is annihilated by the
Riesz projection.** -/
theorem rieszProjection_apply_eq_zero_of_pow_eq_zero {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {mu : ℂ}
    {n : ℕ} {x : H} (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T)
    (hmu : mu ∉ closedBall c r) (hx : ((T - mu • (1 : H →L[ℂ] H)) ^ n) x = 0) :
    rieszProjection T c r x = 0 := by
  set N : H →L[ℂ] H := T - mu • (1 : H →L[ℂ] H) with hNdef
  have hsphne : ∀ lam ∈ sphere c r, lam ≠ mu := fun lam hlam hcon =>
    hmu (hcon ▸ sphere_subset_closedBall hlam)
  have hci : ∀ k : ℕ, CircleIntegrable
      (fun lam => ((lam - mu)⁻¹ ^ (k + 1)) • ((N ^ k) x)) c r := by
    intro k
    refine ContinuousOn.circleIntegrable hr (ContinuousOn.smul ?_ continuousOn_const)
    exact ContinuousOn.pow (ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn)
      (fun lam hlam => sub_ne_zero.mpr (hsphne lam hlam))) _
  have hexp : (∮ lam in C(c, r), resolvent T lam x) = 0 := by
    rw [circleIntegral.integral_congr hr (fun lam hlam =>
      resolvent_apply_of_pow_eq_zero (h lam hlam) (hsphne lam hlam) hx)]
    rw [circleIntegral.integral_fun_sum (fun k _ => hci k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [circleIntegral.integral_smul_const, circleIntegral_inv_pow_outside c mu hr hmu k, zero_smul]
  rw [rieszProjection_apply T hr h x, hexp, smul_zero]

end GaloisForLFunctions.HTGeometry
