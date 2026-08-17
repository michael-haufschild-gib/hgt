import GaloisForLFunctions.HTGeometry.ComplexPairLocalization

/-!
# Limits of exponential certificates for several conjugate pairs

A single conjugate pair is certified exactly by one separating exponential: on the arc where the
cosine is nonnegative, `log` of the cap is concave, so a line separates it from the convex `log R`.
This file shows that the method cannot survive a second pair, and measures by how much the obvious
repair — treating the pairs one at a time — falls short.

* **The chord obstruction.**  An exponential is log-affine, so if it dominates a comparison function
  at two points it dominates the geometric mean of those values everywhere in between.  Whenever the
  comparison function has two positive values straddling a nonpositive one — impossible for a single
  cap on its own arc, generic for two pairs — the certificate demands strictly more than the
  inequality it is supposed to certify.  Explicitly, there is a two-term positive exponential sum
  dominating the comparison function on all of `ℝ` for which no separating exponential exists.

* **The per-pair gap.**  Splitting `R` into one summand per pair is strictly weaker.  Two pairs at
  frequencies `1` and `2` with opposite signs give a comparison function of supremum `9/4`, attained;
  any per-pair split needs total mass `4`.  The mechanism is the identity
  `9/4 - 2 cos t + 2 cos 2t = (2 cos t - 1/2)^2`, the same coupling between harmonics that makes
  `3 + 4 cos t + cos 2t` nonnegative.

The split is genuinely by constants: two positive exponential sums whose sum is constant are both
constant, since a positive combination of exponentials has vanishing second derivative only when
every exponent vanishes.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-! ## The chord obstruction -/

private theorem exp_rpow' (z w : ℝ) : Real.exp z ^ w = Real.exp (z * w) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos z), Real.log_exp]

/-- A log-affine function is its own geometric interpolation. -/
theorem exp_affine_geom {A μ t₁ t₂ θ : ℝ} (hA : 0 < A) :
    (A * Real.exp (μ * t₁)) ^ θ * (A * Real.exp (μ * t₂)) ^ (1 - θ)
      = A ^ θ * A ^ (1 - θ) * Real.exp (μ * (θ * t₁ + (1 - θ) * t₂)) := by
  rw [Real.mul_rpow hA.le (Real.exp_pos _).le, Real.mul_rpow hA.le (Real.exp_pos _).le,
    exp_rpow', exp_rpow']
  rw [show A ^ θ * Real.exp (μ * t₁ * θ) * (A ^ (1 - θ) * Real.exp (μ * t₂ * (1 - θ)))
      = A ^ θ * A ^ (1 - θ) * (Real.exp (μ * t₁ * θ) * Real.exp (μ * t₂ * (1 - θ))) from by ring,
    ← Real.exp_add]
  congr 2
  ring

/-- **The chord obstruction.**  An exponential dominating `C` at two points where `C` is positive
must exceed the minimum of those two values at every point in between.  In particular it cannot stay
small where `C` dips to zero. -/
theorem min_le_of_exp_dominates {A μ t₁ t₃ t₂ : ℝ} (hA : 0 < A) (h13 : t₁ < t₃) (h32 : t₃ < t₂)
    {C : ℝ → ℝ} (hC1 : 0 < C t₁) (hC2 : 0 < C t₂)
    (hdom : ∀ t ∈ Icc t₁ t₂, C t ≤ A * Real.exp (μ * t)) :
    min (C t₁) (C t₂) ≤ A * Real.exp (μ * t₃) := by
  have h12 : t₁ < t₂ := lt_trans h13 h32
  set θ : ℝ := (t₂ - t₃) / (t₂ - t₁) with hθ
  have hden : (0 : ℝ) < t₂ - t₁ := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, sub_nonneg, div_le_one hden]
    linarith
  have hcomb : θ * t₁ + (1 - θ) * t₂ = t₃ := by
    rw [hθ]
    field_simp
    ring
  have hmin : 0 < min (C t₁) (C t₂) := lt_min hC1 hC2
  have hd1 : C t₁ ≤ A * Real.exp (μ * t₁) := hdom t₁ ⟨le_refl _, le_of_lt h12⟩
  have hd2 : C t₂ ≤ A * Real.exp (μ * t₂) := hdom t₂ ⟨le_of_lt h12, le_refl _⟩
  have step1 : min (C t₁) (C t₂) ^ θ * min (C t₁) (C t₂) ^ (1 - θ)
      ≤ (A * Real.exp (μ * t₁)) ^ θ * (A * Real.exp (μ * t₂)) ^ (1 - θ) := by
    refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hmin.le _) (Real.rpow_nonneg (by positivity) _)
    · exact Real.rpow_le_rpow hmin.le (le_trans (min_le_left _ _) hd1) hθ0
    · exact Real.rpow_le_rpow hmin.le (le_trans (min_le_right _ _) hd2) hθ1
  rw [← Real.rpow_add hmin] at step1
  simp only [add_sub_cancel, Real.rpow_one] at step1
  rw [exp_affine_geom hA, hcomb, ← Real.rpow_add hA] at step1
  simpa using step1

/-! ## A dominating sum with no separating exponential -/

private theorem expSum_two (c a : Fin 2 → ℝ) (t : ℝ) :
    expSum c a t = c 0 * Real.exp (a 0 * t) + c 1 * Real.exp (a 1 * t) := by
  rw [expSum, Fin.sum_univ_two]

/-- **No joint profile.**  If the comparison function takes two positive values straddling a
nonpositive one, then some two-term positive exponential sum dominates it on the whole line while
admitting no separating exponential on the straddling interval.  So no criterion of the form
"`R` dominates `C` iff a single exponential separates them" can hold once `C` has two humps. -/
theorem exists_expSum_no_separating {C : ℝ → ℝ} (hCcont : Continuous C) {M t₁ t₃ t₂ : ℝ}
    (hM : ∀ t, C t ≤ M) (h13 : t₁ < t₃) (h32 : t₃ < t₂)
    (hC1 : 0 < C t₁) (hC2 : 0 < C t₂) (hC3 : C t₃ ≤ 0) :
    ∃ cc aa : Fin 2 → ℝ, (∀ i, 0 < cc i) ∧ (∀ t : ℝ, C t ≤ expSum cc aa t) ∧
      ¬ ∃ A μ : ℝ, 0 < A ∧ (∀ t ∈ Icc t₁ t₂, C t ≤ A * Real.exp (μ * t))
          ∧ (∀ t : ℝ, A * Real.exp (μ * t) ≤ expSum cc aa t) := by
  classical
  set lam : ℝ := min (C t₁) (C t₂) / 2 with hlam
  have hmin : 0 < min (C t₁) (C t₂) := lt_min hC1 hC2
  have hlampos : 0 < lam := by rw [hlam]; linarith
  have hlamlt : lam < min (C t₁) (C t₂) := by rw [hlam]; linarith
  have hMpos : 0 < M := lt_of_lt_of_le hC1 (hM t₁)
  -- a window around `t₃` on which `C` stays below `lam`
  have hev : ∀ᶠ t in nhds t₃, C t < lam := by
    refine (hCcont.continuousAt (x := t₃)).eventually (eventually_lt_nhds ?_)
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set eta : ℝ := ε / 2 with heta
  have hetapos : 0 < eta := by rw [heta]; linarith
  have hwin : ∀ t : ℝ, |t - t₃| ≤ eta → C t ≤ lam := by
    intro t ht
    have : dist t t₃ < ε := by
      rw [Real.dist_eq]
      calc |t - t₃| ≤ eta := ht
        _ < ε := by rw [heta]; linarith
    exact le_of_lt (hball this)
  -- a growth rate large enough that the sum clears `M` outside the window
  set K : ℝ := max 1 (2 * M / (lam * eta)) with hK
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKbig : 2 * M / (lam * eta) ≤ K := le_max_right _ _
  set cc : Fin 2 → ℝ := ![lam / 2 * Real.exp (-(K * t₃)), lam / 2 * Real.exp (K * t₃)] with hcc
  set aa : Fin 2 → ℝ := ![K, -K] with haa
  have hccpos : ∀ i, 0 < cc i := by
    intro i
    fin_cases i
    · show (0 : ℝ) < lam / 2 * Real.exp (-(K * t₃))
      positivity
    · show (0 : ℝ) < lam / 2 * Real.exp (K * t₃)
      positivity
  have hRval : ∀ t : ℝ, expSum cc aa t = lam * Real.cosh (K * (t - t₃)) := by
    intro t
    rw [expSum_two, Real.cosh_eq]
    simp only [hcc, haa, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have h1 : -(K * t₃) + K * t = K * (t - t₃) := by ring
    have h2 : K * t₃ + -K * t = -(K * (t - t₃)) := by ring
    rw [h1, h2]
    ring
  have hdomR : ∀ t : ℝ, C t ≤ expSum cc aa t := by
    intro t
    rw [hRval]
    by_cases hcase : |t - t₃| ≤ eta
    · calc C t ≤ lam := hwin t hcase
        _ = lam * 1 := by ring
        _ ≤ lam * Real.cosh (K * (t - t₃)) :=
            mul_le_mul_of_nonneg_left (Real.one_le_cosh _) hlampos.le
    · push Not at hcase
      have habs : |K * eta| ≤ |K * (t - t₃)| := by
        rw [abs_mul, abs_mul, abs_of_pos hKpos, abs_of_pos hetapos]
        exact mul_le_mul_of_nonneg_left (le_of_lt hcase) hKpos.le
      have hmono : Real.cosh (K * eta) ≤ Real.cosh (K * (t - t₃)) :=
        Real.cosh_le_cosh.mpr habs
      have hlin : K * eta / 2 ≤ Real.cosh (K * eta) := by
        rw [Real.cosh_eq]
        have h1 : K * eta ≤ Real.exp (K * eta) := by
          have := Real.add_one_le_exp (K * eta)
          linarith
        have h2 : (0 : ℝ) < Real.exp (-(K * eta)) := Real.exp_pos _
        linarith
      have hclear : M ≤ lam * Real.cosh (K * eta) := by
        have hstep : 2 * M / (lam * eta) * (lam * eta) ≤ K * (lam * eta) :=
          mul_le_mul_of_nonneg_right hKbig (by positivity)
        rw [div_mul_cancel₀ _ (by positivity : (lam * eta) ≠ 0)] at hstep
        have : lam * (K * eta / 2) ≤ lam * Real.cosh (K * eta) :=
          mul_le_mul_of_nonneg_left hlin hlampos.le
        nlinarith [this, hstep]
      calc C t ≤ M := hM t
        _ ≤ lam * Real.cosh (K * eta) := hclear
        _ ≤ lam * Real.cosh (K * (t - t₃)) := mul_le_mul_of_nonneg_left hmono hlampos.le
  refine ⟨cc, aa, hccpos, hdomR, ?_⟩
  rintro ⟨A, μ, hA, hdom, hbelow⟩
  have hchord := min_le_of_exp_dominates hA h13 h32 hC1 hC2 hdom
  have hval : A * Real.exp (μ * t₃) ≤ lam := by
    have := hbelow t₃
    rw [hRval] at this
    simpa using this
  linarith

/-! ## The per-pair gap -/

/-- The two-pair comparison function `2 cos t - 2 cos 2t` never exceeds `9/4`; the certificate is the
square `(2 cos t - 1/2)^2`. -/
theorem two_cos_sub_two_cos_two_mul_le (t : ℝ) :
    2 * Real.cos t - 2 * Real.cos (2 * t) ≤ 9 / 4 := by
  have h := Real.cos_two_mul t
  nlinarith [sq_nonneg (2 * Real.cos t - 1 / 2)]

/-- The bound `9/4` is attained. -/
theorem exists_two_cos_sub_two_cos_two_mul_eq :
    ∃ t : ℝ, 2 * Real.cos t - 2 * Real.cos (2 * t) = 9 / 4 := by
  refine ⟨Real.arccos (1 / 4), ?_⟩
  have hc : Real.cos (Real.arccos (1 / 4)) = 1 / 4 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  rw [Real.cos_two_mul, hc]
  norm_num

/-- **The per-pair gap.**  Certifying the two pairs separately costs total mass `4`. -/
theorem per_pair_sum_ge_four {r₁ r₂ : ℝ} (h1 : ∀ t : ℝ, 2 * Real.cos t ≤ r₁)
    (h2 : ∀ t : ℝ, -(2 * Real.cos (2 * t)) ≤ r₂) : 4 ≤ r₁ + r₂ := by
  have e1 := h1 0
  have e2 := h2 (π / 2)
  rw [Real.cos_zero] at e1
  have hpi : 2 * (π / 2) = π := by ring
  rw [hpi, Real.cos_pi] at e2
  linarith

/-- Two positive exponential sums over a common exponent family whose sum is constant have every
exponent zero, hence are separately constant.  So the per-pair split above is genuinely a split into
constants. -/
theorem exponents_eq_zero_of_expSum_const {m : ℕ} (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i) {κ : ℝ}
    (h : ∀ t : ℝ, expSum c a t = κ) : ∀ i, a i = 0 := by
  have hfun : expSum c a = fun _ : ℝ => κ := funext h
  have hd1 : expSum (fun i => c i * a i) a = fun _ : ℝ => (0 : ℝ) := by
    rw [← deriv_expSum, hfun]
    exact deriv_const' κ
  have hd2 : expSum (fun i => c i * a i * a i) a = fun _ : ℝ => (0 : ℝ) := by
    rw [← deriv_expSum, hd1]
    exact deriv_const' 0
  have hzero : ∑ i, c i * a i * a i * Real.exp (a i * 0) = 0 := by
    have := congrFun hd2 0
    rwa [expSum] at this
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => by
    have hrw : c i * a i * a i = c i * a i ^ 2 := by ring
    rw [hrw]
    exact mul_nonneg (mul_nonneg (hc i).le (sq_nonneg _)) (Real.exp_pos _).le)).mp hzero
  intro i
  have hi := hterm i (Finset.mem_univ i)
  have hexp : Real.exp (a i * 0) ≠ 0 := Real.exp_ne_zero _
  have hcb : c i * a i * a i = 0 := by
    rcases mul_eq_zero.mp hi with h' | h'
    · exact h'
    · exact absurd h' hexp
  rcases mul_eq_zero.mp hcb with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (ne_of_gt (hc i))
    · exact h''
  · exact h'

end GaloisForLFunctions.HTGeometry
