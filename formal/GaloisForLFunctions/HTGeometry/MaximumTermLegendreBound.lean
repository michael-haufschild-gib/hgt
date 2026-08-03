import GaloisForLFunctions.HTGeometry.MaximumTermConcentration

/-!
# The Legendre bound for the terms of a power series

Comparing the term `|a_n| r^n` with the maximum term at a *different* radius and transporting the
maximum term back with the growth law gives, for every step `u`,

`|a_n| e^{xn} <= mu(e^x) exp(-(n - nu(e^{x+u})) u)`,

and symmetrically below.  Taking the supremum over `u` is the Legendre transform of
`S(x) = log mu(e^x)`: the deficit of a term below the maximum term is the amount by which the index
`n` outruns the central index over the step.

Unlike the one-radius geometric bound, this form improves as the central index becomes regular: if
`nu` grows at most linearly in `u` on a window, the exponent is quadratic in `n - nu(e^x)` and the
terms decay in the Gaussian way that a Wiman--Valiron estimate needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- **The Legendre bound above.**  For every step `u >= 0` the term at radius `e^x` is below the
maximum term there, discounted by the excess of `n` over the central index at `e^{x+u}`. -/
theorem term_le_maxTerm_exp_legendre_above
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x)
        * Real.exp (-(((n : ℝ) - (centralIndex a (Real.exp (x + u)) : ℝ)) * u)) := by
  have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hxu : (0 : ℝ) < Real.exp (x + u) := Real.exp_pos (x + u)
  obtain ⟨-, -, hμx⟩ := exists_maxTerm_eq ha hx hn₀
  obtain ⟨-, -, hμxu⟩ := exists_maxTerm_eq ha hxu hn₀
  -- the term at the larger radius is below the maximum term there
  have h1 : ‖a n‖ * Real.exp (x + u) ^ n ≤ maxTerm a (Real.exp (x + u)) :=
    term_le_maxTerm ha hxu n
  have hsplit : Real.exp (x + u) ^ n = Real.exp x ^ n * Real.exp ((n : ℝ) * u) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  have h2 : ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp (x + u)) * Real.exp (-((n : ℝ) * u)) := by
    rw [hsplit] at h1
    have hpos : (0 : ℝ) < Real.exp ((n : ℝ) * u) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖a n‖ * Real.exp x ^ n * Real.exp ((n : ℝ) * u)
        = ‖a n‖ * (Real.exp x ^ n * Real.exp ((n : ℝ) * u)) := by ring
      _ ≤ maxTerm a (Real.exp (x + u)) := h1
  -- the maximum term at the larger radius is controlled by the growth law
  have hgrow : Real.log (maxTerm a (Real.exp (x + u))) - Real.log (maxTerm a (Real.exp x))
      ≤ (centralIndex a (Real.exp (x + u)) : ℝ) * u := by
    have h := log_maxTerm_exp_sub_le_centralIndex_mul ha hn₀ (u := x) (v := x + u) (by linarith)
    simpa using h
  have h3 : maxTerm a (Real.exp (x + u))
      ≤ maxTerm a (Real.exp x) * Real.exp ((centralIndex a (Real.exp (x + u)) : ℝ) * u) := by
    have hlog : Real.log (maxTerm a (Real.exp (x + u)))
        ≤ Real.log (maxTerm a (Real.exp x) *
            Real.exp ((centralIndex a (Real.exp (x + u)) : ℝ) * u)) := by
      rw [Real.log_mul hμx.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    have hrhs : (0 : ℝ) < maxTerm a (Real.exp x)
        * Real.exp ((centralIndex a (Real.exp (x + u)) : ℝ) * u) := by positivity
    exact (Real.log_le_log_iff hμxu hrhs).mp hlog
  calc ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp (x + u)) * Real.exp (-((n : ℝ) * u)) := h2
    _ ≤ maxTerm a (Real.exp x) * Real.exp ((centralIndex a (Real.exp (x + u)) : ℝ) * u)
        * Real.exp (-((n : ℝ) * u)) := by
        exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = maxTerm a (Real.exp x)
        * Real.exp (-(((n : ℝ) - (centralIndex a (Real.exp (x + u)) : ℝ)) * u)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-- **The Legendre bound below.**  Symmetrically, comparing with the smaller radius `e^{x-u}`
discounts by the deficit of `n` under the central index there. -/
theorem term_le_maxTerm_exp_legendre_below
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x)
        * Real.exp (-(((centralIndex a (Real.exp (x - u)) : ℝ) - (n : ℝ)) * u)) := by
  have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hxu : (0 : ℝ) < Real.exp (x - u) := Real.exp_pos (x - u)
  obtain ⟨-, -, hμx⟩ := exists_maxTerm_eq ha hx hn₀
  obtain ⟨-, -, hμxu⟩ := exists_maxTerm_eq ha hxu hn₀
  have h1 : ‖a n‖ * Real.exp (x - u) ^ n ≤ maxTerm a (Real.exp (x - u)) :=
    term_le_maxTerm ha hxu n
  have hsplit : Real.exp x ^ n = Real.exp (x - u) ^ n * Real.exp ((n : ℝ) * u) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  have h2 : ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp (x - u)) * Real.exp ((n : ℝ) * u) := by
    rw [hsplit]
    calc ‖a n‖ * (Real.exp (x - u) ^ n * Real.exp ((n : ℝ) * u))
        = (‖a n‖ * Real.exp (x - u) ^ n) * Real.exp ((n : ℝ) * u) := by ring
      _ ≤ maxTerm a (Real.exp (x - u)) * Real.exp ((n : ℝ) * u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hgrow : (centralIndex a (Real.exp (x - u)) : ℝ) * u
      ≤ Real.log (maxTerm a (Real.exp x)) - Real.log (maxTerm a (Real.exp (x - u))) := by
    have h := centralIndex_mul_le_log_maxTerm_exp_sub ha hn₀ (u := x - u) (v := x) (by linarith)
    simpa using h
  have h3 : maxTerm a (Real.exp (x - u))
      ≤ maxTerm a (Real.exp x)
        * Real.exp (-((centralIndex a (Real.exp (x - u)) : ℝ) * u)) := by
    have hlog : Real.log (maxTerm a (Real.exp (x - u)))
        ≤ Real.log (maxTerm a (Real.exp x) *
            Real.exp (-((centralIndex a (Real.exp (x - u)) : ℝ) * u))) := by
      rw [Real.log_mul hμx.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    have hrhs : (0 : ℝ) < maxTerm a (Real.exp x)
        * Real.exp (-((centralIndex a (Real.exp (x - u)) : ℝ) * u)) := by positivity
    exact (Real.log_le_log_iff hμxu hrhs).mp hlog
  calc ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp (x - u)) * Real.exp ((n : ℝ) * u) := h2
    _ ≤ maxTerm a (Real.exp x) * Real.exp (-((centralIndex a (Real.exp (x - u)) : ℝ) * u))
        * Real.exp ((n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = maxTerm a (Real.exp x)
        * Real.exp (-(((centralIndex a (Real.exp (x - u)) : ℝ) - (n : ℝ)) * u)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-! ## The Gaussian form

If the central index rises at most linearly on the window, the exponent above becomes quadratic in
the excess `n - nu(e^x)`: the step `u` is free, and choosing it proportional to the excess turns a
linear discount into a square. -/

/-- **Gaussian decay above the central index.**  Under a linear bound on the rise of the central
index over the window, the exponent may be optimised in the step, giving decay `exp(-k^2 / (4 L))`
in the excess `k` of the index over the central index. -/
theorem term_le_maxTerm_exp_gaussian_above
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (_hH : 0 < H) (hL : 0 < L)
    (hlip : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    {n : ℕ} {k : ℝ} (hk : k = (n : ℝ) - (centralIndex a (Real.exp x) : ℝ)) (hk0 : 0 < k)
    (hkH : k ≤ 2 * L * H) (hkv : 2 * L * v₀ ≤ k) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x) * Real.exp (-(k ^ 2 / (4 * L))) := by
  set u : ℝ := k / (2 * L) with hu
  have hupos : 0 < u := by
    rw [hu]
    exact div_pos hk0 (by positivity)
  have huH : u ≤ H := by
    rw [hu, div_le_iff₀ (by positivity)]
    linarith
  have hbound := term_le_maxTerm_exp_legendre_above (x := x) ha hn₀ hupos.le n
  refine le_trans hbound ?_
  have hμ : (0 : ℝ) ≤ maxTerm a (Real.exp x) := by
    have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
    exact le_trans (term_nonneg a hx 0) (term_le_maxTerm ha hx 0)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
  have hu₀ : v₀ ≤ u := by
    rw [hu, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)]
    linarith
  have hlipu := hlip u hu₀ huH
  have hexp : k - L * u ≤ (n : ℝ) - (centralIndex a (Real.exp (x + u)) : ℝ) := by
    rw [hk]; linarith
  have hval : (k - L * u) * u = k ^ 2 / (4 * L) := by
    rw [hu]
    field_simp
    ring
  have hmul : (k - L * u) * u ≤ ((n : ℝ) - (centralIndex a (Real.exp (x + u)) : ℝ)) * u :=
    mul_le_mul_of_nonneg_right hexp hupos.le
  rw [hval] at hmul
  linarith

/-- **Gaussian decay below the central index.** -/
theorem term_le_maxTerm_exp_gaussian_below
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (_hH : 0 < H) (hL : 0 < L)
    (hlip : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {n : ℕ} {k : ℝ} (hk : k = (centralIndex a (Real.exp x) : ℝ) - (n : ℝ)) (hk0 : 0 < k)
    (hkH : k ≤ 2 * L * H) (hkv : 2 * L * v₀ ≤ k) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x) * Real.exp (-(k ^ 2 / (4 * L))) := by
  set u : ℝ := k / (2 * L) with hu
  have hupos : 0 < u := by
    rw [hu]
    exact div_pos hk0 (by positivity)
  have huH : u ≤ H := by
    rw [hu, div_le_iff₀ (by positivity)]
    linarith
  have hbound := term_le_maxTerm_exp_legendre_below (x := x) ha hn₀ hupos.le n
  refine le_trans hbound ?_
  have hμ : (0 : ℝ) ≤ maxTerm a (Real.exp x) := by
    have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
    exact le_trans (term_nonneg a hx 0) (term_le_maxTerm ha hx 0)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
  have hu₀ : v₀ ≤ u := by
    rw [hu, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)]
    linarith
  have hlipu := hlip u hu₀ huH
  have hexp : k - L * u ≤ (centralIndex a (Real.exp (x - u)) : ℝ) - (n : ℝ) := by
    rw [hk]; linarith
  have hval : (k - L * u) * u = k ^ 2 / (4 * L) := by
    rw [hu]
    field_simp
    ring
  have hmul : (k - L * u) * u
      ≤ ((centralIndex a (Real.exp (x - u)) : ℝ) - (n : ℝ)) * u :=
    mul_le_mul_of_nonneg_right hexp hupos.le
  rw [hval] at hmul
  linarith

/-! ## Uniform decay beyond the window

The Gaussian exponent is available only while the optimal step stays inside the window.  Past that
point the plain Legendre bound at the full step `H` is stronger than the linearised Gaussian, so a
single exponential rate `K / (4L)` covers every index outside the window `|n - nu| <= K`. -/

/-- **Uniform exponential decay above the window.**  For every index whose excess over the central
index is at least `K`, the term decays at the rate `K / (4L)` per unit of excess. -/
theorem term_le_maxTerm_exp_uniform_above
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L K v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hK0 : 0 < K) (hK : K ≤ 2 * L * H) (hKv : 2 * L * v₀ ≤ K)
    (hlip : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    {n : ℕ} {k : ℝ} (hk : k = (n : ℝ) - (centralIndex a (Real.exp x) : ℝ)) (hkK : K ≤ k) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x) * Real.exp (-(k * K / (4 * L))) := by
  have hμ : (0 : ℝ) ≤ maxTerm a (Real.exp x) := by
    have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
    exact le_trans (term_nonneg a hx 0) (term_le_maxTerm ha hx 0)
  have hk0 : 0 < k := lt_of_lt_of_le hK0 hkK
  rcases le_or_gt k (2 * L * H) with hsmall | hbig
  · refine le_trans (term_le_maxTerm_exp_gaussian_above ha hn₀ hH hL hlip hk hk0 hsmall
      (le_trans hKv hkK)) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
    have : k * K ≤ k * k := mul_le_mul_of_nonneg_left hkK hk0.le
    have hpos : (0 : ℝ) < 4 * L := by linarith
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hpos]
    nlinarith
  · have hbound := term_le_maxTerm_exp_legendre_above (x := x) (u := H) ha hn₀ hH.le n
    refine le_trans hbound ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
    have hv₀H : v₀ ≤ H := by
      have h2L : (0 : ℝ) < 2 * L := by linarith
      nlinarith [hKv, hK]
    have hlipH := hlip H hv₀H le_rfl
    have hexc : k - L * H ≤ (n : ℝ) - (centralIndex a (Real.exp (x + H)) : ℝ) := by
      rw [hk]; linarith
    have hhalf : k / 2 ≤ k - L * H := by linarith
    have hrate : k * K / (4 * L) ≤ (k / 2) * H := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * L)]
      nlinarith
    have hstep : (k / 2) * H ≤ ((n : ℝ) - (centralIndex a (Real.exp (x + H)) : ℝ)) * H :=
      mul_le_mul_of_nonneg_right (le_trans hhalf hexc) hH.le
    linarith

/-- **Uniform exponential decay below the window.** -/
theorem term_le_maxTerm_exp_uniform_below
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L K v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hK0 : 0 < K) (hK : K ≤ 2 * L * H) (hKv : 2 * L * v₀ ≤ K)
    (hlip : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {n : ℕ} {k : ℝ} (hk : k = (centralIndex a (Real.exp x) : ℝ) - (n : ℝ)) (hkK : K ≤ k) :
    ‖a n‖ * Real.exp x ^ n
      ≤ maxTerm a (Real.exp x) * Real.exp (-(k * K / (4 * L))) := by
  have hμ : (0 : ℝ) ≤ maxTerm a (Real.exp x) := by
    have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
    exact le_trans (term_nonneg a hx 0) (term_le_maxTerm ha hx 0)
  have hk0 : 0 < k := lt_of_lt_of_le hK0 hkK
  rcases le_or_gt k (2 * L * H) with hsmall | hbig
  · refine le_trans (term_le_maxTerm_exp_gaussian_below ha hn₀ hH hL hlip hk hk0 hsmall
      (le_trans hKv hkK)) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
    have : k * K ≤ k * k := mul_le_mul_of_nonneg_left hkK hk0.le
    have hpos : (0 : ℝ) < 4 * L := by linarith
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hpos]
    nlinarith
  · have hbound := term_le_maxTerm_exp_legendre_below (x := x) (u := H) ha hn₀ hH.le n
    refine le_trans hbound ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hμ
    have hv₀H : v₀ ≤ H := by
      have h2L : (0 : ℝ) < 2 * L := by linarith
      nlinarith [hKv, hK]
    have hlipH := hlip H hv₀H le_rfl
    have hexc : k - L * H ≤ (centralIndex a (Real.exp (x - H)) : ℝ) - (n : ℝ) := by
      rw [hk]; linarith
    have hhalf : k / 2 ≤ k - L * H := by linarith
    have hrate : k * K / (4 * L) ≤ (k / 2) * H := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * L)]
      nlinarith
    have hstep : (k / 2) * H
        ≤ ((centralIndex a (Real.exp (x - H)) : ℝ) - (n : ℝ)) * H :=
      mul_le_mul_of_nonneg_right (le_trans hhalf hexc) hH.le
    linarith

end GaloisForLFunctions.HTGeometry
