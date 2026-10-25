import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryCompleteness

/-!
# Rankin–Selberg forcing: Bessel's inequality on the boundary

Let `f` be an Euler product with real log-coefficients `Λ(n) g(n)`, `|g| ≤ M`, of either sign: no
nonnegativity is assumed. Its boundary divisor is
`D_f(u) = lim_{x↓0} x Σ Λ(n) n^{−1−x} g(n) cos(u log n)`. The Rankin–Selberg square `f ⊗ f` has
log-coefficients `Λ(n) g(n)² ≥ 0` and pole order `R = lim_{x↓0} x Σ Λ(n) n^{−1−x} g(n)²` at `s = 1`.

**Bessel's inequality** (`rankinSelberg_bessel`). For every finite set `U` of positive heights,
`D_f(0)² + 2 Σ_{u ∈ U} D_f(u)² ≤ R`.

*Proof.* For the prime measure `x Λ(n) n^{−1−x}` the cosines `cos(u log n)`, `u ∈ {0} ∪ U`, have Gram
matrix tending to `diag(1, ½, …, ½)`, because `D_ζ = δ₀` and
`cos A cos B = (cos(A − B) + cos(A + B))/2`. Expand
`x Σ Λ(n) n^{−1−x} (g(n) − D_f(0) − 2 Σ_u D_f(u) cos(u log n))² ≥ 0` and let `x ↓ 0`.

* **Rankin–Selberg forcing law** (`rankinSelberg_forcing`). If `f` and `f ⊗ f` both have a simple
  pole (`D_f(0) = R = 1`), then `D_f(u) = 0` for every `u ≠ 0`. Nonnegativity, integrality and pole
  isolation of `f` are replaced by one condition on its square.
* **Sharpness** (`rankinSelberg_bessel_sharp`). `ζ(s)/(ζ(s + i) ζ(s − i))`, with `g = 1 − 2cos(log n)`,
  has `D_f(0) = 1`, `D_f(1) = −1` and `R = 3 = 1² + 2·(−1)²`: Bessel is an equality (Parseval for the
  trigonometric polynomial `g`). This is the datum showing that (N) is necessary for the Bochner
  forcing law; Rankin–Selberg detects it through its square.

The pole order of `f ⊗ f` bounds the `ℓ²`-norm of the boundary divisor of `f`: positivity of squares
is a forcing mechanism independent of positive definiteness.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Product-to-sum for two cosine modes. -/
theorem cos_mul_cos_log (L u v : ℝ) :
    Real.cos (L * u) * Real.cos (L * v) =
      (Real.cos (L * (u - v)) + Real.cos (L * (u + v))) / 2 := by
  rw [show L * (u - v) = L * u - L * v by ring, show L * (u + v) = L * u + L * v by ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- The trace of the signed weights `Λ(n) n^{−1−x} g(n)` at height `u`. -/
noncomputable def signedTrace (g : ℕ → ℝ) (x u : ℝ) : ℝ :=
  ∑' n, zetaBoundaryWeight x n * g n * Real.cos (logFrequency n * u)

/-- The trace of the square weights `Λ(n) n^{−1−x} g(n)²` at the origin. -/
noncomputable def squareTrace (g : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, zetaBoundaryWeight x n * g n ^ 2

section Bessel

variable {g : ℕ → ℝ} {M : ℝ}

theorem summable_signedTrace_terms (hg : ∀ n, |g n| ≤ M) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable fun n => zetaBoundaryWeight x n * g n * Real.cos (logFrequency n * u) :=
  Summable.of_norm_bounded ((summable_zetaBoundaryWeight hx).mul_right M) fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (zetaBoundaryWeight_nonneg x n)]
    have h1 := Real.abs_cos_le_one (logFrequency n * u)
    have h0 := zetaBoundaryWeight_nonneg x n
    calc zetaBoundaryWeight x n * |g n| * |Real.cos (logFrequency n * u)|
        ≤ zetaBoundaryWeight x n * |g n| * 1 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg h0 (abs_nonneg _))
      _ ≤ zetaBoundaryWeight x n * M := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (hg n) h0

theorem summable_squareTrace_terms (hg : ∀ n, |g n| ≤ M) {x : ℝ} (hx : 0 < x) :
    Summable fun n => zetaBoundaryWeight x n * g n ^ 2 :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n) (sq_nonneg _))
    (fun n => by
      have h0 := zetaBoundaryWeight_nonneg x n
      have : g n ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hg n) 2
      exact mul_le_mul_of_nonneg_left this h0)
    ((summable_zetaBoundaryWeight hx).mul_right (M ^ 2))

/-- The Gram expansion at a fixed damping: the squared residual of `g` against the cosine system,
weighted by the prime measure, written through the traces. -/
theorem residual_hasSum (hg : ∀ n, |g n| ≤ M) {x : ℝ} (hx : 0 < x) (a₀ : ℝ) (U : Finset ℝ)
    (a : ℝ → ℝ) :
    HasSum (fun n => zetaBoundaryWeight x n *
        (g n - a₀ - ∑ u ∈ U, a u * Real.cos (logFrequency n * u)) ^ 2)
      (squareTrace g x - 2 * a₀ * signedTrace g x 0 -
        2 * ∑ u ∈ U, a u * signedTrace g x u +
        a₀ ^ 2 * cosineTrace (zetaBoundaryWeight x) logFrequency 0 +
        2 * a₀ * ∑ u ∈ U, a u * cosineTrace (zetaBoundaryWeight x) logFrequency u +
        ∑ u ∈ U, ∑ v ∈ U, a u * a v *
          ((cosineTrace (zetaBoundaryWeight x) logFrequency (u - v) +
            cosineTrace (zetaBoundaryWeight x) logFrequency (u + v)) / 2)) := by
  have hz := summable_zetaBoundaryWeight hx
  have hnn := zetaBoundaryWeight_nonneg x
  have hC : ∀ w, HasSum (fun n => zetaBoundaryWeight x n * Real.cos (logFrequency n * w))
      (cosineTrace (zetaBoundaryWeight x) logFrequency w) := fun w =>
    (summable_cosineTrace_terms hnn hz logFrequency w).hasSum
  have hS : ∀ w, HasSum (fun n => zetaBoundaryWeight x n * g n * Real.cos (logFrequency n * w))
      (signedTrace g x w) := fun w => (summable_signedTrace_terms hg hx w).hasSum
  have hQ : HasSum (fun n => zetaBoundaryWeight x n * g n ^ 2) (squareTrace g x) :=
    (summable_squareTrace_terms hg hx).hasSum
  have hall := ((((hQ.sub ((hS 0).mul_left (2 * a₀))).sub
    ((hasSum_sum fun u _ => (hS u).mul_left (a u)).mul_left 2)).add
    ((hC 0).mul_left (a₀ ^ 2))).add
    ((hasSum_sum fun u _ => (hC u).mul_left (a u)).mul_left (2 * a₀))).add
    (hasSum_sum fun u _ => hasSum_sum fun v _ =>
      (((hC (u - v)).add (hC (u + v))).div_const 2).mul_left (a u * a v))
  refine hall.congr_fun fun n => ?_
  simp only [mul_zero, Real.cos_zero, mul_one]
  set L := logFrequency n
  set S := ∑ u ∈ U, a u * Real.cos (L * u)
  have hgS : ∑ u ∈ U, a u * (zetaBoundaryWeight x n * g n * Real.cos (L * u)) =
      zetaBoundaryWeight x n * g n * S := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hzS : ∑ u ∈ U, a u * (zetaBoundaryWeight x n * Real.cos (L * u)) =
      zetaBoundaryWeight x n * S := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hSS : ∑ u ∈ U, ∑ v ∈ U, a u * a v * ((zetaBoundaryWeight x n * Real.cos (L * (u - v)) +
      zetaBoundaryWeight x n * Real.cos (L * (u + v))) / 2) = zetaBoundaryWeight x n * S ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [cos_mul_cos_log]
    ring
  rw [hgS, hzS, hSS]
  ring

/-- **Bessel's inequality on the boundary.** -/
theorem rankinSelberg_bessel (hg : ∀ n, |g n| ≤ M) {Df : ℝ → ℝ} {R : ℝ}
    (hf : ∀ u, Tendsto (fun x => x * signedTrace g x u) (𝓝[>] 0) (𝓝 (Df u)))
    (hR : Tendsto (fun x => x * squareTrace g x) (𝓝[>] 0) (𝓝 R))
    {U : Finset ℝ} (hU : ∀ u ∈ U, 0 < u) :
    Df 0 ^ 2 + 2 * ∑ u ∈ U, Df u ^ 2 ≤ R := by
  classical
  set a₀ := Df 0
  set a : ℝ → ℝ := fun u => 2 * Df u
  have hT : ∀ w, Tendsto (fun x => x * cosineTrace (zetaBoundaryWeight x) logFrequency w)
      (𝓝[>] 0) (𝓝 (if w = 0 then 1 else 0)) := fun w => by
    simpa only [zetaBoundaryDivisor_eq] using zeta_isBoundaryDivisor.tendsto w
  -- The normalized residual converges to the Bessel defect.
  have hlim : Tendsto (fun x => x * (squareTrace g x - 2 * a₀ * signedTrace g x 0 -
        2 * ∑ u ∈ U, a u * signedTrace g x u +
        a₀ ^ 2 * cosineTrace (zetaBoundaryWeight x) logFrequency 0 +
        2 * a₀ * ∑ u ∈ U, a u * cosineTrace (zetaBoundaryWeight x) logFrequency u +
        ∑ u ∈ U, ∑ v ∈ U, a u * a v *
          ((cosineTrace (zetaBoundaryWeight x) logFrequency (u - v) +
            cosineTrace (zetaBoundaryWeight x) logFrequency (u + v)) / 2)))
      (𝓝[>] 0) (𝓝 (R - 2 * a₀ * Df 0 - 2 * ∑ u ∈ U, a u * Df u +
        a₀ ^ 2 * (if (0 : ℝ) = 0 then 1 else 0) +
        2 * a₀ * ∑ u ∈ U, a u * (if u = 0 then 1 else 0) +
        ∑ u ∈ U, ∑ v ∈ U, a u * a v *
          (((if u - v = 0 then 1 else 0) + (if u + v = 0 then 1 else 0)) / 2))) := by
    have h := (((((hR.sub ((hf 0).const_mul (2 * a₀))).sub
      ((tendsto_finsetSum U fun u _ => (hf u).const_mul (a u)).const_mul 2)).add
      ((hT 0).const_mul (a₀ ^ 2))).add
      ((tendsto_finsetSum U fun u _ => (hT u).const_mul (a u)).const_mul (2 * a₀))).add
      (tendsto_finsetSum U fun u _ => tendsto_finsetSum U fun v _ =>
        (((hT (u - v)).add (hT (u + v))).div_const 2).const_mul (a u * a v)))
    refine h.congr fun x => ?_
    simp only [Finset.mul_sum]
    ring_nf
  -- Evaluate the limit.
  have hval : R - 2 * a₀ * Df 0 - 2 * ∑ u ∈ U, a u * Df u +
      a₀ ^ 2 * (if (0 : ℝ) = 0 then 1 else 0) +
      2 * a₀ * ∑ u ∈ U, a u * (if u = 0 then 1 else 0) +
      ∑ u ∈ U, ∑ v ∈ U, a u * a v *
        (((if u - v = 0 then 1 else 0) + (if u + v = 0 then 1 else 0)) / 2) =
      R - Df 0 ^ 2 - 2 * ∑ u ∈ U, Df u ^ 2 := by
    have h1 : ∑ u ∈ U, a u * (if u = 0 then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun u hu => by rw [if_neg (hU u hu).ne']; ring
    have h2 : ∑ u ∈ U, ∑ v ∈ U, a u * a v *
        (((if u - v = 0 then (1 : ℝ) else 0) + (if u + v = 0 then 1 else 0)) / 2) =
        ∑ u ∈ U, a u ^ 2 / 2 := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.sum_eq_single_of_mem u hu]
      · rw [sub_self, if_pos rfl, if_neg (by linarith [hU u hu])]
        ring
      · intro v hv hvu
        rw [if_neg (sub_ne_zero.mpr (Ne.symm hvu)), if_neg (by linarith [hU u hu, hU v hv])]
        ring
    rw [if_pos rfl, h1, h2]
    simp only [a, a₀]
    rw [show ∑ u ∈ U, 2 * Df u * Df u = 2 * ∑ u ∈ U, Df u ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring,
      show ∑ u ∈ U, (2 * Df u) ^ 2 / 2 = 2 * ∑ u ∈ U, Df u ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring]
    ring
  rw [hval] at hlim
  have hnn : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤ x * (squareTrace g x - 2 * a₀ * signedTrace g x 0 -
        2 * ∑ u ∈ U, a u * signedTrace g x u +
        a₀ ^ 2 * cosineTrace (zetaBoundaryWeight x) logFrequency 0 +
        2 * a₀ * ∑ u ∈ U, a u * cosineTrace (zetaBoundaryWeight x) logFrequency u +
        ∑ u ∈ U, ∑ v ∈ U, a u * a v *
          ((cosineTrace (zetaBoundaryWeight x) logFrequency (u - v) +
            cosineTrace (zetaBoundaryWeight x) logFrequency (u + v)) / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (le_of_lt hx) ((residual_hasSum hg hx a₀ U a).nonneg fun n =>
      mul_nonneg (zetaBoundaryWeight_nonneg x n) (sq_nonneg _))
  have := ge_of_tendsto hlim hnn
  linarith

/-- **Rankin–Selberg forcing law.** If `f` and `f ⊗ f` both have a simple pole at `s = 1`, the
boundary divisor of `f` vanishes off the origin. -/
theorem rankinSelberg_forcing (hg : ∀ n, |g n| ≤ M) {Df : ℝ → ℝ}
    (hf : ∀ u, Tendsto (fun x => x * signedTrace g x u) (𝓝[>] 0) (𝓝 (Df u)))
    (hR : Tendsto (fun x => x * squareTrace g x) (𝓝[>] 0) (𝓝 1)) (h0 : Df 0 = 1)
    {u : ℝ} (hu : u ≠ 0) : Df u = 0 := by
  -- `Df` is even: the traces are.
  have heven : Df (-u) = Df u := by
    refine tendsto_nhds_unique ((hf (-u)).congr fun x => ?_) (hf u)
    simp [signedTrace, mul_neg, Real.cos_neg]
  have key : ∀ w, 0 < w → Df w = 0 := by
    intro w hw
    have h := rankinSelberg_bessel hg hf hR (U := {w}) (by simpa using hw)
    rw [Finset.sum_singleton, h0] at h
    nlinarith [sq_nonneg (Df w)]
  rcases lt_or_gt_of_ne hu with h | h
  · rw [← heven]; exact key _ (by linarith)
  · exact key u h

end Bessel

/-! ### Sharpness -/

/-- The coefficients `(3, −4, 2)` of `(1 − 2cos θ)² = 3 − 4cos θ + 2cos 2θ`. -/
def signedSquareCoeff : ℕ → ℝ
  | 0 => 3
  | 1 => -4
  | 2 => 2
  | _ => 0

/-- **Bessel is attained.** For `ζ(s)/(ζ(s+i)ζ(s−i))`, `g = 1 − 2cos(log n)`: `D_f(0) = 1`,
`D_f(1) = −1` and the square has pole order `3 = 1² + 2·(−1)²`. -/
theorem rankinSelberg_bessel_sharp :
    let g : ℕ → ℝ := fun n => HTGeometry.cosinePolynomial signedCoeff 1 (1 * logFrequency n)
    Tendsto (fun x => x * signedTrace g x 0) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun x => x * signedTrace g x 1) (𝓝[>] 0) (𝓝 (-1)) ∧
      Tendsto (fun x => x * squareTrace g x) (𝓝[>] 0) (𝓝 3) := by
  intro g
  have htw : ∀ u, signedTrace g = fun x u' => cosineTrace (twistedWeight signedCoeff 1 1 x)
      logFrequency u' := fun _ => by
    funext x u'
    simp only [signedTrace, cosineTrace, twistedWeight, g]
  have hsq : ∀ x, squareTrace g x = cosineTrace (twistedWeight signedSquareCoeff 2 1 x)
      logFrequency 0 := fun x => by
    simp only [squareTrace, cosineTrace, twistedWeight, g, mul_zero, Real.cos_zero, mul_one]
    refine tsum_congr fun n => ?_
    congr 1
    simp only [HTGeometry.cosinePolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
      signedCoeff, signedSquareCoeff]
    push_cast
    rw [show (2 : ℝ) * (1 * logFrequency n) = 2 * (1 * logFrequency n) from rfl,
      Real.cos_two_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have h := tendsto_twistedTrace signedCoeff 1 1 0
    rw [twistedDivisor_zero _ _ one_ne_zero] at h
    simpa [htw 0, signedCoeff] using h
  · have h := tendsto_twistedTrace signedCoeff 1 1 1
    rw [twistedDivisor_one_at_one] at h
    norm_num [signedCoeff] at h
    simpa [htw 1] using h
  · have h := tendsto_twistedTrace signedSquareCoeff 2 1 0
    rw [twistedDivisor_zero _ _ one_ne_zero] at h
    simp only [signedSquareCoeff] at h
    simpa [hsq] using h

end GaloisForLFunctions.MultiplicativePositivityGeometry
