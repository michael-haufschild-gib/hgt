import Zeta23.Assembly

/-!
# The rank–trace certificate summed over a family of zero configurations

Alpöge–Furman's seam (`Zeta23.Assembly.seamA`) is linear in the trace and the squared Frobenius norm of
the normalised Gram matrix `Ĝ`:

`4 tr Ĝ − ‖Ĝ‖_F² − 2N − 3N_II − (θ₀/(aL))(4 + 2‖Ĝ‖_F + θ₀/(aL)) ≤ N₀*`.

Summing over a finite family of zero configurations (one per L-function) and applying Cauchy–Schwarz to
the tail term `∑ ‖Ĝ_i‖_F ≤ (|F| ∑ ‖Ĝ_i‖_F²)^{1/2}` gives the **family seam** (`family_seamA`): if the
family traces are at least `N − R` and the family Frobenius norms at most `Φ`, then

`∑ N₀*_i ≥ 4(N − R) − Φ − 2N − 3∑ N_II,i − (θ₀/(aL))(4|F| + 2(|F|Φ)^{1/2} + |F|θ₀/(aL))`,

with `N = ∑ N_i`.  With `R = o(N)`, `Φ ≤ (c + o(1))N` and small tails this is `∑ N₀*_i ≥ (2 − c − o(1)) N`:
the family-averaged certificate needs only the family-averaged Frobenius norm.
-/

open Zeta23 Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

/-- **The family seam.** -/
theorem family_seamA {ι : Type*} (s : Finset ι) (Z : ι → ZeroConfig) (P : Params) {T : ℝ}
    (hT : 0 ≤ T) (hB : ∀ i ∈ s, BlockInputs (Z i) P T) {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀)
    (hTl : ∀ i ∈ s, TailInputs (Z i) P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {N R Φ : ℝ} (hN : ∑ i ∈ s, ((Z i).N T (2 * T) : ℝ) = N)
    (htr : N - R ≤ ∑ i ∈ s, rtrace (P.hat T ((Z i).Gz P T)))
    (hΦ : ∑ i ∈ s, frobSq (P.hat T ((Z i).Gz P T)) ≤ Φ) :
    4 * (N - R) - Φ - 2 * N - 3 * ∑ i ∈ s, (NII (Z i) T : ℝ)
      - θ₀ / (P.a T * P.L T) * (4 * s.card + 2 * Real.sqrt (s.card * Φ)
          + s.card * (θ₀ / (P.a T * P.L T)))
      ≤ ∑ i ∈ s, ((Z i).N0star T (2 * T) : ℝ) := by
  set b : ℝ := θ₀ / (P.a T * P.L T) with hb
  have hb0 : 0 ≤ b := div_nonneg hθ₀ (mul_pos ha hL).le
  set f : ι → ℝ := fun i => frobSq (P.hat T ((Z i).Gz P T)) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => frobSq_nonneg _
  -- the summed seam
  have hsum : ∑ i ∈ s, (4 * rtrace (P.hat T ((Z i).Gz P T)) - f i - 2 * ((Z i).N T (2 * T) : ℝ)
      - 3 * (NII (Z i) T : ℝ) - b * (4 + 2 * Real.sqrt (f i) + b))
      ≤ ∑ i ∈ s, ((Z i).N0star T (2 * T) : ℝ) :=
    Finset.sum_le_sum fun i hi => seamA hT (hB i hi) (hTl i hi) ha hL
  -- Cauchy–Schwarz for the tail term
  have hcs : ∑ i ∈ s, Real.sqrt (f i) ≤ Real.sqrt (s.card * Φ) := by
    have h1 : (∑ i ∈ s, Real.sqrt (f i)) ^ 2 ≤ s.card * ∑ i ∈ s, f i := by
      have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (f i))
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
      simpa [Real.sq_sqrt (hf0 _)] using this
    have h2 : (s.card : ℝ) * ∑ i ∈ s, f i ≤ s.card * Φ :=
      mul_le_mul_of_nonneg_left hΦ (Nat.cast_nonneg _)
    rw [← Real.sqrt_sq (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg (f i))]
    exact Real.sqrt_le_sqrt (h1.trans h2)
  have htail : b * (4 * s.card + 2 * ∑ i ∈ s, Real.sqrt (f i) + s.card * b)
      ≤ b * (4 * s.card + 2 * Real.sqrt (s.card * Φ) + s.card * b) := by
    apply mul_le_mul_of_nonneg_left _ hb0; linarith
  have e : ∑ i ∈ s, b * (4 + 2 * Real.sqrt (f i) + b)
      = b * (4 * s.card + 2 * ∑ i ∈ s, Real.sqrt (f i) + s.card * b) := by
    rw [← Finset.mul_sum]; congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum]
    simp only [nsmul_eq_mul]; ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, e, hN] at hsum
  linarith

end RHTower
