import GaloisForLFunctions.HTGeometry.LagrangeRemainder
import GaloisForLFunctions.HTGeometry.SeparatedNodeProducts

/-!
# Sup bound for Lagrange interpolants over separated nodes

For `η`-separated nodes in a unit-radius window around `x`, each Lagrange
basis value obeys the crude bound `|ℓ_t(x)| ≤ 2^N/(η^N·N!)`, hence

`|P(x)| ≤ (N+1)·2^N/(η^N·N!)·max_t |f(t)|`.

The constant is exponential of size `e^{O(N)}` when `η ≈ 1/(2N)`; combined
with the factorially small interpolation remainder this is exactly the
loss-free trade in limsup-type oversampling arguments.
-/

noncomputable section

namespace HTGeometry

open Polynomial

/-- Crude Lagrange basis bound over separated nodes. -/
theorem abs_eval_basis_le
    {s : Finset ℝ} {N : ℕ} (hcard : s.card = N + 1) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {x : ℝ} (hclose : ∀ u ∈ s, |x - u| ≤ 1)
    {t : ℝ} (ht : t ∈ s) :
    |(Lagrange.basis s id t).eval x| ≤ 2 ^ N / (η ^ N * N.factorial) := by
  have hden := prod_erase_abs_sub_ge hcard hη.le hsep ht
  have hden0 : (0:ℝ) < η ^ N * ((N.factorial : ℝ) / 2 ^ N) := by positivity
  have heval : (Lagrange.basis s id t).eval x
      = ∏ u ∈ s.erase t, ((t - u)⁻¹ * (x - u)) := by
    rw [Lagrange.basis, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro u _
    simp [Lagrange.basisDivisor]
  rw [heval, Finset.abs_prod]
  have habs : ∀ u ∈ s.erase t,
      |(t - u)⁻¹ * (x - u)| = |x - u| * |t - u|⁻¹ := by
    intro u _
    rw [abs_mul, abs_inv]
    ring
  rw [Finset.prod_congr rfl habs, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have hnum : (∏ u ∈ s.erase t, |x - u|) ≤ 1 :=
    Finset.prod_le_one (fun u _ => abs_nonneg _)
      (fun u hu => hclose u (Finset.mem_of_mem_erase hu))
  have hprodpos : (0:ℝ) < ∏ u ∈ s.erase t, |t - u| :=
    lt_of_lt_of_le hden0 hden
  have hinvle : (∏ u ∈ s.erase t, |t - u|)⁻¹
      ≤ (η ^ N * ((N.factorial : ℝ) / 2 ^ N))⁻¹ :=
    (inv_le_inv₀ hprodpos hden0).2 hden
  have h1 : (η:ℝ) ^ N ≠ 0 := by positivity
  have h2 : ((N.factorial : ℝ)) ≠ 0 := by positivity
  have h3 : (2:ℝ) ^ N ≠ 0 := by positivity
  calc (∏ u ∈ s.erase t, |x - u|) * (∏ u ∈ s.erase t, |t - u|)⁻¹
      ≤ 1 * (η ^ N * ((N.factorial : ℝ) / 2 ^ N))⁻¹ := by
        apply mul_le_mul hnum hinvle (by positivity) (by norm_num)
    _ = 2 ^ N / (η ^ N * N.factorial) := by
        rw [one_mul]
        field_simp
    _ ≤ 2 ^ N / (η ^ N * N.factorial) := le_rfl

/-- **Interpolant sup bound over separated nodes**:
`|P(x)| ≤ (N+1)·2^N/(η^N·N!)·B` when the data is bounded by `B`. -/
theorem abs_eval_interpolate_le_of_separated
    {s : Finset ℝ} {N : ℕ} (hcard : s.card = N + 1) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {x : ℝ} (hclose : ∀ u ∈ s, |x - u| ≤ 1)
    {f : ℝ → ℝ} {B : ℝ} (hB : ∀ t ∈ s, |f t| ≤ B) :
    |(Lagrange.interpolate s id f).eval x|
      ≤ (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * B := by
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB t₀ ht₀)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  calc |∑ t ∈ s, (Polynomial.C (f t) * Lagrange.basis s id t).eval x|
      ≤ ∑ t ∈ s, |(Polynomial.C (f t) * Lagrange.basis s id t).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ s, B * (2 ^ N / (η ^ N * N.factorial)) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
        exact mul_le_mul (hB t ht)
          (abs_eval_basis_le hcard hη hsep hclose ht) (abs_nonneg _) hB0
    _ = (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * B := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring

end HTGeometry
