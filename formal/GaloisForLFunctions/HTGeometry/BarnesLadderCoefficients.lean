import GaloisForLFunctions.HTGeometry.BarnesLadderOrderOne

/-!
# The ladder coefficients are summable

The telescoping factor of the ladder correction has a closed form,

```text
1/w_{n+e_j} - 1/w_n = -ω_j / (w_n w_{n+e_j}),
```

so each coefficient of the correction, obtained by dividing that factor by a product of `N-1`
further cone values, is `ω_j` over a product of `N+1` cone values.  Both cone values are at least a
fixed multiple of the total degree, while the ambient cone value is at most a fixed multiple of it,
so each coefficient is dominated by the inverse `(N+1)`-st power of the ambient cone value — the
critical exponent, which is summable.

These are the constants that appear when the correction series is expanded in powers of the
argument.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## Closed form of the telescoping factor -/

omit [Nonempty ι] in
theorem conePeriod_inv_sub_inv (ω : ι → ℂ) (n : ι → ℕ) (j : ι)
    (hw : conePeriod ω n ≠ 0) (hw' : conePeriod ω (n + Pi.single j 1) ≠ 0) :
    (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹ =
      -(ω j) / (conePeriod ω n * conePeriod ω (n + Pi.single j 1)) := by
  have hshift : conePeriod ω (n + Pi.single j 1) = conePeriod ω n + ω j :=
    conePeriod_add_single ω n j
  rw [hshift] at hw' ⊢
  field_simp
  ring

/-! ## An upper bound for the cone value -/

omit [Nonempty ι] [DecidableEq ι] in
theorem norm_conePeriod_le (ω : ι → ℂ) (n : ι → ℕ) :
    ‖conePeriod ω n‖ ≤ (∑ i, ‖ω i‖) * ∑ i, (n i : ℝ) := by
  classical
  calc ‖conePeriod ω n‖ ≤ ∑ i, ‖(n i : ℂ) * ω i‖ := norm_sum_le _ _
    _ = ∑ i, (n i : ℝ) * ‖ω i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ ∑ i, (∑ k, (n k : ℝ)) * ‖ω i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => (n k : ℝ))
          (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    _ = (∑ i, ‖ω i‖) * ∑ i, (n i : ℝ) := by
        rw [← Finset.mul_sum]
        ring

omit [DecidableEq ι] in
theorem sum_norm_pos (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) : 0 < ∑ i, ‖ω i‖ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hpos : 0 < ‖ω i₀‖ := by
    refine norm_pos_iff.mpr fun hcon => ?_
    have := hω i₀
    rw [hcon] at this
    simp at this
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (f := fun i => ‖ω i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ i₀))

/-! ## The coefficients and their bound -/

/-- The coefficient attached to one exponent vector and one split of the genus. -/
def barnesLadderCoefficient (ω : ι → ℂ) (j : ι) (k : ℕ) (n : ι → ℕ) : ℂ :=
  if n = 0 then 0
  else -(ω j) / (conePeriod ω n ^ (k + 1) *
    conePeriod ω (n + Pi.single j 1) ^ (Fintype.card ι - k))

theorem norm_barnesLadderCoefficient_le (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι)
    {k : ℕ} (hk : k < Fintype.card ι) {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ i, δ ≤ (ω i).im)
    {n : ι → ℕ} (hn : n ≠ 0) :
    ‖barnesLadderCoefficient ω j k n‖ ≤
      ‖ω j‖ * ((∑ i, ‖ω i‖) / δ) ^ (Fintype.card ι + 1) *
        (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ := by
  classical
  set N : ℕ := Fintype.card ι with hN
  set s : ℝ := ∑ i, (n i : ℝ) with hs
  set M : ℝ := ∑ i, ‖ω i‖ with hM
  have hMpos : 0 < M := sum_norm_pos ω hω
  have hwpos : 0 < ‖conePeriod ω n‖ := norm_pos_iff.mpr (conePeriod_ne_zero ω hω hn)
  have hlow : δ * s ≤ ‖conePeriod ω n‖ := mul_sum_le_norm_conePeriod ω hδ n
  have hlow' : δ * s ≤ ‖conePeriod ω (n + Pi.single j 1)‖ := by
    refine le_trans ?_ (mul_sum_le_norm_conePeriod ω hδ (n + Pi.single j 1))
    refine mul_le_mul_of_nonneg_left ?_ hδpos.le
    refine Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast Nat.le_add_right (n i) _
  have hup : ‖conePeriod ω n‖ ≤ M * s := norm_conePeriod_le ω n
  have hsnn : (0 : ℝ) ≤ s := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hδsnn : (0 : ℝ) ≤ δ * s := by positivity
  have hstep : δ / M * ‖conePeriod ω n‖ ≤ δ * s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
    nlinarith
  have hkey : (δ / M) ^ (N + 1) * ‖conePeriod ω n‖ ^ (N + 1) ≤
      ‖conePeriod ω n‖ ^ (k + 1) * ‖conePeriod ω (n + Pi.single j 1)‖ ^ (N - k) := by
    calc (δ / M) ^ (N + 1) * ‖conePeriod ω n‖ ^ (N + 1)
        = (δ / M * ‖conePeriod ω n‖) ^ (N + 1) := by rw [mul_pow]
      _ ≤ (δ * s) ^ (N + 1) := pow_le_pow_left₀ (by positivity) hstep _
      _ = (δ * s) ^ (k + 1) * (δ * s) ^ (N - k) := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ ‖conePeriod ω n‖ ^ (k + 1) * ‖conePeriod ω (n + Pi.single j 1)‖ ^ (N - k) :=
          mul_le_mul (pow_le_pow_left₀ hδsnn hlow _) (pow_le_pow_left₀ hδsnn hlow' _)
            (by positivity) (by positivity)
  have hPpos : 0 < ‖conePeriod ω n‖ ^ (k + 1) *
      ‖conePeriod ω (n + Pi.single j 1)‖ ^ (N - k) := by
    have hw'pos : 0 < ‖conePeriod ω (n + Pi.single j 1)‖ :=
      norm_pos_iff.mpr (conePeriod_ne_zero ω hω (add_single_ne_zero n j))
    positivity
  rw [barnesLadderCoefficient, if_neg hn, norm_div, norm_neg, norm_mul, norm_pow, norm_pow,
    ← div_eq_mul_inv, div_le_div_iff₀ hPpos (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hkey
    (by positivity : (0 : ℝ) ≤ ‖ω j‖ * (M / δ) ^ (N + 1))
  calc ‖ω j‖ * ‖conePeriod ω n‖ ^ (N + 1)
      = ‖ω j‖ * (M / δ) ^ (N + 1) *
        ((δ / M) ^ (N + 1) * ‖conePeriod ω n‖ ^ (N + 1)) := by
        rw [mul_assoc, ← mul_assoc ((M / δ) ^ (N + 1)), ← mul_pow]
        rw [div_mul_div_comm, mul_comm M δ, div_self (by positivity), one_pow, one_mul]
    _ ≤ ‖ω j‖ * (M / δ) ^ (N + 1) *
        (‖conePeriod ω n‖ ^ (k + 1) * ‖conePeriod ω (n + Pi.single j 1)‖ ^ (N - k)) := hmul

/-! ## Summability -/

theorem summable_barnesLadderCoefficient (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι)
    {k : ℕ} (hk : k < Fintype.card ι) :
    Summable fun n : ι → ℕ => barnesLadderCoefficient ω j k n := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_im ω hω
  refine Summable.of_norm ?_
  exact summable_of_conePeriod_majorant ω hω (fun n => norm_nonneg _)
    (‖ω j‖ * ((∑ i, ‖ω i‖) / δ) ^ (Fintype.card ι + 1)) 0
    fun n hn _ => norm_barnesLadderCoefficient_le ω hω j hk hδpos hδ hn

end

end GaloisForLFunctions
