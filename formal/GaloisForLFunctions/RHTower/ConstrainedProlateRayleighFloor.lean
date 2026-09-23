import GaloisForLFunctions.RHTower.ConstrainedProlateSecularRayleigh

/-!
# The secular root is the exact Rayleigh floor of the constrained diagonal form

For a diagonal sequence `d` with a strict two-step head `d_0 < d_1 < d_2 ≤ d_{j+2}` and a
square-summable constraint sequence `ℓ` with `ℓ_0, ℓ_1 ≠ 0`, every square-summable coordinate
vector `x` annihilated by the constraint satisfies

```text
μ₀ ∑ x_j²  ≤  ∑ d_j x_j² ,      μ₀ = infiniteSecularRoot d ℓ ,
```

and equality holds at the secular vector.  The mechanism is Cauchy–Schwarz against the weights
`ℓ_j²/(d_j − μ₀)` on the indices `j ≥ 1`, whose total is exactly `ℓ_0²/(μ₀ − d_0)` because the
secular function vanishes at `μ₀`; the constraint then converts the single negative head term into
a quantity dominated by the positive tail.
-/

noncomputable section

open Filter Set

namespace RHTower

variable {d ℓ : ℕ → ℝ}

/-- Two square-summable real sequences, of arbitrary sign, have summable product. -/
theorem summable_mul_of_sq_summable {f g : ℕ → ℝ}
    (hf : Summable fun j => f j ^ (2 : ℕ)) (hg : Summable fun j => g j ^ (2 : ℕ)) :
    Summable fun j : ℕ => f j * g j := by
  refine Summable.of_abs ?_
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_) ((hf.add hg).div_const 2)
  rw [abs_mul]
  nlinarith [sq_abs (f j), sq_abs (g j), sq_nonneg (|f j| - |g j|)]

/-- Beyond the head index the diagonal strictly exceeds the ground root. -/
theorem infiniteSecularRoot_lt_succ (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) (j : ℕ) :
    infiniteSecularRoot d ℓ < d (j + 1) := by
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  match j with
  | 0 => exact hrmem.2
  | (m + 1) => have := hd2 m; linarith [hrmem.2]

/-- **The constrained Rayleigh floor.**  On the constraint hyperplane the diagonal quadratic form
is bounded below by the ground secular root times the squared norm. -/
theorem tsum_mul_sq_ge_infiniteSecularRoot (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0)
    {x : ℕ → ℝ} (hx2 : Summable fun j => x j ^ (2 : ℕ))
    (hdx : Summable fun j => d j * x j ^ (2 : ℕ))
    (hcon : (∑' j : ℕ, ℓ j * x j) = 0) :
    infiniteSecularRoot d ℓ * ∑' j : ℕ, x j ^ (2 : ℕ) ≤ ∑' j : ℕ, d j * x j ^ (2 : ℕ) := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  set μ := infiniteSecularRoot d ℓ with hμdef
  have hμ0 : d 0 < μ := hrmem.1
  have hμ1 : μ < d 1 := hrmem.2
  have hμ2 : μ < d 2 := lt_trans hμ1 h12
  have hpos : ∀ j : ℕ, 0 < d (j + 1) - μ := by
    intro j
    match j with
    | 0 => linarith
    | (m + 1) => have := hd2 m; linarith
  set w : ℕ → ℝ := fun j => ℓ j ^ (2 : ℕ) / (d j - μ) with hwdef
  have hallw : Summable w := by
    refine (summable_nat_add_iff (f := w) 2).mp ?_
    exact (summable_infiniteSecularTail hd2 hsum hμ2).congr fun j => rfl
  have hAsum : Summable (fun j : ℕ => w (j + 1)) := (summable_nat_add_iff 1).mpr hallw
  set A := ∑' j : ℕ, w (j + 1) with hAdef
  have hzero : ∑' j : ℕ, w j = 0 := by
    rw [← infiniteSecular_eq_tsum hallw]
    exact hr0
  have hAval : A = ℓ 0 ^ (2 : ℕ) / (μ - d 0) := by
    have hsplit : ∑' j : ℕ, w j = w 0 + A := hallw.tsum_eq_zero_add
    have h1 : ℓ 0 ^ (2 : ℕ) / (d 0 - μ) + A = 0 := by
      rw [hAdef]
      rw [hzero] at hsplit
      simpa [hwdef] using hsplit.symm
    have h2 : ℓ 0 ^ (2 : ℕ) / (d 0 - μ) = -(ℓ 0 ^ (2 : ℕ) / (μ - d 0)) := by
      rw [← div_neg, neg_sub]
    rw [h2] at h1
    linarith
  have hAnonneg : 0 ≤ A :=
    tsum_nonneg fun j => div_nonneg (sq_nonneg _) (le_of_lt (hpos j))
  set y : ℕ → ℝ := fun j => (d j - μ) * x j ^ (2 : ℕ) with hydef
  have hySummable : Summable y :=
    (hdx.sub (hx2.mul_left μ)).congr fun j => by simp [hydef]; ring
  have hSsum : Summable (fun j : ℕ => y (j + 1)) := (summable_nat_add_iff 1).mpr hySummable
  set S := ∑' j : ℕ, y (j + 1) with hSdef
  have hSnonneg : 0 ≤ S :=
    tsum_nonneg fun j => mul_nonneg (le_of_lt (hpos j)) (sq_nonneg _)
  have hlx : Summable fun j : ℕ => ℓ j * x j := summable_mul_of_sq_summable hsum hx2
  have hlxs : Summable fun j : ℕ => ℓ (j + 1) * x (j + 1) := (summable_nat_add_iff 1).mpr hlx
  set P := ∑' j : ℕ, ℓ (j + 1) * x (j + 1) with hPdef
  have hPval : P = -(ℓ 0 * x 0) := by
    have hsp : (∑' j : ℕ, ℓ j * x j) = ℓ 0 * x 0 + P := hlx.tsum_eq_zero_add
    rw [hcon] at hsp
    linarith
  have hCS : P ^ (2 : ℕ) ≤ A * S := by
    have hfin : ∀ s : Finset ℕ, (∑ j ∈ s, ℓ (j + 1) * x (j + 1)) ^ (2 : ℕ) ≤ A * S := by
      intro s
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun j => ℓ (j + 1) / Real.sqrt (d (j + 1) - μ))
        (fun j => Real.sqrt (d (j + 1) - μ) * x (j + 1))
      have he1 : ∀ j : ℕ,
          (ℓ (j + 1) / Real.sqrt (d (j + 1) - μ)) * (Real.sqrt (d (j + 1) - μ) * x (j + 1))
            = ℓ (j + 1) * x (j + 1) := by
        intro j
        have hs : Real.sqrt (d (j + 1) - μ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos j))
        field_simp
      have he2 : ∀ j : ℕ, (ℓ (j + 1) / Real.sqrt (d (j + 1) - μ)) ^ (2 : ℕ) = w (j + 1) := by
        intro j
        rw [div_pow, Real.sq_sqrt (le_of_lt (hpos j))]
      have he3 : ∀ j : ℕ, (Real.sqrt (d (j + 1) - μ) * x (j + 1)) ^ (2 : ℕ) = y (j + 1) := by
        intro j
        rw [mul_pow, Real.sq_sqrt (le_of_lt (hpos j))]
      simp only [he1, he2, he3] at hcs
      have hA1 : ∑ j ∈ s, w (j + 1) ≤ A :=
        hAsum.sum_le_tsum s fun j _ => div_nonneg (sq_nonneg _) (le_of_lt (hpos j))
      have hS1 : ∑ j ∈ s, y (j + 1) ≤ S :=
        hSsum.sum_le_tsum s fun j _ => mul_nonneg (le_of_lt (hpos j)) (sq_nonneg _)
      have hSs : 0 ≤ ∑ j ∈ s, y (j + 1) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (hpos j)) (sq_nonneg _)
      exact le_trans hcs (mul_le_mul hA1 hS1 hSs hAnonneg)
    have htend : Filter.Tendsto
        (fun s : Finset ℕ => ∑ j ∈ s, ℓ (j + 1) * x (j + 1)) atTop (nhds P) := hlxs.hasSum
    exact le_of_tendsto (htend.pow 2) (Filter.Eventually.of_forall hfin)
  have hl0 : 0 < ℓ 0 ^ (2 : ℕ) := by positivity
  have hmd : 0 < μ - d 0 := by linarith
  have hkey : (μ - d 0) * x 0 ^ (2 : ℕ) ≤ S := by
    have hstep : ℓ 0 ^ (2 : ℕ) * x 0 ^ (2 : ℕ) ≤ (ℓ 0 ^ (2 : ℕ) / (μ - d 0)) * S := by
      rw [← hAval]
      calc ℓ 0 ^ (2 : ℕ) * x 0 ^ (2 : ℕ) = P ^ (2 : ℕ) := by rw [hPval]; ring
        _ ≤ A * S := hCS
    rw [div_mul_eq_mul_div, le_div_iff₀ hmd] at hstep
    have h3 : ℓ 0 ^ (2 : ℕ) * ((μ - d 0) * x 0 ^ (2 : ℕ)) ≤ ℓ 0 ^ (2 : ℕ) * S := by nlinarith [hstep]
    exact le_of_mul_le_mul_left h3 hl0
  have hsplitY : ∑' j : ℕ, y j = y 0 + S := hySummable.tsum_eq_zero_add
  have hYnonneg : 0 ≤ ∑' j : ℕ, y j := by
    have hy0 : y 0 = -((μ - d 0) * x 0 ^ (2 : ℕ)) := by simp [hydef]; ring
    rw [hsplitY, hy0]
    linarith
  have hYval : ∑' j : ℕ, y j = (∑' j : ℕ, d j * x j ^ (2 : ℕ)) - μ * ∑' j : ℕ, x j ^ (2 : ℕ) := by
    have hcongr : ∑' j : ℕ, y j = ∑' j : ℕ, (d j * x j ^ (2 : ℕ) - μ * x j ^ (2 : ℕ)) :=
      tsum_congr fun j => by simp [hydef]; ring
    rw [hcongr, Summable.tsum_sub hdx (hx2.mul_left μ), tsum_mul_left]
  linarith [hYnonneg, hYval]

end RHTower

end
