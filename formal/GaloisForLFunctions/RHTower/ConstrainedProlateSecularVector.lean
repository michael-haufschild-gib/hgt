import GaloisForLFunctions.RHTower.ConstrainedProlateInfiniteSecular

/-!
# The exact constrained eigenvector: coordinates, constraint membership, and two-mode collapse

A constrained eigenvector of the diagonal leakage operator with eigenvalue `μ` off the diagonal
spectrum has coordinates proportional to

```text
v_j = ℓ_j / (d_j − μ).
```

This module develops that coordinate vector at the exact infinite-dimensional constrained ground
root `μ_0`.  Four facts are proved:

* the coordinate eigen-equation `d_j·v_j = μ·v_j + ℓ_j` (the resolvent form of the constrained
  eigenvalue problem);
* the vanishing-integral membership `Σ_j ℓ_j v_j = 0` at `μ_0` — the secular equation *is* the
  constraint, so the exact eigenvector lies in the constrained hyperplane;
* the tail/head weight bounds: the squared tail mass is at most `T/(d_2 − μ)²` while the zeroth
  squared coordinate is at least `ℓ_0²/d_1²`;
* at the two-mode trial value the head pair `(v_0, v_1)` is exactly orthogonal to `(ℓ_0, ℓ_1)` —
  the direction of the two-mode seed.

Under the aperture-family hypotheses of the infinite secular transfer (Bessel bound, Fuchs-type
scale separations, coordinate limits) the tail-to-head mass ratio of the exact constrained ground
vector collapses at rate `(λ·d_1/(d_2 − d_1))²`:

```text
Σ_{j≥2} v_j² / v_0² → 0,
```

so the exact optimizer is asymptotically supported on its first two coordinates — the
quantitative "the constrained ground vector is asymptotically two-mode" step.
-/

open Filter Set

namespace RHTower

noncomputable section

/-- The coordinate vector of a constrained eigenvector at spectral parameter `μ`. -/
def secularVector (d ℓ : ℕ → ℝ) (μ : ℝ) (j : ℕ) : ℝ := ℓ j / (d j - μ)

variable {d ℓ : ℕ → ℝ}

/-- The coordinate eigen-equation: away from the poles, `d_j v_j = μ v_j + ℓ_j`, i.e. the
diagonal operator moves the eigenvector by `μ` up to a multiple of the constraint vector. -/
theorem secularVector_eigen {μ : ℝ} (j : ℕ) (hne : d j - μ ≠ 0) :
    d j * secularVector d ℓ μ j = μ * secularVector d ℓ μ j + ℓ j := by
  unfold secularVector
  field_simp
  ring

/-- The squared coordinates from index `2` on are summable below the uniform floor. -/
theorem summable_secularVector_sq_tail (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) {μ : ℝ} (hμ : μ < d 2) :
    Summable fun j : ℕ => secularVector d ℓ μ (j + 2) ^ (2 : ℕ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + 2) ^ (2 : ℕ) := (summable_nat_add_iff 2).mpr hsum
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (hsum2.div_const ((d 2 - μ) ^ (2 : ℕ)))
  unfold secularVector
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith [hd2 j]) 2)

/-- **Squared tail mass of the exact eigenvector** (the uniform tail weight estimate): below the
uniform floor, `Σ_{j≥2} v_j² ≤ T/(d_2 − μ)²`. -/
theorem secularVector_sq_tail_le (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ (2 : ℕ)) {μ : ℝ} (hμ : μ < d 2) :
    (∑' j : ℕ, secularVector d ℓ μ (j + 2) ^ (2 : ℕ))
      ≤ (∑' j : ℕ, ℓ (j + 2) ^ (2 : ℕ)) / (d 2 - μ) ^ (2 : ℕ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + 2) ^ (2 : ℕ) := (summable_nat_add_iff 2).mpr hsum
  rw [← tsum_div_const]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_secularVector_sq_tail hd2 hsum hμ)
    (hsum2.div_const _)
  unfold secularVector
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith [hd2 j]) 2)

/-- **Head weight floor**: inside the first spectral gap, with `d_0 ≥ 0`, the zeroth squared
coordinate of the eigenvector is at least `ℓ_0²/d_1²`. -/
theorem secularVector_head_sq_ge (hd0 : 0 ≤ d 0) {μ : ℝ} (hμ : μ ∈ Set.Ioo (d 0) (d 1)) :
    ℓ 0 ^ (2 : ℕ) / d 1 ^ (2 : ℕ) ≤ secularVector d ℓ μ 0 ^ (2 : ℕ) := by
  unfold secularVector
  rw [div_pow]
  refine div_le_div_of_nonneg_left (sq_nonneg _) ?_ ?_
  · exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (ne_of_lt (by linarith [hμ.1] : d 0 - μ < 0))))
  · rw [show (d 0 - μ) ^ (2 : ℕ) = (μ - d 0) ^ (2 : ℕ) by ring]
    exact pow_le_pow_left₀ (by linarith [hμ.1]) (by linarith [hμ.2]) 2

/-- **The exact constrained ground vector satisfies the vanishing-integral constraint**:
`Σ_j ℓ_j v_j = 0` at the ground root — the secular equation is exactly the statement that the
eigenvector lies in the constrained hyperplane. -/
theorem secularVector_constraint (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    ∑' j : ℕ, ℓ j * secularVector d ℓ (infiniteSecularRoot d ℓ) j = 0 := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have hμ2 : infiniteSecularRoot d ℓ < d 2 := by linarith [hrmem.2]
  have htails := summable_infiniteSecularTail hd2 hsum hμ2
  have hall : Summable (fun j : ℕ => ℓ j ^ (2 : ℕ) / (d j - infiniteSecularRoot d ℓ)) :=
    (summable_nat_add_iff 2).mp htails
  have hcongr : ∀ j : ℕ, ℓ j * secularVector d ℓ (infiniteSecularRoot d ℓ) j
      = ℓ j ^ (2 : ℕ) / (d j - infiniteSecularRoot d ℓ) := by
    intro j
    unfold secularVector
    rw [pow_two]
    exact (mul_div_assoc _ _ _).symm
  calc ∑' j : ℕ, ℓ j * secularVector d ℓ (infiniteSecularRoot d ℓ) j
      = ∑' j : ℕ, ℓ j ^ (2 : ℕ) / (d j - infiniteSecularRoot d ℓ) := tsum_congr hcongr
    _ = infiniteSecular d ℓ (infiniteSecularRoot d ℓ) := (infiniteSecular_eq_tsum hall).symm
    _ = 0 := hr0

/-- **At the two-mode trial value the head pair is the two-mode seed direction**: `(v_0, v_1)`
is exactly orthogonal to `(ℓ_0, ℓ_1)`, hence proportional to `(−ℓ_1, ℓ_0)`. -/
theorem secularVector_twoMode_head_orthogonal (h01 : d 0 < d 1)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    ℓ 0 * secularVector d ℓ (GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)) 0
      + ℓ 1 * secularVector d ℓ
          (GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)) 1 = 0 := by
  have h := GaloisForLFunctions.twoModeSecular_eq_zero h01 hℓ0 hℓ1
  unfold secularVector
  have e0 : ℓ 0 * (ℓ 0 / (d 0 - GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)))
      = ℓ 0 ^ (2 : ℕ) / (d 0 - GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)) := by
    rw [pow_two]
    exact (mul_div_assoc _ _ _).symm
  have e1 : ℓ 1 * (ℓ 1 / (d 1 - GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)))
      = ℓ 1 ^ (2 : ℕ) / (d 1 - GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)) := by
    rw [pow_two]
    exact (mul_div_assoc _ _ _).symm
  rw [e0, e1]
  exact h

end

/-! ## The aperture-family collapse of the tail fraction -/

/-- **The exact constrained ground vector is asymptotically two-mode.**  Under the transfer
hypotheses, the squared-tail to squared-head mass ratio of the exact eigenvector at the exact
ground root collapses to zero at rate `(λ·d_1/(d_2 − d_1))²`. -/
theorem secularVector_tail_fraction_tendsto_zero
    {d ℓ : ℝ → ℕ → ℝ} {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam)
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam =>
      (∑' j : ℕ, secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) (j + 2) ^ (2 : ℕ))
        / secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ (2 : ℕ))
      atTop (nhds 0) := by
  have ha0sq : (0 : ℝ) < a0 ^ (2 : ℕ) := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha0))
  have hℓ0ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have hℓ1ne : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := hl1.eventually_ne ha1
  have hℓ0big : ∀ᶠ lam in atTop, a0 ^ (2 : ℕ) / 2 ≤ ℓ lam 0 ^ (2 : ℕ) :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by linarith))).mono fun x hx => hx.le
  have hbound : Tendsto (fun lam =>
      4 / a0 ^ (2 : ℕ) * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ (2 : ℕ)) atTop (nhds 0) := by
    have h2 := htail.mul htail
    have h3 : Tendsto (fun lam => (lam * d lam 1 / (d lam 2 - d lam 1)) ^ (2 : ℕ))
        atTop (nhds 0) := by
      simpa [pow_two] using h2
    simpa using h3.const_mul (4 / a0 ^ (2 : ℕ))
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (tsum_nonneg fun j => sq_nonneg _) (sq_nonneg _)) ?_ hbound
  filter_upwards [hstruct, hsum, hbessel, hℓ0ne, hℓ1ne, hℓ0big, eventually_ge_atTop (1 : ℝ)]
    with lam hst hsm hbes h0 h1 hbig hl1'
  obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, hr0, hrle⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1'
  have hd1pos : 0 < d lam 1 := lt_of_le_of_lt hd0 h01
  have hd21 : 0 < d lam 2 - d lam 1 := by linarith
  have hT0 : 0 ≤ ∑' j : ℕ, ℓ lam (j + 2) ^ (2 : ℕ) := tsum_nonneg fun j => sq_nonneg _
  have hT2 : (∑' j : ℕ, ℓ lam (j + 2) ^ (2 : ℕ)) ≤ 2 * lam := by
    have hfull := hsm.sum_add_tsum_nat_add 2
    have hfin : 0 ≤ ∑ i ∈ Finset.range 2, ℓ lam i ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith [hbes]
  have htail_le : (∑' j : ℕ, secularVector (d lam) (ℓ lam)
        (infiniteSecularRoot (d lam) (ℓ lam)) (j + 2) ^ (2 : ℕ))
      ≤ 2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ) := by
    have h1' := secularVector_sq_tail_le hd2 hsm
      (μ := infiniteSecularRoot (d lam) (ℓ lam)) (by linarith [hrmem.2])
    have h2' : (∑' j : ℕ, ℓ lam (j + 2) ^ (2 : ℕ))
          / (d lam 2 - infiniteSecularRoot (d lam) (ℓ lam)) ^ (2 : ℕ)
        ≤ (∑' j : ℕ, ℓ lam (j + 2) ^ (2 : ℕ)) / (d lam 2 - d lam 1) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_left hT0 (pow_pos hd21 2)
        (pow_le_pow_left₀ hd21.le (by linarith [hrmem.2]) 2)
    have h3' : (∑' j : ℕ, ℓ lam (j + 2) ^ (2 : ℕ)) / (d lam 2 - d lam 1) ^ (2 : ℕ)
        ≤ 2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ) :=
      div_le_div_of_le_of_pos hT2 (pow_pos hd21 2)
    exact le_trans h1' (le_trans h2' h3')
  have hheadfloor : 0 < a0 ^ (2 : ℕ) / 2 / d lam 1 ^ (2 : ℕ) :=
    div_pos (half_pos ha0sq) (pow_pos hd1pos 2)
  have hhead_ge : a0 ^ (2 : ℕ) / 2 / d lam 1 ^ (2 : ℕ)
      ≤ secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ (2 : ℕ) := by
    have h1'' := secularVector_head_sq_ge (ℓ := ℓ lam) hd0 hrmem
    have h2'' : a0 ^ (2 : ℕ) / 2 / d lam 1 ^ (2 : ℕ) ≤ ℓ lam 0 ^ (2 : ℕ) / d lam 1 ^ (2 : ℕ) :=
      div_le_div_of_le_of_pos hbig (pow_pos hd1pos 2)
    exact le_trans h2'' h1''
  have hheadpos : 0 < secularVector (d lam) (ℓ lam)
      (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ (2 : ℕ) := lt_of_lt_of_le hheadfloor hhead_ge
  have hnn : 0 ≤ 2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ) :=
    div_nonneg (by linarith) (sq_nonneg _)
  have heqA : 2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ) / (a0 ^ (2 : ℕ) / 2 / d lam 1 ^ (2 : ℕ))
      = 4 * lam * d lam 1 ^ (2 : ℕ) / (a0 ^ (2 : ℕ) * (d lam 2 - d lam 1) ^ (2 : ℕ)) := by
    field_simp
    ring
  have heqB : 4 / a0 ^ (2 : ℕ) * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ (2 : ℕ)
      = 4 * lam ^ (2 : ℕ) * d lam 1 ^ (2 : ℕ) / (a0 ^ (2 : ℕ) * (d lam 2 - d lam 1) ^ (2 : ℕ)) := by
    field_simp
  calc (∑' j : ℕ, secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) (j + 2) ^ (2 : ℕ))
        / secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ (2 : ℕ)
      ≤ (2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ))
        / secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ (2 : ℕ) :=
        div_le_div_of_le_of_pos htail_le hheadpos
    _ ≤ (2 * lam / (d lam 2 - d lam 1) ^ (2 : ℕ)) / (a0 ^ (2 : ℕ) / 2 / d lam 1 ^ (2 : ℕ)) :=
        div_le_div_of_nonneg_left hnn hheadfloor hhead_ge
    _ = 4 * lam * d lam 1 ^ (2 : ℕ) / (a0 ^ (2 : ℕ) * (d lam 2 - d lam 1) ^ (2 : ℕ)) := heqA
    _ ≤ 4 * lam ^ (2 : ℕ) * d lam 1 ^ (2 : ℕ) / (a0 ^ (2 : ℕ) * (d lam 2 - d lam 1) ^ (2 : ℕ)) := by
        refine div_le_div_of_le_of_pos ?_ (mul_pos ha0sq (pow_pos hd21 2))
        have hle : 4 * lam ≤ 4 * lam ^ (2 : ℕ) := by nlinarith
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = 4 / a0 ^ (2 : ℕ) * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ (2 : ℕ) := heqB.symm

end RHTower
