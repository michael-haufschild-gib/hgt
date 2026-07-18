import GaloisForLFunctions.RHTower.ConstrainedProlateSecularVector

/-!
# Head alignment of the exact constrained eigenvector with the two-mode seed

In the head plane spanned by the first two modes, the two-mode seed direction is exactly the
orthogonal complement of the constraint direction `(ℓ_0, ℓ_1)`.  The exact constrained
eigenvector `v_j = ℓ_j/(d_j − μ_0)` pairs against the constraint head by exactly the negative
of the infinite tail:

```text
ℓ_0 v_0 + ℓ_1 v_1 = − Σ_{j≥2} ℓ_j²/(d_j − μ_0),
```

because the full secular equation vanishes at the root.  The head defect is therefore bounded
by the uniform tail estimate `T/(d_2 − d_1)`, and after normalizing by the head mass and the
constraint mass the squared defect collapses at rate `(λ·d_1/(d_2 − d_1))²`:

```text
(ℓ_0v_0 + ℓ_1v_1)² / ((v_0² + v_1²)(ℓ_0² + ℓ_1²)) → 0.
```

Together with the vanishing tail fraction `Σ_{j≥2}v_j²/v_0² → 0`, this is the projective form
of the card's eigenvector convergence: the exact constrained ground direction converges to the
two-mode seed direction, head alignment and tail collapse both at the `O(λ^{-7})`-matching
rates of the Fuchs hierarchy.
-/

open Filter Set

namespace RHTower

/-- Division by a fixed positive constant is monotone. -/
private theorem div_le_div_of_le_of_pos₃ {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']
  exact h

variable {d ℓ : ℕ → ℝ}

/-- **The head–constraint pairing is exactly the negative tail.**  At the exact ground root the
first two coordinates of the eigenvector pair against `(ℓ_0, ℓ_1)` by minus the infinite
tail — the secular equation localized to the head plane. -/
theorem secularVector_head_seed_pairing (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
      + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1
      = -infiniteSecularTail d ℓ (infiniteSecularRoot d ℓ) := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have e0 : ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
      = ℓ 0 ^ 2 / (d 0 - infiniteSecularRoot d ℓ) := by
    unfold secularVector
    rw [pow_two]
    exact (mul_div_assoc _ _ _).symm
  have e1 : ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1
      = ℓ 1 ^ 2 / (d 1 - infiniteSecularRoot d ℓ) := by
    unfold secularVector
    rw [pow_two]
    exact (mul_div_assoc _ _ _).symm
  unfold infiniteSecular at hr0
  rw [e0, e1]
  linarith

/-- The absolute head defect is bounded by the uniform tail estimate. -/
theorem abs_secularVector_head_seed_pairing_le (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    |ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
      + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1|
      ≤ (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - d 1) := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have hT0 : 0 ≤ ∑' j : ℕ, ℓ (j + 2) ^ 2 := tsum_nonneg fun j => sq_nonneg _
  rw [secularVector_head_seed_pairing h01 h12 hd2 hsum hℓ0 hℓ1, abs_neg,
    abs_of_nonneg (infiniteSecularTail_nonneg hd2 (by linarith [hrmem.2]))]
  have h1 := infiniteSecularTail_le hd2 hsum
    (μ := infiniteSecularRoot d ℓ) (by linarith [hrmem.2])
  have h2 : (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - infiniteSecularRoot d ℓ)
      ≤ (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - d 1) :=
    div_le_div_of_nonneg_left hT0 (by linarith) (by linarith [hrmem.2])
  exact le_trans h1 h2

/-- **Head alignment of the exact eigenvector with the two-mode seed.**  The squared
head–constraint defect, normalized by the head mass and the constraint mass, collapses at rate
`(λ·d_1/(d_2 − d_1))²`: in the head plane the exact constrained ground direction becomes
orthogonal to `(ℓ_0, ℓ_1)`, i.e. aligns with the two-mode seed. -/
theorem secularVector_head_seed_defect_tendsto_zero
    {d ℓ : ℝ → ℕ → ℝ} {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam =>
      (ℓ lam 0 * secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0
        + ℓ lam 1 * secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1) ^ 2
      / ((secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2
            + secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1 ^ 2)
          * (ℓ lam 0 ^ 2 + ℓ lam 1 ^ 2))) atTop (nhds 0) := by
  have ha0sq : (0 : ℝ) < a0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha0))
  have hℓ0ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have hℓ1ne : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := hl1.eventually_ne ha1
  have hℓ0big : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by linarith))).mono fun x hx => hx.le
  have hbound : Tendsto (fun lam =>
      16 / a0 ^ 4 * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ 2) atTop (nhds 0) := by
    have h2 := htail.mul htail
    have h3 : Tendsto (fun lam => (lam * d lam 1 / (d lam 2 - d lam 1)) ^ 2)
        atTop (nhds 0) := by
      simpa [pow_two] using h2
    simpa using h3.const_mul (16 / a0 ^ 4)
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))) ?_ hbound
  filter_upwards [hstruct, hsum, hbessel, hℓ0ne, hℓ1ne, hℓ0big, eventually_ge_atTop (0 : ℝ)]
    with lam hst hsm hbes h0 h1 hbig hlam0
  obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, hr0, hrle⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hd1pos : 0 < d lam 1 := lt_of_le_of_lt hd0 h01
  have hd21 : 0 < d lam 2 - d lam 1 := by linarith
  have hT2 : (∑' j : ℕ, ℓ lam (j + 2) ^ 2) ≤ 2 * lam := by
    have hfull := hsm.sum_add_tsum_nat_add 2
    have hfin : 0 ≤ ∑ i ∈ Finset.range 2, ℓ lam i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith [hbes]
  -- the numerator bound
  have hnum : (ℓ lam 0 * secularVector (d lam) (ℓ lam)
        (infiniteSecularRoot (d lam) (ℓ lam)) 0
      + ℓ lam 1 * secularVector (d lam) (ℓ lam)
        (infiniteSecularRoot (d lam) (ℓ lam)) 1) ^ 2
      ≤ (2 * lam / (d lam 2 - d lam 1)) ^ 2 := by
    have habs := abs_secularVector_head_seed_pairing_le h01 h12 hd2 hsm h0 h1
    have hstep : |ℓ lam 0 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 0
        + ℓ lam 1 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 1|
        ≤ 2 * lam / (d lam 2 - d lam 1) :=
      le_trans habs (div_le_div_of_le_of_pos₃ hT2 hd21)
    calc (ℓ lam 0 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 0
        + ℓ lam 1 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 1) ^ 2
        = |ℓ lam 0 * secularVector (d lam) (ℓ lam)
            (infiniteSecularRoot (d lam) (ℓ lam)) 0
          + ℓ lam 1 * secularVector (d lam) (ℓ lam)
            (infiniteSecularRoot (d lam) (ℓ lam)) 1| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * lam / (d lam 2 - d lam 1)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hstep 2
  -- the denominator floor
  have hheadfloor : 0 < a0 ^ 2 / 2 / d lam 1 ^ 2 :=
    div_pos (half_pos ha0sq) (pow_pos hd1pos 2)
  have hhead_ge : a0 ^ 2 / 2 / d lam 1 ^ 2
      ≤ secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2 := by
    have h1'' := secularVector_head_sq_ge (ℓ := ℓ lam) hd0 hrmem
    have h2'' : a0 ^ 2 / 2 / d lam 1 ^ 2 ≤ ℓ lam 0 ^ 2 / d lam 1 ^ 2 :=
      div_le_div_of_le_of_pos₃ hbig (pow_pos hd1pos 2)
    exact le_trans h2'' h1''
  have hDfloor : 0 < a0 ^ 2 / 2 / d lam 1 ^ 2 * (a0 ^ 2 / 2) :=
    mul_pos hheadfloor (half_pos ha0sq)
  have hD_ge : a0 ^ 2 / 2 / d lam 1 ^ 2 * (a0 ^ 2 / 2)
      ≤ (secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2
          + secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1 ^ 2)
        * (ℓ lam 0 ^ 2 + ℓ lam 1 ^ 2) := by
    have hv : a0 ^ 2 / 2 / d lam 1 ^ 2
        ≤ secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2
          + secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1 ^ 2 := by
      nlinarith [hhead_ge, sq_nonneg (secularVector (d lam) (ℓ lam)
        (infiniteSecularRoot (d lam) (ℓ lam)) 1)]
    have hℓ : a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 + ℓ lam 1 ^ 2 := by
      nlinarith [hbig, sq_nonneg (ℓ lam 1)]
    exact mul_le_mul hv hℓ (half_pos ha0sq).le
      (le_trans hheadfloor.le hv)
  -- assemble
  have heq : (2 * lam / (d lam 2 - d lam 1)) ^ 2
        / (a0 ^ 2 / 2 / d lam 1 ^ 2 * (a0 ^ 2 / 2))
      = 16 / a0 ^ 4 * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ 2 := by
    field_simp
    ring
  calc (ℓ lam 0 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 0
        + ℓ lam 1 * secularVector (d lam) (ℓ lam)
          (infiniteSecularRoot (d lam) (ℓ lam)) 1) ^ 2
      / ((secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2
            + secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1 ^ 2)
          * (ℓ lam 0 ^ 2 + ℓ lam 1 ^ 2))
      ≤ (2 * lam / (d lam 2 - d lam 1)) ^ 2
        / ((secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 0 ^ 2
            + secularVector (d lam) (ℓ lam) (infiniteSecularRoot (d lam) (ℓ lam)) 1 ^ 2)
          * (ℓ lam 0 ^ 2 + ℓ lam 1 ^ 2)) :=
        div_le_div_of_le_of_pos₃ hnum (lt_of_lt_of_le hDfloor hD_ge)
    _ ≤ (2 * lam / (d lam 2 - d lam 1)) ^ 2
        / (a0 ^ 2 / 2 / d lam 1 ^ 2 * (a0 ^ 2 / 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hDfloor hD_ge
    _ = 16 / a0 ^ 4 * (lam * d lam 1 / (d lam 2 - d lam 1)) ^ 2 := heq

end RHTower
