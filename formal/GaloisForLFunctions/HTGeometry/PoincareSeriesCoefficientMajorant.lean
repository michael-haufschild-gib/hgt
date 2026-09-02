import GaloisForLFunctions.HTGeometry.PoincareSeriesKloostermanPhase

/-!
# The majorant for the Fourier expansion of the Poincaré series

The terms produced by the exponential expansion and the Lipschitz sums are, in absolute value,

  `(2πm/c)^j/j! · c^{-(k+j)} · (2π)^{k+j}/(k+j-1)! · n^{k+j-1} e^{-2πyn}`,

indexed by `(c, u, j, n)` with `u` ranging over the `φ(c) ≤ c` units mod `c`.  Using
`n^s e^{-2πyn} ≤ s! (πy)^{-s} e^{-πyn}` they are dominated by the product majorant

  `(2π)^k (πy)^{1-k} c^{-k} · (4πm/y)^j/j! · e^{-πyn}`,

which is summable over `(Σ_{c ≥ 1} (ℤ/c)ˣ × ℕ) × ℕ` as soon as `k ≥ 3`.
-/

open Complex
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The index type `(c, u, j)`. -/
abbrev CoefIndex := Σ c : ℕ+, (ZMod c)ˣ × ℕ

/-- The product majorant, with `k = k' + 1`. -/
def coefMajorant (k' : ℕ) (m : ℕ) (y : ℝ) (p : CoefIndex) (n : ℕ) : ℝ :=
  ((2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ * (((p.1 : ℕ) : ℝ) ^ (k' + 1))⁻¹ *
    ((4 * π * m / y) ^ p.2.2 / (p.2.2.factorial : ℝ))) * Real.exp (-(π * y) * n)

theorem coefMajorant_nonneg (k' m : ℕ) {y : ℝ} (hy : 0 < y) (p : CoefIndex) (n : ℕ) :
    0 ≤ coefMajorant k' m y p n := by
  unfold coefMajorant
  positivity

/-! ## The pointwise bound -/

/-- `n^s e^{-2πyn} ≤ s! (πy)^{-s} e^{-πyn}`. -/
theorem pow_mul_exp_le {y : ℝ} (hy : 0 < y) (s n : ℕ) :
    (n : ℝ) ^ s * Real.exp (-(2 * π * y) * n)
      ≤ (s.factorial : ℝ) * ((π * y) ^ s)⁻¹ * Real.exp (-(π * y) * n) := by
  have hpy : 0 < π * y := by positivity
  have h := Real.pow_div_factorial_le_exp (π * y * n) (by positivity) s
  have hs : (0 : ℝ) < s.factorial := by positivity
  rw [div_le_iff₀ hs, mul_pow] at h
  -- h : (πy)^s * n^s ≤ exp(πyn) * s!
  have h2 : (n : ℝ) ^ s ≤ (s.factorial : ℝ) * ((π * y) ^ s)⁻¹ * Real.exp (π * y * n) := by
    rw [mul_comm ((π * y) ^ s) _] at h
    have hp : (0 : ℝ) < (π * y) ^ s := pow_pos hpy s
    calc (n : ℝ) ^ s = (n : ℝ) ^ s * (π * y) ^ s * ((π * y) ^ s)⁻¹ := by
          field_simp
      _ ≤ Real.exp (π * y * n) * s.factorial * ((π * y) ^ s)⁻¹ := by gcongr
      _ = (s.factorial : ℝ) * ((π * y) ^ s)⁻¹ * Real.exp (π * y * n) := by ring
  calc (n : ℝ) ^ s * Real.exp (-(2 * π * y) * n)
      ≤ (s.factorial : ℝ) * ((π * y) ^ s)⁻¹ * Real.exp (π * y * n) * Real.exp (-(2 * π * y) * n) := by
        gcongr
    _ = (s.factorial : ℝ) * ((π * y) ^ s)⁻¹ * Real.exp (-(π * y) * n) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The pointwise bound** of the expansion term by the majorant. -/
theorem term_le_coefMajorant {k' : ℕ} {y : ℝ} (hy : 0 < y) (m : ℕ) (p : CoefIndex) (n : ℕ) :
    (2 * π * m / (p.1 : ℝ)) ^ p.2.2 / (p.2.2.factorial : ℝ) * (((p.1 : ℕ) : ℝ) ^ (k' + 1 + p.2.2))⁻¹ *
        ((2 * π) ^ (k' + 1 + p.2.2) / ((k' + p.2.2).factorial : ℝ)) *
        ((n : ℝ) ^ (k' + p.2.2) * Real.exp (-(2 * π * y) * n))
      ≤ coefMajorant k' m y p n := by
  obtain ⟨c, u, j⟩ := p
  simp only
  have hc : (0 : ℝ) < (c : ℕ) := by exact_mod_cast c.pos
  have hc1 : (1 : ℝ) ≤ (c : ℕ) := by exact_mod_cast Nat.succ_le_of_lt c.pos
  have hc' : ((c : ℕ) : ℝ) ≠ 0 := hc.ne'
  have hy' : y ≠ 0 := hy.ne'
  have hpy : 0 < π * y := by positivity
  have hA : 0 ≤ (2 * π * m / (c : ℝ)) ^ j / (j.factorial : ℝ) * (((c : ℕ) : ℝ) ^ (k' + 1 + j))⁻¹ *
      ((2 * π) ^ (k' + 1 + j) / ((k' + j).factorial : ℝ)) := by positivity
  calc (2 * π * m / (c : ℝ)) ^ j / (j.factorial : ℝ) * (((c : ℕ) : ℝ) ^ (k' + 1 + j))⁻¹ *
        ((2 * π) ^ (k' + 1 + j) / ((k' + j).factorial : ℝ)) *
        ((n : ℝ) ^ (k' + j) * Real.exp (-(2 * π * y) * n))
      ≤ (2 * π * m / (c : ℝ)) ^ j / (j.factorial : ℝ) * (((c : ℕ) : ℝ) ^ (k' + 1 + j))⁻¹ *
        ((2 * π) ^ (k' + 1 + j) / ((k' + j).factorial : ℝ)) *
        (((k' + j).factorial : ℝ) * ((π * y) ^ (k' + j))⁻¹ * Real.exp (-(π * y) * n)) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_le hy (k' + j) n) hA
    _ = ((2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ * (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ *
          ((4 * π * m / (((c : ℕ) : ℝ) ^ 2 * y)) ^ j / (j.factorial : ℝ))) * Real.exp (-(π * y) * n) := by
        have hf : ((k' + j).factorial : ℝ) ≠ 0 := by positivity
        have hj : (j.factorial : ℝ) ≠ 0 := by positivity
        have hcj : ((c : ℕ) : ℝ) ^ j ≠ 0 := pow_ne_zero _ hc'
        have hcy : (((c : ℕ) : ℝ) ^ 2 * y) ^ j ≠ 0 := pow_ne_zero _ (by positivity)
        rw [div_pow, div_pow]
        field_simp
        ring_nf
        rw [show (4 : ℝ) ^ j = 2 ^ (j * 2) by rw [mul_comm, pow_mul]; norm_num]
        ring
    _ ≤ coefMajorant k' m y ⟨c, (u, j)⟩ n := by
        unfold coefMajorant
        simp only
        have hsq : (1 : ℝ) ≤ ((c : ℕ) : ℝ) ^ 2 := one_le_pow₀ hc1
        have hfrac : 4 * π * m / (((c : ℕ) : ℝ) ^ 2 * y) ≤ 4 * π * m / y :=
          div_le_div_of_nonneg_left (by positivity) hy (le_mul_of_one_le_left hy.le hsq)
        have hbr : (4 * π * m / (((c : ℕ) : ℝ) ^ 2 * y)) ^ j / (j.factorial : ℝ)
            ≤ (4 * π * m / y) ^ j / (j.factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfrac j) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr (by positivity))
          (Real.exp_pos _).le

/-! ## Summability of the majorant -/

theorem summable_pnat_pow_inv {p : ℕ} (hp : 1 < p) :
    Summable fun c : ℕ+ => (((c : ℕ) : ℝ) ^ p)⁻¹ :=
  (Real.summable_nat_pow_inv.mpr hp).comp_injective PNat.coe_injective

theorem summable_coefMajorant_fiber (k' m : ℕ) {y : ℝ} (hy : 0 < y) (c : ℕ+) :
    Summable fun q : (ZMod c)ˣ × ℕ => (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
      (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ * ((4 * π * m / y) ^ q.2 / (q.2.factorial : ℝ)) := by
  have hj : Summable fun j : ℕ => (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
      (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ * ((4 * π * m / y) ^ j / (j.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial _).mul_left _
  exact (summable_prod_of_nonneg (fun q => by
    obtain ⟨u, j⟩ := q
    show (0 : ℝ) ≤ (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ * (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ *
      ((4 * π * m / y) ^ j / (j.factorial : ℝ))
    positivity)).mpr ⟨fun _ => hj, Summable.of_finite⟩

/-- The `(c, u, j)`-part of the majorant is summable for `k' ≥ 2`. -/
theorem summable_coefMajorant_sigma {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun p : CoefIndex => (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
      (((p.1 : ℕ) : ℝ) ^ (k' + 1))⁻¹ * ((4 * π * m / y) ^ p.2.2 / (p.2.2.factorial : ℝ)) := by
  have hnn : ∀ p : CoefIndex, 0 ≤ (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
      (((p.1 : ℕ) : ℝ) ^ (k' + 1))⁻¹ * ((4 * π * m / y) ^ p.2.2 / (p.2.2.factorial : ℝ)) :=
    fun p => by positivity
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun c => summable_coefMajorant_fiber k' m hy c, ?_⟩
  set T : ℝ := ∑' j : ℕ, (4 * π * m / y) ^ j / (j.factorial : ℝ) with hT
  have hTnn : 0 ≤ T := tsum_nonneg fun j => by positivity
  -- the inner sum is `card (units) * const * T ≤ c * const * T`
  have hinner : ∀ c : ℕ+, ∑' q : (ZMod c)ˣ × ℕ, (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
      (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ * ((4 * π * m / y) ^ q.2 / (q.2.factorial : ℝ))
      ≤ (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ * T * (((c : ℕ) : ℝ) ^ k')⁻¹ := by
    intro c
    rw [(summable_coefMajorant_fiber k' m hy c).tsum_prod, tsum_fintype]
    simp_rw [tsum_mul_left]
    rw [← hT, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
    have hc : (0 : ℝ) < (c : ℕ) := by exact_mod_cast c.pos
    have htot : ((c : ℕ).totient : ℝ) ≤ (c : ℕ) := by exact_mod_cast Nat.totient_le _
    calc ((c : ℕ).totient : ℝ) * ((2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
          (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ * T)
        ≤ ((c : ℕ) : ℝ) * ((2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ *
          (((c : ℕ) : ℝ) ^ (k' + 1))⁻¹ * T) := by gcongr
      _ = (2 * π) ^ (k' + 1) * ((π * y) ^ k')⁻¹ * T * (((c : ℕ) : ℝ) ^ k')⁻¹ := by
          rw [pow_succ]
          field_simp
          ring
  refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun q => hnn ⟨c, q⟩) hinner ?_
  exact (summable_pnat_pow_inv hk').mul_left _

/-- **The majorant is summable** over `(c, u, j, n)` for `k' ≥ 2`. -/
theorem summable_coefMajorant {k' : ℕ} (hk' : 2 ≤ k') (m : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun x : CoefIndex × ℕ => coefMajorant k' m y x.1 x.2 := by
  have hg : Summable fun n : ℕ => Real.exp (-(π * y) * n) := by
    have := Real.summable_exp_nat_mul_iff.mpr (by nlinarith [Real.pi_pos] : -(π * y) < 0)
    refine this.congr fun n => ?_
    ring_nf
  exact Summable.mul_of_nonneg (summable_coefMajorant_sigma hk' m hy) hg
    (fun p => by positivity) (fun n => (Real.exp_pos _).le)

end

end GaloisForLFunctions.HTGeometry
