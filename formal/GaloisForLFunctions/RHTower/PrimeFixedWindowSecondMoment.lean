import GaloisForLFunctions.RHTower.PrimeFixedWindowChebyshev

/-!
# The second moment of the fixed-length window, fully integrated

Integrating `sq_fixedIncr_psi_le_uniform` term by term. Each of the three pieces is a multiplicative
second moment over a range inside `[X, 8X]`, or an explicit polynomial, so
`integral_sq_multIncr_psi_sub_le` bounds them all by the three dyadic moments at `X`, `2X`, `4X`.
Combined with `volume_fixedIncr_psi_gt_le` this is Guth–Maynard's Corollary 1.4 in the fixed-length
normalisation, reduced to the numeric choice of `δ` and `J₀`.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory intervalIntegral Finset

noncomputable section

/-- The total of the three dyadic multiplicative moments covering `[X, 8X]`. -/
def multWindowMomentTotal (δ ε X : ℝ) : ℝ :=
  multWindowMoment δ ε X + multWindowMoment δ ε (2 * X) + multWindowMoment δ ε (4 * X)

/-- One dilated block integral, bounded by the total. -/
theorem integral_sq_multIncr_block_le {δ ε X : ℝ} {j : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 4 ≤ X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (hc : (1 + δ) ^ j ≤ 4) :
    ∫ x in X..(2 * X), (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2
      ≤ multWindowMomentTotal δ ε X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hδ1 : (1 : ℝ) ≤ 1 + δ := by linarith
  have hcj : (1 : ℝ) ≤ (1 + δ) ^ j := one_le_pow₀ hδ1
  have hc0 : (1 + δ) ^ j ≠ 0 := by positivity
  have hgrid : ∀ x : ℝ, gridPt δ x j = x * (1 + δ) ^ j := fun _ => rfl
  simp_rw [hgrid]
  rw [integral_comp_mul_right (fun u => (multIncr Chebyshev.psi δ u) ^ 2) hc0]
  have hinv : ((1 + δ) ^ j)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hcj
  have hinv0 : (0 : ℝ) ≤ ((1 + δ) ^ j)⁻¹ := by positivity
  have hsub := integral_sq_multIncr_psi_sub_le (a := X * (1 + δ) ^ j) (b := 2 * X * (1 + δ) ^ j)
    hε hε1 hX hδ0 hδ hbig (by nlinarith) (by nlinarith) (by nlinarith)
  have htot0 : 0 ≤ multWindowMomentTotal δ ε X := by
    have hnn : (0 : ℝ) ≤ ∫ u in (X * (1 + δ) ^ j)..(2 * X * (1 + δ) ^ j),
        (multIncr Chebyshev.psi δ u) ^ 2 := by
      refine intervalIntegral.integral_nonneg (by nlinarith) fun u _ => sq_nonneg _
    rw [multWindowMomentTotal]
    linarith [hsub, hnn]
  rw [smul_eq_mul, multWindowMomentTotal] at *
  nlinarith [hsub, hinv, hinv0, htot0]

/-- **The fixed-window second moment, integrated.**  For `x ∈ [X, 2X]` the pointwise bound of
`sq_fixedIncr_psi_le_uniform` integrates to `(2J₀² + 4)` times the dyadic total plus the explicit
polynomial term. -/
theorem integral_sq_fixedIncr_psi_total_le {δ ε X y : ℝ} {J₀ : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : 4 ≤ X) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hy : 0 ≤ y) (hyX : y ≤ X)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (hJ₀ : X + y ≤ gridPt δ X J₀) (hJc : (1 + δ) ^ J₀ ≤ 4) :
    ∫ x in X..(2 * X), (fixedIncr Chebyshev.psi y x) ^ 2
      ≤ (2 * (J₀ : ℝ) ^ 2 + 4) * multWindowMomentTotal δ ε X + 4 * δ ^ 2 * X * (2 * X + y) ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX2 : X ≤ 2 * X := by linarith
  have hδ1 : (1 : ℝ) ≤ 1 + δ := by linarith
  -- the three integrable pieces
  have hiBlocks : ∀ j ∈ range J₀, IntervalIntegrable
      (fun x => (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2) volume X (2 * X) := by
    intro j _
    have hcj : (1 : ℝ) ≤ (1 + δ) ^ j := one_le_pow₀ hδ1
    have hbnd : ∀ x ∈ Set.Ioc X (2 * X),
        |multIncr Chebyshev.psi δ (gridPt δ x j)|
          ≤ Chebyshev.psi ((1 + δ) * (2 * X * (1 + δ) ^ j))
            + Chebyshev.psi (2 * X * (1 + δ) ^ j) + δ * (2 * X * (1 + δ) ^ j) := by
      intro x hx
      have hx0 : 0 < x := lt_trans hX0 hx.1
      refine abs_multIncr_psi_le (a := 0) (b := 2 * X * (1 + δ) ^ j) hδ0.le le_rfl ⟨?_, ?_⟩
      · show 0 < x * (1 + δ) ^ j; positivity
      · show x * (1 + δ) ^ j ≤ 2 * X * (1 + δ) ^ j
        exact mul_le_mul_of_nonneg_right hx.2 (by positivity)
    exact intervalIntegrable_sq_of_bound hX2
      ((measurable_multIncr_psi δ).comp (measurable_id.mul_const ((1 + δ) ^ j))) hbnd
  have hiSum : IntervalIntegrable
      (fun x => ∑ j ∈ range J₀, (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2) volume X (2 * X) := by
    have h := IntervalIntegrable.sum (range J₀) hiBlocks
    have e : (∑ i ∈ range J₀, fun x => (multIncr Chebyshev.psi δ (gridPt δ x i)) ^ 2)
        = fun x => ∑ j ∈ range J₀, (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2 := by
      funext x; simp [Finset.sum_apply]
    rwa [e] at h
  have hiShift : IntervalIntegrable
      (fun x => (multIncr Chebyshev.psi δ (x + y)) ^ 2) volume X (2 * X) := by
    have hbnd : ∀ x ∈ Set.Ioc X (2 * X), |multIncr Chebyshev.psi δ (x + y)|
        ≤ Chebyshev.psi ((1 + δ) * (2 * X + y)) + Chebyshev.psi (2 * X + y) + δ * (2 * X + y) := by
      intro x hx
      have hx0 : 0 < x := lt_trans hX0 hx.1
      exact abs_multIncr_psi_le (a := 0) (b := 2 * X + y) hδ0.le le_rfl
        ⟨by linarith, by linarith [hx.2]⟩
    exact intervalIntegrable_sq_of_bound hX2
      ((measurable_multIncr_psi δ).comp (measurable_id.add_const y)) hbnd
  have hiPoly : IntervalIntegrable (fun x : ℝ => 4 * δ ^ 2 * (x + y) ^ 2) volume X (2 * X) :=
    (continuous_const.mul ((continuous_id.add continuous_const).pow 2)).intervalIntegrable _ _
  have hiG : IntervalIntegrable (fun x => (fixedIncr Chebyshev.psi y x) ^ 2) volume X (2 * X) :=
    intervalIntegrable_sq_fixedIncr_psi hy hX0.le hX2
  have hiRHS : IntervalIntegrable
      (fun x => 2 * (J₀ : ℝ) * (∑ j ∈ range J₀, (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
        + 4 * (multIncr Chebyshev.psi δ (x + y)) ^ 2 + 4 * δ ^ 2 * (x + y) ^ 2) volume X (2 * X) :=
    ((hiSum.const_mul _).add (hiShift.const_mul _)).add hiPoly
  have hstep : ∫ x in X..(2 * X), (fixedIncr Chebyshev.psi y x) ^ 2
      ≤ ∫ x in X..(2 * X),
          (2 * (J₀ : ℝ) * (∑ j ∈ range J₀, (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
            + 4 * (multIncr Chebyshev.psi δ (x + y)) ^ 2 + 4 * δ ^ 2 * (x + y) ^ 2) :=
    integral_mono_on hX2 hiG hiRHS fun x hx =>
      sq_fixedIncr_psi_le_uniform hδ0 hX0 hy hJ₀ hx
  rw [integral_add ((hiSum.const_mul _).add (hiShift.const_mul _)) hiPoly,
    integral_add (hiSum.const_mul _) (hiShift.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (s := range J₀)
      (f := fun j x => (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2) hiBlocks] at hstep
  -- each block, the shifted term, and the polynomial
  have hblocks : ∀ j ∈ range J₀,
      (∫ x in X..(2 * X), (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
        ≤ multWindowMomentTotal δ ε X := by
    intro j hj
    have hjJ : j ≤ J₀ := le_of_lt (Finset.mem_range.mp hj)
    have hcj : (1 + δ) ^ j ≤ 4 := le_trans (pow_le_pow_right₀ hδ1 hjJ) hJc
    exact integral_sq_multIncr_block_le hε hε1 hX hδ0 hδ hbig hcj
  have hsumle : (∑ j ∈ range J₀, ∫ x in X..(2 * X),
      (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
      ≤ (J₀ : ℝ) * multWindowMomentTotal δ ε X := by
    calc (∑ j ∈ range J₀, ∫ x in X..(2 * X),
          (multIncr Chebyshev.psi δ (gridPt δ x j)) ^ 2)
        ≤ ∑ _j ∈ range J₀, multWindowMomentTotal δ ε X := Finset.sum_le_sum hblocks
      _ = (J₀ : ℝ) * multWindowMomentTotal δ ε X := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hshift : (∫ x in X..(2 * X), (multIncr Chebyshev.psi δ (x + y)) ^ 2)
      ≤ multWindowMomentTotal δ ε X := by
    rw [integral_comp_add_right (fun u => (multIncr Chebyshev.psi δ u) ^ 2) y]
    exact integral_sq_multIncr_psi_sub_le hε hε1 hX hδ0 hδ hbig (by linarith) (by linarith)
      (by linarith)
  have hpoly : (∫ x in X..(2 * X), 4 * δ ^ 2 * (x + y) ^ 2) ≤ 4 * δ ^ 2 * X * (2 * X + y) ^ 2 := by
    have hb : ∀ x ∈ Set.Icc X (2 * X), 4 * δ ^ 2 * (x + y) ^ 2 ≤ 4 * δ ^ 2 * (2 * X + y) ^ 2 := by
      intro x hx
      have h1 : (x + y) ^ 2 ≤ (2 * X + y) ^ 2 := by nlinarith [hx.2, hx.1, hy]
      nlinarith [sq_nonneg δ, h1]
    have hconst : IntervalIntegrable (fun _ : ℝ => 4 * δ ^ 2 * (2 * X + y) ^ 2) volume X (2 * X) :=
      intervalIntegrable_const
    have := integral_mono_on hX2 hiPoly hconst hb
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : (2 * X - X) * (4 * δ ^ 2 * (2 * X + y) ^ 2) = 4 * δ ^ 2 * X * (2 * X + y) ^ 2 := by
      ring
    linarith [this, e]
  have hJ0 : (0 : ℝ) ≤ 2 * (J₀ : ℝ) := by positivity
  nlinarith [hstep, hsumle, hshift, hpoly, hJ0]


/-- **Guth–Maynard Corollary 1.4, in the fixed-length normalisation.**  The exceptional set on which
a window of fixed length `y` has discrepancy above `r` has measure at most the second moment over
`r²`, and the second moment is bounded by the three dyadic multiplicative moments plus an explicit
polynomial term.  Everything on the right is expressed through `zeroShortWeight` by
`multWindowMoment_le`, which is the quantity a zero-density estimate controls. -/
theorem volume_psi_fixed_window_le {δ ε X y r : ℝ} {J₀ : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : 4 ≤ X) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hy : 0 ≤ y) (hyX : y ≤ X) (hr : 0 < r)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2)
    (hJ₀ : X + y ≤ gridPt δ X J₀) (hJc : (1 + δ) ^ J₀ ≤ 4) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ r < |Chebyshev.psi (x + y) - Chebyshev.psi x - y|}).toReal
      ≤ ((2 * (J₀ : ℝ) ^ 2 + 4) * multWindowMomentTotal δ ε X
          + 4 * δ ^ 2 * X * (2 * X + y) ^ 2) / r ^ 2 :=
  volume_fixedIncr_psi_gt_le (by linarith) hy hr
    (integral_sq_fixedIncr_psi_total_le hε hε1 hX hδ0 hδ hy hyX hbig hJ₀ hJc)


/-- **The block parameters exist.**  For `0 ≤ y ≤ X` and `0 < δ ≤ 1/2` the minimal block count
reaching past `X + y` also satisfies `(1+δ)^{J₀} ≤ 4`, because the overshoot of
`exists_blockCount` gives `X(1+δ)^{J₀} ≤ (X+y)(1+δ) ≤ 3X`. -/
theorem exists_blockParams {X y δ : ℝ} (hX : 0 < X) (hy : 0 ≤ y) (hyX : y ≤ X) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) :
    ∃ J₀ : ℕ, X + y ≤ gridPt δ X J₀ ∧ (1 + δ) ^ J₀ ≤ 4 := by
  obtain ⟨J, hlo, hhi, _⟩ := exists_blockCount hδ0 hX hy
  refine ⟨J, hlo, ?_⟩
  have hgrid : gridPt δ X J = X * (1 + δ) ^ J := rfl
  rw [hgrid] at hhi
  have h3 : X * (1 + δ) ^ J ≤ 3 * X := by nlinarith
  nlinarith [h3]

/-- **Corollary 1.4 in the fixed-length normalisation, with the block count supplied.**  No
hypothesis on `J₀` remains: it is produced from `X`, `y` and `δ`. -/
theorem exists_volume_psi_fixed_window_le {δ ε X y r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : 4 ≤ X) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hy : 0 ≤ y) (hyX : y ≤ X) (hr : 0 < r)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * (δ * X) ^ 2) :
    ∃ J₀ : ℕ, (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ r < |Chebyshev.psi (x + y) - Chebyshev.psi x - y|}).toReal
      ≤ ((2 * (J₀ : ℝ) ^ 2 + 4) * multWindowMomentTotal δ ε X
          + 4 * δ ^ 2 * X * (2 * X + y) ^ 2) / r ^ 2 := by
  obtain ⟨J₀, hJ₀, hJc⟩ := exists_blockParams (by linarith) hy hyX hδ0 hδ
  exact ⟨J₀, volume_psi_fixed_window_le hε hε1 hX hδ0 hδ hy hyX hr hbig hJ₀ hJc⟩

end

end RHTower
