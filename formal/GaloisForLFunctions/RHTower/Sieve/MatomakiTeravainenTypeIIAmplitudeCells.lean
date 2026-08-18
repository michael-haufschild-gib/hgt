import GaloisForLFunctions.RHTower.Sieve.NoncoprimeUnionBound

/-!
# Matomäki--Teräväinen Type-II amplitude-cell cancellation

This module formalizes the power cancellation in the `\mathcal T_2` case of Proposition 4.2 of
Matomäki--Teräväinen.  If a dyadic cell has cardinality

`C * T ^ (2 * min sigma₁ sigma₂ - delta)`

and its two amplitudes are bounded by `2 * M₁ ^ (-sigma₁)` and
`2 * M₂ ^ (-sigma₂)`, then `T = M₁ * M₂` forces its weighted energy to be at
most `16 * C * T ^ (-delta)`.  The final theorems sum this estimate over an
overlapping finite cell cover, producing exactly the finite logarithmic loss used in the paper.
-/

namespace RHTower.Sieve

/-- The scalar exponent cancellation underlying the Type-II amplitude-cell argument. -/
theorem matomakiTeravainen_typeII_amplitude_cell_scale
    {T M₁ M₂ sigma₁ sigma₂ delta C R A B : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hT : T = M₁ * M₂)
    (hC : 0 ≤ C)
    (hcount : R ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta))
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ 2 * M₁ ^ (-sigma₁))
    (hB : B ≤ 2 * M₂ ^ (-sigma₂)) :
    R * A ^ 2 * B ^ 2 ≤ 16 * C * T ^ (-delta) := by
  have hM₁0 : 0 < M₁ := lt_of_lt_of_le zero_lt_one hM₁
  have hM₂0 : 0 < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  have hT0 : 0 < T := by rw [hT]; positivity
  have hAupper0 : 0 ≤ 2 * M₁ ^ (-sigma₁) := by positivity
  have hBupper0 : 0 ≤ 2 * M₂ ^ (-sigma₂) := by positivity
  have hA2 : A ^ 2 ≤ 4 * M₁ ^ (-2 * sigma₁) := by
    have hs := pow_le_pow_left₀ hA0 hA 2
    calc
      A ^ 2 ≤ (2 * M₁ ^ (-sigma₁)) ^ 2 := hs
      _ = 4 * M₁ ^ (-2 * sigma₁) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM₁0.le]
        congr 2
        ring
  have hB2 : B ^ 2 ≤ 4 * M₂ ^ (-2 * sigma₂) := by
    have hs := pow_le_pow_left₀ hB0 hB 2
    calc
      B ^ 2 ≤ (2 * M₂ ^ (-sigma₂)) ^ 2 := hs
      _ = 4 * M₂ ^ (-2 * sigma₂) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM₂0.le]
        congr 2
        ring
  have hmin₁ : 2 * (min sigma₁ sigma₂ - sigma₁) ≤ 0 := by
    nlinarith [min_le_left sigma₁ sigma₂]
  have hmin₂ : 2 * (min sigma₁ sigma₂ - sigma₂) ≤ 0 := by
    nlinarith [min_le_right sigma₁ sigma₂]
  have hfac₁ : M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM₁ hmin₁
  have hfac₂ : M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM₂ hmin₂
  have hscale :
      T ^ (2 * min sigma₁ sigma₂ - delta) *
          (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) ≤ T ^ (-delta) := by
    have heq :
        T ^ (2 * min sigma₁ sigma₂ - delta) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) =
          T ^ (-delta) *
            (M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
              M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂))) := by
      have hsplitT : T ^ (2 * min sigma₁ sigma₂) =
          M₁ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (2 * min sigma₁ sigma₂) := by
        rw [hT, Real.mul_rpow hM₁0.le hM₂0.le]
      rw [show 2 * min sigma₁ sigma₂ - delta =
          (-delta) + 2 * min sigma₁ sigma₂ by ring,
        Real.rpow_add hT0]
      rw [hsplitT]
      have hcombine₁ :
          M₁ ^ (2 * min sigma₁ sigma₂) * M₁ ^ (-2 * sigma₁) =
            M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) := by
        rw [← Real.rpow_add hM₁0]
        congr 1
        ring
      have hcombine₂ :
          M₂ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (-2 * sigma₂) =
            M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)) := by
        rw [← Real.rpow_add hM₂0]
        congr 1
        ring
      rw [show T ^ (-delta) *
          (M₁ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (2 * min sigma₁ sigma₂)) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) =
          T ^ (-delta) *
            ((M₁ ^ (2 * min sigma₁ sigma₂) * M₁ ^ (-2 * sigma₁)) *
             (M₂ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (-2 * sigma₂))) by ring]
      rw [hcombine₁, hcombine₂]
    rw [heq]
    have hprod :
        M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
            M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)) ≤ 1 := by
      have hnonneg : 0 ≤ M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) := by positivity
      calc
        M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
              M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂))
            ≤ M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) * 1 :=
          mul_le_mul_of_nonneg_left hfac₂ hnonneg
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hfac₁ (by norm_num)
        _ = 1 := by ring
    have hpow0 : 0 ≤ T ^ (-delta) := by positivity
    simpa using mul_le_mul_of_nonneg_left hprod hpow0
  have hAB : A ^ 2 * B ^ 2 ≤
      16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) := by
    calc
      A ^ 2 * B ^ 2 ≤
          (4 * M₁ ^ (-2 * sigma₁)) * (4 * M₂ ^ (-2 * sigma₂)) :=
        mul_le_mul hA2 hB2 (sq_nonneg B) (by positivity)
      _ = 16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) := by ring
  have hcount0 : 0 ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta) := by positivity
  calc
    R * A ^ 2 * B ^ 2 = R * (A ^ 2 * B ^ 2) := by ring
    _ ≤ (C * T ^ (2 * min sigma₁ sigma₂ - delta)) *
          (16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))) :=
      mul_le_mul hcount hAB (by positivity) hcount0
    _ = 16 * C *
          (T ^ (2 * min sigma₁ sigma₂ - delta) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))) := by ring
    _ ≤ 16 * C * T ^ (-delta) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The scale-distorted form needed when `M₁ * M₂ = T (log T) ^ O(1)`.
The comparison loss remains explicit instead of being hidden in asymptotic notation. -/
theorem matomakiTeravainen_typeII_amplitude_cell_scale_comparable
    {T M₁ M₂ K sigma₁ sigma₂ delta C R A B : ℝ}
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : 0 ≤ sigma₁) (hsigma₂ : 0 ≤ sigma₂)
    (hC : 0 ≤ C)
    (hcount : R ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta))
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ 2 * M₁ ^ (-sigma₁))
    (hB : B ≤ 2 * M₂ ^ (-sigma₂)) :
    R * A ^ 2 * B ^ 2 ≤
      16 * C * K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by
  have hM₁0 : 0 < M₁ := lt_of_lt_of_le zero_lt_one hM₁
  have hM₂0 : 0 < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hA2 : A ^ 2 ≤ 4 * M₁ ^ (-2 * sigma₁) := by
    have hs := pow_le_pow_left₀ hA0 hA 2
    calc
      A ^ 2 ≤ (2 * M₁ ^ (-sigma₁)) ^ 2 := hs
      _ = 4 * M₁ ^ (-2 * sigma₁) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM₁0.le]
        congr 2
        ring
  have hB2 : B ^ 2 ≤ 4 * M₂ ^ (-2 * sigma₂) := by
    have hs := pow_le_pow_left₀ hB0 hB 2
    calc
      B ^ 2 ≤ (2 * M₂ ^ (-sigma₂)) ^ 2 := hs
      _ = 4 * M₂ ^ (-2 * sigma₂) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM₂0.le]
        congr 2
        ring
  have hmin0 : 0 ≤ min sigma₁ sigma₂ := le_min hsigma₁ hsigma₂
  have htwomin0 : 0 ≤ 2 * min sigma₁ sigma₂ := mul_nonneg (by norm_num) hmin0
  have hTpow : T ^ (2 * min sigma₁ sigma₂) ≤
      (K * (M₁ * M₂)) ^ (2 * min sigma₁ sigma₂) :=
    Real.rpow_le_rpow hT0.le hT htwomin0
  have hmin₁ : 2 * (min sigma₁ sigma₂ - sigma₁) ≤ 0 := by
    nlinarith [min_le_left sigma₁ sigma₂]
  have hmin₂ : 2 * (min sigma₁ sigma₂ - sigma₂) ≤ 0 := by
    nlinarith [min_le_right sigma₁ sigma₂]
  have hfac₁ : M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM₁ hmin₁
  have hfac₂ : M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM₂ hmin₂
  have hresidual :
      M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
          M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)) ≤ 1 := by
    have hnonneg : 0 ≤ M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) := by positivity
    calc
      M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
            M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂))
          ≤ M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) * 1 :=
        mul_le_mul_of_nonneg_left hfac₂ hnonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hfac₁ (by norm_num)
      _ = 1 := by ring
  have hscale :
      T ^ (2 * min sigma₁ sigma₂ - delta) *
          (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) ≤
        K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by
    have hrewrite :
        (K * (M₁ * M₂)) ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) =
          K ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
              M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂))) := by
      rw [Real.mul_rpow hK0.le (mul_nonneg hM₁0.le hM₂0.le),
        Real.mul_rpow hM₁0.le hM₂0.le]
      rw [show K ^ (2 * min sigma₁ sigma₂) *
          (M₁ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (2 * min sigma₁ sigma₂)) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) =
        K ^ (2 * min sigma₁ sigma₂) *
          ((M₁ ^ (2 * min sigma₁ sigma₂) * M₁ ^ (-2 * sigma₁)) *
           (M₂ ^ (2 * min sigma₁ sigma₂) * M₂ ^ (-2 * sigma₂))) by ring]
      rw [← Real.rpow_add hM₁0, ← Real.rpow_add hM₂0]
      congr 2 <;> ring_nf
    rw [show 2 * min sigma₁ sigma₂ - delta =
        (-delta) + 2 * min sigma₁ sigma₂ by ring,
      Real.rpow_add hT0]
    calc
      T ^ (-delta) * T ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))
          ≤ T ^ (-delta) * (K * (M₁ * M₂)) ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) := by
        gcongr
      _ = T ^ (-delta) * ((K * (M₁ * M₂)) ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))) := by ring
      _ = T ^ (-delta) *
          (K ^ (2 * min sigma₁ sigma₂) *
            (M₁ ^ (2 * (min sigma₁ sigma₂ - sigma₁)) *
              M₂ ^ (2 * (min sigma₁ sigma₂ - sigma₂)))) := by rw [hrewrite]
      _ ≤ T ^ (-delta) * (K ^ (2 * min sigma₁ sigma₂) * 1) := by
        gcongr
      _ = K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by ring
  have hAB : A ^ 2 * B ^ 2 ≤
      16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) := by
    calc
      A ^ 2 * B ^ 2 ≤
          (4 * M₁ ^ (-2 * sigma₁)) * (4 * M₂ ^ (-2 * sigma₂)) :=
        mul_le_mul hA2 hB2 (sq_nonneg B) (by positivity)
      _ = 16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂)) := by ring
  have hcount0 : 0 ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta) := by positivity
  calc
    R * A ^ 2 * B ^ 2 = R * (A ^ 2 * B ^ 2) := by ring
    _ ≤ (C * T ^ (2 * min sigma₁ sigma₂ - delta)) *
          (16 * (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))) :=
      mul_le_mul hcount hAB (by positivity) hcount0
    _ = 16 * C *
          (T ^ (2 * min sigma₁ sigma₂ - delta) *
            (M₁ ^ (-2 * sigma₁) * M₂ ^ (-2 * sigma₂))) := by ring
    _ ≤ 16 * C * (K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 16 * C * K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by ring

/-- A Huxley cardinality saving at the smaller amplitude exponent cancels both
dyadic amplitudes once the two Dirichlet lengths multiply to `T`. -/
theorem matomakiTeravainen_typeII_amplitude_cell_energy
    {α : Type*} {S : Finset α} {F₁ F₂ : α → ℝ}
    {T M₁ M₂ sigma₁ sigma₂ delta C : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hT : T = M₁ * M₂)
    (hC : 0 ≤ C)
    (hcount : (S.card : ℝ) ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta))
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hF₁ : ∀ q ∈ S, F₁ q ≤ 2 * M₁ ^ (-sigma₁))
    (hF₂ : ∀ q ∈ S, F₂ q ≤ 2 * M₂ ^ (-sigma₂)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ 16 * C * T ^ (-delta) := by
  classical
  let A : ℝ := 2 * M₁ ^ (-sigma₁)
  let B : ℝ := 2 * M₂ ^ (-sigma₂)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ A ^ 2 * B ^ 2 := by
    intro q hq
    have h1 : F₁ q ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (hF₁0 q hq) (hF₁ q hq) 2
    have h2 : F₂ q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hF₂0 q hq) (hF₂ q hq) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ ∑ _q ∈ S, A ^ 2 * B ^ 2 := by
      exact Finset.sum_le_sum fun q hq => hpoint q hq
    _ = (S.card : ℝ) * A ^ 2 * B ^ 2 := by simp [mul_assoc]
    _ ≤ 16 * C * T ^ (-delta) := by
      exact matomakiTeravainen_typeII_amplitude_cell_scale hM₁ hM₂ hT hC hcount
        hA0 hB0 (by simp [A]) (by simp [B])

/-- Weighted cell energy with an explicit product-scale distortion. -/
theorem matomakiTeravainen_typeII_amplitude_cell_energy_comparable
    {α : Type*} {S : Finset α} {F₁ F₂ : α → ℝ}
    {T M₁ M₂ K sigma₁ sigma₂ delta C : ℝ}
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : 0 ≤ sigma₁) (hsigma₂ : 0 ≤ sigma₂)
    (hC : 0 ≤ C)
    (hcount : (S.card : ℝ) ≤ C * T ^ (2 * min sigma₁ sigma₂ - delta))
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hF₁ : ∀ q ∈ S, F₁ q ≤ 2 * M₁ ^ (-sigma₁))
    (hF₂ : ∀ q ∈ S, F₂ q ≤ 2 * M₂ ^ (-sigma₂)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤
      16 * C * K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by
  classical
  let A : ℝ := 2 * M₁ ^ (-sigma₁)
  let B : ℝ := 2 * M₂ ^ (-sigma₂)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ A ^ 2 * B ^ 2 := by
    intro q hq
    have h1 : F₁ q ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (hF₁0 q hq) (hF₁ q hq) 2
    have h2 : F₂ q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hF₂0 q hq) (hF₂ q hq) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ ∑ _q ∈ S, A ^ 2 * B ^ 2 := by
      exact Finset.sum_le_sum fun q hq => hpoint q hq
    _ = (S.card : ℝ) * A ^ 2 * B ^ 2 := by simp [mul_assoc]
    _ ≤ 16 * C * K ^ (2 * min sigma₁ sigma₂) * T ^ (-delta) := by
      exact matomakiTeravainen_typeII_amplitude_cell_scale_comparable hT0 hM₁ hM₂ hK hT
        hsigma₁ hsigma₂ hC hcount hA0 hB0 (by simp [A]) (by simp [B])

/-- Summing the preceding cancellation over any finite family of amplitude cells
costs only the number of cells, even if the cells overlap. -/
theorem matomakiTeravainen_typeII_amplitude_cells_energy
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ delta C : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hT : T = M₁ * M₂)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i)) :
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2
      ≤ (I.card : ℝ) * (16 * C * T ^ (-delta)) := by
  classical
  calc
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ i ∈ I, ∑ q ∈ cells i, F₁ q ^ 2 * F₂ q ^ 2 :=
      sum_biUnion_le_of_nonneg fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ ≤ ∑ _i ∈ I, 16 * C * T ^ (-delta) := by
      exact Finset.sum_le_sum fun i hi =>
        matomakiTeravainen_typeII_amplitude_cell_energy hM₁ hM₂ hT hC (hcount i hi)
          (fun q _hq => hF₁0 q) (fun q _hq => hF₂0 q)
          (hF₁ i hi) (hF₂ i hi)
    _ = (I.card : ℝ) * (16 * C * T ^ (-delta)) := by simp

/-- Covered-set form used for the exceptional set in Matomäki--Teräväinen's
Type-II decomposition. No disjointness of the amplitude cells is required. -/
theorem matomakiTeravainen_typeII_covered_amplitude_cells_energy
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α} {S : Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ delta C : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hS : S ⊆ I.biUnion cells)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hT : T = M₁ * M₂)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
      ≤ (I.card : ℝ) * (16 * C * T ^ (-delta)) := by
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun q _hq _hnq => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ (I.card : ℝ) * (16 * C * T ^ (-delta)) :=
      matomakiTeravainen_typeII_amplitude_cells_energy hM₁ hM₂ hT hC hcount
        hF₁0 hF₂0 hF₁ hF₂

/-- Comparable-scale sum over amplitude cells. The exact distortion loss is retained cellwise. -/
theorem matomakiTeravainen_typeII_amplitude_cells_energy_comparable
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ K delta C : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : ∀ i ∈ I, 0 ≤ sigma₁ i) (hsigma₂ : ∀ i ∈ I, 0 ≤ sigma₂ i)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i)) :
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2 ≤
      ∑ i ∈ I, 16 * C * K ^ (2 * min (sigma₁ i) (sigma₂ i)) * T ^ (-delta) := by
  classical
  calc
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ i ∈ I, ∑ q ∈ cells i, F₁ q ^ 2 * F₂ q ^ 2 :=
      sum_biUnion_le_of_nonneg fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ ≤ ∑ i ∈ I, 16 * C * K ^ (2 * min (sigma₁ i) (sigma₂ i)) * T ^ (-delta) := by
      exact Finset.sum_le_sum fun i hi =>
        matomakiTeravainen_typeII_amplitude_cell_energy_comparable hT0 hM₁ hM₂ hK hT
          (hsigma₁ i hi) (hsigma₂ i hi) hC (hcount i hi)
          (fun q _hq => hF₁0 q) (fun q _hq => hF₂0 q) (hF₁ i hi) (hF₂ i hi)

/-- Uniform comparable-scale bound when every cell's smaller amplitude exponent is at most `mu`. -/
theorem matomakiTeravainen_typeII_amplitude_cells_energy_comparable_uniform
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ K delta C mu : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : ∀ i ∈ I, 0 ≤ sigma₁ i) (hsigma₂ : ∀ i ∈ I, 0 ≤ sigma₂ i)
    (hmu : ∀ i ∈ I, min (sigma₁ i) (sigma₂ i) ≤ mu)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i)) :
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2 ≤
      (I.card : ℝ) * (16 * C * K ^ (2 * mu) * T ^ (-delta)) := by
  calc
    ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ i ∈ I, 16 * C * K ^ (2 * min (sigma₁ i) (sigma₂ i)) * T ^ (-delta) :=
      matomakiTeravainen_typeII_amplitude_cells_energy_comparable hT0 hM₁ hM₂ hK hT
        hsigma₁ hsigma₂ hC hcount hF₁0 hF₂0 hF₁ hF₂
    _ ≤ ∑ _i ∈ I, 16 * C * K ^ (2 * mu) * T ^ (-delta) := by
      exact Finset.sum_le_sum fun i hi => by
        have hexp : 2 * min (sigma₁ i) (sigma₂ i) ≤ 2 * mu := by nlinarith [hmu i hi]
        have hpow := Real.rpow_le_rpow_of_exponent_le hK hexp
        gcongr
    _ = (I.card : ℝ) * (16 * C * K ^ (2 * mu) * T ^ (-delta)) := by simp

/-- Covered-set version of the uniform comparable-scale Type-II estimate. -/
theorem matomakiTeravainen_typeII_covered_amplitude_cells_energy_comparable_uniform
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α} {S : Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ K delta C mu : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hS : S ⊆ I.biUnion cells)
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : ∀ i ∈ I, 0 ≤ sigma₁ i) (hsigma₂ : ∀ i ∈ I, 0 ≤ sigma₂ i)
    (hmu : ∀ i ∈ I, min (sigma₁ i) (sigma₂ i) ≤ mu)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤
      (I.card : ℝ) * (16 * C * K ^ (2 * mu) * T ^ (-delta)) := by
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ q ∈ I.biUnion cells, F₁ q ^ 2 * F₂ q ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun q _hq _hnq => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ (I.card : ℝ) * (16 * C * K ^ (2 * mu) * T ^ (-delta)) :=
      matomakiTeravainen_typeII_amplitude_cells_energy_comparable_uniform hT0 hM₁ hM₂ hK hT
        hsigma₁ hsigma₂ hmu hC hcount hF₁0 hF₂0 hF₁ hF₂

/-- The full `T₂` power saving: once the finite cell and comparable-scale loss fits in half of
the Huxley saving, the covered exceptional-set energy saves the other half. -/
theorem matomakiTeravainen_typeII_covered_amplitude_cells_power_saving
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α} {S : Finset α}
    {F₁ F₂ : α → ℝ} {T M₁ M₂ K delta C mu : ℝ} {sigma₁ sigma₂ : ι → ℝ}
    (hS : S ⊆ I.biUnion cells)
    (hT0 : 0 < T) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hsigma₁ : ∀ i ∈ I, 0 ≤ sigma₁ i) (hsigma₂ : ∀ i ∈ I, 0 ≤ sigma₂ i)
    (hmu : ∀ i ∈ I, min (sigma₁ i) (sigma₂ i) ≤ mu)
    (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I,
      ((cells i).card : ℝ) ≤ C * T ^ (2 * min (sigma₁ i) (sigma₂ i) - delta))
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2 * M₁ ^ (-sigma₁ i))
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2 * M₂ ^ (-sigma₂ i))
    (hbudget : (I.card : ℝ) * (16 * C * K ^ (2 * mu)) ≤ T ^ (delta / 2)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(delta / 2)) := by
  have henergy :=
    matomakiTeravainen_typeII_covered_amplitude_cells_energy_comparable_uniform hS hT0
      hM₁ hM₂ hK hT hsigma₁ hsigma₂ hmu hC hcount hF₁0 hF₂0 hF₁ hF₂
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ (I.card : ℝ) * (16 * C * K ^ (2 * mu) * T ^ (-delta)) := henergy
    _ = ((I.card : ℝ) * (16 * C * K ^ (2 * mu))) * T ^ (-delta) := by ring
    _ ≤ T ^ (delta / 2) * T ^ (-delta) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = T ^ (-(delta / 2)) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

end RHTower.Sieve
