/-
# Exact block localization for Bourgain's `A₆` curve

A consecutive block of normalized square-root-curve samples is exactly the
local sum used by the osculating-cell estimates.  No Taylor approximation
enters this identification.
-/
import GaloisForLFunctions.RHTower.BourgainA6PhysicalBox
import GaloisForLFunctions.RHTower.BourgainAnisotropicCellGrid

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Weighted block of samples
`(q+m)/N ↦ ((q+m)/N,((q+m)/N)²,((q+m)/N)^(3/2),
((q+m)/N)^(1/2))`. -/
def bourgainA6PhysicalBlockSum
    (N M q : ℕ) (c : Fin M → ℂ)
    (x : BourgainPhaseSpace) : ℂ :=
  ∑ m : Fin M,
    c m * bourgainUnitCharacter
      (bourgainSquareRootCurvePhase x
        (((q + bourgainIndex m : ℕ) : ℝ) / (N : ℝ)))

/-- A physical block is literally an exact local sum based at
`sqrt(q/N)`, with denominator `N`. -/
theorem bourgainA6PhysicalBlockSum_eq_exactLocalSum
    (N M q : ℕ) (c : Fin M → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainA6PhysicalBlockSum N M q c x =
      bourgainSquareRootExactLocalSum M (N : ℝ)
        (Real.sqrt ((q : ℝ) / (N : ℝ))) c x := by
  unfold bourgainA6PhysicalBlockSum bourgainSquareRootExactLocalSum
  apply Fintype.sum_congr
  intro m
  congr 2
  congr 1
  rw [Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ) / (N : ℝ))]
  push_cast
  ring

/-- Exact partition of a normalized `A₆` curve sum at scale `K*M` into
`K` consecutive blocks of length `M`. -/
theorem bourgainA6NormalizedCurveSum_mul_eq_sum_blocks
    (K M : ℕ) (x : BourgainPhaseSpace) :
    bourgainA6NormalizedCurveSum (K * M) x =
      ∑ i : Fin K,
        bourgainA6PhysicalBlockSum (K * M) M (M * i.1)
          (fun _ => 1) x := by
  unfold bourgainA6NormalizedCurveSum
  rw [← (finProdFinEquiv : Fin K × Fin M ≃ Fin (K * M)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  unfold bourgainA6PhysicalBlockSum
  apply Fintype.sum_congr
  intro m
  rw [one_mul]
  congr 2
  congr 1
  unfold bourgainIndex
  norm_cast
  rw [finProdFinEquiv_apply_val]
  simp only
  omega

/-- Block partition with every block rewritten as the exact local sum used by
the osculating-cell theorem. -/
theorem bourgainA6NormalizedCurveSum_mul_eq_sum_exactLocal
    (K M : ℕ) (x : BourgainPhaseSpace) :
    bourgainA6NormalizedCurveSum (K * M) x =
      ∑ i : Fin K,
        bourgainSquareRootExactLocalSum M (K * M : ℕ)
          (Real.sqrt (((M * i.1 : ℕ) : ℝ) / ((K * M : ℕ) : ℝ)))
          (fun _ => 1) x := by
  rw [bourgainA6NormalizedCurveSum_mul_eq_sum_blocks]
  apply Fintype.sum_congr
  intro i
  exact bourgainA6PhysicalBlockSum_eq_exactLocalSum
    (K * M) M (M * i.1) (fun _ => 1) x

/-- The base parameter of a nonempty block is positive. -/
theorem sqrt_natCast_div_pos
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) :
    0 < Real.sqrt ((q : ℝ) / (N : ℝ)) := by
  apply Real.sqrt_pos.2
  positivity

/-- Ordered positive block starts give ordered square-root base
parameters. -/
theorem sqrt_natCast_div_lt
    {N q₁ q₂ : ℕ} (hN : 0 < N) (hq : q₁ < q₂) :
    Real.sqrt ((q₁ : ℝ) / (N : ℝ)) <
      Real.sqrt ((q₂ : ℝ) / (N : ℝ)) := by
  apply Real.sqrt_lt_sqrt (by positivity)
  exact div_lt_div_of_pos_right (by exact_mod_cast hq) (by positivity)

/-- Quantitative separation of square-root base parameters for blocks inside
`[1,N]`.  A gap of at least `M` in integer starts gives a base gap at least
`M/(2N)`. -/
theorem sqrt_natCast_div_sub_ge
    {N M q₁ q₂ : ℕ} (hN : 0 < N)
    (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    (M : ℝ) / (2 * (N : ℝ)) ≤
      Real.sqrt ((q₂ : ℝ) / (N : ℝ)) -
        Real.sqrt ((q₁ : ℝ) / (N : ℝ)) := by
  let A : ℝ := (q₁ : ℝ) / (N : ℝ)
  let B : ℝ := (q₂ : ℝ) / (N : ℝ)
  let a : ℝ := Real.sqrt A
  let b : ℝ := Real.sqrt B
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    apply div_le_div_of_nonneg_right _ hNr.le
    exact_mod_cast (le_trans (Nat.le_add_right q₁ M) hq)
  have hab : a ≤ b := by
    exact Real.sqrt_le_sqrt hAB
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb1 : b ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    dsimp [B]
    exact (div_le_one hNr).2 (by exact_mod_cast hq₂N)
  have ha_sq : a ^ (2 : ℕ) = A := by
    exact Real.sq_sqrt hA
  have hb_sq : b ^ (2 : ℕ) = B := by
    exact Real.sq_sqrt hB
  have hgapCast : (q₁ : ℝ) + (M : ℝ) ≤ (q₂ : ℝ) := by
    exact_mod_cast hq
  have hfrac :
      (M : ℝ) / (N : ℝ) ≤ B - A := by
    dsimp [A, B]
    have heq :
        (q₂ : ℝ) / (N : ℝ) - (q₁ : ℝ) / (N : ℝ) =
          ((q₂ : ℝ) - (q₁ : ℝ)) / (N : ℝ) := by
      ring
    rw [heq]
    exact (div_le_div_iff_of_pos_right hNr).2 (by linarith)
  have hfactor : B - A = (b - a) * (b + a) := by
    nlinarith [ha_sq, hb_sq]
  have hsum : b + a ≤ 2 := by
    nlinarith
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmain : (M : ℝ) / (N : ℝ) ≤ 2 * (b - a) := by
    calc
      (M : ℝ) / (N : ℝ) ≤ B - A := hfrac
      _ = (b - a) * (b + a) := hfactor
      _ ≤ (b - a) * 2 :=
        mul_le_mul_of_nonneg_left hsum hdiff
      _ = 2 * (b - a) := by ring
  calc
    (M : ℝ) / (2 * (N : ℝ)) =
        ((M : ℝ) / (N : ℝ)) / 2 := by
          field_simp
    _ ≤
        (Real.sqrt ((q₂ : ℝ) / (N : ℝ)) -
          Real.sqrt ((q₁ : ℝ) / (N : ℝ))) := by
      dsimp [a, b] at hmain
      linarith

/-- Combined osculating/parabola determinant for two normalized `A₆`
blocks. -/
def bourgainA6BlockPhaseDeterminant
    (N M q₁ q₂ : ℕ) : ℝ :=
  let a := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
  let b := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
  ((M : ℝ) / (N : ℝ)) ^ (6 : ℕ) *
    (3 * (b - a) ^ (4 : ℕ) /
      (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))

/-- A pair of length-`M` blocks, separated by at least one block and lying
inside `[1,N]`, has combined phase determinant at least
`(3/512)(M/N)^10`. -/
theorem bourgainA6BlockPhaseDeterminant_ge
    {N M q₁ q₂ : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    (3 / 512 : ℝ) * ((M : ℝ) / (N : ℝ)) ^ (10 : ℕ) ≤
      bourgainA6BlockPhaseDeterminant N M q₁ q₂ := by
  let s : ℝ := (M : ℝ) / (N : ℝ)
  let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
  let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
  let d : ℝ := b - a
  let P : ℝ := a ^ (3 : ℕ) * b ^ (3 : ℕ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have ha : 0 < a := by
    exact sqrt_natCast_div_pos hN hq₁
  have hq₁q₂ : q₁ < q₂ := by omega
  have hab : a < b := by
    exact sqrt_natCast_div_lt hN hq₁q₂
  have hb : 0 < b := lt_trans ha hab
  have hd : s / 2 ≤ d := by
    dsimp [s, d, a, b]
    convert sqrt_natCast_div_sub_ge hN hq hq₂N using 1
    all_goals ring
  have ha1 : a ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hNr).2
      (by exact_mod_cast (le_trans hq₁q₂.le hq₂N))
  have hb1 : b ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hNr).2 (by exact_mod_cast hq₂N)
  have ha3 : a ^ (3 : ℕ) ≤ 1 := by
    simpa using pow_le_pow_left₀ ha.le ha1 3
  have hb3 : b ^ (3 : ℕ) ≤ 1 := by
    simpa using pow_le_pow_left₀ hb.le hb1 3
  have hP : P ≤ 1 := by
    dsimp [P]
    calc
      a ^ (3 : ℕ) * b ^ (3 : ℕ) ≤
          1 * 1 := by
        exact mul_le_mul ha3 hb3 (by positivity) (by positivity)
      _ = 1 := by ring
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hd4 :
      (s / 2) ^ (4 : ℕ) ≤ d ^ (4 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hd 4
  have hsmall :
      (3 / 512 : ℝ) * s ^ (4 : ℕ) ≤
        3 * d ^ (4 : ℕ) / 32 := by
    calc
      (3 / 512 : ℝ) * s ^ (4 : ℕ) =
          3 * (s / 2) ^ (4 : ℕ) / 32 := by ring
      _ ≤ 3 * d ^ (4 : ℕ) / 32 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd4 (by positivity))
          (by norm_num)
  have hden :
      3 * d ^ (4 : ℕ) / 32 ≤
        3 * d ^ (4 : ℕ) / (32 * P) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * P)).2
    have hmul :
        3 * d ^ (4 : ℕ) * P ≤ 3 * d ^ (4 : ℕ) := by
      exact mul_le_of_le_one_right (by positivity) hP
    nlinarith
  have hresult :
      (3 / 512 : ℝ) * s ^ (10 : ℕ) ≤
        s ^ (6 : ℕ) * (3 * d ^ (4 : ℕ) / (32 * P)) := by
    calc
      (3 / 512 : ℝ) * s ^ (10 : ℕ) =
          s ^ (6 : ℕ) * ((3 / 512 : ℝ) * s ^ (4 : ℕ)) := by ring
      _ ≤ s ^ (6 : ℕ) * (3 * d ^ (4 : ℕ) / 32) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ s ^ (6 : ℕ) * (3 * d ^ (4 : ℕ) / (32 * P)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  convert hresult using 1
  all_goals
    simp only [bourgainA6BlockPhaseDeterminant, s, a, b, d, P]
    ring

/-- Sharp reciprocal-Jacobian form of the block determinant estimate. -/
theorem abs_inv_bourgainA6BlockPhaseDeterminant_le
    {N M q₁ q₂ : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| ≤
      (512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ) := by
  let L : ℝ :=
    (3 / 512 : ℝ) * ((M : ℝ) / (N : ℝ)) ^ (10 : ℕ)
  let D : ℝ := bourgainA6BlockPhaseDeterminant N M q₁ q₂
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hLD : L ≤ D := by
    exact bourgainA6BlockPhaseDeterminant_ge hN hM hq₁ hq hq₂N
  have hD : 0 < D := lt_of_lt_of_le hL hLD
  have hinv : D⁻¹ ≤ L⁻¹ :=
    (inv_le_inv₀ hD hL).2 hLD
  rw [abs_of_pos (inv_pos.mpr hD)]
  calc
    D⁻¹ ≤ L⁻¹ := hinv
    _ = (512 / 3 : ℝ) *
        ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ) := by
      dsimp [L]
      field_simp

/-- Real main term obtained from one sharp anisotropic cell for two
unit-coefficient `A₆` blocks. -/
def bourgainA6BlockSharpCellMainTerm
    (N M q₁ q₂ : ℕ) (C ε : ℝ) : ℝ :=
  |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| *
    (((M : ℝ) ^ (3 : ℕ) *
        (C * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (3 : ℕ))) *
      ((M : ℝ) ^ (3 : ℕ) *
        (C * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (3 : ℕ))))

/-- The determinant bound gives the sharp one-cell main-term scale
`N^10 M^(2+ε)`.  After division by physical volume `N^6`, this is exactly
Bourgain's `N^(4+ε)M²` scale, before Taylor-error absorption. -/
theorem bourgainA6BlockSharpCellMainTerm_le
    {N M q₁ q₂ : ℕ} {C ε : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hq₁ : 0 < q₁) (hq : q₁ + M ≤ q₂) (hq₂N : q₂ ≤ N) :
    bourgainA6BlockSharpCellMainTerm N M q₁ q₂ C ε ≤
      (512 / 3 : ℝ) * C ^ (2 : ℕ) *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hJ :=
    abs_inv_bourgainA6BlockPhaseDeterminant_le
      hN hM hq₁ hq hq₂N
  let B : ℝ :=
    ((M : ℝ) ^ (3 : ℕ) *
        (C * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (3 : ℕ))) *
      ((M : ℝ) ^ (3 : ℕ) *
        (C * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (3 : ℕ)))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have heps :
      (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) =
        (M : ℝ) ^ ε := by
    rw [← Real.rpow_add hMr]
    congr 1
    ring
  have hB :
      B = C ^ (2 : ℕ) * (M : ℝ) ^ (12 : ℕ) *
        (M : ℝ) ^ ε := by
    dsimp [B]
    rw [← heps]
    ring
  have hpow :
      (M : ℝ) ^ (2 + ε) =
        (M : ℝ) ^ (2 : ℕ) * (M : ℝ) ^ ε := by
    rw [Real.rpow_add hMr, Real.rpow_two]
  unfold bourgainA6BlockSharpCellMainTerm
  change
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| * B ≤ _
  calc
    |(bourgainA6BlockPhaseDeterminant N M q₁ q₂)⁻¹| * B ≤
        ((512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ)) * B :=
      mul_le_mul_of_nonneg_right hJ hB0
    _ = (512 / 3 : ℝ) * C ^ (2 : ℕ) *
        (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (2 + ε) := by
      rw [hB, hpow]
      field_simp

/-- Exact osculating-cell integral estimate specialized to two normalized
`A₆` blocks.  This is the local analytic input before physical-domain
covering and the Bourgain--Guth scale recurrence. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_translatedCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hq₁ : 0 < q₁) → (hq : q₁ < q₂) →
      ∀ (c₁ c₂ : Fin M → ℂ) (y : BourgainPhaseSpace),
      let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
      let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
      let hscale : (M : ℝ) / (N : ℝ) ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hM.ne')
          (Nat.cast_ne_zero.mpr hN.ne')
      let R : ℝ :=
        ‖((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            (sqrt_natCast_div_pos hN hq₁)
            (sqrt_natCast_div_lt hN hq)).symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
          (‖((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm :
              BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
            ((M : ℝ) ^ (2 : ℕ) / 2))
      let J : ENNReal :=
        ENNReal.ofReal
          |((((M : ℝ) / (N : ℝ)) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹|
      let B : ℝ :=
        ((M : ℝ) ^ (3 : ℕ) *
          (C * (M : ℝ) ^ (ε / 2) *
            (∑ n : Fin M, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) *
        ((M : ℝ) ^ (3 : ℕ) *
          (C * (M : ℝ) ^ (ε / 2) *
            (∑ n : Fin M, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)))
      (∫⁻ z in bourgainTranslatedOsculatingFundamentalCell
          M ((M : ℝ) / (N : ℝ)) a b y,
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ c₁ z‖ ^ (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ c₂ z‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (J * ENNReal.ofReal B +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  R a b ((M : ℝ) / (N : ℝ)) c₁ c₂) *
              (J * ENNReal.ofReal ((M : ℝ) ^ (6 : ℕ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_translatedFundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hq₁ hq c₁ c₂ y
  simpa only [bourgainA6PhysicalBlockSum_eq_exactLocalSum] using
    hbound M hM
      (show (0 : ℝ) < N by exact_mod_cast hN)
      (sqrt_natCast_div_pos hN hq₁)
      (sqrt_natCast_div_lt hN hq)
      c₁ c₂ y

end

end RHTower
