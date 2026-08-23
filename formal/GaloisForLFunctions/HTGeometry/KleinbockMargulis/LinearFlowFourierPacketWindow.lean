import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowCharacterWindow
import GaloisForLFunctions.HTGeometry.WindowMeanSeparatedModes

open Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

noncomputable section

variable {n : ℕ}

/-- Strong extremality excludes every exact nonzero integer resonance. -/
theorem dotProd_ne_zero_of_not_vwma
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {q : Fin n → ℤ} (hq : q ≠ 0) :
    dotProd q y ≠ 0 := by
  intro hzero
  apply hy
  refine ⟨1, by norm_num, ?_⟩
  let ray : ℕ → (Fin n → ℤ) := fun k i => ((k + 1 : ℕ) : ℤ) * q i
  have hray : Function.Injective ray := by
    intro a b hab
    have hcoord : ∃ i, q i ≠ 0 := by
      by_contra hall
      apply hq
      funext i
      simpa using not_not.mp (not_exists.mp hall i)
    obtain ⟨i, hi⟩ := hcoord
    have habi := congrFun hab i
    dsimp [ray] at habi
    have : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) :=
      mul_right_cancel₀ hi habi
    exact Nat.add_right_cancel (by exact_mod_cast this)
  refine (Set.infinite_range_of_injective hray).mono ?_
  intro q' hq'
  obtain ⟨k, rfl⟩ := hq'
  refine ⟨0, ?_⟩
  have hdot : dotProd (ray k) y = 0 := by
    calc
      dotProd (ray k) y = ((k + 1 : ℕ) : ℝ) * dotProd q y := by
        simp only [dotProd, ray, Int.cast_mul, Int.cast_natCast]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hzero, mul_zero]
  rw [hdot]
  simp only [Int.cast_zero, add_zero, abs_zero, zero_mul]
  exact (Real.rpow_pos_of_pos (PiPlus_pos (ray k)) _).le

/-- A non-VWMA packet has one global multiplicative Diophantine constant,
including the finitely many low-height characters. -/
theorem exists_global_multiplicativeLinearForm_lower
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : Fin n → ℤ, q ≠ 0 →
      PiPlus q ^ (-eps) ≤ C * |dotProd q y| * PiPlus q := by
  obtain ⟨R, hR, hlarge⟩ :=
    exists_eventual_multiplicativeLinearForm_lower hy heps
  let low : Set (Fin n → ℤ) := {q | PiPlus q ≤ R ∧ q ≠ 0}
  have hlow : low.Finite :=
    (finite_PiPlus_le R).subset fun _ hq => hq.1
  obtain ⟨C₀, hC₀⟩ :=
    (hlow.image fun q => PiPlus q ^ (-eps) / (|dotProd q y| * PiPlus q)).exists_le
  refine ⟨max 1 C₀, le_max_left _ _, ?_⟩
  intro q hq
  have hdot : dotProd q y ≠ 0 := dotProd_ne_zero_of_not_vwma hy hq
  have hdenom : 0 < |dotProd q y| * PiPlus q :=
    mul_pos (abs_pos.mpr hdot) (PiPlus_pos q)
  by_cases hhigh : R < PiPlus q
  · have hbase := (hlarge q hhigh 0).le
    simp only [Int.cast_zero, add_zero] at hbase
    calc
      PiPlus q ^ (-eps) ≤ |dotProd q y| * PiPlus q := hbase
      _ ≤ max 1 C₀ * (|dotProd q y| * PiPlus q) :=
        le_mul_of_one_le_left hdenom.le (le_max_left _ _)
      _ = max 1 C₀ * |dotProd q y| * PiPlus q := by ring
  · have hmem : q ∈ low := ⟨le_of_not_gt hhigh, hq⟩
    have hratio : PiPlus q ^ (-eps) / (|dotProd q y| * PiPlus q) ≤ C₀ :=
      hC₀ _ ⟨q, hmem, rfl⟩
    have hbase : PiPlus q ^ (-eps) ≤ C₀ * (|dotProd q y| * PiPlus q) :=
      (div_le_iff₀ hdenom).mp hratio
    calc
      PiPlus q ^ (-eps) ≤ C₀ * (|dotProd q y| * PiPlus q) := hbase
      _ ≤ max 1 C₀ * (|dotProd q y| * PiPlus q) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hdenom.le
      _ = max 1 C₀ * |dotProd q y| * PiPlus q := by ring

/-- Global moving-window suppression: one constant controls every nonzero
integer character, including all low-height modes. -/
theorem exists_global_characterWindowSuppression
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : Fin n → ℤ, q ≠ 0 →
      ∀ u T : ℝ, 0 < T →
        ‖(1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
            PiPlus q ^ (-eps) ≤
          2 * C * PiPlus q / T := by
  obtain ⟨C, hC, hlinear⟩ :=
    exists_global_multiplicativeLinearForm_lower hy heps
  refine ⟨C, hC, ?_⟩
  intro q hq u T hT
  have hdot : dotProd q y ≠ 0 := dotProd_ne_zero_of_not_vwma hy hq
  have habs : 0 < |dotProd q y| := abs_pos.mpr hdot
  have hosc := norm_integral_exp_window_le hdot u T
  have hoscMul :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          |dotProd q y| ≤ 2 :=
    (le_div_iff₀ habs).mp hosc
  have hweighted :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤
        2 * C * PiPlus q := by
    calc
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤
        ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
          (C * |dotProd q y| * PiPlus q) :=
        mul_le_mul_of_nonneg_left (hlinear q hq) (norm_nonneg _)
      _ = C *
          (‖∫ t in u..(u + T),
            Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
              |dotProd q y|) * PiPlus q := by ring
      _ ≤ C * 2 * PiPlus q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hoscMul (le_trans zero_le_one hC))
          (le_trans zero_le_one (one_le_PiPlus q))
      _ = 2 * C * PiPlus q := by ring
  rw [norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hT.le]
  calc
    (1 / T *
        ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖) *
          PiPlus q ^ (-eps) =
      (1 / T) *
        (‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ *
            PiPlus q ^ (-eps)) := by ring
    _ ≤ (1 / T) * (2 * C * PiPlus q) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = 2 * C * PiPlus q / T := by field_simp

/-- Weighted Fourier ℓ¹ cost natural for multiplicative Diophantine flow. -/
noncomputable def multiplicativeFourierL1Cost
    (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (eps : ℝ) : ℝ :=
  ∑ q ∈ s, ‖c q‖ * (PiPlus q / PiPlus q ^ (-eps))

/-- **Finite-packet discrepancy law.**  For a non-VWMA flow, one draw-dependent
constant controls every translated window and every finite nonconstant Fourier
packet.  Complexity enters only through a multiplicative Fourier ℓ¹ cost; there
is no minimum spectral gap and no worst-character union bound. -/
theorem exists_global_finiteFourierPacketWindowSuppression
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ),
        (∀ q ∈ s, q ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                ∑ q ∈ s, c q *
                  Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ ≤
            (2 * C / T) * multiplicativeFourierL1Cost s c eps := by
  classical
  obtain ⟨C, hC, hchar⟩ :=
    exists_global_characterWindowSuppression hy heps
  refine ⟨C, hC, ?_⟩
  intro s c hs u T hT
  have hsplit :
      (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ q ∈ s, c q *
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I) =
        ∑ q ∈ s, c q *
          ((1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by
        rw [intervalIntegral.integral_const_mul]
        ring
    · intro q _
      exact (intervalIntegrable_exp_mode (dotProd q y) u T).const_mul (c q)
  rw [hsplit]
  calc
    ‖∑ q ∈ s, c q *
        ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))‖ ≤
      ∑ q ∈ s, ‖c q *
        ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ s, (2 * C / T) *
        (‖c q‖ * (PiPlus q / PiPlus q ^ (-eps))) := by
      refine Finset.sum_le_sum fun q hq => ?_
      have hw : 0 < PiPlus q ^ (-eps) :=
        Real.rpow_pos_of_pos (PiPlus_pos q) _
      have hqchar := hchar q (hs q hq) u T hT
      have hmean :
          ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ ≤
            (2 * C * PiPlus q / T) / PiPlus q ^ (-eps) :=
        (le_div_iff₀ hw).2 hqchar
      rw [norm_mul]
      calc
        ‖c q‖ *
            ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)‖ ≤
          ‖c q‖ * ((2 * C * PiPlus q / T) / PiPlus q ^ (-eps)) :=
          mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
        _ = (2 * C / T) *
            (‖c q‖ * (PiPlus q / PiPlus q ^ (-eps))) := by ring
    _ = (2 * C / T) * multiplicativeFourierL1Cost s c eps := by
      rw [multiplicativeFourierL1Cost, Finset.mul_sum]

/-- Centered form: every finite Fourier observable approaches its Haar
constant coefficient uniformly over the starting time of the window. -/
theorem exists_global_finiteFourierPacketHaarDiscrepancy
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a₀ : ℂ) (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ),
        (∀ q ∈ s, q ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖((1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                (a₀ + ∑ q ∈ s, c q *
                  Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))) - a₀‖ ≤
            (2 * C / T) * multiplicativeFourierL1Cost s c eps := by
  classical
  obtain ⟨C, hC, hpacket⟩ :=
    exists_global_finiteFourierPacketWindowSuppression hy heps
  refine ⟨C, hC, ?_⟩
  intro a₀ s c hs u T hT
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ q ∈ s, c q *
        Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))
      MeasureTheory.volume u (u + T) := by
    have hcont : Continuous fun t : ℝ => ∑ q ∈ s, c q *
        Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I) := by
      refine continuous_finsetSum _ fun q _ => ?_
      fun_prop
    exact hcont.intervalIntegrable u (u + T)
  have hcenter :
      ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a₀ + ∑ q ∈ s, c q *
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))) - a₀ =
        (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ q ∈ s, c q *
              Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I) := by
    let J : ℂ := ∫ t in u..(u + T),
      ∑ q ∈ s, c q *
        Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I)
    have hadd :
        (∫ t in u..(u + T),
          (a₀ + ∑ q ∈ s, c q *
            Complex.exp ((t : ℂ) * (dotProd q y : ℂ) * Complex.I))) =
          (T : ℂ) * a₀ + J := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
    rw [hadd]
    change (1 / (T : ℂ)) * ((T : ℂ) * a₀ + J) - a₀ =
      (1 / (T : ℂ)) * J
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
    field_simp
    ring
  rw [hcenter]
  exact hpacket s c hs u T hT

end

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
