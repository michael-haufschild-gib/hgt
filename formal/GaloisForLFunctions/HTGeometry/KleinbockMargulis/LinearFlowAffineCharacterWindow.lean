import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowIndexedFourierPacketWindow

open Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

noncomputable section

variable {n : ℕ}

/-- Strong extremality excludes every exact nonconstant affine integer
character. -/
theorem affineDot_ne_zero_of_not_vwma
    {y : Fin n → ℝ} (hy : ¬ VWMA y)
    (p : ℤ) (q : Fin n → ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    dotProd q y + (p : ℝ) ≠ 0 := by
  by_cases hq : q = 0
  · subst q
    simp only [dotProd, Pi.zero_apply, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    exact_mod_cast hpq.resolve_right (by simp)
  · intro hzero
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
    refine ⟨((k + 1 : ℕ) : ℤ) * p, ?_⟩
    have hdot : dotProd (ray k) y =
        ((k + 1 : ℕ) : ℝ) * dotProd q y := by
      simp only [dotProd, ray, Int.cast_mul, Int.cast_natCast]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsum : dotProd (ray k) y +
        ((((k + 1 : ℕ) : ℤ) * p : ℤ) : ℝ) = 0 := by
      rw [hdot]
      push_cast
      rw [← mul_add, hzero, mul_zero]
    rw [hsum, abs_zero, zero_mul]
    exact (Real.rpow_pos_of_pos (PiPlus_pos (ray k)) _).le

/-- Nearest integer realizes the smallest affine frequency for fixed `q`. -/
theorem abs_affineDot_round_le
    (y : Fin n → ℝ) (q : Fin n → ℤ) (p : ℤ) :
    |dotProd q y + ((round (-dotProd q y) : ℤ) : ℝ)| ≤
      |dotProd q y + (p : ℝ)| := by
  calc
    |dotProd q y + ((round (-dotProd q y) : ℤ) : ℝ)| =
        |-dotProd q y - ((round (-dotProd q y) : ℤ) : ℝ)| := by
      rw [show -dotProd q y - ((round (-dotProd q y) : ℤ) : ℝ) =
        -(dotProd q y + ((round (-dotProd q y) : ℤ) : ℝ)) by ring, abs_neg]
    _ ≤ |-dotProd q y - (p : ℝ)| := round_le (-dotProd q y) p
    _ = |dotProd q y + (p : ℝ)| := by
      rw [show -dotProd q y - (p : ℝ) = -(dotProd q y + (p : ℝ)) by ring, abs_neg]

/-- One global Diophantine constant controls all nonconstant affine
characters, including clock harmonics. -/
theorem exists_global_affineMultiplicativeLinearForm_lower
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℤ) (q : Fin n → ℤ),
      (p ≠ 0 ∨ q ≠ 0) →
      PiPlus q ^ (-eps) ≤ C * |dotProd q y + (p : ℝ)| * PiPlus q := by
  obtain ⟨R, hR, hlarge⟩ :=
    exists_eventual_multiplicativeLinearForm_lower hy heps
  let low : Set (Fin n → ℤ) := {q | PiPlus q ≤ R ∧ q ≠ 0}
  have hlow : low.Finite :=
    (finite_PiPlus_le R).subset fun _ hq => hq.1
  let nearest : (Fin n → ℤ) → ℤ := fun q => round (-dotProd q y)
  obtain ⟨C0, hC0⟩ :=
    (hlow.image fun q =>
      PiPlus q ^ (-eps) /
        (|dotProd q y + (nearest q : ℝ)| * PiPlus q)).exists_le
  refine ⟨max 1 C0, le_max_left _ _, ?_⟩
  intro p q hpq
  by_cases hq : q = 0
  · subst q
    have hp : p ≠ 0 := hpq.resolve_right (by simp)
    have habs : (1 : ℝ) ≤ |(p : ℝ)| := by exact_mod_cast Int.one_le_abs hp
    simp only [PiPlus, Pi.zero_apply, Int.cast_zero, abs_zero, max_eq_right zero_le_one,
      Finset.prod_const_one, Real.one_rpow, dotProd, zero_mul, Finset.sum_const_zero,
      zero_add, mul_one]
    exact le_trans habs (le_mul_of_one_le_left (abs_nonneg _) (le_max_left _ _))
  · have hfreq : dotProd q y + (nearest q : ℝ) ≠ 0 :=
      affineDot_ne_zero_of_not_vwma hy (nearest q) q (Or.inr hq)
    have hdenom : 0 < |dotProd q y + (nearest q : ℝ)| * PiPlus q :=
      mul_pos (abs_pos.mpr hfreq) (PiPlus_pos q)
    by_cases hhigh : R < PiPlus q
    · have hbase := (hlarge q hhigh p).le
      calc
        PiPlus q ^ (-eps) ≤ |dotProd q y + (p : ℝ)| * PiPlus q := hbase
        _ ≤ max 1 C0 * (|dotProd q y + (p : ℝ)| * PiPlus q) :=
          le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) (PiPlus_pos q).le)
            (le_max_left _ _)
        _ = max 1 C0 * |dotProd q y + (p : ℝ)| * PiPlus q := by ring
    · have hmem : q ∈ low := ⟨le_of_not_gt hhigh, hq⟩
      have hratio : PiPlus q ^ (-eps) /
          (|dotProd q y + (nearest q : ℝ)| * PiPlus q) ≤ C0 :=
        hC0 _ ⟨q, hmem, rfl⟩
      have hbase : PiPlus q ^ (-eps) ≤
          C0 * (|dotProd q y + (nearest q : ℝ)| * PiPlus q) :=
        (div_le_iff₀ hdenom).mp hratio
      have hnearest := abs_affineDot_round_le y q p
      calc
        PiPlus q ^ (-eps) ≤
            C0 * (|dotProd q y + (nearest q : ℝ)| * PiPlus q) := hbase
        _ ≤ max 1 C0 * (|dotProd q y + (nearest q : ℝ)| * PiPlus q) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg (abs_nonneg _) (PiPlus_pos q).le)
        _ ≤ max 1 C0 * (|dotProd q y + (p : ℝ)| * PiPlus q) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnearest (PiPlus_pos q).le)
            (le_trans zero_le_one (le_max_left _ _))
        _ = max 1 C0 * |dotProd q y + (p : ℝ)| * PiPlus q := by ring

/-- Global moving-window suppression for every nonconstant affine
character. -/
theorem exists_global_affineCharacterWindowSuppression
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℤ) (q : Fin n → ℤ),
      (p ≠ 0 ∨ q ≠ 0) → ∀ u T : ℝ, 0 < T →
        ‖(1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              Complex.exp ((t : ℂ) *
                ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
            PiPlus q ^ (-eps) ≤
          2 * C * PiPlus q / T := by
  obtain ⟨C, hC, hlinear⟩ :=
    exists_global_affineMultiplicativeLinearForm_lower hy heps
  refine ⟨C, hC, ?_⟩
  intro p q hpq u T hT
  have hfreq : dotProd q y + (p : ℝ) ≠ 0 :=
    affineDot_ne_zero_of_not_vwma hy p q hpq
  have habs : 0 < |dotProd q y + (p : ℝ)| := abs_pos.mpr hfreq
  have hosc := norm_integral_exp_window_le hfreq u T
  have hoscMul :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
          |dotProd q y + (p : ℝ)| ≤ 2 :=
    (le_div_iff₀ habs).mp hosc
  have hweighted :
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤ 2 * C * PiPlus q := by
    calc
      ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps) ≤
        ‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
          (C * |dotProd q y + (p : ℝ)| * PiPlus q) :=
        mul_le_mul_of_nonneg_left (hlinear p q hpq) (norm_nonneg _)
      _ = C *
          (‖∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
            |dotProd q y + (p : ℝ)|) * PiPlus q := by ring
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
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖) *
          PiPlus q ^ (-eps) =
      (1 / T) *
        (‖∫ t in u..(u + T),
          Complex.exp ((t : ℂ) *
            ((dotProd q y + (p : ℝ) : ℝ) : ℂ) * Complex.I)‖ *
          PiPlus q ^ (-eps)) := by ring
    _ ≤ (1 / T) * (2 * C * PiPlus q) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = 2 * C * PiPlus q / T := by field_simp

variable {ι : Type*} [Fintype ι]

/-- Indexed affine packet discrepancy. Equal full-projective characters
may occur on many sheets; all multiplicity is retained. -/
theorem exists_global_indexedAffineFourierPacketHaarDiscrepancy
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a0 : ℂ) (c : ι → ℂ) (p : ι → ℤ) (q : ι → Fin n → ℤ),
        (∀ i, p i ≠ 0 ∨ q i ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖((1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                (a0 + ∑ i, c i * Complex.exp
                  ((t : ℂ) *
                    ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))) - a0‖ ≤
            (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
  classical
  obtain ⟨C, hC, hchar⟩ :=
    exists_global_affineCharacterWindowSuppression hy heps
  refine ⟨C, hC, ?_⟩
  intro a0 c p q hpq u T hT
  have hsplit :
      (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I) =
        ∑ i, c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [intervalIntegral.integral_const_mul]
        ring
    · intro i _
      exact (intervalIntegrable_exp_mode
        (dotProd (q i) y + (p i : ℝ)) u T).const_mul (c i)
  have hosc :
      ‖(1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
    rw [hsplit]
    calc
      ‖∑ i, c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        ∑ i, ‖c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) *
              ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, (2 * C / T) *
          (‖c i‖ * (PiPlus (q i) / PiPlus (q i) ^ (-eps))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw : 0 < PiPlus (q i) ^ (-eps) :=
          Real.rpow_pos_of_pos (PiPlus_pos (q i)) _
        have hi := hchar (p i) (q i) (hpq i) u T hT
        have hmean :
            ‖(1 / (T : ℂ)) *
                ∫ t in u..(u + T),
                  Complex.exp ((t : ℂ) *
                    ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
              (2 * C * PiPlus (q i) / T) / PiPlus (q i) ^ (-eps) :=
          (le_div_iff₀ hw).2 hi
        rw [norm_mul]
        calc
          ‖c i‖ *
              ‖(1 / (T : ℂ)) *
                ∫ t in u..(u + T),
                  Complex.exp ((t : ℂ) *
                    ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
            ‖c i‖ * ((2 * C * PiPlus (q i) / T) /
              PiPlus (q i) ^ (-eps)) :=
            mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
          _ = (2 * C / T) *
              (‖c i‖ * (PiPlus (q i) / PiPlus (q i) ^ (-eps))) := by ring
      _ = (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
        rw [indexedMultiplicativeFourierL1Cost, Finset.mul_sum]
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) * ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume u (u + T) := by
    have hcont : Continuous fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) * ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I) := by
      refine continuous_finsetSum _ fun i _ => ?_
      fun_prop
    exact hcont.intervalIntegrable u (u + T)
  have hcenter :
      ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a0 + ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))) - a0 =
        (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) *
                ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I) := by
    let J : ℂ := ∫ t in u..(u + T),
      ∑ i, c i * Complex.exp
        ((t : ℂ) * ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I)
    have hadd :
        (∫ t in u..(u + T),
          (a0 + ∑ i, c i * Complex.exp
            ((t : ℂ) *
              ((dotProd (q i) y + (p i : ℝ) : ℝ) : ℂ) * Complex.I))) =
          (T : ℂ) * a0 + J := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
    rw [hadd]
    change (1 / (T : ℂ)) * ((T : ℂ) * a0 + J) - a0 =
      (1 / (T : ℂ)) * J
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
    field_simp
    ring
  rw [hcenter]
  exact hosc

end

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
