import GaloisForLFunctions.RHTower.NearDiagonalBlockBound

/-!
# The dyadic sum of the near-diagonal block bounds

Peeling the bottom dyadic block and keeping the increasing term symbolic, the block estimates sum
to `2500 √(T r/(36 π A)) + 12 √(36 π/(T r)) · Σ_{j<J} √((A 2^j)^(3 : ℕ))` over any range
`[A, B)` with `B ≤ A 2^J`.
-/

namespace RHTower

noncomputable section

/-- The near-diagonal exponential sum over an integer range. -/
def nearDiagonalSum (T r : ℝ) (A B : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico A B,
    Complex.exp (((2 * Real.pi * nearDiagonalPhase T r m : ℝ) : ℂ) * Complex.I)

/-- The symbolic increasing (top-scale) sum of the dyadic block bounds. -/
def nearDiagonalTopSum (A J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, Real.sqrt (((A : ℝ) * 2 ^ j) ^ (3 : ℕ))

theorem nearDiagonalTopSum_nonneg (A J : ℕ) : 0 ≤ nearDiagonalTopSum A J :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem nearDiagonalTopSum_succ (A J : ℕ) :
    nearDiagonalTopSum A (J + 1)
      = Real.sqrt ((A : ℝ) ^ (3 : ℕ)) + nearDiagonalTopSum (2 * A) J := by
  rw [nearDiagonalTopSum, nearDiagonalTopSum, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  push_cast
  ring

theorem nearDiagonalLambda_anti {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {M M' : ℝ}
    (hM : 0 < M) (hMM : M ≤ M') :
    nearDiagonalLambda T r M' ≤ nearDiagonalLambda T r M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM' : (0 : ℝ) < M' := lt_of_lt_of_le hM hMM
  have hcube : M ^ (3 : ℕ) ≤ M' ^ (3 : ℕ) := pow_le_pow_left₀ hM.le hMM 3
  rw [nearDiagonalLambda, nearDiagonalLambda]
  gcongr

theorem sqrt_block_split {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (_hM : 0 ≤ M) :
    Real.sqrt (36 * Real.pi * M ^ (3 : ℕ) / (T * r))
      = Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (M ^ (3 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

theorem sqrt_half_scale {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x / 2) = Real.sqrt x / Real.sqrt 2 := by
  rw [Real.sqrt_div hx]

theorem const_recursion : (720 : ℝ) + 2500 / Real.sqrt 2 ≤ 2500 := by
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ (2 : ℕ)) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hdiv : (2500 : ℝ) / Real.sqrt 2 ≤ 2500 / 1.414 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  linarith

/-- **The dyadic sum of the block bounds.** -/
theorem norm_nearDiagonalSum_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    ∀ (J A B : ℕ), 1 ≤ A → r ≤ (A : ℝ) → B ≤ A * 2 ^ J →
      nearDiagonalLambda T r (A : ℝ) ≤ 1 →
      ‖nearDiagonalSum T r A B‖
        ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A))
          + 12 * Real.sqrt (36 * Real.pi / (T * r)) * nearDiagonalTopSum A J := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  intro J
  induction J with
  | zero =>
    intro A B hA hrA hB hlam
    have hBA : B ≤ A := by simpa using hB
    rw [nearDiagonalSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
    have h1 : 0 ≤ Real.sqrt (T * r / (36 * Real.pi * A)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
    have h3 := nearDiagonalTopSum_nonneg A 0
    nlinarith
  | succ J ih =>
    intro A B hA hrA hB hlam
    have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    by_cases hBA : B ≤ A
    · rw [nearDiagonalSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
      have h1 : 0 ≤ Real.sqrt (T * r / (36 * Real.pi * A)) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
      have h3 := nearDiagonalTopSum_nonneg A (J + 1)
      nlinarith
    · have hAB : A < B := Nat.lt_of_not_le hBA
      set C := min B (2 * A) with hCdef
      have hAC : A ≤ C := le_min hAB.le (by omega)
      have hCB : C ≤ B := min_le_left _ _
      have hACstrict : A < C := lt_min hAB (by omega)
      have hsplit : nearDiagonalSum T r A B
          = nearDiagonalSum T r A C + nearDiagonalSum T r C B := by
        rw [nearDiagonalSum, nearDiagonalSum, nearDiagonalSum,
          ← Finset.sum_Ico_consecutive _ hAC hCB]
      -- the bottom block
      have hblockeq : nearDiagonalSum T r A C
          = ∑ n ∈ Finset.range (C - A),
              Complex.exp (((2 * Real.pi * nearDiagonalPhase T r ((A : ℝ) + n) : ℝ) : ℂ)
                * Complex.I) := by
        rw [nearDiagonalSum, Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 3
        push_cast
        ring
      have hNle : ((C - A : ℕ) : ℝ) ≤ (A : ℝ) := by
        have : C ≤ 2 * A := min_le_right _ _
        have hle : C - A ≤ A := by omega
        exact_mod_cast hle
      have hblock : ‖nearDiagonalSum T r A C‖ ≤ nearDiagonalBlockBound T r (A : ℝ) := by
        rw [hblockeq]
        refine norm_nearDiagonalBlock_le_bound hT hr hA0 hrA (by omega) ?_ hNle hlam
        have : ((C - A - 1 : ℕ) : ℝ) ≤ ((C - A : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith
      -- the tail
      have htail : ‖nearDiagonalSum T r C B‖
          ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A)) / Real.sqrt 2
            + 12 * Real.sqrt (36 * Real.pi / (T * r)) * nearDiagonalTopSum (2 * A) J := by
        by_cases hB2 : B ≤ 2 * A
        · have hCB' : C = B := min_eq_left hB2
          rw [hCB', nearDiagonalSum, Finset.Ico_self, Finset.sum_empty, norm_zero]
          have h1 : 0 ≤ Real.sqrt (T * r / (36 * Real.pi * A)) := Real.sqrt_nonneg _
          have h2 : 0 ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
          have h3 := nearDiagonalTopSum_nonneg (2 * A) J
          have h4 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
          positivity
        · have hC2 : C = 2 * A := min_eq_right (Nat.le_of_not_le hB2)
          have hlam2 : nearDiagonalLambda T r ((2 * A : ℕ) : ℝ) ≤ 1 := by
            refine le_trans (nearDiagonalLambda_anti hT hr hA0 ?_) hlam
            push_cast
            linarith
          have hB' : B ≤ (2 * A) * 2 ^ J := by
            have : A * 2 ^ (J + 1) = (2 * A) * 2 ^ J := by ring
            omega
          have hih := ih (2 * A) B (by omega) (by push_cast; linarith) hB' hlam2
          rw [hC2]
          refine hih.trans (le_of_eq ?_)
          have hcast : ((2 * A : ℕ) : ℝ) = 2 * (A : ℝ) := by push_cast; ring
          have harg : T * r / (36 * Real.pi * (2 * (A : ℝ)))
              = (T * r / (36 * Real.pi * (A : ℝ))) / 2 := by
            rw [div_div]
            congr 1
            ring
          have hfirst : 2500 * Real.sqrt (T * r / (36 * Real.pi * ((2 * A : ℕ) : ℝ)))
              = 2500 * Real.sqrt (T * r / (36 * Real.pi * (A : ℝ))) / Real.sqrt 2 := by
            rw [hcast, harg, sqrt_half_scale (by positivity)]
            ring
          rw [hfirst]
      -- combine
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add hblock htail).trans ?_
      rw [nearDiagonalBlockBound, sqrt_block_split hT hr hA0.le, nearDiagonalTopSum_succ]
      have hs1 : 0 ≤ Real.sqrt (T * r / (36 * Real.pi * A)) := Real.sqrt_nonneg _
      have hs2 : 0 ≤ Real.sqrt (36 * Real.pi / (T * r)) := Real.sqrt_nonneg _
      have hs3 : 0 ≤ Real.sqrt (((A : ℝ)) ^ (3 : ℕ)) := Real.sqrt_nonneg _
      have hs4 := nearDiagonalTopSum_nonneg (2 * A) J
      have hconst := const_recursion
      have hkey : (720 + 2500 / Real.sqrt 2) * Real.sqrt (T * r / (36 * Real.pi * A))
          ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_right hconst hs1
      have hexpand : 12 * Real.sqrt (36 * Real.pi / (T * r))
            * (Real.sqrt ((A : ℝ) ^ (3 : ℕ)) + nearDiagonalTopSum (2 * A) J)
          = 12 * (Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt ((A : ℝ) ^ (3 : ℕ)))
            + 12 * Real.sqrt (36 * Real.pi / (T * r)) * nearDiagonalTopSum (2 * A) J := by
        ring
      have hdiv : 2500 * Real.sqrt (T * r / (36 * Real.pi * A)) / Real.sqrt 2
          = (2500 / Real.sqrt 2) * Real.sqrt (T * r / (36 * Real.pi * A)) := by
        ring
      rw [hexpand, hdiv]
      have hkey2 : 720 * Real.sqrt (T * r / (36 * Real.pi * A))
          + (2500 / Real.sqrt 2) * Real.sqrt (T * r / (36 * Real.pi * A))
          ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A)) := by
        rw [← add_mul]
        exact hkey
      linarith

end

end RHTower
