import GaloisForLFunctions.RHTower.NearDiagonalInnerSum

/-!
# Exponential sums over a phase with reciprocal-cube curvature

The near-diagonal chain proves van der Corput's second-derivative bound for the single phase
`F_r(u) = (T/2π) log(1 + r/u)`.  Every phase produced downstream of Vaughan's identity — in
particular the DIFFERENCE `F_{s₁}(u) − F_{s₂}(u)` that a Cauchy--Schwarz in the type-II sum
creates — has the same reciprocal-cube curvature profile with a different scale.  This file
abstracts the chain: the only input is

`Y/(36π M³) ≤ φ''(u) ≤ 90·Y/(36π M³)` on every dyadic block `[M, 2M]` with `M ≥ M₀`,

and the output is the same two-term estimate `√(Y/A) + √(B³/Y)`.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- The dyadic curvature scale of a phase with reciprocal-cube curvature. -/
def curvedLambda (Y M : ℝ) : ℝ := Y / (36 * Real.pi * M ^ 3)

/-- A phase whose second derivative is pinned to `Y/M³` on every dyadic block above `M₀`. -/
structure CurvedPhase (φ φ' φ'' : ℝ → ℝ) (Y M₀ : ℝ) : Prop where
  M₀_pos : 0 < M₀
  Y_pos : 0 < Y
  deriv₁ : ∀ u : ℝ, M₀ ≤ u → HasDerivAt φ (φ' u) u
  deriv₂ : ∀ u : ℝ, M₀ ≤ u → HasDerivAt φ' (φ'' u) u
  curv_lo : ∀ M u : ℝ, M₀ ≤ M → M ≤ u → u ≤ 2 * M → curvedLambda Y M ≤ φ'' u
  curv_hi : ∀ M u : ℝ, M₀ ≤ M → M ≤ u → u ≤ 2 * M → φ'' u ≤ 90 * curvedLambda Y M

theorem curvedLambda_pos {Y M : ℝ} (hY : 0 < Y) (hM : 0 < M) : 0 < curvedLambda Y M := by
  rw [curvedLambda]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

theorem curvedLambda_anti {Y : ℝ} (hY : 0 < Y) {M M' : ℝ} (hM : 0 < M) (hMM : M ≤ M') :
    curvedLambda Y M' ≤ curvedLambda Y M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM' : (0 : ℝ) < M' := lt_of_lt_of_le hM hMM
  have hcube : M ^ 3 ≤ M' ^ 3 := pow_le_pow_left₀ hM.le hMM 3
  rw [curvedLambda, curvedLambda]
  gcongr

/-- The raw second-derivative bound on a block of `N` unit-spaced points at scale `M`. -/
theorem norm_curvedBlock_le {φ φ' φ'' : ℝ → ℝ} {Y M₀ : ℝ} (h : CurvedPhase φ φ' φ'' Y M₀)
    {M : ℝ} (hM : M₀ ≤ M) {N : ℕ} (hN : 1 ≤ N) (hspan : (((N : ℕ) - 1 : ℕ) : ℝ) ≤ M)
    (hlam1 : curvedLambda Y M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * φ (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ (2 * (N : ℝ) * 90 * curvedLambda Y M + 3)
          * (3 / Real.sqrt (curvedLambda Y M) + 1) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le h.M₀_pos hM
  have hlam0 : 0 < curvedLambda Y M := curvedLambda_pos h.Y_pos hM0
  have hmemsub : ∀ x ∈ Set.Icc M (M + (((N : ℕ) - 1 : ℕ) : ℝ)), M ≤ x ∧ x ≤ 2 * M := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨hx1, by linarith⟩
  refine second_derivative_test φ φ' φ'' M N hN hlam0 hlam1 ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, -⟩ := hmemsub x hx
    exact h.deriv₁ x (le_trans hM hx1)
  · intro x hx
    obtain ⟨hx1, -⟩ := hmemsub x hx
    exact h.deriv₂ x (le_trans hM hx1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hmemsub x hx
    exact h.curv_lo M x hM hx1 hx2
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hmemsub x hx
    exact h.curv_hi M x hM hx1 hx2

/-- The clean dyadic block bound. -/
def curvedBlockBound (Y M : ℝ) : ℝ :=
  720 * Real.sqrt (Y / (36 * Real.pi * M)) + 12 * Real.sqrt (36 * Real.pi * M ^ 3 / Y)

theorem mul_sqrt_curvedLambda {Y M : ℝ} (hM : 0 < M) :
    M * Real.sqrt (curvedLambda Y M) = Real.sqrt (Y / (36 * Real.pi * M)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : M * Real.sqrt (curvedLambda Y M) = Real.sqrt (M ^ 2 * curvedLambda Y M) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le]
  rw [h]
  congr 1
  rw [curvedLambda]
  field_simp

theorem inv_sqrt_curvedLambda {Y M : ℝ} (hY : 0 < Y) (hM : 0 < M) :
    1 / Real.sqrt (curvedLambda Y M) = Real.sqrt (36 * Real.pi * M ^ 3 / Y) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [one_div, ← Real.sqrt_inv, curvedLambda]
  congr 1
  field_simp

/-- **The clean dyadic block estimate.** -/
theorem norm_curvedBlock_le_bound {φ φ' φ'' : ℝ → ℝ} {Y M₀ : ℝ} (h : CurvedPhase φ φ' φ'' Y M₀)
    {M : ℝ} (hM : M₀ ≤ M) {N : ℕ} (hN : 1 ≤ N) (hspan : (((N : ℕ) - 1 : ℕ) : ℝ) ≤ M)
    (hNM : (N : ℝ) ≤ M) (hlam1 : curvedLambda Y M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * φ (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ curvedBlockBound Y M := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le h.M₀_pos hM
  have hlam0 : 0 < curvedLambda Y M := curvedLambda_pos h.Y_pos hM0
  set s : ℝ := Real.sqrt (curvedLambda Y M) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hlam0
  have hs1 : s ≤ 1 := by
    rw [hsdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hlam1
  have hssq : s ^ 2 = curvedLambda Y M := Real.sq_sqrt hlam0.le
  have hraw := norm_curvedBlock_le h hM hN hspan hlam1
  refine hraw.trans ?_
  have hgoal : (2 * (N : ℝ) * 90 * curvedLambda Y M + 3) * (3 / s + 1)
      ≤ 720 * (M * s) + 12 * (1 / s) := by
    have hb := block_algebra hs0 hs1 (Nat.cast_nonneg N) hNM
    rwa [hssq] at hb
  refine hgoal.trans (le_of_eq ?_)
  rw [curvedBlockBound, hsdef, mul_sqrt_curvedLambda hM0,
    ← inv_sqrt_curvedLambda h.Y_pos hM0]

/-- The exponential sum of a curved phase over an integer range. -/
def curvedSum (φ : ℝ → ℝ) (A B : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico A B, Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)

theorem sqrt_curved_block_split {Y M : ℝ} (hY : 0 < Y) (_hM : 0 ≤ M) :
    Real.sqrt (36 * Real.pi * M ^ 3 / Y)
      = Real.sqrt (36 * Real.pi / Y) * Real.sqrt (M ^ 3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- **The dyadic sum of the curved block bounds.** -/
theorem norm_curvedSum_le {φ φ' φ'' : ℝ → ℝ} {Y M₀ : ℝ} (h : CurvedPhase φ φ' φ'' Y M₀) :
    ∀ (J A B : ℕ), 1 ≤ A → M₀ ≤ (A : ℝ) → B ≤ A * 2 ^ J →
      curvedLambda Y (A : ℝ) ≤ 1 →
      ‖curvedSum φ A B‖
        ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * A))
          + 12 * Real.sqrt (36 * Real.pi / Y) * nearDiagonalTopSum A J := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  intro J
  induction J with
  | zero =>
    intro A B hA hMA hB hlam
    have hBA : B ≤ A := by simpa using hB
    rw [curvedSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
    have h1 : 0 ≤ Real.sqrt (Y / (36 * Real.pi * A)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (36 * Real.pi / Y) := Real.sqrt_nonneg _
    have h3 := nearDiagonalTopSum_nonneg A 0
    nlinarith
  | succ J ih =>
    intro A B hA hMA hB hlam
    have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    by_cases hBA : B ≤ A
    · rw [curvedSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
      have h1 : 0 ≤ Real.sqrt (Y / (36 * Real.pi * A)) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (36 * Real.pi / Y) := Real.sqrt_nonneg _
      have h3 := nearDiagonalTopSum_nonneg A (J + 1)
      nlinarith
    · have hAB : A < B := Nat.lt_of_not_le hBA
      set C := min B (2 * A) with hCdef
      have hAC : A ≤ C := le_min hAB.le (by omega)
      have hCB : C ≤ B := min_le_left _ _
      have hsplit : curvedSum φ A B = curvedSum φ A C + curvedSum φ C B := by
        rw [curvedSum, curvedSum, curvedSum, ← Finset.sum_Ico_consecutive _ hAC hCB]
      have hblockeq : curvedSum φ A C
          = ∑ n ∈ Finset.range (C - A),
              Complex.exp (((2 * Real.pi * φ ((A : ℝ) + n) : ℝ) : ℂ) * Complex.I) := by
        rw [curvedSum, Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 3
        push_cast
        ring
      have hNle : ((C - A : ℕ) : ℝ) ≤ (A : ℝ) := by
        have : C ≤ 2 * A := min_le_right _ _
        have hle : C - A ≤ A := by omega
        exact_mod_cast hle
      have hblock : ‖curvedSum φ A C‖ ≤ curvedBlockBound Y (A : ℝ) := by
        rw [hblockeq]
        refine norm_curvedBlock_le_bound h hMA (by omega) ?_ hNle hlam
        have : ((C - A - 1 : ℕ) : ℝ) ≤ ((C - A : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith
      have htail : ‖curvedSum φ C B‖
          ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * A)) / Real.sqrt 2
            + 12 * Real.sqrt (36 * Real.pi / Y) * nearDiagonalTopSum (2 * A) J := by
        by_cases hB2 : B ≤ 2 * A
        · have hCB' : C = B := min_eq_left hB2
          rw [hCB', curvedSum, Finset.Ico_self, Finset.sum_empty, norm_zero]
          have h1 : 0 ≤ Real.sqrt (Y / (36 * Real.pi * A)) := Real.sqrt_nonneg _
          have h2 : 0 ≤ Real.sqrt (36 * Real.pi / Y) := Real.sqrt_nonneg _
          have h3 := nearDiagonalTopSum_nonneg (2 * A) J
          have h4 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
          positivity
        · have hC2 : C = 2 * A := min_eq_right (Nat.le_of_not_le hB2)
          have hlam2 : curvedLambda Y ((2 * A : ℕ) : ℝ) ≤ 1 := by
            refine le_trans (curvedLambda_anti h.Y_pos hA0 ?_) hlam
            push_cast
            linarith
          have hB' : B ≤ (2 * A) * 2 ^ J := by
            have : A * 2 ^ (J + 1) = (2 * A) * 2 ^ J := by ring
            omega
          have hMA2 : M₀ ≤ ((2 * A : ℕ) : ℝ) := by
            refine le_trans hMA ?_
            push_cast
            linarith
          have hih := ih (2 * A) B (by omega) hMA2 hB' hlam2
          rw [hC2]
          refine hih.trans (le_of_eq ?_)
          have hcast : ((2 * A : ℕ) : ℝ) = 2 * (A : ℝ) := by push_cast; ring
          have harg : Y / (36 * Real.pi * (2 * (A : ℝ)))
              = (Y / (36 * Real.pi * (A : ℝ))) / 2 := by
            rw [div_div]
            congr 1
            ring
          have hfirst : 2500 * Real.sqrt (Y / (36 * Real.pi * ((2 * A : ℕ) : ℝ)))
              = 2500 * Real.sqrt (Y / (36 * Real.pi * (A : ℝ))) / Real.sqrt 2 := by
            rw [hcast, harg, sqrt_half_scale (div_nonneg h.Y_pos.le (by positivity))]
            ring
          rw [hfirst]
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add hblock htail).trans ?_
      rw [curvedBlockBound, sqrt_curved_block_split h.Y_pos hA0.le, nearDiagonalTopSum_succ]
      have hs1 : 0 ≤ Real.sqrt (Y / (36 * Real.pi * A)) := Real.sqrt_nonneg _
      have hs2 : 0 ≤ Real.sqrt (36 * Real.pi / Y) := Real.sqrt_nonneg _
      have hs3 : 0 ≤ Real.sqrt (((A : ℝ)) ^ 3) := Real.sqrt_nonneg _
      have hs4 := nearDiagonalTopSum_nonneg (2 * A) J
      have hconst := const_recursion
      have hkey : (720 + 2500 / Real.sqrt 2) * Real.sqrt (Y / (36 * Real.pi * A))
          ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_right hconst hs1
      have hexpand : 12 * Real.sqrt (36 * Real.pi / Y)
            * (Real.sqrt ((A : ℝ) ^ 3) + nearDiagonalTopSum (2 * A) J)
          = 12 * (Real.sqrt (36 * Real.pi / Y) * Real.sqrt ((A : ℝ) ^ 3))
            + 12 * Real.sqrt (36 * Real.pi / Y) * nearDiagonalTopSum (2 * A) J := by
        ring
      have hdiv : 2500 * Real.sqrt (Y / (36 * Real.pi * A)) / Real.sqrt 2
          = (2500 / Real.sqrt 2) * Real.sqrt (Y / (36 * Real.pi * A)) := by
        ring
      rw [hexpand, hdiv]
      have hkey2 : 720 * Real.sqrt (Y / (36 * Real.pi * A))
          + (2500 / Real.sqrt 2) * Real.sqrt (Y / (36 * Real.pi * A))
          ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * A)) := by
        rw [← add_mul]
        exact hkey
      linarith

/-- **The curved-phase exponential sum over an arbitrary range.** -/
theorem norm_curvedSum_le_final {φ φ' φ'' : ℝ → ℝ} {Y M₀ : ℝ} (h : CurvedPhase φ φ' φ'' Y M₀)
    (A B : ℕ) (hA : 1 ≤ A) (hMA : M₀ ≤ (A : ℝ)) (hlam : curvedLambda Y (A : ℝ) ≤ 1) :
    ‖curvedSum φ A B‖
      ≤ 2500 * Real.sqrt (Y / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / Y) * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs2 : 0 ≤ Real.sqrt (36 * Real.pi / Y) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (Y / (36 * Real.pi * A)) := Real.sqrt_nonneg _
  by_cases hBA : B ≤ A
  · rw [curvedSum, Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty, norm_zero]
    have h3 : 0 ≤ Real.sqrt (((B : ℝ)) ^ 3) := Real.sqrt_nonneg _
    nlinarith
  · have hAB : A < B := Nat.lt_of_not_le hBA
    set Jmin := Nat.find (exists_dyadic_cover_nat A B hA) with hJmin
    have hcover : B ≤ A * 2 ^ Jmin := Nat.find_spec (exists_dyadic_cover_nat A B hA)
    have hJpos : 1 ≤ Jmin := by
      by_contra hcon
      have hJ0 : Jmin = 0 := by omega
      rw [hJ0, pow_zero, mul_one] at hcover
      omega
    have htop : (A : ℝ) * 2 ^ Jmin ≤ 2 * (B : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j, Jmin = j + 1 := ⟨Jmin - 1, by omega⟩
      have hjlt : j < Nat.find (exists_dyadic_cover_nat A B hA) := by
        rw [← hJmin, hj]
        omega
      have hnot : ¬ (B ≤ A * 2 ^ j) := Nat.find_min (exists_dyadic_cover_nat A B hA) hjlt
      have hlt : A * 2 ^ j < B := Nat.lt_of_not_le hnot
      have hcast : ((A * 2 ^ j : ℕ) : ℝ) < (B : ℝ) := by exact_mod_cast hlt
      push_cast at hcast
      rw [hj, show (A : ℝ) * 2 ^ (j + 1) = 2 * ((A : ℝ) * 2 ^ j) by ring]
      linarith
    have hmain := norm_curvedSum_le h Jmin A B hA hMA hcover hlam
    refine hmain.trans ?_
    have hcol := nearDiagonalTopSum_le A Jmin
    have hmono : Real.sqrt (((A : ℝ) * 2 ^ Jmin) ^ 3) ≤ Real.sqrt ((2 * (B : ℝ)) ^ 3) := by
      refine Real.sqrt_le_sqrt ?_
      have hnn : (0 : ℝ) ≤ (A : ℝ) * 2 ^ Jmin := by positivity
      exact pow_le_pow_left₀ hnn htop 3
    have hcube : Real.sqrt ((2 * (B : ℝ)) ^ 3) = 2 * Real.sqrt 2 * Real.sqrt (((B : ℝ)) ^ 3) := by
      rw [show (2 * (B : ℝ)) ^ 3 = ((B : ℝ)) ^ 3 * 8 by ring, Real.sqrt_mul (by positivity)]
      have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      rw [h8]
      ring
    have hsq2 : Real.sqrt 2 ≤ 1.5 := by
      rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hfin : nearDiagonalTopSum A Jmin ≤ (9 / 5 : ℝ) * Real.sqrt (((B : ℝ)) ^ 3) := by
      refine hcol.trans ?_
      rw [hcube] at hmono
      have hB3 : 0 ≤ Real.sqrt (((B : ℝ)) ^ 3) := Real.sqrt_nonneg _
      nlinarith [hmono, hB3]
    have hprod : 12 * Real.sqrt (36 * Real.pi / Y) * nearDiagonalTopSum A Jmin
        ≤ 22 * Real.sqrt (36 * Real.pi / Y) * Real.sqrt (((B : ℝ)) ^ 3) := by
      have h12 : (0 : ℝ) ≤ 12 * Real.sqrt (36 * Real.pi / Y) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hfin h12
      have hQB : (0 : ℝ) ≤ Real.sqrt (36 * Real.pi / Y) * Real.sqrt (((B : ℝ)) ^ 3) :=
        mul_nonneg hs2 (Real.sqrt_nonneg _)
      linarith [hmul, hQB]
    linarith [hmain, hprod]

end

end RHTower.Sieve
