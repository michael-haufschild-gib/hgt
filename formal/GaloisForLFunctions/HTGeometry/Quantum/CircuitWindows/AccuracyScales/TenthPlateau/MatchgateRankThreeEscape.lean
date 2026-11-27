import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.SpinFermionRankTwoBarrier

/-! # `U(2)^⊗N`-invariant full bond-determinant conditioning and matchgate `so(2N)` escape

This module formulates the `U(2)^⊗N`-gauge-invariant full bond determinant + longitudinal-field
bulk event `Ω_rk3(n, η)` (`bondRankThreeFieldEvent n η`) on the `1`D `N = n + 2` qubit Pauli chain
and proves that it simultaneously eliminates all locally rotated Ising chains, the entire locally
rotated `(5N - 4)`-dimensional matchgate / `so(2N)` free-fermion manifold, and every nonlocal
Pauli-Majorana Clifford quadratic subalgebra, abstracting Clifford quadratic-vs-quartic
orthogonality over general `C*`-algebras `{A : Type*} [CStarAlgebra A]`:

1. **Sharp `3 × 3` determinant-to-singular-matrix Frobenius bound:**
   - `four_det3_sq_le_frob_fourth_mul_dist_sq`: for all `B, M : Matrix (Fin 3) (Fin 3) ℝ` with
     `M.det = 0`, `4 * B.det ^ 2 ≤ frobSq3 B ^ 2 * frobSq3 (B - M)`.
2. **Product-Gaussian tail of `Ω_rk3(n, η)` (`bondRankThreeFieldEvent`):**
   - `bondRankThreeFieldEvent_compl_prob_le`: general `(r₁, r₂)` cofactor-pivot bound and sharp
     `η ∈ [0, 1]` specialization `ℙ(Ω_rk3(n, η)ᶜ) ≤ (38 * n + 39) * η ^ 2`.
3. **Simultaneous `U(2)^⊗N`-gauge-invariant separation from rotated Ising and matchgate manifolds:**
   - `locallyRotated_bondDetZero_operator_dist_ge`,
     `locallyRotatedIsing_operator_dist_ge_of_bondDet`, and
     `locallyRotatedMatchgate_operator_dist_ge_of_bondDet`: for every local unitary tuple
     `R : Fin (n + 2) → U(2)` and every shell `v` with `det (bondMatrix v e) = 0` (including all
     diagonal Ising shells and all `(5N - 4)`-parameter `so(2N)` matchgate shells
     `isMatchgateChainLabel`),
     `4 * (bondMatrix u e).det ^ 2 ≤ frobSq3 (bondMatrix u e) ^ 2 * ‖H(u) - W H(v) W*‖²`.
4. **Abstract `C*`-algebra Clifford quadratic-vs-quartic exclusion and nonlocal Pauli-Majorana escape:**
   - `not_mem_cliffordQuadraticSpan_of_commuting_triple` and
     `not_mem_pauliMajoranaQuadraticSpan_of_bondDet_ne_zero`: over any nontrivial `C*`-algebra `A`,
     no commuting non-proportional quadratic Clifford pair `Γ_{a₀} Γ_{b₀}, Γ_{a₁} Γ_{b₁}` can have
     its product in `cliffordQuadraticSpan Γ`; hence any chain `u` with `(bondMatrix u e).det ≠ 0`
     is excluded from the quadratic `so(2N)` span of **every** (even nonlocal) Pauli-Majorana
     Clifford frame on `Register (n + 2)`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool

/-! ## Section 1: Sharp `3 × 3` determinant-to-singular-matrix Frobenius inequality -/

private def colCross3 (M : Matrix (Fin 3) (Fin 3) ℝ) (q₁ q₂ : Fin 3) : Fin 3 → ℝ
  | 0 => M 1 q₁ * M 2 q₂ - M 2 q₁ * M 1 q₂
  | 1 => M 2 q₁ * M 0 q₂ - M 0 q₁ * M 2 q₂
  | 2 => M 0 q₁ * M 1 q₂ - M 1 q₁ * M 0 q₂

private theorem exists_unit_left_ker_of_det3_eq_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hdet : M.det = 0) :
    ∃ u : Fin 3 → ℝ,
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 ∧
      ∀ q : Fin 3, u 0 * M 0 q + u 1 * M 1 q + u 2 * M 2 q = 0 := by
  have hnorm_unit {v : Fin 3 → ℝ}
      (hv_pos : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
      (hv_ker : ∀ q : Fin 3, v 0 * M 0 q + v 1 * M 1 q + v 2 * M 2 q = 0) :
      ∃ u : Fin 3 → ℝ,
        u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 ∧
        ∀ q : Fin 3, u 0 * M 0 q + u 1 * M 1 q + u 2 * M 2 q = 0 := by
    let r := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hv_pos
    have hr_sq : r ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := Real.sq_sqrt hv_pos.le
    refine ⟨fun p => v p / r, ?_, fun q => ?_⟩
    · field_simp [hr_pos.ne']
      linarith only [hr_sq]
    · have hq := hv_ker q
      calc (v 0 / r) * M 0 q + (v 1 / r) * M 1 q + (v 2 / r) * M 2 q
          = (v 0 * M 0 q + v 1 * M 1 q + v 2 * M 2 q) / r := by ring
        _ = 0 := by rw [hq, zero_div]
  have hdet_exp : M.det =
      M 0 0 * (M 1 1 * M 2 2 - M 2 1 * M 1 2) +
      M 1 0 * (M 2 1 * M 0 2 - M 0 1 * M 2 2) +
      M 2 0 * (M 0 1 * M 1 2 - M 1 1 * M 0 2) := by
    rw [Matrix.det_fin_three]; ring
  let c₁₂ := colCross3 M 1 2
  let c₂₀ := colCross3 M 2 0
  let c₀₁ := colCross3 M 0 1
  by_cases hc₁₂ : 0 < c₁₂ 0 ^ 2 + c₁₂ 1 ^ 2 + c₁₂ 2 ^ 2
  · refine hnorm_unit hc₁₂ fun q => ?_
    fin_cases q
    · dsimp [c₁₂, colCross3]; linarith only [hdet, hdet_exp]
    · dsimp [c₁₂, colCross3]; ring
    · dsimp [c₁₂, colCross3]; ring
  · by_cases hc₂₀ : 0 < c₂₀ 0 ^ 2 + c₂₀ 1 ^ 2 + c₂₀ 2 ^ 2
    · refine hnorm_unit hc₂₀ fun q => ?_
      fin_cases q
      · dsimp [c₂₀, colCross3]; ring
      · dsimp [c₂₀, colCross3]; linarith only [hdet, hdet_exp]
      · dsimp [c₂₀, colCross3]; ring
    · by_cases hc₀₁ : 0 < c₀₁ 0 ^ 2 + c₀₁ 1 ^ 2 + c₀₁ 2 ^ 2
      · refine hnorm_unit hc₀₁ fun q => ?_
        fin_cases q
        · dsimp [c₀₁, colCross3]; ring
        · dsimp [c₀₁, colCross3]; ring
        · dsimp [c₀₁, colCross3]; linarith only [hdet, hdet_exp]
      · have hz₁₂ : c₁₂ 0 = 0 ∧ c₁₂ 1 = 0 ∧ c₁₂ 2 = 0 := by
          refine ⟨?_, ?_, ?_⟩ <;>
            nlinarith only [hc₁₂, sq_nonneg (c₁₂ 0), sq_nonneg (c₁₂ 1), sq_nonneg (c₁₂ 2)]
        have hz₂₀ : c₂₀ 0 = 0 ∧ c₂₀ 1 = 0 ∧ c₂₀ 2 = 0 := by
          refine ⟨?_, ?_, ?_⟩ <;>
            nlinarith only [hc₂₀, sq_nonneg (c₂₀ 0), sq_nonneg (c₂₀ 1), sq_nonneg (c₂₀ 2)]
        have hz₀₁ : c₀₁ 0 = 0 ∧ c₀₁ 1 = 0 ∧ c₀₁ 2 = 0 := by
          refine ⟨?_, ?_, ?_⟩ <;>
            nlinarith only [hc₀₁, sq_nonneg (c₀₁ 0), sq_nonneg (c₀₁ 1), sq_nonneg (c₀₁ 2)]
        have hfin3 (q : Fin 3) : q = 0 ∨ q = 1 ∨ q = 2 := by fin_cases q <;> simp
        have hmin01 (q₁ q₂ : Fin 3) : M 0 q₁ * M 1 q₂ = M 1 q₁ * M 0 q₂ := by
          dsimp [c₁₂, c₂₀, c₀₁, colCross3] at hz₁₂ hz₂₀ hz₀₁
          rcases hfin3 q₁ with rfl | rfl | rfl <;>
            rcases hfin3 q₂ with rfl | rfl | rfl <;> linarith
        have hmin02 (q₁ q₂ : Fin 3) : M 0 q₁ * M 2 q₂ = M 2 q₁ * M 0 q₂ := by
          dsimp [c₁₂, c₂₀, c₀₁, colCross3] at hz₁₂ hz₂₀ hz₀₁
          rcases hfin3 q₁ with rfl | rfl | rfl <;>
            rcases hfin3 q₂ with rfl | rfl | rfl <;> linarith
        by_cases hex : ∃ a b : Fin 3, M a b ≠ 0
        · obtain ⟨a, b, hab⟩ := hex
          have hpos_sq : 0 < M a b ^ 2 := sq_pos_of_ne_zero hab
          rcases a with ⟨_ | _ | _ | na, ha⟩
          · change 0 < M 0 b ^ 2 at hpos_sq
            let v : Fin 3 → ℝ := fun p => match p with | 0 => M 1 b | 1 => -M 0 b | 2 => 0
            refine hnorm_unit (v := v)
              (by dsimp [v]; nlinarith only [hpos_sq, sq_nonneg (M 1 b)]) fun q => ?_
            dsimp [v]; linear_combination -(hmin01 b q)
          · change 0 < M 1 b ^ 2 at hpos_sq
            let v : Fin 3 → ℝ := fun p => match p with | 0 => -M 1 b | 1 => M 0 b | 2 => 0
            refine hnorm_unit (v := v)
              (by dsimp [v]; nlinarith only [hpos_sq, sq_nonneg (M 0 b)]) fun q => ?_
            dsimp [v]; linear_combination hmin01 b q
          · change 0 < M 2 b ^ 2 at hpos_sq
            let v : Fin 3 → ℝ := fun p => match p with | 0 => -M 2 b | 1 => 0 | 2 => M 0 b
            refine hnorm_unit (v := v)
              (by dsimp [v]; nlinarith only [hpos_sq, sq_nonneg (M 0 b)]) fun q => ?_
            dsimp [v]; linear_combination hmin02 b q
          · omega
        · push Not at hex
          refine ⟨fun p => if p = 0 then 1 else 0, by simp, fun q => ?_⟩
          simp [hex]

private theorem exists_orthog3_row_zero_eq {u : Fin 3 → ℝ}
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) :
    ∃ O : Matrix (Fin 3) (Fin 3) ℝ,
      Oᵀ * O = 1 ∧ O * Oᵀ = 1 ∧ ∀ p : Fin 3, O 0 p = u p := by
  by_cases hu0 : u 0 = 1
  · have hu1 : u 1 = 0 := by nlinarith only [hu, hu0, sq_nonneg (u 1), sq_nonneg (u 2)]
    have hu2 : u 2 = 0 := by nlinarith only [hu, hu0, sq_nonneg (u 1), sq_nonneg (u 2)]
    refine ⟨1, by simp, by simp, fun p => ?_⟩
    rcases p with ⟨_ | _ | _ | np, hp⟩
    · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = u 0; simp [hu0]
    · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = u 1; simp [hu1]
    · change (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = u 2; simp [hu2]
    · omega
  · have hu0_lt : u 0 < 1 := by
      have hle : u 0 ^ 2 ≤ 1 := by nlinarith only [hu, sq_nonneg (u 1), sq_nonneg (u 2)]
      have habs : |u 0| ≤ 1 := (sq_le_one_iff_abs_le_one (u 0)).mp hle
      exact lt_of_le_of_ne (le_of_abs_le habs) hu0
    let s : ℝ := 2 * (1 - u 0)
    have hs_pos : 0 < s := by dsimp [s]; linarith only [hu0_lt]
    let v : Fin 3 → ℝ := fun p => if p = 0 then u 0 - 1 else u p
    have hv_sq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = s := by
      have hv0 : v 0 = u 0 - 1 := rfl
      have hv1 : v 1 = u 1 := rfl
      have hv2 : v 2 = u 2 := rfl
      rw [hv0, hv1, hv2]; dsimp [s]; nlinarith only [hu]
    let O : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      (if i = j then 1 else 0) - (2 / s) * v i * v j
    have hsymm : Oᵀ = O := by
      ext i j
      simp only [Matrix.transpose_apply, O, show (j = i) = (i = j) from propext eq_comm]
      ring
    have hOO : O * O = 1 := by
      ext i j
      rw [Matrix.mul_apply]
      have hterm (k : Fin 3) :
          O i k * O k j =
            (if i = k then (if k = j then (1 : ℝ) else 0) else 0) -
              (if i = k then (2 / s) * v i * v j else 0) -
              (if k = j then (2 / s) * v i * v j else 0) +
              (4 / s ^ 2) * v i * v j * v k ^ 2 := by
        dsimp only [O]
        by_cases hik : i = k <;> by_cases hkj : k = j
        · subst hik; subst hkj; simp; ring
        · subst hik; simp [hkj]; ring
        · subst hkj; simp [hik]; ring
        · simp [hik, hkj]; ring
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum, Fin.sum_univ_three,
        hv_sq, Matrix.one_apply]
      have hcancel : -(2 / s * v i * v j) - 2 / s * v i * v j +
          4 / s ^ 2 * v i * v j * s = 0 := by
        field_simp [hs_pos.ne']
      linarith only [hcancel]
    refine ⟨O, by rw [hsymm, hOO], by rw [hsymm, hOO], fun p => ?_⟩
    by_cases hp : p = 0
    · subst hp
      simp only [O, v, s, ↓reduceIte]
      field_simp [hs_pos.ne']
    · have h0p : (0 : Fin 3) ≠ p := Ne.symm hp
      simp only [O, v, s, h0p, hp, ↓reduceIte]
      field_simp [hs_pos.ne']

/-- Sharp `3 × 3` determinant-to-singular-matrix Frobenius inequality: for all
`B, M : Matrix (Fin 3) (Fin 3) ℝ` with `M.det = 0`,
`4 * B.det ^ 2 ≤ frobSq3 B ^ 2 * frobSq3 (B - M)`. -/
theorem four_det3_sq_le_frob_fourth_mul_dist_sq (B M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M.det = 0) :
    4 * B.det ^ 2 ≤ frobSq3 B ^ 2 * frobSq3 (B - M) := by
  obtain ⟨u, hu_norm, hu_ker⟩ := exists_unit_left_ker_of_det3_eq_zero hM
  obtain ⟨O, hOL, _hOR, hO_row0⟩ := exists_orthog3_row_zero_eq hu_norm
  let B' : Matrix (Fin 3) (Fin 3) ℝ := O * B
  have hO_det_sq : O.det ^ 2 = 1 := by
    have hd := congrArg Matrix.det hOL
    rwa [Matrix.det_mul, Matrix.det_transpose, ← sq, Matrix.det_one] at hd
  have hdet_eq : B'.det ^ 2 = B.det ^ 2 := by
    dsimp [B']; rw [Matrix.det_mul, mul_pow, hO_det_sq, one_mul]
  have hfrob_eq : frobSq3 B' = frobSq3 B := by
    have htr (X : Matrix (Fin 3) (Fin 3) ℝ) : frobSq3 X = Matrix.trace (Xᵀ * X) := by
      simp only [frobSq3, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, sq, Fin.sum_univ_three]
      ring
    rw [htr B', htr B]
    dsimp [B']
    rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc Oᵀ, hOL, one_mul]
  have hrow0_eq (q : Fin 3) :
      B' 0 q = u 0 * (B 0 q - M 0 q) + u 1 * (B 1 q - M 1 q) + u 2 * (B 2 q - M 2 q) := by
    dsimp [B']
    rw [Matrix.mul_apply, Fin.sum_univ_three, hO_row0 0, hO_row0 1, hO_row0 2]
    linarith only [hu_ker q]
  have hcol_cs (q : Fin 3) :
      B' 0 q ^ 2 ≤ (B 0 q - M 0 q) ^ 2 + (B 1 q - M 1 q) ^ 2 + (B 2 q - M 2 q) ^ 2 := by
    let d0 := B 0 q - M 0 q
    let d1 := B 1 q - M 1 q
    let d2 := B 2 q - M 2 q
    have hlag : (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (d0 ^ 2 + d1 ^ 2 + d2 ^ 2) -
        (u 0 * d0 + u 1 * d1 + u 2 * d2) ^ 2 =
        (u 0 * d1 - u 1 * d0) ^ 2 + (u 1 * d2 - u 2 * d1) ^ 2 + (u 2 * d0 - u 0 * d2) ^ 2 := by
      ring
    have hnn : 0 ≤ (u 0 * d1 - u 1 * d0) ^ 2 + (u 1 * d2 - u 2 * d1) ^ 2 +
        (u 2 * d0 - u 0 * d2) ^ 2 := by positivity
    rw [hrow0_eq q]
    change (u 0 * d0 + u 1 * d1 + u 2 * d2) ^ 2 ≤ d0 ^ 2 + d1 ^ 2 + d2 ^ 2
    rw [hu_norm, one_mul] at hlag
    linarith only [hlag, hnn]
  have hrow0_le : B' 0 0 ^ 2 + B' 0 1 ^ 2 + B' 0 2 ^ 2 ≤ frobSq3 (B - M) := by
    have hf : frobSq3 (B - M) =
        ((B 0 0 - M 0 0) ^ 2 + (B 1 0 - M 1 0) ^ 2 + (B 2 0 - M 2 0) ^ 2) +
        ((B 0 1 - M 0 1) ^ 2 + (B 1 1 - M 1 1) ^ 2 + (B 2 1 - M 2 1) ^ 2) +
        ((B 0 2 - M 0 2) ^ 2 + (B 1 2 - M 1 2) ^ 2 + (B 2 2 - M 2 2) ^ 2) := by
      simp only [frobSq3, Fin.sum_univ_three, Matrix.sub_apply]
      ring
    linarith only [hf, hcol_cs 0, hcol_cs 1, hcol_cs 2]
  let r0 := B' 0 0 ^ 2 + B' 0 1 ^ 2 + B' 0 2 ^ 2
  let r1 := B' 1 0 ^ 2 + B' 1 1 ^ 2 + B' 1 2 ^ 2
  let r2 := B' 2 0 ^ 2 + B' 2 1 ^ 2 + B' 2 2 ^ 2
  let C0 := B' 1 1 * B' 2 2 - B' 1 2 * B' 2 1
  let C1 := B' 1 2 * B' 2 0 - B' 1 0 * B' 2 2
  let C2 := B' 1 0 * B' 2 1 - B' 1 1 * B' 2 0
  have hdet_B' : B'.det = B' 0 0 * C0 + B' 0 1 * C1 + B' 0 2 * C2 := by
    rw [Matrix.det_fin_three]; dsimp [C0, C1, C2]; ring
  have hcs_det : B'.det ^ 2 ≤ r0 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2) := by
    have hid : r0 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2) - (B' 0 0 * C0 + B' 0 1 * C1 + B' 0 2 * C2) ^ 2 =
        (B' 0 0 * C1 - B' 0 1 * C0) ^ 2 + (B' 0 1 * C2 - B' 0 2 * C1) ^ 2 +
          (B' 0 2 * C0 - B' 0 0 * C2) ^ 2 := by
      dsimp [r0]; ring
    rw [hdet_B']
    linarith only [hid, sq_nonneg (B' 0 0 * C1 - B' 0 1 * C0),
      sq_nonneg (B' 0 1 * C2 - B' 0 2 * C1), sq_nonneg (B' 0 2 * C0 - B' 0 0 * C2)]
  have hlag_cof : 4 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2) ≤ (r1 + r2) ^ 2 := by
    have hid1 : r1 * r2 - (C0 ^ 2 + C1 ^ 2 + C2 ^ 2) =
        (B' 1 0 * B' 2 0 + B' 1 1 * B' 2 1 + B' 1 2 * B' 2 2) ^ 2 := by
      dsimp [r1, r2, C0, C1, C2]; ring
    have hid2 : (r1 + r2) ^ 2 - 4 * (r1 * r2) = (r1 - r2) ^ 2 := by ring
    linarith only [hid1, hid2,
      sq_nonneg (B' 1 0 * B' 2 0 + B' 1 1 * B' 2 1 + B' 1 2 * B' 2 2), sq_nonneg (r1 - r2)]
  have hr12_le : r1 + r2 ≤ frobSq3 B' := by
    have hf : frobSq3 B' = r0 + r1 + r2 := by
      simp only [frobSq3, Fin.sum_univ_three, r0, r1, r2]
    have hr0_nn : 0 ≤ r0 := by dsimp [r0]; positivity
    linarith only [hf, hr0_nn]
  have hr12_sq : (r1 + r2) ^ 2 ≤ frobSq3 B' ^ 2 :=
    pow_le_pow_left₀ (by dsimp [r1, r2]; positivity) hr12_le 2
  rw [← hdet_eq, ← hfrob_eq]
  calc 4 * B'.det ^ 2
      ≤ 4 * (r0 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2)) := by linarith only [hcs_det]
    _ = r0 * (4 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2)) := by ring
    _ ≤ r0 * frobSq3 B' ^ 2 :=
          mul_le_mul_of_nonneg_left (hlag_cof.trans hr12_sq) (by dsimp [r0]; positivity)
    _ ≤ frobSq3 (B - M) * frobSq3 B' ^ 2 :=
          mul_le_mul_of_nonneg_right hrow0_le (sq_nonneg _)
    _ = frobSq3 B' ^ 2 * frobSq3 (B - M) := mul_comm _ _

/-! ## Section 2: `U(2)^⊗N`-invariant full bond determinant + longitudinal-field event `Ω_rk3` -/

/-- Onsite `3`-vector `h_v(u)` of a chain shell `u : PathShell n` at site `v`. -/
def onsiteVec {n : ℕ} (u : PathShell n) (v : Fin (n + 2)) : Fin 3 → ℝ :=
  fun a => u (.inl (v, a))

/-- Onsite `3`-vector read from `x : PrefixIndex n → ℝ` at site `v`. -/
def onsiteVecOfPrefix (n : ℕ) (x : PrefixIndex n → ℝ) (v : Fin (n + 2)) : Fin 3 → ℝ :=
  fun a => x ((pathCoeffEquiv n).symm (.inl (v, a)))

/-- Squared Euclidean norm `∑_{a : Fin 3} (h a)²` of an onsite field `3`-vector. -/
def onsiteNormSq (h : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, (h a) ^ 2

/-- `U(2)^⊗N`-gauge-invariant full bond determinant + longitudinal/onsite-field bulk event
`Ω_rk3(n, η)`: every bond `e` satisfies `η³ ≤ |det B_e(x)|` and every site `v` satisfies
`η² ≤ ‖h_v(x)‖₂²`. -/
def bondRankThreeFieldEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | (∀ e : Fin (n + 1), η ^ 3 ≤ |(bondMatrixOfPrefix n x e).det|) ∧
       (∀ v : Fin (n + 2), η ^ 2 ≤ onsiteNormSq (onsiteVecOfPrefix n x v))}

private def signedCofactor3 (b : Fin 3 × Fin 3 → ℝ) : Fin 3 × Fin 3 → ℝ
  | (0, 0) => b (1, 1) * b (2, 2) - b (1, 2) * b (2, 1)
  | (0, 1) => -(b (1, 0) * b (2, 2) - b (1, 2) * b (2, 0))
  | (0, 2) => b (1, 0) * b (2, 1) - b (1, 1) * b (2, 0)
  | (1, 0) => -(b (0, 1) * b (2, 2) - b (0, 2) * b (2, 1))
  | (1, 1) => b (0, 0) * b (2, 2) - b (0, 2) * b (2, 0)
  | (1, 2) => -(b (0, 0) * b (2, 1) - b (0, 1) * b (2, 0))
  | (2, 0) => b (0, 1) * b (1, 2) - b (0, 2) * b (1, 1)
  | (2, 1) => -(b (0, 0) * b (1, 2) - b (0, 2) * b (1, 0))
  | (2, 2) => b (0, 0) * b (1, 1) - b (0, 1) * b (1, 0)

private def restDet3 (b : Fin 3 × Fin 3 → ℝ) (pq₀ : Fin 3 × Fin 3) : ℝ :=
  (Matrix.of fun p q => if (p, q) = pq₀ then 0 else b (p, q)).det

private theorem det3_eq_entry_mul_signedCofactor_add_rest (b : Fin 3 × Fin 3 → ℝ)
    (pq₀ : Fin 3 × Fin 3) :
    (Matrix.of fun p q => b (p, q)).det =
      b pq₀ * signedCofactor3 b pq₀ + restDet3 b pq₀ := by
  rcases pq₀ with ⟨p₀, q₀⟩
  fin_cases p₀ <;> fin_cases q₀ <;>
    simp [signedCofactor3, restDet3, Matrix.det_fin_three, Prod.ext_iff] <;>
    ring

private theorem sum_signedCofactor3_sq_eq_bondMinorInvariant (b : Fin 3 × Fin 3 → ℝ) :
    (∑ pq₀ : Fin 3 × Fin 3, (signedCofactor3 b pq₀) ^ 2) =
      bondMinorInvariant (fun p q => b (p, q)) := by
  rw [bondMinorInvariant_eq_half_frob_diff, Fintype.sum_prod_type]
  simp only [frobSq3, Fin.sum_univ_three, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.isValue, signedCofactor3]
  ring

private theorem signedCofactor3_congr_compl {b₁ b₂ : Fin 3 × Fin 3 → ℝ} {pq₀ : Fin 3 × Fin 3}
    (h : ∀ pq : Fin 3 × Fin 3, pq ≠ pq₀ → b₁ pq = b₂ pq) :
    signedCofactor3 b₁ pq₀ = signedCofactor3 b₂ pq₀ := by
  rcases pq₀ with ⟨p₀, q₀⟩
  fin_cases p₀ <;> fin_cases q₀ <;>
    simp only [signedCofactor3] <;>
    repeat rw [h _ (by decide)]

private theorem restDet3_congr_compl {b₁ b₂ : Fin 3 × Fin 3 → ℝ} {pq₀ : Fin 3 × Fin 3}
    (h : ∀ pq : Fin 3 × Fin 3, pq ≠ pq₀ → b₁ pq = b₂ pq) :
    restDet3 b₁ pq₀ = restDet3 b₂ pq₀ := by
  unfold restDet3
  congr 1; ext p q
  by_cases hpq : (p, q) = pq₀
  · simp [hpq]
  · simp [hpq, h (p, q) hpq]

private theorem gaussianReal_Icc_shifted_le' (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 1).real (Icc (c - δ) (c + δ)) ≤ δ := by
  have h1 : (gaussianReal 0 1) (Icc (c - δ) (c + δ)) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume (Icc (c - δ) (c + δ)) := by
    rw [gaussianReal_apply 0 (by norm_num) _, ← setLIntegral_const]
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards with t _
    rw [gaussianPDF]
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))
  have hlen : c + δ - (c - δ) = 2 * δ := by ring
  rw [Real.volume_Icc, hlen, ← ENNReal.ofReal_mul (by positivity)] at h1
  have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    Real.le_sqrt_of_sq_le (by linarith only [Real.pi_gt_three])
  have hinv_le : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 :=
    one_div (Real.sqrt (2 * Real.pi)) ▸ one_div_le_one_div_of_le two_pos hsqrt_ge2
  have hprod_le : (Real.sqrt (2 * Real.pi))⁻¹ * (2 * δ) ≤ δ := by
    nlinarith only [hinv_le, hδ]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal hδ (h1.trans (ENNReal.ofReal_le_ofReal hprod_le))

private theorem nine_gaussian_bondDet_lt_prob_le {η r₁ r₂ : ℝ}
    (hη : 0 ≤ η) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    (Measure.pi fun _ : Fin 3 × Fin 3 => gaussianReal 0 1).real
      {b : Fin 3 × Fin 3 → ℝ | |(Matrix.of fun p q => b (p, q)).det| < η ^ 3} ≤
      r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2) := by
  let γ := gaussianReal 0 1
  let μ₉ := Measure.pi fun _ : Fin 3 × Fin 3 => γ
  haveI : IsProbabilityMeasure μ₉ := by dsimp only [μ₉]; infer_instance
  let MinorSmall : Set (Fin 3 × Fin 3 → ℝ) :=
    {b | bondMinorInvariant (fun p q => b (p, q)) < r₂ ^ 4}
  have hMinor_prob : μ₉.real MinorSmall ≤ r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 := by
    -- Pull back from `bondRankTwoEvent_compl_prob_le` on `n = 0` (`1` bond)!
    let emb : Fin 3 × Fin 3 → PrefixIndex 0 := fun pq => (pathCoeffEquiv 0).symm (.inr (0, pq))
    have hemb_inj : Function.Injective emb :=
      fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv 0).symm.injective h))).2
    let μ₀ := Measure.pi fun _ : PrefixIndex 0 => γ
    haveI : IsProbabilityMeasure μ₀ := by dsimp only [μ₀]; infer_instance
    have hi := ProbabilityTheory.iIndepFun_pi (μ := fun _ : PrefixIndex 0 => γ)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
    have hmp : MeasurePreserving (fun (x : PrefixIndex 0 → ℝ) pq => x (emb pq)) μ₀ μ₉ := by
      refine ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _), ?_⟩
      have h := (hi.precomp hemb_inj).map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
      have hmap (pq : Fin 3 × Fin 3) :
          Measure.map (fun x : PrefixIndex 0 → ℝ => x (emb pq)) μ₀ = γ :=
        (measurePreserving_eval (fun _ : PrefixIndex 0 => γ) (emb pq)).map_eq
      exact h.trans (congrArg Measure.pi (funext hmap))
    have hmeas_ms : MeasurableSet MinorSmall := by
      have hcont : Continuous fun b : Fin 3 × Fin 3 → ℝ =>
          bondMinorInvariant (fun p q => b (p, q)) := by
        unfold bondMinorInvariant
        refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
        by_cases h : p.1 < p.2 ∧ q.1 < q.2
        · simp only [if_pos h]
          exact (((continuous_apply (p.1, q.1)).mul (continuous_apply (p.2, q.2))).sub
            ((continuous_apply (p.1, q.2)).mul (continuous_apply (p.2, q.1)))).pow 2
        · simp only [if_neg h]; exact continuous_const
      exact measurableSet_lt hcont.measurable measurable_const
    have hpre_eq : (fun (x : PrefixIndex 0 → ℝ) pq => x (emb pq)) ⁻¹' MinorSmall =
        (bondRankTwoEvent 0 r₂)ᶜ := by
      ext x
      simp only [mem_preimage, MinorSmall, mem_setOf_eq, mem_compl_iff, bondRankTwoEvent,
        not_forall, not_le]
      exact ⟨fun h => ⟨0, h⟩, fun ⟨e, he⟩ => by
        have he0 : e = 0 := Fin.ext (by omega)
        exact he0 ▸ he⟩
    have h1 := congrArg ENNReal.toReal (hmp.measure_preimage hmeas_ms.nullMeasurableSet)
    change μ₀.real ((fun x pq => x (emb pq)) ⁻¹' MinorSmall) = μ₉.real MinorSmall at h1
    rw [hpre_eq] at h1
    have hb := (bondRankTwoEvent_compl_prob_le 0 hr₂.le).1 r₁ hr₁
    simp only [Nat.zero_add, Nat.cast_one, one_mul] at hb
    exact h1.symm.trans_le hb
  let CofSet (pq₀ : Fin 3 × Fin 3) : Set (Fin 3 × Fin 3 → ℝ) :=
    {b | r₂ ^ 2 / 3 ≤ |signedCofactor3 b pq₀| ∧
         |(Matrix.of fun p q => b (p, q)).det| ≤ η ^ 3}
  have hcov : {b : Fin 3 × Fin 3 → ℝ | |(Matrix.of fun p q => b (p, q)).det| < η ^ 3} ⊆
      MinorSmall ∪ ⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), CofSet pq₀ := by
    intro b hlt
    by_cases hms : b ∈ MinorSmall
    · exact Or.inl hms
    · right
      have hge : r₂ ^ 4 ≤ ∑ pq₀ : Fin 3 × Fin 3, (signedCofactor3 b pq₀) ^ 2 := by
        rw [sum_signedCofactor3_sq_eq_bondMinorInvariant]
        exact le_of_not_gt hms
      have hex : ∃ pq₀ : Fin 3 × Fin 3, r₂ ^ 2 / 3 ≤ |signedCofactor3 b pq₀| := by
        by_contra hall_lt
        push Not at hall_lt
        have hsq_lt (pq₀ : Fin 3 × Fin 3) : (signedCofactor3 b pq₀) ^ 2 < r₂ ^ 4 / 9 := by
          have h1 := hall_lt pq₀
          have hnn : 0 ≤ |signedCofactor3 b pq₀| := abs_nonneg _
          have h2 : |signedCofactor3 b pq₀| ^ 2 < (r₂ ^ 2 / 3) ^ 2 :=
            pow_lt_pow_left₀ h1 hnn (by decide)
          rw [sq_abs] at h2
          linarith only [h2, show (r₂ ^ 2 / 3) ^ 2 = r₂ ^ 4 / 9 by ring]
        have hsum_lt : (∑ pq₀ : Fin 3 × Fin 3, (signedCofactor3 b pq₀) ^ 2) <
            ∑ _pq₀ : Fin 3 × Fin 3, (r₂ ^ 4 / 9) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun pq₀ _ => hsq_lt pq₀
        have hc9 : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by decide
        rw [Finset.sum_const, hc9, nsmul_eq_mul] at hsum_lt
        linarith only [hge, hsum_lt]
      obtain ⟨pq₀, hpq₀⟩ := hex
      exact mem_iUnion₂.mpr ⟨pq₀, Finset.mem_univ pq₀, hpq₀, hlt.le⟩
  have hcof_prob (pq₀ : Fin 3 × Fin 3) : μ₉.real (CofSet pq₀) ≤ 3 * (η ^ 3 / r₂ ^ 2) := by
    let Comp : Fin 3 × Fin 3 → Prop := fun pq => pq = pq₀
    have hCof_meas : MeasurableSet (CofSet pq₀) := by
      have hcont_cof : Continuous fun b : Fin 3 × Fin 3 → ℝ => signedCofactor3 b pq₀ := by
        rcases pq₀ with ⟨p₀, q₀⟩
        fin_cases p₀ <;> fin_cases q₀ <;> dsimp [signedCofactor3] <;> fun_prop
      have hcont_det : Continuous fun b : Fin 3 × Fin 3 → ℝ =>
          (Matrix.of fun p q => b (p, q)).det := by
        simp only [Matrix.det_fin_three, Matrix.of_apply]
        fun_prop
      exact (measurableSet_le measurable_const (continuous_abs.comp hcont_cof).measurable).inter
        (measurableSet_le (continuous_abs.comp hcont_det).measurable measurable_const)
    let e_sp := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin 3 × Fin 3 => ℝ) Comp
    have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin 3 × Fin 3 => γ) Comp
    let μ_c := @Measure.pi (Subtype Comp) (fun _ => ℝ) (Subtype.fintype Comp) _ (fun _ => γ)
    let μ_r := @Measure.pi {pq : Fin 3 × Fin 3 // ¬ Comp pq} (fun _ => ℝ)
      (Subtype.fintype fun pq => ¬ Comp pq) _ (fun _ => γ)
    have hmeas_eq : μ₉ (CofSet pq₀) = (μ_c.prod μ_r) (e_sp.symm ⁻¹' CofSet pq₀) := by
      rw [← hmp.measure_preimage (e_sp.symm.measurable hCof_meas).nullMeasurableSet]
      congr 1; ext b; change b ∈ CofSet pq₀ ↔ e_sp.symm (e_sp b) ∈ CofSet pq₀
      rw [e_sp.symm_apply_apply]
    have hprod_eval : (μ_c.prod μ_r) (e_sp.symm ⁻¹' CofSet pq₀) =
        ∫⁻ z, μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ CofSet pq₀} ∂μ_r :=
      Measure.prod_apply_symm (e_sp.symm.measurable hCof_meas)
    let δ' := 3 * (η ^ 3 / r₂ ^ 2)
    have hδ'_nn : 0 ≤ δ' := by dsimp [δ']; positivity
    let u₀ : Subtype Comp := ⟨pq₀, rfl⟩
    have huniq_u : ∀ u : Subtype Comp, u = u₀ := fun ⟨pq, hpq⟩ => Subtype.ext hpq
    have hsec_le (z : {pq : Fin 3 × Fin 3 // ¬ Comp pq} → ℝ) :
        μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ CofSet pq₀} ≤ ENNReal.ofReal δ' := by
      let b_z : Fin 3 × Fin 3 → ℝ := e_sp.symm (fun _ => 0, z)
      let C_z := signedCofactor3 b_z pq₀
      let R_z := restDet3 b_z pq₀
      have hagree (w : Subtype Comp → ℝ) (pq : Fin 3 × Fin 3) (hpq : pq ≠ pq₀) :
          e_sp.symm (w, z) pq = b_z pq := by
        simp [b_z, e_sp, Comp, hpq, MeasurableEquiv.piEquivPiSubtypeProd]
      by_cases hCz : r₂ ^ 2 / 3 ≤ |C_z|
      · have hCz_pos : 0 < |C_z| := (by positivity : 0 < r₂ ^ 2 / 3).trans_le hCz
        have hCz_ne : C_z ≠ 0 := abs_pos.mp hCz_pos
        let center : ℝ := -R_z / C_z
        have hsub_box : {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ CofSet pq₀} ⊆
            Set.univ.pi fun _ : Subtype Comp => Icc (center - δ') (center + δ') := by
          intro w ⟨_, hdet_le⟩ u _
          rw [huniq_u u]
          have hc_eq : signedCofactor3 (e_sp.symm (w, z)) pq₀ = C_z :=
            signedCofactor3_congr_compl (hagree w)
          have hr_eq : restDet3 (e_sp.symm (w, z)) pq₀ = R_z :=
            restDet3_congr_compl (hagree w)
          have hw_eq : e_sp.symm (w, z) pq₀ = w u₀ := by
            simp [e_sp, u₀, Comp, MeasurableEquiv.piEquivPiSubtypeProd]
          rw [det3_eq_entry_mul_signedCofactor_add_rest _ pq₀, hc_eq, hr_eq, hw_eq] at hdet_le
          have hdiff : |w u₀ - center| ≤ δ' := by
            have hid : w u₀ - center = (w u₀ * C_z + R_z) / C_z := by
              dsimp [center]; field_simp [hCz_ne]
            rw [hid, abs_div]
            have h1 : |w u₀ * C_z + R_z| / |C_z| ≤ η ^ 3 / (r₂ ^ 2 / 3) :=
              (div_le_div_of_nonneg_right hdet_le hCz_pos.le).trans
                (div_le_div_of_nonneg_left (pow_nonneg hη 3) (by positivity) hCz)
            exact h1.trans_eq (by dsimp [δ']; ring)
          have hbd := abs_le.mp hdiff
          exact ⟨by linarith only [hbd.1], by linarith only [hbd.2]⟩
        calc μ_c {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ CofSet pq₀}
            ≤ μ_c (Set.univ.pi fun _ : Subtype Comp => Icc (center - δ') (center + δ')) :=
              measure_mono hsub_box
          _ = γ (Icc (center - δ') (center + δ')) := by
              dsimp only [μ_c]
              rw [@Measure.pi_pi (Subtype Comp) (fun _ => ℝ) (Subtype.fintype Comp) _ (fun _ => γ)]
              refine Finset.prod_eq_single u₀ ?_ ?_
              · rintro ⟨pq, hpq⟩ _ hne; exact (hne (Subtype.ext hpq)).elim
              · intro h; exact (h (@Finset.mem_univ (Subtype Comp) (Subtype.fintype Comp) u₀)).elim
          _ ≤ ENNReal.ofReal δ' := by
              rw [← ENNReal.ofReal_toReal (measure_ne_top γ _)]
              exact ENNReal.ofReal_le_ofReal (gaussianReal_Icc_shifted_le' center hδ'_nn)
      · have hemp : {w : Subtype Comp → ℝ | e_sp.symm (w, z) ∈ CofSet pq₀} = ∅ := by
          ext w; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
          rintro ⟨h1, _⟩
          rw [signedCofactor3_congr_compl (hagree w)] at h1
          exact hCz h1
        rw [hemp, measure_empty]; simp
    have htot : μ₉ (CofSet pq₀) ≤ ENNReal.ofReal δ' := by
      rw [hmeas_eq, hprod_eval]
      refine (lintegral_mono hsec_le).trans ?_
      haveI : IsProbabilityMeasure μ_r := by dsimp only [μ_r]; infer_instance
      rw [lintegral_const, measure_univ, mul_one]
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal hδ'_nn htot
  calc μ₉.real {b : Fin 3 × Fin 3 → ℝ | |(Matrix.of fun p q => b (p, q)).det| < η ^ 3}
      ≤ μ₉.real (MinorSmall ∪ ⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), CofSet pq₀) :=
          measureReal_mono hcov (measure_ne_top _ _)
    _ ≤ μ₉.real MinorSmall +
          μ₉.real (⋃ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), CofSet pq₀) :=
          measureReal_union_le _ _
    _ ≤ (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4) +
          ∑ pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), μ₉.real (CofSet pq₀) :=
          add_le_add hMinor_prob (measureReal_biUnion_finset_le _ _)
    _ ≤ (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4) +
          ∑ _pq₀ ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), (3 * (η ^ 3 / r₂ ^ 2)) :=
          add_le_add le_rfl (Finset.sum_le_sum fun pq₀ _ => hcof_prob pq₀)
    _ = r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2) := by
          have hc9 : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by decide
          rw [Finset.sum_const, hc9, nsmul_eq_mul]; ring

/-- Product-Gaussian failure bound for `bondRankThreeFieldEvent n η` (`Ω_rk3(n, η)`):
1. For every `η ≥ 0` and pivot scales `r₁, r₂ > 0`,
   `ℙ(Ω_rk3(n, η)ᶜ) ≤ (n + 1) * (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2)) + (n + 2) * η ^ 3`.
2. For every `η ∈ [0, 1]`, setting `r₁ = √(√η)` and `r₂ = √η` gives
   `ℙ(Ω_rk3(n, η)ᶜ) ≤ (38 * n + 39) * η ^ 2`. -/
theorem bondRankThreeFieldEvent_compl_prob_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (∀ r₁ > 0, ∀ r₂ > 0,
      (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
        (bondRankThreeFieldEvent n η)ᶜ ≤
        ((n + 1 : ℕ) : ℝ) * (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2)) +
          ((n + 2 : ℕ) : ℝ) * η ^ 3) ∧
    (η ≤ 1 →
      (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
        (bondRankThreeFieldEvent n η)ᶜ ≤
        ((38 * n + 39 : ℕ) : ℝ) * η ^ 2) := by
  let γ := gaussianReal 0 1
  let μ := Measure.pi fun _ : PrefixIndex n => γ
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hmeas_det : MeasurableSet {b : Fin 3 × Fin 3 → ℝ |
      |(Matrix.of fun p q => b (p, q)).det| < η ^ 3} := by
    have hcont : Continuous fun b : Fin 3 × Fin 3 → ℝ =>
        |(Matrix.of fun p q => b (p, q)).det| := by
      simp only [Matrix.det_fin_three, Matrix.of_apply]
      fun_prop
    exact measurableSet_lt hcont.measurable measurable_const
  have hmp_bond (e : Fin (n + 1)) :
      MeasurePreserving
        (fun (x : PrefixIndex n → ℝ) (pq : Fin 3 × Fin 3) =>
          x ((pathCoeffEquiv n).symm (.inr (e, pq))))
        μ (Measure.pi fun _ : Fin 3 × Fin 3 => γ) := by
    let emb : Fin 3 × Fin 3 → PrefixIndex n := fun pq => (pathCoeffEquiv n).symm (.inr (e, pq))
    have hemb_inj : Function.Injective emb :=
      fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective h))).2
    have hi := ProbabilityTheory.iIndepFun_pi (μ := fun _ : PrefixIndex n => γ)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
    refine ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _), ?_⟩
    have h := (hi.precomp hemb_inj).map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
    have hmap (pq : Fin 3 × Fin 3) :
        Measure.map (fun x : PrefixIndex n → ℝ => x (emb pq)) μ = γ :=
      (measurePreserving_eval (fun _ : PrefixIndex n => γ) (emb pq)).map_eq
    exact h.trans (congrArg Measure.pi (funext hmap))
  have hsite_union :
      μ.real (⋃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
        {x : PrefixIndex n → ℝ | onsiteNormSq (onsiteVecOfPrefix n x v) < η ^ 2}) ≤
        ((n + 2 : ℕ) : ℝ) * η ^ 3 := by
    let S_site (v : Fin (n + 2)) : Finset (PrefixIndex n) :=
      Finset.univ.map ⟨fun a : Fin 3 => (pathCoeffEquiv n).symm (.inl (v, a)),
        fun _ _ h => (Prod.mk.inj (Sum.inl.inj ((pathCoeffEquiv n).symm.injective h))).2⟩
    have hcard_site : ∀ v ∈ (Finset.univ : Finset (Fin (n + 2))), (S_site v).card = 3 := by
      intro v _; simp [S_site]
    have hsub_site : (⋃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
        {x : PrefixIndex n → ℝ | onsiteNormSq (onsiteVecOfPrefix n x v) < η ^ 2}) ⊆
        {x : PrefixIndex n → ℝ | ∃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
          ∀ i ∈ S_site v, |x i| < η} := by
      intro x hx
      obtain ⟨v, hv, hlt⟩ := mem_iUnion₂.mp hx
      refine ⟨v, hv, fun i hi => ?_⟩
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      have ha_le : (onsiteVecOfPrefix n x v a) ^ 2 ≤ onsiteNormSq (onsiteVecOfPrefix n x v) :=
        Finset.single_le_sum (f := fun b : Fin 3 => (onsiteVecOfPrefix n x v b) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      have hsq_lt : |onsiteVecOfPrefix n x v a| ^ 2 < η ^ 2 := by
        rw [sq_abs]; exact ha_le.trans_lt hlt
      exact (sq_lt_sq₀ (abs_nonneg _) hη).mp hsq_lt
    have hb := (pi_smallCube_union_prob_le (Finset.univ : Finset (Fin (n + 2)))
      S_site 3 hcard_site hη).2
    simp only [Finset.card_univ, Fintype.card_fin] at hb
    exact (measureReal_mono hsub_site (measure_ne_top _ _)).trans hb
  have hgen : ∀ r₁ > 0, ∀ r₂ > 0,
      μ.real (bondRankThreeFieldEvent n η)ᶜ ≤
        ((n + 1 : ℕ) : ℝ) * (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2)) +
          ((n + 2 : ℕ) : ℝ) * η ^ 3 := by
    intro r₁ hr₁ r₂ hr₂
    have hsub : (bondRankThreeFieldEvent n η)ᶜ ⊆
        (⋃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
          {x : PrefixIndex n → ℝ | |(bondMatrixOfPrefix n x e).det| < η ^ 3}) ∪
        (⋃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
          {x : PrefixIndex n → ℝ | onsiteNormSq (onsiteVecOfPrefix n x v) < η ^ 2}) := by
      intro x hx
      rw [mem_compl_iff, bondRankThreeFieldEvent, mem_setOf_eq, not_and_or] at hx
      rcases hx with h1 | h2
      · left; push Not at h1; obtain ⟨e, he⟩ := h1
        exact mem_iUnion₂.mpr ⟨e, Finset.mem_univ e, he⟩
      · right; push Not at h2; obtain ⟨v, hv⟩ := h2
        exact mem_iUnion₂.mpr ⟨v, Finset.mem_univ v, hv⟩
    have hbond_le (e : Fin (n + 1)) :
        μ.real {x : PrefixIndex n → ℝ | |(bondMatrixOfPrefix n x e).det| < η ^ 3} ≤
          r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2) := by
      have hpre := congrArg ENNReal.toReal
        ((hmp_bond e).measure_preimage hmeas_det.nullMeasurableSet)
      exact hpre.trans_le (nine_gaussian_bondDet_lt_prob_le hη hr₁ hr₂)
    calc μ.real (bondRankThreeFieldEvent n η)ᶜ
        ≤ μ.real ((⋃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
            {x : PrefixIndex n → ℝ | |(bondMatrixOfPrefix n x e).det| < η ^ 3}) ∪
          (⋃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
            {x : PrefixIndex n → ℝ | onsiteNormSq (onsiteVecOfPrefix n x v) < η ^ 2})) :=
            measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real (⋃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
            {x : PrefixIndex n → ℝ | |(bondMatrixOfPrefix n x e).det| < η ^ 3}) +
          μ.real (⋃ v ∈ (Finset.univ : Finset (Fin (n + 2))),
            {x : PrefixIndex n → ℝ | onsiteNormSq (onsiteVecOfPrefix n x v) < η ^ 2}) :=
            measureReal_union_le _ _
      _ ≤ (∑ e ∈ (Finset.univ : Finset (Fin (n + 1))),
            μ.real {x : PrefixIndex n → ℝ | |(bondMatrixOfPrefix n x e).det| < η ^ 3}) +
          ((n + 2 : ℕ) : ℝ) * η ^ 3 :=
            add_le_add (measureReal_biUnion_finset_le _ _) hsite_union
      _ ≤ (∑ _e ∈ (Finset.univ : Finset (Fin (n + 1))),
            (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2))) +
          ((n + 2 : ℕ) : ℝ) * η ^ 3 :=
            add_le_add (Finset.sum_le_sum fun e _ => hbond_le e) le_rfl
      _ = ((n + 1 : ℕ) : ℝ) * (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2)) +
          ((n + 2 : ℕ) : ℝ) * η ^ 3 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨hgen, fun hη1 => ?_⟩
  rcases eq_or_lt_of_le hη with rfl | hη_pos
  · have hemp : (bondRankThreeFieldEvent n 0)ᶜ = ∅ := by
      ext x
      simp only [mem_compl_iff, bondRankThreeFieldEvent, mem_setOf_eq, mem_empty_iff_false,
        iff_false, not_and_or, not_forall, not_le]
      rintro (⟨e, hlt⟩ | ⟨v, hlt⟩)
      · have hnn := abs_nonneg (bondMatrixOfPrefix n x e).det
        norm_num at hlt; linarith only [hlt, hnn]
      · have hnn : 0 ≤ onsiteNormSq (onsiteVecOfPrefix n x v) :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        norm_num at hlt; linarith only [hlt, hnn]
    rw [hemp, measureReal_empty]; norm_num
  · let r₂ := Real.sqrt η
    let r₁ := Real.sqrt r₂
    have hr₂_pos : 0 < r₂ := Real.sqrt_pos.mpr hη_pos
    have hr₁_pos : 0 < r₁ := Real.sqrt_pos.mpr hr₂_pos
    have hr₂_le1 : r₂ ≤ 1 := Real.sqrt_le_one.mpr hη1
    have hr₁_le1 : r₁ ≤ 1 := Real.sqrt_le_one.mpr hr₂_le1
    have hr₂_sq : r₂ ^ 2 = η := Real.sq_sqrt hη_pos.le
    have hr₁_sq : r₁ ^ 2 = r₂ := Real.sq_sqrt hr₂_pos.le
    have hr₁_pow4 : r₁ ^ 4 = η := by
      calc r₁ ^ 4 = (r₁ ^ 2) ^ 2 := by ring
        _ = η := by rw [hr₁_sq, hr₂_sq]
    have hr₁_9_le : r₁ ^ 9 ≤ η ^ 2 := by
      calc r₁ ^ 9 = (r₁ ^ 4) ^ 2 * r₁ := by ring
        _ = η ^ 2 * r₁ := by rw [hr₁_pow4]
        _ ≤ η ^ 2 * 1 := mul_le_mul_of_nonneg_left hr₁_le1 (sq_nonneg η)
        _ = η ^ 2 := mul_one _
    have hmid_le : (r₂ ^ 2 / r₁) ^ 4 ≤ η ^ 2 := by
      have heq : (r₂ ^ 2 / r₁) ^ 4 = η ^ 3 := by
        rw [hr₂_sq, div_pow, hr₁_pow4]
        field_simp [hη_pos.ne']
      rw [heq]
      nlinarith only [hη_pos, hη1, sq_nonneg η]
    have hlast_eq : η ^ 3 / r₂ ^ 2 = η ^ 2 := by
      rw [hr₂_sq]; field_simp [hη_pos.ne']
    have hη3_le : η ^ 3 ≤ η ^ 2 := by nlinarith only [hη_pos, hη1, sq_nonneg η]
    calc μ.real (bondRankThreeFieldEvent n η)ᶜ
        ≤ ((n + 1 : ℕ) : ℝ) * (r₁ ^ 9 + 9 * (r₂ ^ 2 / r₁) ^ 4 + 27 * (η ^ 3 / r₂ ^ 2)) +
            ((n + 2 : ℕ) : ℝ) * η ^ 3 := hgen r₁ hr₁_pos r₂ hr₂_pos
      _ ≤ ((n + 1 : ℕ) : ℝ) * (η ^ 2 + 9 * η ^ 2 + 27 * η ^ 2) +
            ((n + 2 : ℕ) : ℝ) * η ^ 2 := by
            rw [hlast_eq]
            exact add_le_add
              (mul_le_mul_of_nonneg_left (by linarith only [hr₁_9_le, hmid_le]) (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left hη3_le (Nat.cast_nonneg _))
      _ = ((38 * n + 39 : ℕ) : ℝ) * η ^ 2 := by push_cast; ring

/-! ## Section 3: Simultaneous `U(2)^⊗N`-gauge-invariant separation from rotated Ising and matchgates -/

/-- Predicate identifying the `5N - 4 = 5n + 6` nearest-neighbor `so(2N)` matchgate labels in
`PathLabel n`: onsite `Z_s` (`a = 2`) and bond `XY`-block couplings (`p ≠ 2 ∧ q ≠ 2`). -/
def isMatchgateChainLabel {n : ℕ} : PathLabel n → Prop
  | .inl (_, a) => a = 2
  | .inr (_, (p, q)) => p ≠ 2 ∧ q ≠ 2

instance {n : ℕ} (l : PathLabel n) : Decidable (isMatchgateChainLabel l) := by
  cases l with
  | inl va => dsimp [isMatchgateChainLabel]; infer_instance
  | inr epq => rcases epq with ⟨e, p, q⟩; dsimp [isMatchgateChainLabel]; infer_instance

private theorem conj_anyPauli_eq_real_pauli_comb (R₀ : Matrix Bool Bool ℂ)
    (hR₀ : star R₀ * R₀ = 1 ∧ R₀ * star R₀ = 1) (b : Fin 3) :
    let M := R₀ * finiteQubitPauli b * star R₀
    let O_col : Fin 3 → ℝ := fun a => (Matrix.trace (finiteQubitPauli a * M)).re / 2
    Matrix.trace M = 0 ∧
    M = ∑ a : Fin 3, ((O_col a : ℝ) : ℂ) • finiteQubitPauli a := by
  intro M O_col
  have hP_sa (a : Fin 3) : star (finiteQubitPauli a) = finiteQubitPauli a := by
    rw [Matrix.star_eq_conjTranspose, (finiteQubitPauli_isHermitian a).eq]
  have htr_star (X : Matrix Bool Bool ℂ) : star (Matrix.trace X) = Matrix.trace (star X) := by
    simp [Matrix.trace]
  have htr0 : Matrix.trace M = 0 := by
    dsimp only [M]
    rw [Matrix.trace_mul_comm, ← mul_assoc, hR₀.1, one_mul]
    fin_cases b <;> simp [Matrix.trace, finiteQubitPauli]
  have hM_sa : star M = M := by
    dsimp only [M]
    rw [star_mul, star_mul, star_star, hP_sa b, mul_assoc]
  have hreal_tr (a : Fin 3) :
      Matrix.trace (finiteQubitPauli a * M) / 2 = ((O_col a : ℝ) : ℂ) := by
    have hst : star (Matrix.trace (finiteQubitPauli a * M)) =
        Matrix.trace (finiteQubitPauli a * M) := by
      rw [htr_star, star_mul, hM_sa, hP_sa a, Matrix.trace_mul_comm]
    have him0 : (Matrix.trace (finiteQubitPauli a * M)).im = 0 := by
      have h := congrArg Complex.im hst
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith only [h]
    dsimp only [O_col]
    apply Complex.ext
    · simp
    · simp [him0]
  have htwo_decomp (X : Matrix Bool Bool ℂ) :
      X = (Matrix.trace X / 2) • (1 : Matrix Bool Bool ℂ) +
        ∑ a : Fin 3, (Matrix.trace (finiteQubitPauli a * X) / 2) • finiteQubitPauli a := by
    ext x y
    fin_cases x <;> fin_cases y
    all_goals simp [finiteQubitPauli, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
    · ring
    · ring_nf; rw [Complex.I_sq]; ring
    · ring_nf; rw [Complex.I_sq]; ring
    · ring
  refine ⟨htr0, ?_⟩
  have hdec := htwo_decomp M
  rw [htr0, zero_div, zero_smul, zero_add] at hdec
  rw [hdec]
  exact Finset.sum_congr rfl fun a _ => by rw [hreal_tr a]

/-- Master `U(2)^⊗N`-gauge-invariant operator-norm lower bound against **all** locally rotated
chain Hamiltonians with singular bond matrix `(bondMatrix v e).det = 0` (with **unrestricted**
onsite fields and other bonds):
`4 * (bondMatrix u e).det ^ 2 ≤ frobSq3 (bondMatrix u e) ^ 2 *
  ‖pathHamiltonian u - prodLocalMatrix R * pathHamiltonian v * star (prodLocalMatrix R)‖ ^ 2`. -/
theorem locallyRotated_bondDetZero_operator_dist_ge {n : ℕ}
    (u v : PathShell n) (e : Fin (n + 1)) (hv_det : (bondMatrix v e).det = 0)
    (R : Fin (n + 2) → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1) :
    let W := prodLocalMatrix R
    4 * (bondMatrix u e).det ^ 2 ≤
      frobSq3 (bondMatrix u e) ^ 2 *
        ‖pathHamiltonian u - W * pathHamiltonian v * star W‖ ^ 2 := by
  intro W
  let N := n + 2
  let M_R : Fin N → Fin 3 → Matrix Bool Bool ℂ := fun s b => R s * finiteQubitPauli b * star (R s)
  let O_R : Fin N → Matrix (Fin 3) (Fin 3) ℝ :=
    fun s a b => (Matrix.trace (finiteQubitPauli a * M_R s b)).re / 2
  have hMR (s : Fin N) (b : Fin 3) := conj_anyPauli_eq_real_pauli_comb (R s) (hR s) b
  have hR_one (s : Fin N) : R s * (1 : Matrix Bool Bool ℂ) * star (R s) = 1 := by
    rw [mul_one, (hR s).2]
  have htrace_prodLocal (A B : Fin N → Matrix Bool Bool ℂ) :
      Matrix.trace (prodLocalMatrix A * prodLocalMatrix B) =
        ∏ s : Fin N, Matrix.trace (A s * B s) := by
    rw [prodLocalMatrix_mul, Matrix.trace]
    simp only [Matrix.diag_apply, prodLocalMatrix]
    rw [← Fintype.prod_sum (fun s (b : Bool) => (A s * B s) b b)]
    rfl
  have hpauli_tr_one (a b : Fin 3) :
      Matrix.trace (star (finiteQubitPauli a) * finiteQubitPauli b) =
        if a = b then 2 else 0 := by
    fin_cases a <;> fin_cases b <;>
      simp [finiteQubitPauli, Matrix.trace, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply] <;>
      norm_num
  have hpauli_tr_zero (a : Fin 3) : Matrix.trace (star (finiteQubitPauli a)) = 0 := by
    rw [Matrix.star_eq_conjTranspose, (finiteQubitPauli_isHermitian a).eq]
    fin_cases a <;> simp [finiteQubitPauli, Matrix.trace]
  have htr_any_label (pq : Fin 3 × Fin 3) (l : PathLabel n) :
      Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
        (W * finitePauliMatrix (pathWord l) * star W)) =
        match l with
        | .inl _ => 0
        | .inr (e', pq') =>
            if e' = e then
              (2 : ℂ) ^ N * ((O_R e.castSucc pq.1 pq'.1 * O_R e.succ pq.2 pq'.2 : ℝ) : ℂ)
            else 0 := by
    rw [prodLocalMatrix_conj_pauli]
    have hP_st : star (finitePauliMatrix (couplingWord e pq)) =
        prodLocalMatrix (fun s => star (boolPauliOption (couplingWord e pq s))) := by
      rw [← prodLocalMatrix_star]; rfl
    rw [hP_st, htrace_prodLocal]
    rcases l with ⟨s₀, q₀⟩ | ⟨e', pq'⟩
    · have hex_end : ∃ t : Fin N, (t = e.castSucc ∨ t = e.succ) ∧ t ≠ s₀ := by
        by_cases h1 : e.castSucc = s₀
        · exact ⟨e.succ, Or.inr rfl, fun h2 => e.castSucc_lt_succ.ne (h1.trans h2.symm)⟩
        · exact ⟨e.castSucc, Or.inl rfl, h1⟩
      obtain ⟨t, ht_end, ht_ne⟩ := hex_end
      refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
      have hnone : pathWord (.inl (s₀, q₀)) t = none := by simp [pathWord, onsiteWord, ht_ne]
      rw [hnone, show boolPauliOption none = 1 from rfl, hR_one t]
      rcases ht_end with rfl | rfl
      · simp [couplingWord, boolPauliOption, hpauli_tr_zero]
      · simp [couplingWord, e.castSucc_lt_succ.ne', boolPauliOption, hpauli_tr_zero]
    · by_cases hee' : e' = e
      · subst e'
        dsimp only
        rw [if_pos rfl]
        let pairSet : Finset (Fin N) := {e.castSucc, e.succ}
        have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
        rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
        have hrest_prod : (∏ s ∈ pairSetᶜ,
            Matrix.trace (star (boolPauliOption (couplingWord e pq s)) *
              (R s * boolPauliOption (pathWord (.inr (e, pq')) s) * star (R s)))) =
            (2 : ℂ) ^ n := by
          have hc_card : pairSetᶜ.card = n := by
            have h1 := Finset.card_compl_add_card pairSet
            rw [Finset.card_pair hne_cs, Fintype.card_fin] at h1
            dsimp [N] at h1; omega
          have h1 : ∀ s ∈ pairSetᶜ,
              Matrix.trace (star (boolPauliOption (couplingWord e pq s)) *
                (R s * boolPauliOption (pathWord (.inr (e, pq')) s) * star (R s))) = 2 := by
            intro s hs
            simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
            have hs1 : couplingWord e pq s = none := by simp [couplingWord, hs.1, hs.2]
            have hs2 : pathWord (.inr (e, pq')) s = none := by simp [pathWord, couplingWord, hs.1, hs.2]
            rw [hs1, hs2, show boolPauliOption none = 1 from rfl, star_one, one_mul, hR_one s,
              Matrix.trace_one, Fintype.card_bool, Nat.cast_ofNat]
          rw [Finset.prod_congr rfl h1, Finset.prod_const, hc_card]
        have hend1 : Matrix.trace (star (boolPauliOption (couplingWord e pq e.castSucc)) *
            (R e.castSucc * boolPauliOption (pathWord (.inr (e, pq')) e.castSucc) * star (R e.castSucc))) =
            2 * ((O_R e.castSucc pq.1 pq'.1 : ℝ) : ℂ) := by
          have hc1 : boolPauliOption (couplingWord e pq e.castSucc) = finiteQubitPauli pq.1 := by
            simp [couplingWord, boolPauliOption]
          have hc2 : R e.castSucc * boolPauliOption (pathWord (.inr (e, pq')) e.castSucc) *
              star (R e.castSucc) = M_R e.castSucc pq'.1 := by
            simp [pathWord, couplingWord, boolPauliOption, M_R]
          rw [hc1, hc2]
          dsimp only [M_R]
          rw [(hMR e.castSucc pq'.1).2, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq.1]
          · rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.1 pq.1, if_pos rfl, smul_eq_mul, mul_comm]
          · intro a _ ha; rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.1 a, if_neg ha.symm, smul_zero]
          · simp
        have hend2 : Matrix.trace (star (boolPauliOption (couplingWord e pq e.succ)) *
            (R e.succ * boolPauliOption (pathWord (.inr (e, pq')) e.succ) * star (R e.succ))) =
            2 * ((O_R e.succ pq.2 pq'.2 : ℝ) : ℂ) := by
          have hc1 : boolPauliOption (couplingWord e pq e.succ) = finiteQubitPauli pq.2 := by
            simp [couplingWord, hne_cs.symm, boolPauliOption]
          have hc2 : R e.succ * boolPauliOption (pathWord (.inr (e, pq')) e.succ) *
              star (R e.succ) = M_R e.succ pq'.2 := by
            simp [pathWord, couplingWord, hne_cs.symm, boolPauliOption, M_R]
          rw [hc1, hc2]
          dsimp only [M_R]
          rw [(hMR e.succ pq'.2).2, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq.2]
          · rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.2 pq.2, if_pos rfl, smul_eq_mul, mul_comm]
          · intro a _ ha; rw [Matrix.mul_smul, Matrix.trace_smul, hpauli_tr_one pq.2 a, if_neg ha.symm, smul_zero]
          · simp
        rw [hend1, hend2, hrest_prod, Complex.ofReal_mul]
        have hpowN : (2 : ℂ) ^ N = (2 : ℂ) * (2 : ℂ) * (2 : ℂ) ^ n := by
          dsimp [N]; rw [pow_add]; ring
        rw [hpowN]; ring
      · dsimp only
        rw [if_neg hee']
        have hex_out : ∃ t : Fin N, (t = e'.castSucc ∨ t = e'.succ) ∧
            t ≠ e.castSucc ∧ t ≠ e.succ := by
          rcases lt_or_gt_of_ne hee' with hlt | hgt
          · refine ⟨e'.castSucc, Or.inl rfl, fun h => ?_, fun h => ?_⟩
            · exact hlt.ne (Fin.castSucc_injective _ h)
            · have hv' := congrArg Fin.val h; simp at hv'; have : e'.val < e.val := hlt; omega
          · refine ⟨e'.succ, Or.inr rfl, fun h => ?_, fun h => ?_⟩
            · have hv' := congrArg Fin.val h; simp at hv'; have : e.val < e'.val := hgt; omega
            · exact hgt.ne' (Fin.succ_injective _ h)
        obtain ⟨t, ht_e', ht_ne1, ht_ne2⟩ := hex_out
        refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
        have hnone_e : couplingWord e pq t = none := by simp [couplingWord, ht_ne1, ht_ne2]
        rcases ht_e' with rfl | rfl
        · have hsome : R e'.castSucc * boolPauliOption (pathWord (.inr (e', pq')) e'.castSucc) *
              star (R e'.castSucc) = M_R e'.castSucc pq'.1 := by
            simp [pathWord, couplingWord, boolPauliOption, M_R]
          rw [hnone_e, show boolPauliOption none = 1 from rfl, star_one, one_mul, hsome]
          exact (hMR e'.castSucc pq'.1).1
        · have hsome : R e'.succ * boolPauliOption (pathWord (.inr (e', pq')) e'.succ) *
              star (R e'.succ) = M_R e'.succ pq'.2 := by
            simp [pathWord, couplingWord, e'.castSucc_lt_succ.ne', boolPauliOption, M_R]
          rw [hnone_e, show boolPauliOption none = 1 from rfl, star_one, one_mul, hsome]
          exact (hMR e'.succ pq'.2).1
  let M_rot : Matrix (Fin 3) (Fin 3) ℝ := O_R e.castSucc * bondMatrix v e * (O_R e.succ)ᵀ
  have hM_rot_det : M_rot.det = 0 := by
    dsimp [M_rot]
    rw [Matrix.det_mul, Matrix.det_mul, hv_det, mul_zero, zero_mul]
  let Δ := pathHamiltonian u - W * pathHamiltonian v * star W
  have htr_Δ (pq : Fin 3 × Fin 3) :
      ((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ) =
        ((bondMatrix u e pq.1 pq.2 - M_rot pq.1 pq.2 : ℝ) : ℂ) := by
    have htr_u : Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * pathHamiltonian u) =
        (2 : ℂ) ^ N * ((bondMatrix u e pq.1 pq.2 : ℝ) : ℂ) := by
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.trace_sum,
        Finset.sum_eq_single (.inr (e, pq))]
      · rw [Matrix.mul_smul, Matrix.trace_smul]
        have hu := finitePauliMatrix_mem_unitary (couplingWord e pq)
        change _ • Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
          finitePauliMatrix (couplingWord e pq)) = _
        rw [(Unitary.mem_iff.mp hu).1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
        rfl
      · intro l _ hne
        rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul]
        have hword_ne : couplingWord e pq ≠ pathWord l := fun hw =>
          hne (@pathWord_injective n (.inr (e, pq)) l hw).symm
        rw [if_neg hword_ne, smul_zero]
      · simp
    have htr_v : Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
        (W * pathHamiltonian v * star W)) =
        (2 : ℂ) ^ N * ((M_rot pq.1 pq.2 : ℝ) : ℂ) := by
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
        Fintype.sum_sum_type]
      have hinl : (∑ x : Fin N × Fin 3,
          Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) *
            (W * (((v (.inl x) : ℝ) : ℂ) • finitePauliMatrix (pathWord (.inl x))) * star W))) = 0 :=
        Finset.sum_eq_zero fun x _ => by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
            htr_any_label pq (.inl x), smul_zero]
      rw [hinl, zero_add, Fintype.sum_prod_type, Finset.sum_eq_single e]
      · have hrot_val : M_rot pq.1 pq.2 = ∑ pq' : Fin 3 × Fin 3,
            v (.inr (e, pq')) * (O_R e.castSucc pq.1 pq'.1 * O_R e.succ pq.2 pq'.2) := by
          dsimp [M_rot, bondMatrix]
          rw [Matrix.mul_apply, Fintype.sum_prod_type]
          simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p' _ => ?_
          exact Finset.sum_congr rfl fun q' _ => by dsimp [bondMatrix]; ring
        rw [hrot_val, Complex.ofReal_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun pq' _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          htr_any_label pq (.inr (e, pq'))]
        dsimp only
        rw [if_pos rfl, smul_eq_mul]
        push_cast; ring
      · intro e' _ hee'
        refine Finset.sum_eq_zero fun pq' _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          htr_any_label pq (.inr (e', pq'))]
        dsimp only
        rw [if_neg hee', smul_zero]
      · simp
    dsimp only [Δ]
    rw [Matrix.mul_sub, Matrix.trace_sub, htr_u, htr_v]
    have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    push_cast
    field_simp [h2ne]
  -- Direct orthogonality Bessel bound on bond `e`
  have herr_sum : frobSq3 (bondMatrix u e - M_rot) ≤ ‖Δ‖ ^ 2 := by
    let α : Fin 3 × Fin 3 → ℂ := fun pq =>
      ((2 : ℂ) ^ N)⁻¹ * Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ)
    let Δ_proj : Register N := ∑ pq : Fin 3 × Fin 3, α pq • finitePauliMatrix (couplingWord e pq)
    let Rem : Register N := Δ - Δ_proj
    have horth_pq (pq₁ pq₂ : Fin 3 × Fin 3) :
        Matrix.trace (star (finitePauliMatrix (couplingWord e pq₁)) *
          finitePauliMatrix (couplingWord e pq₂)) =
          if pq₁ = pq₂ then (2 : ℂ) ^ N else 0 := by
      rw [trace_star_finitePauliMatrix_mul, Fintype.card_fin]
      by_cases h : pq₁ = pq₂
      · subst h; simp [N]
      · have hc_ne : couplingWord e pq₁ ≠ couplingWord e pq₂ := fun hw =>
          h ((Prod.mk.inj (Sum.inr.inj (@pathWord_injective n (.inr (e, pq₁)) (.inr (e, pq₂)) hw))).2)
        rw [if_neg hc_ne, if_neg h]
    have htr_proj_eq (pq : Fin 3 × Fin 3) :
        Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Δ_proj) =
          (2 : ℂ) ^ N * α pq := by
      dsimp only [Δ_proj]
      rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq]
      · rw [Matrix.mul_smul, Matrix.trace_smul, horth_pq pq pq, if_pos rfl, smul_eq_mul, mul_comm]
      · intro rs _ hrs
        rw [Matrix.mul_smul, Matrix.trace_smul, horth_pq pq rs, if_neg hrs.symm, smul_zero]
      · simp
    have htr_rem_zero (pq : Fin 3 × Fin 3) :
        Matrix.trace (star (finitePauliMatrix (couplingWord e pq)) * Rem) = 0 := by
      dsimp only [Rem]
      rw [Matrix.mul_sub, Matrix.trace_sub, htr_proj_eq pq]
      dsimp only [α]
      have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
      rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul, sub_self]
    have hhs_eq (X : Register N) :
        (Matrix.trace (star X * X)).re = ∑ b : Config N, ∑ a : Config N, ‖X a b‖ ^ 2 := by
      rw [Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hcross1 : Matrix.trace (star Δ_proj * Rem) = 0 := by
      dsimp only [Δ_proj]
      rw [star_sum, Matrix.sum_mul, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun pq _ => ?_
      rw [star_smul, Matrix.smul_mul, Matrix.trace_smul, htr_rem_zero pq, smul_zero]
    have hcross2 : (Matrix.trace (star Rem * Δ_proj)).re = 0 := by
      have htr_star (X : Register N) : star (Matrix.trace X) = Matrix.trace (star X) := by
        simp [Matrix.trace, star_sum]
      have hst : star (Matrix.trace (star Δ_proj * Rem)) = Matrix.trace (star Rem * Δ_proj) := by
        rw [htr_star, star_mul, star_star]
      rw [hcross1, star_zero] at hst
      rw [← hst, Complex.zero_re]
    have hproj_hs : (Matrix.trace (star Δ_proj * Δ_proj)).re =
        (2 : ℝ) ^ N * ∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2 := by
      have hc : Matrix.trace (star Δ_proj * Δ_proj) =
          (2 : ℂ) ^ N * ∑ pq : Fin 3 × Fin 3, (star (α pq) * α pq) := by
        conv_lhs => arg 1; arg 1; dsimp only [Δ_proj]
        rw [star_sum, Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun pq _ => ?_
        rw [star_smul, Matrix.smul_mul, Matrix.trace_smul, htr_proj_eq pq, smul_eq_mul]
        ring
      rw [hc]
      have hsum_real : (∑ pq : Fin 3 × Fin 3, star (α pq) * α pq) =
          ((∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun pq _ => ?_
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      rw [hsum_real, show ((2 : ℂ) ^ N) = (((2 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    have hpyth : (2 : ℝ) ^ N * (∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2) ≤
        ∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2 := by
      have hΔ_split : Δ = Rem + Δ_proj := by dsimp [Rem]; abel
      have htr_split : (Matrix.trace (star Δ * Δ)).re =
          (Matrix.trace (star Rem * Rem)).re + (Matrix.trace (star Δ_proj * Δ_proj)).re := by
        conv_lhs => rw [hΔ_split]
        rw [star_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
          Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
        simp only [Complex.add_re, hcross1, hcross2, add_zero, zero_add]
      have hrem_nn : 0 ≤ (Matrix.trace (star Rem * Rem)).re := by
        rw [hhs_eq]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [← hhs_eq Δ, htr_split, ← hproj_hs]
      linarith only [hrem_nn]
    have hΔ_hs_le : (∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2) ≤ (2 : ℝ) ^ N * ‖Δ‖ ^ 2 := by
      have hcol (b : Config N) : (∑ a : Config N, ‖Δ a b‖ ^ 2) ≤ ‖Δ‖ ^ 2 := by
        let e_b : EuclideanSpace ℂ (Config N) := EuclideanSpace.single b 1
        have he_n : ‖e_b‖ = 1 := by simp [e_b]
        have hle := pow_le_pow_left₀ (norm_nonneg _)
          ((Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) Δ).le_opNorm e_b) 2
        rw [Matrix.l2_opNorm_toEuclideanCLM, he_n, mul_one, EuclideanSpace.norm_sq_eq] at hle
        refine (le_of_eq ?_).trans hle
        refine Finset.sum_congr rfl fun a _ => ?_
        have happ : (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) Δ e_b).ofLp a = Δ a b := by
          rw [Matrix.ofLp_toEuclideanCLM]; simp [e_b]
        rw [happ]
      calc (∑ b : Config N, ∑ a : Config N, ‖Δ a b‖ ^ 2)
          ≤ ∑ _b : Config N, ‖Δ‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
        _ = (2 : ℝ) ^ N * ‖Δ‖ ^ 2 := by simp [Config, Finset.sum_const, nsmul_eq_mul]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos two_pos N
    have hsum_eq : frobSq3 (bondMatrix u e - M_rot) = ∑ pq : Fin 3 × Fin 3, ‖α pq‖ ^ 2 := by
      rw [frobSq3, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      dsimp only [α]
      rw [htr_Δ (p, q), Complex.norm_real, Real.norm_eq_abs, sq_abs, Matrix.sub_apply]
    rw [hsum_eq]
    exact le_of_mul_le_mul_left (hpyth.trans hΔ_hs_le) h2pos
  exact (four_det3_sq_le_frob_fourth_mul_dist_sq (bondMatrix u e) M_rot hM_rot_det).trans
    (mul_le_mul_of_nonneg_left herr_sum (sq_nonneg _))

/-- `U(2)^⊗N`-gauge-invariant operator-norm separation from **all** locally rotated Ising chains
via the full bond determinant `(bondMatrix u e).det`. -/
theorem locallyRotatedIsing_operator_dist_ge_of_bondDet {n : ℕ}
    (u v : PathShell n) (hv : ∀ l : PathLabel n, ¬ IsDiagLabel l → v l = 0)
    (R : Fin (n + 2) → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (e : Fin (n + 1)) :
    let W := prodLocalMatrix R
    4 * (bondMatrix u e).det ^ 2 ≤
      frobSq3 (bondMatrix u e) ^ 2 *
        ‖pathHamiltonian u - W * pathHamiltonian v * star W‖ ^ 2 := by
  have hv_det : (bondMatrix v e).det = 0 := by
    have h0 (q : Fin 3) : bondMatrix v e 0 q = 0 :=
      hv (.inr (e, (0, q))) (by simp [IsDiagLabel])
    rw [Matrix.det_fin_three, h0 0, h0 1, h0 2]; ring
  exact locallyRotated_bondDetZero_operator_dist_ge u v e hv_det R hR

/-- `U(2)^⊗N`-gauge-invariant operator-norm separation from the **entire** locally rotated
`(5N - 4)`-parameter `so(2N)` matchgate / free-fermion manifold `isMatchgateChainLabel` via
`(bondMatrix u e).det`. -/
theorem locallyRotatedMatchgate_operator_dist_ge_of_bondDet {n : ℕ}
    (u v : PathShell n) (hv : ∀ l : PathLabel n, ¬ isMatchgateChainLabel l → v l = 0)
    (R : Fin (n + 2) → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (e : Fin (n + 1)) :
    let W := prodLocalMatrix R
    4 * (bondMatrix u e).det ^ 2 ≤
      frobSq3 (bondMatrix u e) ^ 2 *
        ‖pathHamiltonian u - W * pathHamiltonian v * star W‖ ^ 2 := by
  have hv_det : (bondMatrix v e).det = 0 := by
    have h2 (q : Fin 3) : bondMatrix v e 2 q = 0 :=
      hv (.inr (e, (2, q))) (by simp [isMatchgateChainLabel])
    rw [Matrix.det_fin_three, h2 0, h2 1, h2 2]; ring
  exact locallyRotated_bondDetZero_operator_dist_ge u v e hv_det R hR

/-! ## Section 4: Abstract `C*`-algebra Clifford quadratic-vs-quartic exclusion & nonlocal escape -/

/-- `ℂ`-linear span of identity and quadratic Clifford products `{1} ∪ {γ_a γ_b : a ≠ b}`. -/
def cliffordQuadraticSpan {A : Type*} [CStarAlgebra A] {m : ℕ} (γ : Fin m → A) : Submodule ℂ A :=
  Submodule.span ℂ ({(1 : A)} ∪ {X : A | ∃ a b : Fin m, a ≠ b ∧ X = γ a * γ b})

/-- Abstract Clifford quadratic-vs-quartic exclusion: over any nontrivial `C*`-algebra `A`, if
`γ : Fin m → A` satisfies `γ_a² = 1` and `γ_a γ_b = -γ_b γ_a` (`a ≠ b`), then for any four
pairwise distinct indices `a₀, b₀, a₁, b₁ : Fin m`, the quartic Clifford monomial
`γ_{a₀} * γ_{b₀} * γ_{a₁} * γ_{b₁}` does **not** belong to `cliffordQuadraticSpan γ`. -/
theorem quartic_not_mem_cliffordQuadraticSpan {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {m : ℕ} {γ : Fin m → A}
    (hsq : ∀ a, γ a * γ a = 1) (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a))
    {a₀ b₀ a₁ b₁ : Fin m}
    (h01 : a₀ ≠ b₀) (h02 : a₀ ≠ a₁) (h03 : a₀ ≠ b₁)
    (h12 : b₀ ≠ a₁) (h13 : b₀ ≠ b₁) (h23 : a₁ ≠ b₁) :
    (γ a₀ * γ b₀) * (γ a₁ * γ b₁) ∉ cliffordQuadraticSpan γ := by
  intro hmem
  let S₄ : Finset (Fin m) := {a₀, b₀, a₁, b₁}
  have hcard4 : S₄.card = 4 := by
    simp [S₄, h01, h02, h03, h12, h13, h23]
  let Q₄ : A := (γ a₀ * γ b₀) * (γ a₁ * γ b₁)
  -- Conjugating `Q₄` by `γ d` negates `Q₄` for `d ∈ S₄` and fixes `Q₄` for `d ∉ S₄`.
  have hconj_pair {x y : Fin m} (hxy : x ≠ y) (d : Fin m) :
      γ d * (γ x * γ y) * γ d =
        if d = x ∨ d = y then -(γ x * γ y) else γ x * γ y := by
    by_cases hdx : d = x
    · subst hdx
      have hdy : d ≠ y := hxy
      rw [if_pos (Or.inl rfl), ← mul_assoc (γ d) (γ d), hsq d, one_mul, hanti y d hdy.symm]
    · by_cases hdy : d = y
      · subst hdy
        rw [if_pos (Or.inr rfl), ← mul_assoc (γ d) (γ x), mul_assoc (γ d * γ x), hsq d,
          mul_one, hanti d x hdx]
      · rw [if_neg (not_or.mpr ⟨hdx, hdy⟩)]
        calc γ d * (γ x * γ y) * γ d
            = (γ d * γ x) * (γ y * γ d) := by simp only [mul_assoc]
          _ = (-(γ x * γ d)) * (-(γ d * γ y)) := by rw [hanti d x hdx, hanti y d (Ne.symm hdy)]
          _ = γ x * (γ d * γ d) * γ y := by rw [neg_mul, mul_neg, neg_neg]; simp only [mul_assoc]
          _ = γ x * γ y := by rw [hsq d, mul_one]
  have hconj_Q₄ (d : Fin m) :
      γ d * Q₄ * γ d = if d ∈ S₄ then -Q₄ else Q₄ := by
    have hsplit : γ d * ((γ a₀ * γ b₀) * (γ a₁ * γ b₁)) * γ d =
        (γ d * (γ a₀ * γ b₀) * γ d) * (γ d * (γ a₁ * γ b₁) * γ d) := by
      calc γ d * ((γ a₀ * γ b₀) * (γ a₁ * γ b₁)) * γ d
          = γ d * (γ a₀ * γ b₀) * (γ d * γ d) * (γ a₁ * γ b₁) * γ d := by
              rw [hsq d, mul_one]; simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    dsimp [Q₄]
    rw [hsplit, hconj_pair h01 d, hconj_pair h23 d]
    simp only [S₄, Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne d a₀ with rfl | hda0
    · have hnot : ¬ (d = a₁ ∨ d = b₁) := not_or.mpr ⟨h02, h03⟩
      simp [hnot]
    · rcases eq_or_ne d b₀ with rfl | hdb0
      · have hnot : ¬ (d = a₁ ∨ d = b₁) := not_or.mpr ⟨h12, h13⟩
        simp [hda0, hnot]
      · rcases eq_or_ne d a₁ with rfl | hda1
        · simp [hda0, hdb0]
        · rcases eq_or_ne d b₁ with rfl | hdb1
          · simp [hda0, hdb0, hda1]
          · simp [hda0, hdb0, hda1, hdb1]
  -- Define the `ℂ`-linear operator `minusTwirl d (X) = (1/2) • (X - γ_d X γ_d)`
  -- which fixes `Q₄` for `d ∈ S₄` and annihilates any element fixed by `Ad(γ_d)`.
  let minusTwirl (d : Fin m) : A →ₗ[ℂ] A :=
    { toFun := fun X => (1 / 2 : ℂ) • (X - γ d * X * γ d)
      map_add' := fun X Y => by
        rw [← smul_add]
        refine congrArg ((1 / 2 : ℂ) • ·) ?_
        rw [mul_add, add_mul]; abel
      map_smul' := fun r X => by
        simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul,
          mul_comm (1 / 2 : ℂ) r] }
  let P₄ : A →ₗ[ℂ] A :=
    (minusTwirl a₀).comp ((minusTwirl b₀).comp ((minusTwirl a₁).comp (minusTwirl b₁)))
  have hfix_d {d : Fin m} (hd : d ∈ S₄) : minusTwirl d Q₄ = Q₄ := by
    dsimp [minusTwirl]
    rw [hconj_Q₄ d, if_pos hd, sub_neg_eq_add, ← two_smul ℂ Q₄, smul_smul,
      show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
  have hP₄_Q₄ : P₄ Q₄ = Q₄ := by
    dsimp [P₄]
    rw [hfix_d (by simp [S₄]), hfix_d (by simp [S₄]), hfix_d (by simp [S₄]), hfix_d (by simp [S₄])]
  have hP₄_gen_zero : ∀ X ∈ ({(1 : A)} ∪ {X : A | ∃ a b : Fin m, a ≠ b ∧ X = γ a * γ b}),
      P₄ X = 0 := by
    rintro X (rfl | ⟨x, y, hxy, rfl⟩)
    · have hm1 (d : Fin m) : minusTwirl d 1 = 0 := by
        dsimp [minusTwirl]; rw [mul_one, hsq d, sub_self, smul_zero]
      dsimp [P₄]; rw [hm1 b₁, map_zero, map_zero, map_zero]
    · -- At least one of `{a₀, b₀, a₁, b₁}` lies outside `{x, y}` since `S₄.card = 4 > 2`.
      have hex_out : ∃ d ∈ S₄, d ≠ x ∧ d ≠ y := by
        by_contra hall_in
        push Not at hall_in
        have hsub : S₄ ⊆ {x, y} := fun d hd => by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hdx : d = x
          · exact Or.inl hdx
          · exact Or.inr (hall_in d hd hdx)
        have hle := (Finset.card_le_card hsub).trans (Finset.card_pair hxy).le
        omega
      obtain ⟨d, hd_S, hdx, hdy⟩ := hex_out
      have hkill_d : minusTwirl d (γ x * γ y) = 0 := by
        dsimp [minusTwirl]
        rw [hconj_pair hxy d, if_neg (not_or.mpr ⟨hdx, hdy⟩), sub_self, smul_zero]
      have hdich (e : Fin m) :
          minusTwirl e (γ x * γ y) = 0 ∨ minusTwirl e (γ x * γ y) = γ x * γ y := by
        dsimp [minusTwirl]
        rw [hconj_pair hxy e]
        by_cases he : e = x ∨ e = y
        · right
          rw [if_pos he, sub_neg_eq_add, ← two_smul ℂ, smul_smul,
            show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
        · left; rw [if_neg he, sub_self, smul_zero]
      have hstep_zero {Y : A} (hY : Y = 0 ∨ Y = γ x * γ y) (e : Fin m) :
          minusTwirl e Y = 0 ∨ minusTwirl e Y = γ x * γ y := by
        rcases hY with rfl | rfl
        · rw [map_zero]; exact Or.inl rfl
        · exact hdich e
      simp only [S₄, Finset.mem_insert, Finset.mem_singleton] at hd_S
      dsimp [P₄]
      rcases hd_S with rfl | rfl | rfl | rfl
      · rcases hstep_zero (hstep_zero (hdich b₁) a₁) b₀ with hz | heq
        · rw [hz, map_zero]
        · rw [heq, hkill_d]
      · rcases hstep_zero (hdich b₁) a₁ with hz | heq
        · rw [hz, map_zero, map_zero]
        · rw [heq, hkill_d, map_zero]
      · rcases hdich b₁ with hz | heq
        · rw [hz, map_zero, map_zero, map_zero]
        · rw [heq, hkill_d, map_zero, map_zero]
      · rw [hkill_d, map_zero, map_zero, map_zero]
  have hP₄_zero : P₄ Q₄ = 0 := by
    dsimp only [Q₄]
    refine Submodule.span_induction ?_ (map_zero P₄)
      (fun u v _ _ hu hv => by rw [map_add, hu, hv, add_zero])
      (fun r u _ hu => by rw [map_smul, hu, smul_zero]) hmem
    exact hP₄_gen_zero
  rw [hP₄_Q₄] at hP₄_zero
  have hQ₄_sq : Q₄ * Q₄ = 1 := by
    dsimp [Q₄]
    have hcomm : (γ a₀ * γ b₀) * (γ a₁ * γ b₁) = (γ a₁ * γ b₁) * (γ a₀ * γ b₀) := by
      have hc := hconj_pair h23 a₀
      rw [if_neg (not_or.mpr ⟨h02, h03⟩)] at hc
      have hc2 := hconj_pair h23 b₀
      rw [if_neg (not_or.mpr ⟨h12, h13⟩)] at hc2
      calc (γ a₀ * γ b₀) * (γ a₁ * γ b₁)
          = γ a₀ * (γ b₀ * (γ a₁ * γ b₁) * γ b₀) * γ b₀ := by
              simp only [mul_assoc]; rw [hsq b₀, mul_one]
        _ = γ a₀ * ((γ a₁ * γ b₁) * γ b₀) := by rw [hc2]; simp only [mul_assoc]
        _ = (γ a₀ * (γ a₁ * γ b₁) * γ a₀) * (γ a₀ * γ b₀) := by
              simp only [mul_assoc]; rw [← mul_assoc (γ a₀) (γ a₀), hsq a₀, one_mul]
        _ = (γ a₁ * γ b₁) * (γ a₀ * γ b₀) := by rw [hc]
    have hp1 : (γ a₀ * γ b₀) * (γ a₀ * γ b₀) = -1 := by
      rw [← mul_assoc, mul_assoc (γ a₀), hanti b₀ a₀ h01.symm, mul_neg, ← mul_assoc,
        hsq a₀, one_mul, neg_mul, hsq b₀]
    have hp2 : (γ a₁ * γ b₁) * (γ a₁ * γ b₁) = -1 := by
      rw [← mul_assoc, mul_assoc (γ a₁), hanti b₁ a₁ h23.symm, mul_neg, ← mul_assoc,
        hsq a₁, one_mul, neg_mul, hsq b₁]
    calc ((γ a₀ * γ b₀) * (γ a₁ * γ b₁)) * ((γ a₀ * γ b₀) * (γ a₁ * γ b₁))
        = (γ a₀ * γ b₀) * ((γ a₁ * γ b₁) * (γ a₀ * γ b₀)) * (γ a₁ * γ b₁) := by
            simp only [mul_assoc]
      _ = ((γ a₀ * γ b₀) * (γ a₀ * γ b₀)) * ((γ a₁ * γ b₁) * (γ a₁ * γ b₁)) := by
            rw [← hcomm]; simp only [mul_assoc]
      _ = 1 := by rw [hp1, hp2, neg_mul, mul_neg, neg_neg, one_mul]
  rw [hP₄_zero, zero_mul] at hQ₄_sq
  exact (zero_ne_one : (0 : A) ≠ 1) hQ₄_sq

/-- Abstract commuting-triple obstruction to quadratic Clifford membership: over any nontrivial
`C*`-algebra `A`, no three elements `Q₀ = z₀ • (γ_{a₀} * γ_{b₀})`, `Q₁ = z₁ • (γ_{a₁} * γ_{b₁})`
(`z₀ ≠ 0`, `z₁ ≠ 0`, `a₀ ≠ b₀`, `a₁ ≠ b₁`) and `Q₂ ∈ cliffordQuadraticSpan γ` can satisfy
`Q₀ * Q₁ = Q₁ * Q₀`, `∀ c : ℂ, Q₀ ≠ c • Q₁`, and `Q₀ * Q₁ = Q₂`. -/
theorem not_mem_cliffordQuadraticSpan_of_commuting_triple {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {m : ℕ} {γ : Fin m → A}
    (hsq : ∀ a, γ a * γ a = 1) (hanti : ∀ a b, a ≠ b → γ a * γ b = -(γ b * γ a))
    {a₀ b₀ a₁ b₁ : Fin m} {z₀ z₁ : ℂ} (hz₀ : z₀ ≠ 0) (hz₁ : z₁ ≠ 0)
    (h01 : a₀ ≠ b₀) (h23 : a₁ ≠ b₁)
    (hcomm : (z₀ • (γ a₀ * γ b₀)) * (z₁ • (γ a₁ * γ b₁)) =
      (z₁ • (γ a₁ * γ b₁)) * (z₀ • (γ a₀ * γ b₀)))
    (hnprop : ∀ c : ℂ, z₀ • (γ a₀ * γ b₀) ≠ c • (z₁ • (γ a₁ * γ b₁))) :
    (z₀ • (γ a₀ * γ b₀)) * (z₁ • (γ a₁ * γ b₁)) ∉ cliffordQuadraticSpan γ := by
  -- First show `{a₀, b₀}` and `{a₁, b₁}` are disjoint (`a₀, b₀, a₁, b₁` all distinct).
  have hpair_comm : (γ a₀ * γ b₀) * (γ a₁ * γ b₁) = (γ a₁ * γ b₁) * (γ a₀ * γ b₀) := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm z₁ z₀] at hcomm
    have h := congrArg ((z₀ * z₁)⁻¹ • ·) hcomm
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hz₀ hz₁), one_smul] using h
  have hpair_ne : γ a₀ * γ b₀ ≠ γ a₁ * γ b₁ ∧ γ a₀ * γ b₀ ≠ -(γ a₁ * γ b₁) := by
    refine ⟨fun heq => hnprop (z₀ * z₁⁻¹) ?_, fun heq => hnprop (-(z₀ * z₁⁻¹)) ?_⟩
    · rw [heq, smul_smul, mul_assoc, inv_mul_cancel₀ hz₁, mul_one]
    · rw [heq, smul_neg, neg_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hz₁, mul_one]
  -- If `x = u` and `y ≠ v`, `(γ_x γ_y)(γ_x γ_v) = -(γ_x γ_v)(γ_x γ_y)` and `(γ_x γ_y)² = -1 ≠ 0`.
  have hanti_share {x y v : Fin m} (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v) :
      (γ x * γ y) * (γ x * γ v) ≠ (γ x * γ v) * (γ x * γ y) := by
    intro hc
    have hL : (γ x * γ y) * (γ x * γ v) = -(γ y * γ v) := by
      rw [← mul_assoc, mul_assoc (γ x), hanti y x hxy.symm, mul_neg, ← mul_assoc,
        hsq x, one_mul, neg_mul]
    have hR : (γ x * γ v) * (γ x * γ y) = γ y * γ v := by
      rw [← mul_assoc, mul_assoc (γ x), hanti v x hxv.symm, mul_neg, ← mul_assoc,
        hsq x, one_mul, neg_mul, hanti v y hyv.symm, neg_neg]
    rw [hL, hR] at hc
    have h2 : ((2 : ℂ) • (γ y * γ v)) = 0 := by
      rw [two_smul]
      conv_lhs => arg 1; rw [← hc]
      exact neg_add_cancel _
    have h0 : γ y * γ v = 0 := by
      have h := congrArg ((2 : ℂ)⁻¹ • ·) h2
      simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, smul_zero] using h
    have h1 : (γ y * γ v) * (γ v * γ y) = 1 := by
      rw [← mul_assoc, mul_assoc (γ y), hsq v, mul_one, hsq y]
    rw [h0, zero_mul] at h1
    exact (zero_ne_one : (0 : A) ≠ 1) h1
  have h02 : a₀ ≠ a₁ := by
    intro h; subst h
    by_cases hb : b₀ = b₁
    · subst hb; exact hpair_ne.1 rfl
    · exact hanti_share h01 h23 hb hpair_comm
  have h03 : a₀ ≠ b₁ := by
    intro h; subst h
    by_cases hb : b₀ = a₁
    · subst hb; exact hpair_ne.2 (hanti a₀ b₀ h01)
    · have hc' : (γ a₀ * γ b₀) * (γ a₀ * γ a₁) = (γ a₀ * γ a₁) * (γ a₀ * γ b₀) := by
        rw [hanti a₀ a₁ h23.symm, neg_mul, mul_neg, hpair_comm]
      exact hanti_share h01 h23.symm hb hc'
  have h12 : b₀ ≠ a₁ := by
    intro h; subst h
    have hc' : (γ b₀ * γ a₀) * (γ b₀ * γ b₁) = (γ b₀ * γ b₁) * (γ b₀ * γ a₀) := by
      rw [hanti b₀ a₀ h01.symm, neg_mul, mul_neg, hpair_comm]
    exact hanti_share h01.symm h23 h03 hc'
  have h13 : b₀ ≠ b₁ := by
    intro h; subst h
    have hc' : (γ b₀ * γ a₀) * (γ b₀ * γ a₁) = (γ b₀ * γ a₁) * (γ b₀ * γ a₀) := by
      rw [hanti b₀ a₀ h01.symm, hanti b₀ a₁ h23.symm, neg_mul, mul_neg, neg_neg,
        mul_neg, neg_mul, neg_neg, hpair_comm]
    exact hanti_share h01.symm h23.symm h02 hc'
  intro hmem
  rw [smul_mul_smul_comm] at hmem
  have hmem4 := Submodule.smul_mem (cliffordQuadraticSpan γ) (z₀ * z₁)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hz₀ hz₁), one_smul] at hmem4
  exact quartic_not_mem_cliffordQuadraticSpan hsq hanti h01 h02 h03 h12 h13 h23 hmem4

private theorem optMul_some_of_distinct3 {q₀ q₁ q₂ : Fin 3}
    (h01 : q₀ ≠ q₁) (h02 : q₀ ≠ q₂) (h12 : q₁ ≠ q₂) :
    optMul (some q₀) (some q₁) = some q₂ := by
  fin_cases q₀ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp_all [optMul]

/-- Nonlocal Pauli-Majorana Clifford escape: for **any** family `Γ : Fin (2 * (n + 2)) → Register (n + 2)`
of pairwise-anticommuting signed Pauli strings (`Γ_a² = 1`, `Γ_a Γ_b = -Γ_b Γ_a` for `a ≠ b`, and
`∀ a, ∃ z_a P_a, z_a ≠ 0 ∧ Γ_a = z_a • finitePauliMatrix P_a`), if `(bondMatrix u e).det ≠ 0` on
some bond `e : Fin (n + 1)`, then `pathHamiltonian u ∉ cliffordQuadraticSpan Γ`. -/
theorem not_mem_pauliMajoranaQuadraticSpan_of_bondDet_ne_zero {n : ℕ}
    (Γ : Fin (2 * (n + 2)) → Register (n + 2))
    (hsq : ∀ a, Γ a * Γ a = 1)
    (hanti : ∀ a b, a ≠ b → Γ a * Γ b = -(Γ b * Γ a))
    (hpauli : ∀ a, ∃ (z : ℂ) (P : Fin (n + 2) → Option (Fin 3)),
      z ≠ 0 ∧ Γ a = z • finitePauliMatrix P)
    (u : PathShell n) (e : Fin (n + 1)) (hdet : (bondMatrix u e).det ≠ 0) :
    pathHamiltonian u ∉ cliffordQuadraticSpan Γ := by
  intro hmem
  let N := n + 2
  haveI : Nontrivial (Register N) := by
    refine ⟨⟨0, 1, fun h => (zero_ne_one : (0 : ℂ) ≠ 1) ?_⟩⟩
    simpa using congrFun (congrFun h (fun _ => false)) (fun _ => false)
  -- Each generator of `cliffordQuadraticSpan Γ` is a scalar multiple of a single `finitePauliMatrix`.
  have hquad_pauli (a b : Fin (2 * N)) :
      ∃ (w : ℂ) (Q : Fin N → Option (Fin 3)),
        w ≠ 0 ∧ Γ a * Γ b = w • finitePauliMatrix Q := by
    obtain ⟨z₁, P₁, hz₁, h₁⟩ := hpauli a
    obtain ⟨z₂, P₂, hz₂, h₂⟩ := hpauli b
    refine ⟨(z₁ * z₂) * ∏ s : Fin N, optPhase (P₁ s) (P₂ s),
      fun s => optMul (P₁ s) (P₂ s), ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero hz₁ hz₂) (Finset.prod_ne_zero_iff.mpr fun s _ => ?_)
      have hnorm := norm_optPhase (P₁ s) (P₂ s)
      intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
    · rw [h₁, h₂, smul_mul_smul_comm, finitePauliMatrix_mul, smul_smul]
  -- If `H(u) ∈ cliffordQuadraticSpan Γ` and `u l ≠ 0`, `finitePauliMatrix (pathWord l)` has
  -- nonzero trace inner product with some quadratic generator `Γ_a * Γ_b` (`a ≠ b`), hence equals
  -- a nonzero multiple of that `Γ_a * Γ_b`!
  have hterm_quad (l : PathLabel n) (hul : u l ≠ 0) :
      ∃ (a b : Fin (2 * N)) (z : ℂ), a ≠ b ∧ z ≠ 0 ∧
        finitePauliMatrix (pathWord l) = z • (Γ a * Γ b) := by
    let P_l := finitePauliMatrix (pathWord l)
    have htr_Pl_H : Matrix.trace (star P_l * pathHamiltonian u) ≠ 0 := by
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single l]
      · rw [Matrix.mul_smul, Matrix.trace_smul]
        have hu := finitePauliMatrix_mem_unitary (pathWord l)
        change _ • Matrix.trace (star P_l * P_l) ≠ 0
        rw [(Unitary.mem_iff.mp hu).1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, smul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hul) (pow_ne_zero N (by norm_num))
      · intro l' _ hne
        rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul]
        have hw_ne : pathWord l ≠ pathWord l' := fun hw => hne (@pathWord_injective n l l' hw).symm
        rw [if_neg hw_ne, smul_zero]
      · simp
    have hex_gen : ∃ X ∈ ({(1 : Register N)} ∪ {X | ∃ a b : Fin (2 * N), a ≠ b ∧ X = Γ a * Γ b}),
        Matrix.trace (star P_l * X) ≠ 0 := by
      by_contra hall0
      push Not at hall0
      have h0 : Matrix.trace (star P_l * pathHamiltonian u) = 0 := by
        refine Submodule.span_induction ?_ (by simp)
          (fun x y _ _ hx hy => by rw [Matrix.mul_add, Matrix.trace_add, hx, hy, add_zero])
          (fun r x _ hx => by rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]) hmem
        exact hall0
      exact htr_Pl_H h0
    obtain ⟨X, hX_gen, htr_ne⟩ := hex_gen
    rcases hX_gen with rfl | ⟨a, b, hab, rfl⟩
    · exfalso
      apply htr_ne
      have h1 : (1 : Register N) = finitePauliMatrix (pauliIdentityLabel N) := by
        ext x y; rw [Matrix.one_apply]
        by_cases hxy : x = y
        · subst hxy; simp [finitePauliMatrix, pauliIdentityLabel, boolPauliOptionEntry, boolPauliOption]
        · rw [if_neg hxy]
          obtain ⟨s, hs⟩ := Function.ne_iff.mp hxy
          exact (Finset.prod_eq_zero (Finset.mem_univ s)
            (by simp [pauliIdentityLabel, boolPauliOptionEntry, boolPauliOption, hs])).symm
      rw [h1, trace_star_finitePauliMatrix_mul, if_neg (pathWord_ne_identity l)]
    · obtain ⟨w, Q, hw_ne, hΓQ⟩ := hquad_pauli a b
      rw [hΓQ, Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul] at htr_ne
      by_cases hPQ : pathWord l = Q
      · subst hPQ
        refine ⟨a, b, w⁻¹, hab, inv_ne_zero hw_ne, ?_⟩
        rw [hΓQ, smul_smul, inv_mul_cancel₀ hw_ne, one_smul]
      · rw [if_neg hPQ, smul_zero] at htr_ne
        exact (htr_ne rfl).elim
  -- Since `(bondMatrix u e).det ≠ 0`, some permutation `π : Equiv.Perm (Fin 3)` has
  -- `bondMatrix u e 0 (π 0) ≠ 0`, `bondMatrix u e 1 (π 1) ≠ 0`, `bondMatrix u e 2 (π 2) ≠ 0`.
  have hex_perm : ∃ (q₀ q₁ q₂ : Fin 3) (sgn : ℂ),
      q₀ ≠ q₁ ∧ q₀ ≠ q₂ ∧ q₁ ≠ q₂ ∧ (sgn = 1 ∨ sgn = -1) ∧
      (optPhase (some q₀) (some q₁) = sgn * Complex.I ∧
        optPhase (some q₁) (some q₀) = -(sgn * Complex.I)) ∧
      bondMatrix u e 0 q₀ ≠ 0 ∧ bondMatrix u e 1 q₁ ≠ 0 ∧ bondMatrix u e 2 q₂ ≠ 0 := by
    by_contra hall_z
    push Not at hall_z
    have hz_term (q₀ q₁ q₂ : Fin 3) (sgn : ℂ) (h01 : q₀ ≠ q₁) (h02 : q₀ ≠ q₂) (h12 : q₁ ≠ q₂)
        (hsgn : sgn = 1 ∨ sgn = -1)
        (hph : optPhase (some q₀) (some q₁) = sgn * Complex.I ∧
          optPhase (some q₁) (some q₀) = -(sgn * Complex.I)) :
        bondMatrix u e 0 q₀ * bondMatrix u e 1 q₁ * bondMatrix u e 2 q₂ = 0 := by
      by_cases h0 : bondMatrix u e 0 q₀ = 0
      · rw [h0, zero_mul, zero_mul]
      · by_cases h1 : bondMatrix u e 1 q₁ = 0
        · rw [h1, mul_zero, zero_mul]
        · rw [hall_z q₀ q₁ q₂ sgn h01 h02 h12 hsgn hph h0 h1, mul_zero]
    have t012 := hz_term 0 1 2 1 (by decide) (by decide) (by decide) (Or.inl rfl) (by simp [optPhase])
    have t021 := hz_term 0 2 1 (-1) (by decide) (by decide) (by decide) (Or.inr rfl) (by simp [optPhase])
    have t102 := hz_term 1 0 2 (-1) (by decide) (by decide) (by decide) (Or.inr rfl) (by simp [optPhase])
    have t120 := hz_term 1 2 0 1 (by decide) (by decide) (by decide) (Or.inl rfl) (by simp [optPhase])
    have t201 := hz_term 2 0 1 1 (by decide) (by decide) (by decide) (Or.inl rfl) (by simp [optPhase])
    have t210 := hz_term 2 1 0 (-1) (by decide) (by decide) (by decide) (Or.inr rfl) (by simp [optPhase])
    apply hdet
    rw [Matrix.det_fin_three]
    linarith only [t012, t021, t102, t120, t201, t210]
  obtain ⟨q₀, q₁, q₂, sgn, hq01, hq02, hq12, _hsgn, hph_q, hu0, hu1, hu2⟩ := hex_perm
  obtain ⟨a₀, b₀, z₀, hab₀, hz₀, hQ₀⟩ := hterm_quad (.inr (e, (0, q₀))) hu0
  obtain ⟨a₁, b₁, z₁, hab₁, hz₁, hQ₁⟩ := hterm_quad (.inr (e, (1, q₁))) hu1
  obtain ⟨a₂, b₂, z₂, hab₂, hz₂, hQ₂⟩ := hterm_quad (.inr (e, (2, q₂))) hu2
  let P₀ := finitePauliMatrix (couplingWord e (0, q₀))
  let P₁ := finitePauliMatrix (couplingWord e (1, q₁))
  let P₂ := finitePauliMatrix (couplingWord e (2, q₂))
  -- Check `P₀ * P₁ = P₁ * P₀` and `P₀ * P₁ = (-sgn) • P₂`!
  have hprod_P01 : P₀ * P₁ = (-sgn) • P₂ ∧ P₁ * P₀ = (-sgn) • P₂ := by
    have hlbl1 : (fun s : Fin N => optMul (couplingWord e (0, q₀) s) (couplingWord e (1, q₁) s)) =
        couplingWord e (2, q₂) := by
      funext s
      by_cases hs1 : s = e.castSucc
      · subst hs1; simp only [couplingWord, ↓reduceIte]; decide
      · by_cases hs2 : s = e.succ
        · subst hs2; simp only [couplingWord, e.castSucc_lt_succ.ne', ↓reduceIte]
          exact optMul_some_of_distinct3 hq01 hq02 hq12
        · simp [couplingWord, hs1, hs2, optMul]
    have hlbl2 : (fun s : Fin N => optMul (couplingWord e (1, q₁) s) (couplingWord e (0, q₀) s)) =
        couplingWord e (2, q₂) := by
      rw [← hlbl1]; funext s; exact optMul_comm _ _
    have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
    let pairSet : Finset (Fin N) := {e.castSucc, e.succ}
    have hout1 : ∀ s ∈ pairSetᶜ,
        optPhase (couplingWord e (0, q₀) s) (couplingWord e (1, q₁) s) = 1 := by
      intro s hs
      simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [couplingWord, hs.1, hs.2, optPhase]
    have hout2 : ∀ s ∈ pairSetᶜ,
        optPhase (couplingWord e (1, q₁) s) (couplingWord e (0, q₀) s) = 1 := by
      intro s hs
      simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [couplingWord, hs.1, hs.2, optPhase]
    refine ⟨?_, ?_⟩
    · dsimp [P₀, P₁, P₂]
      rw [finitePauliMatrix_mul, hlbl1, ← Finset.prod_mul_prod_compl pairSet,
        Finset.prod_pair hne_cs, Finset.prod_eq_one hout1, mul_one]
      simp only [couplingWord, ↓reduceIte, hne_cs.symm]
      have h01_ph : optPhase (some (0 : Fin 3)) (some 1) = Complex.I := rfl
      rw [h01_ph, hph_q.1]
      congr 1; ring_nf; rw [Complex.I_sq]; ring
    · dsimp [P₀, P₁, P₂]
      rw [finitePauliMatrix_mul, hlbl2, ← Finset.prod_mul_prod_compl pairSet,
        Finset.prod_pair hne_cs, Finset.prod_eq_one hout2, mul_one]
      simp only [couplingWord, ↓reduceIte, hne_cs.symm]
      have h10_ph : optPhase (some (1 : Fin 3)) (some 0) = -Complex.I := rfl
      rw [h10_ph, hph_q.2]
      congr 1; ring_nf; rw [Complex.I_sq]; ring
  have hcomm_01 : (z₀ • (Γ a₀ * Γ b₀)) * (z₁ • (Γ a₁ * Γ b₁)) =
      (z₁ • (Γ a₁ * Γ b₁)) * (z₀ • (Γ a₀ * Γ b₀)) := by
    rw [← hQ₀, ← hQ₁]
    change P₀ * P₁ = P₁ * P₀
    rw [hprod_P01.1, hprod_P01.2]
  have hnprop_01 : ∀ c : ℂ, z₀ • (Γ a₀ * Γ b₀) ≠ c • (z₁ • (Γ a₁ * Γ b₁)) := by
    intro c hprop
    rw [← hQ₀, ← hQ₁] at hprop
    change P₀ = c • P₁ at hprop
    have htr := congrArg (fun X => Matrix.trace (star P₀ * X)) hprop
    have hu_P₀ := finitePauliMatrix_mem_unitary (couplingWord e (0, q₀))
    have hL : Matrix.trace (star P₀ * P₀) = (2 : ℂ) ^ N := by
      rw [(Unitary.mem_iff.mp hu_P₀).1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    have hword_ne : couplingWord e (0, q₀) ≠ couplingWord e (1, q₁) := fun hw => by
      have h := congrFun hw e.castSucc
      simp [couplingWord] at h
    have hR : Matrix.trace (star P₀ * (c • P₁)) = 0 := by
      rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul,
        if_neg hword_ne, smul_zero]
    rw [hL, hR] at htr
    exact pow_ne_zero N (by norm_num) htr
  have hmem_prod : (z₀ • (Γ a₀ * Γ b₀)) * (z₁ • (Γ a₁ * Γ b₁)) ∈ cliffordQuadraticSpan Γ := by
    rw [← hQ₀, ← hQ₁]
    change P₀ * P₁ ∈ cliffordQuadraticSpan Γ
    rw [hprod_P01.1, show P₂ = z₂ • (Γ a₂ * Γ b₂) from hQ₂, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a₂, b₂, hab₂, rfl⟩))
  exact not_mem_cliffordQuadraticSpan_of_commuting_triple hsq hanti hz₀ hz₁ hab₀ hab₁
    hcomm_01 hnprop_01 hmem_prod

#print axioms four_det3_sq_le_frob_fourth_mul_dist_sq
#print axioms bondRankThreeFieldEvent_compl_prob_le
#print axioms locallyRotated_bondDetZero_operator_dist_ge
#print axioms locallyRotatedIsing_operator_dist_ge_of_bondDet
#print axioms locallyRotatedMatchgate_operator_dist_ge_of_bondDet
#print axioms quartic_not_mem_cliffordQuadraticSpan
#print axioms not_mem_cliffordQuadraticSpan_of_commuting_triple
#print axioms not_mem_pauliMajoranaQuadraticSpan_of_bondDet_ne_zero

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
