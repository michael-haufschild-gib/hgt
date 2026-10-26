import GaloisForLFunctions.MultiplicativePositivityGeometry.FiniteBoundaryDivisors
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryDivisorRange
import GaloisForLFunctions.RHTower.LogVonMangoldtGaussianSums

/-!
# Bochner's theorem for locally finite boundary divisors

`D : ℝ → ℝ` is *locally finite* if every set `{v : D v ≠ 0, |v| ≤ R}` is finite. Such a `D` is the
boundary divisor of a family of nonnegative weights iff it is even and positive definite
(`locallyFinite_boundary_divisor_iff`). Infinitely many poles and zeros at arbitrary heights are
allowed; no lattice and no bound on their orders is assumed.

* **Fejér truncation** (`IsEvenPosDef.mul_fejerFactor`). `D(v)(1 − |v|/N)⁺` is positive definite:
  `N(1 − |x − y|/N)⁺` is the length of `[x, x + N] ∩ [y, y + N]`, so each Gram form of the product is
  the integral over `t` of a Gram form of `D` with coefficients `c_i 1_{[x_i, x_i + N]}(t)`. For
  locally finite `D` it is a finite configuration, so its Bohr polynomial is nonnegative.
* **Approximate identity** (`dirichletMean`). `Q_n(u) = n^{−2} Σ_{k=1}^{n²} cos(ku/n)` has
  nonnegative coefficients, `Q_n(0) = 1` and `|Q_n(u)| ≤ π/(n|u|)` for `0 < |u| ≤ πn`.
* **Convolution** (`convPoly_eq`). `E(0)Q_n(u) + Σ_z E(z)(Q_n(u − z) + Q_n(u + z))` equals
  `n^{−2} Σ_k P_E(k/n) cos(ku/n)`, a positive cosine polynomial when the Bohr polynomial `P_E ≥ 0`.
  Taking `n` large against the number of points of the truncation, it tends to `D(u)` at every `u`:
  all other points of `D` keep a fixed distance from `u`.

The range theorem (`isBoundaryDivisor_of_tendsto_posCosPoly`) turns the sequence into weights.
Local finiteness cannot be dropped: `1_ℚ` is positive definite and not a boundary divisor
(`rationalIndicator_not_boundaryDivisor`).
-/

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Fejér truncation -/

/-- The Fejér factor `(1 − |v|/N)⁺`. -/
noncomputable def fejerFactor (N v : ℝ) : ℝ := max (1 - |v| / N) 0

theorem fejerFactor_nonneg (N v : ℝ) : 0 ≤ fejerFactor N v := le_max_right _ _

theorem fejerFactor_le_one {N : ℝ} (hN : 0 < N) (v : ℝ) : fejerFactor N v ≤ 1 := by
  have : 0 ≤ |v| / N := by positivity
  exact max_le (by linarith) zero_le_one

theorem fejerFactor_eq_zero {N v : ℝ} (hN : 0 < N) (hv : N ≤ |v|) : fejerFactor N v = 0 :=
  max_eq_right (by rw [sub_nonpos, le_div_iff₀ hN]; linarith)

/-- The overlap of `[x, x + N]` and `[y, y + N]` has length `N (1 − |x − y|/N)⁺`. -/
theorem integral_indicator_mul_indicator {N : ℝ} (hN : 0 < N) (x y : ℝ) :
    ∫ t, (Set.Icc x (x + N)).indicator (1 : ℝ → ℝ) t * (Set.Icc y (y + N)).indicator 1 t =
      N * fejerFactor N (x - y) := by
  have hfun : (fun t => (Set.Icc x (x + N)).indicator (1 : ℝ → ℝ) t *
      (Set.Icc y (y + N)).indicator 1 t) = (Set.Icc x (x + N) ∩ Set.Icc y (y + N)).indicator 1 := by
    rw [Set.inter_indicator_one]; rfl
  rw [hfun, integral_indicator_one (measurableSet_Icc.inter measurableSet_Icc), Set.Icc_inter_Icc,
    Real.volume_real_Icc, fejerFactor, mul_max_of_nonneg _ _ hN.le, mul_zero, mul_sub, mul_one,
    mul_div_cancel₀ _ hN.ne', min_add_add_right]
  congr 1
  linarith [max_sub_min_eq_abs' x y]

/-- **Fejér truncation preserves positive definiteness.** -/
theorem IsEvenPosDef.mul_fejerFactor {D : ℝ → ℝ} (hD : IsEvenPosDef D) {N : ℝ} (hN : 0 < N) :
    IsEvenPosDef fun v => D v * fejerFactor N v where
  even u := by simp only [fejerFactor, abs_neg, hD.even]
  posDef n x c := by
    set f : Fin n → ℝ → ℝ := fun i => (Set.Icc (x i) (x i + N)).indicator 1
    have hint : ∀ i j, Integrable fun t => f i t * f j t := fun i j => by
      have hfun : (fun t => f i t * f j t) =
          (Set.Icc (x i) (x i + N) ∩ Set.Icc (x j) (x j + N)).indicator 1 := by
        simp only [f]; rw [Set.inter_indicator_one]; rfl
      rw [hfun]
      exact (continuous_one.integrableOn_Icc.mono_set Set.inter_subset_left).integrable_indicator
        (measurableSet_Icc.inter measurableSet_Icc)
    -- Each Gram form is `N⁻¹ ∫ (Gram form of D with coefficients c_i f_i(t)) dt`.
    have key : ∑ i, ∑ j, c i * c j * (D (x i - x j) * fejerFactor N (x i - x j)) =
        N⁻¹ * ∫ t, ∑ i, ∑ j, c i * f i t * (c j * f j t) * D (x i - x j) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (((hint i j).const_mul (c i * c j)).mul_const (D (x i - x j))).congr
            (Eventually.of_forall fun t => by ring), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ =>
          (((hint i j).const_mul (c i * c j)).mul_const (D (x i - x j))).congr
            (Eventually.of_forall fun t => by ring), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (fun t => c i * f i t * (c j * f j t) * D (x i - x j)) =
          fun t => c i * c j * D (x i - x j) * (f i t * f j t) by funext t; ring,
        integral_const_mul, integral_indicator_mul_indicator hN]
      field_simp
    rw [key]
    exact mul_nonneg (inv_nonneg.mpr hN.le)
      (integral_nonneg fun t => hD.posDef n x fun i => c i * f i t)

/-! ### The approximate identity -/

/-- `Q_n(u) = n^{−2} Σ_{k=1}^{n²} cos(ku/n)`. -/
noncomputable def dirichletMean (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (n ^ 2), 1 / (n : ℝ) ^ 2 * Real.cos ((k : ℝ) / n * u)

theorem dirichletMean_zero {n : ℕ} (hn : 0 < n) : dirichletMean n 0 = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [dirichletMean, mul_zero, Real.cos_zero, mul_one, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, Nat.add_sub_cancel]
  push_cast
  field_simp

/-- `|Q_n(u)| ≤ π/(n|u|)` for `0 < |u| ≤ πn`. -/
theorem abs_dirichletMean_le {n : ℕ} (hn : 0 < n) {u : ℝ} (hu0 : 0 < |u|)
    (hu : |u| ≤ Real.pi * n) : |dirichletMean n u| ≤ Real.pi / (n * |u|) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrw : dirichletMean n u = 1 / (n : ℝ) ^ 2 * ∑ k ∈ Icc 1 (n ^ 2), Real.cos (k * (u / n)) := by
    rw [dirichletMean, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [show (k : ℝ) / n * u = k * (u / n) by ring]
  set y := u / n / 2 with hy_def
  have hyabs : |y| = |u| / (2 * n) := by
    rw [hy_def, abs_div, abs_div, abs_of_pos hn', abs_two, div_div, mul_comm]
  have hy0 : 0 < |y| := by rw [hyabs]; positivity
  have hy : |y| ≤ Real.pi / 2 := by
    rw [hyabs, div_le_div_iff₀ (by positivity) two_pos]; nlinarith
  -- Jordan's inequality.
  have hsin : 2 / Real.pi * |y| ≤ |Real.sin y| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy ⊢
      exact (Real.mul_le_sin h hy).trans (le_abs_self _)
    · rw [abs_of_neg h] at hy ⊢
      have := Real.mul_le_sin (neg_nonneg.mpr h.le) hy
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hsin0 : 0 < |Real.sin y| := lt_of_lt_of_le (by positivity) hsin
  have hsum := RHTower.GaussZeroSum.abs_sum_cos_le (θ := u / n) (abs_pos.mp hsin0) (n ^ 2)
  rw [hrw, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (n : ℝ) ^ 2 * |∑ k ∈ Icc 1 (n ^ 2), Real.cos (k * (u / n))|
      ≤ 1 / (n : ℝ) ^ 2 * (1 / (2 / Real.pi * |y|)) :=
        mul_le_mul_of_nonneg_left (hsum.trans (one_div_le_one_div_of_le (by positivity) hsin))
          (by positivity)
    _ = Real.pi / (n * |u|) := by
        rw [hyabs]; field_simp

/-! ### Convolution with a finite configuration -/

/-- `E(0) Q_n(u) + Σ_{z ∈ Z} E(z)(Q_n(u − z) + Q_n(u + z))`: the configuration `E` smoothed by
`Q_n`. -/
noncomputable def convPoly (E : ℝ → ℝ) (Z : Finset ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  E 0 * dirichletMean n u + ∑ z ∈ Z, E z * (dirichletMean n (u - z) + dirichletMean n (u + z))

/-- Convolving a cosine polynomial with a configuration multiplies its coefficients by the Bohr
polynomial at the frequencies. -/
theorem conv_bohr (E : ℝ → ℝ) (Z : Finset ℝ) {ι : Type*} (s : Finset ι) (c lam : ι → ℝ) (u : ℝ) :
    E 0 * ∑ k ∈ s, c k * Real.cos (lam k * u) + ∑ z ∈ Z, E z *
      (∑ k ∈ s, c k * Real.cos (lam k * (u - z)) + ∑ k ∈ s, c k * Real.cos (lam k * (u + z))) =
      ∑ k ∈ s, c k * bohrPoly E Z (lam k) * Real.cos (lam k * u) := by
  have hmode : ∀ k z, c k * (2 * E z * Real.cos (z * lam k)) * Real.cos (lam k * u) =
      E z * (c k * Real.cos (lam k * (u - z)) + c k * Real.cos (lam k * (u + z))) := by
    intro k z
    rw [show lam k * (u - z) = lam k * u - z * lam k by ring,
      show lam k * (u + z) = lam k * u + z * lam k by ring, Real.cos_sub, Real.cos_add]
    ring
  have h1 : ∀ k ∈ s, c k * bohrPoly E Z (lam k) * Real.cos (lam k * u) =
      E 0 * (c k * Real.cos (lam k * u)) + ∑ z ∈ Z, E z *
        (c k * Real.cos (lam k * (u - z)) + c k * Real.cos (lam k * (u + z))) := by
    intro k _
    simp only [bohrPoly, apPoly]
    rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun z _ => hmode k z
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

theorem convPoly_eq (E : ℝ → ℝ) (Z : Finset ℝ) (n : ℕ) (u : ℝ) :
    convPoly E Z n u = ∑ k ∈ Icc 1 (n ^ 2),
      1 / (n : ℝ) ^ 2 * bohrPoly E Z ((k : ℝ) / n) * Real.cos ((k : ℝ) / n * u) :=
  conv_bohr E Z (Icc 1 (n ^ 2)) (fun _ => 1 / (n : ℝ) ^ 2) (fun k => (k : ℝ) / n) u

/-- A configuration with nonnegative Bohr polynomial smooths to a positive cosine polynomial. -/
theorem convPoly_isPosCosPoly {E : ℝ → ℝ} {Z : Finset ℝ} (hP : ∀ t, 0 ≤ bohrPoly E Z t) (n : ℕ) :
    IsPosCosPoly (convPoly E Z n) := by
  rw [show convPoly E Z n = fun u => ∑ k ∈ Icc 1 (n ^ 2),
      1 / (n : ℝ) ^ 2 * bohrPoly E Z ((k : ℝ) / n) * Real.cos ((k : ℝ) / n * u) from
    funext (convPoly_eq E Z n)]
  exact isPosCosPoly_finset_sum _ _ _ fun k _ => mul_nonneg (by positivity) (hP _)

/-- The smoothing error at `u` is controlled by `Q_n − δ₀` at the differences `u − v`. -/
theorem abs_convPoly_sub_le {E : ℝ → ℝ} {Z : Finset ℝ} (hcfg : IsFiniteConfig E Z) {n : ℕ}
    {u M B : ℝ} (hM : ∀ v, |E v| ≤ M)
    (hY : ∀ v, (v = 0 ∨ v ∈ Z ∨ -v ∈ Z) → |dirichletMean n (u - v) - diracAt (u - v)| ≤ B) :
    |convPoly E Z n u - E u| ≤ M * B * (1 + 2 * Z.card) := by
  have hY0 : |dirichletMean n u - diracAt u| ≤ B := by simpa using hY 0 (Or.inl rfl)
  have hYm : ∀ z ∈ Z, |dirichletMean n (u - z) - diracAt (u - z)| ≤ B :=
    fun z hz => hY z (Or.inr (Or.inl hz))
  have hYp : ∀ z ∈ Z, |dirichletMean n (u + z) - diracAt (u + z)| ≤ B := fun z hz => by
    simpa using hY (-z) (Or.inr (Or.inr (by simpa using hz)))
  have halg : convPoly E Z n u - E u = E 0 * (dirichletMean n u - diracAt u) +
      ∑ z ∈ Z, E z * ((dirichletMean n (u - z) - diracAt (u - z)) +
        (dirichletMean n (u + z) - diracAt (u + z))) := by
    rw [← congrFun (apDivisor_bohr hcfg) u]
    simp only [convPoly, apDivisor]
    have hz : ∀ z ∈ Z, E z * ((dirichletMean n (u - z) - diracAt (u - z)) +
        (dirichletMean n (u + z) - diracAt (u + z))) =
        E z * (dirichletMean n (u - z) + dirichletMean n (u + z)) -
          2 * E z / 2 * (diracAt (u + z) + diracAt (u - z)) := fun z _ => by ring
    rw [Finset.sum_congr rfl hz, Finset.sum_sub_distrib]
    ring
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [halg]
  refine (abs_add_le _ _).trans ?_
  have hsum : |∑ z ∈ Z, E z * ((dirichletMean n (u - z) - diracAt (u - z)) +
      (dirichletMean n (u + z) - diracAt (u + z)))| ≤ ∑ z ∈ Z, M * (B + B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z hz => ?_)
    rw [abs_mul]
    exact mul_le_mul (hM z) ((abs_add_le _ _).trans (add_le_add (hYm z hz) (hYp z hz)))
      (abs_nonneg _) hM0
  rw [abs_mul]
  have h0 := mul_le_mul (hM 0) hY0 (abs_nonneg _) hM0
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-! ### Locally finite configurations -/

variable {D : ℝ → ℝ}

/-- A locally finite function keeps every other point of its support (and `0`) at a positive
distance from a given `u`. -/
theorem exists_gap (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (u : ℝ) :
    ∃ δ > 0, ∀ v, (D v ≠ 0 ∨ v = 0) → v ≠ u → δ ≤ |u - v| := by
  classical
  set T : Finset ℝ := (insert 0 (hloc (|u| + 1)).toFinset).erase u
  have hnear : ∀ v, (D v ≠ 0 ∨ v = 0) → v ≠ u → |v| ≤ |u| + 1 → v ∈ T := by
    intro v hv hvu hvb
    refine Finset.mem_erase.mpr ⟨hvu, ?_⟩
    rcases hv with hv | rfl
    · exact Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).mpr ⟨hv, hvb⟩)
    · exact Finset.mem_insert_self _ _
  have hfar : ∀ v, ¬ |v| ≤ |u| + 1 → 1 ≤ |u - v| := fun v hv => by
    have := abs_sub_abs_le_abs_sub v u
    rw [abs_sub_comm] at this
    linarith
  by_cases hT : T.Nonempty
  · obtain ⟨v₀, hv₀, hmin⟩ := T.exists_min_image (fun v => |u - v|) hT
    have hv₀u : v₀ ≠ u := (Finset.mem_erase.mp hv₀).1
    refine ⟨min 1 |u - v₀|, lt_min one_pos (abs_pos.mpr (sub_ne_zero.mpr hv₀u.symm)),
      fun v hv hvu => ?_⟩
    by_cases hvb : |v| ≤ |u| + 1
    · exact (min_le_right _ _).trans (hmin v (hnear v hv hvu hvb))
    · exact (min_le_left _ _).trans (hfar v hvb)
  · refine ⟨1, one_pos, fun v hv hvu => ?_⟩
    by_cases hvb : |v| ≤ |u| + 1
    · exact absurd ⟨v, hnear v hv hvu hvb⟩ hT
    · exact hfar v hvb

/-- The heights `0 < z ≤ N + 1` carrying `D`. -/
noncomputable def fejerHeights (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    Finset ℝ :=
  ((hloc ((N : ℝ) + 1)).toFinset).filter (0 < ·)

/-- The Fejér truncation `D(v)(1 − |v|/(N + 1))⁺`. -/
noncomputable def fejerConfig (D : ℝ → ℝ) (N : ℕ) (v : ℝ) : ℝ := D v * fejerFactor ((N : ℝ) + 1) v

theorem mem_fejerHeights {hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite} {N : ℕ} {z : ℝ} :
    z ∈ fejerHeights hloc N ↔ (D z ≠ 0 ∧ |z| ≤ (N : ℝ) + 1) ∧ 0 < z := by
  simp [fejerHeights]

theorem fejerConfig_isFiniteConfig (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    IsFiniteConfig (fejerConfig D N) (fejerHeights hloc N) where
  pos z hz := (mem_fejerHeights.mp hz).2
  even u := by simp only [fejerConfig, fejerFactor, abs_neg, hpd.even]
  supp u hu hZ := by
    unfold fejerConfig
    by_cases hDu : D u = 0
    · rw [hDu, zero_mul]
    by_cases hub : |u| ≤ (N : ℝ) + 1
    · exfalso
      refine hZ (mem_fejerHeights.mpr ⟨⟨?_, by rwa [abs_abs]⟩, abs_pos.mpr hu⟩)
      rcases abs_choice u with h | h <;> rw [h]
      · exact hDu
      · rwa [hpd.even]
    · rw [fejerFactor_eq_zero (by positivity) (not_le.mp hub).le, mul_zero]

theorem fejerConfig_isEvenPosDef (hpd : IsEvenPosDef D) (N : ℕ) :
    IsEvenPosDef (fejerConfig D N) :=
  hpd.mul_fejerFactor (by positivity)

/-- The smoothing order `(N + 1)(1 + 2 #Z_N)`. -/
noncomputable def fejerOrder (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) : ℕ :=
  (N + 1) * (1 + 2 * (fejerHeights hloc N).card)

/-- The approximating positive cosine polynomials. -/
noncomputable def fejerPoly (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    ℝ → ℝ :=
  convPoly (fejerConfig D N) (fejerHeights hloc N) (fejerOrder hloc N)

theorem fejerPoly_isPosCosPoly (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    IsPosCosPoly (fejerPoly hloc N) :=
  convPoly_isPosCosPoly (bohrPoly_nonneg (fejerConfig_isFiniteConfig hpd hloc N)
    (fejerConfig_isEvenPosDef hpd N)) _

/-- The smoothing error at stage `N`, once `|u| ≤ N`, is at most `D(0) π/((N + 1) δ)`. -/
theorem abs_fejerPoly_sub_le (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {u δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ v, (D v ≠ 0 ∨ v = 0) → v ≠ u → δ ≤ |u - v|) {N : ℕ} (hN : |u| ≤ N) :
    |fejerPoly hloc N u - fejerConfig D N u| ≤ D 0 * Real.pi / (((N : ℝ) + 1) * δ) := by
  have hcfg := fejerConfig_isFiniteConfig hpd hloc N
  have hn : 0 < fejerOrder hloc N := by unfold fejerOrder; positivity
  have hnR : (fejerOrder hloc N : ℝ) = ((N : ℝ) + 1) * (1 + 2 * (fejerHeights hloc N).card) := by
    unfold fejerOrder; push_cast; ring
  have hNn : (N : ℝ) + 1 ≤ fejerOrder hloc N := by
    rw [hnR]; nlinarith [(Nat.cast_nonneg (fejerHeights hloc N).card : (0 : ℝ) ≤ _)]
  have hM : ∀ v, |fejerConfig D N v| ≤ D 0 := fun v => by
    unfold fejerConfig
    rw [abs_mul, abs_of_nonneg (fejerFactor_nonneg _ _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (fejerFactor_le_one (by positivity) v)).trans
      (hpd.abs_le_apply_zero v)
  have hY : ∀ v, (v = 0 ∨ v ∈ fejerHeights hloc N ∨ -v ∈ fejerHeights hloc N) →
      |dirichletMean (fejerOrder hloc N) (u - v) - diracAt (u - v)| ≤
        Real.pi / (fejerOrder hloc N * δ) := by
    intro v hv
    -- Every such `v` is `0` or a point of `D` with `|v| ≤ N + 1`.
    have hv' : (D v ≠ 0 ∨ v = 0) ∧ |v| ≤ (N : ℝ) + 1 := by
      rcases hv with rfl | hv | hv
      · exact ⟨Or.inr rfl, by simp; positivity⟩
      · exact ⟨Or.inl (mem_fejerHeights.mp hv).1.1, (mem_fejerHeights.mp hv).1.2⟩
      · have h := (mem_fejerHeights.mp hv).1
        rw [hpd.even, abs_neg] at h
        exact ⟨Or.inl h.1, h.2⟩
    by_cases hw : u - v = 0
    · rw [hw, dirichletMean_zero hn, diracAt, if_pos rfl, sub_self, abs_zero]
      positivity
    · have hvu : v ≠ u := fun h => hw (by rw [h, sub_self])
      have h1 := hgap v hv'.1 hvu
      have h2 : |u - v| ≤ Real.pi * fejerOrder hloc N := by
        have := abs_sub u v
        nlinarith [Real.pi_gt_three, hv'.2]
      rw [diracAt, if_neg hw, sub_zero]
      refine (abs_dirichletMean_le hn (abs_pos.mpr hw) h2).trans ?_
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
        (mul_le_mul_of_nonneg_left h1 (by positivity))
  refine (abs_convPoly_sub_le hcfg hM hY).trans (le_of_eq ?_)
  rw [hnR]
  field_simp

theorem tendsto_fejerFactor (u : ℝ) :
    Tendsto (fun N : ℕ => fejerFactor ((N : ℝ) + 1) u) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (h0.const_mul |u|).const_sub 1
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|u|⌉₊] with N hN
  have hN' : |u| ≤ (N : ℝ) + 1 := by
    have h1 := Nat.le_ceil |u|
    have h2 : (⌈|u|⌉₊ : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold fejerFactor
  rw [max_eq_left (by rw [sub_nonneg, div_le_one (by positivity)]; exact hN'), mul_one_div]

/-- **The Fejér polynomials converge to `D` at every height.** -/
theorem tendsto_fejerPoly (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (u : ℝ) :
    Tendsto (fun N => fejerPoly hloc N u) atTop (𝓝 (D u)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hloc u
  have hE : Tendsto (fun N : ℕ => fejerConfig D N u) atTop (𝓝 (D u)) := by
    have := (tendsto_fejerFactor u).const_mul (D u)
    rwa [mul_one] at this
  have h0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hB : Tendsto (fun N : ℕ => D 0 * Real.pi / (((N : ℝ) + 1) * δ)) atTop (𝓝 0) := by
    have h := h0.const_mul (D 0 * Real.pi / δ)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    rw [div_mul_div_comm, mul_one, mul_comm δ]
  have herr : Tendsto (fun N : ℕ => fejerPoly hloc N u - fejerConfig D N u) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [eventually_ge_atTop ⌈|u|⌉₊] with N hN
    rw [Real.norm_eq_abs]
    exact abs_fejerPoly_sub_le hpd hloc hδ hgap ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  have := hE.add herr
  rw [add_zero] at this
  exact this.congr fun N => by ring

/-- **Locally finite positive-definite functions are boundary divisors.** -/
theorem locallyFinite_isBoundaryDivisor (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    ∃ (lam : ℕ × ℕ → ℝ) (w : ℝ → ℕ × ℕ → ℝ), IsBoundaryDivisor lam w D :=
  isBoundaryDivisor_of_tendsto_posCosPoly (fejerPoly_isPosCosPoly hpd hloc)
    (tendsto_fejerPoly hpd hloc)

/-- **Bochner's theorem for locally finite boundary divisors.** A locally finite `D` is the boundary
divisor of some family of nonnegative weights iff it is even and positive definite. -/
theorem locallyFinite_boundary_divisor_iff
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    (∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w D) ↔ IsEvenPosDef D :=
  ⟨fun ⟨_, _, _, hw⟩ => hw.isEvenPosDef, fun hpd =>
    let ⟨lam, w, hw⟩ := locallyFinite_isBoundaryDivisor hpd hloc
    ⟨_, lam, w, hw⟩⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
