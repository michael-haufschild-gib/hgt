import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing

/-!
# The overlap ratio is the covered measure

An atomic test `f = Σ_{n ≤ N} x_n g(· − log n)` with `g` supported in `[0, w]` vanishes off the
cover `⋃_n [log n, log n + w]` (`atomicTest_eq_zero_of_not_mem_atomCover`), a set of measure at
most `N w` (`measureReal_atomCover_le`). Since `N δ_N ≤ 1` (`natCast_mul_atomSpacing_le_one`), an
atomic test of overlap ratio `K = w/δ_N` lives on a set of measure at most `K`, whatever `N` and
the coefficients are.

* **No atomic test of bounded overlap approximates an interval**
  (`sub_le_setIntegral_sq_of_overlap`): for every interval `I` of length `L`,
  `∫_I (1 − f)² ≥ L − K`. At the fixed ratio `c★` of the spacing, where Weil positivity, the Hodge
  index and `(TD_π)` of the atomic family are theorems, no atomic test comes within `L²`-distance
  `√(1 − c★)` of the indicator of a unit interval (`one_sub_fixedWidthRatio_le_setIntegral_sq`):
  the families on which the Hodge index is proved are not exhaustive.
* **Exhaustion needs unbounded overlap** (`le_overlap_of_setIntegral_sq_le`): approximating the
  indicator of an interval of length `L` to `L²`-error `ε` forces `K ≥ L − ε²`. Covering the atomic
  range `[0, log N]` forces `K ≥ log N − ε²`: the overlap ratio of an exhaustive atomic family grows
  at least like `log N`, the regime in which the fixed-width positivity of the atomic Weil Grams is
  RH.
* **Adapted families and the Nyquist rate** (`adaptedTest`, `measureReal_adaptedCover_le`,
  `sub_le_setIntegral_sq_adapted`): with a bump of width `w_n ≤ c log(1 + 1/n)` at each atom — a
  fixed fraction of the local spacing — the cells are disjoint for `c < 1`
  (`adaptedCell_disjoint`) and cover measure at most `c log(N + 1)`, a fraction `c` of the range
  `[0, log(N + 1)]` of the atoms: `∫_{[0, log(N+1)]} (1 − f)² ≥ (1 − c) log(N + 1)`. Ratio one is
  the Nyquist rate of the adapted family.
-/

noncomputable section

open MeasureTheory Set Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-- The cover `⋃_{1 ≤ n ≤ N} [log n, log n + w]` of the atoms. -/
def atomCover (N : ℕ) (w : ℝ) : Set ℝ :=
  ⋃ n ∈ Finset.Icc 1 N, Set.Icc (Real.log n) (Real.log n + w)

theorem measurableSet_atomCover (N : ℕ) (w : ℝ) : MeasurableSet (atomCover N w) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc

/-- An atomic test vanishes off the cover of its atoms. -/
theorem atomicTest_eq_zero_of_not_mem_atomCover (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (N : ℕ) (x : ℕ → ℝ) {u : ℝ} (hu : u ∉ atomCover N w) : atomicTest N x g u = 0 := by
  unfold atomicTest
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn' : u ∉ Set.Icc (Real.log n) (Real.log n + w) := fun h =>
    hu (Set.mem_biUnion hn h)
  rw [hgsupp _ fun h => hn' ⟨by linarith [h.1], by linarith [h.2]⟩, mul_zero]

/-- **The cover has measure at most `N w`.** -/
theorem measureReal_atomCover_le (hw : 0 ≤ w) (N : ℕ) : volume.real (atomCover N w) ≤ N * w := by
  calc volume.real (atomCover N w)
      ≤ ∑ n ∈ Finset.Icc 1 N, volume.real (Set.Icc (Real.log n) (Real.log n + w)) :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, w := Finset.sum_congr rfl fun n _ => by
        rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    _ = N * w := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num

/-- `N δ_N ≤ 1`: the atoms `log n`, `n ≤ N`, have total spacing budget one. -/
theorem natCast_mul_atomSpacing_le_one {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) * atomSpacing N ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h : atomSpacing N ≤ 1 / N := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
    unfold atomSpacing
    linarith
  calc (N : ℝ) * atomSpacing N ≤ N * (1 / N) := mul_le_mul_of_nonneg_left h hN0.le
    _ = 1 := by field_simp

/-- **No atomic test approximates an interval beyond its covered measure**:
`∫_{[a, a+L]} (1 − f)² ≥ L − N w`. -/
theorem sub_le_setIntegral_sq (hg : Continuous g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    L - N * w ≤ ∫ u in Set.Icc a (a + L), (1 - atomicTest N x g u) ^ 2 := by
  set I := Set.Icc a (a + L)
  set S := atomCover N w
  have hcont : Continuous fun u => (1 - atomicTest N x g u) ^ 2 := by
    unfold atomicTest
    exact (continuous_const.sub (continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hg.comp (continuous_id.sub continuous_const)))).pow 2
  have hint : IntegrableOn (fun u => (1 - atomicTest N x g u) ^ 2) I :=
    hcont.continuousOn.integrableOn_Icc
  -- off the cover the integrand is one
  have hoff : ∫ u in I \ S, (1 - atomicTest N x g u) ^ 2 = volume.real (I \ S) := by
    rw [setIntegral_congr_fun (measurableSet_Icc.diff (measurableSet_atomCover N w))
      (g := fun _ => (1 : ℝ)) fun u hu => by
        simp only [atomicTest_eq_zero_of_not_mem_atomCover hgsupp N x hu.2, sub_zero, one_pow],
      setIntegral_const, smul_eq_mul, mul_one]
  have hmono : ∫ u in I \ S, (1 - atomicTest N x g u) ^ 2 ≤
      ∫ u in I, (1 - atomicTest N x g u) ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun u => sq_nonneg _)
      (Filter.Eventually.of_forall Set.sdiff_subset)
  have hmeas : L - N * w ≤ volume.real (I \ S) := by
    have hS : volume S ≠ ⊤ := by
      show volume (⋃ n ∈ Finset.Icc 1 N, Set.Icc (Real.log n) (Real.log n + w)) ≠ ⊤
      refine ne_of_lt ((measure_biUnion_finset_le _ _).trans_lt ?_)
      exact ENNReal.sum_lt_top.mpr fun n _ => by simp [Real.volume_Icc]
    have h1 := le_measureReal_sdiff (μ := volume) (s₁ := I) (s₂ := S) hS
    rw [Real.volume_real_Icc_of_le (by linarith)] at h1
    have h2 := measureReal_atomCover_le hw N
    linarith
  linarith

/-- **Bounded overlap does not exhaust**: an atomic test of overlap ratio at most `K`
(`w ≤ K δ_N`) satisfies `∫_{[a, a+L]} (1 − f)² ≥ L − K`. -/
theorem sub_le_setIntegral_sq_of_overlap (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) {N : ℕ} (hN : 1 ≤ N) {K : ℝ}
    (hK : w ≤ K * atomSpacing N) (x : ℕ → ℝ) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    L - K ≤ ∫ u in Set.Icc a (a + L), (1 - atomicTest N x g u) ^ 2 := by
  have h := sub_le_setIntegral_sq hg hgsupp hw N x a hL
  have hK0 : 0 ≤ K := by
    by_contra h0
    push Not at h0
    have := mul_neg_of_neg_of_pos h0 (atomSpacing_pos hN)
    linarith
  have hNw : (N : ℝ) * w ≤ K := by
    calc (N : ℝ) * w ≤ N * (K * atomSpacing N) :=
          mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg N)
      _ = K * (N * atomSpacing N) := by ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left (natCast_mul_atomSpacing_le_one hN) hK0
      _ = K := mul_one K
  linarith

/-- **The families of the proved Hodge index are not exhaustive**: at the fixed fraction `c★` of
the spacing, every atomic test is at `L²`-distance at least `√(1 − c★)` from the indicator of a
unit interval. -/
theorem one_sub_fixedWidthRatio_le_setIntegral_sq (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) {N : ℕ} (hN : 1 ≤ N)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) (x : ℕ → ℝ) (a : ℝ) :
    1 - fixedWidthRatio ≤ ∫ u in Set.Icc a (a + 1), (1 - atomicTest N x g u) ^ 2 :=
  sub_le_setIntegral_sq_of_overlap hg hgsupp hw0 hN hw x a zero_le_one

/-- **Exhaustion needs unbounded overlap**: if an atomic test of overlap ratio at most `K`
approximates the indicator of an interval of length `L` to `L²`-error `ε`, then `K ≥ L − ε²`. -/
theorem le_overlap_of_setIntegral_sq_le (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) {N : ℕ} (hN : 1 ≤ N) {K : ℝ}
    (hK : w ≤ K * atomSpacing N) (x : ℕ → ℝ) (a : ℝ) {L ε : ℝ} (hL : 0 ≤ L)
    (happrox : ∫ u in Set.Icc a (a + L), (1 - atomicTest N x g u) ^ 2 ≤ ε ^ 2) :
    L - ε ^ 2 ≤ K := by
  have := sub_le_setIntegral_sq_of_overlap hg hgsupp hw hN hK x a hL
  linarith

/-! ### Adapted families -/

/-- The **adapted atomic test** `Σ_{n ≤ N} x_n G_n(u − log n)`, one bump per atom. -/
def adaptedTest (N : ℕ) (x : ℕ → ℝ) (G : ℕ → ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, x n * G n (u - Real.log n)

/-- The cover `⋃_{1 ≤ n ≤ N} [log n, log n + w_n]` of an adapted family. -/
def adaptedCover (N : ℕ) (W : ℕ → ℝ) : Set ℝ :=
  ⋃ n ∈ Finset.Icc 1 N, Set.Icc (Real.log n) (Real.log n + W n)

theorem adaptedTest_eq_zero_of_not_mem {G : ℕ → ℝ → ℝ} {W : ℕ → ℝ}
    (hG : ∀ n u, u ∉ Set.Icc 0 (W n) → G n u = 0) (N : ℕ) (x : ℕ → ℝ) {u : ℝ}
    (hu : u ∉ adaptedCover N W) : adaptedTest N x G u = 0 := by
  unfold adaptedTest
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn' : u ∉ Set.Icc (Real.log n) (Real.log n + W n) := fun h =>
    hu (Set.mem_biUnion hn h)
  rw [hG n _ fun h => hn' ⟨by linarith [h.1], by linarith [h.2]⟩, mul_zero]

/-- The local spacings telescope: `Σ_{n ≤ N} log(1 + 1/n) = log(N + 1)`. -/
theorem sum_log_one_add_inv (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (1 + 1 / (n : ℝ)) = Real.log (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    have h1 : (0 : ℝ) < N + 1 := by positivity
    rw [← Real.log_mul h1.ne' (by positivity)]
    congr 1
    field_simp

/-- **An adapted family of ratio `c` covers measure at most `c log(N + 1)`.** -/
theorem measureReal_adaptedCover_le {W : ℕ → ℝ} {c : ℝ} (hW0 : ∀ n, 0 ≤ W n)
    (hW : ∀ n, 1 ≤ n → W n ≤ c * Real.log (1 + 1 / (n : ℝ))) (N : ℕ) :
    volume.real (adaptedCover N W) ≤ c * Real.log (N + 1) := by
  calc volume.real (adaptedCover N W)
      ≤ ∑ n ∈ Finset.Icc 1 N, volume.real (Set.Icc (Real.log n) (Real.log n + W n)) :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, W n := Finset.sum_congr rfl fun n _ => by
        rw [Real.volume_real_Icc_of_le (by linarith [hW0 n])]; ring
    _ ≤ ∑ n ∈ Finset.Icc 1 N, c * Real.log (1 + 1 / (n : ℝ)) :=
        Finset.sum_le_sum fun n hn => hW n (Finset.mem_Icc.mp hn).1
    _ = c * Real.log (N + 1) := by rw [← Finset.mul_sum, sum_log_one_add_inv]

/-- **The cells of an adapted family below the Nyquist rate are disjoint**: for `c < 1` the cell
of the atom `n` ends before the atom `n + 1`. -/
theorem adaptedCell_disjoint {c : ℝ} (hc : c < 1) {n : ℕ} (hn : 1 ≤ n) :
    Real.log n + c * Real.log (1 + 1 / (n : ℝ)) < Real.log (n + 1 : ℕ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : (0 : ℝ) < 1 / n := by positivity
  have hl : 0 < Real.log (1 + 1 / (n : ℝ)) := Real.log_pos (by linarith)
  have he : Real.log (n + 1 : ℕ) = Real.log n + Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [he]
  nlinarith

/-- **An adapted family covers only the fraction `c` of its range**:
`∫_{[0, log(N+1)]} (1 − f)² ≥ (1 − c) log(N + 1)`. -/
theorem sub_le_setIntegral_sq_adapted {G : ℕ → ℝ → ℝ} {W : ℕ → ℝ} {c : ℝ}
    (hGc : ∀ n, Continuous (G n)) (hG : ∀ n u, u ∉ Set.Icc 0 (W n) → G n u = 0)
    (hW0 : ∀ n, 0 ≤ W n) (hW : ∀ n, 1 ≤ n → W n ≤ c * Real.log (1 + 1 / (n : ℝ)))
    (N : ℕ) (x : ℕ → ℝ) :
    (1 - c) * Real.log (N + 1) ≤
      ∫ u in Set.Icc 0 (0 + Real.log (N + 1)), (1 - adaptedTest N x G u) ^ 2 := by
  set L := Real.log ((N : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  set I := Set.Icc (0 : ℝ) (0 + L)
  set S := adaptedCover N W
  have hcont : Continuous fun u => (1 - adaptedTest N x G u) ^ 2 := by
    unfold adaptedTest
    exact (continuous_const.sub (continuous_finsetSum _ fun n _ =>
      continuous_const.mul ((hGc n).comp (continuous_id.sub continuous_const)))).pow 2
  have hint : IntegrableOn (fun u => (1 - adaptedTest N x G u) ^ 2) I :=
    hcont.continuousOn.integrableOn_Icc
  have hmS : MeasurableSet S := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc
  have hoff : ∫ u in I \ S, (1 - adaptedTest N x G u) ^ 2 = volume.real (I \ S) := by
    rw [setIntegral_congr_fun (measurableSet_Icc.diff hmS) (g := fun _ => (1 : ℝ)) fun u hu => by
        simp only [adaptedTest_eq_zero_of_not_mem hG N x hu.2, sub_zero, one_pow],
      setIntegral_const, smul_eq_mul, mul_one]
  have hmono : ∫ u in I \ S, (1 - adaptedTest N x G u) ^ 2 ≤
      ∫ u in I, (1 - adaptedTest N x G u) ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun u => sq_nonneg _)
      (Filter.Eventually.of_forall Set.sdiff_subset)
  have hS : volume S ≠ ⊤ := by
    show volume (⋃ n ∈ Finset.Icc 1 N, Set.Icc (Real.log n) (Real.log n + W n)) ≠ ⊤
    refine ne_of_lt ((measure_biUnion_finset_le _ _).trans_lt ?_)
    exact ENNReal.sum_lt_top.mpr fun n _ => by simp [Real.volume_Icc]
  have h1 := le_measureReal_sdiff (μ := volume) (s₁ := I) (s₂ := S) hS
  rw [Real.volume_real_Icc_of_le (by linarith)] at h1
  have h2 := measureReal_adaptedCover_le hW0 hW N
  have : (1 - c) * L = L - c * L := by ring
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
