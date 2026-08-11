import Mathlib

/-!
# Sharp boundary countermodels for the capacity-polar horizon

Two two-dimensional families delimit the capacity-polar horizon law.

* `momentGram` is the moment family `Q_t = diag(1,0) + ∫₀ᵗ (1,s)ᵀ(1,s) ds`.  It increases in `t`,
  so along a sequence `t_n ↓ 0` the direct metrics `G_{t_n} = Q_{t_n}⁻¹` increase.  The reduced
  quadratic form on the finite-cost direction converges, `⟪G_t e₀, e₀⟫ = 4/(4+t) → 1`, while the
  uncompressed vector diverges, `(G_t e₀)₁ = -6/(t(4+t)) → -∞`.  No operator convergence is
  available.

* `rotatingGram` is the family `Q_c = !![1, √(c(1-c)); √(c(1-c)), c]`.  Every member is positive
  definite with determinant `c²`, and `Q_c → diag(1,0)` as `c → 0`, but the family is not Loewner
  ordered and `⟪Q_c⁻¹ e₀, e₀⟫ = 1/c → ∞` although `e₀` lies in the limiting range.  Monotonicity
  is therefore essential.
-/

open Filter Matrix
open scoped Topology ENNReal NNReal

namespace HTGeometry.ConstraintMotiveRelativity

/-! ## The moment family: no vector convergence -/

/-- The moment cometric `Q_t = diag(1,0) + ∫₀ᵗ (1,s)ᵀ(1,s) ds`. -/
noncomputable def momentGram (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + t, t ^ 2 / 2; t ^ 2 / 2, t ^ 3 / 3]

/-- The direct metric of the moment family. -/
noncomputable def momentMetric (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (12 / (t ^ 3 * (4 + t))) • !![t ^ 3 / 3, -(t ^ 2 / 2); -(t ^ 2 / 2), 1 + t]

theorem momentMetric_mul_momentGram {t : ℝ} (ht : 0 < t) :
    momentMetric t * momentGram t = 1 := by
  have ht3 : t ^ 3 ≠ 0 := by positivity
  have ht4 : (4 : ℝ) + t ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentMetric, momentGram, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> try ring

/-- **The moment cometric increases.**  This is the integral form
`Q_t - Q_s = ∫ₛᵗ (1,u)ᵀ(1,u) du`. -/
theorem momentGram_mono {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (momentGram s *ᵥ x) ≤ x ⬝ᵥ (momentGram t *ᵥ x) := by
  have hexp : ∀ r : ℝ, x ⬝ᵥ (momentGram r *ᵥ x)
      = (1 + r) * x 0 ^ 2 + r ^ 2 * (x 0 * x 1) + r ^ 3 / 3 * x 1 ^ 2 := by
    intro r
    simp [momentGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hexp, hexp]
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_refl _
  · have hA : 0 < t - s := by linarith
    set a := x 0
    set b := x 1
    have key : 4 * (t - s) *
        ((t - s) * a ^ 2 + (t ^ 2 - s ^ 2) * (a * b) + (t ^ 3 - s ^ 3) / 3 * b ^ 2)
        = (2 * (t - s) * a + (t ^ 2 - s ^ 2) * b) ^ 2 + (t - s) ^ 4 / 3 * b ^ 2 := by
      ring
    have hrhs : 0 ≤ (2 * (t - s) * a + (t ^ 2 - s ^ 2) * b) ^ 2 + (t - s) ^ 4 / 3 * b ^ 2 := by
      positivity
    have hprod : 0 ≤ 4 * (t - s) *
        ((t - s) * a ^ 2 + (t ^ 2 - s ^ 2) * (a * b) + (t ^ 3 - s ^ 3) / 3 * b ^ 2) := by
      rw [key]; exact hrhs
    have hpos : (0 : ℝ) < 4 * (t - s) := by linarith
    have hform : 0 ≤ (t - s) * a ^ 2 + (t ^ 2 - s ^ 2) * (a * b) + (t ^ 3 - s ^ 3) / 3 * b ^ 2 :=
      nonneg_of_mul_nonneg_right hprod hpos
    linarith

/-- The reduced capacity of the first coordinate. -/
theorem momentMetric_form {t : ℝ} (ht : 0 < t) :
    ![(1 : ℝ), 0] ⬝ᵥ (momentMetric t *ᵥ ![1, 0]) = 4 / (4 + t) := by
  have ht3 : t ^ 3 ≠ 0 := by positivity
  have ht4 : (4 : ℝ) + t ≠ 0 := by linarith
  simp [momentMetric, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  field_simp
  try ring

/-- The uncompressed second coordinate of the lifted vector. -/
theorem momentMetric_apply_snd {t : ℝ} (ht : 0 < t) :
    (momentMetric t *ᵥ ![(1 : ℝ), 0]) 1 = -(6 / (t * (4 + t))) := by
  have ht3 : t ^ 3 ≠ 0 := by positivity
  have ht4 : (4 : ℝ) + t ≠ 0 := by linarith
  have ht0 : t ≠ 0 := ne_of_gt ht
  simp [momentMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  try ring

/-- The chart parameter sequence. -/
noncomputable def momentParam (n : ℕ) : ℝ := 1 / (n + 1)

theorem momentParam_pos (n : ℕ) : 0 < momentParam n := by
  rw [momentParam]; positivity

theorem momentParam_le_one (n : ℕ) : momentParam n ≤ 1 := by
  rw [momentParam, div_le_one (by positivity)]
  try linarith [Nat.cast_nonneg (α := ℝ) n]

theorem momentParam_antitone : Antitone momentParam := by
  intro m n hmn
  rw [momentParam, momentParam]
  gcongr
  try exact_mod_cast hmn

theorem tendsto_momentParam : Tendsto momentParam atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat.congr fun _ => rfl

/-- **The reduced quadratic form converges.** -/
theorem tendsto_momentMetric_form :
    Tendsto (fun n => ![(1 : ℝ), 0] ⬝ᵥ (momentMetric (momentParam n) *ᵥ ![1, 0])) atTop
      (𝓝 1) := by
  have hform : ∀ n, ![(1 : ℝ), 0] ⬝ᵥ (momentMetric (momentParam n) *ᵥ ![1, 0])
      = 4 / (4 + momentParam n) := fun n => momentMetric_form (momentParam_pos n)
  have hlim : Tendsto (fun n => 4 / (4 + momentParam n)) atTop (𝓝 (4 / (4 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_momentParam) (by norm_num)
  rw [show (4 : ℝ) / (4 + 0) = 1 by norm_num] at hlim
  exact hlim.congr fun n => (hform n).symm

/-- **The uncompressed vectors do not converge.**  Their second coordinate is unbounded below. -/
theorem not_bddBelow_momentMetric_snd :
    ¬ BddBelow (Set.range fun n => (momentMetric (momentParam n) *ᵥ ![(1 : ℝ), 0]) 1) := by
  rintro ⟨M, hM⟩
  have hval : ∀ n, (momentMetric (momentParam n) *ᵥ ![(1 : ℝ), 0]) 1
      = -(6 / (momentParam n * (4 + momentParam n))) :=
    fun n => momentMetric_apply_snd (momentParam_pos n)
  obtain ⟨n, hn⟩ := exists_nat_gt (-M)
  have hp := momentParam_pos n
  have hle := momentParam_le_one n
  set A : ℝ := momentParam n * (4 + momentParam n) with hA
  have hApos : 0 < A := by rw [hA]; nlinarith
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : ((n : ℝ) + 1) * A ≤ 5 := by
    have hval2 : momentParam n * ((n : ℝ) + 1) = 1 := by
      rw [momentParam]; try field_simp
    have : ((n : ℝ) + 1) * A = (4 + momentParam n) * (momentParam n * ((n : ℝ) + 1)) := by
      rw [hA]; ring
    rw [this, hval2, mul_one]
    linarith
  have hbound := hM (Set.mem_range_self n)
  rw [hval n, ← hA] at hbound
  have h1 : 6 / A ≤ -M := by linarith
  have hid : 6 / A - 6 * ((n : ℝ) + 1) / 5 = 6 * (5 - ((n : ℝ) + 1) * A) / (5 * A) := by
    field_simp; try ring
  have hnn : 0 ≤ 6 * (5 - ((n : ℝ) + 1) * A) / (5 * A) := by
    apply div_nonneg
    · linarith
    · positivity
  linarith

/-! ## The rotating family: monotonicity is essential -/

/-- The off-diagonal entry of the rotating cometric. -/
noncomputable def rotatingOff (c : ℝ) : ℝ := Real.sqrt (c * (1 - c))

/-- The rotating cometric `Q_c`. -/
noncomputable def rotatingGram (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, rotatingOff c; rotatingOff c, c]

/-- Its inverse. -/
noncomputable def rotatingMetric (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / c ^ 2) • !![c, -rotatingOff c; -rotatingOff c, 1]

theorem rotatingOff_sq {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    rotatingOff c ^ 2 = c - c ^ 2 := by
  rw [rotatingOff, Real.sq_sqrt (by nlinarith)]
  ring

theorem rotatingMetric_mul_rotatingGram {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    rotatingMetric c * rotatingGram c = 1 := by
  have hs := rotatingOff_sq h0 h1
  have hc : c ≠ 0 := ne_of_gt h0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotatingMetric, rotatingGram, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> try nlinarith [hs]

/-- **The rotating direct capacity blows up.** -/
theorem rotatingMetric_form {c : ℝ} (h0 : 0 < c) (_h1 : c < 1) :
    ![(1 : ℝ), 0] ⬝ᵥ (rotatingMetric c *ᵥ ![1, 0]) = 1 / c := by
  have hc : c ≠ 0 := ne_of_gt h0
  simp [rotatingMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  try ring

/-- Every member of the rotating family is positive definite. -/
theorem rotatingGram_posDef {c : ℝ} (h0 : 0 < c) (h1 : c < 1) (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (rotatingGram c *ᵥ x) := by
  have hs := rotatingOff_sq h0 h1
  have hexp : x ⬝ᵥ (rotatingGram c *ᵥ x)
      = x 0 ^ 2 + 2 * rotatingOff c * (x 0 * x 1) + c * x 1 ^ 2 := by
    simp [rotatingGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hid : x 0 ^ 2 + 2 * rotatingOff c * (x 0 * x 1) + c * x 1 ^ 2
      = (x 0 + rotatingOff c * x 1) ^ 2 + c ^ 2 * x 1 ^ 2 := by
    linear_combination (-(x 1 ^ 2)) * hs
  rw [hexp, hid]
  rcases eq_or_ne (x 1) 0 with hb | hb
  · have ha : x 0 ≠ 0 := by
      intro h0'
      exact hx (funext fun i => by fin_cases i <;> simp [h0', hb])
    have hsq : 0 < x 0 ^ 2 := by
      rcases ha.lt_or_gt with h | h <;> nlinarith
    rw [hb]
    simpa using hsq
  · have hpos : 0 < c ^ 2 * x 1 ^ 2 := by
      have : 0 < x 1 ^ 2 := by rcases hb.lt_or_gt with h | h <;> nlinarith
      positivity
    nlinarith [sq_nonneg (x 0 + rotatingOff c * x 1)]

/-- The rotating cometrics converge entrywise to the degenerate limit. -/
theorem tendsto_rotatingGram_entry {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) (i j : Fin 2) :
    Tendsto (fun n => rotatingGram (c n) i j) atTop
      (𝓝 ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j)) := by
  have hoff : Tendsto (fun n => rotatingOff (c n)) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n => c n * (1 - c n)) atTop (𝓝 0) := by
      simpa using hc.mul (tendsto_const_nhds.sub hc)
    have hsq := (Real.continuous_sqrt.tendsto 0).comp hprod
    simpa [rotatingOff, Function.comp_def] using hsq
  fin_cases i <;> fin_cases j <;> simp [rotatingGram]
  · exact hoff
  · exact hoff
  · exact hc

/-- **Blow-up of the rotating inverse capacity.** -/
theorem tendsto_rotatingMetric_form_atTop {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hpos : ∀ n, 0 < c n) (hlt : ∀ n, c n < 1) :
    Tendsto (fun n => ![(1 : ℝ), 0] ⬝ᵥ (rotatingMetric (c n) *ᵥ ![1, 0])) atTop atTop := by
  have hval : ∀ n, ![(1 : ℝ), 0] ⬝ᵥ (rotatingMetric (c n) *ᵥ ![1, 0]) = 1 / c n :=
    fun n => rotatingMetric_form (hpos n) (hlt n)
  have hwithin : Tendsto c atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc
      (Filter.Eventually.of_forall fun n => hpos n)
  have hinv : Tendsto (fun n => (c n)⁻¹) atTop atTop := hwithin.inv_tendsto_nhdsGT_zero
  have hdiv : Tendsto (fun n => 1 / c n) atTop atTop :=
    hinv.congr fun n => (one_div (c n)).symm
  exact hdiv.congr fun n => (hval n).symm


/-! ## The diagonal family: finite dimension is essential -/

section Diagonal

/-- Finite sums commute with monotone suprema in `ℝ≥0∞`. -/
theorem finsetSum_iSup_of_monotone {f : ℕ → ℕ → ℝ≥0∞} (hf : ∀ k, Monotone fun n => f n k)
    (s : Finset ℕ) : ∑ k ∈ s, (⨆ n, f n k) = ⨆ n, ∑ k ∈ s, f n k := by
  classical
  refine le_antisymm ?_ (iSup_le fun n => Finset.sum_le_sum fun k _ => le_iSup (fun m => f m k) n)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (add_le_add le_rfl ih) ?_
      refine ENNReal.iSup_add_iSup_le fun i j => le_iSup_of_le (max i j) ?_
      rw [Finset.sum_insert ha]
      exact add_le_add (hf a (le_max_left i j))
        (Finset.sum_le_sum fun k _ => hf k (le_max_right i j))

/-- Monotone suprema commute with countable sums in `ℝ≥0∞`. -/
theorem tsum_iSup_of_monotone {f : ℕ → ℕ → ℝ≥0∞} (hf : ∀ k, Monotone fun n => f n k) :
    ∑' k, (⨆ n, f n k) = ⨆ n, ∑' k, f n k := by
  refine le_antisymm ?_ (iSup_le fun n => ENNReal.tsum_le_tsum fun k => le_iSup (fun m => f m k) n)
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [finsetSum_iSup_of_monotone hf s]
  exact iSup_le fun n => le_iSup_of_le n (ENNReal.sum_le_tsum s)

/-- The diagonal weights `k ↦ (k+1)⁻²` of the model cometric. -/
noncomputable def diagWeight (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ 2)⁻¹

theorem diagWeight_pos (k : ℕ) : 0 < diagWeight k := by
  rw [diagWeight]; positivity

theorem inv_succ_antitone {m n : ℕ} (hmn : m ≤ n) : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := by
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  gcongr

/-- The regularized direct-capacity term of coordinate `k` at stage `n`. -/
noncomputable def diagEnergyTerm (x : ℕ → ℝ) (n k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (x k ^ 2 / (diagWeight k + ((n : ℝ) + 1)⁻¹))

/-- The limiting term `(k+1)² |x_k|²`. -/
noncomputable def diagLimitTerm (x : ℕ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((k : ℝ) + 1) ^ 2 * x k ^ 2)

/-- The regularized direct capacity of the diagonal chart. -/
noncomputable def diagEnergy (x : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ := ∑' k, diagEnergyTerm x n k

/-- The limiting energy `∑ (k+1)² |x_k|²`. -/
noncomputable def diagLimitEnergy (x : ℕ → ℝ) : ℝ≥0∞ := ∑' k, diagLimitTerm x k

theorem diagEnergyTerm_monotone (x : ℕ → ℝ) (k : ℕ) :
    Monotone fun n => diagEnergyTerm x n k := by
  intro m n hmn
  refine ENNReal.ofReal_le_ofReal ?_
  have hw := diagWeight_pos k
  have hm : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
  have hle := inv_succ_antitone hmn
  gcongr
  try linarith

theorem iSup_diagEnergyTerm (x : ℕ → ℝ) (k : ℕ) :
    (⨆ n, diagEnergyTerm x n k) = diagLimitTerm x k := by
  have hw := diagWeight_pos k
  have hval : x k ^ 2 / diagWeight k = ((k : ℝ) + 1) ^ 2 * x k ^ 2 := by
    rw [diagWeight]; field_simp
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => one_div _
  have hden : Tendsto (fun n : ℕ => diagWeight k + ((n : ℝ) + 1)⁻¹) atTop (𝓝 (diagWeight k)) := by
    simpa using tendsto_const_nhds.add hinv
  have htendR : Tendsto (fun n : ℕ => x k ^ 2 / (diagWeight k + ((n : ℝ) + 1)⁻¹)) atTop
      (𝓝 (x k ^ 2 / diagWeight k)) := tendsto_const_nhds.div hden (ne_of_gt hw)
  have htend : Tendsto (fun n => diagEnergyTerm x n k) atTop (𝓝 (diagLimitTerm x k)) := by
    rw [diagLimitTerm, ← hval]
    exact (ENNReal.continuous_ofReal.tendsto _).comp htendR
  exact tendsto_nhds_unique (tendsto_atTop_iSup (diagEnergyTerm_monotone x k)) htend

/-- **Monotone convergence of the regularized diagonal capacities.**  This is the domain
computation of the infinite-dimensional countermodel. -/
theorem iSup_diagEnergy (x : ℕ → ℝ) : (⨆ n, diagEnergy x n) = diagLimitEnergy x := by
  have h1 : (⨆ n, diagEnergy x n) = ⨆ n, ∑' k, diagEnergyTerm x n k := rfl
  have h2 : diagLimitEnergy x = ∑' k, diagLimitTerm x k := rfl
  rw [h1, h2, ← tsum_iSup_of_monotone (diagEnergyTerm_monotone x)]
  exact tsum_congr fun k => iSup_diagEnergyTerm x k

/-- The witness sequence `x_k = (k+1)⁻²`. -/
noncomputable def diagWitness (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ 2)⁻¹

theorem summable_inv_sq : Summable fun k : ℕ => ((((k : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 h
  refine h2.congr fun k => ?_
  push_cast
  rw [one_div]

/-- **The witness has finite limiting energy.** -/
theorem diagLimitEnergy_diagWitness_ne_top : diagLimitEnergy diagWitness ≠ ⊤ := by
  have hterm : ∀ k, diagLimitTerm diagWitness k
      = ENNReal.ofReal ((((k : ℝ) + 1) ^ 2)⁻¹) := by
    intro k
    show ENNReal.ofReal (((k : ℝ) + 1) ^ 2 * diagWitness k ^ 2)
      = ENNReal.ofReal ((((k : ℝ) + 1) ^ 2)⁻¹)
    congr 1
    have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    rw [diagWitness]
    field_simp
  have hE : diagLimitEnergy diagWitness = ∑' k, diagLimitTerm diagWitness k := rfl
  rw [hE]
  simp only [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_inv_sq]
  exact ENNReal.ofReal_ne_top

/-- **The witness is not in the range of the limiting cometric.**  The only diagonal preimage is
the constant sequence `1`, which is not square summable.  In infinite dimensions bounded direct
capacity therefore does not force membership in the range of the limiting cometric. -/
theorem diagWitness_preimage_not_summable (y : ℕ → ℝ)
    (hy : ∀ k, diagWeight k * y k = diagWitness k) : ¬ Summable fun k => y k ^ 2 := by
  have hone : ∀ k, y k = 1 := by
    intro k
    have hk := hy k
    rw [diagWeight, diagWitness] at hk
    have hne : (((k : ℝ) + 1) ^ 2)⁻¹ ≠ 0 := by positivity
    field_simp at hk
    linarith
  intro hsum
  have hconst : Summable fun _ : ℕ => (1 : ℝ) := by
    refine hsum.congr fun k => ?_
    rw [hone k]; norm_num
  have h0 := hconst.tendsto_atTop_zero
  have h1 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h0
  exact one_ne_zero h1

end Diagonal

end HTGeometry.ConstraintMotiveRelativity
