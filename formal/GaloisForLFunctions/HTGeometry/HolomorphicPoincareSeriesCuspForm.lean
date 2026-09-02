import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeriesModularForm

/-!
# The Poincaré series of positive index is a cusp form

For `k ≥ 3` and `m ≥ 1` the Poincaré series `P_m` of weight `k` vanishes at the cusp.  Split the
sum over coprime pairs `(c, d)` according to whether `c = 0`.  The two terms with `c = 0` are
`(±1)^{-k} e(m(z + n))`, each of norm `exp(-2π m y)`.  For `c ≠ 0` the summand is dominated by
`|cz + d|^{-k} ≤ y^{-1/2} |cz + d|^{-(k - 1/2)}`, because `|cz + d| ≥ |c| y ≥ y`, and the
remaining exponent `k - 1/2 > 2` keeps the sum convergent uniformly on a vertical strip.  Hence
`‖P_m(z)‖ ≤ 2 exp(-2π m y) + C y^{-1/2}` on the strip `|x| ≤ 1, y ≥ 2`, and by translation
invariance for every `z` with `y ≥ 2`; both terms tend to zero as `y → ∞`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularForm Complex Matrix CongruenceSubgroup Set Filter Topology
open scoped MatrixGroups Real Manifold ModularForm

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The two summands with `c = 0` -/

/-- A coprime pair with first entry zero has second entry `±1`. -/
theorem gammaSet_snd_eq_of_fst_eq_zero (v : gammaSet 1 1 0) (h : v.1 0 = 0) :
    v.1 1 = 1 ∨ v.1 1 = -1 := by
  have hg := (gammaSet_one_mem_iff 1 v.1).mp v.2
  rw [h, Int.gcd_zero_left] at hg
  have := Int.natAbs_eq_iff.mp hg
  simpa using this

/-- A pair with first entry zero has sup norm one. -/
theorem norm_eq_one_of_fst_eq_zero (v : gammaSet 1 1 0) (h : v.1 0 = 0) : ‖v.1‖ = 1 := by
  rw [norm_eq_max_natAbs, h]
  rcases gammaSet_snd_eq_of_fst_eq_zero v h with h2 | h2 <;> simp [h2]

/-- The norm of a `c = 0` summand is at most `exp(-2π m y)`. -/
theorem norm_poincareSummand_le_exp_of_fst_eq_zero (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0)
    (h : v.1 0 = 0) (z : ℍ) :
    ‖poincareSummand k m v z‖ ≤ Real.exp (-(2 * π * m * z.im)) := by
  have hd : (v.1 1 : ℂ) = 1 ∨ (v.1 1 : ℂ) = -1 := by
    rcases gammaSet_snd_eq_of_fst_eq_zero v h with h1 | h1 <;> simp [h1]
  have hnormd : ‖(v.1 1 : ℂ)‖ = 1 := by
    rcases hd with h1 | h1 <;> simp [h1]
  have heis : ‖eisSummand k v.1 z‖ = 1 := by
    simp only [eisSummand, h, Int.cast_zero, zero_mul, zero_add, norm_zpow, hnormd, one_zpow]
  have him : (gammaSetMatrix v • z).im = z.im := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
      gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one, h]
    rcases hd with h1 | h1 <;> simp [h1]
  have hre : (2 * π * I * m * ((gammaSetMatrix v • z : ℍ) : ℂ)).re = -(2 * π * m * z.im) := by
    have : (2 * π * I * m * ((gammaSetMatrix v • z : ℍ) : ℂ))
        = ((2 * π * m : ℝ) : ℂ) * (I * ((gammaSetMatrix v • z : ℍ) : ℂ)) := by
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im, him]
    ring
  rw [poincareSummand, norm_mul, heis, one_mul, Complex.norm_exp, hre]

/-! ## The summands with `c ≠ 0` -/

/-- For `c ≠ 0` the linear factor satisfies `|cz + d| ≥ y`. -/
theorem im_le_norm_linear_of_fst_ne_zero (x : Fin 2 → ℤ) (h : x 0 ≠ 0) (z : ℍ) :
    z.im ≤ ‖(x 0 : ℂ) * z + x 1‖ := by
  have him : ((x 0 : ℂ) * z + x 1).im = x 0 * z.im := by
    simp [Complex.mul_im]
  have h1 : (1 : ℝ) ≤ |(x 0 : ℝ)| := by
    have := Int.one_le_abs h
    exact_mod_cast this
  calc z.im = 1 * z.im := (one_mul _).symm
    _ ≤ |(x 0 : ℝ)| * z.im := mul_le_mul_of_nonneg_right h1 z.im_pos.le
    _ = |((x 0 : ℂ) * z + x 1).im| := by rw [him, abs_mul, abs_of_pos z.im_pos]
    _ ≤ ‖(x 0 : ℂ) * z + x 1‖ := Complex.abs_im_le_norm _

/-- For `c ≠ 0` the summand is dominated by `y^{-1/2}` times the vertical-strip bound with the
exponent `k - 1/2`. -/
theorem norm_poincareSummand_le_of_fst_ne_zero {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (v : gammaSet 1 1 0)
    (h : v.1 0 ≠ 0) {A B : ℝ} (hB : 0 < B) {z : ℍ} (hz : z ∈ verticalStrip A B) :
    ‖poincareSummand k m v z‖ ≤ z.im ^ (-(1 / 2 : ℝ)) *
      (r ⟨⟨A, B⟩, hB⟩ ^ (-((k : ℝ) - 1 / 2)) * ‖v.1‖ ^ (-((k : ℝ) - 1 / 2))) := by
  refine (norm_poincareSummand_le k m v z).trans ?_
  have hle := im_le_norm_linear_of_fst_ne_zero v.1 h z
  have hpos : 0 < ‖(v.1 0 : ℂ) * z + v.1 1‖ := lt_of_lt_of_le z.im_pos hle
  have hsplit : ‖eisSummand k v.1 z‖ = ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-(1 / 2 : ℝ)) *
      ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-((k : ℝ) - 1 / 2)) := by
    rw [← Real.rpow_add hpos, eisSummand, norm_zpow, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have hk' : (0 : ℝ) ≤ (k : ℝ) - 1 / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine mul_le_mul ?_ (summand_bound_of_mem_verticalStrip hk' v.1 hB hz)
    (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg z.im_pos.le _)
  exact Real.rpow_le_rpow_of_nonpos z.im_pos hle (by norm_num)

/-! ## The uniform bound on a vertical strip -/

/-- The cusp majorant `2 exp(-2π m y) + y^{-1/2} · r^{-(k-1/2)} · Σ_x ‖x‖^{-(k-1/2)}`. -/
def poincareCuspBound (k : ℤ) (m : ℕ) (y : ℝ) : ℝ :=
  2 * Real.exp (-(2 * π * m * y)) + y ^ (-(1 / 2 : ℝ)) *
    (r ⟨⟨1, 2⟩, two_pos⟩ ^ (-((k : ℝ) - 1 / 2)) * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-((k : ℝ) - 1 / 2)))

/-- The pointwise majorant of the summands: `exp(-2π m y)` on the two pairs with `c = 0`, and the
strip bound of exponent `k - 1/2` scaled by `y^{-1/2}` everywhere. -/
def poincareSummandMajorant (k : ℤ) (m : ℕ) (z : ℍ) (v : gammaSet 1 1 0) : ℝ :=
  (if v.1 0 = 0 then Real.exp (-(2 * π * m * z.im)) else 0) +
    z.im ^ (-(1 / 2 : ℝ)) *
      (r ⟨⟨1, 2⟩, two_pos⟩ ^ (-((k : ℝ) - 1 / 2)) * ‖v.1‖ ^ (-((k : ℝ) - 1 / 2)))

theorem norm_poincareSummand_le_majorant {k : ℤ} (hk : 3 ≤ k) (m : ℕ) {z : ℍ}
    (hz : z ∈ verticalStrip 1 2) (v : gammaSet 1 1 0) :
    ‖poincareSummand k m v z‖ ≤ poincareSummandMajorant k m z v := by
  unfold poincareSummandMajorant
  by_cases h : v.1 0 = 0
  · rw [if_pos h]
    refine (norm_poincareSummand_le_exp_of_fst_eq_zero k m v h z).trans ?_
    have : 0 ≤ z.im ^ (-(1 / 2 : ℝ)) *
        (r ⟨⟨1, 2⟩, two_pos⟩ ^ (-((k : ℝ) - 1 / 2)) * ‖v.1‖ ^ (-((k : ℝ) - 1 / 2))) :=
      mul_nonneg (Real.rpow_nonneg z.im_pos.le _)
        (mul_nonneg (Real.rpow_nonneg (r_pos _).le _) (Real.rpow_nonneg (norm_nonneg _) _))
    linarith
  · rw [if_neg h, zero_add]
    exact norm_poincareSummand_le_of_fst_ne_zero hk m v h two_pos hz

/-- The indicator of the two pairs with `c = 0`, scaled by a constant, is summable. -/
theorem summable_ite_fst_eq_zero (E : ℝ) (hE : 0 ≤ E) :
    Summable fun v : gammaSet 1 1 0 => (if v.1 0 = 0 then E else 0) := by
  have hsum : Summable fun v : gammaSet 1 1 0 => ‖v.1‖ ^ (-(3 : ℝ)) :=
    (summable_one_div_norm_rpow (by norm_num)).subtype _
  refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) (hsum.mul_left E)
  · split_ifs
    · exact hE
    · exact le_rfl
  · split_ifs with h
    · rw [norm_eq_one_of_fst_eq_zero v h, Real.one_rpow, mul_one]
    · exact mul_nonneg hE (Real.rpow_nonneg (norm_nonneg _) _)

/-- There are at most two coprime pairs with `c = 0`, so the indicator sum is at most `2E`. -/
theorem tsum_ite_fst_eq_zero_le (E : ℝ) (hE : 0 ≤ E) :
    ∑' v : gammaSet 1 1 0, (if v.1 0 = 0 then E else 0) ≤ 2 * E := by
  refine (summable_ite_fst_eq_zero E hE).tsum_le_of_sum_le fun s => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hE
  have h2 : ((({1, -1} : Finset ℤ)).card : ℝ) = 2 := by
    rw [Finset.card_pair (by norm_num)]
    norm_num
  rw [← h2]
  refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun v : gammaSet 1 1 0 => v.1 1) ?_ ?_)
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact gammaSet_snd_eq_of_fst_eq_zero v hv.2
  · intro v hv w hw hvw
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [hv.2, hw.2]
    · simpa using hvw

theorem summable_poincareSummandMajorant {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    Summable (poincareSummandMajorant k m z) := by
  have hs : (2 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsum : Summable fun v : gammaSet 1 1 0 => ‖v.1‖ ^ (-((k : ℝ) - 1 / 2)) :=
    (summable_one_div_norm_rpow hs).subtype _
  exact (summable_ite_fst_eq_zero _ (Real.exp_pos _).le).add ((hsum.mul_left _).mul_left _)

/-- **The strip bound.** On `|x| ≤ 1, y ≥ 2` the Poincaré series is dominated by
`poincareCuspBound k m y`. -/
theorem norm_poincareSeries_le_of_mem_verticalStrip {k : ℤ} (hk : 3 ≤ k) (m : ℕ) {z : ℍ}
    (hz : z ∈ verticalStrip 1 2) : ‖poincareSeries k m z‖ ≤ poincareCuspBound k m z.im := by
  have hs : (2 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsum : Summable fun v : gammaSet 1 1 0 => ‖v.1‖ ^ (-((k : ℝ) - 1 / 2)) :=
    (summable_one_div_norm_rpow hs).subtype _
  have hE : 0 ≤ Real.exp (-(2 * π * m * z.im)) := (Real.exp_pos _).le
  have hmaj : ‖poincareSeries k m z‖ ≤ ∑' v, poincareSummandMajorant k m z v := by
    unfold poincareSeries
    refine (norm_tsum_le_tsum_norm (summable_norm_poincareSummand hk m z)).trans ?_
    exact (summable_norm_poincareSummand hk m z).tsum_le_tsum
      (norm_poincareSummand_le_majorant hk m hz) (summable_poincareSummandMajorant hk m z)
  refine hmaj.trans ?_
  unfold poincareSummandMajorant poincareCuspBound
  rw [Summable.tsum_add (summable_ite_fst_eq_zero _ hE) ((hsum.mul_left _).mul_left _),
    tsum_mul_left, tsum_mul_left]
  refine add_le_add (tsum_ite_fst_eq_zero_le _ hE) ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
    (Real.rpow_nonneg (r_pos _).le _)) (Real.rpow_nonneg z.im_pos.le _)
  exact Summable.tsum_subtype_le (fun x : Fin 2 → ℤ => ‖x‖ ^ (-((k : ℝ) - 1 / 2))) _
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) (summable_one_div_norm_rpow hs)

/-- The strip bound holds for every `z` with `y ≥ 2`, by translating into the strip. -/
theorem norm_poincareSeries_le_of_two_le_im {k : ℤ} (hk : 3 ≤ k) (m : ℕ) {z : ℍ}
    (hz : 2 ≤ z.im) : ‖poincareSeries k m z‖ ≤ poincareCuspBound k m z.im := by
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z Nat.one_pos
  have hstrip : ModularGroup.T ^ ((1 : ℕ) * n) • z ∈ verticalStrip 1 2 := by
    simpa using verticalStrip_anti_right ((1 : ℕ) : ℝ) hz hn
  have him : (ModularGroup.T ^ ((1 : ℕ) * n) • z).im = z.im := by
    rw [modular_T_zpow_smul, vadd_im]
  rw [← poincareSeriesSIFGamma_apply,
    ← SlashInvariantForm.T_zpow_width_invariant 1 k n (poincareSeriesSIFGamma k m) z,
    poincareSeriesSIFGamma_apply, ← him]
  exact norm_poincareSeries_le_of_mem_verticalStrip hk m hstrip

/-! ## Vanishing at the cusp -/

theorem tendsto_poincareCuspBound_atTop (k : ℤ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (poincareCuspBound k m) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => 2 * Real.exp (-(2 * π * m * y))) atTop (𝓝 0) := by
    have hpos : 0 < 2 * π * m := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hpos)).const_mul
      (2 : ℝ)
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) *
      (r ⟨⟨1, 2⟩, two_pos⟩ ^ (-((k : ℝ) - 1 / 2)) * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-((k : ℝ) - 1 / 2))))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).mul_const
      (r ⟨⟨1, 2⟩, two_pos⟩ ^ (-((k : ℝ) - 1 / 2)) * ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-((k : ℝ) - 1 / 2)))
  have := h1.add h2
  rw [add_zero] at this
  exact this

/-- **Cuspidality.** For `k ≥ 3` and `m ≥ 1` the Poincaré series vanishes at the cusp. -/
theorem isZeroAtImInfty_poincareSeries {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    IsZeroAtImInfty (poincareSeries k m) := by
  have hcomp : Tendsto (fun z : ℍ => poincareCuspBound k m z.im) atImInfty (𝓝 0) :=
    (tendsto_poincareCuspBound_atTop k hm).comp Filter.tendsto_comap
  show Tendsto (poincareSeries k m) atImInfty (𝓝 0)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hcomp)
  exact (atImInfty_mem _).mpr ⟨2, fun z hz => norm_poincareSeries_le_of_two_le_im hk m hz⟩

/-- **The Poincaré series of weight `k ≥ 3` and index `m ≥ 1` is a cusp form of level one.** -/
def poincareSeriesCF {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) : CuspForm 𝒮ℒ k where
  toFun := poincareSeries k m
  slash_action_eq' := (poincareSeriesSIF k m).slash_action_eq'
  holo' := poincareSeries_mdifferentiable hk m
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [poincareSeries_slash_apply k m γ]
    exact isZeroAtImInfty_poincareSeries hk hm

theorem poincareSeriesCF_apply {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) (z : ℍ) :
    poincareSeriesCF hk hm z = poincareSeries k m z := rfl

/-- The cusp form and the modular form packagings of `P_m` have the same underlying function. -/
theorem coe_poincareSeriesCF {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    (poincareSeriesCF hk hm : ℍ → ℂ) = poincareSeriesMF hk m := rfl

end

end GaloisForLFunctions.HTGeometry
