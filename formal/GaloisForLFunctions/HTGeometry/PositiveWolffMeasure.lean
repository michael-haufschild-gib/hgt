import Mathlib

/-!
# Positive point masses on an annulus with all positive moments zero

**Theorem** (`exists_positive_wolff_annulus`). For `0 ≤ r < R` there are a countable set `t` of
points of the open annulus `r < |z| < R` and positive weights `c` such that
* `Σ_{x∈t} c_x x^k = 0` for every `k ≥ 1`, and `Σ_{x∈t} c_x = π(R² − r²)`;
* the points accumulate at the outer circle: every `R' < R` is exceeded by some `|x|`, while
  `|x| < R` for all `x ∈ t`;
* if `r > 0`, also `Σ_{x∈t} c_x x^{−k} = 0` for every `k ≥ 1`.

**Proof.** The annulus `A` is invariant under the rotation `z ↦ e^{iπ/k} z`, which preserves Lebesgue
measure and multiplies `z^k` by `−1`; hence `∫_A z^k = 0`. A closed disc `D(a,ρ)` satisfies
`∫_D z^k = πρ² a^k`: translate to the origin, expand `(w + a)^k`, and kill every positive power of `w`
by the rotation argument on `D(0,ρ)`; for `ρ < |a|` the same holds for `z^{−k}` through the
expansion `(a+w)^{−k} = a^{−k} Σ_n C(n+k−1, k−1)(−w/a)^n`. By the Besicovitch covering theorem almost all of `A` is a
countable disjoint union of closed discs `D(x, ρ_x)` centred in `A` with
`ρ_x < min(R − |x|, |x| − r)/2`; summing the disc identity over them gives the moments, with weights
`c_x = πρ_x²`. If every centre had `|x| ≤ R'` with `r ≤ R' < R`, all discs would lie in `|z| ≤ (R+R')/2`
and miss the open annulus `(R+R')/2 < |z| < R`, which has positive measure.
-/

open MeasureTheory Metric Set Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

/-! ## Rotation kills positive moments on radial sets -/

/-- The rotation by `e^{iπ/k}`. -/
def halfTurnRoot (k : ℕ) : Circle := Circle.exp (Real.pi / k)

theorem halfTurnRoot_pow {k : ℕ} (hk : 1 ≤ k) : ((halfTurnRoot k : ℂ)) ^ k = -1 := by
  rw [halfTurnRoot, Circle.coe_exp, ← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have : (k : ℂ) * (((Real.pi / k : ℝ) : ℂ) * I) = Real.pi * I := by
    push_cast; field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- **Radial sets.** On a set defined by a condition on `|z|`, every positive power integrates to
zero. -/
theorem setIntegral_pow_radial_eq_zero (T : Set ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ z in (fun z : ℂ => ‖z‖) ⁻¹' T, z ^ k = 0 := by
  set u := halfTurnRoot k
  have hmp := (rotation u).measurePreserving
  have hemb : MeasurableEmbedding (rotation u) := (rotation u).toHomeomorph.measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb (fun z : ℂ => z ^ k) ((fun z : ℂ => ‖z‖) ⁻¹' T)
  have hpre : (rotation u) ⁻¹' ((fun z : ℂ => ‖z‖) ⁻¹' T) = (fun z : ℂ => ‖z‖) ⁻¹' T := by
    ext z
    simp only [mem_preimage, rotation_apply, norm_mul, Circle.norm_coe, one_mul]
  rw [hpre] at h1
  have hu : (u : ℂ) ^ k = -1 := halfTurnRoot_pow hk
  simp only [rotation_apply, mul_pow] at h1
  rw [integral_const_mul, hu] at h1
  have h2 : (2 : ℂ) * ∫ z in (fun z : ℂ => ‖z‖) ⁻¹' T, z ^ k = 0 := by linear_combination -h1
  simpa using h2

theorem closedBall_zero_eq_preimage (ρ : ℝ) :
    closedBall (0 : ℂ) ρ = (fun z : ℂ => ‖z‖) ⁻¹' Iic ρ := by
  ext z; simp [mem_closedBall, dist_zero_right]

/-- **Radial sets, inverse powers.** On a set defined by a condition on `|z|`, every negative power
integrates to zero. -/
theorem setIntegral_inv_pow_radial_eq_zero (T : Set ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ z in (fun z : ℂ => ‖z‖) ⁻¹' T, (z ^ k)⁻¹ = 0 := by
  set u := halfTurnRoot k
  have hmp := (rotation u).measurePreserving
  have hemb : MeasurableEmbedding (rotation u) := (rotation u).toHomeomorph.measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb (fun z : ℂ => (z ^ k)⁻¹) ((fun z : ℂ => ‖z‖) ⁻¹' T)
  have hpre : (rotation u) ⁻¹' ((fun z : ℂ => ‖z‖) ⁻¹' T) = (fun z : ℂ => ‖z‖) ⁻¹' T := by
    ext z
    simp only [mem_preimage, rotation_apply, norm_mul, Circle.norm_coe, one_mul]
  rw [hpre] at h1
  have hu : ((u : ℂ) ^ k)⁻¹ = -1 := by rw [halfTurnRoot_pow hk]; norm_num
  simp only [rotation_apply, mul_pow, mul_inv] at h1
  rw [integral_const_mul, hu] at h1
  have h2 : (2 : ℂ) * ∫ z in (fun z : ℂ => ‖z‖) ⁻¹' T, (z ^ k)⁻¹ = 0 := by linear_combination -h1
  simpa using h2

/-! ## The mean value identity on discs -/

theorem real_volume_closedBall {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℂ) :
    volume.real (closedBall a ρ) = Real.pi * ρ ^ 2 := by
  rw [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hρ]
  simp [mul_comm]

/-- **Discs.** `∫_{D(a,ρ)} z^k = πρ² a^k`. -/
theorem setIntegral_closedBall_pow (a : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) :
    ∫ z in closedBall a ρ, z ^ k = ((Real.pi * ρ ^ 2 : ℝ) : ℂ) * a ^ k := by
  have hmp := measurePreserving_add_left (volume : Measure ℂ) a
  have hemb : MeasurableEmbedding (fun w : ℂ => a + w) := (MeasurableEquiv.addLeft a).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb (fun z : ℂ => z ^ k) (closedBall a ρ)
  have hpre : (fun w : ℂ => a + w) ⁻¹' closedBall a ρ = closedBall 0 ρ := by
    ext w; simp [mem_closedBall, dist_eq_norm]
  rw [hpre] at h1
  rw [← h1]
  have hexp : ∀ w : ℂ, (a + w) ^ k = ∑ m ∈ Finset.range (k + 1), w ^ m * a ^ (k - m) * (k.choose m) := by
    intro w; rw [add_comm]; exact add_pow w a k
  simp_rw [hexp]
  rw [integral_finsetSum]
  · rw [Finset.sum_range_succ']
    have hzero : ∀ m ∈ Finset.range k,
        ∫ w in closedBall (0 : ℂ) ρ, w ^ (m + 1) * a ^ (k - (m + 1)) * (k.choose (m + 1) : ℂ) = 0 := by
      intro m _
      have : ∀ w : ℂ, w ^ (m + 1) * a ^ (k - (m + 1)) * (k.choose (m + 1) : ℂ) =
          (a ^ (k - (m + 1)) * (k.choose (m + 1) : ℂ)) * w ^ (m + 1) := fun w => by ring
      simp_rw [this]
      rw [integral_const_mul, closedBall_zero_eq_preimage, setIntegral_pow_radial_eq_zero _ (by omega),
        mul_zero]
    rw [Finset.sum_eq_zero hzero, zero_add]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [setIntegral_const, real_volume_closedBall hρ, Complex.real_smul]
  · intro m _
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_closedBall _ _)

/-- **Discs away from the origin, inverse powers.** For `ρ < |a|`, `∫_{D(a,ρ)} z^{−(m+1)} = πρ² a^{−(m+1)}`.
The expansion `(a + w)^{−(m+1)} = a^{−(m+1)} Σ_n C(n+m, m)(−w/a)^n` converges uniformly on `|w| ≤ ρ`, and
every positive power of `w` integrates to zero over `D(0, ρ)`. -/
theorem setIntegral_closedBall_inv_pow (a : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρa : ρ < ‖a‖) (m : ℕ) :
    ∫ z in closedBall a ρ, (z ^ (m + 1))⁻¹ = ((Real.pi * ρ ^ 2 : ℝ) : ℂ) * (a ^ (m + 1))⁻¹ := by
  have ha0 : 0 < ‖a‖ := lt_of_le_of_lt hρ hρa
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  have hmp := measurePreserving_add_left (volume : Measure ℂ) a
  have hemb : MeasurableEmbedding (fun w : ℂ => a + w) := (MeasurableEquiv.addLeft a).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb (fun z : ℂ => (z ^ (m + 1))⁻¹) (closedBall a ρ)
  have hpre : (fun w : ℂ => a + w) ⁻¹' closedBall a ρ = closedBall 0 ρ := by
    ext w; simp [mem_closedBall, dist_eq_norm]
  rw [hpre] at h1
  rw [← h1]
  set μ := (volume : Measure ℂ).restrict (closedBall 0 ρ) with hμ
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  set q : ℝ := ρ / ‖a‖ with hq
  have hq0 : 0 ≤ q := div_nonneg hρ ha0.le
  have hq1 : q < 1 := (div_lt_one ha0).mpr hρa
  have hqs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) m
    (r := q) (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  set F : ℕ → ℂ → ℂ := fun n w => (a ^ (m + 1))⁻¹ * (((n + m).choose m : ℂ) * (-w / a) ^ n) with hF
  set bound : ℕ → ℂ → ℝ := fun n _ => ‖a ^ (m + 1)‖⁻¹ * (((n + m).choose m : ℝ) * q ^ n) with hbound
  have hrw : ∀ w ∈ closedBall (0 : ℂ) ρ, ‖-w / a‖ ≤ q := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    rw [norm_div, norm_neg, hq]
    exact div_le_div_of_nonneg_right hw ha0.le
  have hpt : ∀ w ∈ closedBall (0 : ℂ) ρ, HasSum (fun n => F n w) (((a + w) ^ (m + 1))⁻¹) := by
    intro w hw
    have hr1 : ‖-w / a‖ < 1 := lt_of_le_of_lt (hrw w hw) hq1
    have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) m hr1).mul_left (a ^ (m + 1))⁻¹
    have he : (a + w) = a * (1 - -w / a) := by field_simp; ring
    rw [he, mul_pow, mul_inv]
    rw [one_div] at hs
    exact hs
  have hmain := hasSum_integral_of_dominated_convergence (μ := μ) bound
    (fun n => by
      show AEStronglyMeasurable (fun w => (a ^ (m + 1))⁻¹ * (((n + m).choose m : ℂ) * (-w / a) ^ n)) μ
      exact (continuous_const.mul (continuous_const.mul
        ((continuous_neg.div_const a).pow n))).aestronglyMeasurable)
    (fun n => by
      rw [hμ, ae_restrict_iff' measurableSet_closedBall]
      refine Filter.Eventually.of_forall fun w hw => ?_
      have h := hrw w hw
      show ‖(a ^ (m + 1))⁻¹ * (((n + m).choose m : ℂ) * (-w / a) ^ n)‖ ≤
        ‖a ^ (m + 1)‖⁻¹ * (((n + m).choose m : ℝ) * q ^ n)
      rw [norm_mul, norm_inv, norm_mul, norm_pow, Complex.norm_natCast]
      gcongr
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h n)
    (Filter.Eventually.of_forall fun _ => (hqs.summable.mul_left _))
    (by
      show Integrable (fun _ : ℂ => ∑' n : ℕ, ‖a ^ (m + 1)‖⁻¹ * (((n + m).choose m : ℝ) * q ^ n)) μ
      exact integrable_const _)
    (by
      rw [hμ, ae_restrict_iff' measurableSet_closedBall]
      exact Filter.Eventually.of_forall fun w hw => hpt w hw)
  have hterm : ∀ n, ∫ w, F n w ∂μ =
      if n = 0 then ((Real.pi * ρ ^ 2 : ℝ) : ℂ) * (a ^ (m + 1))⁻¹ else 0 := by
    intro n
    have hFn : ∀ w, F n w = ((a ^ (m + 1))⁻¹ * ((n + m).choose m : ℂ) * (-1 / a) ^ n) * w ^ n := by
      intro w; simp only [hF]; rw [show -w / a = (-1 / a) * w by ring, mul_pow]; ring
    simp_rw [hFn]
    rw [integral_const_mul]
    split_ifs with hn
    · subst hn
      simp only [pow_zero, mul_one, Nat.zero_add, Nat.choose_self, Nat.cast_one]
      rw [hμ, setIntegral_const, real_volume_closedBall hρ, Complex.real_smul, mul_one, mul_comm]
    · rw [hμ, closedBall_zero_eq_preimage, setIntegral_pow_radial_eq_zero _ (Nat.one_le_iff_ne_zero.mpr hn),
        mul_zero]
  have hsingle : HasSum (fun n => ∫ w, F n w ∂μ) (((Real.pi * ρ ^ 2 : ℝ) : ℂ) * (a ^ (m + 1))⁻¹) := by
    simp_rw [hterm]
    exact hasSum_ite_eq 0 _
  exact hmain.unique hsingle

/-! ## The covering -/

/-- The open annulus `r < |z| < R`. -/
def annulus (r R : ℝ) : Set ℂ := (fun z : ℂ => ‖z‖) ⁻¹' Ioo r R

theorem measurableSet_annulus (r R : ℝ) : MeasurableSet (annulus r R) :=
  measurableSet_Ioo.preimage continuous_norm.measurable

/-- The admissible radius at a point of the annulus. -/
def admissibleRadius (r R : ℝ) (x : ℂ) : ℝ := min (R - ‖x‖) (‖x‖ - r) / 2

theorem closedBall_subset_annulus {r R : ℝ} {x : ℂ} {ρ : ℝ} (hx : x ∈ annulus r R)
    (hρ : ρ < admissibleRadius r R x) : closedBall x ρ ⊆ annulus r R := by
  intro z hz
  have hx' : r < ‖x‖ ∧ ‖x‖ < R := hx
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : ρ < (R - ‖x‖) / 2 := lt_of_lt_of_le hρ (by unfold admissibleRadius; gcongr; exact min_le_left _ _)
  have h2 : ρ < (‖x‖ - r) / 2 := lt_of_lt_of_le hρ (by unfold admissibleRadius; gcongr; exact min_le_right _ _)
  have t1 := norm_sub_norm_le z x
  have t2 := norm_sub_norm_le x z
  rw [norm_sub_rev] at t2
  show r < ‖z‖ ∧ ‖z‖ < R
  constructor <;> linarith

theorem norm_le_of_mem_closedBall_admissible {r R : ℝ} {x z : ℂ} {ρ : ℝ}
    (hρ : ρ < admissibleRadius r R x) (hz : z ∈ closedBall x ρ) : ‖z‖ ≤ (R + ‖x‖) / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : ρ < (R - ‖x‖) / 2 := lt_of_lt_of_le hρ (by unfold admissibleRadius; gcongr; exact min_le_left _ _)
  have t1 := norm_sub_norm_le z x
  linarith

/-- **Positive Wolff measure on an annulus.** -/
theorem exists_positive_wolff_annulus {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ∃ (t : Set ℂ) (c : ℂ → ℝ), t.Countable ∧ t ⊆ annulus r R ∧ (∀ x ∈ t, 0 < c x) ∧
      (∀ R' < R, ∃ x ∈ t, R' < ‖x‖) ∧
      HasSum (fun x : t => c x) (Real.pi * (R ^ 2 - r ^ 2)) ∧
      (∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * (x : ℂ) ^ k) 0) ∧
      (0 < r → ∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * ((x : ℂ) ^ k)⁻¹) 0) := by
  classical
  set A := annulus r R with hAdef
  have hAmeas : MeasurableSet A := measurableSet_annulus r R
  obtain ⟨t, ρ, htc, htA, hρ, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure ℂ) (fun _ => univ) A
      (fun x _ δ hδ => ⟨δ / 2, mem_univ _, by constructor <;> linarith⟩)
      (admissibleRadius r R) (fun x hx => by
        have hx' : r < ‖x‖ ∧ ‖x‖ < R := hx
        unfold admissibleRadius
        have := lt_min (by linarith : (0 : ℝ) < R - ‖x‖) (by linarith : (0 : ℝ) < ‖x‖ - r)
        linarith)
  haveI : Countable t := htc.to_subtype
  have hρpos : ∀ x ∈ t, 0 < ρ x := fun x hx => (hρ x hx).2.1
  have hρlt : ∀ x ∈ t, ρ x < admissibleRadius r R x := fun x hx => (hρ x hx).2.2
  set U := ⋃ x ∈ t, closedBall x (ρ x) with hUdef
  have hUiU : U = ⋃ i : t, closedBall (i : ℂ) (ρ i) := biUnion_eq_iUnion _ _
  have hUA : U ⊆ A := iUnion₂_subset fun x hx => closedBall_subset_annulus (htA hx) (hρlt x hx)
  have hUae : U =ᵐ[volume] A := by
    rw [ae_eq_set, sdiff_eq_empty.mpr hUA, measure_empty]
    exact ⟨rfl, hnull⟩
  have hpd : Pairwise (Function.onFun Disjoint fun i : t => closedBall (i : ℂ) (ρ i)) :=
    fun i j hij => hdisj i.2 j.2 (Subtype.coe_injective.ne hij)
  have hAsub : A ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : r < ‖z‖ ∧ ‖z‖ < R := hz
    rw [mem_closedBall, dist_zero_right]; exact hz'.2.le
  have hint : ∀ k : ℕ, IntegrableOn (fun z : ℂ => z ^ k) U volume := fun k =>
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      (hUA.trans hAsub)
  have hsum : ∀ k : ℕ, HasSum (fun i : t => ((Real.pi * ρ i ^ 2 : ℝ) : ℂ) * (i : ℂ) ^ k)
      (∫ z in A, z ^ k) := by
    intro k
    have h := hasSum_integral_iUnion (μ := volume) (f := fun z : ℂ => z ^ k)
      (fun i : t => measurableSet_closedBall) hpd (by rw [← hUiU]; exact hint k)
    rw [← hUiU, setIntegral_congr_set hUae] at h
    have hf : (fun i : t => ∫ z in closedBall (i : ℂ) (ρ i), z ^ k) =
        fun i : t => ((Real.pi * ρ i ^ 2 : ℝ) : ℂ) * (i : ℂ) ^ k :=
      funext fun i => setIntegral_closedBall_pow _ (hρpos i i.2).le k
    rw [hf] at h
    exact h
  have hUmeas : MeasurableSet U := MeasurableSet.biUnion htc fun _ _ => measurableSet_closedBall
  have hUfin : volume U < ⊤ :=
    lt_of_le_of_lt (measure_mono (hUA.trans hAsub)) measure_closedBall_lt_top
  have hsumInv : 0 < r → ∀ k : ℕ, 1 ≤ k →
      HasSum (fun i : t => ((Real.pi * ρ i ^ 2 : ℝ) : ℂ) * ((i : ℂ) ^ k)⁻¹) (∫ z in A, (z ^ k)⁻¹) := by
    intro hr0 k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hintU : IntegrableOn (fun z : ℂ => (z ^ (m + 1))⁻¹) U volume := by
      refine IntegrableOn.of_bound hUfin
        ((continuous_id.pow (m + 1)).measurable.inv.aestronglyMeasurable) ((r ^ (m + 1))⁻¹) ?_
      rw [ae_restrict_iff' hUmeas]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hzA : r < ‖z‖ ∧ ‖z‖ < R := hUA hz
      rw [norm_inv, norm_pow]
      exact inv_anti₀ (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hzA.1.le _)
    have h := hasSum_integral_iUnion (μ := volume) (f := fun z : ℂ => (z ^ (m + 1))⁻¹)
      (fun i : t => measurableSet_closedBall) hpd (by rw [← hUiU]; exact hintU)
    rw [← hUiU, setIntegral_congr_set hUae] at h
    have hf : (fun i : t => ∫ z in closedBall (i : ℂ) (ρ i), (z ^ (m + 1))⁻¹) =
        fun i : t => ((Real.pi * ρ i ^ 2 : ℝ) : ℂ) * ((i : ℂ) ^ (m + 1))⁻¹ := by
      funext i
      have hiA : r < ‖(i : ℂ)‖ ∧ ‖(i : ℂ)‖ < R := htA i.2
      have hlt := hρlt i i.2
      have hρi : ρ i < ‖(i : ℂ)‖ := by
        have : admissibleRadius r R i ≤ (‖(i : ℂ)‖ - r) / 2 := by
          unfold admissibleRadius; gcongr; exact min_le_right _ _
        linarith
      exact setIntegral_closedBall_inv_pow _ (hρpos i i.2).le hρi m
    rw [hf] at h
    exact h
  refine ⟨t, fun x => Real.pi * ρ x ^ 2, htc, htA, fun x hx => by have := hρpos x hx; positivity,
    ?_, ?_, ?_, ?_⟩
  · -- accumulation at the outer circle
    intro R' hR'
    by_contra hno
    push Not at hno
    set R'' := max R' r with hR''
    have hR''R : R'' < R := max_lt hR' hrR
    set a := (R + R'') / 2 with hadef
    have hUa : U ⊆ closedBall (0 : ℂ) a := by
      refine iUnion₂_subset fun x hx => ?_
      intro z hz
      have h1 := norm_le_of_mem_closedBall_admissible (hρlt x hx) hz
      have h2 : ‖x‖ ≤ R'' := (hno x hx).trans (le_max_left _ _)
      rw [mem_closedBall, dist_zero_right]; rw [hadef]; linarith
    set V := (fun z : ℂ => ‖z‖) ⁻¹' Ioo a R with hVdef
    have hVopen : IsOpen V := isOpen_Ioo.preimage continuous_norm
    have hVne : V.Nonempty := by
      refine ⟨(((a + R) / 2 : ℝ) : ℂ), ?_⟩
      have ha0 : 0 ≤ a := by rw [hadef]; have := le_max_right R' r; linarith
      show a < ‖(((a + R) / 2 : ℝ) : ℂ)‖ ∧ ‖(((a + R) / 2 : ℝ) : ℂ)‖ < R
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      constructor <;> linarith
    have hVsub : V ⊆ A \ U := by
      intro z hz
      have hz' : a < ‖z‖ ∧ ‖z‖ < R := hz
      refine ⟨?_, fun hzU => ?_⟩
      · show r < ‖z‖ ∧ ‖z‖ < R
        have : r ≤ R'' := le_max_right _ _
        constructor <;> linarith
      · have := hUa hzU
        rw [mem_closedBall, dist_zero_right] at this
        linarith
    have hpos := hVopen.measure_pos (volume : Measure ℂ) hVne
    have hle := measure_mono (μ := volume) hVsub
    rw [hnull] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  · -- the total mass
    have h0 := hsum 0
    simp only [pow_zero, mul_one] at h0
    rw [setIntegral_const, Complex.real_smul, mul_one] at h0
    have hvol : volume.real A = Real.pi * (R ^ 2 - r ^ 2) := by
      have hA : A = ball (0 : ℂ) R \ closedBall 0 r := by
        ext z; simp [hAdef, annulus, mem_ball, mem_closedBall, dist_zero_right, and_comm]
      rw [hA, measureReal_sdiff (fun z hz => by
          rw [mem_closedBall, dist_zero_right] at hz; rw [mem_ball, dist_zero_right]; linarith)
        measurableSet_closedBall, real_volume_closedBall hr]
      rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by linarith)]
      simp; ring
    rw [hvol] at h0
    exact Complex.hasSum_ofReal.mp h0
  · intro k hk
    have h := hsum k
    rw [hAdef, annulus, setIntegral_pow_radial_eq_zero _ hk] at h
    exact h
  · intro hr0 k hk
    have h := hsumInv hr0 k hk
    rw [hAdef, annulus, setIntegral_inv_pow_radial_eq_zero _ hk] at h
    exact h

end GaloisForLFunctions.HTGeometry.PositiveWolffMeasure
