/-
# Local divergence of a repaired-frequency source

A positive measure `mu` on the half line whose shifted power moments `∫ x^{n+1} dmu` equal the
shifted factorial moments `(2n+1)! ∫ y^{n+1} dnu` of a compactly supported measure `nu` is forced
by determinacy to be the explicit density measure of `ShiftedFactorialMomentDensity`.  If `nu`
carries mass away from the origin, that density stays bounded below near `0`, and the resulting
`dx / x` behaviour makes `mu` infinite on every neighbourhood of the zero frequency.
-/
import GaloisForLFunctions.HTGeometry.ShiftedFactorialMomentDensity
import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- Near the origin the representing density is bounded below by a positive constant. -/
theorem le_factorialMomentDensity {nu : Measure ℝ} [IsFiniteMeasure nu] {eta : ℝ}
    (heta : 0 < eta) {x : ℝ} (hxeta : x ≤ eta) :
    Real.exp (-1) * (nu (Ici eta)).toReal / 2 ≤ factorialMomentDensity nu x := by
  have hint : Integrable (fun y => sqrtExpDensity y x) (nu.restrict (Ioi 0)) := by
    refine Integrable.mono' (integrable_const 1) ?_ ?_
    · exact (measurable_uncurry_sqrtExpDensity.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrtExpDensity_nonneg y x)]
      exact sqrtExpDensity_le_one y x
  have hsub : Ici eta ⊆ Ioi (0:ℝ) := fun y hy => lt_of_lt_of_le heta hy
  have hmono : (∫ y in Ici eta, sqrtExpDensity y x ∂nu)
      ≤ ∫ y in Ioi (0:ℝ), sqrtExpDensity y x ∂nu := by
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub)
    filter_upwards with y using sqrtExpDensity_nonneg y x
  have hlow : Real.exp (-1) * (nu (Ici eta)).toReal
      ≤ ∫ y in Ici eta, sqrtExpDensity y x ∂nu := by
    have hpt : ∀ y ∈ Ici eta, Real.exp (-1) ≤ sqrtExpDensity y x := by
      intro y hy
      have hy' : (0:ℝ) < y := lt_of_lt_of_le heta hy
      rw [sqrtExpDensity]
      refine Real.exp_le_exp.2 ?_
      have hxy : x / y ≤ 1 := by
        rw [div_le_one hy']
        exact le_trans hxeta hy
      have hsq : Real.sqrt (x / y) ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt hxy
      linarith
    have hconst : (∫ _y in Ici eta, Real.exp (-1) ∂nu) ≤ ∫ y in Ici eta, sqrtExpDensity y x ∂nu := by
      refine setIntegral_mono_on (integrable_const _).integrableOn ?_ measurableSet_Ici hpt
      exact hint.mono_measure (Measure.restrict_mono hsub le_rfl)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at hconst
    exact hconst
  rw [factorialMomentDensity]
  have := le_trans hlow hmono
  linarith

/-! ### The shifted measure and determinacy -/

theorem integral_pow_shiftedMeasure {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x) (n : ℕ) :
    (∫ x, x ^ n ∂(mu.withDensity fun x => ENNReal.ofReal x)) = ∫ x, x ^ (n + 1) ∂mu := by
  rw [integral_withDensity_eq_integral_toReal_smul ENNReal.measurable_ofReal
    (by filter_upwards with x using ENNReal.ofReal_lt_top) (fun x : ℝ => x ^ n)]
  refine integral_congr_ae ?_
  filter_upwards [hmu] with x hx
  rw [smul_eq_mul, ENNReal.toReal_ofReal hx, pow_succ]
  ring

theorem integrable_pow_shiftedMeasure {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x) {n : ℕ}
    (hint : Integrable (fun x : ℝ => x ^ (n + 1)) mu) :
    Integrable (fun x : ℝ => x ^ n) (mu.withDensity fun x => ENNReal.ofReal x) := by
  rw [MeasureTheory.integrable_withDensity_iff ENNReal.measurable_ofReal
    (by filter_upwards with x using ENNReal.ofReal_lt_top)]
  refine hint.congr ?_
  filter_upwards [hmu] with x hx
  rw [ENNReal.toReal_ofReal hx, pow_succ]

theorem isFiniteMeasure_shiftedMeasure {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : Integrable (fun x : ℝ => x ^ (0 + 1)) mu) :
    IsFiniteMeasure (mu.withDensity fun x => ENNReal.ofReal x) := by
  constructor
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnn : ∀ᵐ x ∂mu, 0 ≤ x ^ (0 + 1) := by
    filter_upwards [hmu] with x hx
    simpa using hx
  have hfin := hint.2
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn] at hfin
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine lintegral_congr_ae ?_
  filter_upwards with x
  simp

theorem ae_nonneg_factorialMomentMeasure (nu : Measure ℝ) :
    ∀ᵐ x ∂(factorialMomentMeasure nu), 0 ≤ x := by
  rw [factorialMomentMeasure]
  refine (MeasureTheory.withDensity_absolutelyContinuous _ _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using le_of_lt hx

theorem ae_nonneg_shiftedMeasure {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x) :
    ∀ᵐ x ∂(mu.withDensity fun x => ENNReal.ofReal x), 0 ≤ x :=
  (MeasureTheory.withDensity_absolutelyContinuous _ _) hmu

/-- **Determinacy.**  The explicit density is the unique finite Stieltjes representative of the
shifted factorial moment sequence. -/
theorem shiftedMeasure_eq_factorialMomentMeasure {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu) :
    factorialMomentMeasure nu = mu.withDensity fun x => ENNReal.ofReal x := by
  haveI := isFiniteMeasure_factorialMomentMeasure hsupp
  haveI := isFiniteMeasure_shiftedMeasure hmu (hmomInt 0)
  have hRs : (0:ℝ) < Real.sqrt R := Real.sqrt_pos.2 hR
  refine HTGeometry.measure_eq_of_hasStieltjesMoments_of_hardy
    (s := fun n => (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu)
    ⟨fun n => ⟨integrable_pow_factorialMomentMeasure hsupp n,
      integral_pow_factorialMomentMeasure hsupp n⟩, ae_nonneg_factorialMomentMeasure nu⟩
    ⟨fun n => ⟨integrable_pow_shiftedMeasure hmu (hmomInt n),
      by rw [integral_pow_shiftedMeasure hmu n, hmom n]⟩, ae_nonneg_shiftedMeasure hmu⟩
    (c := 1 / (2 * Real.sqrt R)) (by positivity) ?_
  refine integrable_exp_sqrt_factorialMomentMeasure hR hsupp ?_
  rw [div_lt_div_iff₀ (by positivity) hRs]
  nlinarith

/-! ### Local divergence at the zero-frequency border -/

/-- **Locally infinite repaired-frequency source.**  A positive measure on the open half line whose
`(n+1)`-st moments are the shifted factorial moments `(2n+1)! S_{n+1}` of a compactly supported `ν`
carrying mass away from the origin has infinite mass in every neighbourhood of frequency zero. -/
theorem measure_Ioo_eq_top_of_shiftedFactorialMoments {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    {eta : ℝ} (heta : 0 < eta) (hnu : nu (Ici eta) ≠ 0)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0:ℝ), y ^ (n + 1) ∂nu)
    {delta : ℝ} (hdelta : 0 < delta) :
    mu (Ioo 0 delta) = ⊤ := by
  classical
  have heq := shiftedMeasure_eq_factorialMomentMeasure hR hsupp hmu hmomInt hmom
  set c : ℝ := Real.exp (-1) * (nu (Ici eta)).toReal / 2 with hc
  have hcpos : 0 < c := by
    have h1 : (0:ℝ) < (nu (Ici eta)).toReal := by
      refine ENNReal.toReal_pos hnu (measure_ne_top nu _)
    rw [hc]
    positivity
  set t : ℝ := min delta eta with ht
  have htpos : 0 < t := lt_min hdelta heta
  set A : ℕ → Set ℝ := fun j => Ioo (t / 2 ^ (j + 1)) (t / 2 ^ j) with hA
  have hApos : ∀ j, (0:ℝ) < t / 2 ^ (j + 1) := fun j => by positivity
  have hAsub : ∀ j, A j ⊆ Ioo 0 delta := by
    intro j x hx
    refine ⟨lt_trans (hApos j) hx.1, lt_of_lt_of_le hx.2 ?_⟩
    calc t / 2 ^ j ≤ t := by
          refine div_le_self htpos.le ?_
          exact one_le_pow₀ (by norm_num)
      _ ≤ delta := min_le_left _ _
  have hkey : ∀ i j : ℕ, i < j → Disjoint (A i) (A j) := by
    intro i j hlt
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    have h1 : x < t / 2 ^ j := hxj.2
    have h2 : t / 2 ^ (i + 1) < x := hxi.1
    have h3 : t / 2 ^ j ≤ t / 2 ^ (i + 1) := by
      refine div_le_div_of_nonneg_left htpos.le (by positivity) ?_
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h
    · exact (hkey j i h).symm
  -- the key per-block lower bound
  have hblock : ∀ j : ℕ, ENNReal.ofReal c / 2 ≤ mu (A j) := by
    intro j
    have hmeas : MeasurableSet (A j) := measurableSet_Ioo
    have hsub0 : A j ⊆ Ioi (0:ℝ) := fun x hx => lt_trans (hApos j) hx.1
    -- upper bound via the shifted measure
    have hupper : (mu.withDensity fun x => ENNReal.ofReal x) (A j)
        ≤ ENNReal.ofReal (t / 2 ^ j) * mu (A j) := by
      rw [MeasureTheory.withDensity_apply _ hmeas]
      calc (∫⁻ x in A j, ENNReal.ofReal x ∂mu)
          ≤ ∫⁻ _x in A j, ENNReal.ofReal (t / 2 ^ j) ∂mu := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hmeas] with x hx
            exact ENNReal.ofReal_le_ofReal hx.2.le
        _ = ENNReal.ofReal (t / 2 ^ j) * mu (A j) := by
            rw [MeasureTheory.setLIntegral_const]
    -- lower bound via the density
    have hlower : ENNReal.ofReal c * ENNReal.ofReal (t / 2 ^ (j + 1))
        ≤ factorialMomentMeasure nu (A j) := by
      rw [factorialMomentMeasure, MeasureTheory.withDensity_apply _ hmeas,
        Measure.restrict_restrict hmeas]
      have hinter : A j ∩ Ioi (0:ℝ) = A j := Set.inter_eq_left.2 hsub0
      rw [hinter]
      have hvol : volume (A j) = ENNReal.ofReal (t / 2 ^ (j + 1)) := by
        rw [hA, Real.volume_Ioo]
        congr 1
        field_simp
        ring
      calc ENNReal.ofReal c * ENNReal.ofReal (t / 2 ^ (j + 1))
          = ∫⁻ _x in A j, ENNReal.ofReal c := by
            rw [MeasureTheory.setLIntegral_const, hvol]
        _ ≤ ∫⁻ x in A j, ENNReal.ofReal (factorialMomentDensity nu x) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hmeas] with x hx
            refine ENNReal.ofReal_le_ofReal ?_
            refine le_factorialMomentDensity heta ?_
            refine le_trans hx.2.le ?_
            calc t / 2 ^ j ≤ t := by
                  refine div_le_self htpos.le ?_
                  exact one_le_pow₀ (by norm_num)
              _ ≤ eta := min_le_right _ _
    rw [heq] at hlower
    have hchain : ENNReal.ofReal c * ENNReal.ofReal (t / 2 ^ (j + 1))
        ≤ ENNReal.ofReal (t / 2 ^ j) * mu (A j) := le_trans hlower hupper
    have hsplit : ENNReal.ofReal (t / 2 ^ j)
        = 2 * ENNReal.ofReal (t / 2 ^ (j + 1)) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
      ring
    rw [hsplit] at hchain
    have hne0 : ENNReal.ofReal (t / 2 ^ (j + 1)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hApos j
    have hnetop : ENNReal.ofReal (t / 2 ^ (j + 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcancel : ENNReal.ofReal c ≤ 2 * mu (A j) := by
      have hrw : 2 * ENNReal.ofReal (t / 2 ^ (j + 1)) * mu (A j)
          = (2 * mu (A j)) * ENNReal.ofReal (t / 2 ^ (j + 1)) := by ring
      rw [hrw] at hchain
      exact (ENNReal.mul_le_mul_iff_left hne0 hnetop).1 hchain
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [mul_comm]
    exact hcancel
  -- summing the blocks
  have hall : ∀ N : ℕ, (N : ENNReal) * (ENNReal.ofReal c / 2) ≤ mu (Ioo 0 delta) := by
    intro N
    have hunion : mu (⋃ j ∈ Finset.range N, A j) ≤ mu (Ioo 0 delta) :=
      measure_mono (Set.iUnion₂_subset fun j _ => hAsub j)
    have hdisjsum : mu (⋃ j ∈ Finset.range N, A j) = ∑ j ∈ Finset.range N, mu (A j) :=
      measure_biUnion_finset (fun i _ j _ hij => hAdisj hij) (fun j _ => measurableSet_Ioo)
    rw [hdisjsum] at hunion
    refine le_trans ?_ hunion
    calc (N : ENNReal) * (ENNReal.ofReal c / 2)
        = ∑ _j ∈ Finset.range N, (ENNReal.ofReal c / 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range N, mu (A j) := Finset.sum_le_sum fun j _ => hblock j
  by_contra hfin
  have hkne : ENNReal.ofReal c / 2 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.ofReal_eq_zero, not_or, not_le]
    exact ⟨hcpos, by norm_num⟩
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hkne hfin
  exact absurd (hall N) (not_le.2 hN)
