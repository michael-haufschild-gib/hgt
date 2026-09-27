import GaloisForLFunctions.RHTower.ErrorExponentAbscissaExcessLaw

/-!
# Off-line multiplicity clusters: bounded depth without an error exponent

The equivalence `abs_re_sub_half_le_iff_eventually_relaxed` between the abscissa excess and the
eventual error exponent assumes a uniform bound on the off-line multiplicity of unit windows.
This hypothesis cannot be dropped, even under the ζ-type local count.

The **cluster configuration** (`offLineClusterConfig`) has, at each height `e^{k+1}`, the pair
`¾ + ie^{k+1}`, `¼ + ie^{k+1}`, each of multiplicity `k + 1 = ⌊log γ⌋`.  Every zero has
`|β - ½| = ¼`, there are no zeros below ordinate `2`, and `N(t, t + 1] ≤ 2 log(|t| + 3)`.  Yet
(`offLineClusterConfig_eventually_not_relaxed`) at every large level `a` the relaxed Hodge index
fails for every exponent `θ`, and the Weil form is unbounded below on the polar-constrained `C²`
tests supported in `[-a, a]` (`offLineClusterConfig_weil_unbounded_below`).

**Proof.**  The test is the polar-corrected deep-zero test
`e^{-iγ₀u} sinh(u/4)(a² - u²)₊^{5/2} + c₁ w_a + c₂ sinh(u/2) w_a` at `γ₀ = e^{k+1}`.
* **Isolation.**  Distinct heights are more than `e^k` apart, so for `k > a` the pair at
  `e^{k+1}` is isolated at radius `e^a`.
* **Weil form.**  The isolation inequality `re_W_modulatedTest_le_of_isolated` keeps the
  multiplicity: the pair contributes `-2(k + 1)P²`, `P = ∫ s sinh(u/4)`, while every other zero
  and the polar correction contribute `O((k + 2) ‖s‖²)`, because `log(e^{k+1} + 3) ≤ k + 2`.
* **Size.**  For `a` large, `P² ≥ 12288 (‖s‖₁ + ‖s''‖₁)²` (`eventually_cluster_size`), so
  `Re W ≤ -(3/2)(k + 1) P²`.  The polar coefficients are `O(1/k)` and the test energy stays
  bounded by a constant `K₀(a)`.  Taking `k P² > e^{θa} K₀` violates the relaxed index.

The error exponent therefore measures the depth together with the off-line multiplicity: a
multiplicity growing like `log γ` at fixed depth already makes it infinite.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### The cluster configuration -/

/-- `β + i e^{k+1}`. -/
def clusterPoint (β : ℝ) (k : ℕ) : ℂ := ⟨β, Real.exp (k + 1)⟩

theorem clusterPoint_re (β : ℝ) (k : ℕ) : (clusterPoint β k).re = β := rfl

theorem clusterPoint_im (β : ℝ) (k : ℕ) : (clusterPoint β k).im = Real.exp (k + 1) := rfl

theorem floor_log_clusterPoint_im (β : ℝ) (k : ℕ) : ⌊Real.log (clusterPoint β k).im⌋₊ = k + 1 := by
  rw [clusterPoint_im, Real.log_exp]
  exact_mod_cast Nat.floor_natCast (R := ℝ) (k + 1)

theorem reflect_clusterPoint (β : ℝ) (k : ℕ) : reflect (clusterPoint β k) = clusterPoint (1 - β) k := by
  apply Complex.ext <;> simp [reflect, clusterPoint]

/-- Distinct cluster heights are more than `max(1, e^k)` apart. -/
theorem exp_le_abs_cluster_height_sub {j k : ℕ} (hjk : j ≠ k) :
    Real.exp k ≤ |Real.exp (j + 1) - Real.exp (k + 1)| ∧
      1 < |Real.exp (j + 1) - Real.exp (k + 1)| := by
  have he := Real.exp_one_gt_d9
  rcases lt_or_gt_of_ne hjk with h | h
  · have hj : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    have h1 : Real.exp (j + 1) ≤ Real.exp k := Real.exp_le_exp.mpr hj
    have h2 : Real.exp (k + 1) = Real.exp k * Real.exp 1 := Real.exp_add _ _
    have hk1 : 1 ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
    rw [abs_sub_comm, abs_of_pos (by nlinarith)]
    constructor <;> nlinarith
  · have hk : (k : ℝ) + 2 ≤ j + 1 := by
      have : k + 1 ≤ j := h
      have : ((k + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast this
      push_cast at this; linarith
    have h1 : Real.exp (k + 2) ≤ Real.exp (j + 1) := Real.exp_le_exp.mpr hk
    have h2 : Real.exp (k + 2) = Real.exp (k + 1) * Real.exp 1 := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp k ≤ Real.exp (k + 1) := Real.exp_le_exp.mpr (by linarith)
    have hk1 : 1 ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
    rw [abs_of_pos (by nlinarith)]
    constructor <;> nlinarith

theorem clusterPoint_injective_height {β β' : ℝ} {j k : ℕ}
    (h : (clusterPoint β j).im = (clusterPoint β' k).im) : j = k := by
  by_contra hjk
  have := (exp_le_abs_cluster_height_sub hjk).2
  rw [clusterPoint_im, clusterPoint_im] at h
  rw [h, sub_self, abs_zero] at this
  linarith

/-- **The off-line cluster configuration.**  At each height `e^{k+1}` the pair `¾ + ie^{k+1}`,
`¼ + ie^{k+1}`, each of multiplicity `k + 1 = ⌊log γ⌋`. -/
def offLineClusterConfig : ZeroConfig where
  carrier := Set.range (clusterPoint (3 / 4)) ∪ Set.range (clusterPoint (1 / 4))
  mult := fun ρ => ⌊Real.log ρ.im⌋₊
  one_le_mult := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> rw [floor_log_clusterPoint_im] <;> omega
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp only [clusterPoint_re] <;> constructor <;> norm_num
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · right; exact ⟨k, by rw [reflect_clusterPoint]; norm_num⟩
    · left; exact ⟨k, by rw [reflect_clusterPoint]; norm_num⟩
  mult_reflect := fun ρ _ => by simp only [Tail.reflect_im]
  finite_window := by
    intro T₁ T₂
    have hF : (Finset.range ⌈T₂⌉₊ : Set ℕ).Finite := Finset.finite_toSet _
    refine ((hF.image (clusterPoint (3 / 4))).union (hF.image (clusterPoint (1 / 4)))).subset ?_
    have hk : ∀ k : ℕ, Real.exp (k + 1) ≤ T₂ → k ∈ (Finset.range ⌈T₂⌉₊ : Set ℕ) := by
      intro k hk
      have h1 := Real.add_one_lt_exp (x := (k : ℝ) + 1) (by positivity)
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_ceil.mpr (by linarith)
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, -, h2⟩
    · exact Or.inl ⟨k, hk k h2, rfl⟩
    · exact Or.inr ⟨k, hk k h2, rfl⟩

theorem offLineClusterConfig_mult (β : ℝ) (k : ℕ) :
    offLineClusterConfig.mult (clusterPoint β k) = k + 1 := floor_log_clusterPoint_im β k

theorem offLineClusterConfig_depth :
    ∀ ρ ∈ offLineClusterConfig.carrier, |ρ.re - 1 / 2| = 1 / 4 := by
  rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> rw [clusterPoint_re] <;> norm_num [abs_of_pos, abs_of_neg]

theorem offLineClusterConfig_two_le_im : ∀ ρ ∈ offLineClusterConfig.carrier, 2 ≤ |ρ.im| := by
  rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> rw [clusterPoint_im, abs_of_pos (Real.exp_pos _)] <;>
  · have := Real.add_one_le_exp ((k : ℝ) + 1)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- **ζ-type local count.**  `N(t, t + 1] ≤ 2 log(|t| + 3)`. -/
theorem offLineClusterConfig_local_count (t : ℝ) :
    (offLineClusterConfig.N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3) := by
  classical
  set Z := offLineClusterConfig with hZ
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  have hlog0 : 0 ≤ Real.log (|t| + 3) := (zero_le_one).trans (one_le_log_abs_add_three t)
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · unfold ZeroConfig.N
    rw [hE, finsum_mem_empty]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog0
  obtain ⟨hρ₀c, hρ₀t⟩ := hρ₀
  have hρ₀t' : t < ρ₀.im ∧ ρ₀.im ≤ t + 1 := hρ₀t
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ρ₀.im = Real.exp (k + 1) := by
    rcases hρ₀c with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> exact ⟨k, rfl⟩
  have hsub : hfin.toFinset ⊆ {clusterPoint (3 / 4) k, clusterPoint (1 / 4) k} := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨hρc, hρt⟩ := hρ
    have hρt' : t < ρ.im ∧ ρ.im ≤ t + 1 := hρt
    have hj : ∀ β j, ρ = clusterPoint β j → j = k := by
      intro β j hρj
      by_contra hjk
      have := (exp_le_abs_cluster_height_sub hjk).2
      rw [← clusterPoint_im β j, ← hρj, ← hk] at this
      have h2 : |ρ.im - ρ₀.im| < 1 := abs_sub_lt_iff.mpr
        ⟨by linarith [hρt'.1, hρt'.2, hρ₀t'.1, hρ₀t'.2],
          by linarith [hρt'.1, hρt'.2, hρ₀t'.1, hρ₀t'.2]⟩
      linarith
    rcases hρc with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hj _ j rfl]; simp
    · rw [hj _ j rfl]; simp
  have hne : clusterPoint (3 / 4) k ≠ clusterPoint (1 / 4) k := by
    intro h
    have := congrArg Complex.re h
    rw [clusterPoint_re, clusterPoint_re] at this
    norm_num at this
  have hN : (Z.N t (t + 1) : ℝ) ≤ 2 * (k + 1) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    have e1 : Z.mult (clusterPoint (3 / 4) k) = k + 1 := offLineClusterConfig_mult _ _
    have e2 : Z.mult (clusterPoint (1 / 4) k) = k + 1 := offLineClusterConfig_mult _ _
    rw [Finset.sum_pair hne, e1, e2] at h
    have : (∑ ρ ∈ hfin.toFinset, Z.mult ρ : ℕ) ≤ 2 * (k + 1) := by omega
    exact_mod_cast this
  have ht : Real.exp (k + 1) - 1 ≤ t := by linarith [hρ₀t'.2]
  have hlog : (k : ℝ) + 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [le_abs_self t])
  linarith

/-! ### The polar-corrected deep-zero test at an arbitrary height -/

/-- The polar-corrected test `e^{-iγ₀u} s(u) + c₁ w_a(u) + c₂ sinh(u/2) w_a(u)` with
`s = sinh(δu) w_a(u)`: its coefficients are at most `H/α` and `H/β`, where
`H = 4 e^{a/2} ‖s‖/(1 + |γ₀|)²` bounds the two polar values of the modulated test. -/
theorem exists_polarCorrected_sinhTest {a δ : ℝ} (ha : 0 < a) (γ₀ : ℝ) :
    ∃ c₁ c₂ : ℂ,
      ContDiff ℝ 2 (polarCorrectedTest γ₀ (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2))
        c₁ c₂) ∧
      tsupport (polarCorrectedTest γ₀ (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2))
        c₁ c₂) ⊆ Icc (-a) a ∧
      paperFT (polarCorrectedTest γ₀ (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2))
        c₁ c₂) (I / 2) = 0 ∧
      paperFT (polarCorrectedTest γ₀ (sinhTest a δ) (sinhTestWeight a) (sinhTest a (1 / 2))
        c₁ c₂) (-(I / 2)) = 0 ∧
      ‖c₁‖ ≤ Real.exp (a / 2) * (4 * testNorm (sinhTest a δ)) / (1 + |γ₀|) ^ 2 /
        (a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ)) ∧
      ‖c₂‖ ≤ Real.exp (a / 2) * (4 * testNorm (sinhTest a δ)) / (1 + |γ₀|) ^ 2 /
        deepZeroEnergyBound a (1 / 2) (a / 4) ∧
      ‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2)) ≤
        testNorm (sinhTest a δ) * polarCorrectionBound a γ₀ := by
  have hIhalf : I * ((1 / 2 : ℝ) : ℂ) = I / 2 := by push_cast; ring
  have hαb := sinhTestWeight_cosh_energy_ge ha
  have hβb : deepZeroEnergyBound a (1 / 2) (a / 4) ≤
      ∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u) :=
    sinhTest_energy_ge (a := a) (δ := 1 / 2) (w := a / 4) (by norm_num) (by positivity) le_rfl
  have hαb0 : 0 < a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) := by positivity
  have hβb0 : 0 < deepZeroEnergyBound a (1 / 2) (a / 4) :=
    deepZeroEnergyBound_pos (by norm_num) (by positivity) (by linarith)
  have hp1 := paperFT_even_I_mul (sinhTestWeight_contDiff a).continuous
    (sinhTestWeight_supp ha.le) (sinhTestWeight_even a) (1 / 2)
  have hm1 := paperFT_even_neg_I_mul (sinhTestWeight_contDiff a).continuous
    (sinhTestWeight_supp ha.le) (sinhTestWeight_even a) (1 / 2)
  have hp2 := paperFT_odd_I_mul (sinhTest_contDiff a (1 / 2)).continuous
    (sinhTest_supp (a := a) (δ := 1 / 2) ha.le) (sinhTest_odd a (1 / 2)) (1 / 2)
  have hm2 := paperFT_odd_neg_I_mul (sinhTest_contDiff a (1 / 2)).continuous
    (sinhTest_supp (a := a) (δ := 1 / 2) ha.le) (sinhTest_odd a (1 / 2)) (1 / 2)
  rw [hIhalf] at hp1 hm1 hp2 hm2
  obtain ⟨hpol1, hpol2⟩ := polarCorrectedTest_polar_zero (γ₀ := γ₀)
    (sinhTest_contDiff a δ).continuous (sinhTestWeight_contDiff a).continuous
    (sinhTest_contDiff a (1 / 2)).continuous (sinhTest_supp ha.le) (sinhTestWeight_supp ha.le)
    (sinhTest_supp ha.le) (hαb0.trans_le hαb).ne' (hβb0.trans_le hβb).ne' hp1 hm1 hp2 hm2
  have hHp := norm_paperFT_modulatedTest_polar_le (γ₀ := γ₀) (sinhTest_contDiff a δ)
    (sinhTest_supp ha.le) (1 / 2) (by norm_num)
  have hHm := norm_paperFT_modulatedTest_polar_le (γ₀ := γ₀) (sinhTest_contDiff a δ)
    (sinhTest_supp ha.le) (-(1 / 2)) (by norm_num)
  rw [hIhalf] at hHp
  rw [show I * ((-(1 / 2) : ℝ) : ℂ) = -(I / 2) by push_cast; ring] at hHm
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℂ, c =
      -(paperFT (modulatedTest γ₀ (sinhTest a δ)) (I / 2) +
          paperFT (modulatedTest γ₀ (sinhTest a δ)) (-(I / 2))) /
        (2 * ((∫ u, sinhTestWeight a u * Real.cosh (1 / 2 * u) : ℝ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℂ, c =
      (paperFT (modulatedTest γ₀ (sinhTest a δ)) (I / 2) -
          paperFT (modulatedTest γ₀ (sinhTest a δ)) (-(I / 2))) /
        (2 * ((∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u) : ℝ) : ℂ)) := ⟨_, rfl⟩
  rw [← hc₁, ← hc₂] at hpol1 hpol2
  have hG := polarCorrection_coeff_bound hαb0 hβb0 hαb hβb hHp hHm
    (testNorm_sinhTestWeight_le ha.le) (testNorm_sinhTest_le ha.le (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (testNorm_nonneg _) (testNorm_nonneg _)
  rw [← hc₁, ← hc₂] at hG
  have hH0 : 0 ≤ Real.exp (a / 2) * (4 * testNorm (sinhTest a δ)) / (1 + |γ₀|) ^ 2 := by
    have := testNorm_nonneg (sinhTest a δ); positivity
  have hα0 := hαb0.trans_le hαb
  have hβ0 := hβb0.trans_le hβb
  refine ⟨c₁, c₂, polarCorrectedTest_contDiff γ₀ (sinhTest_contDiff a δ)
      (sinhTestWeight_contDiff a) (sinhTest_contDiff a (1 / 2)) c₁ c₂,
    tsupport_polarCorrectedTest_subset γ₀ (sinhTest_supp ha.le) (sinhTestWeight_supp ha.le)
      (sinhTest_supp ha.le) c₁ c₂, hpol1, hpol2, ?_, ?_, ?_⟩
  · rw [hc₁, norm_div, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hα0]
    have h1 := norm_add_le (paperFT (modulatedTest γ₀ (sinhTest a δ)) (I / 2))
      (paperFT (modulatedTest γ₀ (sinhTest a δ)) (-(I / 2)))
    calc _ ≤ (2 * (Real.exp (a / 2) * (4 * testNorm (sinhTest a δ)) / (1 + |γ₀|) ^ 2)) /
          (2 * ∫ u, sinhTestWeight a u * Real.cosh (1 / 2 * u)) := by gcongr; linarith
      _ ≤ _ := by
          rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
          exact div_le_div_of_nonneg_left hH0 hαb0 hαb
  · rw [hc₂, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hβ0]
    have h1 := norm_sub_le (paperFT (modulatedTest γ₀ (sinhTest a δ)) (I / 2))
      (paperFT (modulatedTest γ₀ (sinhTest a δ)) (-(I / 2)))
    calc _ ≤ (2 * (Real.exp (a / 2) * (4 * testNorm (sinhTest a δ)) / (1 + |γ₀|) ^ 2)) /
          (2 * ∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u)) := by gcongr; linarith
      _ ≤ _ := by
          rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
          exact div_le_div_of_nonneg_left hH0 hβb0 hβb
  · refine hG.trans (le_of_eq ?_)
    unfold polarCorrectionBound deepZeroNormBound
    ring

theorem norm_sq_polarCorrectedTest_le (γ₀ : ℝ) (s φ₁ φ₂ : ℝ → ℝ) (c₁ c₂ : ℂ) (u : ℝ) :
    ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ ^ 2 ≤
      3 * (s u ^ 2 + ‖c₁‖ ^ 2 * φ₁ u ^ 2 + ‖c₂‖ ^ 2 * φ₂ u ^ 2) := by
  have hm : ‖modulatedTest γ₀ s u‖ = |s u| := by
    unfold modulatedTest
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp
  have ht := norm_add₃_le (a := modulatedTest γ₀ s u) (b := c₁ * (φ₁ u : ℂ))
    (c := c₂ * (φ₂ u : ℂ))
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, hm] at ht
  have hF' : polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u =
      modulatedTest γ₀ s u + c₁ * (φ₁ u : ℂ) + c₂ * (φ₂ u : ℂ) := rfl
  rw [← hF'] at ht
  have hn := norm_nonneg (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u)
  have e1 : |s u| ^ 2 = s u ^ 2 := sq_abs _
  have e2 : (‖c₁‖ * |φ₁ u|) ^ 2 = ‖c₁‖ ^ 2 * φ₁ u ^ 2 := by rw [mul_pow, sq_abs]
  have e3 : (‖c₂‖ * |φ₂ u|) ^ 2 = ‖c₂‖ ^ 2 * φ₂ u ^ 2 := by rw [mul_pow, sq_abs]
  have h1 := pow_le_pow_left₀ hn ht 2
  nlinarith [sq_nonneg (|s u| - ‖c₁‖ * |φ₁ u|), sq_nonneg (|s u| - ‖c₂‖ * |φ₂ u|),
    sq_nonneg (‖c₁‖ * |φ₁ u| - ‖c₂‖ * |φ₂ u|)]

theorem integrable_sq_of_supp {φ : ℝ → ℝ} {a : ℝ} (hφ : Continuous φ)
    (hφs : ∀ u, φ u ≠ 0 → |u| ≤ a) : Integrable (fun u => φ u ^ 2) := by
  have h2 : HasCompactSupport (fun u => φ u * φ u) :=
    (hasCompactSupport_of_support_subset_abs hφs).mul_right
  have : HasCompactSupport (fun u => φ u ^ 2) := by
    rw [show (fun u => φ u ^ 2) = fun u => φ u * φ u from funext fun u => sq _]; exact h2
  exact (hφ.pow 2).integrable_of_hasCompactSupport this

/-- `∫ |F|² ≤ 3(∫ s² + |c₁|² ∫ φ₁² + |c₂|² ∫ φ₂²)` for the polar-corrected test. -/
theorem integral_norm_sq_polarCorrectedTest_le (γ₀ : ℝ) {s φ₁ φ₂ : ℝ → ℝ} {a : ℝ}
    (hs : ContDiff ℝ 2 s) (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (hss : ∀ u, s u ≠ 0 → |u| ≤ a) (h1s : ∀ u, φ₁ u ≠ 0 → |u| ≤ a)
    (h2s : ∀ u, φ₂ u ≠ 0 → |u| ≤ a) (c₁ c₂ : ℂ) :
    ∫ u, ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ ^ 2 ≤
      3 * ((∫ u, s u ^ 2) + ‖c₁‖ ^ 2 * (∫ u, φ₁ u ^ 2) + ‖c₂‖ ^ 2 * ∫ u, φ₂ u ^ 2) := by
  have iS := integrable_sq_of_supp hs.continuous hss
  have i1 := integrable_sq_of_supp hφ₁.continuous h1s
  have i2 := integrable_sq_of_supp hφ₂.continuous h2s
  have hF := (polarCorrectedTest_contDiff γ₀ hs hφ₁ hφ₂ c₁ c₂).continuous
  have hFs : HasCompactSupport (polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂) :=
    hasCompactSupport_of_tsupport_subset_Icc
      (tsupport_polarCorrectedTest_subset γ₀ hss h1s h2s c₁ c₂)
  have iF : Integrable (fun u => ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ ^ 2) := by
    have h2 : HasCompactSupport (fun u => ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ *
        ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖) := hFs.norm.mul_right
    have : HasCompactSupport (fun u => ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ ^ 2) := by
      rw [show (fun u => ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ ^ 2) =
        fun u => ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ *
          ‖polarCorrectedTest γ₀ s φ₁ φ₂ c₁ c₂ u‖ from funext fun u => sq _]
      exact h2
    exact (hF.norm.pow 2).integrable_of_hasCompactSupport this
  have i12 : Integrable (fun u => s u ^ 2 + ‖c₁‖ ^ 2 * φ₁ u ^ 2) := iS.add (i1.const_mul _)
  have i123 : Integrable (fun u => s u ^ 2 + ‖c₁‖ ^ 2 * φ₁ u ^ 2 + ‖c₂‖ ^ 2 * φ₂ u ^ 2) :=
    i12.add (i2.const_mul _)
  have hle := integral_mono iF (i123.const_mul 3) (norm_sq_polarCorrectedTest_le γ₀ s φ₁ φ₂ c₁ c₂)
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add i12 (i2.const_mul _), integral_add iS (i1.const_mul _),
    integral_const_mul, integral_const_mul]

/-! ### The violation -/

/-- The arithmetic of the violation: a pair of multiplicity `k + 1` beats every exponent once
`k P² > e^{θa} K₀`. -/
theorem cluster_violation_arith {k P N L E G W0 W θe K₀ F₂ : ℝ} (hk0 : 0 ≤ k) (hE0 : 0 ≤ E) (hθe : 0 ≤ θe)
    (hW0 : W0 ≤ -2 * (k + 1) * P ^ 2 + 384 * 2 * L * N ^ 2 * (1 + E))
    (hW : W ≤ W0 + G) (hG : G ≤ 1536 * L * N ^ 2)
    (hE : E ≤ 1) (hL : L ≤ k + 2) (hbig : 12288 * N ^ 2 ≤ P ^ 2) (hF₂ : F₂ ≤ K₀)
    (hind : -(θe * F₂) ≤ W) (hkP : θe * K₀ < k * P ^ 2) : False := by
  have hN2 := sq_nonneg N
  have h1 : 384 * 2 * L * N ^ 2 * (1 + E) ≤ 1536 * (k + 2) * N ^ 2 := by
    have h5 : L * N ^ 2 * (1 + E) ≤ (k + 2) * N ^ 2 * 2 := by
      have := mul_le_mul hL (by linarith : 1 + E ≤ 2) (by linarith) (by linarith)
      nlinarith
    nlinarith
  have h2 : G ≤ 1536 * (k + 2) * N ^ 2 := hG.trans (by nlinarith)
  have h3 : 3072 * (k + 2) * N ^ 2 ≤ (k + 1) * P ^ 2 / 2 := by nlinarith
  have h4 : θe * F₂ ≤ θe * K₀ := mul_le_mul_of_nonneg_left hF₂ hθe
  nlinarith [sq_nonneg P]

theorem polarCorrectionBound_eq (a γ₀ : ℝ) :
    polarCorrectionBound a γ₀ = polarCorrectionBound a 0 / (1 + |γ₀|) ^ 2 := by
  unfold polarCorrectionBound
  simp

theorem cluster_height_bounds (k : ℕ) :
    (k : ℝ) + 2 ≤ Real.exp (k + 1) ∧ Real.log (|Real.exp (k + 1)| + 3) ≤ k + 2 ∧
      (k : ℝ) ≤ (1 + |Real.exp (k + 1)|) ^ 2 := by
  have h1 := Real.add_one_le_exp ((k : ℝ) + 1)
  have hpos := Real.exp_pos ((k : ℝ) + 1)
  rw [abs_of_pos hpos]
  refine ⟨by linarith, ?_, by nlinarith⟩
  have he : Real.exp ((k : ℝ) + 2) = Real.exp (k + 1) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have he1 := Real.exp_one_gt_d9
  have hk : 1 ≤ Real.exp ((k : ℝ) + 1) := Real.one_le_exp (by positivity)
  rw [← Real.log_exp ((k : ℝ) + 2)]
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- Beyond height index `k > a`, the pair at height `e^{k+1}` is isolated at radius `e^a`. -/
theorem offLineClusterConfig_isolated {a : ℝ} {k : ℕ} (hka : a < k) :
    ∀ ρ ∈ offLineClusterConfig.carrier, ρ ≠ clusterPoint (3 / 4) k →
      ρ ≠ reflect (clusterPoint (3 / 4) k) →
      |ρ.im - (clusterPoint (3 / 4) k).im| ≤ Real.exp a → ρ.re = 1 / 2 := by
  have hfar : ∀ j : ℕ, j ≠ k → Real.exp a < |Real.exp (j + 1) - Real.exp (k + 1)| := fun j hj =>
    lt_of_lt_of_le (Real.exp_lt_exp.mpr hka) (exp_le_abs_cluster_height_sub hj).1
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩) h1 h2 h3
  · have hj : j ≠ k := fun h => h1 (by rw [h])
    exact absurd h3 (not_le.mpr (hfar j hj))
  · have hj : j ≠ k := fun h => h2 (by rw [h, reflect_clusterPoint]; norm_num)
    exact absurd h3 (not_le.mpr (hfar j hj))

/-- The Weil form of the polar-corrected test at the pair of height index `k`. -/
theorem re_W_cluster_test_le {a : ℝ} (ha : 0 < a) {k : ℕ} (hka : a < k) (c₁ c₂ : ℂ) :
    (offLineClusterConfig.W
        (polarCorrectedTest (Real.exp ((k : ℝ) + 1)) (sinhTest a (1 / 4)) (sinhTestWeight a)
          (sinhTest a (1 / 2)) c₁ c₂)
        (polarCorrectedTest (Real.exp ((k : ℝ) + 1)) (sinhTest a (1 / 4)) (sinhTestWeight a)
          (sinhTest a (1 / 2)) c₁ c₂)).re ≤
      -2 * ((k : ℝ) + 1) * (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u)) ^ 2 +
        384 * 2 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) * testNorm (sinhTest a (1 / 4)) ^ 2 *
          (1 + Real.exp a / (1 + Real.exp a)) +
        768 * Real.exp a * 2 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) *
          (testNorm (sinhTest a (1 / 4)) *
              (‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2))) +
            (‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2))) ^ 2) := by
  have hρ₀ : clusterPoint (3 / 4) k ∈ offLineClusterConfig.carrier := Or.inl ⟨k, rfl⟩
  have hre : (clusterPoint (3 / 4) k).re = 1 / 2 + 1 / 4 := by rw [clusterPoint_re]; norm_num
  have hmaster := re_W_modulatedTest_le_of_isolated offLineClusterConfig (A₀ := 2) (by norm_num)
    offLineClusterConfig_local_count hρ₀ (δ := 1 / 4) (by norm_num) hre ha.le
    (Real.exp_pos a).le (offLineClusterConfig_isolated hka) (sinhTest_contDiff a (1 / 4))
    (sinhTest_odd a (1 / 4)) (sinhTest_supp ha.le)
  have hmult : (offLineClusterConfig.mult (clusterPoint (3 / 4) k) : ℝ) = k + 1 := by
    rw [offLineClusterConfig_mult]; push_cast; ring
  rw [hmult, clusterPoint_im] at hmaster
  have hcorr := re_W_polarCorrected_le offLineClusterConfig (A₀ := 2) (by norm_num)
    offLineClusterConfig_local_count (Real.exp ((k : ℝ) + 1)) ha.le (sinhTest_contDiff a (1 / 4))
    (sinhTestWeight_contDiff a) (sinhTest_contDiff a (1 / 2)) (sinhTest_supp ha.le)
    (sinhTestWeight_supp ha.le) (sinhTest_supp ha.le) c₁ c₂
  linarith

theorem exp_mul_add_sq_le_one {E Pb Q k : ℝ} (hE : 1 ≤ E) (hPb0 : 0 ≤ Pb) (hQ : 0 ≤ Q)
    (hPbk : Pb * k ≤ Q) (hkQ : 2 * Q * E + 1 < k) : E * (Pb + Pb ^ 2) ≤ 1 := by
  have hk0 : 0 < k := by nlinarith
  have h1 : 2 * E * Pb < 1 := by
    by_contra hc
    push Not at hc
    have : 2 * E * (Pb * k) ≤ 2 * E * Q := mul_le_mul_of_nonneg_left hPbk (by positivity)
    nlinarith
  have hPb1 : Pb ≤ 1 / 2 := by nlinarith
  have h2 : E * Pb ^ 2 ≤ E * Pb * (1 / 2) := by
    have : Pb ^ 2 ≤ Pb * (1 / 2) := by nlinarith
    nlinarith
  nlinarith

theorem coeff_le_one_of_lt {H₀ X k D : ℝ} (hX : 0 < X) (hD : 0 < D) (hkD : k ≤ D)
    (hXk : H₀ / X < k) : H₀ / D / X ≤ 1 := by
  rw [div_div, div_le_one (by positivity)]
  rw [div_lt_iff₀ hX] at hXk
  nlinarith

/-- Choice of the height index. -/
theorem exists_cluster_index (a Q H₀ αb βb θe K₀ P : ℝ) :
    ∃ k : ℕ, a < k ∧ 2 * Q * Real.exp a + 1 < k ∧ H₀ / αb < k ∧ H₀ / βb < k ∧
      θe * K₀ / P ^ 2 < k := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max a (max (2 * Q * Real.exp a + 1) (max (H₀ / αb)
    (max (H₀ / βb) (θe * K₀ / P ^ 2)))))
  refine ⟨k, lt_of_le_of_lt (le_max_left _ _) hk, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hk
  · exact lt_of_le_of_lt (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hk
  · exact lt_of_le_of_lt ((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)) hk
  · exact lt_of_le_of_lt ((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)) hk

/-- `∫ |F|² ≤ K₀` once both polar coefficients are at most one. -/
theorem integral_norm_sq_cluster_test_le {a γ₀ : ℝ} (ha : 0 < a) {c₁ c₂ : ℂ} (hc₁ : ‖c₁‖ ≤ 1)
    (hc₂ : ‖c₂‖ ≤ 1) :
    ∫ u, ‖polarCorrectedTest γ₀ (sinhTest a (1 / 4)) (sinhTestWeight a) (sinhTest a (1 / 2))
        c₁ c₂ u‖ ^ 2 ≤
      3 * ((∫ u, sinhTest a (1 / 4) u ^ 2) + (∫ u, sinhTestWeight a u ^ 2) +
        ∫ u, sinhTest a (1 / 2) u ^ 2) := by
  have hL2 := integral_norm_sq_polarCorrectedTest_le γ₀ (sinhTest_contDiff a (1 / 4))
    (sinhTestWeight_contDiff a) (sinhTest_contDiff a (1 / 2)) (sinhTest_supp ha.le)
    (sinhTestWeight_supp ha.le) (sinhTest_supp ha.le) c₁ c₂
  refine hL2.trans ?_
  have i1 : 0 ≤ ∫ u, sinhTestWeight a u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have i2 : 0 ≤ ∫ u, sinhTest a (1 / 2) u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have e1 : ‖c₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c₁]
  have e2 : ‖c₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c₂]
  have h1 := mul_le_mul_of_nonneg_right e1 i1
  have h2 := mul_le_mul_of_nonneg_right e2 i2
  nlinarith

/-- **The cluster configuration defeats every exponent.**  At every level `a ≥ 4` where the
deep-zero test `s = sinh(u/4)(a² - u²)₊^{5/2}` has `12288 (‖s‖₁ + ‖s''‖₁)² ≤ P²`,
`P = ∫ s(u) sinh(u/4)`, the relaxed Hodge index fails for every exponent `θ`: the pair of
multiplicity `k + 1` at height `e^{k+1}`, with `k P² > e^{θa} K₀`, gives a polar-constrained test
with `Re W < -e^{θa} ∫|f|²`. -/
theorem offLineClusterConfig_not_relaxed {a : ℝ} (ha : 4 ≤ a)
    (hbig : 12288 * testNorm (sinhTest a (1 / 4)) ^ 2 ≤
      (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u)) ^ 2) (θ : ℝ) :
    ¬ RelaxedHodgeIndexAtLevel offLineClusterConfig θ a := by
  intro hrel
  have ha0 : 0 < a := by linarith
  have hN0 : 0 ≤ testNorm (sinhTest a (1 / 4)) := testNorm_nonneg _
  have hPpos : 0 < ∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u) := lt_of_lt_of_le
    (by positivity) (sinhTest_energy_ge_exp (b := a) (δ := 1 / 4) ha (by norm_num) (by linarith))
  have hαb0 : 0 < a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ) := by positivity
  have hβb0 : 0 < deepZeroEnergyBound a (1 / 2) (a / 4) :=
    deepZeroEnergyBound_pos (by norm_num) (by positivity) (by linarith)
  have hQ0 : 0 ≤ polarCorrectionBound a 0 := polarCorrectionBound_nonneg ha0 0
  obtain ⟨k, hka, hkQ, hkα, hkβ, hkθ⟩ := exists_cluster_index a (polarCorrectionBound a 0)
    (Real.exp (a / 2) * (4 * testNorm (sinhTest a (1 / 4))))
    (a * (3 * a ^ 2 / 4) ^ (5 / 2 : ℝ)) (deepZeroEnergyBound a (1 / 2) (a / 4))
    (Real.exp (θ * a)) (3 * ((∫ u, sinhTest a (1 / 4) u ^ 2) + (∫ u, sinhTestWeight a u ^ 2) +
      ∫ u, sinhTest a (1 / 2) u ^ 2)) (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u))
  obtain ⟨_, hLk, hden⟩ := cluster_height_bounds k
  have hden0 : 0 < (1 + |Real.exp ((k : ℝ) + 1)|) ^ 2 := by positivity
  obtain ⟨c₁, c₂, hFc, hFs, hp, hm, hc₁, hc₂, hG⟩ :=
    exists_polarCorrected_sinhTest (δ := 1 / 4) ha0 (Real.exp ((k : ℝ) + 1))
  have hc₁1 : ‖c₁‖ ≤ 1 := hc₁.trans (coeff_le_one_of_lt hαb0 hden0 hden hkα)
  have hc₂1 : ‖c₂‖ ≤ 1 := hc₂.trans (coeff_le_one_of_lt hβb0 hden0 hden hkβ)
  have hPb0 := polarCorrectionBound_nonneg ha0 (Real.exp ((k : ℝ) + 1))
  have hPbk : polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) * k ≤ polarCorrectionBound a 0 := by
    rw [polarCorrectionBound_eq a (Real.exp ((k : ℝ) + 1)), div_mul_eq_mul_div,
      div_le_iff₀ hden0]
    exact mul_le_mul_of_nonneg_left hden hQ0
  have hEa := exp_mul_add_sq_le_one (Real.one_le_exp ha0.le) hPb0 hQ0 hPbk hkQ
  have hG0 : 0 ≤ ‖c₁‖ * testNorm (sinhTestWeight a) + ‖c₂‖ * testNorm (sinhTest a (1 / 2)) := by
    have := testNorm_nonneg (sinhTestWeight a); have := testNorm_nonneg (sinhTest a (1 / 2))
    positivity
  have hcost := polarCorrection_cost_le hN0 le_rfl hG0 hG hPb0
  have hL0 : 0 ≤ Real.log (|Real.exp ((k : ℝ) + 1)| + 3) :=
    (zero_le_one).trans (one_le_log_abs_add_three _)
  have hcostG := mul_le_mul_of_nonneg_left hcost
    (by positivity : (0 : ℝ) ≤ 768 * Real.exp a * 2 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3))
  have hcostG' : 768 * Real.exp a * 2 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) *
      (testNorm (sinhTest a (1 / 4)) ^ 2 * (polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) +
        polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) ^ 2)) ≤
      1536 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) * testNorm (sinhTest a (1 / 4)) ^ 2 := by
    have e : 768 * Real.exp a * 2 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) *
        (testNorm (sinhTest a (1 / 4)) ^ 2 * (polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) +
          polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) ^ 2)) =
        1536 * Real.log (|Real.exp ((k : ℝ) + 1)| + 3) * testNorm (sinhTest a (1 / 4)) ^ 2 *
          (Real.exp a * (polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) +
            polarCorrectionBound a (Real.exp ((k : ℝ) + 1)) ^ 2)) := by ring
    rw [e]
    exact mul_le_of_le_one_right (by positivity) hEa
  have hW := re_W_cluster_test_le ha0 (lt_of_lt_of_le hka le_rfl) c₁ c₂
  have hF₂ := integral_norm_sq_cluster_test_le (γ₀ := Real.exp ((k : ℝ) + 1)) ha0 hc₁1 hc₂1
  have hind := hrel _ hFc hFs hp hm
  have hkP : Real.exp (θ * a) * (3 * ((∫ u, sinhTest a (1 / 4) u ^ 2) +
      (∫ u, sinhTestWeight a u ^ 2) + ∫ u, sinhTest a (1 / 2) u ^ 2)) <
      k * (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u)) ^ 2 := by
    rwa [div_lt_iff₀ (by positivity)] at hkθ
  have hE0 : 0 ≤ Real.exp a / (1 + Real.exp a) := by positivity
  have hE1 : Real.exp a / (1 + Real.exp a) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  exact cluster_violation_arith (Nat.cast_nonneg k) hE0 (Real.exp_pos _).le le_rfl hW
    (hcostG.trans hcostG') hE1 hLk hbig hF₂ hind hkP

/-! ### All large levels -/

/-- `‖s‖₁ + ‖s''‖₁ ≤ 6 a⁶ e^{a/4}` for the deep-zero test at depth `¼`, `a ≥ 4`. -/
theorem testNorm_sinhTest_quarter_le {a : ℝ} (ha : 4 ≤ a) :
    testNorm (sinhTest a (1 / 4)) ≤ 6 * a ^ 6 * Real.exp (a / 4) := by
  have h := testNorm_sinhTest_le (a := a) (δ := 1 / 4) (by linarith) (by norm_num)
  have hc : Real.cosh (1 / 4 * a) ≤ Real.exp (a / 4) := by
    rw [show 1 / 4 * a = a / 4 by ring]; exact cosh_le_exp_self_of_nonneg (by linarith)
  have ha0 : 0 < a := by linarith
  have h4 : a ^ 4 ≤ a ^ 5 / 4 := by
    have : a ^ 5 = a ^ 4 * a := by ring
    rw [this]; nlinarith [pow_pos ha0 4]
  have h3 : a ^ 3 ≤ a ^ 5 / 16 := by
    have : a ^ 5 = a ^ 3 * a ^ 2 := by ring
    rw [this]; nlinarith [pow_pos ha0 3]
  have hpoly : a ^ 5 + (1 / 4) ^ 2 * a ^ 5 + 10 * (1 / 4) * a ^ 4 + 20 * a ^ 3 ≤ 3 * a ^ 5 := by
    nlinarith
  calc testNorm (sinhTest a (1 / 4))
      ≤ 2 * a * Real.cosh (1 / 4 * a) *
          (a ^ 5 + (1 / 4) ^ 2 * a ^ 5 + 10 * (1 / 4) * a ^ 4 + 20 * a ^ 3) := h
    _ ≤ 2 * a * Real.exp (a / 4) * (3 * a ^ 5) := by
        have : 0 ≤ a ^ 5 + (1 / 4) ^ 2 * a ^ 5 + 10 * (1 / 4) * a ^ 4 + 20 * a ^ 3 := by positivity
        gcongr
    _ = 6 * a ^ 6 * Real.exp (a / 4) := by ring

/-- The size condition of `offLineClusterConfig_not_relaxed` holds for all large levels. -/
theorem eventually_cluster_size :
    ∀ᶠ a in atTop, 4 ≤ a ∧ 12288 * testNorm (sinhTest a (1 / 4)) ^ 2 ≤
      (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u)) ^ 2 := by
  have ht := (Real.tendsto_exp_div_pow_atTop 8).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_ge_atTop 4, ht.eventually_ge_atTop (512 * 10 ^ 9)] with a ha hexp
  refine ⟨ha, ?_⟩
  simp only [Function.comp, id] at hexp
  have ha0 : 0 < a := by linarith
  have hN := testNorm_sinhTest_quarter_le ha
  have hN0 := testNorm_nonneg (sinhTest a (1 / 4))
  have hP := sinhTest_energy_ge_exp (b := a) (δ := 1 / 4) ha (by norm_num) (by linarith)
  have hP0 : 0 ≤ a ^ 2 * Real.exp (2 * (1 / 4 * (a - 2))) / 16 := by positivity
  have hexp' : 512 * 10 ^ 9 * (a / 2) ^ 8 ≤ Real.exp (a / 2) := by
    rwa [le_div_iff₀ (by positivity)] at hexp
  have he2 : Real.exp 2 ≤ 15 / 2 := (exp_numeric_bounds).2.2.2.2.1
  have hsplit : Real.exp (2 * (1 / 4 * (a - 2))) = Real.exp (a / 2) / Real.exp 1 := by
    rw [← Real.exp_sub]; congr 1; ring
  have hsplit2 : Real.exp (a / 4) ^ 2 = Real.exp (a / 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hea := Real.exp_pos (a / 2)
  -- `N² ≤ 36 a¹² e^{a/2}` and `P² ≥ a⁴ e^{a/2}/(256 e²)`
  have hN2 : testNorm (sinhTest a (1 / 4)) ^ 2 ≤ 36 * a ^ 12 * Real.exp (a / 2) := by
    calc testNorm (sinhTest a (1 / 4)) ^ 2 ≤ (6 * a ^ 6 * Real.exp (a / 4)) ^ 2 :=
          pow_le_pow_left₀ hN0 hN 2
      _ = 36 * a ^ 12 * Real.exp (a / 2) := by rw [mul_pow, hsplit2]; ring
  have hP2 : (a ^ 2 * (Real.exp (a / 2) / 3) / 16) ^ 2 ≤
      (∫ u, sinhTest a (1 / 4) u * Real.sinh (1 / 4 * u)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) (le_trans ?_ hP) 2
    rw [hsplit]
    gcongr
  have hbig : 12288 * (36 * a ^ 12 * Real.exp (a / 2)) ≤
      (a ^ 2 * (Real.exp (a / 2) / 3) / 16) ^ 2 := by
    have e : (a ^ 2 * (Real.exp (a / 2) / 3) / 16) ^ 2 =
        a ^ 4 * Real.exp (a / 2) * Real.exp (a / 2) / 2304 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    have h8 : (a / 2) ^ 8 = a ^ 8 / 256 := by ring
    rw [h8] at hexp'
    have hkey : 12288 * 36 * 2304 * a ^ 8 ≤ Real.exp (a / 2) := by nlinarith [pow_pos ha0 8]
    have ha12 : a ^ 12 = a ^ 8 * a ^ 4 := by ring
    rw [ha12]
    have h4 : 0 < a ^ 4 * Real.exp (a / 2) := by positivity
    nlinarith
  calc 12288 * testNorm (sinhTest a (1 / 4)) ^ 2 ≤ 12288 * (36 * a ^ 12 * Real.exp (a / 2)) := by
        linarith
    _ ≤ _ := hbig.trans hP2

/-- **Bounded off-line density is necessary.**  The cluster configuration has depth `¼` at every
zero, the ζ-type local count `N(t, t + 1] ≤ 2 log(|t| + 3)`, and no zeros below ordinate `2`, but
at every large level the relaxed Hodge index fails for every exponent `θ`. -/
theorem offLineClusterConfig_eventually_not_relaxed :
    ∀ᶠ a in atTop, ∀ θ : ℝ, ¬ RelaxedHodgeIndexAtLevel offLineClusterConfig θ a := by
  filter_upwards [eventually_cluster_size] with a ha θ
  exact offLineClusterConfig_not_relaxed ha.1 ha.2 θ

/-- No exponent is eventually admissible for the cluster configuration. -/
theorem offLineClusterConfig_no_eventual_exponent (θ : ℝ) :
    ¬ ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel offLineClusterConfig θ a := by
  intro h
  obtain ⟨a, h1, h2⟩ := (h.and offLineClusterConfig_eventually_not_relaxed).exists
  exact h2 θ h1

/-- At every large level the Weil form of the cluster configuration is unbounded below on the
polar-constrained `C²` tests supported in `[-a, a]`, although every zero has `|β - ½| = ¼`. -/
theorem offLineClusterConfig_weil_unbounded_below :
    ∀ᶠ a in atTop, ∀ C : ℝ, ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
        (offLineClusterConfig.W f f).re < -(C * ∫ u, ‖f u‖ ^ 2) := by
  filter_upwards [offLineClusterConfig_eventually_not_relaxed, eventually_gt_atTop 0]
    with a ha ha0 C
  have h := ha (Real.log (max C 1) / a)
  unfold RelaxedHodgeIndexAtLevel at h
  push Not at h
  obtain ⟨f, hf, hs, hp, hm, hlt⟩ := h
  refine ⟨f, hf, hs, hp, hm, lt_of_lt_of_le hlt ?_⟩
  have he : Real.exp (Real.log (max C 1) / a * a) = max C 1 := by
    rw [div_mul_cancel₀ _ ha0.ne', Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))]
  rw [he]
  have hF : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := mul_le_mul_of_nonneg_right (le_max_left C 1) hF
  linarith

/-- **The off-line density hypothesis cannot be dropped** from
`abs_re_sub_half_le_iff_eventually_relaxed`: there is a configuration with the local count
`N(t, t + 1] ≤ 2 log(|t| + 3)`, no zeros below ordinate `2`, and `|β - ½| ≤ ¼` at every zero, for
which no exponent `θ` is eventually admissible. -/
theorem exists_bounded_depth_without_error_exponent :
    ∃ Z : ZeroConfig, (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3)) ∧
      (∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|) ∧ (∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ 1 / 4) ∧
      ∀ θ : ℝ, ¬ ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel Z θ a :=
  ⟨offLineClusterConfig, offLineClusterConfig_local_count, offLineClusterConfig_two_le_im,
    fun ρ hρ => (offLineClusterConfig_depth ρ hρ).le, offLineClusterConfig_no_eventual_exponent⟩

end RHTower
