import GaloisForLFunctions.RHTower.OffLineDensityWeilLowerBound
import GaloisForLFunctions.RHTower.RelaxedHodgeDepthDictionary

/-!
# The error exponent of the Weil form is twice the abscissa excess

The relaxed Hodge index with exponent `θ` at level `a` is
`Re W(f, f) ≥ -e^{θa} ∫|f|²` for polar-constrained `C²` tests supported in `[-a, a]`
(`RelaxedHodgeIndexAtLevel`).  For a zero configuration with local count
`N(t, t+1] ≤ A₀ log(|t| + 3)`, no zeros below ordinate `2`, and off-line multiplicity at most `D`
in every unit window, and for `η ≥ 0` (`abs_re_sub_half_le_iff_eventually_relaxed`):

> all zeros satisfy `|β - ½| ≤ η` if and only if the relaxed index holds for all large levels at
> every exponent `θ > 2η`.

Hence the infimum of the eventual error exponents is exactly `2 sup_ρ |β - ½|`.

* **Upper bound** (`eventually_relaxedHodgeIndex_of_depth`).  The converse bound
  `Re W ≥ -3500 (2a + 3) D e^{2η(a+2)} ∫|f|²` of `re_W_ge_of_depth_offLineDensity` has polynomial
  prefactor, which `e^{(θ - 2η)a}` eventually absorbs.
* **Lower bound** (`abs_re_sub_half_le_of_eventually_relaxed`).  The relaxed dictionary
  `relaxed_hodge_dictionary` confines every zero of height up to `exp(εa/(2·10⁴ A₀ log² a))` to
  `|β - ½| ≤ θ/2 + ε`, and for each fixed zero its size condition holds for all large `a`.
  This direction uses neither the depth bound nor the off-line density.

The depth that matters is the global one.  For every `T ≥ 2` the configuration whose only zeros
are `¾ + iT` and `¼ + iT` has no off-line zero below height `T`, and its eventual error exponent is
exactly `½` (`offLinePairConfig_eventually_relaxed_iff`).  So no hypothesis on the zeros up to a
fixed height controls the error exponent.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### The upper bound: depth `η` gives every exponent `θ > 2η` eventually -/

/-- The converse bound as a relaxed Hodge index. -/
theorem relaxedHodgeIndexAtLevel_of_depth_offLineDensity (Z : ZeroConfig) {η D θ a : ℝ}
    (hη0 : 0 ≤ η) (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (hD : OffLineDensityBound Z D)
    (ha : 0 ≤ a) (hθ : 3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) ≤ Real.exp (θ * a)) :
    RelaxedHodgeIndexAtLevel Z θ a := by
  intro f hf hsupp _ _
  have hfs : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hsupp (subset_tsupport f hu))
  have h := re_W_ge_of_depth_offLineDensity Z hη0 hη hD ha hf.continuous hfs
  have hF : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := mul_le_mul_of_nonneg_right hθ hF
  linarith

/-- For `θ > 2η` the polynomial factor `3500 (2a + 3) D e^{4η}` is eventually beaten by
`e^{(θ - 2η) a}`. -/
theorem eventually_depth_constant_le_exp {η D θ : ℝ} (hD : 0 ≤ D)
    (hθ : 2 * η < θ) :
    ∀ᶠ a in atTop, 3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) ≤ Real.exp (θ * a) := by
  set ε := θ - 2 * η with hε
  have hε0 : 0 < ε := by linarith
  set C := 3500 * D * Real.exp (4 * η) with hC
  have hC0 : 0 ≤ C := by positivity
  filter_upwards [eventually_ge_atTop (max 1 (10 * C / ε ^ 2))] with a ha
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have haC : 10 * C / ε ^ 2 ≤ a := (le_max_right _ _).trans ha
  have hq := Real.quadratic_le_exp_of_nonneg (x := ε * a) (by positivity)
  have hCa : 10 * C ≤ ε ^ 2 * a := by
    rw [div_le_iff₀ (by positivity)] at haC; linarith
  have hpoly : C * (2 * a + 3) ≤ Real.exp (ε * a) := by
    have h1 : C * (2 * a + 3) ≤ C * (5 * a) := mul_le_mul_of_nonneg_left (by linarith) hC0
    have h2 : C * (5 * a) ≤ (ε * a) ^ 2 / 2 := by nlinarith
    have h3 : 0 ≤ 1 + ε * a := by positivity
    linarith
  have hsplit : Real.exp (θ * a) = Real.exp (2 * η * a) * Real.exp (ε * a) := by
    rw [← Real.exp_add]; congr 1; rw [hε]; ring
  have hsplit' : Real.exp (2 * η * (a + 2)) = Real.exp (2 * η * a) * Real.exp (4 * η) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, hsplit']
  have hE := Real.exp_pos (2 * η * a)
  calc 3500 * (2 * a + 3) * D * (Real.exp (2 * η * a) * Real.exp (4 * η))
      = Real.exp (2 * η * a) * (C * (2 * a + 3)) := by rw [hC]; ring
    _ ≤ Real.exp (2 * η * a) * Real.exp (ε * a) := mul_le_mul_of_nonneg_left hpoly hE.le

/-- **Upper bound on the error exponent.**  Depth at most `η` and bounded off-line density give
the relaxed Hodge index at every exponent `θ > 2η` for all large levels. -/
theorem eventually_relaxedHodgeIndex_of_depth (Z : ZeroConfig) {η D θ : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (hD : OffLineDensityBound Z D)
    (hθ : 2 * η < θ) : ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel Z θ a := by
  filter_upwards [eventually_depth_constant_le_exp hD.nonneg hθ, eventually_ge_atTop 0]
    with a ha ha0
  exact relaxedHodgeIndexAtLevel_of_depth_offLineDensity Z hη0 hη hD ha0 ha

/-! ### The lower bound: an eventual exponent `θ` confines every zero to `|β - ½| ≤ θ/2` -/

theorem eventually_log_pow_le_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ a in atTop, Real.log a ^ n ≤ c * a := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [(tendsto_order.1 h).2 c hc, eventually_gt_atTop 0] with a ha ha0
  simp only [one_mul, add_zero] at ha
  rw [div_lt_iff₀ ha0] at ha
  exact ha.le

/-- The size condition of the relaxed dictionary holds for all large levels. -/
theorem eventually_relaxed_dictionary_size {A₀ ε y : ℝ} (hA₀ : 1 ≤ A₀) (hε : 0 < ε) :
    ∀ᶠ a in atTop, Real.exp 12 ≤ a ∧ 1 / ε ≤ a ∧
      10 ^ 4 * A₀ * (Real.log (|y| + 306) + Real.log a + 2 / ε + 2) * Real.log a ^ 2 ≤
        ε * a := by
  set L := Real.log (|y| + 306) + 2 / ε + 2 with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log (|y| + 306) := Real.log_nonneg (by linarith [abs_nonneg y])
    positivity
  have hK : 0 < 10 ^ 4 * A₀ := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp 12), eventually_ge_atTop (1 / ε),
    eventually_log_pow_le_mul 3 (c := ε / (2 * (10 ^ 4 * A₀))) (by positivity),
    eventually_log_pow_le_mul 2 (c := ε / (2 * (10 ^ 4 * A₀) * (L + 1))) (by positivity)]
    with a h12 hε' h3 h2
  refine ⟨h12, hε', ?_⟩
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith [Real.add_one_le_exp 12])
  have e : 10 ^ 4 * A₀ * (Real.log (|y| + 306) + Real.log a + 2 / ε + 2) * Real.log a ^ 2 =
      10 ^ 4 * A₀ * Real.log a ^ 3 + 10 ^ 4 * A₀ * L * Real.log a ^ 2 := by rw [hL]; ring
  rw [e]
  have h3' : 10 ^ 4 * A₀ * Real.log a ^ 3 ≤ ε * a / 2 := by
    have := mul_le_mul_of_nonneg_left h3 hK.le
    calc 10 ^ 4 * A₀ * Real.log a ^ 3 ≤ 10 ^ 4 * A₀ * (ε / (2 * (10 ^ 4 * A₀)) * a) := this
      _ = ε * a / 2 := by field_simp
  have h2' : 10 ^ 4 * A₀ * L * Real.log a ^ 2 ≤ ε * a / 2 := by
    have hla : 0 ≤ Real.log a ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 10 ^ 4 * A₀ * (L + 1))
    have h4 : 10 ^ 4 * A₀ * L * Real.log a ^ 2 ≤ 10 ^ 4 * A₀ * (L + 1) * Real.log a ^ 2 := by
      have : L ≤ L + 1 := by linarith
      gcongr
    calc 10 ^ 4 * A₀ * L * Real.log a ^ 2 ≤ 10 ^ 4 * A₀ * (L + 1) * Real.log a ^ 2 := h4
      _ ≤ 10 ^ 4 * A₀ * (L + 1) * (ε / (2 * (10 ^ 4 * A₀) * (L + 1)) * a) := this
      _ = ε * a / 2 := by field_simp
  linarith

/-- **Lower bound on the error exponent.**  If the relaxed Hodge index with exponent `θ` holds at
all large levels, every zero satisfies `|β - ½| ≤ θ/2`.  Only the local count and the absence of
zeros below ordinate `2` are used. -/
theorem abs_re_sub_half_le_of_eventually_relaxed (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|) {θ : ℝ} (hθ : 0 ≤ θ)
    (hev : ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel Z θ a) :
    ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ θ / 2 := by
  intro ρ hρ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, hrel, h12, haε, hsize⟩ :=
    (hev.and (eventually_relaxed_dictionary_size (y := ρ.im) hA₀ hε)).exists
  exact relaxed_hodge_dictionary Z hA₀ hloc hlow hθ hε h12 haε hrel hρ hsize

/-- **Error exponent = twice the abscissa excess.**  For a configuration with local count
`N(t, t+1] ≤ A₀ log(|t| + 3)`, no zeros below ordinate `2`, and off-line multiplicity at most `D`
in every unit window, and for `η ≥ 0`:

> every zero has `|β - ½| ≤ η` if and only if, for every `θ > 2η`, the relaxed Hodge index
> `Re W(f, f) ≥ -e^{θa} ∫|f|²` (polar-constrained `C²` tests on `[-a, a]`) holds for all large `a`.

So the infimum of the eventual error exponents is exactly `2 sup_ρ |β - ½|`. -/
theorem abs_re_sub_half_le_iff_eventually_relaxed (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|) {D : ℝ} (hD : OffLineDensityBound Z D) {η : ℝ}
    (hη0 : 0 ≤ η) :
    (∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) ↔
      ∀ θ : ℝ, 2 * η < θ → ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel Z θ a := by
  constructor
  · intro hη θ hθ
    exact eventually_relaxedHodgeIndex_of_depth Z hη0 hη hD hθ
  · intro hev ρ hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := abs_re_sub_half_le_of_eventually_relaxed Z hA₀ hloc hlow (by positivity)
      (hev (2 * η + 2 * ε) (by linarith)) ρ hρ
    linarith

/-- The relaxed index is monotone in the exponent. -/
theorem relaxedHodgeIndexAtLevel_mono {Z : ZeroConfig} {θ θ' a : ℝ} (hθ : θ ≤ θ') (ha : 0 ≤ a)
    (h : RelaxedHodgeIndexAtLevel Z θ a) : RelaxedHodgeIndexAtLevel Z θ' a := by
  intro f hf hs h1 h2
  have hF : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have he : Real.exp (θ * a) ≤ Real.exp (θ' * a) := Real.exp_le_exp.mpr (by nlinarith)
  have := mul_le_mul_of_nonneg_right he hF
  linarith [h f hf hs h1 h2]

/-! ### One off-line pair at an arbitrary height -/

/-- The pair `{¾ + iT, ¼ + iT}`, both simple. -/
def offLinePairConfig (T : ℝ) : ZeroConfig where
  carrier := {⟨3 / 4, T⟩, ⟨1 / 4, T⟩}
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ (rfl | rfl) <;> constructor <;> norm_num
  reflect_mem := by
    rintro ρ (rfl | rfl)
    · right; apply Complex.ext <;> norm_num [reflect]
    · left; apply Complex.ext <;> norm_num [reflect]
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Set.toFinite _).subset Set.inter_subset_left

theorem offLinePairConfig_N_le (T t : ℝ) : ((offLinePairConfig T).N t (t + 1) : ℝ) ≤ 2 := by
  have hN : (offLinePairConfig T).N t (t + 1) = ((offLinePairConfig T).window t (t + 1)).ncard := by
    unfold ZeroConfig.N
    exact finsum_one
  have hc : (offLinePairConfig T).carrier = {⟨3 / 4, T⟩, ⟨1 / 4, T⟩} := rfl
  have h : ((offLinePairConfig T).window t (t + 1)).ncard ≤ 2 := by
    have hsub : (offLinePairConfig T).window t (t + 1) ⊆ ({⟨3 / 4, T⟩, ⟨1 / 4, T⟩} : Set ℂ) := by
      rw [← hc]; exact Set.inter_subset_left
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  rw [hN]
  exact_mod_cast h

theorem offLinePairConfig_local_count (T t : ℝ) :
    ((offLinePairConfig T).N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3) := by
  have := one_le_log_abs_add_three t
  linarith [offLinePairConfig_N_le T t]

theorem offLinePairConfig_depth (T : ℝ) :
    ∀ ρ ∈ (offLinePairConfig T).carrier, |ρ.re - 1 / 2| = 1 / 4 := by
  rintro ρ (rfl | rfl) <;> norm_num [abs_of_pos, abs_of_neg]

/-- **Depth is seen at every height.**  For every `T ≥ 2`, the configuration whose only zeros are
`¾ + iT` and `¼ + iT` (so no off-line zero below height `T`) has eventual error exponent exactly
`½`: the relaxed index holds for all large levels at every `θ > ½`, and at no `θ < ½`. -/
theorem offLinePairConfig_eventually_relaxed_iff {T : ℝ} (hT : 2 ≤ T) {θ : ℝ} (hθ : θ ≠ 1 / 2) :
    (∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel (offLinePairConfig T) θ a) ↔ 1 / 2 < θ := by
  have hD : OffLineDensityBound (offLinePairConfig T) 2 :=
    offLineDensityBound_of_count _ (offLinePairConfig_N_le T)
  have hη : ∀ ρ ∈ (offLinePairConfig T).carrier, |ρ.re - 1 / 2| ≤ 1 / 4 := fun ρ hρ =>
    (offLinePairConfig_depth T ρ hρ).le
  have hlow : ∀ ρ ∈ (offLinePairConfig T).carrier, 2 ≤ |ρ.im| := by
    rintro ρ (rfl | rfl) <;> simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] using hT
  constructor
  · intro hev
    by_contra hle
    push Not at hle
    have hlt : θ < 1 / 2 := lt_of_le_of_ne hle hθ
    have hev' : ∀ᶠ a in atTop, RelaxedHodgeIndexAtLevel (offLinePairConfig T) (max θ 0) a := by
      filter_upwards [hev, eventually_ge_atTop 0] with a ha ha0
      exact relaxedHodgeIndexAtLevel_mono (le_max_left θ 0) ha0 ha
    have h := abs_re_sub_half_le_of_eventually_relaxed (offLinePairConfig T) (by norm_num)
      (offLinePairConfig_local_count T) hlow (le_max_right θ 0) hev' ⟨3 / 4, T⟩ (Or.inl rfl)
    rw [offLinePairConfig_depth T _ (Or.inl rfl)] at h
    have : max θ 0 < 1 / 2 := max_lt hlt (by norm_num)
    linarith
  · intro hgt
    exact eventually_relaxedHodgeIndex_of_depth _ (by norm_num) hη hD (by linarith)

end RHTower
