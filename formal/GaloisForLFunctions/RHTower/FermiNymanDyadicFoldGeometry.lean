import GaloisForLFunctions.RHTower.FermiNymanWitnessGermLaws

/-!
# Dyadic fold geometry of the alternating Nyman–Beurling system

For `f` on `(0,1]` the dyadic fold is `(Pf)(u) = Σ_{j≥0} 2^{−j} f(2^{−j}u)`, read on the top octave
`(1/2, 1]`.  It is the adjoint of the self-similar extension: for every square-integrable `f` and
every a.e. dyadically self-similar square-integrable `w`,

`∫_0^1 f(t) w̄(t) dt = ∫_{1/2}^1 (Pf)(u) w̄(u) du`.

The fold of the alternating generator `φ_a(t) = {1/(at)} − 2{1/(2at)}`, `a ≥ 1`, is the single
function `−1/(au)`: the terms `2^{−j}({2^j y} − 2{2^{j−1} y})`, `y = 1/(au) ∈ (0, 2)`, telescope to
`−2{y/2} = −y`.  The fold of the dyadic Haar target is `0`, and the fold of a self-similar function
is twice its top-octave restriction.

Consequences.

* A measurable square-integrable a.e. self-similar function pairs with `φ_a` to
  `−a⁻¹ · conj(∫_{1/2}^1 w(u) du/u)`; it is a witness of the system iff its top-octave logarithmic
  mean vanishes.  This is the bounded-witness classification without continuity or boundedness.
* **RH ⟺ every fold-free square-integrable function (`Pf = 0` a.e. on `(1/2,1]`) is an
  `L²(0,1]`-limit of finite generator combinations.**  Under RH every witness is a.e. self-similar,
  so a fold-free `f` is orthogonal to the witness space, which is the annihilator of the generator
  span; conversely the Haar target is fold-free.
* **Harmonic penalty.**  For every finite combination and every a.e. self-similar `w`,
  `|∫_{1/2}^1 (Pf) w̄ + (Σ_j c_j/a_j) · conj(∫_{1/2}^1 w/u)|² ≤ (∫_0^1 |w|²)(∫_0^1 |f − Σ_j c_j φ_{a_j}|²)`.
  With `w` the self-similar extension of `1/u` and `f` the Haar target,
  `∫_0^1 |h − Σ_j c_j φ_{a_j}|² ≥ ½ |Σ_j c_j/a_j|²`: no approximant of the Haar target can
  outrun its harmonic coefficient sum.

In Hilbert-space terms `L²(0,1] = ker P ⊕ 𝓢` with `𝓢` the self-similar functions; the generator
family has the one-dimensional self-similar shadow `−1/(au)`, the Haar target lies in `ker P`, and
the Riemann hypothesis is the density of the fold-free parts of the generators in `ker P`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry

/-! ## The dyadic fold and the dyadic shells -/

/-- The dyadic fold `(Pf)(u) = Σ_{j≥0} 2^{−j} f(2^{−j} u)`. -/
def dyadicFold (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' j : ℕ, (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * f ((1 / 2 : ℝ) ^ j * u)

/-- The `j`-th dyadic shell `(2^{−j−1}, 2^{−j}]`. -/
def dyadicShell (j : ℕ) : Set ℝ := Ioc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j)

theorem measurableSet_dyadicShell (j : ℕ) : MeasurableSet (dyadicShell j) := measurableSet_Ioc

theorem half_pow_succ_lt (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) < (1 / 2 : ℝ) ^ j := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos (by norm_num) j) (by norm_num)

theorem pairwise_disjoint_dyadicShell :
    Pairwise fun j k : ℕ => Disjoint (dyadicShell j) (dyadicShell k) := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · refine Set.disjoint_left.2 fun t ht ht' => ?_
    have h1 : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    exact absurd (ht'.2.trans h1) (not_le.2 ht.1)
  · refine Set.disjoint_left.2 fun t ht ht' => ?_
    have h1 : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    exact absurd (ht.2.trans h1) (not_le.2 ht'.1)

theorem iUnion_dyadicShell : (⋃ j, dyadicShell j) = Ioc (0 : ℝ) 1 := by
  ext t
  simp only [mem_iUnion, dyadicShell, mem_Ioc]
  constructor
  · rintro ⟨j, h1, h2⟩
    exact ⟨lt_trans (pow_pos (by norm_num) _) h1,
      h2.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near_of_lt_one h0 h1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, hn0, hn1⟩

/-- Shell substitution: `∫_{2^{−j−1}}^{2^{−j}} F(t) dt = 2^{−j} ∫_{1/2}^1 F(2^{−j} u) du`. -/
theorem setIntegral_dyadicShell_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (j : ℕ) :
    (∫ t in dyadicShell j, F t) =
      ((1 / 2 : ℝ) ^ j) • ∫ u in Ioc (1 / 2 : ℝ) 1, F ((1 / 2 : ℝ) ^ j * u) := by
  have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) j
  rw [dyadicShell, ← intervalIntegral.integral_of_le (half_pow_succ_lt j).le,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h := intervalIntegral.integral_comp_mul_left (a := 1 / 2) (b := 1) F hc.ne'
  rw [mul_one, show (1 / 2 : ℝ) ^ j * (1 / 2) = (1 / 2 : ℝ) ^ (j + 1) by rw [pow_succ]] at h
  rw [h, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- Transport of an a.e. statement along `u ↦ c u`, `c ≠ 0`. -/
theorem ae_comp_mul_left {p : ℝ → Prop} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ᵐ x ∂(volume : Measure ℝ), p x) : ∀ᵐ u ∂(volume : Measure ℝ), p (c * u) := by
  rw [ae_iff] at h ⊢
  have : {u : ℝ | ¬ p (c * u)} = (fun x => c * x) ⁻¹' {x | ¬ p x} := rfl
  rw [this, Real.volume_preimage_mul_left hc, h, mul_zero]

/-- a.e. dyadic self-similarity on `(0,1]` iterates to every dyadic scale on the top octave. -/
theorem ae_selfSimilar_pow {w : ℝ → ℂ}
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) (j : ℕ) :
    ∀ᵐ u ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)), w ((1 / 2 : ℝ) ^ j * u) = w u := by
  induction j with
  | zero => exact Eventually.of_forall fun u => by simp
  | succ j ih =>
    rw [ae_restrict_iff' measurableSet_Ioc] at hs ih ⊢
    have hc : ((1 / 2 : ℝ) ^ j) ≠ 0 := (pow_pos (by norm_num) j).ne'
    have hs' := ae_comp_mul_left hc hs
    filter_upwards [hs', ih] with u hu hu' humem
    have hu0 : 0 < u := lt_trans (by norm_num) humem.1
    have hmem : (1 / 2 : ℝ) ^ j * u ∈ Ioc (0 : ℝ) 1 := by
      refine ⟨mul_pos (pow_pos (by norm_num) j) hu0, ?_⟩
      calc (1 / 2 : ℝ) ^ j * u ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) humem.2 hu0.le zero_le_one
        _ = 1 := one_mul 1
    calc w ((1 / 2 : ℝ) ^ (j + 1) * u) = w (((1 / 2 : ℝ) ^ j * u) / 2) := by
          congr 1; rw [pow_succ]; ring
      _ = w ((1 / 2 : ℝ) ^ j * u) := hu hmem
      _ = w u := hu' humem

/-! ## Folds of the generators, the Haar target and self-similar functions -/

theorem fract_half_telescoping (y : ℝ) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y) - 2 * (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y / 2) =
      (2 * (1 / 2 : ℝ) ^ (j + 1) * Int.fract (2 ^ (j + 1) * y / 2)) -
        (2 * (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y / 2)) := by
  have : (2 : ℝ) ^ (j + 1) * y / 2 = 2 ^ j * y := by rw [pow_succ]; ring
  rw [this, pow_succ]; ring

/-- **Fold of the alternating generator.**  For `a ≥ 1` and `u ∈ (1/2, 1]`,
`Σ_{j≥0} 2^{−j} φ_a(2^{−j} u) = −1/(au)`. -/
theorem hasSum_dyadicFold_fermiNymanGen {a u : ℝ} (ha : 1 ≤ a) (hu : u ∈ Ioc (1 / 2 : ℝ) 1) :
    HasSum (fun j : ℕ => (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * fermiNymanGen a ((1 / 2 : ℝ) ^ j * u))
      (-(((a * u)⁻¹ : ℝ) : ℂ)) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hau : 1 / 2 < a * u := by
    calc 1 / 2 < u := hu.1
      _ = 1 * u := (one_mul u).symm
      _ ≤ a * u := mul_le_mul_of_nonneg_right ha hu0.le
  set y : ℝ := (a * u)⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 (by linarith)
  have hy2 : y < 2 := by
    rw [hy, inv_lt_comm₀ (by linarith) (by norm_num)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    exact hau
  set H : ℕ → ℝ := fun j => 2 * (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y / 2) with hH
  have hterm : ∀ j : ℕ, (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * fermiNymanGen a ((1 / 2 : ℝ) ^ j * u) =
      ((H (j + 1) - H j : ℝ) : ℂ) := by
    intro j
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) j
    have h1 : 1 / (a * ((1 / 2 : ℝ) ^ j * u)) = 2 ^ j * y := by
      rw [hy, one_div_pow]; field_simp
    have h2 : 1 / (2 * a * ((1 / 2 : ℝ) ^ j * u)) = 2 ^ j * y / 2 := by
      rw [hy, one_div_pow]; field_simp
    have h3 : (H (j + 1) - H j : ℝ) =
        (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y) - 2 * (1 / 2 : ℝ) ^ j * Int.fract (2 ^ j * y / 2) :=
      (fract_half_telescoping y j).symm
    rw [h3]
    simp only [fermiNymanGen, nymanGen, h1, h2]
    push_cast
    ring
  have hH0 : H 0 = y := by
    simp only [hH, pow_zero, mul_one, one_mul]
    rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    ring
  have hHbound : ∀ j, |H j| ≤ 2 * (1 / 2 : ℝ) ^ j := by
    intro j
    simp only [hH]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ j),
      abs_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_right (by positivity) (Int.fract_lt_one _).le
  have htend : Tendsto H atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun j => 2 * (1 / 2 : ℝ) ^ j) (fun j => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hHbound j
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      simpa using this
  have hsumR : HasSum (fun j => H (j + 1) - H j) (-y) := by
    have hsummable : Summable fun j => ‖H (j + 1) - H j‖ := by
      refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
        (summable_geometric_two.mul_left 3)
      rw [Real.norm_eq_abs]
      calc |H (j + 1) - H j| ≤ |H (j + 1)| + |H j| := abs_sub _ _
        _ ≤ 2 * (1 / 2 : ℝ) ^ (j + 1) + 2 * (1 / 2 : ℝ) ^ j := add_le_add (hHbound _) (hHbound _)
        _ ≤ 3 * (1 / 2 : ℝ) ^ j := by
          rw [pow_succ]; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j]
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsummable]
    simp only [Finset.sum_range_sub, hH0]
    have := htend.sub_const y
    simpa using this
  have hfun : (fun j : ℕ => (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * fermiNymanGen a ((1 / 2 : ℝ) ^ j * u)) =
      fun j => ((H (j + 1) - H j : ℝ) : ℂ) := funext hterm
  rw [hfun, show (-(((a * u)⁻¹ : ℝ) : ℂ)) = (((-y : ℝ)) : ℂ) by rw [hy]; push_cast; ring]
  exact Complex.hasSum_ofReal.2 hsumR

/-- **Fold of the dyadic Haar target is zero** on the top octave. -/
theorem hasSum_dyadicFold_dyadicHaar {u : ℝ} (hu : u ∈ Ioc (1 / 2 : ℝ) 1) :
    HasSum (fun j : ℕ => (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * dyadicHaar ((1 / 2 : ℝ) ^ j * u)) 0 := by
  have hterm : ∀ j : ℕ, (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * dyadicHaar ((1 / 2 : ℝ) ^ j * u) =
      (((if j = 0 then (2 : ℝ) else 0) - (1 / 2 : ℝ) ^ j : ℝ) : ℂ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [pow_zero, one_mul, Complex.ofReal_one, dyadicHaar, if_neg (not_le.2 hu.1)]
      norm_num
    · have hle : (1 / 2 : ℝ) ^ j * u ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ j * u ≤ (1 / 2 : ℝ) ^ 1 * 1 :=
              mul_le_mul (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hu.2
                (by linarith [hu.1]) (by norm_num)
          _ = 1 / 2 := by norm_num
      have hj0 : j ≠ 0 := hj.ne'
      simp only [dyadicHaar, if_pos hle, if_neg hj0]
      push_cast
      ring
  have hfun : (fun j : ℕ => (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * dyadicHaar ((1 / 2 : ℝ) ^ j * u)) =
      fun j => (((if j = 0 then (2 : ℝ) else 0) - (1 / 2 : ℝ) ^ j : ℝ) : ℂ) := funext hterm
  rw [hfun]
  have h1 : HasSum (fun j : ℕ => (if j = 0 then (2 : ℝ) else 0) - (1 / 2 : ℝ) ^ j) 0 := by
    have := (hasSum_ite_eq (0 : ℕ) (2 : ℝ)).sub hasSum_geometric_two
    simpa using this
  have := Complex.hasSum_ofReal.2 h1
  simpa using this

/-- **Fold of a self-similar function** is twice its top-octave value. -/
theorem hasSum_dyadicFold_of_selfSimilar {w : ℝ → ℂ} (hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t)
    {u : ℝ} (hu : u ∈ Ioc (1 / 2 : ℝ) 1) :
    HasSum (fun j : ℕ => (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * w ((1 / 2 : ℝ) ^ j * u)) (2 * w u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have hpow : ∀ j : ℕ, w ((1 / 2 : ℝ) ^ j * u) = w u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hmem : (1 / 2 : ℝ) ^ j * u ∈ Ioc (0 : ℝ) 1 := by
        refine ⟨mul_pos (pow_pos (by norm_num) j) hu0, ?_⟩
        calc (1 / 2 : ℝ) ^ j * u ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) hu.2 hu0.le zero_le_one
          _ = 1 := one_mul 1
      rw [← ih, ← hs _ hmem]
      congr 1; rw [pow_succ]; ring
  simp_rw [hpow]
  have h := (Complex.hasSum_ofReal.2 hasSum_geometric_two).mul_right (w u)
  simpa using h

/-- For an a.e. self-similar function the fold is a.e. twice the function on the top octave. -/
theorem dyadicFold_ae_eq_of_ae_selfSimilar {w : ℝ → ℂ}
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) :
    ∀ᵐ u ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)), dyadicFold w u = 2 * w u := by
  have hall := ae_all_iff.2 (ae_selfSimilar_pow hs)
  filter_upwards [hall] with u hu
  unfold dyadicFold
  simp_rw [hu]
  have h := (Complex.hasSum_ofReal.2 hasSum_geometric_two).mul_right (w u)
  rw [h.tsum_eq]
  push_cast
  ring

/-! ## The fold pairing identity -/

/-- Square-integrable functions pair integrably: `‖f w̄‖ ≤ (‖f‖² + ‖w‖²)/2`. -/
theorem integrableOn_mul_conj_of_sq {f w : ℝ → ℂ} (hf : Measurable f) (hw : Measurable w)
    {S : Set ℝ} (hfs : IntegrableOn (fun t => ‖f t‖ ^ 2) S)
    (hws : IntegrableOn (fun t => ‖w t‖ ^ 2) S) :
    IntegrableOn (fun t => f t * (starRingEnd ℂ) (w t)) S := by
  refine ((hfs.add hws).div_const 2).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (hf.mul (Complex.continuous_conj.measurable.comp hw)).aestronglyMeasurable
  · simp only [Pi.add_apply]
    rw [norm_mul, Complex.norm_conj]
    nlinarith [two_mul_le_add_sq ‖f t‖ ‖w t‖]

/-- Transport of square-integrability to the top octave along `u ↦ 2^{−j} u`. -/
theorem integrableOn_sq_comp_half_pow {f : ℝ → ℂ}
    (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1)) (j : ℕ) :
    IntegrableOn (fun u => ‖f ((1 / 2 : ℝ) ^ j * u)‖ ^ 2) (Ioc (1 / 2 : ℝ) 1) := by
  have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) j
  have hsub : dyadicShell j ⊆ Ioc 0 1 := by
    rw [← iUnion_dyadicShell]; exact subset_iUnion _ j
  have h1 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume ((1 / 2 : ℝ) ^ (j + 1))
      ((1 / 2 : ℝ) ^ j) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (half_pow_succ_lt j).le).2 (hf.mono_set hsub)
  have h2 := h1.comp_mul_left (c := (1 / 2 : ℝ) ^ j)
  have e0 : (1 / 2 : ℝ) ^ (j + 1) / (1 / 2 : ℝ) ^ j = 1 / 2 := by
    rw [pow_succ]; field_simp
  have e1 : (1 / 2 : ℝ) ^ j / (1 / 2 : ℝ) ^ j = 1 := div_self hc.ne'
  rw [e0, e1, intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h2
  exact h2

/-- **Fold pairing identity.**  For square-integrable `f` and a.e. self-similar square-integrable
`w`, `∫_0^1 f w̄ = ∫_{1/2}^1 (Pf) w̄`. -/
theorem integral_mul_conj_eq_integral_dyadicFold {f w : ℝ → ℂ} (hfm : Measurable f)
    (hwm : Measurable w) (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1))
    (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) :
    (∫ t in Ioc (0 : ℝ) 1, f t * (starRingEnd ℂ) (w t)) =
      ∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold f u * (starRingEnd ℂ) (w u) := by
  set F : ℝ → ℂ := fun t => f t * (starRingEnd ℂ) (w t) with hF
  have hFint : IntegrableOn F (Ioc 0 1) := integrableOn_mul_conj_of_sq hfm hwm hf hw
  have hNint : IntegrableOn (fun t => ‖f t‖ * ‖w t‖) (Ioc 0 1) := by
    have hn : IntegrableOn (fun t => ‖F t‖) (Ioc 0 1) := hFint.norm
    refine hn.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [hF, norm_mul, Complex.norm_conj]
  have hdecomp : (∫ t in Ioc (0 : ℝ) 1, F t) = ∑' j, ∫ t in dyadicShell j, F t := by
    rw [← iUnion_dyadicShell]
    exact integral_iUnion measurableSet_dyadicShell pairwise_disjoint_dyadicShell
      (by rw [iUnion_dyadicShell]; exact hFint)
  set G : ℕ → ℝ → ℂ := fun j u =>
    (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * f ((1 / 2 : ℝ) ^ j * u) * (starRingEnd ℂ) (w u) with hG
  have hshell : ∀ j, (∫ t in dyadicShell j, F t) = ∫ u in Ioc (1 / 2 : ℝ) 1, G j u := by
    intro j
    rw [setIntegral_dyadicShell_eq F j, ← integral_smul]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 (ae_selfSimilar_pow hs j)
    filter_upwards [this] with u hu humem
    simp only [hF, hG, hu humem, Complex.real_smul]
    ring
  have hGint : ∀ j, Integrable (G j) (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
    intro j
    have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) j
    have hfj := integrableOn_sq_comp_half_pow hf j
    have hwj : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc (1 / 2 : ℝ) 1) :=
      hw.mono_set (Ioc_subset_Ioc_left (by norm_num))
    refine (((hfj.add hwj).div_const 2).const_mul ((1 / 2 : ℝ) ^ j)).mono' ?_
      (Eventually.of_forall fun u => ?_)
    · exact ((measurable_const.mul (hfm.comp (measurable_const_mul _))).mul
        (Complex.continuous_conj.measurable.comp hwm)).aestronglyMeasurable
    · simp only [hG, Pi.add_apply, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hc]
      have h2 := two_mul_le_add_sq ‖f ((1 / 2 : ℝ) ^ j * u)‖ ‖w u‖
      calc (1 / 2 : ℝ) ^ j * ‖f ((1 / 2 : ℝ) ^ j * u)‖ * ‖w u‖
          = (1 / 2 : ℝ) ^ j * (‖f ((1 / 2 : ℝ) ^ j * u)‖ * ‖w u‖) := by ring
        _ ≤ (1 / 2 : ℝ) ^ j * ((‖f ((1 / 2 : ℝ) ^ j * u)‖ ^ 2 + ‖w u‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hnorm : ∀ j, (∫ u in Ioc (1 / 2 : ℝ) 1, ‖G j u‖) =
      ∫ t in dyadicShell j, ‖f t‖ * ‖w t‖ := by
    intro j
    have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) j
    rw [setIntegral_dyadicShell_eq (fun t => ‖f t‖ * ‖w t‖) j, ← integral_smul]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 (ae_selfSimilar_pow hs j)
    filter_upwards [this] with u hu humem
    simp only [hG, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, hu humem, smul_eq_mul]
    ring
  have hsum : Summable fun j => ∫ u in Ioc (1 / 2 : ℝ) 1, ‖G j u‖ := by
    simp_rw [hnorm]
    refine (hasSum_integral_iUnion measurableSet_dyadicShell pairwise_disjoint_dyadicShell
      ?_).summable
    rw [iUnion_dyadicShell]; exact hNint
  rw [hdecomp]
  simp_rw [hshell]
  rw [integral_tsum_of_summable_integral_norm hGint hsum]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  simp only [hG, dyadicFold]
  rw [tsum_mul_right]

/-! ## Generators and the Haar target against self-similar functions -/

theorem integrableOn_normSq_fermiNymanGen (a : ℝ) :
    IntegrableOn (fun t => ‖fermiNymanGen a t‖ ^ 2) (Ioc 0 1) :=
  (memLp_two_iff_integrable_sq_norm (measurable_fermiNymanGen a).aestronglyMeasurable).mp
    (memLp_fermiNymanGen_Ioc a)

theorem integrableOn_normSq_dyadicHaar :
    IntegrableOn (fun t => ‖dyadicHaar t‖ ^ 2) (Ioc 0 1) :=
  (memLp_two_iff_integrable_sq_norm measurable_dyadicHaar.aestronglyMeasurable).mp
    memLp_dyadicHaar_Ioc

/-- **Every generator reads the logarithmic mean of an a.e. self-similar function**:
`∫_0^1 φ_a w̄ = −a⁻¹ · conj(∫_{1/2}^1 w(u) du/u)`. -/
theorem integral_fermiNymanGen_mul_conj_of_ae_selfSimilar {w : ℝ → ℂ} (hwm : Measurable w)
    (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w t)) =
      -((a : ℂ)⁻¹) * (starRingEnd ℂ) (dyadicLogMean w) := by
  rw [integral_mul_conj_eq_integral_dyadicFold (measurable_fermiNymanGen a) hwm
    (integrableOn_normSq_fermiNymanGen a) hw hs]
  have hfold : ∀ u ∈ Ioc (1 / 2 : ℝ) 1,
      dyadicFold (fermiNymanGen a) u = -(((a * u)⁻¹ : ℝ) : ℂ) :=
    fun u hu => (hasSum_dyadicFold_fermiNymanGen ha hu).tsum_eq
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => by rw [hfold u hu]),
    dyadicLogMean, ← integral_conj, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  push_cast
  ring

/-- An a.e. self-similar square-integrable function is a witness iff its top-octave logarithmic
mean vanishes: the spurious witnesses are exactly the self-similar functions of zero
logarithmic mean, without any continuity or boundedness. -/
theorem isL2FermiWitness_iff_dyadicLogMean_eq_zero_of_ae_selfSimilar {w : ℝ → ℂ}
    (hwm : Measurable w) (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) :
    IsL2FermiWitness w ↔ dyadicLogMean w = 0 := by
  constructor
  · intro hwit
    have h := hwit.orth 1 le_rfl
    rw [integral_fermiNymanGen_mul_conj_of_ae_selfSimilar hwm hw hs le_rfl] at h
    simpa using h
  · intro hL
    refine ⟨hwm, hw, fun a ha => ?_⟩
    rw [integral_fermiNymanGen_mul_conj_of_ae_selfSimilar hwm hw hs ha, hL, map_zero, mul_zero]

/-- The Haar target is orthogonal to every a.e. self-similar square-integrable function. -/
theorem integral_dyadicHaar_mul_conj_of_ae_selfSimilar {w : ℝ → ℂ} (hwm : Measurable w)
    (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)) = 0 := by
  rw [integral_mul_conj_eq_integral_dyadicFold measurable_dyadicHaar hwm
    integrableOn_normSq_dyadicHaar hw hs]
  refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
  simp only [dyadicFold, (hasSum_dyadicFold_dyadicHaar hu).tsum_eq, zero_mul]

/-! ## Fold-free functions and the Riemann hypothesis -/

/-- A square-integrable function orthogonal to every square-integrable witness is an `L²`-limit of
finite generator combinations. -/
theorem exists_fermiNymanCombination_approx_of_orth_witness {f : ℝ → ℂ} (hfm : Measurable f)
    (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1))
    (horth : ∀ w : ℝ → ℂ, IsL2FermiWitness w →
      ∫ t in Ioc (0 : ℝ) 1, f t * (starRingEnd ℂ) (w t) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
      (∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  have hmem : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mpr hf
  set fLp : Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)) := hmem.toLp f with hfLp
  have hclos : fLp ∈ closure (fermiGenSpan : Set (Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1)))) := by
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨w, hw, hae⟩ := exists_isL2FermiWitness_of_mem_orthogonal hu
    rw [L2.inner_def]
    have hh : (fLp : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := MemLp.coeFn_toLp _
    have hval : (∫ t, inner ℂ ((u : ℝ → ℂ) t) ((fLp : ℝ → ℂ) t)
        ∂(volume.restrict (Ioc (0 : ℝ) 1))) =
        ∫ t in Ioc (0 : ℝ) 1, f t * (starRingEnd ℂ) (w t) := by
      refine integral_congr_ae ?_
      filter_upwards [hh, hae] with t h1 h2
      rw [RCLike.inner_apply, h1, h2]
    rw [hval]
    exact horth w hw
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hclos (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hb
  choose a ha hga using fun i => (g i).2
  refine ⟨n, c, a, fun i => (ha i), ?_⟩
  have hb' : b = ∑ i ∈ Finset.univ, c i • fermiGenLp (a i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hga i]
  have hcomb : MemLp (fermiNymanCombination c a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    unfold fermiNymanCombination
    exact memLp_finsetSum Finset.univ (f := fun i => fun t => c i * fermiNymanGen (a i) t)
      (fun i _ => (memLp_fermiNymanGen_Ioc (a i)).const_mul (c i))
  have hdiff : MemLp (fun t => f t - fermiNymanCombination c a t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := hmem.sub hcomb
  have hnorm : dist fLp b = (eLpNorm (fun t => f t - fermiNymanCombination c a t)
      2 (volume.restrict (Ioc (0 : ℝ) 1))).toReal := by
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub fLp b, MemLp.coeFn_toLp hmem,
      coeFn_sum_smul_fermiGenLp c a Finset.univ] with t h1 h2 h3
    have h2' : (fLp : ℝ → ℂ) t = f t := h2
    rw [h1, Pi.sub_apply, h2', hb', h3]
    rfl
  rw [hnorm, hdiff.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)] at hdist
  have hint : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^ 2 :=
    integral_nonneg fun t => by positivity
  have h2 : ((∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^
      (2 : ℝ≥0∞).toReal) ^ (2 : ℝ≥0∞).toReal⁻¹) =
      Real.sqrt (∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [h2, Real.sqrt_lt_sqrt_iff hint] at hdist
  exact hdist

/-- The Haar target is fold-free on the top octave. -/
theorem dyadicFold_dyadicHaar {u : ℝ} (hu : u ∈ Ioc (1 / 2 : ℝ) 1) : dyadicFold dyadicHaar u = 0 :=
  (hasSum_dyadicFold_dyadicHaar hu).tsum_eq

/-- **RH ⟺ every fold-free square-integrable function is an `L²(0,1]`-limit of finite
generator combinations.** -/
theorem riemannHypothesis_iff_foldFree_approximable :
    RiemannHypothesis ↔
      ∀ f : ℝ → ℂ, Measurable f → IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1) →
        (∀ᵐ u ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)), dyadicFold f u = 0) →
        ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
          (∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  constructor
  · intro hRH f hfm hf hfold ε hε
    refine exists_fermiNymanCombination_approx_of_orth_witness hfm hf (fun w hw => ?_) hε
    have hs := hw.ae_selfSimilar_of_riemannHypothesis hRH
    rw [integral_mul_conj_eq_integral_dyadicFold hfm hw.measurable hf hw.sq hs]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfold] with u hu
    simp [hu]
  · intro h
    apply riemannHypothesis_of_dyadicHaar_approximable
    refine h dyadicHaar measurable_dyadicHaar integrableOn_normSq_dyadicHaar ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun u hu => dyadicFold_dyadicHaar hu

/-! ## The fold–Cauchy–Schwarz inequality -/

/-- Cauchy–Schwarz for the pairing of two square-integrable functions on `(0,1]`. -/
theorem norm_sq_integral_mul_conj_le_of_sq {g w : ℝ → ℂ} (hg : Measurable g) (hw : Measurable w)
    (hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioc 0 1))
    (hw2 : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)) :
    ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      (∫ t in Ioc (0 : ℝ) 1, ‖g t‖ ^ 2) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 := by
  have h1 : ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ≤
      ∫ t in Ioc (0 : ℝ) 1, ‖g t‖ * ‖w t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have h2 := sq_integral_mul_le (μ := volume.restrict (Ioc (0 : ℝ) 1)) (f := fun t => ‖g t‖)
    (g := fun t => ‖w t‖) hg.aestronglyMeasurable.norm hw.aestronglyMeasurable.norm hg2 hw2
  have h0 : 0 ≤ ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ := norm_nonneg _
  calc ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ^ 2
      ≤ (∫ t in Ioc (0 : ℝ) 1, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

theorem integrableOn_normSq_fermiNymanCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    IntegrableOn (fun t => ‖fermiNymanCombination c a t‖ ^ 2) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := (∑ j, ‖c j‖ * 3) ^ 2) measure_Ioc_lt_top.ne
    ((measurable_fermiNymanCombination c a).norm.pow_const 2 |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fermiNymanCombination_le c a t) 2

theorem integrableOn_normSq_sub {f g : ℝ → ℂ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1))
    (hg : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioc 0 1)) :
    IntegrableOn (fun t => ‖f t - g t‖ ^ 2) (Ioc 0 1) :=
  (memLp_two_iff_integrable_sq_norm (hfm.sub hgm).aestronglyMeasurable).mp
    (((memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mpr hf).sub
      ((memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).mpr hg))

/-- **Fold pairing of an approximation error.**  Against an a.e. self-similar `w`, the error
`f − Σ_j c_j φ_{a_j}` pairs to the fold pairing of `f` plus the harmonic coefficient sum times the
conjugate logarithmic mean of `w`. -/
theorem integral_sub_combination_mul_conj_of_ae_selfSimilar {f w : ℝ → ℂ} (hfm : Measurable f)
    (hwm : Measurable w) (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1))
    (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t)
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (ha : ∀ j, 1 ≤ a j) :
    (∫ t in Ioc (0 : ℝ) 1, (f t - fermiNymanCombination c a t) * (starRingEnd ℂ) (w t)) =
      (∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold f u * (starRingEnd ℂ) (w u)) +
        (∑ j, c j / (a j : ℂ)) * (starRingEnd ℂ) (dyadicLogMean w) := by
  have h1 : IntegrableOn (fun t => f t * (starRingEnd ℂ) (w t)) (Ioc 0 1) :=
    integrableOn_mul_conj_of_sq hfm hwm hf hw
  have h2 : IntegrableOn (fun t => fermiNymanCombination c a t * (starRingEnd ℂ) (w t))
      (Ioc 0 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanCombination c a) hwm
      (integrableOn_normSq_fermiNymanCombination c a) hw
  have hsplit : (fun t => (f t - fermiNymanCombination c a t) * (starRingEnd ℂ) (w t)) =
      fun t => f t * (starRingEnd ℂ) (w t) -
        fermiNymanCombination c a t * (starRingEnd ℂ) (w t) := by
    funext t; ring
  rw [hsplit, integral_sub h1 h2, integral_mul_conj_eq_integral_dyadicFold hfm hwm hf hw hs,
    sub_eq_add_neg]
  congr 1
  have hcomb : (fun t => fermiNymanCombination c a t * (starRingEnd ℂ) (w t)) =
      fun t => ∑ j, c j * (fermiNymanGen (a j) t * (starRingEnd ℂ) (w t)) := by
    funext t; unfold fermiNymanCombination; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hcomb, integral_finsetSum _ (fun j _ => (integrableOn_mul_conj_of_sq
    (measurable_fermiNymanGen _) hwm (integrableOn_normSq_fermiNymanGen _) hw).const_mul _)]
  simp_rw [integral_const_mul, integral_fermiNymanGen_mul_conj_of_ae_selfSimilar hwm hw hs (ha _)]
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Fold–Cauchy–Schwarz inequality.**  For every finite generator combination and every a.e.
self-similar square-integrable `w`,
`|∫_{1/2}^1 (Pf) w̄ + (Σ_j c_j/a_j) conj(∫_{1/2}^1 w/u)|² ≤ (∫_0^1 |f − Σ_j c_j φ_{a_j}|²)(∫_0^1 |w|²)`. -/
theorem norm_sq_fold_pairing_le {f w : ℝ → ℂ} (hfm : Measurable f)
    (hwm : Measurable w) (hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc 0 1))
    (hw : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t)
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (ha : ∀ j, 1 ≤ a j) :
    ‖(∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold f u * (starRingEnd ℂ) (w u)) +
        (∑ j, c j / (a j : ℂ)) * (starRingEnd ℂ) (dyadicLogMean w)‖ ^ 2 ≤
      (∫ t in Ioc (0 : ℝ) 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) *
        ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 := by
  rw [← integral_sub_combination_mul_conj_of_ae_selfSimilar hfm hwm hf hw hs c a ha]
  exact norm_sq_integral_mul_conj_le_of_sq (hfm.sub (measurable_fermiNymanCombination c a)) hwm
    (integrableOn_normSq_sub hfm (measurable_fermiNymanCombination c a) hf
      (integrableOn_normSq_fermiNymanCombination c a)) hw

/-! ## The self-similar extension and the harmonic penalty -/

/-- The dyadic shell index of `t ∈ (0,1]`: the `j` with `2^j t ∈ (1/2, 1]`. -/
def dyadicShellIndex (t : ℝ) : ℕ := ⌊Real.logb 2 t⁻¹⌋₊

/-- The self-similar extension of a top-octave profile `g`: `t ↦ g(2^{j(t)} t)`. -/
def selfSimilarExtension (g : ℝ → ℂ) (t : ℝ) : ℂ := g (2 ^ dyadicShellIndex t * t)

theorem measurable_dyadicShellIndex : Measurable dyadicShellIndex := by
  unfold dyadicShellIndex
  refine Nat.measurable_floor.comp ?_
  show Measurable fun t : ℝ => Real.log t⁻¹ / Real.log 2
  exact (Real.measurable_log.comp measurable_inv).div_const _

theorem measurable_selfSimilarExtension {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (selfSimilarExtension g) := by
  unfold selfSimilarExtension
  refine hg.comp (Measurable.mul ?_ measurable_id)
  exact (measurable_from_nat (f := fun j : ℕ => (2 : ℝ) ^ j)).comp measurable_dyadicShellIndex

/-- `2^{j(t)} t ∈ (1/2, 1]` for `t ∈ (0,1]`. -/
theorem two_pow_dyadicShellIndex_mul_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (2 : ℝ) ^ dyadicShellIndex t * t ∈ Ioc (1 / 2 : ℝ) 1 := by
  have hinv : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht.1, ht.2⟩
  have hpos : 0 < t⁻¹ := inv_pos.2 ht.1
  have hlog : 0 ≤ Real.logb 2 t⁻¹ := Real.logb_nonneg (by norm_num) hinv
  set j := dyadicShellIndex t with hj
  have h1 : (j : ℝ) ≤ Real.logb 2 t⁻¹ := Nat.floor_le hlog
  have h2 : Real.logb 2 t⁻¹ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast] at h1
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hpos] at h2
  have h2' : t⁻¹ < 2 ^ (j + 1) := by
    have : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast] at h2
    exact h2
  constructor
  · have := mul_lt_mul_of_pos_right h2' ht.1
    rw [inv_mul_cancel₀ ht.1.ne', pow_succ] at this
    linarith
  · have := mul_le_mul_of_nonneg_right h1 ht.1.le
    rwa [inv_mul_cancel₀ ht.1.ne'] at this

/-- On the top octave the shell index vanishes. -/
theorem dyadicShellIndex_eq_zero {u : ℝ} (hu : u ∈ Ioc (1 / 2 : ℝ) 1) : dyadicShellIndex u = 0 := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  unfold dyadicShellIndex
  rw [Nat.floor_eq_zero, Real.logb_lt_iff_lt_rpow (by norm_num) (inv_pos.2 hu0), Real.rpow_one,
    inv_lt_comm₀ hu0 (by norm_num)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact hu.1

theorem selfSimilarExtension_eq_of_mem {g : ℝ → ℂ} {u : ℝ} (hu : u ∈ Ioc (1 / 2 : ℝ) 1) :
    selfSimilarExtension g u = g u := by
  unfold selfSimilarExtension
  rw [dyadicShellIndex_eq_zero hu, pow_zero, one_mul]

/-- Halving the argument raises the shell index by one. -/
theorem dyadicShellIndex_half {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    dyadicShellIndex (t / 2) = dyadicShellIndex t + 1 := by
  have hinv : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht.1, ht.2⟩
  have hlog : 0 ≤ Real.logb 2 t⁻¹ := Real.logb_nonneg (by norm_num) hinv
  unfold dyadicShellIndex
  have : (t / 2)⁻¹ = t⁻¹ * 2 := by rw [inv_div]; ring
  rw [this, Real.logb_mul (inv_ne_zero ht.1.ne') (by norm_num), Real.logb_self_eq_one (by norm_num),
    Nat.floor_add_one hlog]

/-- The self-similar extension is dyadically self-similar on `(0,1]`. -/
theorem selfSimilarExtension_half {g : ℝ → ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    selfSimilarExtension g (t / 2) = selfSimilarExtension g t := by
  unfold selfSimilarExtension
  rw [dyadicShellIndex_half ht, pow_succ]
  congr 1; ring

theorem ae_selfSimilar_selfSimilarExtension (g : ℝ → ℂ) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      selfSimilarExtension g (t / 2) = selfSimilarExtension g t := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun t ht => selfSimilarExtension_half ht

/-- The canonical self-similar test `s₀ = selfSimilarExtension (u ↦ 1/u)`, bounded by `2`. -/
theorem norm_selfSimilarExtension_inv_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t‖ ≤ 2 := by
  unfold selfSimilarExtension
  have hmem := two_pow_dyadicShellIndex_mul_mem ht
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) hmem.1)]
  rw [inv_le_comm₀ (lt_trans (by norm_num) hmem.1) (by norm_num)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact hmem.1.le

theorem integrableOn_normSq_selfSimilarExtension_inv :
    IntegrableOn (fun t => ‖selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t‖ ^ 2) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 4) measure_Ioc_lt_top.ne
    ((measurable_selfSimilarExtension (Complex.measurable_ofReal.inv)).norm.pow_const 2
      |>.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := norm_selfSimilarExtension_inv_le ht
  nlinarith [norm_nonneg (selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t)]

/-- `∫_{1/2}^1 u^{−2} du = 1`. -/
theorem integral_Ioc_inv_sq : (∫ u in Ioc (1 / 2 : ℝ) 1, ((u : ℂ))⁻¹ * ((u : ℂ))⁻¹) = 1 := by
  have hcongr : ∀ u ∈ Ioc (1 / 2 : ℝ) 1, ((u : ℂ))⁻¹ * ((u : ℂ))⁻¹ = (u : ℂ) ^ (-2 : ℂ) := by
    intro u _
    rw [Complex.cpow_neg, Complex.cpow_ofNat, sq, mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    integral_cpow (Or.inr ⟨by norm_num, by rw [Set.mem_uIcc]; norm_num⟩),
    show (-2 : ℂ) + 1 = -1 by norm_num, Complex.cpow_neg_one, Complex.cpow_neg_one]
  push_cast
  norm_num

/-- The logarithmic mean of `s₀` is `1`. -/
theorem dyadicLogMean_selfSimilarExtension_inv :
    dyadicLogMean (selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)) = 1 := by
  unfold dyadicLogMean
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun u hu => by rw [selfSimilarExtension_eq_of_mem (g := fun u : ℝ => ((u : ℂ))⁻¹) hu])]
  exact integral_Ioc_inv_sq

/-- `∫_0^1 |s₀|² = 2`. -/
theorem integral_normSq_selfSimilarExtension_inv :
    (∫ t in Ioc (0 : ℝ) 1, ‖selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t‖ ^ 2) = 2 := by
  set s₀ := selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) with hs₀
  have hm : Measurable s₀ := measurable_selfSimilarExtension Complex.measurable_ofReal.inv
  have hsq := integrableOn_normSq_selfSimilarExtension_inv
  have hss := ae_selfSimilar_selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)
  have h := integral_mul_conj_eq_integral_dyadicFold hm hm hsq hsq hss
  have hfold := dyadicFold_ae_eq_of_ae_selfSimilar hss
  have hL : (∫ t in Ioc (0 : ℝ) 1, s₀ t * (starRingEnd ℂ) (s₀ t)) =
      ((∫ t in Ioc (0 : ℝ) 1, ‖s₀ t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show s₀ t * (starRingEnd ℂ) (s₀ t) = ((‖s₀ t‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : (∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold s₀ u * (starRingEnd ℂ) (s₀ u)) = 2 := by
    have : (∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold s₀ u * (starRingEnd ℂ) (s₀ u)) =
        ∫ u in Ioc (1 / 2 : ℝ) 1, 2 * (((u : ℂ))⁻¹ * ((u : ℂ))⁻¹) := by
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      rw [ae_restrict_iff' measurableSet_Ioc] at hfold
      filter_upwards [hfold] with u hu humem
      rw [hu humem, hs₀, selfSimilarExtension_eq_of_mem humem]
      simp only [map_inv₀, Complex.conj_ofReal]
      ring
    rw [this, integral_const_mul, integral_Ioc_inv_sq, mul_one]
  rw [hL, hR] at h
  exact_mod_cast h

/-- **Harmonic penalty for the Haar target.**  Every finite generator combination satisfies
`∫_0^1 |h − Σ_j c_j φ_{a_j}|² ≥ ½ |Σ_j c_j / a_j|²`: the harmonic coefficient sum of any
approximant of the Haar target is controlled by its error. -/
theorem dyadicHaar_approximation_harmonic_penalty {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (ha : ∀ j, 1 ≤ a j) :
    ‖∑ j, c j / (a j : ℂ)‖ ^ 2 / 2 ≤
      ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2 := by
  set s₀ := selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) with hs₀
  have hm : Measurable s₀ := measurable_selfSimilarExtension Complex.measurable_ofReal.inv
  have h := norm_sq_fold_pairing_le measurable_dyadicHaar hm integrableOn_normSq_dyadicHaar
    integrableOn_normSq_selfSimilarExtension_inv
    (ae_selfSimilar_selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)) c a ha
  rw [integral_normSq_selfSimilarExtension_inv, dyadicLogMean_selfSimilarExtension_inv, map_one,
    mul_one] at h
  have hz : (∫ u in Ioc (1 / 2 : ℝ) 1, dyadicFold dyadicHaar u * (starRingEnd ℂ) (s₀ u)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu => by rw [dyadicFold_dyadicHaar hu, zero_mul]
  rw [hz, zero_add] at h
  linarith

end RHTower
