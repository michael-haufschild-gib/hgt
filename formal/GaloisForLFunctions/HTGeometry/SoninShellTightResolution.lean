import GaloisForLFunctions.HTGeometry.TwoPolarizationTightFormation
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninEulerCrossShellOverlap
import GaloisForLFunctions.RHTower.GaussianEvenCarrier

/-!
# The bilateral Sonin shell resolution

Fix `a > 0` and `r > 1`.  On the even subspace of `L²(ℝ)` let `P_n` (`n ∈ ℤ`) be multiplication by
the indicator of the annulus `I_n = {a rⁿ < |x| ≤ a rⁿ⁺¹}`, i.e. the difference of the central
cutoffs at radii `a rⁿ⁺¹` and `a rⁿ`.  The annuli are disjoint and exhaust `ℝ ∖ {0}`, so
`Σ_{n ∈ ℤ} P_n = I` strongly and `Σ_n ‖P_n x‖² = ‖x‖²` (`(3.2)`).  With `J` the even Fourier
unitary, `Q_n = J P_n J` is the Fourier shell `F_{a rⁿ⁺¹} - F_{a rⁿ}`, and the tight
two-polarization formation `B x = ((P_n x), (Q_n x))` satisfies `B*B = 2I` with decoder `½ B*` and
duality covariance `W B = B J`.

The finite telescoping identity `Σ_{-N ≤ n < N} P_n = cut(a r^N) - cut(a r^{-N})` reduces the
bilateral limit to the strong limits `cut(t) → I` (`t → ∞`) and `cut(t) → 0` (`t → 0⁺`), both
dominated convergence for bounded multipliers.
-/

open Filter Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

open _root_.RHTower

/-! ### Strong limits of the central cutoffs -/

private theorem indicatorCutoff_central_eq_mul (t : ℝ) (u : SoninL2) :
    indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) u =
      lpBoundedMulCLM (p := 2) (μ := volume)
        (measurable_const.indicator (measurableSet_centralInterval t) :
          Measurable ((centralInterval t).indicator fun _ : ℝ => (1 : ℂ)))
        zero_le_one (fun z => by
          by_cases hz : z ∈ centralInterval t <;> simp [hz]) u := by
  apply Lp.ext
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
    (measurable_const.indicator (measurableSet_centralInterval t) :
      Measurable ((centralInterval t).indicator fun _ : ℝ => (1 : ℂ)))
    zero_le_one (fun z => by by_cases hz : z ∈ centralInterval t <;> simp [hz]) u,
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) u] with z h1 h2
  rw [h1, h2]
  by_cases hz : z ∈ centralInterval t <;> simp [hz]

/-- `cut(t) u → u` as the aperture `t → ∞`. -/
theorem tendsto_indicatorCutoff_central_atTop (u : SoninL2) :
    Tendsto (fun t : ℝ => indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) u)
      atTop (𝓝 u) := by
  have hpt : ∀ z : ℝ, Tendsto (fun t : ℝ => (centralInterval t).indicator (fun _ => (1 : ℂ)) z)
      atTop (𝓝 1) := fun z => by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop |z|] with t ht
    rw [Set.indicator_of_mem (show z ∈ centralInterval t from Set.mem_Icc.2 (abs_le.1 ht))]
  have ht := tendsto_lpBoundedMulCLM_apply (μ := volume) (l := atTop)
    (fun t => (measurable_const.indicator (measurableSet_centralInterval t) :
      Measurable ((centralInterval t).indicator fun _ : ℝ => (1 : ℂ))))
    (measurable_const : Measurable fun _ : ℝ => (1 : ℂ)) zero_le_one
    (fun t z => by by_cases hz : z ∈ centralInterval t <;> simp [hz]) (fun _ => by simp) hpt u
  have he1 : lpBoundedMulCLM (p := 2) (μ := volume)
      (measurable_const : Measurable fun _ : ℝ => (1 : ℂ)) zero_le_one (fun _ => by simp) u =
        u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
      (measurable_const : Measurable fun _ : ℝ => (1 : ℂ)) zero_le_one (fun _ => by simp) u]
      with z hz
    rw [hz, one_mul]
  rw [he1] at ht
  exact ht.congr fun t => (indicatorCutoff_central_eq_mul t u).symm

/-- `cut(t) u → 0` as the aperture `t → 0⁺`: the cutoffs shrink to the null set `{0}`. -/
theorem tendsto_indicatorCutoff_central_zero (u : SoninL2) :
    Tendsto (fun t : ℝ => indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) u)
      (𝓝[>] 0) (𝓝 0) := by
  have hpt : ∀ z : ℝ, Tendsto (fun t : ℝ => (centralInterval t).indicator (fun _ => (1 : ℂ)) z)
      (𝓝[>] 0) (𝓝 (({0} : Set ℝ).indicator (fun _ => (1 : ℂ)) z)) := fun z => by
    by_cases hz : z = 0
    · subst hz
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [Set.indicator_of_mem (Set.mem_singleton 0),
        Set.indicator_of_mem (show (0 : ℝ) ∈ centralInterval t from
          Set.mem_Icc.2 ⟨by linarith, ht.le⟩)]
    · apply tendsto_const_nhds.congr'
      have hz' : 0 < |z| := abs_pos.2 hz
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hz')] with t (ht : t < |z|)
      rw [Set.indicator_of_notMem (by simpa using hz), Set.indicator_of_notMem]
      intro hmem
      exact absurd (abs_le.2 hmem) (not_le.2 ht)
  have ht := tendsto_lpBoundedMulCLM_apply (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (fun t => (measurable_const.indicator (measurableSet_centralInterval t) :
      Measurable ((centralInterval t).indicator fun _ : ℝ => (1 : ℂ))))
    (measurable_const.indicator (measurableSet_singleton 0) :
      Measurable (({0} : Set ℝ).indicator fun _ : ℝ => (1 : ℂ))) zero_le_one
    (fun t z => by by_cases hz : z ∈ centralInterval t <;> simp [hz])
    (fun z => by by_cases hz : z ∈ ({0} : Set ℝ) <;> simp [hz]) hpt u
  have he0 : lpBoundedMulCLM (p := 2) (μ := volume)
      (measurable_const.indicator (measurableSet_singleton 0) :
        Measurable (({0} : Set ℝ).indicator fun _ : ℝ => (1 : ℂ))) zero_le_one
      (fun z => by by_cases hz : z ∈ ({0} : Set ℝ) <;> simp [hz]) u = 0 := by
    have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
      rw [ae_iff]
      simp
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
      (measurable_const.indicator (measurableSet_singleton 0) :
        Measurable (({0} : Set ℝ).indicator fun _ : ℝ => (1 : ℂ))) zero_le_one
      (fun z => by by_cases hz : z ∈ ({0} : Set ℝ) <;> simp [hz]) u, Lp.coeFn_zero ℂ 2 volume, hne]
      with z hz h0 hz0
    rw [hz, h0, Set.indicator_of_notMem (by simpa using hz0), zero_mul]
    rfl
  rw [he0] at ht
  exact ht.congr fun t => (indicatorCutoff_central_eq_mul t u).symm

/-! ### The annular shell family -/

/-- The shell radius `a rⁿ`. -/
def shellRadius (a r : ℝ) (n : ℤ) : ℝ := a * r ^ n

theorem shellRadius_mono {a r : ℝ} (ha : 0 < a) (hr : 1 < r) {m n : ℤ} (hmn : m ≤ n) :
    shellRadius a r m ≤ shellRadius a r n :=
  mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hr.le hmn) ha.le

/-- The physical shell projection `P_n`, multiplication by `1_{a rⁿ < |x| ≤ a rⁿ⁺¹}`. -/
def physicalShell (a r : ℝ) (n : ℤ) : evenSubspace →L[ℂ] evenSubspace :=
  evenIndicatorCutoff (shellRadius a r (n + 1)) - evenIndicatorCutoff (shellRadius a r n)

private theorem cut_mul_cut (s t : ℝ) (x : evenSubspace) :
    evenIndicatorCutoff s (evenIndicatorCutoff t x) = evenIndicatorCutoff (min s t) x := by
  rw [← evenIndicatorCutoff_mul_min]
  rfl

private theorem cut_cut_of_le {s t : ℝ} (h : s ≤ t) (x : evenSubspace) :
    evenIndicatorCutoff s (evenIndicatorCutoff t x) = evenIndicatorCutoff s x := by
  rw [cut_mul_cut, min_eq_left h]

private theorem cut_cut_of_ge {s t : ℝ} (h : t ≤ s) (x : evenSubspace) :
    evenIndicatorCutoff s (evenIndicatorCutoff t x) = evenIndicatorCutoff t x := by
  rw [cut_mul_cut, min_eq_right h]

/-- The physical shells form an orthogonal projection family. -/
def physicalShellFamily {a r : ℝ} (ha : 0 < a) (hr : 1 < r) : ProjectionFamily ℤ evenSubspace where
  P := physicalShell a r
  symm n x y := by
    simp only [physicalShell, sub_apply, inner_sub_left, inner_sub_right,
      evenIndicatorCutoff_symmetric]
  idem n x := by
    have h := shellRadius_mono ha hr (show n ≤ n + 1 by omega)
    simp only [physicalShell, sub_apply, map_sub, cut_cut_of_le le_rfl,
      cut_cut_of_le h, cut_cut_of_ge h]
    abel
  orth m n hmn x := by
    simp only [physicalShell, sub_apply, map_sub]
    rcases lt_or_gt_of_ne hmn with h | h
    · have h1 := shellRadius_mono ha hr (show m + 1 ≤ n + 1 by omega)
      have h2 := shellRadius_mono ha hr (show m + 1 ≤ n by omega)
      have h3 := shellRadius_mono ha hr (show m ≤ n + 1 by omega)
      have h4 := shellRadius_mono ha hr (show m ≤ n by omega)
      rw [cut_cut_of_le h1, cut_cut_of_le h2, cut_cut_of_le h3, cut_cut_of_le h4]
      abel
    · have h1 := shellRadius_mono ha hr (show n + 1 ≤ m + 1 by omega)
      have h2 := shellRadius_mono ha hr (show n + 1 ≤ m by omega)
      have h3 := shellRadius_mono ha hr (show n ≤ m + 1 by omega)
      have h4 := shellRadius_mono ha hr (show n ≤ m by omega)
      rw [cut_cut_of_ge h1, cut_cut_of_ge h2, cut_cut_of_ge h3, cut_cut_of_ge h4]
      abel

/-- **Finite telescoping**: `Σ_{-N ≤ n < N} P_n = cut(a r^N) - cut(a r^{-N})`. -/
theorem sum_physicalShell (a r : ℝ) (N : ℕ) (x : evenSubspace) :
    ∑ n ∈ (Finset.range (2 * N)).image (fun k : ℕ => (k : ℤ) - N), physicalShell a r n x =
      evenIndicatorCutoff (shellRadius a r N) x - evenIndicatorCutoff (shellRadius a r (-N)) x := by
  rw [Finset.sum_image fun k _ l _ hkl => by simpa using hkl]
  have h := Finset.sum_range_sub
    (fun k : ℕ => evenIndicatorCutoff (shellRadius a r ((k : ℤ) - N)) x) (2 * N)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
    zero_sub] at h
  rw [show (2 * (N : ℤ) - N) = N by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [physicalShell, sub_apply, show (k : ℤ) + 1 - N = (k : ℤ) - N + 1 by ring]

/-- The physical shells exhaust the even subspace. -/
theorem physicalShell_approx {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (x : evenSubspace) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ t : Finset ℤ, ‖x - ∑ n ∈ t, physicalShell a r n x‖ < ε := by
  have hup : Tendsto (fun N : ℕ => shellRadius a r N) atTop atTop := by
    simp only [shellRadius, zpow_natCast]
    exact (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop ha
  have hdown : Tendsto (fun N : ℕ => shellRadius a r (-N)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun N => ?_⟩
    · simp only [shellRadius, zpow_neg, zpow_natCast]
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hr)).const_mul a
    · exact mul_pos ha (zpow_pos (by linarith) _)
  have h1 := (tendsto_indicatorCutoff_central_atTop (x : SoninL2)).comp hup
  have h2 := (tendsto_indicatorCutoff_central_zero (x : SoninL2)).comp hdown
  obtain ⟨N, hN1, hN2⟩ := ((Metric.tendsto_nhds.1 h1 (ε / 2) (by positivity)).and
    (Metric.tendsto_nhds.1 h2 (ε / 2) (by positivity))).exists
  refine ⟨(Finset.range (2 * N)).image (fun k : ℕ => (k : ℤ) - N), ?_⟩
  rw [sum_physicalShell]
  simp only [Function.comp_apply, dist_eq_norm, sub_zero] at hN1 hN2
  have hc : x - (evenIndicatorCutoff (shellRadius a r N) x -
      evenIndicatorCutoff (shellRadius a r (-N)) x) =
      (x - evenIndicatorCutoff (shellRadius a r N) x) +
        evenIndicatorCutoff (shellRadius a r (-N)) x := by abel
  rw [hc]
  calc ‖(x - evenIndicatorCutoff (shellRadius a r N) x) +
        evenIndicatorCutoff (shellRadius a r (-N)) x‖
      ≤ ‖x - evenIndicatorCutoff (shellRadius a r N) x‖ +
          ‖evenIndicatorCutoff (shellRadius a r (-N)) x‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add ?_ ?_
        · rw [norm_sub_rev, Submodule.coe_norm]
          exact hN1
        · rw [Submodule.coe_norm]
          exact hN2
    _ = ε := by ring

/-- **`(3.2)`**: the bilateral physical shell resolution of the identity on the even subspace. -/
def soninShellResolution {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    OrthogonalResolution ℤ evenSubspace :=
  (physicalShellFamily ha hr).toResolution fun x ε hε => physicalShell_approx ha hr x ε hε

/-! ### The Fourier polarization -/

/-- The even Fourier unitary `J`, an involution of the even subspace. -/
def evenFourierUnitary : evenSubspace ≃ₗᵢ[ℂ] evenSubspace where
  toLinearEquiv := LinearEquiv.ofInvolutive evenFourierTransform.toLinearMap
    evenFourierTransform_involutive
  norm_map' := evenFourierTransform_isometry

theorem evenFourierUnitary_apply (x : evenSubspace) :
    evenFourierUnitary x = evenFourierTransform x := rfl

theorem evenFourierUnitary_involutive (x : evenSubspace) :
    evenFourierUnitary (evenFourierUnitary x) = x := evenFourierTransform_involutive x

/-- The conjugate shells `Q_n = J P_n J` are the Fourier shells `F_{a rⁿ⁺¹} - F_{a rⁿ}`. -/
theorem soninShellResolution_conj_apply {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (n : ℤ)
    (x : evenSubspace) :
    ((soninShellResolution ha hr).conj evenFourierUnitary evenFourierUnitary_involutive).P n x =
      evenFourierCutoff (shellRadius a r (n + 1)) x - evenFourierCutoff (shellRadius a r n) x := by
  rw [OrthogonalResolution.conj_apply, evenFourierCutoff_eq_reflectedCutoff,
    evenFourierCutoff_eq_reflectedCutoff]
  change evenFourierTransform (physicalShell a r n (evenFourierTransform x)) = _
  simp only [physicalShell, sub_apply, map_sub, reflectedCutoff,
    mul_apply_eq_comp]

/-! ### The tight Sonin formation -/

/-- The two-polarization formation of the bilateral Sonin shells. -/
def soninFormation {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    evenSubspace →L[ℂ] FormationSpace ℤ evenSubspace :=
  formation (soninShellResolution ha hr) evenFourierUnitary evenFourierUnitary_involutive

/-- **§3, `(3.2)` with `(1.3)`–`(2.2)`**: on the even subspace the bilateral physical and Fourier
shells give `Σ_n P_n x = x`, `Σ_n ‖P_n x‖² = ‖x‖²`, and a tight formation with `B*B = 2I`, exact
decoder `½ B*`, Fourier-shell synthesis, and duality covariance `W B = B J`. -/
theorem soninShell_tight_formation {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (x y : evenSubspace) :
    HasSum (fun n : ℤ => physicalShell a r n x) x ∧
      HasSum (fun n : ℤ => ‖physicalShell a r n x‖ ^ 2) (‖x‖ ^ 2) ∧
      HasSum (fun n : ℤ => evenFourierCutoff (shellRadius a r (n + 1)) x -
        evenFourierCutoff (shellRadius a r n) x) x ∧
      ⟪soninFormation ha hr x, soninFormation ha hr y⟫_ℂ = 2 * ⟪x, y⟫_ℂ ∧
      ContinuousLinearMap.adjoint (soninFormation ha hr) ∘L soninFormation ha hr = (2 : ℂ) • 1 ∧
      decoder (soninShellResolution ha hr) evenFourierUnitary evenFourierUnitary_involutive
        (soninFormation ha hr x) = x ∧
      duality evenFourierUnitary evenFourierUnitary_involutive (soninFormation ha hr x) =
        soninFormation ha hr (evenFourierTransform x) := by
  refine ⟨(soninShellResolution ha hr).hasSum x, (soninShellResolution ha hr).hasSum_norm_sq x,
    ?_, inner_formation _ _ _ x y, adjoint_formation_comp _ _ _, decoder_formation _ _ _ x,
    duality_formation _ _ _ x⟩
  have h := ((soninShellResolution ha hr).conj evenFourierUnitary
    evenFourierUnitary_involutive).hasSum x
  exact h.congr_fun fun n => (soninShellResolution_conj_apply ha hr n x).symm

end GaloisForLFunctions.HTGeometry.TightFormation
