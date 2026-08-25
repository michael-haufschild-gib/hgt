import GaloisForLFunctions.HTGeometry.NevanlinnaSmallGrowthArc

/-!
# Small Nevanlinna growth cannot dominate an upper circular arc

This is the upper-half-plane counterpart of the right-arc obstruction.  The fixed arc
`[π / 2, 5π / 6]` has length `π / 3` and lies in `Im z ≥ |z| / 2`; it therefore matches the
rotated Dirichlet realization `s = -i z` used by the upper-end carrier.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem fullCircleIntegral_eq_twoPi_mul_proximity_upper {f : ℂ → ℂ} (R : ℝ) :
    (∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖) =
      (2 * Real.pi) * proximity f ⊤ R := by
  rw [proximity_top, Real.circleAverage_def]
  change (∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖) =
    (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
      ∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖)
  field_simp [ne_of_gt Real.pi_pos]

/-- A codiscrete plane property holds almost everywhere after restriction to the fixed upper
circle arc `[π / 2, 5π / 6]`. -/
theorem ae_restrict_circleMap_mem_of_mem_codiscrete_upperArc {S : Set ℂ}
    (hS : S ∈ Filter.codiscrete ℂ) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ theta ∂MeasureTheory.volume.restrict
      (Set.Icc (Real.pi / 2) (5 * Real.pi / 6)), circleMap 0 R theta ∈ S := by
  apply ae_restrict_le_codiscreteWithin measurableSet_Icc
  change (circleMap 0 R) ⁻¹' S ∈
    Filter.codiscreteWithin (Set.Icc (Real.pi / 2) (5 * Real.pi / 6))
  have hSwithin : S ∈ Filter.codiscreteWithin
      (circleMap 0 R '' Set.Icc (Real.pi / 2) (5 * Real.pi / 6)) := by
    have hSuniv : S ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
      simpa only [Filter.codiscrete] using hS
    exact Filter.codiscreteWithin_mono (Set.subset_univ _) hSuniv
  exact (circleMap_analyticOnNhd_real R _).preimage_mem_codiscreteWithin
    (fun x _ => circleMap_not_eventuallyConst hR x) hSwithin

/-- Finitely many meromorphic functions of characteristic `o(r)` cannot collectively have
positive-logarithmic size at least `c r` almost everywhere on `[π / 2, 5π / 6]` for every large
radius. -/
theorem not_eventually_ae_linear_le_sum_posLog_on_upperArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ᵐ θ ∂MeasureTheory.volume.restrict
        (Set.Icc (Real.pi / 2) (5 * Real.pi / 6)),
      c * R ≤ ∑ j, Real.posLog ‖phi j (circleMap 0 R θ)‖ := by
  intro hlower
  have hcharSum :
      (fun R => ∑ j, characteristic (phi j) ⊤ R) =o[atTop] id := by
    simpa only [Finset.sum_apply] using
      (Asymptotics.IsLittleO.sum (s := Finset.univ) (fun j _ => hsmall j))
  have hscaled :
      (fun R => (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R) =o[atTop] id :=
    hcharSum.const_mul_left (2 * Real.pi)
  have hslope : 0 < (Real.pi / 3) * c :=
    mul_pos (div_pos Real.pi_pos (by norm_num)) hc
  have hupper := hscaled.bound (half_pos hslope)
  obtain ⟨R, ⟨hRlower, hRupper⟩, hR⟩ := Filter.Eventually.exists
    ((hlower.and hupper).and (eventually_ge_atTop (1 : ℝ)))
  let g : Fin n → ℝ → ℝ := fun j θ =>
    Real.posLog ‖phi j (circleMap 0 R θ)‖
  have hfull : ∀ j, IntervalIntegrable (g j) MeasureTheory.volume
      0 (2 * Real.pi) := by
    intro j
    exact MeromorphicOn.circleIntegrable_posLog_norm (fun z _ => hphi j z)
  have harc : ∀ j, IntervalIntegrable (g j) MeasureTheory.volume
      (Real.pi / 2) (5 * Real.pi / 6) := by
    intro j
    apply (hfull j).mono_set
    rw [Set.uIcc_of_le (by nlinarith [Real.pi_pos] : Real.pi / 2 ≤ 5 * Real.pi / 6),
      Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    intro θ hθ
    constructor <;> nlinarith [Real.pi_pos, hθ.1, hθ.2]
  have harcSum : IntervalIntegrable (fun θ => ∑ j, g j θ)
      MeasureTheory.volume (Real.pi / 2) (5 * Real.pi / 6) := by
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using (harc j).add ih
  have hconst : IntervalIntegrable (fun _ : ℝ => c * R)
      MeasureTheory.volume (Real.pi / 2) (5 * Real.pi / 6) :=
    intervalIntegrable_const
  have hintegrated :
      (∫ _ : ℝ in Real.pi / 2..5 * Real.pi / 6, c * R) ≤
        ∫ θ : ℝ in Real.pi / 2..5 * Real.pi / 6, ∑ j, g j θ := by
    apply intervalIntegral.integral_mono_ae_restrict
      (by nlinarith [Real.pi_pos]) hconst harcSum
    exact hRlower
  have harc_le_full : ∀ j,
      (∫ θ : ℝ in Real.pi / 2..5 * Real.pi / 6, g j θ) ≤
        ∫ θ : ℝ in 0..2 * Real.pi, g j θ := by
    intro j
    apply intervalIntegral.integral_mono_interval
      (by positivity) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact Filter.Eventually.of_forall fun θ => Real.posLog_nonneg
    · exact hfull j
  have hproxChar : ∀ j,
      (∫ θ : ℝ in 0..2 * Real.pi, g j θ) ≤
        (2 * Real.pi) * characteristic (phi j) ⊤ R := by
    intro j
    rw [show (∫ θ : ℝ in 0..2 * Real.pi, g j θ) =
        (2 * Real.pi) * proximity (phi j) ⊤ R by
      exact fullCircleIntegral_eq_twoPi_mul_proximity_upper (f := phi j) R]
    exact mul_le_mul_of_nonneg_left (proximity_le_characteristic hR)
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hlowerScaled : (Real.pi / 3) * c * R ≤
      (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R := by
    calc
      (Real.pi / 3) * c * R =
          ∫ _ : ℝ in Real.pi / 2..5 * Real.pi / 6, c * R := by
        rw [intervalIntegral.integral_const]
        ring
      _ ≤ ∫ θ : ℝ in Real.pi / 2..5 * Real.pi / 6, ∑ j, g j θ := hintegrated
      _ = ∑ j, ∫ θ : ℝ in Real.pi / 2..5 * Real.pi / 6, g j θ := by
        exact intervalIntegral.integral_finsetSum (fun j _ => harc j)
      _ ≤ ∑ j, ∫ θ : ℝ in 0..2 * Real.pi, g j θ :=
        Finset.sum_le_sum fun j _ => harc_le_full j
      _ ≤ ∑ j, (2 * Real.pi) * characteristic (phi j) ⊤ R :=
        Finset.sum_le_sum fun j _ => hproxChar j
      _ = (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R := by
        rw [Finset.mul_sum]
  have hscaledNonneg :
      0 ≤ (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Finset.sum_nonneg fun j _ => characteristic_nonneg hR)
  rw [Real.norm_eq_abs, abs_of_nonneg hscaledNonneg] at hRupper
  change (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R ≤
    (Real.pi / 3 * c / 2) * |R| at hRupper
  rw [abs_of_nonneg (zero_le_one.trans hR)] at hRupper
  have hslopeRpos : 0 < (Real.pi / 3) * c * R :=
    mul_pos hslope (zero_lt_one.trans_le hR)
  linarith

/-- Exponential size almost everywhere on the upper arc is impossible for a finite family of
small-growth meromorphic functions. -/
theorem not_eventually_ae_exp_le_sum_norm_on_upperArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ᵐ θ ∂MeasureTheory.volume.restrict
        (Set.Icc (Real.pi / 2) (5 * Real.pi / 6)),
      Real.exp (c * R) ≤ ∑ j, ‖phi j (circleMap 0 R θ)‖ := by
  intro hexp
  apply not_eventually_ae_linear_le_sum_posLog_on_upperArc phi hphi hsmall (half_pos hc)
  filter_upwards [hexp, eventually_ge_atTop
    (max 0 (2 * (n : ℝ) * Real.log 2 / c))] with R hRexp hR
  filter_upwards [hRexp] with θ hthetaExp
  have hR0 : 0 ≤ R := (le_max_left _ _).trans hR
  have hposLogExp : Real.posLog (Real.exp (c * R)) = c * R := by
    rw [Real.posLog, Real.log_exp, max_eq_right]
    exact mul_nonneg hc.le hR0
  have hsumNonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ‖phi j (circleMap 0 R θ)‖ := fun j _ => norm_nonneg _
  have hsplit := posLog_sum_le (Finset.univ : Finset (Fin n))
    (fun j => ‖phi j (circleMap 0 R θ)‖) hsumNonneg
  have hmono : Real.posLog (Real.exp (c * R)) ≤
      Real.posLog (∑ j, ‖phi j (circleMap 0 R θ)‖) :=
    Real.posLog_le_posLog (Real.exp_pos _).le hthetaExp
  have hconstant : 2 * (n : ℝ) * Real.log 2 ≤ c * R := by
    have hthreshold : 2 * (n : ℝ) * Real.log 2 / c ≤ R :=
      (le_max_right _ _).trans hR
    rw [div_le_iff₀ hc] at hthreshold
    simpa [mul_comm] using hthreshold
  rw [hposLogExp] at hmono
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = n := by simp
  rw [hcard] at hsplit
  linarith

end

end GaloisForLFunctions.HTGeometry
