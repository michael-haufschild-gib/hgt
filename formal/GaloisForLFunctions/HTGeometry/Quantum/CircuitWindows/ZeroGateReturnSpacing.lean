import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ResolvedVisits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

/-!
# Mean spacing of zero-gate returns at fine time resolution

Successive first visits separated by at least `h` give a covering and a
packing of return windows. The enclosing-arc Haar law and the spectral
speed squeeze their normalized mean spacing to the reciprocal occupation.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Operator error corresponding to a covering arc of length `r` turns. -/
def zeroGateArcTolerance (r : ℝ) : ℝ := 2 * Real.sin (Real.pi * r / 2)

/-- The zero-gate return set at the indicated covering-arc tolerance. -/
def zeroGateReturnSet {n : ℕ} (H : selfAdjoint (Reg n)) (r : ℝ) : Set ℝ :=
  {t | orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance r}

/-- Haar mass of the short-arc return set for a `D`-dimensional register. -/
def zeroGateArcDensity (D : ℕ) (r : ℝ) : ℝ := (D : ℝ) * r ^ (D - 1)

/-- Each recorded time is the first return at least `h` after its predecessor. -/
def IsZeroGateReturnSequence {n : ℕ} (H : selfAdjoint (Reg n)) (r a h : ℝ)
    (t : ℕ → ℝ) : Prop :=
  t 0 = a ∧ ∀ j, IsLeast {v | t j + h ≤ v ∧ v ∈ zeroGateReturnSet H r} (t (j + 1))

/-- Moving the initial endpoint of a bounded observation interval changes its
occupation length by at most the displacement. -/
theorem abs_occupation_sub_le_start_displacement (A : Set ℝ) (a b T : ℝ) :
    |volume.real (A ∩ Icc a T) - volume.real (A ∩ Icc b T)| ≤ |a - b| := by
  let m (x : ℝ) := volume.real (A ∩ Icc x T)
  have finite (x : ℝ) : volume (A ∩ Icc x T) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have mono {x y : ℝ} (h : x ≤ y) : m y ≤ m x :=
    measureReal_mono (inter_subset_inter_right _ (Icc_subset_Icc_left h)) (finite x)
  have bound (x y : ℝ) (h : x ≤ y) : m x ≤ m y + (y - x) := by
    have hsub : A ∩ Icc x T ⊆ (A ∩ Icc y T) ∪ Icc x y := by
      rintro t ⟨ht, hxt, htT⟩
      exact (le_total y t).elim (fun hyt => Or.inl ⟨ht, hyt, htT⟩)
        (fun hty => Or.inr ⟨hxt, hty⟩)
    have hfinite : volume ((A ∩ Icc y T) ∪ Icc x y) < ⊤ :=
      measure_union_lt_top (lt_top_iff_ne_top.mpr (finite y)) measure_Icc_lt_top
    calc
      m x ≤ volume.real ((A ∩ Icc y T) ∪ Icc x y) := measureReal_mono hsub hfinite.ne
      _ ≤ m y + volume.real (Icc x y) := measureReal_union_le _ _
      _ = m y + (y - x) := by rw [Real.volume_real_Icc_of_le h]
  change |m a - m b| ≤ |a - b|
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (mono hab)), abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith only [bound a b hab]
  · rw [abs_of_nonpos (sub_nonpos.mpr (mono hba)), abs_of_nonneg (sub_nonneg.mpr hba)]
    linarith only [bound b a hba]

private theorem windowProbabilityMeasure_real_eq (A : Set ℝ) (hA : MeasurableSet A)
    {T : ℝ} (hT : 0 < T) :
    (windowProbabilityMeasure T : Measure ℝ).real A = volume.real (A ∩ Icc 0 T) / T := by
  change (((ENNReal.ofReal (windowLength T))⁻¹ • volume.restrict (Ioc 0 (windowLength T))) :
    Measure ℝ).real A = _
  rw [windowLength_eq hT, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le, Measure.restrict_apply hA, div_eq_mul_inv, mul_comm]

/-- Every fixed starting time has the same limiting occupation as the window
starting at zero. -/
theorem tendsto_occupation_from_start (A : Set ℝ) (hA : MeasurableSet A) (a p : ℝ)
    (h : Tendsto (fun T => (windowProbabilityMeasure T : Measure ℝ).real A) atTop (𝓝 p)) :
    Tendsto (fun T => volume.real (A ∩ Icc a T) / (T - a)) atTop (𝓝 p) := by
  let m (x T : ℝ) := volume.real (A ∩ Icc x T)
  have h0 : Tendsto (fun T => m 0 T / T) atTop (𝓝 p) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact windowProbabilityMeasure_real_eq A hA hT
  have ht : Tendsto (fun T : ℝ => T - a) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hinv : Tendsto (fun T : ℝ => (T - a)⁻¹) atTop (𝓝 0) := ht.inv_tendsto_atTop
  have hscale : Tendsto (fun T : ℝ => 1 + a * (T - a)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (hinv.const_mul a).const_add 1
  have hε : Tendsto (fun T : ℝ => |a| / (T - a)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul |a|
  have hd : Tendsto (fun T => (m a T - m 0 T) / (T - a)) atTop (𝓝 0) := by
    have hb : ∀ᶠ T : ℝ in atTop,
        -(|a| / (T - a)) ≤ (m a T - m 0 T) / (T - a) ∧
          (m a T - m 0 T) / (T - a) ≤ |a| / (T - a) := by
      filter_upwards [eventually_gt_atTop a] with T hT
      have hdiff : |m a T - m 0 T| ≤ |a| := by
        simpa only [m, sub_zero] using abs_occupation_sub_le_start_displacement A a 0 T
      refine ⟨?_, div_le_div_of_nonneg_right (abs_le.mp hdiff).2 (sub_nonneg.mpr hT.le)⟩
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp hdiff).1 (sub_nonneg.mpr hT.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [neg_zero] using hε.neg) hε
    · exact hb.mono fun _ h => h.1
    · exact hb.mono fun _ h => h.2
  have hsum := (h0.mul hscale).add hd
  rw [mul_one, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop a] with T hT haT
  field_simp [hT.ne', (sub_pos.mpr haT).ne']
  ring

/-- On the short-arc range, a larger enclosing arc gives strictly larger
operator tolerance. -/
theorem strictMonoOn_zeroGateArcTolerance : StrictMonoOn zeroGateArcTolerance (Icc (0 : ℝ) (1 / 2)) := by
  intro r hr s hs hrs
  have hmem (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
      Real.pi * x / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have h0 := mul_nonneg Real.pi_pos.le hx.1
    have h1 := mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le
    exact ⟨by linarith only [h0, Real.pi_pos], by linarith only [h1, Real.pi_pos]⟩
  exact mul_lt_mul_of_pos_left (Real.strictMonoOn_sin (hmem r hr) (hmem s hs)
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hrs Real.pi_pos) zero_lt_two)) zero_lt_two

private theorem isClosed_zeroGateReturnSet {n : ℕ} (H : selfAdjoint (Reg n)) (r : ℝ) :
    IsClosed (zeroGateReturnSet H r) :=
  isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const

/-- Positive arc tolerance gives an attained first return after every start,
with no spectral independence condition. -/
theorem exists_zeroGateReturnSequence {n : ℕ} (H : selfAdjoint (Reg n))
    (r : Ioc (0 : ℝ) (1 / 2)) (a h : ℝ) :
    ∃ t, IsZeroGateReturnSequence H r a h t := by
  classical
  have hε : 0 < zeroGateArcTolerance r := by
    have h := strictMonoOn_zeroGateArcTolerance
      (show (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) from ⟨le_rfl, by positivity⟩)
      (Ioc_subset_Icc_self r.2) r.2.1
    simpa only [zeroGateArcTolerance, mul_zero, zero_div, Real.sin_zero] using h
  obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * Real.pi / zeroGateArcTolerance r)
  have hQpos : 0 < (Q : ℝ) + 1 := by positivity
  have hallow : 2 * Real.pi / ((Q : ℝ) + 1) ≤ zeroGateArcTolerance r := by
    apply (div_le_iff₀ hQpos).mpr
    have hQ' := (div_lt_iff₀ hε).mp hQ
    rw [mul_comm (zeroGateArcTolerance r), add_mul, one_mul]
    linarith only [hQ', hε]
  let D := Fintype.card (Fin n → Bool)
  have hD : 0 < D := Fintype.card_pos
  have e : (Fin n → Bool) ≃ Fin ((D - 1) + 1) :=
    (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by omega))
  have first (b : ℝ) : ∃ v, IsLeast {u | b ≤ u ∧ u ∈ zeroGateReturnSet H r} v := by
    obtain ⟨v, hv, hreturn⟩ := projective_operator_zero_gate_return_after e H b Q
    have hb : b ≤ v := (le_abs_self b).trans ((le_add_of_nonneg_right zero_le_one).trans hv.1)
    have hz : v ∈ zeroGateReturnSet H r :=
      ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hreturn).trans hallow
    let B := Icc b v ∩ zeroGateReturnSet H r
    have hB : IsCompact B := isCompact_Icc.inter_right (isClosed_zeroGateReturnSet H r)
    have hvB : v ∈ B := ⟨⟨hb, le_rfl⟩, hz⟩
    obtain ⟨hmem, hleast⟩ := hB.isLeast_sInf ⟨v, hvB⟩
    refine ⟨sInf B, ⟨hmem.1.1, hmem.2⟩, ?_⟩
    rintro w ⟨hbw, hw⟩
    rcases le_total w v with hwv | hvw
    · exact hleast ⟨⟨hbw, hwv⟩, hw⟩
    · exact hmem.1.2.trans hvw
  choose hit hhit using first
  let t (j : ℕ) : ℝ := Nat.rec a (fun _ v => hit (v + h)) j
  exact ⟨t, rfl, fun j => hhit (t j + h)⟩

/-- The start and resolution determine the entire sequence of first returns. -/
theorem zeroGateReturnSequence_unique {n : ℕ} {H : selfAdjoint (Reg n)} {r a h : ℝ}
    {t u : ℕ → ℝ} (ht : IsZeroGateReturnSequence H r a h t) (hu : IsZeroGateReturnSequence H r a h u) :
    t = u := by
  funext j
  induction j with
  | zero => exact ht.1.trans hu.1.symm
  | succ j ih =>
      have h := ht.2 j
      rw [ih] at h
      exact h.unique (hu.2 j)

/-- A forward window containing an affordable hit remains affordable at its
start after paying half the spectral width times the window length. -/
theorem zeroGateWindowHits_subset_wider {n : ℕ} (H : selfAdjoint (Reg n))
    (r s h : ℝ) (hbudget : zeroGateArcTolerance r + circuitHamiltonianSpectralWidth H / 2 * h ≤
      zeroGateArcTolerance s) :
    {u | ∃ v ∈ Icc u (u + h), v ∈ zeroGateReturnSet H r} ⊆ zeroGateReturnSet H s := by
  obtain ⟨L, hL, hLip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H 0
  rintro u ⟨v, hv, hr⟩
  have hd := hLip.dist_le_mul u v
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hv.1), hL] at hd
  have hδ : v - u ≤ h := by linarith only [hv.2]
  have hwidth := circuitHamiltonianSpectralWidth_nonneg H
  have hmul := mul_le_mul_of_nonneg_left hδ (div_nonneg hwidth zero_le_two)
  change orbitCircuitDistance H 0 v ≤ zeroGateArcTolerance r at hr
  change orbitCircuitDistance H 0 u ≤ zeroGateArcTolerance s
  linarith only [(abs_le.mp hd).2, hmul, hr, hbudget]

/-- The exact real-valued return fraction applies from any fixed initial time. -/
theorem maximallyProjective_zeroGateOccupation_from_start {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Icc (0 : ℝ) (1 / 2)) (a : ℝ) :
    Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
      (𝓝 (zeroGateArcDensity (2 ^ n) r)) := by
  apply tendsto_occupation_from_start _ (isClosed_zeroGateReturnSet H r).measurableSet
  have he : {t | HasProjectiveCircuitApproximation n (zeroGateArcTolerance r) 0
      (unitaryEvolution (H : Reg n) t)} = zeroGateReturnSet H r := by
    ext t
    exact hasProjectiveCircuitApproximation_iff_infDist _ _ _
  have hp := maximallyProjective_zeroGateWindow_tendsto H hmax r
  change Tendsto (fun T => (windowProbabilityMeasure T : Measure ℝ)
    {t | HasProjectiveCircuitApproximation n (zeroGateArcTolerance r) 0
      (unitaryEvolution (H : Reg n) t)}) atTop _ at hp
  rw [he, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hp
  have hfinite : ((↑(2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (r : ℝ) ^ (2 ^ n - 1)) ≠ ⊤ := by
    finiteness
  have hreal := (ENNReal.tendsto_toReal hfinite).comp hp
  change Tendsto (fun T => ((windowProbabilityMeasure T : Measure ℝ) (zeroGateReturnSet H r)).toReal)
    atTop _ at hreal
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal r.2.1, zeroGateArcDensity] using hreal

/-- Positive narrow and wide occupations bound the mean spacing of first
visits. The required observation length is uniform in the resolution. -/
theorem exists_resolved_visit_spacing_threshold (A B : Set ℝ) (a p q : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hA : Tendsto (fun T => volume.real (A ∩ Icc a T) / (T - a)) atTop (𝓝 p))
    (hB : Tendsto (fun T => volume.real (B ∩ Icc a T) / (T - a)) atTop (𝓝 q))
    (η : ℝ) (hη : 0 < η) :
    ∃ R > 0, ∀ h > 0,
      {u | ∃ v ∈ Icc u (u + h), v ∈ A} ⊆ B →
      ∀ t : ℕ → ℝ, t 0 = a →
      (∀ i, IsLeast {v | t i + h ≤ v ∧ v ∈ A} (t (i + 1))) →
      ∀ j : ℕ, R ≤ (j : ℝ) * h →
        q⁻¹ - η < (t j - a) / ((j : ℝ) * h) ∧
        (t j - a) / ((j : ℝ) * h) < p⁻¹ + η := by
  let density (S : Set ℝ) (T : ℝ) := volume.real (S ∩ Icc a T) / (T - a)
  have htail : ∀ᶠ T : ℝ in atTop,
      0 < density A T ∧ (density A T)⁻¹ < p⁻¹ + η ∧ q⁻¹ - η < (density B T)⁻¹ := by
    exact (hA.eventually (eventually_gt_nhds hp)).and
      (((hA.inv₀ hp.ne').eventually (eventually_lt_nhds (lt_add_of_pos_right _ hη))).and
        ((hB.inv₀ hq.ne').eventually (eventually_gt_nhds (sub_lt_self _ hη))))
  obtain ⟨T, hT⟩ := eventually_atTop.1 htail
  refine ⟨max 1 (T - a), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro h hh hsub t ht hfirst j hj
  have hmin (i : ℕ) : a + (i : ℝ) * h ≤ t i := by
    induction i with
    | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using ht.ge
    | succ i ih =>
        have hstep := (hfirst i).1.1
        rw [Nat.cast_succ, add_mul, one_mul]
        linarith only [ih, hstep]
  have hja := (le_max_right 1 (T - a)).trans hj
  have hTj : T ≤ t j := by linarith only [hja, hmin j]
  have hjh : 0 < (j : ℝ) * h := (zero_lt_one.trans_le (le_max_left 1 (T - a))).trans_le hj
  have htime : 0 < t j - a := by linarith only [hmin j, hjh]
  obtain ⟨hcover, hpack⟩ := resolved_visit_occupation_bounds A t a h h hh le_rfl ht hfirst j
  have hpack' : (j : ℝ) * h ≤ volume.real (B ∩ Icc a (t j)) :=
    hpack.trans (measureReal_mono (inter_subset_inter_left _ hsub)
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne))
  have hlow : density A (t j) ≤ (j : ℝ) * h / (t j - a) :=
    div_le_div_of_nonneg_right hcover htime.le
  have hhigh : (j : ℝ) * h / (t j - a) ≤ density B (t j) :=
    div_le_div_of_nonneg_right hpack' htime.le
  obtain ⟨hApos, hup, hlo⟩ := hT (t j) hTj
  have hpos : 0 < (j : ℝ) * h / (t j - a) := div_pos hjh htime
  have hBpos : 0 < density B (t j) := hpos.trans_le hhigh
  have hl := hlo.trans_le ((inv_le_inv₀ hBpos hpos).mpr hhigh)
  have hu := ((inv_le_inv₀ hpos hApos).mpr hlow).trans_lt hup
  simpa only [inv_div] using And.intro hl hu

private theorem zeroGateArcDensity_pos (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < zeroGateArcDensity (2 ^ n) r := by
  unfold zeroGateArcDensity
  exact mul_pos (by positivity) (pow_pos hr _)

/-- For any resolution covered by the spectral tolerance margin, the
reciprocals of the narrow and wide return fractions bound mean spacing. -/
theorem maximallyProjective_zeroGateSpacing_sandwich {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r s : Ioc (0 : ℝ) (1 / 2)) (a η : ℝ) (hη : 0 < η) :
    ∃ R > 0, ∀ h > 0,
      zeroGateArcTolerance r + circuitHamiltonianSpectralWidth H / 2 * h ≤ zeroGateArcTolerance s →
      ∀ t, IsZeroGateReturnSequence H r a h t → ∀ j : ℕ, R ≤ (j : ℝ) * h →
        (zeroGateArcDensity (2 ^ n) s)⁻¹ - η < (t j - a) / ((j : ℝ) * h) ∧
        (t j - a) / ((j : ℝ) * h) < (zeroGateArcDensity (2 ^ n) r)⁻¹ + η := by
  obtain ⟨R, hR, h⟩ := exists_resolved_visit_spacing_threshold
    (zeroGateReturnSet H r) (zeroGateReturnSet H s) a
    (zeroGateArcDensity (2 ^ n) r) (zeroGateArcDensity (2 ^ n) s)
    (zeroGateArcDensity_pos n r.2.1) (zeroGateArcDensity_pos n s.2.1)
    (maximallyProjective_zeroGateOccupation_from_start H hmax ⟨r, Ioc_subset_Icc_self r.2⟩ a)
    (maximallyProjective_zeroGateOccupation_from_start H hmax ⟨s, Ioc_subset_Icc_self s.2⟩ a) η hη
  exact ⟨R, hR, fun δ hδ hbudget t ht =>
    h δ hδ (zeroGateWindowHits_subset_wider H r s δ hbudget) t ht.1 ht.2⟩

/-- The normalized mean spacing converges jointly as resolution vanishes
and the accumulated resolution `j*h` grows, from every fixed start. -/
theorem maximallyProjective_zeroGateSpacing_joint {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Ioo (0 : ℝ) (1 / 2)) (a η : ℝ) (hη : 0 < η) :
    ∃ h₀ > 0, ∃ R > 0, ∀ h > 0, h ≤ h₀ →
      ∀ t, IsZeroGateReturnSequence H r a h t → ∀ j : ℕ, R ≤ (j : ℝ) * h →
        |(t j - a) / ((j : ℝ) * h) - (zeroGateArcDensity (2 ^ n) r)⁻¹| < η := by
  let d (x : ℝ) := (zeroGateArcDensity (2 ^ n) x)⁻¹
  have hpos := zeroGateArcDensity_pos n r.2.1
  have hdensity : Continuous (zeroGateArcDensity (2 ^ n)) :=
    continuous_const.mul (continuous_id.pow (2 ^ n - 1))
  have hd : Tendsto d (𝓝[>] (r : ℝ)) (𝓝 (d r)) :=
    (hdensity.continuousAt.inv₀ hpos.ne').tendsto.mono_left nhdsWithin_le_nhds
  have hhη : 0 < η / 2 := half_pos hη
  have hright : ∀ᶠ s in 𝓝[>] (r : ℝ), (r : ℝ) < s := self_mem_nhdsWithin
  have hs : ∀ᶠ s in 𝓝[>] (r : ℝ),
      (r : ℝ) < s ∧ s < 1 / 2 ∧ d r - η / 2 < d s := by
    exact hright.and
      (((eventually_lt_nhds r.2.2).filter_mono nhdsWithin_le_nhds).and
        (hd.eventually (eventually_gt_nhds (sub_lt_self _ hhη))))
  obtain ⟨s, hrs, hsπ, hds⟩ := hs.exists
  have hs0 : 0 < s := r.2.1.trans hrs
  let r' : Ioc (0 : ℝ) (1 / 2) := ⟨r, r.2.1, r.2.2.le⟩
  let s' : Ioc (0 : ℝ) (1 / 2) := ⟨s, hs0, hsπ.le⟩
  obtain ⟨R, hR, hbound⟩ := maximallyProjective_zeroGateSpacing_sandwich H hmax r' s' a (η / 2) hhη
  let w := circuitHamiltonianSpectralWidth H / 2
  have hw : 0 ≤ w := div_nonneg (circuitHamiltonianSpectralWidth_nonneg H) zero_le_two
  have hw1 : 0 < 1 + w := add_pos_of_pos_of_nonneg zero_lt_one hw
  have hgap : zeroGateArcTolerance r < zeroGateArcTolerance s :=
    strictMonoOn_zeroGateArcTolerance ⟨r.2.1.le, r.2.2.le⟩ ⟨hs0.le, hsπ.le⟩ hrs
  let h₀ := (zeroGateArcTolerance s - zeroGateArcTolerance r) / (1 + w)
  refine ⟨h₀, div_pos (sub_pos.mpr hgap) hw1, R, hR, ?_⟩
  intro h hh hsmall t ht j hj
  have hpay : w * h ≤ zeroGateArcTolerance s - zeroGateArcTolerance r := by
    calc
      w * h ≤ (1 + w) * h := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hh.le
      _ ≤ _ := by rw [mul_comm]; exact (le_div_iff₀ hw1).mp hsmall
  have hbudget : zeroGateArcTolerance r + w * h ≤ zeroGateArcTolerance s := by
    linarith only [hpay]
  obtain ⟨hlo, hhi⟩ := hbound h hh hbudget t ht j hj
  change d s - η / 2 < (t j - a) / ((j : ℝ) * h) at hlo
  change (t j - a) / ((j : ℝ) * h) < d r + η / 2 at hhi
  change |(t j - a) / ((j : ℝ) * h) - d r| < η
  exact abs_lt.mpr ⟨by linarith only [hlo, hds], by linarith only [hhi, hη]⟩

/-- One typical Gaussian Pauli chain has the exact fine-resolution spacing
constant on every prefix of at least three sites, at every interior short-arc tolerance. -/
theorem gaussian_path_zeroGateSpacing_joint :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Ioo (0 : ℝ) (1 / 2), ∀ a η : ℝ, 0 < η →
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∃ h₀ > 0, ∃ R > 0, ∀ h > 0, h ≤ h₀ →
        ∃! t, IsZeroGateReturnSequence H r a h t ∧ ∀ j : ℕ, R ≤ (j : ℝ) * h →
          |(t j - a) / ((j : ℝ) * h) - (zeroGateArcDensity (2 ^ (k + 3)) r)⁻¹| < η := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k r a η hη
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  obtain ⟨h₀, h₀pos, R, hR, hbound⟩ := maximallyProjective_zeroGateSpacing_joint H (hω k) r a η hη
  refine ⟨h₀, h₀pos, R, hR, fun h hh hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_zeroGateReturnSequence H ⟨r, r.2.1, r.2.2.le⟩ a h
  exact ⟨t, ⟨ht, hbound h hh hs t ht⟩, fun v hv => zeroGateReturnSequence_unique hv.1 ht⟩

#print axioms abs_occupation_sub_le_start_displacement
#print axioms tendsto_occupation_from_start
#print axioms exists_zeroGateReturnSequence
#print axioms zeroGateReturnSequence_unique
#print axioms zeroGateWindowHits_subset_wider
#print axioms maximallyProjective_zeroGateOccupation_from_start
#print axioms exists_resolved_visit_spacing_threshold
#print axioms maximallyProjective_zeroGateSpacing_sandwich
#print axioms maximallyProjective_zeroGateSpacing_joint
#print axioms gaussian_path_zeroGateSpacing_joint

end

end GaloisForLFunctions.HTGeometry
