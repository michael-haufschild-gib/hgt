import GaloisForLFunctions.BiScaleUncertainty.FiniteMomentEnergyInvariance

/-!
# Finite-source scalarization with exact local data and energy domination

Separate two compact sources far enough to eliminate every local cross-correlation. The plus
and minus combinations then have identical local data. Their energies average to the component
energy sum, so one choice costs no more. Iteration removes finite vector rank without a limiting
argument, preserving any bounded collection of correlation constraints.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The source translation used to separate the components. -/
def sourceTranslate (g : ℝ → ℝ) (T u : ℝ) : ℝ := g (u - T)

theorem autocorr_sourceTranslate (g : ℝ → ℝ) (T x : ℝ) :
    autocorr (sourceTranslate g T) x = autocorr g x := by
  unfold autocorr sourceTranslate
  rw [← integral_add_right_eq_self (fun u => g (u - T) * g (u + x - T)) T]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u + T - T = u by ring, show u + T + x - T = u + x by ring]

theorem biScaleLevyEnergy_sourceTranslate (g : ℝ → ℝ) (T : ℝ) :
    biScaleLevyEnergy (sourceTranslate g T) = biScaleLevyEnergy g := by
  simp only [biScaleLevyEnergy, autocorr_sourceTranslate]

/-- The literal correlation parallelogram identity for real compact sources. -/
theorem autocorr_source_parallelogram {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (x : ℝ) :
    autocorr (fun u => f u + g u) x + autocorr (fun u => f u - g u) x =
      2 * (autocorr f x + autocorr g x) := by
  unfold autocorr
  rw [← integral_add (integrable_mul_shift (g := fun u => f u + g u) (hf.add hg) (hfc.add hgc) x)
    (integrable_mul_shift (g := fun u => f u - g u) (hf.sub hg) (hfc.sub hgc) x),
    ← integral_add (integrable_mul_shift hf hfc x) (integrable_mul_shift hg hgc x),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Quadratic energy obeys the same parallelogram identity, with all integrability discharged. -/
theorem biScaleLevyEnergy_source_parallelogram {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    biScaleLevyEnergy (fun u => f u + g u) + biScaleLevyEnergy (fun u => f u - g u) =
      2 * (biScaleLevyEnergy f + biScaleLevyEnergy g) := by
  unfold biScaleLevyEnergy
  rw [← integral_add (integrableOn_biScaleLevyIntegrand (hf.add hg) (hfc.add hgc))
    (integrableOn_biScaleLevyIntegrand (hf.sub hg) (hfc.sub hgc)),
    ← integral_add (integrableOn_biScaleLevyIntegrand hf hfc)
      (integrableOn_biScaleLevyIntegrand hg hgc), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h0 := autocorr_source_parallelogram hf.continuous hg.continuous hfc hgc 0
  have hx := autocorr_source_parallelogram hf.continuous hg.continuous hfc hgc x
  linear_combination (archLevySinhWeight x) * h0 - (archLevySinhWeight x) * hx

private theorem source_support_radius {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ D : ℝ, 0 < D ∧ ∀ u, D < |u| → f u = 0 := by
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 0 + 1, by positivity, ?_⟩
  intro u hu
  by_contra hne
  have hmem : u ∈ tsupport f := subset_closure (Function.mem_support.mpr hne)
  have hbound := hr hmem
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hbound
  linarith [le_max_left r 0]

/-- Support separation kills both cross-products on a whole bounded correlation window. -/
theorem exists_sourceTranslate_local_cross_zero {f g : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (A : ℝ) :
    ∃ T : ℝ, ∀ x, |x| ≤ A → ∀ u,
      f u * sourceTranslate g T (u + x) = 0 ∧ sourceTranslate g T u * f (u + x) = 0 := by
  obtain ⟨Df, _, hf⟩ := source_support_radius hfc
  obtain ⟨Dg, _, hg⟩ := source_support_radius hgc
  refine ⟨Df + Dg + A + 1, ?_⟩
  intro x hx u
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  constructor
  · by_cases hu : f u = 0
    · simp [hu]
    · have huB : |u| ≤ Df := le_of_not_gt (fun h => hu (hf u h))
      have hz : g (u + x - (Df + Dg + A + 1)) = 0 := hg _
        (lt_of_lt_of_le (by linarith [le_abs_self u] :
          Dg < -(u + x - (Df + Dg + A + 1))) (neg_le_abs _))
      simp [sourceTranslate, hz]
  · by_cases hu : f (u + x) = 0
    · simp [hu]
    · have huB : |u + x| ≤ Df := le_of_not_gt (fun h => hu (hf (u + x) h))
      have hz : g (u - (Df + Dg + A + 1)) = 0 := hg _
        (lt_of_lt_of_le (by linarith [le_abs_self (u + x)] :
          Dg < -(u - (Df + Dg + A + 1))) (neg_le_abs _))
      simp [sourceTranslate, hz]

theorem autocorr_add_of_cross_zero {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (x : ℝ) (hcross : ∀ u, f u * g (u + x) = 0 ∧ g u * f (u + x) = 0) :
    autocorr (fun u => f u + g u) x = autocorr f x + autocorr g x := by
  unfold autocorr
  rw [← integral_add (integrable_mul_shift hf hfc x) (integrable_mul_shift hg hgc x)]
  apply integral_congr_ae
  filter_upwards [] with u
  rcases hcross u with ⟨h1, h2⟩
  nlinarith only [h1, h2]

/-- Two arbitrary compact sources have one scalar source with exactly their summed local
correlation and no greater energy. Individual components need not satisfy the local constraints. -/
theorem exists_scalar_pair_local_energy_le {f g : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (A : ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ r k ∧ HasCompactSupport k ∧
      (∀ x, |x| ≤ A → autocorr k x = autocorr f x + autocorr g x) ∧
      biScaleLevyEnergy k ≤ biScaleLevyEnergy f + biScaleLevyEnergy g := by
  obtain ⟨T, hcross⟩ := exists_sourceTranslate_local_cross_zero hfc hgc A
  let q := sourceTranslate g T
  have hq : ContDiff ℝ r q := hg.comp (contDiff_id.sub contDiff_const)
  have hqc : HasCompactSupport q := hgc.comp_homeomorph (Homeomorph.subRight T)
  have hlocal : ∀ x, |x| ≤ A → autocorr (fun u => f u + q u) x =
      autocorr f x + autocorr g x := by
    intro x hx
    rw [autocorr_add_of_cross_zero hf.continuous hq.continuous hfc hqc x (hcross x hx)]
    exact congrArg (fun z => autocorr f x + z) (autocorr_sourceTranslate g T x)
  have hpar := biScaleLevyEnergy_source_parallelogram (hf.of_le hr) (hq.of_le hr) hfc hqc
  have hE : biScaleLevyEnergy q = biScaleLevyEnergy g := biScaleLevyEnergy_sourceTranslate g T
  rw [hE] at hpar
  by_cases hplus : biScaleLevyEnergy (fun u => f u + q u) ≤ biScaleLevyEnergy f + biScaleLevyEnergy g
  · exact ⟨_, hf.add hq, hfc.add hqc, hlocal, hplus⟩
  · refine ⟨_, hf.sub hq, hfc.sub hqc, ?_, by linarith⟩
    intro x hx
    have hp := autocorr_source_parallelogram hf.continuous hq.continuous hfc hqc x
    rw [hlocal x hx, show autocorr q x = autocorr g x from autocorr_sourceTranslate g T x] at hp
    linarith

theorem autocorr_source_const_mul (f : ℝ → ℝ) (c x : ℝ) :
    autocorr (fun u => c * f u) x = c ^ 2 * autocorr f x := by
  unfold autocorr
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

theorem biScaleLevyEnergy_source_const_mul (f : ℝ → ℝ) (c : ℝ) :
    biScaleLevyEnergy (fun u => c * f u) = c ^ 2 * biScaleLevyEnergy f := by
  unfold biScaleLevyEnergy
  simp only [autocorr_source_const_mul, ← mul_sub, mul_assoc]
  exact integral_const_mul _ _

/-- Every nonnegative weighted pair has an exact local scalar realization with energy domination. -/
theorem exists_scalar_weighted_pair_local_energy_le {f g : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (A : ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ r k ∧ HasCompactSupport k ∧
      (∀ x, |x| ≤ A → autocorr k x = a * autocorr f x + b * autocorr g x) ∧
      biScaleLevyEnergy k ≤ a * biScaleLevyEnergy f + b * biScaleLevyEnergy g := by
  obtain ⟨k, hk, hkc, hlocal, hE⟩ := exists_scalar_pair_local_energy_le hr
    (f := fun u => Real.sqrt a * f u) (g := fun u => Real.sqrt b * g u)
    (contDiff_const.mul hf) (contDiff_const.mul hg) hfc.mul_left hgc.mul_left A
  refine ⟨k, hk, hkc, ?_, ?_⟩
  · intro x hx
    simpa only [autocorr_source_const_mul, Real.sq_sqrt ha, Real.sq_sqrt hb] using hlocal x hx
  · simpa only [biScaleLevyEnergy_source_const_mul, Real.sq_sqrt ha, Real.sq_sqrt hb] using hE

/-- Unit-mass local correlation data together with an upper allowance for energy. -/
def localSourceEnergyEpigraph (r : WithTop ℕ∞) (A : ℝ) : Set ((ℝ → ℝ) × ℝ) :=
  {p | ∃ f : ℝ → ℝ, ContDiff ℝ r f ∧ HasCompactSupport f ∧ autocorr f 0 = 1 ∧
    (∀ x, |x| ≤ A → autocorr f x = p.1 x) ∧ biScaleLevyEnergy f ≤ p.2}

/-- The actual real scalar-source local energy epigraph is convex, without taking a closure
or relaxing to vector sources. Support enlargement is allowed. -/
theorem convex_localSourceEnergyEpigraph (r : WithTop ℕ∞) (hr : 2 ≤ r)
    (A : ℝ) (hA : 0 ≤ A) : Convex ℝ (localSourceEnergyEpigraph r A) := by
  rintro p ⟨f, hf, hfc, hRf, hpf, hEf⟩ q ⟨g, hg, hgc, hRg, hqg, hEg⟩ a b ha hb hab
  obtain ⟨k, hk, hkc, hlocal, hE⟩ :=
    exists_scalar_weighted_pair_local_energy_le hr hf hg hfc hgc ha hb A
  refine ⟨k, hk, hkc, ?_, ?_, ?_⟩
  · simpa only [hRf, hRg, mul_one, hab] using hlocal 0 (by simpa using hA)
  · intro x hx
    simpa only [hpf x hx, hqg x hx, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] using hlocal x hx
  · exact hE.trans (add_le_add (mul_le_mul_of_nonneg_left hEf ha) (mul_le_mul_of_nonneg_left hEg hb))

/-- Finite vector-valued sources can be replaced by a real scalar source with exactly the same
local total correlation and no greater total energy. This is exact, not merely a limiting claim. -/
theorem exists_scalar_list_local_energy_le (sources : List (ℝ → ℝ)) {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hs : ∀ f ∈ sources, ContDiff ℝ r f ∧ HasCompactSupport f) (A : ℝ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ r k ∧ HasCompactSupport k ∧
      (∀ x, |x| ≤ A → autocorr k x = (sources.map (fun f => autocorr f x)).sum) ∧
      biScaleLevyEnergy k ≤ (sources.map biScaleLevyEnergy).sum := by
  induction sources with
  | nil =>
      refine ⟨fun _ => 0, contDiff_const, ?_, ?_, ?_⟩
      · exact HasCompactSupport.zero
      · intro x _; simp [autocorr]
      · simp [biScaleLevyEnergy, autocorr]
  | cons f sources ih =>
      have hf := hs f (List.mem_cons_self ..)
      have htail : ∀ g ∈ sources, ContDiff ℝ r g ∧ HasCompactSupport g :=
        fun g hg => hs g (List.mem_cons_of_mem _ hg)
      obtain ⟨g, hg, hgc, hlocalg, hEg⟩ := ih htail
      obtain ⟨k, hk, hkc, hlocalk, hEk⟩ :=
        exists_scalar_pair_local_energy_le hr hf.1 hg hf.2 hgc A
      refine ⟨k, hk, hkc, ?_, ?_⟩
      · intro x hx
        simpa only [List.map_cons, List.sum_cons, hlocalg x hx] using hlocalk x hx
      · simp only [List.map_cons, List.sum_cons]
        linarith

/-- Finite real vector rank does not change any valid logarithmic-grid energy lower bound.
The zero constraints are imposed on the total correlation, not component by component. -/
theorem finite_source_log_grid_lower_bound_iff (r : WithTop ℕ∞) (hr : 2 ≤ r)
    (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f) ↔
    (∀ sources : List (ℝ → ℝ),
      (∀ f ∈ sources, ContDiff ℝ r f ∧ HasCompactSupport f) →
      0 < (sources.map (fun f => autocorr f 0)).sum →
      (∀ n ∈ Finset.Icc 2 N, (sources.map (fun f => autocorr f (Real.log (n : ℝ)))).sum = 0) →
      C ≤ (sources.map biScaleLevyEnergy).sum / (sources.map (fun f => autocorr f 0)).sum) := by
  constructor
  · intro hscalar sources hs hR hgrid
    let A := max (Real.log (N : ℝ)) 0
    obtain ⟨k, hk, hkc, hlocal, hE⟩ := exists_scalar_list_local_energy_le sources hr hs A
    have hmass : autocorr k 0 = (sources.map (fun f => autocorr f 0)).sum :=
      hlocal 0 (by simpa only [abs_zero] using le_max_right (Real.log (N : ℝ)) 0)
    have hkR : 0 < autocorr k 0 := by rwa [hmass]
    have hgridk : ∀ n ∈ Finset.Icc 2 N, autocorr k (Real.log (n : ℝ)) = 0 := by
      intro n hn
      have hnrange := Finset.mem_Icc.mp hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have hbound : |Real.log (n : ℝ)| ≤ A := by
        rw [abs_of_nonneg hln]
        exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
      rw [hlocal _ hbound, hgrid n hn]
    have hkC := hscalar k hk hkc hkR hgridk
    unfold normalizedArchEnergy at hkC
    rw [hmass] at hkC
    exact hkC.trans (div_le_div_of_nonneg_right hE hR.le)
  · intro hvector f hf hfc hR hgrid
    have hs : ∀ g ∈ [f], ContDiff ℝ r g ∧ HasCompactSupport g := by
      intro g hg
      have he : g = f := by simpa using hg
      subst g
      exact ⟨hf, hfc⟩
    have hmass : 0 < (([f] : List (ℝ → ℝ)).map (fun g => autocorr g 0)).sum := by simpa using hR
    have hz : ∀ n ∈ Finset.Icc 2 N,
        (([f] : List (ℝ → ℝ)).map (fun g => autocorr g (Real.log (n : ℝ)))).sum = 0 := by
      intro n hn
      simpa using hgrid n hn
    simpa [normalizedArchEnergy] using hvector [f] hs hmass hz

/-- In particular, the polar scalar-source problem and the unconstrained finite-vector problem
have the same sharp finite-grid constant. -/
theorem polar_finite_source_log_grid_lower_bound_iff (r : WithTop ℕ∞) (hr : 2 ≤ r)
    (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) →
      (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0 → C ≤ normalizedArchEnergy f) ↔
    (∀ sources : List (ℝ → ℝ),
      (∀ f ∈ sources, ContDiff ℝ r f ∧ HasCompactSupport f) →
      0 < (sources.map (fun f => autocorr f 0)).sum →
      (∀ n ∈ Finset.Icc 2 N, (sources.map (fun f => autocorr f (Real.log (n : ℝ)))).sum = 0) →
      C ≤ (sources.map biScaleLevyEnergy).sum / (sources.map (fun f => autocorr f 0)).sum) :=
  (polar_log_grid_lower_bound_iff r hr N C).trans (finite_source_log_grid_lower_bound_iff r hr N C)

end
end GaloisForLFunctions.BiScaleUncertainty
