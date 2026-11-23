import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ResponseRange

/-! # Norm limits of conserving omissions on translated occupation lanes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology ContinuousLinearMap

/-- Spectra of positive conserving projections with exactly r omitted directions. -/
def physicalSpectra (r : ℕ) : Set (SpectralBand r) :=
  {b | ∃ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)), physicalSpectrum P hd hc = b}

theorem laneSpectra_subset_physicalSpectra (r : ℕ) : laneSpectra r ⊆ physicalSpectra r := by
  rintro b ⟨v,rfl⟩
  unfold laneSpectrum
  exact ⟨_,_,_,rfl⟩

/-- Translating the whole missing family along an increasing coordinate injection preserves conservation. -/
theorem extended_lanes_conserve {r : ℕ} (f : ℕ+ ↪ ℕ+) (hf : ∀ i, i ≤ f i) (u : Fin r → MissingWave) :
    Conserving (projected (omitFamily (fun i => extendModes f (laneWaves u i)))) := by
  let W (i : Fin r) := extendModes f (laneWaves u i)
  let P := omitFamily W
  rw [projected_conserves_iff]
  intro x y h
  have hk : criticalOperator (x-y) ∈ P.val.toLinearMap.ker := by
    change P.val (criticalOperator (x-y)) = 0
    rw [map_sub,map_sub,sub_eq_zero]
    exact h
  rw [omitFamily_ker] at hk
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hk
  let v := ∑ i, c i • laneWaves u i
  have he : extendModes f v = criticalOperator (x-y) := by
    simpa only [v,map_sum,map_smul,W] using hc
  have hm : v ∈ familySpan (laneWaves u) := Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have hr := restrictModes_mem_heat hf (x := criticalOperator (x-y)) ⟨x-y,rfl⟩
  rw [← he,restrict_extend] at hr
  have hz := lane_span_meets_heat u hm hr
  rw [hz,map_zero] at he
  exact sub_eq_zero.mp (critical_injective (he.symm.trans (map_zero _).symm))

/-- Every direction is a norm limit of waves outside the critical heat range. -/
theorem exists_missingWave_tendsto (x : Gas) : ∃ v : ℕ → MissingWave, Tendsto (fun n => (v n).val) atTop (𝓝 x) := by
  let R := LinearMap.range criticalOperator.toLinearMap
  by_cases hx : x ∈ R
  · let w (n : ℕ) := x + (occupationWeight n:ℂ) • reciprocalTail
    have hw (n : ℕ) : w n ∉ R := by
      intro h
      have hs := (R.add_mem_iff_right hx).mp h
      exact reciprocalTail_outside ((R.smul_mem_iff (Complex.ofReal_ne_zero.mpr (occupationWeight_pos n).ne')).mp hs)
    refine ⟨fun n => ⟨w n,hw n⟩,?_⟩
    have ht : Tendsto (fun n => (occupationWeight n:ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp occupationWeight_tendsto
    simpa only [w,zero_smul,add_zero] using (tendsto_const_nhds (x := x)).add
      (ht.smul (tendsto_const_nhds (x := reciprocalTail)))
  · exact ⟨fun _ => ⟨x,hx⟩,tendsto_const_nhds⟩

/-- Convergence of finitely many nonzero orthogonal omitted directions gives norm convergence of the squares. -/
theorem tendsto_family_square {r : ℕ} {u : ℕ → Fin r → Gas} {v : Fin r → Gas}
    (hn : ∀ n i, u n i ≠ 0) (ho : ∀ n i j, i ≠ j → inner ℂ (u n i) (u n j) = 0)
    (hv : ∀ i, v i ≠ 0) (hvO : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0)
    (h : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) :
    Tendsto (fun n => projected (omitFamily (u n))^2) atTop (𝓝 (projected (omitFamily v)^2)) := by
  have he (i : Fin r) : Tendsto (fun n => lineCorrection (u n i)) atTop (𝓝 (lineCorrection (v i))) :=
    tendsto_const_nhds.sub (((continuousAt_omitted_root (hv i)).tendsto.comp (h i)).pow 2)
  have eqn (n : ℕ) := family_square (hn n) (ho n)
  simp only [eqn,family_square hv hvO]
  exact tendsto_const_nhds.sub (tendsto_finsetSum Finset.univ (fun i _ => he i))

/-- A norm limit of physical squares with specified approximation numbers gives a point of the physical spectral closure. -/
theorem mem_closure_physicalSpectra_of_squares {r : ℕ} {P : ℕ → Projection} (hd : ∀ n, MissingDimension (P n) r)
    (hc : ∀ n, Conserving (projected (P n))) {A : GasOp} (h : Tendsto (fun n => projected (P n)^2) atTop (𝓝 A))
    (b : SpectralBand r) (hb : ∀ k, _root_.RHTower.approxNumber A k = (b k).val) :
    b ∈ closure (physicalSpectra r) := by
  let s (n : ℕ) := physicalSpectrum (P n) (hd n) (hc n)
  have ht : Tendsto s atTop (𝓝 b) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_subtype_rng.mpr
    rw [← hb k]
    exact ((_root_.RHTower.approxNumber_lipschitz k).continuous.tendsto A).comp h
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n => ⟨P n,hd n,hc n,rfl⟩)

#print axioms extended_lanes_conserve
#print axioms exists_missingWave_tendsto
#print axioms tendsto_family_square
#print axioms mem_closure_physicalSpectra_of_squares

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
