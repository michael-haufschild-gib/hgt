import GaloisForLFunctions.RHTower.WeilPaperNullObservationDirections
import GaloisForLFunctions.RHTower.WeilPaperPositiveMixtureCubes
import GaloisForLFunctions.RHTower.WeilPaperComplexNullObservations
import GaloisForLFunctions.RHTower.WeilPaperTorusSpectralClassification

/-!
# Arbitrarily high-dimensional cubes of representing probabilities

Independent sampled directions invisible to a finite observer admit simultaneous
positive realization. One common positive background and one common normalization
retain all directions, all complex integer constraints, and the fixed observations.
-/

open Complex
open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Every finite observer misses arbitrarily many real kernel directions, jointly realized
inside a positive normalized cube with a faithful full-kernel parameterization. -/
theorem exists_spectralRepresentingMeasure_cube_real_directions (k n : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, T (c s).1.1 = T (c t).1.1) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) ∧
      Function.Injective (fun v => mixtureSample (L v)) ∧
      (∀ v y, (mixtureSample (L v) y).im = 0) := by
  classical
  obtain ⟨D, hD, hinj⟩ := exists_paperNullObservationDirections k n T
  obtain ⟨u, _, _, _⟩ := exists_complexNullMixtures_same_finite_observations 0 0
  let e (i : Fin n) : Fin n → ℝ := Pi.single i 1
  let p (i : Fin n) := paperRealMixture (paperNullPositivePart (D (e i)))
  let q (i : Fin n) := paperRealMixture (paperNullNegativePart (D (e i)))
  let D' := paperRealMixture.comp (paperNullMassSpace.subtype.comp D)
  have hp i : ∀ f, 0 ≤ p i f :=
    paperRealMixture_nonneg _ (paperNullPositivePart_nonneg (D (e i)))
  have hq i : ∀ f, 0 ≤ q i f :=
    paperRealMixture_nonneg _ (paperNullNegativePart_nonneg (D (e i)))
  have hpq i : p i - q i = D' (e i) := by
    change paperRealMixture _ - paperRealMixture _ = paperRealMixture (D (e i)).1
    rw [← map_sub, paperNullPositivePart_sub_negativePart]
  have hmass i : mixtureSample (p i) 0 = mixtureSample (q i) 0 := by
    simpa only [p, q, mixtureSample_paperRealMixture_zero] using
      paperNullPositivePart_mass_eq (D (e i))
  have hnull i (j : ℕ) (hj : 2 ≤ j) :
      mixtureSample (p i) (Real.log j) = 0 ∧ mixtureSample (q i) (Real.log j) = 0 :=
    ⟨(defect_eq_zero_iff_paperRealMixture_complex_null _).mp
      (defect_paperNullPositivePart (D (e i))) j hj,
      (defect_eq_zero_iff_paperRealMixture_complex_null _).mp
      (defect_paperNullNegativePart (D (e i))) j hj⟩
  let raw := paperMixtureCube u.1.1 p q
  let M : ℝ := 1 + ∑ i, (mixtureSample (q i) 0).re
  have hM : 0 < M := by
    have hn i : 0 ≤ (mixtureSample (q i) 0).re :=
      (norm_nonneg _).trans (mixtureSample_norm_le_mass (q i) (hq i) 0)
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)
    dsimp [M]
    linarith
  have hrawpos t : ∀ f, 0 ≤ raw t f := paperMixtureCube_nonneg _ _ _ u.1.2.1 hp hq t
  have hrawmass t : mixtureSample (raw t) 0 = (M : ℂ) := by
    calc
      _ = mixtureSample u.1.1 0 + ∑ i, mixtureSample (q i) 0 :=
        paperMixtureCube_observe_eq (Finsupp.linearCombination ℝ _) _ _ _ hmass t
      _ = (M : ℂ) := by
        rw [u.1.2.2]
        simp only [M, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mixtureSample_zero_real (q i)
  have hrawnull t (j : ℕ) (hj : 2 ≤ j) : mixtureSample (raw t) (Real.log j) = 0 := by
    have hpair i : mixtureSample (p i) (Real.log j) = mixtureSample (q i) (Real.log j) :=
      (hnull i j hj).1.trans (hnull i j hj).2.symm
    have h := paperMixtureCube_observe_eq (Finsupp.linearCombination ℝ
      (fun f : WeilTestFn => Zeta23.EF.weilTest f.1 f.1 (Real.log j))) u.1.1 p q hpair t
    change mixtureSample (raw t) (Real.log j) =
      mixtureSample u.1.1 (Real.log j) + ∑ i, mixtureSample (q i) (Real.log j) at h
    simpa [u.2 j hj, fun i => (hnull i j hj).2] using h
  have hlinear (v : Fin n → ℝ) : (∑ i, v i • D' (e i)) = D' v := by
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    ext j
    simp [e, Pi.single_apply]
  have hrawdiff s t : raw s - raw t = D' (fun i => (s i).1 - (t i).1) := by
    rw [paperMixtureCube_sub]
    simp_rw [hpq]
    exact hlinear _
  have hrawT s t : T (raw s) = T (raw t) := by
    apply sub_eq_zero.mp
    rw [← map_sub, hrawdiff]
    exact hD _
  let c (t : Fin n → Set.Icc (0 : ℝ) 1) : ComplexNullMixture :=
    ⟨paperNormalizeMass M hM (raw t) (hrawpos t) (hrawmass t), by
      intro j hj
      change mixtureSample (M⁻¹ • raw t) (Real.log j) = 0
      rw [mixtureSample_smul, hrawnull t j hj, smul_zero]⟩
  let t₀ : Fin n → Set.Icc (0 : ℝ) 1 := fun _ => ⟨0, by simp⟩
  let L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ) := M⁻¹ • D'
  have hkernel : Function.Injective (fun v => mixtureSample (L v)) := by
    intro v w h
    apply hinj
    ext j
    let r := paperConsecutiveEdge (k + n) j
    let y := Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)
    have hs := congrFun h y
    change mixtureSample (M⁻¹ • D' v) y = mixtureSample (M⁻¹ • D' w) y at hs
    rw [mixtureSample_smul, mixtureSample_smul, Complex.real_smul, Complex.real_smul] at hs
    have hs' := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hM.ne')) hs
    change mixtureSample (paperRealMixture (D v).1) y =
      mixtureSample (paperRealMixture (D w).1) y at hs'
    rw [mixtureSample_paperRealMixture, mixtureSample_paperRealMixture] at hs'
    exact Complex.ofReal_injective hs'
  have hreal (v : Fin n → ℝ) (y : ℝ) : (mixtureSample (L v) y).im = 0 := by
    change (mixtureSample (M⁻¹ • paperRealMixture (D v).1) y).im = 0
    rw [mixtureSample_smul, mixtureSample_paperRealMixture, Complex.real_smul]
    simp
  refine ⟨c, M⁻¹ • raw t₀, L, fun v w h => hkernel (congrArg mixtureSample h),
    ?_, ?_, ?_, hkernel, hreal⟩
  · intro t
    change M⁻¹ • raw t = M⁻¹ • raw t₀ + M⁻¹ • D' (fun i => (t i).1)
    rw [← smul_add]
    congr 1
    have hd := hrawdiff t t₀
    simp only [t₀, sub_zero] at hd
    exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  · intro s t
    change T (M⁻¹ • raw s) = T (M⁻¹ • raw t)
    rw [map_smul, map_smul, hrawT]
  · intro s t hst
    let v : Fin n → ℝ := fun i => (s i).1 - (t i).1
    have hs : mixtureSample (c s).1.1 = mixtureSample (c t).1.1 :=
      (spectralProbability_eq_iff_mixtureSample_eq _ _).mp
        ((spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mp
          (congrArg Subtype.val hst))
    have hd : mixtureSample (L v) = 0 := by
      funext y
      change mixtureSample (M⁻¹ • D' (fun i => (s i).1 - (t i).1)) y = 0
      rw [← hrawdiff s t, smul_sub, mixtureSample_sub]
      exact sub_eq_zero.mpr (congrFun hs y)
    have hv : v = 0 := hkernel (hd.trans (by funext y; simp [mixtureSample]))
    funext i
    apply Subtype.ext
    exact sub_eq_zero.mp (congrFun hv i)

/-- Any finite real observation vector is constant on an injectively parameterized cube
of representing spectral probabilities of every finite dimension. -/
theorem exists_injective_spectralRepresentingMeasure_cube (k n : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, T (c s).1.1 = T (c t).1.1) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  obtain ⟨c, b, L, hL, haff, hT, hinj, _, _⟩ :=
    exists_spectralRepresentingMeasure_cube_real_directions k n T
  exact ⟨c, b, L, hL, haff, hT, hinj⟩

/-- Full Weil energy and any finite set of complex correlations can stay fixed on
injective cubes of representing spectral probabilities of arbitrary dimension. -/
theorem exists_spectralRepresentingMeasure_cube_same_energy_samples (n : ℕ) {k : ℕ}
    (y : Fin k → ℝ) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, energy (c s).1.1 = energy (c t).1.1) ∧
      (∀ i s t, mixtureSample (c s).1.1 (y i) = mixtureSample (c t).1.1 (y i)) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨c, b, L, hL, haff, hc, hinj⟩ := exists_injective_spectralRepresentingMeasure_cube
    (Module.finrank ℝ E) n (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs s t : paperEnergySampleObserver y (c s).1.1 =
      paperEnergySampleObserver y (c t).1.1 := e.injective (hc s t)
  exact ⟨c, b, L, hL, haff, fun s t => congrArg Prod.fst (hobs s t),
    fun i s t => congrFun (congrArg Prod.snd (hobs s t)) i, hinj⟩

end RHTower.WeilWorkPBAP
