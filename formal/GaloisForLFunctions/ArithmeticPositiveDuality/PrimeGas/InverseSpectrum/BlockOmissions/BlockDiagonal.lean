import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockIndex
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FamilyLoss
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.ProgressionReadings
import GaloisForLFunctions.RHTower.IsometricSandwichApproxNumber

/-! # Spectrum of squared heat with a block of coordinates removed -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap

/-- Projection away from finitely many named occupations sets their coordinates to zero. -/
theorem omit_modes_on {r : ℕ} (g : Fin r ↪ ℕ+) (x : Gas) (j : Fin r) :
    (omitFamily (fun k => modeWave (g k))).val x (g j) = 0 := by
  let W := familySpan (fun k => modeWave (g k))
  have hm : modeWave (g j) ∈ W := Submodule.subset_span ⟨j,rfl⟩
  have hp := (W.mem_orthogonal _).mp (Wᗮ.starProjection_apply_mem x) _ hm
  change (Wᗮ.starProjection x) (g j) = 0
  simpa [modeWave,lp.inner_single_left] using hp

/-- All other coordinates are retained by the projection. -/
theorem omit_modes_off {r : ℕ} (g : Fin r ↪ ℕ+) {i : ℕ+} (hi : i ∉ range g) (x : Gas) :
    (omitFamily (fun k => modeWave (g k))).val x i = x i := by
  let W := familySpan (fun k => modeWave (g k))
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (W.starProjection_apply_mem x)
  have hz (j : Fin r) : modeWave (g j) i = 0 :=
    (lp.single_apply (E := fun _ : ℕ+ => ℂ) 2 (g j) (1:ℂ) i).trans (Pi.single_eq_of_ne (fun h => hi ⟨j,h.symm⟩) _)
  have he : (W.starProjection x) i = 0 := by
    rw [← ha]
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,hz,smul_zero,Finset.sum_const_zero]
  change (Wᗮ.starProjection x) i = x i
  rw [Submodule.starProjection_orthogonal',sub_apply,one_apply_eq_self,lp.coeFn_sub,Pi.sub_apply,he,sub_zero]

/-- A finite gap in the heat diagonal deletes exactly those r terms in its decreasing singular sequence. -/
theorem block_square_approxNumber (N r n : ℕ) :
    _root_.RHTower.approxNumber ((projected (omitFamily (fun j => modeWave (blockLabel N r j))))^2) n =
      (blockSpectrum N r n).val := by
  let e : ℕ ≃ ℕ+ := Equiv.ofBijective number ⟨number_injective,number_surjective⟩
  let f := skipLabel N r
  let w (k : ℕ) := occupationWeight (skipIndex N r k)
  let m (i : ℕ+) : ℂ := (w (e.symm i):ℝ)
  have hw (k : ℕ) : 0 ≤ w k := (occupationWeight_pos _).le
  have ha : Antitone w := fun _ _ hij => occupationWeight_antitone ((skipIndex_strictMono N r).monotone hij)
  have hm (i : ℕ+) : ‖m i‖ = w (e.symm i) := (Complex.norm_real _).trans (Real.norm_of_nonneg (hw _))
  let D := _root_.HTGeometry.ellTwoDiagonal m (fun i => (hm i).trans_le (ha (Nat.zero_le _)))
  have hD : _root_.RHTower.approxNumber D n = w n :=
    _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq e hm hw (fun {_ _} hij => ha hij) n
  have hweight (i : ℕ+) : attenuation (f i)^2 = w (e.symm i) := by
    obtain ⟨k,rfl⟩ := e.surjective i
    rw [e.symm_apply_apply]
    change attenuation (skipLabel N r (number k))^2 = _
    rw [skipLabel_number]
    rfl
  let P := omitFamily (fun j => modeWave (blockLabel N r j))
  let U := (extendModes f).toContinuousLinearMap
  have he : projected P ^ 2 = (U ∘L D) ∘L U.adjoint := by
    change projected P ^ 2 = ((extendModes f).toContinuousLinearMap ∘L D) ∘L (extendModes f).toContinuousLinearMap.adjoint
    rw [projected_square,← _root_.RHTower.lpCoordinatePullback_eq_adjoint_lpScalarInjection f f.injective]
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change criticalOperator (P.val (criticalOperator x)) i = extendModes f (D (restrictModes f x)) i
    rw [critical_apply]
    by_cases hi : i ∈ range f
    · obtain ⟨j,rfl⟩ := hi
      have hn : f j ∉ range (blockLabel N r) := fun ⟨k,h⟩ => skipLabel_not_block N r j k h.symm
      rw [omit_modes_off _ hn,critical_apply,_root_.RHTower.lpScalarInjection_coordinate]
      change (attenuation (f j):ℂ)*((attenuation (f j):ℂ)*x (f j)) = (w (e.symm j):ℂ)*x (f j)
      rw [← mul_assoc,← Complex.ofReal_mul,← pow_two,hweight]
    · obtain ⟨j,hj⟩ := mem_block_of_not_skipped hi
      rw [_root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ _ _ hi,← hj,omit_modes_on,mul_zero]
  change _root_.RHTower.approxNumber (projected P ^ 2) n = w n
  rw [he,_root_.RHTower.approxNumber_linearIsometry_adjoint_sandwich,hD]

#print axioms omit_modes_on
#print axioms omit_modes_off
#print axioms block_square_approxNumber

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
