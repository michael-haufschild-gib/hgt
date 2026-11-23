import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Canonical
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates

/-! # Restricting heat waves to subsequences of occupations

An injection that only increases the occupation number decreases heat
amplitudes. Its coordinate pullback therefore preserves the heat range.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

abbrev extendModes (f : ℕ+ ↪ ℕ+) := _root_.RHTower.lpScalarInjection f f.injective
abbrev restrictModes (f : ℕ+ ↪ ℕ+) := _root_.RHTower.lpCoordinatePullback (E := ℂ) f f.injective

theorem restrict_extend (f : ℕ+ ↪ ℕ+) (x : Gas) : restrictModes f (extendModes f x) = x := by
  apply lp.ext
  funext i
  exact _root_.RHTower.lpScalarInjection_coordinate f f.injective x i

theorem restrict_extend_disjoint {f g : ℕ+ ↪ ℕ+} (hg : ∀ i j, f i ≠ g j) (x : Gas) :
    restrictModes f (extendModes g x) = 0 := by
  apply lp.ext
  funext i
  exact _root_.RHTower.lpScalarInjection_coordinate_of_not_mem g g.injective x (f i)
    (fun ⟨j,h⟩ => hg i j h.symm)

theorem attenuation_antitone : Antitone attenuation := fun i j hij =>
  inv_anti₀ (Real.sqrt_pos_of_pos (by exact_mod_cast i.pos : 0 < (i.val:ℝ)))
    (Real.sqrt_le_sqrt (by exact_mod_cast hij : (i.val:ℝ) ≤ (j.val:ℝ)))

/-- Pulling back along an occupation-increasing injection takes physical heat waves to physical heat waves. -/
theorem restrictModes_mem_heat {f : ℕ+ ↪ ℕ+} (hf : ∀ n, n ≤ f n) {x : Gas}
    (hx : x ∈ LinearMap.range criticalOperator.toLinearMap) :
    restrictModes f x ∈ LinearMap.range criticalOperator.toLinearMap := by
  obtain ⟨u,rfl⟩ := hx
  let m (n : ℕ+) : ℂ := ((attenuation (f n)/attenuation n:ℝ):ℂ)
  have hm (n : ℕ+) : ‖m n‖ ≤ 1 := by
    change ‖((attenuation (f n)/attenuation n:ℝ):ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg (attenuation_pos _).le (attenuation_pos _).le)]
    exact (div_le_one (attenuation_pos n)).mpr (attenuation_antitone (hf n))
  let M := HTGeometry.LpDiagonal.lpDiag m 1 zero_le_one hm
  refine ⟨M (restrictModes f u),?_⟩
  apply lp.ext
  funext n
  change (attenuation n:ℂ)*(m n*u (f n)) = (attenuation (f n):ℂ)*u (f n)
  rw [← mul_assoc]
  congr 1
  change (attenuation n:ℂ)*((attenuation (f n)/attenuation n:ℝ):ℂ) = _
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp [(attenuation_pos n).ne']

/-- A wave exterior to the heat range stays exterior after extension to higher occupations. -/
theorem extendModes_outside {f : ℕ+ ↪ ℕ+} (hf : ∀ n, n ≤ f n) {v : Gas}
    (hv : v ∉ LinearMap.range criticalOperator.toLinearMap) :
    extendModes f v ∉ LinearMap.range criticalOperator.toLinearMap :=
  fun h => hv (restrict_extend f v ▸ restrictModes_mem_heat hf h)

/-- Disjoint coordinate embeddings have orthogonal ranges. -/
theorem extendModes_orthogonal {f g : ℕ+ ↪ ℕ+} (hg : ∀ i j, f i ≠ g j) (x y : Gas) :
    inner ℂ (extendModes f x) (extendModes g y) = 0 := by
  have h := adjoint_inner_right (extendModes f).toContinuousLinearMap x (extendModes g y)
  rw [← _root_.RHTower.lpCoordinatePullback_eq_adjoint_lpScalarInjection] at h
  change inner ℂ x (restrictModes f (extendModes g y)) = _ at h
  rw [restrict_extend_disjoint hg,inner_zero_right] at h
  exact h.symm

/-- The diagonal heat preserves each embedded coordinate sector. -/
theorem heat_extendModes (f : ℕ+ ↪ ℕ+) (x : Gas) :
    ∃ z : Gas, criticalOperator (extendModes f x) = extendModes f z := by
  let a (n : ℕ+) : ℂ := attenuation (f n)
  have ha (n : ℕ+) : ‖a n‖ ≤ 1 := by
    change ‖(attenuation (f n):ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le]
    have h := attenuation_antitone (show (1:ℕ+) ≤ f n from (f n).pos)
    simpa [attenuation,gain] using h
  let M := HTGeometry.LpDiagonal.lpDiag a 1 zero_le_one ha
  refine ⟨M x,?_⟩
  apply lp.ext
  funext i
  rw [critical_apply]
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j,rfl⟩ := hi
    rw [_root_.RHTower.lpScalarInjection_coordinate,_root_.RHTower.lpScalarInjection_coordinate]
    rfl
  · rw [_root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ _ _ hi,
      _root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ _ _ hi,mul_zero]

#print axioms heat_extendModes
#print axioms restrictModes_mem_heat
#print axioms extendModes_outside

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
