import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.PhysicalLimits
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockIndex

/-! # Physical square limits on disjoint translated progressions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Squared heat operators with exactly r missing directions. -/
def physicalSquares (r : ℕ) : Set GasOp :=
  {A | ∃ (P : Projection) (_ : MissingDimension P r) (_ : Conserving (projected P)), projected P^2 = A}

/-- A norm limit of physical squares has its complete singular sequence in the physical spectral closure. -/
theorem spectral_limit_of_square_limit {r : ℕ} {A : GasOp} (hA : A ∈ closure (physicalSquares r)) :
    ∃ b ∈ closure (physicalSpectra r), ∀ k, (b k).val = _root_.RHTower.approxNumber A k := by
  obtain ⟨v,hv,ht⟩ := mem_closure_iff_seq_limit.mp hA
  change ∀ n, ∃ (P : Projection) (_ : MissingDimension P r) (_ : Conserving (projected P)), projected P^2 = v n at hv
  choose P hd hc he using hv
  have hs : Tendsto (fun n => projected (P n)^2) atTop (𝓝 A) := by simpa only [he] using ht
  have hband (k : ℕ) : _root_.RHTower.approxNumber A k ∈ Icc (occupationWeight (k+r)) (occupationWeight k) := by
    apply isClosed_Icc.mem_of_tendsto (((_root_.RHTower.approxNumber_lipschitz k).continuous.tendsto A).comp hs)
    exact Eventually.of_forall (fun n => (physicalSpectrum (P n) (hd n) (hc n) k).property)
  let b : SpectralBand r := fun k => ⟨_,hband k⟩
  exact ⟨b,mem_closure_physicalSpectra_of_squares hd hc hs b (fun _ => rfl),fun _ => rfl⟩

/-- Translate the r disjoint occupation progressions past an arbitrary prefix. -/
def translatedMode {r : ℕ} (N : ℕ) (j : Fin r) (x : Gas) :=
  extendModes (skipLabel 0 N) (extendModes (progression j) x)

theorem translatedMode_continuous {r : ℕ} (N : ℕ) (j : Fin r) :
    Continuous (translatedMode N j) := (extendModes (skipLabel 0 N)).continuous.comp (extendModes (progression j)).continuous

theorem translatedMode_norm {r : ℕ} (N : ℕ) (j : Fin r) (x : Gas) : ‖translatedMode N j x‖ = ‖x‖ := by
  unfold translatedMode
  rw [LinearIsometry.norm_map,LinearIsometry.norm_map]

theorem translatedMode_ne {r : ℕ} (N : ℕ) (j : Fin r) {x : Gas} (hx : x ≠ 0) : translatedMode N j x ≠ 0 :=
  norm_ne_zero_iff.mp ((translatedMode_norm N j x).trans_ne (norm_ne_zero_iff.mpr hx))

theorem translatedMode_orthogonal {r : ℕ} (N : ℕ) {i j : Fin r} (hne : i ≠ j) (x y : Gas) :
    inner ℂ (translatedMode N i x) (translatedMode N j y) = 0 := by
  unfold translatedMode
  rw [LinearIsometry.inner_map_map]
  exact extendModes_orthogonal (progression_separate hne) x y

theorem translatedMode_single {r : ℕ} (N : ℕ) (j : Fin r) (n : ℕ+) :
    translatedMode N j (modeWave n) = modeWave (skipLabel 0 N (progression j n)) := by
  unfold translatedMode
  rw [show extendModes (progression j) (modeWave n) = modeWave (progression j n) from
    _root_.RHTower.lpScalarInjection_single _ _ _ _]
  exact _root_.RHTower.lpScalarInjection_single _ _ _ _

theorem translatedMode_first {r : ℕ} (N : ℕ) (j : Fin r) :
    translatedMode N j (modeWave 1) = modeWave (number (N+j.val)) := by
  rw [translatedMode_single,progression_one,skipLabel_number]
  simp only [skipIndex,Nat.not_lt_zero,if_false,Nat.add_comm j.val]

/-- The normalized family need only be exterior in the approximating operators. Any nonzero lane directions may occur in the limit. -/
theorem translated_square_mem_closure {r : ℕ} (N : ℕ) (x : Fin r → Gas) (hx : ∀ j, x j ≠ 0) :
    projected (omitFamily (fun j => translatedMode N j (x j)))^2 ∈ closure (physicalSquares r) := by
  choose v hv using fun j => exists_missingWave_tendsto (x j)
  let u (n : ℕ) (j : Fin r) := v j n
  let W (n : ℕ) (j : Fin r) := translatedMode N j (u n j).val
  have hn (n : ℕ) (j : Fin r) : W n j ≠ 0 := translatedMode_ne N j (missingWave_ne_zero _)
  have ho (n : ℕ) (i j : Fin r) (h : i ≠ j) : inner ℂ (W n i) (W n j) = 0 :=
    translatedMode_orthogonal N h _ _
  have ht := tendsto_family_square hn ho (fun j => translatedMode_ne N j (hx j))
    (fun i j h => translatedMode_orthogonal N h (x i) (x j))
    (fun j => ((translatedMode_continuous N j).tendsto (x j)).comp (hv j))
  apply mem_closure_of_tendsto ht
  exact Eventually.of_forall (fun n => ⟨omitFamily (W n),missingDimension_family (hn n) (ho n),
    extended_lanes_conserve (skipLabel 0 N) (skipLabel_increases 0 N) (u n),rfl⟩)

#print axioms spectral_limit_of_square_limit
#print axioms translated_square_mem_closure

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
