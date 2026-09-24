import GaloisForLFunctions.RHTower.WeightOneCliffordSpectralClosure
import GaloisForLFunctions.HTGeometry.DilationSpectralType
import GaloisForLFunctions.HTGeometry.ResolventCompactness

/-!
# Bare weight-one Clifford operator has no Xi spectral occurrence

The exact Fourier square is multiplication by `a² - (2πξ)²`. Every level set has at most
two points and hence zero Lebesgue measure. Thus neither the natural Clifford square nor its
Dirac root has any nonzero `L²` eigenvector, for any mass. The square's resolvent at `i` is
noncompact. A direct eigenvalue or compact-resolvent determinant identification with Xi is
therefore impossible for this unchanged operator. An arithmetic scattering construction or
a changed domain/operator is not excluded.
-/

open MeasureTheory

namespace RHTower

private theorem weightOneSquare_level_finite (a : ℝ) (lam : ℂ) :
    Set.Finite {ξ : ℝ | ((weightOneSpectralSquareEnergy a ξ : ℝ) : ℂ) = lam} := by
  by_cases h : ({ξ : ℝ | ((weightOneSpectralSquareEnergy a ξ : ℝ) : ℂ) = lam}).Nonempty
  · obtain ⟨u, hu⟩ := h
    have hsub : {ξ : ℝ | ((weightOneSpectralSquareEnergy a ξ : ℝ) : ℂ) = lam} ⊆
        ({u, -u} : Set ℝ) := by
      intro ξ hξ
      have he : weightOneSpectralSquareEnergy a ξ =
          weightOneSpectralSquareEnergy a u := by
        exact_mod_cast hξ.trans hu.symm
      have hc : (2 * Real.pi) ^ 2 ≠ (0 : ℝ) := by positivity
      have hm : (2 * Real.pi) ^ 2 * ξ ^ 2 = (2 * Real.pi) ^ 2 * u ^ 2 := by
        unfold weightOneSpectralSquareEnergy at he
        linarith
      have hs : ξ ^ 2 = u ^ 2 := mul_left_cancel₀ hc hm
      have hprod : (ξ - u) * (ξ + u) = 0 := by nlinarith [hs]
      have hsplit : ξ = u ∨ ξ = -u := by
        rcases mul_eq_zero.mp hprod with h | h
        · left; linarith
        · right; linarith
      simpa using hsplit
    have hfin : ({u, -u} : Set ℝ).Finite := by simp
    exact hfin.subset hsub
  · have hempty : {ξ : ℝ | ((weightOneSpectralSquareEnergy a ξ : ℝ) : ℂ) = lam} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty]
    exact Set.finite_empty

/-- **Sharp frequency-fibre classification.** Every nonempty level of the W1C square
consists of exactly the two reflected Fourier frequencies (one at the turning point).
There are no hidden arithmetic spectral labels in the unchanged multiplier. -/
theorem weightOneSpectralSquareEnergy_fibre_eq_twoPoint (a u : ℝ) :
    {ξ : ℝ | weightOneSpectralSquareEnergy a ξ = weightOneSpectralSquareEnergy a u} =
      ({u, -u} : Set ℝ) := by
  ext ξ
  constructor
  · intro h
    change weightOneSpectralSquareEnergy a ξ = weightOneSpectralSquareEnergy a u at h
    have hc : (2 * Real.pi) ^ 2 ≠ (0 : ℝ) := by positivity
    have hm : (2 * Real.pi) ^ 2 * ξ ^ 2 = (2 * Real.pi) ^ 2 * u ^ 2 := by
      unfold weightOneSpectralSquareEnergy at h
      linarith
    have hs : ξ ^ 2 = u ^ 2 := mul_left_cancel₀ hc hm
    have hprod : (ξ - u) * (ξ + u) = 0 := by nlinarith [hs]
    rcases mul_eq_zero.mp hprod with h | h
    · simp [sub_eq_zero.mp h]
    · have : ξ = -u := by linarith
      simp [this]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · rfl
    · simp [weightOneSpectralSquareEnergy]

/-- The exact W1C square has empty point spectrum at every real mass. -/
theorem weightOneSpectralSquare_hasNoEigenvector (a : ℝ) :
    GaloisForLFunctions.HTGeometry.HasNoEigenvector (weightOneSpectralSquare a) := by
  apply GaloisForLFunctions.HTGeometry.hasNoEigenvector_maximalRealL2Mul
  intro lam
  exact (weightOneSquare_level_finite a lam).measure_zero _

/-- The natural Clifford root also has empty point spectrum: any eigenvector would give
an eigenvector of its exact natural square. -/
theorem weightOneSpectralDirac_hasNoEigenvector (a : ℝ) :
    GaloisForLFunctions.HTGeometry.HasNoEigenvector (weightOneSpectralDirac a) := by
  intro lam f hf
  let Q := weightOneSpectralDirac a
  have hqmem : Q f ∈ Q.domain := by
    rw [hf]
    exact Q.domain.smul_mem lam f.property
  have hsmem : (f : SoninL2) ∈ (weightOneSpectralSquare a).domain :=
    (weightOneSpectralSquare_domain_iff_naturalDiracSquare a (f : SoninL2)).2
      ⟨f.property, hqmem⟩
  have hqnext : Q ⟨Q f, hqmem⟩ = lam ^ 2 • (f : SoninL2) := by
    have heq : (⟨Q f, hqmem⟩ : Q.domain) = lam • f := Subtype.ext hf
    rw [heq]
    calc
      Q (lam • f) = lam • Q f := Q.map_smul lam f
      _ = lam ^ 2 • (f : SoninL2) := by rw [hf, smul_smul, pow_two]
  have hsquare : weightOneSpectralSquare a ⟨(f : SoninL2), hsmem⟩ =
      lam ^ 2 • (f : SoninL2) := by
    rw [← weightOneSpectralDirac_sq_apply a ⟨(f : SoninL2), hsmem⟩ f.property hqmem]
    exact hqnext
  exact weightOneSpectralSquare_hasNoEigenvector a (lam ^ 2)
    ⟨(f : SoninL2), hsmem⟩ hsquare

/-- The unchanged W1C square has no compact resolvent at `i`. Thus the existing
compact-resolvent Fredholm-determinant receiver cannot be attached to it directly. -/
theorem weightOneSpectralSquare_not_compactResolvent (a : ℝ) :
    ¬ IsCompactOperator
      (GaloisForLFunctions.HTGeometry.resolventCLM
        (weightOneSpectralSquare_isSelfAdjoint a)
        (z := Complex.I) (by norm_num)) := by
  have hzw : -Complex.I = (starRingEnd ℂ) Complex.I := by simp
  exact GaloisForLFunctions.HTGeometry.not_isCompactOperator_resolventCLM
    (weightOneSpectralSquare_isSelfAdjoint a)
    (weightOneSpectralSquare_hasNoEigenvector a)
    (z := Complex.I) (w := -Complex.I)
    (by norm_num) (by norm_num) hzw

end RHTower
