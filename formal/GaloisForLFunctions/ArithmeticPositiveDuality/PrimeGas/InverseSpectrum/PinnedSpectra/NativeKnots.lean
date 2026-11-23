import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.SpectralBasis
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.PrescribedModes

/-! # Native eigenvalues surviving a single omitted direction -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open InnerProductSpace ContinuousLinearMap

private theorem native_square_at (y : Gas) (n : ℕ) : squareHeat.val y (number n) = (occupationWeight n:ℂ)*y (number n) := by
  change (attenuation (number n):ℂ)*((attenuation (number n):ℂ)*y (number n)) = _
  rw [← mul_assoc,← sq,← Complex.ofReal_pow]
  rfl

private theorem native_coordinate_ne {i j : ℕ} (h : i ≠ j) :
    (occupationWeight i:ℂ)-(occupationWeight j:ℂ) ≠ 0 :=
  sub_ne_zero.mpr (fun he => h (occupationWeight_strictAnti.injective (Complex.ofReal_inj.mp he)))

/-- For a native pole, the rank-one eigenvector equation forces the corresponding omitted amplitude to vanish. -/
theorem omitted_native_eigen_iff (v : MissingWave) (j : ℕ) :
    (∃ y : Gas, y ≠ 0 ∧ (projected (omitLine v.val)^2) y = (occupationWeight j:ℂ) • y) ↔ v.val (number j) = 0 := by
  let w := criticalOperator v.val
  let d : ℂ := ((‖v.val‖^2:ℝ):ℂ)⁻¹
  have hd : d ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))))
  have hw : w (number j) = 0 ↔ v.val (number j) = 0 := by
    change (attenuation (number j):ℂ)*v.val (number j) = 0 ↔ _
    rw [mul_eq_zero,or_iff_right (Complex.ofReal_ne_zero.mpr (attenuation_pos _).ne')]
  constructor
  · rintro ⟨y,hy,he⟩
    apply hw.mp
    by_contra hne
    rw [line_square] at he
    change squareHeat.val y-d • (inner ℂ w y • w) = (occupationWeight j:ℂ) • y at he
    rw [smul_smul] at he
    let c := d*inner ℂ w y
    have hcoord (n : ℕ) : ((occupationWeight n:ℂ)-(occupationWeight j:ℂ))*y (number n) = c*w (number n) := by
      have h := congrArg (fun u : Gas => u (number n)) he
      change squareHeat.val y (number n)-c*w (number n) = (occupationWeight j:ℂ)*y (number n) at h
      rw [native_square_at] at h
      linear_combination h
    have h0 := hcoord j
    rw [sub_self,zero_mul] at h0
    have hc : c = 0 := (mul_eq_zero.mp h0.symm).resolve_right hne
    have ho : inner ℂ w y = 0 := (mul_eq_zero.mp hc).resolve_left hd
    have hoff (n : ℕ) (hn : n ≠ j) : y (number n) = 0 := by
      have h := hcoord n
      rw [hc,zero_mul] at h
      exact (mul_eq_zero.mp h).resolve_left (native_coordinate_ne hn)
    rw [lp.inner_eq_tsum,← Equiv.pnatEquivNat.symm.tsum_eq] at ho
    change (∑' n, inner ℂ (w (number n)) (y (number n))) = 0 at ho
    rw [tsum_eq_single j (fun n hn => by rw [hoff n hn,inner_zero_right])] at ho
    rw [RCLike.inner_apply] at ho
    have hj : y (number j) = 0 := (mul_eq_zero.mp ho).resolve_right (by simpa using hne)
    apply hy
    apply lp.ext
    funext l
    obtain ⟨n,rfl⟩ := number_surjective l
    exact (eq_or_ne n j).elim (fun h => h ▸ hj) (hoff n)
  · intro hj
    let y := modeWave (number j)
    have hnorm := modeWave_norm (number j)
    have hy : y ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
    have ho : inner ℂ w y = 0 := by simp [y,modeWave,lp.inner_single_right,hw.mpr hj]
    refine ⟨y,hy,?_⟩
    rw [line_square]
    change squareHeat.val y-d • (inner ℂ w y • w) = _
    rw [ho,zero_smul,smul_zero,sub_zero]
    change criticalOperator (criticalOperator (modeWave (number j))) = _
    rw [heat_modeWave,map_smul,heat_modeWave,smul_smul,← sq,← Complex.ofReal_pow]
    rfl

/-- Ordered squared heat spectrum of one actual missing wave. -/
def missingSpectrum (v : MissingWave) : SpectralBand 1 :=
  physicalSpectrum (omitLine v.val) ((missingDimension_one_iff _).mpr ⟨v.val,missingWave_ne_zero v,rfl⟩)
    (((nonzero_line_conserves_iff _).mpr v.property).2)

theorem missingSpectrum_physical (v : MissingWave) : missingSpectrum v ∈ physicalSpectra 1 :=
  ⟨omitLine v.val,(missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩,((nonzero_line_conserves_iff _).mpr v.property).2,rfl⟩

/-- Reading all surviving native eigenvalues recovers the entire zero set of the missing wave. -/
theorem native_level_occurs_iff (v : MissingWave) (j : ℕ) :
    (∃ n, (missingSpectrum v n).val = occupationWeight j) ↔ v.val (number j) = 0 := by
  let P := omitLine v.val
  have hd : MissingDimension P 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc : Conserving (projected P) := ((nonzero_line_conserves_iff _).mpr v.property).2
  rw [← omitted_native_eigen_iff]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨e,he⟩ := exists_physical_heat_basis P hd hc
    exact ⟨e n,norm_ne_zero_iff.mp ((e.orthonormal.1 n).trans_ne one_ne_zero),
      (he n).trans (congrArg (fun t : ℝ => (t:ℂ) • e n) hn)⟩
  · rintro ⟨y,hy,he⟩
    have hhs := conserving_square_hs ⟨projected P,projected_positive P,hc⟩
    obtain ⟨n,hn⟩ := exists_sgVal_eq_of_eigenvalue hhs.isCompactOperator (projected_square_positive P).isSymmetric hy he
      (Complex.ofReal_ne_zero.mpr (occupationWeight_pos j).ne')
    exact ⟨n,(projected_square_sgVal P hd hc n).symm.trans (Complex.ofReal_inj.mp hn)⟩

#print axioms omitted_native_eigen_iff
#print axioms native_level_occurs_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
