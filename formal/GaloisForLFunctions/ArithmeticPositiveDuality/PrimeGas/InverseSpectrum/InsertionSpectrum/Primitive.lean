import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Content
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Ordered

/-! # Primitive factorization of an exterior wave and its partition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Remove every prime occupation shared by all coordinates. -/
def primitiveWave (v : MissingWave) : MissingWave :=
  ((preimage_iff_dvd_content (occupationContent v) v).mpr dvd_rfl).exists.choose

theorem insert_primitive (v : MissingWave) : insertMissing (occupationContent v) (primitiveWave v) = v :=
  ((preimage_iff_dvd_content (occupationContent v) v).mpr dvd_rfl).exists.choose_spec

theorem primitive_content (v : MissingWave) : occupationContent (primitiveWave v) = 1 := by
  have h := congrArg occupationContent (insert_primitive v)
  rw [content_insert] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- The common integer and the primitive exterior direction are jointly unique. -/
theorem primitive_factorization (a : ℕ+) (u v : MissingWave) :
    insertMissing a u = v ∧ occupationContent u = 1 ↔ a = occupationContent v ∧ u = primitiveWave v := by
  constructor
  · rintro ⟨he,hp⟩
    have ha := congrArg occupationContent he
    rw [content_insert,hp,mul_one] at ha
    subst a
    exact ⟨rfl,((preimage_iff_dvd_content _ v).mpr dvd_rfl).unique he (insert_primitive v)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨insert_primitive v,primitive_content v⟩

/-- Successive insertions compose on the whole gas by multiplication of their labels. -/
theorem insertMissing_comp (a d : ℕ+) (v : MissingWave) :
    insertMissing a (insertMissing d v) = insertMissing (a*d) v := by
  let V (k : ℕ+) := (insertWave k).toContinuousLinearMap
  have he : (V a).comp (V d) = V (a*d) := by
    apply ContinuousLinearMap.ext_on (s := Set.range (HilbertSchmidt.lpBasis ℕ+))
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ+).dense_span)
    rintro _ ⟨n,rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    change insertWave a (insertWave d (modeWave n)) = insertWave (a*d) (modeWave n)
    rw [insert_mode,insert_mode,insert_mode,mul_assoc]
  exact Subtype.ext (congrArg (fun T : GasOp => T v.val) he)

/-- Removing common occupations selects the same exterior wave along the whole insertion orbit. -/
theorem primitiveWave_insert (a : ℕ+) (v : MissingWave) : primitiveWave (insertMissing a v) = primitiveWave v := by
  have he : insertMissing (a*occupationContent v) (primitiveWave v) = insertMissing a v := by
    rw [← insertMissing_comp,insert_primitive]
  exact ((primitive_factorization _ _ _).mp ⟨he,primitive_content v⟩).2.symm

/-- The content-normalized relative partition is the measured partition loss of the primitive wave. -/
theorem primitive_partition (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    omissionPartition (primitiveWave v) z = omissionPartition v z/heat z (occupationContent v) := by
  apply (eq_div_iff (Complex.exp_ne_zero _)).mpr
  rw [mul_comm,← omissionPartition_insert _ _ hz,insert_primitive]

theorem primitive_partition_insert (a : ℕ+) (v : MissingWave) (z : ℂ) :
    omissionPartition (primitiveWave (insertMissing a v)) z = omissionPartition (primitiveWave v) z := by
  rw [primitiveWave_insert]

/-- Two physical spectra agree exactly when their common factors and their primitive spectra agree. -/
theorem spectra_eq_iff_content_and_primitive (v w : MissingWave) :
    missingSpectrum v = missingSpectrum w ↔ occupationContent v = occupationContent w ∧
      missingSpectrum (primitiveWave v) = missingSpectrum (primitiveWave w) := by
  have hv (x : MissingWave) : refinedSpectrum (occupationContent x) (missingSpectrum (primitiveWave x)) = missingSpectrum x := by
    rw [← missingSpectrum_insert,insert_primitive]
  constructor
  · intro h
    have hc := content_eq_of_spectrum h
    refine ⟨hc,refined_injective (occupationContent w) ?_⟩
    calc
      refinedSpectrum (occupationContent w) (missingSpectrum (primitiveWave v)) = missingSpectrum v := hc ▸ hv v
      _ = missingSpectrum w := h
      _ = _ := (hv w).symm
  · rintro ⟨hc,hs⟩
    rw [← hv v,← hv w,hc,hs]

#print axioms spectra_eq_iff_content_and_primitive
#print axioms insert_primitive
#print axioms primitive_content
#print axioms primitive_factorization
#print axioms insertMissing_comp
#print axioms primitiveWave_insert
#print axioms primitive_partition
#print axioms primitive_partition_insert

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
