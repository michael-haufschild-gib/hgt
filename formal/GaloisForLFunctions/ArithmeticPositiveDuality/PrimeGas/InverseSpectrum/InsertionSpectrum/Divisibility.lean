import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Sector

/-! # Detecting a common occupation factor from surviving native levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

private theorem recover_supported (a : ℕ+) (v : Gas)
    (h : ∀ k ∉ Set.range (insertLabels a), v k = 0) :
    insertWave a (primeCoShift a v) = v := by
  apply lp.ext
  funext k
  by_cases hk : k ∈ Set.range (insertLabels a)
  · obtain ⟨n,rfl⟩ := hk
    exact (insertWave_at a _ n).trans (primeCoShift_apply a v n)
  · exact (insertWave_off a _ k hk).trans (h k hk).symm

private theorem inserted_preimage_exterior (a : ℕ+) (v : MissingWave) (y : Gas)
    (h : insertWave a y = v.val) : y ∉ LinearMap.range criticalOperator.toLinearMap := by
  rintro ⟨x,hx⟩
  apply v.property
  refine ⟨(attenuation a:ℂ)⁻¹ • insertWave a x,?_⟩
  change criticalOperator ((attenuation a:ℂ)⁻¹ • insertWave a x) = v.val
  rw [map_smul,heat_insertWave,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (attenuation_pos a).ne'),one_smul]
  exact (congrArg (insertWave a) hx).trans h

/-- A common factor of the occupied labels is visible from the native eigenvalues alone. -/
theorem insertion_preimage_iff_native (a : ℕ+) (v : MissingWave) :
    (∃! u : MissingWave, insertMissing a u = v) ↔
      ∀ j, (¬a ∣ number j) → ∃ n, (missingSpectrum v n).val = occupationWeight j := by
  constructor
  · rintro ⟨u,rfl,_⟩ j hj
    apply (native_level_occurs_iff _ j).mpr
    exact insertWave_off a u.val _ (fun ⟨k,hk⟩ => hj ⟨k,hk.symm⟩)
  · intro h
    have hs (k : ℕ+) (hk : k ∉ Set.range (insertLabels a)) : v.val k = 0 := by
      obtain ⟨j,rfl⟩ := number_surjective k
      apply (native_level_occurs_iff _ j).mp (h j ?_)
      exact fun ⟨n,hn⟩ => hk ⟨n,hn.symm⟩
    have he := recover_supported a v.val hs
    let u : MissingWave := ⟨primeCoShift a v.val, inserted_preimage_exterior a v _ he⟩
    refine ⟨u,Subtype.ext he,?_⟩
    intro w hw
    apply Subtype.ext
    exact (remove_insert a w.val).symm.trans (congrArg (fun t : MissingWave => primeCoShift a t.val) hw)

/-- Spectrally indistinguishable omissions admit exactly the same occupation factors. -/
theorem same_spectrum_same_factors {v w : MissingWave} (h : missingSpectrum v = missingSpectrum w) (a : ℕ+) :
    (∃! u : MissingWave, insertMissing a u = v) ↔ ∃! u : MissingWave, insertMissing a u = w := by
  rw [insertion_preimage_iff_native,insertion_preimage_iff_native,h]

#print axioms insertion_preimage_iff_native
#print axioms same_spectrum_same_factors

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
