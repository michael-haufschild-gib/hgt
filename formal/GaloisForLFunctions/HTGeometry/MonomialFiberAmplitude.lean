import GaloisForLFunctions.HTGeometry.PermutationSumIndependence
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise

/-!
# The amplitude a monomial carries at a frequency

The expansion of a monomial in the jets of an exponential carrier is indexed by tuples of indices.
Over the frequency of an injective tuple the fibre is exactly the permutation orbit of that tuple, so
the amplitude carried there is the product of the chosen amplitudes times the symmetrisation of the
monomial, evaluated at the chosen frequencies.

This is the bridge between the analytic conclusion -- every fibre amplitude of a vanishing series is
zero -- and the algebraic one, that symmetrisations of distinct multisets are independent.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The frequency of a tuple. -/
def tupleFrequency (omega : ι → ℝ) {M : ℕ} (n : Fin M → ι) : ℝ := ∑ j, omega (n j)

omit [DecidableEq ι] in
theorem tupleFrequency_comp_perm (omega : ι → ℝ) {M : ℕ} (i : Fin M → ι)
    (sigma : Equiv.Perm (Fin M)) :
    tupleFrequency omega (fun j => i (sigma j)) = tupleFrequency omega i :=
  Fintype.sum_equiv sigma _ _ fun _ => rfl

/-- **The fibre over the frequency of an injective tuple is its permutation orbit.** -/
def fiberPermEquiv {omega : ι → ℝ} (h : RationallyIndependentSequence omega) {M : ℕ}
    {i : Fin M → ι} (hi : Function.Injective i) :
    Equiv.Perm (Fin M) ≃ {n : Fin M → ι // tupleFrequency omega n = tupleFrequency omega i} := by
  refine Equiv.ofBijective
    (fun sigma => ⟨fun j => i (sigma j), tupleFrequency_comp_perm omega i sigma⟩) ⟨?_, ?_⟩
  · intro sigma tau hst
    have hval : ∀ j, i (sigma j) = i (tau j) := fun j => congrFun (congrArg Subtype.val hst) j
    exact Equiv.ext fun j => hi (hval j)
  · rintro ⟨n, hn⟩
    obtain ⟨sigma, hsigma⟩ :=
      exists_perm_of_tupleCount_eq hi (tupleCount_eq_of_frequency_eq h hn)
    exact ⟨sigma, Subtype.ext hsigma.symm⟩

/-- **The amplitude a monomial carries at the frequency of an injective tuple.** -/
theorem fiberAmplitude_monomial {omega : ι → ℝ} (h : RationallyIndependentSequence omega)
    (a : ι → ℂ) {M : ℕ} (s : Fin M → ℕ) {i : Fin M → ι} (hi : Function.Injective i) :
    fiberAmplitude (fun n : Fin M → ι => ∏ j, a (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j)
        (tupleFrequency omega) (tupleFrequency omega i)
      = (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (permSum s) := by
  classical
  set x : Fin M → ℂ := fun l => Complex.I * (omega (i l) : ℂ) with hx
  set B : (Fin M → ι) → ℂ :=
    fun n => ∏ j, a (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j with hB
  have hstep : fiberAmplitude B (tupleFrequency omega) (tupleFrequency omega i)
      = ∑' sigma : Equiv.Perm (Fin M), B (fun j => i (sigma j)) := by
    rw [fiberAmplitude, ← (fiberPermEquiv h hi).tsum_eq (fun n => B (n : Fin M → ι))]
    exact tsum_congr fun sigma => rfl
  rw [hstep, tsum_fintype]
  have hterm : ∀ sigma : Equiv.Perm (Fin M),
      B (fun j => i (sigma j)) = (∏ l, a (i l)) * ∏ j, x (sigma j) ^ s j := by
    intro sigma
    show (∏ j, a (i (sigma j)) * (Complex.I * (omega (i (sigma j)) : ℂ)) ^ s j)
      = (∏ l, a (i l)) * ∏ j, x (sigma j) ^ s j
    rw [Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv sigma (fun j => a (i (sigma j))) (fun l => a (i l)) fun _ => rfl
  rw [Finset.sum_congr rfl fun sigma _ => hterm sigma, ← Finset.mul_sum]
  congr 1
  rw [permSum, map_sum]
  have hperm : ∀ sigma : Equiv.Perm (Fin M),
      MvPolynomial.eval x
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j => s (sigma j)) (1 : ℂ))
        = ∏ j, x j ^ s (sigma j) := by
    intro sigma
    rw [MvPolynomial.eval_monomial]
    simp [Finsupp.prod_fintype]
  rw [Finset.sum_congr rfl fun sigma _ => hperm sigma]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin M)))
    (fun sigma => ∏ j, x (sigma j) ^ s j) (fun sigma => ∏ j, x j ^ s (sigma j)) fun sigma => ?_
  exact Fintype.prod_equiv sigma (fun j => x (sigma j) ^ s j)
    (fun j => x j ^ s (sigma⁻¹ j)) fun j => by simp

end

end GaloisForLFunctions.HTGeometry
