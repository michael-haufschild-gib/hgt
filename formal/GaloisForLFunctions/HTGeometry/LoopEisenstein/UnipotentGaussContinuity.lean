import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentGaussCoefficients
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientContinuity

/-!
# Continuous strict-prefix Gauss corrections

Gauss division by a principal unit uses finite convolution and the inverse
recursion. Its coefficients, and the strict-prefix defects of products,
are continuous functions of the original free coefficients.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R X : Type*} [CommRing R]

section
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace X]

private theorem continuous_coeff_mul (f g : X → PowerSeries R)
    (hf : ∀ n, Continuous fun x => PowerSeries.coeff n (f x))
    (hg : ∀ n, Continuous fun x => PowerSeries.coeff n (g x)) (N : ℕ) :
    Continuous fun x => PowerSeries.coeff N (f x * g x) := by
  have he : (fun x => PowerSeries.coeff N (f x * g x)) =
      (fun x => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeries.coeff p.1 (f x) * PowerSeries.coeff p.2 (g x)) := by
    funext x
    rw [PowerSeries.coeff_mul]
  rw [he]
  exact continuous_finsetSum _ fun p _ => (hf p.1).mul (hg p.2)

/-- Every upper Gauss coefficient is continuous in the free coefficient stream. -/
theorem continuous_unipotentUpperGaussDecoded_coeff (N : ℕ) :
    Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (unipotentUpperGauss ((unipotentCoefficientStreamEquiv R).symm x)) :=
  continuous_coeff_mul _ _ (continuous_unipotentDecoded_coeff 0 1)
    (continuous_coeff_invOfUnit_one _ (continuous_unipotentDecoded_coeff 1 1)) N

/-- Every lower Gauss coefficient is continuous in the free coefficient stream. -/
theorem continuous_unipotentLowerGaussDecoded_coeff (N : ℕ) :
    Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (unipotentLowerGauss ((unipotentCoefficientStreamEquiv R).symm x)) :=
  continuous_coeff_mul _ _ (continuous_unipotentDecoded_coeff 1 0)
    (continuous_coeff_invOfUnit_one _ (continuous_unipotentDecoded_coeff 0 0)) N

end

/-- The upper Gauss defect of a product, evaluated on strict input prefixes. -/
def unipotentUpperGaussCorrection (n : ℕ) (x y : Fin (3*n) → R) : R :=
  PowerSeries.coeff n (unipotentUpperGauss (unipotentPrefixCompletion x * unipotentPrefixCompletion y)) -
    unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion x) (3*n) -
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion y) (3*n)

/-- The lower Gauss defect of a product, evaluated on strict input prefixes. -/
def unipotentLowerGaussCorrection (n : ℕ) (x y : Fin (3*n+1) → R) : R :=
  PowerSeries.coeff (n+1) (unipotentLowerGauss (unipotentPrefixCompletion x * unipotentPrefixCompletion y)) -
    unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion x) (3*n+1) -
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion y) (3*n+1)

private theorem prefixCompletion_agrees (g : unipotentCoefficientGroup R) (N : ℕ) :
    ∀ k < N, unipotentCoefficientStreamEquiv R g k =
      unipotentCoefficientStreamEquiv R
        (unipotentPrefixCompletion (fun i : Fin N => unipotentCoefficientStreamEquiv R g i)) k := by
  intro k hk
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply, dif_pos hk]

/-- The upper correction reads exactly the two strict prefixes. -/
theorem unipotentUpperGauss_product_eq_correction (g h : unipotentCoefficientGroup R) (n : ℕ) :
    PowerSeries.coeff n (unipotentUpperGauss (g*h)) =
      PowerSeries.coeff n (g.1 0 1) + PowerSeries.coeff n (h.1 0 1) +
        unipotentUpperGaussCorrection n
          (fun i => unipotentCoefficientStreamEquiv R g i)
          (fun i => unipotentCoefficientStreamEquiv R h i) := by
  have he := unipotentUpperGauss_product_defect_prefix g h _ _ n
    (prefixCompletion_agrees g (3*n)) (prefixCompletion_agrees h (3*n))
  simp only [unipotentUpperGaussCorrection, unipotentStream_upperRight] at *
  linear_combination he

/-- The lower correction reads exactly the two strict prefixes. -/
theorem unipotentLowerGauss_product_eq_correction (g h : unipotentCoefficientGroup R) (n : ℕ) :
    PowerSeries.coeff (n+1) (unipotentLowerGauss (g*h)) =
      PowerSeries.coeff (n+1) (g.1 1 0) + PowerSeries.coeff (n+1) (h.1 1 0) +
        unipotentLowerGaussCorrection n
          (fun i => unipotentCoefficientStreamEquiv R g i)
          (fun i => unipotentCoefficientStreamEquiv R h i) := by
  have he := unipotentLowerGauss_product_defect_prefix g h _ _ n
    (prefixCompletion_agrees g (3*n+1)) (prefixCompletion_agrees h (3*n+1))
  simp only [unipotentLowerGaussCorrection, unipotentStream_lowerLeft] at *
  linear_combination he

section
variable [TopologicalSpace R]

private theorem continuous_prefixCompletion_stream (N : ℕ) :
    Continuous fun x : Fin N → R => unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion x) := by
  apply continuous_pi
  intro k
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply]
  by_cases hk : k < N
  · simp only [dif_pos hk]
    exact continuous_apply (⟨k,hk⟩ : Fin N)
  · simp only [dif_neg hk]
    exact continuous_const

variable [IsTopologicalRing R]

private theorem continuous_prefixProduct_stream (N : ℕ) :
    Continuous fun p : (Fin N → R) × (Fin N → R) =>
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1 * unipotentPrefixCompletion p.2) := by
  have hf := (continuous_prefixCompletion_stream (R := R) N).comp
    (continuous_fst : Continuous (Prod.fst : (Fin N → R) × (Fin N → R) → Fin N → R))
  have hg := (continuous_prefixCompletion_stream (R := R) N).comp
    (continuous_snd : Continuous (Prod.snd : (Fin N → R) × (Fin N → R) → Fin N → R))
  have hc : Continuous fun p : (Fin N → R) × (Fin N → R) =>
      unipotentStreamProduct
        (unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1),
          unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.2)) :=
    continuous_unipotentStreamProduct.comp (hf.prodMk hg)
  simpa only [unipotentStreamProduct, Equiv.symm_apply_apply] using
    hc

/-- The finite upper correction is continuous in the two strict input prefixes. -/
theorem continuous_unipotentUpperGaussCorrection (n : ℕ) :
    Continuous fun p : (Fin (3*n) → R) × (Fin (3*n) → R) =>
      unipotentUpperGaussCorrection n p.1 p.2 := by
  have hp : Continuous fun p : (Fin (3*n) → R) × (Fin (3*n) → R) =>
      PowerSeries.coeff n (unipotentUpperGauss
        ((unipotentCoefficientStreamEquiv R).symm
          (unipotentCoefficientStreamEquiv R
            (unipotentPrefixCompletion p.1 * unipotentPrefixCompletion p.2)))) :=
    (continuous_unipotentUpperGaussDecoded_coeff (R := R) n).comp
      (continuous_prefixProduct_stream (R := R) (3*n))
  simp only [Equiv.symm_apply_apply] at hp
  exact (hp.sub ((continuous_apply (3*n)).comp
    ((continuous_prefixCompletion_stream (R := R) (3*n)).comp continuous_fst))).sub
    ((continuous_apply (3*n)).comp
      ((continuous_prefixCompletion_stream (R := R) (3*n)).comp continuous_snd))

/-- The finite lower correction is continuous in the two strict input prefixes. -/
theorem continuous_unipotentLowerGaussCorrection (n : ℕ) :
    Continuous fun p : (Fin (3*n+1) → R) × (Fin (3*n+1) → R) =>
      unipotentLowerGaussCorrection n p.1 p.2 := by
  have hp : Continuous fun p : (Fin (3*n+1) → R) × (Fin (3*n+1) → R) =>
      PowerSeries.coeff (n+1) (unipotentLowerGauss
        ((unipotentCoefficientStreamEquiv R).symm
          (unipotentCoefficientStreamEquiv R
            (unipotentPrefixCompletion p.1 * unipotentPrefixCompletion p.2)))) :=
    (continuous_unipotentLowerGaussDecoded_coeff (R := R) (n+1)).comp
      (continuous_prefixProduct_stream (R := R) (3*n+1))
  simp only [Equiv.symm_apply_apply] at hp
  exact (hp.sub ((continuous_apply (3*n+1)).comp
    ((continuous_prefixCompletion_stream (R := R) (3*n+1)).comp continuous_fst))).sub
    ((continuous_apply (3*n+1)).comp
      ((continuous_prefixCompletion_stream (R := R) (3*n+1)).comp continuous_snd))

end
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentUpperGauss_product_eq_correction

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentLowerGauss_product_eq_correction

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.continuous_unipotentUpperGaussCorrection

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.continuous_unipotentLowerGaussCorrection
