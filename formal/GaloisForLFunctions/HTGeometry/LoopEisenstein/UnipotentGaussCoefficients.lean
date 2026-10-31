import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientPrefixes
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentTriangularMultiplication

/-!
# Strict coefficient dependence of unipotent Gauss coordinates

Subtracting the free upper or lower entry from its Gauss coordinate leaves
a product with a zero constant coefficient. The missing convolution boundary
terms make these changes triangular in the free coefficient order.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R : Type*} [CommRing R]

private theorem principalInverse_constant {p : PowerSeries R}
    (hp : PowerSeries.constantCoeff p = 1) :
    PowerSeries.constantCoeff (PowerSeries.invOfUnit p 1) = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := R)) (PowerSeries.mul_invOfUnit p 1 hp)
  simpa only [map_mul, hp, one_mul, map_one] using h

/-- The upper root in upper–diagonal–lower Gauss order. -/
def unipotentUpperGauss (g : unipotentCoefficientGroup R) : PowerSeries R :=
  g.1 0 1 * PowerSeries.invOfUnit (g.1 1 1) 1

/-- The lower root in lower–diagonal–upper Gauss order. -/
def unipotentLowerGauss (g : unipotentCoefficientGroup R) : PowerSeries R :=
  g.1 1 0 * PowerSeries.invOfUnit (g.1 0 0) 1

private theorem inverse_lowerRight_sub_one_constant (g : unipotentCoefficientGroup R) :
    PowerSeries.constantCoeff (PowerSeries.invOfUnit (g.1 1 1) 1 - 1) = 0 := by
  rw [map_sub, principalInverse_constant
    ((mem_unipotentCoefficientGroup R g).mp g.property).2.2, map_one, sub_self]

private theorem inverse_upperLeft_sub_one_constant (g : unipotentCoefficientGroup R) :
    PowerSeries.constantCoeff (PowerSeries.invOfUnit (g.1 0 0) 1 - 1) = 0 := by
  rw [map_sub, principalInverse_constant
    ((mem_unipotentCoefficientGroup R g).mp g.property).1, map_one, sub_self]

/-- The upper Gauss defect needs no current upper-right coefficient. -/
theorem unipotentUpperGauss_defect_congr (g h : unipotentCoefficientGroup R) (N : ℕ)
    (ha : ∀ n ≤ N, PowerSeries.coeff n (g.1 0 0) = PowerSeries.coeff n (h.1 0 0))
    (hb : ∀ n < N, PowerSeries.coeff n (g.1 0 1) = PowerSeries.coeff n (h.1 0 1))
    (hc : ∀ n ≤ N, PowerSeries.coeff n (g.1 1 0) = PowerSeries.coeff n (h.1 1 0)) :
    PowerSeries.coeff N (unipotentUpperGauss g) - PowerSeries.coeff N (g.1 0 1) =
      PowerSeries.coeff N (unipotentUpperGauss h) - PowerSeries.coeff N (h.1 0 1) := by
  have hd (n : ℕ) (hn : n ≤ N) :
      PowerSeries.coeff n (g.1 1 1) = PowerSeries.coeff n (h.1 1 1) :=
    unipotentCoefficient_lowerRight_congr g h n
      (fun m hm => ha m (hm.trans hn))
      (fun m hm => hb m (lt_of_lt_of_le hm hn))
      (fun m hm => hc m (hm.trans hn))
  have he (k : unipotentCoefficientGroup R) :
      unipotentUpperGauss k - k.1 0 1 =
        k.1 0 1 * (PowerSeries.invOfUnit (k.1 1 1) 1 - 1) := by
    unfold unipotentUpperGauss
    ring
  rw [← map_sub, ← map_sub, he, he]
  apply coeff_mul_congr_zero_right N (inverse_lowerRight_sub_one_constant g)
    (inverse_lowerRight_sub_one_constant h) hb
  intro n hn
  rw [map_sub, map_sub]
  congr 1
  exact RHTower.deningerBigWittInvOfUnit_coeff_congr (fun m hm => hd m (hm.trans hn))

/-- The lower Gauss defect uses only strictly earlier upper-left and lower-left coefficients. -/
theorem unipotentLowerGauss_defect_congr (g h : unipotentCoefficientGroup R) (N : ℕ)
    (ha : ∀ n < N, PowerSeries.coeff n (g.1 0 0) = PowerSeries.coeff n (h.1 0 0))
    (hc : ∀ n < N, PowerSeries.coeff n (g.1 1 0) = PowerSeries.coeff n (h.1 1 0)) :
    PowerSeries.coeff N (unipotentLowerGauss g) - PowerSeries.coeff N (g.1 1 0) =
      PowerSeries.coeff N (unipotentLowerGauss h) - PowerSeries.coeff N (h.1 1 0) := by
  have he (k : unipotentCoefficientGroup R) :
      unipotentLowerGauss k - k.1 1 0 =
        k.1 1 0 * (PowerSeries.invOfUnit (k.1 0 0) 1 - 1) := by
    unfold unipotentLowerGauss
    ring
  rw [← map_sub, ← map_sub, he, he]
  apply coeff_mul_congr_zero_constants N
    ((mem_unipotentCoefficientGroup R g).mp g.property).2.1
    (inverse_upperLeft_sub_one_constant g)
    ((mem_unipotentCoefficientGroup R h).mp h.property).2.1
    (inverse_upperLeft_sub_one_constant h) hc
  intro n hn
  rw [map_sub, map_sub]
  congr 1
  exact RHTower.deningerBigWittInvOfUnit_coeff_congr (fun m hm => ha m (lt_of_le_of_lt hm hn))

private theorem prefix_upperLeft {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m ≤ N) : PowerSeries.coeff m (g.1 0 0) = PowerSeries.coeff m (h.1 0 0) := by
  cases m with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff,
      ((mem_unipotentCoefficientGroup R g).mp g.property).1,
      ((mem_unipotentCoefficientGroup R h).mp h.property).1]
  | succ m => simpa only [unipotentStream_upperLeft] using hp (3 * m + 2) (by omega)

private theorem prefix_lowerLeft {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m ≤ N + 1) : PowerSeries.coeff m (g.1 1 0) = PowerSeries.coeff m (h.1 1 0) := by
  cases m with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff,
      ((mem_unipotentCoefficientGroup R g).mp g.property).2.1,
      ((mem_unipotentCoefficientGroup R h).mp h.property).2.1]
  | succ m => simpa only [unipotentStream_lowerLeft] using hp (3 * m + 1) (by omega)

/-- The upper Gauss change is triangular in the full free-coefficient stream. -/
theorem unipotentUpperGauss_defect_prefix (g h : unipotentCoefficientGroup R) (n : ℕ)
    (hp : ∀ k < 3 * n,
      unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k) :
    PowerSeries.coeff n (unipotentUpperGauss g) - unipotentCoefficientStreamEquiv R g (3 * n) =
      PowerSeries.coeff n (unipotentUpperGauss h) - unipotentCoefficientStreamEquiv R h (3 * n) := by
  simp only [unipotentStream_upperRight]
  apply unipotentUpperGauss_defect_congr
  · exact fun m hm => prefix_upperLeft hp m (by omega)
  · intro m hm
    simpa only [unipotentStream_upperRight] using hp (3 * m) (by omega)
  · exact fun m hm => prefix_lowerLeft hp m (by omega)

/-- The lower Gauss change is triangular in the full free-coefficient stream. -/
theorem unipotentLowerGauss_defect_prefix (g h : unipotentCoefficientGroup R) (n : ℕ)
    (hp : ∀ k < 3 * n + 1,
      unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k) :
    PowerSeries.coeff (n + 1) (unipotentLowerGauss g) -
        unipotentCoefficientStreamEquiv R g (3 * n + 1) =
      PowerSeries.coeff (n + 1) (unipotentLowerGauss h) -
        unipotentCoefficientStreamEquiv R h (3 * n + 1) := by
  simp only [unipotentStream_lowerLeft]
  apply unipotentLowerGauss_defect_congr
  · exact fun m hm => prefix_upperLeft hp m (by omega)
  · exact fun m hm => prefix_lowerLeft hp m (by omega)

private theorem product_prefix_congr (g h g' h' : unipotentCoefficientGroup R) (N : ℕ)
    (hg : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < N, unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    ∀ k < N, unipotentCoefficientStreamEquiv R (g * h) k =
      unipotentCoefficientStreamEquiv R (g' * h') k := by
  intro k hk
  have he := unipotentStreamDefect_prefix_congr g h g' h' k
    (fun j hj => hg j (hj.trans hk)) (fun j hj => hh j (hj.trans hk))
  unfold unipotentStreamDefect at he
  rw [hg k hk, hh k hk] at he
  linear_combination he

/-- The upper Gauss coefficient of a product is the sum of the current upper
coefficients, with a correction determined by the two strict input prefixes. -/
theorem unipotentUpperGauss_product_defect_prefix (g h g' h' : unipotentCoefficientGroup R) (n : ℕ)
    (hg : ∀ k < 3 * n,
      unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < 3 * n,
      unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    PowerSeries.coeff n (unipotentUpperGauss (g * h)) -
        PowerSeries.coeff n (g.1 0 1) - PowerSeries.coeff n (h.1 0 1) =
      PowerSeries.coeff n (unipotentUpperGauss (g' * h')) -
        PowerSeries.coeff n (g'.1 0 1) - PowerSeries.coeff n (h'.1 0 1) := by
  have he := unipotentUpperGauss_defect_prefix (g * h) (g' * h') n
    (product_prefix_congr g h g' h' (3 * n) hg hh)
  have hm := unipotentStreamDefect_prefix_congr g h g' h' (3 * n) hg hh
  simp only [unipotentStreamDefect, unipotentStream_upperRight] at he hm
  linear_combination he + hm

/-- The lower Gauss coefficient of a product has the corresponding strict-prefix law. -/
theorem unipotentLowerGauss_product_defect_prefix (g h g' h' : unipotentCoefficientGroup R) (n : ℕ)
    (hg : ∀ k < 3 * n + 1,
      unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < 3 * n + 1,
      unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    PowerSeries.coeff (n + 1) (unipotentLowerGauss (g * h)) -
        PowerSeries.coeff (n + 1) (g.1 1 0) - PowerSeries.coeff (n + 1) (h.1 1 0) =
      PowerSeries.coeff (n + 1) (unipotentLowerGauss (g' * h')) -
        PowerSeries.coeff (n + 1) (g'.1 1 0) - PowerSeries.coeff (n + 1) (h'.1 1 0) := by
  have he := unipotentLowerGauss_defect_prefix (g * h) (g' * h') n
    (product_prefix_congr g h g' h' (3 * n + 1) hg hh)
  have hm := unipotentStreamDefect_prefix_congr g h g' h' (3 * n + 1) hg hh
  simp only [unipotentStreamDefect, unipotentStream_lowerLeft] at he hm
  linear_combination he + hm

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentUpperGauss_defect_congr
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentLowerGauss_defect_congr
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentUpperGauss_product_defect_prefix
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentLowerGauss_product_defect_prefix
