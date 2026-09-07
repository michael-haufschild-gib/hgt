import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-! # Quantitative perturbation of the four-dimensional Hankel determinant -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem four_product_error {a b c d A B C D M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hb : |b| ≤ M) (hc : |c| ≤ M) (hd : |d| ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M)
    (hea : |a-A| ≤ δ) (heb : |b-B| ≤ δ) (hec : |c-C| ≤ δ) (hed : |d-D| ≤ δ) :
    |a*b*c*d-A*B*C*D| ≤ 4*M^3*δ := by
  have h1 : |(a-A)*b*c*d| ≤ δ*M*M*M := by
    simp only [abs_mul]
    gcongr
  have h2 : |A*(b-B)*c*d| ≤ M*δ*M*M := by
    simp only [abs_mul]
    gcongr
  have h3 : |A*B*(c-C)*d| ≤ M*M*δ*M := by
    simp only [abs_mul]
    gcongr
  have h4 : |A*B*C*(d-D)| ≤ M*M*M*δ := by
    simp only [abs_mul]
    gcongr
  rw [show a*b*c*d-A*B*C*D = (a-A)*b*c*d+A*(b-B)*c*d+A*B*(c-C)*d+A*B*C*(d-D) by ring]
  have ht1 := abs_add_le ((a-A)*b*c*d) (A*(b-B)*c*d)
  have ht2 := abs_add_le ((a-A)*b*c*d+A*(b-B)*c*d) (A*B*(c-C)*d)
  have ht3 := abs_add_le ((a-A)*b*c*d+A*(b-B)*c*d+A*B*(c-C)*d) (A*B*C*(d-D))
  nlinarith only [h1, h2, h3, h4, ht1, ht2, ht3]

/-- Every determinant monomial retains the entire four-factor error. -/
theorem hankelFourDet_error_le {a b : Fin 7 → ℝ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (ha : ∀ i, |a i| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (he : ∀ i, |a i-b i| ≤ δ) :
    |hankelFourDet (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)-
      hankelFourDet (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6)| ≤ 96*M^3*δ := by
  have h0 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 4) (ha 6)
    (hb 0) (hb 2) (hb 4) (he 0) (he 2) (he 4) (he 6))
  have h1 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 5) (ha 5)
    (hb 0) (hb 2) (hb 5) (he 0) (he 2) (he 5) (he 5))
  have h2 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 3) (ha 6)
    (hb 0) (hb 3) (hb 3) (he 0) (he 3) (he 3) (he 6))
  have h3 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 4) (ha 5)
    (hb 0) (hb 3) (hb 4) (he 0) (he 3) (he 4) (he 5))
  have h4 := abs_le.mp (four_product_error hM hδ (ha 4) (ha 4) (ha 4)
    (hb 0) (hb 4) (hb 4) (he 0) (he 4) (he 4) (he 4))
  have h5 := abs_le.mp (four_product_error hM hδ (ha 1) (ha 4) (ha 6)
    (hb 1) (hb 1) (hb 4) (he 1) (he 1) (he 4) (he 6))
  have h6 := abs_le.mp (four_product_error hM hδ (ha 1) (ha 5) (ha 5)
    (hb 1) (hb 1) (hb 5) (he 1) (he 1) (he 5) (he 5))
  have h7 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 3) (ha 6)
    (hb 1) (hb 2) (hb 3) (he 1) (he 2) (he 3) (he 6))
  have h8 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 4) (ha 5)
    (hb 1) (hb 2) (hb 4) (he 1) (he 2) (he 4) (he 5))
  have h9 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 3) (ha 5)
    (hb 1) (hb 3) (hb 3) (he 1) (he 3) (he 3) (he 5))
  have h10 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 4) (ha 4)
    (hb 1) (hb 3) (hb 4) (he 1) (he 3) (he 4) (he 4))
  have h11 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 2) (ha 6)
    (hb 2) (hb 2) (hb 2) (he 2) (he 2) (he 2) (he 6))
  have h12 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 3) (ha 5)
    (hb 2) (hb 2) (hb 3) (he 2) (he 2) (he 3) (he 5))
  have h13 := abs_le.mp (four_product_error hM hδ (ha 2) (ha 4) (ha 4)
    (hb 2) (hb 2) (hb 4) (he 2) (he 2) (he 4) (he 4))
  have h14 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 3) (ha 4)
    (hb 2) (hb 3) (hb 3) (he 2) (he 3) (he 3) (he 4))
  have h15 := abs_le.mp (four_product_error hM hδ (ha 3) (ha 3) (ha 3)
    (hb 3) (hb 3) (hb 3) (he 3) (he 3) (he 3) (he 3))
  apply abs_le.mpr
  unfold hankelFourDet
  constructor
  · linear_combination 1*h0.1 + 1*h1.2 + 1*h2.2 + 2*h3.1 + 1*h4.2 + 1*h5.2 + 1*h6.1 + 2*h7.1 + 2*h8.2 + 2*h9.2 + 2*h10.1 + 1*h11.2 + 2*h12.1 + 1*h13.1 + 3*h14.2 + 1*h15.1
  · linear_combination 1*h0.2 + 1*h1.1 + 1*h2.1 + 2*h3.2 + 1*h4.1 + 1*h5.1 + 1*h6.2 + 2*h7.2 + 2*h8.1 + 2*h9.1 + 2*h10.2 + 1*h11.1 + 2*h12.2 + 1*h13.2 + 3*h14.1 + 1*h15.2

end
end GaloisForLFunctions.HTGeometry
