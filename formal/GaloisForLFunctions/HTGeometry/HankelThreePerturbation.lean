import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet

/-! # A uniform perturbation bound for the cubic Hankel determinant -/
namespace HTGeometry
noncomputable section

private theorem triple_product_error {a b c A B C M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hb : |b| ≤ M) (hc : |c| ≤ M) (hA : |A| ≤ M) (hB : |B| ≤ M)
    (haA : |a-A| ≤ δ) (hbB : |b-B| ≤ δ) (hcC : |c-C| ≤ δ) :
    |a*b*c-A*B*C| ≤ 3*M^(2 : ℕ)*δ := by
  have h1 : |(a-A)*b*c| ≤ δ*M*M := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul haA hb (abs_nonneg _) hδ) hc (abs_nonneg _) (by positivity)
  have h2 : |A*(b-B)*c| ≤ M*δ*M := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hA hbB (abs_nonneg _) hM) hc (abs_nonneg _) (by positivity)
  have h3 : |A*B*(c-C)| ≤ M*M*δ := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hA hB (abs_nonneg _) hM) hcC (abs_nonneg _) (by positivity)
  rw [show a*b*c-A*B*C = (a-A)*b*c+A*(b-B)*c+A*B*(c-C) by ring]
  have ht := abs_add_le ((a-A)*b*c+A*(b-B)*c) (A*B*(c-C))
  have ht' := abs_add_le ((a-A)*b*c) (A*(b-B)*c)
  nlinarith only [h1, h2, h3, ht, ht']

/-- Entrywise errors at most delta on two bounded tuples change the determinant by at most
`18 M² delta`; the bound accounts for all six signed cubic monomials. -/
theorem signedEvenHankelThreeDet_error_le
    {a b c d e A B C D E M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hp : |a| ≤ M ∧ |b| ≤ M ∧ |c| ≤ M ∧ |d| ≤ M ∧ |e| ≤ M)
    (hq : |A| ≤ M ∧ |B| ≤ M ∧ |C| ≤ M ∧ |D| ≤ M ∧ |E| ≤ M)
    (he : |a-A| ≤ δ ∧ |b-B| ≤ δ ∧ |c-C| ≤ δ ∧ |d-D| ≤ δ ∧ |e-E| ≤ δ) :
    |HilbertMetric.signedEvenHankelThreeDet a b c d e -
      HilbertMetric.signedEvenHankelThreeDet A B C D E| ≤ 18*M^(2 : ℕ)*δ := by
  rcases hp with ⟨ha, hb, hc, hd, he'⟩
  rcases hq with ⟨hA, hB, hC, hD, hE⟩
  rcases he with ⟨haA, hbB, hcC, hdD, heE⟩
  have h1 := triple_product_error hM hδ hc he' hA hC haA hcC heE
  have h2 := triple_product_error hM hδ hd hd hA hD haA hdD hdD
  have h3 := triple_product_error hM hδ hb he' hB hB hbB hbB heE
  have h4 := triple_product_error hM hδ hc hd hB hC hbB hcC hdD
  have h5 := triple_product_error hM hδ hc hc hC hC hcC hcC hcC
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have hb3 := abs_le.mp h3
  have hb4 := abs_le.mp h4
  have hb5 := abs_le.mp h5
  apply abs_le.mpr
  unfold HilbertMetric.signedEvenHankelThreeDet
  constructor <;> nlinarith only [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2,
    hb4.1, hb4.2, hb5.1, hb5.2]

end
end HTGeometry
