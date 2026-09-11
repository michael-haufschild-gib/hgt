import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailSharpReserve
import GaloisForLFunctions.HTGeometry.HankelFourPerturbation
/-!
# Entry-specific perturbation of the reserved even Hankel determinant

The product telescope retains the error at each of the seven entries.
Ceilings `[2, 1/3, 1/4, 1/3, 1, 2, 5]` give determinant error at most
`3*10^12*epsilon` when entry `k` has error at most `120^k*epsilon`.
The exact first-atom profiles leave room for these errors at scale fifteen.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def fourEntryError (M δ : Fin 7 → ℝ) (i j k l : Fin 7) : ℝ :=
  δ i*M j*M k*M l+M i*δ j*M k*M l+M i*M j*δ k*M l+M i*M j*M k*δ l

private theorem four_entry_error {a b M δ : Fin 7 → ℝ}
    (hM : ∀ i, 0 ≤ M i) (hδ : ∀ i, 0 ≤ δ i)
    (ha : ∀ i, |a i| ≤ M i) (hb : ∀ i, |b i| ≤ M i)
    (he : ∀ i, |a i-b i| ≤ δ i) (i j k l : Fin 7) :
    |a i*a j*a k*a l-b i*b j*b k*b l| ≤ fourEntryError M δ i j k l := by
  have hMi := hM i
  have hMj := hM j
  have hMk := hM k
  have hMl := hM l
  have hδi := hδ i
  have hδj := hδ j
  have hδk := hδ k
  have hδl := hδ l
  have h1 : |(a i-b i)*a j*a k*a l| ≤ δ i*M j*M k*M l := by
    simp only [abs_mul]
    gcongr <;> first | positivity | exact he _ | exact ha _
  have h2 : |b i*(a j-b j)*a k*a l| ≤ M i*δ j*M k*M l := by
    simp only [abs_mul]
    gcongr <;> first | positivity | exact he _ | exact ha _ | exact hb _
  have h3 : |b i*b j*(a k-b k)*a l| ≤ M i*M j*δ k*M l := by
    simp only [abs_mul]
    gcongr <;> first | positivity | exact he _ | exact ha _ | exact hb _
  have h4 : |b i*b j*b k*(a l-b l)| ≤ M i*M j*M k*δ l := by
    simp only [abs_mul]
    gcongr <;> first | positivity | exact he _ | exact hb _
  rw [show a i*a j*a k*a l-b i*b j*b k*b l =
      (a i-b i)*a j*a k*a l+b i*(a j-b j)*a k*a l+
        b i*b j*(a k-b k)*a l+b i*b j*b k*(a l-b l) by ring]
  have ht1 := abs_add_le ((a i-b i)*a j*a k*a l) (b i*(a j-b j)*a k*a l)
  have ht2 := abs_add_le ((a i-b i)*a j*a k*a l+b i*(a j-b j)*a k*a l) (b i*b j*(a k-b k)*a l)
  have ht3 := abs_add_le ((a i-b i)*a j*a k*a l+b i*(a j-b j)*a k*a l+
    b i*b j*(a k-b k)*a l) (b i*b j*b k*(a l-b l))
  unfold fourEntryError
  linarith only [h1, h2, h3, h4, ht1, ht2, ht3]

/-- Separate entry ceilings preserve the small errors at lower derivative orders. -/
def hankelFourTailEntryCeiling (i : Fin 7) : ℝ :=
  if i.val = 0 then 2 else if i.val = 1 then 1/3 else if i.val = 2 then 1/4
  else if i.val = 3 then 1/3 else if i.val = 4 then 1 else if i.val = 5 then 2 else 5

private def hankelFourProductTerms (a : Fin 7 → ℝ) : Fin 16 → ℝ :=
  ![a 0*a 2*a 4*a 6,
    a 0*a 2*a 5*a 5,
    a 0*a 3*a 3*a 6,
    a 0*a 3*a 4*a 5,
    a 0*a 4*a 4*a 4,
    a 1*a 1*a 4*a 6,
    a 1*a 1*a 5*a 5,
    a 1*a 2*a 3*a 6,
    a 1*a 2*a 4*a 5,
    a 1*a 3*a 3*a 5,
    a 1*a 3*a 4*a 4,
    a 2*a 2*a 2*a 6,
    a 2*a 2*a 3*a 5,
    a 2*a 2*a 4*a 4,
    a 2*a 3*a 3*a 4,
    a 3*a 3*a 3*a 3]

private def hankelFourTermErrors (M δ : Fin 7 → ℝ) : Fin 16 → ℝ :=
  ![fourEntryError M δ 0 2 4 6,
    fourEntryError M δ 0 2 5 5,
    fourEntryError M δ 0 3 3 6,
    fourEntryError M δ 0 3 4 5,
    fourEntryError M δ 0 4 4 4,
    fourEntryError M δ 1 1 4 6,
    fourEntryError M δ 1 1 5 5,
    fourEntryError M δ 1 2 3 6,
    fourEntryError M δ 1 2 4 5,
    fourEntryError M δ 1 3 3 5,
    fourEntryError M δ 1 3 4 4,
    fourEntryError M δ 2 2 2 6,
    fourEntryError M δ 2 2 3 5,
    fourEntryError M δ 2 2 4 4,
    fourEntryError M δ 2 3 3 4,
    fourEntryError M δ 3 3 3 3]

private def hankelFourTermCoefficients : Fin 16 → ℝ :=
  ![1,-1,-1,2,-1,-1,1,2,-2,-2,2,-1,2,1,-3,1]

/-- An entry-specific perturbation estimate in the reflected Gaussian tail coordinates. -/
theorem hankelFourDet_error_le_scale120 {a b : Fin 7 → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (ha : ∀ i, |a i| ≤ hankelFourTailEntryCeiling i)
    (hb : ∀ i, |b i| ≤ hankelFourTailEntryCeiling i)
    (he : ∀ i, |a i-b i| ≤ (120 : ℝ)^i.val*ε) :
    |hankelFourDet (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)-
      hankelFourDet (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6)| ≤ 3000000000000*ε := by
  have hM (i : Fin 7) : 0 ≤ hankelFourTailEntryCeiling i := by fin_cases i <;> norm_num [hankelFourTailEntryCeiling]
  have hδ (i : Fin 7) : 0 ≤ (120 : ℝ)^i.val*ε := by positivity
  have hdet (v : Fin 7 → ℝ) :
      hankelFourDet (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) =
        ∑ i : Fin 16, hankelFourTermCoefficients i*hankelFourProductTerms v i := by
    norm_num [Fin.sum_univ_succ, hankelFourTermCoefficients, hankelFourProductTerms, hankelFourDet]
    ring
  have hp (i : Fin 16) : |hankelFourProductTerms a i-hankelFourProductTerms b i| ≤
      hankelFourTermErrors hankelFourTailEntryCeiling (fun k => (120 : ℝ)^k.val*ε) i := by
    fin_cases i
    · exact four_entry_error hM hδ ha hb he 0 2 4 6
    · exact four_entry_error hM hδ ha hb he 0 2 5 5
    · exact four_entry_error hM hδ ha hb he 0 3 3 6
    · exact four_entry_error hM hδ ha hb he 0 3 4 5
    · exact four_entry_error hM hδ ha hb he 0 4 4 4
    · exact four_entry_error hM hδ ha hb he 1 1 4 6
    · exact four_entry_error hM hδ ha hb he 1 1 5 5
    · exact four_entry_error hM hδ ha hb he 1 2 3 6
    · exact four_entry_error hM hδ ha hb he 1 2 4 5
    · exact four_entry_error hM hδ ha hb he 1 3 3 5
    · exact four_entry_error hM hδ ha hb he 1 3 4 4
    · exact four_entry_error hM hδ ha hb he 2 2 2 6
    · exact four_entry_error hM hδ ha hb he 2 2 3 5
    · exact four_entry_error hM hδ ha hb he 2 2 4 4
    · exact four_entry_error hM hδ ha hb he 2 3 3 4
    · exact four_entry_error hM hδ ha hb he 3 3 3 3
  rw [hdet a, hdet b, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 16, |hankelFourTermCoefficients i*hankelFourProductTerms a i-
        hankelFourTermCoefficients i*hankelFourProductTerms b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 16, |hankelFourTermCoefficients i| *
        hankelFourTermErrors hankelFourTailEntryCeiling (fun k => (120 : ℝ)^k.val*ε) i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hp i) (abs_nonneg _)
    _ ≤ 3000000000000*ε := by
      norm_num [Fin.sum_univ_succ, hankelFourTermCoefficients, hankelFourTermErrors,
        fourEntryError, hankelFourTailEntryCeiling]
      linarith only [hε]

end
end GaloisForLFunctions.HTGeometry
namespace HTGeometry
noncomputable section
/-- The sixth profile remains bounded on the extended scale-fifteen ray. -/
theorem firstAtomEvenTailProfile_six_abs_le_of_fifteen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/15) :
    |firstAtomEvenTailProfile 6 u| ≤ 4000000000 := by
  have hd : 18/5 ≤ 4-6*u := by linarith
  have hD : 129/10 ≤ firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    nlinarith [sq_nonneg (4-6*u-18/5)]
  have hp (n : ℕ) : 0 ≤ u^n ∧ u^n ≤ (1/15 : ℝ)^n :=
    ⟨pow_nonneg hu0 n, pow_le_pow_left₀ hu0 hu1 n⟩
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  have h7 := hp 7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  have hN : |firstAtomEvenTailNumerator6 u| ≤ 51000000000 := by
    unfold firstAtomEvenTailNumerator6
    apply abs_le.mpr
    constructor <;> nlinarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2]
  norm_num [firstAtomEvenTailProfile]
  rw [abs_div, abs_of_pos (by linarith : 0 < firstAtomOddTailDenominator u)]
  apply (div_le_iff₀ (by linarith : 0 < firstAtomOddTailDenominator u)).mpr
  nlinarith only [hD, hN]

/-- Each balanced first-atom entry leaves room for its order-specific complete-source error. -/
theorem firstAtomEvenTailBalanced_with_error_le_of_fifteen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/15) (k : Fin 7) :
    |firstAtomEvenTailBalanced k u|+(120 : ℝ)^k.val*(2/(10 : ℝ)^17) ≤
      GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling k := by
  have hu7 : u ≤ 1/7 := by linarith
  have h1 := firstAtomOddScaleSeven_profile1_bounds hu0 hu7
  have h2 := firstAtomOddScaleSeven_profile2_bounds hu0 hu7
  have h3 := firstAtomOddScaleSeven_profile3_bounds hu0 hu7
  have h4 := firstAtomOddScaleSeven_profile4_bounds hu0 hu7
  have h5 := firstAtomOddScaleSeven_profile5_bounds hu0 hu7
  have h6 := firstAtomEvenTailProfile_six_abs_le_of_fifteen hu0 hu1
  have h6' : |firstAtomEvenTailProfile 6 u / (32 : ℝ)^6-100000000/(32 : ℝ)^6| ≤ 4 := by
    have ht := abs_sub (firstAtomEvenTailProfile 6 u / (32 : ℝ)^6) (100000000/(32 : ℝ)^6)
    norm_num [abs_div] at ht
    linarith
  fin_cases k
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile]
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h1.1]
    linarith [h1.2]
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h2.1]
    linarith [h2.2]
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h3.1]
    linarith [h3.2]
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h4.1]
    linarith [h4.2]
  · norm_num [GaloisForLFunctions.HTGeometry.hankelFourTailEntryCeiling, firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h5.1]
    linarith [h5.2]
  · change |firstAtomEvenTailProfile 6 u/(32 : ℝ)^6-100000000/(32 : ℝ)^6|+
        (120 : ℝ)^6*(2/(10 : ℝ)^17) ≤ 5
    norm_num at h6' ⊢
    linarith only [h6']

end
end HTGeometry
