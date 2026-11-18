import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnReciprocalProductRectangles

/-!
# Centered reciprocal fractional parts across a product window

A product in a dyadic cell determines its corner up to a factor four.
This permits summation over both full factor intervals while retaining
the sharp product restriction and arbitrary separated weights.
-/

noncomputable section
open Finset RHTower GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.PrimeExponentialSums

/-- Bilinear centered fractional parts in the sharp window `L < p*m ≤ U`. -/
def fractionalProductTerm (Z : ℝ) (L U : ℕ) (α β : ℕ → ℂ) (p m : ℕ) : ℂ :=
  if L < p*m ∧ p*m ≤ U then (α p*β m)*(saw (Z/m/p) : ℂ) else 0

/-- Arbitrary truncated factor intervals in a near-square product window.
Each factor subdivision costs only a logarithm. -/
theorem centered_fractional_reciprocal_product_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b c d H L U : ℕ}, 1 ≤ H → H^4 ≤ a → H ≤ c →
      a ≤ b → c ≤ d → ∀ {Z : ℝ}, 0 < Z → (U : ℝ)^2 ≤ H*Z → 16*Z ≤ H*(L : ℝ)^2 →
      ∀ (α β : ℕ → ℂ) {A B : ℝ}, 0 ≤ A → 0 ≤ B →
        (∀ p ∈ Ico a b, ‖α p‖ ≤ A) → (∀ m ∈ Ico c d, ‖β m‖ ≤ B) →
      ‖∑ p ∈ Ico a b, ∑ m ∈ Ico c d, fractionalProductTerm Z L U α β p m‖ ≤
        K*(1+Real.log b)*(1+Real.log d)*(A*B*U)/Real.sqrt (Real.sqrt H) := by
  obtain ⟨K,hK,hrect⟩ := centered_fractional_reciprocal_product_rectangle
  refine ⟨4*K,by positivity,?_⟩
  intro a b c d H L U hH ha hc hab hcd Z hZ hLo hHi α β A B hA hB hα hβ
  let F := fractionalProductTerm Z L U α β
  let G := K*(A*B*U)/Real.sqrt (Real.sqrt H)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have ha₁ := (Nat.one_le_pow 4 H hH).trans ha
  have hc₁ := hH.trans hc
  have block {P P' V V' : ℕ} (hp : a ≤ P) (hp' : P' ≤ b) (ht : P' ≤ 2*P)
      (hv : c ≤ V) (hv' : V' ≤ d) (hs : V' ≤ 2*V) :
      ‖∑ p ∈ Ico P P', ∑ m ∈ Ico V V', F p m‖ ≤ G := by
    by_cases hhit : ∃ p ∈ Ico P P', ∃ m ∈ Ico V V', L < p*m ∧ p*m ≤ U
    swap
    · have zero (p : ℕ) (hpp : p ∈ Ico P P') (m : ℕ) (hmm : m ∈ Ico V V') : F p m=0 :=
        if_neg (fun hcut => hhit ⟨p,hpp,m,hmm,hcut⟩)
      simpa only [sum_eq_zero (fun p hpp => sum_eq_zero (fun m hmm => zero p hpp m hmm)),
        norm_zero] using hG
    obtain ⟨p,hp₀,m,hm₀,hprod⟩ := hhit
    obtain ⟨hPp,hpP⟩ := mem_Ico.mp hp₀
    obtain ⟨hVm,hmV⟩ := mem_Ico.mp hm₀
    have corner : P*V ≤ U := (Nat.mul_le_mul hPp hVm).trans hprod.2
    have top : L ≤ 4*(P*V) := by
      have hh := Nat.mul_le_mul (hpP.le.trans ht) (hmV.le.trans hs)
      exact hprod.1.le.trans (hh.trans_eq (by ring))
    have corner' : (P : ℝ)*V ≤ U := by exact_mod_cast corner
    have top' : (L : ℝ) ≤ 4*((P : ℝ)*V) := by exact_mod_cast top
    have hlo := (pow_le_pow_left₀ (by positivity) corner' 2).trans hLo
    have hhi : Z ≤ H*((P : ℝ)*V)^2 := by
      have hh := hHi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg L) top' 2)
        (Nat.cast_nonneg H))
      linarith only [hh]
    let s := Ico P P'
    let t := Ico V V'
    let extend (s : Finset ℕ) (w : ℕ → ℂ) (i : ℕ) := if i ∈ s then w i else 0
    let D := Ico P (2*P)
    let J := Ico V (2*V)
    have hα' (i : ℕ) (_hi : i ∈ D) : ‖extend s α i‖ ≤ A := by
      by_cases hi : i ∈ s
      · obtain ⟨hl,hu⟩ := mem_Ico.mp hi
        simpa [extend,hi] using hα i (mem_Ico.mpr ⟨hp.trans hl,hu.trans_le hp'⟩)
      · simpa [extend,hi] using hA
    have hβ' (i : ℕ) (_hi : i ∈ J) : ‖extend t β i‖ ≤ B := by
      by_cases hi : i ∈ t
      · obtain ⟨hl,hu⟩ := mem_Ico.mp hi
        simpa [extend,hi] using hβ i (mem_Ico.mpr ⟨hv.trans hl,hu.trans_le hv'⟩)
      · simpa [extend,hi] using hB
    have hz := hrect hH (hc.trans hv) (ha.trans hp) hZ hlo hhi L U _ _ hA hB hα' hβ'
    let cut (q : ℕ×ℕ) := L<q.1*q.2 ∧ q.1*q.2≤U
    let weight (q : ℕ×ℕ) := (extend s α q.1*extend t β q.2)*(saw (Z/q.2/q.1) : ℂ)
    have eq : (∑ i ∈ s, ∑ j ∈ t, F i j) = ∑ q ∈ (D ×ˢ J).filter cut, weight q := by
      calc _ = ∑ q ∈ (s ×ˢ t).filter cut, weight q := by
                  rw [sum_filter,sum_product]
                  apply sum_congr rfl
                  intro i hi
                  apply sum_congr rfl
                  intro j hj
                  simp only [F,fractionalProductTerm,weight,extend,hi,hj,if_true]
           _ = _ := by
                  apply sum_subset
                  · intro q hq
                    obtain ⟨hm,hcut⟩ := mem_filter.mp hq
                    obtain ⟨hi,hj⟩ := mem_product.mp hm
                    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨(mem_Ico.mp hi).1,
                      (mem_Ico.mp hi).2.trans_le ht⟩,mem_Ico.mpr ⟨(mem_Ico.mp hj).1,
                      (mem_Ico.mp hj).2.trans_le hs⟩⟩,hcut⟩
                  · intro q hq hmiss
                    have hcut := (mem_filter.mp hq).2
                    by_cases hi : q.1 ∈ s
                    · have hj : q.2 ∉ t := fun hj => hmiss (mem_filter.mpr ⟨mem_product.mpr ⟨hi,hj⟩,hcut⟩)
                      simp [weight,extend,hj]
                    · simp [weight,extend,hi]
    rw [eq]
    apply hz.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hK
    rw [mul_assoc (A*B)]
    exact mul_le_mul_of_nonneg_left corner' (mul_nonneg hA hB)
  let E := 2*(1+Real.log d)*G
  have hE : 0 ≤ E := by dsimp [E]; have := Real.log_natCast_nonneg d; positivity
  have total := Sieve.norm_sum_Ico_le_of_blocks (fun p => ∑ m ∈ Ico c d, F p m) E hab ha₁ hE
    (fun P P' _ _ ht hp hp' => by
      rw [sum_comm]
      exact Sieve.norm_sum_Ico_le_of_blocks (fun m => ∑ p ∈ Ico P P', F p m) G hcd hc₁ hG
        (fun V V' _ _ hs hv hv' => by rw [sum_comm]; exact block hp hp' ht hv hv' hs))
  exact total.trans_eq (by dsimp [E,G]; ring)

end GaloisForLFunctions.PrimeExponentialSums
