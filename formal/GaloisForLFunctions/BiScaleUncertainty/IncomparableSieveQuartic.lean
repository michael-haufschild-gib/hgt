import GaloisForLFunctions.BiScaleUncertainty.SieveMomentFourier
import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery

/-!
# Incomparable orders and complete quartic ambiguity

Fourier inversion turns equality on every zero-sum tuple into equality of full
translated lag arrays. A quartet on two incomparable additive orders has no
singleton order, so its surviving coordinate products depend only on squares.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false
variable {P : ℕ} [NeZero P]

private theorem sum_cons {m : ℕ} (F : (Fin (m+1) → ZMod P) → ℂ) :
    (∑ h, F h) = ∑ t : ZMod P, ∑ h : Fin m → ZMod P, F (Fin.cons t h) := by
  calc
    _ = ∑ x : ZMod P × (Fin m → ZMod P), F (Fin.cons x.1 x.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ZMod P))
        _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

private theorem momentDFT_cons {m : ℕ} (T : (Fin (m+1) → ZMod P) → ℂ)
    (t : ZMod P) (r : Fin m → ZMod P) :
    momentDFT T (Fin.cons t r) =
      ZMod.dft (fun s => momentDFT (fun h => T (Fin.cons s h)) r) t := by
  simp only [momentDFT,ZMod.dft_apply,smul_eq_mul]
  rw [sum_cons]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp_rw [Finset.mul_sum,mul_assoc]

/-- Full lag Fourier data determine the entire translated observation array. -/
theorem momentDFT_injective (m : ℕ) :
    Function.Injective (momentDFT (P := P) (m := m)) := by
  induction m with
  | zero =>
    intro T U h
    funext x
    have hx := congrFun h x
    have sum_at (F : (Fin 0 → ZMod P) → ℂ) : (∑ y, F y) = F x := by
      apply Finset.sum_eq_single x
      · intro y _ hy
        exact (hy (Subsingleton.elim y x)).elim
      · intro hx
        exact (hx (Finset.mem_univ x)).elim
    simpa only [momentDFT,Fin.prod_univ_zero,one_mul,sum_at] using hx
  | succ m ih =>
    intro T U h
    have hs (r : Fin m → ZMod P) :
        (fun s => momentDFT (fun t => T (Fin.cons s t)) r) =
          (fun s => momentDFT (fun t => U (Fin.cons s t)) r) := by
      apply ZMod.dft.injective
      funext s
      rw [← momentDFT_cons,← momentDFT_cons]
      exact congrFun h (Fin.cons s r)
    funext x
    have ht := ih (funext (fun r => congrFun (hs r) (x 0)))
    have hx := congrFun ht (Fin.tail x)
    simpa only [Fin.cons_self_tail] using hx

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments


open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false
variable {P : ℕ}

private theorem singleton_order_dvd {m B : ℕ} (r : Fin m → ZMod P)
    (hz : (∑ i, r i) = 0) (j : Fin m)
    (hj : ∀ i, i ≠ j → addOrderOf (r i) ∣ B) : addOrderOf (r j) ∣ B := by
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
  have ht : (∑ i, B • r i) = B • r j := by
    apply Finset.sum_eq_single j
    · intro i _ hi
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hj i hi)
    · simp
  rw [← Finset.smul_sum,hz,smul_zero] at ht
  exact ht.symm

/-- An incomparable pair cannot occur with odd multiplicities in a resonant quartet. -/
theorem incomparable_quartic_products {A B : ℕ} (hAB : ¬ A ∣ B) (hBA : ¬ B ∣ A)
    (v w : ℕ → ℝ) (hv : ∀ q, q ≠ A → q ≠ B → v q = 0)
    (hw : ∀ q, q ≠ A → q ≠ B → w q = 0)
    (hA : v A ^ 2 = w A ^ 2) (hB : v B ^ 2 = w B ^ 2)
    (r : Fin 4 → ZMod P) (hz : (∑ i, r i) = 0) :
    (∏ i, v (addOrderOf (r i))) = ∏ i, w (addOrderOf (r i)) := by
  classical
  by_cases hs : ∀ i, addOrderOf (r i) = A ∨ addOrderOf (r i) = B
  · have noA (i : Fin 4) (hi : addOrderOf (r i) = A)
        (hj : ∀ j, j ≠ i → addOrderOf (r j) = B) : False := by
      apply hAB
      rw [← hi]
      exact singleton_order_dvd r hz i (fun j hji => by rw [hj j hji])
    have noB (i : Fin 4) (hi : addOrderOf (r i) = B)
        (hj : ∀ j, j ≠ i → addOrderOf (r j) = A) : False := by
      apply hBA
      rw [← hi]
      exact singleton_order_dvd r hz i (fun j hji => by rw [hj j hji])
    have hA4 : v A ^ 4 = w A ^ 4 := by
      linear_combination (v A^2+w A^2)*hA
    have hB4 : v B ^ 4 = w B ^ 4 := by
      linear_combination (v B^2+w B^2)*hB
    have hAB2 : v A^2 * v B^2 = w A^2 * w B^2 := by rw [hA,hB]
    rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;>
      rcases hs 2 with h2 | h2 <;> rcases hs 3 with h3 | h3 <;>
      rw [Fin.prod_univ_four,Fin.prod_univ_four,h0,h1,h2,h3]
    · simpa only [pow_succ,pow_zero,mul_one,one_mul] using hA4
    · exact (noB 3 h3 (by intro j hj; fin_cases j <;> simp_all)).elim
    · exact (noB 2 h2 (by intro j hj; fin_cases j <;> simp_all)).elim
    · linear_combination hAB2
    · exact (noB 1 h1 (by intro j hj; fin_cases j <;> simp_all)).elim
    · linear_combination hAB2
    · linear_combination hAB2
    · exact (noA 0 h0 (by intro j hj; fin_cases j <;> simp_all)).elim
    · exact (noB 0 h0 (by intro j hj; fin_cases j <;> simp_all)).elim
    · linear_combination hAB2
    · linear_combination hAB2
    · exact (noA 1 h1 (by intro j hj; fin_cases j <;> simp_all)).elim
    · linear_combination hAB2
    · exact (noA 2 h2 (by intro j hj; fin_cases j <;> simp_all)).elim
    · exact (noA 3 h3 (by intro j hj; fin_cases j <;> simp_all)).elim
    · simpa only [pow_succ,pow_zero,mul_one,one_mul] using hB4
  · push Not at hs
    obtain ⟨j,hjA,hjB⟩ := hs
    have hzv : (∏ i, v (addOrderOf (r i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (hv _ hjA hjB)
    have hzw : (∏ i, w (addOrderOf (r i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (hw _ hjA hjB)
    rw [hzv,hzw]

open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Equality on every resonance is equality of the full literal observation. -/
theorem translatedMoment_eq_of_resonant_products (N : ℕ) (c e : ℕ → ℝ) (m : ℕ)
    (he : ∀ r : Fin m → ZMod N.factorial, (∑ i, r i) = 0 →
      (∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) =
        ∏ i, selbergMultiplesCoord N e (addOrderOf (r i))) (h : Fin m → ℕ) :
    translatedMoment N c h = translatedMoment N e h := by
  have hf : translationMoment (residueSignal N (fun d => (c d : ℂ))) =
      (translationMoment (residueSignal N (fun d => (e d : ℂ))) :
        (Fin m → ZMod N.factorial) → ℂ) := by
    apply momentDFT_injective m
    funext r
    rw [momentDFT_sieve,momentDFT_sieve]
    by_cases hz : (∑ i, r i) = 0
    · rw [if_pos hz,if_pos hz]
      apply congrArg (fun z : ℂ => (N.factorial : ℂ)^m*z)
      simp only [coordinate_ofReal]
      exact_mod_cast he r hz
    · rw [if_neg hz,if_neg hz]
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq,translatedMoment_complex_eq]
  exact congrFun hf (fun i => (h i : ZMod N.factorial))

/-- Two incomparable orders have identical quartic arrays whenever their squares agree. -/
theorem incomparable_quartic_moments (N A B : ℕ) (c e : ℕ → ℝ)
    (hAB : ¬ A ∣ B) (hBA : ¬ B ∣ A)
    (hc : ∀ q, q ≠ A → q ≠ B → selbergMultiplesCoord N c q = 0)
    (he : ∀ q, q ≠ A → q ≠ B → selbergMultiplesCoord N e q = 0)
    (hA : selbergMultiplesCoord N c A ^ 2 = selbergMultiplesCoord N e A ^ 2)
    (hB : selbergMultiplesCoord N c B ^ 2 = selbergMultiplesCoord N e B ^ 2)
    (h : Fin 4 → ℕ) : translatedMoment N c h = translatedMoment N e h := by
  apply translatedMoment_eq_of_resonant_products N c e 4 _ h
  intro r hz
  exact incomparable_quartic_products hAB hBA _ _ hc he hA hB r hz

/-- Squares of all coordinates determine all quadratic lag observations. -/
theorem quadratic_moments_of_coordinate_squares (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ q, selbergMultiplesCoord N c q ^ 2 = selbergMultiplesCoord N e q ^ 2)
    (h : Fin 2 → ℕ) : translatedMoment N c h = translatedMoment N e h := by
  apply translatedMoment_eq_of_resonant_products N c e 2 _ h
  intro r hz
  rw [Fin.sum_univ_two] at hz
  have hr : r 1 = -r 0 := by linear_combination hz
  rw [Fin.prod_univ_two,Fin.prod_univ_two,hr,addOrderOf_neg]
  simpa only [pow_two] using he (addOrderOf (r 0))

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
