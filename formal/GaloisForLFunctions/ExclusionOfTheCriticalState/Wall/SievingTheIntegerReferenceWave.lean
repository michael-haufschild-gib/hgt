import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegerWaveHasVanishingMeanAbsoluteError
import GaloisForLFunctions.HTGeometry.PrimeSieveEulerTrace

/-!
# Removing small prime factors from the integer reference wave

Adjoining a prime subtracts a translated copy of the previous reference.
Dividing by the sieve density preserves the polar wave exactly. In the error
recursion the local absolute multiplier is the inverse of 1 − 1/√p.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

/-- Density-normalized integer reference supported on the sifted integers. -/
def sievedIntegerReference (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  sievedSum (fun n : ℕ => continuousIntegerAtom Φ n t) P / sieveDensity P

private theorem sievedSum_insert_dilate {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P)
    {f : ℕ → ℝ} (hf : Summable f) :
    sievedSum f (insert p P) = sievedSum f P - sievedSum (fun n => f ((p:ℕ)*n)) P := by
  classical
  let A := {n : ℕ | n.Coprime (sievePrimorial P)}
  let M := {n : ℕ | n.Coprime (sievePrimorial P) ∧ (p:ℕ) ∣ n}
  have hinj : Function.Injective (fun n : ℕ => (p:ℕ)*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left p.2.pos h
  have hsupp : Function.support (M.indicator f) ⊆ Set.range (fun n : ℕ => (p:ℕ)*n) := by
    intro n hn
    by_contra hn'
    apply hn
    apply Set.indicator_of_notMem
    rintro ⟨_,⟨k,hk⟩⟩
    exact hn' ⟨k,hk.symm⟩
  have hm : (∑' n, M.indicator f n) = sievedSum (fun n => f ((p:ℕ)*n)) P := by
    rw [← hinj.tsum_eq hsupp,sievedSum]
    apply tsum_congr fun n => ?_
    by_cases hn : n.Coprime (sievePrimorial P)
    · rw [Set.indicator_of_mem (show (p:ℕ)*n ∈ M from
        ⟨Nat.coprime_mul_iff_left.2 ⟨coprime_sievePrimorial hp,hn⟩,⟨n,rfl⟩⟩),Set.indicator_of_mem (show n ∈ {m : ℕ | m.Coprime (sievePrimorial P)} from hn)]
    · rw [Set.indicator_of_notMem (show (p:ℕ)*n ∉ M from fun h => hn (Nat.coprime_mul_iff_left.1 h.1).2),
        Set.indicator_of_notMem (show n ∉ {m : ℕ | m.Coprime (sievePrimorial P)} from hn)]
  rw [← hm,sievedSum,sievedSum,← (hf.indicator A).tsum_sub (hf.indicator M)]
  apply tsum_congr fun n => ?_
  by_cases hn : n.Coprime (sievePrimorial P) <;> by_cases hd : (p:ℕ) ∣ n <;>
    simp [A,M,Set.indicator,coprime_sievePrimorial_insert_iff hp,hn,hd]
  split_ifs
  simp_all [M]

private theorem integerAtom_at_multiple (Φ : ℝ → ℝ) (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    continuousIntegerAtom Φ ((p:ℕ)*n:ℕ) t = (Real.sqrt (p:ℕ))⁻¹*continuousIntegerAtom Φ n (t-Real.log (p:ℕ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [continuousIntegerAtom]
  have hp : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.2.pos
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [continuousIntegerAtom,continuousIntegerAtom,Nat.cast_mul,Real.sqrt_mul hp.le,
    Real.log_mul hp.ne' hn0.ne',mul_inv_rev]
  rw [show t-(Real.log (p:ℕ)+Real.log n)=(t-Real.log (p:ℕ))-Real.log n by ring]; ring

/-- One new prime removes exactly the reference wave over its multiples. -/
theorem sievedIntegerReference_insert {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P)
    {Φ : ℝ → ℝ} {t : ℝ} (hf : Summable (fun n : ℕ => continuousIntegerAtom Φ n t)) :
    sievedIntegerReference (insert p P) Φ t = (sievedIntegerReference P Φ t -
      (Real.sqrt (p:ℕ))⁻¹*sievedIntegerReference P Φ (t-Real.log (p:ℕ)))/(1-((p:ℕ):ℝ)⁻¹) := by
  let s := (Real.sqrt (p:ℕ))⁻¹
  have hm : sievedSum (fun n : ℕ => continuousIntegerAtom Φ ((p:ℕ)*n:ℕ) t) P =
      s*sievedSum (fun n : ℕ => continuousIntegerAtom Φ n (t-Real.log (p:ℕ))) P := by
    rw [sievedSum,sievedSum,← tsum_mul_left]
    apply tsum_congr fun n => ?_
    by_cases hn : n.Coprime (sievePrimorial P)
    · rw [Set.indicator_of_mem (show n ∈ {m : ℕ | m.Coprime (sievePrimorial P)} from hn),Set.indicator_of_mem (show n ∈ {m : ℕ | m.Coprime (sievePrimorial P)} from hn)]; exact integerAtom_at_multiple Φ p n t
    · rw [Set.indicator_of_notMem (show n ∉ {m : ℕ | m.Coprime (sievePrimorial P)} from hn),Set.indicator_of_notMem (show n ∉ {m : ℕ | m.Coprime (sievePrimorial P)} from hn),mul_zero]
  rw [sievedIntegerReference,sievedSum_insert_dilate hp hf,hm,sieveDensity_insert hp,
    sievedIntegerReference,sievedIntegerReference]
  simp only [s,div_eq_mul_inv,mul_inv_rev]; ring

/-- Subtracting the polar term commutes exactly with sieve normalization. -/
def sievedReferenceError (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (A t : ℝ) : ℝ :=
  sievedIntegerReference P Φ t - Real.exp (t/2)*A

theorem sievedReferenceError_insert {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P)
    {Φ : ℝ → ℝ} {t : ℝ} (hf : Summable (fun n : ℕ => continuousIntegerAtom Φ n t)) (A : ℝ) :
    sievedReferenceError (insert p P) Φ A t = (sievedReferenceError P Φ A t -
      (Real.sqrt (p:ℕ))⁻¹*sievedReferenceError P Φ A (t-Real.log (p:ℕ)))/(1-((p:ℕ):ℝ)⁻¹) := by
  have hpos : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.2.pos
  have hr := Real.sq_sqrt hpos.le
  have hfactor : 0 < 1-((p:ℕ):ℝ)⁻¹ := sub_pos.2 ((inv_lt_one_iff₀).2 (Or.inr (one_lt_prime_cast p)))
  have he : Real.exp ((t-Real.log (p:ℕ))/2) = Real.exp (t/2)/Real.sqrt (p:ℕ) := by
    rw [sub_div,Real.exp_sub,Real.exp_half (Real.log (p:ℕ)),Real.exp_log hpos]
  have hpolar : (Real.sqrt (p:ℕ))⁻¹*Real.exp ((t-Real.log (p:ℕ))/2) = ((p:ℕ):ℝ)⁻¹*Real.exp (t/2) := by
    rw [he,show ((p:ℕ):ℝ)⁻¹ = ((Real.sqrt (p:ℕ))^2)⁻¹ from congrArg Inv.inv hr.symm]; ring
  simp only [sievedReferenceError,sievedIntegerReference_insert hp hf]
  rw [mul_sub,← mul_assoc _ (Real.exp _) A,hpolar,eq_div_iff hfactor.ne',sub_mul,div_mul_cancel₀ _ hfactor.ne']
  ring

private theorem translated_Iic_mass {g : ℝ → ℝ} {T s : ℝ} (hi : IntegrableOn g (Iic T)) (hs : 0 ≤ s) :
    IntegrableOn (fun t => g (t-s)) (Iic T) ∧
      (∫ t in Iic T, |g (t-s)|) ≤ ∫ t in Iic T, |g t| := by
  let v := (Iic T).indicator g
  have hv : Integrable v := (integrable_indicator_iff measurableSet_Iic).2 hi
  have hvt := hv.comp_sub_right s
  have hvG (t : ℝ) (ht : t ∈ Iic T) : v (t-s) = g (t-s) :=
    indicator_of_mem (show t-s ∈ Iic T from (sub_le_self t hs).trans ht) _
  refine ⟨hvt.integrableOn.congr_fun hvG measurableSet_Iic,?_⟩
  calc _ = ∫ t in Iic T, |v (t-s)| :=
         setIntegral_congr_fun measurableSet_Iic fun t ht => congrArg abs (hvG t ht).symm
    _ ≤ ∫ t, |v (t-s)| := setIntegral_le_integral hvt.abs (Eventually.of_forall fun _ => abs_nonneg _)
    _ = ∫ t, |v t| := integral_sub_right_eq_self (fun t => |v t|) s
    _ = _ := by
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae (Eventually.of_forall fun t => ?_)
      by_cases h : t ∈ Iic T <;> simp [v,h]

private theorem sqrt_prime_inv_lt (p : Nat.Primes) : (Real.sqrt (p:ℕ))⁻¹ < 1 := by
  apply (inv_lt_one_iff₀).2 (Or.inr _)
  simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (one_lt_prime_cast p)

/-- Exact upper bound for the integrated error after any finite set of primes is removed. -/
theorem sievedReferenceError_integral_le (P : Finset Nat.Primes) (Φ : ℝ → ℝ) (A T : ℝ)
    (hf : ∀ t : ℝ, Summable (fun n : ℕ => continuousIntegerAtom Φ n t))
    (hi : IntegrableOn (sievedReferenceError ∅ Φ A) (Iic T)) :
    IntegrableOn (sievedReferenceError P Φ A) (Iic T) ∧
    (∫ t in Iic T, |sievedReferenceError P Φ A t|) ≤
      (∏ p ∈ P, (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹)*(∫ t in Iic T, |sievedReferenceError ∅ Φ A t|) := by
  induction P using Finset.induction with
  | empty => simpa only [Finset.prod_empty,one_mul] using And.intro hi (le_refl _)
  | @insert p P hp ih =>
    let a := (Real.sqrt (p:ℕ))⁻¹
    let b := 1-((p:ℕ):ℝ)⁻¹
    let g := sievedReferenceError P Φ A
    let G := fun t : ℝ => g (t-Real.log (p:ℕ))
    have ha : 0 ≤ a := inv_nonneg.2 (Real.sqrt_nonneg _)
    have ha1 : a < 1 := sqrt_prime_inv_lt p
    have hb : 0 < b := sub_pos.2 ((inv_lt_one_iff₀).2 (Or.inr (one_lt_prime_cast p)))
    have he : sievedReferenceError (insert p P) Φ A = fun t => (g t-a*G t)/b :=
      funext fun t => sievedReferenceError_insert hp (hf t) A
    have hG := translated_Iic_mass ih.1 (Real.log_nonneg (one_lt_prime_cast p).le)
    have hi' : IntegrableOn (fun t => (g t-a*G t)/b) (Iic T) := (ih.1.sub (hG.1.const_mul a)).div_const b
    have hmass := hG.2
    have hfac : (1+a)/b = (1-a)⁻¹ := by
      have hs : a^2 = ((p:ℕ):ℝ)⁻¹ := by dsimp only [a]; rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      change (1+a)/(1-((p:ℕ):ℝ)⁻¹) = _
      rw [← hs]
      field_simp [(sub_pos.2 ha1).ne',show 1-a^2 ≠ 0 by rw [hs]; exact hb.ne']
      ring
    rw [he,Finset.prod_insert hp]
    refine ⟨hi',?_⟩
    calc _ ≤ ∫ t in Iic T, (|g t|+a*|G t|)/b := by
           apply integral_mono hi'.abs ((ih.1.abs.add (hG.1.abs.const_mul a)).div_const b)
           intro t
           change |(g t-a*G t)/b| ≤ (|g t|+a*|G t|)/b
           rw [abs_div,abs_of_pos hb]
           exact div_le_div_of_nonneg_right ((abs_sub _ _).trans_eq (by rw [abs_mul,abs_of_nonneg ha])) hb.le
      _ ≤ ((1+a)/b)*(∫ t in Iic T, |g t|) := by
           rw [integral_div,integral_add ih.1.abs (hG.1.abs.const_mul a),integral_const_mul]
           have h := mul_le_mul_of_nonneg_left hmass ha
           calc _ ≤ ((∫ t in Iic T, |g t|)+a*(∫ t in Iic T, |g t|))/b :=
                    div_le_div_of_nonneg_right (add_le_add le_rfl h) hb.le
             _ = _ := by ring
      _ ≤ _ := by
           rw [hfac,mul_assoc]
           exact mul_le_mul_of_nonneg_left ih.2 (inv_nonneg.2 (sub_pos.2 ha1).le)

#print axioms sievedReferenceError_integral_le
#print axioms sievedReferenceError_insert

end GaloisForLFunctions.ExclusionOfTheCriticalState
