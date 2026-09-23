import GaloisForLFunctions.RHTower.MobiusDivisorHeadNeutralization

/-!
# Uniform mass rounding of complete late-prime histories

The first covering prefix of any fixed enumeration rounds a consumed
nonnegative mass upward by at most one coefficient. Replacing an actual
late subset by that prefix changes the head and removed singleton squares
through an exact source identity. Its energy error is bounded at each state,
independently of how many states preceded it. Nested replacements preserve
middle-prime insertions and control every internal late-prime block state.
A uniform quadratic energy order therefore permits any fixed relative order
of its isolated late primes, with a uniform enlargement of the constant.
This does not construct the interacting middle-prime order.
-/

noncomputable section
open Finset
namespace RHTower

/-- First bounded prefix whose mass reaches the target; the terminal index is the fallback. -/
def firstMassPrefix (w : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  if h : ∃ j, j ≤ n ∧ t ≤ ∑ i ∈ range j, w i then Nat.find h else n

private theorem prefix_exists (w : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (ht : t ≤ ∑ i ∈ range n,w i) : ∃ j,j ≤ n ∧ t ≤ ∑ i ∈ range j,w i :=
  ⟨n,le_rfl,ht⟩

/-- The selected prefix is bounded and covers every attainable target. -/
theorem firstMassPrefix_spec (w : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (ht : t ≤ ∑ i ∈ range n,w i) :
    firstMassPrefix w n t ≤ n ∧ t ≤ ∑ i ∈ range (firstMassPrefix w n t),w i := by
  rw [firstMassPrefix,dif_pos (prefix_exists w n t ht)]
  exact Nat.find_spec (prefix_exists w n t ht)

/-- Larger attainable targets select nested prefixes in the same fixed order. -/
theorem firstMassPrefix_mono (w : ℕ → ℝ) (n : ℕ) {s t : ℝ}
    (hst : s ≤ t) (ht : t ≤ ∑ i ∈ range n,w i) :
    firstMassPrefix w n s ≤ firstMassPrefix w n t := by
  have hs := hst.trans ht
  have h := firstMassPrefix_spec w n t ht
  rw [firstMassPrefix,dif_pos (prefix_exists w n s hs)]
  exact Nat.find_min' (prefix_exists w n s hs) ⟨h.1,hst.trans h.2⟩

/-- A zero target uses the empty prefix. -/
theorem firstMassPrefix_zero (w : ℕ → ℝ) (n : ℕ) : firstMassPrefix w n 0 = 0 := by
  have hex : ∃ j,j ≤ n ∧ (0:ℝ) ≤ ∑ i ∈ range j,w i := ⟨0,Nat.zero_le _,by simp⟩
  rw [firstMassPrefix,dif_pos hex]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ⟨Nat.zero_le _,by simp⟩)

/-- Upward rounding loses at most one coefficient, uniformly over the entire target interval. -/
theorem firstMassPrefix_mass_le (w : ℕ → ℝ) (n : ℕ) (t D : ℝ)
    (ht0 : 0 ≤ t) (hD : 0 ≤ D) (hw : ∀ i < n,w i ≤ D)
    (ht : t ≤ ∑ i ∈ range n,w i) :
    ∑ i ∈ range (firstMassPrefix w n t),w i ≤ t+D := by
  have hex := prefix_exists w n t ht
  rw [firstMassPrefix,dif_pos hex]
  generalize hj : Nat.find hex = j
  have hjn : j ≤ n := hj ▸ (Nat.find_spec hex).1
  cases j with
  | zero => simpa using add_nonneg ht0 hD
  | succ k =>
    have hk : ¬ (k ≤ n ∧ t ≤ ∑ i ∈ range k,w i) :=
      Nat.find_min hex (by rw [hj]; omega)
    have hbefore : (∑ i ∈ range k,w i) < t := by
      exact lt_of_not_ge (fun h => hk ⟨by omega,h⟩)
    rw [Finset.sum_range_succ]
    linarith [hw k (by omega)]

/-- An arbitrary fixed enumeration of source indices, truncated at a prefix length. -/
def primeOrderPrefix (e : ℕ → ℕ) (j : ℕ) : Finset ℕ := (range j).image e

/-- Prefixes are nested without any arithmetic or sorting assumption. -/
theorem primeOrderPrefix_mono (e : ℕ → ℕ) : Monotone (primeOrderPrefix e) := by
  intro i j hij
  exact image_subset_image (range_mono hij)

/-- Injective enumeration retains the literal mass of every bounded prefix. -/
theorem primeOrderPrefix_mass (M n : ℕ) (e : ℕ → ℕ)
    (he : Set.InjOn e (range n)) {j : ℕ} (hj : j ≤ n) :
    (∑ p ∈ primeOrderPrefix e j,divisorUnsignedDilationChannel M p) =
      ∑ i ∈ range j,divisorUnsignedDilationChannel M (e i) := by
  apply sum_image
  intro a ha b hb hab
  exact he (range_mono hj ha) (range_mono hj hb) hab

private theorem late_signed_mass (M : ℕ) (L : Finset ℕ) (hL : ∀ p ∈ L,p.Prime) :
    (∑ p ∈ L,mobiusDivisorDilationChannel M p) =
      -(∑ p ∈ L,divisorUnsignedDilationChannel M p) := by
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro p hp
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime (hL p hp)]
  push_cast
  ring

/-- Replacing a late subset changes only its removed squares and the mass displaced in the head. -/
theorem mobiusDivisorSelectionEnergy_late_mass_difference (M : ℕ) (P R L : Finset ℕ)
    (hR : ∀ p ∈ R,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hfR : ∀ p ∈ R,p ∉ P) (hfL : ∀ p ∈ L,p ∉ P) :
    let d := (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
      ∑ p ∈ R,divisorUnsignedDilationChannel M p
    mobiusDivisorSelectionEnergy M (P ∪ L)-mobiusDivisorSelectionEnergy M (P ∪ R) =
      -2*mobiusDivisorSelectionFibre M (P ∪ R) ∅*d+d^(2 : ℕ)+
        (∑ p ∈ R,(mobiusDivisorDilationChannel M p)^(2 : ℕ))-
        ∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ) := by
  dsimp only
  rw [mobiusDivisorSelectionEnergy_union_late_primes M P L hL hfL,
    mobiusDivisorSelectionEnergy_union_late_primes M P R hR hfR,
    mobiusDivisorSelectionHead_union_late_primes M P R hR hfR,
    late_signed_mass M L (fun p hp => (hL p hp).1),
    late_signed_mass M R (fun p hp => (hR p hp).1)]
  ring

/-- Bounded mass displacement has one pointwise energy cost, independent of the number of prior steps. -/
theorem mobiusDivisorSelectionEnergy_late_mass_rounding_le (M : ℕ) (P R L : Finset ℕ)
    (hR : ∀ p ∈ R,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hfR : ∀ p ∈ R,p ∉ P) (hfL : ∀ p ∈ L,p ∉ P) (B D : ℝ)
    (hQ : mobiusDivisorSelectionEnergy M (P ∪ R) ≤ B)
    (hd0 : 0 ≤ (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
      ∑ p ∈ R,divisorUnsignedDilationChannel M p)
    (hdD : (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
      (∑ p ∈ R,divisorUnsignedDilationChannel M p) ≤ D) :
    mobiusDivisorSelectionEnergy M (P ∪ L) ≤ B+2*Real.sqrt B*D+D^(2 : ℕ)+
      ∑ p ∈ R,(mobiusDivisorDilationChannel M p)^(2 : ℕ) := by
  let d := (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
    ∑ p ∈ R,divisorUnsignedDilationChannel M p
  have hd : 0 ≤ d := hd0
  have hDd : d ≤ D := hdD
  have hD : 0 ≤ D := hd.trans hDd
  have he := mobiusDivisorSelectionEnergy_late_mass_difference M P R L hR hL hfR hfL
  change mobiusDivisorSelectionEnergy M (P ∪ L)-mobiusDivisorSelectionEnergy M (P ∪ R) =
    -2*mobiusDivisorSelectionFibre M (P ∪ R) ∅*d+d^(2 : ℕ)+
      (∑ p ∈ R,(mobiusDivisorDilationChannel M p)^(2 : ℕ))-
      ∑ p ∈ L,(mobiusDivisorDilationChannel M p)^(2 : ℕ) at he
  have hhead := (abs_mobiusDivisorSelectionHead_le_sqrt_energy M (P ∪ R)).trans
    (Real.sqrt_le_sqrt hQ)
  have hf := (abs_le.mp hhead).1
  have hsL := sum_nonneg (s := L) (fun p _ => sq_nonneg (mobiusDivisorDilationChannel M p))
  nlinarith [mul_nonneg (show 0 ≤ mobiusDivisorSelectionFibre M (P ∪ R) ∅+Real.sqrt B by linarith) hd,
    mul_nonneg (Real.sqrt_nonneg B) (sub_nonneg.mpr hDd),
    mul_nonneg (sub_nonneg.mpr hDd) (add_nonneg hD hd)]

/-- Any replacement with at most a square-root mass error keeps a uniform quadratic energy bound. -/
theorem mobiusDivisorSelectionEnergy_late_rounding_quadratic (M : ℕ) (hM : 1 ≤ M)
    (P R L : Finset ℕ)
    (hR : ∀ p ∈ R,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ M ≤ 2*p)
    (hfR : ∀ p ∈ R,p ∉ P) (hfL : ∀ p ∈ L,p ∉ P) (C : ℝ) (hC : 0 ≤ C)
    (hQ : mobiusDivisorSelectionEnergy M (P ∪ R) ≤ C*(M:ℝ)^(2 : ℕ))
    (hd0 : 0 ≤ (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
      ∑ p ∈ R,divisorUnsignedDilationChannel M p)
    (hdD : (∑ p ∈ L,divisorUnsignedDilationChannel M p)-
      (∑ p ∈ R,divisorUnsignedDilationChannel M p) ≤ Real.sqrt M) :
    mobiusDivisorSelectionEnergy M (P ∪ L) ≤ (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ) := by
  have h := mobiusDivisorSelectionEnergy_late_mass_rounding_le M P R L hR hL hfR hfL
    (C*(M:ℝ)^(2 : ℕ)) (Real.sqrt M) hQ hd0 hdD
  have hsub : R ⊆ Icc 1 M := by
    intro p hp
    exact mem_Icc.mpr ⟨(hR p hp).1.pos,(hR p hp).2.1.le⟩
  have hs := (sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => sq_nonneg (mobiusDivisorDilationChannel M p))).trans
    (sum_mobiusDivisorDilationChannel_sq_le_quadratic M)
  rw [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg M),
    Real.sq_sqrt (Nat.cast_nonneg M)] at h
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hr : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hm)
  have hprod := mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) hm0) (sub_nonneg.mpr hr)
  nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm)]

/-- Every intermediate subset between two late-prefix endpoints obeys their common ceiling. -/
theorem mobiusDivisorSelectionEnergy_between_late_subsets_le (M : ℕ) (P A L V : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p < M ∧ M ≤ 2*p) (hfL : ∀ p ∈ L,p ∉ P)
    (hAV : A ⊆ V) (hVL : V ⊆ L) (B : ℝ)
    (hA : mobiusDivisorSelectionEnergy M (P ∪ A) ≤ B)
    (hB : mobiusDivisorSelectionEnergy M (P ∪ L) ≤ B) :
    mobiusDivisorSelectionEnergy M (P ∪ V) ≤ B := by
  have hAL := hAV.trans hVL
  have hs : ∀ W : Finset ℕ,A ⊆ W → (P ∪ A) ∪ (W \ A)=P ∪ W := by
    intro W hAW
    ext p
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro ((hp|hp)|⟨hp,_⟩)
      · exact Or.inl hp
      · exact Or.inr (hAW hp)
      · exact Or.inr hp
    · intro hp
      by_cases hpA : p ∈ A
      · exact Or.inl (Or.inr hpA)
      · rcases hp with hp | hp
        · exact Or.inl (Or.inl hp)
        · exact Or.inr ⟨hp,hpA⟩
  have hfree : ∀ p ∈ L \ A,p ∉ P ∪ A := by
    intro p hp
    simp only [mem_union,not_or]
    exact ⟨hfL p (mem_sdiff.mp hp).1,(mem_sdiff.mp hp).2⟩
  have hsub : V \ A ⊆ L \ A := by
    intro p hp
    exact mem_sdiff.mpr ⟨hVL (mem_sdiff.mp hp).1,(mem_sdiff.mp hp).2⟩
  have h := mobiusDivisorSelectionEnergy_late_block_le_max_endpoints M (P ∪ A) (L \ A)
    (V \ A) (fun p hp => hL p (mem_sdiff.mp hp).1) hfree hsub
  rw [hs V hAV,hs L hAL] at h
  exact h.trans (max_le hA hB)

/-- Any monotone late-subset history admits replacements in any fixed enumerated late order.
The uniform bound includes every intermediate late prefix, unchanged-mass middle steps,
and the terminal completion of the fixed order. -/
theorem exists_mobiusDivisor_fixed_late_order_history (M n : ℕ) (hM : 1 ≤ M)
    (e : ℕ → ℕ) (he : Set.InjOn e (range n))
    (hprime : ∀ i < n,(e i).Prime ∧ e i < M ∧ M ≤ 2*e i)
    (P R : ℕ → Finset ℕ) (hRmono : Monotone R)
    (hR : ∀ k,R k ⊆ primeOrderPrefix e n)
    (hfree : ∀ k,∀ p ∈ primeOrderPrefix e n,p ∉ P k)
    (C : ℝ) (hC : 0 ≤ C)
    (hQ : ∀ k,mobiusDivisorSelectionEnergy M (P k ∪ R k) ≤ C*(M:ℝ)^(2 : ℕ)) :
    ∃ j : ℕ → ℕ,Monotone j ∧ (∀ k,j k ≤ n) ∧
      (∀ k,mobiusDivisorSelectionEnergy M (P k ∪ primeOrderPrefix e (j k)) ≤
        (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) ∧
      (∀ k l,(∑ p ∈ R k,divisorUnsignedDilationChannel M p)=
        (∑ p ∈ R l,divisorUnsignedDilationChannel M p) → j k=j l) ∧
      (∀ k l,P k=P l → ∀ r,j k ≤ r → r ≤ j l →
        mobiusDivisorSelectionEnergy M (P k ∪ primeOrderPrefix e r) ≤
          (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) ∧
      (∀ k,R k=primeOrderPrefix e n → ∀ r,j k ≤ r → r ≤ n →
        mobiusDivisorSelectionEnergy M (P k ∪ primeOrderPrefix e r) ≤
          (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) ∧
      (∀ k,R k=∅ → j k=0) := by
  let w : ℕ → ℝ := fun i => divisorUnsignedDilationChannel M (e i)
  let t : ℕ → ℝ := fun k => ∑ p ∈ R k,divisorUnsignedDilationChannel M p
  let j : ℕ → ℕ := fun k => firstMassPrefix w n (t k)
  have hU : ∀ p ∈ primeOrderPrefix e n,p.Prime ∧ p < M ∧ M ≤ 2*p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hT (k : ℕ) : t k ≤ ∑ i ∈ range n,w i := by
    have h := sum_le_sum_of_subset_of_nonneg (hR k)
      (fun p _ _ => divisorUnsignedDilationChannel_nonneg M p)
    rw [primeOrderPrefix_mass M n e he le_rfl] at h
    exact h
  have htnonneg (k : ℕ) : 0 ≤ t k := sum_nonneg
    (fun p _ => divisorUnsignedDilationChannel_nonneg M p)
  have hw (i : ℕ) (hi : i < n) : w i ≤ Real.sqrt M :=
    divisorUnsignedDilationChannel_late_le_sqrt (hprime i hi).1.pos
      (hprime i hi).2.1 (hprime i hi).2.2
  have hjn (k : ℕ) : j k ≤ n := (firstMassPrefix_spec w n (t k) (hT k)).1
  have hjmono : Monotone j := by
    intro k l hkl
    apply firstMassPrefix_mono w n _ (hT l)
    exact sum_le_sum_of_subset_of_nonneg (hRmono hkl)
      (fun p _ _ => divisorUnsignedDilationChannel_nonneg M p)
  have hmass (k : ℕ) :
      0 ≤ (∑ p ∈ primeOrderPrefix e (j k),divisorUnsignedDilationChannel M p)-t k ∧
      (∑ p ∈ primeOrderPrefix e (j k),divisorUnsignedDilationChannel M p)-t k ≤ Real.sqrt M := by
    rw [primeOrderPrefix_mass M n e he (hjn k)]
    have hlo := (firstMassPrefix_spec w n (t k) (hT k)).2
    have hhi := firstMassPrefix_mass_le w n (t k) (Real.sqrt M) (htnonneg k)
      (Real.sqrt_nonneg _) hw (hT k)
    constructor <;> linarith only [hlo,hhi]
  have hbound (k : ℕ) :
      mobiusDivisorSelectionEnergy M (P k ∪ primeOrderPrefix e (j k)) ≤
        (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ) := by
    have hsub := primeOrderPrefix_mono e (hjn k)
    exact mobiusDivisorSelectionEnergy_late_rounding_quadratic M hM (P k) (R k)
      (primeOrderPrefix e (j k)) (fun p hp => hU p (hR k hp))
      (fun p hp => hU p (hsub hp)) (fun p hp => hfree k p (hR k hp))
      (fun p hp => hfree k p (hsub hp)) C hC (hQ k) (hmass k).1 (hmass k).2
  have hCB : C*(M:ℝ)^(2 : ℕ) ≤ (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg C) (sq_nonneg (M:ℝ)),sq_nonneg (M:ℝ)]
  refine ⟨j,hjmono,hjn,hbound,?_,?_,?_,?_⟩
  · intro k l h
    exact congrArg (firstMassPrefix w n) h
  · intro k l hP r hkr hrl
    have hL := primeOrderPrefix_mono e (hjn l)
    have hright := hbound l
    rw [← hP] at hright
    exact mobiusDivisorSelectionEnergy_between_late_subsets_le M (P k)
      (primeOrderPrefix e (j k)) (primeOrderPrefix e (j l)) (primeOrderPrefix e r)
      (fun p hp => hU p (hL hp)) (fun p hp => hfree k p (hL hp))
      (primeOrderPrefix_mono e hkr) (primeOrderPrefix_mono e hrl) _ (hbound k) hright
  · intro k hfull r hkr hrn
    have hright := hQ k
    rw [hfull] at hright
    exact mobiusDivisorSelectionEnergy_between_late_subsets_le M (P k)
      (primeOrderPrefix e (j k)) (primeOrderPrefix e n) (primeOrderPrefix e r)
      hU (hfree k) (primeOrderPrefix_mono e hkr) (primeOrderPrefix_mono e hrn)
      _ (hbound k) (hright.trans hCB)
  · intro k hk
    dsimp [j,t]
    rw [hk,sum_empty,firstMassPrefix_zero]

/-- Canonical late-order transformation of an actual monotone processed-prime chain.
Every middle step is retained literally; every late step is replaced by a bounded
block in the prescribed order. The start and completion include all actual terms. -/
theorem exists_mobiusDivisor_fixed_late_order_chain (M n : ℕ) (hM : 1 ≤ M)
    (e : ℕ → ℕ) (he : Set.InjOn e (range n))
    (hprime : ∀ i < n,(e i).Prime ∧ e i < M ∧ M ≤ 2*e i)
    (H : ℕ → Finset ℕ) (hHmono : Monotone H) (hH0 : H 0=∅)
    (C : ℝ) (hC : 0 ≤ C)
    (hQ : ∀ k,mobiusDivisorSelectionEnergy M (H k) ≤ C*(M:ℝ)^(2 : ℕ)) :
    ∃ j : ℕ → ℕ,Monotone j ∧ j 0=0 ∧ (∀ k,j k ≤ n) ∧
      (∀ k,mobiusDivisorSelectionEnergy M
        ((H k \ primeOrderPrefix e n) ∪ primeOrderPrefix e (j k)) ≤
          (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) ∧
      (∀ k q,H (k+1)=insert q (H k) → q ∉ primeOrderPrefix e n →
        j (k+1)=j k ∧
        ((H (k+1) \ primeOrderPrefix e n) ∪ primeOrderPrefix e (j (k+1))) =
          insert q ((H k \ primeOrderPrefix e n) ∪ primeOrderPrefix e (j k))) ∧
      (∀ k q,H (k+1)=insert q (H k) → q ∈ primeOrderPrefix e n →
        (H (k+1) \ primeOrderPrefix e n)=(H k \ primeOrderPrefix e n) ∧
        ∀ r,j k ≤ r → r ≤ j (k+1) → mobiusDivisorSelectionEnergy M
          ((H k \ primeOrderPrefix e n) ∪ primeOrderPrefix e r) ≤
            (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) ∧
      (∀ k,primeOrderPrefix e n ⊆ H k → ∀ r,j k ≤ r → r ≤ n →
        mobiusDivisorSelectionEnergy M
          ((H k \ primeOrderPrefix e n) ∪ primeOrderPrefix e r) ≤
            (C+2*Real.sqrt C+723)*(M:ℝ)^(2 : ℕ)) := by
  let U := primeOrderPrefix e n
  let P : ℕ → Finset ℕ := fun k => H k \ U
  let R : ℕ → Finset ℕ := fun k => H k ∩ U
  have hdecomp (k : ℕ) : P k ∪ R k=H k := by
    ext p
    simp only [P,R,mem_union,mem_sdiff,mem_inter]
    tauto
  have hRmono : Monotone R := by
    intro k l hkl p hp
    exact mem_inter.mpr ⟨hHmono hkl (mem_inter.mp hp).1,(mem_inter.mp hp).2⟩
  have hfree : ∀ k,∀ p ∈ U,p ∉ P k := by
    intro k p hp hn
    exact (mem_sdiff.mp hn).2 hp
  obtain ⟨j,hjmono,hjn,hbound,hjeq,hbetween,hend,hzero⟩ :=
    exists_mobiusDivisor_fixed_late_order_history M n hM e he hprime P R hRmono
      (fun _ => inter_subset_right) hfree C hC (fun k => by rw [hdecomp]; exact hQ k)
  have hstart : j 0=0 := hzero 0 (by simp [R,hH0])
  refine ⟨j,hjmono,hstart,hjn,hbound,?_,?_,?_⟩
  · intro k q hstep hq
    have hRstep : R (k+1)=R k := by
      dsimp only [R]
      rw [hstep,insert_inter_of_notMem hq]
    have hj : j (k+1)=j k := hjeq (k+1) k (by rw [hRstep])
    refine ⟨hj,?_⟩
    rw [hj,hstep,insert_sdiff_of_notMem _ hq,insert_union]
  · intro k q hstep hq
    have hPstep : P (k+1)=P k := by
      dsimp only [P]
      rw [hstep,insert_sdiff_of_mem _ hq]
    refine ⟨hPstep,?_⟩
    exact hbetween k (k+1) hPstep.symm
  · intro k hk
    apply hend k
    exact inter_eq_right.mpr hk

end RHTower
