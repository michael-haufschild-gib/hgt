import GaloisForLFunctions.CountingHolography.Sections.TheJetRadiusOfPoleBalancedSections
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Small multiplicities on square conductors

The three conductors have only bounded or quadratic ratios. At a quadratic
lag each unrounded row costs at most a constant times m²/n. If this is
smaller than one, all positive exponents come from a fixed finite prime set.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset AbsoluteGeometryOfSpecZ ArithmeticFunction

/-- At any fixed total multiplicity the positive ordinary-prime product
is bounded independently of the number and sizes of the conductors. -/
theorem ordinary_modulus_quartic : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    Real.log (ordinaryPrimeModulus a) ≤ C*(∑ i, |(a i : ℝ)|)^4 := by
  obtain ⟨A,hA,h⟩ := contactMultiplicity_size
  refine ⟨34*A^2,by positivity,fun N a => ?_⟩
  let M := ∑ i, |(a i : ℝ)|
  let T := A*M^2
  have ht : 0 ≤ T := mul_nonneg (zero_le_one.trans hA) (sq_nonneg _)
  let L := 3*windowEnd N
  let Q := ⌊T^2⌋₊
  let x := contactMultiplicity (packet a) L (resolution a)
  let S := (Icc 2 L).filter Nat.Prime
  let J := S.filter (· ≤ Q)
  have bound (k : ℕ) : x k ≤ T/Real.sqrt k := (le_abs_self _).trans (h N a L (resolution a) k)
  have hf (k : ℕ) : (⌊x k⌋₊ : ℝ) ≤ T/Real.sqrt k := by
    by_cases hneg : x k < 0
    · rw [Nat.floor_of_nonpos hneg.le,Nat.cast_zero]
      exact div_nonneg ht (Real.sqrt_nonneg _)
    exact (Nat.floor_le (le_of_not_gt hneg)).trans (bound k)
  have htail : ∀ k ∈ S, k ∉ J → (⌊x k⌋₊ : ℝ)*vonMangoldt k = 0 := by
    intro k hk hj
    have hp := (mem_filter.mp hk).2.pos
    have hkr : T^2 < (k:ℝ) := lt_of_not_ge fun he =>
      hj (mem_filter.mpr ⟨hk,Nat.le_floor he⟩)
    have hs := Real.sqrt_lt_sqrt (sq_nonneg T) hkr
    rw [Real.sqrt_sq ht] at hs
    have hx : x k < 1 := (bound k).trans_lt ((div_lt_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp))).mpr hs)
    rw [Nat.floor_eq_zero.mpr hx,Nat.cast_zero,zero_mul]
  have hJ : J ⊆ Ioc 0 Q := fun k hk => mem_Ioc.mpr
    ⟨(mem_filter.mp (mem_filter.mp hk).1).2.pos,(mem_filter.mp hk).2⟩
  have hs := _root_.RHTower.sum_vonMangoldt_div_sqrt_le Q
  have hQ : (Q:ℝ) ≤ T^2 := Nat.floor_le (sq_nonneg _)
  have hroot := Real.sqrt_le_sqrt hQ
  rw [Real.sqrt_sq ht] at hroot
  rw [log_ordinaryPrimeModulus]
  change (∑ k ∈ S, (⌊x k⌋₊ : ℝ)*vonMangoldt k) ≤ _
  rw [← sum_subset (filter_subset _ _) htail]
  calc _ ≤ ∑ k ∈ J, T*(vonMangoldt k/Real.sqrt k) := sum_le_sum fun k _ =>
          (mul_le_mul_of_nonneg_right (hf k) vonMangoldt_nonneg).trans_eq (by ring)
    _ ≤ T*(34*T) := by
          rw [← mul_sum]
          apply mul_le_mul_of_nonneg_left _ ht
          refine (sum_le_sum_of_subset_of_nonneg hJ
            (fun k _ _ => div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))).trans ?_
          exact hs.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
    _ = _ := by unfold T M; ring

private theorem square_contact_gap : ∃ D : ℝ, 1 ≤ D ∧ ∀ {n k L r : ℕ}, 0 < n →
    contactMultiplicity (packet (successorSquareTriple n)) L r k ≠ 0 →
      (k:ℝ) ≤ 9*D ∨ (n:ℝ)^2 ≤ D*k := by
  obtain ⟨D,hD,hd⟩ := contactMultiplicity_support
  refine ⟨D,hD,fun {n k L r} hn h => ?_⟩
  obtain ⟨i,j,hi,hj,h₁,h₂⟩ := hd _ _ L r k h
  let p := (n:ℝ)^2
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hD' := zero_le_one.trans hD
  have hp : 0 < p := sq_pos_of_pos (zero_lt_one.trans_le hn')
  have ht : p ≤ ((2*n+1:ℕ):ℝ)^2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    push_cast
    linarith only [hn']
  have htop : ((2*n+1:ℕ):ℝ)^2 ≤ 9*p := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*n+1)
      (by linarith only [hn'] : 2*(n:ℝ)+1 ≤ 3*n) 2
    push_cast
    linarith only [hh]
  have split {l : Fin ((2*n+1)^2+1)} (hl : successorSquareTriple n l ≠ 0) :
      (l:ℝ)+1 = 1 ∨ p ≤ (l:ℝ)+1 := by
    rcases successorSquareTriple_support hn hl with he | he | he
    · exact Or.inl he
    · exact Or.inr he.ge
    · exact Or.inr (ht.trans_eq he.symm)
  rcases split hi with he | he
  · rw [he,mul_one] at h₁ h₂
    rcases split hj with hj' | hj'
    · rw [hj',mul_one] at h₁
      exact Or.inl (by linarith only [h₁,hD])
    · exact Or.inr (hj'.trans h₂)
  · have hj' : (j:ℝ)+1 ≤ 9*p := by
      rcases successorSquareTriple_support hn hj with h | h | h
      · rw [h]
        linarith only [one_le_pow₀ hn' (n := 2)]
      · rw [h]
        linarith only [hp]
      · exact h.le.trans htop
    apply Or.inl
    apply (mul_le_mul_iff_left₀ hp).mp
    linarith only [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α := ℝ) k),h₁,
      mul_le_mul_of_nonneg_left hj' hD']

/-- Below a fixed multiple of the square-root multiplicity every positive
contact exponent is supported in the same finite set of lags. -/
theorem positive_successorSquare_contacts_at_small_multiplicity :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ {n m : ℕ}, 0 < n → C*(m:ℝ)^2 ≤ n →
      ∀ {k L r : ℕ}, Q < k →
        contactMultiplicity (packet (m • successorSquareTriple n)) L r k < 1 := by
  obtain ⟨D,hD,hd⟩ := square_contact_gap
  obtain ⟨A,hA,ha⟩ := contactMultiplicity_size
  have hA' := zero_lt_one.trans_le hA
  have hD' := zero_lt_one.trans_le hD
  refine ⟨32*A*D,by positivity,⌈9*D⌉₊,fun {n m} hn hm {k L r} hk => ?_⟩
  let X := contactMultiplicity (packet (successorSquareTriple n)) L r k
  rw [packet_smul,contactMultiplicity_scale]
  change (m:ℝ)^2*X < 1
  by_cases hx : X = 0
  · rw [hx,mul_zero]; exact zero_lt_one
  rcases hd hn hx with hlow | hhigh
  · have hk' : (⌈9*D⌉₊ : ℝ) < k := by exact_mod_cast hk
    exact False.elim (hk'.not_ge (hlow.trans (Nat.le_ceil _)))
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hrt := Real.sqrt_le_sqrt hhigh
  rw [Real.sqrt_sq hn'.le,Real.sqrt_mul hD'.le] at hrt
  have hs := hrt.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hD)) (Real.sqrt_nonneg _))
  have hfit : 32*A*(m:ℝ)^2 ≤ Real.sqrt k := by
    apply (mul_le_mul_iff_right₀ hD').mp
    linarith only [hm,hs]
  have hmul : (m:ℝ)^2*(16*A) < Real.sqrt k := by
    by_cases hzero : m = 0
    · simpa only [hzero,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_mul] using Real.sqrt_pos.mpr hk'
    · have hp := mul_pos hA' (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero) : 0<(m:ℝ)))
      linarith only [hfit,hp]
  have hmass := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
  have ht : X ≤ 16*A/Real.sqrt k := (le_abs_self X).trans ((ha _ _ L r k).trans
    (div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_left hmass hA'.le]) (Real.sqrt_nonneg _)))
  refine (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_lt ?_
  rw [← mul_div_assoc,div_lt_one (Real.sqrt_pos.mpr hk')]
  exact hmul

/-- In the square-root range even the product of all positive ordinary
valuations fits in a single integer base to the power m². -/
theorem small_multiplicity_ordinary_modulus : ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧
    ∀ {n m : ℕ}, 0 < n → C*(m:ℝ)^2 ≤ n →
      ordinaryPrimeModulus (m • successorSquareTriple n) ≤ B^(m^2) := by
  obtain ⟨C,hC,Q,hQ⟩ := positive_successorSquare_contacts_at_small_multiplicity
  obtain ⟨A,hA,hsize⟩ := contactMultiplicity_size
  have hA0 := zero_le_one.trans hA
  let W := ∑ k ∈ Icc 2 Q, vonMangoldt k
  let B := ⌈Real.exp (16*A*W)⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hlog : 16*A*W ≤ Real.log B :=
    (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
  refine ⟨C,hC,B,hB,fun {n m} hn hm => ?_⟩
  let a := successorSquareTriple n
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution (m • a)
  let x := fun k => contactMultiplicity (packet (m • a)) L r k
  let S := (Icc 2 L).filter Nat.Prime
  let T := S.filter (· ≤ Q)
  let M := 16*A*(m:ℝ)^2
  have hM : 0 ≤ M := by unfold M; positivity
  have hx (k : ℕ) (hk : k ∈ S) : (⌊x k⌋₊ : ℝ) ≤ M := by
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast (mem_filter.mp hk).2.one_le
    have hr' : 1 ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk'
    by_cases hneg : x k < 0
    · simpa only [Nat.floor_of_nonpos hneg.le,Nat.cast_zero] using hM
    refine (Nat.floor_le (le_of_not_gt hneg)).trans ?_
    have he := hsize _ a L r k
    have hmass := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
    have hb : contactMultiplicity (packet a) L r k ≤ 16*A :=
      (le_abs_self _).trans (he.trans ((div_le_self (by positivity) hr').trans
        (by linarith only [mul_le_mul_of_nonneg_left hmass hA0])))
    unfold x
    rw [packet_smul,contactMultiplicity_scale]
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq (by unfold M; ring)
  have hs : ∀ k ∈ S, k ∉ T → (⌊x k⌋₊ : ℝ)*vonMangoldt k = 0 := by
    intro k hk ht
    have hkQ : Q < k := lt_of_not_ge fun he => ht (mem_filter.mpr ⟨hk,he⟩)
    have hx' : x k < 1 := hQ hn hm hkQ
    rw [Nat.floor_eq_zero.mpr hx',Nat.cast_zero,zero_mul]
  have hT : T ⊆ Icc 2 Q := fun k hk => mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp (mem_filter.mp hk).1).1).1,(mem_filter.mp hk).2⟩
  have hh : Real.log (ordinaryPrimeModulus (m • a)) ≤ Real.log B*(m:ℝ)^2 := by
    rw [log_ordinaryPrimeModulus]
    change (∑ k ∈ S, (⌊x k⌋₊ : ℝ)*vonMangoldt k) ≤ _
    rw [← sum_subset (filter_subset _ _) hs]
    calc _ ≤ ∑ k ∈ T, M*vonMangoldt k := sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_right (hx k (mem_filter.mp hk).1) vonMangoldt_nonneg
      _ ≤ M*W := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ hM
        exact sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => vonMangoldt_nonneg)
      _ ≤ _ := (show M*W = 16*A*W*(m:ℝ)^2 by unfold M; ring).le.trans
        (mul_le_mul_of_nonneg_right hlog (sq_nonneg _))
  have hp : 0 < ordinaryPrimeModulus (m • a) := prod_pos fun k _ => pow_pos (contactBase_pos k) _
  have hp' : 0 < B^(m^2) := pow_pos hB _
  have he : Real.log (ordinaryPrimeModulus (m • a)) ≤ Real.log ((B^(m^2) : ℕ):ℝ) := by
    rw [Nat.cast_pow,Real.log_pow,Nat.cast_pow,mul_comm _ (Real.log B)]
    exact hh
  exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hp')).mp he

/-- The ordinary-prime comparison holds throughout the square-root range
with no assumption on the zeta zeros. -/
theorem small_multiplicity_ordinary_generator : ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧
    ∀ {n m : ℕ}, 0 < n → C*(m:ℝ)^2 ≤ n →
      ordinaryPrimeGenerator (m • successorSquareTriple n) ≤ (B:ℚ)^(m^2) := by
  obtain ⟨C,hC,B,hB,h⟩ := small_multiplicity_ordinary_modulus
  exact ⟨C,hC,B,hB,fun {n m} hn hm => (ordinaryPrimeGenerator_le_modulus _).trans
    (by exact_mod_cast h hn hm)⟩

#print axioms ordinary_modulus_quartic
#print axioms small_multiplicity_ordinary_generator
#print axioms positive_successorSquare_contacts_at_small_multiplicity
#print axioms small_multiplicity_ordinary_modulus

end GaloisForLFunctions.CountingHolography.Sections
