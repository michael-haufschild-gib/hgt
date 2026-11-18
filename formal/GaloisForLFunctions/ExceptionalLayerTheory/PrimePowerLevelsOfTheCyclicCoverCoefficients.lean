import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeCountInADyadicBinomialGcd
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# Prime-power levels of the Taylor coefficients of a cyclic cover

The numerator of the degree-N coefficient of (1-z)^(-a/q), after multiplying
by q^N N!, is the product of the integers in residue a up to qN. At a level
coprime to q, its multiples traverse complete residue periods and one terminal
segment. The smallest terminal count is the last quotient class.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Integer numerator before projective reduction. -/
def cyclicCoefficientRow (q N a : ℕ) : ℕ :=
  ∏ k ∈ (Icc 1 (q*N)).filter (fun k => k%q=a), k

/-- Number of occurrences of a prime-power level, also defined at arbitrary moduli. -/
def cyclicCoefficientLevel (q N a m : ℕ) : ℕ :=
  ∑ k ∈ (Icc 1 (q*N)).filter (m ∣ ·), if k%q=a then 1 else 0

theorem cyclicCoefficientRow_pos (q N a : ℕ) : 0 < cyclicCoefficientRow q N a :=
  prod_pos fun _ hk => (mem_Icc.mp (mem_filter.mp hk).1).1

/-- Progression product for the rising factorial q^N (a/q)_N. -/
theorem cyclicCoefficientRow_eq_prod {q a : ℕ} (ha : 0 < a) (haq : a < q) (N : ℕ) :
    cyclicCoefficientRow q N a = ∏ j ∈ range N, (q*j+a) := by
  have hq := ha.trans haq
  unfold cyclicCoefficientRow
  apply prod_bij (fun k _ => k/q)
  · intro k hk
    obtain ⟨hkI,hm⟩ := mem_filter.mp hk
    have hlt : k < q*N := lt_of_le_of_ne (mem_Icc.mp hkI).2 (fun e => by
      rw [e,Nat.mul_mod_right] at hm; omega)
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [mul_comm] using hlt)
  · intro x hx y hy he
    have h₁ := Nat.mod_add_div x q
    have h₂ := Nat.mod_add_div y q
    dsimp only at he
    rw [he,(mem_filter.mp hx).2] at h₁
    rw [(mem_filter.mp hy).2] at h₂
    omega
  · intro j hj
    have h := Nat.mul_le_mul_left q (show j+1≤N from mem_range.mp hj)
    rw [Nat.mul_succ] at h
    refine ⟨q*j+a,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩,?_⟩
    · simp [Nat.add_mod,Nat.mod_eq_of_lt haq]
    · rw [Nat.mul_add_div hq,Nat.div_eq_of_lt haq,add_zero]
  · intro k hk
    have h := Nat.mod_add_div k q
    rw [(mem_filter.mp hk).2] at h
    omega

theorem cyclicCoefficientRow_succ {q a : ℕ} (ha : 0 < a) (haq : a < q) (N : ℕ) :
    cyclicCoefficientRow q (N+1) a = cyclicCoefficientRow q N a*(q*N+a) := by
  rw [cyclicCoefficientRow_eq_prod ha haq,prod_range_succ,cyclicCoefficientRow_eq_prod ha haq]

/-- The largest coordinate lies within a factor N+1 of q^N N!, uniformly
in the degree q of the cover. -/
theorem cyclicCoefficientRow_top_bounds {q : ℕ} (hq : 2≤q) (N : ℕ) :
    cyclicCoefficientRow q N (q-1) ≤ q^N*N.factorial ∧
      q^N*N.factorial ≤ (N+1)*cyclicCoefficientRow q N (q-1) := by
  have hq' : 0 < q-1 := by omega
  have hq'' : q-1 < q := by omega
  induction N with
  | zero => simp [cyclicCoefficientRow_eq_prod hq' hq'']
  | succ N ih =>
    rw [cyclicCoefficientRow_succ hq' hq'',pow_succ,Nat.factorial_succ]
    have ha : q*N+(q-1) ≤ q*(N+1) := by rw [Nat.mul_succ]; omega
    constructor
    · exact (Nat.mul_le_mul ih.1 ha).trans_eq (by ring)
    · have he : q*(N+1) = q*N+(q-1)+1 := by rw [Nat.mul_succ]; omega
      have hx : N+1 ≤ q*N+(q-1) := by
        have h := Nat.mul_le_mul_right N hq
        omega
      have hp : (N+1)*(q*(N+1)) ≤ (N+2)*(q*N+(q-1)) := by
        rw [he]; nlinarith only [hx]
      calc
        _ = (q^N*N.factorial)*(q*(N+1)) := by ring
        _ ≤ ((N+1)*cyclicCoefficientRow q N (q-1))*(q*(N+1)) := Nat.mul_le_mul_right _ ih.2
        _ = cyclicCoefficientRow q N (q-1)*((N+1)*(q*(N+1))) := by ring
        _ ≤ _ := (Nat.mul_le_mul_left _ hp).trans_eq (by ring)

private theorem residue_prefix_card {q r : ℕ} (hr : 0 < r) (hrq : r < q) (T : ℕ) :
    ((Icc 1 T).filter (fun k => k%q=r)).card = (T+(q-r))/q := by
  have hq : 0 < q := hr.trans hrq
  rw [← card_range ((T+(q-r))/q)]
  apply card_bij (fun k _ => k/q)
  · intro k hk
    obtain ⟨hkI,hkr⟩ := mem_filter.mp hk
    have ht := (mem_Icc.mp hkI).2
    have hs := Nat.mod_add_div k q
    apply mem_range.mpr
    change k/q+1 ≤ (T+(q-r))/q
    rw [Nat.le_div_iff_mul_le hq,Nat.add_mul,one_mul,mul_comm (k/q) q]
    omega
  · intro x hx y hy he
    obtain ⟨_,hrx⟩ := mem_filter.mp hx
    obtain ⟨_,hry⟩ := mem_filter.mp hy
    have h₁ := Nat.mod_add_div x q
    have h₂ := Nat.mod_add_div y q
    dsimp only at he
    rw [he,hrx] at h₁
    rw [hry] at h₂
    omega
  · intro b hb
    have hle : (b+1)*q ≤ T+(q-r) := (Nat.le_div_iff_mul_le hq).mp (mem_range.mp hb)
    rw [Nat.add_mul,one_mul,mul_comm b q] at hle
    refine ⟨q*b+r,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩,?_⟩
    · simp [Nat.add_mod,Nat.mod_eq_of_lt hrq]
    · rw [Nat.mul_add_div hq,Nat.div_eq_of_lt hrq,add_zero]

private theorem residue_prefix_count {q r : ℕ} (hr : 0 < r) (hrq : r < q) (T : ℕ) :
    (∑ k ∈ Icc 1 T, if k%q=r then 1 else 0) = T/q+(if r≤T%q then 1 else 0) := by
  rw [sum_boole,residue_prefix_card hr hrq,Nat.add_div (by omega : 0 < q)]
  rw [Nat.div_eq_of_lt (by omega : q-r < q),Nat.mod_eq_of_lt (by omega : q-r < q),add_zero]
  split_ifs <;> omega

/-- Labeling a nonzero residue by m*r, the complete periods contribute N/m
and the final period contributes one exactly when it reaches r. -/
theorem cyclicCoefficientLevel_at_multiple {q m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hrq : r < q) (hc : m.Coprime q) (N : ℕ) :
    cyclicCoefficientLevel q N ((m*r)%q) m =
      N/m + (if r≤(q*N/m)%q then 1 else 0) := by
  have hq : 0 < q := hr.trans hrq
  have hmod (n : ℕ) : (m*n)%q=(m*r)%q ↔ n%q=r := by
    change (m*n ≡ m*r [MOD q]) ↔ _
    constructor
    · intro h
      have he : n ≡ r [MOD q] := h.cancel_left_of_coprime hc.symm
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt hrq] using he
    · intro h
      have he : n ≡ r [MOD q] := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hrq] using h
      exact he.mul_left m
  rw [cyclicCoefficientLevel,_root_.RHTower.sum_Icc_filter_dvd_reindex m _ hm]
  simp_rw [hmod]
  rw [residue_prefix_count hr hrq,Nat.div_div_eq_div_mul,mul_comm m q,Nat.mul_div_mul_left N m hq]

private theorem level_last_indicator (q t : ℕ) (hq : 0 < q) :
    q-1 ≤ t%q ↔ q ∣ t+1 := by
  have ht := Nat.mod_lt t hq
  have hs := Nat.mod_add_div t q
  constructor
  · intro h
    refine ⟨t/q+1,?_⟩
    rw [Nat.mul_add,mul_one]
    omega
  · rintro ⟨k,hk⟩
    have hk' : 0 < k := by by_contra! e; have : k=0 := by omega; simp [this] at hk
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk'.ne'
    rw [Nat.mul_succ] at hk
    by_contra! he
    have h₁ : t/q ≤ l := by
      by_contra! h
      have h' := Nat.mul_le_mul_left q (show l+1≤t/q by omega)
      rw [Nat.mul_succ] at h'
      omega
    have h₂ := Nat.mul_le_mul_left q h₁
    omega

/-- The row immediately preceding zero after multiplication by the level
achieves the last-class indicator, including at composite coprime levels. -/
theorem cyclicCoefficientLevel_last {q m : ℕ} (hq : 2≤q) (hm : 0 < m) (hc : m.Coprime q) (N : ℕ) :
    cyclicCoefficientLevel q N ((m*(q-1))%q) m =
      N/m + (if q ∣ q*N/m+1 then 1 else 0) := by
  rw [cyclicCoefficientLevel_at_multiple hm (by omega : 0<q-1) (by omega : q-1<q) hc,
    level_last_indicator q _ (by omega)]

private theorem label_of_coprime {q m a : ℕ} (ha : 0 < a) (haq : a < q)
    (hc : m.Coprime q) :
    ∃ r : ℕ, 0 < r ∧ r < q ∧ (m*r)%q=a := by
  letI : NeZero q := ⟨(ha.trans haq).ne'⟩
  let u := ZMod.unitOfCoprime m hc
  let x := (↑u⁻¹ : ZMod q)*(a : ZMod q)
  have hx : (m:ZMod q)*x=(a:ZMod q) := by
    rw [← ZMod.coe_unitOfCoprime m hc]
    change (u : ZMod q)*((↑u⁻¹ : ZMod q)*(a:ZMod q))=_
    simp [← mul_assoc]
  have he : (m*x.val)%q=a := by
    have he' := congrArg ZMod.val (show (↑(m*x.val) : ZMod q)=(a:ZMod q) by
      rw [Nat.cast_mul,ZMod.natCast_zmod_val]; exact hx)
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt haq] using he'
  refine ⟨x.val,?_,ZMod.val_lt x,he⟩
  by_contra! h
  have hz : x.val=0 := by omega
  simp [hz] at he
  omega

/-- Every nonzero residue contains the common last-class level. The possible
excess at a single coprime modulus is at most one. -/
theorem cyclicCoefficientLevel_bounds {q m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (haq : a < q) (hc : m.Coprime q) (N : ℕ) :
    N/m+(if q ∣ q*N/m+1 then 1 else 0) ≤ cyclicCoefficientLevel q N a m ∧
      cyclicCoefficientLevel q N a m ≤ N/m+1 := by
  obtain ⟨r,hr,hrq,he⟩ := label_of_coprime ha haq hc
  rw [← he,cyclicCoefficientLevel_at_multiple hm hr hrq hc]
  rw [← level_last_indicator q _ (ha.trans haq)]
  split_ifs <;> omega

/-- The row valuation is the sum of its level counts through the largest
prime power that can occur among its factors. -/
theorem factorization_cyclicCoefficientRow {q N a p B : ℕ} (hp : p.Prime)
    (hB : q*N < p^B) :
    (cyclicCoefficientRow q N a).factorization p =
      ∑ e ∈ Ico 1 B, cyclicCoefficientLevel q N a (p^e) := by
  let S := (Icc 1 (q*N)).filter (fun k => k%q=a)
  have hpos {k : ℕ} (hk : k∈S) : 0 < k := (mem_Icc.mp (mem_filter.mp hk).1).1
  rw [cyclicCoefficientRow,Nat.factorization_prod (fun k hk => (hpos hk).ne'),Finsupp.finset_sum_apply]
  calc
    _ = ∑ k ∈ S, ∑ e ∈ Ico 1 B, if p^e ∣ k then 1 else 0 := by
      refine sum_congr rfl fun k hk => ?_
      rw [sum_boole,Nat.factorization_eq_card_pow_dvd_of_lt hp (hpos hk)
        ((mem_Icc.mp (mem_filter.mp hk).1).2.trans_lt hB)]
    _ = ∑ e ∈ Ico 1 B, ∑ k ∈ S, if p^e ∣ k then 1 else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun e _ => ?_
      simp only [S,cyclicCoefficientLevel,sum_boole,filter_filter]
      congr 1
      exact filter_congr fun k _ => and_comm

#print axioms cyclicCoefficientRow_top_bounds
#print axioms cyclicCoefficientLevel_at_multiple
#print axioms cyclicCoefficientLevel_last
#print axioms cyclicCoefficientLevel_bounds
#print axioms factorization_cyclicCoefficientRow

end GaloisForLFunctions.ExceptionalLayerTheory
