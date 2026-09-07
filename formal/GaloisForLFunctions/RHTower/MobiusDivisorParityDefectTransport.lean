import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeExtension

/-!
# Quantitative transport of retained Möbius-parity defects

The actual oriented field splits into good and reversed-sign energies. Every
prime merger has gain at most twice their geometric mean. A merger from an
oriented input creates at most its copied packet energy in new sign defects;
the literal adjacent-cutoff law supplies an arithmetic budget for this cost.
-/
noncomputable section
open Finset
namespace RHTower

/-- The literal retained coordinate with its original Möbius parity removed. -/
def mobiusDivisorOrientedFibre (M : ℕ) (P R : Finset ℕ) : ℝ :=
  (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M P R

/-- Squared energy of retained coordinates whose signs reverse their original Möbius parity. -/
def mobiusDivisorParityDefectEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,(max (-mobiusDivisorOrientedFibre M P R) 0)^2

/-- Squared energy of retained coordinates aligned with their original Möbius parity. -/
def mobiusDivisorParityGoodEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,(max (mobiusDivisorOrientedFibre M P R) 0)^2

private theorem parity_square (n : ℕ) : ((-1:ℝ)^n)^2=1 := by
  calc
    _ = ((-1:ℝ)^2)^n := by rw [← pow_mul,← pow_mul,Nat.mul_comm n 2]
    _ = 1 := by norm_num

private theorem positive_negative_square (a : ℝ) : (max a 0)^2+(max (-a) 0)^2=a^2 := by
  by_cases ha : 0 ≤ a
  · simp [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha)]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    simp [max_eq_right ha',max_eq_left (neg_nonneg.mpr ha')]

private theorem opposite_product_le (a b : ℝ) :
    -a*b ≤ max a 0*max (-b) 0+max (-a) 0*max b 0 := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_left ha,max_eq_left hb,max_eq_right (neg_nonpos.mpr ha),
      max_eq_right (neg_nonpos.mpr hb)]
    exact mul_nonneg ha hb
  · have hb' : b ≤ 0 := le_of_not_ge hb
    simp [max_eq_left ha,max_eq_right hb',max_eq_right (neg_nonpos.mpr ha),
      max_eq_left (neg_nonneg.mpr hb')]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    simp [max_eq_right ha',max_eq_left hb,max_eq_left (neg_nonneg.mpr ha'),
      max_eq_right (neg_nonpos.mpr hb)]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hb' : b ≤ 0 := le_of_not_ge hb
    simp [max_eq_right ha',max_eq_right hb',max_eq_left (neg_nonneg.mpr ha'),
      max_eq_left (neg_nonneg.mpr hb')]
    exact mul_nonneg_of_nonpos_of_nonpos ha' hb'

private theorem paired_cauchy {α : Type*} (T : Finset α) (a b c d : α → ℝ) :
    (∑ i ∈ T,(a i*d i+b i*c i)) ≤
      Real.sqrt (∑ i ∈ T,((a i)^2+(b i)^2))*Real.sqrt (∑ i ∈ T,((c i)^2+(d i)^2)) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (T ×ˢ (univ : Finset Bool))
    (fun x => if x.2 then a x.1 else b x.1)
    (fun x => if x.2 then d x.1 else c x.1)
  simpa [sum_product,Fintype.sum_bool,add_comm] using h

private theorem split_prime_labels {M q : ℕ} (hq : q.Prime) (hqM : q<M)
    (f : Finset ℕ → ℝ) :
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,f R) =
      (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset,f R)+
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset,f (insert q R) := by
  have hqU : q ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hqM,hq⟩
  conv_lhs => rw [← insert_erase hqU]
  exact sum_powerset_insert (notMem_erase q _) f

private theorem prime_not_mem_label {M q : ℕ} {R : Finset ℕ}
    (hR : R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset) : q ∉ R := by
  intro h
  have := mem_powerset.mp hR h
  simp at this

/-- Removing Möbius parity preserves the exact coordinate square. -/
theorem mobiusDivisorOrientedFibre_sq (M : ℕ) (P R : Finset ℕ) :
    (mobiusDivisorOrientedFibre M P R)^2=(mobiusDivisorSelectionFibre M P R)^2 := by
  rw [mobiusDivisorOrientedFibre,mul_pow,parity_square,one_mul]

/-- Prime processing subtracts the partner in oriented coordinates. -/
theorem mobiusDivisorOrientedFibre_insert (M : ℕ) (P R : Finset ℕ) (q : ℕ) (hqR : q ∉ R) :
    mobiusDivisorOrientedFibre M (insert q P) R =
      mobiusDivisorOrientedFibre M P R-mobiusDivisorOrientedFibre M P (insert q R) := by
  unfold mobiusDivisorOrientedFibre
  rw [mobiusDivisorSelectionFibre_insert,if_neg hqR,card_insert_of_notMem hqR,pow_succ]
  ring

/-- Good and reversed-sign energies partition the complete literal source energy exactly. -/
theorem mobiusDivisorParityGoodEnergy_add_defect (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorParityGoodEnergy M P+mobiusDivisorParityDefectEnergy M P =
      mobiusDivisorSelectionEnergy M P := by
  unfold mobiusDivisorParityGoodEnergy mobiusDivisorParityDefectEnergy
  rw [← sum_add_distrib]
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,_)=
    ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,(mobiusDivisorSelectionFibre M P R)^2
  exact sum_congr rfl (fun R _ => (positive_negative_square _).trans (mobiusDivisorOrientedFibre_sq M P R))

/-- Reversed-sign energy is nonnegative at every actual retained state. -/
theorem mobiusDivisorParityDefectEnergy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorParityDefectEnergy M P := sum_nonneg (fun _ _ => sq_nonneg _)

/-- Correctly oriented energy is nonnegative at every actual retained state. -/
theorem mobiusDivisorParityGoodEnergy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorParityGoodEnergy M P := sum_nonneg (fun _ _ => sq_nonneg _)

/-- The original arithmetic source has no Möbius-parity defect at any cutoff. -/
theorem mobiusDivisorParityDefectEnergy_empty (M : ℕ) : mobiusDivisorParityDefectEnergy M ∅=0 := by
  apply sum_eq_zero
  intro R hR
  have h : 0 ≤ mobiusDivisorOrientedFibre M ∅ R := mobiusDivisorSelectionFibre_empty_parity_nonneg M R
  simp [max_eq_right (neg_nonpos.mpr h)]

/-- Every prime-merger gain is bounded by twice the geometric mean of actual good and reversed-sign energy. -/
theorem mobiusDivisorSelectionEnergy_insert_le_parity_geometric
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q<M) (hqP : q ∉ P) :
    mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P ≤
      2*Real.sqrt (mobiusDivisorParityGoodEnergy M P)*Real.sqrt (mobiusDivisorParityDefectEnergy M P) := by
  let T := ((mobiusDivisorSelectionPrimes M).erase q).powerset
  let a := fun R => mobiusDivisorOrientedFibre M P R
  let b := fun R => mobiusDivisorOrientedFibre M P (insert q R)
  have hprod (R : Finset ℕ) (hR : R ∈ T) :
      mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R) = -a R*b R := by
    dsimp [a,b,mobiusDivisorOrientedFibre]
    rw [card_insert_of_notMem (prime_not_mem_label hR),pow_succ]
    calc
      _ = ((-1:ℝ)^R.card)^2*(mobiusDivisorSelectionFibre M P R*
        mobiusDivisorSelectionFibre M P (insert q R)) := by rw [parity_square,one_mul]
      _ = _ := by ring
  have hgain := mobiusDivisorSelectionEnergy_insert_cross hq M P hqM hqP
  have hbound : (∑ R ∈ T,mobiusDivisorSelectionFibre M P R*
      mobiusDivisorSelectionFibre M P (insert q R)) ≤
      ∑ R ∈ T,(max (a R) 0*max (-b R) 0+max (-a R) 0*max (b R) 0) := by
    apply sum_le_sum
    intro R hR
    rw [hprod R hR]
    exact opposite_product_le _ _
  have hG : mobiusDivisorParityGoodEnergy M P =
      ∑ R ∈ T,((max (a R) 0)^2+(max (b R) 0)^2) := by
    unfold mobiusDivisorParityGoodEnergy
    rw [split_prime_labels hq hqM,← sum_add_distrib]
  have hD : mobiusDivisorParityDefectEnergy M P =
      ∑ R ∈ T,((max (-a R) 0)^2+(max (-b R) 0)^2) := by
    unfold mobiusDivisorParityDefectEnergy
    rw [split_prime_labels hq hqM,← sum_add_distrib]
  have hcs := paired_cauchy T (fun R => max (a R) 0) (fun R => max (b R) 0)
    (fun R => max (-a R) 0) (fun R => max (-b R) 0)
  rw [← hG,← hD] at hcs
  have hcs' : (∑ R ∈ T,(max (a R) 0*max (-b R) 0+max (-a R) 0*max (b R) 0)) ≤
      Real.sqrt (mobiusDivisorParityGoodEnergy M P)*Real.sqrt (mobiusDivisorParityDefectEnergy M P) := by
    simpa only [mul_comm] using hcs
  linarith only [hgain,hbound,hcs']

/-- A merger from an oriented input creates at most the removed partner packet energy in new sign defects. -/
theorem mobiusDivisorParityDefectEnergy_insert_le_packet
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q<M)
    (hparity : ∀ R : Finset ℕ,0 ≤ mobiusDivisorOrientedFibre M P R) :
    mobiusDivisorParityDefectEnergy M (insert q P) ≤
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset,
        (mobiusDivisorSelectionFibre M P (insert q R))^2 := by
  unfold mobiusDivisorParityDefectEnergy
  rw [split_prime_labels hq hqM]
  have hz : (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset,
      (max (-mobiusDivisorOrientedFibre M (insert q P) (insert q R)) 0)^2)=0 := by
    apply sum_eq_zero
    intro R hR
    simp [mobiusDivisorOrientedFibre,mobiusDivisorSelectionFibre_insert]
  rw [hz,add_zero]
  apply sum_le_sum
  intro R hR
  rw [mobiusDivisorOrientedFibre_insert M P R q (prime_not_mem_label hR),
    ← mobiusDivisorOrientedFibre_sq M P (insert q R)]
  have hle : max (-(mobiusDivisorOrientedFibre M P R-mobiusDivisorOrientedFibre M P (insert q R))) 0 ≤
      mobiusDivisorOrientedFibre M P (insert q R) := by
    apply max_le
    · linarith only [hparity R]
    · exact hparity _
  have hn := le_max_right (-(mobiusDivisorOrientedFibre M P R-
    mobiusDivisorOrientedFibre M P (insert q R))) (0:ℝ)
  have hp := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ mobiusDivisorOrientedFibre M P (insert q R)+
      max (-(mobiusDivisorOrientedFibre M P R-mobiusDivisorOrientedFibre M P (insert q R))) 0 by linarith only [hparity (insert q R),hn])
  nlinarith only [hp]

/-- The exact clipped source controls newly created parity defects by its two smaller retained energies. -/
theorem mobiusDivisorParityDefectEnergy_insert_le_adjacent
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q<M) (hqP : q ∉ P)
    (hparity : ∀ R : Finset ℕ,0 ≤ mobiusDivisorOrientedFibre M P R) :
    mobiusDivisorParityDefectEnergy M (insert q P) ≤
      (q:ℝ)*((1-divisorPrimeClipWeight M q)*mobiusDivisorSelectionEnergy (M/q) P+
        divisorPrimeClipWeight M q*mobiusDivisorSelectionEnergy (M/q+1) P) := by
  exact (mobiusDivisorParityDefectEnergy_insert_le_packet M P hq hqM hparity).trans
    (sum_mobiusDivisorPrimeFibre_sq_le hq M P hqP _ (fun R hR => prime_not_mem_label hR))

/-- Every first prime has an unconditional quadratic adjacent-cutoff budget for its created sign defects. -/
theorem mobiusDivisorParityDefectEnergy_singleton_le_quadratic
    (M : ℕ) {q : ℕ} (hq : q.Prime) (hqM : q<M) :
    mobiusDivisorParityDefectEnergy M {q} ≤ (722:ℝ)*q*
      ((1-divisorPrimeClipWeight M q)*(M/q:ℕ)^2+divisorPrimeClipWeight M q*(M/q+1:ℕ)^2) := by
  have h := mobiusDivisorParityDefectEnergy_insert_le_adjacent M ∅ hq hqM (by simp)
    (fun R => mobiusDivisorSelectionFibre_empty_parity_nonneg M R)
  have hA := sum_mobiusDivisorDilationChannel_sq_le_quadratic (M/q)
  have hB := sum_mobiusDivisorDilationChannel_sq_le_quadratic (M/q+1)
  rw [← mobiusDivisorSelectionEnergy_empty] at hA hB
  have hw0 := divisorPrimeClipWeight_nonneg M q hq.pos
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M q := by
    have := divisorPrimeClipWeight_lt_one M q hq.pos
    linarith
  have hA' := mul_le_mul_of_nonneg_left hA hw1
  have hB' := mul_le_mul_of_nonneg_left hB hw0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA' hB') (Nat.cast_nonneg (α := ℝ) q)
  simp only [insert_empty_eq] at h
  nlinarith only [h,hsum]
/-- After any first prime, the actual second-merger cost is controlled by the created defect and original diagonal. -/
theorem mobiusDivisorSelectionEnergy_second_prime_le_defect
    (M : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M) (hqp : q≠p) :
    mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M {p}+
      2*Real.sqrt (mobiusDivisorSelectionEnergy M ∅)*Real.sqrt (mobiusDivisorParityDefectEnergy M {p}) := by
  have hgain := mobiusDivisorSelectionEnergy_insert_le_parity_geometric M {p} hq hqM (by simpa using hqp)
  have hfirst := mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M ∅ hp hpM (by simp)
    (fun R => mobiusDivisorSelectionFibre_empty_parity_nonneg M R)
  simp only [insert_empty_eq] at hfirst
  have hG : mobiusDivisorParityGoodEnergy M {p} ≤ mobiusDivisorSelectionEnergy M ∅ := by
    have hsplit := mobiusDivisorParityGoodEnergy_add_defect M {p}
    have hnonneg := mobiusDivisorParityDefectEnergy_nonneg M {p}
    linarith only [hsplit,hnonneg,hfirst]
  have hroot := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg (mobiusDivisorParityDefectEnergy M {p}))
  linarith only [hgain,hroot]
end RHTower
