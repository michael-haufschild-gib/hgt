import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange
import GaloisForLFunctions.RHTower.CausalMobiusThetaPrimorialInnovation

/-!
# Recovering the Möbius prefix from an increasing prime cutoff

Sift each integer at its own cutoff. On any interval where the cutoff
is constant, its signed sum is a difference of two ordinary coprime
prefixes. At a higher prime the exact deletion recurrence decreases
either the cutoff or the integer argument. The finite Euler product pays
for both children without multiplying their number into the estimate.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- An ordinary prefix on a fixed set: n is tested only at b(n). -/
def siftedPrefix (b : ℕ → ℕ) (X : ℕ) :=
  ∑ n ∈ Icc 1 X,coprimeMoebiusIndicator (primorial (b n)) n

/-- The positive cost of inverting the Euler factors through y
in a sharp prefix power norm. -/
def deletionPrice (s : ℝ) (y : ℕ) :=
  ∏ p ∈ Nat.primesLE y,(1-(1/(p:ℝ))^s)⁻¹

private abbrev row (y n : ℕ) := coprimeMoebiusSum (primorial y) n
private abbrev weight (s : ℝ) (p : ℕ) := (1/(p:ℝ))^s

theorem deletion_weight_lt_one {s : ℝ} (hs : 0<s) {p : ℕ} (hp : Nat.Prime p) :
    (1/(p:ℝ))^s<1 := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one (by positivity) ((div_lt_one (zero_lt_one.trans hp1)).2 hp1) hs

/-- Every Euler deletion factor costs at least one. -/
theorem deletionPrice_one_le {s : ℝ} (hs : 0<s) (y : ℕ) : 1 ≤ deletionPrice s y := by
  apply one_le_prod
  intro p hp
  rw [←one_div]
  exact (one_le_div (sub_pos.mpr (deletion_weight_lt_one hs (Nat.mem_primesLE.mp hp).2))).2
    (sub_le_self _ (Real.rpow_nonneg (by positivity) _))

/-- Only a prime successor introduces a new Euler factor. -/
theorem deletionPrice_succ (s : ℝ) (y : ℕ) :
    deletionPrice s (y+1) = if (y+1).Prime then deletionPrice s y*(1-(1/((y+1:ℕ):ℝ))^s)⁻¹ else deletionPrice s y := by
  unfold deletionPrice Nat.primesLE Nat.primesBelow
  rw [prod_filter,prod_filter,prod_range_succ]
  split_ifs <;> simp_all

private theorem row_step {y : ℕ} (hp : (y+1).Prime) (n : ℕ) :
    row y n = row (y+1) n-row (y+1) (n/(y+1)) := by
  have hnd : ¬y+1 ∣ primorial y := fun h => (Nat.not_succ_le_self y) (hp.dvd_primorial_iff.1 h)
  unfold row
  rw [RHTower.DeletionResidueMartingale.primorial_succ_eq,if_pos hp]
  exact coprimeMoebiusSum_prime_relation hp hnd n

private theorem row_unchanged {y : ℕ} (hp : ¬(y+1).Prime) (n : ℕ) :
    row (y+1) n=row y n := by
  simp only [row,RHTower.DeletionResidueMartingale.primorial_succ_eq,if_neg hp]

private theorem quotient_weight {s : ℝ} (hs : 0<s) (n : ℕ) {p : ℕ} (hp : 0<p) :
    ((n/p:ℕ):ℝ)^s ≤ weight s p*(n:ℝ)^s := by
  have hpos : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hf : ((n/p:ℕ):ℝ) ≤ (1/(p:ℝ))*(n:ℝ) := by
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hpos).2 (by exact_mod_cast Nat.div_mul_le_self n p)
  simpa only [Real.mul_rpow (by positivity : (0:ℝ) ≤ 1/(p:ℝ)) (Nat.cast_nonneg n)] using
    Real.rpow_le_rpow (Nat.cast_nonneg _) hf hs.le

/-- The terminal interval on which a nondecreasing integer cutoff is constant. -/
theorem interval_of_last_cutoff (b : ℕ → ℕ) (hb : Monotone b) (t : ℕ) :
    ∃ l, l ≤ t ∧ (l=0 ∨ l<t ∧ b l<b t) ∧ ∀ n,l<n → n ≤ t → b n=b t := by
  let S := (Icc 1 t).filter fun n => b n<b t
  by_cases h : S.Nonempty
  · let l := S.max' h
    obtain ⟨hi,hl⟩ := mem_filter.mp (max'_mem S h)
    change b l<b t at hl
    have hlt := (mem_Icc.mp hi).2
    refine ⟨l,hlt,Or.inr ⟨lt_of_le_of_ne hlt (fun e => hl.ne (congrArg b e)),hl⟩,?_⟩
    intro n hn hnt
    apply le_antisymm (hb hnt)
    by_contra! hbad
    exact hn.not_ge (le_max' S n (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hnt⟩,hbad⟩))
  · refine ⟨0,Nat.zero_le _,Or.inl rfl,fun n hn ht => le_antisymm (hb ht) ?_⟩
    by_contra! hbad
    exact h ⟨n,mem_filter.mpr ⟨mem_Icc.mpr ⟨hn,ht⟩,hbad⟩⟩

private theorem plateau_difference (b : ℕ → ℕ) {l t y : ℕ} (hl : l ≤ t)
    (hy : ∀ n,l<n → n ≤ t → b n=y) :
    row y t-row y l=siftedPrefix b t-siftedPrefix b l := by
  have sub : Icc 1 l ⊆ Icc 1 t := Icc_subset_Icc le_rfl hl
  unfold row coprimeMoebiusSum siftedPrefix
  rw [←sum_sdiff_eq_sub sub,←sum_sdiff_eq_sub sub]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hi,hout⟩ := mem_sdiff.mp hn
  have h1 := (mem_Icc.mp hi).1
  rw [hy n (lt_of_not_ge (fun h => hout (mem_Icc.mpr ⟨h1,h⟩))) (mem_Icc.mp hi).2]

private def allowance (C : ℝ) (k : ℕ) := 2*C*(k+1)

private theorem allowance_mono {C : ℝ} (hC : 0 ≤ C) {i j : ℕ} (h : i ≤ j) :
    allowance C i ≤ allowance C j := mul_le_mul_of_nonneg_left
  (add_le_add_left (Nat.cast_le.mpr h) _) (by positivity)

/-- A bound for the ordinary prefix on the fixed sifted set gives a uniform
bound on every coprime prefix whose prime cutoff is at least b(n). -/
theorem recovering_above_an_increasing_prime_cutoff (b : ℕ → ℕ) (hb : Monotone b)
    {s C : ℝ} (hs : 0<s) (hC : 0 ≤ C) (h : ∀ n,|siftedPrefix b n| ≤ C*(n:ℝ)^s)
    (n y : ℕ) (hy : b n ≤ y) :
    |coprimeMoebiusSum (primorial y) n| ≤ 2*C*((b n:ℝ)+1)*deletionPrice s y*(n:ℝ)^s := by
  change |row y n| ≤ allowance C (b n)*deletionPrice s y*(n:ℝ)^s
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
    by_cases hz : n=0
    · simp [hz,row,coprimeMoebiusSum,Real.zero_rpow hs.ne']
    have hn := Nat.pos_of_ne_zero hz
    have pow0 (t : ℕ) := Real.rpow_nonneg (Nat.cast_nonneg t) s
    induction y,hy using Nat.le_induction with
    | base =>
      let Y := b n
      obtain ⟨l,hl,early,flat⟩ := interval_of_last_cutoff b hb n
      have id := plateau_difference b hl flat
      have hlpow := Real.rpow_le_rpow (Nat.cast_nonneg l) (Nat.cast_le.mpr hl) hs.le
      have hlA := (h l).trans (mul_le_mul_of_nonneg_left hlpow hC)
      have delta := abs_sub (siftedPrefix b n) (siftedPrefix b l)
      have d : |row Y n-row Y l| ≤ 2*C*(n:ℝ)^s := by rw [id]; linarith only [delta,h n,hlA]
      have E := deletionPrice_one_le hs Y
      have hE := zero_le_one.trans E
      rcases early with rfl | ⟨hln,hjump⟩
      · have z : row Y 0=0 := by simp [row,coprimeMoebiusSum]
        rw [z,sub_zero] at d
        apply d.trans
        apply mul_le_mul_of_nonneg_right _ (pow0 n)
        have ha : 2*C ≤ allowance C (b n) := by
          simpa only [allowance,Nat.cast_zero,zero_add,mul_one] using
            allowance_mono hC (Nat.zero_le (b n))
        exact ha.trans (le_mul_of_one_le_right (by unfold allowance; positivity) E)
      · have hbnd := ih l hln Y (hb hl)
        have hh := hbnd.trans (mul_le_mul_of_nonneg_left hlpow
          (mul_nonneg (by unfold allowance; positivity) hE))
        have hj : allowance C (b l)+2*C ≤ allowance C (b n) := by
          have hc : (b l:ℝ)+1 ≤ b n := by exact_mod_cast hjump
          dsimp only [allowance]
          nlinarith only [mul_nonneg (by positivity : 0 ≤ 2*C) (sub_nonneg.mpr hc)]
        have room := mul_le_mul_of_nonneg_right hj hE
        have ec := le_mul_of_one_le_right (by positivity : 0 ≤ 2*C) E
        have diff : allowance C (b l)*deletionPrice s Y+2*C ≤ allowance C (b n)*deletionPrice s Y := by
          linarith only [room,ec]
        have bound := mul_le_mul_of_nonneg_right diff (pow0 n)
        have tri := abs_add_le (row Y n-row Y l) (row Y l)
        rw [sub_add_cancel] at tri
        linarith only [tri,d,hh,bound]
    | succ y hy prev =>
      by_cases hp : (y+1).Prime
      · let a := allowance C (b n)
        let r := weight s (y+1)
        let E := deletionPrice s (y+1)
        have he : 0 ≤ E := zero_le_one.trans (deletionPrice_one_le hs _)
        have ha : 0 ≤ a := by dsimp [a,allowance]; positivity
        have gap : 0<1-r := sub_pos.mpr (deletion_weight_lt_one hs hp)
        have pay : E*(1-r)=deletionPrice s y := by
          dsimp only [E,r]; rw [deletionPrice_succ,if_pos hp,mul_assoc,inv_mul_cancel₀ gap.ne',mul_one]
        have hsmall := ih (n/(y+1)) (Nat.div_lt_self hn hp.one_lt) (y+1)
          ((hb (Nat.div_le_self ..)).trans (hy.trans (Nat.le_succ _)))
        have cap := allowance_mono hC (hb (Nat.div_le_self n (y+1)))
        have hh := hsmall.trans (mul_le_mul (mul_le_mul_of_nonneg_right cap he)
          (quotient_weight hs n hp.pos) (pow0 _) (mul_nonneg ha he))
        have split : row (y+1) n=row y n+row (y+1) (n/(y+1)) := by linarith only [row_step hp n]
        rw [split]
        apply (abs_add_le ..).trans
        change |row y n|+|row (y+1) (n/(y+1))| ≤ a*E*(n:ℝ)^s
        calc _ ≤ a*deletionPrice s y*(n:ℝ)^s+a*E*(r*(n:ℝ)^s) := add_le_add prev hh
             _ = _ := by rw [←pay]; ring
      · simpa only [row_unchanged hp,deletionPrice_succ s y,if_neg hp] using prev

/-- The cost increases as further primes are deleted. -/
theorem deletionPrice_mono {s : ℝ} (hs : 0<s) : Monotone (deletionPrice s) := by
  apply monotone_nat_of_le_succ
  intro y
  rw [deletionPrice_succ]
  split_ifs with hp
  · apply le_mul_of_one_le_right (zero_le_one.trans (deletionPrice_one_le hs _))
    rw [←one_div]
    exact (one_le_div (sub_pos.mpr (deletion_weight_lt_one hs hp))).2
      (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
  · exact le_rfl

private theorem undo_cutoff {s : ℝ} (hs : 0<s) (X y : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n ≤ X,|row y n| ≤ C*(n:ℝ)^s) :
    |row 0 X| ≤ C*deletionPrice s y*(X:ℝ)^s := by
  induction y generalizing C with
  | zero => simpa [deletionPrice] using h X le_rfl
  | succ y ih =>
    by_cases hp : (y+1).Prime
    · let r := weight s (y+1)
      have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
      have gap : 0<1-r := sub_pos.mpr (deletion_weight_lt_one hs hp)
      have hf : 1+r ≤ (1-r)⁻¹ := by
        rw [←one_div]; apply (le_div_iff₀ gap).2; nlinarith only [sq_nonneg r]
      have hrow (n : ℕ) (hn : n ≤ X) : |row y n| ≤ C*(1+r)*(n:ℝ)^s := by
        rw [row_step hp]
        apply (abs_sub ..).trans
        have small := (h (n/(y+1)) ((Nat.div_le_self ..).trans hn)).trans
          (mul_le_mul_of_nonneg_left (quotient_weight hs n hp.pos) hC)
        calc _ ≤ C*(n:ℝ)^s+C*(r*(n:ℝ)^s) := add_le_add (h n hn) small
             _ = _ := by ring
      have hh := ih (mul_nonneg hC (by positivity)) hrow
      rw [deletionPrice_succ,if_pos hp]
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      calc _ ≤ (C*(1-r)⁻¹)*deletionPrice s y := mul_le_mul_of_nonneg_right
                 (mul_le_mul_of_nonneg_left hf hC) (zero_le_one.trans (deletionPrice_one_le hs _))
           _ = _ := by ring
    · rw [deletionPrice_succ,if_neg hp]
      exact ih hC (fun n hn => by simpa only [row_unchanged hp] using h n hn)

/-- Sharp recovery of the full prefix from the fixed sifted set. No estimate
at a different prime cutoff occurs on the right. -/
theorem full_prefix_from_sifted_prefix (b : ℕ → ℕ) (hb : Monotone b) {s C : ℝ}
    (hs : 0<s) (hC : 0 ≤ C) (h : ∀ n,|siftedPrefix b n| ≤ C*(n:ℝ)^s) (X : ℕ) :
    |coprimeMoebiusSum 1 X| ≤ (2*C*((b X:ℝ)+1))*(deletionPrice s (b X))^2*(X:ℝ)^s := by
  let E := deletionPrice s (b X)
  have he : 0 ≤ E := zero_le_one.trans (deletionPrice_one_le hs _)
  have hrow (n : ℕ) (hn : n ≤ X) : |row (b X) n| ≤ allowance C (b X)*E*(n:ℝ)^s := by
    have hh := recovering_above_an_increasing_prime_cutoff b hb hs hC h n (b X) (hb hn)
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (allowance_mono hC (hb hn)) he) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hallow : 0 ≤ allowance C (b X) := by dsimp only [allowance]; positivity
  have result := undo_cutoff hs X (b X) (mul_nonneg hallow he) hrow
  rw [show row 0 X=coprimeMoebiusSum 1 X by simp [row]] at result
  exact result.trans_eq (by dsimp only [allowance,E]; ring)

private theorem constant_rows {s C : ℝ} (hs : 0<s) (hC : 0 ≤ C)
    (h : ∀ n,|coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s) (t y : ℕ) :
    |row y t| ≤ 2*C*deletionPrice s y*(t:ℝ)^s := by
  let b := fun _ : ℕ => (0:ℕ)
  have hb : Monotone b := fun _ _ _ => le_rfl
  have hz (n : ℕ) : siftedPrefix b n=coprimeMoebiusSum 1 n := by simp [siftedPrefix,b,coprimeMoebiusSum]
  simpa only [b,Nat.cast_zero,zero_add,mul_one] using
    recovering_above_an_increasing_prime_cutoff b hb hs hC (fun n => (hz n).symm ▸ h n) t y (Nat.zero_le _)

/-- Conversely, a full-prefix bound controls the signed prefix of all
integers that pass their own prime cutoff. -/
theorem sifted_prefix_from_full_prefix (b : ℕ → ℕ) (hb : Monotone b) {s C : ℝ}
    (hs : 0<s) (hC : 0 ≤ C) (h : ∀ n,|coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s) (X : ℕ) :
    |siftedPrefix b X| ≤ 4*C*((b X:ℝ)+1)*deletionPrice s (b X)*(X:ℝ)^s := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
    obtain ⟨l,hl,earlier,flat⟩ := interval_of_last_cutoff b hb X
    let V := deletionPrice s (b X)*(X:ℝ)^s
    have hE := zero_le_one.trans (deletionPrice_one_le hs (b X))
    have hx := Real.rpow_nonneg (Nat.cast_nonneg X) s
    have hlx := Real.rpow_le_rpow (Nat.cast_nonneg l) (Nat.cast_le.mpr hl) hs.le
    have hid := plateau_difference b hl flat
    have hr := constant_rows hs hC h X (b X)
    have hlr := (constant_rows hs hC h l (b X)).trans
      (mul_le_mul_of_nonneg_left hlx (mul_nonneg (by positivity) hE))
    have d : |siftedPrefix b X-siftedPrefix b l| ≤ 4*C*V := by
      rw [←hid]
      apply (abs_sub ..).trans
      dsimp only [V]
      linarith only [hr,hlr]
    have previous : |siftedPrefix b l| ≤ (4*C*(b X:ℝ))*V := by
      rcases earlier with rfl | ⟨hlt,hjump⟩
      · have hz : siftedPrefix b 0=0 := by simp [siftedPrefix]
        rw [hz,abs_zero]
        dsimp only [V]
        positivity
      · have hj : (b l:ℝ)+1 ≤ b X := by exact_mod_cast hjump
        have hprev := ih l hlt
        apply hprev.trans
        change _ ≤ (4*C*(b X:ℝ))*(deletionPrice s (b X)*(X:ℝ)^s)
        rw [←mul_assoc]
        apply mul_le_mul _ hlx (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (by positivity) hE)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hj (by positivity))
          (deletionPrice_mono hs (hb hl)) (zero_le_one.trans (deletionPrice_one_le hs _)) (by positivity)
    have tri := abs_add_le (siftedPrefix b X-siftedPrefix b l) (siftedPrefix b l)
    rw [sub_add_cancel] at tri
    dsimp only [V] at d previous
    linarith only [tri,d,previous]

#print axioms recovering_above_an_increasing_prime_cutoff
#print axioms full_prefix_from_sifted_prefix
#print axioms sifted_prefix_from_full_prefix

end GaloisForLFunctions.RestrictedFactorizationCalculus
