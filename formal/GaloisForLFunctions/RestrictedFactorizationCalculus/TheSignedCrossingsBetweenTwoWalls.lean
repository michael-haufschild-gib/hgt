import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensExponentOnOneSparseFixedSet

/-!
# Signed crossings after cutting a divisor table at two walls

A local divisor d sends its external cofactor times d to the same cofactor
times its partner. Both walls and the sharp observation cutoff therefore
clip a single cofactor interval. The signed charge is a difference of two
coprime Möbius prefixes; the power-bound constant is uniform in all three
cutoffs.
-/

noncomputable section

open Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

open GaloisForLFunctions.QuantitativeFactorizationMatching

/-- Signed prefix on fixed squarefree vertices. -/
def fixedSignedPrefix (F : ℕ → ℕ) (X : ℕ) :=
  ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => F n=n),(μ n:ℝ)

/-- Signed prefix on the lower endpoints of crossing edges. -/
def crossingSignedPrefix (F : ℕ → ℕ) (X : ℕ) :=
  ∑ n ∈ (Icc 1 X).filter (fun n => X<F n),(μ n:ℝ)

/-- At every cutoff the fixed and crossing charges add to the full prefix. -/
theorem fixed_add_crossing (F : ℕ → ℕ) (hF : ∀ n : ℕ,Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    fixedSignedPrefix F X+crossingSignedPrefix F X=coprimeMoebiusSum 1 X := by
  let S := squarefreeOf (Icc 1 X)
  let A := S.filter (fun n => F n=n)
  let B := S.filter (fun n => X<F n)
  let W := (Icc 1 X).filter (fun n => X<F n)
  have he : prefixUnpaid F X=A ∪ B := by
    ext n
    simp only [prefixUnpaid,A,B,S,mem_filter,mem_union]
    tauto
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro n ha hb
    obtain ⟨hs,hx⟩ := mem_filter.mp hb
    rw [(mem_filter.mp ha).2] at hx
    exact (mem_Icc.mp (mem_filter.mp hs).1).2.not_gt hx
  have hsub : B ⊆ W := fun n h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
  have hc : ∑ n ∈ B,(μ n:ℝ)=∑ n ∈ W,(μ n:ℝ) := by
    apply sum_subset hsub
    intro n hn hno
    have hsq : ¬Squarefree n := fun h => hno (mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hn).1,h⟩,(mem_filter.mp hn).2⟩)
    rw [moebius_eq_zero_of_not_squarefree hsq,Int.cast_zero]
  have hh := prefix_switch_balance F hF X
  rw [he,sum_union dis] at hh
  change (∑ n ∈ A,(μ n:ℝ))+(∑ n ∈ W,(μ n:ℝ))=_
  rw [←hc]
  rw [show coprimeMoebiusSum 1 X=∑ n ∈ Icc 1 X,(μ n:ℝ) by
    simp [coprimeMoebiusSum,coprimeMoebiusIndicator]]
  exact_mod_cast hh.symm

/-- Lower endpoints crossing X with both ends retained inside the two walls. -/
def wallCrossings (F : ℕ → ℕ) (L U X : ℕ) := (Ioc L X).filter (fun n => X<F n ∧ F n ≤ U)

/-- Quotient cutoffs of a retained crossing from local divisor d to e. -/
def crossingUpper (U X d e : ℕ) := min (X/d) (U/e)
def crossingLower (L U X d e : ℕ) := min (crossingUpper U X d e) (max (L/d) (X/e))

private theorem gcd_class_prefix {Q d : ℕ} (hd : d ∈ Q.divisors) (b : ℕ) :
    ∑ n ∈ (Icc 1 (b*d)).filter (fun n => n.gcd Q=d),(μ n:ℝ) =
      (μ d:ℝ)*coprimeMoebiusSum Q b := by
  have hh := signed_prefix_of_gcd_classes (Q := Q) (E := {d}) (singleton_subset_iff.mpr hd) (b*d)
  simpa only [mem_singleton,divisorPrefix,sum_singleton,Nat.mul_div_cancel _ (Nat.pos_of_mem_divisors hd)] using hh

/-- Within one local divisor class the three sharp walls select exactly a
difference of two cofactor prefixes, independently of the summand. -/
theorem crossing_divisor_class_eq_sdiff (F : ℕ → ℕ) {Q d : ℕ} (hd : d ∈ Q.divisors)
    (scale : ∀ n : ℕ,F n=(n/n.gcd Q)*F (n.gcd Q)) (L U X : ℕ) :
    let row := fun t : ℕ => (Icc 1 (t*d)).filter (fun n => n.gcd Q=d)
    (wallCrossings F L U X).filter (fun n => n.gcd Q=d)=
      row (crossingUpper U X d (F d)) \ row (crossingLower L U X d (F d)) := by
  let e := F d
  let a := crossingLower L U X d e
  let b := crossingUpper U X d e
  let row (t : ℕ) := (Icc 1 (t*d)).filter (fun n => n.gcd Q=d)
  have hd0 := Nat.pos_of_mem_divisors hd
  have hab : a ≤ b := min_le_left ..
  change _ = row b \ row a
  ext n
  by_cases hg : n.gcd Q=d
  · let c := n/d
    have hn : c*d=n := Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left n Q)
    have hF : F n=c*e := by rw [scale n,hg]
    have lower {u : ℕ} : u<n ↔ u/d<c := by rw [Nat.div_lt_iff_lt_mul hd0,hn]
    have upper {u : ℕ} : n ≤ u ↔ c ≤ u/d := by rw [Nat.le_div_iff_mul_le hd0,hn]
    have rowmem (t : ℕ) : n ∈ row t ↔ 0<n ∧ c ≤ t := by
      simp only [row,mem_filter,mem_Icc,hg,and_true]
      rw [upper,Nat.mul_div_cancel _ hd0]
      rfl
    by_cases he : e=0
    · have hb : b=0 := by simp [b,crossingUpper,he]
      have ha : a=0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp only [wallCrossings,mem_filter,hg,hF,he,Nat.mul_zero,not_lt_zero,false_and,
        and_false,false_and,Finset.mem_sdiff,rowmem,ha,hb]
      tauto
    have he0 := Nat.pos_of_ne_zero he
    have eLow : X<F n ↔ X/e<c := by rw [hF,Nat.div_lt_iff_lt_mul he0]
    have eHi : F n ≤ U ↔ c ≤ U/e := by rw [hF,Nat.le_div_iff_mul_le he0]
    simp only [wallCrossings,mem_filter,mem_Ioc,hg,and_true,lower,upper,eLow,eHi,
      Finset.mem_sdiff,rowmem,Nat.zero_div]
    change (L/d<c ∧ c ≤ X/d) ∧ X/e<c ∧ c ≤ U/e ↔ (0<c ∧ c ≤ b) ∧ ¬(0<c ∧ c ≤ a)
    dsimp only [a,b,crossingLower,crossingUpper]
    constructor
    · rintro ⟨⟨hl,hx⟩,hX,hU⟩
      exact ⟨⟨(Nat.zero_le _).trans_lt hl,le_min hx hU⟩,fun h =>
        (max_lt hl hX).not_ge ((min_le_right ..).trans' h.2)⟩
    · rintro ⟨⟨hpos,hb⟩,hno⟩
      have hgap : max (L/d) (X/e)<c := lt_of_not_ge (fun h => hno ⟨hpos,le_min hb h⟩)
      exact ⟨⟨(le_max_left ..).trans_lt hgap,hb.trans (min_le_left ..)⟩,
        (le_max_right ..).trans_lt hgap,hb.trans (min_le_right ..)⟩
  · simp only [wallCrossings,row,mem_filter,hg,and_false,Finset.mem_sdiff,false_and]

private theorem one_crossing_row (F : ℕ → ℕ) {Q d : ℕ} (hd : d ∈ Q.divisors)
    (scale : ∀ n : ℕ,F n=(n/n.gcd Q)*F (n.gcd Q)) (L U X : ℕ) :
    let a := crossingLower L U X d (F d)
    let b := crossingUpper U X d (F d)
    ∑ n ∈ (wallCrossings F L U X).filter (fun n => n.gcd Q=d),(μ n:ℝ) =
      (μ d:ℝ)*(coprimeMoebiusSum Q b-coprimeMoebiusSum Q a) := by
  let e := F d
  let a := crossingLower L U X d e
  let b := crossingUpper U X d e
  let row (t : ℕ) := (Icc 1 (t*d)).filter (fun n => n.gcd Q=d)
  have hab : a ≤ b := min_le_left ..
  have sub : row a ⊆ row b := fun n hn => mem_filter.mpr ⟨Icc_subset_Icc le_rfl
    (Nat.mul_le_mul_right d hab) (mem_filter.mp hn).1,(mem_filter.mp hn).2⟩
  have heq := crossing_divisor_class_eq_sdiff F hd scale L U X
  change _ = (μ d:ℝ)*(coprimeMoebiusSum Q b-coprimeMoebiusSum Q a)
  rw [heq,sum_sdiff_eq_sub sub]
  change (∑ n ∈ (Icc 1 (b*d)).filter (fun n => n.gcd Q=d),(μ n:ℝ))-
    (∑ n ∈ (Icc 1 (a*d)).filter (fun n => n.gcd Q=d),(μ n:ℝ))=_
  rw [gcd_class_prefix hd,gcd_class_prefix hd,mul_sub]

/-- Exact signed charge at the cutoff X after discarding every pair that
exits the interval (L,U]. This also treats coincident or reversed walls. -/
theorem signed_crossings_between_walls (F : ℕ → ℕ) {Q : ℕ} (hQ : 0<Q)
    (scale : ∀ n : ℕ,F n=(n/n.gcd Q)*F (n.gcd Q)) (L U X : ℕ) :
    ∑ n ∈ wallCrossings F L U X,(μ n:ℝ) =
      ∑ d ∈ Q.divisors,(μ d:ℝ)*(coprimeMoebiusSum Q (crossingUpper U X d (F d))-
        coprimeMoebiusSum Q (crossingLower L U X d (F d))) := by
  have maps : ∀ n ∈ wallCrossings F L U X,n.gcd Q ∈ Q.divisors :=
    fun _ _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,hQ.ne'⟩
  rw [←sum_fiberwise_of_maps_to maps (fun n => (μ n:ℝ))]
  exact sum_congr rfl (fun d hd => one_crossing_row F hd scale L U X)

/-- A positive power bound passes to clipped crossings uniformly in the
two walls and the observation point. Only the fixed divisor table enters
the new constant. -/
theorem uniform_power_of_clipped_crossings (F : ℕ → ℕ) {Q : ℕ} (hQ : Squarefree Q)
    (scale : ∀ n : ℕ,F n=(n/n.gcd Q)*F (n.gcd Q)) {θ : ℝ} (hθ : 0<θ)
    (h : PrefixPower θ (coprimeMoebiusSum 1)) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ L U X : ℕ,
      |∑ n ∈ wallCrossings F L U X,(μ n:ℝ)| ≤ K*(X:ℝ)^θ := by
  obtain ⟨C,hC,hc⟩ := (coprime_prefix_preserves_every_power hQ hθ).2 h
  refine ⟨(Q.divisors.card:ℝ)*(2*C),by positivity,fun L U X => ?_⟩
  rw [signed_crossings_between_walls F (Nat.pos_of_ne_zero hQ.ne_zero) scale]
  have at_cut {a : ℕ} (ha : a ≤ X) : |coprimeMoebiusSum Q a| ≤ C*(X:ℝ)^θ :=
    (hc a).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.cast_le.mpr ha) hθ.le) hC)
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ _d ∈ Q.divisors,2*C*(X:ℝ)^θ := by
         apply sum_le_sum
         intro d _
         let a := crossingLower L U X d (F d)
         let b := crossingUpper U X d (F d)
         have hb : b ≤ X := (min_le_left ..).trans (Nat.div_le_self ..)
         have ha : a ≤ X := (min_le_left ..).trans hb
         have hm : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
         rw [abs_mul]
         apply (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans
         rw [one_mul]
         apply (abs_sub ..).trans
         linarith only [at_cut hb,at_cut ha]
       _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

#print axioms signed_crossings_between_walls
#print axioms uniform_power_of_clipped_crossings

end GaloisForLFunctions.RestrictedFactorizationCalculus
