import GaloisForLFunctions.RestrictedFactorizationCalculus.BoundedSignedChargeOnCoprimeCofactors
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedCrossingsBetweenTwoWalls

/-!
# Dense restricted exchanges with uniformly bounded signed crossings

Both ends of a divisor exchange have the same cofactor outside the
modulus. A single cofactor test therefore keeps or discards the whole
edge. Every clipped crossing row reads an interval of the retained
cofactor signs. Bounded cofactor prefixes bound all such crossings.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def externalPart (Q n : ℕ) := n/n.gcd Q

private theorem recover_external (Q n : ℕ) : externalPart Q n*n.gcd Q=n :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left n Q)

private theorem external_coprime (Q : ℕ) {n : ℕ} (hs : Squarefree n) : (externalPart Q n).Coprime Q := by
  let c := externalPart Q n
  let d := n.gcd Q
  have he : c*d=n := recover_external Q n
  have hx := (Nat.squarefree_mul_iff.mp ((congrArg Squarefree he).mpr hs)).1
  have hcn : c ∣ n := ⟨d,he.symm⟩
  have hh : c.gcd d=c.gcd Q := by dsimp only [d]; rw [←Nat.gcd_assoc,Nat.gcd_eq_left hcn]
  change c.gcd Q=1
  exact hh.symm.trans hx.gcd_eq_one

private theorem external_dvd (F : ℕ → ℕ) {Q : ℕ}
    (scale : ∀ n,F n=(n/n.gcd Q)*F (n.gcd Q)) {n : ℕ} (hs : Squarefree n) :
    externalPart Q n ∣ externalPart Q (F n) := by
  have hd : externalPart Q n ∣ F n := (scale n) ▸ dvd_mul_right _ _
  have h : (externalPart Q n).Coprime ((F n).gcd Q) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right ..) (external_coprime Q hs)
  apply h.dvd_of_dvd_mul_right
  rwa [recover_external]

/-- Keep precisely the edges whose common external cofactor passes the test. -/
def cofactorThinnedTable (Q : ℕ) (F : ℕ → ℕ) (keep : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact if keep (externalPart Q n) then F n else n

private theorem thin_law (F : ℕ → ℕ) {Q : ℕ}
    (scale : ∀ n,F n=(n/n.gcd Q)*F (n.gcd Q))
    (law : ∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (keep : ℕ → Prop) (n : ℕ) (hs : Squarefree n) :
    cofactorThinnedTable Q F keep (cofactorThinnedTable Q F keep n)=n ∧
      (cofactorThinnedTable Q F keep n=n ∨ GlobalDyadicOneTwoRel n (cofactorThinnedTable Q F keep n)) := by
  classical
  by_cases h : keep (externalPart Q n)
  · obtain ⟨back,legal⟩ := law n hs
    have sy : Squarefree (F n) := legal.elim (fun e => e.symm ▸ hs) (fun e => e.2.1)
    have reverse := external_dvd F scale sy
    rw [back] at reverse
    have eql := Nat.dvd_antisymm (external_dvd F scale hs) reverse
    simp only [cofactorThinnedTable,if_pos h,←eql,back]
    exact ⟨trivial,legal⟩
  · simp [cofactorThinnedTable,h]

private theorem thin_unpaid_count (F : ℕ → ℕ) {Q : ℕ} (hQ : 0<Q) (keep : ℕ → Prop) (X : ℕ) :
    (prefixUnpaid (cofactorThinnedTable Q F keep) X).card ≤
      (prefixUnpaid F X).card+Q.divisors.card*((Icc 1 X).filter (fun n => ¬keep n)).card := by
  classical
  let D := (Icc 1 X).filter (fun n => ¬keep n)
  let images := fun d : ℕ => D.image (· * d)
  have sub : prefixUnpaid (cofactorThinnedTable Q F keep) X ⊆ prefixUnpaid F X ∪ Q.divisors.biUnion images := by
    intro n hn
    obtain ⟨hs,hu⟩ := mem_filter.mp hn
    by_cases h : keep (externalPart Q n)
    · rw [cofactorThinnedTable,if_pos h] at hu; exact mem_union_left _ (mem_filter.mpr ⟨hs,hu⟩)
    have hi := mem_Icc.mp (mem_filter.mp hs).1
    have he := recover_external Q n
    have hp : 0<externalPart Q n := by
      by_contra! ho
      have hz : externalPart Q n=0 := by omega
      rw [hz,zero_mul] at he; omega
    have hd : n.gcd Q ∈ Q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,hQ.ne'⟩
    have hX := (Nat.div_le_self n (n.gcd Q)).trans hi.2
    exact mem_union_right _ (mem_biUnion.mpr ⟨_,hd,mem_image.mpr ⟨externalPart Q n,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hX⟩,h⟩,he⟩⟩)
  apply (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_left _ _))
  apply (card_biUnion_le ..).trans
  exact (sum_le_sum (fun d (_ : d ∈ Q.divisors) => (card_image_le (s := D) (f := (· * d))))).trans_eq (by simp [D])

/-- Ordinary signed prefix on the retained external cofactors. -/
def retainedCofactorPrefix (Q : ℕ) (keep : ℕ → Prop) (b : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Icc 1 b).filter keep,coprimeMoebiusIndicator Q n

private theorem weighted_divisor_row {Q d : ℕ} (hd : d ∈ Q.divisors) (keep : ℕ → Prop) (b : ℕ) :
    (∑ n ∈ (Icc 1 (b*d)).filter (fun n => n.gcd Q=d),
      if keep (externalPart Q n) then (μ n:ℝ) else 0)=(μ d:ℝ)*retainedCofactorPrefix Q keep b := by
  classical
  let f := fun n : ℕ => if n.gcd Q=d then (if keep (n/d) then (μ n:ℝ) else 0) else 0
  have replace : (∑ n ∈ (Icc 1 (b*d)).filter (fun n => n.gcd Q=d),
      if keep (externalPart Q n) then (μ n:ℝ) else 0)=∑ n ∈ (Icc 1 (b*d)).filter (d ∣ ·),f n := by
    rw [sum_filter,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases h : n.gcd Q=d
    · have hdvd : d ∣ n := h ▸ Nat.gcd_dvd_left n Q
      simp [f,h,externalPart,hdvd]
    · by_cases h' : d ∣ n <;> simp [f,h,h']
  have hd0 := Nat.pos_of_mem_divisors hd
  rw [replace,RHTower.sum_Icc_dvd_reindex d (b*d) hd0,Nat.mul_div_cancel _ hd0,retainedCofactorPrefix,sum_filter,mul_sum]
  apply sum_congr rfl
  intro c _
  simp only [f,Nat.mul_div_cancel_left _ hd0]
  by_cases retain : keep c
  · rw [if_pos retain,if_pos retain]
    by_cases hc : Q.Coprime c
    · have hg : (d*c).gcd Q=d := (Nat.Coprime.gcd_mul_right_cancel d hc.symm).trans
        (Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hd))
      rw [if_pos hg,coprimeMoebiusIndicator,if_pos hc,
        isMultiplicative_moebius.map_mul_of_coprime (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hc),
        Int.cast_mul]
    · rw [coprimeMoebiusIndicator,if_neg hc,mul_zero]
      split_ifs with hg
      · have hz : ¬Squarefree (d*c) := by
          intro hsq
          have co := external_coprime Q hsq
          rw [externalPart,hg,Nat.mul_div_cancel_left _ hd0] at co
          exact hc co.symm
        rw [moebius_eq_zero_of_not_squarefree hz,Int.cast_zero]
      · rfl
  · simp [retain]

private theorem masked_wall_eq (F : ℕ → ℕ) (Q : ℕ) (keep : ℕ → Prop) (L U X : ℕ) :
    wallCrossings (cofactorThinnedTable Q F keep) L U X=
      (wallCrossings F L U X).filter (fun n => keep (externalPart Q n)) := by
  ext n
  by_cases hn : keep (externalPart Q n)
  · simp [wallCrossings,cofactorThinnedTable,hn]
  · simp only [wallCrossings,mem_filter,cofactorThinnedTable,mem_Ioc,hn,if_false,and_false,iff_false]
    omega

/-- Exact clipped crossing charge after selecting external cofactors.
The bound is independent of both outer walls and of the cutoff. -/
theorem bounded_walls_of_retained_cofactor_prefix (F : ℕ → ℕ) {Q : ℕ} (hQ : 0<Q)
    (scale : ∀ n,F n=(n/n.gcd Q)*F (n.gcd Q)) (keep : ℕ → Prop) {J : ℝ}
    (bound : ∀ b,|retainedCofactorPrefix Q keep b| ≤ J) (L U X : ℕ) :
    |∑ n ∈ wallCrossings (cofactorThinnedTable Q F keep) L U X,(μ n:ℝ)| ≤ Q.divisors.card*(2*J) := by
  classical
  let A := wallCrossings F L U X
  let f := fun n : ℕ => if keep (externalPart Q n) then (μ n:ℝ) else 0
  have maps : ∀ n ∈ A,n.gcd Q ∈ Q.divisors := fun n _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,hQ.ne'⟩
  rw [masked_wall_eq,sum_filter]
  change |∑ n ∈ A,f n| ≤ _
  rw [←sum_fiberwise_of_maps_to maps f]
  apply (abs_sum_le_sum_abs ..).trans
  have single (d : ℕ) (hd : d ∈ Q.divisors) : |∑ n ∈ A.filter (fun n => n.gcd Q=d),f n| ≤ 2*J := by
    let a := crossingLower L U X d (F d)
    let b := crossingUpper U X d (F d)
    let row := fun t : ℕ => (Icc 1 (t*d)).filter (fun n => n.gcd Q=d)
    have sub : row a ⊆ row b := filter_subset_filter _ (Icc_subset_Icc le_rfl
      (Nat.mul_le_mul_right d (min_le_left ..)))
    have eq : A.filter (fun n => n.gcd Q=d)=row b \ row a := crossing_divisor_class_eq_sdiff F hd scale L U X
    rw [eq,sum_sdiff_eq_sub sub]
    change |(∑ n ∈ row b,if keep (externalPart Q n) then (μ n:ℝ) else 0)-
      (∑ n ∈ row a,if keep (externalPart Q n) then (μ n:ℝ) else 0)| ≤ _
    rw [weighted_divisor_row hd,weighted_divisor_row hd,←mul_sub,abs_mul]
    have hm : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    have hi := (abs_sub (retainedCofactorPrefix Q keep b) (retainedCofactorPrefix Q keep a)).trans (add_le_add (bound b) (bound a))
    exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans ((one_mul _).le.trans (hi.trans_eq (by ring)))
  exact (sum_le_sum single).trans_eq (by simp)

/-- For every tolerance one short restricted matching has small unpaid
fraction and bounded signed crossing charge after any clipping. -/
theorem dense_short_table_with_bounded_signed_walls {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℕ → ℕ, (∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧
      |(F n:ℝ)-n| ≤ ε*n) ∧ (∀ᶠ X : ℕ in atTop, ((prefixUnpaid F X).card:ℝ) ≤ ε*X) ∧
      ∃ K : ℝ,0 ≤ K ∧ ∀ L U X,|∑ n ∈ wallCrossings F L U X,(μ n:ℝ)| ≤ K := by
  classical
  obtain ⟨Q,hs,F,scale,law,_,count,_⟩ := finite_divisor_table_detecting_every_mertens_power (half_pos hε)
  have hQ := Nat.pos_of_ne_zero hs.ne_zero
  let D := (Q.divisors.card:ℝ)
  have hD : 0<D := Nat.cast_pos.mpr (card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hQ.ne'⟩⟩)
  obtain ⟨J,price,removed⟩ := bounded_charge_after_thinning_coprime_cofactors hQ (div_pos (half_pos hε) hD)
  let test := retainSign (coprimeSign Q) (fun _ => J)
  let G := cofactorThinnedTable Q F test
  have move := thin_law F scale (fun n h => ⟨(law n h).1,(law n h).2.1⟩) test
  refine ⟨G,fun n hn => ⟨(move n hn).1,(move n hn).2,?_⟩,?_,D*(2*(J:ℝ)),
    mul_nonneg hD.le (mul_nonneg (by norm_num) (Nat.cast_nonneg J)),?_⟩
  · by_cases h : test (externalPart Q n)
    · simpa [G,cofactorThinnedTable,h] using ((law n hn).2.2.trans
        (mul_le_mul_of_nonneg_right (half_le_self hε.le) (Nat.cast_nonneg n)))
    · simp [G,cofactorThinnedTable,h,mul_nonneg hε.le (Nat.cast_nonneg n)]
  · filter_upwards [count,removed] with X hX hdrop
    have size : ((prefixUnpaid G X).card:ℝ) ≤ (prefixUnpaid F X).card+
        D*(((Icc 1 X).filter (fun n => ¬test n)).card:ℝ) := by
      dsimp only [D,G]
      exact_mod_cast thin_unpaid_count F hQ test X
    have paid := mul_le_mul_of_nonneg_left hdrop hD.le
    have cancel : D*((ε/2)/D*(X:ℝ))=ε/2*X := by field_simp
    rw [cancel] at paid
    linarith only [hX,size,paid]
  · exact bounded_walls_of_retained_cofactor_prefix F hQ scale test price

#print axioms dense_short_table_with_bounded_signed_walls

end GaloisForLFunctions.RestrictedFactorizationCalculus
