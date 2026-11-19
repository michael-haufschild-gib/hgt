import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows
import GaloisForLFunctions.SignedArithmeticCorrespondences.IndependentEnergiesOfInfiniteEndpointSections
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFormOfLogarithmicTailsIsDeterminedByTheRowsOfTheFlatTail
import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture

/-!
# Paired interleaved prime valuation layers

For p-free a and b the only prime-power contact between a and p^h b is
the matched pair a=b. Dilation transports the remaining two poles and jet
with a single reciprocal factor. Two spacings therefore read the signed
coefficient inner product exactly, even when the layers interleave.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt

private theorem free_pos {p a : ℕ} (ha : ¬ p ∣ a) : 0<a := by
  by_contra! h
  exact ha (by simp [show a=0 by omega])

private theorem layer_dvd (p : ℕ) (h : ℕ+) (b : ℕ) : p ∣ p^(h:ℕ)*b :=
  dvd_trans (dvd_pow_self p h.pos.ne') (dvd_mul_right _ _)

/-- Distinct p-free cores have zero contact across positive valuation layers.
A matched core reads exactly the specified weight on the prime power. -/
theorem ratioContact_prime_layers {p : ℕ} (hp : p.Prime) (h : ℕ+) (η : ℕ → ℝ)
    {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    ratioContact (fun n => η n*Λ n) a (p^(h:ℕ)*b) =
      if a=b then η (p^(h:ℕ))*Real.log p else 0 := by
  have hr : ¬ p^(h:ℕ)*b ∣ a := fun h' => ha ((layer_dvd p h b).trans h')
  rw [ratioContact,if_neg hr,add_zero]
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl,if_pos (dvd_mul_left _ _),Nat.mul_div_cancel _ (free_pos ha),
      ArithmeticFunction.vonMangoldt_apply_pow h.pos.ne',ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [if_neg hab]
  split_ifs with hab'
  · have hc := (hp.coprime_iff_not_dvd.mpr ha).symm.pow_right (h:ℕ)
    obtain ⟨c,rfl⟩ := hc.dvd_of_dvd_mul_left hab'
    have hc₀ : c≠0 := fun e => hb (by simp [e])
    have hc₁ : c≠1 := fun e => hab (by simp [e])
    have hc₂ : ¬p ∣ c := fun e => hb (e.trans (dvd_mul_left _ _))
    have hquot : p^(h:ℕ)*(a*c)/a = p^(h:ℕ)*c := by
      rw [Nat.mul_left_comm,Nat.mul_div_cancel_left _ (free_pos ha)]
    rw [hquot,BezoutValuationIncidence.vonMangoldt_mul_eq_zero_of_coprime
      ((hp.coprime_iff_not_dvd.mpr hc₂).pow_left (h:ℕ))
      (Nat.one_lt_pow h.pos.ne' hp.one_lt) (by omega),mul_zero]
  · rfl

/-- Integral graph coefficients assembled at the indicated conductor labels.
Collisions add with their signs. -/
def graphSection (S : Finset ℕ) (f : ℕ → ℕ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ S, if n=f a then u a else 0

private theorem distinct_atoms (W : Finset ℕ) {m n : ℕ} (hm : m∈W) (hn : n∈W) (hne : m≠n)
    (x y : ℝ) :
    formBilin W (fun k => if k=m then x else 0) (fun k => if k=n then y else 0) =
      x*y*(1/(m:ℝ)+1/(n:ℝ)-jetKernel m n-HodgeTheoryOfAFixedPart.contact m n) := by
  have he : m∈W.erase n := mem_erase.mpr ⟨hne,hm⟩
  have hrow (j : ℕ) :
      (∑ i ∈ W.erase j, (if i=m then x else 0)*(if j=n then y else 0)*
        HodgeTheoryOfAFixedPart.pairKernel i j) =
        if j=n then x*y*HodgeTheoryOfAFixedPart.pairKernel m n else 0 := by
    by_cases hj : j=n
    · subst j
      simp only [if_pos rfl,ite_mul,zero_mul,sum_ite_eq',if_pos he]
    · simp only [if_neg hj,mul_zero,zero_mul,sum_const_zero]
  rw [formBilin,combBilin,sum_congr rfl (fun j _ => hrow j)]
  simp only [degOne,degTwo,ite_div,zero_div,ite_mul,zero_mul,
    sum_ite_eq',if_pos hm,if_pos hn,if_neg hne,mul_zero,HodgeTheoryOfAFixedPart.pairKernel]
  ring

/-- Mixed Weil intersection of the two layers, with an arbitrary multiplier
on the prime-power contacts. Ordinary weights give the full comb form. -/
def layerPair (η : ℕ → ℝ) (p : ℕ) (h d : ℕ+) (S : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, u a*v b*(
    1/(((d:ℕ)*a:ℕ):ℝ)+1/(((d:ℕ)*(p^(h:ℕ)*b):ℕ):ℝ)-
    jetKernel ((d:ℕ)*a) ((d:ℕ)*(p^(h:ℕ)*b))-
    ratioContact (fun t => η t*Λ t) ((d:ℕ)*a) ((d:ℕ)*(p^(h:ℕ)*b)))

/-- The ordinary layer pairing retains both pole degrees, all real jets and
all prime contacts on any containing comb window. The diagonal is empty. -/
theorem formBilin_prime_layers (p : ℕ) (h d : ℕ+) (S W : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a)
    (hw : ∀ a ∈ S, (d:ℕ)*a∈W ∧ (d:ℕ)*(p^(h:ℕ)*a)∈W) (u v : ℕ → ℝ) :
    formBilin W (graphSection S (fun a => (d:ℕ)*a) u)
      (graphSection S (fun b => (d:ℕ)*(p^(h:ℕ)*b)) v) = layerPair (fun _ => 1) p h d S u v := by
  unfold graphSection layerPair
  rw [formBilin_sum_left]
  refine sum_congr rfl fun a ha => ?_
  rw [formBilin_sum_right]
  refine sum_congr rfl fun b hb => ?_
  have hne : (d:ℕ)*a ≠ (d:ℕ)*(p^(h:ℕ)*b) := fun e =>
    hs a ha ((Nat.eq_of_mul_eq_mul_left d.pos e).symm ▸ layer_dvd p h b)
  simpa only [one_mul,ratioContact,HodgeTheoryOfAFixedPart.contact] using
    distinct_atoms W (hw a ha).1 (hw b hb).2 hne (u a) (v b)

/-- The geometric part of the mixed entry at unit spacing. -/
def layerGeometry (p : ℕ) (h : ℕ+) (S : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, u a*v b*(1/(a:ℝ)+1/((p^(h:ℕ)*b:ℕ):ℝ)-jetKernel a (p^(h:ℕ)*b))

/-- The exact boundary consists of one reciprocal-spacing term. Every prime
contribution is the weighted inner product on the p-free cores. -/
theorem layerPair_exact {p : ℕ} (hp : p.Prime) (h d : ℕ+) (S : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a) (η u v : ℕ → ℝ) :
    layerPair η p h d S u v = layerGeometry p h S u v/(d:ℝ)-
      (η (p^(h:ℕ))*Real.log p)*(∑ a ∈ S, u a*v a) := by
  let c := η (p^(h:ℕ))*Real.log p
  have e (a b : ℕ) (ha : a∈S) (hb : b∈S) :
      u a*v b*(1/(((d:ℕ)*a:ℕ):ℝ)+1/(((d:ℕ)*(p^(h:ℕ)*b):ℕ):ℝ)-
      jetKernel ((d:ℕ)*a) ((d:ℕ)*(p^(h:ℕ)*b))-
      ratioContact (fun t => η t*Λ t) ((d:ℕ)*a) ((d:ℕ)*(p^(h:ℕ)*b))) =
      u a*v b*(1/(a:ℝ)+1/((p^(h:ℕ)*b:ℕ):ℝ)-jetKernel a (p^(h:ℕ)*b))/(d:ℝ)-
      (if b=a then c*(u a*v a) else 0) := by
    rw [ratioContact_dilate,ratioContact_prime_layers hp h η (hs a ha) (hs b hb),jetKernel_dilate]
    simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
    by_cases he : a=b
    · subst b; simp only [if_pos rfl,c]; ring
    · simp only [if_neg he,if_neg he.symm]; ring
  unfold layerPair layerGeometry
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => e a b ha hb]
  simp only [sum_sub_distrib,sum_ite_eq',sum_div,mul_sum]
  rw [sum_congr rfl (fun a ha => if_pos ha : ∀ a ∈ S, (if a∈S then c*(u a*v a) else 0) = c*(u a*v a))]

/-- Dilation by e divides the defect after removing the matched prime
contact by e, at every starting spacing and independently of the coefficients. -/
theorem layerPair_compose {p : ℕ} (hp : p.Prime) (h d e : ℕ+) (S : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a) (η u v : ℕ → ℝ) :
    let C := (η (p^(h:ℕ))*Real.log p)*(∑ a ∈ S, u a*v a)
    (e:ℝ)*(layerPair η p h (e*d) S u v+C) = layerPair η p h d S u v+C := by
  intro C
  rw [layerPair_exact hp h (e*d) S hs,layerPair_exact hp h d S hs]
  have he : (e:ℝ) ≠ 0 := (Nat.cast_pos.mpr e.pos).ne'
  change (e:ℝ)*(_/(((e:ℕ)*(d:ℕ):ℕ):ℝ)-C+C) = _/(d:ℝ)-C+C
  rw [sub_add_cancel,sub_add_cancel,Nat.cast_mul]
  field_simp

/-- Doubling the spacing and subtracting the original reading extracts
the prime channel exactly at every cutoff. -/
theorem layerPair_two_spacings {p : ℕ} (hp : p.Prime) (h d : ℕ+) (S : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a) (η u v : ℕ → ℝ) :
    2*layerPair η p h (2*d) S u v-layerPair η p h d S u v =
      -(η (p^(h:ℕ))*Real.log p)*(∑ a ∈ S, u a*v a) := by
  have he := layerPair_compose hp h d 2 S hs η u v
  change (2:ℝ)*(_+_) = _+_ at he
  linarith only [he]

private def geomEntry (m n : ℕ) : ℝ := 1/(m:ℝ)+1/(n:ℝ)-jetKernel m n

private theorem geomEntry_comm (m n : ℕ) : geomEntry m n = geomEntry n m := by
  rw [geomEntry,geomEntry,jetKernel_comm m n,add_comm]

/-- Row allowance for the two pole degrees and the real jets in (N,N+M]. -/
def layerWindowPrice (N M : ℕ) : ℝ := (M:ℝ)*(2/N)+harm M+(M:ℝ)/(4*N)

private theorem geom_row {N M n : ℕ} (hN : 0<N) (hn : n∈Ioc N (N+M)) :
    ∑ m ∈ (Ioc N (N+M)).erase n, |geomEntry m n| ≤ layerWindowPrice N M := by
  let W := Ioc N (N+M)
  have hnR : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hdiv {m : ℕ} (hm : m∈W) : 1/(m:ℝ) ≤ 1/(N:ℝ) :=
    one_div_le_one_div_of_le hnR (Nat.cast_le.mpr (mem_Ioc.mp hm).1.le)
  have h (m : ℕ) (hm : m∈W.erase n) : |geomEntry m n| ≤ 2/(N:ℝ)+jetKernel m n := by
    have hz := abs_sub (1/(m:ℝ)+1/(n:ℝ)) (jetKernel m n)
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (jetKernel_nonneg m n)] at hz
    dsimp only [geomEntry]
    linarith only [hz,hdiv (mem_of_mem_erase hm),hdiv hn]
  have hc : ((W.erase n).card:ℝ) ≤ M := by
    have he := card_le_card (erase_subset n W)
    have hw : W.card=M := by simp [W,Nat.card_Ioc]
    exact_mod_cast he.trans_eq hw
  apply (sum_le_sum h).trans
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,layerWindowPrice]
  linarith only [sum_jetKernel_erase_le hN (M := M) (Subset.refl W) hn,
    mul_le_mul_of_nonneg_right hc (by positivity : 0≤2/(N:ℝ))]

private theorem geom_subrow {N M n : ℕ} (hN : 0<N) (hn : n∈Ioc N (N+M))
    (S : Finset ℕ) (g : ℕ → ℕ) (hg : Function.Injective g)
    (hmem : ∀ a ∈ S, g a∈(Ioc N (N+M)).erase n) :
    ∑ a ∈ S, |geomEntry (g a) n| ≤ layerWindowPrice N M := by
  calc _ = ∑ m ∈ S.image g, |geomEntry m n| := (sum_image (fun _ _ _ _ he => hg he)).symm
       _ ≤ ∑ m ∈ (Ioc N (N+M)).erase n, |geomEntry m n| :=
         sum_le_sum_of_subset_of_nonneg (by rintro _ hm; obtain ⟨a,ha,rfl⟩ := mem_image.mp hm; exact hmem a ha)
           (fun _ _ _ => abs_nonneg _)
       _ ≤ _ := geom_row hN hn

private theorem mixed_rows (S : Finset ℕ) (K : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) {B : ℝ}
    (hr : ∀ a ∈ S, ∑ b ∈ S, |K a b| ≤ B) (hc : ∀ b ∈ S, ∑ a ∈ S, |K a b| ≤ B) :
    |∑ a ∈ S, ∑ b ∈ S, u a*v b*K a b| ≤ B*((∑ a ∈ S, u a^2)+(∑ b ∈ S, v b^2))/2 := by
  have entry (a b : ℕ) : |u a*v b*K a b| ≤ (u a^2* |K a b|+v b^2* |K a b|)/2 := by
    have hp : |u a| * |v b| ≤ (u a^2+v b^2)/2 := by
      nlinarith only [sq_nonneg (|u a| - |v b|),sq_abs (u a),sq_abs (v b)]
    simp only [abs_mul]
    calc _ ≤ ((u a^2+v b^2)/2)*|K a b| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
         _ = _ := by ring
  have charge (w : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (h : ∀ a ∈ S, ∑ b ∈ S, |A a b| ≤ B) :
      (∑ a ∈ S, ∑ b ∈ S, w a^2* |A a b|) ≤ B*∑ a ∈ S, w a^2 := by
    rw [mul_sum]
    refine sum_le_sum fun a ha => ?_
    rw [← mul_sum,mul_comm B]
    exact mul_le_mul_of_nonneg_left (h a ha) (sq_nonneg _)
  calc _ ≤ ∑ a ∈ S, ∑ b ∈ S, |u a*v b*K a b| :=
         (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
       _ ≤ ∑ a ∈ S, ∑ b ∈ S, (u a^2* |K a b|+v b^2* |K a b|)/2 :=
         sum_le_sum fun a _ => sum_le_sum fun b _ => entry a b
       _ ≤ _ := by
         simp only [← sum_div,sum_add_distrib]
         rw [sum_comm (f := fun a b => v b^2* |K a b|)]
         rw [mul_add]
         exact div_le_div_of_nonneg_right (add_le_add (charge u K hr) (charge v (fun a b => K b a) hc)) (by norm_num)

/-- Uniform error for the full mixed Weil form at one spacing. The price
depends only on the window and the two individual coefficient masses. -/
theorem layerPair_error {p : ℕ} (hp : p.Prime) (h d : ℕ+) (S : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a) {N M : ℕ} (hN : 0<N)
    (hw : ∀ a ∈ S, a∈Ioc N (N+M) ∧ p^(h:ℕ)*a∈Ioc N (N+M)) (η u v : ℕ → ℝ) :
    |layerPair η p h d S u v+(η (p^(h:ℕ))*Real.log p)*(∑ a ∈ S, u a*v a)| ≤
      (layerWindowPrice N M*((∑ a ∈ S, u a^2)+(∑ b ∈ S, v b^2))/2)/(d:ℝ) := by
  have hd : 0<(d:ℝ) := Nat.cast_pos.mpr d.pos
  rw [layerPair_exact hp h d S hs,sub_add_cancel,abs_div,abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  apply mixed_rows S (fun a b => geomEntry a (p^(h:ℕ)*b)) u v
  · intro a ha
    simp_rw [geomEntry_comm a]
    apply geom_subrow hN (hw a ha).1 S _ (fun _ _ he => Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) he)
    intro b hb
    exact mem_erase.mpr ⟨fun he => hs a ha (he ▸ layer_dvd p h b),(hw b hb).2⟩
  · intro b hb
    apply geom_subrow hN (hw b hb).2 S id Function.injective_id
    intro a ha
    exact mem_erase.mpr ⟨fun he => hs a ha (he.symm ▸ layer_dvd p h b),(hw a ha).1⟩

open Classical in
/-- Multiplier for the Liouville twist on prime powers. -/
def liouvilleContactSign (n : ℕ) : ℝ := if IsSquare n then 1 else -1

theorem liouvilleContactSign_weight (n : ℕ) :
    liouvilleContactSign n*Λ n = SelectiveArithmetic.liouvilleWeight n := by
  by_cases hn : IsSquare n <;> simp [liouvilleContactSign,SelectiveArithmetic.liouvilleWeight,hn]

/-- On matched adjacent layers, the ordinary and Liouville intersections
have strictly opposite signs whenever the explicit row price fits inside
the prime contact. The threshold is independent of the signed coefficients. -/
theorem layerPair_opposite_signs {p : ℕ} (hp : p.Prime) (d : ℕ+) (S : Finset ℕ)
    (hs : ∀ a ∈ S, ¬p ∣ a) {N M : ℕ} (hN : 0<N)
    (hw : ∀ a ∈ S, a∈Ioc N (N+M) ∧ p*a∈Ioc N (N+M))
    (hprice : layerWindowPrice N M < (d:ℝ)*Real.log p) (u : ℕ → ℝ)
    (hu : 0<∑ a ∈ S, u a^2) :
    layerPair (fun _ => 1) p 1 d S u u < 0 ∧ 0 < layerPair liouvilleContactSign p 1 d S u u := by
  have hw' : ∀ a ∈ S, a∈Ioc N (N+M) ∧ p^((1:ℕ+):ℕ)*a∈Ioc N (N+M) := by simpa using hw
  have he (η : ℕ → ℝ) := layerPair_error hp 1 d S hs hN hw' η u u
  have ho := (abs_le.mp (he (fun _ => 1))).2
  have ht := (abs_le.mp (he liouvilleContactSign)).1
  have hsign : liouvilleContactSign p = -1 := if_neg (Nat.prime_iff.mp hp).not_isSquare
  simp only [PNat.val_ofNat,pow_one,one_mul,hsign,neg_one_mul,← sq] at ho ht
  have hd : 0<(d:ℝ) := Nat.cast_pos.mpr d.pos
  have hp' : layerWindowPrice N M/(d:ℝ)<Real.log p := (div_lt_iff₀ hd).mpr (by rwa [mul_comm])
  have hg := mul_lt_mul_of_pos_right hp' hu
  have hn : layerWindowPrice N M*((∑ a ∈ S, u a^2)+(∑ a ∈ S, u a^2))/2/(d:ℝ) =
      (layerWindowPrice N M/(d:ℝ))*(∑ a ∈ S, u a^2) := by ring
  rw [hn] at ho ht
  constructor <;> linarith only [ho,ht,hg]

/-- Odd cores on a growing interval, all retained together with their doubles. -/
def lateOddCores (k : ℕ) : Finset ℕ := (Icc (2*k+3) (4*k+7)).filter (fun a => ¬2 ∣ a)

/-- These two layers genuinely interleave at every cutoff. One spacing threshold
works for every nonzero signed coefficient vector on the entire odd interval. -/
theorem late_odd_layers_opposite_signs (k : ℕ) :
    let S := lateOddCores k
    (∃ a ∈ S, ∃ b ∈ S, a<2*a ∧ 2*a<b ∧ b<2*b) ∧
    ∃ D : ℕ+, ∀ d : ℕ+, D≤d → ∀ u : ℕ → ℝ, 0<∑ a ∈ S, u a^2 →
      layerPair (fun _ => 1) 2 1 d S u u < 0 ∧ 0 < layerPair liouvilleContactSign 2 1 d S u u := by
  intro S
  have hm {a : ℕ} (ha : a∈S) : 2*k+3≤a ∧ a≤4*k+7 := mem_Icc.mp (mem_filter.mp ha).1
  constructor
  · refine ⟨2*k+3,?_,4*k+7,?_,by omega,by omega,by omega⟩ <;>
      simp only [S,lateOddCores,mem_filter,mem_Icc] <;> omega
  · let A := layerWindowPrice (2*k+2) (6*k+12)
    let D : ℕ+ := ⟨⌊A/Real.log 2⌋₊+1,Nat.succ_pos _⟩
    have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨D,fun d hd u hu => ?_⟩
    apply layerPair_opposite_signs Nat.prime_two d S (fun a ha => (mem_filter.mp ha).2)
      (N := 2*k+2) (M := 6*k+12) (by omega) _ _ u hu
    · intro a ha
      have h := hm ha
      simp only [mem_Ioc]
      omega
    · have hlt : A/Real.log 2 < (D:ℝ) := by
        simpa only [D,Nat.cast_succ] using Nat.lt_floor_add_one (A/Real.log 2)
      have hle : (D:ℝ) ≤ d := by exact_mod_cast hd
      exact (div_lt_iff₀ hl).mp (hlt.trans_le hle)

/-- On square-summable sections the two-spacing measurement converges to
the p-free inner product, even with an arbitrary new spacing at each cutoff. -/
theorem completed_layerPair_two_spacings {p : ℕ} (hp : p.Prime) (h : ℕ+) (d : ℕ → ℕ+)
    (η u v : ℕ → ℝ) (hu : Summable (fun n => u n^2)) (hv : Summable (fun n => v n^2)) :
    let S := fun N => (range N).filter (fun a => ¬p ∣ a)
    Tendsto (fun N => 2*layerPair η p h (2*d N) (S N) u v-layerPair η p h (d N) (S N) u v)
      atTop (𝓝 (-(η (p^(h:ℕ))*Real.log p)*(∑' a : ℕ, if ¬p ∣ a then u a*v a else 0))) := by
  intro S
  let F (a : ℕ) := if ¬p ∣ a then u a*v a else 0
  have hs : Summable F := by
    apply Summable.of_norm_bounded ((hu.add hv).div_const 2)
    intro a
    simp only [F,Real.norm_eq_abs,Pi.add_apply]
    split_ifs
    · rw [abs_mul]
      nlinarith only [sq_nonneg (|u a| - |v a|),sq_abs (u a),sq_abs (v a)]
    · rw [abs_zero]; positivity
  apply (hs.hasSum.tendsto_sum_nat.const_mul (-(η (p^(h:ℕ))*Real.log p))).congr
  intro N
  rw [layerPair_two_spacings hp h (d N) (S N) (fun _ ha => (mem_filter.mp ha).2)]
  simp only [S,sum_filter,F]

private def scaledJump (N : ℕ) (x : ℝ) := (roundedJump N x:ℝ)/((N:ℝ)+1)

private theorem scaledJump_abs (N : ℕ) (x : ℝ) : |scaledJump N x| ≤ |x| := by
  have hs : 0<(N:ℝ)+1 := by positivity
  have ht : |((roundedJump N x):ℝ)| = (⌊((N:ℝ)+1)*|x|⌋₊:ℝ) := by
    by_cases hx : x<0 <;> simp [roundedJump,hx]
  rw [scaledJump,abs_div,ht,abs_of_pos hs,div_le_iff₀ hs,mul_comm (|x|) ((N:ℝ)+1)]
  exact Nat.floor_le (mul_nonneg hs.le (abs_nonneg x))

private theorem scaledJump_limit (x : ℝ) : Tendsto (fun N => scaledJump N x) atTop (𝓝 x) := by
  have hs : Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have he := (tendsto_nat_floor_mul_div_atTop (abs_nonneg x)).comp hs
  simp only [Function.comp_def,Nat.cast_succ,mul_comm (|x|)] at he
  by_cases hx : x<0
  · simpa only [scaledJump,roundedJump,if_pos hx,Int.cast_neg,Int.cast_natCast,neg_div,
      abs_of_neg hx,neg_neg] using he.neg
  · simpa only [scaledJump,roundedJump,if_neg hx,Int.cast_natCast,abs_of_nonneg (le_of_not_gt hx)] using he

/-- Both spacings use the same two rounded integer graph families, divided
by the common multiplicity in each variable. Their difference converges
on every square-summable pair, independently of the spacing sequence. -/
theorem integral_exhaustion_of_prime_layers {p : ℕ} (hp : p.Prime) (h : ℕ+) (d : ℕ → ℕ+)
    (η u v : ℕ → ℝ) (hu : Summable (fun n => u n^2)) (hv : Summable (fun n => v n^2)) :
    let S := fun N => (range N).filter (fun a => ¬p ∣ a)
    let U := fun (N a : ℕ) => (roundedJump N (u a):ℝ)/((N:ℝ)+1)
    let V := fun (N a : ℕ) => (roundedJump N (v a):ℝ)/((N:ℝ)+1)
    Tendsto (fun N => 2*layerPair η p h (2*d N) (S N) (U N) (V N)-
      layerPair η p h (d N) (S N) (U N) (V N)) atTop
      (𝓝 (-(η (p^(h:ℕ))*Real.log p)*(∑' a : ℕ, if ¬p ∣ a then u a*v a else 0))) := by
  intro S U V
  let F (N a : ℕ) := if a∈S N then U N a*V N a else 0
  have he (a : ℕ) : Tendsto (fun N => F N a) atTop (𝓝 (if ¬p ∣ a then u a*v a else 0)) := by
    by_cases ha : p ∣ a
    · simpa [F,S,ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · rw [if_pos ha]
      apply ((scaledJump_limit (u a)).mul (scaledJump_limit (v a))).congr'
      filter_upwards [eventually_gt_atTop a] with N hN
      simp only [F,S,mem_filter,mem_range,hN,ha,not_false_eq_true,and_self,if_true,U,V,scaledJump]
  have hdom (N a : ℕ) : ‖F N a‖ ≤ (u a^2+v a^2)/2 := by
    rw [Real.norm_eq_abs]
    by_cases ha : a∈S N
    · rw [F,if_pos ha,abs_mul]
      calc _ ≤ |u a| * |v a| := mul_le_mul (scaledJump_abs N _) (scaledJump_abs N _) (abs_nonneg _) (abs_nonneg _)
           _ ≤ _ := by nlinarith only [sq_nonneg (|u a| - |v a|),sq_abs (u a),sq_abs (v a)]
    · simp only [F,if_neg ha,abs_zero]; positivity
  have hg : Summable (fun a => (u a^2+v a^2)/2) := (hu.add hv).div_const 2
  have ht := tendsto_tsum_of_dominated_convergence hg he (Eventually.of_forall hdom)
  apply (ht.const_mul (-(η (p^(h:ℕ))*Real.log p))).congr
  intro N
  rw [layerPair_two_spacings hp h (d N) (S N) (fun _ ha => (mem_filter.mp ha).2),
    tsum_eq_sum (s := S N) (fun a ha => by simp [F,ha])]
  exact congrArg _ (sum_congr rfl fun a ha => if_pos ha)

#print axioms ratioContact_prime_layers
#print axioms formBilin_prime_layers
#print axioms layerPair_compose
#print axioms layerPair_two_spacings
#print axioms layerPair_error
#print axioms liouvilleContactSign_weight
#print axioms layerPair_opposite_signs
#print axioms late_odd_layers_opposite_signs
#print axioms completed_layerPair_two_spacings
#print axioms integral_exhaustion_of_prime_layers
end GaloisForLFunctions.SignedArithmeticCorrespondences
