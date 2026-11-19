import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature
import GaloisForLFunctions.MatomakiRadziwill.LiouvilleShortSums
import GaloisForLFunctions.«twin-prime».AffineSquarefreeTransfer
import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange

/-!
# Bounded-primitive approximation of coprime Möbius rows

A fixed coprime Möbius row can be approximated in mean absolute error
by a sequence with uniformly bounded partial sums. Consequently sums on
any disjoint family of long cofactor intervals are simultaneously small
in total absolute value. The endpoints can depend on the signs.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev pref (f : ℕ → ℝ) (X : ℕ) := ∑ n ∈ Icc 1 X,f n

/-- Approximation in prefix mean absolute error by a row with bounded
partial sums. The constant absorbs the finite initial segment. -/
def admitsBoundedPrimitiveApproximation (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ g : ℕ → ℝ, ∃ K : ℝ,0 ≤ K ∧ ∀ X : ℕ,
    |pref g X| ≤ K ∧ pref (fun n => |f n-g n|) X ≤ ε*X+K

private theorem approx_zero : admitsBoundedPrimitiveApproximation (fun _ => 0) := by
  intro ε hε
  exact ⟨fun _ => 0,0,le_rfl,fun X => by simp [pref,mul_nonneg hε.le (Nat.cast_nonneg X)]⟩

private theorem approx_add {f v : ℕ → ℝ} (hf : admitsBoundedPrimitiveApproximation f)
    (hv : admitsBoundedPrimitiveApproximation v) : admitsBoundedPrimitiveApproximation (fun n => f n+v n) := by
  intro ε hε
  obtain ⟨g,K,hK,hg⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨u,B,hB,hu⟩ := hv (ε/2) (half_pos hε)
  refine ⟨fun n => g n+u n,K+B,add_nonneg hK hB,fun X => ⟨?_,?_⟩⟩
  · simpa only [pref,sum_add_distrib] using (abs_add_le (pref g X) (pref u X)).trans (add_le_add (hg X).1 (hu X).1)
  · have hh (n : ℕ) : |(f n+v n)-(g n+u n)| ≤ |f n-g n|+|v n-u n| := by
      rw [show (f n+v n)-(g n+u n)=(f n-g n)+(v n-u n) by ring]
      exact abs_add_le _ _
    apply (sum_le_sum (fun n _ => hh n)).trans
    rw [sum_add_distrib]
    linarith only [(hg X).2,(hu X).2]

private theorem approx_scale {f : ℕ → ℝ} (hf : admitsBoundedPrimitiveApproximation f) (a : ℝ) :
    admitsBoundedPrimitiveApproximation (fun n => a*f n) := by
  by_cases z : a=0
  · simpa [z] using approx_zero
  intro ε hε
  obtain ⟨g,K,hK,hg⟩ := hf (ε/|a|) (div_pos hε (abs_pos.mpr z))
  refine ⟨fun n => a*g n,|a| * K,mul_nonneg (abs_nonneg _) hK,fun X => ⟨?_,?_⟩⟩
  · simpa only [pref,←mul_sum,abs_mul] using mul_le_mul_of_nonneg_left (hg X).1 (abs_nonneg a)
  · simp only [pref,←mul_sub,abs_mul,←mul_sum]
    apply (mul_le_mul_of_nonneg_left (hg X).2 (abs_nonneg a)).trans_eq
    field_simp [(abs_pos.mpr z).ne']

private theorem approx_sum {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ S,admitsBoundedPrimitiveApproximation (f i)) :
    admitsBoundedPrimitiveApproximation (fun n => ∑ i ∈ S,f i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [sum_empty] using approx_zero
  | @insert i S hi ih =>
    simp only [sum_insert hi]
    exact approx_add (hf i (mem_insert_self ..)) (ih (fun j hj => hf j (mem_insert_of_mem hj)))

private def dilate (d : ℕ) (f : ℕ → ℝ) (n : ℕ) := if d ∣ n then f (n/d) else 0

private theorem pref_dilate {d : ℕ} (hd : 0<d) (f : ℕ → ℝ) (X : ℕ) :
    pref (dilate d f) X=pref f (X/d) := by
  simp only [pref,dilate,←sum_filter,RHTower.sum_Icc_dvd_reindex d X hd,Nat.mul_div_cancel_left _ hd]

private theorem approx_dilate {f : ℕ → ℝ} (hf : admitsBoundedPrimitiveApproximation f) {d : ℕ} (hd : 0<d) :
    admitsBoundedPrimitiveApproximation (dilate d f) := by
  intro ε hε
  obtain ⟨g,K,hK,hg⟩ := hf ε hε
  refine ⟨dilate d g,K,hK,fun X => ⟨by rw [pref_dilate hd]; exact (hg _).1,?_⟩⟩
  have eq (n : ℕ) : |dilate d f n-dilate d g n|=dilate d (fun k => |f k-g k|) n := by
    by_cases h : d ∣ n <;> simp [dilate,h]
  simp_rw [eq]
  rw [pref_dilate hd]
  exact (hg _).2.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Nat.div_le_self X d)) hε.le) K)

private abbrev lam (n : ℕ) := (liouville n:ℝ)

private theorem lam_abs (n : ℕ) : |lam n| ≤ 1 := by
  by_cases h : n=0
  · simp [lam,h]
  · simp [lam,liouville_apply h,abs_pow]

private theorem bounded_sum (f : ℕ → ℝ) (hf : ∀ n,|f n| ≤ 1) (S : Finset ℕ) :
    |∑ n ∈ S,f n| ≤ S.card := by
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun n _ => hf n)).trans_eq (by simp))

private theorem shift_sum (f : ℕ → ℝ) (a N : ℕ) :
    (∑ n ∈ Icc 1 N,f (a+n))=pref f (a+N)-pref f a := by
  induction N with
  | zero => simp [pref]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega),ih,Nat.add_succ]
    unfold pref
    rw [sum_Icc_succ_top (by omega : 1 ≤ a+N+1)]
    ring

private def forwardMean (f : ℕ → ℝ) (h n : ℕ) := (∑ i ∈ Icc 1 h,f (n+i))/(h:ℝ)

private theorem forwardMean_primitive (f : ℕ → ℝ) (hf : ∀ n,|f n| ≤ 1) {h : ℕ} (hh : 0<h) (X : ℕ) :
    |pref (fun n => f n-forwardMean f h n) X| ≤ 2*h := by
  have hh' : (0:ℝ)<h := Nat.cast_pos.mpr hh
  have scale (n : ℕ) : f n-forwardMean f h n=(∑ i ∈ Icc 1 h,(f n-f (n+i)))/(h:ℝ) := by
    rw [forwardMean,sum_sub_distrib]; simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
    field_simp
  have single (i : ℕ) (hi : i ∈ Icc 1 h) : |∑ n ∈ Icc 1 X,(f n-f (n+i))| ≤ 2*h := by
    have a := shift_sum f i X
    have b := shift_sum f X i
    rw [add_comm i X] at a
    have eq : (∑ n ∈ Icc 1 X,(f n-f (n+i)))=pref f i-∑ n ∈ Icc 1 i,f (X+n) := by
      rw [sum_sub_distrib,b]; simp_rw [add_comm _ i]; rw [a]; ring
    rw [eq]
    apply (abs_sub ..).trans
    have h1 := bounded_sum f hf (Icc 1 i)
    have h2 := bounded_sum (fun n => f (X+n)) (fun n => hf _) (Icc 1 i)
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at h1 h2
    have hle := (Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hi).2
    linarith only [h1,h2,hle]
  unfold pref
  simp_rw [scale]
  rw [←sum_div,sum_comm,abs_div,abs_of_pos hh',div_le_iff₀ hh']
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum single).trans_eq ?_)
  simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; ring

private theorem dyadic_to_prefix (e : ℕ → ℝ) (he : ∀ n,0 ≤ e n) {δ : ℝ} (hδ : 0<δ)
    {N : ℕ} (box : ∀ X,N ≤ X → ∑ n ∈ Ico X (2*X),e n ≤ (δ/2)*X) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ X,pref e X ≤ δ*X+B := by
  let B := pref e (2*N+2)
  have hB : 0 ≤ B := sum_nonneg (fun n _ => he n)
  refine ⟨B,hB,?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases small : X ≤ 2*N+2
    · apply (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl small) (fun n _ _ => he n)).trans
      linarith only [mul_nonneg hδ.le (Nat.cast_nonneg X)]
    let m := X/2
    have hm : m<X := Nat.div_lt_self (by omega) (by decide)
    have mN : N ≤ m+1 := by dsimp only [m]; omega
    have sub : Ioc m X ⊆ Ico (m+1) (2*(m+1)) := by
      intro n hn; obtain ⟨ha,hb⟩ := mem_Ioc.mp hn; apply mem_Ico.mpr
      dsimp only [m] at *; omega
    have inc := (sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => he n)).trans (box _ mN)
    have hsum := sum_Ioc_consecutive e (Nat.zero_le m) hm.le
    have transI (t : ℕ) : Ioc 0 t=Icc 1 t := rfl
    rw [transI,transI] at hsum
    have frac : (m:ℝ)+((m:ℝ)+1)/2 ≤ X := by
      have h1 : 3*m+1 ≤ 2*X := by dsimp only [m] at *; omega
      have h2 : (3:ℝ)*m+1 ≤ 2*X := by exact_mod_cast h1
      linarith only [h2]
    have total := mul_le_mul_of_nonneg_left frac hδ.le
    change pref e m+_ = pref e X at hsum
    push_cast at inc total
    linarith only [inc,hsum,ih m hm,total]

private theorem forwardMean_mean (δ : ℝ) (hδ : 0<δ) :
    ∃ h : ℕ,0<h ∧ ∃ B : ℝ,0 ≤ B ∧ ∀ X,pref (fun n => |forwardMean lam h n|) X ≤ δ*X+B := by
  let b := δ/4
  have hb : 0<b := by positivity
  obtain ⟨h₀,hr⟩ := MatomakiRadziwill.exists_short_sum_mean_square_liouville_le (sq_pos_of_pos hb)
  let h := h₀+1
  have hh : 0<h := Nat.succ_pos _
  obtain ⟨N,hn⟩ := hr h (Nat.le_succ _)
  refine ⟨h,hh,dyadic_to_prefix _ (fun n => abs_nonneg _) hδ (N := N) ?_⟩
  intro X hX
  let a := forwardMean lam h
  have hp : (0:ℝ)<h := Nat.cast_pos.mpr hh
  have same (t : ℕ) : ‖∑ n ∈ Ioc t (t+h),(liouville n:ℂ)‖=|(∑ i ∈ Icc 1 h,lam (t+i))| := by
    have hI := sum_Ioc_consecutive lam (Nat.zero_le t) (Nat.le_add_right t h)
    change pref lam t+_ = pref lam (t+h) at hI
    rw [shift_sum]
    have realEq : (∑ n ∈ Ioc t (t+h),(liouville n:ℂ))=((∑ n ∈ Ioc t (t+h),lam n):ℝ) := by
      push_cast; rfl
    rw [realEq,Complex.norm_real,Real.norm_eq_abs]; congr 1; linarith only [hI]
  have hsq := hn X hX
  simp_rw [same,sq_abs] at hsq
  have sq (t : ℕ) : (∑ i ∈ Icc 1 h,lam (t+i))^2=a t^2*(h:ℝ)^2 := by
    dsimp only [a,forwardMean]; field_simp
  simp_rw [sq] at hsq
  rw [←sum_mul] at hsq
  have H : ∑ k ∈ range X,a (X+k)^2 ≤ b^2*X :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).1 (hsq.trans_eq (by ring))
  have each (k : ℕ) : 2*b*|a (X+k)| ≤ a (X+k)^2+b^2 := by
    nlinarith only [sq_nonneg (|a (X+k)|-b),sq_abs (a (X+k))]
  have hsum := sum_le_sum (s := range X) (fun k _ => each k)
  rw [←mul_sum,sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hsum
  have fin : ∑ k ∈ range X,|a (X+k)| ≤ b*X := by
    apply (mul_le_mul_iff_right₀ (show 0<2*b by positivity)).1
    linarith only [hsum,H]
  rw [sum_Ico_eq_sum_range]
  have len : 2*X-X=X := by omega
  rw [len]
  simpa only [add_comm X] using fin.trans (mul_le_mul_of_nonneg_right
    (by dsimp only [b]; linarith only [hδ] : b ≤ δ/2) (Nat.cast_nonneg X))

/-- The fixed-window mean square for Liouville gives approximation in
mean absolute error by sequences whose partial sums are bounded. -/
theorem liouville_admits_bounded_primitive_approximation :
    admitsBoundedPrimitiveApproximation (fun n => (liouville n:ℝ)) := by
  intro ε hε
  obtain ⟨h,hh,B,hB,he⟩ := forwardMean_mean ε hε
  refine ⟨fun n => lam n-forwardMean lam h n,2*h+B,by positivity,fun X => ⟨?_,?_⟩⟩
  · exact (forwardMean_primitive lam lam_abs hh X).trans (by linarith only [hB])
  · simp only [sub_sub_cancel]
    exact (he X).trans (by linarith only [Nat.cast_nonneg (α := ℝ) h])

private theorem lam_divisibility (l : ℕ) (hl : 0<l) :
    admitsBoundedPrimitiveApproximation (fun n => if l ∣ n then lam n else 0) := by
  have eq : (fun n => if l ∣ n then lam n else 0)=(fun n => lam l*dilate l lam n) := by
    funext n
    by_cases hn : l ∣ n
    · rw [if_pos hn,dilate,if_pos hn]
      obtain ⟨k,rfl⟩ := hn
      simp [lam,liouville_apply_mul,Nat.mul_div_cancel_left _ hl]
    · simp [dilate,hn]
  rw [eq]
  exact approx_scale (approx_dilate liouville_admits_bounded_primitive_approximation hl) _

private theorem coprime_flag {Q : ℕ} (hQ : 0<Q) (n : ℕ) :
    (∑ e ∈ Q.divisors,(if e ∣ n then (μ e:ℝ) else 0))=if Q.Coprime n then 1 else 0 := by
  have eq : Q.divisors.filter (· ∣ n)=(Q.gcd n).divisors := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,Nat.gcd_ne_zero_left hQ.ne'⟩,
      fun h => ⟨⟨h.1.1,hQ.ne'⟩,h.1.2⟩⟩
  rw [←sum_filter,eq,RHTower.sum_divisors_moebiusCast (Nat.gcd_ne_zero_left hQ.ne')]
  change (1:ArithmeticFunction ℝ) (Q.gcd n)=if Q.gcd n=1 then 1 else 0
  exact ArithmeticFunction.one_apply

private def approxRow (Q D n : ℕ) : ℝ :=
  if Q.Coprime n then TwinPrime.AffineSquarefree.approx D n else 0

private theorem approxRow_admits {Q : ℕ} (hQ : 0<Q) (D : ℕ) :
    admitsBoundedPrimitiveApproximation (approxRow Q D) := by
  classical
  let t := fun (d e n : ℕ) => ((μ d:ℝ)*(μ e:ℝ))*
    (if (d*d).lcm e ∣ n then lam n else 0)
  have ez : approxRow Q D=fun n => ∑ d ∈ Icc 1 D,∑ e ∈ Q.divisors,t d e n := by
    funext n
    have term (d e : ℕ) : t d e n=lam n*(if d*d ∣ n then (μ d:ℝ) else 0)*
        (if e ∣ n then (μ e:ℝ) else 0) := by
      by_cases hd : d*d ∣ n <;> by_cases he : e ∣ n <;> simp [t,Nat.lcm_dvd_iff,hd,he]
      ring
    simp_rw [term,←mul_sum]
    rw [coprime_flag hQ,←sum_mul,←mul_sum,←sum_filter]
    by_cases h : Q.Coprime n <;> simp [approxRow,TwinPrime.AffineSquarefree.approx,lam,h]
  rw [ez]
  apply approx_sum
  intro d hd
  apply approx_sum
  intro e he
  exact approx_scale (lam_divisibility _ (Nat.lcm_pos (Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hd).1)
    (Nat.pos_of_mem_divisors he))) _

/-- Every fixed coprime Möbius row is a prefix-mean limit of sequences
with bounded primitives. The approximants have no analytic input
depending on the test intervals. -/
theorem coprime_moebius_admits_bounded_primitive_approximation {Q : ℕ} (hQ : 0<Q) :
    admitsBoundedPrimitiveApproximation (coprimeMoebiusIndicator Q) := by
  intro ε hε
  let δ := ε/4
  have hδ : 0<δ := by positivity
  obtain ⟨d,hd⟩ := exists_nat_gt (1/δ)
  have hd' : 0<d := Nat.cast_pos.mp ((one_div_pos.mpr hδ).trans hd)
  let D : ℕ+ := ⟨d,hd'⟩
  let row : TwinPrime.AffineSquarefree.Row := ⟨1,0,by simp⟩
  obtain ⟨g,K,hK,hg⟩ := approxRow_admits hQ d δ hδ
  let B := K+1/δ
  have hB : K ≤ B := le_add_of_nonneg_right (one_div_pos.mpr hδ).le
  refine ⟨g,B,hK.trans hB,fun X => ⟨(hg X).1.trans hB,?_⟩⟩
  have tail := TwinPrime.AffineSquarefree.sum_abs_moebius_sub_approx_le row X D
  change (∑ t ∈ Icc 1 X,|(μ (1*t+0):ℝ)-TwinPrime.AffineSquarefree.approx d (1*t+0)|) ≤
    (X:ℝ)/d+(Nat.sqrt (1*X+0):ℝ) at tail
  simp only [one_mul,add_zero] at tail
  have cut : pref (fun n => |coprimeMoebiusIndicator Q n-approxRow Q d n|) X ≤
      (X:ℝ)/d+(Nat.sqrt X:ℝ) := by
    apply le_trans _ tail
    apply sum_le_sum
    intro n _
    change |coprimeMoebiusIndicator Q n-approxRow Q d n| ≤ |(μ n:ℝ)-TwinPrime.AffineSquarefree.approx d n|
    by_cases hn : Q.Coprime n
    · simp only [approxRow,coprimeMoebiusIndicator,if_pos hn,le_refl]
    · simp only [approxRow,coprimeMoebiusIndicator,if_neg hn,sub_self,abs_zero,abs_nonneg]
  have inv : 1/(d:ℝ) ≤ δ := (div_le_iff₀ (Nat.cast_pos.mpr hd')).2 (by
    linarith only [(div_lt_iff₀ hδ).1 hd])
  have cost := mul_le_mul_of_nonneg_left inv (Nat.cast_nonneg X)
  have sr : ((Nat.sqrt X:ℕ):ℝ)^2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have sq := mul_le_mul_of_nonneg_left sr (sq_nonneg δ)
  have sq' := sq_nonneg (δ*(Nat.sqrt X:ℝ)-1)
  have sqrtCost : (Nat.sqrt X:ℝ) ≤ δ*X+1/δ := by
    have nonneg := mul_nonneg hδ.le (Nat.cast_nonneg (Nat.sqrt X): (0:ℝ) ≤ Nat.sqrt X)
    have he : δ*(Nat.sqrt X:ℝ) ≤ δ^2*X+1 := by nlinarith only [sq,sq',nonneg]
    apply (mul_le_mul_iff_right₀ hδ).1
    rw [mul_add,one_div,mul_inv_cancel₀ hδ.ne']
    linarith only [he]
  have triangle (n : ℕ) : |coprimeMoebiusIndicator Q n-g n| ≤
      |coprimeMoebiusIndicator Q n-approxRow Q d n|+|approxRow Q d n-g n| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (coprimeMoebiusIndicator Q n-approxRow Q d n)
      (approxRow Q d n-g n)
  apply (sum_le_sum (fun n _ => triangle n)).trans
  rw [sum_add_distrib]
  have err := (hg X).2
  change _ ≤ ε*X+(K+1/δ)
  rw [div_eq_mul_inv] at cut
  simp only [one_div] at cost
  have hx := mul_nonneg hδ.le (Nat.cast_nonneg X)
  dsimp only [δ] at err cost sqrtCost hx ⊢
  linarith only [cut,cost,sqrtCost,err,hx]

/-- A common error budget for every disjoint choice of sharp intervals.
The endpoints may be selected after seeing all the Möbius signs. -/
theorem total_coprime_charge_on_disjoint_intervals {Q : ℕ} (hQ : 0<Q) {δ : ℝ} (hδ : 0<δ) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ {ι : Type} (S : Finset ι) (a b : ι → ℕ) (X : ℕ),
      (∀ i ∈ S,a i ≤ b i ∧ b i ≤ X) →
      (∀ i ∈ S,∀ j ∈ S,i ≠ j → Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
      ∑ i ∈ S, |∑ n ∈ Ioc (a i) (b i),coprimeMoebiusIndicator Q n| ≤
        δ*X+K*(2*S.card+1) := by
  classical
  obtain ⟨g,K,hK,hg⟩ := coprime_moebius_admits_bounded_primitive_approximation hQ δ hδ
  refine ⟨K,hK,?_⟩
  intro ι S a b X ends separate
  let I := fun i => Ioc (a i) (b i)
  let err := fun n => |coprimeMoebiusIndicator Q n-g n|
  have row (i : ι) (hi : i ∈ S) :
      |∑ n ∈ I i,coprimeMoebiusIndicator Q n| ≤ (∑ n ∈ I i,err n)+2*K := by
    have split := sum_Ioc_consecutive g (Nat.zero_le (a i)) (ends i hi).1
    change pref g (a i)+(∑ n ∈ I i,g n)=pref g (b i) at split
    have eq : (∑ n ∈ I i,g n)=pref g (b i)-pref g (a i) := by linarith only [split]
    have bound := (abs_sub (pref g (b i)) (pref g (a i))).trans (add_le_add (hg _).1 (hg _).1)
    have tri := abs_add_le (∑ n ∈ I i,(coprimeMoebiusIndicator Q n-g n)) (∑ n ∈ I i,g n)
    have eqsum : (∑ n ∈ I i,(coprimeMoebiusIndicator Q n-g n))+(∑ n ∈ I i,g n)=
        ∑ n ∈ I i,coprimeMoebiusIndicator Q n := by rw [sum_sub_distrib,sub_add_cancel]
    rw [eqsum] at tri
    have dif := abs_sum_le_sum_abs (fun n => coprimeMoebiusIndicator Q n-g n) (I i)
    rw [eq] at tri
    dsimp only [err]
    linarith only [tri,bound,dif]
  have sub : S.biUnion I ⊆ Icc 1 X := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := mem_biUnion.mp hn
    have lo := (mem_Ioc.mp hn).1
    exact mem_Icc.mpr ⟨by omega,(mem_Ioc.mp hn).2.trans (ends i hi).2⟩
  have joined : (∑ i ∈ S,∑ n ∈ I i,err n) ≤ pref err X := by
    rw [←sum_biUnion (by intro i hi j hj hij; exact separate i hi j hj hij)]
    exact sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => abs_nonneg _)
  apply (sum_le_sum row).trans
  rw [sum_add_distrib,sum_const,nsmul_eq_mul]
  linarith only [joined,(hg X).2]

#print axioms total_coprime_charge_on_disjoint_intervals
#print axioms liouville_admits_bounded_primitive_approximation
#print axioms coprime_moebius_admits_bounded_primitive_approximation

end GaloisForLFunctions.RestrictedFactorizationCalculus
