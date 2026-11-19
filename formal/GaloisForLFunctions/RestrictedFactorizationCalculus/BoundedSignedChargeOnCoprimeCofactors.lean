import GaloisForLFunctions.RestrictedFactorizationCalculus.MeanApproximationOfCoprimeMobiusRows

/-!
# Bounded signed charge after thinning actual cofactor signs

Keep the next sign exactly when it stays inside the prescribed interval.
Against any comparison sequence whose primitive stays inside the interval,
a rejected sign pays one full unit of approximation error. This gives a
bounded cofactor prefix after discarding an arbitrarily small proportion.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Running sum of the signs retained within an integer cap. -/
def retainedSum (f : ℕ → ℤ) (B : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 =>
    let s := retainedSum f B n
    if |s+f (n+1)| ≤ (B (n+1):ℤ) then s+f (n+1) else s

/-- Whether the sign at n can be retained. -/
def retainSign (f : ℕ → ℤ) (B : ℕ → ℕ) (n : ℕ) : Prop :=
  |retainedSum f B (n-1)+f n| ≤ (B n:ℤ)

private theorem state_step (f : ℕ → ℤ) (B : ℕ → ℕ) (n : ℕ) :
    retainedSum f B (n+1)=retainedSum f B n+(if retainSign f B (n+1) then f (n+1) else 0) := by
  classical
  by_cases h : retainSign f B (n+1)
  · rw [if_pos h]; exact if_pos h
  · rw [if_neg h,add_zero]; exact if_neg h

/-- The running state is the ordinary sharp prefix on the selected set. -/
theorem sum_retained_signs (f : ℕ → ℤ) (B : ℕ → ℕ) (X : ℕ) :
    (∑ n ∈ (Icc 1 X).filter (retainSign f B),(f n:ℝ))=(retainedSum f B X:ℝ) := by
  classical
  rw [sum_filter]
  induction X with
  | zero => simp [retainedSum]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega),ih,state_step,Int.cast_add]
    by_cases h : retainSign f B (n+1) <;> simp [h]

theorem retained_within_cap (f : ℕ → ℤ) {B : ℕ → ℕ} (hB : Monotone B) (X : ℕ) :
    |retainedSum f B X| ≤ (B X:ℤ) := by
  induction X with
  | zero => simp [retainedSum]
  | succ n ih =>
    rw [retainedSum]
    split
    · assumption
    · exact ih.trans (by exact_mod_cast hB (Nat.le_succ n))

private def loss (f : ℕ → ℤ) (B : ℕ → ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X,if retainSign f B n then 0 else 1

private abbrev rowPrefix (g : ℕ → ℝ) (X : ℕ) := ∑ n ∈ Icc 1 X,g n

private theorem partial_succ (g : ℕ → ℝ) (n : ℕ) : rowPrefix g (n+1)=rowPrefix g n+g (n+1) :=
  sum_Icc_succ_top (by omega : 1 ≤ n+1) g

/-- Once the comparison primitive is inside the cap, every rejected sign
decreases the prospective distance to that primitive by exactly one. -/
private theorem comparison_step {f : ℕ → ℤ} (hf : ∀ n,|f n| ≤ 1) {B : ℕ → ℕ} (hB : Monotone B)
    (g : ℕ → ℝ) (n : ℕ) (hg : |rowPrefix g (n+1)| ≤ B (n+1)) :
    loss f B (n+1)+|(retainedSum f B (n+1):ℝ)-rowPrefix g (n+1)| ≤
      loss f B n+|(retainedSum f B n:ℝ)-rowPrefix g n|+|(f (n+1):ℝ)-g (n+1)| := by
  classical
  let s := retainedSum f B n
  let v := f (n+1)
  let P := rowPrefix g (n+1)
  have tri : |(s:ℝ)+(v:ℝ)-P| ≤ |(s:ℝ)-rowPrefix g n|+|(v:ℝ)-g (n+1)| := by
    dsimp only [P]; rw [partial_succ]
    simpa only [show (s:ℝ)+v-(rowPrefix g n+g (n+1))=((s:ℝ)-rowPrefix g n)+((v:ℝ)-g (n+1)) by ring]
      using abs_add_le ((s:ℝ)-rowPrefix g n) ((v:ℝ)-g (n+1))
  have past : |s| ≤ (B (n+1):ℤ) := (retained_within_cap f hB n).trans (by exact_mod_cast hB (Nat.le_succ n))
  have loHi := abs_le.mp past
  have vLim := abs_le.mp (hf (n+1))
  change -1 ≤ v ∧ v ≤ 1 at vLim
  have hs := state_step f B n
  have hl : loss f B (n+1)=loss f B n+(if retainSign f B (n+1) then 0 else 1) :=
    sum_Icc_succ_top (by omega : 1 ≤ n+1) (fun i => if retainSign f B i then 0 else 1)
  rw [hs,hl,Int.cast_add]
  by_cases take : retainSign f B (n+1)
  · rw [if_pos take,if_pos take,add_zero]
    change _+|(s:ℝ)+v-P| ≤ _
    linarith only [tri]
  rw [if_neg take,if_neg take,Int.cast_zero,add_zero]
  change ¬|s+v| ≤ (B (n+1):ℤ) at take
  rw [abs_le] at take
  have faces : (s=(B (n+1):ℤ) ∧ v=1) ∨ (s= -(B (n+1):ℤ) ∧ v= -1) := by omega
  obtain ⟨low,high⟩ := abs_le.mp hg
  change loss f B n+1+|(s:ℝ)-P| ≤ loss f B n+|(s:ℝ)-rowPrefix g n|+|(v:ℝ)-g (n+1)|
  rcases faces with ⟨hi,hv⟩ | ⟨lo,hv⟩
  · have close : P ≤ (s:ℝ) := by rw [hi]; exact_mod_cast high
    have v1 : (v:ℝ)=1 := by exact_mod_cast hv
    rw [v1,abs_of_nonneg (by linarith only [close] : 0 ≤ (s:ℝ)+1-P)] at tri
    rw [v1,abs_of_nonneg (sub_nonneg.mpr close)]
    linarith only [tri]
  · have close : (s:ℝ) ≤ P := by rw [lo,Int.cast_neg]; exact_mod_cast low
    have v1 : (v:ℝ)= -1 := by exact_mod_cast hv
    rw [v1,abs_of_nonpos (by linarith only [close] : (s:ℝ)+ -1-P ≤ 0)] at tri
    rw [v1,abs_of_nonpos (sub_nonpos.mpr close)]
    linarith only [tri]

private theorem comparison_from {f : ℕ → ℤ} (hf : ∀ n,|f n| ≤ 1) {B : ℕ → ℕ} (hB : Monotone B)
    (g : ℕ → ℝ) {N : ℕ} (hg : ∀ n,N ≤ n → |rowPrefix g n| ≤ B n) (k : ℕ) :
    loss f B (N+k)+|(retainedSum f B (N+k):ℝ)-rowPrefix g (N+k)| ≤
      loss f B N+|(retainedSum f B N:ℝ)-rowPrefix g N|+
      rowPrefix (fun n => |(f n:ℝ)-g n|) (N+k)-rowPrefix (fun n => |(f n:ℝ)-g n|) N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,partial_succ (fun n => |(f n:ℝ)-g n|)]
    apply (comparison_step hf hB g (N+k) (hg _ (by omega))).trans
    linarith only [ih]

private theorem loss_eq_card (f : ℕ → ℤ) (B : ℕ → ℕ) (X : ℕ) :
    loss f B X=(((Icc 1 X).filter (fun n => ¬retainSign f B n)).card:ℝ) := by
  classical
  unfold loss
  simp only [←ite_not (α := ℝ) (retainSign f B _) 1 0,sum_boole]

/-- At every prefix the retained signs minimize the total absolute
modification among all real sequences whose partial sums stay in the
cap. Each discarded sign costs one unit; the terminal distance to a
competitor is also paid by its total modification. -/
theorem retained_signs_are_prefix_optimal (f : ℕ → ℤ) (hf : ∀ n,|f n| ≤ 1) (J : ℕ)
    (g : ℕ → ℝ) (bound : ∀ n,|∑ i ∈ Icc 1 n,g i| ≤ J) (X : ℕ) :
    ((((Icc 1 X).filter (fun n => ¬retainSign f (fun _ => J) n)).card):ℝ)+
      |(retainedSum f (fun _ => J) X:ℝ)-∑ n ∈ Icc 1 X,g n| ≤
      ∑ n ∈ Icc 1 X,|(f n:ℝ)-g n| := by
  have h := comparison_from hf (B := fun _ => J) monotone_const g (N := 0) (fun n _ => bound n) X
  simpa only [Nat.zero_add,loss_eq_card,retainedSum,rowPrefix,Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),
    sum_empty,sub_zero,filter_empty,card_empty,Nat.cast_zero,Int.cast_zero,abs_zero,zero_add] using h

/-- The ordinary Möbius sign after imposing the cofactor modulus. -/
def coprimeSign (Q n : ℕ) : ℤ := if Q.Coprime n then μ n else 0

private theorem sign_real (Q n : ℕ) : (coprimeSign Q n:ℝ)=coprimeMoebiusIndicator Q n := by
  by_cases h : Q.Coprime n <;> simp [coprimeSign,coprimeMoebiusIndicator,h]

private theorem sign_small (Q n : ℕ) : |coprimeSign Q n| ≤ 1 := by
  by_cases h : Q.Coprime n
  · simpa only [coprimeSign,if_pos h] using (abs_moebius_le_one (n := n))
  · simp [coprimeSign,h]

/-- For every tolerated loss a single fixed cap bounds the ordinary
retained cofactor sum at all endpoints, while an eventually arbitrarily
small fraction of the cofactor positions is discarded. -/
theorem bounded_charge_after_thinning_coprime_cofactors {Q : ℕ} (hQ : 0<Q) {ε : ℝ} (hε : 0<ε) :
    ∃ J : ℕ, (∀ X : ℕ, |∑ n ∈ (Icc 1 X).filter (retainSign (coprimeSign Q) (fun _ => J)),
      coprimeMoebiusIndicator Q n| ≤ J) ∧
      ∀ᶠ X : ℕ in atTop, ((((Icc 1 X).filter (fun n => ¬retainSign (coprimeSign Q) (fun _ => J) n)).card):ℝ) ≤ ε*X := by
  obtain ⟨g,K,hK,hg⟩ := coprime_moebius_admits_bounded_primitive_approximation hQ (ε/2) (half_pos hε)
  let J := ⌈K⌉₊
  let B := fun _ : ℕ => J
  have mono : Monotone B := monotone_const
  have cap (n : ℕ) : |rowPrefix g n| ≤ B n := (hg n).1.trans (Nat.le_ceil _)
  refine ⟨J,fun X => ?_,?_⟩
  · simp_rw [←sign_real,sum_retained_signs]
    exact_mod_cast retained_within_cap (coprimeSign Q) mono X
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2*K/ε)] with X hx
    have step := retained_signs_are_prefix_optimal (coprimeSign Q) (sign_small Q) J g cap X
    simp_rw [sign_real] at step
    have err := (hg X).2
    have room := (div_le_iff₀ hε).1 hx
    linarith only [step,err,room,abs_nonneg ((retainedSum (coprimeSign Q) B X:ℝ)-rowPrefix g X)]

/-- Every prescribed diverging integer cap gives a sequential thinning
of density zero. Its complement has signed prefix bounded by that cap. -/
theorem vanishing_loss_for_every_diverging_cap {Q : ℕ} (hQ : 0<Q) (B : ℕ → ℕ)
    (mono : Monotone B) (top : Tendsto B atTop atTop) :
    (∀ X, |∑ n ∈ (Icc 1 X).filter (retainSign (coprimeSign Q) B),coprimeMoebiusIndicator Q n| ≤ B X) ∧
    ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
      ((((Icc 1 X).filter (fun n => ¬retainSign (coprimeSign Q) B n)).card):ℝ) ≤ ε*X := by
  refine ⟨fun X => ?_,?_⟩
  · simp_rw [←sign_real,sum_retained_signs]
    exact_mod_cast retained_within_cap (coprimeSign Q) mono X
  intro ε hε
  obtain ⟨g,K,hK,hg⟩ := coprime_moebius_admits_bounded_primitive_approximation hQ (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (top.eventually_ge_atTop ⌈K⌉₊)
  have cap (n : ℕ) (hn : N ≤ n) : |rowPrefix g n| ≤ B n :=
    (hg n).1.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (hN n hn)))
  let F := coprimeSign Q
  let A := loss F B N+|(retainedSum F B N:ℝ)-rowPrefix g N|
  have errN : 0 ≤ rowPrefix (fun n => |coprimeMoebiusIndicator Q n-g n|) N :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  filter_upwards [eventually_ge_atTop N,tendsto_natCast_atTop_atTop.eventually_ge_atTop (2*(A+K)/ε)] with X hx hr
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hx
  have step := comparison_from (sign_small Q) mono g cap k
  have err := (hg (N+k)).2
  simp_rw [sign_real] at step
  change loss F B (N+k)+_ ≤ A+_-_ at step
  rw [←loss_eq_card]
  have room := (div_le_iff₀ hε).1 hr
  linarith only [step,err,errN,room,abs_nonneg ((retainedSum F B (N+k):ℝ)-rowPrefix g (N+k))]

#print axioms retained_signs_are_prefix_optimal
#print axioms bounded_charge_after_thinning_coprime_cofactors
#print axioms vanishing_loss_for_every_diverging_cap

end GaloisForLFunctions.RestrictedFactorizationCalculus
