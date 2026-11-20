import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedPrefixOfOneTruncatedExchange
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedCrossingsBetweenTwoWalls
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensExponentOnOneSparseFixedSet
import GaloisForLFunctions.RHTower.Sieve.IntervalSelberg

/-!
# Detecting every Mertens exponent on each of two complementary signed prefixes

The difference of any two local refinements is an iterated dilation
difference on one coprime Möbius prefix. At a failed exponent at most
one refinement can have a bounded fixed charge, and at most one a
bounded crossing charge. Three choices suffice at every exponent together.
-/
noncomputable section
open Filter Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev Prefix := ℕ → ℝ
private abbrev M : Prefix := coprimeMoebiusSum 1

private theorem sub_bound {s : ℝ} {F G : Prefix} (a : PrefixPower s F) (b : PrefixPower s G) :
    PrefixPower s (fun n => F n-G n) := by
  obtain ⟨C,cp,left⟩ := a
  obtain ⟨D,dp,right⟩ := b
  exact ⟨C+D,add_nonneg cp dp,fun n => (abs_sub ..).trans ((add_le_add (left n) (right n)).trans_eq (add_mul ..).symm)⟩

private theorem up_bound {s t : ℝ} (order : s ≤ t) {F : Prefix} (zero : F 0=0) (a : PrefixPower s F) :
    PrefixPower t F := by
  obtain ⟨C,c0,cap⟩ := a
  refine ⟨C,c0,fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · rw [zero,abs_zero]; positivity
  exact (cap n).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp) order) c0)

private theorem dilate_bound {s : ℝ} (sp : 0<s) {F : Prefix} (bound : PrefixPower s F) (a : ℕ) :
    PrefixPower s (fun n => F (n/a)) := by
  obtain ⟨C,c0,cap⟩ := bound
  exact ⟨C,c0,fun n => (cap _).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.div_le_self n a)) sp.le) c0)⟩

private theorem oriented_difference {p q : ℕ} (pp : 0<p) (qp : 0<q) (diff : p ≠ q)
    {s : ℝ} (sp : 0<s) (F : Prefix) (zero : F 0=0) :
    PrefixPower s (dilationDifference p q F) ↔ PrefixPower s F := by
  rcases lt_or_gt_of_ne diff with lt | gt
  · exact prefixPower_dilationDifference_iff pp lt sp F zero
  have swap : PrefixPower s (dilationDifference p q F) ↔ PrefixPower s (dilationDifference q p F) := by
    unfold PrefixPower dilationDifference
    constructor <;> rintro ⟨C,c0,cap⟩ <;> exact ⟨C,c0,fun n => (abs_sub_comm ..).le.trans (cap n)⟩
  exact swap.trans (prefixPower_dilationDifference_iff qp gt sp F zero)

private def tag : Fin 3 → ℕ := ![2,3,5]

private theorem tag_prime (i : Fin 3) : (tag i).Prime := by fin_cases i <;> decide
private theorem tag_le_five (i : Fin 3) : tag i ≤ 5 := by fin_cases i <;> decide
private theorem tags_distinct : Function.Injective tag := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction

private theorem three_choices {P C : Fin 3 → Prop}
    (fixed : ∀ i j,i ≠ j → P i → P j → False)
    (cross : ∀ i j,i ≠ j → C i → C j → False) (each : ∀ i,P i ∨ C i) : False := by
  rcases each 0 with h0 | h0 <;> rcases each 1 with h1 | h1 <;> rcases each 2 with h2 | h2 <;>
    first | exact fixed 0 1 (by decide) h0 h1 | exact fixed 0 2 (by decide) h0 h2 |
            exact fixed 1 2 (by decide) h1 h2 | exact cross 0 1 (by decide) h0 h1 |
            exact cross 0 2 (by decide) h0 h2 | exact cross 1 2 (by decide) h1 h2

/-- Translating one detecting difference by three distinct prime
dilations forces one refinement to detect every positive exponent
in both complementary prefixes. -/
private theorem joint_exponents (D U : Prefix) (D0 : D 0=0) (U0 : U 0=0)
    (detect : ∀ s,0<s → (PrefixPower s U ↔ PrefixPower s M))
    (upper : ∀ s,0<s → PrefixPower s M → PrefixPower s D) :
    let F := fun i n => D n-U (n/tag i)
    let C := fun i n => M n-F i n
    ∃ i : Fin 3,∀ s,0<s →
      (PrefixPower s (F i) ↔ PrefixPower s M) ∧ (PrefixPower s (C i) ↔ PrefixPower s M) := by
  let F := fun i n => D n-U (n/tag i)
  let C := fun i n => M n-F i n
  have mz : M 0=0 := by simp [M,coprimeMoebiusSum]
  have fzero (i : Fin 3) : F i 0=0 := by simp [F,D0,U0]
  have czero (i : Fin 3) : C i 0=0 := by simp only [C,mz,fzero,sub_self]
  have fcap (s : ℝ) (sp : 0<s) (m : PrefixPower s M) (i : Fin 3) : PrefixPower s (F i) :=
    sub_bound (upper s sp m) (dilate_bound sp ((detect s sp).mpr m) (tag i))
  have ccap (s : ℝ) (sp : 0<s) (m : PrefixPower s M) (i : Fin 3) : PrefixPower s (C i) :=
    sub_bound m (fcap s sp m i)
  have recover {s : ℝ} (sp : 0<s) (i j : Fin 3) (ne : i ≠ j)
      (pair : PrefixPower s (fun n => U (n/tag i)-U (n/tag j))) : PrefixPower s M :=
    (detect s sp).mp ((oriented_difference (tag_prime i).pos (tag_prime j).pos
      (fun h => ne (tags_distinct h)) sp U U0).mp pair)
  have choose : ∃ i : Fin 3,∀ s,0<s → ¬PrefixPower s M → ¬(PrefixPower s (F i) ∨ PrefixPower s (C i)) := by
    by_contra! obstruction
    choose s positive failed paid using obstruction
    obtain ⟨j,_,maximal⟩ := exists_max_image (univ : Finset (Fin 3)) s univ_nonempty
    have each (i : Fin 3) : PrefixPower (s j) (F i) ∨ PrefixPower (s j) (C i) :=
      (paid i).imp (up_bound (maximal i (mem_univ i)) (fzero i)) (up_bound (maximal i (mem_univ i)) (czero i))
    apply three_choices _ _ each
    · intro u v ne left right
      apply failed j (recover (positive j) u v ne ?_)
      have eq : (fun n => F v n-F u n)=(fun n => U (n/tag u)-U (n/tag v)) := by funext n; dsimp only [F]; ring
      exact eq ▸ sub_bound right left
    · intro u v ne left right
      apply failed j (recover (positive j) u v ne ?_)
      have eq : (fun n => C u n-C v n)=(fun n => U (n/tag u)-U (n/tag v)) := by funext n; dsimp only [C,F]; ring
      exact eq ▸ sub_bound left right
  obtain ⟨i,works⟩ := choose
  refine ⟨i,fun s sp => ⟨⟨fun h => by by_contra bad; exact works s sp bad (Or.inl h),fun h => fcap s sp h i⟩,
    ⟨fun h => by by_contra bad; exact works s sp bad (Or.inr h),fun h => ccap s sp h i⟩⟩⟩

private def mark (F : ℕ → ℕ) (Q d e n : ℕ) :=
  if n.gcd Q=d then n/d*e else if n.gcd Q=e then n/e*d else F n

private theorem cofactor_edge {d e : ℕ} (edge : GlobalDyadicOneTwoRel d e) {c : ℕ}
    (sq : Squarefree c) (cd : c.Coprime d) (ce : c.Coprime e) : GlobalDyadicOneTwoRel (c*d) (c*e) := by
  obtain ⟨sd,se,sign,a,p,q,r,hp,hq,hr,lt,pair⟩ := edge
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨cd,sq,sd⟩,Nat.squarefree_mul_iff.mpr ⟨ce,sq,se⟩,?_,c*a,p,q,r,hp,hq,hr,lt,?_⟩
  · rw [isMultiplicative_moebius.map_mul_of_coprime cd,isMultiplicative_moebius.map_mul_of_coprime ce,sign,mul_neg]
  · rcases pair with ⟨a',b'⟩ | ⟨a',b'⟩
    · exact Or.inl ⟨by rw [a',Nat.mul_assoc],by rw [b',Nat.mul_assoc]⟩
    · exact Or.inr ⟨by rw [a',Nat.mul_assoc],by rw [b',Nat.mul_assoc]⟩

private theorem marked_move {n Q d e : ℕ} (sq : Squarefree n) (hit : n.gcd Q=d) (ed : e ∣ Q)
    (edge : GlobalDyadicOneTwoRel d e) {h : ℝ} (short : |(e:ℝ)-d| ≤ h*d) :
    let c := n/d
    (c*e).gcd Q=e ∧ (c*e)/e*d=n ∧ GlobalDyadicOneTwoRel n (c*e) ∧ |((c*e:ℕ):ℝ)-n| ≤ h*n := by
  let c := n/d
  have dn : d ∣ n := hit ▸ Nat.gcd_dvd_left n Q
  have dq : d ∣ Q := hit ▸ Nat.gcd_dvd_right n Q
  have ce : c*d=n := Nat.div_mul_cancel dn
  have cQ : c.Coprime Q := by
    change (n/d).Coprime Q
    rw [←hit]
    rcases Nat.eq_zero_or_pos Q with rfl | pos
    · simp [Nat.div_self (Nat.pos_of_ne_zero sq.ne_zero)]
    · exact Nat.coprime_div_gcd_of_squarefree sq pos.ne'
  have cp : 0<e := Nat.pos_of_ne_zero edge.2.1.ne_zero
  have sc := sq.squarefree_of_dvd (Nat.div_dvd_of_dvd dn)
  refine ⟨(Nat.Coprime.gcd_mul_left_cancel e cQ).trans (Nat.gcd_eq_left ed),?_,?_,?_⟩
  · rw [Nat.mul_div_cancel _ cp]; exact ce
  · exact ce ▸ cofactor_edge edge sc (Nat.Coprime.coprime_dvd_right dq cQ) (Nat.Coprime.coprime_dvd_right ed cQ)
  · change |((c*e:ℕ):ℝ)-n| ≤ h*n
    conv_lhs => rw [←ce,Nat.cast_mul,Nat.cast_mul,←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul_of_nonneg_left short (Nat.cast_nonneg (α := ℝ) c)).trans_eq (by rw [←ce,Nat.cast_mul]; ring)

private theorem mark_law {F : ℕ → ℕ} {Q d e : ℕ} {h : ℝ} (different : d ≠ e)
    (dd : d ∣ Q) (ed : e ∣ Q) (edge : GlobalDyadicOneTwoRel d e)
    (shortD : |(e:ℝ)-d| ≤ h*d) (shortE : |(d:ℝ)-e| ≤ h*e)
    (law : ∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ h*n)
    (old : ∀ n,Squarefree n → (n.gcd Q=d ∨ n.gcd Q=e) → F n=n) (n : ℕ) (sq : Squarefree n) :
    let G := mark F Q d e
    G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧ |(G n:ℝ)-n| ≤ h*n ∧
      (G n=n ↔ F n=n ∧ ¬(n.gcd Q=d ∨ n.gcd Q=e)) := by
  have distinct {x y : ℕ} (move : GlobalDyadicOneTwoRel x y) : y ≠ x := by
    rintro rfl
    have sign := move.2.2.1
    rcases moebius_eq_one_or_neg_one_of_squarefree move.1 with pos | neg <;> omega
  by_cases d1 : n.gcd Q=d
  · obtain ⟨toE,back,rel,near⟩ := marked_move sq d1 ed edge shortD
    simp only [mark,if_pos d1,toE,if_neg different.symm,if_true,back,true_and]
    exact ⟨Or.inr rel,near,iff_of_false (distinct rel) (fun bad => bad.2 (Or.inl d1))⟩
  by_cases e1 : n.gcd Q=e
  · obtain ⟨toD,back,rel,near⟩ := marked_move sq e1 dd edge.symm shortE
    simp only [mark,if_neg d1,if_pos e1,toD,if_true,back,true_and]
    exact ⟨Or.inr rel,near,iff_of_false (distinct rel) (fun bad => bad.2 (Or.inr e1))⟩
  have outside := not_or.mpr ⟨d1,e1⟩
  obtain ⟨back,rel,near⟩ := law n sq
  have sq' := rel.elim (fun same => by rw [same]; exact sq) (fun move => move.2.1)
  have kept : ¬((F n).gcd Q=d ∨ (F n).gcd Q=e) := fun hit => outside (by
    have same := back.symm.trans (old _ sq' hit)
    simpa only [←same] using hit)
  simp only [mark,if_neg d1,if_neg e1,if_neg (not_or.mp kept).1,if_neg (not_or.mp kept).2,back,true_and]
  exact ⟨rel,near,iff_and_self.mpr (fun _ => outside)⟩

private theorem marked_prefix {F : ℕ → ℕ} {Q d e : ℕ} (ne : d ≠ e) (md : d ∈ Q.divisors) (me : e ∈ Q.divisors)
    (signD : μ d=1) (signE : μ e= -1)
    (fix : ∀ n,Squarefree n → (mark F Q d e n=n ↔ F n=n ∧ ¬(n.gcd Q=d ∨ n.gcd Q=e)))
    (old : ∀ n,Squarefree n → (n.gcd Q=d ∨ n.gcd Q=e) → F n=n) (X : ℕ) :
    fixedSignedPrefix (mark F Q d e) X=fixedSignedPrefix F X-
      (coprimeMoebiusSum Q (X/d)-coprimeMoebiusSum Q (X/e)) := by
  let E : Finset ℕ := {d,e}
  have sub : E ⊆ Q.divisors := fun x hx => by
    rcases (show x=d ∨ x=e by simpa only [E,mem_insert,mem_singleton] using hx) with rfl | rfl
    · exact md
    · exact me
  have budget := signed_prefix_of_gcd_classes sub X
  have value : divisorPrefix E (coprimeMoebiusSum Q) X=coprimeMoebiusSum Q (X/d)-coprimeMoebiusSum Q (X/e) := by
    rw [divisorPrefix,show E=insert d {e} from rfl,sum_insert (by simpa using ne),sum_singleton,signD,signE]
    push_cast; ring
  rw [←value,←budget]
  simp only [fixedSignedPrefix,squarefreeOf,sum_filter,←sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  by_cases sq : Squarefree n
  · simp only [if_pos sq,E,mem_insert,mem_singleton,fix n sq]
    by_cases hit : n.gcd Q=d ∨ n.gcd Q=e
    · simp [hit,old n sq hit]
    · simp [hit]
  · simp only [if_neg sq,moebius_eq_zero_of_not_squarefree sq,Int.cast_zero,ite_self,sub_zero]

private theorem short_map_fixes_small_gcd {F : ℕ → ℕ} {P Q n a b : ℕ}
    (square : Squarefree P) (extn : P ∣ Q) (ap : 0<a) (low : a ≤ 5) (cop : b.Coprime P)
    (gcdRow : n.gcd Q=a*b) (scale : ∀ n,F n=n/n.gcd P*F (n.gcd P))
    {h : ℝ} (hp : 0 ≤ h) (tiny : h ≤ 1/10)
    (close : ∀ x,Squarefree x → |(F x:ℝ)-x| ≤ h*x) : F n=n := by
  let g := n.gcd P
  have eq : g=a.gcd P := by
    change n.gcd P=_
    calc n.gcd P=(n.gcd Q).gcd P := by rw [Nat.gcd_assoc,Nat.gcd_eq_right extn]
         _ = _ := by rw [gcdRow]; exact Nat.Coprime.gcd_mul_right_cancel a cop
  have small : g ≤ 5 := eq.le.trans ((Nat.gcd_le_left P ap).trans low)
  have sq := square.squarefree_of_dvd (Nat.gcd_dvd_right n P)
  have gap : |(F g:ℝ)-g|<1 := (close g sq).trans_lt (by
    have cap := mul_le_mul tiny (Nat.cast_le.mpr small : (g:ℝ) ≤ 5) (Nat.cast_nonneg g) (by norm_num)
    linarith only [cap])
  have right : F g<g+1 := by exact_mod_cast (show (F g:ℝ)<g+1 by linarith only [(abs_lt.mp gap).2])
  have left : g<F g+1 := by exact_mod_cast (show (g:ℝ)<F g+1 by linarith only [(abs_lt.mp gap).1])
  have fixed : F g=g := by omega
  rw [scale]
  change n/g*F g=n
  rw [fixed,Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

/-- At prescribed sparsity and maximum relative length, one table
retains every positive Mertens power in each of its two signed charges,
including at any attained endpoint exponent. -/
theorem simultaneous_mertens_powers_on_fixed_and_crossing_vertices {ε : ℝ} (ep : 0<ε) :
    ∃ G : ℕ → ℕ,(∀ n,Squarefree n → G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧ |(G n:ℝ)-n| ≤ ε*n) ∧
      (∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧ ∀ s : ℝ,0<s →
        (PrefixPower s (fixedSignedPrefix G) ↔ PrefixPower s (coprimeMoebiusSum 1)) ∧
        (PrefixPower s (crossingSignedPrefix G) ↔ PrefixPower s (coprimeMoebiusSum 1)) := by
  let h := min ε (1/10)
  have hp : 0<h := lt_min ep (by norm_num)
  obtain ⟨P,sqP,F,scale,law,_,count,spectrum⟩ := finite_divisor_table_detecting_every_mertens_power hp
  obtain ⟨J,larger⟩ := exists_nat_gt (1/h)
  have j0 : 0<(J:ℝ) := (one_div_pos.mpr hp).trans larger
  have pay : 1/(J:ℝ) ≤ h := (div_le_iff₀ j0).mpr (by
    have room := (div_lt_iff₀ hp).mp larger
    linarith only [room])
  obtain ⟨e,pHigh,qHigh,rHigh,np,nw⟩ := exists_short_primitive_exchange_above J (P+5) (Nat.cast_pos.mp j0)
  let B := P+5*(e.p+e.w)+5
  let Q := primorial B
  have sqQ : Squarefree Q := squarefree_primorial B
  have extends : P ∣ Q := RHTower.Sieve.dvd_primorial_of_squarefree sqP (by dsimp only [B]; omega)
  have bigCoprime {v : ℕ} (prime : v.Prime) (high : P+5<v) : v.Coprime P :=
    prime.coprime_iff_not_dvd.mpr (fun dvd => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero sqP.ne_zero) dvd; omega)
  have cp := bigCoprime e.prime_p pHigh
  have cw : e.w.Coprime P := (bigCoprime e.prime_q qHigh).mul_left (bigCoprime e.prime_r rHigh)
  obtain ⟨_,_,signP,signW,distinct⟩ := e.primitives
  let d := fun i => tag i*e.p
  let w := fun i => tag i*e.w
  let G := fun i => mark F Q (d i) (w i)
  have noEq (i : Fin 3) : d i ≠ w i := fun eq => distinct (Nat.eq_of_mul_eq_mul_left (tag_prime i).pos eq).symm
  have oddPair (i : Fin 3) :
      Squarefree (d i) ∧ Squarefree (w i) ∧ μ (d i)=1 ∧ μ (w i)= -1 := by
    let l := tag i
    have t := tag_le_five i
    have prime := tag_prime i
    have copr {v : ℕ} (q : v.Prime) (large : P+5<v) : l.Coprime v :=
      (Nat.coprime_primes prime q).mpr (by change tag i ≠ v; omega)
    have lp := copr e.prime_p pHigh
    have lw : l.Coprime e.w := (copr e.prime_q qHigh).mul_right (copr e.prime_r rHigh)
    have sw : Squarefree e.w := Nat.squarefree_mul_iff.mpr
      ⟨(Nat.coprime_primes e.prime_q e.prime_r).mpr e.lt.ne,e.prime_q.squarefree,e.prime_r.squarefree⟩
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨lp,prime.squarefree,e.prime_p.squarefree⟩,
      Nat.squarefree_mul_iff.mpr ⟨lw,prime.squarefree,sw⟩,?_,?_⟩
    · change μ (l*e.p)=1
      rw [isMultiplicative_moebius.map_mul_of_coprime lp,moebius_apply_prime prime,signP]; decide
    · change μ (l*e.w)= -1
      rw [isMultiplicative_moebius.map_mul_of_coprime lw,moebius_apply_prime prime,signW]; decide
  have marked (i : Fin 3) : d i ∈ Q.divisors ∧ w i ∈ Q.divisors := by
    have ad := Nat.mul_le_mul_right e.p (tag_le_five i)
    have aw := Nat.mul_le_mul_right e.w (tag_le_five i)
    obtain ⟨sd,sw,_,_⟩ := oddPair i
    exact ⟨Nat.mem_divisors.mpr ⟨RHTower.Sieve.dvd_primorial_of_squarefree sd (by dsimp only [d,B]; omega),sqQ.ne_zero⟩,
      Nat.mem_divisors.mpr ⟨RHTower.Sieve.dvd_primorial_of_squarefree sw (by dsimp only [w,B]; omega),sqQ.ne_zero⟩⟩
  have old (i : Fin 3) (n : ℕ) (_ : Squarefree n) (hit : n.gcd Q=d i ∨ n.gcd Q=w i) : F n=n := by
    rcases hit with hit | hit
    · exact short_map_fixes_small_gcd sqP extends (tag_prime i).pos (tag_le_five i) cp hit scale hp.le (min_le_right ..) (fun x sx => (law x sx).2.2)
    · exact short_map_fixes_small_gcd sqP extends (tag_prime i).pos (tag_le_five i) cw hit scale hp.le (min_le_right ..) (fun x sx => (law x sx).2.2)
  have times {x z : ℕ} (i : Fin 3) (near : |(z:ℝ)-x| ≤ (x:ℝ)/J) :
      |((tag i*z:ℕ):ℝ)-((tag i*x:ℕ):ℝ)| ≤ h*((tag i*x:ℕ):ℝ) := by
    have fit := mul_le_mul_of_nonneg_right pay (Nat.cast_nonneg (α := ℝ) x)
    have price := near.trans (by simpa only [one_div,div_eq_mul_inv,mul_comm (J:ℝ)⁻¹] using fit)
    rw [Nat.cast_mul,Nat.cast_mul,←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg (tag i))]
    exact (mul_le_mul_of_nonneg_left price (Nat.cast_nonneg (tag i))).trans_eq (by ring)
  have refined (i : Fin 3) (n : ℕ) (sq : Squarefree n) :
      G i (G i n)=n ∧ (G i n=n ∨ GlobalDyadicOneTwoRel n (G i n)) ∧ |(G i n:ℝ)-n| ≤ h*n ∧
        (G i n=n ↔ F n=n ∧ ¬(n.gcd Q=d i ∨ n.gcd Q=w i)) := by
    obtain ⟨sd,sw,ds,ws⟩ := oddPair i
    have edge : GlobalDyadicOneTwoRel (d i) (w i) := ⟨sd,sw,by rw [ds,ws]; decide,
      tag i,e.p,e.q,e.r,e.prime_p,e.prime_q,e.prime_r,e.lt,Or.inl ⟨rfl,rfl⟩⟩
    exact mark_law (noEq i) (Nat.dvd_of_mem_divisors (marked i).1) (Nat.dvd_of_mem_divisors (marked i).2)
      edge (times i ((abs_sub_comm ..).le.trans np)) (times i nw) law (old i) n sq
  let U := dilationDifference e.p e.w (coprimeMoebiusSum Q)
  have recover (s : ℝ) (sp : 0<s) : PrefixPower s U ↔ PrefixPower s M :=
    (oriented_difference e.prime_p.pos (Nat.mul_pos e.prime_q.pos e.prime_r.pos) distinct.symm sp _ (by simp [coprimeMoebiusSum])).trans
      (coprime_prefix_preserves_every_power sqQ sp)
  have base : (fun X => ∑ n ∈ Icc 1 X,(μ n:ℝ))=M := by funext X; simp [M,coprimeMoebiusSum,coprimeMoebiusIndicator]
  rw [base] at spectrum
  have price (i : Fin 3) (X : ℕ) : fixedSignedPrefix (G i) X=fixedSignedPrefix F X-U (X/tag i) := by
    obtain ⟨_,_,ds,ws⟩ := oddPair i
    have head := marked_prefix (noEq i) (marked i).1 (marked i).2 ds ws
      (fun n sn => (refined i n sn).2.2.2) (old i) X
    simpa only [G,U,dilationDifference,d,w,Nat.div_div_eq_div_mul] using head
  obtain ⟨i,detect⟩ := joint_exponents (fixedSignedPrefix F) U (by simp [fixedSignedPrefix,squarefreeOf])
    (by simp [U,dilationDifference]) recover (fun s sp => (spectrum s sp).mpr)
  have lawG (n : ℕ) (sn : Squarefree n) := (refined i n sn).1
  have relG (n : ℕ) (sn : Squarefree n) := (refined i n sn).2.1
  have rest (X : ℕ) : crossingSignedPrefix (G i) X=M X-(fixedSignedPrefix F X-U (X/tag i)) := by
    have sum := fixed_add_crossing (G i) (fun n sn => ⟨lawG n sn,relG n sn⟩) X
    rw [price] at sum
    linarith only [sum]
  refine ⟨G i,fun n sn => ⟨lawG n sn,relG n sn,((refined i n sn).2.2.1).trans
    (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg n))⟩,?_,?_⟩
  · filter_upwards [count] with X cap
    have sub : prefixUnpaid (G i) X ⊆ prefixUnpaid F X := by
      intro n hn
      obtain ⟨inside,possible⟩ := mem_filter.mp hn
      have sn := (mem_filter.mp inside).2
      refine mem_filter.mpr ⟨inside,?_⟩
      by_cases hit : n.gcd Q=d i ∨ n.gcd Q=w i
      · exact Or.inl (old i n sn hit)
      · simpa only [G,mark,if_neg (not_or.mp hit).1,if_neg (not_or.mp hit).2] using possible
    exact (Nat.cast_le.mpr (card_le_card sub)).trans (cap.trans (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg X)))
  · intro s sp
    rw [funext (price i),funext rest]
    exact detect s sp

end GaloisForLFunctions.RestrictedFactorizationCalculus
