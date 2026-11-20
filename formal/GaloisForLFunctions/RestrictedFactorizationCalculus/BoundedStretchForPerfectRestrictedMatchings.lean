import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensAbscissaOnOneDensityZeroFixedSet
import Mathlib.NumberTheory.Bertrand
import GaloisForLFunctions.RestrictedFactorizationCalculus.PerfectCompletionAtEverySharpCutoff

/-!
# Bounded stretch for a perfect restricted matching

Prime tables on odd moduli preserve divisibility by two. Their odd
pairs can be copied to their doubles. An increasing prime ray joins
the remaining even prime to these pairs without using the unit.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem range_switch_preserves_two {J : ℕ} {I : Finset ℕ} (ready : ∀ k ∈ I,bandReady J k)
    {n : ℕ} (sq : Squarefree n) : (rangeSwitch J I n).gcd 2=n.gcd 2 := by
  by_cases active : (activeBands J I n).Nonempty
  · let k := (activeBands J I n).min' active
    have hk := mem_filter.mp (min'_mem (activeBands J I n) active)
    have odd : (switchModulus k).Coprime 2 := by
      apply Nat.Coprime.symm
      apply Nat.prime_two.coprime_iff_not_dvd.mpr
      intro divides
      have member := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,divides,(switchModulus_spec k).2.2.ne'⟩
      rw [(switchModulus_spec k).2.1] at member
      obtain ⟨_,low,high⟩ := mem_switchPrimes.mp member
      have one : (2:ℕ)^k = 1 := by have := Nat.two_pow_pos k; omega
      rw [one] at high
      norm_num at high
    rw [rangeSwitch,dif_pos active]
    exact (switchInteger_on_endpoint (ready k hk.1) sq hk.2).2.2.2.2 2 odd
  · rw [rangeSwitch,dif_neg active]

/-- One short matching preserves divisibility by two. Its unpaid
squarefree vertices have density zero at every sharp prefix. -/
theorem density_one_matching_preserving_two :
    ∃ F : ℕ → ℕ, (∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧
        (F n).gcd 2=n.gcd 2 ∧ F n ≤ 2*n) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid F X).card:ℝ) ≤ ε*X ∧
        (Squarefree X → |(F X:ℝ)-X| ≤ ε*X) := by
  let h := fun j : ℕ => 1/((j:ℝ)+2)
  have hp (j : ℕ) : 0<h j := by dsimp only [h]; positivity
  choose J I ready law balance count using fun j => dense_prime_range_table_at_every_prefix (hp j)
  let f := fun j => rangeSwitch (J j) (I j)
  choose start good using fun j => eventually_atTop.mp (count j)
  let L : ℕ → ℕ := Nat.rec (start 0) (fun j old => max (start (j+1)) ((j+2)*old+1))
  have spacing (j : ℕ) : (j+2)*L j<L (j+1) := (Nat.lt_succ_self _).trans_le (le_max_right ..)
  have strict : StrictMono L := strictMono_nat_of_lt_succ (fun j =>
    (Nat.le_mul_of_pos_left (L j) (by omega : 0<j+2)).trans_lt (spacing j))
  have onset (j : ℕ) : start j ≤ L j := by cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left .. 
  let F := blockSwitch L f
  have edges (j n : ℕ) (hs : Squarefree n) := (law j n hs).1
  have localLaw (j n : ℕ) (hs : Squarefree n) : f j (f j n)=n ∧ (f j n=n ∨ GlobalDyadicOneTwoRel n (f j n)) :=
    ⟨edges j n hs,(law j n hs).2.1⟩
  refine ⟨F,?_,dense_blocks_of_spaced_walls L f strict spacing localLaw
    (fun j n hn => good j n ((onset j).trans hn)) (fun j n hs => (law j n hs).2.2)⟩
  intro n hs
  obtain ⟨back,edge⟩ := block_law strict.monotone localLaw n hs
  refine ⟨back,edge,?_⟩
  by_cases hit : ∃ j,InBlock L j n
  · obtain ⟨j,hj⟩ := hit
    change (blockSwitch L f n).gcd 2=n.gcd 2 ∧ blockSwitch L f n ≤ 2*n
    rw [block_eval strict.monotone f hj]
    split
    · have width : h j ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) j])
      have gap := ((abs_le.mp (law j n hs).2.2).2).trans
        (mul_le_mul_of_nonneg_right width (Nat.cast_nonneg n))
      have maxSize : (f j n:ℝ) ≤ 2*(n:ℝ) := by linarith only [gap]
      exact ⟨range_switch_preserves_two (ready j) hs,by exact_mod_cast maxSize⟩
    · exact ⟨rfl,by omega⟩
  · have same : F n=n := dif_neg hit
    rw [same]; exact ⟨rfl,by omega⟩

private def biggerPrime (n : ℕ) := (Nat.exists_prime_lt_and_le_two_mul (2*max n 1) (by positivity)).choose

private def rayPrime : ℕ → ℕ := Nat.rec 5 (fun _ p => biggerPrime p)

private theorem ray_step (j : ℕ) : (rayPrime (j+1)).Prime ∧ 2*rayPrime j<rayPrime (j+1) ∧
    rayPrime (j+1) ≤ 4*rayPrime j := by
  have positive (i : ℕ) : 0<rayPrime i := by
    cases i with
    | zero => decide
    | succ i => exact (Nat.exists_prime_lt_and_le_two_mul (2*max (rayPrime i) 1) (by positivity)).choose_spec.1.pos
  have h := (Nat.exists_prime_lt_and_le_two_mul (2*max (rayPrime j) 1) (by positivity)).choose_spec
  change (rayPrime (j+1)).Prime ∧ 2*max (rayPrime j) 1 < rayPrime (j+1) ∧
    rayPrime (j+1) ≤ 2*(2*max (rayPrime j) 1) at h
  rw [max_eq_left (positive j)] at h
  exact ⟨h.1,h.2.1,by simpa only [show 4*rayPrime j=2*(2*rayPrime j) by ring] using h.2.2⟩

private theorem ray_strict : StrictMono rayPrime := strictMono_nat_of_lt_succ (fun j =>
  (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans_lt (ray_step j).2.1)

private theorem ray_primes (j : ℕ) : (rayPrime j).Prime ∧ 5 ≤ rayPrime j := by
  refine ⟨?_,ray_strict.monotone (Nat.zero_le j)⟩
  cases j with
  | zero => decide
  | succ j => exact (ray_step j).1

-- The singleton at the foot of the ray supplies the missing even prime.
private def oddRay : ℕ → ℕ
  | 0 => 1
  | j+1 => 3*rayPrime j

private theorem odd_ray_strict : StrictMono oddRay := strictMono_nat_of_lt_succ fun j => by
  cases j with
  | zero => decide
  | succ j => exact Nat.mul_lt_mul_of_pos_left (ray_strict (Nat.lt_succ_self j)) (by decide)

private theorem odd_ray_properties (j : ℕ) : Squarefree (oddRay j) ∧ ¬2 ∣ oddRay j := by
  cases j with
  | zero => exact ⟨squarefree_one,by decide⟩
  | succ j =>
    obtain ⟨prime,large⟩ := ray_primes j
    have cp := (Nat.coprime_primes (by decide : Nat.Prime 3) prime).mpr (by omega)
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨cp,(by decide : Nat.Prime 3).squarefree,prime.squarefree⟩,?_⟩
    intro dvd
    rcases Nat.prime_two.dvd_mul.mp dvd with inThree | inPrime
    · exact (by decide : ¬2 ∣ 3) inThree
    · have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two prime).mp inPrime
      omega

private theorem ray_edge (j : ℕ) : GlobalDyadicOneTwoRel (2*oddRay j) (oddRay (j+1)) := by
  obtain ⟨sq,odd⟩ := odd_ray_properties j
  have cp := Nat.prime_two.coprime_iff_not_dvd.mpr odd
  have source := Nat.squarefree_mul_iff.mpr ⟨cp,Nat.prime_two.squarefree,sq⟩
  refine ⟨source,(odd_ray_properties (j+1)).1,?_,?_⟩
  · cases j with
    | zero =>
      change μ 2 = -μ (3*5)
      rw [isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 3 5),
        moebius_apply_prime Nat.prime_two,moebius_apply_prime (by decide : Nat.Prime 3),
        moebius_apply_prime (by decide : Nat.Prime 5)]
      decide
    | succ i =>
      have mu (k : ℕ) : μ (oddRay (k+1))=1 := by
        obtain ⟨prime,large⟩ := ray_primes k
        change μ (3*rayPrime k)=1
        rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.coprime_primes (by decide : Nat.Prime 3) prime).mpr (by omega)),
          moebius_apply_prime (by decide : Nat.Prime 3),moebius_apply_prime prime]
        decide
      rw [isMultiplicative_moebius.map_mul_of_coprime cp,moebius_apply_prime Nat.prime_two,mu,mu]
      decide
  · cases j with
    | zero => exact ⟨1,2,3,5,by decide,by decide,by decide,by decide,Or.inl ⟨rfl,rfl⟩⟩
    | succ i =>
      exact ⟨3,rayPrime (i+1),2,rayPrime i,(ray_primes _).1,Nat.prime_two,(ray_primes _).1,
        by have h := (ray_primes i).2; omega,Or.inr ⟨rfl,by change 2*(3*rayPrime i)=3*(2*rayPrime i); ring⟩⟩

private theorem ray_stretch (j : ℕ) : 2*oddRay j ≤ oddRay (j+1) ∧ oddRay (j+1) ≤ 8*(2*oddRay j) := by
  cases j with
  | zero => decide
  | succ i =>
    obtain ⟨_,low,high⟩ := ray_step i
    change 2*(3*rayPrime i) ≤ 3*rayPrime (i+1) ∧ 3*rayPrime (i+1) ≤ 8*(2*(3*rayPrime i))
    omega

private def raySwap (n : ℕ) :=
  if evenEnd : ∃ j,n=2*oddRay j then oddRay (evenEnd.choose+1)
  else if oddEnd : ∃ j,n=oddRay (j+1) then 2*oddRay oddEnd.choose else n

private theorem ray_on_double (j : ℕ) : raySwap (2*oddRay j)=oddRay (j+1) := by
  have h : ∃ i,2*oddRay j=2*oddRay i := ⟨j,rfl⟩
  have eq := odd_ray_strict.injective (Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h.choose_spec)
  rw [raySwap,dif_pos h,←eq]

private theorem ray_on_odd (j : ℕ) : raySwap (oddRay (j+1))=2*oddRay j := by
  have h : ∃ i,oddRay (j+1)=oddRay (i+1) := ⟨j,rfl⟩
  have absent : ¬∃ i,oddRay (j+1)=2*oddRay i := fun ⟨i,eq⟩ => (odd_ray_properties _).2 ⟨oddRay i,eq⟩
  have eq := Nat.succ.inj (odd_ray_strict.injective h.choose_spec)
  rw [raySwap,dif_neg absent,dif_pos h,←eq]

private theorem ray_at_unit : raySwap 1=1 := by
  have ev : ¬∃ j,1=2*oddRay j := fun ⟨j,h⟩ => by omega
  have od : ¬∃ j,1=oddRay (j+1) := fun ⟨j,h⟩ => (odd_ray_strict (Nat.succ_pos j)).ne h
  rw [raySwap,dif_neg ev,dif_neg od]

private abbrev onRay (t : ℕ) := ∃ j,t=oddRay j
private def layer (b : Bool) (t : ℕ) := if b then 2*t else t

private theorem squarefree_double {t : ℕ} (sq : Squarefree t) (odd : ¬2 ∣ t) : Squarefree (2*t) :=
  Nat.squarefree_mul_iff.mpr ⟨Nat.prime_two.coprime_iff_not_dvd.mpr odd,Nat.prime_two.squarefree,sq⟩

private theorem double_edge {n m : ℕ} (edge : GlobalDyadicOneTwoRel n m)
    (odd : ¬2 ∣ n) (odd' : ¬2 ∣ m) : GlobalDyadicOneTwoRel (2*n) (2*m) := by
  obtain ⟨sq,sq',sign,c,p,q,r,pr,qr,rr,order,pair⟩ := edge
  refine ⟨squarefree_double sq odd,squarefree_double sq' odd',?_,2*c,p,q,r,pr,qr,rr,order,?_⟩
  · rw [isMultiplicative_moebius.map_mul_of_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr odd),
      isMultiplicative_moebius.map_mul_of_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr odd'),sign,mul_neg]
  · rcases pair with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inl ⟨by rw [a,Nat.mul_assoc],by rw [b,Nat.mul_assoc]⟩
    · exact Or.inr ⟨by rw [a,Nat.mul_assoc],by rw [b,Nat.mul_assoc]⟩

private theorem edge_to_double {n : ℕ} (sq : Squarefree n) (odd : ¬2 ∣ n) (np : 1<n) :
    GlobalDyadicOneTwoRel n (2*n) := by
  let p := n.minFac
  have prime : p.Prime := Nat.minFac_prime np.ne'
  have dvd : p ∣ n := Nat.minFac_dvd _
  have order : 2<p := lt_of_le_of_ne prime.two_le (fun e => odd (by rwa [e]))
  have decomp : n/p*p=n := Nat.div_mul_cancel dvd
  refine ⟨sq,squarefree_double sq odd,?_,n/p,p,2,p,prime,Nat.prime_two,prime,order,Or.inl ⟨decomp.symm,?_⟩⟩
  · rw [isMultiplicative_moebius.map_mul_of_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr odd),moebius_apply_prime Nat.prime_two]
    ring
  · calc 2*n = 2*(n/p*p) := congrArg (2*·) decomp.symm
         _ = _ := by ring

private def oddTable (F : ℕ → ℕ) (b : Bool) (t : ℕ) :=
  if onRay t then raySwap (layer b t)
  else if F t=t ∨ onRay (F t) then layer (!b) t else layer b (F t)

private def completedTable (F : ℕ → ℕ) (n : ℕ) :=
  if Squarefree n then
    if 2 ∣ n then oddTable F true (n/2) else oddTable F false n
  else n

private theorem completed_on_layer (F : ℕ → ℕ) (b : Bool) {t : ℕ}
    (sq : Squarefree t) (odd : ¬2 ∣ t) : completedTable F (layer b t)=oddTable F b t := by
  cases b
  · simp [completedTable,layer,sq,odd]
  · have dvd : 2 ∣ 2*t := ⟨t,rfl⟩
    simp [completedTable,layer,squarefree_double sq odd,dvd]

private theorem on_ray_double (F : ℕ → ℕ) (j : ℕ) :
    completedTable F (2*oddRay j)=oddRay (j+1) := by
  rw [show 2*oddRay j=layer true (oddRay j) from rfl,
    completed_on_layer _ _ (odd_ray_properties _).1 (odd_ray_properties _).2,oddTable,if_pos (show onRay (oddRay j) from ⟨j,rfl⟩)]
  exact ray_on_double j

private theorem on_ray_odd (F : ℕ → ℕ) (j : ℕ) :
    completedTable F (oddRay (j+1))=2*oddRay j := by
  rw [show oddRay (j+1)=layer false (oddRay (j+1)) from rfl,
    completed_on_layer _ _ (odd_ray_properties _).1 (odd_ray_properties _).2,oddTable,if_pos (show onRay (oddRay (j+1)) from ⟨j+1,rfl⟩)]
  exact ray_on_odd j

private theorem on_ray_unit (F : ℕ → ℕ) : completedTable F 1=1 := by
  change completedTable F (layer false 1)=1
  rw [completed_on_layer _ _ squarefree_one (by decide),oddTable,if_pos (show onRay 1 from ⟨0,rfl⟩)]
  exact ray_at_unit

private theorem endpoints_differ {n m : ℕ} (edge : GlobalDyadicOneTwoRel n m) : m ≠ n := by
  rintro rfl
  have sign := edge.2.2.1
  rcases moebius_eq_one_or_neg_one_of_squarefree edge.1 with pos | neg <;> omega

private theorem canonical_layer {n : ℕ} (sq : Squarefree n) :
    ∃ (b : Bool) (t : ℕ),n=layer b t ∧ Squarefree t ∧ ¬2 ∣ t := by
  by_cases even : 2 ∣ n
  · obtain ⟨t,rfl⟩ := even
    obtain ⟨cop,_,sq'⟩ := Nat.squarefree_mul_iff.mp sq
    exact ⟨true,t,rfl,sq',Nat.prime_two.coprime_iff_not_dvd.mp cop⟩
  · exact ⟨false,n,rfl,sq,even⟩

private abbrev seedLaw (F : ℕ → ℕ) := ∀ n,Squarefree n → F (F n)=n ∧
  (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ (F n).gcd 2=n.gcd 2 ∧ F n ≤ 2*n

private theorem seed_odd {F : ℕ → ℕ} (law : seedLaw F) {t : ℕ} (sq : Squarefree t)
    (odd : ¬2 ∣ t) : ¬2 ∣ F t := by
  intro dvd
  have g := Nat.dvd_gcd dvd (dvd_refl 2)
  rw [(law t sq).2.2.1] at g
  exact odd (g.trans (Nat.gcd_dvd_left ..))

private theorem completed_law {F : ℕ → ℕ} (law : seedLaw F) (n : ℕ) :
    let G := completedTable F
    G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (Squarefree n → 1<n → G n ≠ n) ∧ G n ≤ 8*n := by
  let G := completedTable F
  change G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧ _ ∧ _
  by_cases sq : Squarefree n
  · obtain ⟨b,t,hn,st,odd⟩ := canonical_layer sq
    subst n
    have pair {m z : ℕ} (first : G m=z) (back : G z=m) (edge : GlobalDyadicOneTwoRel m z) (width : z ≤ 8*m) :
        G (G m)=m ∧ (G m=m ∨ GlobalDyadicOneTwoRel m (G m)) ∧ (Squarefree m → 1< m → G m ≠ m) ∧ G m ≤ 8*m := by
      rw [first]; exact ⟨back,Or.inr edge,fun _ _ => endpoints_differ edge,width⟩
    by_cases ray : onRay t
    · obtain ⟨j,rfl⟩ := ray
      cases b with
      | true => exact pair (on_ray_double F j) (on_ray_odd F j) (ray_edge j) (ray_stretch j).2
      | false =>
        cases j with
        | zero =>
          change G (G 1)=1 ∧ (G 1=1 ∨ GlobalDyadicOneTwoRel 1 (G 1)) ∧
            (Squarefree 1 → 1<1 → G 1 ≠ 1) ∧ G 1 ≤ 8*1
          have one : G 1=1 := on_ray_unit F
          simp [one]
        | succ j =>
          exact pair (on_ray_odd F j) (on_ray_double F j) (ray_edge j).symm
            ((ray_stretch j).1.trans (Nat.le_mul_of_pos_left _ (by decide : 0<8)))
    have large : 1<t := by
      have pos := Nat.pos_of_ne_zero st.ne_zero
      have unit : t ≠ 1 := fun eq => ray ⟨0,eq⟩
      omega
    by_cases replace : F t=t ∨ onRay (F t)
    · have move (v : Bool) : G (layer v t)=layer (!v) t := by
        rw [show G=completedTable F from rfl,completed_on_layer _ _ st odd,oddTable,if_neg ray,if_pos replace]
      cases b with
      | false => exact pair (move false) (move true) (edge_to_double st odd large) (by change 2*t ≤ 8*t; omega)
      | true => exact pair (move true) (move false) (edge_to_double st odd large).symm (by change t ≤ 8*(2*t); omega)
    · obtain ⟨back,edge,_,bound⟩ := law t st
      have diff : F t ≠ t := fun same => replace (Or.inl same)
      have free : ¬onRay (F t) := fun h => replace (Or.inr h)
      have actual := edge.resolve_left diff
      have odd' := seed_odd law st odd
      have forward (v : Bool) : G (layer v t)=layer v (F t) := by
        rw [show G=completedTable F from rfl,completed_on_layer _ _ st odd,oddTable,if_neg ray,if_neg replace]
      have returnMap (v : Bool) : G (layer v (F t))=layer v t := by
        rw [show G=completedTable F from rfl,completed_on_layer _ _ actual.2.1 odd',oddTable,if_neg free,back,
          if_neg (not_or.mpr ⟨Ne.symm diff,ray⟩)]
      cases b with
      | false => exact pair (forward false) (returnMap false) actual (by change F t ≤ 8*t; omega)
      | true =>
        exact pair (forward true) (returnMap true) (double_edge actual odd odd')
          (by change 2*F t ≤ 8*(2*t); omega)
  · have fixed : G n=n := if_neg sq
    exact ⟨(congrArg G fixed).trans fixed,Or.inl fixed,fun h => (sq h).elim,
      fixed.le.trans (Nat.le_mul_of_pos_left n (by decide : 0<8))⟩

/-- The reserved odd ray meets an initial interval at most logarithmically often. -/
private theorem count_on_odd_ray (X : ℕ) :
    ((Icc 1 X).filter onRay).card ≤ Nat.log 2 X+1 := by
  have grow (j : ℕ) : 2^j ≤ oddRay j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [pow_succ,Nat.mul_comm]
      exact (Nat.mul_le_mul_left 2 ih).trans (ray_stretch j).1
  have covered : (Icc 1 X).filter onRay ⊆ (range (Nat.log 2 X+1)).image oddRay := by
    intro t ht
    obtain ⟨inside,j,rfl⟩ := mem_filter.mp ht
    exact mem_image.mpr ⟨j,mem_range.mpr (Nat.lt_succ_of_le
      (Nat.le_log_of_pow_le (by decide) ((grow j).trans (mem_Icc.mp inside).2))),rfl⟩
  exact (card_le_card covered).trans (card_image_le.trans (card_range _).le)

private def rayCover (X : ℕ) := (range ((2*X).sqrt+1)).image oddRay

private theorem ray_in_cover {t X : ℕ} (hit : onRay t) (size : t ≤ X) : t ∈ rayCover X := by
  have linear (j : ℕ) : j+1 ≤ oddRay j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans_lt (odd_ray_strict (Nat.lt_succ_self _))
  have quadratic (j : ℕ) : j*j ≤ 2*oddRay j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => nlinarith only [ih,linear j,(ray_stretch j).1]
  obtain ⟨j,rfl⟩ := hit
  exact mem_image.mpr ⟨j,mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt.mpr
    ((quadratic j).trans (Nat.mul_le_mul_left 2 size)))),rfl⟩

private def exceptionalRows (F : ℕ → ℕ) (X : ℕ) :=
  (squarefreeOf (Icc 1 X)).filter (fun t => F t=t ∨ onRay t ∨ onRay (F t))

private theorem number_of_exceptional_rows {F : ℕ → ℕ} (law : seedLaw F) (X : ℕ) :
    (exceptionalRows F X).card ≤ (prefixUnpaid F X).card+2*(min (4*X).sqrt (Nat.log 2 (2*X))+1) := by
  let R := (Icc 1 (2*X)).filter onRay
  let S := (squarefreeOf (Icc 1 X)).filter (fun t => onRay (F t))
  have sub : exceptionalRows F X ⊆ (prefixUnpaid F X ∪ R) ∪ S := by
    intro t ht
    obtain ⟨mem,ob⟩ := mem_filter.mp ht
    have size := (mem_Icc.mp (mem_filter.mp mem).1).2
    rcases ob with fixed | ray | imageRay
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,Or.inl fixed⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp mem).1).1,by omega⟩,ray⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem,imageRay⟩)
  have inj : S.card ≤ R.card := by
    apply card_le_card_of_injOn F
    · intro t ht
      obtain ⟨mem,hit⟩ := mem_filter.mp ht
      obtain ⟨interval,sq⟩ := mem_filter.mp mem
      have imageSq := (law t sq).2.1.elim (fun h => by rw [h]; exact sq) (fun rel => rel.2.1)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero imageSq.ne_zero,
        (law t sq).2.2.2.trans (Nat.mul_le_mul_left 2 (mem_Icc.mp interval).2)⟩,hit⟩
    · intro a ha b hb eq
      rw [←(law a (mem_filter.mp (mem_filter.mp ha).1).2).1,
        ←(law b (mem_filter.mp (mem_filter.mp hb).1).2).1,eq]
  have cover : R ⊆ rayCover (2*X) := fun t ht => ray_in_cover (mem_filter.mp ht).2 (mem_Icc.mp (mem_filter.mp ht).1).2
  have bound : R.card ≤ (4*X).sqrt+1 := (card_le_card cover).trans ((card_image_le.trans (card_range _).le).trans_eq
    (by change (2*(2*X)).sqrt+1=(4*X).sqrt+1; rw [←Nat.mul_assoc]))
  have logBound : R.card ≤ Nat.log 2 (2*X)+1 := count_on_odd_ray (2*X)
  have cost := (card_le_card sub).trans (card_union_le ..)
  have union := card_union_le (prefixUnpaid F X) R
  omega

/-- Vertices with an exchange longer than a prescribed fraction
of their own height. -/
def longRelativeExchanges (G : ℕ → ℕ) (δ : ℝ) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun (n : ℕ) => δ*(n:ℝ) < |(G n:ℝ)-n|)

private theorem long_exchanges_from_odd_rows {F : ℕ → ℕ} {δ : ℝ} (dp : 0<δ) (N X : ℕ)
    (near : ∀ t,N ≤ t → Squarefree t → |(F t:ℝ)-t| ≤ δ*t) :
    (longRelativeExchanges (completedTable F) δ X).card ≤ 2*((exceptionalRows F X).card+N) := by
  let E := exceptionalRows F X ∪ range N
  have sub : longRelativeExchanges (completedTable F) δ X ⊆ E ∪ E.image (2*·) := by
    intro n hn
    obtain ⟨interval,far⟩ := mem_filter.mp hn
    by_cases sn : Squarefree n
    · obtain ⟨b,t,rfl,st,odd⟩ := canonical_layer sn
      have ts : t ≤ X := (show t ≤ layer b t by cases b <;> simp [layer] <;> omega).trans (mem_Icc.mp interval).2
      have member : t ∈ E := by
        by_contra out
        have earlier : N ≤ t := le_of_not_gt (fun h => out (mem_union_right _ (mem_range.mpr h)))
        have safe : ¬(F t=t ∨ onRay t ∨ onRay (F t)) := fun h =>
          out (mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero st.ne_zero,ts⟩,st⟩,h⟩))
        have kept : ¬onRay t := fun h => safe (Or.inr (Or.inl h))
        have paired : ¬(F t=t ∨ onRay (F t)) := fun h => safe (h.elim Or.inl (fun z => Or.inr (Or.inr z)))
        rw [completed_on_layer _ _ st odd,oddTable,if_neg kept,if_neg paired] at far
        have close := near t earlier st
        cases b with
        | false => exact (not_lt_of_ge close) far
        | true =>
          change δ*((2*t:ℕ):ℝ) < |((2*F t:ℕ):ℝ)-((2*t:ℕ):ℝ)| at far
          rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,←mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at far
          linarith only [far,close]
      cases b with
      | false => exact mem_union_left _ member
      | true => exact mem_union_right _ (mem_image.mpr ⟨t,member,rfl⟩)
    · have same : completedTable F n=n := if_neg sn
      rw [same,sub_self,abs_zero] at far
      exact (not_lt_of_ge (mul_nonneg dp.le (Nat.cast_nonneg _)) far).elim
  have cover := (card_le_card sub).trans (card_union_le ..)
  have doubled : (E.image (2*·)).card ≤ E.card := card_image_le
  have size := (card_union_le (exceptionalRows F X) (range N)).trans_eq (by rw [card_range])
  change E.card ≤ _ at size
  omega

private theorem sublinear_ray_count {h : ℝ} (hp : 0<h) :
    ∀ᶠ X : ℕ in atTop,(((4*X).sqrt:ℕ):ℝ) ≤ h*X := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (4/h^2)] with X big
  have x0 := Nat.cast_nonneg (α := ℝ) X
  have room := (div_le_iff₀ (sq_pos_of_pos hp)).mp big
  have sq : (((4*X).sqrt:ℕ):ℝ)^2 ≤ 4*(X:ℝ) := by exact_mod_cast Nat.sqrt_le' (4*X)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hp.le x0)).mp
  nlinarith only [sq,mul_le_mul_of_nonneg_right room x0]

private theorem few_long_exchanges {F : ℕ → ℕ} (law : seedLaw F)
    (dense : ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid F X).card:ℝ) ≤ ε*X ∧
      (Squarefree X → |(F X:ℝ)-X| ≤ ε*X)) {δ η : ℝ} (dp : 0<δ) (ep : 0<η) :
    ∀ᶠ X : ℕ in atTop,((longRelativeExchanges (completedTable F) δ X).card:ℝ) ≤ η*X := by
  obtain ⟨N,near⟩ := eventually_atTop.mp ((dense δ dp).mono (fun _ h => h.2))
  let h := η/8
  have hp : 0<h := div_pos ep (by norm_num)
  filter_upwards [dense h hp,sublinear_ray_count hp,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (((N:ℝ)+2)/h)] with X paid root late
  have small := (number_of_exceptional_rows law X).trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (min_le_left _ _) 1)) _)
  have rows := (Nat.cast_le (α := ℝ)).mpr small
  have far := (Nat.cast_le (α := ℝ)).mpr (long_exchanges_from_odd_rows dp N X near)
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at rows far
  have bound := (div_le_iff₀ hp).mp late
  dsimp only [h] at *
  linarith only [rows,far,paid.1,root,bound]

private theorem unpaid_of_few_long_exchanges {G : ℕ → ℕ}
    (perfect : ∀ n,Squarefree n → 1<n → G n ≠ n)
    (rare : ∀ δ η : ℝ,0<δ → 0<η → ∀ᶠ X : ℕ in atTop,((longRelativeExchanges G δ X).card:ℝ) ≤ η*X)
    {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X := by
  let h := ε/4
  have hp : 0<h := div_pos ep (by norm_num)
  filter_upwards [rare h h hp hp,tendsto_natCast_atTop_atTop.eventually_ge_atTop (2/h)] with X count big
  let d := ⌈h*(X:ℝ)⌉₊
  let E := longRelativeExchanges G h X
  have sub : prefixUnpaid G X ⊆ (insert 1 E) ∪ Ioc (X-d) X := by
    intro n hn
    obtain ⟨mem,why⟩ := mem_filter.mp hn
    obtain ⟨inside,sq⟩ := mem_filter.mp mem
    obtain ⟨np,nx⟩ := mem_Icc.mp inside
    rcases why with fixed | outside
    · have one : n=1 := by by_contra bad; exact perfect n sq (by omega) fixed
      exact mem_union_left _ (mem_insert.mpr (Or.inl one))
    · by_cases paid : n ∈ E
      · exact mem_union_left _ (mem_insert.mpr (Or.inr paid))
      have short := le_of_not_gt (fun bad => paid (mem_filter.mpr ⟨inside,bad⟩))
      have delta := ((abs_le.mp short).2.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr nx) hp.le)).trans (Nat.le_ceil _)
      have cross : (X:ℝ)<G n := Nat.cast_lt.mpr outside
      have high : X<n+d := by exact_mod_cast (show (X:ℝ)<(n:ℝ)+d by linarith only [delta,cross])
      exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,nx⟩)
  have strip : (Ioc (X-d) X).card ≤ d := by rw [Nat.card_Ioc]; omega
  have costs := (card_le_card sub).trans (card_union_le ..)
  have ins := card_insert_le 1 E
  have total : ((prefixUnpaid G X).card:ℝ) ≤ (E.card:ℝ)+1+d := by
    exact_mod_cast (show (prefixUnpaid G X).card ≤ E.card+1+d by omega)
  have round : (d:ℝ)<h*X+1 := Nat.ceil_lt_add_one (mul_nonneg hp.le (Nat.cast_nonneg X))
  have room := (div_le_iff₀ hp).mp big
  change (E.card:ℝ) ≤ h*X at count
  dsimp only [h] at *
  linarith only [total,count,round,room]

/-- Every squarefree nonunit moves by a genuine one-to-two prime
exchange with multiplicative stretch at most eight. At every positive
relative length the exceptional population has density zero, as does
the population unpaid at each sharp prefix. -/
theorem perfect_restricted_matching_with_bounded_stretch :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧ (∀ n,G n ≤ 8*n) ∧
      (∀ δ η : ℝ,0<δ → 0<η → ∀ᶠ X : ℕ in atTop,((longRelativeExchanges G δ X).card:ℝ) ≤ η*X) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X := by
  obtain ⟨F,seed,dense⟩ := density_one_matching_preserving_two
  let G := completedTable F
  have pair := completed_law seed
  have perfect (n : ℕ) := (pair n).2.2.1
  have rare (δ η : ℝ) (dp : 0<δ) (ep : 0<η) := few_long_exchanges seed dense dp ep
  exact ⟨G,fun n => (pair n).1,fun n => (pair n).2.1,perfect,fun n => (pair n).2.2.2,rare,
    fun _ ep => unpaid_of_few_long_exchanges perfect rare ep⟩

end GaloisForLFunctions.RestrictedFactorizationCalculus
