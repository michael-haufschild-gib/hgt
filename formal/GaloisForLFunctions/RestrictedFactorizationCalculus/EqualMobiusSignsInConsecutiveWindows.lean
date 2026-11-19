import GaloisForLFunctions.RestrictedFactorizationCalculus.SelectingMobiusSignsByDilatingOneInterval
import GaloisForLFunctions.QuantitativeFactorizationMatching.AllFiniteLayersCellMatching

/-!
# Equal Möbius signs in consecutive windows of fixed length

Given k, windows with exactly k nonzero entries all of either prescribed
sign have positive lower natural density. Dilations select a sign class
of the marked inputs, and an extra prime reverses all the signs.
-/

noncomputable section

open Filter Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Exactly k nonzero entries in the length-H window, all of sign e. -/
def equalSignWindow (H k : ℕ) (e : ℤ) (x : ℕ) : Prop :=
  ((Icc 1 H).filter (fun r => μ (x+r) ≠ 0)).card=k ∧ ∀ r ∈ Icc 1 H,μ (x+r)=0 ∨ μ (x+r)=e

private theorem many_labels (m : ℕ) : ∃ P : Finset ℕ,P.card=m ∧ ∀ p ∈ P,p.Prime := by
  induction m with
  | zero => exact ⟨∅,rfl,by simp⟩
  | succ m ih =>
    obtain ⟨P,hP,prime⟩ := ih
    obtain ⟨p,big,hp⟩ := Nat.exists_infinite_primes (P.sup id+1)
    have out : p ∉ P := fun h => (Nat.not_succ_le_self _) (big.trans (Finset.le_sup (f := id) h))
    refine ⟨insert p P,by rw [card_insert_of_notMem out,hP],?_⟩
    intro q hq
    exact (mem_insert.mp hq).elim (fun h => h ▸ hp) (prime q)

private theorem select_same_sign (P : Finset ℕ) {k x : ℕ} (many : 2*k ≤ P.card)
    (live : ∀ p ∈ P,Squarefree (x+p)) :
    ∃ E ⊆ P,E.card=k ∧ ∃ e : ℤ,(e=1 ∨ e= -1) ∧ ∀ p ∈ E,μ (x+p)=e := by
  let pos := P.filter (fun p => μ (x+p)=1)
  let neg := P.filter (fun p => ¬μ (x+p)=1)
  have total : pos.card+neg.card=P.card := card_filter_add_card_filter_not ..
  by_cases h : k ≤ pos.card
  · obtain ⟨E,sub,card⟩ := exists_subset_card_eq h
    exact ⟨E,sub.trans (filter_subset ..),card,1,Or.inl rfl,fun p hp => (mem_filter.mp (sub hp)).2⟩
  · obtain ⟨E,sub,card⟩ := exists_subset_card_eq (by omega : k ≤ neg.card)
    refine ⟨E,sub.trans (filter_subset ..),card,-1,Or.inr rfl,?_⟩
    intro p hp
    obtain ⟨hP,hn⟩ := mem_filter.mp (sub hp)
    have nz := squarefree_iff_moebius_ne_zero.mp (live p hP)
    rcases moebius_eq_or (x+p) with hh | hh | hh <;> omega

private abbrev primeProduct (V : Finset ℕ) := ∏ p ∈ V,p

private theorem selector (P E : Finset ℕ) {z : ℕ} (hz : z.Prime) (out : z ∉ P)
    (prime : ∀ p ∈ P,p.Prime) {e σ : ℤ} (he : e=1 ∨ e= -1) (hσ : σ=1 ∨ σ= -1) :
    ∃ t : ℕ,0<t ∧ t ≤ primeProduct (insert z P) ∧ μ t*e=σ ∧
      ∀ p ∈ P,(¬p ∣ t ↔ p ∈ E) := by
  let V := P \ E
  let t := primeProduct V
  have pv (p : ℕ) (hp : p ∈ V) := prime p (mem_sdiff.mp hp).1
  obtain ⟨sq,supp,ht⟩ := squarefree_and_primeFactors_prod_primes pv
  have htP : t ∣ primeProduct P := Finset.prod_dvd_prod_of_subset V P id sdiff_subset
  have base := Nat.le_of_dvd (squarefree_and_primeFactors_prod_primes prime).2.2 htP
  have flip : primeProduct (insert z P)=z*primeProduct P := prod_insert out
  have read (p : ℕ) (hp : p ∈ P) : ¬p ∣ t ↔ p ∈ E := by
    have h : p ∣ t ↔ p ∈ V := by
      rw [←supp]; exact ⟨fun hd => Nat.mem_primeFactors.mpr ⟨prime p hp,hd,ht.ne'⟩,Nat.dvd_of_mem_primeFactors⟩
    constructor
    · intro absent
      exact by_contra (fun no => absent (h.mpr (mem_sdiff.mpr ⟨hp,no⟩)))
    · intro kept dvd
      exact (mem_sdiff.mp (h.mp dvd)).2 kept
  have notz : ¬z ∣ t := by
    intro h
    have mem : z ∈ t.primeFactors := Nat.mem_primeFactors.mpr ⟨hz,h,ht.ne'⟩
    change t.primeFactors=V at supp
    rw [supp] at mem
    exact out (mem_sdiff.mp mem).1
  have one : μ t=1 ∨ μ t= -1 := by
    exact (moebius_eq_or t).resolve_left (squarefree_iff_moebius_ne_zero.mp sq)
  by_cases same : μ t*e=σ
  · refine ⟨t,ht,base.trans ?_,same,read⟩
    rw [flip]; exact Nat.le_mul_of_pos_left _ hz.pos
  · refine ⟨z*t,Nat.mul_pos hz.pos ht,flip ▸ Nat.mul_le_mul_left z base,?_,?_⟩
    · rw [isMultiplicative_moebius.map_mul_of_coprime (hz.coprime_iff_not_dvd.mpr notz),moebius_apply_prime hz]
      rcases he with rfl | rfl <;> rcases hσ with rfl | rfl <;> rcases one with h | h <;> simp_all
    · intro p hp
      have pd : ¬p ∣ z := fun h => out (((Nat.prime_dvd_prime_iff_eq (prime p hp) hz).mp h) ▸ hp)
      simpa only [(prime p hp).dvd_mul,pd,false_or] using read p hp

private theorem read_equal_window {P : Finset ℕ} {H T k x : ℕ} {e σ : ℤ} {E : Finset ℕ}
    (prime : ∀ p ∈ P,p.Prime) (sub : E ⊆ P) (card : E.card=k) (sign : ∀ p ∈ E,μ (x+p)=e)
    (hσ : σ=1 ∨ σ= -1) {t : ℕ} (ht : 0<t) (htT : t ≤ T) (hH : T*(P.sup id) ≤ H)
    (mult : μ t*e=σ) (test : ∀ p ∈ P,(¬p ∣ t ↔ p ∈ E))
    (read : ∀ r ∈ Icc 1 H,μ (t*x+r)=markedMobiusReading P t x r) : equalSignWindow H k σ (t*x) := by
  have inside (p : ℕ) (hp : p ∈ E) : t*p ∈ Icc 1 H := mem_Icc.mpr
    ⟨Nat.mul_pos ht (prime p (sub hp)).pos,(Nat.mul_le_mul htT (Finset.le_sup (f := id) (sub hp))).trans hH⟩
  have live (p : ℕ) (hp : p ∈ E) : μ (t*x+t*p)=σ := by
    rw [read _ (inside p hp),markedMobiusReading]
    rw [Nat.mul_div_cancel_left _ ht,if_pos ⟨dvd_mul_right ..,sub hp,(test p (sub hp)).2 hp⟩,sign p hp,mult]
  have dead (r : ℕ) (hr : r ∈ Icc 1 H) (absent : r ∉ E.image (t*·)) : μ (t*x+r)=0 := by
    rw [read _ hr,markedMobiusReading,if_neg]
    rintro ⟨dvd,mark,allowed⟩
    exact absent (mem_image.mpr ⟨r/t,(test _ mark).1 allowed,Nat.mul_div_cancel' dvd⟩)
  have eq : (Icc 1 H).filter (fun r => μ (t*x+r) ≠ 0)=E.image (t*·) := by
    ext r
    constructor
    · rintro h
      exact by_contra (fun absent => (mem_filter.mp h).2 (dead r (mem_filter.mp h).1 absent))
    · rintro h
      obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨inside p hp,by rw [live p hp]; rcases hσ with rfl | rfl <;> decide⟩
  constructor
  · rw [eq,card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left ht h),card]
  intro r hr
  by_cases h : r ∈ E.image (t*·)
  · obtain ⟨p,hp,rfl⟩ := mem_image.mp h
    exact Or.inr (live p hp)
  · exact Or.inl (dead r hr h)

/-- Both orientations of a window containing exactly k nonzero equal
signs occur with positive lower natural density at the same length. -/
theorem positive_lower_density_of_equal_sign_windows (k : ℕ) :
    ∃ H C : ℕ,0<H ∧ 0<C ∧ ∀ σ : ℤ,σ=1 ∨ σ= -1 →
      ∀ᶠ X : ℕ in atTop,X ≤ C*((Icc 1 X).filter (equalSignWindow H k σ)).card := by
  obtain ⟨P,hcard,prime⟩ := many_labels (2*k)
  obtain ⟨z,big,hz⟩ := Nat.exists_infinite_primes (P.sup id+1)
  have out : z ∉ P := fun h => (Nat.not_succ_le_self _) (big.trans (Finset.le_sup (f := id) h))
  let T := primeProduct (insert z P)
  have hT : 0<T := prod_pos (fun p hp => (mem_insert.mp hp).elim (fun e => e ▸ hz.pos) (fun h => (prime p h).pos))
  let H := T*(P.sup id)+1
  obtain ⟨D,b,hD,read,occurs⟩ := all_bounded_dilations_of_one_mobius_window P prime T H
  let A := T*(D+b+1)
  have hA : 0<A := Nat.mul_pos hT (Nat.succ_pos _)
  refine ⟨H,4*A*T,Nat.succ_pos _,by positivity,?_⟩
  intro σ hσ
  obtain ⟨N₀,goodFrom⟩ := eventually_atTop.mp occurs
  filter_upwards [eventually_ge_atTop (A*(N₀+2))] with X hx
  let N := X/A
  have late : N₀+2 ≤ N := (Nat.le_div_iff_mul_le hA).mpr (by rwa [Nat.mul_comm])
  let good := (Icc 1 N).filter (fun n => ∀ p ∈ P,Squarefree (D*n+b+p))
  let hits := (Icc 1 X).filter (equalSignWindow H k σ)
  let row := fun t => (Icc 1 N).filter (fun n => equalSignWindow H k σ (t*(D*n+b)))
  have enough : N ≤ 2*good.card := by
    have h := goodFrom N (by omega)
    change (N:ℝ)/2 ≤ good.card at h
    exact_mod_cast (show (N:ℝ) ≤ 2*good.card by linarith only [h])
  have sub : good ⊆ (Icc 1 T).biUnion row := by
    intro n hn
    obtain ⟨hi,live⟩ := mem_filter.mp hn
    obtain ⟨E,sub,card,e,he,same⟩ := select_same_sign P hcard.ge live
    obtain ⟨t,ht,htT,mult,test⟩ := selector P E hz out prime he hσ
    exact mem_biUnion.mpr ⟨t,mem_Icc.mpr ⟨ht,htT⟩,mem_filter.mpr ⟨hi,
      read_equal_window prime sub card same hσ ht htT (Nat.le_succ _) mult test (read n t ht htT)⟩⟩
  have count (t : ℕ) (ht : t ∈ Icc 1 T) : (row t).card ≤ hits.card := by
    have t0 := (mem_Icc.mp ht).1
    apply card_le_card_of_injOn (fun n => t*(D*n+b))
    · intro n hn
      obtain ⟨hI,pure⟩ := mem_filter.mp hn
      obtain ⟨n0,nN⟩ := mem_Icc.mp hI
      have bound : D*n+b ≤ (D+b+1)*n := by nlinarith only [Nat.mul_le_mul_left b n0]
      have limit : t*(D*n+b) ≤ X := calc
        t*(D*n+b) ≤ T*((D+b+1)*n) := Nat.mul_le_mul (mem_Icc.mp ht).2 bound
        _ = A*n := (Nat.mul_assoc ..).symm
        _ ≤ A*N := Nat.mul_le_mul_left _ nN
        _ ≤ X := Nat.mul_div_le X A
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos t0 (Nat.add_pos_left (Nat.mul_pos hD n0) _),limit⟩,pure⟩
    · intro m _ n _ eq
      exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left t0 eq))
  have mass := (card_le_card sub).trans ((card_biUnion_le ..).trans (sum_le_sum count))
  simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at mass
  have lower : X ≤ 2*(A*N) := by
    have hi := Nat.mod_lt X hA
    have rem := Nat.mod_add_div X A
    change X%A+A*N=X at rem
    have grow := Nat.mul_le_mul_left A (show 1 ≤ N by omega)
    omega
  have star : A*N ≤ A*(2*(T*hits.card)) := Nat.mul_le_mul_left _ (enough.trans (Nat.mul_le_mul_left 2 mass))
  exact lower.trans ((Nat.mul_le_mul_left 2 star).trans_eq (by ring))

#print axioms positive_lower_density_of_equal_sign_windows

end GaloisForLFunctions.RestrictedFactorizationCalculus
