import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# Two sharp cutoffs around a smooth vertex

A fixed vertex or an edge leaving an interval is charged to one endpoint
of the interval. Products of many primes of comparable size cannot move a
short distance: the common cofactor alone is too large. Counting them in
disjoint cells gives a lower bound uniform over all global switches.
-/

noncomputable section

open Finset RHTower
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Each fixed vertex or exit from a prescribed set in an interval contributes
to the unpaid population at one of its two sharp endpoints. -/
theorem window_debt_le_two_prefixes {F : ℕ → ℕ}
    (hF : ∀ n, Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    {a b : ℕ} {S : Finset ℕ} (hS : ∀ n ∈ S,n ∈ Ioc a b ∧ Squarefree n ∧
      (F n=n ∨ F n ∉ Ioc a b)) :
    S.card ≤ (prefixUnpaid F a).card + (prefixUnpaid F b).card := by
  let D := S.filter (fun n => F n ≤ a)
  have low : D.card ≤ (prefixUnpaid F a).card := by
    apply card_le_card_of_injOn F
    · intro n hn
      obtain ⟨h,hle⟩ := mem_filter.mp hn
      obtain ⟨hI,hs,_⟩ := hS n h
      obtain ⟨back,hfix | edge⟩ := hF n hs
      · exact ((mem_Ioc.mp hI).1.not_ge (hfix ▸ hle)).elim
      · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero edge.2.1.ne_zero,hle⟩,
          edge.2.1⟩,Or.inr (by rw [back]; exact (mem_Ioc.mp hI).1)⟩
    · intro n hn m hm e
      have hn' := (hF n (hS n (mem_filter.mp hn).1).2.1).1
      have hm' := (hF m (hS m (mem_filter.mp hm).1).2.1).1
      exact hn'.symm.trans ((congrArg F e).trans hm')
  have high : S \ D ⊆ prefixUnpaid F b := by
    intro n hn
    obtain ⟨hm,hno⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hI,hs,exits⟩ := hS n hm
    have hab := mem_Ioc.mp hI
    have hlo : a < F n := Nat.lt_of_not_ge (fun h => hno (mem_filter.mpr ⟨hm,h⟩))
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le a |>.trans_lt hab.1,hab.2⟩,hs⟩,?_⟩
    exact exits.imp_right fun h => Nat.lt_of_not_ge (fun hh => h (mem_Ioc.mpr ⟨hlo,hh⟩))
  have hdis := card_sdiff_add_card_eq_card (show D ⊆ S from filter_subset _ _)
  have hh := card_le_card high
  omega

private def octaveProducts (t k : ℕ) :=
  ((windowPrimes (2*t) (4*t)).powersetCard k).image (fun s => ∏ p ∈ s,p)

private theorem product_facts {t k n : ℕ} (hn : n ∈ octaveProducts t k) :
    Squarefree n ∧ (2*t)^k ≤ n ∧ n ≤ (4*t)^k ∧ ∀ p : ℕ,p.Prime → p ∣ n → p ≤ 4*t := by
  obtain ⟨s,hs,rfl⟩ := mem_image.mp hn
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hs
  have facts {p : ℕ} (hp : p ∈ s) := (mem_windowPrimes (by positivity) (by positivity)).1 (hsub hp)
  have hl (p : ℕ) (hp : p ∈ s) : 2*t ≤ p := by exact_mod_cast (facts hp).2.1.le
  have hu (p : ℕ) (hp : p ∈ s) : p ≤ 4*t := by exact_mod_cast (facts hp).2.2
  have hs' (p : ℕ) (hp : p ∈ s) := (facts hp).1
  refine ⟨_root_.Sieve.prodDistinctPrimes_squarefree s hs',?_,?_,?_⟩
  · simpa only [prod_const,hcard] using prod_le_prod' hl
  · simpa only [prod_const,hcard] using prod_le_prod' hu
  · intro p hp hd
    obtain ⟨q,hq,he⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).1 hd
    exact ((Nat.prime_dvd_prime_iff_eq hp (hs' _ hq)).1 he) ▸ hu q hq

private theorem product_count (t k : ℕ) :
    (octaveProducts t k).card=(windowPrimes (2*t) (4*t)).card.choose k := by
  rw [octaveProducts,card_image_of_injOn,card_powersetCard]
  intro s hs u hu e
  have primes {s : Finset ℕ} (h : s ∈ (windowPrimes (2*t) (4*t)).powersetCard k) :
      ∀ p ∈ s,p.Prime := fun _ hp => ((mem_windowPrimes (by positivity) (by positivity)).1
        ((mem_powersetCard.mp h).1 hp)).1
  exact (Nat.primeFactors_prod (primes hs)).symm.trans
    ((congrArg Nat.primeFactors e).trans (Nat.primeFactors_prod (primes hu)))

private theorem product_cannot_move_short {d t n m : ℕ} (ht : 0<t)
    (hn : n ∈ octaveProducts t (d+4)) (h : GlobalDyadicOneTwoRel n m) :
    n+t^(d+2) ≤ m ∨ m+t^(d+2) ≤ n := by
  obtain ⟨_,hl,_,smooth⟩ := product_facts hn
  obtain ⟨_,_,_,c,p,q,r,hp,hq,hr,hqr,e⟩ := h
  have hscale : t^(d+2)*(4*t)^2 ≤ n := by
    apply le_trans _ hl
    have hc : 16 ≤ 2^(d+4) := Nat.pow_le_pow_right (by decide : 0<2) (show 4 ≤ d+4 by omega)
    calc _ = 16*(t^(d+2)*t^2) := by ring
         _ ≤ 2^(d+4)*(t^(d+2)*t^2) := Nat.mul_le_mul_right _ hc
         _ = (2*t)^(d+4) := by rw [←pow_add,mul_pow]
  have ne : p ≠ q*r := by
    intro he
    have hqp : q=p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (he ▸ Nat.dvd_mul_right q r)
    have hlt : q<q*r := by simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hr.one_lt hq.pos
    exact hlt.ne (hqp.trans he)
  have gap {u v : ℕ} (hu : n=c*u) (hv : m=c*v) (hsize : u ≤ (4*t)^2) (huv : u ≠ v) :
      n+t^(d+2) ≤ m ∨ m+t^(d+2) ≤ n := by
    have hcap : n ≤ c*(4*t)^2 := hu ▸ Nat.mul_le_mul_left c hsize
    have hc : t^(d+2) ≤ c := Nat.le_of_mul_le_mul_right (hscale.trans hcap) (by positivity)
    rw [hu,hv]
    rcases lt_or_gt_of_ne huv with h | h
    · exact Or.inl ((Nat.add_le_add_left hc _).trans
        (by simpa only [Nat.mul_succ] using Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)))
    · exact Or.inr ((Nat.add_le_add_left hc _).trans
        (by simpa only [Nat.mul_succ] using Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)))
  rcases e with ⟨hn,hm⟩ | ⟨hm,hn⟩
  · have hp' := smooth p hp (hn ▸ Nat.dvd_mul_left p c)
    exact gap hn hm (hp'.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by positivity : 0<4*t) (by decide : 1 ≤ 2))) ne
  · have hd := (show q*r ∣ n from hn ▸ Nat.dvd_mul_left (q*r) c)
    have hq' := smooth q hq ((Nat.dvd_mul_right q r).trans hd)
    have hr' := smooth r hr ((Nat.dvd_mul_left r q).trans hd)
    exact gap hn hm ((Nat.mul_le_mul hq' hr').trans_eq (pow_two _).symm) ne.symm

/-- On a finite explicit grid of cutoffs, a single involution must exhibit
at least the indicated share of an entire prime-product population. -/
theorem exists_large_unpaid_cutoff (F : ℕ → ℕ)
    (hF : ∀ n, Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (d t : ℕ) (ht : 0<t) :
    ∃ x ≤ (4*t)^(d+4), (windowPrimes (2*t) (4*t)).card.choose (d+4) ≤
      2*(4^(d+4)*t^2)*(prefixUnpaid F x).card := by
  let D := t^(d+2)
  let G := 4^(d+4)*t^2
  let S := octaveProducts t (d+4)
  let U := (4*t)^(d+4)
  let f (x : ℕ) := (prefixUnpaid F x).card
  have hg : G*D=U := by
    dsimp [U,D,G]
    rw [mul_pow,mul_assoc,←pow_add]; congr 2; omega
  have pos : 0<D := pow_pos ht _
  let Z := (range (U+1)).image f
  have hnZ : Z.Nonempty := ⟨f 0,mem_image_of_mem _ (mem_range.mpr (Nat.succ_pos _))⟩
  let K := Z.max' hnZ
  have bound {x : ℕ} (h : x ≤ U) : f x ≤ K := le_max' _ _ (mem_image_of_mem _ (mem_range.mpr (by omega)))
  obtain ⟨x,hx,hxK⟩ := mem_image.mp (max'_mem Z hnZ)
  refine ⟨x,Nat.le_of_lt_succ (mem_range.mp hx),?_⟩
  let cell (j : ℕ) := S.filter (fun n => n ∈ Ioc (j*D) ((j+1)*D))
  have covers : S ⊆ (range G).biUnion cell := by
    intro n hn
    obtain ⟨hs,_,hU,_⟩ := product_facts hn
    have hp : 0<n := Nat.pos_of_ne_zero hs.ne_zero
    let j := (n-1)/D
    have hj : j<G := (Nat.div_lt_iff_lt_mul pos).2 (by rw [hg]; omega)
    have hquot : j*D ≤ n-1 := Nat.div_mul_le_self _ _
    have hu : n-1<(j+1)*D := (Nat.div_lt_iff_lt_mul pos).1 (Nat.lt_succ_self j)
    exact mem_biUnion.mpr ⟨j,mem_range.mpr hj,mem_filter.mpr ⟨hn,mem_Ioc.mpr ⟨by omega,by omega⟩⟩⟩
  have cells (j : ℕ) (hj : j ∈ range G) : (cell j).card ≤ 2*K := by
    have hu : (j+1)*D ≤ U := hg ▸ Nat.mul_le_mul_right D (Nat.succ_le_of_lt (mem_range.mp hj))
    have hl : j*D ≤ U := (Nat.mul_le_mul_right _ (Nat.le_succ j)).trans hu
    have hs (n : ℕ) (hn : n ∈ cell j) : n ∈ Ioc (j*D) ((j+1)*D) ∧
        Squarefree n ∧ (F n=n ∨ F n ∉ Ioc (j*D) ((j+1)*D)) := by
      obtain ⟨hin,hat⟩ := mem_filter.mp hn
      have hsq := (product_facts hin).1
      refine ⟨hat,hsq,?_⟩
      rcases (hF n hsq).2 with eq | edge
      · exact Or.inl eq
      · refine Or.inr (fun hm => ?_)
        obtain ⟨hn₁,hn₂⟩ := mem_Ioc.mp hat
        obtain ⟨hm₁,hm₂⟩ := mem_Ioc.mp hm
        have sep := product_cannot_move_short ht hin edge
        change n+D ≤ F n ∨ F n+D ≤ n at sep
        rw [Nat.succ_mul] at hn₂ hm₂
        omega
    exact (window_debt_le_two_prefixes hF hs).trans
      ((Nat.add_le_add (bound hl) (bound hu)).trans_eq (two_mul _).symm)
  have hcard := (card_le_card covers).trans ((card_biUnion_le ..).trans (sum_le_sum cells))
  change (S.card) ≤ ∑ _j ∈ range G,2*K at hcard
  simp only [sum_const,card_range,nsmul_eq_mul] at hcard
  rw [←product_count]
  change S.card ≤ 2*G*f x
  rw [hxK]
  change S.card ≤ 2*G*K
  change S.card ≤ G*(2*K) at hcard
  exact hcard.trans_eq (by ring)

#print axioms window_debt_le_two_prefixes
#print axioms exists_large_unpaid_cutoff

end GaloisForLFunctions.RestrictedFactorizationCalculus
