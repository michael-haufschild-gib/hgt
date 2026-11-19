import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyForBalancedProducts
import GaloisForLFunctions.QuantitativeFactorizationMatching.GlobalDyadicGraphAndCofactorFibres

/-!
# Simultaneous transport across ordered cofactor fibres

Pair the primes and eligible semiprimes of each quotient interval in increasing
order. Removing the largest prime from a prime endpoint or the largest two
from a semiprime endpoint recovers the indexing cofactor. Thus every rank in
every row is used at most once, even with unrestricted factor count.
-/

noncomputable section

open Finset RHTower
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The cofactor after removing the largest prime, with value zero at zero and one. -/
def stem (n : ℕ) : ℕ := n / n.primeFactors.sup id

/-- Removing a prime larger than every factor recovers the cofactor exactly. -/
theorem stem_mul_of_largest {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) : stem (c*p) = c := by
  have hn := Nat.mul_ne_zero hc hp.ne_zero
  have hm : p ∈ (c*p).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_left p c, hn⟩
  have hmax : (c*p).primeFactors.sup id = p := by
    refine le_antisymm (Finset.sup_le_iff.mpr fun d hd => ?_) (le_sup (f := id) hm)
    obtain ⟨hdp, hdvd, _⟩ := Nat.mem_primeFactors.mp hd
    rcases hdp.dvd_mul.mp hdvd with h | h
    · exact (htop _ (Nat.mem_primeFactors.mpr ⟨hdp, h, hc⟩)).le
    · exact Nat.le_of_dvd hp.pos h
  simp only [stem, hmax, Nat.mul_div_cancel _ hp.pos]

/-- All factors of the intermediate cofactor lie below the last prime. -/
theorem below_pair {c q r : ℕ} (hc : c ≠ 0) (hq : q.Prime) (hqr : q < r)
    (htop : ∀ d ∈ c.primeFactors, d < q) :
    ∀ d ∈ (c*q).primeFactors, d < r := by
  intro d hd
  obtain ⟨hdp, hdvd, _⟩ := Nat.mem_primeFactors.mp hd
  rcases hdp.dvd_mul.mp hdvd with h | h
  · exact (htop _ (Nat.mem_primeFactors.mpr ⟨hdp, h, hc⟩)).trans hqr
  · exact (Nat.le_of_dvd hq.pos h).trans_lt hqr

/-- Removing the largest two primes in order recovers both intermediate cofactors. -/
theorem ordered_stems {c q r : ℕ} (hc : c≠0) (hq : q.Prime) (hr : r.Prime)
    (hqr : q<r) (ht : ∀ d ∈ c.primeFactors, d<q) :
    stem (c*(q*r))=c*q ∧ stem (stem (c*(q*r)))=c := by
  rw [←mul_assoc,stem_mul_of_largest (Nat.mul_ne_zero hc hq.ne_zero) hr (below_pair hc hq hqr ht),
    stem_mul_of_largest hc hq ht]
  exact ⟨rfl,rfl⟩

/-- For ordered primes the last two deletions recover both intermediate cofactors. -/
theorem stem_ordered_triple {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    stem (p*(q*r)) = p*q ∧ stem (stem (p*(q*r))) = p := by
  have ht : ∀ d ∈ p.primeFactors, d < q :=
    fun _ hd => (Nat.le_of_dvd hp.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hpq
  exact ordered_stems hp.ne_zero hq hr hqr ht

/-- Appending a strictly larger prime adds one distinct factor. -/
theorem card_append_largest {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) :
    (c*p).primeFactors.card = c.primeFactors.card + 1 := by
  have hn : p ∉ c.primeFactors := fun h => (htop _ h).false
  rw [Nat.primeFactors_mul hc hp.ne_zero, hp.primeFactors,union_comm,singleton_union,
    card_insert_of_notMem hn]

/-- The ordered semiprime end of an exchange adds two distinct prime factors. -/
theorem card_append_ordered_pair {c q r : ℕ} (hc : c ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hqr : q < r) (ht : ∀ d ∈ c.primeFactors, d < q) :
    (c*(q*r)).primeFactors.card = c.primeFactors.card + 2 := by
  rw [← mul_assoc, card_append_largest (Nat.mul_ne_zero hc hq.ne_zero) hr
    (below_pair hc hq hqr ht),card_append_largest hc hq ht]

/-- A larger prime reverses the cofactor sign. -/
theorem mu_append {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) : μ (c*p) = -μ c := by
  have hnd : ¬ p ∣ c := fun h => (htop _ (Nat.mem_primeFactors.mpr ⟨hp, h, hc⟩)).false
  rw [isMultiplicative_moebius.map_mul_of_coprime ((hp.coprime_iff_not_dvd.2 hnd).symm),
    moebius_apply_prime hp, mul_neg_one]

/-- Primes in the sharp quotient interval which decode to the given cofactor. -/
def primeRow (L U c : ℕ) : Finset ℕ := by
  classical exact (windowPrimes ((L:ℝ)/c) ((U:ℝ)/c)).filter fun p =>
    ∀ d ∈ c.primeFactors, d < p

/-- Eligible semiprimes with both factors larger than every cofactor prime. -/
def productRow (K : ℝ) (L U c : ℕ) : Finset ℕ := by
  classical
  exact (balancedProducts K (Real.sqrt ((L:ℝ)/c)) ((L:ℝ)/c) ((U:ℝ)/c)).filter fun w =>
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ w = q*r ∧
      Real.sqrt ((L:ℝ)/c) / K < q ∧ ∀ d ∈ c.primeFactors, d < q

private theorem interval_mul {L U c w : ℕ} (hc : c ≠ 0)
    (hl : (L:ℝ)/c < w) (hu : (w:ℝ) ≤ (U:ℝ)/c) : c*w ∈ Ioc L U := by
  have hc0 : (0:ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hl' := (div_lt_iff₀ hc0).1 hl
  have hu' := (le_div_iff₀ hc0).1 hu
  rw [mul_comm]
  exact mem_Ioc.mpr ⟨by exact_mod_cast hl', by exact_mod_cast hu'⟩

/-- The prime quotient cut includes precisely the two original integer endpoints
with the lower one open. -/
theorem balancedProduct_mem_interval {K s : ℝ} {L U c w : ℕ} (hc : c ≠ 0)
    (hw : w ∈ balancedProducts K s ((L:ℝ)/c) ((U:ℝ)/c)) : c*w ∈ Ioc L U := by
  obtain ⟨q, hq, hw⟩ := mem_biUnion.mp hw
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hw
  have hp : q.Prime := (mem_filter.mp hq).2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
  obtain ⟨_, hl, hu⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hr
  apply interval_mul hc <;> push_cast
  · simpa only [mul_comm (r:ℝ)] using (div_lt_iff₀ hq0).1 hl
  · simpa only [mul_comm (r:ℝ)] using (le_div_iff₀ hq0).1 hu

/-- Once a product occurs inside an octave, every prime in its row exceeds
every cofactor prime. Thus the whole prime supply is eligible. -/
theorem primeRow_eq_of_product {K : ℝ} {L U c w : ℕ} (hc : c ≠ 0)
    (hU : U ≤ 2*L) (hw : w ∈ productRow K L U c) :
    primeRow L U c = windowPrimes ((L:ℝ)/c) ((U:ℝ)/c) := by
  obtain ⟨hbal,q,r,_,hr,_,heq,_,htop⟩ := mem_filter.mp hw
  have hI := (mem_Ioc.mp (balancedProduct_mem_interval hc hbal)).2
  rw [heq, ← mul_assoc] at hI
  have hm := Nat.mul_le_mul_left (c*q) hr.two_le
  have hscale : c*q ≤ L := by omega
  have hc0 : (0:ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hqL : (q:ℝ) ≤ (L:ℝ)/c := by
    rw [le_div_iff₀ hc0, mul_comm]; exact_mod_cast hscale
  apply filter_eq_self.mpr
  intro p hp d hd
  obtain ⟨_, hl, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hp
  exact (htop d hd).trans (by exact_mod_cast hqL.trans_lt hl)

private def entry (S : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < S.card then (S.orderIsoOfFin rfl ⟨i, hi⟩ : ℕ) else 0

private theorem entry_mem {S : Finset ℕ} {i : ℕ} (hi : i < S.card) : entry S i ∈ S := by
  simpa only [entry, dif_pos hi] using (S.orderIsoOfFin rfl ⟨i, hi⟩).property

private theorem entry_inj {S : Finset ℕ} {i j : ℕ} (hi : i < S.card) (hj : j < S.card)
    (he : entry S i = entry S j) : i = j := by
  simp only [entry, dif_pos hi, dif_pos hj] at he
  exact congrArg Fin.val ((S.orderIsoOfFin rfl).injective (Subtype.ext he))

private def rankIn (S : Finset ℕ) (n : ℕ) : ℕ :=
  if hn : n ∈ S then ((S.orderIsoOfFin rfl).symm ⟨n,hn⟩).val else S.card

private theorem rank_entry {S : Finset ℕ} {i : ℕ} (hi : i < S.card) :
    rankIn S (entry S i) = i := by
  rw [rankIn, dif_pos (entry_mem hi)]
  simp only [entry, dif_pos hi]
  exact congrArg Fin.val ((S.orderIsoOfFin rfl).symm_apply_apply ⟨i,hi⟩)

/-- Number of prime-to-semiprime exchanges in a cofactor row at these endpoints. -/
def rowCount (K : ℝ) (L U c : ℕ) : ℕ :=
  min (primeRow L U c).card (productRow K L U c).card

private def addresses (K : ℕ → ℝ) (L U : ℕ) : Finset (ℕ × ℕ) := by
  classical exact ((Icc 1 U).filter (fun c => μ c = -1)).biUnion fun c =>
    (range (rowCount (K c) L U c)).image (fun i => (c,i))

private theorem mem_addresses {K : ℕ → ℝ} {L U c i : ℕ} :
    (c,i) ∈ addresses K L U ↔ c ∈ Icc 1 U ∧ μ c = -1 ∧ i < rowCount (K c) L U c := by
  classical simp [addresses, and_assoc]

private def primeEnd (L U : ℕ) (a : ℕ × ℕ) := a.1 * entry (primeRow L U a.1) a.2
private def productEnd (K : ℕ → ℝ) (L U : ℕ) (a : ℕ × ℕ) :=
  a.1 * entry (productRow (K a.1) L U a.1) a.2

private theorem address_endpoints {K : ℕ → ℝ} {L U c i : ℕ} (ha : (c,i) ∈ addresses K L U) :
    let m := primeEnd L U (c,i)
    let n := productEnd K L U (c,i)
    m ∈ posParity (Ioc L U) ∧ n ∈ negParity (Ioc L U) ∧
      GlobalDyadicOneTwoRel m n ∧ stem m = c ∧ stem (stem n) = c ∧
        n.primeFactors.card = m.primeFactors.card + 1 := by
  obtain ⟨hcI, hcμ, hi⟩ := mem_addresses.mp ha
  have hc := (mem_Icc.mp hcI).1
  have hcn : c ≠ 0 := by omega
  have hp := entry_mem (S := primeRow L U c) (hi.trans_le (min_le_left ..))
  have hw := entry_mem (S := productRow (K c) L U c) (hi.trans_le (min_le_right ..))
  obtain ⟨hwp, q, r, hq, hr, hqr, heq, _, ht⟩ := mem_filter.mp hw
  obtain ⟨hpm, hpt⟩ := mem_filter.mp hp
  obtain ⟨hpr, hpl, hpu⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hpm
  have hpI := interval_mul hcn hpl hpu
  have hwI := balancedProduct_mem_interval hcn hwp
  have hop := mu_append hcn hpr hpt
  have hcq := Nat.mul_ne_zero hcn hq.ne_zero
  have htr := below_pair hcn hq hqr ht
  have hprod : μ (c * entry (productRow (K c) L U c) i) = -1 := by
    rw [heq, ← mul_assoc, mu_append hcq hr htr, mu_append hcn hq ht, hcμ]; norm_num
  have hprime : μ (c * entry (primeRow L U c) i) = 1 := by rw [hop, hcμ]; norm_num
  refine ⟨mem_filter.mpr ⟨hpI, hprime⟩, mem_filter.mpr ⟨hwI, hprod⟩,
    ⟨squarefree_iff_moebius_ne_zero.mpr (by change μ (c * entry _ i) ≠ 0; rw [hprime]; decide),
     squarefree_iff_moebius_ne_zero.mpr (by change μ (c * entry _ i) ≠ 0; rw [hprod]; decide),
     by change μ (c * entry _ i) = -μ (c * entry _ i); rw [hprime,hprod]; decide,
     c, _, q, r, hpr, hq, hr, hqr, Or.inl ⟨rfl, congrArg (c*·) heq⟩⟩, stem_mul_of_largest hcn hpr hpt, ?_⟩
  constructor
  · change stem (stem (c * entry (productRow (K c) L U c) i)) = c
    rw [heq, ← mul_assoc, stem_mul_of_largest hcq hr htr, stem_mul_of_largest hcn hq ht]
  · change (c * entry (productRow (K c) L U c) i).primeFactors.card =
        (c * entry (primeRow L U c) i).primeFactors.card + 1
    rw [heq, ← mul_assoc, card_append_largest hcq hr htr, card_append_largest hcn hq ht,
      card_append_largest hcn hpr hpt]

private theorem endpoint_inj {K : ℕ → ℝ} {L U : ℕ} (prime : Bool) :
    Set.InjOn (if prime then primeEnd L U else productEnd K L U) (addresses K L U) := by
  rintro ⟨c,i⟩ ha ⟨d,j⟩ hb he
  obtain ⟨hc, _, hi⟩ := mem_addresses.mp ha
  obtain ⟨_, _, hj⟩ := mem_addresses.mp hb
  have hpos := (mem_Icc.mp hc).1
  obtain ⟨_, _, _, hp, hw,_⟩ := address_endpoints ha
  obtain ⟨_, _, _, hp', hw',_⟩ := address_endpoints hb
  cases prime
  · change productEnd K L U (c,i) = productEnd K L U (d,j) at he
    have hcd := hw.symm.trans ((congrArg (fun n => stem (stem n)) he).trans hw')
    subst d
    exact Prod.ext rfl (entry_inj (hi.trans_le (min_le_right ..)) (hj.trans_le (min_le_right ..))
      (Nat.eq_of_mul_eq_mul_left hpos he))
  · change primeEnd L U (c,i) = primeEnd L U (d,j) at he
    have hcd := hp.symm.trans ((congrArg stem he).trans hp')
    subst d
    exact Prod.ext rfl (entry_inj (hi.trans_le (min_le_left ..)) (hj.trans_le (min_le_left ..))
      (Nat.eq_of_mul_eq_mul_left hpos he))

/-- A single matching across every cofactor and every factor count. At each
negative cofactor exactly the first `min(#primes,#products)` entries of both
rows are used. This describes the boundary even in cells containing no prime. -/
theorem exists_ranked_transport (K : ℕ → ℝ) (L U : ℕ) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc L U),
      (∀ m ∈ M.sources, (M.partner m).primeFactors.card = m.primeFactors.card + 1) ∧
      ∀ c ∈ Icc 1 U, μ c = -1 →
        ((M.sources.filter (fun m => stem m = c)).card = rowCount (K c) L U c ∧
         (M.targets.filter (fun n => stem (stem n) = c)).card = rowCount (K c) L U c ∧
         ∀ w ∈ productRow (K c) L U c, (productRow (K c) L U c).card ≤ (primeRow L U c).card →
           c*w ∈ M.targets) := by
  classical
  let S := addresses K L U
  let f := primeEnd L U
  let g := productEnd K L U
  let unpair := fun n => (stem n, rankIn (primeRow L U (stem n)) (n / stem n))
  have hf : Set.InjOn f S := endpoint_inj true
  have hg : Set.InjOn g S := endpoint_inj false
  have inv (a : ℕ × ℕ) (ha : a ∈ S) : unpair (f a) = a := by
    obtain ⟨c,i⟩ := a
    obtain ⟨hc,_,hi⟩ := mem_addresses.mp ha
    have hstem := (address_endpoints ha).2.2.2.1
    have hdiv : primeEnd L U (c,i) / c = entry (primeRow L U c) i := by
      change (c * entry _ i) / c = _
      rw [mul_comm, Nat.mul_div_cancel _ (mem_Icc.mp hc).1]
    change (stem (primeEnd L U (c,i)), _) = (c,i)
    dsimp only [unpair, f]
    rw [hstem,hdiv,rank_entry (hi.trans_le (min_le_left ..))]
  let M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc L U) := {
    sources := S.image f
    partner := g ∘ unpair
    sources_subset := by
      intro m hm
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
      exact (address_endpoints ha).1
    injOn := by
      intro x hx y hy he
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      simp only [Function.comp_apply, inv _ ha, inv _ hb] at he
      exact congrArg f (hg ha hb he)
    partner_mem := by
      intro m hm
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
      simp only [Function.comp_apply, inv _ ha]
      exact (address_endpoints ha).2.1
    adj := by
      intro m hm
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
      simp only [Function.comp_apply, inv _ ha]
      exact (address_endpoints ha).2.2.1 }
  have tset : M.targets = S.image g := by
    ext n
    simp only [OppositeParityMatching.targets, M, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨a,ha,rfl⟩,rfl⟩
      exact ⟨a,ha,by rw [inv _ ha]⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨f a, ⟨a,ha,rfl⟩,by rw [inv _ ha]⟩
  refine ⟨M,?_,fun c hc hμ => ?_⟩
  · intro m hm
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
    change (g (unpair (f a))).primeFactors.card = (f a).primeFactors.card + 1
    rw [inv _ ha]
    exact (address_endpoints ha).2.2.2.2.2
  have rowcard (e : ℕ × ℕ → ℕ) (decode : ℕ → ℕ) (he : Set.InjOn e S)
      (hd : ∀ a ∈ S, decode (e a) = a.1) :
      (((S.image e).filter (fun n => decode n = c)).card) = rowCount (K c) L U c := by
    have heq : (S.image e).filter (fun n => decode n = c) =
        (range (rowCount (K c) L U c)).image (fun i => e (c,i)) := by
      ext n
      constructor
      · intro hn
        obtain ⟨hm, hd'⟩ := mem_filter.mp hn
        obtain ⟨⟨a,i⟩,ha,rfl⟩ := mem_image.mp hm
        have hc' := (hd _ ha).symm.trans hd'
        change a = c at hc'
        subst a
        exact mem_image.mpr ⟨i, mem_range.mpr (mem_addresses.mp ha).2.2,rfl⟩
      · intro hn
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
        have ha : (c,i) ∈ S := mem_addresses.mpr ⟨hc,hμ,mem_range.mp hi⟩
        exact mem_filter.mpr ⟨mem_image_of_mem e ha,hd _ ha⟩
    rw [heq, card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact congrArg Prod.snd (he (mem_addresses.mpr ⟨hc,hμ,mem_range.mp hi⟩)
      (mem_addresses.mpr ⟨hc,hμ,mem_range.mp hj⟩) hij)
  refine ⟨rowcard f stem hf (fun _ h => (address_endpoints h).2.2.2.1),
    by rw [tset]; exact rowcard g (fun n => stem (stem n)) hg (fun _ h => (address_endpoints h).2.2.2.2.1), ?_⟩
  intro w hw hle
  let i := ((productRow (K c) L U c).orderIsoOfFin rfl).symm ⟨w,hw⟩
  have hi : i.val < rowCount (K c) L U c := by rw [rowCount,min_eq_right hle]; exact i.isLt
  have ha : (c,i.val) ∈ S := mem_addresses.mpr ⟨hc,hμ,hi⟩
  rw [tset]
  refine mem_image.mpr ⟨(c,i.val),ha,?_⟩
  change c * entry (productRow (K c) L U c) i.val = c * w
  simp only [entry, dif_pos i.isLt]
  exact congrArg (fun x : productRow (K c) L U c => c * (x:ℕ))
    ((productRow (K c) L U c).orderIsoOfFin rfl |>.apply_symm_apply ⟨w,hw⟩)

/-- For a positive vertex of an octave the ordered cofactor removes exactly
the two largest prime factors. -/
theorem ordered_cofactor_of_positive {X m : ℕ} (hm : m ∈ posParity (Ioc X (2*X))) :
    evenPrefixCofactor m = stem (stem m) := by
  have hi := mem_Ioc.mp (mem_filter.mp hm).1
  have hX : 1≤X := by omega
  let b := evenPrefixCofactor m
  have hf : m ∈ fibrePos X b := mem_filter.mpr ⟨hm,rfl⟩
  obtain ⟨hb,_,q,r,hq,hr,hqr,he,ht⟩ := mem_fibrePos_structure hX hf
  change b = stem (stem m)
  exact (congrArg (fun u => stem (stem u)) he |>.trans (ordered_stems hb.ne_zero hq hr hqr ht).2).symm

/-- For a negative vertex the ordered cofactor removes exactly its largest prime. -/
theorem ordered_cofactor_of_negative {n : ℕ} (hμ : μ n = -1) :
    evenPrefixCofactor n = stem n := by
  have hs := squarefree_iff_moebius_ne_zero.mpr (show μ n ≠ 0 by omega)
  have hodd : ¬ Even n.primeFactors.card := by
    intro he
    rw [moebius_eq_neg_one_pow_omega hs, he.neg_one_pow] at hμ
    omega
  have hne : n.primeFactors.Nonempty := by
    by_contra! h
    rw [h, card_empty] at hodd
    exact hodd ⟨0,rfl⟩
  have hsup : n.primeFactors.sup id = n.primeFactors.max' hne :=
    le_antisymm (Finset.sup_le_iff.mpr (fun d hd => le_max' _ d hd)) (le_sup (f := id) (max'_mem _ _))
  simp only [evenPrefixCofactor, dif_pos hne, if_neg hodd, stem, hsup]

/-- One matching exhausts every eligible negative row in sufficiently large
quotient cells, down to each fixed log-power relative width. Every covered
integer lies in an ordered fibre with no positive vertex in the *full* octave. -/
theorem exists_transport_covering_empty_fibres (k B : ℕ) :
    let K : ℝ := k+1
    ∃ T : ℝ, ∀ L U : ℕ, ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc L U),
      ∀ c ∈ Icc 1 U, μ c = -1 → ∀ w ∈ productRow K L U c,
        let s := Real.sqrt ((L:ℝ)/c)
        T ≤ s → U ≤ 2*L →
        (L:ℝ)/c / Real.log s ^ B ≤ (U:ℝ)/c - (L:ℝ)/c →
        c*w ∈ M.targets ∧ fibrePos L (evenPrefixCofactor (c*w)) = ∅ := by
  dsimp only
  let K : ℝ := k+1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (eventually_balancedProducts_capacity K B 1)
  refine ⟨max T (2*K^3), fun L U => ?_⟩
  obtain ⟨M,_,hM⟩ := exists_ranked_transport (fun _ => K) L U
  refine ⟨M, fun c hc hμ w hw => ?_⟩
  let s := Real.sqrt ((L:ℝ)/c)
  intro hs hU hgap
  have hcn : c ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hc).1
  have hc0 : (0:ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hcn
  have hsq : s^2 = (L:ℝ)/c := Real.sq_sqrt (by positivity)
  obtain ⟨hbal,q,r,hq,hr,hqr,hwqr,hqlo,htop⟩ := mem_filter.mp hw
  have hI := mem_Ioc.mp (balancedProduct_mem_interval hcn hbal)
  have hpall := primeRow_eq_of_product hcn hU hw
  have hcap := hT s ((le_max_left _ _).trans hs) ((L:ℝ)/c) ((U:ℝ)/c)
    hsq.le (div_le_div_of_nonneg_right (by exact_mod_cast hI.1.le.trans hI.2) hc0.le) (by
      rw [hsq, ← mul_div_assoc]; exact div_le_div_of_nonneg_right (by exact_mod_cast hU) hc0.le)
    (by rw [hsq]; exact hgap)
  have hcov := (hM c hc hμ).2.2 w hw (by
    rw [hpall]
    exact (card_le_card (filter_subset _ _)).trans (by simpa only [one_mul] using hcap))
  refine ⟨hcov, ?_⟩
  have hnμ := (mem_filter.mp (M.targets_subset hcov)).2
  rw [ordered_cofactor_of_negative hnμ, hwqr, ← mul_assoc,
    stem_mul_of_largest (Nat.mul_ne_zero hcn hq.ne_zero) hr (below_pair hcn hq hqr htop)]
  apply fibrePos_eq_empty_of_primeFactor_sq_ge (by omega : 1 ≤ L)
    (Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_left q c, Nat.mul_ne_zero hcn hq.ne_zero⟩)
  have hlarge : 2*K^3 ≤ s := (le_max_right _ _).trans hs
  have hs0 := Real.sqrt_nonneg ((L:ℝ)/c)
  have hq' := (div_lt_iff₀ hK).1 hqlo
  have hcube : 2*s^2 ≤ (q:ℝ)^3 := by
    apply le_of_mul_le_mul_right _ (pow_pos hK 3)
    calc 2*s^2*K^3 ≤ s^3 := by nlinarith only [mul_le_mul_of_nonneg_left hlarge (sq_nonneg s)]
         _ ≤ ((q:ℝ)*K)^3 := pow_le_pow_left₀ hs0 hq'.le 3
         _ = _ := by ring
  rw [hsq] at hcube
  have hfin := (div_le_iff₀ hc0).1 (show 2*(L:ℝ)/c ≤ (q:ℝ)^3 by
    rwa [mul_div_assoc])
  exact_mod_cast (show 2*(L:ℝ) ≤ (c:ℝ)*q*q^2 by linarith only [hfin])

end GaloisForLFunctions.RestrictedFactorizationCalculus
