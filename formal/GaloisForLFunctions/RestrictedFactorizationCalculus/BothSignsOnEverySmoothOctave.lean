import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary
import GaloisForLFunctions.RestrictedFactorizationCalculus.TransportAcrossOrderedFibres
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans

/-!
# Both Möbius signs among smooth integers on every octave

Adjoining a new largest prime from a polynomial window preserves positive
lower density, reverses the sign and lowers the smoothness exponent.
Iteration gives a positive density at every fixed positive exponent.
-/

noncomputable section

open Finset Filter RHTower
open ArithmeticFunction hiding id
open scoped Classical Topology ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def signOf (b : Bool) : ℤ := if b then 1 else -1

/-- Integers in the sharp octave with specified sign and every prime divisor
at most the stated power of its upper endpoint. -/
def smoothSignOctave (b : Bool) (t x : ℝ) :=
  ((Icc 1 ⌊x⌋₊).filter fun n => x/2<(n:ℝ) ∧ μ n=signOf b ∧
    ∀ q ∈ n.primeFactors,(q:ℝ) ≤ x^t)

private theorem base_count (b : Bool) {x : ℝ} (hx : 0 ≤ x) :
    (smoothSignOctave b 1 x).card+coprimeMoebiusSignCount 1 ⌊x/2⌋₊ b =
      coprimeMoebiusSignCount 1 ⌊x⌋₊ b := by
  let S := fun t : ℝ => (Icc 1 ⌊t⌋₊).filter (fun n => Nat.Coprime 1 n ∧ μ n=signOf b)
  have hsub : S (x/2) ⊆ S x := by
    intro n hn
    obtain ⟨hi,h⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨Icc_subset_Icc le_rfl (Nat.floor_le_floor (by linarith : x/2 ≤ x)) hi,h⟩
  have he : smoothSignOctave b 1 x=S x \\ S (x/2) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hi,hl,hm,_⟩ := mem_filter.mp hn
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hi,Nat.coprime_one_left _,hm⟩,fun ha =>
        hl.not_ge ((Nat.cast_le.mpr (mem_Icc.mp (mem_filter.mp ha).1).2).trans (Nat.floor_le (by positivity)))⟩
    · intro hn
      obtain ⟨h,ha⟩ := mem_sdiff.mp hn
      obtain ⟨hi,hc,hm⟩ := mem_filter.mp h
      have hn0 := (mem_Icc.mp hi).1
      have hnx := (Nat.cast_le.mpr (mem_Icc.mp hi).2).trans (Nat.floor_le hx)
      refine mem_filter.mpr ⟨hi,lt_of_not_ge (fun hu => ha (mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hn0,Nat.le_floor hu⟩,hc,hm⟩)),hm,?_⟩
      intro q hq
      rw [Real.rpow_one]
      exact (Nat.cast_le.mpr (Nat.le_of_dvd hn0 (Nat.mem_primeFactors.mp hq).2.1)).trans hnx
  rw [he]
  exact card_sdiff_add_card_eq_card hsub

private theorem base_density (b : Bool) : ∃ c : ℝ,0<c ∧
    ∀ᶠ x : ℝ in atTop,c*x ≤ ((smoothSignOctave b 1 x).card:ℝ) := by
  let d := coprimeSquarefreeDensity 1
  have hd : 0<d := coprimeSquarefreeDensity_pos _
  have h := tendsto_coprimeMoebiusSignMean (1:ℕ+) b
  have hh := h.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<1/2)).mpr tendsto_id)
  refine ⟨d/8,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),h.eventually_const_lt (by change 7*d/16<d/2; linarith only [hd]),
    hh.eventually_lt_const (by change d/2<9*d/16; linarith only [hd])] with x hx hlo hhi
  have hx0 := zero_lt_one.trans_le hx
  change 7*d/16<(coprimeMoebiusSignCount 1 ⌊x⌋₊ b:ℝ)/x at hlo
  change (coprimeMoebiusSignCount 1 ⌊(1/2:ℝ)*x⌋₊ b:ℝ)/((1/2:ℝ)*x)<9*d/16 at hhi
  rw [show (1/2:ℝ)*x=x/2 by ring] at hhi
  have htot := (lt_div_iff₀ hx0).1 hlo
  have hpart := (div_lt_iff₀ (half_pos hx0)).1 hhi
  have he := congrArg ((↑) : ℕ → ℝ) (base_count b hx0.le)
  push_cast only [Nat.cast_add] at he
  -- The sign density tends to d/2 independently at both endpoints.
  nlinarith only [htot,hpart,he,mul_pos hd hx0]

/-- A fixed polynomial prime window has a positive uniform reciprocal mass. -/
private theorem polynomial_window_mass {a b : ℝ} (ha : 0<a) (hab : a<b) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ x : ℝ in atTop,c ≤ ∑ p ∈ windowPrimes (x^a) (x^b),1/(p:ℝ) := by
  let c := (b-a)/(2*b)
  have hb := ha.trans hab
  refine ⟨c,div_pos (sub_pos.mpr hab) (by positivity),?_⟩
  have grow := Real.tendsto_log_atTop.eventually_ge_atTop
    (2*(Real.log 2+Sieve.mertensBlockGapConst)/(b-a))
  filter_upwards [eventually_ge_atTop (2:ℝ),grow,
    (tendsto_rpow_atTop ha).eventually_ge_atTop 2] with x hx hlog hxa
  have hx1 : 1<x := by linarith only [hx]
  have hx0 := zero_lt_one.trans hx1
  have hlog0 := Real.log_pos hx1
  let A := ⌊x^a⌋₊
  let B := ⌊x^b⌋₊
  let P := windowPrimes (x^a) (x^b)
  have hAB := Real.rpow_le_rpow_of_exponent_le hx1.le hab.le
  have hA : 1 ≤ A := (Nat.one_le_floor_iff _).2 (by linarith only [hxa])
  have hA0 : (0:ℝ)<A := by exact_mod_cast hA
  have hle : A ≤ B := Nat.floor_le_floor hAB
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := fun p hp => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hp).1.trans hle,(Nat.mem_primesLE.mp hp).2⟩
  have hua := Real.log_le_log hA0 (Nat.floor_le (Real.rpow_nonneg hx0.le a))
  have hlow : x^b/2 ≤ (B:ℝ) := by
    have hf := Nat.lt_floor_add_one (x^b)
    change x^b/2 ≤ (⌊x^b⌋₊:ℝ)
    linarith only [hf,hxa,hAB]
  have hlb := Real.log_le_log (half_pos (Real.rpow_pos_of_pos hx0 b)) hlow
  rw [Real.log_rpow hx0] at hua
  rw [Real.log_div (Real.rpow_pos_of_pos hx0 b).ne' (by norm_num),Real.log_rpow hx0] at hlb
  have hgap := (div_le_iff₀ (sub_pos.mpr hab)).1 hlog
  have mass : (b-a)*Real.log x/2 ≤ ∑ p ∈ P, Real.log p/p := by
    rw [show P=Nat.primesLE B \\ Nat.primesLE A from windowPrimes_eq_primesLE_sdiff _ _,sum_sdiff_eq_sub hsub]
    unfold Sieve.mertensBlockGapConst at hgap
    linarith only [Sieve.mertensFirst_lower (hA.trans hle),Sieve.mertensFirst_upper hA,hgap,hua,hlb]
  have bound : ∑ p ∈ P,Real.log p/p ≤ (b*Real.log x)*∑ p ∈ P,1/(p:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpr,_,hhi⟩ := (mem_windowPrimes (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx0.le _)).1 hp
    have hh := Real.log_le_log (Nat.cast_pos.mpr hpr.pos) hhi
    rw [Real.log_rpow hx0] at hh
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg p)
  have hh := mass.trans bound
  calc c = ((b-a)*Real.log x/2)/(b*Real.log x) := by
         dsimp only [c]; field_simp; ring
       _ ≤ _ := (div_le_iff₀ (mul_pos hb hlog0)).2 (by rw [mul_comm _ (b*Real.log x)]; exact hh)

private theorem smooth_step (b : Bool) {a u t : ℝ}
    (ha : 0<a) (hau : a<u) (hu : u<1) (ht : 0<t) (htop : (1-a)*t=a)
    (prev : ∃ c : ℝ,0<c ∧ ∀ᶠ x : ℝ in atTop,c*x ≤ ((smoothSignOctave (!b) t x).card:ℝ)) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ x : ℝ in atTop,c*x ≤ ((smoothSignOctave b u x).card:ℝ) := by
  obtain ⟨c,hc,hcount⟩ := prev
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcount
  obtain ⟨r,hr,hp⟩ := polynomial_window_mass ha hau
  refine ⟨c*r,mul_pos hc hr,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hp,
    (tendsto_rpow_atTop (sub_pos.mpr hu)).eventually_ge_atTop N] with x hx hmass hN0
  have hx1 : 1<x := by linarith only [hx]
  have hx0 := zero_lt_one.trans hx1
  let P := windowPrimes (x^a) (x^u)
  let V (p : ℕ) := smoothSignOctave (!b) t (x/p)
  let E (p : ℕ) := (V p).image (· * p)
  have pf {p : ℕ} (h : p ∈ P) := (mem_windowPrimes (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx0.le _)).1 h
  have xp {p : ℕ} (h : p ∈ P) :
      x^(1-u) ≤ x/(p:ℝ) ∧ x/(p:ℝ) ≤ x^(1-a) := by
    obtain ⟨hp,hlo,hhi⟩ := pf h
    have hp0 := (Nat.cast_pos (α := ℝ)).mpr hp.pos
    constructor
    · apply (le_div_iff₀ hp0).2
      calc _ ≤ x^(1-u)*x^u := mul_le_mul_of_nonneg_left hhi (Real.rpow_nonneg hx0.le _)
           _ = x := by rw [←Real.rpow_add hx0,sub_add_cancel,Real.rpow_one]
    · apply (div_le_iff₀ hp0).2
      calc x = x^(1-a)*x^a := by rw [←Real.rpow_add hx0,sub_add_cancel,Real.rpow_one]
           _ ≤ _ := mul_le_mul_of_nonneg_left hlo.le (Real.rpow_nonneg hx0.le _)
  have facts {p m : ℕ} (hp : p ∈ P) (hm : m ∈ V p) :
      m ≠ 0 ∧ (∀ q ∈ m.primeFactors,q<p) ∧ m*p ∈ smoothSignOctave b u x := by
    obtain ⟨hpr,hlo,hhi⟩ := pf hp
    have hp0 := (Nat.cast_pos (α := ℝ)).mpr hpr.pos
    obtain ⟨hi,hl,hμ,hsm⟩ := mem_filter.mp hm
    obtain ⟨hm1,hmU⟩ := mem_Icc.mp hi
    have hm0 := Nat.ne_of_gt hm1
    have hr : (x/(p:ℝ))^t ≤ x^a := by
      apply (Real.rpow_le_rpow (div_nonneg hx0.le hp0.le) (xp hp).2 ht.le).trans_eq
      rw [←Real.rpow_mul hx0.le,htop]
    have htop' (q : ℕ) (hq : q ∈ m.primeFactors) : q<p :=
      Nat.cast_lt.mp (((hsm q hq).trans hr).trans_lt hlo)
    have cop : m.Coprime p := (hpr.coprime_iff_not_dvd.2 (fun h => (lt_irrefl p)
      (htop' p (Nat.mem_primeFactors.mpr ⟨hpr,h,hm0⟩)))).symm
    have hu' := (Nat.cast_le.mpr hmU).trans (Nat.floor_le (div_nonneg hx0.le hp0.le))
    have hl' : x/2 < (m:ℝ)*p := (div_lt_iff₀ hp0).1 (by
      calc (x/2)/(p:ℝ) = (x/(p:ℝ))/2 := by ring
           _ < _ := hl)
    have hmul : ((m*p:ℕ):ℝ) ≤ x := by
      rw [Nat.cast_mul]; exact (le_div_iff₀ hp0).1 hu'
    refine ⟨hm0,htop',mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm1 hpr.pos,Nat.le_floor hmul⟩,
      by simpa only [Nat.cast_mul] using hl',?_,?_⟩⟩
    · rw [isMultiplicative_moebius.map_mul_of_coprime cop,hμ,moebius_apply_prime hpr]
      cases b <;> decide
    · intro q hq
      obtain ⟨hq',hd,_⟩ := Nat.mem_primeFactors.mp hq
      rcases hq'.dvd_mul.mp hd with hm | hp'
      · exact (Nat.cast_le.mpr (htop' q (Nat.mem_primeFactors.mpr ⟨hq',hm,hm0⟩)).le).trans hhi
      · exact ((Nat.prime_dvd_prime_iff_eq hq' hpr).1 hp') ▸ hhi
  have dis : (P: Set ℕ).PairwiseDisjoint E := by
    intro p hp q hq hne
    apply disjoint_left.mpr
    intro n hn hn'
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨v,hv,he⟩ := mem_image.mp hn'
    obtain ⟨hm0,hmt,_⟩ := facts hp hm
    obtain ⟨hv0,hvt,_⟩ := facts hq hv
    have hstem := congrArg stem he
    rw [stem_mul_of_largest hv0 (pf hq).1 hvt,stem_mul_of_largest hm0 (pf hp).1 hmt] at hstem
    rw [hstem] at he
    exact hne (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) he.symm)
  have he (p : ℕ) (hp : p ∈ P) : (E p).card=(V p).card :=
    card_image_of_injOn (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right (pf hp).1.pos h)
  have sub : P.biUnion E ⊆ smoothSignOctave b u x := by
    intro n hn
    obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hv
    exact (facts hp hm).2.2
  have count := card_le_card sub
  rw [card_biUnion dis,sum_congr rfl he] at count
  have hh := (Nat.cast_le (α := ℝ)).mpr count
  push_cast only [Nat.cast_sum] at hh
  calc c*r*x ≤ (c*x)*∑ p ∈ P,1/(p:ℝ) := by
         rw [mul_right_comm c r x]; exact mul_le_mul_of_nonneg_left hmass (mul_nonneg hc.le hx0.le)
       _ = ∑ p ∈ P,c*(x/(p:ℝ)) := by rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
       _ ≤ ∑ p ∈ P,((V p).card:ℝ) := sum_le_sum (fun p hp => hN _ (hN0.trans (xp hp).1))
       _ ≤ _ := hh

private theorem smooth_induction (k : ℕ) (b : Bool) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ x : ℝ in atTop,c*x ≤ ((smoothSignOctave b (2/((k:ℝ)+2)) x).card:ℝ) := by
  induction k generalizing b with
  | zero => simpa using base_density b
  | succ k ih =>
    let a := 2/((k:ℝ)+4)
    let u := 2/((k:ℝ)+3)
    let t := 2/((k:ℝ)+2)
    have h0 := Nat.cast_nonneg (α := ℝ) k
    have ha : 0<a := by dsimp only [a]; positivity
    have hau : a<u := div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith only [h0])
    have hu : u<1 := (div_lt_one (by positivity)).2 (by linarith only [h0])
    have he : (1-a)*t=a := by dsimp only [a,t]; field_simp; ring
    have hh := smooth_step b ha hau hu (show 0<t by dsimp only [t]; positivity) he (ih (!b))
    simpa only [Nat.cast_succ,show (k:ℝ)+1+2=(k:ℝ)+3 by ring] using hh

/-- Every fixed smoothness exponent leaves a positive lower density of
each Möbius sign in every sufficiently large sharp octave. -/
theorem both_signs_at_every_smoothness_exponent {δ : ℝ} (hδ : 0<δ) (b : Bool) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ x : ℝ in atTop,c*x ≤ ((smoothSignOctave b δ x).card:ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2/δ)
  have hle : 2/((k:ℝ)+2) ≤ δ := (div_le_iff₀ (by positivity)).2 (by
    linarith only [(div_lt_iff₀ hδ).1 hk,hδ])
  obtain ⟨c,hc,h⟩ := smooth_induction k b
  refine ⟨c,hc,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx hx1
  apply hx.trans (Nat.cast_le.mpr (card_le_card ?_))
  intro n hn
  obtain ⟨hi,hl,hm,ht⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hi,hl,hm,fun q hq => (ht q hq).trans (Real.rpow_le_rpow_of_exponent_le hx1 hle)⟩

end GaloisForLFunctions.RestrictedFactorizationCalculus
