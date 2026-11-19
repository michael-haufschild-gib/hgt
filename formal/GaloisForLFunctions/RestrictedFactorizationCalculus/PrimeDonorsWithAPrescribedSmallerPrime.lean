import GaloisForLFunctions.RestrictedFactorizationCalculus.AlternatingCofactorDescent
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import Mathlib.Analysis.PSeries

/-!
# Prime donors with a prescribed smaller split prime

Primes r in short multiplicative cells can all be paired to distinct primes
v near pr. Spacing the cells by the factor 2p keeps every donor and every
partner distinct. Their reciprocal mass diverges by the ordinary prime
number theorem and the harmonic series.
-/

noncomputable section

open Finset Filter RHTower
open scoped Classical Topology

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem eventually_donor_counts {p α : ℝ} (hp : 2 ≤ p) (ha : 1<α) (ha2 : α ≤ 5/4) :
    ∀ᶠ T : ℝ in atTop, (windowPrimes T (α*T)).card ≤ (windowPrimes (p*T) (α*(p*T))).card ∧
      ((α-1)/2)*T/Real.log T ≤ ((windowPrimes T (α*T)).card:ℝ) := by
  obtain ⟨U,_,upper⟩ := exists_card_windowPrimes_le 1 (ε := 1/10) (by norm_num)
  obtain ⟨L,_,lower⟩ := exists_card_windowPrimes_div_ge 1 (ε := 1/10) (by norm_num)
  filter_upwards [eventually_ge_atTop (max 3 (max U L)),
    Real.tendsto_log_atTop.eventually_ge_atTop (1/(α-1)),
    Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log (2*p))] with T hT hlog hlogP
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0<T := by linarith only [hT3]
  have hT1 : 1<T := by linarith only [hT3]
  have hL := Real.log_pos hT1
  have hα := sub_pos.mpr ha
  have hgap := (div_le_iff₀ hα).1 hlog
  have gap {x : ℝ} (hx : T ≤ x) : x/Real.log x^(1:ℝ) ≤ α*x-x := by
    have hx0 := hT0.trans_le hx
    have hlogx := Real.log_le_log hT0 hx
    rw [Real.rpow_one,show α*x-x=(α-1)*x by ring,div_le_iff₀ (hL.trans_le hlogx)]
    have hh := mul_le_mul_of_nonneg_right hlogx hα.le
    nlinarith only [mul_le_mul_of_nonneg_right (hgap.trans hh) hx0.le]
  have hlow (d : ℝ) (hd : 1 ≤ d) (hdp : d ≤ p) :
      (3/5)*((α-1)*(d*T))/Real.log T ≤ ((windowPrimes (d*T) (α*(d*T))).card:ℝ) := by
    let x := 2*(d*T)
    have hd0 := zero_lt_one.trans_le hd
    have hx : T ≤ x := by dsimp only [x]; nlinarith only [mul_le_mul_of_nonneg_right hd hT0.le,hT0]
    have hx0 := hT0.trans_le hx
    have hx0L := hL.trans_le (Real.log_le_log hT0 hx)
    have hscale : x ≤ α*x := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.le hx0.le
    have hceil : α*x ≤ 2*x := mul_le_mul_of_nonneg_right (by linarith only [ha2]) hx0.le
    have hl := lower x (((le_max_right _ _).trans ((le_max_right _ _).trans hT)).trans hx)
      2 (by norm_num) (by norm_num) x (α*x) le_rfl hscale hceil (gap hx)
    have hA : x/2=d*T := by dsimp [x]; ring
    have hB : α*x/2=α*(d*T) := by dsimp [x]; ring
    rw [hA,hB] at hl
    have hlogd := Real.log_le_log (by positivity : 0<2*d) (mul_le_mul_of_nonneg_left hdp (by norm_num : 0 ≤ (2:ℝ)))
    have hlogx : Real.log x ≤ (3/2)*Real.log T := by
      rw [show x=(2*d)*T by dsimp [x]; ring,Real.log_mul (by positivity) hT0.ne']
      linarith only [hlogP,hlogd]
    have hs := mul_le_mul_of_nonneg_left hlogx (mul_nonneg hα.le (mul_nonneg hd0.le hT0.le))
    apply le_trans _ hl
    rw [div_le_div_iff₀ hL (by positivity)]
    dsimp only [x] at *
    nlinarith only [hs]
  have hu := upper T ((le_max_left _ _).trans ((le_max_right _ _).trans hT)) T (α*T) le_rfl
    (by nlinarith only [mul_nonneg hα.le hT0.le]) (mul_le_mul_of_nonneg_right (by linarith only [ha2]) hT0.le) (gap le_rfl)
  have hpr := hlow p (by linarith only [hp]) le_rfl
  have hsingle := hlow 1 le_rfl (by linarith only [hp])
  rw [one_mul] at hsingle
  constructor
  · apply Nat.cast_le.mp (hu.trans (le_trans ?_ hpr))
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [mul_le_mul_of_nonneg_right hp (mul_nonneg hα.le hT0.le)]
  · apply le_trans _ hsingle
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [mul_nonneg hα.le hT0.le]

/-- Every donor prime has a distinct larger prime close to its multiple by
p. All primes involved at either end exceed the prescribed lower cutoff. -/
def DonorPairs (p J V : ℕ) (R : Finset ℕ) (f : ℕ → ℕ) := Set.InjOn f R ∧
  Disjoint R (R.image f) ∧ ∀ r ∈ R,r.Prime ∧ V<r ∧ (f r).Prime ∧
    (3/2:ℝ)*r ≤ f r ∧ |(f r:ℝ)-p*r| ≤ ((p:ℝ)*r)/J ∧
    |(f r:ℝ)-p*r| ≤ (f r:ℝ)/J


/-- Above any prescribed finite set, pairs for one prescribed smaller
prime can carry arbitrarily large reciprocal donor mass. -/
theorem arbitrarily_large_donor_mass {p J : ℕ} (hp : p.Prime) (hJ : 0<J) (V : ℕ) (L : ℝ) :
    ∃ R : Finset ℕ, ∃ f : ℕ → ℕ, DonorPairs p J V R f ∧ L ≤ ∑ r ∈ R,1/(r:ℝ) := by
  let α := 1+1/(4*(J:ℝ))
  let B := 2*(p:ℝ)
  have hj : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hj0 : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have ha : 1<α := by dsimp [α]; positivity
  have ha2 : α ≤ 5/4 := by
    dsimp only [α]
    have he := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4)
      (show (4:ℝ) ≤ 4*J by linarith only [hj])
    linarith only [he]
  have ha0 := zero_lt_one.trans ha
  have hB : 1<B := by dsimp only [B]; linarith only [hp2]
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_donor_counts hp2 ha ha2)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hB).eventually_ge_atTop (max H (V:ℝ)))
  let T (i : ℕ) := B^((K+1)*(i+1))
  have t0 (i : ℕ) : 0<T i := pow_pos (zero_lt_one.trans hB) _
  have tL (i : ℕ) : max H (V:ℝ) ≤ T i :=
    hK _ (by nlinarith only [Nat.zero_le i,Nat.zero_le K,Nat.zero_le (K*i)])
  let R (i : ℕ) := windowPrimes (T i) (α*T i)
  let P (i : ℕ) := windowPrimes ((p:ℝ)*T i) (α*((p:ℝ)*T i))
  let f (i : ℕ) := rankedSlot (R i) (P i)
  have supply (i : ℕ) := hH (T i) ((le_max_left ..).trans (tL i))
  have rmem {i r : ℕ} (h : r ∈ R i) := (mem_windowPrimes (t0 i).le (mul_nonneg ha0.le (t0 i).le)).1 h
  have pmem {i r : ℕ} (h : r ∈ R i) : (f i r).Prime ∧ (p:ℝ)*T i<f i r ∧ (f i r:ℝ) ≤ α*((p:ℝ)*T i) :=
    (mem_windowPrimes (mul_nonneg hp0.le (t0 i).le) (by positivity)).1 (rankedSlot_mem (supply i).1 h)
  have sep {i j : ℕ} (h : i<j) : B*T i ≤ T j := by
    rw [show B*T i=B^((K+1)*(i+1)+1) by rw [pow_succ,mul_comm]; rfl]
    apply pow_le_pow_right₀ hB.le
    have hh := Nat.mul_le_mul_left (K+1) (Nat.succ_le_succ h)
    omega
  have unique {i j : ℕ} {x : ℝ} (hi : T i<x ∧ x ≤ B*T i) (hj : T j<x ∧ x ≤ B*T j) : i=j := by
    rcases lt_trichotomy i j with h | h | h
    · exact (hj.1.not_ge (hi.2.trans (sep h))).elim
    · exact h
    · exact (hi.1.not_ge (hj.2.trans (sep h))).elim
  have rrange {i r : ℕ} (h : r ∈ R i) : T i<r ∧ (r:ℝ) ≤ B*T i :=
    ⟨(rmem h).2.1,(rmem h).2.2.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [B]; linarith only [ha2,hp2]) (t0 i).le)⟩
  have prange {i r : ℕ} (h : r ∈ R i) : T i<f i r ∧ (f i r:ℝ) ≤ B*T i := by
    have hh := pmem h
    have hlow : T i ≤ (p:ℝ)*T i := by nlinarith only [mul_le_mul_of_nonneg_right hp2 (t0 i).le,t0 i]
    refine ⟨hlow.trans_lt hh.2.1,hh.2.2.trans ?_⟩
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_right ha2 (mul_nonneg hp0.le (t0 i).le),
      mul_nonneg hp0.le (t0 i).le]
  let C := (α-1)/(2*(α*((K:ℝ)+1)*Real.log B))
  have hlogB := Real.log_pos hB
  have hC : 0<C := by dsimp only [C]; positivity
  have row (i : ℕ) : C*(1/((i:ℝ)+1)) ≤ ∑ r ∈ R i,1/(r:ℝ) := by
    have htlog : Real.log (T i)=((K:ℝ)+1)*((i:ℝ)+1)*Real.log B := by
      dsimp only [T]; rw [Real.log_pow]; push_cast; ring
    have hlogt : 0<Real.log (T i) := by rw [htlog]; positivity
    calc C*(1/((i:ℝ)+1)) = (((α-1)/2)*T i/Real.log (T i))*(1/(α*T i)) := by
           rw [htlog]; dsimp only [C]; field_simp; ring
         _ ≤ ((R i).card:ℝ)*(1/(α*T i)) := mul_le_mul_of_nonneg_right (supply i).2 (by positivity)
         _ = ∑ _r ∈ R i,1/(α*T i) := by simp
         _ ≤ _ := sum_le_sum (fun r hr => one_div_le_one_div_of_le
           (Nat.cast_pos.mpr (rmem hr).1.pos) (rmem hr).2.2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop (L/C))
  let I := range N
  let D := I.biUnion R
  have address {r : ℕ} (h : r ∈ D) : ∃ i : I,r ∈ R i := by
    obtain ⟨i,hi,hr⟩ := mem_biUnion.mp h
    exact ⟨⟨i,hi⟩,hr⟩
  let g (r : ℕ) := if h : r ∈ D then f (address h).choose r else 0
  have eval (i : I) {r : ℕ} (h : r ∈ R i) : g r=f i r := by
    have hd : r ∈ D := mem_biUnion.mpr ⟨i,i.property,h⟩
    have he : (address hd).choose=i := Subtype.ext (unique (rrange (address hd).choose_spec) (rrange h))
    simp only [g,dif_pos hd,he]
  have hinj : Set.InjOn g D := by
    intro r hr s hs eq
    obtain ⟨i,hi⟩ := address hr
    obtain ⟨j,hj⟩ := address hs
    rw [eval i hi,eval j hj] at eq
    have hh := prange hi
    rw [eq] at hh
    have he : i=j := Subtype.ext (unique hh (prange hj))
    subst j
    exact rankedSlot_inj (supply i).1 hi hj eq
  refine ⟨D,g,⟨hinj,?_,?_⟩,?_⟩
  · apply disjoint_left.mpr
    intro r hr h
    obtain ⟨s,hs,he⟩ := mem_image.mp h
    obtain ⟨i,hi⟩ := address hr
    obtain ⟨j,hj⟩ := address hs
    rw [eval j hj] at he
    have hh := prange hj
    rw [he] at hh
    have hij : i=j := Subtype.ext (unique (rrange hi) hh)
    subst j
    have hv := (pmem hj).2.1
    rw [he] at hv
    exact hv.not_ge ((rmem hi).2.2.trans (mul_le_mul_of_nonneg_right (by linarith only [ha2,hp2]) (t0 _).le))
  · intro r hr
    obtain ⟨i,hi⟩ := address hr
    rw [eval i hi]
    obtain ⟨hr',hrlo,hrhi⟩ := rmem hi
    obtain ⟨hv',hvlo,hvhi⟩ := pmem hi
    have hv : V<r := Nat.cast_lt.mp (((le_max_right ..).trans (tL i)).trans_lt hrlo)
    have gap : |(f i r:ℝ)-p*r| ≤ (α-1)*((p:ℝ)*T i) := by
      apply abs_le.mpr
      constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hrhi hp0.le,
        mul_le_mul_of_nonneg_left hrlo.le hp0.le,hvhi,hvlo.le]
    have gapJ : (α-1)*((p:ℝ)*T i) ≤ ((p:ℝ)*T i)/J := by
      rw [show α-1=1/(4*(J:ℝ)) by dsimp [α]; ring]
      field_simp [hj0.ne']
      nlinarith only [mul_nonneg hp0.le (t0 i).le]
    refine ⟨hr',hv,hv',?_,(gap.trans gapJ).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrlo.le hp0.le) hj0.le),
      (gap.trans gapJ).trans (div_le_div_of_nonneg_right hvlo.le hj0.le)⟩
    nlinarith only [hrhi,hvlo, mul_le_mul_of_nonneg_right hp2 (t0 i).le,
      mul_le_mul_of_nonneg_right ha2 (t0 i).le,t0 i]
  · have dis : (I : Set ℕ).PairwiseDisjoint R :=
      fun _ _ _ _ h => disjoint_left.mpr (fun _ ha hb => h (unique (rrange ha) (rrange hb)))
    change L ≤ ∑ r ∈ I.biUnion R,1/(r:ℝ)
    rw [sum_biUnion dis]
    have htot := (div_le_iff₀ hC).1 (hN N le_rfl)
    calc L ≤ C*(∑ i ∈ range N,1/((i:ℝ)+1)) := by simpa only [mul_comm] using htot
         _ = ∑ i ∈ I,C*(1/((i:ℝ)+1)) := mul_sum ..
         _ ≤ _ := sum_le_sum fun i _ => row i

end GaloisForLFunctions.RestrictedFactorizationCalculus
