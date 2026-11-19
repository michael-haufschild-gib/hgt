import GaloisForLFunctions.PrimeTorusTheory.TheFiniteTimeBohrIsometry
import GaloisForLFunctions.RHTower.SixExponentials.PrimePowers

/-!
# Unit crossings of the three-prime resonator

The trace identity in the proof of El Kaouni's Proposition 6.13
(arXiv:2610.42022) factors the unit level of a three-phase sum into
three antipodal walls. On a logarithmic orbit of distinct primes the
three wall clocks never ring together. Their total crossing density
depends only on the largest and smallest prime.
-/

noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.PrimeTorusTheory.ThreePhase

/-- Factorization of the trace defect on the three-dimensional unit torus. -/
theorem unit_trace_factor {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    ((‖a+b+c‖^2-1 : ℝ):ℂ)*(a*b*c) = (a+b)*(a+c)*(b+c) := by
  have hzero {z : ℂ} (hz : ‖z‖=1) : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)
  rw [Complex.ofReal_sub, Complex.ofReal_one, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self, map_add, map_add,
    ← Complex.inv_eq_conj ha, ← Complex.inv_eq_conj hb, ← Complex.inv_eq_conj hc]
  field_simp [hzero ha,hzero hb,hzero hc] <;> ring

/-- Absolute trace defect is exactly the product of the three antipodal
chords. This measures near misses as well as exact crossings. -/
theorem abs_trace_defect {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |‖a+b+c‖^2-1| = ‖a+b‖*‖a+c‖*‖b+c‖ := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ha,hb,hc,mul_one] using
    congrArg norm (unit_trace_factor ha hb hc)

theorem unit_trace_iff {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    ‖a+b+c‖=1 ↔ b = -a ∨ c = -a ∨ c = -b := by
  have h := abs_trace_defect ha hb hc
  have hu : ‖a+b+c‖=1 ↔ |‖a+b+c‖^2-1|=0 := by
    rw [abs_eq_zero,sub_eq_zero]
    constructor
    · intro he; rw [he,one_pow]
    · intro he; nlinarith only [he,norm_nonneg (a+b+c)]
  rw [hu,h]
  simp only [mul_eq_zero,norm_eq_zero,add_eq_zero_iff_neg_eq,or_assoc,eq_comm (a := -a),
    eq_comm (a := -b)]

private theorem one_le_largest_chord {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    1 ≤ ‖a+b‖ ∨ 1 ≤ ‖a+c‖ ∨ 1 ≤ ‖b+c‖ := by
  have energy : ‖a+b‖^2+‖a+c‖^2+‖b+c‖^2 =
      ‖a‖^2+‖b‖^2+‖c‖^2+‖a+b+c‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im]
    ring
  rw [ha,hb,hc] at energy
  by_contra! h
  have small {z : ℂ} (hz : ‖z‖ < 1) : ‖z‖^2 < 1 := by
    simpa using pow_lt_pow_left₀ hz (norm_nonneg z) (by decide : 2 ≠ 0)
  linarith only [energy,small h.1,small h.2.1,small h.2.2,sq_nonneg ‖a+b+c‖]

/-- Quadratic stability of the antipodal walls. At least one of the three
chords has length one or greater, so the defect bounds the square of
the distance to the nearest wall. -/
theorem small_defect_forces_antipodes {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    {ε : ℝ} (hε : 0 ≤ ε) (he : |‖a+b+c‖^2-1| ≤ ε^2) :
    ‖a+b‖ ≤ ε ∨ ‖a+c‖ ≤ ε ∨ ‖b+c‖ ≤ ε := by
  rw [abs_trace_defect ha hb hc] at he
  by_contra! hn
  have hprod {x y z : ℝ} (hx : ε < x) (hy : ε < y) (hz : 1 ≤ z) :
      ε^2 < x*y*z := by
    have hxy : ε*ε < x*y := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hx.le hy hε (hε.trans_lt hx)
    exact (by simpa only [sq] using hxy).trans_le
      (le_mul_of_one_le_right (mul_nonneg (hε.trans hx.le) (hε.trans hy.le)) hz)
  rcases one_le_largest_chord ha hb hc with h | h | h
  · linarith only [he,hprod hn.2.1 hn.2.2 h]
  · linarith only [he,hprod hn.1 hn.2.2 h]
  · exact (hprod hn.1 hn.2.1 h).not_ge he

/-- A pair of integer phases becomes antipodal exactly at the odd
half-periods of its logarithmic gap. -/
theorem phase_antipodal_iff (a b : ℕ) (t : ℝ) :
    nPhase b t = -nPhase a t ↔ ∃ j : ℤ, (Real.log b-Real.log a)*t = (2*j+1)*Real.pi := by
  unfold nPhase
  rw [show -cexp (I * ((Real.log a:ℂ)*(t:ℂ))) =
    cexp (I * ((Real.log a:ℂ)*(t:ℂ)) + Real.pi*I) by rw [Complex.exp_add,Complex.exp_pi_mul_I]; ring,
    Complex.exp_eq_exp_iff_exists_int]
  apply exists_congr
  intro j
  constructor
  · intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.intCast_re,Complex.intCast_im,
      Complex.ofNat_re,Complex.ofNat_im] at hi
    linarith only [hi]
  · intro he
    have h := congrArg ((↑) : ℝ → ℂ) he
    push_cast at h
    linear_combination I*h

private def oddCount (w T : ℝ) : ℕ := ⌊(T*w/Real.pi+1)/2⌋₊

private def clock (w T : ℝ) : Finset ℝ := (range (oddCount w T)).image
  (fun j : ℕ => (2*j+1)*Real.pi/w)

private theorem mem_clock {w T t : ℝ} (hw : 0 < w) (hT : 0 ≤ T) :
    t ∈ clock w T ↔ 0 < t ∧ t ≤ T ∧ ∃ j : ℤ, w*t = (2*j+1)*Real.pi := by
  have hnon : 0 ≤ (T*w/Real.pi+1)/2 := by positivity
  have hpos := Real.pi_pos
  have hbound (j : ℕ) : j < oddCount w T ↔ (2*(j:ℝ)+1)*Real.pi/w ≤ T := by
    change j+1 ≤ ⌊_⌋₊ ↔ _
    rw [Nat.le_floor_iff hnon, div_le_iff₀ hw]
    push_cast
    constructor <;> intro h
    · have h' : (2*(j:ℝ)+1) ≤ T*w/Real.pi := by linarith only [h]
      exact (le_div_iff₀ hpos).mp h'
    · have h' := (le_div_iff₀ hpos).mpr h
      linarith only [h']
  rw [clock, mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨by positivity,(hbound j).mp (mem_range.mp hj), (j:ℤ), ?_⟩
    push_cast
    field_simp
  · rintro ⟨ht,htT,j,hj⟩
    have hh : 0 < (2*(j:ℝ)+1) := pos_of_mul_pos_left (hj ▸ mul_pos hw ht) hpos.le
    have hj0 : 0 ≤ j := by
      by_contra! h
      have hn : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      linarith only [hh,hn]
    lift j to ℕ using hj0 with k
    push_cast at hj
    have he : (2*(k:ℝ)+1)*Real.pi/w=t := (div_eq_iff hw.ne').mpr (by linarith only [hj])
    exact ⟨k,mem_range.mpr ((hbound k).mpr (he.symm ▸ htT)),he⟩

private theorem card_clock {w : ℝ} (hw : 0 < w) (T : ℝ) : (clock w T).card = oddCount w T := by
  rw [clock, card_image_of_injective,card_range]
  intro i j he
  have h := (div_left_inj' hw.ne').mp he
  have h' := mul_right_cancel₀ Real.pi_ne_zero h
  exact_mod_cast (show (i:ℝ) = j by linarith only [h'])

private def independent (x y : ℝ) : Prop :=
  ∀ a b : ℤ, (a:ℝ)*x+(b:ℝ)*y=0 → a=0 ∧ b=0

private theorem disjoint_clocks {x y T : ℝ} (hx : 0 < x) (hy : 0 < y) (hT : 0 ≤ T)
    (hi : independent x y) : Disjoint (clock x T) (clock y T) := by
  apply disjoint_left.mpr
  intro t htx hty
  obtain ⟨ht,_,j,hj⟩ := (mem_clock hx hT).mp htx
  obtain ⟨_,_,k,hk⟩ := (mem_clock hy hT).mp hty
  have hcross : t*((2*(k:ℝ)+1)*x-(2*(j:ℝ)+1)*y)=0 := by
    linear_combination (2*(k:ℝ)+1)*hj - (2*(j:ℝ)+1)*hk
  have hz := (mul_eq_zero.mp hcross).resolve_left ht.ne'
  have h := hi (2*k+1) (-(2*j+1)) (by push_cast; linarith only [hz])
  omega

private theorem independent_prime_gaps {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) : independent (Real.log q-Real.log p) (Real.log r-Real.log q) := by
  intro a b he
  have hreal : ((-a:ℤ):ℝ)*Real.log p+((a-b:ℤ):ℝ)*Real.log q+(b:ℝ)*Real.log r=0 := by
    push_cast
    linarith only [he]
  have h := GaloisForLFunctions.RHTower.SixExponentials.prime_logs_independent hp hq hr
    hpq.ne (hpq.trans hqr).ne hqr.ne (-a) (a-b) b (by exact_mod_cast hreal)
  omega

/-- The actual set of positive unit crossings up to the given height. -/
def crossingTimes (p q r : ℕ) (T : ℝ) : Finset ℝ :=
  clock (Real.log q-Real.log p) T ∪ clock (Real.log r-Real.log q) T ∪ clock (Real.log r-Real.log p) T

theorem mem_crossingTimes {p q r : ℕ} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    {T t : ℝ} (hT : 0 ≤ T) :
    t ∈ crossingTimes p q r T ↔ 0 < t ∧ t ≤ T ∧ ‖nPhase p t+nPhase q t+nPhase r t‖=1 := by
  have posGap {a b : ℕ} (ha : 0 < a) (hab : a < b) : 0 < Real.log b-Real.log a :=
    sub_pos.mpr (Real.log_lt_log (by exact_mod_cast ha) (by exact_mod_cast hab))
  simp only [crossingTimes,mem_union,mem_clock (posGap hp hpq) hT,
    mem_clock (posGap (hp.trans hpq) hqr) hT,mem_clock (posGap hp (hpq.trans hqr)) hT,
    unit_trace_iff (norm_nPhase _ _) (norm_nPhase _ _) (norm_nPhase _ _),phase_antipodal_iff]
  tauto

/-- Three exact lattice counts give the unit crossings of distinct prime
phases, with no multiple counting at simultaneous resonances. -/
theorem card_crossingTimes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) {T : ℝ} (hT : 0 ≤ T) :
    (crossingTimes p q r T).card =
      ⌊(T*(Real.log q-Real.log p)/Real.pi+1)/2⌋₊ +
      ⌊(T*(Real.log r-Real.log q)/Real.pi+1)/2⌋₊ +
      ⌊(T*(Real.log r-Real.log p)/Real.pi+1)/2⌋₊ := by
  let x := Real.log q-Real.log p
  let y := Real.log r-Real.log q
  have hx : 0 < x := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpq))
  have hy : 0 < y := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqr))
  have hi := independent_prime_gaps hp hq hr hpq hqr
  have hxy : Real.log r-Real.log p=x+y := by dsimp [x,y]; ring
  have hi₁ : independent x (x+y) := by
    intro a b he
    have h := hi (a+b) b (by push_cast; change _*x+_*y=0; linarith only [he])
    omega
  have hi₂ : independent y (x+y) := by
    intro a b he
    have h := hi b (a+b) (by push_cast; change _*x+_*y=0; linarith only [he])
    omega
  change ((clock x T ∪ clock y T) ∪ clock (Real.log r-Real.log p) T).card =
    oddCount x T + oddCount y T + oddCount (Real.log r-Real.log p) T
  rw [hxy,card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_clocks hx (add_pos hx hy) hT hi₁,
    disjoint_clocks hy (add_pos hx hy) hT hi₂⟩), card_union_of_disjoint (disjoint_clocks hx hy hT hi),
    card_clock hx,card_clock hy,card_clock (add_pos hx hy)]

private theorem rounded_pair_error {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let R := fun x : ℝ => ⌊(x+1)/2⌋₊
    |((R u + R v + R (u+v) : ℕ) : ℝ) - (u+v)| ≤ 1 := by
  intro R
  have hr (x : ℝ) (hx : 0 ≤ x) : 2*(R x:ℝ)-1 ≤ x ∧ x ≤ 2*(R x:ℝ)+1 := by
    have h₁ := Nat.floor_le (show 0 ≤ (x+1)/2 by positivity)
    have h₂ := Nat.lt_floor_add_one ((x+1)/2)
    dsimp only [R]
    constructor <;> linarith only [h₁,h₂]
  obtain ⟨hu₁,hu₂⟩ := hr u hu
  obtain ⟨hv₁,hv₂⟩ := hr v hv
  obtain ⟨hw₁,hw₂⟩ := hr (u+v) (add_nonneg hu hv)
  rw [abs_le]
  push_cast
  rcases lt_trichotomy (R u+R v) (R (u+v)) with h | h | h
  · have h' : (R u:ℝ)+R v+1 ≤ R (u+v) := by exact_mod_cast Nat.succ_le_of_lt h
    constructor <;> linarith only [hu₁,hu₂,hv₁,hv₂,hw₁,hw₂,h']
  · have h' : (R u:ℝ)+R v=R (u+v) := by exact_mod_cast h
    constructor <;> linarith only [hw₁,hw₂,h']
  · have h' : (R (u+v):ℝ)+1 ≤ R u+R v := by exact_mod_cast Nat.succ_le_of_lt h
    constructor <;> linarith only [hu₁,hu₂,hv₁,hv₂,hw₁,hw₂,h']

/-- The counting error is at most one for every time. The middle prime
drops out of the linear term. Rounding the largest gap couples the
other two rounding errors since their unrounded gaps add exactly. -/
theorem crossing_count_error {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) {T : ℝ} (hT : 0 ≤ T) :
    |((crossingTimes p q r T).card : ℝ) - T*(Real.log r-Real.log p)/Real.pi| ≤ 1 := by
  rw [card_crossingTimes hp hq hr hpq hqr hT]
  have posGap {a b : ℕ} (ha : 0 < a) (hab : a < b) : 0 ≤ T*(Real.log b-Real.log a)/Real.pi :=
    div_nonneg (mul_nonneg hT (sub_nonneg.mpr (Real.log_le_log
      (by exact_mod_cast ha) (by exact_mod_cast hab.le)))) Real.pi_pos.le
  have he : T*(Real.log r-Real.log p)/Real.pi =
      T*(Real.log q-Real.log p)/Real.pi + T*(Real.log r-Real.log q)/Real.pi := by ring
  rw [he]
  exact rounded_pair_error (posGap hp.pos hpq) (posGap hq.pos hqr)

/-- End of the nth complete relative revolution of the two outer primes. -/
def outerPeriod (p r n : ℕ) := 2*(n:ℝ)*Real.pi/(Real.log r-Real.log p)

private theorem complementary_period_counts {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hi : independent x y) (n : ℕ) :
    let T := 2*(n:ℝ)*Real.pi/(x+y)
    oddCount x T + oddCount y T = n ∧ oddCount (x+y) T = n := by
  intro T
  let a := oddCount x T
  let b := oddCount y T
  have hxy := add_pos hx hy
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hs (w : ℝ) : T*w/Real.pi=2*n*w/(x+y) := by
    dsimp only [T]; field_simp [hxy.ne',Real.pi_ne_zero] <;> ring
  have htot : T*(x+y)/Real.pi=2*n := by rw [hs,mul_div_cancel_right₀ _ hxy.ne']
  have hsum : T*x/Real.pi+T*y/Real.pi=2*n := by rw [← htot]; ring
  have bounds {w : ℝ} (hw : 0 < w) :
      2*(oddCount w T:ℝ)-1 ≤ T*w/Real.pi ∧ T*w/Real.pi < 2*(oddCount w T:ℝ)+1 := by
    have h₁ := Nat.floor_le (show 0 ≤ (T*w/Real.pi+1)/2 by positivity)
    have h₂ := Nat.lt_floor_add_one ((T*w/Real.pi+1)/2)
    unfold oddCount
    constructor <;> linarith only [h₁,h₂]
  obtain ⟨ha₁,ha₂⟩ := bounds hx
  obtain ⟨hb₁,hb₂⟩ := bounds hy
  change 2*(a:ℝ)-1 ≤ _ at ha₁
  change _ < 2*(a:ℝ)+1 at ha₂
  change 2*(b:ℝ)-1 ≤ _ at hb₁
  change _ < 2*(b:ℝ)+1 at hb₂
  constructor
  · change a+b=n
    by_contra hn
    have hl : n < a+b+1 := by exact_mod_cast (show (n:ℝ) < (a:ℝ)+b+1 by linarith only [ha₂,hb₂,hsum])
    have hu : a+b ≤ n+1 := by exact_mod_cast (show (a:ℝ)+b ≤ n+1 by linarith only [ha₁,hb₁,hsum])
    have hab : (a:ℝ)+b=n+1 := by exact_mod_cast (show a+b=n+1 by omega)
    have htie : T*x/Real.pi = 2*(a:ℝ)-1 := by linarith only [ha₁,hb₁,hsum,hab]
    rw [hs,div_eq_iff hxy.ne'] at htie
    have h := hi (2*(n:ℤ)-(2*(a:ℤ)-1)) (-(2*(a:ℤ)-1)) (by push_cast; linarith only [htie])
    omega
  · unfold oddCount
    rw [htot]
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> push_cast <;> linarith

/-- After n complete outer periods exactly 2n unit crossings have
occurred. The two inner counts complement one another because the
half-integer rounding ties would contradict prime-log independence. -/
theorem card_at_outer_period {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (n : ℕ) :
    (crossingTimes p q r (outerPeriod p r n)).card = 2*n := by
  let x := Real.log q-Real.log p
  let y := Real.log r-Real.log q
  have hx : 0 < x := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpq))
  have hy : 0 < y := sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqr))
  have he : Real.log r-Real.log p=x+y := by dsimp [x,y]; ring
  have hp₀ : 0 ≤ outerPeriod p r n := by rw [outerPeriod,he]; positivity
  have h := complementary_period_counts hx hy (independent_prime_gaps hp hq hr hpq hqr) n
  rw [card_crossingTimes hp hq hr hpq hqr hp₀]
  change oddCount x _ + oddCount y _ + oddCount (Real.log r-Real.log p) _ = 2*n
  simp only [outerPeriod,he,h.1,h.2,two_mul]

/-- Every complete outer period contains exactly two crossings. One
is the outer pair's antipodal time, leaving exactly one inner pair
crossing in each period, irrespective of the middle prime. -/
theorem two_crossings_each_outer_period {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (n : ℕ) :
    ((crossingTimes p q r (outerPeriod p r (n+1))) ∖ (crossingTimes p q r (outerPeriod p r n))).card = 2 := by
  have hg := sub_pos.mpr (Real.log_lt_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_lt.mpr (hpq.trans hqr)))
  have hn : 0 ≤ outerPeriod p r n := by unfold outerPeriod; positivity
  have hle : outerPeriod p r n ≤ outerPeriod p r (n+1) := by
    unfold outerPeriod
    apply div_le_div_of_nonneg_right _ hg.le
    push_cast
    linarith only [Real.pi_pos]
  have hs : crossingTimes p q r (outerPeriod p r n) ⊆ crossingTimes p q r (outerPeriod p r (n+1)) := by
    intro t ht
    obtain ⟨h₁,h₂,h₃⟩ := (mem_crossingTimes hp.pos hpq hqr hn).mp ht
    exact (mem_crossingTimes hp.pos hpq hqr (hn.trans hle)).mpr ⟨h₁,h₂.trans hle,h₃⟩
  rw [card_sdiff_of_subset hs,card_at_outer_period hp hq hr hpq hqr,card_at_outer_period hp hq hr hpq hqr]
  omega

#print axioms card_at_outer_period
#print axioms two_crossings_each_outer_period
#print axioms unit_trace_factor
#print axioms abs_trace_defect
#print axioms unit_trace_iff
#print axioms small_defect_forces_antipodes
#print axioms phase_antipodal_iff
#print axioms mem_crossingTimes
#print axioms card_crossingTimes
#print axioms crossing_count_error
end GaloisForLFunctions.PrimeTorusTheory.ThreePhase
