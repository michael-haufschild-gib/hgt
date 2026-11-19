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

/-- A near-unit observation forces at least one near-antipodal pair.
The cubic threshold is uniform over the whole torus. -/
theorem small_defect_forces_antipodes {a b c : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1)
    {ε : ℝ} (hε : 0 ≤ ε) (he : |‖a+b+c‖^2-1| ≤ ε^3) :
    ‖a+b‖ ≤ ε ∨ ‖a+c‖ ≤ ε ∨ ‖b+c‖ ≤ ε := by
  rw [abs_trace_defect ha hb hc] at he
  by_contra! hn
  have hp : ε^3 < ‖a+b‖*‖a+c‖*‖b+c‖ := by
    rw [pow_succ, sq]
    exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (mul_le_mul hn.1.le hn.2.1.le hε (norm_nonneg _)) hn.2.2 hε
      (mul_pos (hε.trans_lt hn.1) (hε.trans_lt hn.2.1))
  exact hp.not_ge he

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
    refine ⟨by positivity,hbound j |>.mp (mem_range.mp hj), (j:ℤ), ?_⟩
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
    exact ⟨k,mem_range.mpr ((hbound k).mpr (he ▸ htT)),he⟩

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

/-- The counting error is at most three halves for every time. The middle
prime drops out of the linear term. -/
theorem crossing_count_error {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) {T : ℝ} (hT : 0 ≤ T) :
    |((crossingTimes p q r T).card : ℝ) - T*(Real.log r-Real.log p)/Real.pi| ≤ 3/2 := by
  rw [card_crossingTimes hp hq hr hpq hqr hT]
  push_cast
  have hround {w : ℝ} (hw : 0 ≤ w) :
      |(⌊(T*w/Real.pi+1)/2⌋₊:ℝ)-T*w/(2*Real.pi)| ≤ 1/2 := by
    have h1 := Nat.floor_le (show 0 ≤ (T*w/Real.pi+1)/2 by positivity)
    have h2 := Nat.lt_floor_add_one ((T*w/Real.pi+1)/2)
    rw [abs_le]
    constructor <;> linarith only [h1,h2]
  have posGap {a b : ℕ} (ha : 0 < a) (hab : a < b) : 0 ≤ Real.log b-Real.log a :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab.le))
  obtain ⟨h₁,h₂⟩ := abs_le.mp (hround (posGap hp.pos hpq))
  obtain ⟨h₃,h₄⟩ := abs_le.mp (hround (posGap hq.pos hqr))
  obtain ⟨h₅,h₆⟩ := abs_le.mp (hround (posGap hp.pos (hpq.trans hqr)))
  rw [abs_le]
  constructor <;> linarith only [h₁,h₂,h₃,h₄,h₅,h₆]

#print axioms unit_trace_factor
#print axioms abs_trace_defect
#print axioms unit_trace_iff
#print axioms small_defect_forces_antipodes
#print axioms phase_antipodal_iff
#print axioms mem_crossingTimes
#print axioms card_crossingTimes
#print axioms crossing_count_error
end GaloisForLFunctions.PrimeTorusTheory.ThreePhase
