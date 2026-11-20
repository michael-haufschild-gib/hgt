import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros
import GaloisForLFunctions.RHTower.XiWeilCriterionConverse
import GaloisForLFunctions.RHTower.Suzuki.SuzukiV0WeilForm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# One rational height comparison per Jensen degree

Doubling the height above a real root increases its Euclidean distance.
Conversely, a nonreal zero of the centered completed zeta cannot keep
halving its height through other zeros: those zeros would accumulate on
the real axis. Continuity makes a strict reversal visible at a rational
pair, and pointwise Jensen convergence preserves its margin at every
large degree. A recurrent schedule therefore needs only two evaluations
of each scaled Jensen polynomial.
-/

open Polynomial Complex Filter Topology Metric FiniteFreeProbability RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private def pointAtHeight (x y : ℝ) : ℂ := ⟨x,y⟩

private theorem continuous_pointAtHeight {α : Type*} [TopologicalSpace α]
    {x y : α → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun a => pointAtHeight (x a) (y a)) := by
  have he : (fun a => pointAtHeight (x a) (y a)) =
      fun a => (x a:ℂ)+(y a:ℂ)*I := by
    funext a
    apply Complex.ext <;> simp [pointAtHeight]
  rw [he]
  exact (continuous_ofReal.comp hx).add ((continuous_ofReal.comp hy).mul continuous_const)

private theorem real_root_double (x y : ℝ) {r : ℂ} (hr : r.im=0) :
    ‖pointAtHeight x y-r‖ ≤ ‖pointAtHeight x (2*y)-r‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    pointAtHeight,hr,sub_zero]
  nlinarith only [sq_nonneg y]

/-- The modulus of a polynomial with real roots increases on doubling
either signed height at a fixed real abscissa. -/
theorem real_rooted_height_doubling (P : ℂ[X]) (h : ∀ r ∈ P.roots, r.im=0) (x y : ℝ) :
    ‖P.eval ⟨x,y⟩‖ ≤ ‖P.eval ⟨x,2*y⟩‖ := by
  have prod (l : Multiset ℂ) (hl : ∀ r∈l, r.im=0) :
      ‖(l.map (fun r => pointAtHeight x y-r)).prod‖ ≤
        ‖(l.map (fun r => pointAtHeight x (2*y)-r)).prod‖ := by
    induction l using Multiset.induction_on with
    | empty => simp
    | cons r l ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
      exact mul_le_mul (real_root_double x y (hl r (Multiset.mem_cons_self ..)))
        (ih (fun a ha => hl a (Multiset.mem_cons_of_mem ha))) (norm_nonneg _) (norm_nonneg _)
  have sp := IsAlgClosed.splits P
  rw [sp.eval_eq_prod_roots,sp.eval_eq_prod_roots,norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_left (prod _ h) (norm_nonneg _)

/-- Change in the modulus between rational heights y and 2y at abscissa x. -/
def rationalHeightGain (F : ℂ → ℂ) (v : ℚ × ℚ) : ℝ :=
  ‖F ⟨v.1,2*(v.2:ℝ)⟩‖ - ‖F ⟨v.1,v.2⟩‖

private theorem real_doubling_of_rational (h : ∀ v, 0≤rationalHeightGain XiC v) (x y : ℝ) :
    ‖XiC (pointAtHeight x y)‖ ≤ ‖XiC (pointAtHeight x (2*y))‖ := by
  have hc : Continuous XiC := continuousOn_univ.mp XiC_analytic.continuousOn
  have hr : DenseRange (fun a : ℚ => (a:ℝ)) := Rat.denseRange_cast
  apply (hr.prodMap hr).induction_on (x,y)
    (p:=fun v : ℝ × ℝ => ‖XiC (pointAtHeight v.1 v.2)‖ ≤ ‖XiC (pointAtHeight v.1 (2*v.2))‖)
  · exact isClosed_le ((hc.comp (continuous_pointAtHeight continuous_fst continuous_snd)).norm)
      ((hc.comp (continuous_pointAtHeight continuous_fst (continuous_const.mul continuous_snd))).norm)
  · intro v
    exact sub_nonneg.mp (h v)

/-- Testing just one dilation on rational vertical lines forces all zeros
onto the real axis. Iterated halving would otherwise violate isolation. -/
theorem rh_of_XiC_rational_height_doubling (h : ∀ v, 0≤rationalHeightGain XiC v) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_forall_XiC_zero_im_eq_zero.mpr
  intro z hz
  by_contra hi
  let t (n : ℕ) := z.im*(1/2:ℝ)^n
  have zero (n : ℕ) : XiC (pointAtHeight z.re (t n))=0 := by
    induction n with
    | zero => simpa [t,pointAtHeight] using hz
    | succ n ih =>
      have step := real_doubling_of_rational h z.re (t (n+1))
      have he : 2*t (n+1)=t n := by dsimp only [t]; rw [pow_succ]; ring
      rw [he,ih,norm_zero] at step
      exact norm_eq_zero.mp (le_antisymm step (norm_nonneg _))
  obtain ⟨R,hR,g,_,hgne,hfac⟩ := XiC_peel_ball (z.re:ℂ)
  have small : Tendsto (fun n : ℕ => |z.im| * (1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul |z.im|
  obtain ⟨n,hn⟩ := (small.eventually_lt_const hR).exists
  let w := pointAtHeight z.re (t n)
  have hdiff : w-(z.re:ℂ)=(t n:ℂ)*I := by apply Complex.ext <;> simp [w,pointAtHeight]
  have hm : w∈ball (z.re:ℂ) R := by
    rw [mem_ball,dist_eq_norm,hdiff,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    simpa only [t,abs_mul,abs_of_nonneg (show 0≤(1/2:ℝ)^n by positivity)] using hn
  have hnz : w-(z.re:ℂ)≠0 := by
    rw [hdiff]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero hi (pow_ne_zero _ (by norm_num)))) I_ne_zero
  exact (mul_ne_zero (pow_ne_zero _ hnz) (hgne w hm)) ((hfac w hm).symm.trans (zero n))

/-- The positive forward degree d+1 is scaled to converge to the same
entire function at every fixed test point. -/
def jensenHeightGain (d : ℕ) : ℚ × ℚ → ℝ :=
  rationalHeightGain (scaledJensen xiCoeff (d+1))

private theorem jensen_height_gain_tendsto (v : ℚ × ℚ) :
    Tendsto (fun d => jensenHeightGain d v) atTop (𝓝 (rationalHeightGain XiC v)) := by
  exact ((tendsto_scaledJensen_xiCoeff _).norm.sub (tendsto_scaledJensen_xiCoeff _).norm).comp
    (tendsto_add_atTop_nat 1)

/-- Under RH every degree passes every signed rational height comparison. -/
theorem jensen_height_gain_nonneg_of_rh (h : RiemannHypothesis) (d : ℕ) (v : ℚ × ℚ) :
    0≤jensenHeightGain d v := by
  have emp : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨u,hu⟩ := xiSpectralPoint_real_of_rh h q
    exact hq (by simp [hu])
  have cnt := nonrealRootCount_xiScaledReal_le (d:=d+1) (Nat.succ_pos _)
  have upper := jensenNonrealCount_le_of_encard (m:=0) (by simp [emp]) (d+1)
  have filterZero := Multiset.card_eq_zero.mp (show
      (((xiScaledReal (d+1)).map ofRealHom).roots.filter (fun r => r.im≠0)).card = 0 from by
    rw [← nonrealRootCount_eq]
    exact Nat.le_zero.mp (cnt.trans upper))
  apply sub_nonneg.mpr
  rw [←eval_map_xiScaledReal,←eval_map_xiScaledReal]
  apply real_rooted_height_doubling
  intro r hr
  by_contra hi
  have bad : r ∈ ((xiScaledReal (d+1)).map ofRealHom).roots.filter (fun r => r.im≠0) :=
    Multiset.mem_filter.mpr ⟨hr,hi⟩
  rw [filterZero] at bad
  exact Multiset.notMem_zero _ bad

/-- Failure of RH yields a fixed rational pair with a positive margin of
reversal at every sufficiently large degree. -/
theorem not_rh_iff_persistent_rational_height_reversal :
    ¬ RiemannHypothesis ↔ ∃ v : ℚ × ℚ, ∃ ε : ℝ, 0<ε ∧
      ∀ᶠ d in atTop, jensenHeightGain d v < -ε := by
  constructor
  · intro hn
    have fail : ¬ ∀ v, 0≤rationalHeightGain XiC v := fun h => hn (rh_of_XiC_rational_height_doubling h)
    push Not at fail
    obtain ⟨v,hv⟩ := fail
    refine ⟨v,-rationalHeightGain XiC v/2,by linarith only [hv],?_⟩
    exact (jensen_height_gain_tendsto v).eventually_lt_const (by linarith only [hv])
  · rintro ⟨v,ε,hε,hv⟩ h
    obtain ⟨d,hd⟩ := hv.exists
    linarith only [hd,hε,jensen_height_gain_nonneg_of_rh h d v]

/-- Every finite family can grow at its own rate: eventual inclusion of
each rational pair suffices, even if passing is required only cofinally. -/
theorem rh_iff_cofinal_finite_height_comparisons (S : ℕ → Finset (ℚ × ℚ))
    (hS : ∀ v, ∀ᶠ d in atTop, v∈S d) :
    RiemannHypothesis ↔ ∃ᶠ d in atTop, ∀ v∈S d, 0≤jensenHeightGain d v := by
  constructor
  · exact fun h => Frequently.of_forall fun d v _ => jensen_height_gain_nonneg_of_rh h d v
  · intro h
    by_contra hn
    obtain ⟨v,ε,hε,hd⟩ := not_rh_iff_persistent_rational_height_reversal.mp hn
    obtain ⟨d,good,mem,bad⟩ := (h.and_eventually ((hS v).and hd)).exists
    linarith only [good v mem,hε,bad]

/-- The exponent of two in the observation index selects a rational
pair. Each pair has its own full residue class of indices. -/
def scheduledRationalHeights (d : ℕ) : ℚ × ℚ :=
  (Encodable.decode (α:=ℚ × ℚ) (d.factorization 2)).getD (0,0)

theorem scheduledRationalHeights_on_progression (v : ℚ × ℚ) (n : ℕ) :
    scheduledRationalHeights (2^(Encodable.encode v)*(2*n+1)) = v := by
  have odd : ¬ 2 ∣ 2*n+1 := by omega
  simp only [scheduledRationalHeights,Nat.factorization_mul (by positivity : (2:ℕ)^Encodable.encode v ≠ 0)
    (by omega : 2*n+1≠0),Finsupp.add_apply,Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd odd,add_zero,Encodable.encodek,Option.getD_some]

theorem scheduledRationalHeights_recurrent (v : ℚ × ℚ) :
    ∃ᶠ d in atTop, scheduledRationalHeights d=v := by
  apply frequently_atTop.mpr
  intro n
  have pos : 1≤(2:ℕ)^Encodable.encode v := Nat.succ_le_of_lt (pow_pos (by decide) _)
  refine ⟨_,?_,scheduledRationalHeights_on_progression v n⟩
  exact (by omega : n≤2*n+1).trans (by simpa only [one_mul] using Nat.mul_le_mul_right (2*n+1) pos)

/-- Two evaluations per degree suffice: RH is equivalent to eventual
success along this single explicit schedule of height comparisons. -/
theorem rh_iff_one_scheduled_height_comparison :
    RiemannHypothesis ↔ ∀ᶠ d in atTop, 0≤jensenHeightGain d (scheduledRationalHeights d) := by
  constructor
  · exact fun h => Eventually.of_forall fun d => jensen_height_gain_nonneg_of_rh h d _
  · intro good
    by_contra hn
    obtain ⟨v,ε,hε,hd⟩ := not_rh_iff_persistent_rational_height_reversal.mp hn
    obtain ⟨d,eq,hgood,hbad⟩ := ((scheduledRationalHeights_recurrent v).and_eventually (good.and hd)).exists
    rw [eq] at hgood
    linarith only [hgood,hbad,hε]

/-- Under failure of RH, a whole arithmetic progression of scheduled
comparisons fails with one fixed margin. Its common difference is twice
a power of two. -/
theorem not_rh_iff_progression_height_reversal :
    ¬ RiemannHypothesis ↔ ∃ k a : ℕ, ∃ ε : ℝ, 0<ε ∧ ∀ n : ℕ,
      jensenHeightGain (a+(2^k*2)*n) (scheduledRationalHeights (a+(2^k*2)*n)) < -ε := by
  constructor
  · intro hn
    obtain ⟨v,ε,hε,hd⟩ := not_rh_iff_persistent_rational_height_reversal.mp hn
    obtain ⟨N,hN⟩ := eventually_atTop.mp hd
    let k := Encodable.encode v
    let a := 2^k*(2*N+1)
    have hp : 1≤(2:ℕ)^k := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have ha : N≤a := (by omega : N≤2*N+1).trans
      (by simpa only [one_mul] using Nat.mul_le_mul_right (2*N+1) hp)
    refine ⟨k,a,ε,hε,fun n => ?_⟩
    have eq : a+(2^k*2)*n=2^k*(2*(N+n)+1) := by dsimp only [a]; ring
    have test : scheduledRationalHeights (a+(2^k*2)*n)=v := by
      rw [eq]
      exact scheduledRationalHeights_on_progression v (N+n)
    rw [test]
    exact hN _ (ha.trans (Nat.le_add_right _ _))
  · rintro ⟨k,a,ε,hε,hbad⟩ h
    have bad := hbad 0
    simp only [Nat.mul_zero,Nat.add_zero] at bad
    linarith only [bad,hε,jensen_height_gain_nonneg_of_rh h a (scheduledRationalHeights a)]

/-- At least one entire residue class contributes uniform reversals. The
number of failures through a linearly growing cutoff is bounded below
linearly, even after discarding any finite initial run. -/
theorem scheduled_reversal_count_of_not_rh (hn : ¬ RiemannHypothesis) :
    ∃ a D : ℕ, 0<D ∧ ∃ ε : ℝ, 0<ε ∧ ∀ N : ℕ,
      N ≤ ((Finset.range (a+D*N)).filter
        (fun d => jensenHeightGain d (scheduledRationalHeights d) < -ε)).card := by
  classical
  obtain ⟨k,a,ε,hε,hbad⟩ := not_rh_iff_progression_height_reversal.mp hn
  let D := (2:ℕ)^k*2
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨a,D,hD,ε,hε,fun N => ?_⟩
  let f (i : ℕ) := a+D*i
  have inj : Function.Injective f := fun i j hj =>
    Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel hj)
  have sub : (Finset.range N).image f ⊆ (Finset.range (a+D*N)).filter
      (fun d => jensenHeightGain d (scheduledRationalHeights d) < -ε) := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hi) hD) a),hbad i⟩
  simpa only [Finset.card_image_of_injective _ inj,Finset.card_range] using Finset.card_le_card sub

#print axioms not_rh_iff_progression_height_reversal
#print axioms scheduled_reversal_count_of_not_rh
#print axioms real_rooted_height_doubling
#print axioms rh_of_XiC_rational_height_doubling
#print axioms not_rh_iff_persistent_rational_height_reversal
#print axioms rh_iff_cofinal_finite_height_comparisons
#print axioms rh_iff_one_scheduled_height_comparison

end GaloisForLFunctions.GaloisTheoryOfZeros
