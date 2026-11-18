import GaloisForLFunctions.CountingHolography.Sections.PrimeSectionAllowanceAtTheStripEdge
import GaloisForLFunctions.CountingHolography.Sections.SectionHeightsAndThePickIndex

/-!
# Midpoint products of small sections

In a positive direction the ordinary logarithmic section count recovers the
signed degree. Moving the midpoint far enough in one such direction makes
both endpoints positive. The second difference of the three ordinary log
cardinalities then recovers twice the degree of the displacement.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography

/-- Small sections at the metric and modulus of the given divisor. -/
def divisorSections {N : ℕ} (a : Fin N → ℤ) : Finset ℤ :=
  smallSections (generator a : ℝ) (radius a)

private theorem divisorSections_card_pos {N : ℕ} (a : Fin N → ℤ) :
    0 < (divisorSections a).card := by
  rw [divisorSections, card_smallSections]
  omega

/-- Logarithm of the exact cardinality before the rounding to an integer height. -/
def logCard {N : ℕ} (a : Fin N → ℤ) : ℝ := Real.log (divisorSections a).card

theorem logCard_tateLimit {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => logCard (m • a) / (m : ℝ)^2) atTop
      (𝓝 (max (integerProbe N a) 0)) := by
  have h := splineCount_tateLimit a
  have hi : Tendsto (fun m : ℕ => 1 / (m : ℝ)^2) atTop (𝓝 0) := by
    rw [show (fun m : ℕ => 1 / (m : ℝ)^2) = (fun m : ℕ => ((m : ℝ)^2)⁻¹) by
      funext m; rw [one_div]]
    exact ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h (by simpa only [add_zero] using h.add hi)
  · filter_upwards with m
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply Nat.floor_le
    exact Real.log_nonneg (by exact_mod_cast divisorSections_card_pos (m • a))
  · filter_upwards with m
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Nat.lt_floor_add_one (logCard (m • a))).le (sq_nonneg _)

/-- For a fixed displacement, translating far enough along a positive ray
keeps the displaced vector in the positive cone. -/
theorem eventually_positive_shift {N : ℕ} (b a : Fin N → ℤ) (hb : 0 < integerProbe N b) :
    ∀ᶠ k : ℕ in atTop, 0 < integerProbe N (k • b + a) := by
  let F (t : ℝ) := ∑ i : Fin N, ∑ j : Fin N, (atomGram N i j).re *
    ((b i : ℝ) + t * a i) * ((b j : ℝ) + t * a j)
  have hF : Continuous F := by unfold F; fun_prop
  have h₀ : F 0 = integerProbe N b := by simp only [F, integerProbe_eq_sum, zero_mul, add_zero]
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hpos : 0 < F 0 := by rwa [h₀]
  have hf := ((hF.tendsto 0).comp hi).eventually_const_lt hpos
  filter_upwards [hf, eventually_ge_atTop 1] with k hk hk1
  have hk' : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk1).ne'
  have hka (i : Fin N) : (k • b) i = (k : ℤ)*b i := by
    change k • (b i) = _
    rw [nsmul_eq_mul]
  have he : integerProbe N (k • b + a) = (k : ℝ)^2 * F (k : ℝ)⁻¹ := by
    simp only [integerProbe_eq_sum, F, Finset.mul_sum, Pi.add_apply, hka,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [he]
  exact mul_pos (sq_pos_of_ne_zero hk') hk

/-- Normalized logarithmic excess of the outer product over the doubled midpoint. -/
def midpointExcess {N : ℕ} (b a : Fin N → ℤ) (m : ℕ) : ℝ :=
  (logCard (m • (b+a)) + logCard (m • (b-a)) - 2 * logCard (m • b)) / (m : ℝ)^2

theorem midpointExcess_tateLimit_of_nonneg {N : ℕ} (b a : Fin N → ℤ)
    (hc : 0 ≤ integerProbe N b) (hp : 0 ≤ integerProbe N (b+a)) (hn : 0 ≤ integerProbe N (b-a)) :
    Tendsto (midpointExcess b a) atTop (𝓝 (2 * integerProbe N a)) := by
  have hl := ((logCard_tateLimit (b+a)).add (logCard_tateLimit (b-a))).sub
    ((logCard_tateLimit b).const_mul 2)
  rw [max_eq_left hp, max_eq_left hn, max_eq_left hc, integerProbe_parallelogram, add_sub_cancel_left] at hl
  unfold midpointExcess
  exact hl.congr fun m => by ring

/-- One ordinary count, evaluated on three positive rays, detects the
signed Weil degree even when the displacement itself is negative. -/
theorem eventually_midpointExcess_tateLimit {N : ℕ} (b a : Fin N → ℤ) (hb : 0 < integerProbe N b) :
    ∀ᶠ k : ℕ in atTop, Tendsto (midpointExcess (k • b) a) atTop (𝓝 (2 * integerProbe N a)) := by
  filter_upwards [eventually_positive_shift b a hb, eventually_positive_shift b (-a) hb,
    eventually_ge_atTop 1] with k hp hn hk
  rw [← sub_eq_add_neg] at hn
  have hc : 0 < integerProbe N (k • b) := by rw [integerProbe_smul]; positivity
  exact midpointExcess_tateLimit_of_nonneg _ _ hc.le hp.le hn.le

/-- Extend a divisor by zero, preserving its conductor labels. -/
def padDivisor {N M : ℕ} (h : N ≤ M) (a : Fin N → ℤ) : Fin M → ℤ :=
  Function.extend (fun i : Fin N => (⟨i.val, i.isLt.trans_le h⟩ : Fin M)) a 0

theorem integerProbe_pad {N M : ℕ} (h : N ≤ M) (a : Fin N → ℤ) :
    integerProbe M (padDivisor h a) = integerProbe N a := by
  let e (i : Fin N) : Fin M := ⟨i.val, i.isLt.trans_le h⟩
  have hi : Function.Injective e := fun i j hij => Fin.ext (congrArg (Fin.val : Fin M → ℕ) hij)
  have he : (fun i => ((padDivisor h a i : ℤ) : ℂ)) = Function.extend e (fun i => (a i : ℂ)) 0 := by
    funext k
    change ((Function.extend e a 0 k : ℤ) : ℂ) = _
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i,rfl⟩ := hk
      rw [hi.extend_apply, hi.extend_apply]
    · simp only [Function.extend_apply' _ _ _ hk, Pi.zero_apply, Int.cast_zero]
  unfold integerProbe
  rw [he, hermQuad_extend hi]
  congr 1

/-- Two copies of the midpoint section set embed in the product of the
two outer section sets at the same multiplicity. -/
def midpointEmbeds {N : ℕ} (b a : Fin N → ℤ) (m : ℕ) : Prop :=
  Nonempty (((divisorSections (m • b)) × (divisorSections (m • b))) ↪
    ((divisorSections (m • (b+a))) × (divisorSections (m • (b-a)))))

theorem midpointEmbeds_iff {N : ℕ} (b a : Fin N → ℤ) {m : ℕ} (hm : 0 < m) :
    midpointEmbeds b a m ↔ 0 ≤ midpointExcess b a m := by
  have compare (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
      x*x ≤ y*z ↔ 0 ≤ Real.log y + Real.log z - 2*Real.log x := by
    have hx' : 0 < (x : ℝ) := Nat.cast_pos.mpr hx
    have hy' : 0 < (y : ℝ) := Nat.cast_pos.mpr hy
    have hz' : 0 < (z : ℝ) := Nat.cast_pos.mpr hz
    rw [← Nat.cast_le (α := ℝ), Nat.cast_mul, Nat.cast_mul,
      ← Real.log_le_log_iff (mul_pos hx' hx') (mul_pos hy' hz'),
      Real.log_mul hx'.ne' hx'.ne', Real.log_mul hy'.ne' hz'.ne']
    constructor <;> intro h <;> linarith only [h]
  simp only [midpointEmbeds, Function.Embedding.nonempty_iff_card_le, Fintype.card_prod,
    Fintype.card_coe, midpointExcess, logCard, le_div_iff₀ (by positivity : 0 < (m : ℝ)^2), zero_mul]
  exact compare _ _ _ (divisorSections_card_pos _) (divisorSections_card_pos _) (divisorSections_card_pos _)

/-- On two positive directions, all sufficiently late midpoint products
admit injections at every sufficiently high translation. -/
theorem eventually_midpointEmbeds_of_pos {N : ℕ} (b a : Fin N → ℤ)
    (hb : 0 < integerProbe N b) (ha : 0 < integerProbe N a) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop, midpointEmbeds (k • b) a m := by
  filter_upwards [eventually_midpointExcess_tateLimit b a hb] with k hk
  filter_upwards [hk.eventually_const_lt (mul_pos two_pos ha), eventually_ge_atTop 1] with m hm hm1
  exact (midpointEmbeds_iff _ _ hm1).mpr hm.le

/-- Use a fixed background at arbitrarily large translations. Both
divisors are extended by zero to the larger conductor horizon. -/
def midpointTest {P : ℕ} (b : Fin P → ℤ) : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ k : ℕ in atTop, ∃ᶠ m : ℕ in atTop,
    midpointEmbeds (k • padDivisor (le_max_left P N) b) (padDivisor (le_max_right P N) a) m

theorem riemannHypothesis_iff_midpointTest {P : ℕ} (b : Fin P → ℤ) (hb : 0 < integerProbe P b) :
    RiemannHypothesis ↔ midpointTest b := by
  constructor
  · intro hRH N a
    let B := padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    have hb' : 0 < integerProbe (max P N) B := by simpa only [B, integerProbe_pad] using hb
    change ∀ᶠ k : ℕ in atTop, ∃ᶠ m : ℕ in atTop, midpointEmbeds (k • B) A m
    by_cases ha : A = 0
    · rw [ha]
      exact .of_forall fun k => (Eventually.of_forall fun m => by
        unfold midpointEmbeds
        simp only [add_zero, sub_zero]
        exact ⟨Function.Embedding.refl _⟩).frequently
    · exact (eventually_midpointEmbeds_of_pos B A hb' (integerProbe_pos_of_rh hRH ha)).mono
        fun _ hm => hm.frequently
  · intro h
    apply riemannHypothesis_iff_integerProbes.mpr
    intro N a
    let B := padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    have hb' : 0 < integerProbe (max P N) B := by simpa only [B, integerProbe_pad] using hb
    obtain ⟨k,hk,hl⟩ := ((h N a).and (eventually_midpointExcess_tateLimit B A hb')).exists
    by_contra! hneg
    have ha' : integerProbe (max P N) A < 0 := by simpa only [A, integerProbe_pad] using hneg
    obtain ⟨m,hm,hm',hm1⟩ := (hk.and_eventually
      ((hl.eventually_lt_const (mul_neg_of_pos_of_neg two_pos ha')).and (eventually_ge_atTop 1))).exists
    exact (not_lt_of_ge ((midpointEmbeds_iff _ _ hm1).mp hm)) hm'

/-- A single two-atom background exists unconditionally and tests all
signed displacements through products of ordinary small-section sets. -/
theorem exists_prime_background_midpointTest :
    ∃ (p : ℕ) (b : Fin (p+1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p+1) b ∧ (RiemannHypothesis ↔ midpointTest b) := by
  obtain ⟨p,hp,h⟩ := exists_positive_prime_pair_or_difference
  rcases h with h | h
  · exact ⟨p, _, hp, Or.inl rfl, h, riemannHypothesis_iff_midpointTest _ h⟩
  · exact ⟨p, _, hp, Or.inr rfl, h, riemannHypothesis_iff_midpointTest _ h⟩

#print axioms eventually_midpointExcess_tateLimit
#print axioms exists_prime_background_midpointTest

end GaloisForLFunctions.CountingHolography.Sections
