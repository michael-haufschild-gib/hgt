import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountRiesz
import GaloisForLFunctions.RHTower.BeurlingSystemMellin

/-!
# Euler continuation of the positive near-count model

Odd prime labels together with extra labels of norms three and four give
`ζ_B(s) = ζ(s) / ((1 + 2^(-s)) (1 - 3^(-s)))` for `Re s > 1`.
The formula is derived from the actual generalized-integer series using its
coordinate bijection and absolute convergence. The quotient continues it to
`Re s > 0`, with residue one at one and unchanged zero multiplicities elsewhere.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- The actual norm count is at most twice the threshold. Compare its mass with the
first count average at twice that threshold. -/
theorem hasLinearCounting : system.HasLinearCounting 2 := by
  intro X hX
  have hx : 0 < X := zero_lt_one.trans_le hX
  have h2 : 1 ≤ 2 * X := by linarith only [hX]
  let S := (isDiscrete X).toFinset
  let T := (isDiscrete (2 * X)).toFinset
  have hST : S ⊆ T := by
    intro g hg
    have hh : system.intNorm g ≤ X := (isDiscrete X).mem_toFinset.mp hg
    apply (isDiscrete (2 * X)).mem_toFinset.mpr
    change system.intNorm g ≤ 2 * X
    linarith only [hh, hX]
  have hcard : S.card = system.countBall X := by
    rw [RHTower.BeurlingSystem.countBall, Set.ncard_eq_toFinset_card _ (isDiscrete X)]
  have hR : X * (system.countBall X : ℝ) ≤ rieszCount (2 * X) := by
    calc
      _ = ∑ _g ∈ S, X := by rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
      _ ≤ ∑ g ∈ S, (2 * X - system.intNorm g) := by
        apply Finset.sum_le_sum
        intro g hg
        have hh : system.intNorm g ≤ X := (isDiscrete X).mem_toFinset.mp hg
        linarith only [hh]
      _ ≤ ∑ g ∈ T, (2 * X - system.intNorm g) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hST
        intro g hg _
        exact sub_nonneg.mpr ((isDiscrete (2 * X)).mem_toFinset.mp hg)
      _ = rieszCount (2 * X) := rfl
  have hr := (riesz_log_bound h2).1
  have hlog := Real.log_nonneg h2
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnonneg : 0 ≤ (2 * X) * Real.log (2 * X) / (12 * Real.log 3) := by positivity
  by_contra hh
  have hbad := mul_pos hx (sub_pos.mpr (lt_of_not_ge hh))
  nlinarith only [hR, hr, hnonneg, hbad]

open RHTower.BeurlingDeletion

private abbrev oddNat := {u : ℕ // SFree ({2} : Set ℕ) u}

private def coordinateMap (g : system.Integer) : oddNat × ℕ × ℕ :=
  (⟨(coordinates g).1, coordinates_sfree g⟩, (coordinates g).2)

private theorem coordinateMap_injective : Function.Injective coordinateMap := by
  intro g g' he
  apply coordinates_injective
  exact congrArg (fun v : oddNat × ℕ × ℕ => (v.1.val, v.2)) he

private theorem coordinateMap_surjective : Function.Surjective coordinateMap := by
  rintro ⟨u, a, b⟩
  obtain ⟨g, hg⟩ := exists_coordinates u.property a b
  refine ⟨g, Prod.ext ?_ ?_⟩
  · apply Subtype.ext
    exact congrArg Prod.fst hg
  · change (coordinates g).2 = (a, b)
    exact congrArg (fun v : ℕ × ℕ × ℕ => v.2) hg

/-- Generalized integers are indexed by an odd integer and the two extra-label exponents. -/
private def coordinateEquiv : system.Integer ≃ oddNat × ℕ × ℕ :=
  Equiv.ofBijective coordinateMap ⟨coordinateMap_injective, coordinateMap_surjective⟩

private theorem coordinateEquiv_norm (g : system.Integer) :
    system.intNorm g = ((coordinateEquiv g).1.val : ℝ) *
      (3 : ℝ) ^ (coordinateEquiv g).2.1 * (4 : ℝ) ^ (coordinateEquiv g).2.2 :=
  intNorm_coordinates g

/-- Positive real bases have no branch ambiguity when taking natural powers. -/
private theorem real_pow_cpow {x : ℝ} (hx : 0 < x) (n : ℕ) (s : ℂ) :
    ((x ^ n : ℝ) : ℂ) ^ s = ((x : ℂ) ^ s) ^ n := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos hx n).ne'),
    ← Complex.ofReal_log (pow_pos hx n).le, Real.log_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]

private theorem coordinate_cpow (g : system.Integer) (s : ℂ) :
    (system.intNorm g : ℂ) ^ (-s) =
      ((coordinateEquiv g).1.val : ℂ) ^ (-s) *
        ((3 : ℂ) ^ (-s)) ^ (coordinateEquiv g).2.1 *
        ((4 : ℂ) ^ (-s)) ^ (coordinateEquiv g).2.2 := by
  rw [coordinateEquiv_norm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    real_pow_cpow (by norm_num : (0 : ℝ) < 3),
    real_pow_cpow (by norm_num : (0 : ℝ) < 4)]
  norm_cast

private theorem norm_cpow_lt_one {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    ‖(q : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith only [hs])

private def oddSeries (s : ℂ) : ℂ := ∑' u : oddNat, (u.val : ℂ) ^ (-s)

/-- Absolute convergence permits the coordinate bijection and the two geometric sums. -/
private theorem zeta_series_factor {s : ℂ} (hs : 1 < s.re) :
    system.zetaSeriesC s = oddSeries s * (1 - (3 : ℂ) ^ (-s))⁻¹ *
      (1 - (4 : ℂ) ^ (-s))⁻¹ := by
  let F : oddNat × ℕ × ℕ → ℂ := fun v =>
    (v.1.val : ℂ) ^ (-s) * ((3 : ℂ) ^ (-s)) ^ v.2.1 * ((4 : ℂ) ^ (-s)) ^ v.2.2
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have h3 : ‖(3 : ℂ) ^ (-s)‖ < 1 := norm_cpow_lt_one (q := 3) (by norm_num) hs0
  have h4 : ‖(4 : ℂ) ^ (-s)‖ < 1 := norm_cpow_lt_one (q := 4) (by norm_num) hs0
  have hsum := RHTower.BeurlingSystem.summable_intNorm_cpow isDiscrete hasLinearCounting hs
  have hcomp : Summable (F ∘ coordinateEquiv) := by
    apply hsum.congr
    intro g
    exact coordinate_cpow g s
  have hF : Summable F := coordinateEquiv.summable_iff.mp hcomp
  have hrow (u : oddNat) : Summable (fun ab : ℕ × ℕ => F (u, ab)) :=
    hF.comp_injective (fun ab cd he => congrArg Prod.snd he)
  have heq : system.zetaSeriesC s = ∑' v, F v := by
    rw [RHTower.BeurlingSystem.zetaSeriesC]
    calc
      _ = ∑' g : system.Integer, F (coordinateEquiv g) :=
        tsum_congr (fun g => coordinate_cpow g s)
      _ = ∑' v, F v := coordinateEquiv.tsum_eq F
  rw [heq, hF.tsum_prod]
  have hi (u : oddNat) : (∑' ab : ℕ × ℕ, F (u, ab)) =
      (u.val : ℂ) ^ (-s) * (1 - (3 : ℂ) ^ (-s))⁻¹ * (1 - (4 : ℂ) ^ (-s))⁻¹ := by
    rw [(hrow u).tsum_prod]
    dsimp only [F]
    simp_rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h4]
    rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_norm_lt_one h3]
  simp_rw [hi]
  rw [tsum_mul_right, tsum_mul_right]
  rfl

/-- Enumerate positive odd integers without losing generator multiplicities. -/
private def oddEquiv : ℕ ≃ oddNat where
  toFun n := ⟨2 * n + 1, (sfree_two_iff _).mpr (by omega)⟩
  invFun u := u.val / 2
  left_inv n := by dsimp; omega
  right_inv u := by
    apply Subtype.ext
    have h := (sfree_two_iff u.val).mp u.property
    dsimp
    omega

private def parityEquiv : ℕ ⊕ ℕ ≃ ℕ := Equiv.ofBijective
  (Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b => simp only [Sum.elim_inl] at h; congr 1; omega
        | inr b => simp only [Sum.elim_inl, Sum.elim_inr] at h; omega
      | inr a =>
        cases b with
        | inl b => simp only [Sum.elim_inl, Sum.elim_inr] at h; omega
        | inr b => simp only [Sum.elim_inr] at h; congr 1; omega
    · intro n
      by_cases h : n % 2 = 0
      · exact ⟨Sum.inl (n / 2), by simp only [Sum.elim_inl]; omega⟩
      · exact ⟨Sum.inr (n / 2), by simp only [Sum.elim_inr]; omega⟩)

private theorem zeta_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
  have hhas : HasSum (LSeries.term (1 : ℕ → ℂ) s) (riemannZeta s) :=
    LSeriesHasSum_one hs
  have hshift := (hasSum_nat_add_iff' 1).mpr hhas
  simpa [LSeries.term, Complex.cpow_neg] using hshift

/-- Splitting ordinary positive integers by parity removes the Euler factor at two. -/
private theorem oddSeries_eq {s : ℂ} (hs : 1 < s.re) :
    oddSeries s = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let w : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) ^ (-s)
  let f : ℕ ⊕ ℕ → ℂ := w ∘ parityEquiv
  have hw : Summable w := (zeta_hasSum hs).summable
  have hodd : Summable (f ∘ Sum.inl) :=
    hw.comp_injective (fun n m h => by change 2*n=2*m at h; omega)
  have heven : Summable (f ∘ Sum.inr) :=
    hw.comp_injective (fun n m h => by change 2*n+1=2*m+1 at h; omega)
  have htotal : (∑' n, f (Sum.inl n)) + (∑' n, f (Sum.inr n)) = riemannZeta s := by
    rw [← hodd.tsum_sum heven]
    exact (parityEquiv.tsum_eq w).trans (zeta_hasSum hs).tsum_eq
  have hO : (∑' n, f (Sum.inl n)) = oddSeries s := by
    exact oddEquiv.tsum_eq (fun u => (u.val : ℂ) ^ (-s))
  have hE : (∑' n, f (Sum.inr n)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    calc
      _ = ∑' n : ℕ, (2 : ℂ) ^ (-s) * w n := by
        apply tsum_congr
        intro n
        change (((2*n+1)+1:ℕ):ℂ)^(-s) = (2:ℂ)^(-s)*(((n+1:ℕ):ℂ)^(-s))
        have he : (2*n+1)+1 = 2*(n+1) := by omega
        rw [he, Nat.cast_mul]
        exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2)
          (by positivity : (0:ℝ) ≤ ((n+1:ℕ):ℝ)) (-s)
      _ = _ := by rw [tsum_mul_left, (zeta_hasSum hs).tsum_eq]
  rw [hO, hE] at htotal
  linear_combination htotal

private theorem sub_cpow_ne_zero {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    1 - (q : ℂ) ^ (-s) ≠ 0 := by
  intro he
  have hz : (q : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
  have hnorm := norm_cpow_lt_one hq hs
  rw [hz, norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

private theorem add_cpow_ne_zero {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    1 + (q : ℂ) ^ (-s) ≠ 0 := by
  intro he
  have hz : (q : ℂ) ^ (-s) = -1 := by linear_combination he
  have hnorm := norm_cpow_lt_one hq hs
  rw [hz, norm_neg, norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

/-- Finite Euler denominator of the positive near-count model. -/
def eulerDenominator (s : ℂ) : ℂ := (1 + (2 : ℂ) ^ (-s)) * (1 - (3 : ℂ) ^ (-s))

/-- Both Euler factors are nonzero in the open right half-plane. -/
theorem eulerDenominator_ne_zero {s : ℂ} (hs : 0 < s.re) : eulerDenominator s ≠ 0 :=
  mul_ne_zero (add_cpow_ne_zero (q := 2) (by norm_num) hs)
    (sub_cpow_ne_zero (q := 3) (by norm_num) hs)

/-- Explicit continuation of the actual generalized-integer Dirichlet series. -/
def zetaContinuation (s : ℂ) : ℂ := riemannZeta s / eulerDenominator s

/-- The actual Dirichlet series equals the explicit quotient for `Re s > 1`. -/
theorem zetaSeriesC_eq_continuation {s : ℂ} (hs : 1 < s.re) :
    system.zetaSeriesC s = zetaContinuation s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have h2 : 1 - (2 : ℂ) ^ (-s) ≠ 0 := by
    simpa using sub_cpow_ne_zero (q := 2) (by norm_num) hs0
  have h3 : 1 - (3 : ℂ) ^ (-s) ≠ 0 := by
    simpa using sub_cpow_ne_zero (q := 3) (by norm_num) hs0
  have h4 : 1 - (4 : ℂ) ^ (-s) ≠ 0 := by
    simpa using sub_cpow_ne_zero (q := 4) (by norm_num) hs0
  have hp2 : 1 + (2 : ℂ) ^ (-s) ≠ 0 := by
    simpa using add_cpow_ne_zero (q := 2) (by norm_num) hs0
  have h42 : (4 : ℂ) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ 2 := by
    have h := real_pow_cpow (by norm_num : (0 : ℝ) < 2) 2 (-s)
    norm_num at h
    exact h
  rw [zeta_series_factor hs, oddSeries_eq hs]
  dsimp only [zetaContinuation, eulerDenominator]
  rw [h42] at h4 ⊢
  field_simp [h2, h3, h4, hp2]
  ring

/-- The continuation has exactly the same zeros as zeta in the open right half-plane. -/
theorem zetaContinuation_zero_iff {s : ℂ} (hs : 0 < s.re) :
    zetaContinuation s = 0 ↔ riemannZeta s = 0 := by
  rw [zetaContinuation, div_eq_zero_iff]
  simp only [eulerDenominator_ne_zero hs, or_false]

private theorem analyticAt_cpow_neg {q : ℝ} (hq : 0 < q) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s := by
  refine DifferentiableOn.analyticAt (s := Set.univ) ?_ Filter.univ_mem
  intro z _
  exact (DifferentiableAt.const_cpow (differentiableAt_id.neg)
    (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))).differentiableWithinAt

private theorem analyticAt_eulerDenominator (s : ℂ) : AnalyticAt ℂ eulerDenominator s :=
  (analyticAt_const.add (analyticAt_cpow_neg (by norm_num : (0:ℝ)<2) s)).mul
    (analyticAt_const.sub (analyticAt_cpow_neg (by norm_num : (0:ℝ)<3) s))

/-- The continuation is analytic in the open right half-plane away from one. -/
theorem analyticAt_zetaContinuation {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ zetaContinuation s :=
  (analyticOn_riemannZeta s hs1).div (analyticAt_eulerDenominator s)
    (eulerDenominator_ne_zero hs)

/-- Multiplication by the nonvanishing analytic Euler correction preserves every zero order. -/
theorem analyticOrderAt_zetaContinuation {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt zetaContinuation s = analyticOrderAt riemannZeta s := by
  have he : zetaContinuation = riemannZeta * eulerDenominator⁻¹ := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul (analyticOn_riemannZeta s hs1)
    ((analyticAt_eulerDenominator s).inv (eulerDenominator_ne_zero hs)),
    (((analyticAt_eulerDenominator s).inv (eulerDenominator_ne_zero hs)).analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (eulerDenominator_ne_zero hs))), add_zero]

private theorem eulerDenominator_one : eulerDenominator 1 = 1 := by
  norm_num [eulerDenominator, Complex.cpow_neg, Complex.cpow_one]

/-- The continuation has residue one at its pole at one, matching the count density. -/
theorem zetaContinuation_residue_one :
    Filter.Tendsto (fun s : ℂ => (s - 1) * zetaContinuation s)
      (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
  have hd : Filter.Tendsto eulerDenominator (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    simpa only [eulerDenominator_one] using
      (analyticAt_eulerDenominator 1).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have h := riemannZeta_residue_one.div hd (by norm_num : (1:ℂ) ≠ 0)
  change Filter.Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s) / eulerDenominator s)
    (nhdsWithin 1 {1}ᶜ) (nhds ((1 : ℂ) / 1)) at h
  simpa only [div_one, mul_div_assoc, zetaContinuation] using h

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
