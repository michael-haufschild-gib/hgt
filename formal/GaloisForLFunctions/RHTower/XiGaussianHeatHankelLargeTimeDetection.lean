import GaloisForLFunctions.RHTower.XiGaussianHeatHankelHeightHorizon
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver

/-!
# Detection of an off-line zero at large heat time with bounded rank

Let `u = w_{q₀}` be the heat frequency of an off-line zero copy, `Im u ≠ 0`, and let `K_u` be the
monic polynomial vanishing at the finitely many other heat frequencies of real part
`≤ Re u + 1` (`heatLowFrequencyKiller`).  For `P_t = K_u · ((X − ū) + t (X − u))` (`heatPairTest`) the
frequencies of real part `≤ Re u + 1` other than `u, ū` contribute nothing to the heat Hankel form.
Each copy at `u` or `ū` contributes `Re(c₀(a) t̄)` with
`|c₀(a)| = e^{-a Re u} |K_u(u)| |K_u(ū)| |u − ū|²`, and the remaining frequencies contribute
`O(e^{-a (Re u + 1)})`.  Choosing the phase of `t` makes the pair term `−|c₀(a)|`.

**Theorem** (`exists_heatHankel_re_neg_of_not_riemannHypothesis`).  Without RH there are a rank
`N` and a time `A > 0` such that for every `a ≥ A` the heat Hankel form is negative on a nonzero
polynomial of degree `< N`.  Hence some `Δ_M(a)`, `M ≤ N`, is `≤ 0` for every `a ≥ A`
(`exists_heatMomentDet_nonpos_of_not_riemannHypothesis`), and

`RH ⟺ ∀ N, Δ_N(a) > 0 for all large a`
(`riemannHypothesis_iff_forall_eventually_heatMomentDet_pos`).

The rank is `deg K_u + 2`, i.e. the number of other heat frequencies of real part `≤ Re u + 1`
plus two.  This is the converse of the height horizon (`exists_height_heatMomentDet_pos`): a fixed
rank detects an off-line zero at large time once it exceeds the number of heat frequencies below it.
-/

open Complex Polynomial Matrix Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix coeffMass coeffMass_nonneg coeffMass_add_le
  coeffMass_C_mul posDef_leadingMatrix_of_det_pos)

namespace RHTower

noncomputable section

/-- Only finitely many zero copies have heat frequency of real part `≤ R`. -/
theorem finite_setOf_re_xiHeatFrequency_le (R : ℝ) :
    {q : XiZeroCopy | (xiHeatFrequency q).re ≤ R}.Finite := by
  have hs := summable_exp_neg_mul_re_xiHeatFrequency (b := 1) one_pos
  have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-R)))
  refine (Filter.eventually_cofinite.1 hev).subset fun q (hq : (xiHeatFrequency q).re ≤ R) => ?_
  show ¬ (Real.exp (-(1 * (xiHeatFrequency q).re)) < Real.exp (-R))
  rw [not_lt, one_mul]
  exact Real.exp_le_exp.2 (by linarith)

/-! ## The killing polynomial and the pair test -/

open Classical in
/-- The heat frequencies of real part `≤ Re u + 1`, other than `u` and `ū`. -/
def heatLowFrequencies (u : ℂ) : Finset ℂ :=
  ((finite_setOf_re_xiHeatFrequency_le (u.re + 1)).toFinset.image xiHeatFrequency).filter
    fun w => w ≠ u ∧ w ≠ (starRingEnd ℂ) u

/-- The monic polynomial vanishing exactly at `heatLowFrequencies u`. -/
def heatLowFrequencyKiller (u : ℂ) : ℂ[X] := ∏ w ∈ heatLowFrequencies u, (X - C w)

/-- The pair test polynomial `K_u · ((X − ū) + t (X − u))`. -/
def heatPairTest (u t : ℂ) : ℂ[X] :=
  heatLowFrequencyKiller u * ((X - C ((starRingEnd ℂ) u)) + C t * (X - C u))

theorem mem_heatLowFrequencies {u : ℂ} {q : XiZeroCopy} (hq : (xiHeatFrequency q).re ≤ u.re + 1)
    (hu : xiHeatFrequency q ≠ u) (hub : xiHeatFrequency q ≠ (starRingEnd ℂ) u) :
    xiHeatFrequency q ∈ heatLowFrequencies u := by
  classical
  rw [heatLowFrequencies, Finset.mem_filter]
  exact ⟨Finset.mem_image_of_mem _ ((finite_setOf_re_xiHeatFrequency_le _).mem_toFinset.2 hq),
    hu, hub⟩

theorem eval_heatLowFrequencyKiller_of_mem {u w : ℂ} (hw : w ∈ heatLowFrequencies u) :
    (heatLowFrequencyKiller u).eval w = 0 := by
  rw [heatLowFrequencyKiller, eval_prod]
  exact Finset.prod_eq_zero hw (by simp)

theorem eval_heatLowFrequencyKiller_ne_zero {u z : ℂ} (hz : z ∉ heatLowFrequencies u) :
    (heatLowFrequencyKiller u).eval z ≠ 0 := by
  rw [heatLowFrequencyKiller, eval_prod, Finset.prod_ne_zero_iff]
  intro w hw
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  rintro rfl
  exact hz hw

theorem self_not_mem_heatLowFrequencies (u : ℂ) : u ∉ heatLowFrequencies u := by
  classical
  simp [heatLowFrequencies]

theorem conj_not_mem_heatLowFrequencies (u : ℂ) : (starRingEnd ℂ) u ∉ heatLowFrequencies u := by
  classical
  simp [heatLowFrequencies]

theorem eval_heatPairTest_self (u t : ℂ) :
    (heatPairTest u t).eval u = (heatLowFrequencyKiller u).eval u * (u - (starRingEnd ℂ) u) := by
  simp [heatPairTest]

theorem eval_heatPairTest_conj (u t : ℂ) :
    (heatPairTest u t).eval ((starRingEnd ℂ) u) =
      (heatLowFrequencyKiller u).eval ((starRingEnd ℂ) u) * (t * ((starRingEnd ℂ) u - u)) := by
  simp [heatPairTest]

theorem eval_heatPairTest_of_mem {u t w : ℂ} (hw : w ∈ heatLowFrequencies u) :
    (heatPairTest u t).eval w = 0 := by
  rw [heatPairTest, eval_mul, eval_heatLowFrequencyKiller_of_mem hw, zero_mul]

theorem natDegree_heatPairTest_le (u t : ℂ) :
    (heatPairTest u t).natDegree ≤ (heatLowFrequencyKiller u).natDegree + 1 := by
  refine natDegree_mul_le.trans (Nat.add_le_add_left ?_ _)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_X_sub_C]
  · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C])

/-- The coefficient-mass bound for unimodular `t`. -/
def heatPairTestMass (u : ℂ) : ℝ :=
  coeffMass (heatLowFrequencyKiller u * (X - C ((starRingEnd ℂ) u))) +
    coeffMass (heatLowFrequencyKiller u * (X - C u))

theorem heatPairTestMass_nonneg (u : ℂ) : 0 ≤ heatPairTestMass u :=
  add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)

theorem coeffMass_heatPairTest_le {u t : ℂ} (ht : ‖t‖ = 1) : coeffMass (heatPairTest u t) ≤ heatPairTestMass u := by
  have : heatPairTest u t = heatLowFrequencyKiller u * (X - C ((starRingEnd ℂ) u)) +
      C t * (heatLowFrequencyKiller u * (X - C u)) := by
    rw [heatPairTest]; ring
  rw [this]
  refine (coeffMass_add_le _ _).trans ?_
  rw [coeffMass_C_mul, ht, one_mul]
  rfl

/-! ## The pair term -/

/-- The pair coefficient `c₀(a) = e^{-au} K_u(u) \overline{K_u(ū)} (u − ū)²`. -/
def heatPairCoefficient (a : ℝ) (u : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * u) * (heatLowFrequencyKiller u).eval u *
    (starRingEnd ℂ) ((heatLowFrequencyKiller u).eval ((starRingEnd ℂ) u)) * (u - (starRingEnd ℂ) u) ^ 2

/-- The size of the pair coefficient without the heat factor. -/
def heatPairSize (u : ℂ) : ℝ :=
  ‖(heatLowFrequencyKiller u).eval u‖ * ‖(heatLowFrequencyKiller u).eval ((starRingEnd ℂ) u)‖ *
    ‖u - (starRingEnd ℂ) u‖ ^ 2

theorem norm_heatPairCoefficient (a : ℝ) (u : ℂ) :
    ‖heatPairCoefficient a u‖ = Real.exp (-(a * u.re)) * heatPairSize u := by
  rw [heatPairCoefficient, heatPairSize, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_conj,
    norm_pow]
  have : (-(a : ℂ) * u).re = -(a * u.re) := by simp
  rw [this]
  ring

theorem heatPairSize_pos {u : ℂ} (hu : u.im ≠ 0) : 0 < heatPairSize u := by
  have huu : u ≠ (starRingEnd ℂ) u := fun h => hu (Complex.conj_eq_iff_im.1 h.symm)
  have h1 := eval_heatLowFrequencyKiller_ne_zero (self_not_mem_heatLowFrequencies u)
  have h2 := eval_heatLowFrequencyKiller_ne_zero (conj_not_mem_heatLowFrequencies u)
  have h3 : 0 < ‖u - (starRingEnd ℂ) u‖ := norm_pos_iff.2 (sub_ne_zero.2 huu)
  rw [heatPairSize]
  have := norm_pos_iff.2 h1
  have := norm_pos_iff.2 h2
  positivity

theorem heatHankelTermAt_heatPairTest (a : ℝ) (u t : ℂ) :
    heatHankelTermAt a (heatPairTest u t) (heatPairTest u t) u = heatPairCoefficient a u * (starRingEnd ℂ) t := by
  rw [heatHankelTermAt, eval_heatPairTest_self, eval_heatPairTest_conj, heatPairCoefficient]
  simp only [map_mul, map_sub, Complex.conj_conj]
  ring

/-- The phase choice `t = −c₀/|c₀|` turns the pair term into `−|c₀|`. -/
theorem re_heatHankelTermAt_heatPairTest_phase (a : ℝ) {u : ℂ} (hc : 0 < ‖heatPairCoefficient a u‖) :
    (heatHankelTermAt a (heatPairTest u (-(heatPairCoefficient a u / (‖heatPairCoefficient a u‖ : ℂ))))
      (heatPairTest u (-(heatPairCoefficient a u / (‖heatPairCoefficient a u‖ : ℂ)))) u).re =
        -‖heatPairCoefficient a u‖ := by
  rw [heatHankelTermAt_heatPairTest]
  set c := heatPairCoefficient a u
  rw [map_neg, map_div₀, Complex.conj_ofReal, mul_neg, mul_div_assoc', Complex.mul_conj,
    Complex.normSq_eq_norm_sq, neg_re, div_ofReal_re, Complex.ofReal_re, sq, mul_div_assoc,
    div_self hc.ne', mul_one]

theorem norm_heatPairPhase {c : ℂ} (hc : 0 < ‖c‖) : ‖-(c / (‖c‖ : ℂ))‖ = 1 := by
  rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_self hc.ne']

/-! ## Bounding the heat Hankel form of the pair test -/

/-- The finitely many copies sitting at `u` or `ū`. -/
def heatPairCopies (u : ℂ) : Finset XiZeroCopy :=
  open Classical in
  (finite_setOf_re_xiHeatFrequency_le (u.re + 1)).toFinset.filter
    fun q => xiHeatFrequency q = u ∨ xiHeatFrequency q = (starRingEnd ℂ) u

theorem mem_heatPairCopies {u : ℂ} {q : XiZeroCopy} :
    q ∈ heatPairCopies u ↔ xiHeatFrequency q = u ∨ xiHeatFrequency q = (starRingEnd ℂ) u := by
  classical
  rw [heatPairCopies, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    show (xiHeatFrequency q).re ≤ u.re + 1
    rcases h with h | h <;> rw [h] <;> simp

/-- The real part of the heat Hankel form of a pair test is at most the pair copies' contribution
plus the frequencies above `Re u + 1`. -/
theorem re_heatHankel_heatPairTest_le {a : ℝ} (ha : 0 < a) {u t : ℂ} :
    (heatHankel a (heatPairTest u t) (heatPairTest u t)).re ≤
      ∑ q ∈ heatPairCopies u, (heatHankelTermAt a (heatPairTest u t) (heatPairTest u t) (xiHeatFrequency q)).re +
        ∑' q : XiZeroCopy, if u.re + 1 < (xiHeatFrequency q).re then
          ‖heatHankelTermAt a (heatPairTest u t) (heatPairTest u t) (xiHeatFrequency q)‖ else 0 := by
  classical
  set P := heatPairTest u t
  set T : XiZeroCopy → ℝ := fun q => (heatHankelTermAt a P P (xiHeatFrequency q)).re
  set g : XiZeroCopy → ℝ := fun q => if u.re + 1 < (xiHeatFrequency q).re then
    ‖heatHankelTermAt a P P (xiHeatFrequency q)‖ else 0
  set e : XiZeroCopy → ℝ := fun q => if q ∈ heatPairCopies u then T q else 0
  have hsum := summable_heatHankelTermAt ha P P
  have hTs : Summable T := (Complex.hasSum_re hsum.hasSum).summable
  have hg0 : ∀ q, 0 ≤ g q := fun q => by
    simp only [g]; split_ifs <;> positivity
  have hgs : Summable g := hsum.norm.of_nonneg_of_le hg0 fun q => by
    simp only [g]; split_ifs <;> simp
  have hes : Summable e := summable_of_ne_finset_zero (s := heatPairCopies u) fun q hq => by
    simp [e, hq]
  have hpt : ∀ q, T q ≤ e q + g q := fun q => by
    by_cases hqF : q ∈ heatPairCopies u
    · simp only [e, if_pos hqF]
      linarith [hg0 q]
    · simp only [e, if_neg hqF, zero_add]
      by_cases hRq : u.re + 1 < (xiHeatFrequency q).re
      · simp only [g, if_pos hRq, T]
        exact Complex.re_le_norm _
      · simp only [g, if_neg hRq]
        rw [mem_heatPairCopies, not_or] at hqF
        have hw := mem_heatLowFrequencies (not_lt.1 hRq) hqF.1 hqF.2
        simp only [T, heatHankelTermAt, P, eval_heatPairTest_of_mem hw, mul_zero, zero_mul, zero_re,
          le_refl]
  have he : ∑' q, e q = ∑ q ∈ heatPairCopies u, T q := by
    rw [tsum_eq_sum (s := heatPairCopies u) fun q hq => by simp [e, hq]]
    exact Finset.sum_congr rfl fun q hq => by simp [e, hq]
  rw [heatHankel, Complex.re_tsum hsum]
  calc ∑' q, T q ≤ ∑' q, (e q + g q) := hTs.tsum_le_tsum hpt (hes.add hgs)
    _ = ∑' q, e q + ∑' q, g q := hes.tsum_add hgs
    _ = _ := by rw [he]

/-- Each pair copy contributes exactly `−|c₀(a)|` at the phase choice. -/
theorem re_heatHankelTermAt_pairCopy (a : ℝ) {u : ℂ} (hc : 0 < ‖heatPairCoefficient a u‖)
    {q : XiZeroCopy} (hq : q ∈ heatPairCopies u) :
    (heatHankelTermAt a (heatPairTest u (-(heatPairCoefficient a u / (‖heatPairCoefficient a u‖ : ℂ))))
      (heatPairTest u (-(heatPairCoefficient a u / (‖heatPairCoefficient a u‖ : ℂ)))) (xiHeatFrequency q)).re =
        -‖heatPairCoefficient a u‖ := by
  rcases mem_heatPairCopies.1 hq with h | h
  · rw [h, re_heatHankelTermAt_heatPairTest_phase a hc]
  · rw [h, heatHankelTermAt_conj, Complex.conj_re, re_heatHankelTermAt_heatPairTest_phase a hc]

/-- The frequencies above `Re u + 1` cost at most `M_u e^{-a(Re u + 1)}` for `a ≥ 1`. -/
theorem tail_heatPairTest_le {a : ℝ} (ha : 1 ≤ a) {u t : ℂ} (ht : ‖t‖ = 1) :
    (∑' q : XiZeroCopy, if u.re + 1 < (xiHeatFrequency q).re then
      ‖heatHankelTermAt a (heatPairTest u t) (heatPairTest u t) (xiHeatFrequency q)‖ else 0) ≤
        heatPairTestMass u ^ 2 * Real.exp (u.re + 1) *
          (∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * ((heatLowFrequencyKiller u).natDegree + 1)) *
            Real.exp (-(1 * (xiHeatFrequency q).re))) * Real.exp (-(a * (u.re + 1))) := by
  set D := (heatLowFrequencyKiller u).natDegree + 1
  set P := heatPairTest u t
  set B := heatPairTestMass u
  set R := u.re + 1
  have hf₁s := summable_one_add_norm_pow_mul_exp one_pos (2 * D)
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hle : ∀ q : XiZeroCopy, (if R < (xiHeatFrequency q).re then
      ‖heatHankelTermAt a P P (xiHeatFrequency q)‖ else 0) ≤
        B ^ 2 * Real.exp R * Real.exp (-(a * R)) *
          ((1 + ‖xiHeatFrequency q‖) ^ (2 * D) * Real.exp (-(1 * (xiHeatFrequency q).re))) := by
    intro q
    split_ifs with hRq
    · have hnorm := norm_heatHankelTermAt_le a P P q
      have hmass : polyMass P = coeffMass P := rfl
      rw [hmass] at hnorm
      have hc := coeffMass_nonneg P
      have hcB : coeffMass P ≤ B := coeffMass_heatPairTest_le ht
      have hbase : 1 ≤ 1 + ‖xiHeatFrequency q‖ := by linarith [norm_nonneg (xiHeatFrequency q)]
      have hpow : (1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) ≤
          (1 + ‖xiHeatFrequency q‖) ^ (2 * D) :=
        pow_le_pow_right₀ hbase (by
          have hPD : P.natDegree ≤ D := natDegree_heatPairTest_le u t
          omega)
      have hexp : Real.exp (-(a * (xiHeatFrequency q).re)) ≤
          Real.exp R * Real.exp (-(a * R)) * Real.exp (-(1 * (xiHeatFrequency q).re)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      refine hnorm.trans ?_
      calc coeffMass P * coeffMass P * ((1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) *
            Real.exp (-(a * (xiHeatFrequency q).re)))
          ≤ B * B * ((1 + ‖xiHeatFrequency q‖) ^ (2 * D) *
            (Real.exp R * Real.exp (-(a * R)) * Real.exp (-(1 * (xiHeatFrequency q).re)))) := by
            have hB0 : 0 ≤ B := heatPairTestMass_nonneg u
            have h1 : coeffMass P * coeffMass P ≤ B * B := mul_le_mul hcB hcB hc hB0
            have h2 := mul_le_mul hpow hexp (by positivity) (by positivity)
            exact mul_le_mul h1 h2 (by positivity) (mul_nonneg hB0 hB0)
        _ = _ := by ring
    · have := heatPairTestMass_nonneg u
      positivity
  calc _ ≤ ∑' q : XiZeroCopy, B ^ 2 * Real.exp R * Real.exp (-(a * R)) *
          ((1 + ‖xiHeatFrequency q‖) ^ (2 * D) * Real.exp (-(1 * (xiHeatFrequency q).re))) := by
        refine Summable.tsum_le_tsum hle ?_ (hf₁s.mul_left _)
        exact (summable_heatHankelTermAt ha0 P P).norm.of_nonneg_of_le
          (fun q => by split_ifs <;> positivity) fun q => by split_ifs <;> simp
    _ = _ := by rw [tsum_mul_left]; ring

/-! ## Detection -/

/-- **A negative direction at every large heat time, with bounded degree.**  For an off-line heat
frequency `u = w_{q₀}` there are a degree bound `N` and a time `A > 0` such that for every `a ≥ A`
some nonzero polynomial of degree `< N` has negative heat Hankel form. -/
theorem exists_heatHankel_re_neg_of_im_ne_zero {q₀ : XiZeroCopy}
    (hq₀ : (xiHeatFrequency q₀).im ≠ 0) :
    ∃ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree < N ∧ (heatHankel a P P).re < 0 := by
  set u := xiHeatFrequency q₀ with hu
  set D := (heatLowFrequencyKiller u).natDegree + 1
  set S₁ : ℝ := ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * D) *
    Real.exp (-(1 * (xiHeatFrequency q).re))
  have hS₁ : 0 ≤ S₁ := tsum_nonneg fun q => by positivity
  set M : ℝ := heatPairTestMass u ^ 2 * Real.exp (u.re + 1) * S₁
  have hM0 : 0 ≤ M := by have := heatPairTestMass_nonneg u; positivity
  have hc₁ := heatPairSize_pos hq₀
  have huu : u ≠ (starRingEnd ℂ) u := fun h => hq₀ (Complex.conj_eq_iff_im.1 h.symm)
  refine ⟨D + 1, max 1 (Real.log ((M + 1) / heatPairSize u)), lt_max_of_lt_left one_pos,
    fun a haA => ?_⟩
  have ha1 : 1 ≤ a := (le_max_left _ _).trans haA
  have ha : 0 < a := lt_of_lt_of_le one_pos ha1
  have hc : 0 < ‖heatPairCoefficient a u‖ := by rw [norm_heatPairCoefficient]; positivity
  set t := -(heatPairCoefficient a u / (‖heatPairCoefficient a u‖ : ℂ))
  have ht : ‖t‖ = 1 := norm_heatPairPhase hc
  refine ⟨heatPairTest u t, ?_, Nat.lt_succ_of_le (natDegree_heatPairTest_le u t), ?_⟩
  · intro h0
    have := eval_heatPairTest_self u t
    rw [h0, eval_zero] at this
    exact mul_ne_zero (eval_heatLowFrequencyKiller_ne_zero (self_not_mem_heatLowFrequencies u))
      (sub_ne_zero.2 huu) this.symm
  have hpair : ∑ q ∈ heatPairCopies u,
      (heatHankelTermAt a (heatPairTest u t) (heatPairTest u t) (xiHeatFrequency q)).re ≤
        -‖heatPairCoefficient a u‖ := by
    rw [Finset.sum_congr rfl fun q hq => re_heatHankelTermAt_pairCopy a hc hq, Finset.sum_const,
      nsmul_eq_mul]
    have hq₀F : q₀ ∈ heatPairCopies u := mem_heatPairCopies.2 (Or.inl rfl)
    have hcard : (1 : ℝ) ≤ (heatPairCopies u).card := by
      exact_mod_cast Finset.card_pos.2 ⟨q₀, hq₀F⟩
    nlinarith
  have htail := tail_heatPairTest_le ha1 (u := u) ht
  have hlog : (M + 1) / heatPairSize u ≤ Real.exp a := by
    have h1 : Real.log ((M + 1) / heatPairSize u) ≤ a := (le_max_right _ _).trans haA
    calc (M + 1) / heatPairSize u = Real.exp (Real.log ((M + 1) / heatPairSize u)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp a := Real.exp_le_exp.2 h1
  have hsplit : Real.exp (-(a * (u.re + 1))) = Real.exp (-(a * u.re)) * Real.exp (-a) := by
    rw [← Real.exp_add]; congr 1; ring
  have hMa : M * Real.exp (-a) < heatPairSize u := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos a)]
    rw [div_le_iff₀ hc₁] at hlog
    nlinarith
  have hexpu := Real.exp_pos (-(a * u.re))
  calc (heatHankel a (heatPairTest u t) (heatPairTest u t)).re
      ≤ -‖heatPairCoefficient a u‖ + M * Real.exp (-(a * (u.re + 1))) :=
        (re_heatHankel_heatPairTest_le ha).trans (add_le_add hpair htail)
    _ = Real.exp (-(a * u.re)) * (M * Real.exp (-a) - heatPairSize u) := by
        rw [norm_heatPairCoefficient, hsplit]; ring
    _ < 0 := mul_neg_of_pos_of_neg hexpu (by linarith)

/-- **Large-time detection.**  Without RH there are a rank `N` and a time `A > 0` such that, for
every `a ≥ A`, the heat Hankel form is negative on a nonzero polynomial of degree `< N`. -/
theorem exists_heatHankel_re_neg_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree < N ∧ (heatHankel a P P).re < 0 := by
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
  exact exists_heatHankel_re_neg_of_im_ne_zero (q₀ := q₀) hq₀.ne'

/-- Positive leading minors up to size `N` make the heat Hankel form nonnegative on polynomials of
degree `< N` (Sylvester's criterion). -/
theorem heatHankel_re_nonneg_of_det_pos {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hdet : ∀ k ≤ N, 0 < (leadingMatrix (heatMomentArray a) k).det) {P : ℂ[X]}
    (hP : P.natDegree < N) : 0 ≤ (heatHankel a P P).re := by
  have hPD := posDef_leadingMatrix_of_det_pos (heatMomentArray_symm a) hdet
  have hq : ∀ x : Fin N → ℝ,
      0 ≤ ∑ i : Fin N, ∑ j : Fin N, x i * x j * heatMomentArray a i j := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    have hpos := (posDef_iff_dotProduct_mulVec.1 hPD).2 hx
    have hrw : star x ⬝ᵥ (leadingMatrix (heatMomentArray a) N *ᵥ x) =
        ∑ i : Fin N, ∑ j : Fin N, x i * x j * heatMomentArray a i j := by
      simp only [dotProduct, mulVec, leadingMatrix, of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← hrw]
    exact hpos.le
  rw [re_heatHankel_eq_quadratic ha P hP]
  exact add_nonneg (hq fun i => (P.coeff i).re) (hq fun i => (P.coeff i).im)

/-- **Large-time determinant detection.**  Without RH there are `N` and `A > 0` such that for
every `a ≥ A` some leading heat Hankel determinant `Δ_M(a)`, `M ≤ N`, is `≤ 0`. -/
theorem exists_heatMomentDet_nonpos_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ M ≤ N, (leadingMatrix (heatMomentArray a) M).det ≤ 0 := by
  obtain ⟨N, A, hA, h⟩ := exists_heatHankel_re_neg_of_not_riemannHypothesis hRH
  refine ⟨N, A, hA, fun a haA => ?_⟩
  obtain ⟨P, -, hPN, hneg⟩ := h a haA
  by_contra hall
  push Not at hall
  exact hneg.not_ge (heatHankel_re_nonneg_of_det_pos (lt_of_lt_of_le hA haA) hall hPN)

/-- **RH as the large-time Hankel ladder.**  RH holds iff for every rank `N` the determinant
`Δ_N(a)` is positive for all sufficiently large heat times `a`. -/
theorem riemannHypothesis_iff_forall_eventually_heatMomentDet_pos :
    RiemannHypothesis ↔
      ∀ N : ℕ, ∀ᶠ a in atTop, 0 < (leadingMatrix (heatMomentArray a) N).det := by
  constructor
  · intro hRH N
    filter_upwards [eventually_gt_atTop 0] with a ha
    exact (riemannHypothesis_iff_heatMomentDet_pos ha).1 hRH N
  · intro h
    by_contra hRH
    obtain ⟨N, A, -, hA⟩ := exists_heatMomentDet_nonpos_of_not_riemannHypothesis hRH
    have hall : ∀ᶠ a in atTop, ∀ k ∈ Finset.range (N + 1),
        0 < (leadingMatrix (heatMomentArray a) k).det :=
      (Filter.eventually_all_finset _).2 fun k _ => h k
    obtain ⟨a, ha, haA⟩ := (hall.and (eventually_ge_atTop A)).exists
    obtain ⟨k, hk, hdet⟩ := hA a haA
    exact hdet.not_gt (ha k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))

end

end RHTower
