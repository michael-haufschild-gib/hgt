import GaloisForLFunctions.RHTower.ScaleCovariantXiBernsteinAbelCorollary
import GaloisForLFunctions.RHTower.GaussHodgeCoherenceBudget

/-!
# The reciprocal atom test space and `Q₀` positivity

The folded reciprocal support of the completed `xi` divisor is the range of
`xiZeroCopyReciprocalSquare`, the inverse square of the centered spectral coordinate taken with
exact divisor multiplicity.  Summability of `∑ ‖y‖` is the corpus reciprocal-square bound, so the
test set `K = Y ∪ {0}` is compact and every atom is isolated in it.

`xiQZero f = ∑ y f(y)²` is the reciprocal quadratic form.  Its exact features:

* it is uniformly continuous for the sup norm on the atoms, with modulus the total reciprocal mass
  (`norm_xiQZero_sub_le`), so nonnegativity passes to uniform limits
  (`xiQZero_re_nonneg_of_uniform_approx`);
* the conjugation-symmetric atom isolator `xiAtomIsolator a ζ` is supported on `{a, conj a}`, is
  continuous on `K`, and reads off exactly the atom value `2 Re(a ζ²)`, so a strictly negative
  reading forces `xiQZero` strictly negative (`xiQZero_atomIsolator_re_neg`);
* under RH the form is nonnegative on every bounded conjugation-symmetric test
  (`xiQZero_re_nonneg_of_riemannHypothesis`).

Consequently a test space whose uniform closure contains the isolator at an atom forces that atom
into `ℝ_{≥0}` (`xiReciprocalAtom_nonneg_of_visible`), a test space seeing every atom is RH-strength
(`riemannHypothesis_of_visible_all`), and a test space dense only in the functions vanishing on a
set `E` still forces every atom outside `E` (`xiReciprocalAtom_nonneg_of_dense_vanishing`).
-/

noncomputable section

namespace RHTower

open Complex
open scoped ComplexOrder

/-- The folded reciprocal atom support of the completed `xi` divisor. -/
def xiReciprocalAtomSet : Set ℂ := Set.range xiZeroCopyReciprocalSquare

/-- The reciprocal test set `K = Y ∪ {0}`. -/
def xiReciprocalTestSet : Set ℂ := insert 0 xiReciprocalAtomSet

theorem xiZeroCopyReciprocalSquare_ne_zero (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q ≠ 0 := by
  rw [xiZeroCopyReciprocalSquare]
  exact pow_ne_zero 2 (inv_ne_zero (xiSpectralPoint_ne_zero q))

theorem xiSpectralPoint_conjEquiv (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyConjEquiv q) = -(starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [xiSpectralPoint, xiSpectralPoint, xiZeroCopyConjEquiv_point]
  simp only [map_mul, map_sub, map_neg, map_one, map_div₀, map_ofNat, Complex.conj_I]
  ring

/-- Conjugation on divisor copies conjugates the reciprocal atom. -/
theorem xiZeroCopyReciprocalSquare_conjEquiv (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare, xiSpectralPoint_conjEquiv,
    map_pow, map_inv₀, inv_neg, neg_pow]
  simp

/-- The reciprocal atom set is conjugation invariant. -/
theorem xiReciprocalAtomSet_conj {a : ℂ} (ha : a ∈ xiReciprocalAtomSet) :
    (starRingEnd ℂ) a ∈ xiReciprocalAtomSet := by
  obtain ⟨q, rfl⟩ := ha
  exact ⟨xiZeroCopyConjEquiv q, xiZeroCopyReciprocalSquare_conjEquiv q⟩

theorem summable_norm_xiZeroCopyReciprocalSquare :
    Summable fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    xiSpectralPoint_inv_sq_summable
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, one_div, inv_pow]

/-- The quadratic reciprocal form `Q₀[f] = ∑ y f(y)²` over the multiplicity-exact divisor. -/
def xiQZero (f : ℂ → ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q) ^ 2

theorem summable_xiQZeroTerm {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ a ∈ xiReciprocalAtomSet, ‖f a‖ ≤ M) :
    Summable fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q) ^ 2 := by
  refine Summable.of_norm_bounded
    (summable_norm_xiZeroCopyReciprocalSquare.mul_left (M ^ 2)) (fun q => ?_)
  have hle := hM _ ⟨q, rfl⟩
  rw [norm_mul, norm_pow]
  have hsq : ‖f (xiZeroCopyReciprocalSquare q)‖ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc ‖xiZeroCopyReciprocalSquare q‖ * ‖f (xiZeroCopyReciprocalSquare q)‖ ^ 2
      ≤ ‖xiZeroCopyReciprocalSquare q‖ * M ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
    _ = M ^ 2 * ‖xiZeroCopyReciprocalSquare q‖ := by ring

/-- The conjugation-symmetric atom isolator supported on `{a, conj a}`. -/
def xiAtomIsolator (a ζ : ℂ) : ℂ → ℂ :=
  fun z => if z = a then ζ else if z = (starRingEnd ℂ) a then (starRingEnd ℂ) ζ else 0

theorem xiAtomIsolator_norm_le (a ζ z : ℂ) : ‖xiAtomIsolator a ζ z‖ ≤ ‖ζ‖ := by
  unfold xiAtomIsolator
  split_ifs with h1 h2
  · exact le_rfl
  · rw [RCLike.norm_conj]
  · rw [norm_zero]; exact norm_nonneg _

theorem xiAtomIsolator_conjSymm {a ζ : ℂ} (h : a = (starRingEnd ℂ) a → ζ = (starRingEnd ℂ) ζ)
    (z : ℂ) :
    xiAtomIsolator a ζ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (xiAtomIsolator a ζ z) := by
  unfold xiAtomIsolator
  by_cases h1 : z = a
  · subst h1
    by_cases hr : z = (starRingEnd ℂ) z
    · rw [if_pos hr.symm, if_pos rfl]
      exact h hr
    · rw [if_neg (fun hc => hr hc.symm), if_pos rfl, if_pos rfl]
  · by_cases h2 : z = (starRingEnd ℂ) a
    · subst h2
      rw [Complex.conj_conj, if_pos rfl, if_neg h1, if_pos rfl, Complex.conj_conj]
    · have hn1 : (starRingEnd ℂ) z ≠ a := by
        intro hc
        exact h2 (by rw [← hc, Complex.conj_conj])
      have hn2 : (starRingEnd ℂ) z ≠ (starRingEnd ℂ) a := by
        intro hc
        exact h1 (by simpa using congrArg (starRingEnd ℂ) hc)
      rw [if_neg hn1, if_neg hn2, if_neg h1, if_neg h2, map_zero]

/-- The value of the isolator term at each divisor copy. -/
theorem xiQZeroTerm_atomIsolator (a ζ : ℂ) (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q * xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2 =
      if xiZeroCopyReciprocalSquare q = a then a * ζ ^ 2
      else if xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) a then
        (starRingEnd ℂ) (a * ζ ^ 2) else 0 := by
  unfold xiAtomIsolator
  split_ifs with h1 h2
  · rw [h1]
  · rw [h2, map_mul, map_pow]
  · rw [zero_pow (two_ne_zero), mul_zero]

/-- **The isolator detects a bad atom.**  If the isolator weight makes the atom value strictly
negative, the whole reciprocal form is strictly negative. -/
theorem xiQZero_atomIsolator_re_neg (q₀ : XiZeroCopy) (ζ : ℂ)
    (hneg : (xiZeroCopyReciprocalSquare q₀ * ζ ^ 2).re < 0) :
    (xiQZero (xiAtomIsolator (xiZeroCopyReciprocalSquare q₀) ζ)).re < 0 := by
  set a := xiZeroCopyReciprocalSquare q₀ with ha
  set w := a * ζ ^ 2 with hw
  have hsum : Summable fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q * xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2 :=
    summable_xiQZeroTerm (M := ‖ζ‖) (fun b _ => xiAtomIsolator_norm_le a ζ b)
  have hre : (xiQZero (xiAtomIsolator a ζ)).re =
      ∑' q : XiZeroCopy,
        (xiZeroCopyReciprocalSquare q *
          xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2).re :=
    Complex.re_tsum hsum
  rw [hre]
  have hterm : ∀ q : XiZeroCopy,
      (xiZeroCopyReciprocalSquare q *
        xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2).re ≤ 0 := by
    intro q
    rw [xiQZeroTerm_atomIsolator]
    split_ifs
    · exact hneg.le
    · rw [Complex.conj_re]
      exact hneg.le
    · rw [Complex.zero_re]
  have hq0 : (xiZeroCopyReciprocalSquare q₀ *
      xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q₀) ^ 2).re < 0 := by
    rw [xiQZeroTerm_atomIsolator, if_pos rfl]
    exact hneg
  have hsumre : Summable fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q *
        xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2).re :=
    hsum.map Complex.reAddGroupHom Complex.continuous_re
  have := Summable.tsum_lt_tsum (i := q₀) hterm hq0 hsumre summable_zero
  simpa using this

/-- Conjugation symmetry of a test function on a conjugation-invariant set. -/
def IsConjSymmOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ z ∈ K, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)

theorem xiAtomIsolator_isConjSymmOn {a ζ : ℂ}
    (h : a = (starRingEnd ℂ) a → ζ = (starRingEnd ℂ) ζ) (K : Set ℂ) :
    IsConjSymmOn (xiAtomIsolator a ζ) K :=
  fun z _ => xiAtomIsolator_conjSymm h z

/-- **Under RH the reciprocal form is nonnegative on every symmetric bounded test.** -/
theorem xiQZero_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ a ∈ xiReciprocalAtomSet, ‖f a‖ ≤ M)
    (hsymm : IsConjSymmOn f xiReciprocalAtomSet) : 0 ≤ (xiQZero f).re := by
  have hsum : Summable fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q) ^ 2 :=
    summable_xiQZeroTerm hM
  rw [xiQZero, Complex.re_tsum hsum]
  refine tsum_nonneg (fun q => ?_)
  have hmem : xiZeroCopyReciprocalSquare q ∈ xiReciprocalAtomSet := ⟨q, rfl⟩
  have hnn : (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q :=
    riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.mp hRH q
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
  have hconj : (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) = xiZeroCopyReciprocalSquare q :=
    Complex.conj_eq_iff_im.mpr him.symm
  have hfsymm : f (xiZeroCopyReciprocalSquare q) =
      (starRingEnd ℂ) (f (xiZeroCopyReciprocalSquare q)) := by
    have := hsymm _ hmem
    rwa [hconj] at this
  have hfim : (f (xiZeroCopyReciprocalSquare q)).im = 0 :=
    Complex.conj_eq_iff_im.mp hfsymm.symm
  have hsqre : ((f (xiZeroCopyReciprocalSquare q)) ^ 2).re =
      (f (xiZeroCopyReciprocalSquare q)).re ^ 2 := by
    rw [pow_two, Complex.mul_re, hfim]; ring
  have hsqim : ((f (xiZeroCopyReciprocalSquare q)) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im, hfim]; ring
  have hmulre : (xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q) ^ 2).re =
      (xiZeroCopyReciprocalSquare q).re * (f (xiZeroCopyReciprocalSquare q)).re ^ 2 := by
    rw [Complex.mul_re, hsqre, hsqim, ← him]
    ring
  rw [hmulre]
  exact mul_nonneg hre (sq_nonneg _)

/-- **Atom visibility.**  If the reciprocal form is nonnegative on every conjugation-symmetric
isolator at an atom, then that atom is a nonnegative real. -/
theorem xiReciprocalAtom_nonneg_of_isolator (q₀ : XiZeroCopy)
    (h : ∀ ζ : ℂ,
      (xiZeroCopyReciprocalSquare q₀ = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q₀) →
        ζ = (starRingEnd ℂ) ζ) →
      0 ≤ (xiQZero (xiAtomIsolator (xiZeroCopyReciprocalSquare q₀) ζ)).re) :
    (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q₀ := by
  by_contra hcon
  set a := xiZeroCopyReciprocalSquare q₀ with hadef
  have hane : a ≠ 0 := xiZeroCopyReciprocalSquare_ne_zero q₀
  by_cases him : a.im = 0
  · have hreal : a = (starRingEnd ℂ) a := (Complex.conj_eq_iff_im.mpr him).symm
    have hrelt : a.re < 0 := by
      by_contra hre
      exact hcon (Complex.nonneg_iff.mpr ⟨not_lt.mp hre, him.symm⟩)
    have hneg : (a * (1 : ℂ) ^ 2).re < 0 := by simpa using hrelt
    exact absurd (h 1 (fun _ => by simp)) (not_le.mpr (xiQZero_atomIsolator_re_neg q₀ 1 hneg))
  · have hnotreal : ¬ (a = (starRingEnd ℂ) a) := by
      intro hc
      exact him (Complex.conj_eq_iff_im.mp hc.symm)
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ ^ 2 = -(starRingEnd ℂ) a :=
      IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
    have hval : a * ζ ^ 2 = -((Complex.normSq a : ℝ) : ℂ) := by
      rw [hζ, mul_neg, Complex.mul_conj]
    have hneg : (a * ζ ^ 2).re < 0 := by
      rw [hval]
      simp only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero]
      exact Complex.normSq_pos.mpr hane
    exact absurd (h ζ (fun hc => absurd hc hnotreal))
      (not_le.mpr (xiQZero_atomIsolator_re_neg q₀ ζ hneg))

/-- **The reciprocal atom test is exactly RH.** -/
theorem riemannHypothesis_iff_forall_xiAtomIsolator_nonneg :
    RiemannHypothesis ↔
      ∀ (q : XiZeroCopy) (ζ : ℂ),
        (xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
          ζ = (starRingEnd ℂ) ζ) →
        0 ≤ (xiQZero (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re := by
  constructor
  · intro hRH q ζ hζ
    exact xiQZero_re_nonneg_of_riemannHypothesis hRH
      (M := ‖ζ‖) (fun b _ => xiAtomIsolator_norm_le _ ζ b)
      (xiAtomIsolator_isConjSymmOn hζ xiReciprocalAtomSet)
  · intro h
    refine riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.mpr (fun q => ?_)
    exact xiReciprocalAtom_nonneg_of_isolator q (fun ζ hζ => h q ζ hζ)

/-! ### The reciprocal test set is compact and its atoms are isolated -/

theorem tendsto_xiZeroCopyReciprocalSquare_cofinite :
    Filter.Tendsto xiZeroCopyReciprocalSquare Filter.cofinite (nhds 0) :=
  summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero

/-- **The reciprocal test set is compact.** -/
theorem isCompact_xiReciprocalTestSet : IsCompact xiReciprocalTestSet :=
  tendsto_xiZeroCopyReciprocalSquare_cofinite.isCompact_insert_range_of_cofinite

theorem zero_mem_xiReciprocalTestSet : (0 : ℂ) ∈ xiReciprocalTestSet :=
  Set.mem_insert _ _

theorem xiReciprocalAtomSet_subset : xiReciprocalAtomSet ⊆ xiReciprocalTestSet :=
  Set.subset_insert _ _

theorem xiReciprocalAtom_ne_zero {a : ℂ} (ha : a ∈ xiReciprocalAtomSet) : a ≠ 0 := by
  obtain ⟨q, rfl⟩ := ha
  exact xiZeroCopyReciprocalSquare_ne_zero q

/-- Only finitely many points of the test set have norm bounded below. -/
theorem finite_xiReciprocalTestSet_norm_ge {r : ℝ} (hr : 0 < r) :
    {z ∈ xiReciprocalTestSet | r ≤ ‖z‖}.Finite := by
  have hcof : (xiZeroCopyReciprocalSquare ⁻¹' Metric.ball 0 r)ᶜ.Finite := by
    simpa [Filter.eventually_cofinite] using
      tendsto_xiZeroCopyReciprocalSquare_cofinite (Metric.ball_mem_nhds (0 : ℂ) hr)
  refine Set.Finite.subset (hcof.image xiZeroCopyReciprocalSquare) ?_
  rintro z ⟨hzK, hzr⟩
  rcases hzK with rfl | ⟨q, rfl⟩
  · exact absurd hzr (by simpa using hr)
  · refine ⟨q, ?_, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    exact not_lt.mpr hzr

/-- **Every nonzero point of the test set is isolated in it.** -/
theorem xiReciprocalTestSet_singleton_mem_nhdsWithin {a : ℂ} (ha0 : a ≠ 0) :
    {a} ∈ nhdsWithin a xiReciprocalTestSet := by
  have hpos : 0 < ‖a‖ / 2 := by
    have := norm_pos_iff.mpr ha0
    linarith
  have hfin : {z ∈ xiReciprocalTestSet | ‖a‖ / 2 ≤ ‖z‖}.Finite :=
    finite_xiReciprocalTestSet_norm_ge hpos
  have hfin' : ({z ∈ xiReciprocalTestSet | ‖a‖ / 2 ≤ ‖z‖} \ {a}).Finite :=
    hfin.sdiff
  have hclosed : IsClosed ({z ∈ xiReciprocalTestSet | ‖a‖ / 2 ≤ ‖z‖} \ {a}) :=
    hfin'.isClosed
  have hopen : IsOpen (Metric.ball a (‖a‖ / 2) ∩
      ({z ∈ xiReciprocalTestSet | ‖a‖ / 2 ≤ ‖z‖} \ {a})ᶜ) :=
    Metric.isOpen_ball.inter hclosed.isOpen_compl
  have hmem : a ∈ Metric.ball a (‖a‖ / 2) ∩
      ({z ∈ xiReciprocalTestSet | ‖a‖ / 2 ≤ ‖z‖} \ {a})ᶜ :=
    ⟨Metric.mem_ball_self hpos, by simp⟩
  rw [mem_nhdsWithin]
  refine ⟨_, hopen, hmem, ?_⟩
  rintro z ⟨⟨hzball, hzc⟩, hzK⟩
  by_contra hza
  refine hzc ⟨⟨hzK, ?_⟩, hza⟩
  have hd : ‖z - a‖ < ‖a‖ / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have := norm_sub_norm_le a z
  have h2 : ‖a - z‖ = ‖z - a‖ := norm_sub_rev a z
  linarith [this, h2 ▸ hd]

/-- The atom isolator is continuous on the reciprocal test set. -/
theorem continuousOn_xiAtomIsolator {a ζ : ℂ} (ha : a ∈ xiReciprocalAtomSet) :
    ContinuousOn (xiAtomIsolator a ζ) xiReciprocalTestSet := by
  have ha0 : a ≠ 0 := xiReciprocalAtom_ne_zero ha
  have haK : a ∈ xiReciprocalTestSet := xiReciprocalAtomSet_subset ha
  have hcaK : (starRingEnd ℂ) a ∈ xiReciprocalTestSet :=
    xiReciprocalAtomSet_subset (xiReciprocalAtomSet_conj ha)
  have hca0 : (starRingEnd ℂ) a ≠ 0 := by
    simpa using ha0
  have hpairClosed : IsClosed ({a, (starRingEnd ℂ) a} : Set ℂ) :=
    (Set.toFinite _).isClosed
  intro z hz
  have hconst : ∀ᶠ w in nhdsWithin z xiReciprocalTestSet,
      xiAtomIsolator a ζ w = xiAtomIsolator a ζ z := by
    rcases eq_or_ne z a with rfl | hza
    · exact Filter.mem_of_superset
        (xiReciprocalTestSet_singleton_mem_nhdsWithin ha0) (by rintro w rfl; rfl)
    · rcases eq_or_ne z ((starRingEnd ℂ) a) with rfl | hzb
      · exact Filter.mem_of_superset
          (xiReciprocalTestSet_singleton_mem_nhdsWithin hca0) (by rintro w rfl; rfl)
      · have hznot : z ∈ ({a, (starRingEnd ℂ) a} : Set ℂ)ᶜ := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          push Not
          exact ⟨hza, hzb⟩
        have hnb : ({a, (starRingEnd ℂ) a} : Set ℂ)ᶜ ∈ nhdsWithin z xiReciprocalTestSet :=
          Filter.mem_of_superset
            (nhdsWithin_le_nhds (hpairClosed.isOpen_compl.mem_nhds hznot)) (fun _ h => h)
        refine Filter.mem_of_superset hnb (fun w hw => ?_)
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        push Not at hw
        simp only [Set.mem_setOf_eq, xiAtomIsolator]
        rw [if_neg hw.1, if_neg hw.2, if_neg hza, if_neg hzb]
  exact Filter.Tendsto.congr' (hconst.mono fun w hw => hw.symm) tendsto_const_nhds

/-! ### Uniform continuity of the reciprocal form and closed test spaces -/

theorem xiReciprocalAtomSet_nonempty : xiReciprocalAtomSet.Nonempty :=
  xiScaleCovariantReciprocalSquareSupport_nonempty

/-- The total reciprocal mass `∑ M_y |y|`. -/
def xiReciprocalMass : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖

theorem xiReciprocalMass_nonneg : 0 ≤ xiReciprocalMass :=
  tsum_nonneg fun _ => norm_nonneg _

theorem hasSum_xiReciprocalMass :
    HasSum (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) xiReciprocalMass :=
  summable_norm_xiZeroCopyReciprocalSquare.hasSum

/-- **Uniform continuity of the reciprocal form.**  The form moves by at most the total reciprocal
mass times the product of the uniform bound and the uniform distance. -/
theorem norm_xiQZero_sub_le {f g : ℂ → ℂ} {Mf Mg ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ a ∈ xiReciprocalAtomSet, ‖f a‖ ≤ Mf)
    (hg : ∀ a ∈ xiReciprocalAtomSet, ‖g a‖ ≤ Mg)
    (hfg : ∀ a ∈ xiReciprocalAtomSet, ‖f a - g a‖ ≤ ε) :
    ‖xiQZero f - xiQZero g‖ ≤ (Mf + Mg) * ε * xiReciprocalMass := by
  obtain ⟨a₀, ha₀⟩ := xiReciprocalAtomSet_nonempty
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hf a₀ ha₀)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hg a₀ ha₀)
  have hsf := summable_xiQZeroTerm hf
  have hsg := summable_xiQZeroTerm hg
  rw [xiQZero, xiQZero, ← Summable.tsum_sub hsf hsg]
  refine tsum_of_norm_bounded
    (g := fun q : XiZeroCopy => (Mf + Mg) * ε * ‖xiZeroCopyReciprocalSquare q‖)
    (hasSum_xiReciprocalMass.mul_left ((Mf + Mg) * ε)) (fun q => ?_)
  · have hmem : xiZeroCopyReciprocalSquare q ∈ xiReciprocalAtomSet := ⟨q, rfl⟩
    have hdiff : xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q) ^ 2 -
        xiZeroCopyReciprocalSquare q * g (xiZeroCopyReciprocalSquare q) ^ 2 =
        xiZeroCopyReciprocalSquare q *
          ((f (xiZeroCopyReciprocalSquare q) - g (xiZeroCopyReciprocalSquare q)) *
            (f (xiZeroCopyReciprocalSquare q) + g (xiZeroCopyReciprocalSquare q))) := by
      ring
    rw [hdiff, norm_mul, norm_mul]
    have h1 : ‖f (xiZeroCopyReciprocalSquare q) - g (xiZeroCopyReciprocalSquare q)‖ ≤ ε :=
      hfg _ hmem
    have h2 : ‖f (xiZeroCopyReciprocalSquare q) + g (xiZeroCopyReciprocalSquare q)‖ ≤ Mf + Mg :=
      le_trans (norm_add_le _ _) (add_le_add (hf _ hmem) (hg _ hmem))
    have hstep : ‖f (xiZeroCopyReciprocalSquare q) - g (xiZeroCopyReciprocalSquare q)‖ *
        ‖f (xiZeroCopyReciprocalSquare q) + g (xiZeroCopyReciprocalSquare q)‖ ≤ ε * (Mf + Mg) :=
      mul_le_mul h1 h2 (norm_nonneg _) hε
    calc ‖xiZeroCopyReciprocalSquare q‖ *
          (‖f (xiZeroCopyReciprocalSquare q) - g (xiZeroCopyReciprocalSquare q)‖ *
            ‖f (xiZeroCopyReciprocalSquare q) + g (xiZeroCopyReciprocalSquare q)‖)
        ≤ ‖xiZeroCopyReciprocalSquare q‖ * (ε * (Mf + Mg)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = (Mf + Mg) * ε * ‖xiZeroCopyReciprocalSquare q‖ := by ring

/-- **Positivity passes to uniform limits.** -/
theorem xiQZero_re_nonneg_of_uniform_approx {f : ℂ → ℂ} {M : ℝ}
    (hMf : ∀ a ∈ xiReciprocalAtomSet, ‖f a‖ ≤ M)
    (S : Set (ℂ → ℂ)) (hSpos : ∀ g ∈ S, 0 ≤ (xiQZero g).re)
    (happrox : ∀ ε > 0, ∃ g ∈ S, ∀ a ∈ xiReciprocalAtomSet, ‖f a - g a‖ ≤ ε) :
    0 ≤ (xiQZero f).re := by
  obtain ⟨a₀, ha₀⟩ := xiReciprocalAtomSet_nonempty
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMf a₀ ha₀)
  by_contra hcon
  push Not at hcon
  set δ : ℝ := -(xiQZero f).re with hδ
  have hδpos : 0 < δ := by simpa [hδ] using hcon
  set c : ℝ := (2 * M + 1) * xiReciprocalMass with hc
  have hc0 : 0 ≤ c := by
    have : (0:ℝ) ≤ 2 * M + 1 := by linarith
    exact mul_nonneg this xiReciprocalMass_nonneg
  set ε : ℝ := min 1 (δ / (2 * (c + 1))) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos hδpos (by linarith))
  have hεle : ε ≤ 1 := min_le_left _ _
  obtain ⟨g, hgS, hgapp⟩ := happrox ε hεpos
  have hgbdd : ∀ a ∈ xiReciprocalAtomSet, ‖g a‖ ≤ M + ε := by
    intro a ha
    have := hgapp a ha
    have h2 : ‖g a‖ - ‖f a‖ ≤ ‖g a - f a‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h2
    have := hMf a ha
    linarith
  have hbound := norm_xiQZero_sub_le hεpos.le hMf hgbdd hgapp
  have hcε : (M + (M + ε)) * ε * xiReciprocalMass ≤ c * ε := by
    have h1 : M + (M + ε) ≤ 2 * M + 1 := by linarith
    have h2 : (M + (M + ε)) * ε ≤ (2 * M + 1) * ε :=
      mul_le_mul_of_nonneg_right h1 hεpos.le
    calc (M + (M + ε)) * ε * xiReciprocalMass
        ≤ (2 * M + 1) * ε * xiReciprocalMass :=
          mul_le_mul_of_nonneg_right h2 xiReciprocalMass_nonneg
      _ = c * ε := by rw [hc]; ring
  have hclt : c * ε < δ := by
    have hle : ε ≤ δ / (2 * (c + 1)) := min_le_right _ _
    have hstep : c * ε ≤ c * (δ / (2 * (c + 1))) :=
      mul_le_mul_of_nonneg_left hle hc0
    have hfrac : c * (δ / (2 * (c + 1))) < δ := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hre : -‖xiQZero f - xiQZero g‖ ≤ (xiQZero f - xiQZero g).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hgpos : 0 ≤ (xiQZero g).re := hSpos g hgS
  have hsplit : (xiQZero f - xiQZero g).re = (xiQZero f).re - (xiQZero g).re := by
    simp [Complex.sub_re]
  rw [hsplit] at hre
  have : δ < δ := by
    calc δ = -(xiQZero f).re := hδ
      _ ≤ -((xiQZero g).re - ‖xiQZero f - xiQZero g‖) := by linarith
      _ ≤ ‖xiQZero f - xiQZero g‖ := by linarith
      _ ≤ (M + (M + ε)) * ε * xiReciprocalMass := hbound
      _ ≤ c * ε := hcε
      _ < δ := hclt
  exact lt_irrefl δ this

/-- **Visible atoms are nonnegative.**  If every conjugation-symmetric isolator at an atom is a
uniform limit on the atom set of test functions from `S`, and `Q₀` is nonnegative on `S`, then that
atom is a nonnegative real. -/
theorem xiReciprocalAtom_nonneg_of_visible (S : Set (ℂ → ℂ))
    (hSpos : ∀ g ∈ S, 0 ≤ (xiQZero g).re) (q : XiZeroCopy)
    (hvis : ∀ ζ : ℂ,
      (xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
        ζ = (starRingEnd ℂ) ζ) →
      ∀ ε > 0, ∃ g ∈ S, ∀ a ∈ xiReciprocalAtomSet,
        ‖xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ a - g a‖ ≤ ε) :
    (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q :=
  xiReciprocalAtom_nonneg_of_isolator q fun ζ hζ =>
    xiQZero_re_nonneg_of_uniform_approx (M := ‖ζ‖)
      (fun b _ => xiAtomIsolator_norm_le _ ζ b) S hSpos (hvis ζ hζ)

/-- **Dense test spaces are RH-strength.** -/
theorem riemannHypothesis_of_visible_all (S : Set (ℂ → ℂ))
    (hSpos : ∀ g ∈ S, 0 ≤ (xiQZero g).re)
    (hvis : ∀ (q : XiZeroCopy) (ζ : ℂ),
      (xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
        ζ = (starRingEnd ℂ) ζ) →
      ∀ ε > 0, ∃ g ∈ S, ∀ a ∈ xiReciprocalAtomSet,
        ‖xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ a - g a‖ ≤ ε) :
    RiemannHypothesis :=
  riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.mpr fun q =>
    xiReciprocalAtom_nonneg_of_visible S hSpos q (hvis q)

/-- The isolator at an atom outside a set vanishes on that set. -/
theorem xiAtomIsolator_eq_zero_on {a ζ : ℂ} {E : Set ℂ} (ha : a ∉ E)
    (hca : (starRingEnd ℂ) a ∉ E) : ∀ z ∈ E, xiAtomIsolator a ζ z = 0 := by
  intro z hz
  unfold xiAtomIsolator
  rw [if_neg (fun hc : z = a => ha (by rw [← hc]; exact hz)),
    if_neg (fun hc : z = (starRingEnd ℂ) a => hca (by rw [← hc]; exact hz))]

/-- **Hidden-set variant.**  A test space dense in the continuous conjugation-symmetric functions
vanishing on `E` still forces nonnegativity at every atom outside `E`. -/
theorem xiReciprocalAtom_nonneg_of_dense_vanishing (E : Set ℂ) (S : Set (ℂ → ℂ))
    (hSpos : ∀ g ∈ S, 0 ≤ (xiQZero g).re)
    (hdense : ∀ f : ℂ → ℂ, (∀ z ∈ E, f z = 0) → ContinuousOn f xiReciprocalTestSet →
      IsConjSymmOn f xiReciprocalTestSet → ∀ ε > 0, ∃ g ∈ S,
        ∀ a ∈ xiReciprocalAtomSet, ‖f a - g a‖ ≤ ε)
    (q : XiZeroCopy) (hq : xiZeroCopyReciprocalSquare q ∉ E)
    (hqc : (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) ∉ E) :
    (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q := by
  refine xiReciprocalAtom_nonneg_of_visible S hSpos q (fun ζ hζ => ?_)
  exact hdense _ (xiAtomIsolator_eq_zero_on hq hqc)
    (continuousOn_xiAtomIsolator ⟨q, rfl⟩)
    (xiAtomIsolator_isConjSymmOn hζ xiReciprocalTestSet)

/-- **Test-space closure.**  For a conjugation-symmetric test space `S` whose uniform closure on the
reciprocal test set is everything, nonnegativity of the reciprocal form on `S` is exactly RH. -/
theorem xiQZero_nonneg_on_iff_riemannHypothesis (S : Set (ℂ → ℂ))
    (hSsymm : ∀ g ∈ S, IsConjSymmOn g xiReciprocalAtomSet)
    (hSbdd : ∀ g ∈ S, ∃ M : ℝ, ∀ a ∈ xiReciprocalAtomSet, ‖g a‖ ≤ M)
    (hdense : ∀ f : ℂ → ℂ, ContinuousOn f xiReciprocalTestSet →
      IsConjSymmOn f xiReciprocalTestSet → ∀ ε > 0, ∃ g ∈ S,
        ∀ z ∈ xiReciprocalTestSet, ‖f z - g z‖ ≤ ε) :
    (∀ g ∈ S, 0 ≤ (xiQZero g).re) ↔ RiemannHypothesis := by
  constructor
  · intro hSpos
    refine riemannHypothesis_of_visible_all S hSpos (fun q ζ hζ ε hε => ?_)
    obtain ⟨g, hgS, hg⟩ :=
      hdense _ (continuousOn_xiAtomIsolator ⟨q, rfl⟩)
        (xiAtomIsolator_isConjSymmOn hζ xiReciprocalTestSet) ε hε
    exact ⟨g, hgS, fun a ha => hg a (xiReciprocalAtomSet_subset ha)⟩
  · intro hRH g hgS
    obtain ⟨M, hM⟩ := hSbdd g hgS
    exact xiQZero_re_nonneg_of_riemannHypothesis hRH hM (hSsymm g hgS)

end RHTower
