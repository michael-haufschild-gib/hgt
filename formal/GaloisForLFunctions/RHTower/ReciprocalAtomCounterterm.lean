import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure

/-!
# Reciprocal atom multiplicities and counterterm locality

Each reciprocal atom has a finite fiber of divisor copies, so `xiAtomMultiplicity a` is a positive
natural number at every atom, and conjugate atoms carry equal multiplicity.  Evaluating the
reciprocal form on the atom isolator therefore gives the exact local readings

`Q₀[e_a] = M_a · a ζ²`  (real atom),   `Q₀[e_{a,ζ}] = M_a a ζ² + M_a conj(a ζ²)`  (conjugate pair),

whose real parts are `M_a Re(a ζ²)` and `2 M_a Re(a ζ²)`.

A counterterm is any real functional `C` on test functions and the repaired form is
`Q₀ + C`.  Three consequences follow.

* A counterterm factoring through a linear map `L` and a quadratic form is invisible on `ker L`,
  so repaired positivity is bare `Q₀` positivity on the kernel test space; if that space still
  resolves every atom, the repair is RH-strength.
* Repaired positivity restricts to every atom-isolator subspace, so a counterterm vanishing on all
  of them is RH-transparent.
* Where the counterterm is nonzero it must pay the exact local bill: `M_a a + C[e_a] ≥ 0` at a real
  atom and `2 M_a Re(a ζ²) + C[e_{a,ζ}] ≥ 0` on a conjugate pair.  The atom-fed counterterm
  `-Q₀[e_{a,f(a)}]` shows both bounds are attained.
-/

noncomputable section

namespace RHTower

open Complex
open scoped ComplexOrder

/-- The set of divisor copies carrying a given reciprocal atom. -/
def xiAtomFiber (a : ℂ) : Set XiZeroCopy := {q | xiZeroCopyReciprocalSquare q = a}

theorem xiAtomFiber_finite {a : ℂ} (ha : a ≠ 0) : (xiAtomFiber a).Finite := by
  have hcof : (xiZeroCopyReciprocalSquare ⁻¹' Metric.ball 0 ‖a‖)ᶜ.Finite := by
    simpa [Filter.eventually_cofinite] using
      tendsto_xiZeroCopyReciprocalSquare_cofinite
        (Metric.ball_mem_nhds (0 : ℂ) (norm_pos_iff.mpr ha))
  refine hcof.subset (fun q hq => ?_)
  simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right, not_lt]
  exact le_of_eq (congrArg norm hq).symm

/-- The folded multiplicity of a reciprocal atom. -/
def xiAtomMultiplicity (a : ℂ) : ℕ := (xiAtomFiber a).ncard

theorem summable_xiAtomIndicator {a : ℂ} (ha : a ≠ 0) :
    Summable fun q : XiZeroCopy => if xiZeroCopyReciprocalSquare q = a then (1 : ℂ) else 0 := by
  refine summable_of_hasFiniteSupport ((xiAtomFiber_finite ha).subset (fun q hq => ?_))
  by_contra hc
  exact hq (if_neg hc)

theorem tsum_xiAtomIndicator {a : ℂ} (ha : a ≠ 0) :
    (∑' q : XiZeroCopy, if xiZeroCopyReciprocalSquare q = a then (1 : ℂ) else 0)
      = (xiAtomMultiplicity a : ℂ) := by
  classical
  have hfin := xiAtomFiber_finite ha
  rw [tsum_eq_sum (s := hfin.toFinset) (fun q hq => ?_)]
  · rw [Finset.sum_congr rfl (fun q hq => ?_), Finset.sum_const, nsmul_eq_mul, mul_one,
      xiAtomMultiplicity, Set.ncard_eq_toFinset_card _ hfin]
    exact if_pos (by simpa [xiAtomFiber] using (hfin.mem_toFinset).mp hq)
  · refine if_neg (fun hc => hq ?_)
    exact hfin.mem_toFinset.mpr hc

theorem xiAtomMultiplicity_pos {a : ℂ} (ha : a ∈ xiReciprocalAtomSet) :
    0 < xiAtomMultiplicity a := by
  obtain ⟨q, rfl⟩ := ha
  refine Set.ncard_pos (xiAtomFiber_finite (xiZeroCopyReciprocalSquare_ne_zero q)) |>.mpr ⟨q, rfl⟩

/-- Conjugate atoms carry the same folded multiplicity. -/
theorem xiAtomMultiplicity_conj (a : ℂ) :
    xiAtomMultiplicity ((starRingEnd ℂ) a) = xiAtomMultiplicity a := by
  have hbij : xiAtomFiber ((starRingEnd ℂ) a) = xiZeroCopyConjEquiv '' xiAtomFiber a := by
    ext q
    constructor
    · intro hq
      refine ⟨xiZeroCopyConjEquiv q, ?_, xiZeroCopyConjEquiv_apply_apply q⟩
      have : xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) =
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) :=
        xiZeroCopyReciprocalSquare_conjEquiv q
      rw [xiAtomFiber, Set.mem_setOf_eq, this]
      have hq' : xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) a := hq
      rw [hq', Complex.conj_conj]
    · rintro ⟨p, hp, rfl⟩
      rw [xiAtomFiber, Set.mem_setOf_eq, xiZeroCopyReciprocalSquare_conjEquiv]
      have hp' : xiZeroCopyReciprocalSquare p = a := hp
      rw [hp']
  rw [xiAtomMultiplicity, xiAtomMultiplicity, hbij,
    Set.ncard_image_of_injective _ xiZeroCopyConjEquiv.injective]

/-! ### The reciprocal form at an isolator -/

theorem xiQZero_atomIsolator_of_eq_conj {a : ℂ} (ha : a ≠ 0)
    (heq : a = (starRingEnd ℂ) a) (ζ : ℂ) :
    xiQZero (xiAtomIsolator a ζ) = (xiAtomMultiplicity a : ℂ) * (a * ζ ^ 2) := by
  have hterm : ∀ q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q * xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2 =
        (a * ζ ^ 2) * (if xiZeroCopyReciprocalSquare q = a then (1 : ℂ) else 0) := by
    intro q
    rw [xiQZeroTerm_atomIsolator]
    by_cases h1 : xiZeroCopyReciprocalSquare q = a
    · rw [if_pos h1, if_pos h1, mul_one]
    · rw [if_neg h1, if_neg (by rw [← heq]; exact h1), if_neg h1, mul_zero]
  rw [xiQZero]
  rw [tsum_congr hterm, tsum_mul_left, tsum_xiAtomIndicator ha]
  ring

theorem xiQZero_atomIsolator_of_ne_conj {a : ℂ} (ha : a ≠ 0)
    (hne : a ≠ (starRingEnd ℂ) a) (ζ : ℂ) :
    xiQZero (xiAtomIsolator a ζ) =
      (xiAtomMultiplicity a : ℂ) * (a * ζ ^ 2) +
        (xiAtomMultiplicity a : ℂ) * (starRingEnd ℂ) (a * ζ ^ 2) := by
  have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have hterm : ∀ q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q * xiAtomIsolator a ζ (xiZeroCopyReciprocalSquare q) ^ 2 =
        (a * ζ ^ 2) * (if xiZeroCopyReciprocalSquare q = a then (1 : ℂ) else 0) +
          ((starRingEnd ℂ) (a * ζ ^ 2)) *
            (if xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) a then (1 : ℂ) else 0) := by
    intro q
    rw [xiQZeroTerm_atomIsolator]
    by_cases h1 : xiZeroCopyReciprocalSquare q = a
    · have h2 : xiZeroCopyReciprocalSquare q ≠ (starRingEnd ℂ) a := by
        rw [h1]; exact hne
      rw [if_pos h1, if_pos h1, if_neg h2]
      ring
    · by_cases h2 : xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) a
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  rw [xiQZero, tsum_congr hterm,
    Summable.tsum_add ((summable_xiAtomIndicator ha).mul_left _)
      ((summable_xiAtomIndicator hca).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_xiAtomIndicator ha, tsum_xiAtomIndicator hca,
    xiAtomMultiplicity_conj]
  ring

theorem xiQZero_atomIsolator_re_of_eq_conj {a : ℂ} (ha : a ≠ 0)
    (heq : a = (starRingEnd ℂ) a) (ζ : ℂ) :
    (xiQZero (xiAtomIsolator a ζ)).re = (xiAtomMultiplicity a : ℝ) * (a * ζ ^ 2).re := by
  rw [xiQZero_atomIsolator_of_eq_conj ha heq ζ, Complex.mul_re]
  simp

theorem xiQZero_atomIsolator_re_of_ne_conj {a : ℂ} (ha : a ≠ 0)
    (hne : a ≠ (starRingEnd ℂ) a) (ζ : ℂ) :
    (xiQZero (xiAtomIsolator a ζ)).re =
      2 * (xiAtomMultiplicity a : ℝ) * (a * ζ ^ 2).re := by
  rw [xiQZero_atomIsolator_of_ne_conj ha hne ζ]
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, mul_neg, sub_neg_eq_add]
  ring

/-! ### Finite-rank and continuous counterterms -/

/-- The repaired reciprocal form: the base form plus a counterterm. -/
def xiRepairedForm (C : (ℂ → ℂ) → ℝ) (f : ℂ → ℂ) : ℝ := (xiQZero f).re + C f

/-- **Finite-rank kernel visibility.**  A counterterm factoring through a linear map is invisible
on that map's kernel, so a positive repair is a positive base form there. -/
theorem xiQZero_re_nonneg_on_ker {r : ℕ} (L : (ℂ → ℂ) →ₗ[ℝ] (Fin r → ℝ))
    (B : QuadraticForm ℝ (Fin r → ℝ))
    (h : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm (fun g => B (L g)) f)
    {f : ℂ → ℂ} (hf : L f = 0) : 0 ≤ (xiQZero f).re := by
  have hf' := h f
  rw [xiRepairedForm, hf] at hf'
  simpa using hf'

/-- **A finite-rank counterterm sees only its kernel.**  If the kernel test space still resolves
every reciprocal atom, the repaired positivity is RH-strength. -/
theorem riemannHypothesis_of_finiteRank_kernel_visible {r : ℕ}
    (L : (ℂ → ℂ) →ₗ[ℝ] (Fin r → ℝ)) (B : QuadraticForm ℝ (Fin r → ℝ))
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm (fun g => B (L g)) f)
    (hvis : ∀ (q : XiZeroCopy) (ζ : ℂ),
      (xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
        ζ = (starRingEnd ℂ) ζ) →
      ∀ ε > 0, ∃ g ∈ {u : ℂ → ℂ | L u = 0}, ∀ a ∈ xiReciprocalAtomSet,
        ‖xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ a - g a‖ ≤ ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_visible_all {u : ℂ → ℂ | L u = 0}
    (fun _ hg => xiQZero_re_nonneg_on_ker L B hpos hg) hvis

/-- **Atom locality.**  Positivity of a repaired form restricts to every atom-isolator line. -/
theorem xiRepairedForm_nonneg_on_isolator (C : (ℂ → ℂ) → ℝ)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f) (q : XiZeroCopy) (ζ : ℂ) :
    0 ≤ (xiQZero (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re +
      C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) := hpos _

/-- **Atom-local counterterms are RH-transparent.**  A counterterm vanishing on every atom-isolator
subspace leaves the repaired positivity exactly as strong as RH. -/
theorem riemannHypothesis_of_counterterm_atomLocal (C : (ℂ → ℂ) → ℝ)
    (hC : ∀ (q : XiZeroCopy) (ζ : ℂ), C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) = 0)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f) : RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_xiAtomIsolator_nonneg.mpr (fun q ζ _ => ?_)
  have hq := hpos (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)
  rwa [xiRepairedForm, hC q ζ, add_zero] at hq

/-- **Local domination threshold at a real atom.** -/
theorem counterterm_realAtom_threshold (C : (ℂ → ℂ) → ℝ)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f) (q : XiZeroCopy)
    (hreal : xiZeroCopyReciprocalSquare q = (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)) :
    0 ≤ (xiAtomMultiplicity (xiZeroCopyReciprocalSquare q) : ℝ) *
        (xiZeroCopyReciprocalSquare q).re +
      C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) 1) := by
  have hq := hpos (xiAtomIsolator (xiZeroCopyReciprocalSquare q) 1)
  rw [xiRepairedForm, xiQZero_atomIsolator_re_of_eq_conj
    (xiZeroCopyReciprocalSquare_ne_zero q) hreal 1] at hq
  simpa using hq

/-- **Local domination threshold at a non-real atom.**  The two-real-dimensional isolator form
`C_a(ζ) + 2 M_a Re(a ζ²)` is positive semidefinite. -/
theorem counterterm_nonrealAtom_threshold (C : (ℂ → ℂ) → ℝ)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f) (q : XiZeroCopy)
    (hne : xiZeroCopyReciprocalSquare q ≠ (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q))
    (ζ : ℂ) :
    0 ≤ 2 * (xiAtomMultiplicity (xiZeroCopyReciprocalSquare q) : ℝ) *
        (xiZeroCopyReciprocalSquare q * ζ ^ 2).re +
      C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) := by
  have hq := hpos (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)
  rwa [xiRepairedForm, xiQZero_atomIsolator_re_of_ne_conj
    (xiZeroCopyReciprocalSquare_ne_zero q) hne ζ] at hq

/-- The atom-fed counterterm paying exactly the local bill at one atom. -/
def xiAtomFedCounterterm (a : ℂ) (f : ℂ → ℂ) : ℝ :=
  -(xiQZero (xiAtomIsolator a (f a))).re

theorem xiAtomFedCounterterm_eq_of_eq_conj {a : ℂ} (ha : a ≠ 0)
    (heq : a = (starRingEnd ℂ) a) (f : ℂ → ℂ) :
    xiAtomFedCounterterm a f = -((xiAtomMultiplicity a : ℝ) * (a * f a ^ 2).re) := by
  rw [xiAtomFedCounterterm, xiQZero_atomIsolator_re_of_eq_conj ha heq]

theorem xiAtomFedCounterterm_eq_of_ne_conj {a : ℂ} (ha : a ≠ 0)
    (hne : a ≠ (starRingEnd ℂ) a) (f : ℂ → ℂ) :
    xiAtomFedCounterterm a f = -(2 * (xiAtomMultiplicity a : ℝ) * (a * f a ^ 2).re) := by
  rw [xiAtomFedCounterterm, xiQZero_atomIsolator_re_of_ne_conj ha hne]

/-- **Sharpness.**  The atom-fed counterterm makes the repaired form vanish identically on the
isolator subspace of its atom. -/
theorem xiAtomFedCounterterm_cancels (a ζ : ℂ) :
    xiRepairedForm (xiAtomFedCounterterm a) (xiAtomIsolator a ζ) = 0 := by
  rw [xiRepairedForm, xiAtomFedCounterterm]
  simp [xiAtomIsolator]

/-- The atom-fed counterterm is rank one: it factors through the single evaluation `f ↦ f a`. -/
theorem xiAtomFedCounterterm_factors_eval (a : ℂ) {f g : ℂ → ℂ} (h : f a = g a) :
    xiAtomFedCounterterm a f = xiAtomFedCounterterm a g := by
  rw [xiAtomFedCounterterm, xiAtomFedCounterterm, h]

/-- **A counterterm annihilating every atom-isolator is RH-transparent**, in the finite-rank form:
if the boundary map kills every isolator, the repaired positivity is RH. -/
theorem riemannHypothesis_of_boundaryMap_kills_isolators {r : ℕ}
    (L : (ℂ → ℂ) →ₗ[ℝ] (Fin r → ℝ)) (B : QuadraticForm ℝ (Fin r → ℝ))
    (hL : ∀ (q : XiZeroCopy) (ζ : ℂ),
      L (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) = 0)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm (fun g => B (L g)) f) : RiemannHypothesis :=
  riemannHypothesis_of_counterterm_atomLocal _ (fun q ζ => by rw [hL q ζ]; simp) hpos

/-- **Vanishing point masses annihilate the atom isolators.**  A boundary functional given by
integration against a Borel measure carrying no mass at the two atom points kills the isolator.
A signed boundary functional is the difference of two such integrals, so the same conclusion holds
for it componentwise. -/
theorem integral_xiAtomIsolator_eq_zero {μ : MeasureTheory.Measure ℂ} {a ζ : ℂ}
    (ha : μ {a} = 0) (hca : μ {(starRingEnd ℂ) a} = 0) :
    ∫ z, xiAtomIsolator a ζ z ∂μ = 0 := by
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({a, (starRingEnd ℂ) a} : Set ℂ)) ?_ ?_
  · intro z hz
    by_contra hzc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzc
    push Not at hzc
    exact hz (by simp only [Pi.zero_apply, xiAtomIsolator, if_neg hzc.1, if_neg hzc.2])
  · rw [Set.insert_eq]
    exact MeasureTheory.measure_union_null ha hca

end RHTower
