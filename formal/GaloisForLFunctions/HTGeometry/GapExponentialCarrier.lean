import GaloisForLFunctions.HTGeometry.CompExpDescent
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.GapSeriesEntireCarrier

/-!
# The exponential carrier of a gap series and its translation defects

Composing a gap series with an exponential produces an entire periodic function
`z ↦ ∑ₖ cₖ exp(β·bₖ·z)`.  Its translation defect at a shift `h` is the exponential carrier of the
gap series whose coefficients are multiplied by `exp(β h)^{bₖ} − 1`.  So a defect is either a
finite exponential sum — hence differentially algebraic — or a full superlacunary gap series, hence
hypertranscendental.  There is no intermediate behaviour: the defect spectrum is exactly the set of
shifts for which the phase eventually returns to `1`.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {b : ℕ → ℕ} {c : ℕ → ℂ}

/-- The entire exponential carrier `z ↦ ∑ₖ cₖ exp(β·bₖ·z)` of a gap series. -/
def expGapFun (b : ℕ → ℕ) (c : ℕ → ℂ) (β : ℂ) : ℂ → ℂ :=
  fun z => gapFun b c (Complex.exp (β * z))

theorem contDiff_expGapFun (hEC : EntireCoeffs (gapCoeff b c)) (β : ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (expGapFun b c β) := by
  have hinner : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (β * z) :=
    Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  exact (contDiff_gapFun hEC).comp hinner

/-- **The translation defect of an exponential gap carrier** is again an exponential gap carrier,
with the coefficients multiplied by the phase deficiency. -/
theorem expGapFun_translationDefect (hinj : Function.Injective b)
    (hEC : EntireCoeffs (gapCoeff b c)) (β h : ℂ) :
    (fun z => expGapFun b c β (z + h) - expGapFun b c β z)
      = expGapFun b (fun k => c k * (Complex.exp (β * h) ^ (b k) - 1)) β := by
  funext z
  show gapFun b c (Complex.exp (β * (z + h))) - gapFun b c (Complex.exp (β * z)) = _
  rw [show β * (z + h) = β * h + β * z by ring, Complex.exp_add]
  exact gapFun_dilation_sub hinj hEC _ _

/-- A finitely supported exponential gap carrier is a finite exponential sum, hence differentially
algebraic. -/
theorem differentiallyAlgebraic_expGapFun_of_finite (hinj : Function.Injective b) {K : ℕ}
    (hfin : ∀ k, K ≤ k → c k = 0) (β : ℂ) :
    DifferentiallyAlgebraic (expGapFun b c β) := by
  have heq : expGapFun b c β
      = fun z => ∑ k ∈ Finset.range K, c k * Complex.exp ((β * (b k : ℂ)) * z) := by
    funext z
    show gapFun b c (Complex.exp (β * z)) = _
    rw [gapFun_eq_finsetSum hinj hfin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 2
    ring
  rw [heq]
  exact differentiallyAlgebraic_finset_expSum (Finset.range K) c (fun k => β * (b k : ℂ))

/-- **Hypertranscendence of the exponential gap carrier.** -/
theorem hypertranscendental_expGapFun (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1))
    (hEC : EntireCoeffs (gapCoeff b c)) (hinf : {k : ℕ | c k ≠ 0}.Infinite)
    {β : ℂ} (hβ : β ≠ 0) :
    Hypertranscendental (expGapFun b c β) :=
  hypertranscendental_comp_exp (contDiff_gapFun hEC) hβ
    (hypertranscendental_gapFun hstrict hgap hEC hinf)

/-- **The exact defect dichotomy.**  With nonzero coefficients on an eventually superlacunary
exponent sequence, a translation defect is differentially algebraic exactly when the phase
`exp(β h)` is eventually a `bₖ`-th root of unity — and otherwise it is hypertranscendental. -/
theorem differentiallyAlgebraic_expGapFun_defect_iff (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1))
    (hEC : EntireCoeffs (gapCoeff b c)) (hne : ∀ k, c k ≠ 0)
    {β : ℂ} (hβ : β ≠ 0) (h : ℂ) :
    DifferentiallyAlgebraic (fun z => expGapFun b c β (z + h) - expGapFun b c β z)
      ↔ ∃ K : ℕ, ∀ k, K ≤ k → Complex.exp (β * h) ^ (b k) = 1 := by
  classical
  set u : ℂ := Complex.exp (β * h) with hu
  set c' : ℕ → ℂ := fun k => c k * (u ^ (b k) - 1) with hc'
  have hEC' : EntireCoeffs (gapCoeff b c') := entireCoeffs_gapCoeff_defect hstrict.injective hEC u
  rw [expGapFun_translationDefect hstrict.injective hEC β h]
  constructor
  · intro hDA
    by_contra hcon
    have hinf : {k : ℕ | c' k ≠ 0}.Infinite := by
      intro hfin
      obtain ⟨M, hM⟩ := hfin.bddAbove
      refine hcon ⟨M + 1, fun k hk => ?_⟩
      by_contra hck
      have hmem : k ∈ {k : ℕ | c' k ≠ 0} := mul_ne_zero (hne k) (sub_ne_zero.2 hck)
      have := hM hmem
      omega
    exact hypertranscendental_expGapFun hstrict hgap hEC' hinf hβ hDA
  · rintro ⟨K, hK⟩
    refine differentiallyAlgebraic_expGapFun_of_finite (c := c') hstrict.injective
      (K := K) (fun k hk => ?_) β
    simp only [hc', hK k hk, sub_self, mul_zero]

end

end GaloisForLFunctions.HTGeometry
