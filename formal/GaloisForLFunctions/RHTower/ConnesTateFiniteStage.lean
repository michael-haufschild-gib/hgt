import GaloisForLFunctions.RHTower.ConnesUnramifiedLocalZeta
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The finite-stage Tate factorization

Appendix I Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∫ f(x) Χ_0(x) |x|^s d^*x = Δ_s(f)`, and `Δ_s = L(Χ_0,s) Δ'_s`.

Connes' proof reduces the global integral to an infinite product of the local integrals (25).  At
a *finite* set of places that reduction is Fubini for a finite product of measure spaces, and each
factor is the geometric evaluation of `ConnesUnramifiedLocalZeta`.  The result is the partial
Euler product `∏_{v ∈ S} (1 - Χ_{0,v}(π) q_v^{-s})^{-1}`, which is Lemma 1 over `A_S` — the stage
at which §VII actually works.

The multiplicative Haar measure of `ℚ_p^*` is σ-finite because `ℚ_p^*` is σ-compact: the
valuation/unit homeomorphism carries it to `ℤ × ℤ_p^*`, a countable discrete group times a compact
group.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `ℚ_p^*` is σ-compact: the valuation/unit chart carries `ℤ × ℤ_p^*` onto it. -/
theorem connes_padic_sigmaCompact (p : ℕ) [Fact p.Prime] : SigmaCompactSpace ℚ_[p]ˣ := by
  set e := fieldOnePadicValuationUnitHomeomorph p with he
  refine ⟨⟨fun n => e '' (compactCovering (Multiplicative ℤ × ℤ_[p]ˣ) n), fun n => ?_, ?_⟩⟩
  · exact (isCompact_compactCovering _ n).image e.continuous
  · rw [← Set.image_iUnion, iUnion_compactCovering, Set.image_univ, e.surjective.range_eq]

instance connes_padic_multHaar_sigmaFinite (p : ℕ) [Fact p.Prime] :
    SigmaFinite (fieldOnePadicMultiplicativeHaar p) := by
  haveI := connes_padic_sigmaCompact p
  infer_instance

/-- **Appendix I Lemma 1 at a finite stage.**  The Tate zeta integral of a tensor product of
unramified local test functions over a finite product of `p`-adic multiplicative groups is the
product of the local Euler factors. -/
theorem connes_tate_finiteStage_prod {ι : Type*} [Fintype ι] (P : ι → Nat.Primes)
    (w : ι → ℂ) (hw : ∀ i, ‖w i‖ < 1) :
    (∫ x : (i : ι) → ℚ_[((P i : Nat.Primes) : ℕ)]ˣ,
        ∏ i, connesPadicRadial ((P i : Nat.Primes) : ℕ)
          (connesPadicUnitBallProfile (w i)) (x i)
        ∂(Measure.pi fun i => fieldOnePadicMultiplicativeHaar ((P i : Nat.Primes) : ℕ)))
      = ∏ i, (1 - w i)⁻¹ := by
  rw [integral_fintype_prod_eq_prod
    (fun i => connesPadicRadial ((P i : Nat.Primes) : ℕ) (connesPadicUnitBallProfile (w i)))]
  exact Finset.prod_congr rfl fun i _ =>
    connes_padic_unitBall_geometric ((P i : Nat.Primes) : ℕ) (hw i)

/-- **Appendix I Lemma 1 at a finite stage, zeta form.**  With `Χ_0 = 1` the local factors are
`(1 - p^{-s})^{-1}` and the finite-stage Tate integral is the partial Euler product. -/
theorem connes_tate_finiteStage_eulerProduct {ι : Type*} [Fintype ι] (P : ι → Nat.Primes)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : (i : ι) → ℚ_[((P i : Nat.Primes) : ℕ)]ˣ,
        ∏ i, connesPadicRadial ((P i : Nat.Primes) : ℕ)
          (connesPadicUnitBallProfile ((((P i : Nat.Primes) : ℕ) : ℂ) ^ (-s))) (x i)
        ∂(Measure.pi fun i => fieldOnePadicMultiplicativeHaar ((P i : Nat.Primes) : ℕ)))
      = ∏ i, (1 - (((P i : Nat.Primes) : ℕ) : ℂ) ^ (-s))⁻¹ :=
  connes_tate_finiteStage_prod P _ fun i =>
    connes_padic_norm_cpow_neg_lt_one ((P i : Nat.Primes) : ℕ) hs

end

end GaloisForLFunctions.RHTower
