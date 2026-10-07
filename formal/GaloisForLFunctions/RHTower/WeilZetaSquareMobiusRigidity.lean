import GaloisForLFunctions.RHTower.AbsolutelyConvergentZetaSignRigidity
import GaloisForLFunctions.RHTower.WeilZetaSquareDilationRigidity

/-!
# Uniqueness of Weil-positive completions with an infinite Möbius part

Let `lam = Λ ⋆ a + μ ⋆ f` with `Σ (|a(n)| + |f(n)|) n^{-1/2+δ} < ∞` for some `δ > 0` and `f(1) = 0`.
If `lam` is full-cone Weil-positive, then `a = δ₁` and `f = 0`, so `lam = Λ`
(`eq_delta_and_eq_zero_of_weilPositiveFull_mobius`). Within this class a Weil-positive system
exists iff RH (`exists_weilPositive_mobius_iff`).

The `|ζ|²`-weighted boundary inequality first gives `a = δ₁` (`eq_delta_of_weilPositiveFull`). With
`A = 1` it becomes `Re(F(1/2+it) · conj ζ(1/2+it)) ≤ 0` on the whole line. This forces `F = 0` by the
sign rigidity of absolutely convergent critical Dirichlet series against `ζ`
(`ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos_of_lSeriesSummable`).
-/

open Complex
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

noncomputable section

namespace RHTower.WeilZetaSquare

variable {a f : ℕ → ℝ} {δ : ℝ}

theorem dilSeries_eq_one (h1 : a 1 = 1) (h2 : ∀ n, 2 ≤ n → a n = 0) (s : ℂ) : dilSeries a s = 1 := by
  unfold dilSeries LSeries
  rw [tsum_eq_single 1]
  · simp [LSeries.term, h1]
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [LSeries.term]
    · simp [LSeries.term, h2 n (by omega)]

theorem finiteTypeSeq_eq_zero_right (hf : ∀ n, 1 ≤ n → f n = 0) :
    finiteTypeSeq a f (fun _ => 0) = finiteTypeSeq a (fun _ => 0) (fun _ => 0) := by
  funext n
  unfold finiteTypeSeq
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 1 ≤ p.2 := by
    have := (Nat.mem_divisorsAntidiagonal.mp hp)
    rcases Nat.eq_zero_or_pos p.2 with h | h
    · rw [h, mul_zero] at this; exact absurd this.1.symm this.2
    · exact h
  rw [hf p.2 hp2]

/-- **Uniqueness with an infinite Möbius part.** If `Λ ⋆ a + μ ⋆ f` is full-cone Weil-positive,
with `a, f` absolutely convergent past `½` and `f(1) = 0`, then `a = δ₁` and `f = 0`. -/
theorem eq_delta_and_eq_zero_of_weilPositiveFull_mobius (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hW : WeilPositiveFull (finiteTypeSeq a f (fun _ => 0))) :
    a 1 = 1 ∧ (∀ n, 2 ≤ n → a n = 0) ∧ ∀ n, 1 ≤ n → f n = 0 := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull (SE := 0) hδ ha hf hf1
    WeilFiniteType.regularPart_zero hW (fun t => by simp)
  refine ⟨h1, h2, ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos_of_lSeriesSummable hδ hf hf1 fun y _ => ?_⟩
  have hb := re_boundary_ge hδ ha hf hf1 WeilFiniteType.regularPart_zero hW y
  rw [dilSeries_eq_one h1 h2, sub_self, zero_mul, zero_mul, Complex.zero_re] at hb
  simpa [linePt, dilSeries] using hb

/-- **Within the class `Λ ⋆ a + μ ⋆ f`, a Weil-positive system exists iff RH.** Here `a` and `f` are
absolutely convergent past `½` and `f(1) = 0`. -/
theorem exists_weilPositive_mobius_iff :
    (∃ (a f : ℕ → ℝ) (δ : ℝ), 0 < δ ∧
      LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧
      LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧ f 1 = 0 ∧
      WeilPositiveFull (finiteTypeSeq a f (fun _ => 0))) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · rintro ⟨a, f, δ, hδ, ha, hf, hf1, hW⟩
    obtain ⟨h1, h2, hf0⟩ := eq_delta_and_eq_zero_of_weilPositiveFull_mobius hδ ha hf hf1 hW
    rw [finiteTypeSeq_eq_zero_right hf0, finiteTypeSeq_eq_delta_left h1 h2,
      WeilFiniteType.finiteTypeSeq_delta_zero_zero] at hW
    exact hW
  · intro hW
    refine ⟨fun n => if n = 1 then 1 else 0, fun _ => 0, 1, one_pos, ?_, ?_, rfl, ?_⟩
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
    · refine summable_of_ne_finset_zero (s := ∅) fun n _ => ?_
      simp [LSeries.term]
    · rw [WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      exact hW

end RHTower.WeilZetaSquare
