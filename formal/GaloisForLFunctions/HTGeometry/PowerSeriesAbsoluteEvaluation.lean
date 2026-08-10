import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleSpectralLaw
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open scoped BigOperators

noncomputable section

namespace PowerSeries

def AbsoluteSummableAt (f : PowerSeries ℂ) (u : ℂ) : Prop :=
  Summable fun n : ℕ => ‖PowerSeries.coeff n f * u ^ n‖

def absoluteEval (f : PowerSeries ℂ) (u : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n f * u ^ n

theorem AbsoluteSummableAt.summable {f : PowerSeries ℂ} {u : ℂ}
    (h : f.AbsoluteSummableAt u) :
    Summable fun n : ℕ => PowerSeries.coeff n f * u ^ n :=
  h.of_norm

theorem absoluteSummableAt_zero (u : ℂ) : (0 : PowerSeries ℂ).AbsoluteSummableAt u := by
  simp [AbsoluteSummableAt]

theorem absoluteEval_zero (u : ℂ) : (0 : PowerSeries ℂ).absoluteEval u = 0 := by
  simp [absoluteEval]

theorem absoluteSummableAt_C (c u : ℂ) : (PowerSeries.C c).AbsoluteSummableAt u := by
  rw [AbsoluteSummableAt]
  apply (hasSum_single 0 (fun n hn => ?_)).summable
  simp [PowerSeries.coeff_C, hn]

@[simp] theorem absoluteEval_C (c u : ℂ) : (PowerSeries.C c).absoluteEval u = c := by
  rw [absoluteEval, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

theorem AbsoluteSummableAt.add {f g : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (hg : g.AbsoluteSummableAt u) :
    (f + g).AbsoluteSummableAt u := by
  rw [AbsoluteSummableAt] at hf hg ⊢
  simpa only [map_add, add_mul] using (hf.of_norm.add hg.of_norm).norm

theorem absoluteEval_add {f g : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (hg : g.AbsoluteSummableAt u) :
    (f + g).absoluteEval u = f.absoluteEval u + g.absoluteEval u := by
  rw [absoluteEval, absoluteEval, absoluteEval]
  simpa [map_add, add_mul] using hf.summable.tsum_add hg.summable

theorem AbsoluteSummableAt.sum {L : Type*} (s : Finset L)
    (f : L → PowerSeries ℂ) {u : ℂ}
    (hf : ∀ l ∈ s, (f l).AbsoluteSummableAt u) :
    (∑ l ∈ s, f l).AbsoluteSummableAt u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [absoluteSummableAt_zero]
  | @insert l s hl ih =>
      rw [Finset.sum_insert hl]
      exact (hf l (Finset.mem_insert_self l s)).add
        (ih fun a ha ↦ hf a (Finset.mem_insert_of_mem ha))

theorem absoluteEval_sum {L : Type*} (s : Finset L)
    (f : L → PowerSeries ℂ) {u : ℂ}
    (hf : ∀ l ∈ s, (f l).AbsoluteSummableAt u) :
    (∑ l ∈ s, f l).absoluteEval u = ∑ l ∈ s, (f l).absoluteEval u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [absoluteEval_zero]
  | @insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl,
        absoluteEval_add (hf l (Finset.mem_insert_self l s))
          ((AbsoluteSummableAt.sum s f fun a ha ↦ hf a (Finset.mem_insert_of_mem ha))),
        ih (fun a ha ↦ hf a (Finset.mem_insert_of_mem ha))]

theorem coeff_mul_term (f g : PowerSeries ℂ) (u : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) *
          (PowerSeries.coeff kl.2 g * u ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [show n = kl.1 + kl.2 from
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hkl).symm, pow_add]
  ring

theorem AbsoluteSummableAt.mul {f g : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (hg : g.AbsoluteSummableAt u) :
    (f * g).AbsoluteSummableAt u := by
  rw [AbsoluteSummableAt]
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  convert h using 1
  ext n
  rw [coeff_mul_term]

theorem absoluteEval_mul {f g : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (hg : g.AbsoluteSummableAt u) :
    (f * g).absoluteEval u = f.absoluteEval u * g.absoluteEval u := by
  rw [absoluteEval, absoluteEval, absoluteEval]
  rw [show (fun n => PowerSeries.coeff n (f * g) * u ^ n) =
      fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) *
          (PowerSeries.coeff kl.2 g * u ^ kl.2) by
    funext n
    exact coeff_mul_term f g u n]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

theorem AbsoluteSummableAt.pow {f : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (n : ℕ) :
    (f ^ n).AbsoluteSummableAt u := by
  induction n with
  | zero => change (PowerSeries.C 1).AbsoluteSummableAt u; exact absoluteSummableAt_C 1 u
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem absoluteEval_pow {f : PowerSeries ℂ} {u : ℂ}
    (hf : f.AbsoluteSummableAt u) (n : ℕ) :
    (f ^ n).absoluteEval u = (f.absoluteEval u) ^ n := by
  induction n with
  | zero => change (PowerSeries.C 1).absoluteEval u = 1; exact absoluteEval_C 1 u
  | succ n ih =>
      rw [pow_succ, pow_succ, absoluteEval_mul (hf.pow n) hf, ih]

theorem X_absoluteSummableAt (u : ℂ) :
    (PowerSeries.X : PowerSeries ℂ).AbsoluteSummableAt u := by
  rw [AbsoluteSummableAt]
  apply (hasSum_single 1 (fun m hm => ?_)).summable
  simp [PowerSeries.coeff_X, hm]

@[simp] theorem absoluteEval_X (u : ℂ) :
    (PowerSeries.X : PowerSeries ℂ).absoluteEval u = u := by
  rw [absoluteEval, tsum_eq_single 1]
  · simp
  · intro m hm
    simp [PowerSeries.coeff_X, hm]

theorem coe_absoluteSummableAt (p : Polynomial ℂ) (u : ℂ) :
    (p : PowerSeries ℂ).AbsoluteSummableAt u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.coe_add]
      exact hp.add hq
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact (absoluteSummableAt_C c u).mul ((X_absoluteSummableAt u).pow n)

theorem coe_absoluteEval (p : Polynomial ℂ) (u : ℂ) :
    (p : PowerSeries ℂ).absoluteEval u = p.eval u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.coe_add, absoluteEval_add (coe_absoluteSummableAt p u)
        (coe_absoluteSummableAt q u), Polynomial.eval_add, hp, hq]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_pow]
      rw [Polynomial.coe_X]
      rw [absoluteEval_mul
          (absoluteSummableAt_C c u) ((X_absoluteSummableAt u).pow n),
        absoluteEval_C, absoluteEval_pow (X_absoluteSummableAt u) n,
        Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow]
      simp

theorem eval₂_absoluteSummableAt_and_eval
    (P : Polynomial (Polynomial ℂ)) (f : PowerSeries ℂ) (u : ℂ)
    (hf : f.AbsoluteSummableAt u) :
    (P.eval₂ Polynomial.coeToPowerSeries.ringHom f).AbsoluteSummableAt u ∧
      (P.eval₂ Polynomial.coeToPowerSeries.ringHom f).absoluteEval u =
        P.eval₂ (Polynomial.evalRingHom u) (f.absoluteEval u) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add]
      exact ⟨hP.1.add hQ.1, by
        rw [absoluteEval_add hP.1 hQ.1, hP.2, hQ.2, Polynomial.eval₂_add]⟩
  | monomial n p =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      have hp := coe_absoluteSummableAt p u
      refine ⟨hp.mul (hf.pow n), ?_⟩
      change ((p : PowerSeries ℂ) * f ^ n).absoluteEval u = _
      rw [absoluteEval_mul hp (hf.pow n), coe_absoluteEval,
        absoluteEval_pow hf, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X]
      rfl

theorem polynomial_relation_absoluteEval
    (P : Polynomial (Polynomial ℂ)) (f : PowerSeries ℂ) (u : ℂ)
    (hf : f.AbsoluteSummableAt u)
    (hrel : P.eval₂ Polynomial.coeToPowerSeries.ringHom f = 0) :
    P.eval₂ (Polynomial.evalRingHom u) (f.absoluteEval u) = 0 := by
  have h := (eval₂_absoluteSummableAt_and_eval P f u hf).2
  rw [hrel, absoluteEval_zero] at h
  exact h.symm

end PowerSeries

end
