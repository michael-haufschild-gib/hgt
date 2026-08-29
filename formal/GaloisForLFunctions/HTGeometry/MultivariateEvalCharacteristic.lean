import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.AlgebraicProximityBound

/-!
# The characteristic of a polynomial in several entire functions

A polynomial expression in `z` and finitely many entire functions has characteristic bounded by a
constant multiple of `log r` plus the sum of the characteristics, with an additive constant: the
bound is built by induction on the polynomial from subadditivity of the characteristic under sums and
products.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Filter ValueDistribution

/-- The evaluation of a multivariate polynomial at `(z, G₁ z, …, G_k z)` is entire. -/
theorem analyticOnNhd_eval_cons {k : ℕ} (A : MvPolynomial (Fin (k + 1)) ℂ)
    {G : Fin k → ℂ → ℂ} (hG : ∀ j, AnalyticOnNhd ℂ (G j) Set.univ) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (Fin.cons z (fun j => G j z)) A)
      (Set.univ : Set ℂ) := by
  classical
  induction A using MvPolynomial.induction_on with
  | C a =>
      intro x _
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) x)
  | add p q hp hq =>
      have heq : (fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) (p + q))
          = fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) p
            + MvPolynomial.eval (Fin.cons z (fun j => G j z)) q := by
        funext z
        simp
      rw [heq]
      intro x hx
      exact (hp x hx).add (hq x hx)
  | mul_X p i hp =>
      have hcoord : AnalyticOnNhd ℂ
          (fun z : ℂ => (Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) i)
          (Set.univ : Set ℂ) := by
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simpa using (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ)
        · have heq : (fun z : ℂ => (Fin.cons z (fun jj => G jj z) : Fin (k + 1) → ℂ) j.succ)
              = G j := by
            funext z
            simp
          rw [heq]
          exact hG j
      have heq2 : (fun z : ℂ =>
            MvPolynomial.eval (Fin.cons z (fun j => G j z)) (p * MvPolynomial.X i))
          = fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) p
            * ((Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) i) := by
        funext z
        simp
      rw [heq2]
      intro x hx
      exact (hp x hx).mul (hcoord x hx)

/-- **The characteristic of a polynomial expression in several entire functions.** -/
theorem exists_characteristic_eval_le {k : ℕ} (A : MvPolynomial (Fin (k + 1)) ℂ)
    {G : Fin k → ℂ → ℂ} (hG : ∀ j, AnalyticOnNhd ℂ (G j) Set.univ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r →
      characteristic (fun z => MvPolynomial.eval (Fin.cons z (fun j => G j z)) A) ⊤ r
        ≤ K * (Real.log r + ∑ j, characteristic (G j) ⊤ r) + K := by
  classical
  have hXnn : ∀ r : ℝ, 1 ≤ r → 0 ≤ Real.log r + ∑ j, characteristic (G j) ⊤ r := by
    intro r hr
    have h1 : 0 ≤ Real.log r := Real.log_nonneg hr
    have h2 : 0 ≤ ∑ j, characteristic (G j) ⊤ r :=
      Finset.sum_nonneg fun j _ => ValueDistribution.characteristic_nonneg hr
    linarith
  induction A using MvPolynomial.induction_on with
  | C a =>
      refine ⟨Real.posLog ‖a‖, le_max_left _ _, fun r hr => ?_⟩
      have heq : (fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z))
          (MvPolynomial.C a)) = fun _ : ℂ => a := by
        funext z
        simp
      rw [heq, GaloisForLFunctions.Nevanlinna.characteristic_const_eq]
      have hX := hXnn r hr
      have hp : (0 : ℝ) ≤ Real.posLog ‖a‖ := le_max_left _ _
      nlinarith [hX, hp]
  | add p q hp hq =>
      obtain ⟨K₁, hK₁0, hK₁⟩ := hp
      obtain ⟨K₂, hK₂0, hK₂⟩ := hq
      refine ⟨K₁ + K₂ + Real.log 2, by positivity, fun r hr => ?_⟩
      have hpan := analyticOnNhd_eval_cons p hG
      have hqan := analyticOnNhd_eval_cons q hG
      have hadd := GaloisForLFunctions.Nevanlinna.characteristic_add_le hpan hqan r
      have heq : (fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) (p + q))
          = fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) p
            + MvPolynomial.eval (Fin.cons z (fun j => G j z)) q := by
        funext z
        simp
      rw [heq]
      have h1 := hK₁ r hr
      have h2 := hK₂ r hr
      have hX := hXnn r hr
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [hadd, h1, h2, hX, hlog2]
  | mul_X p i hp =>
      obtain ⟨K₁, hK₁0, hK₁⟩ := hp
      refine ⟨K₁ + 1, by linarith, fun r hr => ?_⟩
      have hpan := analyticOnNhd_eval_cons p hG
      have hcoord : AnalyticOnNhd ℂ (fun z : ℂ => (Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) i)
          (Set.univ : Set ℂ) := by
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simpa using (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ)
        · have heq : (fun z : ℂ => (Fin.cons z (fun jj => G jj z) : Fin (k + 1) → ℂ) j.succ) = G j := by
            funext z
            simp
          rw [heq]
          exact hG j
      have hmul := GaloisForLFunctions.Nevanlinna.characteristic_mul_le hpan hcoord r
      have heq : (fun z : ℂ =>
            MvPolynomial.eval (Fin.cons z (fun j => G j z)) (p * MvPolynomial.X i))
          = fun z : ℂ => MvPolynomial.eval (Fin.cons z (fun j => G j z)) p
            * ((Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) i) := by
        funext z
        simp
      rw [heq]
      have hcoordT : characteristic (fun z : ℂ => (Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) i) ⊤ r
          ≤ Real.log r + ∑ j, characteristic (G j) ⊤ r := by
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · have hbnd : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, ‖(Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) 0‖ ≤ r := by
            intro z hz
            have hzn : ‖z‖ = |r| := by simpa using mem_sphere_zero_iff_norm.mp hz
            simpa [hzn, abs_of_nonneg (by linarith : (0:ℝ) ≤ r)] using le_of_eq rfl
          have hcoord0 : AnalyticOnNhd ℂ (fun z : ℂ => (Fin.cons z (fun j => G j z) : Fin (k + 1) → ℂ) 0)
              (Set.univ : Set ℂ) := by
            simpa using (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ)
          have h := GaloisForLFunctions.Nevanlinna.characteristic_top_le_posLog_of_bound
            hcoord0 hbnd
          have hlogeq : Real.posLog r = Real.log r := by
            rw [Real.posLog, max_eq_right (Real.log_nonneg hr)]
          rw [hlogeq] at h
          have h2 : 0 ≤ ∑ j, characteristic (G j) ⊤ r :=
            Finset.sum_nonneg fun j _ => ValueDistribution.characteristic_nonneg hr
          linarith
        · have hsingle : characteristic (G j) ⊤ r ≤ ∑ jj, characteristic (G jj) ⊤ r :=
            Finset.single_le_sum
              (f := fun jj => characteristic (G jj) ⊤ r)
              (fun jj _ => ValueDistribution.characteristic_nonneg hr) (Finset.mem_univ j)
          have h1 : 0 ≤ Real.log r := Real.log_nonneg hr
          have heq2 : (fun z : ℂ => (Fin.cons z (fun jj => G jj z) : Fin (k + 1) → ℂ) j.succ)
              = G j := by
            funext z
            simp
          rw [heq2]
          linarith
      have h1 := hK₁ r hr
      have hX := hXnn r hr
      nlinarith [hmul, h1, hcoordT, hX, hK₁0]

end GaloisForLFunctions.HTGeometry
