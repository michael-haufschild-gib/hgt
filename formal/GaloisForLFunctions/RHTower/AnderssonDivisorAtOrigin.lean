import GaloisForLFunctions.RHTower.AnderssonTheoremTwo

/-!
# Prescribing a divisor that also charges the origin

The realization of a divisor by a quotient of Weierstrass products carries no order at the origin,
because the elementary factors are normalized there.  Multiplying by an integer power of `z`
supplies it: the extra logarithmic derivative `k/s` costs nothing in the Arakelyan step, because
`(s² + s)·(k/s) = k(s+1)` is entire.
-/

noncomputable section

open MeasureTheory Filter Set Complex GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A prescribed-divisor realization with a prescribed order at the origin. -/
def originDivisorFunction (k : ℤ) (a b : ℕ → ℂ) : ℂ → ℂ :=
  fun z => z ^ k * GaloisForLFunctions.divisorFunction a b z

theorem originDivisorFunction_eq_mul (k : ℤ) (a b : ℕ → ℂ) :
    originDivisorFunction k a b
      = (fun w : ℂ => w ^ k) * GaloisForLFunctions.divisorFunction a b := rfl

theorem ne_zero_of_one_le_re {z : ℂ} (hz : 1 ≤ z.re) : z ≠ 0 := by
  intro h
  rw [h, Complex.zero_re] at hz
  linarith

theorem analyticAt_zpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (k : ℤ) :
    AnalyticAt ℂ (fun w : ℂ => w ^ k) z := by
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) z := analyticAt_id (z := z)
  have h : AnalyticAt ℂ ((id : ℂ → ℂ) ^ k) z := hid.zpow (by simpa using hz)
  have hfun : ((id : ℂ → ℂ) ^ k) = fun w : ℂ => w ^ k := by
    funext w
    rw [Pi.pow_apply]
    rfl
  rwa [hfun] at h

theorem meromorphicAt_zpow (k : ℤ) (z : ℂ) : MeromorphicAt (fun w : ℂ => w ^ k) z := by
  have h : MeromorphicAt ((id : ℂ → ℂ) ^ k) z :=
    MeromorphicAt.zpow (f := (id : ℂ → ℂ)) (x := z) (analyticAt_id (z := z)).meromorphicAt (n := k)
  have hfun : ((id : ℂ → ℂ) ^ k) = fun w : ℂ => w ^ k := by
    funext w
    rw [Pi.pow_apply]
    rfl
  rwa [hfun] at h

theorem analyticAt_originDivisorFunction (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hbre : ∀ n, (b n).re < 1) {z : ℂ} (hz : 1 ≤ z.re) :
    AnalyticAt ℂ (originDivisorFunction k a b) z :=
  (analyticAt_zpow_of_ne_zero (ne_zero_of_one_le_re hz) k).mul
    (divisorFunction_analyticAt_of_re_le ha hane hb hbne hbre hz)

theorem originDivisorFunction_ne_zero (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) {z : ℂ} (hz : 1 ≤ z.re) :
    originDivisorFunction k a b z ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (ne_zero_of_one_le_re hz))
    (divisorFunction_ne_zero_of_re_le ha hane hb hbne hare hbre hz)

theorem logDeriv_originDivisorFunction (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) {z : ℂ} (hz : 1 ≤ z.re) :
    logDeriv (originDivisorFunction k a b) z
      = (k : ℂ) / z + logDeriv (GaloisForLFunctions.divisorFunction a b) z := by
  have hz0 : z ≠ 0 := ne_zero_of_one_le_re hz
  have h1 : (fun w : ℂ => w ^ k) z ≠ 0 := zpow_ne_zero _ hz0
  have h2 : GaloisForLFunctions.divisorFunction a b z ≠ 0 :=
    divisorFunction_ne_zero_of_re_le ha hane hb hbne hare hbre hz
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => w ^ k) z :=
    (analyticAt_zpow_of_ne_zero hz0 k).differentiableAt
  have hd2 : DifferentiableAt ℂ (GaloisForLFunctions.divisorFunction a b) z :=
    (divisorFunction_analyticAt_of_re_le ha hane hb hbne hbre hz).differentiableAt
  have hmul := logDeriv_mul z h1 h2 hd1 hd2
  rw [logDeriv_zpow z k] at hmul
  exact hmul

/-- **Lemma 1 for a divisor charging the origin.** -/
theorem exists_mellin_add_entire_logDeriv_originDivisorFunction (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ (q : ℝ → ℂ) (g : ℂ → ℂ), Differentiable ℂ g ∧
      AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ))) ∧
      Tendsto q atTop (nhds 0) ∧ (∃ M : ℝ, ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M) ∧
      ∀ s : ℂ, 1 < s.re →
        logDeriv (originDivisorFunction k a b) s
          = (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + g s := by
  obtain ⟨G, hGd, hGb⟩ :=
    exists_entire_approx_sq_logDeriv_divisorFunction (1 : ℂ) ha hane hb hbne hare hbre
      (ε := 1) one_pos
  refine exists_mellin_add_entire (G := fun s => G s + (k : ℂ) * (s + 1)) (fun z hz => ?_)
    (hGd.add ((differentiable_const ((k : ℂ))).mul (differentiable_id.add_const 1))) ?_
  · have hFa : AnalyticAt ℂ (originDivisorFunction k a b) z :=
      analyticAt_originDivisorFunction k ha hane hb hbne hbre hz
    have hFne : originDivisorFunction k a b z ≠ 0 :=
      originDivisorFunction_ne_zero k ha hane hb hbne hare hbre hz
    exact hFa.deriv.div hFa hFne
  · intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_one_le_re hs
    rw [logDeriv_originDivisorFunction k ha hane hb hbne hare hbre hs]
    have hexp : (s ^ 2 + s) * ((k : ℂ) / s
          + logDeriv (GaloisForLFunctions.divisorFunction a b) s)
          - (G s + (k : ℂ) * (s + 1))
        = (s ^ 2 + 1 * s) * logDeriv (GaloisForLFunctions.divisorFunction a b) s - G s := by
      field_simp
      ring
    rw [hexp]
    exact hGb s hs

theorem meromorphicOn_originDivisorFunction (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) :
    MeromorphicOn (originDivisorFunction k a b) Set.univ := by
  intro z _
  have h1 : MeromorphicAt (fun w : ℂ => w ^ k) z := meromorphicAt_zpow k z
  exact h1.mul ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z
    (Set.mem_univ z))

theorem meromorphicOrderAt_zpow_id (k : ℤ) (z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => w ^ k) z = if z = 0 then (k : WithTop ℤ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    have hid : MeromorphicAt (fun w : ℂ => w) 0 := (analyticAt_id (z := (0:ℂ))).meromorphicAt
    have hord : meromorphicOrderAt (fun w : ℂ => w) 0 = 1 := by
      have hana : AnalyticAt ℂ (fun w : ℂ => w) 0 := analyticAt_id
      rw [hana.meromorphicOrderAt_eq]
      have h1 : analyticOrderAt (fun w : ℂ => w) 0 = (1 : ℕ) := by
        refine (hana.analyticOrderAt_eq_natCast).2 ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
        filter_upwards with w
        simp
      rw [h1]
      rfl
    have hzp := meromorphicOrderAt_zpow (f := fun w : ℂ => w) (x := (0:ℂ)) hid (n := k)
    rw [hord, mul_one] at hzp
    have hfun : ((fun w : ℂ => w) ^ k) = fun w : ℂ => w ^ k := by
      funext w
      rw [Pi.pow_apply]
    rw [hfun] at hzp
    rw [if_pos rfl]
    exact hzp
  · rw [if_neg hz]
    have hana : AnalyticAt ℂ (fun w : ℂ => w ^ k) z := analyticAt_zpow_of_ne_zero hz k
    have hne : (fun w : ℂ => w ^ k) z ≠ 0 := zpow_ne_zero _ hz
    rw [hana.meromorphicOrderAt_eq,
      (analyticOrderAt_eq_zero (f := fun w : ℂ => w ^ k) (z₀ := z)).2 (Or.inr hne)]
    rfl

theorem meromorphicOrderAt_originDivisorFunction (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) (z : ℂ) :
    meromorphicOrderAt (originDivisorFunction k a b) z
      = (if z = 0 then (k : WithTop ℤ) else 0)
        + (((GaloisForLFunctions.zeroMultiplicity a z : ℤ) : WithTop ℤ)
          - ((GaloisForLFunctions.zeroMultiplicity b z : ℤ) : WithTop ℤ)) := by
  have h1 : MeromorphicAt (fun w : ℂ => w ^ k) z := meromorphicAt_zpow k z
  have h2 := (GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z (Set.mem_univ z)
  rw [originDivisorFunction_eq_mul, meromorphicOrderAt_mul h1 h2, meromorphicOrderAt_zpow_id,
    GaloisForLFunctions.meromorphicOrderAt_divisorFunction_eq_multiplicity ha hane hb hbne]

/-- **Divisor surjectivity with an order at the origin.** -/
theorem exists_continuable_phase_with_divisor_at_origin (k : ℤ) {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (Z s)) ∧
        ∀ z : ℂ, meromorphicOrderAt Z z
          = (if z = 0 then (k : WithTop ℤ) else 0)
            + (((GaloisForLFunctions.zeroMultiplicity a z : ℤ) : WithTop ℤ)
              - ((GaloisForLFunctions.zeroMultiplicity b z : ℤ) : WithTop ℤ)) := by
  obtain ⟨q, g₁, hg₁, hqmeas, hq0, ⟨M, hqb⟩, hrep⟩ :=
    exists_mellin_add_entire_logDeriv_originDivisorFunction k ha hane hb hbne hare hbre
  obtain ⟨χ, hχ, Z, hZmero, hZprod, hZord⟩ :=
    exists_continuable_phase_of_mellin_logDeriv
      (meromorphicOn_originDivisorFunction k ha hane hb hbne)
      (fun z hz => analyticAt_originDivisorFunction k ha hane hb hbne hbre hz)
      (fun z hz => originDivisorFunction_ne_zero k ha hane hb hbne hare hbre hz)
      hg₁ hqmeas hq0 hqb hrep
  refine ⟨χ, hχ, Z, hZmero, hZprod, fun z => ?_⟩
  rw [hZord z]
  exact meromorphicOrderAt_originDivisorFunction k ha hane hb hbne z

end RHTower

end
