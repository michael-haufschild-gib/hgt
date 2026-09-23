import GaloisForLFunctions.RHTower.ProlateHermiteTrialGramRate

/-!
# The rescaled Hermite trial space, with an explicit threshold

`eventually_hermiteTrial_rayleigh_gt` asserts liveness of the trial space below the top rung
"eventually in the bandwidth", with the margin `ε` fixed first.  Every ingredient of its proof is in
fact uniform in `ε`: the aperture masses, the correction bound and the weight bound do not see `ε`
at all, and the off-diagonal Gram entries are quadratically small in the bandwidth by
`exists_bound_hermiteTrialGram_off`.  So the threshold can be exhibited in the shape

```text
T ≤ ε · c ,
```

with one constant `T` serving every margin `0 < ε ≤ 1`.  Reading the threshold this way — rather than
as "`c` large depending on `ε`" — is what allows the margin to be taken as a function of the
bandwidth, and hence the oscillator law to acquire a rate.
-/

noncomputable section

open Filter Topology Set MeasureTheory Finset GaloisForLFunctions.HTGeometry

namespace RHTower

variable {j : ℕ}

/-- **The rescaled Hermite trial space is live below the top rung, with an explicit threshold.**
One constant `T`, depending only on the rung family and the ceiling, serves every margin
`0 < ε ≤ 1`: as soon as `T ≤ ε · c`, every nonzero trial vector has prolate Rayleigh numerator above
`−(Λ+ε)c` times its squared aperture norm. -/
theorem exists_threshold_hermiteTrial_rayleigh_gt
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) {Λ : ℝ}
    (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∃ T : ℝ, 0 < T ∧ ∀ ε c : ℝ, 0 < ε → ε ≤ 1 → T ≤ ε * c →
      ∀ a : Fin (j + 1) → ℝ, (∃ i, a i ≠ 0) →
        -((Λ + ε) * c) * (∫ x in (-1 : ℝ)..1,
            hermiteTrialVector ν a c x * hermiteTrialVector ν a c x)
          < ∫ x in (-1 : ℝ)..1,
              prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x := by
  classical
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin (j + 1) => ∫ x in (-1 : ℝ)..1, hermiteFun (ν i) x ^ (2 : ℕ)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    intro i _
    exact integral_hermiteFun_sq_pos (ν i) (by norm_num)
  have hδle : ∀ i, δ ≤ ∫ x in (-1 : ℝ)..1, hermiteFun (ν i) x ^ (2 : ℕ) := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    have h := hΛ 0
    have hν : (0 : ℝ) ≤ (ν 0 : ℝ) := Nat.cast_nonneg _
    linarith
  set M : ℝ := Λ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_hermiteTrialCorr ν
  obtain ⟨G, hG0, hG⟩ := exists_bound_hermiteTrialGram_off ν hinj
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  refine ⟨max 1 (max (2 * M * G * ((j : ℝ) + 1) / δ) (2 * C * ((j : ℝ) + 1) / δ + 1)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  set T : ℝ := max 1 (max (2 * M * G * ((j : ℝ) + 1) / δ) (2 * C * ((j : ℝ) + 1) / δ + 1))
    with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hTA : 2 * M * G * ((j : ℝ) + 1) / δ ≤ T :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hTB : 2 * C * ((j : ℝ) + 1) / δ + 1 ≤ T :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  intro ε c hε hε1 hεc
  -- the bandwidth is at least the threshold, hence at least one
  have hcpos : 0 < c := by
    by_contra hcon
    have hcon' : c ≤ 0 := not_lt.1 hcon
    have h : ε * c ≤ ε * 0 := mul_le_mul_of_nonneg_left hcon' hε.le
    rw [mul_zero] at h
    linarith
  have hcT : T ≤ c := by nlinarith
  have hc1 : (1 : ℝ) ≤ c := le_trans hT1 hcT
  have hεcsq : T ≤ ε * c ^ (2 : ℕ) := by nlinarith
  -- the weights
  set w : Fin (j + 1) → ℝ := fun i => (Λ + ε) - (2 * (ν i : ℝ) + 1) with hwdef
  have hwge : ∀ i, ε ≤ w i := by
    intro i
    have := hΛ i
    rw [hwdef]
    simp only
    linarith
  have hM : ∀ i, |w i| ≤ M := by
    intro i
    have h1 : ε ≤ w i := hwge i
    have h2 : w i ≤ M := by
      have hν : (0 : ℝ) ≤ (ν i : ℝ) := Nat.cast_nonneg _
      rw [hwdef, hMdef]
      simp only
      linarith
    rw [abs_of_nonneg (by linarith)]
    exact h2
  -- the margin parameters
  set e : ℝ := ε * δ with hedef
  have hepos : 0 < e := mul_pos hε hδpos
  set θ : ℝ := e / (2 * ((j : ℝ) + 1)) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθbound : θ * ((j : ℝ) + 1) ≤ e / 2 := by
    rw [hθdef]
    field_simp
    norm_num
  -- the off-diagonal weighted Gram entries are below the margin
  have hMG : M * G ≤ θ * c ^ (2 : ℕ) := by
    have h2 : 2 * M * G * ((j : ℝ) + 1) ≤ δ * T := by
      rw [div_le_iff₀ hδpos] at hTA
      linarith
    have h3 : δ * T ≤ δ * (ε * c ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hεcsq hδpos.le
    have h4 : θ * c ^ (2 : ℕ) = δ * (ε * c ^ (2 : ℕ)) / (2 * ((j : ℝ) + 1)) := by
      rw [hθdef, hedef]
      field_simp
    rw [h4, le_div_iff₀ (by positivity)]
    nlinarith
  have hAoff : ∀ i k : Fin (j + 1), i ≠ k → |w i * hermiteTrialGram ν c i k| ≤ θ := by
    intro i k hik
    have hGik := hG c hc1 i k hik
    have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
    rw [abs_mul]
    calc |w i| * |hermiteTrialGram ν c i k| ≤ M * (G / c ^ (2 : ℕ)) :=
          mul_le_mul (hM i) hGik (abs_nonneg _) hMpos.le
      _ = M * G / c ^ (2 : ℕ) := by ring
      _ ≤ θ := by rw [div_le_iff₀ hc2]; linarith
  -- the correction mass is beaten by the bandwidth
  have hcbig : C * ((j : ℝ) + 1) < c * (e / 2) := by
    have h2 : 2 * C * ((j : ℝ) + 1) + δ ≤ δ * T := by
      have h := hTB
      rw [div_add' _ _ _ hδpos.ne', div_le_iff₀ hδpos] at h
      linarith
    have h3 : δ * T ≤ δ * (ε * c) := mul_le_mul_of_nonneg_left hεc hδpos.le
    have h4 : c * (e / 2) = δ * (ε * c) / 2 := by
      rw [hedef]
      ring
    rw [h4]
    linarith
  -- the Gram form is positive
  intro a ha
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hsq1 : (1 : ℝ) ≤ Real.sqrt c := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc1
  have hkey : 0 < c * (∑ i, ∑ k, a i * a k * (w i * hermiteTrialGram ν c i k))
      + ∑ i, ∑ k, a i * a k * hermiteTrialCorr ν c i k := by
    refine gramForm_pos_of_bounds (e := e) (C := C) (θ := θ) ?_ hAoff (fun i k => hC c i k)
      hepos hθpos.le hC0 hθbound hcpos hcbig a ha
    intro i
    have h1 : δ ≤ hermiteTrialGram ν c i i :=
      le_trans (hδle i) (hermiteTrialGram_diag_ge hsq1 ν i)
    have h2 : ε ≤ w i := hwge i
    rw [hedef]
    nlinarith [h1, h2, hδpos, hε]
  -- unwind the two Hermite-scale identities
  have hnum := sqrt_mul_hermiteTrial_numerator hcpos ν a
  have hnorm := sqrt_mul_hermiteTrial_norm hcpos ν a
  have hid : (∑ i, ∑ k, a i * a k
        * (-(c * (2 * (ν i : ℝ) + 1)) * hermiteTrialGram ν c i k + hermiteTrialCorr ν c i k))
      + (Λ + ε) * c * (∑ i, ∑ k, a i * a k * hermiteTrialGram ν c i k)
    = c * (∑ i, ∑ k, a i * a k * (w i * hermiteTrialGram ν c i k))
      + ∑ i, ∑ k, a i * a k * hermiteTrialCorr ν c i k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hwdef]
    simp only
    ring
  have hscaled : 0 < Real.sqrt c
      * ((∫ x in (-1 : ℝ)..1,
            prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x)
        + (Λ + ε) * c * ∫ x in (-1 : ℝ)..1,
            hermiteTrialVector ν a c x * hermiteTrialVector ν a c x) := by
    have hexp : Real.sqrt c
        * ((∫ x in (-1 : ℝ)..1,
              prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x)
          + (Λ + ε) * c * ∫ x in (-1 : ℝ)..1,
              hermiteTrialVector ν a c x * hermiteTrialVector ν a c x)
        = (Real.sqrt c * ∫ x in (-1 : ℝ)..1,
              prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x)
          + (Λ + ε) * c * (Real.sqrt c * ∫ x in (-1 : ℝ)..1,
              hermiteTrialVector ν a c x * hermiteTrialVector ν a c x) := by ring
    rw [hexp, hnum, hnorm, hid]
    exact hkey
  by_contra hcon
  rw [not_lt] at hcon
  have hnp : (∫ x in (-1 : ℝ)..1,
        prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x)
      + (Λ + ε) * c * (∫ x in (-1 : ℝ)..1,
        hermiteTrialVector ν a c x * hermiteTrialVector ν a c x) ≤ 0 := by linarith
  nlinarith [hscaled, hsq, hnp]

end RHTower

end
