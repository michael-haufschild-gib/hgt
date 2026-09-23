import GaloisForLFunctions.RHTower.ProlateHermiteTrialEstimate
import GaloisForLFunctions.HTGeometry.GramFormPositivity
import GaloisForLFunctions.HTGeometry.WindowTotalSqueeze

/-!
# The rescaled Hermite trial space

A finite family of rescaled Hermite functions at distinct rungs spans a trial space on which the
prolate Rayleigh quotient stays below the top rung, once the bandwidth is large.

The Gram matrix of the family at the Hermite scale is diagonally dominant: the diagonal entries are
bounded below by the fixed aperture masses `∫_{−1}^{1}φ_n²`, and the off-diagonal entries vanish by
the Wronskian orthogonality.  The bandwidth appears only as the explicit factor `c` on the rung
term, while the corrections stay bounded, so the rung term wins.
-/

open Filter Topology Set MeasureTheory Finset GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {j : ℕ}

/-- Gram entry of the rescaled Hermite family at the Hermite scale. -/
def hermiteTrialGram (ν : Fin (j + 1) → ℕ) (c : ℝ) (i k : Fin (j + 1)) : ℝ :=
  ∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (ν i) xi * hermiteFun (ν k) xi

/-- Correction entry of the rescaled Hermite family at the Hermite scale. -/
def hermiteTrialCorr (ν : Fin (j + 1) → ℕ) (c : ℝ) (i k : Fin (j + 1)) : ℝ :=
  ∫ xi in (-Real.sqrt c)..(Real.sqrt c), hermiteCorrectionIntegrand (ν i) (ν k) xi

/-- A trial vector of the rescaled Hermite family. -/
def hermiteTrialVector (ν : Fin (j + 1) → ℕ) (a : Fin (j + 1) → ℝ) (c : ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * prolateHermiteTrial c (ν i) x

theorem hermiteTrialVector_eq (ν : Fin (j + 1) → ℕ) (a : Fin (j + 1) → ℝ) (c : ℝ) :
    hermiteTrialVector ν a c = fun x => ∑ i, a i * prolateHermiteTrial c (ν i) x := rfl

/-- The squared aperture norm of a trial vector at the Hermite scale. -/
theorem sqrt_mul_hermiteTrial_norm {c : ℝ} (hc : 0 < c) (ν : Fin (j + 1) → ℕ)
    (a : Fin (j + 1) → ℝ) :
    Real.sqrt c * (∫ x in (-1 : ℝ)..1, hermiteTrialVector ν a c x * hermiteTrialVector ν a c x)
      = ∑ i, ∑ k, a i * a k * hermiteTrialGram ν c i k := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  rw [hermiteTrialVector_eq, integral_finsetSum_mul_finsetSum Finset.univ a
    (fun i _ => continuous_prolateHermiteTrial c (ν i)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_trialPair_norm hc, hermiteTrialGram]
  field_simp

/-- The prolate Rayleigh numerator of a trial vector at the Hermite scale. -/
theorem sqrt_mul_hermiteTrial_numerator {c : ℝ} (hc : 0 < c) (ν : Fin (j + 1) → ℕ)
    (a : Fin (j + 1) → ℝ) :
    Real.sqrt c * (∫ x in (-1 : ℝ)..1,
        prolateSLAction c (hermiteTrialVector ν a c) x * hermiteTrialVector ν a c x)
      = ∑ i, ∑ k, a i * a k
          * (-(c * (2 * (ν i : ℝ) + 1)) * hermiteTrialGram ν c i k
            + hermiteTrialCorr ν c i k) := by
  rw [hermiteTrialVector_eq, integral_prolateSLAction_finsetSum_mul Finset.univ a
    (fun i _ x => hasDerivAt_prolateHermiteTrial c (ν i) x)
    (fun i _ x => hasDerivAt_prolateHermiteTrialDeriv hc.le (ν i) x)
    (fun i _ => continuous_prolateHermiteTrial c (ν i))
    (fun i _ => continuous_prolateHermiteTrialDeriv c (ν i))
    (fun i _ => continuous_prolateHermiteTrialDeriv2 c (ν i)) c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, mul_comm (Real.sqrt c) (a i * a k), mul_assoc,
    sqrt_mul_integral_trialPair_numerator hc, hermiteTrialGram, hermiteTrialCorr]

/-- The diagonal Gram entries are bounded below by the fixed unit-window masses. -/
theorem hermiteTrialGram_diag_ge {c : ℝ} (hc : (1 : ℝ) ≤ Real.sqrt c) (ν : Fin (j + 1) → ℕ)
    (i : Fin (j + 1)) :
    (∫ x in (-1 : ℝ)..1, hermiteFun (ν i) x ^ (2 : ℕ)) ≤ hermiteTrialGram ν c i i := by
  have h := window_le_total (f := hermiteFun (ν i)) hc (continuous_hermiteFun (ν i))
  rw [hermiteTrialGram]
  refine le_trans h (le_of_eq ?_)
  exact intervalIntegral.integral_congr fun x _ => by ring

/-- The off-diagonal Gram entries vanish as the bandwidth grows. -/
theorem tendsto_hermiteTrialGram_off (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν)
    {i k : Fin (j + 1)} (hik : i ≠ k) :
    Tendsto (fun c => hermiteTrialGram ν c i k) atTop (𝓝 0) :=
  (tendsto_integral_hermiteFun_mul (fun h => hik (hinj h))).comp Real.tendsto_sqrt_atTop

/-- The correction entries are bounded uniformly in the bandwidth and the index pair. -/
theorem exists_bound_hermiteTrialCorr (ν : Fin (j + 1) → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (i k : Fin (j + 1)), |hermiteTrialCorr ν c i k| ≤ C := by
  choose Cf hCf0 hCf using fun p : Fin (j + 1) × Fin (j + 1) =>
    exists_bound_hermiteCorrection (ν p.1) (ν p.2)
  obtain ⟨C, hC⟩ := Finite.exists_le Cf
  refine ⟨max C 0, le_max_right _ _, fun c i k => ?_⟩
  exact le_trans (hCf (i, k) _ _) (le_trans (hC (i, k)) (le_max_left _ _))

/-- **The rescaled Hermite trial space is live below the top rung.**  For a finite family of
distinct Hermite rungs all bounded by `Λ`, every nonzero trial vector has prolate Rayleigh
numerator above `−(Λ+ε)c` times its squared aperture norm, once the bandwidth is large. -/
theorem eventually_hermiteTrial_rayleigh_gt
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) {Λ ε : ℝ} (hε : 0 < ε)
    (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∀ᶠ c in atTop, ∀ a : Fin (j + 1) → ℝ, (∃ i, a i ≠ 0) →
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
  set w : Fin (j + 1) → ℝ := fun i => (Λ + ε) - (2 * (ν i : ℝ) + 1) with hwdef
  have hwge : ∀ i, ε ≤ w i := by
    intro i
    have := hΛ i
    rw [hwdef]
    simp only
    linarith
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin (j + 1) => |w i|)
  have hMpos : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hε ((hwge 0).trans (le_abs_self _)))
    (hM 0)
  obtain ⟨C, hC0, hC⟩ := exists_bound_hermiteTrialCorr ν
  set e : ℝ := ε * δ with hedef
  have hepos : 0 < e := mul_pos hε hδpos
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  set θ : ℝ := e / (2 * ((j : ℝ) + 1)) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθbound : θ * ((j : ℝ) + 1) ≤ e / 2 := by
    rw [hθdef]
    field_simp
    norm_num
  -- the off-diagonal Gram entries eventually fall below `θ / M`
  have hoffev : ∀ᶠ c in atTop, ∀ p : Fin (j + 1) × Fin (j + 1),
      p.1 ≠ p.2 → |hermiteTrialGram ν c p.1 p.2| ≤ θ / M := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun c h => absurd hp h
    · have hlim := tendsto_hermiteTrialGram_off ν hinj hp
      have hpos : 0 < θ / M := div_pos hθpos hMpos
      filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hlim (θ / M) hpos] with c hc
      exact fun _ => le_of_lt (by simpa [Real.norm_eq_abs] using hc)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ), hoffev,
    eventually_gt_atTop (C * ((j : ℝ) + 1) / (e / 2))] with c hcpos hc1 hcoff hcthr
  intro a ha
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hsq1 : (1 : ℝ) ≤ Real.sqrt c := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc1
  have hcbig : C * ((j : ℝ) + 1) < c * (e / 2) := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < e / 2)] at hcthr
    linarith
  -- the Gram form is positive
  have hkey : 0 < c * (∑ i, ∑ k, a i * a k * (w i * hermiteTrialGram ν c i k))
      + ∑ i, ∑ k, a i * a k * hermiteTrialCorr ν c i k := by
    refine gramForm_pos_of_bounds (e := e) (C := C) (θ := θ) ?_ ?_ (fun i k => hC c i k)
      hepos hθpos.le hC0 hθbound hcpos hcbig a ha
    · intro i
      have h1 : δ ≤ hermiteTrialGram ν c i i :=
        le_trans (hδle i) (hermiteTrialGram_diag_ge hsq1 ν i)
      have h2 : ε ≤ w i := hwge i
      rw [hedef]
      nlinarith [h1, h2, hδpos, hε]
    · intro i k hik
      have h := hcoff (i, k) hik
      have hw := hM i
      rw [abs_mul]
      calc |w i| * |hermiteTrialGram ν c i k| ≤ M * (θ / M) :=
            mul_le_mul hw h (abs_nonneg _) (le_of_lt hMpos)
        _ = θ := by field_simp
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

/-- **The rescaled Hermite trial vectors are nondegenerate.**  Once the bandwidth is large, every
nonzero coefficient vector gives a trial function of positive aperture mass — so the family is
genuinely `j+1`-dimensional on the aperture. -/
theorem eventually_hermiteTrial_norm_pos (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) :
    ∀ᶠ c in atTop, ∀ a : Fin (j + 1) → ℝ, (∃ i, a i ≠ 0) →
      0 < ∫ x in (-1 : ℝ)..1, hermiteTrialVector ν a c x * hermiteTrialVector ν a c x := by
  classical
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin (j + 1) => ∫ x in (-1 : ℝ)..1, hermiteFun (ν i) x ^ (2 : ℕ)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    intro i _
    exact integral_hermiteFun_sq_pos (ν i) (by norm_num)
  have hδle : ∀ i, δ ≤ ∫ x in (-1 : ℝ)..1, hermiteFun (ν i) x ^ (2 : ℕ) := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  set θ : ℝ := δ / (2 * ((j : ℝ) + 1)) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθbound : θ * ((j : ℝ) + 1) ≤ δ / 2 := by
    rw [hθdef]
    field_simp
    norm_num
  have hoffev : ∀ᶠ c in atTop, ∀ p : Fin (j + 1) × Fin (j + 1),
      p.1 ≠ p.2 → |hermiteTrialGram ν c p.1 p.2| ≤ θ := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun c h => absurd hp h
    · have hlim := tendsto_hermiteTrialGram_off ν hinj hp
      filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hlim θ hθpos] with c hc
      exact fun _ => le_of_lt (by simpa [Real.norm_eq_abs] using hc)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ), hoffev]
    with c hcpos hc1 hcoff
  intro a ha
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hsq1 : (1 : ℝ) ≤ Real.sqrt c := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc1
  have hkey : 0 < c * (∑ i, ∑ k, a i * a k * hermiteTrialGram ν c i k)
      + ∑ i, ∑ k, a i * a k * (fun _ _ : Fin (j + 1) => (0 : ℝ)) i k := by
    refine gramForm_pos_of_bounds (e := δ) (C := 0) (θ := θ)
      (fun i => le_trans (hδle i) (hermiteTrialGram_diag_ge hsq1 ν i))
      (fun i k hik => hcoff (i, k) hik) (fun i k => by simp)
      hδpos hθpos.le le_rfl hθbound hcpos (by simpa using mul_pos hcpos (by linarith : (0:ℝ) < δ / 2))
      a ha
  have hzero : (∑ i : Fin (j + 1), ∑ k : Fin (j + 1),
      a i * a k * (fun _ _ : Fin (j + 1) => (0 : ℝ)) i k) = 0 := by
    simp
  rw [hzero, add_zero] at hkey
  have hS : 0 < ∑ i, ∑ k, a i * a k * hermiteTrialGram ν c i k := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hkey, hcpos, hcon]
  rw [← sqrt_mul_hermiteTrial_norm hcpos ν a] at hS
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [hS, hsq, hcon]

end RHTower
