import GaloisForLFunctions.HTGeometry.SchwartzSmoothMultiplierApproximation

/-!
# Smooth multiplier symmetry on compact spectral packets

Polynomial momentum symmetry extends, by smooth Weierstrass approximation, to every smooth
temperate real multiplier on compact packets.  Complex polarization then gives the adjoint law
for arbitrary complex temperate multipliers.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial

noncomputable section

namespace SchwartzMap

def rescalePolynomialToSpectralMomentum (P : ℝ[X]) : ℝ[X] :=
  P.comp (Polynomial.C ((2 * Real.pi)⁻¹) * Polynomial.X)

theorem eval_rescalePolynomialToSpectralMomentum (P : ℝ[X]) (t : ℝ) :
    (rescalePolynomialToSpectralMomentum P).eval (2 * Real.pi * t) = P.eval t := by
  rw [rescalePolynomialToSpectralMomentum, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem hasTemperateGrowth_ofReal
    {f : ℝ → ℝ} (hf : Function.HasTemperateGrowth f) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x : ℂ)) := by
  have h := Complex.ofRealCLM.hasTemperateGrowth.comp hf
  rw [show Complex.ofRealCLM ∘ f = (fun x : ℝ => (f x : ℂ)) by
    funext x
    exact Complex.ofRealCLM_apply (f x)] at h
  exact h

theorem polynomialCoordinateCLM_eq_polynomialSpectralMomentumCLM
    (P : ℝ[X]) :
    SchwartzMap.smulLeftCLM ℂ (fun t => ((P.eval t : ℝ) : ℂ)) =
      polynomialSpectralMomentumCLM (rescalePolynomialToSpectralMomentum P) := by
  ext f t
  have htemp : Function.HasTemperateGrowth (fun x : ℝ => ((P.eval x : ℝ) : ℂ)) := by
    exact hasTemperateGrowth_ofReal (polynomial_eval_hasTemperateGrowth P)
  rw [SchwartzMap.smulLeftCLM_apply_apply htemp,
    polynomialSpectralMomentumCLM_apply,
    eval_rescalePolynomialToSpectralMomentum]
  simp

theorem ContinuousSchwartzSesquilinearForm.fourierPullback_polynomialCoordinate_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (P : ℝ[X]) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback
        (SchwartzMap.smulLeftCLM ℂ (fun t => ((P.eval t : ℝ) : ℂ)) f) g =
      Q.fourierPullback f
        (SchwartzMap.smulLeftCLM ℂ (fun t => ((P.eval t : ℝ) : ℂ)) g) := by
  rw [polynomialCoordinateCLM_eq_polynomialSpectralMomentumCLM]
  exact Q.fourierPullback_polynomialSpectralMomentum_symmetric hQ
    (rescalePolynomialToSpectralMomentum P) f g

/-- Every smooth temperate real multiplier is symmetric on compact spectral packets. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_realSmoothMultiplier_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (a : ℝ → ℝ) (ha : Function.HasTemperateGrowth a)
    {T : ℝ} (hT : 0 ≤ T) (f g : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ T})
    (hg : tsupport g ⊆ {t : ℝ | |t| ≤ T}) :
    Q.fourierPullback
        (SchwartzMap.smulLeftCLM ℂ (fun t => (a t : ℂ)) f) g =
      Q.fourierPullback f
        (SchwartzMap.smulLeftCLM ℂ (fun t => (a t : ℂ)) g) := by
  obtain ⟨P, hP⟩ :=
    Polynomial.exists_polynomial_sequence_eventually_near_all_iteratedDeriv
      ha.1 (show -T ≤ T by linarith)
  let A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun t => (a t : ℂ))
  let AP : ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ := fun n =>
    SchwartzMap.smulLeftCLM ℂ (fun t => (((P n).eval t : ℝ) : ℂ))
  let E : ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ := fun n =>
    SchwartzMap.smulLeftCLM ℂ (fun t => ((P n).eval t - a t : ℂ))
  have hef : Tendsto (fun n => E n f) atTop (nhds 0) :=
    tendsto_polynomial_multiplier_error_mul_schwartz_zero ha P hT hP f hf
  have heg : Tendsto (fun n => E n g) atTop (nhds 0) :=
    tendsto_polynomial_multiplier_error_mul_schwartz_zero ha P hT hP g hg
  have hdecompF (n : ℕ) : AP n f = E n f + A f := by
    ext t
    have hpC : Function.HasTemperateGrowth
        (fun x : ℝ => (((P n).eval x : ℝ) : ℂ)) := by
      exact hasTemperateGrowth_ofReal (polynomial_eval_hasTemperateGrowth (P n))
    have heC : Function.HasTemperateGrowth
        (fun x : ℝ => (((P n).eval x : ℝ) : ℂ) - (a x : ℂ)) := hpC.sub
      (hasTemperateGrowth_ofReal ha)
    have haC : Function.HasTemperateGrowth (fun x : ℝ => (a x : ℂ)) := by
      exact hasTemperateGrowth_ofReal ha
    change (AP n f) t = (E n f) t + (A f) t
    rw [show (AP n f) t = (((P n).eval t : ℝ) : ℂ) * f t by
        exact SchwartzMap.smulLeftCLM_apply_apply hpC f t,
      show (E n f) t = ((((P n).eval t : ℝ) : ℂ) - (a t : ℂ)) * f t by
        exact SchwartzMap.smulLeftCLM_apply_apply heC f t,
      show (A f) t = (a t : ℂ) * f t by
        exact SchwartzMap.smulLeftCLM_apply_apply haC f t]
    ring
  have hdecompG (n : ℕ) : AP n g = E n g + A g := by
    ext t
    have hpC : Function.HasTemperateGrowth
        (fun x : ℝ => (((P n).eval x : ℝ) : ℂ)) := by
      exact hasTemperateGrowth_ofReal (polynomial_eval_hasTemperateGrowth (P n))
    have heC : Function.HasTemperateGrowth
        (fun x : ℝ => (((P n).eval x : ℝ) : ℂ) - (a x : ℂ)) := hpC.sub
      (hasTemperateGrowth_ofReal ha)
    have haC : Function.HasTemperateGrowth (fun x : ℝ => (a x : ℂ)) := by
      exact hasTemperateGrowth_ofReal ha
    change (AP n g) t = (E n g) t + (A g) t
    rw [show (AP n g) t = (((P n).eval t : ℝ) : ℂ) * g t by
        exact SchwartzMap.smulLeftCLM_apply_apply hpC g t,
      show (E n g) t = ((((P n).eval t : ℝ) : ℂ) - (a t : ℂ)) * g t by
        exact SchwartzMap.smulLeftCLM_apply_apply heC g t,
      show (A g) t = (a t : ℂ) * g t by
        exact SchwartzMap.smulLeftCLM_apply_apply haC g t]
    ring
  have hPf : Tendsto (fun n => AP n f) atTop (nhds (A f)) := by
    have hconst : Tendsto (fun _n : ℕ => A f) atTop (nhds (A f)) := tendsto_const_nhds
    simpa only [hdecompF, zero_add] using hef.add hconst
  have hPg : Tendsto (fun n => AP n g) atTop (nhds (A g)) := by
    have hconst : Tendsto (fun _n : ℕ => A g) atTop (nhds (A g)) := tendsto_const_nhds
    simpa only [hdecompG, zero_add] using heg.add hconst
  have hgconst : Tendsto (fun _n : ℕ => g) atTop (nhds g) := tendsto_const_nhds
  have hfconst : Tendsto (fun _n : ℕ => f) atTop (nhds f) := tendsto_const_nhds
  have hleft := Q.fourierPullback.tendsto_apply hPf hgconst
  have hright := Q.fourierPullback.tendsto_apply hfconst hPg
  have heq : (fun n => Q.fourierPullback (AP n f) g) =
      fun n => Q.fourierPullback f (AP n g) := by
    funext n
    exact Q.fourierPullback_polynomialCoordinate_symmetric hQ (P n) f g
  rw [heq] at hleft
  simpa [A] using tendsto_nhds_unique hleft hright

/-- Complex adjoint law for every smooth temperate multiplier on compact spectral packets. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_complexSmoothMultiplier_adjoint
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (a : ℝ → ℂ) (ha : Function.HasTemperateGrowth a)
    {T : ℝ} (hT : 0 ≤ T) (f g : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ T})
    (hg : tsupport g ⊆ {t : ℝ | |t| ≤ T}) :
    Q.fourierPullback (SchwartzMap.smulLeftCLM ℂ a f) g =
      Q.fourierPullback f
        (SchwartzMap.smulLeftCLM ℂ (fun t => (starRingEnd ℂ) (a t)) g) := by
  let ar : ℝ → ℝ := fun t => (a t).re
  let ai : ℝ → ℝ := fun t => (a t).im
  let Ar : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun t => (ar t : ℂ))
  let Ai : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun t => (ai t : ℂ))
  have har : Function.HasTemperateGrowth ar := Complex.reCLM.hasTemperateGrowth.comp ha
  have hai : Function.HasTemperateGrowth ai := Complex.imCLM.hasTemperateGrowth.comp ha
  have hre := Q.fourierPullback_realSmoothMultiplier_symmetric hQ ar har hT f g hf hg
  have him := Q.fourierPullback_realSmoothMultiplier_symmetric hQ ai hai hT f g hf hg
  change Q.fourierPullback (Ar f) g = Q.fourierPullback f (Ar g) at hre
  change Q.fourierPullback (Ai f) g = Q.fourierPullback f (Ai g) at him
  have hleft : SchwartzMap.smulLeftCLM ℂ a f = Ar f + I • Ai f := by
    ext t
    have harC : Function.HasTemperateGrowth (fun x : ℝ => (ar x : ℂ)) := by
      exact hasTemperateGrowth_ofReal har
    have haiC : Function.HasTemperateGrowth (fun x : ℝ => (ai x : ℂ)) := by
      exact hasTemperateGrowth_ofReal hai
    rw [SchwartzMap.smulLeftCLM_apply_apply ha]
    simp only [smul_eq_mul]
    change a t * f t = (Ar f) t + I * (Ai f) t
    rw [show (Ar f) t = (ar t : ℂ) * f t by
        exact SchwartzMap.smulLeftCLM_apply_apply harC f t,
      show (Ai f) t = (ai t : ℂ) * f t by
        exact SchwartzMap.smulLeftCLM_apply_apply haiC f t]
    rw [show a t = (ar t : ℂ) + I * (ai t : ℂ) by
      apply Complex.ext <;> simp [ar, ai]]
    ring
  have hconj : Function.HasTemperateGrowth (fun t => (starRingEnd ℂ) (a t)) := by
    have hreC : Function.HasTemperateGrowth (fun t => (ar t : ℂ)) :=
      hasTemperateGrowth_ofReal har
    have himC : Function.HasTemperateGrowth (fun t => (-I) * (ai t : ℂ)) :=
      (Function.HasTemperateGrowth.const (-I)).mul
        (hasTemperateGrowth_ofReal hai)
    have hadd := hreC.add himC
    convert hadd using 1
    funext t
    apply Complex.ext <;> simp [ar, ai]
  have hright :
      SchwartzMap.smulLeftCLM ℂ (fun t => (starRingEnd ℂ) (a t)) g =
        Ar g + (-I) • Ai g := by
    ext t
    have harC : Function.HasTemperateGrowth (fun x : ℝ => (ar x : ℂ)) := by
      exact hasTemperateGrowth_ofReal har
    have haiC : Function.HasTemperateGrowth (fun x : ℝ => (ai x : ℂ)) := by
      exact hasTemperateGrowth_ofReal hai
    rw [SchwartzMap.smulLeftCLM_apply_apply hconj]
    simp only [smul_eq_mul]
    change (starRingEnd ℂ) (a t) * g t = (Ar g) t + (-I) * (Ai g) t
    rw [show (Ar g) t = (ar t : ℂ) * g t by
        exact SchwartzMap.smulLeftCLM_apply_apply harC g t,
      show (Ai g) t = (ai t : ℂ) * g t by
        exact SchwartzMap.smulLeftCLM_apply_apply haiC g t]
    rw [show (starRingEnd ℂ) (a t) = (ar t : ℂ) - I * (ai t : ℂ) by
      apply Complex.ext <;> simp [ar, ai]]
    ring
  rw [hleft, hright, Q.fourierPullback.apply_add_left,
    Q.fourierPullback.apply_smul_left, Q.fourierPullback.apply_add_right,
    Q.fourierPullback.apply_smul_right, hre, him]
  simp

/-- **Diagonal product factorization.**  On compact spectral packets, a momentum-symmetric form
depends on `f` and `g` only through `f * conj g`: a compactly supported cutoff equal to one on the
support of `g` recovers the pairing exactly. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_eq_product_cutoff
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    {T : ℝ} (hT : 0 ≤ T) (f g χ : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ T})
    (hχsupp : tsupport χ ⊆ {t : ℝ | |t| ≤ T})
    (hχ : ∀ t ∈ tsupport g, χ t = 1) :
    Q.fourierPullback f g = Q.fourierPullback (pointwiseMulConj f g) χ := by
  let a : ℝ → ℂ := fun t => (starRingEnd ℂ) (g t)
  have ha : Function.HasTemperateGrowth a := by
    have hgrowth := (conjSLM g).hasTemperateGrowth
    rw [show (conjSLM g : ℝ → ℂ) = a by
      funext t
      simp [a]] at hgrowth
    exact hgrowth
  have hadj := Q.fourierPullback_complexSmoothMultiplier_adjoint
    hQ a ha hT f χ hf hχsupp
  have hleft : SchwartzMap.smulLeftCLM ℂ a f = pointwiseMulConj f g := by
    ext t
    rw [SchwartzMap.smulLeftCLM_apply_apply ha]
    change (starRingEnd ℂ) (g t) * f t = f t * (starRingEnd ℂ) (g t)
    ring
  have hdouble : Function.HasTemperateGrowth
      (fun t => (starRingEnd ℂ) (a t)) := by
    convert g.hasTemperateGrowth using 1
    funext t
    simp [a]
  have hright :
      SchwartzMap.smulLeftCLM ℂ (fun t => (starRingEnd ℂ) (a t)) χ = g := by
    ext t
    rw [SchwartzMap.smulLeftCLM_apply_apply hdouble]
    by_cases ht : t ∈ tsupport g
    · rw [hχ t ht]
      simp [a]
    · have hgt : g t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [a, hgt]
  rw [hleft, hright] at hadj
  exact hadj.symm

/-- A canonical smooth spectral cutoff equal to one on `[-|R|, |R|]` and supported in
`[-(|R| + 2), |R| + 2]`. -/
def compactIntervalCutoff (R : ℝ) : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  exact (b.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

@[simp] theorem compactIntervalCutoff_apply_of_abs_le
    (R : ℝ) {t : ℝ} (ht : |t| ≤ |R|) :
    compactIntervalCutoff R t = 1 := by
  rw [compactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  change (b t : ℂ) = 1
  have hmem : t ∈ Metric.closedBall (0 : ℝ) b.rIn := by
    rw [Metric.mem_closedBall]
    change dist t 0 ≤ |R| + 1
    rw [Real.dist_0_eq_abs]
    linarith
  exact_mod_cast b.one_of_mem_closedBall hmem

@[simp] theorem compactIntervalCutoff_tsupport (R : ℝ) :
    tsupport (compactIntervalCutoff R) = {t : ℝ | |t| ≤ |R| + 2} := by
  rw [compactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  change tsupport (fun t : ℝ => ((b t : ℝ) : ℂ)) = _
  have hsupp : Function.support (fun t : ℝ => ((b t : ℝ) : ℂ)) =
      Function.support b := by
    ext t
    simp only [Function.mem_support]
    norm_cast
  rw [tsupport, hsupp, ← tsupport, b.tsupport_eq]
  ext t
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    Set.mem_setOf_eq]
  rfl

/-- Canonical compact-packet diagonal factorization, with no externally supplied cutoff. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_eq_product_compactIntervalCutoff
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (f g : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧
      Q.fourierPullback f g =
        Q.fourierPullback (pointwiseMulConj f g) (compactIntervalCutoff R) := by
  have hcompact : IsCompact (tsupport f ∪ tsupport g) := hf.union hg
  obtain ⟨B, hB⟩ := hcompact.isBounded.exists_norm_le
  let R : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right B 0
  have hbound : ∀ t ∈ tsupport f ∪ tsupport g, |t| ≤ R := by
    intro t ht
    have hnorm : ‖t‖ ≤ B := hB t ht
    simpa only [Real.norm_eq_abs] using hnorm.trans (le_max_left B 0)
  refine ⟨R, hR, ?_⟩
  apply Q.fourierPullback_eq_product_cutoff hQ (T := R + 2) (by linarith)
  · intro t ht
    exact (hbound t (Or.inl ht)).trans (by linarith)
  · rw [compactIntervalCutoff_tsupport]
    intro t ht
    change |t| ≤ R + 2
    simpa [abs_of_nonneg hR] using ht
  · intro t ht
    apply compactIntervalCutoff_apply_of_abs_le
    simpa [abs_of_nonneg hR] using hbound t (Or.inr ht)

end SchwartzMap
