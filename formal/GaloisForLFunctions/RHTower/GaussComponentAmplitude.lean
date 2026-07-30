import GaloisForLFunctions.RHTower.GaussComponentPhaseResidue
import GaloisForLFunctions.HTGeometry.GaussComponentHaarAverage

/-!
# The Gauss moving-amplitude observable
-/

namespace RHTower

open Filter Topology MeasureTheory intervalIntegral

noncomputable section

/-- Explicit representative of the translated prime-scale amplitude on one period. -/
def gaussAmplitudeSegment (p : ℝ) (m : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) * Real.exp (((m : ℝ) * Real.log p) * δ) +
    δ * Real.exp (((m : ℝ) * Real.log p) * (δ - 1))

lemma gaussAmplitudeSegment_zero (p : ℝ) (m : ℕ) :
    gaussAmplitudeSegment p m 0 = 1 := by
  simp [gaussAmplitudeSegment]

lemma gaussAmplitudeSegment_one (p : ℝ) (m : ℕ) :
    gaussAmplitudeSegment p m 1 = 1 := by
  simp [gaussAmplitudeSegment]

lemma continuous_gaussAmplitudeSegment (p : ℝ) (m : ℕ) :
    Continuous (gaussAmplitudeSegment p m) := by
  unfold gaussAmplitudeSegment
  fun_prop

/-- The continuous one-periodic Gauss amplitude on the additive circle. -/
def gaussAmplitudeCircle (p : ℝ) (m : ℕ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨AddCircle.liftIoc 1 0 (gaussAmplitudeSegment p m),
    AddCircle.liftIoc_zero_continuous
      (by simp [gaussAmplitudeSegment])
      (continuous_gaussAmplitudeSegment p m).continuousOn⟩

/-- Complex-valued version used by harmonic logarithmic equidistribution. -/
def gaussAmplitudeCircleComplex (p : ℝ) (m : ℕ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun x => (gaussAmplitudeCircle p m x : ℂ),
    Complex.continuous_ofReal.comp (gaussAmplitudeCircle p m).continuous⟩

lemma gaussAmplitudeCircleComplex_apply (p : ℝ) (m : ℕ) (x : AddCircle (1 : ℝ)) :
    gaussAmplitudeCircleComplex p m x = (gaussAmplitudeCircle p m x : ℂ) :=
  rfl

theorem intervalIntegral_gaussAmplitudeSegment
    (p : ℝ) (hp : 1 < p) (m : ℕ) (hm : 1 ≤ m) :
    ∫ δ in (0 : ℝ)..1, gaussAmplitudeSegment p m δ =
      (p ^ m - 1) ^ 2 / (p ^ m * (m : ℝ) ^ 2 * (Real.log p) ^ 2) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  let c : ℝ := (m : ℝ) * Real.log p
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos hmR (Real.log_pos hp)
  let F : ℝ → ℝ := fun x =>
    Real.exp (c * x) * ((1 - x) / c + 1 / c ^ 2) +
      Real.exp (c * (x - 1)) * (x / c - 1 / c ^ 2)
  have hseg : ∀ x : ℝ,
      gaussAmplitudeSegment p m x =
        (1 - x) * Real.exp (c * x) + x * Real.exp (c * (x - 1)) := by
    intro x
    rfl
  have hF : ∀ x : ℝ, HasDerivAt F (gaussAmplitudeSegment p m x) x := by
    intro x
    rw [hseg]
    dsimp [F]
    have hcx : HasDerivAt (fun y : ℝ => c * y) c x := by
      convert! (hasDerivAt_id x).const_mul c using 1
      ring
    have hcx1 : HasDerivAt (fun y : ℝ => c * (y - 1)) c x := by
      convert! ((hasDerivAt_id x).sub_const 1).const_mul c using 1
      ring
    have hlin1 : HasDerivAt (fun y : ℝ => (1 - y) / c + 1 / c ^ 2) (-1 / c) x := by
      convert! (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).div_const c).add_const
        (1 / c ^ 2) using 1
      ring
    have hlin2 : HasDerivAt (fun y : ℝ => y / c - 1 / c ^ 2) (1 / c) x := by
      convert! (((hasDerivAt_id x).div_const c).sub_const (1 / c ^ 2)) using 1
    convert! ((hcx.exp.mul hlin1).add (hcx1.exp.mul hlin2)) using 1
    field_simp [hc.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hF x) ((continuous_gaussAmplitudeSegment p m).intervalIntegrable 0 1)]
  dsimp [F]
  have hec : Real.exp c = p ^ m := by
    dsimp [c]
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have hecn : Real.exp (-c) = (p ^ m : ℝ)⁻¹ := by
    rw [Real.exp_neg, hec]
  have hpm : (p ^ m : ℝ) ≠ 0 := (pow_pos hp0 m).ne'
  norm_num only [mul_one, mul_zero, sub_self, Real.exp_zero, one_mul, sub_zero,
    zero_div, zero_sub, mul_neg, mul_neg_one]
  rw [hec, hecn]
  have hcne : c ≠ 0 := hc.ne'
  dsimp [c] at hcne ⊢
  field_simp [hcne, hpm]
  ring

/-- Haar mean of the continuous Gauss moving-amplitude observable. -/
theorem integral_gaussAmplitudeCircle
    (p : ℝ) (hp : 1 < p) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, gaussAmplitudeCircle p m x ∂GaloisForLFunctions.unitCircleHaar =
      (p ^ m - 1) ^ 2 / (p ^ m * (m : ℝ) ^ 2 * (Real.log p) ^ 2) := by
  change ∫ x, AddCircle.liftIoc 1 0 (gaussAmplitudeSegment p m) x
      ∂AddCircle.haarAddCircle = _
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  simpa only [zero_add] using intervalIntegral_gaussAmplitudeSegment p hp m hm

/-- Complex form of the exact Haar mean. -/
theorem integral_gaussAmplitudeCircleComplex
    (p : ℝ) (hp : 1 < p) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, gaussAmplitudeCircleComplex p m x
        ∂GaloisForLFunctions.unitCircleHaar =
      (((p ^ m - 1) ^ 2 / (p ^ m * (m : ℝ) ^ 2 * (Real.log p) ^ 2) : ℝ) : ℂ) := by
  rw [show (∫ x, gaussAmplitudeCircleComplex p m x
        ∂GaloisForLFunctions.unitCircleHaar) =
      ((∫ x, gaussAmplitudeCircle p m x
        ∂GaloisForLFunctions.unitCircleHaar : ℝ) : ℂ) by
    simpa only [gaussAmplitudeCircleComplex_apply] using
      (integral_complex_ofReal
        (μ := GaloisForLFunctions.unitCircleHaar)
        (f := fun x => gaussAmplitudeCircle p m x)
        )]
  rw [integral_gaussAmplitudeCircle p hp m hm]

/-- The doubled principal Fourier-diagonal model for `G^m`. -/
def gaussPrincipalDiagonalTerm {m : ℕ} (k : Fin m) (p : Nat.Primes) (n : ℕ) : ℂ :=
  (2 * ((p : ℝ) ^ m) : ℂ) *
    gaussComponentPrimeMagnitudeEnergy k p n *
      gaussAmplitudeCircleComplex (p : ℝ) m (gaussComponentPhasePoint m p n)

/-- Exact logarithmic mean of the two-sided principal Fourier diagonal. -/
theorem gaussPrincipalDiagonalTerm_logResidue
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gaussPrincipalDiagonalTerm k p n) /
        (Real.log N : ℂ)) atTop
      (nhds ((2 * ((p : ℝ) ^ m - 1) ^ 2 /
        ((m : ℝ) ^ 2 * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hbase := gaussComponentPrimeMagnitudeEnergy_phase_logResidue hm k p
    (gaussAmplitudeCircleComplex (p : ℝ) m)
  have hscaled := hbase.const_mul (2 * ((p : ℝ) ^ m) : ℂ)
  rw [integral_gaussAmplitudeCircleComplex (p : ℝ) hp m hm] at hscaled
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  have hpow : ((p : ℝ) ^ m) ≠ 0 := by positivity
  have hscalar :
      (2 * ((p : ℝ) ^ m)) *
          (Real.log (p : ℝ) *
            (((p : ℝ) ^ m - 1) ^ 2 /
              ((p : ℝ) ^ m * (m : ℝ) ^ 2 * Real.log (p : ℝ) ^ 2))) =
        2 * ((p : ℝ) ^ m - 1) ^ 2 /
          ((m : ℝ) ^ 2 * Real.log (p : ℝ)) := by
    field_simp [hlog, hpow]
  have hscalarC :
      (2 * ((p : ℝ) ^ m) : ℂ) *
          ((Real.log (p : ℝ) : ℂ) *
            ((((p : ℝ) ^ m - 1) ^ 2 /
              ((p : ℝ) ^ m * (m : ℝ) ^ 2 * Real.log (p : ℝ) ^ 2) : ℝ) : ℂ)) =
        ((2 * ((p : ℝ) ^ m - 1) ^ 2 /
          ((m : ℝ) ^ 2 * Real.log (p : ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast hscalar
  rw [hscalarC] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with N
  change
    (2 * ((p : ℝ) ^ m) : ℂ) *
        ((∑ n ∈ Finset.range N,
            (gaussComponentPrimeMagnitudeEnergy k p n : ℂ) *
              gaussAmplitudeCircleComplex (p : ℝ) m (gaussComponentPhasePoint m p n)) /
          (Real.log N : ℂ)) =
      (∑ n ∈ Finset.range N,
          (2 * ((p : ℝ) ^ m) : ℂ) *
            (gaussComponentPrimeMagnitudeEnergy k p n : ℂ) *
              gaussAmplitudeCircleComplex (p : ℝ) m (gaussComponentPhasePoint m p n)) /
        (Real.log N : ℂ)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_assoc, mul_div_assoc]

end

end RHTower
