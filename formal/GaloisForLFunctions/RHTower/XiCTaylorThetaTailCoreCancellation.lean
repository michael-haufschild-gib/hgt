import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCorrelation

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def thetaCuspTailSecondSectionSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
      ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial)

def thetaCuspTailSecondSectionSourceSecondDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
      ((2 * k + 1 : ℕ) : ℂ) *
        ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial)

theorem hasDerivAt_thetaCuspTailSecondSection_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondSection d z t)
      (thetaCuspTailSecondSectionSourceDerivative d z x) x := by
  unfold thetaCuspTailSecondSection
    thetaCuspTailSecondSectionSourceDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) *
        ((t : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt
      have hpow := hbase.pow (2 * k + 2)
      have hscaled :=
        (HasDerivAt.const_mul ((-1 : ℂ) ^ k * z ^ (2 * k)) hpow).mul_const
          (((2 * k + 2).factorial : ℂ)⁻¹)
      have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      convert hscaled using 1
      · funext y
        simp only [Pi.pow_apply, div_eq_mul_inv]
        ring
      · rw [hsub]
        simp only [div_eq_mul_inv]
        ring)
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

theorem hasDerivAt_thetaCuspTailSecondSectionSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      thetaCuspTailSecondSectionSourceDerivative d z t)
      (thetaCuspTailSecondSectionSourceSecondDerivative d z x) x := by
  unfold thetaCuspTailSecondSectionSourceDerivative
    thetaCuspTailSecondSectionSourceSecondDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((t : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (A' := fun (k : ℕ) =>
      (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
        ((2 * k + 1 : ℕ) : ℂ) *
          ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt
      have hpow := hbase.pow (2 * k + 1)
      have hscaled :=
        (HasDerivAt.const_mul
          ((-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ)) hpow).mul_const
            (((2 * k + 2).factorial : ℂ)⁻¹)
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      convert hscaled using 1
      · funext y
        simp only [Pi.pow_apply, div_eq_mul_inv]
        ring
      · rw [hsub]
        simp only [div_eq_mul_inv]
        ring)
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

theorem thetaCuspTailSecondSectionSourceSecondDerivative_eq_truncatedCosine
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSectionSourceSecondDerivative d z x =
      truncatedCosineSection d z x := by
  unfold thetaCuspTailSecondSectionSourceSecondDerivative
    truncatedCosineSection
  apply Finset.sum_congr rfl
  intro k _
  have hfac : (2 * k + 2).factorial =
      (2 * k).factorial * (2 * k + 1) * (2 * k + 2) := by
    calc
      (2 * k + 2).factorial = (2 * k + 1).factorial * (2 * k + 2) := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]
        ring
      _ = ((2 * k).factorial * (2 * k + 1)) * (2 * k + 2) := by
        rw [Nat.factorial_succ]
        ring
  have hratio :
      (((2 * k + 2 : ℕ) : ℂ) * ((2 * k + 1 : ℕ) : ℂ)) /
          (((2 * k + 2).factorial : ℕ) : ℂ) =
        1 / (((2 * k).factorial : ℕ) : ℂ) := by
    rw [hfac]
    push_cast
    have hfac0 : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k)
    have hodd : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : 2 * k + 1 ≠ 0)
    have heven : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : 2 * k + 2 ≠ 0)
    have hodd' : 2 * (k : ℂ) + 1 ≠ 0 := by
      rw [show 2 * (k : ℂ) + 1 = ((2 * k + 1 : ℕ) : ℂ) by
        push_cast
        ring]
      exact hodd
    field_simp [hfac0, hodd, heven, hodd']
  rw [mul_pow]
  calc
    (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
          ((2 * k + 1 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k) / (2 * k + 2).factorial) =
        (-1 : ℂ) ^ k * z ^ (2 * k) * (x : ℂ) ^ (2 * k) *
          ((((2 * k + 2 : ℕ) : ℂ) * ((2 * k + 1 : ℕ) : ℂ)) /
            (((2 * k + 2).factorial : ℕ) : ℂ)) := by
      push_cast
      ring
    _ = (-1 : ℂ) ^ k * z ^ (2 * k) * (x : ℂ) ^ (2 * k) *
          (1 / (((2 * k).factorial : ℕ) : ℂ)) := by rw [hratio]
    _ = (-1 : ℂ) ^ k * (z ^ (2 * k) * (x : ℂ) ^ (2 * k)) /
          (2 * k).factorial := by
      push_cast
      ring

def thetaCuspTailSecondCoreAtomSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  -(z ^ 2 + 1 / 4) *
    thetaCuspTailSecondSectionSourceDerivative d z x

theorem hasDerivAt_thetaCuspTailSecondCoreAtom_source
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspTailSecondCoreAtom d z t)
      (thetaCuspTailSecondCoreAtomSourceDerivative d z x) x := by
  unfold thetaCuspTailSecondCoreAtom
    thetaCuspTailSecondCoreAtomSourceDerivative
  convert (hasDerivAt_const x (1 : ℂ)).sub
    ((hasDerivAt_thetaCuspTailSecondSection_source d z x).const_mul
      (z ^ 2 + 1 / 4)) using 1 <;> ring

theorem hasDerivAt_thetaCuspTailSecondCoreAtomSourceDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      thetaCuspTailSecondCoreAtomSourceDerivative d z t)
      (-(z ^ 2 + 1 / 4) * truncatedCosineSection d z x) x := by
  unfold thetaCuspTailSecondCoreAtomSourceDerivative
  have h := (hasDerivAt_thetaCuspTailSecondSectionSourceDerivative d z x).const_mul
    (-(z ^ 2 + 1 / 4))
  rw [thetaCuspTailSecondSectionSourceSecondDerivative_eq_truncatedCosine] at h
  exact h

theorem thetaCuspTailSecondCoreAtom_sourceSecondDerivative
    (d : ℕ) (z : ℂ) (x : ℝ) :
    deriv (fun t : ℝ => deriv
      (fun u : ℝ => thetaCuspTailSecondCoreAtom d z u) t) x =
      -(z ^ 2 + 1 / 4) * truncatedCosineSection d z x := by
  have hfirst : deriv (fun u : ℝ => thetaCuspTailSecondCoreAtom d z u) =
      fun t : ℝ => thetaCuspTailSecondCoreAtomSourceDerivative d z t := by
    funext t
    exact (hasDerivAt_thetaCuspTailSecondCoreAtom_source d z t).deriv
  rw [hfirst]
  exact (hasDerivAt_thetaCuspTailSecondCoreAtomSourceDerivative d z x).deriv

/-- The exact one-source integration-by-parts identity, including its boundary seam.  It is
stated at the finite-section level and follows by comparing the two already proved canonical
representations of the same core polynomial. -/
theorem integral_thetaCuspTailSecondDensity_mul_coreAtom_eq_seam_sub_tail
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      1 - 4 * (z ^ 2 + 1 / 4) *
        ∫ x : ℝ in Ioi 0,
          (thetaCuspTailDerivative 0 x : ℂ) *
            truncatedCosineSection d z x := by
  have hrho := xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral d z
  have htail := xiCTaylorThetaTailCorePolynomial_eval_eq_integral d z
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
        2 * (xiCTaylorThetaTailCorePolynomial d).eval z := by
          rw [hrho]
          ring
    _ = 2 * (1 / 2 - (z ^ 2 + 1 / 4) *
          (2 * ∫ x : ℝ in Ioi 0,
            (thetaCuspTailDerivative 0 x : ℂ) *
              truncatedCosineSection d z x)) := by rw [htail]
    _ = 1 - 4 * (z ^ 2 + 1 / 4) *
          ∫ x : ℝ in Ioi 0,
            (thetaCuspTailDerivative 0 x : ℂ) *
              truncatedCosineSection d z x := by ring

end
end RHTower
