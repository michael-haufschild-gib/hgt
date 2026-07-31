import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

theorem thetaCuspTailSecondSection_euler
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (x : ℂ) * thetaCuspTailSecondSectionSourceDerivative d z x =
      z * thetaCuspTailSecondSectionDerivative d z x +
        2 * thetaCuspTailSecondSection d z x := by
  unfold thetaCuspTailSecondSectionSourceDerivative
    thetaCuspTailSecondSectionDerivative thetaCuspTailSecondSection
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  cases k with
  | zero =>
      push_cast
      ring
  | succ k =>
      have hpow : z * z ^ (2 * (k + 1) - 1) = z ^ (2 * (k + 1)) := by
        simpa [mul_comm] using mul_pow_sub_one (by omega : 2 * (k + 1) ≠ 0) z
      have hxpow : (x : ℂ) * (x : ℂ) ^ (2 * (k + 1) + 1) =
          (x : ℂ) ^ (2 * (k + 1) + 2) := by
        rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by omega, pow_succ]
        ring
      push_cast
      field_simp
      rw [show (x : ℂ) * z ^ (2 * (k + 1)) * (↑k + 1 + 1) *
          (x : ℂ) ^ (2 * (k + 1) + 1) =
          (↑k + 2) * z ^ (2 * (k + 1)) *
            ((x : ℂ) * (x : ℂ) ^ (2 * (k + 1) + 1)) by ring,
        hxpow]
      rw [show (↑k + 1) * z * z ^ (2 * (k + 1) - 1) =
          (↑k + 1) * (z * z ^ (2 * (k + 1) - 1)) by ring, hpow]
      ring

theorem thetaCuspTailSecondCoreAtom_euler
    (d : ℕ) (z : ℂ) (x : ℝ) :
    z * thetaCuspTailSecondCoreAtomDerivative d z x =
      (x : ℂ) * thetaCuspTailSecondCoreAtomSourceDerivative d z x +
        (1 / 2 : ℂ) * thetaCuspTailSecondSection d z x := by
  rw [thetaCuspTailSecondCoreAtomDerivative,
    thetaCuspTailSecondCoreAtomSourceDerivative]
  have heuler := thetaCuspTailSecondSection_euler d z x
  rw [show (x : ℂ) *
      (-(z ^ 2 + 1 / 4) * thetaCuspTailSecondSectionSourceDerivative d z x) =
      -(z ^ 2 + 1 / 4) *
        ((x : ℂ) * thetaCuspTailSecondSectionSourceDerivative d z x) by ring]
  rw [heuler]
  ring

def thetaCuspTailSecondDensityDerivative (x : ℝ) : ℝ :=
  4 * thetaCuspTailDerivative 3 x

theorem hasDerivAt_thetaCuspTailSecondDensity (x : ℝ) :
    HasDerivAt thetaCuspTailSecondDensity
      (thetaCuspTailSecondDensityDerivative x) x := by
  unfold thetaCuspTailSecondDensity thetaCuspTailSecondDensityDerivative
  simpa using (hasDerivAt_thetaCuspTailDerivative 2 x).const_mul 4

def thetaCuspTailSecondScoreDensity (x : ℝ) : ℝ :=
  thetaCuspTailSecondDensity x +
    x * thetaCuspTailSecondDensityDerivative x

theorem integrableOn_thetaCuspTailSecondDensityDerivative_mul_id :
    IntegrableOn (fun x : ℝ =>
      x * thetaCuspTailSecondDensityDerivative x) (Ioi 0) := by
  unfold thetaCuspTailSecondDensityDerivative
  simpa only [pow_one, mul_assoc, mul_left_comm, mul_comm] using!
    (integrableOn_pow_mul_thetaCuspTailDerivative 1 3).const_mul 4

theorem integral_Ioi_thetaCuspTailSecondDensityDerivative_mul_id :
    (∫ x : ℝ in Ioi 0, x * thetaCuspTailSecondDensityDerivative x) = -1 := by
  have hzero : Tendsto
      (fun x : ℝ => x * thetaCuspTailSecondDensity x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    unfold thetaCuspTailSecondDensity
    convert (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos
      (k := 1) (by omega) 2).const_mul 4 using 1 <;>
      simp [pow_one, mul_left_comm, mul_comm]
  have htop : Tendsto
      (fun x : ℝ => x * thetaCuspTailSecondDensity x)
      atTop (nhds 0) := by
    unfold thetaCuspTailSecondDensity
    convert (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero 1 2).const_mul 4
      using 1 <;> simp [pow_one, mul_left_comm, mul_comm]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x)
    (u' := fun _ : ℝ => 1)
    (v := thetaCuspTailSecondDensity)
    (v' := thetaCuspTailSecondDensityDerivative)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => hasDerivAt_thetaCuspTailSecondDensity x)
    integrableOn_thetaCuspTailSecondDensityDerivative_mul_id
    (by
      have hrho : IntegrableOn thetaCuspTailSecondDensity (Ioi 0) := by
        simpa only [pow_zero, one_mul] using
          integrableOn_pow_mul_thetaCuspTailSecondDensity 0
      rw [show ((fun _ : ℝ => (1 : ℝ)) * thetaCuspTailSecondDensity) =
          thetaCuspTailSecondDensity by funext x; simp]
      exact hrho)
    hzero htop
  rw [show (fun x : ℝ => (1 : ℝ) * thetaCuspTailSecondDensity x) =
      thetaCuspTailSecondDensity by funext x; simp] at hibp
  rw [integral_thetaCuspTailSecondDensity] at hibp
  linarith

theorem integrableOn_thetaCuspTailSecondScoreDensity :
    IntegrableOn thetaCuspTailSecondScoreDensity (Ioi 0) := by
  unfold thetaCuspTailSecondScoreDensity
  have hrho : IntegrableOn thetaCuspTailSecondDensity (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 0
  exact hrho.add integrableOn_thetaCuspTailSecondDensityDerivative_mul_id

theorem integral_Ioi_thetaCuspTailSecondScoreDensity :
    (∫ x : ℝ in Ioi 0, thetaCuspTailSecondScoreDensity x) = 0 := by
  unfold thetaCuspTailSecondScoreDensity
  have hrho : IntegrableOn thetaCuspTailSecondDensity (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 0
  rw [integral_add
    hrho
    integrableOn_thetaCuspTailSecondDensityDerivative_mul_id,
    integral_thetaCuspTailSecondDensity,
    integral_Ioi_thetaCuspTailSecondDensityDerivative_mul_id]
  ring

theorem integrableOn_pow_mul_thetaCuspTailDerivative_complex_mul_section
    (q m d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      ((x ^ q * thetaCuspTailDerivative m x : ℝ) : ℂ) *
        thetaCuspTailSecondSection d z x) (Ioi 0) := by
  unfold thetaCuspTailSecondSection
  rw [show (fun x : ℝ =>
      ((x ^ q * thetaCuspTailDerivative m x : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (d + 1),
          (-1 : ℂ) ^ k * z ^ (2 * k) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        ((-1 : ℂ) ^ k * z ^ (2 * k) /
            ((2 * k + 2).factorial : ℂ)) *
          (((x ^ (q + 2 * k + 2) * thetaCuspTailDerivative m x : ℝ) : ℂ)) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    rw [pow_add]
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _ =>
    ((integrableOn_pow_mul_thetaCuspTailDerivative (q + 2 * k + 2) m).ofReal).const_mul
      ((-1 : ℂ) ^ k * z ^ (2 * k) / ((2 * k + 2).factorial : ℂ))

theorem integrableOn_thetaCuspTailSecondScoreDensity_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondScoreDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) (Ioi 0) := by
  have hrho := integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z
  have htail : IntegrableOn (fun x : ℝ =>
      ((x * thetaCuspTailSecondDensityDerivative x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ =>
        ((x ^ 1 * thetaCuspTailDerivative 3 x : ℝ) : ℂ)) (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspTailDerivative 1 3).ofReal
    have hsection :=
      integrableOn_pow_mul_thetaCuspTailDerivative_complex_mul_section 1 3 d z
    unfold thetaCuspTailSecondDensityDerivative thetaCuspTailSecondCoreAtom
    rw [show (fun x : ℝ => ((x * (4 * thetaCuspTailDerivative 3 x) : ℝ) : ℂ) *
        (1 - (z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x)) =
      fun x : ℝ => (4 : ℂ) *
          ((x ^ 1 * thetaCuspTailDerivative 3 x : ℝ) : ℂ) -
        (4 : ℂ) * (z ^ 2 + 1 / 4) *
          (((x ^ 1 * thetaCuspTailDerivative 3 x : ℝ) : ℂ) *
            thetaCuspTailSecondSection d z x) by
      funext x
      push_cast
      simp only [pow_one]
      ring]
    exact (hbase.const_mul 4).sub
      (hsection.const_mul (4 * (z ^ 2 + 1 / 4)))
  unfold thetaCuspTailSecondScoreDensity
  rw [show (fun x : ℝ =>
      ((thetaCuspTailSecondDensity x +
        x * thetaCuspTailSecondDensityDerivative x : ℝ) : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x +
        ((x * thetaCuspTailSecondDensityDerivative x : ℝ) : ℂ) *
          thetaCuspTailSecondCoreAtom d z x by
    funext x
    push_cast
    ring]
  exact hrho.add htail

theorem integrableOn_id_mul_density_mul_coreAtomSourceDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSecondDensity thetaCuspTailSecondCoreAtomSourceDerivative
    thetaCuspTailSecondSectionSourceDerivative
  rw [show (fun x : ℝ => ((x * (4 * thetaCuspTailDerivative 2 x) : ℝ) : ℂ) *
      (-(z ^ 2 + 1 / 4) *
        ∑ k ∈ Finset.range (d + 1),
          (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))) =
    fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
      (-4 * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) *
        ((2 * k + 2 : ℕ) : ℂ) /
          ((2 * k + 2).factorial : ℂ)) *
        (((x ^ (2 * k + 2) * thetaCuspTailDerivative 2 x : ℝ) : ℂ)) by
    funext x
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    rw [show (x : ℂ) ^ (2 * k + 2) =
        (x : ℂ) * (x : ℂ) ^ (2 * k + 1) by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ]
      ring]
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _ =>
    ((integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 2) 2).ofReal).const_mul
      (-4 * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) *
        ((2 * k + 2 : ℕ) : ℂ) / ((2 * k + 2).factorial : ℂ))

theorem id_mul_density_mul_coreAtom_tendsto_atTop_zero
    (d : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ =>
      ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) atTop (nhds 0) := by
  rw [show (fun x : ℝ =>
      ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
    fun x : ℝ =>
      (4 : ℂ) * (((x ^ 1 * thetaCuspTailDerivative 2 x : ℝ) : ℂ)) -
      ∑ k ∈ Finset.range (d + 1),
        (4 * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
          ((2 * k + 2).factorial : ℂ)) *
            (((x ^ (2 * k + 3) * thetaCuspTailDerivative 2 x : ℝ) : ℂ)) by
    funext x
    unfold thetaCuspTailSecondDensity thetaCuspTailSecondCoreAtom
      thetaCuspTailSecondSection
    push_cast
    rw [mul_sub, mul_one, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · simp only [pow_one]
      ring
    · apply Finset.sum_congr rfl
      intro k _
      rw [show (x : ℂ) ^ (2 * k + 3) =
          (x : ℂ) ^ 1 * (x : ℂ) ^ (2 * k + 2) by
        rw [show 2 * k + 3 = 1 + (2 * k + 2) by omega, pow_add]]
      ring]
  have hfirst : Tendsto (fun x : ℝ =>
      (4 : ℂ) * (((x ^ 1 * thetaCuspTailDerivative 2 x : ℝ) : ℂ)))
      atTop (nhds 0) := by
    have hreal := pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero 1 2
    have hcomplex : Tendsto (fun x : ℝ =>
        (((x ^ 1 * thetaCuspTailDerivative 2 x : ℝ) : ℂ))) atTop (nhds 0) :=
      (Complex.ofRealCLM.continuous.tendsto 0).comp hreal
    simpa using hcomplex.const_mul (4 : ℂ)
  have hsum : Tendsto (fun x : ℝ =>
      ∑ k ∈ Finset.range (d + 1),
        (4 * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
          ((2 * k + 2).factorial : ℂ)) *
            (((x ^ (2 * k + 3) * thetaCuspTailDerivative 2 x : ℝ) : ℂ)))
      atTop (nhds 0) := by
    have h := tendsto_finsetSum (s := Finset.range (d + 1)) (a := fun _ => (0 : ℂ))
      (fun k _ => by
        have hreal :=
          pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (2 * k + 3) 2
        have hcomplex : Tendsto (fun x : ℝ =>
            (((x ^ (2 * k + 3) * thetaCuspTailDerivative 2 x : ℝ) : ℂ)))
            atTop (nhds 0) :=
          (Complex.ofRealCLM.continuous.tendsto 0).comp hreal
        simpa using hcomplex.const_mul
          (4 * (z ^ 2 + 1 / 4) * (-1 : ℂ) ^ k * z ^ (2 * k) /
            ((2 * k + 2).factorial : ℂ)))
    simpa using h
  convert hfirst.sub hsum using 1 ; simp

theorem integral_Ioi_density_id_mul_coreAtomSourceDerivative_eq_neg_score
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) =
      -∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondScoreDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x := by
  let u : ℝ → ℂ := fun x => ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun x => (thetaCuspTailSecondScoreDensity x : ℂ)
  let v : ℝ → ℂ := fun x => thetaCuspTailSecondCoreAtom d z x
  let v' : ℝ → ℂ := fun x => thetaCuspTailSecondCoreAtomSourceDerivative d z x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa using! Complex.ofRealCLM.hasDerivAt
    have hrho : HasDerivAt
        (fun t : ℝ => (thetaCuspTailSecondDensity t : ℂ))
        (thetaCuspTailSecondDensityDerivative x : ℂ) x := by
      exact (hasDerivAt_thetaCuspTailSecondDensity x).ofReal_comp
    dsimp [u, u', thetaCuspTailSecondScoreDensity]
    have hmul := hx.mul hrho
    simpa only [Pi.mul_apply, Complex.ofReal_add, Complex.ofReal_mul,
      one_mul] using! hmul
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    exact hasDerivAt_thetaCuspTailSecondCoreAtom_source d z x
  have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hscalar :=
      (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos
        (k := 1) (by omega) 2).const_mul 4
    have hcore : Tendsto v (nhdsWithin 0 (Ioi 0))
        (nhds (thetaCuspTailSecondCoreAtom d z 0)) := by
      exact (hasDerivAt_thetaCuspTailSecondCoreAtom_source d z 0).continuousAt.tendsto.mono_left
        inf_le_left
    have hu0 : Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      dsimp [u, thetaCuspTailSecondDensity]
      have hscalar0 : Tendsto
          (fun x : ℝ => 4 * (x ^ 1 * thetaCuspTailDerivative 2 x))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa only [mul_zero] using! hscalar
      have hcomplex : Tendsto
          (fun x : ℝ =>
            ((4 * (x ^ 1 * thetaCuspTailDerivative 2 x) : ℝ) : ℂ))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa only [Function.comp_apply, Complex.ofRealCLM_apply, map_zero] using!
          ((Complex.ofRealCLM.continuous.tendsto 0).comp hscalar0)
      exact hcomplex.congr' (Filter.Eventually.of_forall (fun t => by
        simp only [pow_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring))
    simpa only [Pi.mul_apply, zero_mul] using! hu0.mul hcore
  have htop : Tendsto (u * v) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, u, v] using!
      id_mul_density_mul_coreAtom_tendsto_atTop_zero d z
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    (by
      simpa only [Pi.mul_apply, u, v'] using!
        integrableOn_id_mul_density_mul_coreAtomSourceDerivative d z)
    (by
      simpa only [Pi.mul_apply, u', v] using!
        integrableOn_thetaCuspTailSecondScoreDensity_mul_coreAtom d z)
    hzero htop
  simpa only [Pi.mul_apply, u, u', v, v', zero_sub, sub_zero] using hibp

theorem thetaCuspTailSecondCore_score_identity
    (d : ℕ) (z : ℂ) :
    (z ^ 2 + 1 / 4) * z *
        (∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondCoreAtomDerivative d z x) =
      -(z ^ 2 + 1 / 4) *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondScoreDensity x : ℂ) *
              thetaCuspTailSecondCoreAtom d z x) +
        (1 / 2 : ℂ) *
          (1 - ∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensity x : ℂ) *
              thetaCuspTailSecondCoreAtom d z x) := by
  let D : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let X : ℂ := ∫ x : ℝ in Ioi 0,
    ((x * thetaCuspTailSecondDensity x : ℝ) : ℂ) *
      thetaCuspTailSecondCoreAtomSourceDerivative d z x
  let Q : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondScoreDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  let S : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondSection d z x
  let V : ℂ := ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  have hEuler : z * D = X + (1 / 2 : ℂ) * S := by
    dsimp [D, X, S]
    rw [← integral_const_mul]
    have hX := integrableOn_id_mul_density_mul_coreAtomSourceDerivative d z
    have hS := integrableOn_thetaCuspTailSecondDensity_mul_section d z
    rw [← integral_const_mul]
    rw [← integral_add hX (hS.const_mul (1 / 2 : ℂ))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have he := thetaCuspTailSecondCoreAtom_euler d z x
    push_cast
    linear_combination (thetaCuspTailSecondDensity x : ℂ) * he
  have hIBP : X = -Q := by
    exact integral_Ioi_density_id_mul_coreAtomSourceDerivative_eq_neg_score d z
  have hCore : (z ^ 2 + 1 / 4) * S = 1 - V := by
    dsimp [S, V]
    have hmass := integrableOn_thetaCuspTailSecondDensity_complex
    have hsection := integrableOn_thetaCuspTailSecondDensity_mul_section d z
    rw [show (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) -
        (z ^ 2 + 1 / 4) *
          ((thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSection d z x) by
      funext x
      unfold thetaCuspTailSecondCoreAtom
      ring]
    rw [integral_sub hmass (hsection.const_mul (z ^ 2 + 1 / 4)),
      integral_const_mul, integral_thetaCuspTailSecondDensity_complex]
    ring
  change (z ^ 2 + 1 / 4) * z * D =
    -(z ^ 2 + 1 / 4) * Q + (1 / 2 : ℂ) * (1 - V)
  calc
    (z ^ 2 + 1 / 4) * z * D =
        (z ^ 2 + 1 / 4) * (z * D) := by ring
    _ = (z ^ 2 + 1 / 4) * (X + (1 / 2 : ℂ) * S) := by rw [hEuler]
    _ = -(z ^ 2 + 1 / 4) * Q +
        (1 / 2 : ℂ) * ((z ^ 2 + 1 / 4) * S) := by rw [hIBP]; ring
    _ = -(z ^ 2 + 1 / 4) * Q + (1 / 2 : ℂ) * (1 - V) := by rw [hCore]

theorem xiCTaylorThetaTailCorePolynomial_score_identity
    (d : ℕ) (z : ℂ) :
    (z ^ 2 + 1 / 4) * z *
        (xiCTaylorThetaTailCorePolynomial d).derivative.eval z =
      -(1 / 2 : ℂ) * (z ^ 2 + 1 / 4) *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondScoreDensity x : ℂ) *
              thetaCuspTailSecondCoreAtom d z x) +
        1 / 4 - (1 / 2 : ℂ) *
          (xiCTaylorThetaTailCorePolynomial d).eval z := by
  have h := thetaCuspTailSecondCore_score_identity d z
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral,
    xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral]
  linear_combination (1 / 2 : ℂ) * h

/-- The mean-zero score has no independent moment data: its `m`th moment is exactly `-m` times
the corresponding canonical density moment.  Thus the score coordinate records a genuine
cancellation, but does not smuggle in a new coefficient sequence. -/
theorem integral_Ioi_pow_mul_thetaCuspTailSecondScoreDensity (m : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ m * thetaCuspTailSecondScoreDensity x) =
      -(m : ℝ) *
        ∫ x : ℝ in Ioi 0, x ^ m * thetaCuspTailSecondDensity x := by
  have hzero : Tendsto
      (fun x : ℝ => x ^ (m + 1) * thetaCuspTailSecondDensity x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    unfold thetaCuspTailSecondDensity
    convert (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos
      (k := m + 1) (by omega) 2).const_mul 4 using 1 <;>
      simp [mul_left_comm, mul_comm]
  have htop : Tendsto
      (fun x : ℝ => x ^ (m + 1) * thetaCuspTailSecondDensity x)
      atTop (nhds 0) := by
    unfold thetaCuspTailSecondDensity
    convert (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (m + 1) 2).const_mul 4
      using 1 <;> simp [mul_left_comm, mul_comm]
  have hderivInt : IntegrableOn (fun x : ℝ =>
      x ^ (m + 1) * thetaCuspTailSecondDensityDerivative x) (Ioi 0) := by
    unfold thetaCuspTailSecondDensityDerivative
    simpa only [mul_assoc, mul_left_comm, mul_comm] using!
      (integrableOn_pow_mul_thetaCuspTailDerivative (m + 1) 3).const_mul 4
  have hbase := integrableOn_pow_mul_thetaCuspTailSecondDensity m
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x ^ (m + 1))
    (u' := fun x : ℝ => ((m + 1 : ℕ) : ℝ) * x ^ m)
    (v := thetaCuspTailSecondDensity)
    (v' := thetaCuspTailSecondDensityDerivative)
    (fun x _ => by simpa using hasDerivAt_pow (m + 1) x)
    (fun x _ => hasDerivAt_thetaCuspTailSecondDensity x)
    hderivInt
    (by
      rw [show ((fun x : ℝ => ((m + 1 : ℕ) : ℝ) * x ^ m) *
          thetaCuspTailSecondDensity) =
        fun x : ℝ => ((m + 1 : ℕ) : ℝ) *
          (x ^ m * thetaCuspTailSecondDensity x) by funext x; simp; ring]
      exact hbase.const_mul ((m + 1 : ℕ) : ℝ))
    hzero htop
  unfold thetaCuspTailSecondScoreDensity
  rw [show (fun x : ℝ =>
      x ^ m * (thetaCuspTailSecondDensity x +
        x * thetaCuspTailSecondDensityDerivative x)) =
    fun x : ℝ => x ^ m * thetaCuspTailSecondDensity x +
      x ^ (m + 1) * thetaCuspTailSecondDensityDerivative x by
    funext x
    rw [pow_succ]
    ring]
  rw [integral_add hbase hderivInt]
  rw [show (fun x : ℝ => (((m + 1 : ℕ) : ℝ) * x ^ m) *
      thetaCuspTailSecondDensity x) =
    fun x : ℝ => ((m + 1 : ℕ) : ℝ) *
      (x ^ m * thetaCuspTailSecondDensity x) by funext x; ring,
    integral_const_mul] at hibp
  rw [show (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring] at hibp
  linear_combination hibp

/-- The most direct Chebyshev shortcut for the score covariance is false even before averaging:
at one rational upper-half-plane point the degree-two core cross phase takes both orientations as
the ordered source pair varies. -/
theorem thetaCuspTailSecondCoreAtom_crossPhase_not_ordered :
    let H := thetaCuspTailSecondCoreAtom 2 (2 + I / 5)
    (H (1 / 10)).im * (H 0).re - (H (1 / 10)).re * (H 0).im < 0 ∧
    0 < (H (11 / 5)).im * (H (9 / 10)).re -
      (H (11 / 5)).re * (H (9 / 10)).im := by
  dsimp only
  constructor <;>
    norm_num [thetaCuspTailSecondCoreAtom, thetaCuspTailSecondSection,
      Finset.sum_range_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    ring_nf <;> norm_num

end
end RHTower
