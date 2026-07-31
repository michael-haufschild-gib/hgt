import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsCertificateReduction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Fixed incomplete-Gamma coordinate for the single Gibbs certificate

The substitution `t = exp (2x)` transports every moment of the positive first Liouville Gibbs
atom to one fixed incomplete-Gamma density on `(1, infinity)`.  In combination with the exact
single-Gibbs reduction, both remaining low-degree source certificates are therefore inequalities
in moments of one elementary positive half-line density.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Fixed positive log-Gamma integrand for the `m`-th first-atom Gibbs moment. -/
def thetaCuspFirstAtomSingleGibbsGammaIntegrand (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log t) ^ m * t ^ (1 / 4 : ℝ) * Real.exp (-Real.pi * t)

/-- Continuity of the fixed log-Gamma integrand on the positive half-line. -/
theorem continuousOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand (m : ℕ) :
    ContinuousOn (thetaCuspFirstAtomSingleGibbsGammaIntegrand m) (Ioi 0) := by
  intro t ht
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht.ne'
  have hr14 : ContinuousAt (fun u : ℝ => u ^ (1 / 4 : ℝ)) t :=
    Real.continuousAt_rpow_const t _ (Or.inl ht.ne')
  have hlin : ContinuousAt (fun u : ℝ => -Real.pi * u) t :=
    continuousAt_const.mul continuousAt_id
  have hexp : ContinuousAt (fun u : ℝ => Real.exp (-Real.pi * u)) t :=
    Real.continuous_exp.continuousAt.comp hlin
  exact (((hlog.pow m).mul hr14).mul hexp).continuousWithinAt

/-- Absolute integrability of the fixed log-Gamma integrand above one. -/
theorem integrableOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand (m : ℕ) :
    IntegrableOn (thetaCuspFirstAtomSingleGibbsGammaIntegrand m) (Ioi 1) := by
  let k : ℕ := m + 1
  have hbase : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
    have hk : (-1 : ℝ) < (k : ℝ) :=
      lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
    convert integrableOn_rpow_mul_exp_neg_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) hk (by norm_num) using 1
    ext t
    rw [Real.rpow_natCast, Real.rpow_one]
  have hmajor : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 1) :=
    hbase.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro t ht
      exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
  apply Integrable.mono hmajor
  · exact (continuousOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand m).mono
      (show Ioi (1 : ℝ) ⊆ Ioi 0 by
        intro t ht
        exact lt_trans (by norm_num : (0 : ℝ) < 1) ht) |>.aestronglyMeasurable
          measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hlog : Real.log t ≤ t := Real.log_le_self ht0
    have hlogpow : (Real.log t) ^ m ≤ t ^ m := by gcongr
    have ht14 : t ^ (1 / 4 : ℝ) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht.le (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hexp : Real.exp (-Real.pi * t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hmajorNonneg : 0 ≤ t ^ k * Real.exp (-t) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
    unfold thetaCuspFirstAtomSingleGibbsGammaIntegrand
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg ht0 _), abs_of_pos (Real.exp_pos _)]
    calc
      (Real.log t) ^ m * t ^ (1 / 4 : ℝ) * Real.exp (-Real.pi * t) ≤
          t ^ m * t * Real.exp (-t) := by gcongr
      _ = t ^ k * Real.exp (-t) := by
        dsimp [k]
        rw [pow_succ]

/-- Exact fixed-coordinate formula for every first-atom Gibbs moment. -/
theorem thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral (m : ℕ) :
    thetaCuspLiouvilleGibbsMoment m 1 =
      (1 / (2 : ℝ) ^ (m + 1)) *
        ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomSingleGibbsGammaIntegrand m t := by
  let f : ℝ → ℝ := fun x => Real.exp (2 * x)
  let f' : ℝ → ℝ := fun x => 2 * Real.exp (2 * x)
  let g : ℝ → ℝ := fun t =>
    (1 / (2 : ℝ) ^ (m + 1)) * thetaCuspFirstAtomSingleGibbsGammaIntegrand m t
  have hf : ContinuousOn f (Ici 0) := by
    dsimp [f]
    fun_prop
  have hft : Tendsto f atTop atTop := by
    dsimp [f]
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hff' : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x :=
      by simpa using (hasDerivAt_id x).const_mul 2
    have h := (Real.hasDerivAt_exp (2 * x)).comp x hlin
    refine h.hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    ring
  have himageIoi : f '' Ioi (0 : ℝ) ⊆ Ioi 1 := by
    rintro t ⟨x, hx, rfl⟩
    dsimp [f]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hx)
  have himageIci : f '' Ici (0 : ℝ) ⊆ Ici 1 := by
    rintro t ⟨x, hx, rfl⟩
    dsimp [f]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hx)
  have hgcont : ContinuousOn g (f '' Ioi (0 : ℝ)) := by
    exact ((continuousOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand m).const_mul _).mono
      (himageIoi.trans (show Ioi (1 : ℝ) ⊆ Ioi 0 by
        intro t ht
        exact lt_trans (by norm_num : (0 : ℝ) < 1) ht))
  have hg1 : IntegrableOn g (f '' Ici (0 : ℝ)) := by
    have hgammaIci : IntegrableOn (thetaCuspFirstAtomSingleGibbsGammaIntegrand m) (Ici 1) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_thetaCuspFirstAtomSingleGibbsGammaIntegrand m
    exact (hgammaIci.mono_set himageIci).const_mul
      (1 / (2 : ℝ) ^ (m + 1))
  have hcompose : (fun x : ℝ => (g ∘ f) x * f' x) =
      fun x : ℝ => x ^ m * thetaCuspLiouvilleGibbsAtom 1 x := by
    funext x
    simp only [g, f, f', Function.comp_apply, thetaCuspFirstAtomSingleGibbsGammaIntegrand,
      thetaCuspLiouvilleGibbsAtom_apply, Nat.cast_one, one_mul, Real.log_exp]
    rw [Real.rpow_def_of_pos (Real.exp_pos _) (1 / 4 : ℝ)]
    simp only [Real.log_exp]
    have he14 : Real.exp (2 * x * (1 / 4 : ℝ)) = Real.exp (x / 2) := by
      congr 1
      ring
    have he2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
      calc
        Real.exp (2 * x) = Real.exp ((2 : ℝ) * x) := rfl
        _ = Real.exp x ^ 2 := Real.exp_nat_mul x 2
    have hscale :
        (1 / (2 : ℝ) ^ (m + 1)) * (2 * x) ^ m *
            (2 * Real.exp (2 * x)) =
          x ^ m * Real.exp (2 * x) := by
      rw [mul_pow]
      field_simp
      ring
    rw [he14]
    rw [show
      1 / (2 : ℝ) ^ (m + 1) *
          ((2 * x) ^ m * Real.exp (x / 2) *
            Real.exp (-Real.pi * Real.exp (2 * x))) *
          (2 * Real.exp (2 * x)) =
        ((1 / (2 : ℝ) ^ (m + 1)) * (2 * x) ^ m *
          (2 * Real.exp (2 * x))) * Real.exp (x / 2) *
            Real.exp (-Real.pi * Real.exp (2 * x)) by ring,
      hscale]
    rw [he2]
    ring
  have hg2 : IntegrableOn (fun x : ℝ => (g ∘ f) x * f' x) (Ici 0) := by
    rw [hcompose]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        m (Polynomial.X ^ 2) (n := 1) (by norm_num)
  have hsubst := integral_comp_mul_deriv_Ioi hf hft hff' hgcont hg1 hg2
  rw [hcompose] at hsubst
  dsimp [f, g] at hsubst
  norm_num at hsubst
  rw [thetaCuspLiouvilleGibbsMoment, hsubst, integral_const_mul]
  simp only [one_div]

end RHTower
