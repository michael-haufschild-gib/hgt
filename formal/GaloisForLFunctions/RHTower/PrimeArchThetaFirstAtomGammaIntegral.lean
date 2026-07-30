import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Fixed incomplete-Gamma coordinates for the dominant theta atom

The substitution `t = exp (2x)` sends every even moment of the dominant `n = 1`
theta-cusp source atom to one integral over the fixed half-line `(1, infinity)`.  The transformed
integrand is elementary, positive on that half-line, and exponentially decaying.  This is the
coordinate surface on which the two remaining buffered first-atom moment inequalities can be
proved by rational analytic bounds.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The fixed incomplete-Gamma integrand for the `2j`-th dominant theta-atom moment. -/
def thetaCuspFirstAtomGammaIntegrand (j : ℕ) (t : ℝ) : ℝ :=
  (Real.log t) ^ (2 * j) *
    (2 * Real.pi * t ^ (5 / 4 : ℝ) - 3 * t ^ (1 / 4 : ℝ)) *
      Real.exp (-Real.pi * t)

theorem continuousOn_thetaCuspFirstAtomGammaIntegrand (j : ℕ) :
    ContinuousOn (thetaCuspFirstAtomGammaIntegrand j) (Ioi 0) := by
  intro t ht
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht.ne'
  have hr14 : ContinuousAt (fun u : ℝ => u ^ (1 / 4 : ℝ)) t :=
    Real.continuousAt_rpow_const t _ (Or.inl ht.ne')
  have hr54 : ContinuousAt (fun u : ℝ => u ^ (5 / 4 : ℝ)) t :=
    Real.continuousAt_rpow_const t _ (Or.inl ht.ne')
  have hlogpow : ContinuousAt (fun u : ℝ => Real.log u ^ (2 * j)) t := hlog.pow _
  have h54 : ContinuousAt (fun u : ℝ => 2 * Real.pi * u ^ (5 / 4 : ℝ)) t :=
    continuousAt_const.mul hr54
  have h14 : ContinuousAt (fun u : ℝ => 3 * u ^ (1 / 4 : ℝ)) t :=
    continuousAt_const.mul hr14
  have hlin : ContinuousAt (fun u : ℝ => -Real.pi * u) t :=
    continuousAt_const.mul continuousAt_id
  have hexp : ContinuousAt (fun u : ℝ => Real.exp (-Real.pi * u)) t :=
    Real.continuous_exp.continuousAt.comp hlin
  exact ((hlogpow.mul (h54.sub h14)).mul hexp).continuousWithinAt

/-- The fixed incomplete-Gamma integrand is absolutely integrable. -/
theorem integrableOn_thetaCuspFirstAtomGammaIntegrand (j : ℕ) :
    IntegrableOn (thetaCuspFirstAtomGammaIntegrand j) (Ioi 1) := by
  let k : ℕ := 2 * j + 2
  have hbase : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
    have hk : (-1 : ℝ) < (k : ℝ) :=
      lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
    convert integrableOn_rpow_mul_exp_neg_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) hk (by norm_num) using 1
    ext t
    rw [Real.rpow_natCast, Real.rpow_one]
  have hmajor : IntegrableOn (fun t : ℝ => 10 * (t ^ k * Real.exp (-t))) (Ioi 1) :=
    (hbase.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro t ht
      exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)).const_mul 10
  apply Integrable.mono hmajor
  · exact (continuousOn_thetaCuspFirstAtomGammaIntegrand j).mono
      (show Ioi (1 : ℝ) ⊆ Ioi 0 by
        intro t ht
        exact lt_trans (by norm_num : (0 : ℝ) < 1) ht) |>.aestronglyMeasurable
          measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hlog : Real.log t ≤ t := Real.log_le_self ht0
    have hlogpow : (Real.log t) ^ (2 * j) ≤ t ^ (2 * j) := by gcongr
    have ht14 : t ^ (1 / 4 : ℝ) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht.le (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have ht54 : t ^ (5 / 4 : ℝ) ≤ t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht.le (by norm_num)
    have hpi : 2 * Real.pi ≤ 7 := by nlinarith [Real.pi_lt_d2]
    have hr14non : 0 ≤ t ^ (1 / 4 : ℝ) := Real.rpow_nonneg ht0 _
    have hr54non : 0 ≤ t ^ (5 / 4 : ℝ) := Real.rpow_nonneg ht0 _
    have h54non : 0 ≤ 2 * Real.pi * t ^ (5 / 4 : ℝ) := by positivity
    have h14non : 0 ≤ 3 * t ^ (1 / 4 : ℝ) := by positivity
    have hpoly :
        |2 * Real.pi * t ^ (5 / 4 : ℝ) - 3 * t ^ (1 / 4 : ℝ)| ≤
          10 * t ^ 2 := by
      calc
        |2 * Real.pi * t ^ (5 / 4 : ℝ) - 3 * t ^ (1 / 4 : ℝ)| ≤
            2 * Real.pi * t ^ (5 / 4 : ℝ) + 3 * t ^ (1 / 4 : ℝ) := by
              calc
                |2 * Real.pi * t ^ (5 / 4 : ℝ) - 3 * t ^ (1 / 4 : ℝ)| ≤
                    |2 * Real.pi * t ^ (5 / 4 : ℝ)| +
                      |3 * t ^ (1 / 4 : ℝ)| := abs_sub _ _
                _ = 2 * Real.pi * t ^ (5 / 4 : ℝ) +
                    3 * t ^ (1 / 4 : ℝ) := by
                      rw [abs_of_nonneg h54non, abs_of_nonneg h14non]
        _ ≤ 7 * t ^ 2 + 3 * t := by gcongr
        _ ≤ 10 * t ^ 2 := by
          have ht_sq : t ≤ t ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr ht.le) ht0]
          nlinarith
    have hexp : Real.exp (-Real.pi * t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hmajorNonneg : 0 ≤ 10 * (t ^ k * Real.exp (-t)) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
    unfold thetaCuspFirstAtomGammaIntegrand
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hlog0,
      abs_of_pos (Real.exp_pos _)]
    calc
      (Real.log t) ^ (2 * j) *
            |2 * Real.pi * t ^ (5 / 4 : ℝ) - 3 * t ^ (1 / 4 : ℝ)| *
          Real.exp (-Real.pi * t) ≤
        t ^ (2 * j) * (10 * t ^ 2) * Real.exp (-t) := by gcongr
      _ = 10 * (t ^ k * Real.exp (-t)) := by
        dsimp [k]
        rw [show t ^ (2 * j) * (10 * t ^ 2) =
            10 * (t ^ (2 * j) * t ^ 2) by ring, ← pow_add]
        ring

/-- Exact fixed-coordinate value of every even moment of the dominant theta source atom. -/
theorem thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral (j : ℕ) :
    thetaCuspAtomRawEvenMoment j 1 =
      (2 * Real.pi / (4 : ℝ) ^ j) *
        ∫ t : ℝ in Ioi 1, thetaCuspFirstAtomGammaIntegrand j t := by
  let f : ℝ → ℝ := fun x => Real.exp (2 * x)
  let f' : ℝ → ℝ := fun x => 2 * Real.exp (2 * x)
  let g : ℝ → ℝ := fun t =>
    (Real.pi / (4 : ℝ) ^ j) * thetaCuspFirstAtomGammaIntegrand j t
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
    simpa only [f, f', Function.comp_def, mul_comm] using! h.hasDerivWithinAt
  have himageIoi : f '' Ioi (0 : ℝ) ⊆ Ioi 1 := by
    rintro t ⟨x, hx, rfl⟩
    dsimp [f]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hx)
  have himageIci : f '' Ici (0 : ℝ) ⊆ Ici 1 := by
    rintro t ⟨x, hx, rfl⟩
    dsimp [f]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hx)
  have hgcont : ContinuousOn g (f '' Ioi (0 : ℝ)) := by
    exact ((continuousOn_thetaCuspFirstAtomGammaIntegrand j).const_mul _).mono
      (himageIoi.trans (show Ioi (1 : ℝ) ⊆ Ioi 0 by
        intro t ht
        exact lt_trans (by norm_num : (0 : ℝ) < 1) ht))
  have hg1 : IntegrableOn g (f '' Ici (0 : ℝ)) := by
    have hgammaIci : IntegrableOn (thetaCuspFirstAtomGammaIntegrand j) (Ici 1) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_thetaCuspFirstAtomGammaIntegrand j
    exact (hgammaIci.mono_set himageIci).const_mul (Real.pi / (4 : ℝ) ^ j)
  have hcompose : (fun x : ℝ => (g ∘ f) x * f' x) =
      fun x : ℝ => x ^ (2 * j) * thetaCuspSourceTerm x 1 := by
    funext x
    simp only [g, f, f', Function.comp_apply,
      thetaCuspFirstAtomGammaIntegrand, thetaCuspSourceTerm, thetaCuspSeed,
      Nat.cast_one, one_mul, Real.log_exp]
    rw [Real.rpow_def_of_pos (Real.exp_pos _) (5 / 4 : ℝ),
      Real.rpow_def_of_pos (Real.exp_pos _) (1 / 4 : ℝ)]
    simp only [Real.log_exp]
    have he54 : Real.exp (2 * x * (5 / 4 : ℝ)) = Real.exp (x / 2) ^ 5 := by
      calc
        Real.exp (2 * x * (5 / 4 : ℝ)) =
            Real.exp ((5 : ℝ) * (x / 2)) := by congr 1 <;> ring
        _ = Real.exp (x / 2) ^ 5 := Real.exp_nat_mul (x / 2) 5
    have he14 : Real.exp (2 * x * (1 / 4 : ℝ)) = Real.exp (x / 2) := by
      congr 1
      ring
    have he2 : Real.exp (2 * x) = Real.exp (x / 2) ^ 4 := by
      calc
        Real.exp (2 * x) = Real.exp ((4 : ℝ) * (x / 2)) := by congr 1 <;> ring
        _ = Real.exp (x / 2) ^ 4 := Real.exp_nat_mul (x / 2) 4
    have hex : Real.exp x = Real.exp (x / 2) ^ 2 := by
      calc
        Real.exp x = Real.exp ((2 : ℝ) * (x / 2)) := by congr 1 <;> ring
        _ = Real.exp (x / 2) ^ 2 := Real.exp_nat_mul (x / 2) 2
    have hpow : (4 : ℝ) ^ j = 2 ^ (2 * j) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hscale : (Real.pi / (4 : ℝ) ^ j) * (2 * x) ^ (2 * j) =
        Real.pi * x ^ (2 * j) := by
      rw [mul_pow, ← hpow]
      field_simp
    rw [he54, he14, he2, hex]
    rw [show
      Real.pi / (4 : ℝ) ^ j *
          ((2 * x) ^ (2 * j) *
            (2 * Real.pi * Real.exp (x / 2) ^ 5 - 3 * Real.exp (x / 2)) *
              Real.exp (-Real.pi * Real.exp (x / 2) ^ 4)) *
            (2 * Real.exp (x / 2) ^ 4) =
        (Real.pi / (4 : ℝ) ^ j * (2 * x) ^ (2 * j)) *
          (2 * Real.pi * Real.exp (x / 2) ^ 5 - 3 * Real.exp (x / 2)) *
            Real.exp (-Real.pi * Real.exp (x / 2) ^ 4) *
              (2 * Real.exp (x / 2) ^ 4) by ring, hscale]
    ring
  have hg2 : IntegrableOn (fun x : ℝ => (g ∘ f) x * f' x) (Ici 0) := by
    rw [hcompose]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hsubst := integral_comp_mul_deriv_Ioi hf hft hff' hgcont hg1 hg2
  rw [hcompose] at hsubst
  dsimp [f, g] at hsubst
  norm_num at hsubst
  rw [thetaCuspAtomRawEvenMoment, hsubst, integral_const_mul]
  ring

end RHTower
