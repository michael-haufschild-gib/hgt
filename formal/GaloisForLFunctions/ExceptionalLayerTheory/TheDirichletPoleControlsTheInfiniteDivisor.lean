import GaloisForLFunctions.HTGeometry.PolygammaSeries
import GaloisForLFunctions.RHTower.ArchLadderRegular
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedDirichletDivisor
import GaloisForLFunctions.ExceptionalLayerTheory.ThePositiveDirichletMomentKernel
import GaloisForLFunctions.RHTower.DirichletLStripBounds
import GaloisForLFunctions.RHTower.XiHypertranscendenceChain
import GaloisForLFunctions.RHTower.FermiNymanConfluentCoupling
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.HTGeometry.HalfPlanePolePushing

/-!
# The Dirichlet pole controls the complete infinite divisor

For a real primitive nonprincipal character, the positive Euler kernel
and both Gamma ladders bound every paired even zero moment by its pole
moment. The completed divisor also has a reciprocal-square mass bound
uniform in conductor and height.

Removing exactly one real exceptional multiplicity copy cancels the
pole to first order in its distance from one. The remaining two infinite
families have summable norms and a common moment bound. These are the
arithmetic inputs to infinite power-sum detection; no simplicity or
finite-support assumption is used.
-/

open Complex Filter Topology

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A real pole contributes nonnegatively to the paired real and vertical
observations, in every reciprocal power. -/
theorem real_resolvent_two_point_nonneg {x : ℝ} (hx : 0 < x) (t : ℝ) (m : ℕ) :
    0 ≤ (((x : ℂ) ^ m)⁻¹).re + ((((x : ℂ) + t * I) ^ m)⁻¹).re := by
  have hn : x ≤ ‖(x : ℂ) + t * I‖ := by
    simpa using re_le_norm ((x : ℂ) + t * I)
  have hb : ‖(((x : ℂ) + t * I) ^ m)⁻¹‖ ≤ (x ^ m)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (pow_pos hx m) (pow_le_pow_left₀ hx.le hn m)
  have ha := abs_re_le_norm ((((x : ℂ) + t * I) ^ m)⁻¹)
  have hl := neg_abs_le ((((x : ℂ) + t * I) ^ m)⁻¹).re
  rw [← ofReal_pow, ← ofReal_inv, ofReal_re]
  linarith only [hb, ha, hl]

/-- The entire Gamma pole series has the required sign in the paired
observation. Absolute convergence permits summation of the termwise law. -/
theorem gamma_reciprocal_moments_two_point_nonneg {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) (m : ℕ) :
    0 ≤ (∑' n : ℕ, (((σ : ℂ) + n) ^ (m + 2))⁻¹).re +
      (∑' n : ℕ, (((σ : ℂ) + t * I + n) ^ (m + 2))⁻¹).re := by
  have hs0 : Summable (fun n : ℕ => (((σ : ℂ) + n) ^ (m + 2))⁻¹) := by
    simpa only [ofReal_zero, zero_mul, add_zero] using summable_polygamma_terms hσ 0 m
  have hst := summable_polygamma_terms hσ t m
  have hs0r := hasSum_re hs0.hasSum
  have hstr := hasSum_re hst.hasSum
  refine (hs0r.add hstr).nonneg fun n => ?_
  have hp : 0 < σ + (n : ℝ) := by positivity
  have heq : (σ : ℂ) + t * I + n = ((σ + (n : ℝ) : ℝ) : ℂ) + t * I := by push_cast; ring
  have hbase : (σ : ℂ) + (n : ℂ) = ((σ + (n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [heq, hbase]
  exact real_resolvent_two_point_nonneg hp t (m + 2)

/-- Every odd digamma jet has nonnegative paired real part. The full
pole series, rather than a finite approximation, supplies the sign. -/
theorem digamma_odd_jet_two_point_nonneg {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) (k : ℕ) :
    0 ≤ (iteratedDeriv (2 * k + 1) Complex.digamma (σ : ℂ)).re +
      (iteratedDeriv (2 * k + 1) Complex.digamma ((σ : ℂ) + t * I)).re := by
  have hzero := (hasSum_polygamma_series hσ 0 (2 * k)).tsum_eq
  have hheight := (hasSum_polygamma_series hσ t (2 * k)).tsum_eq
  have heven : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  simp only [ofReal_zero, zero_mul, add_zero, heven, one_div] at hzero
  rw [heven, one_div] at hheight
  have h := gamma_reciprocal_moments_two_point_nonneg hσ t (2 * k)
  rw [hzero, hheight] at h
  have hcast : ((2 * k + 1).factorial : ℂ) = (((2 * k + 1).factorial : ℝ) : ℂ) := by simp
  rw [hcast, ← ofReal_inv, re_ofReal_mul, re_ofReal_mul, ← mul_add] at h
  exact nonneg_of_mul_nonneg_right h (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _)))

/-- The digamma contribution of a real Gamma ladder. -/
def gammaHalfLogDerivative (d : ℝ) (s : ℂ) : ℂ :=
  Complex.digamma ((s + (d : ℂ)) / 2) / 2

theorem gammaHalfLogDerivative_jet (d : ℝ) (j : ℕ) {s : ℂ}
    (hs : 0 < (s + (d : ℂ)).re) :
    iteratedDeriv j (gammaHalfLogDerivative d) s =
      (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma ((s + (d : ℂ)) / 2) := by
  have hp : ∀ n : ℕ, (s + (d : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hs, hh, hn0]
  have heq : gammaHalfLogDerivative d = fun w : ℂ =>
      (1 / 2 : ℂ) * (fun u : ℂ => Complex.digamma (u / 2)) (w - (-(d : ℂ))) := by
    funext w
    simp only [gammaHalfLogDerivative, sub_neg_eq_add]
    ring
  rw [heq, iteratedDeriv_const_mul_field]
  change (1 / 2 : ℂ) * iteratedDeriv j
    (fun w : ℂ => (fun u : ℂ => Complex.digamma (u / 2)) (w - (-(d : ℂ)))) s = _
  rw [iteratedDeriv_comp_sub_const j (fun u : ℂ => Complex.digamma (u / 2)) (-(d : ℂ))]
  change (1 / 2 : ℂ) * iteratedDeriv j (fun u : ℂ => Complex.digamma (u / 2)) (s - (-(d : ℂ))) = _
  rw [sub_neg_eq_add,
    RHTower.iteratedDeriv_half_digamma j (s + (d : ℂ)) hp, pow_succ]
  ring

/-- Every odd jet of a real Gamma ladder is nonnegative in the paired
observation used by the Euler kernel. -/
theorem gammaHalfLogDerivative_odd_jet_nonneg {d σ : ℝ} (hd : 0 ≤ d) (hσ : 0 < σ)
    (t : ℝ) (k : ℕ) :
    0 ≤ (iteratedDeriv (2 * k + 1) (gammaHalfLogDerivative d) (σ : ℂ)).re +
      (iteratedDeriv (2 * k + 1) (gammaHalfLogDerivative d) ((σ : ℂ) + t * I)).re := by
  have hsum : 0 < σ + d := add_pos_of_pos_of_nonneg hσ hd
  have h0 : 0 < ((σ : ℂ) + (d : ℂ)).re := by simpa only [add_re, ofReal_re] using hsum
  have ht : 0 < ((σ : ℂ) + t * I + (d : ℂ)).re := by simpa using hsum
  rw [gammaHalfLogDerivative_jet d (2 * k + 1) h0,
    gammaHalfLogDerivative_jet d (2 * k + 1) ht]
  have harg0 : ((σ : ℂ) + (d : ℂ)) / 2 = (((σ + d) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hargt : ((σ : ℂ) + t * I + (d : ℂ)) / 2 =
      (((σ + d) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hscale : (1 / 2 : ℂ) ^ (2 * k + 1 + 1) =
      (((1 / 2 : ℝ) ^ (2 * k + 1 + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [harg0, hargt, hscale, re_ofReal_mul, re_ofReal_mul, ← mul_add]
  exact mul_nonneg (by positivity) (digamma_odd_jet_two_point_nonneg (by linarith : 0 < (σ + d) / 2) (t / 2) k)

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex Filter Topology RHTower

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

private theorem half_translate_off_poles {d : ℝ} (hd : 0 ≤ d)
    {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, (s + (d : ℂ)) / 2 ≠ -(n : ℂ) := by
  intro n heq
  have hh := congrArg Complex.re heq
  simp only [div_ofNat_re, add_re, ofReal_re, neg_re, natCast_re] at hh
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith only [hs, hd, hh, hn]

private theorem logDeriv_conductor_factor (s : ℂ) :
    logDeriv (fun z : ℂ => (q : ℂ) ^ (z / 2)) s = (Real.log q : ℂ) / 2 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hd : HasDerivAt (fun z : ℂ => (q : ℂ) ^ (z / 2))
      ((q : ℂ) ^ (s / 2) * Complex.log (q : ℂ) * (1 / 2)) s := by
    simpa only [id_eq] using! ((hasDerivAt_id s).div_const 2).const_cpow (Or.inl hq)
  have hp : (q : ℂ) ^ (s / 2) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hq h.1
  rw [logDeriv_apply, hd.deriv, ← Complex.natCast_log]
  field_simp

/-- The rational pole at zero is absorbed by the first Gamma shift,
leaving the actual trivial-zero ladder of zeta. -/
private theorem logDeriv_xi_shifted {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = (s - 1)⁻¹ + Complex.digamma ((s + 2) / 2) / 2 -
      (Real.log Real.pi : ℂ) / 2 + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; norm_num at hs
  have hp : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    simpa only [ofReal_zero, add_zero] using half_translate_off_poles (d := 0) le_rfl (by linarith : 0 < s.re)
  have hrec := Complex.digamma_apply_add_one (s / 2) hp
  have harg : (s + 2) / 2 = s / 2 + 1 := by ring
  change xiLogDeriv s = _
  rw [xiLogDeriv_split hs, harg, hrec]
  change _ = _ + _ - _ + zetaLogDeriv s
  field_simp
  ring

/-- The entire auxiliary completion splits into its genuine pole, two
Gamma ladders, conductor constant, and the arithmetic Euler derivative. -/
theorem exceptionalCompletion_logDeriv_split {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ d : ℝ, (d = 0 ∨ d = 1) ∧ ∀ s : ℂ, 1 < s.re →
      logDeriv (exceptionalCompletion χ) s =
        (s - 1)⁻¹ + Complex.digamma ((s + 2) / 2) / 2 +
          Complex.digamma ((s + (d : ℂ)) / 2) / 2 +
          ((Real.log q / 2 - Real.log Real.pi : ℝ) : ℂ) +
          exceptionalEulerLogDerivative χ s := by
  obtain ⟨d, hd, hgamma⟩ := gammaFactor_eq_Gammaℝ χ
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  refine ⟨d, hd, fun s hs => ?_⟩
  have hcomp (w : ℂ) (hw : 1 < w.re) :
      DirichletCharacter.completedLFunction χ w = Gammaℝ (w + (d : ℂ)) * χ.LFunction w := by
    have hw0 : w ≠ 0 := by intro h; rw [h, zero_re] at hw; norm_num at hw
    have hg : Gammaℝ (w + (d : ℂ)) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
      rw [add_re, ofReal_re]; linarith only [hw, hd0])
    have hh := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w (Or.inl hw0)
    rw [hgamma w] at hh
    calc
      _ = χ.LFunction w * Gammaℝ (w + (d : ℂ)) := (div_eq_iff hg).mp hh.symm
      _ = _ := mul_comm _ _
  have hE : exceptionalCompletion χ s ≠ 0 := by
    intro h
    exact (not_lt_of_gt hs) (exceptionalCompletion_zero_strip hχ hprim h).2
  have hL : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro h
    apply hE
    rw [exceptionalCompletion, h, mul_zero]
  have hG : Gammaℝ (s + (d : ℂ)) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    rw [add_re, ofReal_re]; linarith only [hs, hd0])
  have hχs : χ.LFunction s ≠ 0 := by
    intro h
    apply hL
    rw [hcomp s hs, h, mul_zero]
  have hpoles := half_translate_off_poles hd0 (by linarith : 0 < s.re)
  have hGdiff : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (z + (d : ℂ))) s := by
    simpa only [Function.comp_def, id_eq] using!
      ((hasDerivAt_Gammaℝ_off_poles hpoles).comp s ((hasDerivAt_id s).add_const (d : ℂ))).differentiableAt
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      fun z => Gammaℝ (z + (d : ℂ)) * χ.LFunction z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact hcomp w hw
  have hlogL : logDeriv (DirichletCharacter.completedLFunction χ) s =
      Complex.digamma ((s + (d : ℂ)) / 2) / 2 - (Real.log Real.pi : ℂ) / 2 +
        logDeriv χ.LFunction s := by
    have hh : logDeriv (DirichletCharacter.completedLFunction χ) s =
        logDeriv (fun z => Gammaℝ (z + (d : ℂ)) * χ.LFunction z) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hh, logDeriv_mul s hG hχs hGdiff (DirichletCharacter.differentiable_LFunction hχ s),
      logDeriv_Gammaℝ_translate_off_poles hpoles]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hps : (q : ℂ) ^ (s / 2) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hq h.1
  have hpow : Differentiable ℂ (fun z : ℂ => (q : ℂ) ^ (z / 2)) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hq)
  have hxi : Differentiable ℂ xi := by
    have heq : xi = riemannXi := funext xi_eq_riemannXi
    rw [heq]
    exact differentiable_riemannXi
  change logDeriv (fun z => (xi z * (q : ℂ) ^ (z / 2)) * DirichletCharacter.completedLFunction χ z) s = _
  rw [logDeriv_mul (f := fun z : ℂ => xi z * (q : ℂ) ^ (z / 2))
      (g := DirichletCharacter.completedLFunction χ) s
      (_root_.mul_ne_zero (xi_ne_zero_of_one_le_re hs.le) hps)
      hL ((hxi.mul hpow) s) (DirichletCharacter.differentiable_completedLFunction hχ s),
    logDeriv_mul (f := xi) (g := fun z : ℂ => (q : ℂ) ^ (z / 2)) s
      (xi_ne_zero_of_one_le_re hs.le) hps (hxi s) (hpow s),
    hlogL, logDeriv_conductor_factor, logDeriv_xi_shifted hs, exceptionalEulerLogDerivative]
  push_cast
  ring

private theorem gammaHalfLogDerivative_analytic {d : ℝ} {s : ℂ}
    (hs : 0 < (s + (d : ℂ)).re) : AnalyticAt ℂ (gammaHalfLogDerivative d) s := by
  have hp : ∀ n : ℕ, (s + (d : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hs, hh, hn0]
  have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  have hψan : AnalyticAt ℂ Complex.digamma ((s + (d : ℂ)) / 2) := by
    have hh := GaloisForLFunctions.analyticAt_iteratedDeriv_logDeriv 0 _ hp
    rw [hψ] at hh
    simpa only [iteratedDeriv_zero] using hh
  have hin : AnalyticAt ℂ (fun w : ℂ => (w + (d : ℂ)) / 2) s := by
    exact (analyticAt_id.add analyticAt_const).div analyticAt_const (by norm_num)
  have hcomp := AnalyticAt.comp (f := fun w : ℂ => (w + (d : ℂ)) / 2) (x := s) hψan hin
  exact (by simpa only [Function.comp_def, gammaHalfLogDerivative] using!
    hcomp.div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0))

private theorem exceptionalEulerLogDerivative_analytic {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (exceptionalEulerLogDerivative χ) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at hs; exact (lt_irrefl _ hs)
  have hζan : AnalyticAt ℂ riemannZeta s := by
    have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact hd.analyticOnNhd isOpen_ne s hs1
  have hχan : AnalyticAt ℂ χ.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      isOpen_univ s (Set.mem_univ s)
  have hχs := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  exact (hζan.deriv.div hζan (riemannZeta_ne_zero_of_one_lt_re hs)).add
    (hχan.deriv.div hχan hχs)

private theorem exceptionalCompletion_odd_jet_split {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ d : ℝ, (d = 0 ∨ d = 1) ∧ ∀ (k : ℕ) (s : ℂ), 1 < s.re →
      iteratedDeriv (2 * k + 1) (logDeriv (exceptionalCompletion χ)) s =
        iteratedDeriv (2 * k + 1) (fun z : ℂ => (z - 1)⁻¹) s +
        iteratedDeriv (2 * k + 1) (gammaHalfLogDerivative 2) s +
        iteratedDeriv (2 * k + 1) (gammaHalfLogDerivative d) s +
        iteratedDeriv (2 * k + 1) (exceptionalEulerLogDerivative χ) s := by
  obtain ⟨d, hd, hsplit⟩ := exceptionalCompletion_logDeriv_split hχ hprim
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  refine ⟨d, hd, fun k s hs => ?_⟩
  let P : ℂ → ℂ := fun z => (z - 1)⁻¹
  let G₂ := gammaHalfLogDerivative 2
  let Gd := gammaHalfLogDerivative d
  let D := exceptionalEulerLogDerivative χ
  have hP : AnalyticAt ℂ P s := by
    have hs1 : s - 1 ≠ 0 := by
      intro h
      have heq := sub_eq_zero.mp h
      rw [heq, one_re] at hs
      exact (lt_irrefl _ hs)
    have hh : AnalyticAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
      (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ))).div (analyticAt_id.sub analyticAt_const) hs1
    simpa only [one_div] using hh
  have hG₂ : AnalyticAt ℂ G₂ s := gammaHalfLogDerivative_analytic (by
    norm_num; linarith only [hs])
  have hGd : AnalyticAt ℂ Gd s := gammaHalfLogDerivative_analytic (by
    rw [add_re, ofReal_re]; linarith only [hs, hd0])
  have hD : AnalyticAt ℂ D s := exceptionalEulerLogDerivative_analytic hχ hs
  have heq : logDeriv (exceptionalCompletion χ) =ᶠ[𝓝 s]
      fun w => ((Real.log q / 2 - Real.log Real.pi : ℝ) : ℂ) + (P + G₂ + Gd + D) w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    rw [hsplit w hw]
    dsimp only [P, G₂, Gd, D, gammaHalfLogDerivative, Pi.add_apply]
    push_cast
    ring
  rw [heq.iteratedDeriv_eq (2 * k + 1), iteratedDeriv_const_add (by omega : 0 < 2 * k + 1),
    iteratedDeriv_add ((hP.add hG₂).add hGd).contDiffAt hD.contDiffAt,
    iteratedDeriv_add (hP.add hG₂).contDiffAt hGd.contDiffAt,
    iteratedDeriv_add hP.contDiffAt hG₂.contDiffAt]

/-- Every even reciprocal moment of the actual nontrivial divisor is
bounded by the pole moment after pairing real and vertical observations.
The Euler kernel and both complete Gamma ladders have the required sign. -/
theorem exceptionalCompletion_even_moment_le_pole {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' i : ExceptionalZeroCopy χ, (((σ : ℂ) - exceptionalZero χ i)⁻¹) ^ (2 * k + 2)).re +
      (∑' i : ExceptionalZeroCopy χ, (((σ : ℂ) + t * I - exceptionalZero χ i)⁻¹) ^ (2 * k + 2)).re ≤
      ((((σ : ℂ) - 1)⁻¹) ^ (2 * k + 2)).re +
        ((((σ : ℂ) + t * I - 1)⁻¹) ^ (2 * k + 2)).re := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  obtain ⟨d, hd, hjet⟩ := exceptionalCompletion_odd_jet_split hχ hprim
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have h0 := congrArg Complex.re (hjet k (σ : ℂ) hs0)
  have ht := congrArg Complex.re (hjet k ((σ : ℂ) + t * I) hst)
  rw [(exceptionalCompletion_logarithmic_moments hχ hprim (2 * k) hs0).2,
    RHTower.iteratedDeriv_shifted_inv] at h0
  rw [(exceptionalCompletion_logarithmic_moments hχ hprim (2 * k) hst).2,
    RHTower.iteratedDeriv_shifted_inv] at ht
  have hodd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  have hcast : ((2 * k + 1).factorial : ℂ) = (((2 * k + 1).factorial : ℝ) : ℂ) := by simp
  norm_num only [show 2 * k + 1 + 1 = 2 * k + 2 by omega, hodd, hcast,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, mul_zero, zero_mul, sub_zero,
    neg_zero, one_mul] at h0 ht
  have hgamma₂ := gammaHalfLogDerivative_odd_jet_nonneg (d := 2) (by norm_num)
    (by linarith : 0 < σ) t k
  have hgammad := gammaHalfLogDerivative_odd_jet_nonneg hd0 (by linarith : 0 < σ) t k
  have heuler := exceptionalEuler_odd_jet_nonneg hreal k hσ t
  have hfac : (0 : ℝ) < (2 * k + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_left (not_le.mp hnot) hfac
  nlinarith only [h0, ht, hgamma₂, hgammad, heuler, hstrict]

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem re_digamma_le_add_one {z : ℂ} (hz : 0 < z.re) :
    (Complex.digamma z).re ≤ (Complex.digamma (z + 1)).re := by
  have hp : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hh
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hz, hh, hn0]
  rw [Complex.digamma_apply_add_one z hp, add_re]
  exact le_add_of_nonneg_right (by rw [inv_re]; exact div_nonneg hz.le (normSq_nonneg _))

/-- A uniform logarithmic upper bound for the real digamma contribution
throughout the right half-plane. -/
theorem re_digamma_le_log_norm_add_two {z : ℂ} (hz : 0 < z.re) :
    (Complex.digamma z).re ≤ Real.log (‖z‖ + 2) + 2 := by
  have hz1 : 0 < (z + 1).re := by rw [add_re, one_re]; linarith only [hz]
  have hz2 : 0 < (z + 2).re := by norm_num; linarith only [hz]
  have hnorm : 2 ≤ ‖z + 2‖ := by
    have hh := re_le_norm (z + 2)
    norm_num at hh
    linarith only [hz, hh]
  have hshift : (Complex.digamma z).re ≤ (Complex.digamma (z + 2)).re := by
    have h := (re_digamma_le_add_one hz).trans (re_digamma_le_add_one hz1)
    simpa only [show z + 1 + 1 = z + 2 by ring] using h
  have herr := HTGeometry.norm_digamma_sub_log_le_of_re_pos hz2 hnorm
  have hre := re_le_norm (Complex.digamma (z + 2) - Complex.log (z + 2))
  rw [sub_re, Complex.log_re] at hre
  have hnormpos : 0 < ‖z + 2‖ := lt_of_lt_of_le (by norm_num) hnorm
  have hrem : 3 / ‖z + 2‖ ≤ 3 / 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnorm
  have hnormUpper : ‖z + 2‖ ≤ ‖z‖ + 2 := by
    simpa only [norm_ofNat] using norm_add_le z (2 : ℂ)
  have hlog := Real.log_le_log hnormpos hnormUpper
  linarith only [hshift, herr, hre, hrem, hlog]

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private theorem exceptionalEulerCoefficient_bounded {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (n : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 2 * Λ n ∧ exceptionalEulerCoefficient χ n = (a : ℂ) := by
  rcases hχ (n : ZMod q) with hn | hn | hn
  · refine ⟨Λ n, vonMangoldt_nonneg, ?_, ?_⟩
    · linarith only [vonMangoldt_nonneg (n := n)]
    · simp [exceptionalEulerCoefficient, hn]
  · refine ⟨2 * Λ n, mul_nonneg (by norm_num) vonMangoldt_nonneg, le_rfl, ?_⟩
    simp only [exceptionalEulerCoefficient, hn, one_mul, ofReal_mul, ofReal_ofNat]
    ring
  · exact ⟨0, le_rfl, mul_nonneg (by norm_num) vonMangoldt_nonneg,
      by simp [exceptionalEulerCoefficient, hn]⟩

omit [NeZero q] in
private theorem euler_term_re_lower {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (σ t : ℝ) (n : ℕ) :
    -(LSeries.term (exceptionalEulerCoefficient χ) ((σ : ℂ) + t * I) n).re ≤
      2 * (LSeries.term (fun n => (Λ n : ℂ)) (σ : ℂ) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨a, ha, hab, heq⟩ := exceptionalEulerCoefficient_bounded hχ n
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', heq]
  have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  have hb := abs_re_le_norm ((a : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I))
  rw [norm_div, norm_real, Real.norm_of_nonneg ha, Complex.norm_natCast_cpow_of_pos hn] at hb
  have hneg := neg_le_abs ((a : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I)).re
  have hdiv := div_le_div_of_nonneg_right hab (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [hnσ, Complex.div_ofReal_re, ofReal_re]
  rw [mul_div_assoc] at hdiv
  linarith only [hb, hneg, hdiv]

/-- The Euler contribution to the completed-divisor mass is bounded
uniformly in height and conductor by the zeta pole. -/
theorem exceptionalEuler_re_le_pole {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (exceptionalEulerLogDerivative χ ((σ : ℂ) + t * I)).re ≤ 2 / (σ - 1) + 2 := by
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hsum : LSeriesSummable (exceptionalEulerCoefficient χ) ((σ : ℂ) + t * I) :=
    (LSeriesSummable_vonMangoldt hst).add (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hst)
  have hχsum := (hasSum_re hsum.LSeriesHasSum).neg
  have hζsum := (hasSum_re (LSeriesSummable_vonMangoldt (show 1 < (σ : ℂ).re from hσ)).LSeriesHasSum).mul_left 2
  have hle := hasSum_le (euler_term_re_lower hχ σ t) hχsum hζsum
  have heq : exceptionalEulerLogDerivative χ ((σ : ℂ) + t * I) =
      -LSeries (exceptionalEulerCoefficient χ) ((σ : ℂ) + t * I) := by
    simpa using exceptionalEulerLogDerivative_jet χ 0 hst
  have hz := RHTower.neg_re_logDeriv_riemannZeta_real_le_neg hσ hσ2
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1 < (σ : ℂ).re from hσ)] at hz
  rw [heq, neg_re]
  simp only [div_eq_mul_inv, one_mul] at hz ⊢
  linarith only [hle, hz]

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A real exceptional zero cancels the pole to first order in its
distance from one, uniformly in height and in every reciprocal moment. -/
theorem norm_inverse_moment_real_shift_le {z : ℂ} {α η : ℝ}
    (hα : 0 < α) (hz : α ≤ z.re) (hη : 0 ≤ η) (n : ℕ) :
    ‖(z⁻¹) ^ n - ((z + (η : ℂ))⁻¹) ^ n‖ ≤
      (n : ℝ) * η * α⁻¹ ^ (n + 1) := by
  have hzNorm : α ≤ ‖z‖ := hz.trans (re_le_norm z)
  have hzShiftNorm : α ≤ ‖z + (η : ℂ)‖ := by
    have hre := re_le_norm (z + (η : ℂ))
    rw [add_re, ofReal_re] at hre
    linarith only [hz, hη, hre]
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hα.trans_le hzNorm)
  have hs0 : z + (η : ℂ) ≠ 0 := norm_pos_iff.mp (hα.trans_le hzShiftNorm)
  have ha : ‖z⁻¹‖ ≤ α⁻¹ := by rw [norm_inv]; exact inv_anti₀ hα hzNorm
  have hb : ‖(z + (η : ℂ))⁻¹‖ ≤ α⁻¹ := by rw [norm_inv]; exact inv_anti₀ hα hzShiftNorm
  have hid : z⁻¹ - (z + (η : ℂ))⁻¹ = (η : ℂ) * z⁻¹ * (z + (η : ℂ))⁻¹ := by
    field_simp
    ring
  have hdiff : ‖z⁻¹ - (z + (η : ℂ))⁻¹‖ ≤ η * α⁻¹ ^ 2 := by
    rw [hid, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hη]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left ha hη) hb
      (norm_nonneg _) (mul_nonneg hη (inv_nonneg.mpr hα.le))
    exact hh.trans_eq (by ring)
  cases n with
  | zero => simp
  | succ n =>
    have hp := HTGeometry.norm_pow_sub_pow_le ha hb (n + 1)
    have hm := mul_le_mul_of_nonneg_left hdiff
      (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ) * α⁻¹ ^ (n + 1 - 1))
    refine hp.trans (hm.trans_eq ?_)
    rw [Nat.add_sub_cancel, show n + 1 + 1 = n + 2 by omega, pow_add]
    ring

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

private theorem gamma_half_re_le_height {d σ : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (Complex.digamma (((σ : ℂ) + t * I + (d : ℂ)) / 2)).re ≤
      Real.log (|t| + 3) + 3 := by
  let z : ℂ := ((σ : ℂ) + t * I + (d : ℂ)) / 2
  have harg : z = (((σ + d) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    dsimp only [z]
    push_cast
    ring
  have ha : 0 < (σ + d) / 2 := by linarith only [hσ, hd0]
  have hz : 0 < z.re := by rw [harg]; simpa using ha
  have hn : ‖z‖ ≤ (σ + d) / 2 + |t| / 2 := by
    rw [harg]
    have hh := norm_add_le ((((σ + d) / 2 : ℝ) : ℂ)) (((t / 2 : ℝ) : ℂ) * I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hh
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
  have hargle : ‖z‖ + 2 ≤ 2 * (|t| + 3) := by
    linarith only [hn, hσ2, hd2, abs_nonneg t]
  have hlog := Real.log_le_log (by positivity : 0 < ‖z‖ + 2) hargle
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : |t| + 3 ≠ 0)] at hlog
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hψ := re_digamma_le_log_norm_add_two hz
  change (Complex.digamma z).re ≤ _
  linarith only [hlog, hlog2, hψ]

private theorem exceptionalCompletion_re_logDeriv_le_conductor {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (logDeriv (exceptionalCompletion χ) ((σ : ℂ) + t * I)).re ≤
      3 / (σ - 1) + 5 * (1 + Real.log q + Real.log (|t| + 3)) := by
  obtain ⟨d, hd, heq⟩ := exceptionalCompletion_logDeriv_split hχ hprim
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hd2 : d ≤ 2 := by rcases hd with rfl | rfl <;> norm_num
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h₁ := gamma_half_re_le_height (d := 2) (by norm_num) le_rfl hσ hσ2 t
  simp only [ofReal_ofNat] at h₁
  have h₂ := gamma_half_re_le_height hd0 hd2 hσ hσ2 t
  have hEuler := exceptionalEuler_re_le_pole hreal hσ hσ2 t
  have hPole : ((((σ : ℂ) + t * I - 1)⁻¹)).re ≤ 1 / (σ - 1) := by
    refine (re_le_norm _).trans ?_
    rw [norm_inv, one_div]
    apply inv_anti₀ (by linarith : 0 < σ - 1)
    have hh := re_le_norm ((σ : ℂ) + t * I - 1)
    simpa using hh
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have htlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
  have hπlog : 0 ≤ Real.log Real.pi := Real.log_nonneg
    (le_trans (by norm_num : (1 : ℝ) ≤ 3) Real.pi_gt_three.le)
  rw [heq _ hst, add_re, add_re, add_re, add_re, div_ofNat_re, div_ofNat_re, ofReal_re]
  simp only [div_eq_mul_inv, one_mul] at h₁ h₂ hEuler hPole ⊢
  norm_num only at h₁ h₂ hEuler hPole ⊢
  nlinarith only [h₁, h₂, hEuler, hPole, hqlog, htlog, hπlog]

/-- The complete reciprocal-square mass has logarithmic conductor
growth, uniformly throughout the Euler strip. -/
theorem exceptionalCompletion_mass_le_conductor {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (∑' i : ExceptionalZeroCopy χ, 1 / ‖(σ : ℂ) + t * I - exceptionalZero χ i‖ ^ 2) ≤
      16 * (1 / (σ - 1) ^ 2 +
        (1 + Real.log q + Real.log (|t| + 3)) / (σ - 1)) := by
  have hα : 0 < σ - 1 := by linarith only [hσ]
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hm := exceptionalCompletion_mass_le_logDeriv hχ hprim hreal hst
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, add_zero] at hm
  have hb := exceptionalCompletion_re_logDeriv_le_conductor hχ hprim hreal hσ hσ2 t
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 0 ≤ 1 + Real.log q + Real.log (|t| + 3) := by
    have hqlog := Real.log_nonneg hq1
    have htlog := Real.log_nonneg (show 1 ≤ |t| + 3 by linarith only [abs_nonneg t])
    linarith only [hqlog, htlog]
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_left (not_le.mp hnot) hα
  have hid : (σ - 1) * (16 * (1 / (σ - 1) ^ 2 +
      (1 + Real.log q + Real.log (|t| + 3)) / (σ - 1))) =
      16 / (σ - 1) + 16 * (1 + Real.log q + Real.log (|t| + 3)) := by
    field_simp
  rw [hid] at hstrict
  have hi : 0 < 1 / (σ - 1) := one_div_pos.mpr hα
  simp only [div_eq_mul_inv, one_mul] at hm hb hi hstrict
  nlinarith only [hm, hb, hL, hi, hstrict]

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

local instance (χ : DirichletCharacter ℂ q) : DecidableEq (ExceptionalZeroCopy χ) := Classical.decEq _

/-- One multiplicity copy is removed, even if other copies have the
same ordinate and real part. -/
def deletedExceptionalResolvent (χ : DirichletCharacter ℂ q)
    (i₁ : ExceptionalZeroCopy χ) (s : ℂ) (i : ExceptionalZeroCopy χ) : ℂ := by
  classical
  exact if i = i₁ then 0 else ((s - exceptionalZero χ i)⁻¹) ^ 2

private theorem deletedExceptionalResolvent_pow (χ : DirichletCharacter ℂ q)
    (i₁ : ExceptionalZeroCopy χ) (s : ℂ) {k : ℕ} (hk : 0 < k)
    (i : ExceptionalZeroCopy χ) :
    deletedExceptionalResolvent χ i₁ s i ^ k =
      if i = i₁ then 0 else ((s - exceptionalZero χ i)⁻¹) ^ (2 * k) := by
  classical
  by_cases hi : i = i₁
  · simp only [deletedExceptionalResolvent, hi, if_true, zero_pow hk.ne']
  · simp only [deletedExceptionalResolvent, hi, if_false, pow_mul]

private theorem exceptionalResolvent_power_summable {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re)
    {k : ℕ} (hk : 0 < k) :
    Summable (fun i : ExceptionalZeroCopy χ => ((s - exceptionalZero χ i)⁻¹) ^ (2 * k)) := by
  have hh := (exceptionalCompletion_logarithmic_moments hχ hprim (2 * k - 2) hs).1
  rw [show 2 * k - 2 + 2 = 2 * k by omega] at hh
  exact hh.of_norm

theorem deletedExceptionalResolvent_power_summable {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i₁ : ExceptionalZeroCopy χ)
    {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 0 < k) :
    Summable (fun i => deletedExceptionalResolvent χ i₁ s i ^ k) := by
  classical
  have hfull := exceptionalResolvent_power_summable hχ hprim hs hk
  have heq : (fun i => deletedExceptionalResolvent χ i₁ s i ^ k) =
      Function.update (fun i => ((s - exceptionalZero χ i)⁻¹) ^ (2 * k)) i₁ 0 := by
    funext i
    rw [deletedExceptionalResolvent_pow χ i₁ s hk]
    by_cases hi : i = i₁
    · subst i; simp
    · rw [if_neg hi, Function.update_of_ne hi]
  rw [heq]
  exact hfull.update i₁ 0

/-- Deleting the selected copy subtracts exactly one zero moment;
no simplicity premise is used. -/
theorem tsum_deletedExceptionalResolvent_power {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i₁ : ExceptionalZeroCopy χ)
    {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 0 < k) :
    (∑' i, deletedExceptionalResolvent χ i₁ s i ^ k) =
      (∑' i : ExceptionalZeroCopy χ, ((s - exceptionalZero χ i)⁻¹) ^ (2 * k)) -
        ((s - exceptionalZero χ i₁)⁻¹) ^ (2 * k) := by
  classical
  have hfull := exceptionalResolvent_power_summable hχ hprim hs hk
  have hid := hfull.tsum_eq_add_tsum_ite i₁
  simp_rw [deletedExceptionalResolvent_pow χ i₁ s hk]
  exact eq_sub_iff_add_eq.mpr (by rw [hid]; ring)

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

/-- A single real exceptional-zero copy cancels the pole in every
even moment. All other multiplicity copies remain in the sums. -/
theorem deletedExceptionalResolvent_moment_le {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (i₁ : ExceptionalZeroCopy χ) {β : ℝ} (hβ : exceptionalZero χ i₁ = (β : ℂ))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {k : ℕ} (hk : 0 < k) :
    (∑' i, deletedExceptionalResolvent χ i₁ (σ : ℂ) i ^ k).re +
      (∑' i, deletedExceptionalResolvent χ i₁ ((σ : ℂ) + t * I) i ^ k).re ≤
      4 * (k : ℝ) * (1 - β) * (σ - 1)⁻¹ ^ (2 * k + 1) := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hβlt : β < 1 := by
    have hh := (exceptionalZero_strip hχ hprim i₁).2
    simpa only [hβ, ofReal_re] using hh
  have hα : 0 < σ - 1 := by linarith only [hσ]
  have hη : 0 ≤ 1 - β := by linarith only [hβlt]
  have hcomp := exceptionalCompletion_even_moment_le_pole hχ hprim hreal (k - 1) hσ t
  rw [show 2 * (k - 1) + 2 = 2 * k by omega] at hcomp
  have hb0 := norm_inverse_moment_real_shift_le (z := (σ : ℂ) - 1) hα
    (by simp : σ - 1 ≤ ((σ : ℂ) - 1).re) hη (2 * k)
  have hbt := norm_inverse_moment_real_shift_le (z := (σ : ℂ) + t * I - 1) hα
    (by simp : σ - 1 ≤ ((σ : ℂ) + t * I - 1).re) hη (2 * k)
  have heq0 : (σ : ℂ) - 1 + ((1 - β : ℝ) : ℂ) = (σ : ℂ) - (β : ℂ) := by push_cast; ring
  have heqt : (σ : ℂ) + t * I - 1 + ((1 - β : ℝ) : ℂ) =
      (σ : ℂ) + t * I - (β : ℂ) := by push_cast; ring
  rw [heq0] at hb0
  rw [heqt] at hbt
  have hr0 := re_le_norm ((((σ : ℂ) - 1)⁻¹) ^ (2 * k) - (((σ : ℂ) - (β : ℂ))⁻¹) ^ (2 * k))
  have hrt := re_le_norm ((((σ : ℂ) + t * I - 1)⁻¹) ^ (2 * k) -
    (((σ : ℂ) + t * I - (β : ℂ))⁻¹) ^ (2 * k))
  rw [sub_re] at hr0 hrt
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb0 hbt
  rw [tsum_deletedExceptionalResolvent_power hχ hprim i₁ hs0 hk,
    tsum_deletedExceptionalResolvent_power hχ hprim i₁ hst hk, hβ, sub_re, sub_re]
  nlinarith only [hcomp, hb0, hbt, hr0, hrt]

theorem deletedExceptionalResolvent_norm_summable {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i₁ : ExceptionalZeroCopy χ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i => ‖deletedExceptionalResolvent χ i₁ s i‖) := by
  simpa only [pow_one] using (deletedExceptionalResolvent_power_summable hχ hprim i₁ hs (k := 1) (by omega)).norm

/-- Removing one copy cannot increase the complete divisor mass. -/
theorem deletedExceptionalResolvent_mass_le_conductor {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (i₁ : ExceptionalZeroCopy χ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (∑' i, ‖deletedExceptionalResolvent χ i₁ ((σ : ℂ) + t * I) i‖) ≤
      16 * (1 / (σ - 1) ^ 2 +
        (1 + Real.log q + Real.log (|t| + 3)) / (σ - 1)) := by
  classical
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hfull : Summable (fun i : ExceptionalZeroCopy χ =>
      1 / ‖(σ : ℂ) + t * I - exceptionalZero χ i‖ ^ 2) := by
    simpa only [zero_add, norm_pow, norm_inv, inv_pow, one_div] using
      (exceptionalCompletion_logarithmic_moments hχ hprim 0 hst).1
  have hpoint (i : ExceptionalZeroCopy χ) :
      ‖deletedExceptionalResolvent χ i₁ ((σ : ℂ) + t * I) i‖ ≤
        1 / ‖(σ : ℂ) + t * I - exceptionalZero χ i‖ ^ 2 := by
    by_cases hi : i = i₁
    · simp only [deletedExceptionalResolvent, hi, if_true, norm_zero]
      positivity
    · simp only [deletedExceptionalResolvent, hi, if_false, norm_pow, norm_inv, inv_pow, one_div, le_refl]
  exact (Summable.tsum_le_tsum hpoint
    (deletedExceptionalResolvent_norm_summable hχ hprim i₁ hst) hfull).trans
      (exceptionalCompletion_mass_le_conductor hχ hprim hreal hσ hσ2 t)

end GaloisForLFunctions.ExceptionalLayerTheory


open Complex

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

/-- The two complete reciprocal-square families after removing one
exceptional copy from each observation. -/
def pairedExceptionalResolvent (χ : DirichletCharacter ℂ q)
    (i₁ : ExceptionalZeroCopy χ) (σ t : ℝ) :
    ExceptionalZeroCopy χ ⊕ ExceptionalZeroCopy χ → ℂ :=
  Sum.elim (deletedExceptionalResolvent χ i₁ (σ : ℂ))
    (deletedExceptionalResolvent χ i₁ ((σ : ℂ) + t * I))

theorem pairedExceptionalResolvent_norm_summable {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i₁ : ExceptionalZeroCopy χ)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun i => ‖pairedExceptionalResolvent χ i₁ σ t i‖) := by
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  exact Summable.sum _ (deletedExceptionalResolvent_norm_summable hχ hprim i₁ hσ)
    (deletedExceptionalResolvent_norm_summable hχ hprim i₁ hst)

private theorem pairedExceptionalResolvent_tsum_norm {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (i₁ : ExceptionalZeroCopy χ)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' i, ‖pairedExceptionalResolvent χ i₁ σ t i‖) =
      (∑' i, ‖deletedExceptionalResolvent χ i₁ (σ : ℂ) i‖) +
        (∑' i, ‖deletedExceptionalResolvent χ i₁ ((σ : ℂ) + t * I) i‖) := by
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hh := HasSum.sum
    (f := fun i : ExceptionalZeroCopy χ ⊕ ExceptionalZeroCopy χ =>
      ‖pairedExceptionalResolvent χ i₁ σ t i‖)
    (deletedExceptionalResolvent_norm_summable hχ hprim i₁ hσ).hasSum
    (deletedExceptionalResolvent_norm_summable hχ hprim i₁ hst).hasSum
  exact hh.tsum_eq

/-- The paired family has the same logarithmic conductor mass bound
as the full divisor. -/
theorem pairedExceptionalResolvent_mass_le {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (i₁ : ExceptionalZeroCopy χ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    (∑' i, ‖pairedExceptionalResolvent χ i₁ σ t i‖) ≤
      32 * (1 / (σ - 1) ^ 2 +
        (1 + Real.log q + Real.log (|t| + 3)) / (σ - 1)) := by
  have h0 := deletedExceptionalResolvent_mass_le_conductor hχ hprim hreal i₁ hσ hσ2 0
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at h0
  have ht := deletedExceptionalResolvent_mass_le_conductor hχ hprim hreal i₁ hσ hσ2 t
  have hlog : Real.log 3 ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by norm_num) (by linarith only [abs_nonneg t])
  have hlogsum : 1 + Real.log q + Real.log 3 ≤ 1 + Real.log q + Real.log (|t| + 3) := by
    linarith only [hlog]
  have hdiv := div_le_div_of_nonneg_right hlogsum (by linarith : 0 ≤ σ - 1)
  have hinside : 1 / (σ - 1) ^ 2 + (1 + Real.log q + Real.log 3) / (σ - 1) ≤
      1 / (σ - 1) ^ 2 + (1 + Real.log q + Real.log (|t| + 3)) / (σ - 1) := by
    linarith only [hdiv]
  have h0' := h0.trans (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : ℝ) ≤ 16))
  rw [pairedExceptionalResolvent_tsum_norm hχ hprim i₁ hσ t]
  linarith only [h0', ht]

/-- The complete paired family satisfies the exceptional pole-cancellation
bound in every positive power. -/
theorem pairedExceptionalResolvent_moment_le {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (i₁ : ExceptionalZeroCopy χ) {β : ℝ} (hβ : exceptionalZero χ i₁ = (β : ℂ))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {k : ℕ} (hk : 0 < k) :
    (∑' i, pairedExceptionalResolvent χ i₁ σ t i ^ k).re ≤
      4 * (k : ℝ) * (1 - β) * (σ - 1)⁻¹ ^ (2 * k + 1) := by
  have hst : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hh := HasSum.sum
    (f := fun i : ExceptionalZeroCopy χ ⊕ ExceptionalZeroCopy χ =>
      pairedExceptionalResolvent χ i₁ σ t i ^ k)
    (deletedExceptionalResolvent_power_summable hχ hprim i₁ hσ hk).hasSum
    (deletedExceptionalResolvent_power_summable hχ hprim i₁ hst hk).hasSum
  rw [hh.tsum_eq, add_re]
  exact deletedExceptionalResolvent_moment_le hχ hprim hreal i₁ hβ hσ t hk

/-- Evaluating at a target zero's ordinate exposes a positive real
reciprocal-square term. Other copies at the same zero remain detectable. -/
theorem pairedExceptionalResolvent_target {χ : DirichletCharacter ℂ q}
    (i₁ j : ExceptionalZeroCopy χ) (hj : j ≠ i₁) (σ : ℝ) :
    pairedExceptionalResolvent χ i₁ σ (exceptionalZero χ j).im (.inr j) =
      (((σ - (exceptionalZero χ j).re)⁻¹ ^ 2 : ℝ) : ℂ) := by
  classical
  change deletedExceptionalResolvent χ i₁
    ((σ : ℂ) + (exceptionalZero χ j).im * I) j = _
  rw [deletedExceptionalResolvent, if_neg hj]
  have heq : (σ : ℂ) + (exceptionalZero χ j).im * I - exceptionalZero χ j =
      ((σ - (exceptionalZero χ j).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq, ← ofReal_inv, ← ofReal_pow]

end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exceptionalCompletion_even_moment_le_pole
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exceptionalCompletion_mass_le_conductor
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.pairedExceptionalResolvent_mass_le
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.pairedExceptionalResolvent_moment_le
