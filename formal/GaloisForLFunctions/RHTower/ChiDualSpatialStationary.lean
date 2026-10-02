import GaloisForLFunctions.RHTower.ChiDualSpatialFourierTail
import GaloisForLFunctions.RHTower.OscillatoryIntegralComplexAmplitude
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation
import GaloisForLFunctions.RHTower.VanDerCorputLocal
import GaloisForLFunctions.RHTower.QuadraticPhaseStationary
import GaloisForLFunctions.HTGeometry.GammaStirlingCubicLog

/-!
# Stationary value of the literal first spatial Fourier mode

The centered spatial logarithmic phase has a cubic quadratic-model remainder.
The local Fresnel value and both full exterior integrals give a stationary bound;
complex-amplitude freezing retains all variation costs. The final theorem derives
every amplitude bound from the literal Gaussian cutoff and complex power.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The negative of the literal first spatial Fourier phase, centered at its saddle. -/
def chiDualSpatialSaddlePhase (a x : ℝ) : ℝ :=
  2 * Real.pi * (x - a - a * (Real.log x - Real.log a))

theorem chiDualSpatialPhase_sub_saddle (a x : ℝ) :
    chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x -
      chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a =
        -chiDualSpatialSaddlePhase a x := by
  unfold chiDualSpatialPhase chiDualSpatialSaddlePhase
  ring

/-- The actual spatial logarithmic phase has a cubic quadratic-model error. -/
theorem abs_chiDualSpatialSaddlePhase_sub_quadratic_le {a x : ℝ} (ha : 0 < a)
    (hx : |x - a| ≤ a / 2) :
    |chiDualSpatialSaddlePhase a x - Real.pi * (x - a) ^ 2 / a| ≤
      2 * Real.pi * |x - a| ^ 3 / a ^ 2 := by
  have hx0 : 0 < x := by linarith [(abs_le.mp hx).1]
  let u : ℝ := (x - a) / a
  have hu : |u| ≤ 1 / 2 := by
    dsimp only [u]
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  have hnorm : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have ht := GaloisForLFunctions.HTGeometry.norm_log_one_add_sub_taylor_two_le
    (u := (u : ℂ)) (by rwa [hnorm])
  have hbase : 1 + u = x / a := by dsimp only [u]; field_simp; ring
  have hbase0 : 0 < 1 + u := by rw [hbase]; exact div_pos hx0 ha
  have hlog : Complex.log (1 + (u : ℂ)) = (Real.log (1 + u) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hbase0.le]
  have he : Complex.log (1 + (u : ℂ)) - u + (u : ℂ) ^ 2 / 2 =
      ((Real.log (1 + u) - u + u ^ 2 / 2 : ℝ) : ℂ) := by rw [hlog]; push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, hnorm] at ht
  have hlogR : Real.log (1 + u) = Real.log x - Real.log a := by
    rw [hbase, Real.log_div hx0.ne' ha.ne']
  have hphase : chiDualSpatialSaddlePhase a x - Real.pi * (x - a) ^ 2 / a =
      -(2 * Real.pi * a) * (Real.log (1 + u) - u + u ^ 2 / 2) := by
    rw [hlogR]
    dsimp only [chiDualSpatialSaddlePhase, u]
    field_simp
    ring
  rw [hphase, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi * a)]
  calc
    _ ≤ (2 * Real.pi * a) * |u| ^ 3 := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      dsimp only [u]
      rw [abs_div, abs_of_pos ha]
      field_simp

theorem intervalIntegrable_chiDualSpatialSaddle_neg (a : ℝ) {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) :
    IntervalIntegrable (fun x => bourgainOscillation (-chiDualSpatialSaddlePhase a x))
      volume l u := by
  have hlog : ContinuousOn Real.log (uIcc l u) := by
    intro x hx
    rw [uIcc_of_le hlu] at hx
    exact (Real.continuousAt_log (hl.trans_le hx.1).ne').continuousWithinAt
  have hp : ContinuousOn (chiDualSpatialSaddlePhase a) (uIcc l u) := by
    unfold chiDualSpatialSaddlePhase
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).sub
      (continuousOn_const.mul (hlog.sub continuousOn_const)))
  have hb : Continuous bourgainOscillation := by unfold bourgainOscillation; fun_prop
  exact (hb.comp_continuousOn hp.neg).intervalIntegrable

/-- Both complete spatial exterior intervals have an inverse-distance bound. -/
theorem norm_integral_chiDualSpatialSaddle_exterior_le {a h l u : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hl : a / 2 ≤ l) (hlu : l ≤ u)
    (hu : u ≤ 2 * a) (hside : u ≤ a - h ∨ a + h ≤ l) :
    ‖∫ x in l..u, bourgainOscillation (-chiDualSpatialSaddlePhase a x)‖ ≤
      8 * a / (Real.pi * h) := by
  have hxpos (x : ℝ) (hx : x ∈ Icc l u) : 0 < x := by linarith [hx.1]
  have hd (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt (chiDualSpatialSaddlePhase a) (2 * Real.pi * (1 - a / x)) x := by
    have h := (((hasDerivAt_id x).sub_const a).sub
      (((Real.hasDerivAt_log (hxpos x hx).ne').sub_const (Real.log a)).const_mul a)).const_mul
        (2 * Real.pi)
    refine h.congr_deriv ?_
    ring
  have hd' (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt (fun y : ℝ => 2 * Real.pi * (1 - a / y)) (2 * Real.pi * a / x ^ 2) x := by
    have h := ((hasDerivAt_const x 1).sub
      ((hasDerivAt_const x a).div (hasDerivAt_id x) (hxpos x hx).ne')).const_mul (2 * Real.pi)
    refine h.congr_deriv ?_
    dsimp
    ring
  have hc : ContinuousOn (fun x : ℝ => 2 * Real.pi * a / x ^ 2) (Icc l u) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hxpos x hx).ne')
  have hb (x : ℝ) (hx : x ∈ Icc l u) : Real.pi * h / a ≤ |2 * Real.pi * (1 - a / x)| := by
    have hx0 := hxpos x hx
    have he : 2 * Real.pi * (1 - a / x) = 2 * Real.pi * (x - a) / x := by field_simp
    rw [he, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos hx0]
    have hdist : h ≤ |x - a| := by
      rcases hside with hleft | hright
      · exact (show h ≤ -(x - a) by linarith [hx.2]).trans (neg_le_abs _)
      · exact (show h ≤ x - a by linarith [hx.1]).trans (le_abs_self _)
    apply (le_div_iff₀ hx0).mpr
    have hxa : x ≤ 2 * a := hx.2.trans hu
    calc
      _ ≤ (Real.pi * h / a) * (2 * a) := mul_le_mul_of_nonneg_left hxa (by positivity)
      _ = 2 * Real.pi * h := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist (by positivity)
  have htest := firstDerivTestOn hlu (by positivity : 0 < Real.pi * h / a)
    hd hd' hc (fun x _ => hasDerivAt_const x (1 : ℂ)) continuousOn_const
    (fun x hx => by positivity : ∀ x ∈ Icc l u, 0 ≤ 2 * Real.pi * a / x ^ 2) hb
  have he (x : ℝ) : bourgainOscillation (-chiDualSpatialSaddlePhase a x) =
      (starRingEnd ℂ) (bourgainOscillation (chiDualSpatialSaddlePhase a x)) := by
    unfold bourgainOscillation
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  have hi : (∫ x in l..u, bourgainOscillation (-chiDualSpatialSaddlePhase a x)) =
      (starRingEnd ℂ) (∫ x in l..u, bourgainOscillation (chiDualSpatialSaddlePhase a x)) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun x _ => he x)
  rw [hi, Complex.norm_conj]
  simp only [one_mul, norm_one, norm_zero, intervalIntegral.integral_zero, add_zero] at htest
  calc
    _ ≤ 4 * (1 + 1) / (Real.pi * h / a) := htest
    _ = _ := by field_simp; ring

private theorem norm_integral_spatial_center_sub_quad_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2) :
    ‖(∫ x in (a - h)..(a + h), bourgainOscillation (-chiDualSpatialSaddlePhase a x)) -
      ∫ x in (a - h)..(a + h), bourgainOscillation (-Real.pi * (x - a) ^ 2 / a)‖ ≤
        4 * Real.pi * h ^ 4 / a ^ 2 := by
  have hab : a - h ≤ a + h := by linarith
  have hf := intervalIntegrable_chiDualSpatialSaddle_neg a (show 0 < a - h by linarith) hab
  have hg : IntervalIntegrable (fun x : ℝ => bourgainOscillation (-Real.pi * (x - a) ^ 2 / a))
      volume (a - h) (a + h) := by
    apply Continuous.intervalIntegrable
    unfold bourgainOscillation
    fun_prop
  rw [← intervalIntegral.integral_sub hf hg]
  have hb : ∀ x ∈ uIoc (a - h) (a + h),
      ‖bourgainOscillation (-chiDualSpatialSaddlePhase a x) -
        bourgainOscillation (-Real.pi * (x - a) ^ 2 / a)‖ ≤ 2 * Real.pi * h ^ 3 / a ^ 2 := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hdist : |x - a| ≤ h := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have ht := abs_chiDualSpatialSaddlePhase_sub_quadratic_le ha (hdist.trans hha)
    apply (norm_bourgainOscillation_sub_le _ _).trans
    have he : -chiDualSpatialSaddlePhase a x - (-Real.pi * (x - a) ^ 2 / a) =
        -(chiDualSpatialSaddlePhase a x - Real.pi * (x - a) ^ 2 / a) := by ring
    rw [he, abs_neg]
    apply ht.trans
    gcongr
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans_eq
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

private theorem norm_integral_spatial_center_sub_value_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2) :
    ‖(∫ x in (a - h)..(a + h), bourgainOscillation (-chiDualSpatialSaddlePhase a x)) -
      (Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4))‖ ≤
        4 * Real.pi * h ^ 4 / a ^ 2 + 4 * a / (Real.pi * h) := by
  let Q : ℝ → ℂ := fun x => bourgainOscillation (-Real.pi * (x - a) ^ 2 / a)
  let M : ℂ := (Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have htrans : (∫ x in (a - h)..(a + h), Q x) =
      ∫ y in (-h)..h, Complex.exp (((-((2 * Real.pi / a) * y ^ 2 / 2) : ℝ) : ℂ) * I) := by
    have he (x : ℝ) : Q x =
        (fun y : ℝ => Complex.exp (((-((2 * Real.pi / a) * y ^ 2 / 2) : ℝ) : ℂ) * I)) (x - a) := by
      dsimp only [Q, bourgainOscillation]
      congr 1
      push_cast
      ring
    rw [intervalIntegral.integral_congr (fun x _ => he x),
      intervalIntegral.integral_comp_sub_right
        (fun y : ℝ => Complex.exp (((-((2 * Real.pi / a) * y ^ 2 / 2) : ℝ) : ℂ) * I)) a]
    congr 1 <;> ring
  have hquad : ‖(∫ x in (a - h)..(a + h), Q x) - M‖ ≤ 4 * a / (Real.pi * h) := by
    have hfres := GaloisForLFunctions.RHTower.norm_integral_quadPhase_conj_sub_le
      (by positivity : 0 < 2 * Real.pi / a) hh
    have hm : (Real.sqrt (2 * Real.pi / (2 * Real.pi / a)) : ℂ) *
        Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I) = M := by
      have he : 2 * Real.pi / (2 * Real.pi / a) = a := by field_simp
      rw [he]
      dsimp only [M, bourgainOscillation]
      congr 1
      congr 1
      ring
    rw [htrans, ← hm]
    apply hfres.trans_eq
    field_simp
    ring
  have hc := norm_integral_spatial_center_sub_quad_le ha hh hha
  calc
    _ = ‖((∫ x in (a - h)..(a + h), bourgainOscillation (-chiDualSpatialSaddlePhase a x)) -
        ∫ x in (a - h)..(a + h), Q x) + ((∫ x in (a - h)..(a + h), Q x) - M)‖ := by
      congr 1
      dsimp only [M]
      ring
    _ ≤ ‖(∫ x in (a - h)..(a + h), bourgainOscillation (-chiDualSpatialSaddlePhase a x)) -
        ∫ x in (a - h)..(a + h), Q x‖ + ‖(∫ x in (a - h)..(a + h), Q x) - M‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hc hquad

/-- Full stationary leading term for the literal centered spatial log phase. Every
finite pre-saddle and post-saddle segment is retained with an explicit error. -/
theorem norm_integral_chiDualSpatialSaddle_sub_stationary_value_le {a h l u : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, bourgainOscillation (-chiDualSpatialSaddlePhase a t)) -
      (Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4))‖ ≤
        4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h) := by
  let f : ℝ → ℂ := fun t => bourgainOscillation (-chiDualSpatialSaddlePhase a t)
  let M : ℂ := (Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have hl0 : 0 < l := by linarith
  have hc0 : 0 < a - h := by linarith
  have hc : a - h ≤ a + h := by linarith
  have hi1 := intervalIntegrable_chiDualSpatialSaddle_neg a hl0 hlh
  have hi2 := intervalIntegrable_chiDualSpatialSaddle_neg a hc0 hc
  have hi3 := intervalIntegrable_chiDualSpatialSaddle_neg a (show 0 < a + h by linarith) hhu
  have hi12 := intervalIntegrable_chiDualSpatialSaddle_neg a hl0 (show l ≤ a + h by linarith)
  have hsplit : (∫ t in l..u, f t) = (∫ t in l..(a - h), f t) +
      (∫ t in (a - h)..(a + h), f t) + (∫ t in (a + h)..u, f t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi12 hi3,
      ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hleft := norm_integral_chiDualSpatialSaddle_exterior_le ha hh hl hlh
    (show a - h ≤ 2 * a by linarith) (Or.inl (le_refl _))
  have hright := norm_integral_chiDualSpatialSaddle_exterior_le ha hh
    (show a / 2 ≤ a + h by linarith) hhu hu (Or.inr (le_refl _))
  have hcenter := norm_integral_spatial_center_sub_value_le ha hh hha
  change ‖(∫ t in l..u, f t) - M‖ ≤ _
  rw [hsplit]
  have he : (∫ t in l..(a - h), f t) + (∫ t in (a - h)..(a + h), f t) +
      (∫ t in (a + h)..u, f t) - M =
      ((∫ t in l..(a - h), f t) + ((∫ t in (a - h)..(a + h), f t) - M)) +
        (∫ t in (a + h)..u, f t) := by ring
  rw [he]
  have htri := (norm_add_le ((∫ t in l..(a - h), f t) +
    ((∫ t in (a - h)..(a + h), f t) - M)) (∫ t in (a + h)..u, f t)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  apply htri.trans
  change ‖∫ t in l..(a - h), f t‖ + ‖(∫ t in (a - h)..(a + h), f t) - M‖ +
      ‖∫ t in (a + h)..u, f t‖ ≤ _
  calc
    _ ≤ 8 * a / (Real.pi * h) + (4 * Real.pi * h ^ 4 / a ^ 2 + 4 * a / (Real.pi * h)) + 8 * a / (Real.pi * h) :=
      add_le_add (add_le_add hleft hcenter) hright
    _ = _ := by ring


/-- The spatial phase kernel is continuous at every positive spatial point. -/
theorem continuousAt_chiDualSpatialSaddle_neg (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y => bourgainOscillation (-chiDualSpatialSaddlePhase a y)) x := by
  have hlog := Real.continuousAt_log hx.ne'
  unfold bourgainOscillation chiDualSpatialSaddlePhase
  fun_prop

/-- Complex amplitude variation preserves the complete spatial exterior bound. -/
theorem norm_integral_complexAmplitude_mul_spatial_exterior_le
    {a h l u : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hl : a / 2 ≤ l) (hlu : l ≤ u) (hu : u ≤ 2 * a)
    (hside : u ≤ a - h ∨ a + h ≤ l) {v v' : ℝ → ℂ}
    (hv : ∀ x ∈ uIcc l u, HasDerivAt v (v' x) x)
    (hv' : IntervalIntegrable v' volume l u) :
    ‖∫ x in l..u, v x * bourgainOscillation (-chiDualSpatialSaddlePhase a x)‖ ≤
      (8 * a / (Real.pi * h)) * (‖v u‖ + ∫ x in l..u, ‖v' x‖) := by
  let g : ℝ → ℂ := fun x => bourgainOscillation (-chiDualSpatialSaddlePhase a x)
  let G : ℝ → ℂ := fun x => ∫ y in l..x, g y
  have hl0 : 0 < l := by linarith
  have hg : ContinuousOn g (Ioi (0 : ℝ)) :=
    fun x hx => (continuousAt_chiDualSpatialSaddle_neg a hx).continuousWithinAt
  apply norm_integral_complexAmplitude_mul_deriv_le hlu hv (v := G) (v' := g)
  · intro x hx
    rw [uIcc_of_le hlu] at hx
    have hx0 : 0 < x := hl0.trans_le hx.1
    exact intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_chiDualSpatialSaddle_neg a hl0 hx.1)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hg x hx0)
      (continuousAt_chiDualSpatialSaddle_neg a hx0)
  · exact hv'
  · exact intervalIntegrable_chiDualSpatialSaddle_neg a hl0 hlu
  · exact intervalIntegral.integral_same
  · intro x hx
    have hs : x ≤ a - h ∨ a + h ≤ l := by
      rcases hside with hs | hs
      · exact Or.inl (hx.2.trans hs)
      · exact Or.inr hs
    exact norm_integral_chiDualSpatialSaddle_exterior_le ha hh hl hx.1 (hx.2.trans hu) hs

/-- Freezing a complex amplitude at the actual saddle pays a central
Lipschitz cost and both complete exterior variation costs. -/
theorem norm_integral_spatial_amplitude_sub_saddle_le
    {a h l u L : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a)
    (hL : 0 ≤ L) {v v' : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc l u, HasDerivAt v (v' t) t)
    (hvi : IntervalIntegrable v' volume l u)
    (hvL : ∀ t ∈ Set.Icc l u, ‖v' t‖ ≤ L) :
    ‖∫ t in l..u, (v t - v a) *
      bourgainOscillation (-chiDualSpatialSaddlePhase a t)‖ ≤
      2 * L * h ^ 2 + 20 * L * a ^ 2 / (Real.pi * h) := by
  have hlu : l ≤ u := by linarith
  have haI : a ∈ Set.Icc l u := ⟨by linarith, by linarith⟩
  have hLip (t : ℝ) (ht : t ∈ Set.Icc l u) : ‖v t - v a‖ ≤ L * |t - a| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hv x hx).hasDerivWithinAt) hvL (convex_Icc l u) haI ht
  let g : ℝ → ℂ := fun t => bourgainOscillation (-chiDualSpatialSaddlePhase a t)
  let f : ℝ → ℂ := fun t => (v t - v a) * g t
  have hg : ContinuousOn g (Set.Icc l u) := by
    intro x hx
    exact (continuousAt_chiDualSpatialSaddle_neg a (by linarith [hx.1])).continuousWithinAt
  have hvC : ContinuousOn v (Set.Icc l u) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hfC : ContinuousOn f (Set.Icc l u) := (hvC.sub continuousOn_const).mul hg
  have hsub {b c : ℝ} (hb : l ≤ b) (hc : c ≤ u) : Set.Icc b c ⊆ Set.Icc l u :=
    fun _ hx => ⟨hb.trans hx.1, hx.2.trans hc⟩
  have hfInt {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      IntervalIntegrable f volume b c :=
    ContinuousOn.intervalIntegrable_of_Icc hbc (hfC.mono (hsub hb hc))
  have hvInt {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      IntervalIntegrable v' volume b c := by
    apply hvi.mono_set
    rw [Set.uIcc_of_le hbc, Set.uIcc_of_le hlu]
    exact hsub hb hc
  have hvar {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      (∫ t in b..c, ‖v' t‖) ≤ L * (c - b) := by
    have hi := intervalIntegral.integral_mono_on hbc (hvInt hbc hb hc).norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume b c)
      (fun t ht => hvL t (hsub hb hc ht))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi
  have hvSub {b c : ℝ} (hbc : b ≤ c) (hb : l ≤ b) (hc : c ≤ u) :
      ∀ t ∈ Set.uIcc b c, HasDerivAt (fun x => v x - v a) (v' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hbc] at ht
    exact (hv t (hsub hb hc ht)).sub_const (v a)
  have hleft : ‖∫ t in l..(a - h), f t‖ ≤ (8 * a / (Real.pi * h)) * (L * a / 2) := by
    have hb := norm_integral_complexAmplitude_mul_spatial_exterior_le
      ha hh hl hlh (show a - h ≤ 2 * a by linarith) (Or.inl le_rfl)
      (hvSub hlh le_rfl (by linarith)) (hvInt hlh le_rfl (by linarith))
    have hp := hLip (a - h) ⟨hlh, by linarith⟩
    have he : |(a - h) - a| = h := by
      rw [show (a - h) - a = -h by ring, abs_neg, abs_of_pos hh]
    rw [he] at hp
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hvb := hvar hlh le_rfl (show a - h ≤ u by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hl hL]
  have hright : ‖∫ t in (a + h)..u, f t‖ ≤ (8 * a / (Real.pi * h)) * (2 * L * a) := by
    have hb := norm_integral_complexAmplitude_mul_spatial_exterior_le
      ha hh (show a / 2 ≤ a + h by linarith) hhu hu (Or.inr le_rfl)
      (hvSub hhu (by linarith) le_rfl) (hvInt hhu (by linarith) le_rfl)
    have hp := hLip u ⟨hlu, le_rfl⟩
    rw [abs_of_nonneg (show 0 ≤ u - a by linarith)] at hp
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hvb := hvar hhu (show l ≤ a + h by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hu hL, mul_nonneg hL hh.le]
  have hcenter : ‖∫ t in (a - h)..(a + h), f t‖ ≤ 2 * L * h ^ 2 := by
    have hb : ‖∫ t in (a - h)..(a + h), f t‖ ≤ (L * h) * |(a + h) - (a - h)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le (by linarith : a - h ≤ a + h)] at ht
      dsimp only [f, g]
      rw [norm_mul, norm_bourgainOscillation, mul_one]
      apply (hLip t ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) hL
    apply hb.trans_eq
    rw [abs_of_nonneg (by linarith : 0 ≤ (a + h) - (a - h))]
    ring
  have hsplit : (∫ t in l..u, f t) = (∫ t in l..(a - h), f t) +
      (∫ t in (a - h)..(a + h), f t) + (∫ t in (a + h)..u, f t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfInt (by linarith : l ≤ a + h) le_rfl hhu) (hfInt hhu (by linarith) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hfInt hlh le_rfl (by linarith)) (hfInt (by linarith) hlh hhu)]
  change ‖∫ t in l..u, f t‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖∫ t in l..(a - h), f t‖ + ‖∫ t in (a - h)..(a + h), f t‖ +
        ‖∫ t in (a + h)..u, f t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (8 * a / (Real.pi * h)) * (L * a / 2) + 2 * L * h ^ 2 +
        (8 * a / (Real.pi * h)) * (2 * L * a) := add_le_add (add_le_add hleft hcenter) hright
    _ = _ := by ring

/-- Full model stationary value with the literal complex amplitude at the
saddle and an explicit cost for its spatial variation. -/
theorem norm_integral_spatial_complexAmplitude_sub_stationary_le
    {a h l u L : ℝ} (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a)
    (hL : 0 ≤ L) {v v' : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc l u, HasDerivAt v (v' t) t)
    (hvi : IntervalIntegrable v' volume l u)
    (hvL : ∀ t ∈ Set.Icc l u, ‖v' t‖ ≤ L) :
    ‖(∫ t in l..u, v t * bourgainOscillation (-chiDualSpatialSaddlePhase a t)) -
      v a * ((Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4)))‖ ≤
      2 * L * h ^ 2 + 20 * L * a ^ 2 / (Real.pi * h) +
      ‖v a‖ * (4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h)) := by
  have hlu : l ≤ u := by linarith
  let g : ℝ → ℂ := fun t => bourgainOscillation (-chiDualSpatialSaddlePhase a t)
  let M : ℂ := (Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have hg : ContinuousOn g (Set.Icc l u) := by
    intro x hx
    exact (continuousAt_chiDualSpatialSaddle_neg a (by linarith [hx.1])).continuousWithinAt
  have hgInt : IntervalIntegrable g volume l u :=
    intervalIntegrable_chiDualSpatialSaddle_neg a (by linarith) hlu
  have hvC : ContinuousOn v (Set.Icc l u) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hprod : IntervalIntegrable (fun t => v t * g t) volume l u :=
    ContinuousOn.intervalIntegrable_of_Icc hlu (hvC.mul hg)
  have heq : (∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t) =
      ∫ t in l..u, (v t - v a) * g t := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hprod (hgInt.const_mul (v a))]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hfreeze := norm_integral_spatial_amplitude_sub_saddle_le
    ha hh hl hlh hhu hu hL hv hvi hvL
  have hmodel := norm_integral_chiDualSpatialSaddle_sub_stationary_value_le ha hh hha hl hlh hhu hu
  change ‖(∫ t in l..u, v t * g t) - v a * M‖ ≤ _
  calc
    _ = ‖((∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t)) +
        v a * ((∫ t in l..u, g t) - M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, v t * g t) - v a * (∫ t in l..u, g t)‖ +
        ‖v a * ((∫ t in l..u, g t) - M)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [heq, norm_mul]
      exact add_le_add hfreeze (mul_le_mul_of_nonneg_left hmodel (norm_nonneg _))



/-- The literal negative first Fourier mode has its actual saddle amplitude
and complete central/exterior error, uniformly on each fixed compact disc.
All amplitude bounds are derived from the Gaussian cutoff and complex power. -/
theorem exists_chiDualSpatial_first_mode_stationary_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ a : ℝ, 0 < a → N ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * N →
      ∀ h l u : ℝ, 0 < h → h ≤ a / 2 →
      N / 5 - 1 / 2 ≤ l → u ≤ 6 * N / 25 + 1 / 2 → l ≤ a - h → a + h ≤ u →
      ‖(∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
          Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))) -
        (chiDualSpatialSlowAmplitude s N a *
          ((Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4)))) *
          Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ))‖ ≤
        C * N ^ (s.re - 1) * (2 * h ^ 2 / N + 20 * a ^ 2 / (N * Real.pi * h) +
          4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h)) := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualSpatialSlowJets_bound c r
  refine ⟨C, hC, ?_⟩
  intro s hs N hN a ha ht h l u hh hha hl hu hlh hhu
  have hN0 : 0 < N := by linarith
  have hlu : l ≤ u := by linarith
  have hxx (x : ℝ) (hx : x ∈ Icc l u) :
      N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 :=
    ⟨hl.trans hx.1, hx.2.trans hu⟩
  have hxdata (x : ℝ) (hx : x ∈ Icc l u) : 0 < x ∧ x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    obtain ⟨hx0, hxlo, hxhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx x hx)
    refine ⟨hx0, ?_, ?_⟩
    · apply (le_div_iff₀ hN0).mpr
      linarith
    · apply (div_le_iff₀ hN0).mpr
      linarith
  obtain ⟨_, hllo, _, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx l ⟨le_rfl, hlu⟩)
  obtain ⟨_, _, huhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx u ⟨hlu, le_rfl⟩)
  have hlcomp : a / 2 ≤ l := by nlinarith [Real.pi_gt_three, ht.2]
  have hucomp : u ≤ 2 * a := by nlinarith [Real.pi_lt_four, ht.1]
  let U : ℝ := C * N ^ (s.re - 1)
  have hU : 0 ≤ U := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hv : ∀ x ∈ Icc l u, HasDerivAt (chiDualSpatialSlowAmplitude s N)
      (chiDualSpatialSlowFirst s N x) x :=
    fun x hx => hasDerivAt_chiDualSpatialSlowAmplitude s hN0 (hxdata x hx).1
  have hvi : IntervalIntegrable (chiDualSpatialSlowFirst s N) volume l u := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_chiDualSpatialSlowJets s hN0).2.1.mono
    intro x hx
    rw [uIcc_of_le hlu] at hx
    exact (hxdata x hx).1
  have hvL : ∀ x ∈ Icc l u, ‖chiDualSpatialSlowFirst s N x‖ ≤ U / N :=
    fun x hx => (hb s hs N hN0 x (hxdata x hx).2).2.1
  have haa : a ∈ Icc l u := ⟨by linarith, by linarith⟩
  have hA := (hb s hs N hN0 a (hxdata a haa).2).1
  have hm := norm_integral_spatial_complexAmplitude_sub_stationary_le ha hh hha
    hlcomp hlh hhu hucomp (div_nonneg hU hN0.le) hv hvi hvL
  let E : ℂ := Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ))
  have hE : ‖E‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hphase (x : ℝ) :
      Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ)) =
        bourgainOscillation (-chiDualSpatialSaddlePhase a x) * E := by
    dsimp only [bourgainOscillation, E]
    rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add]
    have he := chiDualSpatialPhase_sub_saddle a x
    have hp : chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x =
        -chiDualSpatialSaddlePhase a x +
          chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a := by linarith only [he]
    rw [hp]
  have hi : (∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
      Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))) =
      (∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
        bourgainOscillation (-chiDualSpatialSaddlePhase a x)) * E := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [hphase]
    ring
  rw [hi, ← sub_mul, norm_mul, hE, mul_one]
  apply hm.trans
  calc
    _ ≤ 2 * (U / N) * h ^ 2 + 20 * (U / N) * a ^ 2 / (Real.pi * h) +
        U * (4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h)) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by dsimp only [U]; ring

end RHTower
