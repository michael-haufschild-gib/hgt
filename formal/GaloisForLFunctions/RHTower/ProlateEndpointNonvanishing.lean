import GaloisForLFunctions.RHTower.ProlateRadialODEBridge
import GaloisForLFunctions.RHTower.ProlateEndpointLowerBound

/-!
# Nonvanishing of regular prolate modes at the singular endpoint

The endpoint `x = 1` is regular-singular, so the ordinary solved-form ODE uniqueness theorem does
not apply there.  The Sturm--Liouville flux identity nevertheless gives uniqueness directly.  If a
smooth solution vanishes at `1`, then its endpoint derivative vanishes too.  On a sufficiently short
left neighbourhood, the flux identity bounds the derivative by a strict contraction times the
maximum of the solution.  Hence the solution vanishes locally.  Standard interior ODE uniqueness
then propagates that vanishing across `(-1,1)`.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace RHTower

/-- Interior uniqueness for the prolate equation, based at an arbitrary regular point. -/
theorem eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq_at
    {c chi x0 : ℝ} {Phi Psi : ℝ → ℝ}
    (hx0 : x0 ∈ Ioo (-1 : ℝ) 1)
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi))
    (hPsi1 : Differentiable ℝ Psi) (hPsi2 : Differentiable ℝ (deriv Psi))
    (hPhiEig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiEig : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x)
    (hvalue : Phi x0 = Psi x0) (hderiv : deriv Phi x0 = deriv Psi x0) :
    Set.EqOn Phi Psi (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  let r : ℝ := (max |x| |x0| + 1) / 2
  have hxabs : |x| < 1 := (abs_lt).2 hx
  have hx0abs : |x0| < 1 := (abs_lt).2 hx0
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    have hmaxlt : max |x| |x0| < 1 := max_lt hxabs hx0abs
    dsimp [r]
    linarith
  have hxmem : x ∈ Set.Ioo (-r) r := by
    exact (abs_lt).1 (by dsimp [r]; linarith [le_max_left |x| |x0|])
  have hx0mem : x0 ∈ Set.Ioo (-r) r := by
    exact (abs_lt).1 (by dsimp [r]; linarith [le_max_right |x| |x0|])
  have hstateEq : prolateODEState Phi x0 = prolateODEState Psi x0 := by
    ext <;> simp [prolateODEState, hvalue, hderiv]
  have hstates : Set.EqOn (prolateODEState Phi) (prolateODEState Psi) (Set.Ioo (-r) r) := by
    apply ODE_solution_unique_of_mem_Ioo
      (K := Real.toNNReal
        (1 + (|chi| + c ^ 2 * r ^ 2 + 2 * r) / (1 - r ^ 2)))
      (v := prolateODEField c chi) (s := fun _ => Set.univ) (t₀ := x0)
    · intro t ht
      exact (lipschitzWith_prolateODEField hr0 hr1
        (abs_lt.mpr ht).le).lipschitzOnWith
    · exact hx0mem
    · intro t ht
      exact ⟨hasDerivAt_prolateODEState hPhi1 hPhi2 hPhiEig
        ⟨lt_trans (by linarith [hr1]) ht.1, lt_trans ht.2 hr1⟩, Set.mem_univ _⟩
    · intro t ht
      exact ⟨hasDerivAt_prolateODEState hPsi1 hPsi2 hPsiEig
        ⟨lt_trans (by linarith [hr1]) ht.1, lt_trans ht.2 hr1⟩, Set.mem_univ _⟩
    · exact hstateEq
  exact congrArg Prod.fst (hstates hxmem)

/-- A smooth global prolate solution which vanishes at the regular-singular endpoint vanishes on
the entire aperture. -/
theorem eq_zero_on_Ioo_of_prolateSLAction_eq_of_value_one_eq_zero
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hone : Phi 1 = 0) :
    Set.EqOn Phi (fun _ : ℝ => 0) (Set.Ioo (-1 : ℝ) 1) := by
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  let K : ℝ := |chi| + c ^ 2
  let delta : ℝ := 1 / (2 * (K + 1))
  let b : ℝ := 1 - delta
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hdelta0 : 0 < delta := by dsimp [delta]; positivity
  have hdeltahalf : delta ≤ 1 / 2 := by
    dsimp [delta]
    rw [div_le_iff₀ (by positivity : 0 < 2 * (K + 1))]
    nlinarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hb_le_one : b ≤ 1 := hb1.le
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hb_le_one) hPhi1.continuous.abs.continuousOn
  have hM0 : 0 ≤ |Phi x0| := abs_nonneg _
  have hPhiBound : ∀ t ∈ Icc b 1, |Phi t| ≤ |Phi x0| := by
    intro t ht
    exact isMaxOn_iff.mp hmax t ht
  have hcoeff : ∀ t ∈ Icc b 1, |chi + c ^ 2 * t ^ 2| ≤ K := by
    intro t ht
    have htneg : -1 ≤ t := by linarith [hb0, ht.1]
    have htsq : t ^ 2 ≤ 1 := by nlinarith [ht.2]
    calc
      |chi + c ^ 2 * t ^ 2| ≤ |chi| + |c ^ 2 * t ^ 2| := abs_add_le _ _
      _ = |chi| + c ^ 2 * t ^ 2 := by
        have habs : |c ^ 2 * t ^ 2| = c ^ 2 * t ^ 2 := abs_of_nonneg (by positivity)
        rw [habs]
      _ ≤ K := by dsimp [K]; nlinarith [sq_nonneg c]
  have hderivBound : ∀ y ∈ Icc b 1, |deriv Phi y| ≤ K * |Phi x0| := by
    intro y hy
    rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · have hend := two_mul_deriv_one_eq_of_prolateSLAction_eq (heig 1)
      rw [hone] at hend
      simp only [mul_zero] at hend
      have : deriv Phi 1 = 0 := by linarith
      rw [this, abs_zero]
      positivity
    · have hyband : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hb0, hy.1], hy.2⟩
      have hflux := GaloisForLFunctions.RHTower.prolateFlux_eq_neg_integral
        hsm (fun t _ => heig t) hyband
      have hintegrand : ∀ t ∈ Icc y 1,
          |(chi + c ^ 2 * t ^ 2) * Phi t| ≤ K * |Phi x0| := by
        intro t ht
        have htwindow : t ∈ Icc b 1 := ⟨le_trans hy.1 ht.1, ht.2⟩
        rw [abs_mul]
        exact mul_le_mul (hcoeff t htwindow) (hPhiBound t htwindow)
          (abs_nonneg _) hK0
      have hintBound :
          |∫ t in y..1, (chi + c ^ 2 * t ^ 2) * Phi t|
            ≤ (1 - y) * (K * |Phi x0|) := by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun t : ℝ => (chi + c ^ 2 * t ^ 2) * Phi t)
          (C := K * |Phi x0|)
          (fun t ht => hintegrand t (by
            rw [← uIcc_of_le hy.2]
            exact uIoc_subset_uIcc ht))
        simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.2), mul_comm] using hnorm
      have hfluxBound :
          |(1 - y ^ 2) * deriv Phi y| ≤ (1 - y) * (K * |Phi x0|) := by
        rw [← GaloisForLFunctions.RHTower.prolateFlux]
        rw [hflux, abs_neg]
        exact hintBound
      have hyplus : 1 ≤ 1 + y := by linarith [hb0, hy.1]
      have hyminus : 0 < 1 - y := sub_pos.mpr hy1
      have hweight : 0 ≤ 1 - y ^ 2 := by nlinarith [hb0, hy.1, hy.2]
      rw [abs_mul, abs_of_nonneg hweight] at hfluxBound
      have hfactor : 1 - y ^ 2 = (1 - y) * (1 + y) := by ring
      rw [hfactor] at hfluxBound
      have hcancel : (1 + y) * |deriv Phi y| ≤ K * |Phi x0| := by
        nlinarith [hfluxBound]
      exact le_trans (by nlinarith [abs_nonneg (deriv Phi y)]) hcancel
  have hpointBound : ∀ x ∈ Icc b 1,
      |Phi x| ≤ (1 - x) * (K * |Phi x0|) := by
    intro x hx
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := Phi) (f' := fun y => deriv Phi y) (fun y _ => (hPhi1 y).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hsm).2.continuous.intervalIntegrable x 1)
    have hIntBound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ => deriv Phi y) (C := K * |Phi x0|)
      (fun y hy => by
        simpa [Real.norm_eq_abs] using hderivBound y
          (by
            have hy' : y ∈ Icc x 1 := by
              rw [← uIcc_of_le hx.2]
              exact uIoc_subset_uIcc hy
            exact ⟨le_trans hx.1 hy'.1, hy'.2⟩))
    rw [hFTC, hone, zero_sub] at hIntBound
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.2), mul_comm] using hIntBound
  have hstrict : delta * K < 1 := by
    dsimp [delta]
    rw [div_mul_eq_mul_div, div_lt_one (by positivity : 0 < 2 * (K + 1))]
    nlinarith
  have hx0b : b ≤ x0 := hx0.1
  have hx01 : x0 ≤ 1 := hx0.2
  have hx0width : 1 - x0 ≤ delta := by dsimp [b] at hx0b; linarith
  have hself : |Phi x0| ≤ (delta * K) * |Phi x0| := by
    calc
      |Phi x0| ≤ (1 - x0) * (K * |Phi x0|) := hpointBound x0 hx0
      _ ≤ delta * (K * |Phi x0|) := by
        exact mul_le_mul_of_nonneg_right hx0width (mul_nonneg hK0 hM0)
      _ = (delta * K) * |Phi x0| := by ring
  have hMzero : |Phi x0| = 0 := by
    by_contra hne
    have hMpos : 0 < |Phi x0| := lt_of_le_of_ne hM0 (Ne.symm hne)
    have hcontra : (delta * K) * |Phi x0| < 1 * |Phi x0| :=
      mul_lt_mul_of_pos_right hstrict hMpos
    nlinarith [hself]
  have hzeroWindow : Set.EqOn Phi (fun _ : ℝ => 0) (Icc b 1) := by
    intro x hx
    have hxabs := hPhiBound x hx
    rw [hMzero] at hxabs
    simpa using abs_eq_zero.mp (le_antisymm hxabs (abs_nonneg _))
  let y0 : ℝ := (b + 1) / 2
  have hy0open : y0 ∈ Ioo b 1 := by dsimp [y0]; constructor <;> linarith
  have hy0band : y0 ∈ Ioo (-1 : ℝ) 1 := by
    exact ⟨by linarith [hb0, hy0open.1], hy0open.2⟩
  have hy0value : Phi y0 = 0 := hzeroWindow ⟨hy0open.1.le, hy0open.2.le⟩
  have hlocal : Phi =ᶠ[nhds y0] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy0open] with y hy
    exact hzeroWindow ⟨hy.1.le, hy.2.le⟩
  have hy0deriv : deriv Phi y0 = deriv (fun _ : ℝ => 0) y0 := hlocal.deriv_eq
  have hzeroEig : ∀ x : ℝ,
      prolateSLAction c (fun _ : ℝ => 0) x = chi * (fun _ : ℝ => 0) x := by
    intro x
    simp [prolateSLAction]
  exact eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq_at hy0band
    hPhi1 hPhi2 (by fun_prop) (by fun_prop) heig hzeroEig
    (by simpa using hy0value) (by simpa using hy0deriv)

/-- Every nonzero global joint band/prolate eigenfunction is nonzero at `x = 1`. -/
theorem value_one_ne_of_joint_prolate_band_eigen
    {c lam chi : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    Phi 1 ≠ 0 := by
  intro hone
  have hzeroIoo := eq_zero_on_Ioo_of_prolateSLAction_eq_of_value_one_eq_zero hsm heig hone
  have hzeroIcc : Set.EqOn Phi (fun _ : ℝ => 0) (Set.Icc (-1 : ℝ) 1) := by
    have hclosure : closure (Set.Ioo (-1 : ℝ) 1) = Set.Icc (-1 : ℝ) 1 :=
      closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)
    rw [← hclosure]
    exact hzeroIoo.closure hsm.continuous continuous_const
  have hbandZero : ∀ x : ℝ, bandTransform c Phi x = 0 := by
    intro x
    unfold bandTransform
    calc
      (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * Phi y)
          = ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * 0 := by
              refine intervalIntegral.integral_congr fun y hy => ?_
              rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
              rw [hzeroIcc hy]
      _ = 0 := by simp
  apply hne
  funext x
  have hx := hband x
  rw [hbandZero x] at hx
  exact (mul_eq_zero.mp hx.symm).resolve_left hlam

/-- Signed modes have a regular radial representative with nonzero endpoint value. -/
theorem exists_global_even_radialProlate_endpoint_ne_zero_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Phi : ℝ → ℝ) (chi s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
        Phi ≠ 0 ∧ Function.Even Phi ∧ Phi 1 ≠ 0 ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ 2) Phi x =
            evenProlateSignedValue a n ^ 2 * Phi x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ 2) Phi x = chi * Phi x) ∧
        s = radialSeparationRatio (2 * Real.pi * a ^ 2) chi ∧
        0 ≤ s ∧
        2 * deriv Phi 1 =
          (s * (2 * Real.pi * a ^ 2) ^ 2 - (2 * Real.pi * a ^ 2) ^ 2) * Phi 1 ∧
        (∀ x : ℝ,
          (x ^ 2 - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
            - (s * (2 * Real.pi * a ^ 2) ^ 2
                - (2 * Real.pi * a ^ 2) ^ 2 * x ^ 2) * Phi x = 0) := by
  obtain ⟨Phi, chi, s, hsm, hne, heven, hband, heig, hs, hs0, hend, hradial⟩ :=
    exists_global_even_radialProlate_of_signedMode ha n hvalue
  have hendpoint := value_one_ne_of_joint_prolate_band_eigen hsm hne
    (pow_ne_zero 2 hvalue) hband heig
  exact ⟨Phi, chi, s, hsm, hne, heven, hendpoint, hband, heig, hs, hs0, hend, hradial⟩

end RHTower

end
