import GaloisForLFunctions.ArithmeticCriticalityTheory.SmoothPlateauFamily

/-!
# Comparison of the two-sided energies under pointwise control of the profile differences

The same-side and reflected difference energies of the shifted ground state `ω_a` are integrals
of `m_a(x) m_a(y) (u(x) − u(y))²` against nonnegative measures. Hence a pointwise inequality

    (w(x) − w(y))² ≤ α (u(x) − u(y))² + β (v(x) − v(y))²

between three profiles transfers to the energies, `S(w) ≤ α S(u) + β S(v)` and
`D(w) ≤ α D(u) + β D(v)`. With Young's inequality `(A − cB)² ≤ (1+ε)A² + (1+1/ε)c²B²` this
controls the energies of `u − c v` by those of `u` and `v`.

The same-side energy of a Lipschitz plateau profile (`u = 1` on `[−L, L]`, Lipschitz constant
`Λ`) is at most a constant times `Λ² e^{−8L}`: its jump vanishes unless `x + t > L`, where
`m_a(x+t) ≤ C e^{16a} e^{−16(x+t)}` and `(u(x) − u(x+t))² ≤ Λ² t²`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Young's inequality for a difference -/

theorem young_sq_sub {ε : ℝ} (hε : 0 < ε) (A B c : ℝ) :
    (A - c * B) ^ 2 ≤ (1 + ε) * A ^ 2 + (1 + ε⁻¹) * c ^ 2 * B ^ 2 := by
  have hinv : ε * ε⁻¹ * c ^ 2 * B ^ 2 = c ^ 2 * B ^ 2 := by
    rw [mul_inv_cancel₀ hε.ne', one_mul]
  have hmul : ε * (A - c * B) ^ 2 ≤ ε * ((1 + ε) * A ^ 2 + (1 + ε⁻¹) * c ^ 2 * B ^ 2) := by
    nlinarith [sq_nonneg (ε * A + c * B), hinv]
  exact le_of_mul_le_mul_left hmul hε

/-! ### Integrability of the jumps in the space variable -/

theorem integrableOn_sameSideJump_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (a t : ℝ) :
    IntegrableOn (fun x => sameSideGroundJump (shiftedGroundState a) u t x) (Ioi 0) := by
  have hg : Continuous fun x => shiftDifference a x * shiftDifference a (x + t) :=
    (continuous_shiftDifference a).mul
      ((continuous_shiftDifference a).comp (continuous_id.add continuous_const))
  refine (integrableOn_continuous_mul_sq hg (hu.sub (hu.comp (continuous_id.add continuous_const)))
    (hasCompactSupport_sub_translate huc t) (Ioi 0)).congr_fun (fun x _ => ?_) measurableSet_Ioi
  show shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2 =
    sameSideGroundJump (shiftedGroundState a) u t x
  rw [sameSideGroundJump_shiftedGroundState]

theorem integrableOn_reflectedDifferenceJump_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (a t : ℝ) :
    IntegrableOn (fun x => reflectedDifferenceJump (shiftedGroundState a) u t x) (Ioo 0 t) := by
  have hc : Continuous fun x => reflectedDifferenceJump (shiftedGroundState a) u t x := by
    unfold reflectedDifferenceJump
    exact ((((continuous_riemannKernelReal).mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      (contDiff_shiftedGroundState a).continuous).mul
      ((contDiff_shiftedGroundState a).continuous.comp (continuous_const.sub continuous_id))).mul
      ((hu.sub (hu.comp (continuous_const.sub continuous_id))).pow 2)
  exact (hc.integrableOn_Icc (a := 0) (b := t)).mono_set Ioo_subset_Icc_self

/-! ### Transfer of pointwise inequalities to the energies -/

theorem sameSideEnergy_le_combination {a : ℝ} (ha : 0 < a) {u v w : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) {α β : ℝ}
    (h : ∀ x y, (w x - w y) ^ 2 ≤ α * (u x - u y) ^ 2 + β * (v x - v y) ^ 2) :
    sameSideEnergy (shiftedGroundState a) w ≤
      α * sameSideEnergy (shiftedGroundState a) u + β * sameSideEnergy (shiftedGroundState a) v := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadu := foldedAdmissible_shiftedGroundState ha hu huc
  have hadv := foldedAdmissible_shiftedGroundState ha hv hvc
  have hadw := foldedAdmissible_shiftedGroundState ha hw hwc
  have hI : ∀ t, 0 ≤ t →
      (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) w t x) ≤
        α * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
          β * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) v t x := by
    intro t ht
    have hJu := integrableOn_sameSideJump_shiftedGroundState hu.continuous huc a t
    have hJv := integrableOn_sameSideJump_shiftedGroundState hv.continuous hvc a t
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hJu.const_mul α) (hJv.const_mul β)]
    refine setIntegral_mono_on (integrableOn_sameSideJump_shiftedGroundState hw.continuous hwc a t)
      ((hJu.const_mul α).add (hJv.const_mul β)) measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    simp only [sameSideGroundJump_shiftedGroundState]
    have hm : 0 ≤ shiftDifference a x * shiftDifference a (x + t) :=
      mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
        (shiftDifference_nonneg_of_nonneg ha.le (by linarith))
    calc shiftDifference a x * shiftDifference a (x + t) * (w x - w (x + t)) ^ 2
        ≤ shiftDifference a x * shiftDifference a (x + t) *
          (α * (u x - u (x + t)) ^ 2 + β * (v x - v (x + t)) ^ 2) :=
          mul_le_mul_of_nonneg_left (h x (x + t)) hm
      _ = _ := by ring
  have hA : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) w t x) ≤
      α * (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
      β * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) v t x := by
    have hAu := integrableOn_archLevy_mul_sameSideIntegral hωc hu.continuous hpos hadu
    have hAv := integrableOn_archLevy_mul_sameSideIntegral hωc hv.continuous hpos hadv
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hAu.const_mul α) (hAv.const_mul β)]
    refine setIntegral_mono_on (integrableOn_archLevy_mul_sameSideIntegral hωc hw.continuous hpos hadw)
      ((hAu.const_mul α).add (hAv.const_mul β)) measurableSet_Ioi fun t ht => ?_
    have hL := archLevyDensity_pos (show 0 < t from ht)
    calc archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) w t x
        ≤ archLevyDensity t *
          (α * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
            β * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) v t x) :=
          mul_le_mul_of_nonneg_left (hI t (le_of_lt ht)) hL.le
      _ = _ := by ring
  have hP : (∑' n : ℕ, vonMangoldtAtom n *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) w (Real.log n) x) ≤
      α * (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) +
      β * ∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) v (Real.log n) x := by
    have hPu := summable_atom_mul_sameSideIntegral (u := u) hpos hadu
    have hPv := summable_atom_mul_sameSideIntegral (u := v) hpos hadv
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hPu.mul_left α).tsum_add (hPv.mul_left β)]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_atom_mul_sameSideIntegral hpos hadw)
      ((hPu.mul_left α).add (hPv.mul_left β))
    calc vonMangoldtAtom n *
          ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) w (Real.log n) x
        ≤ vonMangoldtAtom n *
          (α * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) +
            β * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) v (Real.log n) x) :=
          mul_le_mul_of_nonneg_left (hI _ (Real.log_natCast_nonneg n)) (vonMangoldtAtom_nonneg n)
      _ = _ := by ring
  unfold sameSideEnergy
  linarith [hA, hP]

theorem reflectedDifferenceEnergy_le_combination {a : ℝ} (ha : 0 < a) {u v w : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) {α β : ℝ}
    (h : ∀ x y, (w x - w y) ^ 2 ≤ α * (u x - u y) ^ 2 + β * (v x - v y) ^ 2) :
    reflectedDifferenceEnergy (shiftedGroundState a) w ≤
      α * reflectedDifferenceEnergy (shiftedGroundState a) u +
        β * reflectedDifferenceEnergy (shiftedGroundState a) v := by
  have hI : ∀ t,
      (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) w t x) ≤
        α * (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) +
          β * ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) v t x := by
    intro t
    have hJu := integrableOn_reflectedDifferenceJump_shiftedGroundState hu.continuous a t
    have hJv := integrableOn_reflectedDifferenceJump_shiftedGroundState hv.continuous a t
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hJu.const_mul α) (hJv.const_mul β)]
    refine setIntegral_mono_on (integrableOn_reflectedDifferenceJump_shiftedGroundState hw.continuous a t)
      ((hJu.const_mul α).add (hJv.const_mul β)) measurableSet_Ioo fun x hx => ?_
    simp only [reflectedDifferenceJump_shiftedGroundState]
    have hm : 0 ≤ shiftDifference a x * shiftDifference a (t - x) :=
      mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx.1.le)
        (shiftDifference_nonneg_of_nonneg ha.le (by linarith [hx.2]))
    calc shiftDifference a x * shiftDifference a (t - x) * (w x - w (t - x)) ^ 2
        ≤ shiftDifference a x * shiftDifference a (t - x) *
          (α * (u x - u (t - x)) ^ 2 + β * (v x - v (t - x)) ^ 2) :=
          mul_le_mul_of_nonneg_left (h x (t - x)) hm
      _ = _ := by ring
  have hA : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) w t x) ≤
      α * (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) +
      β * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) v t x := by
    have hAu := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc
    have hAv := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hv hvc
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hAu.const_mul α) (hAv.const_mul β)]
    refine setIntegral_mono_on (integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hw hwc)
      ((hAu.const_mul α).add (hAv.const_mul β)) measurableSet_Ioi fun t ht => ?_
    have hL := archLevyDensity_pos (show 0 < t from ht)
    calc archLevyDensity t *
          ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) w t x
        ≤ archLevyDensity t *
          (α * (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) +
            β * ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) v t x) :=
          mul_le_mul_of_nonneg_left (hI t) hL.le
      _ = _ := by ring
  have hP : (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) w (Real.log n) x) ≤
      α * (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) +
      β * ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        reflectedDifferenceJump (shiftedGroundState a) v (Real.log n) x := by
    have hPu := summable_atom_mul_reflectedDifferenceIntegral ha hu huc
    have hPv := summable_atom_mul_reflectedDifferenceIntegral ha hv hvc
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hPu.mul_left α).tsum_add (hPv.mul_left β)]
    refine Summable.tsum_le_tsum (fun n => ?_)
      (summable_atom_mul_reflectedDifferenceIntegral ha hw hwc)
      ((hPu.mul_left α).add (hPv.mul_left β))
    calc vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
          reflectedDifferenceJump (shiftedGroundState a) w (Real.log n) x
        ≤ vonMangoldtAtom n *
          (α * (∫ x in Ioo (0 : ℝ) (Real.log n),
              reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) +
            β * ∫ x in Ioo (0 : ℝ) (Real.log n),
              reflectedDifferenceJump (shiftedGroundState a) v (Real.log n) x) :=
          mul_le_mul_of_nonneg_left (hI _) (vonMangoldtAtom_nonneg n)
      _ = _ := by ring
  unfold reflectedDifferenceEnergy
  linarith [hA, hP]

/-! ### The same-side energy of a Lipschitz plateau -/

theorem mul_exp_neg_six_mul_le_one {t : ℝ} (ht : 0 ≤ t) : t * Real.exp (-(6 * t)) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  linarith [Real.add_one_le_exp (6 * t)]

/-- Pointwise bound of the same-side jump of a Lipschitz plateau:
`m_a(x) m_a(x+t) (u(x) − u(x+t))² ≤ Φ(0) C e^{16a} Λ² e^{−8L} · t² e^{−6t} · e^{−x}`. -/
theorem sameSideGroundJump_plateau_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} {Λ L : ℝ} (hLip : ∀ x y, |u y - u x| ≤ Λ * |y - x|)
    (hone : ∀ x, |x| ≤ L → u x = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    sameSideGroundJump (shiftedGroundState a) u t x ≤
      riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 * Real.exp (-(8 * L)) *
        (t ^ 2 * Real.exp (-(6 * t))) * Real.exp (-x) := by
  rw [sameSideGroundJump_shiftedGroundState]
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hRHS : 0 ≤ riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 * Real.exp (-(8 * L)) *
      (t ^ 2 * Real.exp (-(6 * t))) * Real.exp (-x) := by positivity
  by_cases hboth : x ≤ L ∧ x + t ≤ L
  · rw [hone x (by rw [abs_of_pos hx]; exact hboth.1),
      hone (x + t) (by rw [abs_of_pos (by linarith)]; exact hboth.2), sub_self]
    simpa using hRHS
  · have hfar : L < x + t := by
      rw [not_and_or] at hboth
      rcases hboth with h | h <;> rw [not_le] at h <;> linarith
    have hm1 : shiftDifference a x ≤ riemannKernelReal 0 :=
      (abs_le.mp (abs_shiftDifference_le a x)).2
    have hm1' : 0 ≤ shiftDifference a x := shiftDifference_nonneg_of_nonneg ha.le hx.le
    have hm2 : shiftDifference a (x + t) ≤
        C * Real.exp (16 * a) * (Real.exp (-(8 * L)) * (Real.exp (-(6 * t)) * Real.exp (-x))) := by
      refine (shiftDifference_le_kernel a (x + t)).trans ((hC _).trans ?_)
      rw [← Real.exp_add, ← Real.exp_add, mul_assoc C, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
      linarith [le_abs_self (x + t - a)]
    have hm2' : 0 ≤ shiftDifference a (x + t) := shiftDifference_nonneg_of_nonneg ha.le (by linarith)
    have hd : (u x - u (x + t)) ^ 2 ≤ Λ ^ 2 * t ^ 2 := by
      have h := hLip (x + t) x
      rw [show x - (x + t) = -t by ring, abs_neg, abs_of_nonneg ht] at h
      calc (u x - u (x + t)) ^ 2 = |u x - u (x + t)| ^ 2 := (sq_abs _).symm
        _ ≤ (Λ * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = Λ ^ 2 * t ^ 2 := by ring
    calc shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2
        ≤ riemannKernelReal 0 *
            (C * Real.exp (16 * a) * (Real.exp (-(8 * L)) * (Real.exp (-(6 * t)) * Real.exp (-x)))) *
            (Λ ^ 2 * t ^ 2) :=
          mul_le_mul (mul_le_mul hm1 hm2 hm2' hΘ0) hd (sq_nonneg _) (by positivity)
      _ = _ := by ring

/-- The same-side energy of a Lipschitz plateau is at most
`Φ(0) C e^{16a} Λ² (∫ archLevyDensity(t) t dt + Σ 1/n³) e^{−8L}`. -/
theorem sameSideEnergy_plateau_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) {Λ L : ℝ}
    (hLip : ∀ x y, |u y - u x| ≤ Λ * |y - x|) (hone : ∀ x, |x| ≤ L → u x = 1) :
    sameSideEnergy (shiftedGroundState a) u ≤
      riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 *
        ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 3) *
        Real.exp (-(8 * L)) := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  set K := riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 * Real.exp (-(8 * L)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hI : ∀ t, 0 ≤ t →
      (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) ≤
        K * (t ^ 2 * Real.exp (-(6 * t))) := by
    intro t ht
    calc (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x)
        ≤ ∫ x in Ioi (0 : ℝ), K * (t ^ 2 * Real.exp (-(6 * t))) * Real.exp (-x) :=
          setIntegral_mono_on (integrableOn_sameSideJump_shiftedGroundState hu.continuous huc a t)
            ((integrableOn_exp_neg_Ioi 0).const_mul _) measurableSet_Ioi fun x hx =>
            sameSideGroundJump_plateau_le hC0 hC ha hLip hone ht hx
      _ = K * (t ^ 2 * Real.exp (-(6 * t))) := by
          rw [integral_const_mul, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one]
  have hA : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) ≤
      K * ∫ t in Ioi (0 : ℝ), archLevyDensity t * t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_archLevy_mul_sameSideIntegral hωc hu.continuous hpos hadm)
      (integrableOn_archLevyDensity_mul_id.const_mul _) measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hL := archLevyDensity_pos ht0
    have hte : t ^ 2 * Real.exp (-(6 * t)) ≤ t := by
      have := mul_exp_neg_six_mul_le_one ht0.le
      calc t ^ 2 * Real.exp (-(6 * t)) = t * (t * Real.exp (-(6 * t))) := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left this ht0.le
        _ = t := mul_one t
    calc archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x
        ≤ archLevyDensity t * (K * (t ^ 2 * Real.exp (-(6 * t)))) :=
          mul_le_mul_of_nonneg_left (hI t ht0.le) hL.le
      _ ≤ archLevyDensity t * (K * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hte hK0) hL.le
      _ = K * (archLevyDensity t * t) := by ring
  have hP : (∑' n : ℕ, vonMangoldtAtom n *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) ≤
      K * ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_atom_mul_sameSideIntegral hpos hadm)
      ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num), zero_mul]
      positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
      have hΛlog := vonMangoldtAtom_le_log n
      have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
      have hexp : Real.exp (-(6 * Real.log n)) = 1 / (n : ℝ) ^ 6 := by
        rw [Real.exp_neg, show (6 : ℝ) * Real.log n = ((6 : ℕ) : ℝ) * Real.log n by norm_num,
          Real.exp_nat_mul, Real.exp_log hn0, one_div]
      have hIn := hI (Real.log n) hlog0
      rw [hexp] at hIn
      have hlog2 : Real.log n ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hlog0 hlogn 2
      have hIn' : (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) ≤
          K * ((n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 6)) :=
        hIn.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog2 (by positivity)) hK0)
      have hn6 : (0 : ℝ) < (n : ℝ) ^ 6 := by positivity
      calc vonMangoldtAtom n *
            ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x
          ≤ (n : ℝ) * (K * ((n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 6))) :=
            mul_le_mul (hΛlog.trans hlogn) hIn'
              (integral_sameSideGroundJump_nonneg hpos hlog0) hn0.le
        _ = K * (1 / (n : ℝ) ^ 3) := by
            field_simp
  unfold sameSideEnergy
  rw [hK] at hA hP
  linarith [hA, hP]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
