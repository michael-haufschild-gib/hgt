import GaloisForLFunctions.RHTower.SelbergCuspZeroMean
import GaloisForLFunctions.RHTower.SelbergPoincarePairing

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# The slab integral of the `Γ(N)` Maass–Selberg relation

`|E_∞(z, v)| ≤ E_∞(z, Re v)` (`norm_poincare_le`), and the period integral at height `y` is
`∫_0^N E_∞(x+iy, v) dx = N y^v + φ_{∞∞}(v) y^{1-v}` (`integral_row_eq`, `count₀ = 1` at `∞` for `N ≥ 3`); applied at
`Re v` it bounds `∫_0^N |E_∞|` (`integral_norm_row_le`). This dominates the slab integrand `y^{u-2} E_∞(x+iy, v)` on
`[0,N) × (0,Y]` by `N y^{Re u + Re v − 2} + C y^{Re u − Re v − 1}` (`integrableOn_slabG`), and Fubini gives
`∫_{strip} [y ≤ Y] y^u E_∞(z, v) dμ = N Y^{u+v-1}/(u+v-1) + φ_{∞∞}(v) Y^{u-v}/(u-v)` for `1 < Re v < Re u`
(`slab_eq`).
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassSelbergSlab
open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry
  GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
  GaloisForLFunctions.RHTower.SelbergPoincarePairing
open CongruenceSubgroup

variable (N : ℕ) [NeZero N]

theorem termQ_zero (s : ℂ) (z : ℍ) (q : Cosets N) :
    termQ N 0 s z q = ((((Quotient.out q : Gamma N) : SL(2, ℤ)) • z).im : ℂ) ^ s := by
  have hq : termQ N 0 s z q = term N 0 s z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq]; unfold term; simp

/-- `|E_∞(z, v)| ≤ E_∞(z, Re v)`. -/
theorem norm_poincare_le {v : ℂ} (hv : 1 < v.re) (z : ℍ) :
    ‖poincare N 0 v z‖ ≤ (poincare N 0 (v.re : ℂ) z).re := by
  have hsum := summable_termQ N 0 hv z
  have hre : ∀ q : Cosets N, ‖termQ N 0 v z q‖ = (termQ N 0 (v.re : ℂ) z q).re := by
    intro q
    rw [termQ_zero, termQ_zero, Complex.norm_cpow_eq_rpow_re_of_pos (UpperHalfPlane.im_pos _),
      ← Complex.ofReal_cpow (UpperHalfPlane.im_pos _).le, Complex.ofReal_re]
  have hsum' : Summable (fun q => termQ N 0 (v.re : ℂ) z q) :=
    (summable_termQ N 0 (by simpa using hv) z).of_norm
  unfold poincare
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  rw [Complex.re_tsum hsum']
  exact tsum_congr hre

omit [NeZero N] in
theorem count0_one (hN : 3 ≤ N) : count0 N 1 = 1 := by
  classical
  unfold count0
  have h1 : ((0 : ℤ), (1 : ℤ)) ∈ GaloisForLFunctions.RHTower.SelbergEisensteinCusp.rowMul 1 '' adm N := by
    refine ⟨((0 : ℤ), (1 : ℤ)), ⟨dvd_zero _, by simp, isCoprime_zero_left.mpr isUnit_one⟩, ?_⟩
    simp [GaloisForLFunctions.RHTower.SelbergEisensteinCusp.rowMul]
  have h2 : ((0 : ℤ), (-1 : ℤ)) ∉ GaloisForLFunctions.RHTower.SelbergEisensteinCusp.rowMul 1 '' adm N := by
    rintro ⟨p, hp, hpe⟩
    simp only [GaloisForLFunctions.RHTower.SelbergEisensteinCusp.rowMul, Prod.mk.injEq] at hpe
    have e1 : p.2 = -1 := by simpa using hpe.2
    have hd := hp.2.1
    rw [e1] at hd
    have : (N : ℤ) ∣ 2 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp (by simpa using hd)
      simpa using this
    have := Int.le_of_dvd (by norm_num) this
    omega
  rw [Finset.filter_insert, if_pos h1, Finset.filter_singleton, if_neg h2]
  simp

/-- The horizontal period integral of `E_∞` at height `y` (`Re v > 1`): `∫_0^N E(x+iy, v) dx = N y^v + φ_{∞∞}(v) y^{1-v}`. -/
theorem integral_row_eq (hN : 3 ≤ N) {v : ℂ} (hv : 1 < v.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, poincare N 0 v (ofComplex (point x y)) =
      N * ((y : ℝ) : ℂ) ^ v + phiσ N 1 v * ((y : ℝ) : ℂ) ^ (1 - v) := by
  have h := integral_poincare_cusp_phi N 1 hv hy
  simp only [one_smul] at h
  rw [h, count0_one N hN]; push_cast; ring

theorem continuous_row (v : ℂ) (hv : 1 < v.re) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => poincare N 0 v (ofComplex (point x y))) := by
  have e : (fun x : ℝ => poincare N 0 v (ofComplex (point x y))) =
      fun x => poincare N 0 v (GaloisForLFunctions.RHTower.SelbergCusppieceAveraging.pt x y hy) :=
    funext fun x => by rw [GaloisForLFunctions.RHTower.SelbergCuspConstantTerm.pt_eq]
  rw [e]
  exact (GaloisForLFunctions.RHTower.SelbergPoincareBounded.continuous_poincare N 0 hv).comp
    (GaloisForLFunctions.RHTower.SelbergCuspZeroMean.continuous_pt_x hy)

/-- The real-part bound on the horizontal integral of `|E_∞|`. -/
theorem integral_norm_row_le (hN : 3 ≤ N) {v : ℂ} (hv : 1 < v.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, ‖poincare N 0 v (ofComplex (point x y))‖ ≤
      N * y ^ v.re + ‖phiσ N 1 (v.re : ℂ)‖ * y ^ (1 - v.re) := by
  have hv' : 1 < ((v.re : ℂ)).re := by simpa using hv
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hc := continuous_row N v hv hy
  have hc' := continuous_row N (v.re : ℂ) hv' hy
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hN0 (hc.norm.intervalIntegrable _ _)
    ((Complex.continuous_re.comp hc').intervalIntegrable _ _)
    (fun x _ => norm_poincare_le N hv (ofComplex (point x y)))
  have hre : (∫ u in (0 : ℝ)..N, (Complex.re ∘ fun x => poincare N 0 (v.re : ℂ) (ofComplex (point x y))) u) =
      (∫ x in (0 : ℝ)..N, poincare N 0 (v.re : ℂ) (ofComplex (point x y))).re :=
    Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (hc'.intervalIntegrable _ _)
  refine hmono.trans ?_
  rw [hre, integral_row_eq N hN hv' hy]
  simp only [Complex.add_re]
  have e1 : ((N : ℂ) * ((y : ℝ) : ℂ) ^ ((v.re : ℂ))).re = N * y ^ v.re := by
    rw [← Complex.ofReal_cpow hy.le, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have e2 : (phiσ N 1 (v.re : ℂ) * ((y : ℝ) : ℂ) ^ (1 - (v.re : ℂ))).re ≤
      ‖phiσ N 1 (v.re : ℂ)‖ * y ^ (1 - v.re) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp
  rw [e1]; linarith

open GaloisForLFunctions.RHTower.SelbergTruncationIdentity in
/-- The slab integrand in coordinates: `y^{u-2} E_∞(x + iy, v)` on `[0,N) × (0,Y]`. -/
noncomputable def slabG (u v : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 : ℝ) : ℂ) ^ (u - 2) * poincare N 0 v (ofComplex (point p.1 p.2))

theorem continuousOn_slabG {u v : ℂ} (hv : 1 < v.re) (Y : ℝ) :
    ContinuousOn (slabG N u v) (Ico (0 : ℝ) N ×ˢ Ioc 0 Y) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => poincare N 0 v (ofComplex (point p.1 p.2))) (Ico (0 : ℝ) N ×ˢ Ioc 0 Y) :=
    (continuousOn_g_point (GaloisForLFunctions.RHTower.SelbergPoincareBounded.continuous_poincare N 0 hv)).mono
      (prod_mono le_rfl Ioc_subset_Ioi_self)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ (u - 2)) (Ico (0 : ℝ) N ×ˢ Ioc 0 Y) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.cpow_const
      (fun p hp => Complex.ofReal_mem_slitPlane.mpr hp.2.1)
  exact h2.mul h1

theorem integrableOn_slabG (hN : 3 ≤ N) {u v : ℂ} (hv : 1 < v.re) (huv : v.re < u.re) (Y : ℝ) :
    IntegrableOn (slabG N u v) (Ico (0 : ℝ) N ×ˢ Ioc 0 Y) := by
  have hmeas : MeasurableSet (Ico (0 : ℝ) N ×ˢ Ioc 0 Y) := measurableSet_Ico.prod measurableSet_Ioc
  have hae := (continuousOn_slabG N (u := u) hv Y).aestronglyMeasurable (μ := volume) hmeas
  unfold IntegrableOn
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hae ⊢
  rw [integrable_prod_iff' hae]
  constructor
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy0 : 0 < y := hy.1
    have hc : Continuous (fun x : ℝ => slabG N u v (x, y)) := by
      unfold slabG; simp only; exact continuous_const.mul (continuous_row N v hv hy0)
    exact (hc.integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (N : ℝ))).mono_set Ico_subset_Icc_self
  · -- the y-profile is dominated by an integrable power combination
    set B : ℝ → ℝ := fun y => N * y ^ (u.re + v.re - 2) + ‖phiσ N 1 (v.re : ℂ)‖ * y ^ (u.re - v.re - 1)
    have hB : IntegrableOn B (Ioc 0 Y) := by
      have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := u.re + v.re - 2)
        (by linarith)).1
      have h2 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := u.re - v.re - 1)
        (by linarith)).1
      exact (h1.const_mul _).add (h2.const_mul _)
    refine Integrable.mono' hB ?_ ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun y hy => ?_)))
    · exact hae.norm.prod_swap.integral_prod_right'
    · have hy0 : 0 < y := hy.1
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have e : (∫ x in Ico (0 : ℝ) N, ‖slabG N u v (x, y)‖) =
          y ^ (u.re - 2) * ∫ x in (0 : ℝ)..N, ‖poincare N 0 v (ofComplex (point x y))‖ := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N), ← integral_Ico_eq_integral_Ioc,
          ← integral_const_mul]
        congr 1; funext x
        simp only [slabG]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp
      rw [e]
      have hb := integral_norm_row_le N hN hv hy0
      calc y ^ (u.re - 2) * ∫ x in (0 : ℝ)..N, ‖poincare N 0 v (ofComplex (point x y))‖
          ≤ y ^ (u.re - 2) * (N * y ^ v.re + ‖phiσ N 1 (v.re : ℂ)‖ * y ^ (1 - v.re)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = B y := by
            simp only [B]
            rw [mul_add, ← mul_assoc, mul_comm (y ^ (u.re - 2)) (N : ℝ), mul_assoc, ← Real.rpow_add hy0,
              mul_left_comm, ← Real.rpow_add hy0]
            congr 2 <;> ring_nf

theorem integral_Ioc_cpow {r : ℂ} (hr : -1 < r.re) {Y : ℝ} (hY : 0 < Y) :
    ∫ y in Ioc (0 : ℝ) Y, ((y : ℝ) : ℂ) ^ r = ((Y : ℝ) : ℂ) ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hY.le, integral_cpow (Or.inl hr)]
  have hr1 : r + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Complex.ofReal_zero, Complex.zero_cpow hr1, sub_zero]

open GaloisForLFunctions.RHTower.SelbergTruncationIdentity in
/-- **The slab integral** (`N ≥ 3`, `1 < Re v < Re u`, `Y > 0`):
`∫_{strip} [y ≤ Y] y^u E_∞(z, v) dμ = N Y^{u+v-1}/(u+v-1) + φ_{∞∞}(v) Y^{u-v}/(u-v)`. -/
theorem slab_eq (hN : 3 ≤ N) {u v : ℂ} (hv : 1 < v.re) (huv : v.re < u.re) {Y : ℝ} (hY : 0 < Y) :
    ∫ z in stripN N, seedY u Y z * poincare N 0 v z =
      N * (((Y : ℝ) : ℂ) ^ (u + v - 1) / (u + v - 1)) + phiσ N 1 v * (((Y : ℝ) : ℂ) ^ (u - v) / (u - v)) := by
  set F : ℝ × ℝ → ℂ := fun p => seedY u Y (ofComplex (point p.1 p.2)) * poincare N 0 v (ofComplex (point p.1 p.2))
  have hF : ∀ z : ℍ, seedY u Y z * poincare N 0 v z = F (z.re, z.im) := by
    intro z; simp only [F, ofComplex_point]
  have hA : MeasurableSet (Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  rw [stripN_eq]
  simp_rw [hF]
  rw [RHTower.setIntegral_coord_eq hA (fun p hp => hp.2) F]
  have hsub : Ico (0 : ℝ) N ×ˢ Ioc 0 Y ⊆ Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ) := prod_mono le_rfl Ioc_subset_Ioi_self
  have hpt : ∀ p : ℝ × ℝ, 0 < p.2 → (ofComplex (point p.1 p.2)).im = p.2 := fun p hp =>
    (GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman.ofComplex_point hp).1
  have hzero : ∀ p ∈ (Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ)) \ (Ico (0 : ℝ) N ×ˢ Ioc 0 Y),
      F p / ((p.2 : ℝ) : ℂ) ^ 2 = 0 := by
    intro p hp
    have hp2 : Y < p.2 := by
      have h1 := hp.1.2
      have h2 : p ∉ Ico (0 : ℝ) N ×ˢ Ioc 0 Y := hp.2
      simp only [mem_prod, mem_Ioc, not_and, not_le] at h2
      exact h2 hp.1.1 h1
    simp only [F, seedY]
    rw [hpt p hp.1.2, if_neg (not_le.mpr hp2), zero_mul, zero_div]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA hsub hzero]
  have hG : ∀ p ∈ Ico (0 : ℝ) N ×ˢ Ioc 0 Y, F p / ((p.2 : ℝ) : ℂ) ^ 2 = slabG N u v p := by
    intro p hp
    have hp2 : 0 < p.2 := hp.2.1
    simp only [F, slabG, seedY]
    rw [hpt p hp2, if_pos hp.2.2]
    have hy0 : ((p.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp2.ne'
    rw [Complex.cpow_sub _ _ hy0, show ((p.2 : ℝ) : ℂ) ^ (2 : ℂ) = ((p.2 : ℝ) : ℂ) ^ (2 : ℕ) by
      rw [← Complex.cpow_natCast]; norm_num]
    field_simp
  rw [setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ioc) hG,
    RHTower.setIntegral_prod_eq_iterated (integrableOn_slabG N hN hv huv Y)]
  have hinner : ∀ y ∈ Ioc (0 : ℝ) Y, (∫ x in Ico (0 : ℝ) N, slabG N u v (x, y)) =
      N * ((y : ℝ) : ℂ) ^ (u + v - 2) + phiσ N 1 v * ((y : ℝ) : ℂ) ^ (u - v - 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hy0' : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    simp only [slabG]
    rw [integral_const_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      integral_row_eq N hN hv hy0, mul_add, ← mul_assoc, mul_comm (((y : ℝ) : ℂ) ^ (u - 2)) (N : ℂ), mul_assoc,
      ← Complex.cpow_add _ _ hy0', mul_left_comm, ← Complex.cpow_add _ _ hy0']
    congr 3 <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  have hi1 : IntegrableOn (fun y : ℝ => (N : ℂ) * ((y : ℝ) : ℂ) ^ (u + v - 2)) (Ioc 0 Y) := by
    have := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := Y) (r := u + v - 2)
      (by simp; linarith)).1
    exact this.const_mul _
  have hi2 : IntegrableOn (fun y : ℝ => phiσ N 1 v * ((y : ℝ) : ℂ) ^ (u - v - 1)) (Ioc 0 Y) := by
    have := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := Y) (r := u - v - 1)
      (by simp; linarith)).1
    exact this.const_mul _
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_Ioc_cpow (by simp; linarith) hY, integral_Ioc_cpow (by simp; linarith) hY]
  congr 2 <;> ring_nf

end GaloisForLFunctions.RHTower.SelbergMaassSelbergSlab

