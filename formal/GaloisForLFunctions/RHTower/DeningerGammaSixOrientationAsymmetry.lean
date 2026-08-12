import GaloisForLFunctions.RHTower.DeningerMobiusPrimeNormalSuccessorBlowup

/-!
# Analytic orientation asymmetry of the six-normal

The oriented normal `T_m = 6^{m/2}U_{m log 6}` and its inverse `V_m = T_m^{-1}` act on the physical
`L²` source.  Because the translation is unitary, `V_m` contracts by exactly `6^{-m/2}`, so the
reciprocal face of the oriented normal cannot cancel the forward vertical endpoint, and no sequence
tending to zero in `L²` can realize a nonzero reciprocal endpoint.

* `additiveTranslationUnitary_zero_apply` : the zero translation is the identity.
* `deningerSixNormal_inv` : **`T_m V_m = 1`.**
* `norm_deningerSixNormalInv` : **`‖V_m f‖ = 6^{-m/2}‖f‖`.**
* `deningerSixOrientation_asymmetry` : **the forward face survives, the reciprocal face dies.**
* `tendsto_norm_atTop_of_deningerSixNormalInv_tendsto` : **no reciprocal blow-up from a vanishing
  `L²` source.**
-/

namespace RHTower

open Filter Topology MeasureTheory

noncomputable section

theorem additiveTranslationUnitary_zero_apply (f : MobiusThetaSourceL2) :
    MellinL2.additiveTranslationUnitary 0 f = f := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv 0)
    (MellinL2.realTranslation_measurePreserving 0) f = f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving 0)] with x hx
  rw [hx]
  simp [MellinL2.realTranslationEquiv, Function.comp_apply]

/-- The oriented six-normal `T_m = 6^{m/2}U_{m log 6}`. -/
def deningerSixNormal (m : ℕ) (f : MobiusThetaSourceL2) : MobiusThetaSourceL2 :=
  ((((6 : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ)
    • MellinL2.additiveTranslationUnitary ((m : ℝ) * Real.log 6) f

/-- Its inverse `V_m = 6^{-m/2}U_{-m log 6}`. -/
def deningerSixNormalInv (m : ℕ) (f : MobiusThetaSourceL2) : MobiusThetaSourceL2 :=
  ((((6 : ℝ) ^ (-((m : ℝ) / 2)) : ℝ)) : ℂ)
    • MellinL2.additiveTranslationUnitary (-((m : ℝ) * Real.log 6)) f

/-- **`T_m V_m = 1`.** -/
theorem deningerSixNormal_inv (m : ℕ) (f : MobiusThetaSourceL2) :
    deningerSixNormal m (deningerSixNormalInv m f) = f := by
  rw [deningerSixNormal, deningerSixNormalInv, map_smul, smul_smul,
    additiveTranslationUnitary_add_apply]
  have hzero : (m : ℝ) * Real.log 6 + -((m : ℝ) * Real.log 6) = 0 := by ring
  rw [hzero, additiveTranslationUnitary_zero_apply]
  have hscalar : ((((6 : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ)
      * ((((6 : ℝ) ^ (-((m : ℝ) / 2)) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
    norm_num
  rw [hscalar, one_smul]

/-- **`‖V_m f‖ = 6^{-m/2}‖f‖`.** -/
theorem norm_deningerSixNormalInv (m : ℕ) (f : MobiusThetaSourceL2) :
    ‖deningerSixNormalInv m f‖ = (6 : ℝ) ^ (-((m : ℝ) / 2)) * ‖f‖ := by
  rw [deningerSixNormalInv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) _),
    LinearIsometryEquiv.norm_map]

/-- The doubly inverted normal contracts by `6^{-m}`. -/
theorem norm_deningerSixNormalInv_sq (m : ℕ) (f : MobiusThetaSourceL2) :
    ‖deningerSixNormalInv m (deningerSixNormalInv m f)‖ = (6 : ℝ) ^ (-(m : ℝ)) * ‖f‖ := by
  rw [norm_deningerSixNormalInv, norm_deningerSixNormalInv, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  congr 2
  ring

/-! ## The reciprocal face dies -/

/-- The doubly inverted normal of a convergent sequence tends to zero. -/
theorem tendsto_deningerSixNormalInv_sq_zero {R : ℕ → MobiusThetaSourceL2}
    {Theta : MobiusThetaSourceL2} (hR : Tendsto R atTop (𝓝 Theta)) :
    Tendsto (fun m => deningerSixNormalInv m (deningerSixNormalInv m (R m))) atTop (𝓝 0) := by
  have hbdd : ∃ C : ℝ, ∀ m : ℕ, ‖R m‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hR.norm).bddAbove_range
    exact ⟨C, fun m => hC ⟨m, rfl⟩⟩
  obtain ⟨C, hC⟩ := hbdd
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine squeeze_zero_norm (a := fun m : ℕ => (6 : ℝ) ^ (-(m : ℝ)) * C) (fun m => ?_) ?_
  · rw [norm_deningerSixNormalInv_sq]
    exact mul_le_mul_of_nonneg_left (hC m)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) _).le
  · have hpow : Tendsto (fun m : ℕ => (6 : ℝ) ^ (-(m : ℝ))) atTop (𝓝 0) := by
      have hfun : (fun m : ℕ => (6 : ℝ) ^ (-(m : ℝ))) = fun m : ℕ => ((6 : ℝ)⁻¹) ^ m := by
        funext m
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6), Real.rpow_natCast, ← inv_pow]
      rw [hfun]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hpow.mul_const C

/-- **Theorem 2.1: analytic orientation asymmetry.**  On the complete source `V_m R_m` the oriented
normal acts by `R_m - V_m² R_m`, whose limit is the forward endpoint alone. -/
theorem deningerSixOrientation_asymmetry {R : ℕ → MobiusThetaSourceL2}
    {Theta : MobiusThetaSourceL2} (hR : Tendsto R atTop (𝓝 Theta)) :
    (∀ m : ℕ, deningerSixNormal m (deningerSixNormalInv m (R m))
        - deningerSixNormalInv m (deningerSixNormalInv m (R m))
      = R m - deningerSixNormalInv m (deningerSixNormalInv m (R m)))
    ∧ Tendsto (fun m => deningerSixNormal m (deningerSixNormalInv m (R m))
        - deningerSixNormalInv m (deningerSixNormalInv m (R m))) atTop (𝓝 Theta) := by
  have hid : ∀ m : ℕ, deningerSixNormal m (deningerSixNormalInv m (R m)) = R m :=
    fun m => deningerSixNormal_inv m (R m)
  refine ⟨fun m => by rw [hid m], ?_⟩
  have hfun : (fun m => deningerSixNormal m (deningerSixNormalInv m (R m))
      - deningerSixNormalInv m (deningerSixNormalInv m (R m)))
      = fun m => R m - deningerSixNormalInv m (deningerSixNormalInv m (R m)) := by
    funext m
    rw [hid m]
  rw [hfun]
  simpa using hR.sub (tendsto_deningerSixNormalInv_sq_zero hR)

/-- **Theorem 2.2: no reciprocal blow-up from a vanishing `L²` source.**  If the inverted normals of
a sequence converge to a nonzero limit, the sequence itself is unbounded. -/
theorem tendsto_norm_atTop_of_deningerSixNormalInv_tendsto {K : ℕ → MobiusThetaSourceL2}
    {Y : MobiusThetaSourceL2} (hY : Y ≠ 0)
    (hK : Tendsto (fun m => deningerSixNormalInv m (K m)) atTop (𝓝 Y)) :
    Tendsto (fun m => ‖K m‖) atTop atTop := by
  have hYpos : 0 < ‖Y‖ := norm_pos_iff.2 hY
  have hnorm : Tendsto (fun m => ‖deningerSixNormalInv m (K m)‖) atTop (𝓝 ‖Y‖) := hK.norm
  have heq : ∀ m : ℕ, ‖K m‖ = (6 : ℝ) ^ ((m : ℝ) / 2) * ‖deningerSixNormalInv m (K m)‖ := by
    intro m
    rw [norm_deningerSixNormalInv, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
    have hzero : (m : ℝ) / 2 + -((m : ℝ) / 2) = 0 := by ring
    rw [hzero, Real.rpow_zero, one_mul]
  have hfun : (fun m : ℕ => ‖K m‖)
      = fun m : ℕ => (6 : ℝ) ^ ((m : ℝ) / 2) * ‖deningerSixNormalInv m (K m)‖ := funext heq
  rw [hfun]
  have hpow : Tendsto (fun m : ℕ => (6 : ℝ) ^ ((m : ℝ) / 2)) atTop atTop := by
    have hfun2 : (fun m : ℕ => (6 : ℝ) ^ ((m : ℝ) / 2))
        = fun m : ℕ => ((6 : ℝ) ^ ((1 : ℝ) / 2)) ^ m := by
      funext m
      rw [← Real.rpow_natCast ((6 : ℝ) ^ ((1 : ℝ) / 2)) m,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
      congr 1
      ring
    rw [hfun2]
    refine tendsto_pow_atTop_atTop_of_one_lt ?_
    have hlt : (1 : ℝ) ^ ((1 : ℝ) / 2) < (6 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 6)
        (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [Real.one_rpow] at hlt
  have hev : ∀ᶠ m in atTop, ‖Y‖ / 2 < ‖deningerSixNormalInv m (K m)‖ :=
    hnorm.eventually_const_lt (by linarith)
  refine tendsto_atTop_mono' atTop ?_ (hpow.atTop_mul_const (by linarith : (0 : ℝ) < ‖Y‖ / 2))
  filter_upwards [hev] with m hm
  exact mul_le_mul_of_nonneg_left hm.le
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) _).le

end

end RHTower
