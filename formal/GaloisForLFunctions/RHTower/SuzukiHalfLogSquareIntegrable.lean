import GaloisForLFunctions.RHTower.SuzukiHalfLogScatteringAsymptotic

/-!
# Vanishing scattering moves the trace into `L²`

When the half-log scattering map kills the two channels, the critical `L^{-1/2}` term of the
endpoint trace disappears and the remaining bound is `O(L^{-1})`.  A trace with that decay is square
integrable on a terminal half-line, since `∫^∞ L^{-2} dL` converges.  This is the exact mechanism by
which a single vanishing signed trace moves a homogeneous component off the critical corona.
-/

open Complex Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

omit [InnerProductSpace ℂ X] [CompleteSpace X] [Nontrivial X] in
/-- A trace with `O(1/L)` decay is square integrable on a terminal half-line. -/
theorem integrableOn_sq_of_decay {F : ℝ → X} {C L₀ : ℝ} (hL₀ : 0 < L₀)
    (hmeas : AEStronglyMeasurable F (volume.restrict (Ioi L₀)))
    (hbound : ∀ L ∈ Ioi L₀, ‖F L‖ ≤ C / L) :
    IntegrableOn (fun L => ‖F L‖ ^ 2) (Ioi L₀) volume := by
  have hpow : IntegrableOn (fun L : ℝ => L ^ (-(2:ℝ))) (Ioi L₀) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hL₀
  have hmaj : IntegrableOn (fun L : ℝ => C ^ 2 * L ^ (-(2:ℝ))) (Ioi L₀) volume :=
    hpow.const_mul _
  refine Integrable.mono' hmaj (hmeas.norm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hL0 : 0 < L := lt_trans hL₀ hL
  have hb := hbound L hL
  have hsq : ‖F L‖ ^ 2 ≤ (C / L) ^ 2 := by
    have h0 : 0 ≤ ‖F L‖ := norm_nonneg _
    nlinarith [hb, h0]
  have hval : (C / L) ^ 2 = C ^ 2 * L ^ (-(2:ℝ)) := by
    rw [show (-(2:ℝ)) = -(2:ℝ) from rfl, Real.rpow_neg hL0.le]
    rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖F L‖ ^ 2), ← hval]
  exact hsq

variable {Rint r : ℝ → ℝ} {T : X →L[ℂ] X}

/-- **Vanishing scattering forces `O(1/L)` decay.**  With `β(c₊,c₋) = 0` the endpoint trace has no
critical term, and the truncated transform is bounded by an explicit multiple of `1/L`, uniformly in
the truncation. -/
theorem norm_halfLog_le_of_scatter_zero {r' : ℝ → ℝ} (hT : IsSelfAdjoint T)
    (hR : Rint 0 = 0) {cp cm : X} {A L R B : ℝ}
    (hA : 0 < A) (hAR : A ≤ R) (hTL : ‖T‖ ≤ L) (hL : 0 < L)
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hrnn : ∀ x : ℝ, 0 ≤ r x)
    (hrb : ∀ x : ℝ, |x| ≤ A → |r x| ≤ B)
    (hrc : Continuous r)
    (hr' : ∀ x : ℝ, HasDerivAt r (r' x) x)
    (hr'c : Continuous r')
    (hr'pos : ∀ x : ℝ, 0 ≤ x → 0 ≤ r' x)
    (hr'neg : ∀ x : ℝ, x ≤ 0 → r' x ≤ 0)
    (hβ : halfLogScatter cp cm = 0) :
    ‖(∫ η in (0:ℝ)..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
        + ∫ t in (0:ℝ)..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm)‖
      ≤ ((‖cp‖ + ‖cm‖) * (10 * A ^ (-(1:ℝ)/2) + 2 * (B + ‖T‖) * A ^ ((1:ℝ)/2))) / L := by
  have hTnn : (0:ℝ) ≤ ‖T‖ := norm_nonneg T
  have hTL2 : ‖T‖ / 2 < L := by linarith
  have hmain := norm_halfLog_scattering_asymptotic (T := T) (r := r) (r' := r') (Rint := Rint)
    hT hR hA hAR hTL2 hRint hrnn hrb hrc hr' hr'c hr'pos hr'neg (cp := cp) (cm := cm) (B := B)
  rw [hβ, smul_zero, sub_zero] at hmain
  refine le_trans hmain ?_
  -- arithmetic: each term is dominated by the stated multiple of `1/L`
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (r 0)) (hrb 0 (by simp [hA.le]))
  have hnorms : (0:ℝ) ≤ ‖cp‖ + ‖cm‖ := by positivity
  have hApow : (0:ℝ) < A ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hA _
  have hApow2 : (0:ℝ) < A ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hA _
  have hRpow : R ^ (-(1:ℝ)/2) ≤ A ^ (-(1:ℝ)/2) := by
    have hRpos : 0 < R := lt_of_lt_of_le hA hAR
    have hneg : ∀ y : ℝ, 0 < y → y ^ (-(1:ℝ)/2) = (y ^ ((1:ℝ)/2))⁻¹ := by
      intro y hy
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hy)]
    rw [hneg R hRpos, hneg A hA]
    exact inv_anti₀ hApow2 (Real.rpow_le_rpow hA.le hAR (by norm_num))
  have hLinv : L ^ (-(1:ℝ)) = L⁻¹ := by
    rw [show (-(1:ℝ)) = -(1:ℝ) from rfl, Real.rpow_neg hL.le, Real.rpow_one]
  have hhalf : (L - ‖T‖ / 2)⁻¹ ≤ 2 / L := by
    have h1 : L / 2 ≤ L - ‖T‖ / 2 := by linarith
    have h2 : (0:ℝ) < L / 2 := by linarith
    calc (L - ‖T‖ / 2)⁻¹ ≤ (L / 2)⁻¹ := inv_anti₀ h2 h1
      _ = 2 / L := by field_simp
  rw [hLinv]
  have hterm1 : (‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2) * L⁻¹)
      = ((‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2))) / L := by
    field_simp
  have hterm2 : (4 * ((B / 2 + ‖T‖ / 2) * (‖cp‖ + ‖cm‖)) * A ^ ((1:ℝ)/2)) / L
      = ((‖cp‖ + ‖cm‖) * (2 * (B + ‖T‖) * A ^ ((1:ℝ)/2))) / L := by
    field_simp
    ring
  have hterm3 : (3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ * (‖cp‖ + ‖cm‖)
      ≤ ((‖cp‖ + ‖cm‖) * (8 * A ^ (-(1:ℝ)/2))) / L := by
    have hfac : (3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) ≤ 4 * A ^ (-(1:ℝ)/2) := by linarith
    have hfacnn : (0:ℝ) ≤ 3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2) := by
      have h1 : (0:ℝ) ≤ A ^ (-(1:ℝ)/2) := Real.rpow_nonneg hA.le _
      have h2 : (0:ℝ) ≤ R ^ (-(1:ℝ)/2) := Real.rpow_nonneg (le_trans hA.le hAR) _
      linarith
    have hinvnn : (0:ℝ) ≤ (L - ‖T‖ / 2)⁻¹ := inv_nonneg.mpr (by linarith)
    calc (3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ * (‖cp‖ + ‖cm‖)
        ≤ (4 * A ^ (-(1:ℝ)/2)) * (2 / L) * (‖cp‖ + ‖cm‖) := by
          gcongr
      _ = ((‖cp‖ + ‖cm‖) * (8 * A ^ (-(1:ℝ)/2))) / L := by field_simp; ring
  rw [hterm1, hterm2]
  have hsum : ((‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2))) / L
      + ((‖cp‖ + ‖cm‖) * (2 * (B + ‖T‖) * A ^ ((1:ℝ)/2))) / L
      + ((‖cp‖ + ‖cm‖) * (8 * A ^ (-(1:ℝ)/2))) / L
      = ((‖cp‖ + ‖cm‖) * (10 * A ^ (-(1:ℝ)/2) + 2 * (B + ‖T‖) * A ^ ((1:ℝ)/2))) / L := by
    field_simp
    ring
  linarith [hterm3, hsum]

end

end GaloisForLFunctions.RHTower
