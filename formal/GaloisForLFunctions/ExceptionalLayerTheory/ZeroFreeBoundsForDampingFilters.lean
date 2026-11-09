import GaloisForLFunctions.ExceptionalLayerTheory.EulerBoundsForDampingFilters
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodArbitraryConstant
import GaloisForLFunctions.RHTower.MoebiusAbelSmoothedSaving
import GaloisForLFunctions.RHTower.KuznetsovWhittakerStripBounds
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Zero-free-region bounds for the filtered prime current

A local shift of the Mellin contour uses only zeta heights comparable to the
observation height. The filter retains its spacing gain along every edge.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Polynomial weights preserve an exponential Gaussian Mellin envelope,
uniformly on every closed strip of positive real parts. -/
theorem exists_weighted_gaussianMBKernel_strip_envelope {l u : ℝ}
    (hl : 0 < l) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y x v : ℝ, 0 < y → l ≤ x → x ≤ u →
      ‖gaussianMBKernel y ((x : ℂ) + v * I)‖ * (1 + |v|) ^ n ≤
        C * y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by
  obtain ⟨A, M, hA, hb⟩ :=
    GaloisForLFunctions.RHTower.DeckPointPair.exists_bound_norm_Gamma_strip_all
      (a := l / 2) (b := u / 2) (by positivity)
  let δ : ℝ := Real.pi / 4 - 1 / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [Real.pi_gt_three]
  let D : ℝ := Real.exp δ * ((M + n).factorial : ℝ) / δ ^ (M + n)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨A / 2 * D + 1, by positivity, ?_⟩
  intro y x v hy hx1 hx2
  have hg := hb (x / 2) (v / 2) (by linarith only [hx1]) (by linarith only [hx2])
  have hv : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith only [abs_nonneg v]
  have hg' : ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ ≤
      A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|)) := by
    have he : -(Real.pi * |v / 2| / 2) = -(Real.pi / 4 * |v|) := by
      rw [abs_div, abs_two]
      ring
    rw [he] at hg
    exact hg.trans (by gcongr)
  have hp : (1 + |v|) ^ (M + n) * Real.exp (-(δ * |v|)) ≤ D := by
    have hh := HTGeometry.pow_mul_exp_neg_le hδ (M + n)
      (by positivity : 0 ≤ 1 + |v|)
    calc
      _ = Real.exp δ * ((1 + |v|) ^ (M + n) * Real.exp (-(δ * (1 + |v|)))) := by
        rw [mul_left_comm, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp δ * (((M + n).factorial : ℝ) / δ ^ (M + n)) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = D := by dsimp only [D]; ring
  have he : Real.exp (-(Real.pi / 4 * |v|)) =
      Real.exp (-(δ * |v|)) * Real.exp (-(|v| / 2)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δ]
    ring
  rw [norm_gaussianMBKernel_line hy]
  calc
    _ ≤ 1 / 2 * (A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|))) *
        y ^ (-(x / 2)) * (1 + |v|) ^ n := by gcongr
    _ = (A / 2 * ((1 + |v|) ^ (M + n) * Real.exp (-(δ * |v|)))) *
        y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by rw [he, pow_add]; ring
    _ ≤ (A / 2 * D) * y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by gcongr
    _ ≤ _ := by gcongr; linarith

/-- The whole divisor filter and Gamma kernel have a common strip envelope.
The spacing loss is exactly the number of filter factors. -/
theorem exists_divisorFilter_kernel_strip_envelope (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β l u : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h t x v : ℝ,
      0 < y → 0 ≤ h → h ≤ 1 → l ≤ x → x ≤ u →
      ‖(divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) *
            ((((σ : ℂ) + t * I) + ((x : ℂ) + v * I)) - β))) *
        gaussianMBKernel y ((x : ℂ) + v * I)‖ ≤
      C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
        (1 + |t|) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨B, hB, hb⟩ := exists_divisorDampingFilter_strip_bound F ρ β (|σ| + |u|)
  obtain ⟨A, hA, hgauss⟩ := exists_weighted_gaussianMBKernel_strip_envelope (u := u) hl d
  refine ⟨B ^ d * A, by positivity, ?_⟩
  intro y h t x v hy hh hh1 hx1 hx2
  have hx0 : 0 ≤ x := hl.le.trans hx1
  have hreal : |σ + x| ≤ |σ| + |u| := by
    calc
      _ ≤ |σ| + |x| := abs_add_le _ _
      _ = |σ| + x := by rw [abs_of_nonneg hx0]
      _ ≤ |σ| + |u| := add_le_add le_rfl (hx2.trans (le_abs_self u))
  have hp := hb (σ + x) h t v hreal hh hh1
  have hline : ((σ : ℂ) + t * I) + ((x : ℂ) + v * I) =
      ((σ + x : ℝ) : ℂ) + (t + v) * I := by push_cast; ring
  rw [norm_mul, hline]
  calc
    _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
        ‖gaussianMBKernel y ((x : ℂ) + v * I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = B ^ d * h ^ d * (1 + |t|) ^ d *
        (‖gaussianMBKernel y ((x : ℂ) + v * I)‖ * (1 + |v|) ^ d) := by
      simp only [mul_pow]
      ring
    _ ≤ B ^ d * h ^ d * (1 + |t|) ^ d *
        (A * y ^ (-(x / 2)) * Real.exp (-(|v| / 2))) := by
      gcongr
      exact hgauss y x v hy hx1 hx2
    _ = _ := by ring

private def filteredMellinIntegrand (P : Polynomial ℂ) (s : ℂ)
    (β h y : ℝ) (w : ℂ) : ℂ :=
  P.eval (Complex.exp ((h : ℂ) * (s + w - β))) *
    gaussianMBKernel y w * (-logDeriv riemannZeta (s + w))

private theorem differentiableAt_filteredMellinIntegrand (P : Polynomial ℂ)
    (s : ℂ) (β h : ℝ) {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : 0 < w.re) (hs : s + w ≠ 1) (hz : riemannZeta (s + w) ≠ 0) :
    DifferentiableAt ℂ (filteredMellinIntegrand P s β h y) w := by
  have hG : DifferentiableAt ℂ Complex.Gamma (w / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have he := congrArg Complex.re hm
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at he
    linarith only [hw, he, Nat.cast_nonneg (α := ℝ) m]
  have hK : DifferentiableAt ℂ (gaussianMBKernel y) w := by
    unfold gaussianMBKernel
    exact ((hG.comp w (differentiableAt_id.div_const 2)).const_mul (1 / 2)).mul
      ((differentiableAt_id.div_const 2).neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))
  have hza : AnalyticAt ℂ riemannZeta (s + w) := by
    have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)
  have hld : DifferentiableAt ℂ (logDeriv riemannZeta) (s + w) := by
    simpa only [logDeriv_apply] using
      hza.deriv.differentiableAt.div hza.differentiableAt hz
  have hP : DifferentiableAt ℂ
      (fun z : ℂ => P.eval (Complex.exp ((h : ℂ) * (s + z - β)))) w := by
    exact P.differentiable.differentiableAt.comp w
      (((differentiableAt_id.const_add s).sub_const (β : ℂ)).const_mul (h : ℂ)).cexp
  exact (hP.mul hK).mul ((hld.comp w (differentiableAt_id.const_add s)).neg)

/-- On the local rectangle around height `t`, the actual zeta logarithmic
derivative has a polynomial bound in a strip of any prescribed width. -/
theorem eventually_zeta_local_rectangle (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ x v : ℝ,
      1 - η / Real.log (2 * t) ≤ x → x ≤ 9 / 8 → |v| ≤ t / 2 →
      riemannZeta ((x : ℂ) + (t + v) * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((x : ℂ) + (t + v) * I)‖ ≤ D * (1 + t) ^ 2 := by
  obtain ⟨T₁, _, hz⟩ := Sieve.exists_zero_free_region_arbitrary_constant (2 * η)
  obtain ⟨C, T₂, hC, _, hd⟩ := Sieve.exists_logDeriv_zeta_bound_arbitrary_constant η
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * T₁), eventually_ge_atTop (2 * T₂),
    eventually_ge_atTop (2 * Real.exp (Real.exp 1))] with t ht1 ht2 ht3
  intro x v hx hx1 hv
  have hv' := abs_le.mp hv
  have ht0 : 0 < t := by linarith only [ht3, Real.exp_pos (Real.exp 1)]
  have hγ : Real.exp (Real.exp 1) ≤ t + v := by linarith only [ht3, hv'.1]
  have hγ0 : 0 < t + v := (Real.exp_pos _).trans_le hγ
  have hγ2 : t + v ≤ 2 * t := by linarith only [hv'.2, ht0]
  have hlog : Real.exp 1 ≤ Real.log (t + v) :=
    (Real.le_log_iff_exp_le hγ0).mpr hγ
  have hlog0 : 0 < Real.log (t + v) := (Real.exp_pos 1).trans_le hlog
  have hll : 1 ≤ Real.log (Real.log (t + v)) :=
    (Real.le_log_iff_exp_le hlog0).mpr hlog
  have hlog2 : Real.log (t + v) ≤ Real.log (2 * t) :=
    Real.log_le_log hγ0 hγ2
  have hwidth : η / Real.log (2 * t) ≤ η / Real.log (t + v) :=
    div_le_div_of_nonneg_left hη.le hlog0 hlog2
  have hlow : 1 - η / Real.log (t + v) ≤ x := by linarith only [hx, hwidth]
  have hz' : riemannZeta ((x : ℂ) + (t + v) * I) ≠ 0 := by
    by_cases hx2 : x ≤ 1
    · apply hz x (t + v) (by rw [abs_of_pos hγ0]; linarith only [ht1, hv'.1]) hx2
      rw [abs_of_pos hγ0, mul_div_assoc]
      linarith only [hlow, div_pos hη hlog0]
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using lt_of_not_ge hx2)
  refine ⟨hz', ?_⟩
  have hb := hd x (t + v) (by rw [abs_of_pos hγ0]; linarith only [ht2, hv'.1])
    (by simpa only [abs_of_pos hγ0] using hlow) hx1
  rw [abs_of_pos hγ0] at hb
  have hlogt : Real.log (t + v) ≤ 2 * (1 + t) := by
    have hh := Real.log_le_self hγ0.le
    linarith only [hh, hγ2]
  calc
    _ ≤ C * Real.log (t + v) ^ 2 / Real.log (Real.log (t + v)) := hb
    _ ≤ C * Real.log (t + v) ^ 2 := div_le_self (by positivity) hll
    _ ≤ C * (2 * (1 + t)) ^ 2 := by gcongr
    _ = _ := by ring

private theorem norm_vertical_integral_le_rect {G : ℂ → ℂ} {c r K : ℝ}
    (hG : DifferentiableOn ℂ G (uIcc c r ×ℂ uIcc (-K) K)) :
    ‖∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ ≤
      ‖∫ v in (-K)..K, G ((c : ℂ) + v * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + (-K : ℝ) * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + K * I)‖ := by
  have h := Sieve.integral_vertical_sub_eq_horizontal_rect K hG
  set R := ∫ v in (-K)..K, G ((r : ℂ) + v * I)
  set L := ∫ v in (-K)..K, G ((c : ℂ) + v * I)
  set Bt := ∫ x in c..r, G ((x : ℂ) + (-K : ℝ) * I)
  set Tp := ∫ x in c..r, G ((x : ℂ) + K * I)
  have he : I • R = I • L - Bt + Tp := by
    change I • R - I • L = Tp - Bt at h
    linear_combination h
  have hn : ‖R‖ = ‖I • R‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn, he]
  calc
    _ ≤ ‖I • L - Bt‖ + ‖Tp‖ := norm_add_le _ _
    _ ≤ ‖I • L‖ + ‖Bt‖ + ‖Tp‖ := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]

private theorem norm_integral_le_shifted_rectangle {G : ℂ → ℂ}
    {A b c r K V E : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hcr : c ≤ r)
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hGi : Integrable (fun v : ℝ => G ((r : ℂ) + v * I)))
    (hGd : DifferentiableOn ℂ G (uIcc c r ×ℂ uIcc (-K) K))
    (hline : ∀ v : ℝ, ‖G ((r : ℂ) + v * I)‖ ≤
      A * Real.exp (b * r) * E * Real.exp (-(|v| / 2)))
    (hrect : ∀ x v : ℝ, c ≤ x → x ≤ r → |v| ≤ K →
      ‖G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * x) * V * Real.exp (-(|v| / 2))) :
    ‖∫ v : ℝ, G ((r : ℂ) + v * I)‖ ≤ A *
      (Real.exp (b * c) * V * (2 * K) +
        Real.exp (b * r) * V * Real.exp (-(K / 2)) * (2 * (r - c)) +
        Real.exp (b * r) * E * Real.exp (-(K / 4)) *
          ∫ v : ℝ, Real.exp (-((1 / 4 : ℝ) * |v|))) := by
  have hleft : ‖∫ v in (-K)..K, G ((c : ℂ) + v * I)‖ ≤
      A * Real.exp (b * c) * V * (2 * K) := by
    have hpt : ∀ v ∈ uIoc (-K) K,
        ‖G ((c : ℂ) + v * I)‖ ≤ A * Real.exp (b * c) * V := by
      intro v hv
      rw [uIoc_of_le (by linarith only [hK])] at hv
      have hvK : |v| ≤ K := abs_le.mpr ⟨hv.1.le, hv.2⟩
      exact (hrect c v le_rfl hcr hvK).trans
        (mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (by linarith only [abs_nonneg v])))
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans_eq ?_
    rw [show K - -K = 2 * K by ring, abs_of_nonneg (by positivity)]
  have hedge (v : ℝ) (hv : |v| = K) :
      ‖∫ x in c..r, G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * r) * V * Real.exp (-(K / 2)) * (r - c) := by
    have hpt : ∀ x ∈ uIoc c r, ‖G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * r) * V * Real.exp (-(K / 2)) := by
      intro x hx
      rw [uIoc_of_le hcr] at hx
      have hh := hrect x v hx.1.le hx.2 hv.le
      rw [hv] at hh
      exact hh.trans (by gcongr)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans_eq ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hcr)]
  have htail := MoebiusAbel.norm_integral_sub_intervalIntegral_le hGi hK
    (by positivity : 0 ≤ A * Real.exp (b * r) * E) hline
  have hmid := (norm_vertical_integral_le_rect hGd).trans
    (add_le_add (add_le_add hleft (hedge (-K) (by rw [abs_neg, abs_of_nonneg hK])))
      (hedge K (abs_of_nonneg hK)))
  calc
    _ ≤ ‖∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ +
        ‖(∫ v : ℝ, G ((r : ℂ) + v * I)) -
          ∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ := by
      convert norm_add_le
        (∫ v in (-K)..K, G ((r : ℂ) + v * I))
        ((∫ v : ℝ, G ((r : ℂ) + v * I)) -
          ∫ v in (-K)..K, G ((r : ℂ) + v * I)) using 1 <;> congr 1 <;> abel
    _ ≤ _ := (add_le_add hmid htail).trans_eq (by ring)

end GaloisForLFunctions.ExceptionalLayerTheory
