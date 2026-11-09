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
        rw [show -(δ * |v|) = δ + -(δ * (1 + |v|)) by ring, Real.exp_add]
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
      exact mul_le_mul_of_nonneg_left (hgauss y x v hy hx1 hx2) (by positivity)
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
    rw [show logDeriv riemannZeta = (fun z => deriv riemannZeta z / riemannZeta z) by
      funext z; rw [logDeriv_apply]]
    exact hza.deriv.differentiableAt.div hza.differentiableAt hz
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
      riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I)‖ ≤ D * (1 + t) ^ 2 := by
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
  have hz' : riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I) ≠ 0 := by
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
      exact hh.trans (by gcongr; exact hx.2)
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
          ∫ v in (-K)..K, G ((r : ℂ) + v * I)) using 1
      congr 1
      abel
    _ ≤ _ := (add_le_add hmid htail).trans_eq (by ring)

/-- A local contour shift separates the zero-free saving from the exponentially
smaller truncation error, uniformly in the damping spacing. -/
theorem exists_primeDampingFilter_local_shift_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a η r : ℝ) (hσ : σ < 1) (ha : 0 < a)
    (hη : 0 < η) (hr : 1 < r) (hr1 : r ≤ 9 / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 3) *
          (Real.exp (a * t * (1 - σ - η / Real.log (2 * t)) / 2) +
            Real.exp (a * t * (r - σ) / 2 - t / 8)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let l := (1 - σ) / 2
  let u := r - σ
  have hl : 0 < l := by dsimp only [l]; linarith only [hσ]
  have hu : 0 < u := by dsimp only [u]; linarith only [hσ, hr]
  obtain ⟨A, hA, hkernel⟩ := exists_divisorFilter_kernel_strip_envelope F ρ σ β l u hl
  obtain ⟨D, hD, hrectangle⟩ := eventually_zeta_local_rectangle η hη
  let E := (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r) + 1
  have hE : 0 < E := by
    have hs : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r :=
      tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    dsimp only [E]
    linarith only [hs]
  let J := ∫ v : ℝ, Real.exp (-((1 / 4 : ℝ) * |v|))
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  let B := D + 2 * u * D + E * J + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  let k := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp only [k]; positivity
  refine ⟨k * A * B, by positivity, ?_⟩
  have hloglim : Tendsto (fun t : ℝ => Real.log (2 * t)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hsmall : ∀ᶠ t : ℝ in atTop, η / Real.log (2 * t) < l :=
    (hloglim.const_div_atTop η).eventually (gt_mem_nhds hl)
  filter_upwards [hrectangle, hsmall, eventually_ge_atTop (2 : ℝ)] with t htR htη ht2
  intro h hh hh1
  have ht : 0 < t := by linarith only [ht2]
  have htlog : 0 < Real.log (2 * t) := Real.log_pos (by linarith only [ht2])
  let c := 1 - σ - η / Real.log (2 * t)
  have hcl : l ≤ c := by dsimp only [c, l] at *; linarith only [htη]
  have hc : 0 < c := hl.trans_le hcl
  have hcu : c ≤ u := by
    dsimp only [c, u]
    linarith only [div_pos hη htlog, hr]
  let s : ℂ := (σ : ℂ) + t * I
  let P := divisorDampingFilter F ρ β h
  let G := filteredMellinIntegrand P s β h (Real.exp (-a * t))
  let M := A * h ^ d * (1 + t) ^ d
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hcoord (x v : ℝ) : s + ((x : ℂ) + v * I) =
      ((σ + x : ℝ) : ℂ) + ((t + v : ℝ) : ℂ) * I := by dsimp only [s]; push_cast; ring
  have hre (v : ℝ) : (s + ((u : ℂ) + v * I)).re = r := by
    rw [hcoord]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    dsimp only [u]
    ring
  have heuler (v : ℝ) :
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s + ((u : ℂ) + v * I)) = -logDeriv riemannZeta (s + ((u : ℂ) + v * I)) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by rw [hre]; exact hr), logDeriv_apply, neg_div]
  have hL (v : ℝ) : ‖logDeriv riemannZeta (s + ((u : ℂ) + v * I))‖ ≤ E := by
    have hn := norm_LSeries_vonMangoldt_le
      (s := s + ((u : ℂ) + v * I)) (by rw [hre]; exact hr)
    rw [heuler, norm_neg, hre] at hn
    exact hn.trans (by dsimp only [E]; linarith)
  have hK (x v : ℝ) (hx : l ≤ x) (hx1 : x ≤ u) :
      ‖P.eval (Complex.exp ((h : ℂ) * (s + ((x : ℂ) + v * I) - β))) *
        gaussianMBKernel (Real.exp (-a * t)) ((x : ℂ) + v * I)‖ ≤
      M * Real.exp (a * t * x / 2) * Real.exp (-(|v| / 2)) := by
    have he : (Real.exp (-a * t)) ^ (-(x / 2)) = Real.exp (a * t * x / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    simpa only [P, s, M, d, abs_of_pos ht, he] using
      hkernel (Real.exp (-a * t)) h t x v (Real.exp_pos _) hh hh1 hx hx1
  have hline (v : ℝ) : ‖G ((u : ℂ) + v * I)‖ ≤
      M * Real.exp (a * t * u / 2) * E * Real.exp (-(|v| / 2)) := by
    change ‖(_ * _) * (-logDeriv riemannZeta (s + ((u : ℂ) + v * I)))‖ ≤ _
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (M * Real.exp (a * t * u / 2) * Real.exp (-(|v| / 2))) * E :=
        mul_le_mul (hK u v (hcl.trans hcu) le_rfl) (hL v) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGc : Continuous (fun v : ℝ => G ((u : ℂ) + v * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hs1 : s + ((u : ℂ) + v * I) ≠ 1 := by
      intro he
      have h := congrArg Complex.re he
      rw [hre, Complex.one_re] at h
      linarith only [h, hr]
    have hg : ContinuousAt G ((u : ℂ) + v * I) :=
      (differentiableAt_filteredMellinIntegrand P s β h
      (y := Real.exp (-a * t)) (Real.exp_pos _)
      (by simpa using hu) hs1
      (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hr))).continuousAt
    exact hg.comp (f := fun v : ℝ => (u : ℂ) + v * I) (by fun_prop)
  have hGi : Integrable (fun v : ℝ => G ((u : ℂ) + v * I)) := by
    have hi : Integrable (fun v : ℝ =>
        M * Real.exp (a * t * u / 2) * E * Real.exp (-(|v| / 2))) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        (integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
          (M * Real.exp (a * t * u / 2) * E)
    exact hi.mono' hGc.aestronglyMeasurable (Eventually.of_forall hline)
  have hrect (x v : ℝ) (hx : c ≤ x) (hx1 : x ≤ u) (hv : |v| ≤ t / 2) :
      ‖G ((x : ℂ) + v * I)‖ ≤
        M * Real.exp (a * t * x / 2) * (D * (1 + t) ^ 2) *
          Real.exp (-(|v| / 2)) := by
    have hb := (htR (σ + x) v
      (by dsimp only [c] at hx; linarith only [hx])
      (by dsimp only [u] at hx1; linarith only [hx1, hr1]) hv).2
    rw [← hcoord] at hb
    change ‖(_ * _) * (-logDeriv riemannZeta (s + ((x : ℂ) + v * I)))‖ ≤ _
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (M * Real.exp (a * t * x / 2) * Real.exp (-(|v| / 2))) *
          (D * (1 + t) ^ 2) :=
        mul_le_mul (hK x v (hcl.trans hx) hx1) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGd : DifferentiableOn ℂ G (uIcc c u ×ℂ uIcc (-(t / 2)) (t / 2)) := by
    intro w hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hw
    rw [uIcc_of_le hcu] at hwre
    rw [uIcc_of_le (by linarith only [ht])] at hwim
    have hv : |w.im| ≤ t / 2 := abs_le.mpr hwim
    have he : s + w = ((σ + w.re : ℝ) : ℂ) + ((t + w.im : ℝ) : ℂ) * I := by
      rw [← hcoord]
      congr 1
      exact (Complex.re_add_im w).symm
    have hzw := (htR (σ + w.re) w.im
      (by dsimp only [c] at hwre; linarith only [hwre.1])
      (by dsimp only [u] at hwre; linarith only [hwre.2, hr1]) hv).1
    rw [← he] at hzw
    have hs1 : s + w ≠ 1 := by
      intro hh
      have him := congrArg Complex.im hh
      simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        add_zero, zero_add, Complex.one_im] at him
      linarith only [him, hwim.1, ht]
    exact (differentiableAt_filteredMellinIntegrand P s β h (Real.exp_pos _)
      (hc.trans_le hwre.1) hs1 hzw).differentiableWithinAt
  have hscale (x : ℝ) : a * t / 2 * x = a * t * x / 2 := by ring
  have hbound := norm_integral_le_shifted_rectangle hM
    (by positivity : 0 ≤ a * t / 2) hcu (by positivity : 0 ≤ t / 2)
    (by positivity : 0 ≤ D * (1 + t) ^ 2) hE.le hGi hGd
    (by intro v; rw [hscale]; exact hline v)
    (by intro x v hx hx1 hv; rw [hscale]; exact hrect x v hx hx1 hv)
  have hid : primeDampingFilter P σ β a h t = (k : ℂ) * ∫ v : ℝ, G ((u : ℂ) + v * I) := by
    rw [primeDampingFilter_eq_euler_integral P σ β a h t u hu
      (by dsimp only [u]; linarith only [hr])]
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun v => ?_
    change _ = filteredMellinIntegrand P s β h (Real.exp (-a * t)) ((u : ℂ) + v * I)
    rw [filteredMellinIntegrand, ← heuler]
  let L := Real.exp (a * t * c / 2)
  let R := Real.exp (a * t * u / 2 - t / 8)
  have hL0 : 0 ≤ L := (Real.exp_pos _).le
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hp23 : (1 + t) ^ 2 ≤ (1 + t) ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg (1 + t)) ht.le]
  have hp3 : 1 ≤ (1 + t) ^ 3 := one_le_pow₀ (by linarith only [ht])
  have hleft : Real.exp (a * t / 2 * c) * (D * (1 + t) ^ 2) * (2 * (t / 2)) ≤
      D * (1 + t) ^ 3 * L := by
    have he : a * t / 2 * c = a * t * c / 2 := by ring
    rw [he]
    change L * (D * (1 + t) ^ 2) * (2 * (t / 2)) ≤ _
    have hp : (1 + t) ^ 2 * t ≤ (1 + t) ^ 3 := by
      nlinarith only [sq_nonneg (1 + t)]
    nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hD.le hL0)]
  have hedge : Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 2) *
        Real.exp (-(t / 2 / 2)) * (2 * (u - c)) ≤
      2 * u * D * (1 + t) ^ 3 * R := by
    calc
      _ ≤ Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 3) *
          Real.exp (-(t / 8)) * (2 * u) := by
        have he : Real.exp (-(t / 2 / 2)) ≤ Real.exp (-(t / 8)) :=
          Real.exp_le_exp.mpr (by linarith only [ht])
        have hp := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hp23 hD.le) (Real.exp_pos (a * t / 2 * u)).le
        exact mul_le_mul (mul_le_mul hp he (by positivity) (by positivity))
          (by linarith only [hc]) (by linarith only [hcu]) (by positivity)
      _ = _ := by
        dsimp only [R]
        rw [show a * t * u / 2 - t / 8 = a * t / 2 * u + -(t / 8) by ring,
          Real.exp_add]
        ring
  have htail : Real.exp (a * t / 2 * u) * E * Real.exp (-(t / 2 / 4)) * J ≤
      E * J * (1 + t) ^ 3 * R := by
    calc
      _ = E * J * R := by
        dsimp only [R]
        rw [show a * t * u / 2 - t / 8 = a * t / 2 * u + -(t / 2 / 4) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hp3 (by positivity : 0 ≤ E * J * R)]
  have hDB : D ≤ B := by
    have hh : 0 ≤ 2 * u * D + E * J + 1 := by positivity
    dsimp only [B]
    linarith only [hh]
  have hEB : 2 * u * D + E * J ≤ B := by dsimp only [B]; linarith only [hD]
  have hsum := add_le_add (add_le_add hleft hedge) htail
  have hsum' :
      Real.exp (a * t / 2 * c) * (D * (1 + t) ^ 2) * (2 * (t / 2)) +
      Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 2) * Real.exp (-(t / 2 / 2)) * (2 * (u - c)) +
      Real.exp (a * t / 2 * u) * E * Real.exp (-(t / 2 / 4)) * J ≤
        B * (1 + t) ^ 3 * (L + R) := by
    refine hsum.trans ?_
    calc
      _ = (1 + t) ^ 3 * (D * L + (2 * u * D + E * J) * R) := by ring
      _ ≤ (1 + t) ^ 3 * (B * L + B * R) := by gcongr
      _ = _ := by ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    _ ≤ k * (M * (B * (1 + t) ^ 3 * (L + R))) :=
      mul_le_mul_of_nonneg_left (hbound.trans
        (mul_le_mul_of_nonneg_left hsum' hM)) hk.le
    _ = _ := by
      change k * (M * (B * (1 + t) ^ 3 * (L + R))) =
        (k * A * B) * h ^ d * (1 + t) ^ (d + 3) * (L + R)
      dsimp only [M]
      rw [pow_add]
      ring

/-- Every fixed inverse-logarithmic saving is available unconditionally for
the complete arithmetic filter, uniformly in its spacing. -/
theorem exists_primeDampingFilter_zero_free_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a b : ℝ) (hσ : σ < 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 3) *
            Real.exp (a * (1 - σ) * t / 2 - b * t / Real.log (2 * t)) := by
  classical
  let ε := min (1 / 16 : ℝ) (1 / (16 * a))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 16 := min_le_left _ _
  have hεa : a * ε / 2 ≤ 1 / 32 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * a)).mp (min_le_right (1 / 16) (1 / (16 * a)))
    change ε * (16 * a) ≤ 1 at hh
    nlinarith only [hh]
  let η := 2 * b / a
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_primeDampingFilter_local_shift_bound
    F ρ σ β a η (1 + ε) hσ ha hη (by linarith only [hε])
      (by linarith only [hε1])
  refine ⟨2 * C, by positivity, ?_⟩
  have hloglim : Tendsto (fun t : ℝ => Real.log (2 * t)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hsmall : ∀ᶠ t : ℝ in atTop, b / Real.log (2 * t) < 1 / 16 :=
    (hloglim.const_div_atTop b).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hbound, hsmall, eventually_ge_atTop (2 : ℝ)] with t ht htlog ht2
  intro h hh hh1
  have ht0 : 0 ≤ t := by linarith only [ht2]
  have hlog : 0 < Real.log (2 * t) := Real.log_pos (by linarith only [ht2])
  have hleft : a * t * (1 - σ - η / Real.log (2 * t)) / 2 =
      a * (1 - σ) * t / 2 - b * t / Real.log (2 * t) := by
    dsimp only [η]
    field_simp [ha.ne', hlog.ne']
  have hright : a * t * (1 + ε - σ) / 2 - t / 8 ≤
      a * (1 - σ) * t / 2 - b * t / Real.log (2 * t) := by
    have he := mul_le_mul_of_nonneg_right hεa ht0
    have hb' := mul_le_mul_of_nonneg_right htlog.le ht0
    have heq : b * t / Real.log (2 * t) = (b / Real.log (2 * t)) * t := by ring
    rw [heq]
    nlinarith only [he, hb', ht0]
  have ht' := ht h hh hh1
  rw [hleft] at ht'
  refine ht'.trans ?_
  calc
    _ ≤ C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
        (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 3) *
          (Real.exp (a * (1 - σ) * t / 2 - b * t / Real.log (2 * t)) +
            Real.exp (a * (1 - σ) * t / 2 - b * t / Real.log (2 * t))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (Real.exp_le_exp.mpr hright)) (by positivity)
    _ = _ := by ring

private theorem tendsto_polynomial_mul_exp_neg_div_log (n : ℕ)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => (1 + t) ^ n * Real.exp (-(b * t / Real.log (2 * t))))
      atTop (𝓝 0) := by
  have hloglim : Tendsto (fun t : ℝ => Real.log (2 * t)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hloglim
  have hsmall : ∀ᶠ t : ℝ in atTop,
      Real.log (2 * t) ^ 2 * Real.exp (-Real.log (2 * t)) < b / (2 * ((n : ℝ) + 1)) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  refine squeeze_zero' ?_ ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.comp hloglim)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with t ht ht2
    have ht0 : 0 < 2 * t := by linarith only [ht2]
    have hu : 0 < Real.log (2 * t) := Real.log_pos (by linarith only [ht2])
    have hh := ht.le
    rw [Real.exp_neg, Real.exp_log ht0, ← div_eq_mul_inv,
      div_le_div_iff₀ ht0 (by positivity : 0 < 2 * ((n : ℝ) + 1))] at hh
    have hq : ((n : ℝ) + 1) * Real.log (2 * t) ≤ b * t / Real.log (2 * t) := by
      apply (le_div_iff₀ hu).mpr
      nlinarith only [hh]
    calc
      _ ≤ (2 * t) ^ n * Real.exp (-(b * t / Real.log (2 * t))) := by
        gcongr
        linarith only [ht2]
      _ = Real.exp ((n : ℝ) * Real.log (2 * t) - b * t / Real.log (2 * t)) := by
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log ht0, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hq])

/-- The complete filtered prime current tends to zero at the critical
contraction rate as well as above it. -/
theorem tendsto_primeDampingFilter_zero_of_critical_contraction (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a κ : ℝ) (hσ : σ < 1) (ha : 0 < a) (hκ : 0 < κ)
    (hrate : a * (1 - σ) / 2 ≤
      ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) : ℝ) * κ) :
    Tendsto (fun t : ℝ => primeDampingFilter
      (divisorDampingFilter F ρ β (Real.exp (-κ * t))) σ β a (Real.exp (-κ * t)) t)
      atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨C, hC, hbound⟩ := exists_primeDampingFilter_zero_free_bound F ρ σ β a 1
    hσ ha zero_lt_one
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := (tendsto_polynomial_mul_exp_neg_div_log (d + 3) zero_lt_one).const_mul C
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hbound, eventually_ge_atTop (2 : ℝ)] with t ht ht2
  have ht0 : 0 ≤ t := by linarith only [ht2]
  have hh1 : Real.exp (-κ * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [hκ, ht0])
  have hh := ht (Real.exp (-κ * t)) (Real.exp_pos _).le hh1
  have he : (Real.exp (-κ * t)) ^ d *
      Real.exp (a * (1 - σ) * t / 2 - 1 * t / Real.log (2 * t)) ≤
        Real.exp (-(1 * t / Real.log (2 * t))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hrate ht0
    change a * (1 - σ) / 2 * t ≤ (d : ℝ) * κ * t at hh
    nlinarith only [hh]
  refine hh.trans ?_
  calc
    _ = C * (1 + t) ^ (d + 3) * ((Real.exp (-κ * t)) ^ d *
        Real.exp (a * (1 - σ) * t / 2 - 1 * t / Real.log (2 * t))) := by ring
    _ ≤ C * (1 + t) ^ (d + 3) * Real.exp (-(1 * t / Real.log (2 * t))) := by
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

#print axioms exists_weighted_gaussianMBKernel_strip_envelope
#print axioms exists_divisorFilter_kernel_strip_envelope
#print axioms eventually_zeta_local_rectangle
#print axioms exists_primeDampingFilter_local_shift_bound
#print axioms exists_primeDampingFilter_zero_free_bound
#print axioms tendsto_primeDampingFilter_zero_of_critical_contraction

end GaloisForLFunctions.ExceptionalLayerTheory
