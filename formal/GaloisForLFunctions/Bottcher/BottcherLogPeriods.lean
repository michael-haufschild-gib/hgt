/-
# The period group of `d log φ_c` on a disconnected basin

`ω = greenLogDeriv c` is the single-valued logarithmic derivative of the Böttcher coordinate on the
basin `Ω_c`.  A *basin loop* is a `2π`-periodic `C¹` map `ℝ → Ω_c`, and its period is
`∮ ω = ∫₀^{2π} ω(γ)·γ'`.

* **Upper bound.**  For a basin loop, `f_c^N ∘ γ` lies in the escape region once `2^N` times the
  minimum of `G_c` on the loop exceeds the escape threshold.  There `ω = φ_c'/φ_c`, so the period of
  `f_c^N ∘ γ` is the winding integral of `φ_c ∘ f_c^N ∘ γ` about `0`, an integer multiple of `2πi`,
  and self-similarity `ω(f_c^N z)·(f_c^N)'(z) = 2^N ω(z)` divides it by `2^N`.
* **Realization.**  For `c ∉ M` the depth-`j` lobe sections `Σ_j` below the critical level satisfy
  `G_c ∘ Σ_j = log‖·‖/2^j`, hence `ω(Σ_j v)·Σ_j'(v) = 1/(2^j v)`, and the loop
  `θ ↦ Σ_j(r e^{ikθ})` has period `2πi·k/2^j`.

So the period group is exactly `2πi·ℤ[1/2]`, and the multipliers `exp ∮ω` are exactly the dyadic
roots of unity.
-/
import GaloisForLFunctions.Bottcher.GreenLogDerivCalculus
import GaloisForLFunctions.Bottcher.SubCriticalChain
import GaloisForLFunctions.Bottcher.MontelIterates
import GaloisForLFunctions.Bottcher.SectionTowerStep
import GaloisForLFunctions.Bottcher.DyadicMonodromy

open Complex Set Filter Topology

namespace Bottcher

noncomputable section

/-- A closed `C¹` loop in the basin of infinity: a `2π`-periodic `C¹` map avoiding `K_c`. -/
structure BasinLoop (c : ℂ) where
  γ : ℝ → ℂ
  smooth : ContDiff ℝ 1 γ
  periodic : Function.Periodic γ (2 * Real.pi)
  mem : ∀ θ, γ θ ∉ filledJulia c

/-- The period `∮_γ ω` of the logarithmic derivative of `φ_c` along a basin loop. -/
def BasinLoop.period {c : ℂ} (ℓ : BasinLoop c) : ℂ :=
  ∫ θ in (0:ℝ)..(2 * Real.pi), greenLogDeriv c (ℓ.γ θ) * deriv ℓ.γ θ

/-- The dyadic roots of unity `μ_{2^∞}`. -/
def dyadicRootsOfUnity : Set ℂ := {ζ | ∃ N : ℕ, ζ ^ (2 ^ N) = 1}

/-- **Iterated self-similarity** `ω(f_c^n z)·(f_c^n)'(z) = 2^n ω(z)` on the basin. -/
theorem greenLogDeriv_iterate {c z : ℂ} (hz : z ∉ filledJulia c) (n : ℕ) :
    greenLogDeriv c ((quadratic c)^[n] z) * deriv (quadratic c)^[n] z =
      2 ^ n * greenLogDeriv c z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      have hfz : quadratic c z ∉ filledJulia c := fun h =>
        hz ((quadratic_mem_filledJulia_iff c z).mp h)
      have hd : deriv (quadratic c)^[n + 1] z =
          deriv (quadratic c)^[n] (quadratic c z) * (2 * z) := by
        rw [Function.iterate_succ, deriv_comp z (differentiable_quadratic_iterate c n _)
          (differentiable_quadratic c z), deriv_quadratic]
      rw [hd, Function.iterate_succ_apply, ← mul_assoc, ih hfz, mul_assoc,
        greenLogDeriv_quadratic hz, pow_succ]
      ring

theorem mem_escapeOpen_of_green_gt {c z : ℂ}
    (h : Real.log ((max 2 ‖c‖) ^ (2 : ℕ) + ‖c‖) + 1 < greenFunctionDyn c z) :
    z ∈ escapeOpen c := by
  by_contra hz
  have hle : ‖z‖ ≤ max 2 ‖c‖ := not_lt.mp hz
  linarith [greenFunctionDyn_le_small hle]

theorem BasinLoop.exists_Ico {c : ℂ} (ℓ : BasinLoop c) (θ : ℝ) :
    ∃ θ' ∈ Ico (0:ℝ) (2 * Real.pi), ℓ.γ θ = ℓ.γ θ' :=
  ℓ.periodic.exists_mem_Ico₀ Real.two_pi_pos θ

theorem BasinLoop.continuous_deriv {c : ℂ} (ℓ : BasinLoop c) : Continuous (deriv ℓ.γ) :=
  ℓ.smooth.continuous_deriv le_rfl

theorem BasinLoop.hasDerivAt {c : ℂ} (ℓ : BasinLoop c) (θ : ℝ) :
    HasDerivAt ℓ.γ (deriv ℓ.γ θ) θ :=
  (ℓ.smooth.differentiable one_ne_zero θ).hasDerivAt

theorem differentiableOn_bottcherCoord_escape (c : ℂ) :
    DifferentiableOn ℂ (bottcherCoord c) (escapeOpen c) := fun _ hz =>
  (differentiableAt_bottcherCoord_escape hz).differentiableWithinAt

/-- **Every period is dyadic.**  The period of a basin loop is `2πi·k/2^N` for integers `k`, `N`. -/
theorem BasinLoop.exists_period_eq {c : ℂ} (ℓ : BasinLoop c) :
    ∃ N : ℕ, ∃ k : ℤ, ℓ.period = (k : ℂ) * (2 * Real.pi * Complex.I) / 2 ^ N := by
  have hcont : Continuous ℓ.γ := ℓ.smooth.continuous
  have hGcont : Continuous fun θ => greenFunctionDyn c (ℓ.γ θ) :=
    (continuous_greenFunctionDyn c).comp hcont
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by positivity : (0:ℝ) ≤ 2 * Real.pi)) hGcont.continuousOn
  set δ := greenFunctionDyn c (ℓ.γ θ₀) with hδdef
  have hδ : 0 < δ := lt_of_le_of_ne (greenFunctionDyn_nonneg c _)
    (fun h => ℓ.mem θ₀ ((greenFunctionDyn_eq_zero_iff c _).mp h.symm))
  have hmin' : ∀ θ, δ ≤ greenFunctionDyn c (ℓ.γ θ) := by
    intro θ
    obtain ⟨θ', hθ', hper⟩ := ℓ.exists_Ico θ
    rw [hper]
    exact hmin (Ico_subset_Icc_self hθ')
  set s₀ := Real.log ((max 2 ‖c‖) ^ (2 : ℕ) + ‖c‖) + 1
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (s₀ / δ) (by norm_num : (1:ℝ) < 2)
  have hesc : ∀ θ, (quadratic c)^[N] (ℓ.γ θ) ∈ escapeOpen c := by
    intro θ
    apply mem_escapeOpen_of_green_gt
    rw [greenFunctionDyn_iterate]
    have h1 : s₀ < 2 ^ N * δ := by
      rw [div_lt_iff₀ hδ] at hN
      linarith
    have h2 : 2 ^ N * δ ≤ 2 ^ N * greenFunctionDyn c (ℓ.γ θ) :=
      mul_le_mul_of_nonneg_left (hmin' θ) (by positivity)
    linarith
  -- the loop `u = φ_c ∘ f_c^N ∘ γ`
  set F : ℝ → ℂ := fun θ => (quadratic c)^[N] (ℓ.γ θ) with hFdef
  have hFcont : Continuous F := (differentiable_quadratic_iterate c N).continuous.comp hcont
  set u' : ℝ → ℂ := fun θ => deriv (bottcherCoord c) (F θ) *
    (deriv (quadratic c)^[N] (ℓ.γ θ) * deriv ℓ.γ θ) with hu'def
  have hu_deriv : ∀ θ, HasDerivAt (fun θ => bottcherCoord c (F θ)) (u' θ) θ := by
    intro θ
    have h2 : HasDerivAt (quadratic c)^[N] (deriv (quadratic c)^[N] (ℓ.γ θ)) (ℓ.γ θ) :=
      (differentiable_quadratic_iterate c N _).hasDerivAt
    have h3 : HasDerivAt (bottcherCoord c) (deriv (bottcherCoord c) (F θ)) (F θ) :=
      (differentiableAt_bottcherCoord_escape (hesc θ)).hasDerivAt
    exact h3.comp θ (h2.comp θ (ℓ.hasDerivAt θ))
  have hu'cont : Continuous u' := by
    have hd1 : Continuous fun θ => deriv (bottcherCoord c) (F θ) :=
      ((differentiableOn_bottcherCoord_escape c).deriv (isOpen_escapeOpen c)).continuousOn
        |>.comp_continuous hFcont hesc
    have hd2 : Continuous fun θ => deriv (quadratic c)^[N] (ℓ.γ θ) :=
      ((differentiable_quadratic_iterate c N).contDiff (n := 1)).continuous_deriv le_rfl
        |>.comp hcont
    exact hd1.mul (hd2.mul ℓ.continuous_deriv)
  let L : C1Loop :=
    { γ := fun θ => bottcherCoord c (F θ)
      γ' := u'
      cont := continuous_iff_continuousAt.mpr fun θ => (hu_deriv θ).continuousAt
      cont' := hu'cont
      deriv := fun θ _ => hu_deriv θ
      closed := by
        change bottcherCoord c ((quadratic c)^[N] (ℓ.γ (2 * Real.pi))) =
          bottcherCoord c ((quadratic c)^[N] (ℓ.γ 0))
        rw [show (2 * Real.pi) = 0 + 2 * Real.pi by ring, ℓ.periodic 0] }
  have hA : L.Avoids 0 := fun θ => bottcherCoord_ne_zero c _
  obtain ⟨k, hk⟩ := exists_int_windInt L hA
  have hwind : windInt L 0 = 2 ^ N * ℓ.period := by
    unfold windInt BasinLoop.period
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change (bottcherCoord c (F θ) - 0)⁻¹ * u' θ =
      2 ^ N * (greenLogDeriv c (ℓ.γ θ) * deriv ℓ.γ θ)
    have hlog : (bottcherCoord c (F θ))⁻¹ * deriv (bottcherCoord c) (F θ) =
        greenLogDeriv c (F θ) := by
      rw [greenLogDeriv_eq_logDeriv_bottcherCoord (hesc θ), logDeriv_apply, div_eq_inv_mul]
    have hself := greenLogDeriv_iterate (ℓ.mem θ) N
    rw [sub_zero]
    calc (bottcherCoord c (F θ))⁻¹ * u' θ =
          ((bottcherCoord c (F θ))⁻¹ * deriv (bottcherCoord c) (F θ)) *
            deriv (quadratic c)^[N] (ℓ.γ θ) * deriv ℓ.γ θ := by
          simp only [hu'def]
          ring
      _ = greenLogDeriv c (F θ) * deriv (quadratic c)^[N] (ℓ.γ θ) * deriv ℓ.γ θ := by
          rw [hlog]
      _ = 2 ^ N * (greenLogDeriv c (ℓ.γ θ) * deriv ℓ.γ θ) := by
          rw [hself]
          ring
  refine ⟨N, k, ?_⟩
  rw [hwind] at hk
  rw [eq_div_iff (pow_ne_zero _ two_ne_zero)]
  linear_combination hk

/-- **Every dyadic period is realized.**  For `c ∉ M` and integers `k`, `j` there is a basin loop
of period `2πi·k/2^j`: the image of the circle `θ ↦ r e^{ikθ}` under a depth-`j` lobe section. -/
theorem exists_basinLoop_period_eq {c : ℂ} (hc : Disconnected c) (j : ℕ) (k : ℤ) :
    ∃ ℓ : BasinLoop c, ℓ.period = (k : ℂ) * (2 * Real.pi * Complex.I) / 2 ^ j := by
  have h0 : (0:ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  set g0 := greenFunctionDyn c 0 with hg0def
  have hg0 : 0 < g0 := lt_of_le_of_ne (greenFunctionDyn_nonneg c 0)
    (fun h => h0 ((greenFunctionDyn_eq_zero_iff c 0).mp h.symm))
  obtain ⟨rlo, Rb, R₀, Rinj, h1, h2, h3, -, -, -, h7, -, S, -, -⟩ := exists_tower_deep c hg0 0
  have hrlo0 : 0 < rlo := by linarith
  have hrlo_exp : rlo < Real.exp (2 * g0) := by
    rw [← Real.log_lt_iff_lt_exp hrlo0]
    linarith
  set m := min R₀ (Real.exp (2 * g0)) with hmdef
  have hm : rlo < m := lt_min (by linarith) hrlo_exp
  set ra := rlo + (m - rlo) / 3 with hradef
  set rb := rlo + 2 * (m - rlo) / 3 with hrbdef
  have hra : rlo < ra := by rw [hradef]; linarith
  have hrb : ra < rb := by rw [hradef, hrbdef]; linarith
  have hrbm : rb < m := by rw [hrbdef]; linarith
  have hrbR : rb < R₀ := lt_of_lt_of_le hrbm (min_le_left _ _)
  have hrb2 : Real.log rb < 2 * g0 := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]
    exact lt_of_lt_of_le hrbm (min_le_right _ _)
  obtain ⟨Sj, han, hlev, -, -, -⟩ := exists_subcritical_chain S h1 hra hrb hrbR hrb2 j
  set r := (ra + rb) / 2 with hrdef
  have hr1 : ra < r := by rw [hrdef]; linarith
  have hr2 : r < rb := by rw [hrdef]; linarith
  have hrpos : 0 < r := by linarith
  set w : ℝ → ℂ := fun θ => circleMap 0 r ((k : ℝ) * θ) with hwdef
  have hw_mem : ∀ θ, w θ ∈ annulusSet ra rb := by
    intro θ
    simp only [annulusSet, Set.mem_setOf_eq, hwdef, _root_.norm_circleMap_zero, abs_of_pos hrpos]
    exact ⟨hr1, hr2⟩
  have hw0 : ∀ θ, w θ ≠ 0 := by
    intro θ h
    have := hw_mem θ
    rw [h] at this
    simp only [annulusSet, Set.mem_setOf_eq, norm_zero] at this
    linarith [this.1]
  have hw_deriv : ∀ θ, HasDerivAt w ((k : ℂ) * (w θ * Complex.I)) θ := by
    intro θ
    have h := (hasDerivAt_circleMap 0 r ((k : ℝ) * θ)).scomp θ
      ((hasDerivAt_id θ).const_mul (k : ℝ))
    have heq : ((k : ℝ) * 1) • (circleMap 0 r ((k : ℝ) * θ) * Complex.I) =
        (k : ℂ) * (w θ * Complex.I) := by
      rw [Complex.real_smul]
      push_cast
      simp [hwdef]
    rw [heq] at h
    exact h
  have hwcont : ContDiff ℝ 1 w := by
    have : ContDiff ℝ 1 fun θ : ℝ => (k : ℝ) * θ := contDiff_const.mul contDiff_id
    exact (contDiff_circleMap 0 r).comp this
  have hSan : ContDiffOn ℝ 1 Sj (annulusSet ra rb) :=
    ((han.differentiableOn).contDiffOn (isOpen_annulusSet ra rb)).restrict_scalars ℝ
  have hmem : ∀ θ, Sj (w θ) ∉ filledJulia c := by
    intro θ hK
    have hG := hlev (w θ) (hw_mem θ)
    rw [(greenFunctionDyn_eq_zero_iff c _).mpr hK] at hG
    have hlog : 0 < Real.log ‖w θ‖ := by
      have := (hw_mem θ).1
      exact Real.log_pos (by linarith)
    have : 0 < Real.log ‖w θ‖ / 2 ^ j := by positivity
    linarith
  let ℓ : BasinLoop c :=
    { γ := fun θ => Sj (w θ)
      smooth := hSan.comp_contDiff hwcont hw_mem
      periodic := by
        intro θ
        change Sj (circleMap 0 r ((k : ℝ) * (θ + 2 * Real.pi))) =
          Sj (circleMap 0 r ((k : ℝ) * θ))
        rw [mul_add, ((periodic_circleMap 0 r).int_mul k) ((k : ℝ) * θ)]
      mem := hmem }
  refine ⟨ℓ, ?_⟩
  have hlev' : ∀ v ∈ annulusSet ra rb,
      greenFunctionDyn c (Sj v) = (1 / 2 ^ j : ℝ) * Real.log ‖v‖ := by
    intro v hv
    rw [hlev v hv]
    ring
  have hint : ∀ θ, greenLogDeriv c (ℓ.γ θ) * deriv ℓ.γ θ =
      (k : ℂ) * Complex.I / 2 ^ j := by
    intro θ
    have hSd : HasDerivAt Sj (deriv Sj (w θ)) (w θ) :=
      ((han (w θ) (hw_mem θ)).differentiableAt).hasDerivAt
    have hd : deriv ℓ.γ θ = deriv Sj (w θ) * ((k : ℂ) * (w θ * Complex.I)) :=
      (hSd.comp θ (hw_deriv θ)).deriv
    have hkey := greenLogDeriv_mul_deriv_of_level (isOpen_annulusSet ra rb) hlev'
      (hw_mem θ) (hw0 θ) (han (w θ) (hw_mem θ)).differentiableAt (hmem θ)
    change greenLogDeriv c (Sj (w θ)) * deriv ℓ.γ θ = _
    rw [hd, ← mul_assoc, hkey]
    push_cast
    field_simp [hw0 θ]
  rw [BasinLoop.period, intervalIntegral.integral_congr (fun θ _ => hint θ),
    intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- **The period group of `d log φ_c` is `2πi·ℤ[1/2]`.** -/
theorem exists_basinLoop_period_iff {c : ℂ} (hc : Disconnected c) (P : ℂ) :
    (∃ ℓ : BasinLoop c, ℓ.period = P) ↔
      ∃ N : ℕ, ∃ k : ℤ, P = (k : ℂ) * (2 * Real.pi * Complex.I) / 2 ^ N := by
  constructor
  · rintro ⟨ℓ, rfl⟩
    exact ℓ.exists_period_eq
  · rintro ⟨N, k, rfl⟩
    exact exists_basinLoop_period_eq hc N k

theorem exp_dyadic_period_mem (N : ℕ) (k : ℤ) :
    Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I) / 2 ^ N) ∈ dyadicRootsOfUnity := by
  refine ⟨N, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((2 ^ N : ℕ) : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I) / 2 ^ N) =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- **The scalar monodromy image is the Prüfer `2`-group.**  The multipliers `exp ∮ω` of basin loops
are exactly the dyadic roots of unity. -/
theorem exists_basinLoop_exp_period_iff {c : ℂ} (hc : Disconnected c) (ζ : ℂ) :
    (∃ ℓ : BasinLoop c, Complex.exp ℓ.period = ζ) ↔ ζ ∈ dyadicRootsOfUnity := by
  constructor
  · rintro ⟨ℓ, rfl⟩
    obtain ⟨N, k, hP⟩ := ℓ.exists_period_eq
    rw [hP]
    exact exp_dyadic_period_mem N k
  · rintro ⟨N, hN⟩
    have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 ^ N : ℕ) : ℂ)))
        (2 ^ N) := Complex.isPrimitiveRoot_exp (2 ^ N) (pow_ne_zero N two_ne_zero)
    haveI : NeZero (2 ^ N) := ⟨pow_ne_zero N two_ne_zero⟩
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hN
    obtain ⟨ℓ, hℓ⟩ := exists_basinLoop_period_eq hc N (i : ℤ)
    refine ⟨ℓ, ?_⟩
    rw [hℓ, ← hi, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- **Dyadic multipliers of every order.**  For every `n` some basin loop has multiplier
`exp(2πi/2^n)`, a primitive `2^n`-th root of unity. -/
theorem exists_basinLoop_exp_period_eq_dyadicRoot {c : ℂ} (hc : Disconnected c) (n : ℕ) :
    ∃ ℓ : BasinLoop c, Complex.exp ℓ.period =
      Complex.exp (2 * Real.pi * Complex.I / 2 ^ n) := by
  obtain ⟨ℓ, hℓ⟩ := exists_basinLoop_period_eq hc n 1
  exact ⟨ℓ, by rw [hℓ]; push_cast; ring_nf⟩

/-- **Infinitely many multipliers.**  The multipliers of the continuation of `φ_c` around basin
loops form an infinite set: their orders `2^n` are unbounded. -/
theorem infinite_basinLoop_multipliers {c : ℂ} (hc : Disconnected c) :
    {ζ : ℂ | ∃ ℓ : BasinLoop c, Complex.exp ℓ.period = ζ}.Infinite := by
  have heq : {ζ : ℂ | ∃ ℓ : BasinLoop c, Complex.exp ℓ.period = ζ} = dyadicRootsOfUnity := by
    ext ζ
    exact exists_basinLoop_exp_period_iff hc ζ
  rw [heq]
  have hinj : Function.Injective fun n : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) := by
    intro a b hab
    have h := congrArg orderOf hab
    simp only at h
    rw [orderOf_dyadicRoot, orderOf_dyadicRoot] at h
    exact Nat.pow_right_injective le_rfl h
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  have h := exp_dyadic_period_mem n 1
  convert h using 2
  push_cast
  ring

end

end Bottcher
