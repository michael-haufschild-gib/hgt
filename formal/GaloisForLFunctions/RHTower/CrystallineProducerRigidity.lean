import GaloisForLFunctions.RHTower.ZetaSpectrumAtomicSeries
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.HTGeometry.HamburgerCriticalLine

/-!
# Crystalline Weil-positive producers

A weight system `lam` whose Weil function is an atomic Herglotz series on the zeta spectrum is
von Mangoldt's, and its existence is equivalent to the Riemann hypothesis.

Suppose `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = Φ̃(s)` on `Re s > 1`.  Here
`Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s` is the archimedean datum of `ζ`, and
`Φ̃(s) = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` has atoms at ordinates of zeros of `ζ(½ + it)`.
Then `lam = Λ` and RH holds (`crystalline_producer_rigidity`).  No hypothesis on the other zeros
of `ζ` is used.

* `D = Σ (lam − Λ)(n) n^{−s}` equals `ξ'/ξ − Φ̃`, which is odd under `s ↦ 1 − s`.
* `ζ D` has Dirichlet coefficients `1 ⋆ (lam − Λ)`.  After multiplying by `Γ_ℝ` it becomes
  `Λ ξ'/ξ − Λ Φ̃`, in which the zeros of `ζ` cancel every pole.  The residue at `s = 1` is split off
  as `β Γ_ℝ(s − 1)` (`differentiableOn_crystallineRemainder`).
* The remainder decays on `½ ≤ Re s ≤ 3/2` (`exists_decay_crystallineRemainder`) and is odd across
  the critical line.  The odd Hamburger theorem `coeff_eq_zero_of_critical_line_odd` gives
  `1 ⋆ (lam − Λ) = 0` (`crystallineCoeff_eq_zero`).
* Then `Λ ξ'/ξ = Λ Φ̃`.  Off the line `Φ̃` is holomorphic, so `Λ' = Λ (Φ̃ − 1/s − 1/(s − 1))`.  A zero
  of `Λ` there would be a non-isolated zero (`eventually_eq_zero_of_deriv_eq_mul`), which is
  impossible (`riemannHypothesis_of_completedZetaXiLogDeriv_eq`).
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- `Λ · ξ'/ξ = Λ' + Λ (1/s + 1/(s − 1))`, written through the entire part `Λ₀`; its only poles
are simple poles at `0` and `1`. -/
noncomputable def completedZetaXiLogDeriv (s : ℂ) : ℂ :=
  deriv completedRiemannZeta₀ s + completedRiemannZeta₀ s * (1 / s + 1 / (s - 1))

theorem hasDerivAt_completedRiemannZeta_of_ne {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    HasDerivAt completedRiemannZeta
      (deriv completedRiemannZeta₀ s + 1 / s ^ 2 - 1 / (1 - s) ^ 2) s := by
  have e : completedRiemannZeta = fun z => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
    funext completedRiemannZeta_eq
  rw [e]
  have h1' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha := (differentiable_completedZeta₀ s).hasDerivAt
  have hb : HasDerivAt (fun z : ℂ => 1 / z) (-(1 / s ^ 2)) s := by
    simpa [one_div] using hasDerivAt_inv h0
  have hc : HasDerivAt (fun z : ℂ => 1 / (1 - z)) (1 / (1 - s) ^ 2) s := by
    have h2 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
    have := (hasDerivAt_inv h1').comp s h2
    have e2 : ((fun y : ℂ => y⁻¹) ∘ HSub.hSub 1) = fun z : ℂ => 1 / (1 - z) := by
      funext z; simp [Function.comp]
    rw [e2] at this
    exact this.congr_deriv (by ring)
  have hsum : HasDerivAt (fun z => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z))
      (deriv completedRiemannZeta₀ s - -(1 / s ^ 2) - 1 / (1 - s) ^ 2) s := (ha.sub hb).sub hc
  exact hsum.congr_deriv (by ring)

theorem completedZetaXiLogDeriv_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedZetaXiLogDeriv s =
      deriv completedRiemannZeta s + completedRiemannZeta s * (1 / s + 1 / (s - 1)) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [(hasDerivAt_completedRiemannZeta_of_ne h0 h1).deriv, completedRiemannZeta_eq,
    completedZetaXiLogDeriv]
  have : (1 : ℂ) - s = -(s - 1) := by ring
  rw [this]
  field_simp
  ring

/-- `Λ ξ'/ξ` is odd under `s ↦ 1 − s`. -/
theorem completedZetaXiLogDeriv_one_sub (s : ℂ) :
    completedZetaXiLogDeriv (1 - s) = -completedZetaXiLogDeriv s := by
  have hd : deriv completedRiemannZeta₀ (1 - s) = -deriv completedRiemannZeta₀ s := by
    have h := deriv_comp_const_sub completedRiemannZeta₀ 1 s
    have hf : (fun x => completedRiemannZeta₀ (1 - x)) = completedRiemannZeta₀ :=
      funext completedRiemannZeta₀_one_sub
    rw [hf] at h
    rw [h, neg_neg]
  have hq : (1 : ℂ) / (1 - s) + 1 / (1 - s - 1) = -(1 / s + 1 / (s - 1)) := by
    rw [show (1 : ℂ) - s - 1 = -s by ring, show (1 : ℂ) - s = -(s - 1) by ring, div_neg, div_neg]
    ring
  unfold completedZetaXiLogDeriv
  rw [hd, completedRiemannZeta₀_one_sub, hq]
  ring

theorem differentiable_deriv_completedRiemannZeta₀ :
    Differentiable ℂ (deriv completedRiemannZeta₀) := fun s =>
  ((differentiable_completedZeta₀.differentiableOn.deriv isOpen_univ) s
    (mem_univ s)).differentiableAt (isOpen_univ.mem_nhds (mem_univ s))

theorem differentiableAt_completedZetaXiLogDeriv {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedZetaXiLogDeriv s := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold completedZetaXiLogDeriv
  exact (differentiable_deriv_completedRiemannZeta₀ s).add ((differentiable_completedZeta₀ s).mul
    (((differentiableAt_const _).div differentiableAt_id h0).add
      ((differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) h1')))

/-- Off the critical line the atom denominators are bounded below by a multiple of `t²`, locally
uniformly: `(w − ½)² + t² = (w − ½ − it)(w − ½ + it)`, each factor is at least `Re w − ½` and, for
large `t`, at least `t/2`. -/
theorem exists_atomDenom_lower_bound {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) :
    ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ t : ℝ, 1 ≤ t → ∀ w ∈ ball s₀ r,
      κ * t ^ 2 ≤ ‖(w - 1 / 2) ^ 2 + (t : ℂ) ^ 2‖ := by
  set r := (s₀.re - 1 / 2) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set M := |s₀.im| + r + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg s₀.im; linarith
  refine ⟨r, min (1 / 4) (r ^ 2 / (4 * M ^ 2)), hr0, lt_min (by norm_num) (by positivity),
    fun t ht w hw => ?_⟩
  rw [mem_ball, dist_eq_norm] at hw
  have hre : r ≤ w.re - 1 / 2 := by
    have := (Complex.abs_re_le_norm (w - s₀)).trans hw.le
    rw [Complex.sub_re] at this
    have := abs_le.mp this
    rw [hr] at this ⊢
    linarith [this.1]
  have him : |w.im| ≤ M := by
    have := (Complex.abs_im_le_norm (w - s₀)).trans hw.le
    rw [Complex.sub_im] at this
    have h2 := abs_sub_abs_le_abs_sub w.im s₀.im
    rw [hM]; linarith
  rw [← sub_atomPoint_mul_sub_atomMirror, norm_mul]
  have hP1 : r ≤ ‖w - atomPoint t‖ := by
    have := Complex.abs_re_le_norm (w - atomPoint t)
    rw [Complex.sub_re, atomPoint_re] at this
    exact hre.trans ((le_abs_self _).trans this)
  have hQ1 : r ≤ ‖w - atomMirror t‖ := by
    have := Complex.abs_re_le_norm (w - atomMirror t)
    rw [Complex.sub_re, atomMirror_re] at this
    exact hre.trans ((le_abs_self _).trans this)
  have hP2 := norm_sub_atomPoint_ge (t := t) w
  have hQ2 := norm_sub_atomMirror_ge (t := t) w
  rw [abs_le] at him
  by_cases hbig : 2 * M ≤ t
  · have h1 : t / 2 ≤ ‖w - atomPoint t‖ := by
      have : t / 2 ≤ |w.im - t| := by
        rw [abs_sub_comm]; exact le_abs.mpr (Or.inl (by linarith))
      linarith
    have h2 : t / 2 ≤ ‖w - atomMirror t‖ := by
      have : t / 2 ≤ |w.im + t| := le_abs.mpr (Or.inl (by linarith))
      linarith
    calc min (1 / 4) (r ^ 2 / (4 * M ^ 2)) * t ^ 2 ≤ 1 / 4 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (t / 2) * (t / 2) := by ring
      _ ≤ _ := mul_le_mul h1 h2 (by linarith) (norm_nonneg _)
  · push Not at hbig
    calc min (1 / 4) (r ^ 2 / (4 * M ^ 2)) * t ^ 2 ≤ r ^ 2 / (4 * M ^ 2) * t ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ r ^ 2 / (4 * M ^ 2) * (2 * M) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hbig.le 2) (by positivity)
      _ = r * r := by field_simp; ring
      _ ≤ _ := mul_le_mul hP1 hQ1 hr0.le (norm_nonneg _)

/-- **The atomic series is holomorphic off the critical line** (on `Re s > ½`). -/
theorem differentiableOn_atomicPairSeries {c t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => |c j| / t j ^ 2) :
    DifferentiableOn ℂ (atomicPairSeries c t) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  obtain ⟨r, κ, hr, hκ, hb⟩ := exists_atomDenom_lower_bound hs₀
  have hts : DifferentiableOn ℂ
      (fun s : ℂ => ∑' j, (c j : ℂ) / ((s - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) (ball s₀ r) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun j => κ⁻¹ * (|c j| / t j ^ 2))
      (hsum.mul_left _) (fun j => ?_) isOpen_ball (fun j w hw => ?_)
    · refine (differentiableOn_const _).div (by fun_prop) (fun w hw => ?_)
      have := hb (t j) (hone j) w hw
      have ht := hone j
      have hpos : 0 < κ * t j ^ 2 := by positivity
      intro h0; rw [h0, norm_zero] at this; linarith
    · have hd := hb (t j) (hone j) w hw
      have ht := hone j
      have ht2 : 0 < t j ^ 2 := by positivity
      have hpos : 0 < ‖(w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2‖ :=
        lt_of_lt_of_le (by positivity) hd
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hpos]
      calc |c j| = κ⁻¹ * (|c j| / t j ^ 2) * (κ * t j ^ 2) := by field_simp
        _ ≤ κ⁻¹ * (|c j| / t j ^ 2) * ‖(w - 1 / 2) ^ 2 + (t j : ℂ) ^ 2‖ := by gcongr
  have hd : DifferentiableOn ℂ (atomicPairSeries c t) (ball s₀ r) := by
    unfold atomicPairSeries
    exact ((((differentiableOn_const _).mul (differentiableOn_id.sub
      (differentiableOn_const _))).div (differentiableOn_const _)
      (fun _ _ => by exact_mod_cast Real.pi_ne_zero))).mul hts
  exact (hd.differentiableAt (ball_mem_nhds s₀ hr)).differentiableWithinAt

theorem isOpen_re_gt (a : ℝ) : IsOpen {s : ℂ | a < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The residue coefficient `β = (Λ₀(1) − Φ̃(1))/2`.  `Λ (ξ'/ξ − Φ̃)` has residue `2β` at `s = 1`,
and `Γ_ℝ(s − 1)` has residue `2`. -/
noncomputable def crystallineResidue (c t : ℕ → ℝ) : ℂ :=
  (completedRiemannZeta₀ 1 - atomicPairSeries c t 1) / 2

/-- `Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)`, before removing its singularity at `s = 1`. -/
noncomputable def crystallineRemainderRaw (c t : ℕ → ℝ) (s : ℂ) : ℂ :=
  completedZetaXiLogDeriv s - atomicZetaPart c t s - crystallineResidue c t * Gammaℝ (s - 1)

/-- The remainder `Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)` with its removable singularity at `s = 1` filled. -/
noncomputable def crystallineRemainder (c t : ℕ → ℝ) : ℂ → ℂ :=
  Function.update (crystallineRemainderRaw c t) 1
    (limUnder (𝓝[≠] 1) (crystallineRemainderRaw c t))

theorem differentiableAt_Gammaℝ_sub_one {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => Gammaℝ (z - 1)) s := by
  have hΓ : DifferentiableAt ℂ Gamma ((s - 1) / 2) := by
    apply differentiableAt_Gamma
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      apply h1
      have h' : (s - 1) / 2 = 0 := by simpa using hm
      linear_combination 2 * h'
    · have := congrArg Complex.re hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      simp at this
      linarith
  have e : (fun z : ℂ => Gammaℝ (z - 1)) =
      fun z => (Real.pi : ℂ) ^ (-(z - 1) / 2) * Gamma ((z - 1) / 2) := by
    funext z; rw [Gammaℝ_def]
  rw [e]
  refine DifferentiableAt.mul ?_ ?_
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact hΓ.comp s (by fun_prop)

/-- `(s − 1) Γ_ℝ(s − 1) = 2 π^{−(s−1)/2} Γ((s − 1)/2 + 1)`. -/
theorem sub_one_mul_Gammaℝ_sub_one {s : ℂ} (h1 : s ≠ 1) :
    (s - 1) * Gammaℝ (s - 1) =
      2 * ((Real.pi : ℂ) ^ (-(s - 1) / 2) * Gamma ((s - 1) / 2 + 1)) := by
  have hne : (s - 1) / 2 ≠ 0 := by
    intro h; apply h1; linear_combination 2 * h
  rw [Gammaℝ_def, Complex.Gamma_add_one _ hne]
  ring

/-- The residue at `s = 1` cancels: `(s − 1) · (Λ ξ'/ξ − Λ Φ̃ − β Γ_ℝ(s − 1)) → 0`. -/
theorem tendsto_sub_one_mul_crystallineRemainderRaw {c t : ℕ → ℝ} (h : ZetaAtoms c t) :
    Tendsto (fun z => (z - 1) * crystallineRemainderRaw c t z) (𝓝[≠] 1) (𝓝 0) := by
  set Φ := atomicPairSeries c t with hΦ
  set β := crystallineResidue c t with hβ
  set H : ℂ → ℂ := fun z => (z - 1) * (deriv completedRiemannZeta₀ z +
      completedRiemannZeta₀ z * (1 / z)) + completedRiemannZeta₀ z -
      ((z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) * Φ z -
      β * (2 * ((Real.pi : ℂ) ^ (-(z - 1) / 2) * Gamma ((z - 1) / 2 + 1))) with hHdef
  have hH1 : H 1 = 0 := by
    simp only [hHdef, hβ, crystallineResidue, sub_self, zero_mul, zero_add, neg_zero, zero_div,
      cpow_zero, one_mul, Complex.Gamma_one]
    ring
  have hG : DifferentiableAt ℂ Gamma (((1 : ℂ) - 1) / 2 + 1) := by
    apply differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this; linarith
  have hΦc : ContinuousAt Φ 1 :=
    ((differentiableOn_atomicPairSeries h.one_le h.summable).differentiableAt
      ((isOpen_re_gt _).mem_nhds (by norm_num))).continuousAt
  have hL0 : Continuous completedRiemannZeta₀ := differentiable_completedZeta₀.continuous
  have hdL0 : Continuous (deriv completedRiemannZeta₀) :=
    differentiable_deriv_completedRiemannZeta₀.continuous
  have hinv : ContinuousAt (fun z : ℂ => 1 / z) 1 :=
    continuousAt_const.div continuousAt_id one_ne_zero
  have hpow : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z - 1) / 2)) 1 :=
    (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).continuousAt
  have hgam : ContinuousAt (fun z : ℂ => Gamma ((z - 1) / 2 + 1)) 1 :=
    hG.continuousAt.comp (f := fun z : ℂ => (z - 1) / 2 + 1) (by fun_prop)
  have hsub : ContinuousAt (fun z : ℂ => z - 1) 1 := by fun_prop
  have hHc : ContinuousAt H 1 := by
    refine (((hsub.mul (hdL0.continuousAt.add (hL0.continuousAt.mul hinv))).add
      hL0.continuousAt).sub (((hsub.mul (hL0.continuousAt.sub hinv)).add continuousAt_const).mul
      hΦc)).sub (continuousAt_const.mul (continuousAt_const.mul (hpow.mul hgam)))
  have hev : (fun z => (z - 1) * crystallineRemainderRaw c t z) =ᶠ[𝓝[≠] 1] H := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)),
      self_mem_nhdsWithin] with z hz hz1
    have hz1' : z ≠ 1 := hz1
    rw [mem_ball, dist_eq_norm] at hz
    have hre : 3 / 4 < z.re := by
      have := (Complex.abs_re_le_norm (z - 1)).trans_lt hz
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_lt.mp this
      linarith [this.1]
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hre; simp at hre; linarith
    have hat : ∀ j, z ≠ atomPoint (t j) ∧ z ≠ atomMirror (t j) := fun j =>
      ⟨fun he => by rw [he, atomPoint_re] at hre; norm_num at hre,
       fun he => by rw [he, atomMirror_re] at hre; norm_num at hre⟩
    have ht0 : ∀ j, t j ≠ 0 := fun j => by have := h.one_le j; positivity
    have hZ := atomicZetaPart_eq_mul (c := c) ht0 h.zero hat
    have hΓ := sub_one_mul_Gammaℝ_sub_one hz1'
    have e1 : (z - 1) * (1 / (z - 1)) = 1 := by
      field_simp [sub_ne_zero.mpr hz1']
    have e2 : (z - 1) * (1 / (1 - z)) = -1 := by
      rw [show (1 : ℂ) - z = -(z - 1) by ring, div_neg]
      field_simp [sub_ne_zero.mpr hz1']
    simp only [crystallineRemainderRaw, completedZetaXiLogDeriv, hZ, completedRiemannZeta_eq,
      hHdef]
    rw [← hβ, ← hΦ]
    linear_combination completedRiemannZeta₀ z * e1 + Φ z * e2 - β * hΓ
  have := hHc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  rw [hH1] at this
  exact this.congr' hev.symm

/-- **Removable singularity at `s = 1`.**  The filled remainder is holomorphic on `Re s > 0`. -/
theorem differentiableOn_crystallineRemainder {c t : ℕ → ℝ} (h : ZetaAtoms c t) :
    DifferentiableOn ℂ (crystallineRemainder c t) {s : ℂ | 0 < s.re} := by
  have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  refine differentiableOn_update_limUnder_of_isLittleO hU ?_ ?_
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs0' : 0 < s.re := hs0
    have hne0 : s ≠ 0 := by intro h0; rw [h0] at hs0'; simp at hs0'
    have hne1 : s ≠ 1 := by simpa using hs1
    have hreg : s ∈ zetaRegular := by
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hne0, hne1⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    have hG := differentiableAt_Gammaℝ_sub_one hs0' hne1
    exact ((differentiableAt_completedZetaXiLogDeriv hne0 hne1).sub
      ((differentiableOn_atomicZetaPart h).differentiableAt
        (isOpen_zetaRegular.mem_nhds hreg))).sub ((differentiableAt_const _).mul hG)
  · rw [Asymptotics.isLittleO_iff_tendsto']
    · have h1 := tendsto_sub_one_mul_crystallineRemainderRaw h
      have h2 : Tendsto (fun z : ℂ => (z - 1) * crystallineRemainderRaw c t 1) (𝓝[≠] 1)
          (𝓝 0) := by
        have : Tendsto (fun z : ℂ => (z - 1) * crystallineRemainderRaw c t 1) (𝓝 1)
            (𝓝 ((1 - 1) * crystallineRemainderRaw c t 1)) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      have := h1.sub h2
      rw [sub_zero] at this
      refine this.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      dsimp only
      rw [div_inv_eq_mul]
      ring
    · exact eventually_nhdsWithin_of_forall fun z hz h0 =>
        absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))

/-- `(τ + 4)^N e^{−πτ/4} ≤ K/(1 + τ²)` from a bound `K` on `(y + 4)^{N+2} e^{−πy/4}`. -/
theorem pow_mul_exp_neg_le_div {N : ℕ} {K : ℝ}
    (hK : ∀ y : ℝ, 0 ≤ y → (y + 4) ^ (N + 2) * Real.exp (-(Real.pi * y / 4)) ≤ K) {τ : ℝ}
    (hτ : 0 ≤ τ) : (τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4)) ≤ K / (1 + τ ^ 2) := by
  have h1 : 1 + τ ^ 2 ≤ (τ + 4) ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc (τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4)) * (1 + τ ^ 2)
      ≤ (τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4)) * (τ + 4) ^ 2 := by gcongr
    _ = (τ + 4) ^ (N + 2) * Real.exp (-(Real.pi * τ / 4)) := by ring
    _ ≤ K := hK τ hτ

/-- Points of the closed disc of radius `½` about `w` have real part within `½` of `Re w` and
height within `½` of `|Im w|`. -/
theorem mem_closedBall_half_bounds {w z : ℂ} (hz : z ∈ closedBall w (1 / 2)) :
    w.re - 1 / 2 ≤ z.re ∧ z.re ≤ w.re + 1 / 2 ∧ |w.im| - 1 / 2 ≤ |z.im| ∧
      |z.im| ≤ |w.im| + 1 / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := abs_le.mp ((Complex.abs_re_le_norm (z - w)).trans hz)
  have him := (Complex.abs_im_le_norm (z - w)).trans hz
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have h1 := abs_sub_abs_le_abs_sub w.im z.im
  have h2 := abs_sub_abs_le_abs_sub z.im w.im
  rw [abs_sub_comm] at h1
  refine ⟨by linarith [hre.1], by linarith [hre.2], by linarith, by linarith⟩

/-- **Vertical decay of `Λ ξ'/ξ`** on `½ ≤ Re s ≤ 3/2`, `|Im s| ≥ 4`: Cauchy's estimate on a
disc of radius `½` bounds `Λ'` by the exponential decay of `Λ`. -/
theorem exists_decay_completedZetaXiLogDeriv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → 4 ≤ |w.im| →
      ‖completedZetaXiLogDeriv w‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 2)
  refine ⟨3 * (CΛ * Real.exp (Real.pi / 8)) * K, by positivity, fun w h1 h2 h3 => ?_⟩
  set τ := |w.im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hpi := Real.pi_pos
  set B : ℝ := CΛ * Real.exp (Real.pi / 8) * ((τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4)))
    with hB
  have hB0 : 0 ≤ B := by positivity
  have hdisc : ∀ z ∈ closedBall w (1 / 2), ‖completedRiemannZeta z‖ ≤ B := by
    intro z hz
    obtain ⟨b1, b2, b3, b4⟩ := mem_closedBall_half_bounds hz
    have hb := hΛ z (by linarith) (by linarith) (by linarith)
    have hexp : Real.exp (-(Real.pi * |z.im| / 4)) ≤
        Real.exp (Real.pi / 8) * Real.exp (-(Real.pi * τ / 4)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hpow : |z.im| ^ N ≤ (τ + 4) ^ N :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) N
    calc ‖completedRiemannZeta z‖ ≤ CΛ * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := hb
      _ ≤ CΛ * (τ + 4) ^ N * (Real.exp (Real.pi / 8) * Real.exp (-(Real.pi * τ / 4))) := by
          gcongr
      _ = B := by rw [hB]; ring
  have hw0 : w ≠ 0 := by intro h0; rw [hτ, h0] at h3; norm_num at h3
  have hw1 : w ≠ 1 := by intro h0; rw [hτ, h0] at h3; norm_num at h3
  have hdiff : DiffContOnCl ℂ completedRiemannZeta (ball w (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w (by norm_num)]
    intro z hz
    obtain ⟨-, -, b3, -⟩ := mem_closedBall_half_bounds hz
    have hzim : z.im ≠ 0 := by intro h0; rw [h0, abs_zero] at b3; linarith
    have hreg : z ∈ zetaRegular := by
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun h0 => hzim (by rw [h0]; simp), fun h0 => hzim (by rw [h0]; simp)⟩
    exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
      (isOpen_zetaRegular.mem_nhds hreg)).differentiableWithinAt
  have hderiv : ‖deriv completedRiemannZeta w‖ ≤ B / (1 / 2) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hdiff
      (fun z hz => hdisc z (sphere_subset_closedBall hz))
  have hself : ‖completedRiemannZeta w‖ ≤ B := hdisc w (mem_closedBall_self (by norm_num))
  have hq : ‖1 / w + 1 / (w - 1)‖ ≤ 1 / 2 := by
    have hn1 : 4 ≤ ‖w‖ := h3.trans (Complex.abs_im_le_norm w)
    have hn2 : 4 ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    calc ‖1 / w + 1 / (w - 1)‖ ≤ ‖1 / w‖ + ‖1 / (w - 1)‖ := norm_add_le _ _
      _ = 1 / ‖w‖ + 1 / ‖w - 1‖ := by rw [norm_div, norm_div, norm_one]
      _ ≤ 1 / 4 + 1 / 4 := by gcongr
      _ = 1 / 2 := by norm_num
  rw [completedZetaXiLogDeriv_eq hw0 hw1]
  have hmain : ‖deriv completedRiemannZeta w +
      completedRiemannZeta w * (1 / w + 1 / (w - 1))‖ ≤ 3 * B := by
    calc _ ≤ ‖deriv completedRiemannZeta w‖ +
          ‖completedRiemannZeta w‖ * ‖1 / w + 1 / (w - 1)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ B / (1 / 2) + B * (1 / 2) := by gcongr
      _ ≤ 3 * B := by linarith
  have hK' := pow_mul_exp_neg_le_div hK hτ0
  rw [hτ, sq_abs] at hK'
  calc _ ≤ 3 * B := hmain
    _ = 3 * (CΛ * Real.exp (Real.pi / 8)) * ((τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4))) := by
        rw [hB]; ring
    _ ≤ 3 * (CΛ * Real.exp (Real.pi / 8)) * (K / (1 + w.im ^ 2)) := by gcongr
    _ = _ := by ring

/-- **Vertical decay of `Γ_ℝ(s − 1)`** on `½ ≤ Re s ≤ 3/2`, `|Im s| ≥ 4`. -/
theorem exists_decay_Gammaℝ_sub_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → 4 ≤ |w.im| →
      ‖Gammaℝ (w - 1)‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨Cg, Ng, hCg, hg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip (-1 / 4) (1 / 4)
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (Ng + 2)
  refine ⟨Real.pi * Cg * K, by positivity, fun w h1 h2 h3 => ?_⟩
  set τ := |w.im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hpi := Real.pi_pos
  have him : ((w - 1) / 2).im = w.im / 2 := by simp
  have hre : ((w - 1) / 2).re = (w.re - 1) / 2 := by simp
  have hgam := hg ((w - 1) / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him, abs_div]; norm_num; linarith)
  rw [him, abs_div, abs_two] at hgam
  have hcp : ‖(Real.pi : ℂ) ^ (-(w - 1) / 2)‖ ≤ Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have : (-(w - 1) / 2).re ≤ 1 := by simp; linarith
    calc Real.pi ^ (-(w - 1) / 2).re ≤ Real.pi ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) this
      _ = Real.pi := Real.rpow_one _
  have hexp : Real.exp (-(Real.pi * (τ / 2) / 2)) = Real.exp (-(Real.pi * τ / 4)) := by
    congr 1; ring
  rw [hexp] at hgam
  have hpow : (τ / 2) ^ Ng ≤ (τ + 4) ^ Ng := pow_le_pow_left₀ (by positivity) (by linarith) Ng
  have hK' := pow_mul_exp_neg_le_div hK hτ0
  rw [hτ, sq_abs] at hK'
  rw [Gammaℝ_def, norm_mul]
  calc ‖(Real.pi : ℂ) ^ (-(w - 1) / 2)‖ * ‖Gamma ((w - 1) / 2)‖
      ≤ Real.pi * (Cg * (τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4))) := by
        gcongr
        exact hgam.trans (by gcongr)
    _ = Real.pi * Cg * ((τ + 4) ^ Ng * Real.exp (-(Real.pi * τ / 4))) := by ring
    _ ≤ Real.pi * Cg * (K / (1 + w.im ^ 2)) := by gcongr
    _ = _ := by ring

/-- **Decay of the remainder** on the closed strip `½ ≤ Re s ≤ 3/2`. -/
theorem exists_decay_crystallineRemainder {c t : ℕ → ℝ} (h : ZetaAtoms c t) :
    ∃ C : ℝ, ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2) (3 / 2),
      ‖crystallineRemainder c t s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_decay_completedZetaXiLogDeriv
  obtain ⟨C₂, hC₂, h₂⟩ := exists_decay_atomicZetaPart h
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  set K : Set ℂ := Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 with hKdef
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    rw [hKdef, Complex.mem_reProdIm] at hz
    show 0 < z.re
    linarith [hz.1.1]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_crystallineRemainder h).continuousOn.mono hsub)
  set β := crystallineResidue c t
  refine ⟨max (17 * max M 0) (C₁ + C₂ + ‖β‖ * C₃), fun s hs => ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : 4 ≤ |s.im|
  · have hs1 : s ≠ 1 := by intro h0; rw [h0] at hbig; norm_num at hbig
    rw [crystallineRemainder, Function.update_of_ne hs1, crystallineRemainderRaw]
    calc ‖completedZetaXiLogDeriv s - atomicZetaPart c t s - β * Gammaℝ (s - 1)‖
        ≤ ‖completedZetaXiLogDeriv s‖ + ‖atomicZetaPart c t s‖ + ‖β‖ * ‖Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ C₁ / (1 + s.im ^ 2) + C₂ / (1 + s.im ^ 2) + ‖β‖ * (C₃ / (1 + s.im ^ 2)) := by
          gcongr
          · exact h₁ s hs.1 hs.2 hbig
          · exact h₂ s hs.1 hs.2 hbig
          · exact h₃ s hs.1 hs.2 hbig
      _ = (C₁ + C₂ + ‖β‖ * C₃) / (1 + s.im ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hbig
    have hsK : s ∈ K := by
      rw [hKdef, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    calc ‖crystallineRemainder c t s‖ ≤ max M 0 := hb
      _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- Absolute convergence of `Σ lam(n) n^{−s}` on `Re s > 1`. -/
theorem lseriesSummable_of_summable_abs {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => (lam n : ℂ)) s := by
  refine Summable.of_norm_bounded (hsum s.re hs) (fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [Complex.norm_real, Real.norm_eq_abs]

/-- The Dirichlet coefficients `1 ⋆ (lam − Λ)` of `ζ(s) (Σ lam(n) n^{−s} + ζ'/ζ(s))`. -/
noncomputable def crystallineCoeff (lam : ℕ → ℝ) : ℕ → ℂ :=
  LSeries.convolution 1
    ((fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))

theorem lseriesSummable_crystallineCoeff {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (crystallineCoeff lam) s :=
  (LSeriesSummable_one_iff.mpr hs).convolution ((lseriesSummable_of_summable_abs hsum hs).sub
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs))

theorem LSeries_crystallineCoeff {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (crystallineCoeff lam) s = riemannZeta s * (LSeries (fun n => (lam n : ℂ)) s -
      LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s) := by
  have hl := lseriesSummable_of_summable_abs hsum hs
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [crystallineCoeff, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs) (hl.sub hΛ),
    LSeries_one_eq_riemannZeta hs, LSeries_sub hl hΛ]

/-- `Σ a(n+1) (n+1)^{−s}` is the L-series of `a`. -/
theorem coeffDirichlet_eq_LSeries (a : ℕ → ℂ) (s : ℂ) :
    GaloisForLFunctions.HTGeometry.coeffDirichlet a s = LSeries a s := by
  unfold GaloisForLFunctions.HTGeometry.coeffDirichlet LSeries
  rw [← Nat.succ_injective.tsum_eq (f := LSeries.term a s)]
  · congr 1; ext n
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    push_cast
    rfl
  · intro n hn
    rcases n with _ | n
    · exact absurd (LSeries.term_zero a s) hn
    · exact ⟨n, rfl⟩

theorem summable_coeff_of_LSeriesSummable {a : ℕ → ℂ} {σ : ℝ} (h : LSeriesSummable a σ) :
    Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ := by
  have h1 : Summable fun n => ‖LSeries.term a σ n‖ := summable_norm_iff.mpr h
  have h2 := (summable_nat_add_iff 1).mpr h1
  refine h2.congr (fun n => ?_)
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  push_cast
  simp

/-- `Γ_ℝ ζ · (A + 1/(s − 1) − φ + ζ'/ζ) = Λ ξ'/ξ − Λ φ` on `Re s > 1`, for the ζ datum
`A = Γ_ℝ'/Γ_ℝ + 1/s`. -/
theorem Gammaℝ_mul_riemannZeta_mul_eq {s : ℂ} (hs : 1 < s.re) (φ : ℂ) :
    Gammaℝ s * (riemannZeta s * ((zetaArchimedeanDatum s + 1 / (s - 1) - φ) -
      -deriv riemannZeta s / riemannZeta s)) =
      completedZetaXiLogDeriv s - completedRiemannZeta s * φ := by
  have hre0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hre0; simp at hre0
  have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; simp at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp [Gammaℝ_ne_zero_of_re_pos hre0]
  have hev : completedRiemannZeta =ᶠ[𝓝 s] fun z => Gammaℝ z * riemannZeta z := by
    filter_upwards [(isOpen_re_gt 0).mem_nhds hre0] with z hz
    have hz' : 0 < z.re := hz
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz'; simp at hz'
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp [Gammaℝ_ne_zero_of_re_pos hz']
  have hd : deriv completedRiemannZeta s =
      Gammaℝ s * (digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) * riemannZeta s +
        Gammaℝ s * deriv riemannZeta s := by
    rw [hev.deriv_eq]
    exact ((hasDerivAt_Gammaℝ_of_re_pos hre0).mul
      (differentiableAt_riemannZeta hs1).hasDerivAt).deriv
  rw [completedZetaXiLogDeriv_eq hs0 hs1, hd, hΛ, zetaArchimedeanDatum]
  have e : riemannZeta s * (-deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s :=
    mul_div_cancel₀ _ hζ
  linear_combination (-Gammaℝ s) * e

/-- **Odd Hamburger step.**  The coefficients `1 ⋆ (lam − Λ)` of a crystalline producer vanish. -/
theorem crystallineCoeff_eq_zero {lam c t : ℕ → ℝ} (hat : ZetaAtoms c t)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) (n : ℕ) :
    crystallineCoeff lam (n + 1) = 0 := by
  obtain ⟨C, hC⟩ := exists_decay_crystallineRemainder hat
  have hdiff := differentiableOn_crystallineRemainder hat
  have ht0 : ∀ j, t j ≠ 0 := fun j => by have := hat.one_le j; positivity
  refine GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_critical_line_odd
    (E := crystallineRemainder c t) (β := crystallineResidue c t) (C := C) ?_ ?_ ?_ hC ?_ ?_ n
  · intro σ hσ
    exact summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsum (by simpa using hσ))
  · refine hdiff.continuousOn.mono (fun z hz => ?_)
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hz
    show 0 < z.re
    linarith [hz.1]
  · refine hdiff.mono (fun z hz => ?_)
    show 0 < z.re
    linarith [hz.1]
  · intro s hs
    have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; norm_num at hs
    have hs' : 1 < s.re := by rw [hs]; norm_num
    have hat' : ∀ j, s ≠ atomPoint (t j) ∧ s ≠ atomMirror (t j) := fun j =>
      ⟨fun he => by rw [he, atomPoint_re] at hs; norm_num at hs,
       fun he => by rw [he, atomMirror_re] at hs; norm_num at hs⟩
    have hlam : LSeries (fun n => (lam n : ℂ)) s =
        zetaArchimedeanDatum s + 1 / (s - 1) - atomicPairSeries c t s := by
      linear_combination -(hid s hs')
    rw [coeffDirichlet_eq_LSeries, LSeries_crystallineCoeff hsum hs',
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs', hlam,
      Gammaℝ_mul_riemannZeta_mul_eq hs', crystallineRemainder, Function.update_of_ne hs1,
      crystallineRemainderRaw, atomicZetaPart_eq_mul ht0 hat.zero hat']
    ring
  · intro s hs
    have hs1 : s ≠ 1 := ne_one_of_re_eq_half hs
    have hs1' : 1 - s ≠ 1 := by
      intro h0; apply ne_zero_of_re_eq_half hs; linear_combination -h0
    have hreg : s ∈ zetaRegular := mem_zetaRegular_of_re_eq_half hs
    rw [crystallineRemainder, Function.update_of_ne hs1, Function.update_of_ne hs1',
      crystallineRemainderRaw, crystallineRemainderRaw, completedZetaXiLogDeriv_one_sub,
      atomicZetaPart_one_sub ht0 hat.zero hreg, show (1 : ℂ) - s - 1 = -s by ring]
    ring

/-- **Zeros of solutions of `f' = f g` are not isolated.**  If `f` is analytic at `ρ`, `f(ρ) = 0`,
`g` is continuous at `ρ` and `f' = f g` near `ρ`, then `f` vanishes near `ρ`.  At a zero of order
`m + 1`, `f = (z − ρ)^{m+1} u` gives `(m + 1) u = (z − ρ)(u g − u')`, and `u(ρ) ≠ 0`. -/
theorem eventually_eq_zero_of_deriv_eq_mul {f g : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hg : ContinuousAt g ρ) (hρ : f ρ = 0) (hfg : ∀ᶠ z in 𝓝 ρ, deriv f z = f z * g z) :
    ∀ᶠ z in 𝓝 ρ, f z = 0 := by
  by_contra hne
  obtain ⟨n, u, hu, hu0, hfu⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [smul_eq_mul] at hfu
  rcases n with _ | m
  · have := hfu.self_of_nhds
    rw [hρ, pow_zero, one_mul] at this
    exact hu0 this.symm
  have hfu' : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ (m + 1) * u z := hfu
  have hderiv := hfu'.deriv
  have hkey : ∀ᶠ z in 𝓝[≠] ρ, ((m : ℂ) + 1) * u z = (z - ρ) * (u z * g z - deriv u z) := by
    have hev := hu.eventually_analyticAt.and (hderiv.and (hfg.and hfu'))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hzρ
    obtain ⟨hua, hd, hfg', hfz⟩ := hz
    have hz' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    have h1 : HasDerivAt (fun y => (y - ρ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m) z := by
      have := ((hasDerivAt_id' z).sub_const ρ).pow (m + 1)
      simp only [Nat.add_sub_cancel, mul_one] at this
      exact this
    have hP : HasDerivAt (fun y => (y - ρ) ^ (m + 1) * u y)
        (((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * u z + (z - ρ) ^ (m + 1) * deriv u z) z :=
      h1.mul hua.differentiableAt.hasDerivAt
    rw [hP.deriv, hfg', hfz] at hd
    push_cast at hd
    apply mul_left_cancel₀ (pow_ne_zero m hz')
    linear_combination (-1 : ℂ) * hd
  have hlim1 : Tendsto (fun z => ((m : ℂ) + 1) * u z) (𝓝[≠] ρ) (𝓝 (((m : ℂ) + 1) * u ρ)) :=
    ((continuousAt_const.mul hu.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (z - ρ) * (u z * g z - deriv u z)) (𝓝[≠] ρ) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - ρ) * (u z * g z - deriv u z)) ρ :=
      (continuousAt_id.sub continuousAt_const).mul
        ((hu.continuousAt.mul hg).sub hu.deriv.continuousAt)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
    simpa using this
  have hlim := tendsto_nhds_unique (hlim1.congr' hkey) hlim2
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  exact hu0 ((mul_eq_zero.mp hlim).resolve_left hm)

theorem isPreconnected_zetaRegular : IsPreconnected zetaRegular := by
  have hc : ({0, 1} : Set ℂ).Countable := (Set.toFinite _).countable
  have hr : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact (Set.Countable.isPathConnected_compl_of_one_lt_rank hr hc).isConnected.isPreconnected

theorem completedRiemannZeta_two_ne_zero : completedRiemannZeta 2 ≠ 0 := by
  have h2 : (0 : ℝ) < (2 : ℂ).re := by norm_num
  have hΛ : completedRiemannZeta 2 = Gammaℝ 2 * riemannZeta 2 := by
    rw [riemannZeta_def_of_ne_zero two_ne_zero]
    field_simp [Gammaℝ_ne_zero_of_re_pos h2]
  rw [hΛ]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos h2)
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))

/-- **`Λ ξ'/ξ = Λ Φ̃` forces RH.**  If `Λ ξ'/ξ` equals the ζ-cancelled atomic part on `Re s > 1`,
it does so on `ℂ ∖ {0, 1}`.  Off the critical line this reads `Λ' = Λ (Φ̃ − 1/s − 1/(s − 1))` with a
holomorphic coefficient, so a zero of `Λ` with `Re > ½` would make `Λ` vanish identically. -/
theorem riemannHypothesis_of_completedZetaXiLogDeriv_eq {c t : ℕ → ℝ} (hat : ZetaAtoms c t)
    (hG : ∀ s : ℂ, 1 < s.re → completedZetaXiLogDeriv s = atomicZetaPart c t s) :
    RiemannHypothesis := by
  have hreg2 : (2 : ℂ) ∈ zetaRegular := by
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    norm_num
  have hGa : AnalyticOnNhd ℂ completedZetaXiLogDeriv zetaRegular := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_zetaRegular
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZetaXiLogDeriv hz.1 hz.2).differentiableWithinAt
  have hZa : AnalyticOnNhd ℂ (atomicZetaPart c t) zetaRegular :=
    (differentiableOn_atomicZetaPart hat).analyticOnNhd isOpen_zetaRegular
  have hΛa : AnalyticOnNhd ℂ completedRiemannZeta zetaRegular :=
    differentiableOn_completedRiemannZeta_regular.analyticOnNhd isOpen_zetaRegular
  have hGZ : EqOn completedZetaXiLogDeriv (atomicZetaPart c t) zetaRegular := by
    refine hGa.eqOn_of_preconnected_of_eventuallyEq hZa isPreconnected_zetaRegular hreg2 ?_
    filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact hG z hz
  have ht0 : ∀ j, t j ≠ 0 := fun j => by have := hat.one_le j; positivity
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro ρ hρ hζρ
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hζρ
  push Not at h1
  have hρ0 : ρ ≠ 0 := by intro h0; rw [h0] at hρ; norm_num at hρ
  have hρ1 : ρ ≠ 1 := by intro h0; rw [h0] at h1; norm_num at h1
  have hρreg : ρ ∈ zetaRegular := by
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hρ0, hρ1⟩
  have hΛρ : completedRiemannZeta ρ = 0 := by
    have := riemannZeta_def_of_ne_zero hρ0
    rw [hζρ, eq_comm, div_eq_zero_iff] at this
    exact this.resolve_right (Gammaℝ_ne_zero_of_re_pos (by linarith))
  set g : ℂ → ℂ := fun z => atomicPairSeries c t z - (1 / z + 1 / (z - 1)) with hgdef
  have hΦd : DifferentiableAt ℂ (atomicPairSeries c t) ρ :=
    (differentiableOn_atomicPairSeries hat.one_le hat.summable).differentiableAt
      ((isOpen_re_gt _).mem_nhds hρ)
  have hgc : ContinuousAt g ρ :=
    hΦd.continuousAt.sub ((continuousAt_const.div continuousAt_id hρ0).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hρ1)))
  have hode : ∀ᶠ z in 𝓝 ρ, deriv completedRiemannZeta z = completedRiemannZeta z * g z := by
    have hV : {z : ℂ | 1 / 2 < z.re} ∩ zetaRegular ∈ 𝓝 ρ :=
      inter_mem ((isOpen_re_gt _).mem_nhds hρ) (isOpen_zetaRegular.mem_nhds hρreg)
    filter_upwards [hV] with z hz
    obtain ⟨hzre, hzreg⟩ := hz
    have hzre' : 1 / 2 < z.re := hzre
    have hzreg' := hzreg
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hzreg'
    have hat' : ∀ j, z ≠ atomPoint (t j) ∧ z ≠ atomMirror (t j) := fun j =>
      ⟨fun he => by rw [he, atomPoint_re] at hzre'; norm_num at hzre',
       fun he => by rw [he, atomMirror_re] at hzre'; norm_num at hzre'⟩
    have h := hGZ hzreg
    rw [completedZetaXiLogDeriv_eq hzreg'.1 hzreg'.2, atomicZetaPart_eq_mul ht0 hat.zero hat'] at h
    rw [hgdef]
    linear_combination h
  have hloc := eventually_eq_zero_of_deriv_eq_mul (hΛa ρ hρreg) hgc hΛρ hode
  have hzero := hΛa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_zetaRegular
    hρreg hloc
  exact completedRiemannZeta_two_ne_zero (hzero hreg2)

/-- **Crystalline Weil-positive producers are von Mangoldt and force RH.**  Let `lam` have
`Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let
`Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = (2(s − ½)/π) Σ_j c_j/((s − ½)² + t_j²)` on `Re s > 1`, where
`Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s` is the ζ archimedean datum and the ordinates `t_j ≥ 1` satisfy
`ζ(½ + it_j) = 0` with `Σ |c_j|/t_j² < ∞`.  Then `lam(n) = Λ(n)` for all `n ≥ 1`, and the
Riemann hypothesis holds.

`ζ · (Σ lam(n) n^{−s} + ζ'/ζ)` equals `(ξ'/ξ − Φ̃) ζ`: every pole of `ξ'/ξ − Φ̃` at a zero of `ζ`,
on or off the line, is cancelled.  Both `ξ'/ξ` and `Φ̃` are odd under `s ↦ 1 − s`, so the odd
Hamburger theorem kills the series.  Then `Λ' = Λ (Φ̃ − 1/s − 1/(s − 1))` off the line, which has no
zeros. -/
theorem crystalline_producer_rigidity {lam c t : ℕ → ℝ} (hat : ZetaAtoms c t)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = atomicPairSeries c t s) :
    (∀ n : ℕ, n ≠ 0 → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have ha := crystallineCoeff_eq_zero hat hsum hid
  have hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (lam n : ℂ)) s =
      LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    intro s hs
    have h0 : LSeries (crystallineCoeff lam) s = 0 := by
      rw [← coeffDirichlet_eq_LSeries]
      unfold GaloisForLFunctions.HTGeometry.coeffDirichlet
      simp [ha]
    rw [LSeries_crystallineCoeff hsum hs] at h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left
      (riemannZeta_ne_zero_of_one_le_re hs.le))
  have hΛs : ∀ s : ℂ, 1 < s.re → LSeriesSummable
      ((fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s :=
    fun s hs => (lseriesSummable_of_summable_abs hsum hs).sub
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  refine ⟨?_, ?_⟩
  · have hw : (fun x : ℝ => LSeries ((fun n => (lam n : ℂ)) -
        fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hx' : 1 < (x : ℂ).re := by simpa using hx
      rw [LSeries_sub (lseriesSummable_of_summable_abs hsum hx')
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hx'), hL x hx', sub_self]
      rfl
    rcases LSeries_eventually_eq_zero_iff'.mp hw with h | h
    · intro n hn
      have := h n hn
      simp only [Pi.sub_apply, sub_eq_zero] at this
      exact_mod_cast this
    · exfalso
      have hle := (hΛs 2 (by norm_num)).abscissaOfAbsConv_le
      rw [h] at hle
      simp at hle
  · refine riemannHypothesis_of_completedZetaXiLogDeriv_eq hat (fun s hs => ?_)
    have hat' : ∀ j, s ≠ atomPoint (t j) ∧ s ≠ atomMirror (t j) := fun j =>
      ⟨fun he => by rw [he, atomPoint_re] at hs; norm_num at hs,
       fun he => by rw [he, atomMirror_re] at hs; norm_num at hs⟩
    have ht0 : ∀ j, t j ≠ 0 := fun j => by have := hat.one_le j; positivity
    have h1 : zetaArchimedeanDatum s + 1 / (s - 1) - atomicPairSeries c t s =
        -deriv riemannZeta s / riemannZeta s := by
      rw [← hid s hs, hL s hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
      ring
    have h := Gammaℝ_mul_riemannZeta_mul_eq hs (atomicPairSeries c t s)
    rw [h1, sub_self, mul_zero, mul_zero] at h
    rw [atomicZetaPart_eq_mul ht0 hat.zero hat']
    linear_combination -h

end RHTower

