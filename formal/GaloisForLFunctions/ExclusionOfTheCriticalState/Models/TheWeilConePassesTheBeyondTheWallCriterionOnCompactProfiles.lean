import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.BeyondTheWallContinuationFailsOnTheModels
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw

/-!
# The Weil cone passes the beyond-the-wall criterion on compact profiles

For a weight system `λ : ℕ → ℝ` in the place of `Λ`, the model prime-pole balance is
`Φ_λ(F, p) = Σ_n λ(n) n^{p−½} H_{log n}F(p) + L F(−½)/(p + ½)` with the Lévy heads
`H_x F(p) = ∫_{u ≥ −x} F(u) e^{pu} du` (`modelWallPrimeBalance`). Stage 5 asks that it continue from
`Re p < −½` to `Re p < 0` for every profile of `H`; here only compactly supported profiles are used
(`ModelCompactBeyondTheWallPrimeContinuation`).

* **Compact profiles** (`modelWallPrimeBalance_eq_of_head`). If `F = 0` left of `−A`, then `H_x F = L F`
  for `x ≥ A`, and on `Re p < −½`
  `Φ_λ(F, p) = D(p) + L F(p) L_λ(½ − p) + L F(−½)/(p + ½)`, `L_λ(s) = Σ λ(n) n^{−s}`,
  with `D` a finite sum of entire functions.
* **The Weil cone** (`modelCompactContinuation_of_weilPositiveFull`). For `λ` Weil-positive (full cone),
  `L_λ(s) = A(s) + 1/(s − 1) − Φ_W(s)` on `Re s > 1`, with `A(s) = ψ(s/2)/2 − (log π)/2 + 1/s` and
  `Φ_W` the Herglotz continuation, holomorphic on `Re s > ½` (`weilContinuation`). The pole term of the
  balance cancels the pole of `L_λ` at `s = 1`, so `Φ_λ(F, ·)` continues to `Re p < 0` for every
  compactly supported `F ∈ H`.
* **ζ** (`modelCompactContinuation_eulerLog_iff_riemannHypothesis`). For `λ = Λ` the compact criterion is
  RH: RH is the Weil positivity of `Λ`; off RH a left zero is seen by a smooth compactly supported
  profile (`exists_compact_profile_laplace_ne_zero`), and its balance has a pole in `Re p < 0`
  (`not_wallPrimeBalance_continues_of_seen_zero`).

So the criterion on compact profiles is the Weil-cone membership of `Λ`, and the continuation it asks
for holds on the whole cone: an argument for it that does not use positivity cannot tell `Λ` from any
other Weil-positive weight system.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-- **Stage 5 on compact profiles**: for every profile of `H` that vanishes left of some `−A`, the model
balance continues holomorphically from `Re p < −½` to `Re p < 0`. -/
def ModelCompactBeyondTheWallPrimeContinuation (c : ℕ → ℂ) : Prop :=
  ∀ F : ℝ → ℝ, CriticalHalfLineEnergyDomain F → (∃ A : ℝ, ∀ u, u < -A → F u = 0) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
      EqOn H (modelWallPrimeBalance c F) {p : ℂ | p.re < -(1 / 2)}

theorem ModelBeyondTheWallPrimeContinuation.compact {c : ℕ → ℂ}
    (h : ModelBeyondTheWallPrimeContinuation c) : ModelCompactBeyondTheWallPrimeContinuation c :=
  fun F hF _ => h F hF

/-- Past the support of the profile the Lévy head is the transform. -/
theorem levyHead_eq_laplace_of_head {F : ℝ → ℝ} {A x : ℝ} (hA : ∀ u, u < -A → F u = 0)
    (hx : A ≤ x) (p : ℂ) : levyHead F p x = negativeHalfLineLaplace (cx F) p := by
  unfold levyHead negativeHalfLineLaplace
  rw [← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : -x ≤ u
  · rw [indicator_of_mem (mem_Ici.mpr hu)]; rfl
  · rw [indicator_of_notMem (show u ∉ Ici (-x) by simpa using hu)]
    have : F u = 0 := hA u (by push Not at hu; linarith)
    simp [cx, this]

/-- The model atom times `n^p` is the Dirichlet term of `λ` at `½ − p`. -/
theorem modelAtom_mul_cexp_eq_term {c : ℕ → ℂ} {lam : ℕ → ℝ}
    (hc : ∀ n, 2 ≤ n → modelAtom c n = (lam n : ℂ) / (Real.sqrt n : ℂ)) (n : ℕ) (p : ℂ) :
    modelAtom c n * cexp (p * Real.log n) =
      LSeries.term (_root_.RHTower.WeilHerglotz.lamC lam) ((1 : ℂ) / 2 - p) n := by
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : modelAtom c n = 0 := by unfold modelAtom; rw [if_neg (by omega)]
    rw [h0, zero_mul]
    unfold LSeries.term _root_.RHTower.WeilHerglotz.lamC
    split_ifs <;> simp_all
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [hc n hn]
    unfold LSeries.term _root_.RHTower.WeilHerglotz.lamC
    rw [if_neg (by omega), if_pos hn, Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    have hs : (Real.sqrt n : ℂ) = cexp ((Real.log n : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Complex.ofReal_exp]
      push_cast; ring_nf
    have h1 : cexp ((Real.log n : ℂ) * (1 / 2 - p)) =
        cexp ((Real.log n : ℂ) / 2) / cexp (p * Real.log n) := by
      rw [← Complex.exp_sub]; congr 1; ring
    rw [hs, h1]
    field_simp

/-- **The balance of a compact profile.** If `F = 0` left of `−A` and `λ` is Weil-positive,
then on `Re p < −½` the model balance is `D(p) + L F(p) L_λ(½ − p) + L F(−½)/(p + ½)`, where
`D(p) = Σ_{n < N} a_n n^p (H_{log n}F(p) − L F(p))`, `N = ⌈e^A⌉`. -/
theorem modelWallPrimeBalance_eq_of_head {c : ℕ → ℂ} {lam : ℕ → ℝ}
    (hW : _root_.RHTower.WeilPositiveFull lam)
    (hc : ∀ n, 2 ≤ n → modelAtom c n = (lam n : ℂ) / (Real.sqrt n : ℂ)) {F : ℝ → ℝ}
    {A : ℝ} (hA : ∀ u, u < -A → F u = 0) {p : ℂ} (hp : p.re < -(1 / 2)) :
    modelWallPrimeBalance c F p =
      (∑ n ∈ Finset.range ⌈Real.exp A⌉₊, modelAtom c n * cexp (p * Real.log n) *
          (levyHead F p (Real.log n) - negativeHalfLineLaplace (cx F) p)) +
        negativeHalfLineLaplace (cx F) p *
          LSeries (_root_.RHTower.WeilHerglotz.lamC lam) ((1 : ℂ) / 2 - p) +
        negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2) := by
  set N := ⌈Real.exp A⌉₊
  set LF := negativeHalfLineLaplace (cx F) p
  set t : ℕ → ℂ := fun n => LSeries.term (_root_.RHTower.WeilHerglotz.lamC lam) ((1 : ℂ) / 2 - p) n
  set d : ℕ → ℂ := fun n => modelAtom c n * cexp (p * Real.log n) *
    (levyHead F p (Real.log n) - LF)
  have hs1 : 1 < ((1 : ℂ) / 2 - p).re := by simp; linarith
  have ht : Summable t := _root_.RHTower.WeilHerglotz.summable_term_lamC hW hs1
  have hd0 : ∀ n ∉ Finset.range N, d n = 0 := by
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    have hexp : Real.exp A ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnN)
    have hn0 : (0 : ℝ) < n := (Real.exp_pos A).trans_le hexp
    have hlog : A ≤ Real.log n := by
      rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos A) hexp
    simp only [d, levyHead_eq_laplace_of_head hA hlog, LF, sub_self, mul_zero]
  have hdS : Summable d := summable_of_ne_finset_zero hd0
  have hsplit : ∀ n, modelAtom c n * (cexp (p * Real.log n) * levyHead F p (Real.log n)) =
      LF * t n + d n := by
    intro n
    simp only [d, t, ← modelAtom_mul_cexp_eq_term hc n p]
    ring
  unfold modelWallPrimeBalance modelPrimeHead
  rw [tsum_congr hsplit, (ht.mul_left LF).tsum_add hdS, tsum_mul_left, tsum_eq_sum hd0]
  simp only [LSeries, t, LF]
  ring

/-- **E-M15: every Weil-positive weight system passes stage 5 on compact profiles.** If
`λ` lies in the full Weil cone and `c(n) log n/√n = λ(n)/√n`, the model balance of every compactly
supported profile of `H` continues holomorphically to `Re p < 0`. -/
theorem modelCompactContinuation_of_weilPositiveFull {c : ℕ → ℂ} {lam : ℕ → ℝ}
    (hW : _root_.RHTower.WeilPositiveFull lam)
    (hc : ∀ n, 2 ≤ n → modelAtom c n = (lam n : ℂ) / (Real.sqrt n : ℂ)) :
    ModelCompactBeyondTheWallPrimeContinuation c := by
  intro F hF ⟨A₀, hA₀⟩
  set A : ℝ := max A₀ 0
  have hA : ∀ u, u < -A → F u = 0 := fun u hu => hA₀ u (by linarith [le_max_left A₀ 0])
  have hLF : Differentiable ℂ (negativeHalfLineLaplace (cx F)) :=
    differentiable_laplace_of_head hF.meas hF.integrable hF.support hA
  set Φ := _root_.RHTower.WeilSpectral.weilContinuation hW
  set Ar : ℂ → ℂ := fun s => Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s
  set H : ℂ → ℂ := fun p =>
    (∑ n ∈ Finset.range ⌈Real.exp A⌉₊, modelAtom c n * cexp (p * Real.log n) *
        (levyHead F p (Real.log n) - negativeHalfLineLaplace (cx F) p)) +
      negativeHalfLineLaplace (cx F) p * (Ar ((1 : ℂ) / 2 - p) - Φ ((1 : ℂ) / 2 - p)) -
      dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2)) p
  refine ⟨H, fun p hp => ?_, fun p hp => ?_⟩
  · -- holomorphy on the half-plane
    have hp' : p.re < 0 := hp
    have hD : DifferentiableAt ℂ (fun p => ∑ n ∈ Finset.range ⌈Real.exp A⌉₊,
        modelAtom c n * cexp (p * Real.log n) *
          (levyHead F p (Real.log n) - negativeHalfLineLaplace (cx F) p)) p := by
      refine DifferentiableAt.fun_sum fun n _ => ?_
      exact ((differentiableAt_const _).mul (by fun_prop)).mul
        (((differentiable_levyHead hF (Real.log n)) p).sub (hLF p))
    have hdig : DifferentiableAt ℂ (fun p : ℂ => Complex.digamma (((1 : ℂ) / 2 - p) / 2)) p := by
      have h := _root_.RHTower.differentiableAt_digamma_of_re_pos
        (z := ((1 : ℂ) / 2 - p) / 2) (by simp; linarith)
      exact h.comp p (by fun_prop)
    have hinv : DifferentiableAt ℂ (fun p : ℂ => 1 / ((1 : ℂ) / 2 - p)) p := by
      refine (differentiableAt_const _).div (by fun_prop) ?_
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hAr : DifferentiableAt ℂ (fun p => Ar ((1 : ℂ) / 2 - p)) p := by
      simp only [Ar]
      exact ((hdig.div_const 2).sub (differentiableAt_const _)).add hinv
    have hΦ : DifferentiableAt ℂ (fun p => Φ ((1 : ℂ) / 2 - p)) p := by
      have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have hmem : (1 : ℂ) / 2 - p ∈ {s : ℂ | 1 / 2 < s.re} := by
        show (1 / 2 : ℝ) < ((1 : ℂ) / 2 - p).re
        simp; linarith
      exact ((_root_.RHTower.WeilSpectral.differentiableOn_weilContinuation hW).differentiableAt
        (hopen.mem_nhds hmem)).comp p (by fun_prop)
    have hds : DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2))) p :=
      ((differentiableOn_dslope Filter.univ_mem).2 hLF.differentiableOn).differentiableAt
        Filter.univ_mem
    exact ((hD.add ((hLF p).mul (hAr.sub hΦ))).sub hds).differentiableWithinAt
  · -- agreement with the balance
    have hp' : p.re < -(1 / 2) := hp
    have hs1 : 1 < ((1 : ℂ) / 2 - p).re := by simp; linarith
    have hne : p + 1 / 2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hne' : p ≠ -(1 / 2) := fun h => hne (by rw [h]; ring)
    have hne2 : (1 : ℂ) / 2 - p - 1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hL : LSeries (_root_.RHTower.WeilHerglotz.lamC lam) ((1 : ℂ) / 2 - p) =
        Ar ((1 : ℂ) / 2 - p) + 1 / ((1 : ℂ) / 2 - p - 1) - Φ ((1 : ℂ) / 2 - p) := by
      rw [show Φ ((1 : ℂ) / 2 - p) = _root_.RHTower.WeilHerglotz.weilFunction lam ((1 : ℂ) / 2 - p)
        from _root_.RHTower.WeilSpectral.weilContinuation_eq hW hs1]
      simp only [Ar, _root_.RHTower.WeilHerglotz.weilFunction]
      ring
    rw [modelWallPrimeBalance_eq_of_head hW hc hA hp', hL]
    simp only [H]
    rw [dslope_of_ne _ hne', slope_def_module, smul_eq_mul]
    have e1 : p - -(1 / 2) = p + 1 / 2 := by ring
    have e2 : (1 : ℂ) / 2 - p - 1 = -(p + 1 / 2) := by ring
    rw [e1, e2]
    field_simp
    ring

/-! ### The case of ζ -/

/-- A smooth profile supported in `[−1, 0]` whose transform does not vanish at a given point. -/
theorem exists_compact_profile_laplace_ne_zero (z₀ : ℂ) :
    ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∀ u, u < -1 → G u = 0) ∧
      negativeHalfLineLaplace (cx G) z₀ ≠ 0 := by
  obtain ⟨ψ, hψ, hs, hsupp, hval⟩ := exists_smooth_negInterval_interpolating one_pos
    (fun _ : Fin 1 => -z₀) (fun a b _ => Subsingleton.elim a b) (fun _ => 1)
  have h1 := hval 0
  rw [laplaceTest_eq_integral] at h1
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hz : ∀ u, 0 ≤ u → ψ u = 0 := fun u hu => hsupp u fun hm => absurd hm.2 (not_lt.mpr hu)
  have hz1 : ∀ u, u < -1 → ψ u = 0 := fun u hu => hsupp u fun hm => absurd hm.1 (not_lt.mpr hu.le)
  set G₁ : ℝ → ℝ := fun u => (ψ u).re
  set G₂ : ℝ → ℝ := fun u => (ψ u).im
  have hG₁ : CriticalHalfLineEnergyDomain G₁ :=
    criticalHalfLineEnergyDomain_of_compact_negative (Complex.reCLM.contDiff.comp hψ2)
      (hs.comp_left Complex.zero_re) fun u hu => by simp [G₁, hz u hu]
  have hG₂ : CriticalHalfLineEnergyDomain G₂ :=
    criticalHalfLineEnergyDomain_of_compact_negative (Complex.imCLM.contDiff.comp hψ2)
      (hs.comp_left Complex.zero_im) fun u hu => by simp [G₂, hz u hu]
  have hint : ∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G →
      Integrable fun u : ℝ => cexp (z₀ * (u : ℂ)) * cx G u := fun G hGc hGs =>
    ((by fun_prop : Continuous fun u : ℝ => cexp (z₀ * (u : ℂ))).mul
      (Complex.continuous_ofReal.comp hGc)).integrable_of_hasCompactSupport
      (hGs.comp_left Complex.ofReal_zero).mul_left
  have hsum : negativeHalfLineLaplace (cx G₁) z₀ + I * negativeHalfLineLaplace (cx G₂) z₀ = 1 := by
    rw [← h1]
    unfold negativeHalfLineLaplace
    rw [← integral_const_mul, ← integral_add (hint G₁ (Complex.continuous_re.comp hψ.continuous)
      (hs.comp_left Complex.zero_re)) ((hint G₂ (Complex.continuous_im.comp hψ.continuous)
      (hs.comp_left Complex.zero_im)).const_mul I)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [cx, G₁, G₂]
    have hre : ψ u = ((ψ u).re : ℂ) + I * ((ψ u).im : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (ψ u)]
      ring
    rw [show -(-z₀ * (u : ℂ)) = z₀ * u by ring]
    conv_rhs => rw [hre]
    ring
  by_cases h₁ : negativeHalfLineLaplace (cx G₁) z₀ = 0
  · refine ⟨G₂, hG₂, fun u hu => by simp [G₂, hz1 u hu], fun h₂ => ?_⟩
    rw [h₁, h₂, mul_zero, add_zero] at hsum
    exact zero_ne_one hsum
  · exact ⟨G₁, hG₁, fun u hu => by simp [G₁, hz1 u hu], h₁⟩

/-- **For ζ the compact criterion is RH.** -/
theorem modelCompactContinuation_eulerLog_iff_riemannHypothesis :
    ModelCompactBeyondTheWallPrimeContinuation _root_.RHTower.eulerLogDirichletCoeff ↔
      RiemannHypothesis := by
  constructor
  · intro h
    by_contra hRH
    obtain ⟨q, hq⟩ := _root_.RHTower.exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    set q' := _root_.RHTower.xiZeroCopyReflectEquiv q
    have hq' : (centredZero q').re < 0 := by
      have e := _root_.RHTower.xiZeroCopy_reflect_val q
      simp only [centredZero, q', e, Complex.sub_re, Complex.one_re]
      norm_num; linarith
    obtain ⟨G, hG, hG1, hL⟩ := exists_compact_profile_laplace_ne_zero (centredZero q')
    obtain ⟨H, hH, heq⟩ := h G hG ⟨1, hG1⟩
    refine not_wallPrimeBalance_continues_of_seen_zero hG (δ := 0) (by norm_num) hq' hL
      ⟨H, hH, fun p hp => ?_⟩
    rw [heq hp, modelWallPrimeBalance_eulerLogDirichletCoeff]
  · intro hRH
    refine modelCompactContinuation_of_weilPositiveFull
      (_root_.RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) fun n hn => ?_
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlog_ne : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
    unfold modelAtom
    rw [if_pos hn, _root_.RHTower.eulerLogDirichletCoeff, ← Complex.natCast_log,
      div_mul_cancel₀ _ hlog_ne]

end GaloisForLFunctions.ExclusionOfTheCriticalState

#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.modelCompactContinuation_of_weilPositiveFull
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.modelCompactContinuation_eulerLog_iff_riemannHypothesis
