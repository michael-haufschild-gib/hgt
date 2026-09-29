import GaloisForLFunctions.RHTower.ThetaZeroDivisionCausalKernel
import GaloisForLFunctions.RHTower.OneSignTailImpossible
import GaloisForLFunctions.RHTower.ThetaAllSieveSeedProjector

/-!
# Cofinal prime deletion and the rate kernel of zero division

Let `L` be a conjugation-closed list of zeros of `XiC` (with multiplicities, `Re β > 0`) and `N` a
real polynomial with `N(0) = 0`, `deg N ≤ |L|`, `N ≠ 0`.  The division source
`u = Σ` (zero divisions of the theta source `k`) with Fourier transform `F(z) r(z²)`,
`r(w) = N(w)/∏_{β ∈ L}(1 − w/β²)`, has on `x ≥ 0` the causal form
`u(x) = c k(x) + ∫₀^∞ K(s) k(x + s) ds`, where `c = lim r(−σ²)` and the real exponential polynomial
`K` is the inverse Laplace transform of `r(−q²) − c`.

* **No eventual sign.**  All poles of `r(−q²)` are non-real, so by Landau's theorem (a positive
  measure has a singular Laplace transform at its real abscissa) `K` takes both signs arbitrarily
  far out; so does the rate density `2π K(s) e^{5s/2}` at the rates `λ = π e^{2s}`.
* **Cofinal deletion.**  For `f_ε = k + ε u` and `t > 1`, the normalized flux of the prime-deleted
  source is `(1 + εc) b_{D_S k}(t) + ε ∫₀^∞ K(s) e^{5s/2} b_{D_S k}(e^{2s} t) ds`; along every prime
  exhaustion it converges with all derivatives to
  `B_ε(t) = 2π(1 + εc) e^{−πt} + 2πε ∫₀^∞ K(s) e^{5s/2} e^{−π e^{2s} t} ds`.
* **All-sieve failure.**  `B_ε` is the seed flux of a signed seed measure whose negative part is
  nonzero, so it is not completely monotone for `ε ≠ 0`; one derivative order and one `t > 1`
  witness the failure for all deep enough deletions, along every exhaustion.
* **Exponential type.**  `limsup log|K(s)|/s = a`, the largest real part of a pole; with `m + 1` the
  largest pole order on `Re q = ±a`, `K(s) = s^m e^{as}(Σ_top (A_μ cos(Im μ s) + B_μ sin(Im μ s))
  + o(1))`.  For a single off-line quartet `α, ᾱ` this is
  `s^m e^{|Im α| s}(A cos(Re α s) + B sin(Re α s) + o(1))` with `(A, B) ≠ 0`; divisions by
  critical-line zeros have exponential type zero.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure headLaplace complexLaplace_ofReal hasDerivAt_complexLaplace
  false_of_analyticAt_abscissa)
open GaloisForLFunctions.HTGeometry (isPreconnected_diff_of_countable_of_convex_complex
  QuasiPolynomial CompletelyMonotoneOn CompletelyMonotoneDiff)

namespace RHTower

noncomputable section

/-! ## No eventual sign when the transform has a genuine pole -/

/-- **Landau: no eventual sign.**  Let `g` be continuous with `∫₀^∞ g(L) e^{-σL} dL = G(σ)` for
`σ > 3/2`, where `G` is analytic on `Re z > 1/4` off a finite set `S` of non-real points and has a
genuine pole at some `p ∈ S` with `Re p > 1/4`.  Then `g` is not eventually nonnegative. -/
theorem not_eventually_nonneg_of_pole {g : ℝ → ℝ} (hgc : Continuous g) {Gc : ℂ → ℂ}
    {S : Set ℂ} (hS : S.Finite) (hSre : ∀ z ∈ S, z.im ≠ 0)
    (hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) = Gc ((σ : ℂ)))
    (hGan : ∀ z : ℂ, 1 / 4 < z.re → z ∉ S → AnalyticAt ℂ Gc z)
    {p : ℂ} (hp : 1 / 4 < p.re) (hpole : ¬ 0 ≤ meromorphicOrderAt Gc p) :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → 0 ≤ g L := by
  rintro ⟨H, hH, hTpos⟩
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u) := fun u hu => hTpos (H + u) (by linarith)
  obtain ⟨c, hc, hc4, hc32⟩ := exists_isAbscissa_tail hgc hH hgi hpos
  set ν : Measure ℝ := tailMeasure g H
  have hSreal : ∀ σ : ℝ, (σ : ℂ) ∉ S := fun σ hσ => hSre _ hσ (Complex.ofReal_im σ)
  have hΦan : ∀ σ : ℝ, 1 / 4 < σ → AnalyticAt ℂ (tailTransform g Gc H) ((σ : ℂ)) := by
    intro σ hσ
    refine analyticAt_tailTransform hgc hH ?_ (hGan _ (by simpa using hσ) (hSreal σ))
    intro hcon
    have hre : ((σ : ℂ)).re = ((1 : ℂ) / 4).re := by rw [hcon]
    simp only [Complex.ofReal_re] at hre
    norm_num at hre
    linarith
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} := fun w hw =>
      ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  have hray : ∀ σ : ℝ, c < σ → tailTransform g Gc H ((σ : ℂ)) = complexLaplace ν ((σ : ℂ)) := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => tailTransform g Gc H ((t : ℂ))) (Ioi c) := fun t ht =>
      analyticAt_ofReal_comp (hΦan t (lt_of_le_of_lt hc4 ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν ((t : ℂ))) (Ioi c) := fun t ht =>
      analyticAt_ofReal_comp (hCLan _ (by simpa using ht))
    set z₀ : ℝ := max 2 c + 1
    have hz₀c : c < z₀ := by have := le_max_right 2 c; simp only [z₀]; linarith
    have hz₀big : (3 : ℝ) / 2 < z₀ := by have := le_max_left 2 c; simp only [z₀]; linarith
    have hev : (fun t : ℝ => tailTransform g Gc H ((t : ℂ)))
        =ᶠ[𝓝 z₀] fun t : ℝ => complexLaplace ν ((t : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show z₀ ∈ Ioi ((3 : ℝ) / 2) from hz₀big)] with t ht
      have hgt : (3 : ℝ) / 2 < t := ht
      rw [tailTransform_ofReal hgc hH (by linarith) (hgi t hgt) hpos (htrans t hgt),
        complexLaplace_ofReal]
    exact fun σ hσ => h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi hz₀c hev hσ
  -- Landau pins the abscissa at the reference pole
  have hceq : c = 1 / 4 := by
    by_contra hne
    have hcgt : 1 / 4 < c := lt_of_le_of_ne hc4 (Ne.symm hne)
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl _ (hSreal c)
    set δ : ℝ := min δ₁ (c - 1 / 4)
    have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
    refine false_of_analyticAt_abscissa (Φ := tailTransform g Gc H) hc hδpos (fun z hz => ?_)
      (fun σ h1 _ => by rw [hray σ h1, complexLaplace_ofReal])
    have hdist : dist z ((c : ℂ)) < δ := Metric.mem_ball.mp hz
    have hre : |z.re - c| < δ := by
      have h1 : |z.re - ((c : ℂ)).re| ≤ ‖z - ((c : ℂ))‖ := by
        simpa using Complex.abs_re_le_norm (z - ((c : ℂ)))
      rw [← Complex.dist_eq] at h1
      simpa using lt_of_le_of_lt h1 hdist
    have hzre : 1 / 4 < z.re := by
      have := abs_lt.mp hre; have := min_le_right δ₁ (c - 1 / 4); linarith
    have hz4 : z ≠ 1 / 4 := fun hcon => by rw [hcon] at hzre; norm_num at hzre
    exact analyticAt_tailTransform hgc hH hz4 (hGan z hzre fun hzS =>
      hsub (Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left _ _))) hzS)
  subst hceq
  -- the continuation is holomorphic across the whole half-plane
  set Psi : ℂ → ℂ := fun s : ℂ =>
    Complex.exp (-s * (H : ℂ)) * (complexLaplace ν s - 1 / (s - 1 / 4)) + headLaplace g H s
  have hPsian : ∀ z : ℂ, 1 / 4 < z.re → AnalyticAt ℂ Psi z := by
    intro z hz
    have hz4 : z ≠ 1 / 4 := fun hcon => by rw [hcon] at hz; norm_num at hz
    exact ((((analyticAt_id.neg).mul analyticAt_const).cexp).mul ((hCLan z hz).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz4)))).add
      (analyticAt_headLaplace hgc hH z)
  have hGPsi : ∀ σ : ℝ, 1 / 4 < σ → Gc ((σ : ℂ)) = Psi ((σ : ℂ)) := by
    intro σ hσ
    have h := hray σ hσ
    rw [tailTransform] at h
    have hEE : Complex.exp (-((σ : ℂ)) * (H : ℂ)) * Complex.exp (((σ : ℂ)) * (H : ℂ)) = 1 := by
      rw [← Complex.exp_add, show -((σ : ℂ)) * (H : ℂ) + ((σ : ℂ)) * (H : ℂ) = 0 by ring,
        Complex.exp_zero]
    simp only [Psi]
    rw [← h]
    linear_combination (headLaplace g H ((σ : ℂ)) - Gc ((σ : ℂ))) * hEE
  set W : Set ℂ := {s : ℂ | 1 / 4 < s.re} \ S
  have h2W : (2 : ℂ) ∈ W := ⟨by show (1 : ℝ) / 4 < (2 : ℂ).re; norm_num, by
    have := hSreal 2; simpa using this⟩
  have hWconn : IsPreconnected W :=
    isPreconnected_diff_of_countable_of_convex_complex (convex_halfSpace_re_gt _)
      (isOpen_lt continuous_const Complex.continuous_re) hS.countable h2W
  have hGW : AnalyticOnNhd ℂ Gc W := fun z hz => hGan z hz.1 hz.2
  have hPsiW : AnalyticOnNhd ℂ Psi W := fun z hz => hPsian z hz.1
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] ((2 : ℂ)), Gc z = Psi z := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ), Gc ((t : ℂ)) = Psi ((t : ℂ)) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (2 : ℝ) ∈ Ioi ((1 : ℝ) / 4) by norm_num))] with t ht
      exact hGPsi t ht
    have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have hEqOn := hGW.eqOn_of_preconnected_of_frequently_eq hPsiW hWconn h2W hfreq
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] p, s ∈ W := by
    have hcl : IsClosed (S \ {p}) := (hS.sdiff).isClosed
    have hnot : p ∉ S \ {p} := fun h => h.2 rfl
    have hre : ∀ᶠ s : ℂ in 𝓝 p, 1 / 4 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
    filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds hnot), nhdsWithin_le_nhds hre,
      self_mem_nhdsWithin] with s hs1 hs2 hs3
    exact ⟨hs2, fun hsS => hs1 ⟨hsS, hs3⟩⟩
  have hEv : Gc =ᶠ[𝓝[≠] p] Psi := by
    filter_upwards [hnear] with s hs
    exact hEqOn hs
  exact hpole ((meromorphicOrderAt_congr hEv).symm ▸ (hPsian p hp).meromorphicOrderAt_nonneg)

/-! ## The causal kernel changes sign arbitrarily late -/

theorem zero_not_mem_kernelExponents {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) :
    (0 : ℂ) ∉ kernelExponents L := by
  rintro ⟨β, hβ, h | h⟩
  · exact hL0 β hβ (by simpa [Complex.I_ne_zero] using h.symm)
  · exact hL0 β hβ (by simpa [Complex.I_ne_zero] using h.symm)

theorem ofReal_not_mem_kernelExponents {L : List ℂ} {t : ℝ} (ht : listImBound L < t) :
    (t : ℂ) ∉ kernelExponents L := fun h => by
  have := re_lt_of_mem_kernelExponents (q := (t : ℂ)) (fun β hβ => by
    simp only [Complex.ofReal_re]; linarith [abs_im_le_listImBound hβ]) h
  simp at this

/-- A nonzero numerator vanishing at `0` gives a nonzero kernel. -/
theorem combKernel_ne_zero {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) (he0 : e.eval 0 = 0) (hene : e ≠ 0) : combKernel L e ≠ 0 := by
  intro hK
  have hR : ∀ q, q ∉ kernelExponents L → rateSymbol L e q = combConst L e := fun q hq => by
    rw [rateSymbol_eq_add_laplace hL0 he hq, hK]
    simp [QuasiPolynomial.laplace]
  have hc : combConst L e = 0 := by
    rw [← hR 0 (zero_not_mem_kernelExponents hL0), rateSymbol]
    simp [he0, listDivisor, mul_zero]
  apply hene
  have hpos : 0 ≤ listImBound L := List.sum_nonneg fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
  refine Polynomial.eq_zero_of_infinite_isRoot e (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => -(((listImBound L + 1 + n : ℝ) : ℂ)) ^ 2) ?_ fun n => ?_)
  · intro m n hmn
    simp only at hmn
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_neg,
      Complex.ofReal_inj, neg_inj] at hmn
    have h1 : (0 : ℝ) ≤ listImBound L + 1 + m := by positivity
    have h2 : (0 : ℝ) ≤ listImBound L + 1 + n := by positivity
    have := (sq_eq_sq₀ h1 h2).1 hmn
    exact_mod_cast (by linarith : (m : ℝ) = n)
  · have hq : ((listImBound L + 1 + n : ℝ) : ℂ) ∉ kernelExponents L :=
      ofReal_not_mem_kernelExponents (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have h := hR _ hq
    rw [hc, rateSymbol, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (listDivisor_I_mul_ne_zero hL0 hq)

/-- Transport of a genuine pole under `z = θ + λq`. -/
theorem not_nonneg_order_affine {L : List ℂ} {e : Polynomial ℂ} {μ₀ : ℂ}
    (hpole : ¬ 0 ≤ meromorphicOrderAt (rateSymbol L e) μ₀) {c : ℂ} {lam : ℝ} (hlam : 0 < lam)
    (θ : ℂ) :
    ¬ 0 ≤ meromorphicOrderAt (fun z : ℂ => (lam : ℂ)⁻¹ * (rateSymbol L e ((z - θ) / lam) - c))
      (θ + lam * μ₀) := by
  intro h
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  set Gc : ℂ → ℂ := fun z : ℂ => (lam : ℂ)⁻¹ * (rateSymbol L e ((z - θ) / lam) - c)
  have hmer : MeromorphicAt Gc (θ + lam * μ₀) := by
    have hnum : AnalyticAt ℂ (fun z : ℂ => e.eval (-((z - θ) / lam) ^ 2)) (θ + lam * μ₀) :=
      (e.differentiable.comp (((differentiable_id.sub_const θ).div_const _).pow 2).neg).analyticAt _
    have hden : AnalyticAt ℂ (fun z : ℂ => listDivisor L (Complex.I * ((z - θ) / lam)))
        (θ + lam * μ₀) :=
      ((differentiable_listDivisor L).comp (((differentiable_id.sub_const θ).div_const _).const_mul
        Complex.I)).analyticAt _
    exact (MeromorphicAt.const _ _).mul ((hnum.meromorphicAt.div hden.meromorphicAt).sub
      (MeromorphicAt.const _ _))
  obtain ⟨g, hg, hfg⟩ := (hmer.meromorphicOrderAt_nonneg_iff).1 h
  apply hpole
  refine ((meromorphicAt_rateSymbol L e μ₀).meromorphicOrderAt_nonneg_iff).2
    ⟨fun q => lam * g (θ + lam * q) + c, ?_, ?_⟩
  · exact (analyticAt_const.mul (hg.comp_of_eq (analyticAt_const.add
      (analyticAt_const.mul analyticAt_id)) rfl)).add analyticAt_const
  · have htend : Tendsto (fun q : ℂ => θ + lam * q) (𝓝[≠] μ₀) (𝓝[≠] (θ + lam * μ₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_const.add (continuous_const.mul continuous_id)).tendsto μ₀).mono_left
          nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact fun h => hq (mul_left_cancel₀ hlam' (add_left_cancel h))
    filter_upwards [htend.eventually hfg] with q hq
    simp only [Gc] at hq
    rw [← hq, show (θ + lam * q - θ) / lam = q by field_simp; ring]
    field_simp
    ring

section RealKernel

variable {L : List ℂ} (hL : ThetaDivisionList L) (hconj : (L.map (starRingEnd ℂ)).Perm L)
  {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)

include hL hconj hN

theorem combKernel_eval_eq_ofReal (s : ℝ) :
    (combKernel L (N.map (algebraMap ℝ ℂ))).eval s = ((causalRateKernel L N s : ℝ) : ℂ) :=
  Complex.ext (by simp [causalRateKernel]) (by simp [(combKernel_real hL hconj hN).2 s])

theorem combConst_eq_ofReal :
    combConst L (N.map (algebraMap ℝ ℂ)) = ((causalRateConst L N : ℝ) : ℂ) :=
  Complex.ext (by simp [causalRateConst]) (by simp [(combKernel_real hL hconj hN).1])

/-- **The causal kernel is the inverse Laplace transform of `r(−q²) − c`.** -/
theorem integral_causalRateKernel_mul_exp {q : ℝ} (hq : listImBound L < q) :
    IntegrableOn (fun s => causalRateKernel L N s * Real.exp (-(q * s))) (Ioi 0) ∧
      ((∫ s in Ioi (0 : ℝ), causalRateKernel L N s * Real.exp (-(q * s)) : ℝ) : ℂ) =
        rateSymbol L (N.map (algebraMap ℝ ℂ)) q - causalRateConst L N := by
  have hdeg : (N.map (algebraMap ℝ ℂ)).natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  obtain ⟨hint, hval⟩ := integral_combKernel_mul_cexp hL.ne_zero hdeg (q := (q : ℂ)) (by simpa using hq)
  have hpt : ∀ s : ℝ, (combKernel L (N.map (algebraMap ℝ ℂ))).eval s * Complex.exp (-((q : ℂ) * s)) =
      ((causalRateKernel L N s * Real.exp (-(q * s)) : ℝ) : ℂ) := fun s => by
    rw [combKernel_eval_eq_ofReal hL hconj hN]; push_cast; ring_nf
  simp_rw [hpt] at hint hval
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun hint.re (fun s _ => by
      simp only [RCLike.re_to_complex, Complex.ofReal_re]) measurableSet_Ioi
  · rw [← integral_complex_ofReal, hval, combConst_eq_ofReal hL hconj hN]

/-- The division source is real on the half-line: `u = Re u` there. -/
theorem listComb_thetaListDivision_eq_ofReal {x : ℝ} (hx : 0 ≤ x) :
    listComb thetaListDivision L (N.map (algebraMap ℝ ℂ)) x = ((divisionSource L N x : ℝ) : ℂ) := by
  refine Complex.ext rfl ?_
  have hint := expMomentSource_thetaSourceC.integrableOn_eval_mul_shift
    (combKernel L (N.map (algebraMap ℝ ℂ))) x
  have him := integral_im hint
  simp only [RCLike.im_to_complex] at him
  rw [Complex.ofReal_im, listComb_congr (fun L' y hy => thetaListDivision_eq_halfListDivision L' y hy)
    _ _ hx, listComb_eq_kernel expMomentSource_thetaSourceC, Complex.add_im, ← him]
  simp [(combKernel_real hL hconj hN).1, (combKernel_real hL hconj hN).2, thetaSourceC,
    Complex.mul_im]

end RealKernel

/-- **The causal kernel changes sign arbitrarily late** (both signs; `ε = ±1`). -/
theorem causalRateKernel_not_eventually_signed {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (s₀ : ℝ) :
    ¬ ∀ s, s₀ < s → 0 ≤ ε * causalRateKernel L N s := by
  intro hsign
  set e := N.map (algebraMap ℝ ℂ)
  have hL0 := hL.ne_zero
  have hdeg : e.natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  have he0 : e.eval 0 = 0 := by
    simp only [e, Polynomial.eval_map, Polynomial.eval₂_at_zero, map_eq_zero]
    rwa [← Polynomial.coeff_zero_eq_eval_zero] at hN0
  have hene : e ≠ 0 := Polynomial.map_ne_zero hNne
  obtain ⟨μ₀, hμ₀⟩ := Finsupp.support_nonempty_iff.2 (combKernel_ne_zero hL0 hdeg he0 hene)
  have hpole : ¬ 0 ≤ meromorphicOrderAt (rateSymbol L e) μ₀ := by
    rw [meromorphicOrderAt_rateSymbol hL0 hdeg hμ₀]
    intro h
    have h' : ((0 : ℤ) : WithTop ℤ) ≤ ((-((((combKernel L e) μ₀).natDegree : ℤ) + 1)) : ℤ) := by
      simpa using h
    have := WithTop.coe_le_coe.1 h'
    omega
  obtain ⟨C, A, hC, hA, hb⟩ := exists_bound_eval (combKernel L e)
  have hK : ∀ s : ℝ, 0 ≤ s → |causalRateKernel L N s| ≤ C * Real.exp (A * s) := fun s hs =>
    (Complex.abs_re_le_norm _).trans (hb s hs)
  have hpos : 0 ≤ listImBound L := List.sum_nonneg fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
  set lam : ℝ := 1 / (2 * (A + listImBound L + 1))
  have hlam : 0 < lam := by positivity
  have hlamA : lam * A ≤ 1 / 2 := by
    simp only [lam]; rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hlamB : lam * listImBound L ≤ 1 / 2 := by
    simp only [lam]; rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  set g : ℝ → ℝ := fun x => ε * (causalRateKernel L N (lam * x) * Real.exp x)
  set Gc : ℂ → ℂ := fun z => (ε : ℂ) * ((lam : ℂ)⁻¹ * (rateSymbol L e ((z - 1) / lam) -
    combConst L e))
  have hgc : Continuous g := continuous_const.mul
    (((continuous_causalRateKernel L N).comp (continuous_const.mul continuous_id)).mul
      Real.continuous_exp)
  have hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun x : ℝ => g x * Real.exp (-σ * x)) (Ioi 0) := by
    intro σ hσ
    have hc : 0 < σ - 1 - lam * A := by linarith
    refine ((integrableOn_natPow_mul_exp_neg_mul_Ioi 0 hc).const_mul C).mono'
      ((hgc.mul (by fun_prop)).aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioi
        fun x hx => ?_)
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    simp only [g, Real.norm_eq_abs, abs_mul, hεabs, one_mul, abs_of_pos (Real.exp_pos _), pow_zero]
    calc |causalRateKernel L N (lam * x)| * Real.exp x * Real.exp (-σ * x)
        ≤ C * Real.exp (A * (lam * x)) * Real.exp x * Real.exp (-σ * x) := by
          gcongr; exact hK _ (by positivity)
      _ = C * Real.exp (-((σ - 1 - lam * A) * x)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ x in Ioi (0 : ℝ), g x * Real.exp (-σ * x) : ℝ) : ℂ) = Gc ((σ : ℂ)) := by
    intro σ hσ
    set q : ℝ := (σ - 1) / lam
    have hq : listImBound L < q := by
      simp only [q, lam]; rw [div_div_eq_mul_div, div_one]
      have h1 : 1 / 2 < σ - 1 := by linarith
      nlinarith
    have hsub := integral_comp_mul_left_Ioi (fun s => causalRateKernel L N s * Real.exp (-(q * s)))
      0 hlam
    rw [mul_zero] at hsub
    have hint_eq : ∫ x in Ioi (0 : ℝ), g x * Real.exp (-σ * x) =
        ε * ∫ x in Ioi (0 : ℝ), causalRateKernel L N (lam * x) * Real.exp (-(q * (lam * x))) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [g, q]
      rw [mul_assoc, mul_assoc, ← Real.exp_add]
      congr 3
      field_simp
      ring
    rw [hint_eq, hsub, smul_eq_mul]
    push_cast
    rw [(integral_causalRateKernel_mul_exp hL hconj hN hq).2]
    simp only [Gc, q]
    rw [combConst_eq_ofReal hL hconj hN]
    push_cast
    ring
  set Sset : Set ℂ := (fun μ => 1 + (lam : ℂ) * μ) '' kernelExponents L
  have hSfin : Sset.Finite := (kernelExponents_finite L).image _
  have hSre : ∀ z ∈ Sset, z.im ≠ 0 := by
    rintro z ⟨μ, ⟨β, hβ, rfl | rfl⟩, rfl⟩
    · have := hL.1 β hβ
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.I_re, Complex.I_im, one_mul]
      exact (mul_pos hlam this).ne'
    · have := hL.1 β hβ
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.neg_im, Complex.I_re,
        Complex.I_im, one_mul, mul_neg]
      exact neg_ne_zero.2 (mul_pos hlam this).ne'
  have hGan : ∀ z : ℂ, 1 / 4 < z.re → z ∉ Sset → AnalyticAt ℂ Gc z := by
    intro z _ hz
    have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hq : (z - 1) / lam ∉ kernelExponents L := fun h => hz ⟨_, h, by field_simp; ring⟩
    have hR : AnalyticAt ℂ (rateSymbol L e) ((z - 1) / lam) :=
      ((e.differentiable.comp (differentiable_id.pow 2).neg).analyticAt _).div
        (analyticAt_listDivisor_I_mul L _) (listDivisor_I_mul_ne_zero hL0 hq)
    exact analyticAt_const.mul (analyticAt_const.mul ((hR.comp_of_eq
      ((analyticAt_id.sub analyticAt_const).div_const) rfl).sub analyticAt_const))
  have hμre : -listImBound L ≤ μ₀.re := by
    obtain ⟨β, hβ, h | h⟩ := support_combKernel_subset L e hμ₀
    · rw [h]; simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub]
      linarith [abs_im_le_listImBound hβ, le_abs_self β.im]
    · rw [h]; simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
        one_mul, zero_sub, neg_neg]
      linarith [abs_im_le_listImBound hβ, neg_abs_le β.im]
  have hp : 1 / 4 < (1 + (lam : ℂ) * μ₀).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    nlinarith
  have hGpole : ¬ 0 ≤ meromorphicOrderAt Gc (1 + (lam : ℂ) * μ₀) := by
    have h := not_nonneg_order_affine hpole (c := combConst L e) hlam 1
    rcases hε with rfl | rfl
    · simpa [Gc] using h
    · have hneg : Gc = -fun z : ℂ => (lam : ℂ)⁻¹ * (rateSymbol L e ((z - 1) / lam) - combConst L e) := by
        funext z; simp [Gc]
      rwa [hneg, ← meromorphicOrderAt_neg]
  refine not_eventually_nonneg_of_pole hgc hSfin hSre hgi htrans hGan hp hGpole
    ⟨max s₀ 0 / lam, by positivity, fun x hx => ?_⟩
  have hlx : s₀ < lam * x := by
    have := (div_lt_iff₀ hlam).1 hx
    have := le_max_left s₀ 0
    nlinarith
  have := hsign _ hlx
  simp only [g]
  rw [← mul_assoc]
  exact mul_nonneg this (Real.exp_pos _).le

/-- **Both signs arbitrarily late.**  For a nonzero real numerator with `N(0) = 0`, the causal
kernel takes positive and negative values beyond every `s₀`. -/
theorem causalRateKernel_sign_changes {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) (s₀ : ℝ) :
    (∃ s, s₀ < s ∧ 0 < causalRateKernel L N s) ∧ ∃ s, s₀ < s ∧ causalRateKernel L N s < 0 := by
  constructor
  · by_contra h
    simp only [not_exists, not_and, not_lt] at h
    exact causalRateKernel_not_eventually_signed hL hconj hN hN0 hNne (Or.inr rfl) s₀
      fun s hs => by have := h s hs; linarith
  · by_contra h
    simp only [not_exists, not_and, not_lt] at h
    exact causalRateKernel_not_eventually_signed hL hconj hN hN0 hNne (Or.inl rfl) s₀
      fun s hs => by have := h s hs; linarith

/-! ## The deleted flux of the perturbed source -/

theorem thetaPrimeDeletion_source_mem {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ thetaPrimeDeletion S thetaCuspFullSource y ∧
      thetaPrimeDeletion S thetaCuspFullSource y ≤ thetaCuspFullSource y := by
  rw [thetaPrimeDeletion_thetaCuspFullSource_eq_tsum S hS y]
  have hnn : ∀ m, 0 ≤ thetaCuspSourceTerm y m := fun m => thetaCuspSourceTerm_nonneg hy m
  refine ⟨tsum_nonneg fun m => Set.indicator_nonneg (fun m _ => hnn m) m, ?_⟩
  exact ((summable_thetaCuspSourceTerm y).indicator _).tsum_le_tsum
    (fun m => Set.indicator_le_self' (fun m _ => hnn m) m) (summable_thetaCuspSourceTerm y)

theorem log_prod_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {T : Finset ℕ} (hT : T ⊆ S) :
    0 ≤ Real.log ((∏ p ∈ T, p : ℕ) : ℝ) :=
  Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2
    fun p hp => (hS p (hT hp)).ne_zero))

/-- The perturbed source `f_ε = k + ε u`. -/
def perturbedSource (L : List ℂ) (N : Polynomial ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  thetaCuspFullSource x + ε * divisionSource L N x

theorem exp_half_mul_shift_le {M x s : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    Real.exp (x / 2) * thetaCuspFullSource (x + s) ≤
      Real.exp (-((M + 1 / 2) * s)) *
        (Real.exp ((M + 1 / 2) * |x + s|) * thetaCuspFullSource (x + s)) := by
  have hk := (thetaCuspFullSource_pos (x + s)).le
  rw [← mul_assoc, ← Real.exp_add, abs_of_nonneg (by linarith)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hk
  nlinarith

/-- **Deletion of the causal representation.**  On `x ≥ 0`,
`D_S f_ε(x) = (1 + εc) D_S k(x) + ε ∫₀^∞ K(s) D_S k(x+s) ds`. -/
theorem thetaPrimeDeletion_perturbedSource (L : List ℂ) (N : Polynomial ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    thetaPrimeDeletion S (perturbedSource L N ε) x =
      (1 + ε * causalRateConst L N) * thetaPrimeDeletion S thetaCuspFullSource x +
        ε * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s *
          thetaPrimeDeletion S thetaCuspFullSource (x + s) := by
  unfold thetaPrimeDeletion
  have hshift : ∀ T ∈ S.powerset, 0 ≤ x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) := fun T hT =>
    add_nonneg hx (log_prod_nonneg hS (Finset.mem_powerset.1 hT))
  have hint : ∀ T ∈ S.powerset, IntegrableOn (fun s => causalRateKernel L N s *
      thetaCuspFullSource (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + s)) (Ioi 0) := fun T hT =>
    (divisionSource_eq L N (hshift T hT)).1
  have hsum : (fun s => causalRateKernel L N s * ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
      ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspFullSource (x + s + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))) =
      fun s => ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
        (causalRateKernel L N s *
          thetaCuspFullSource (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + s))) := by
    funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [show x + s + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) = x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + s by
      ring]
    ring
  rw [hsum, integral_finsetSum _ fun T hT => ((hint T hT).const_mul _).const_mul _, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [perturbedSource, (divisionSource_eq L N (hshift T hT)).2, integral_const_mul,
    integral_const_mul]
  ring


theorem exists_abs_causalRateKernel_le (L : List ℂ) (N : Polynomial ℝ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℝ, 0 ≤ s → |causalRateKernel L N s| ≤ C * Real.exp (A * s) := by
  obtain ⟨C, A, hC, hA, hb⟩ := exists_bound_eval (combKernel L (N.map (algebraMap ℝ ℂ)))
  exact ⟨C, A, hC, hA, fun s hs => (Complex.abs_re_le_norm _).trans (hb s hs)⟩

/-- The exponential moment `∫ e^{b|y|} k(y) dy`. -/
theorem integrable_exp_abs_mul_source (b : ℝ) :
    Integrable (fun y => Real.exp (b * |y|) * thetaCuspFullSource y) :=
  HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource b

/-- **Fubini integrability for the flux of the causal integral.** -/
theorem integrable_flux_kernel (L : List ℂ) (N : Polynomial ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : ℝ × ℝ => Real.exp (p.1 / 2) *
      (causalRateKernel L N p.2 * thetaPrimeDeletion S thetaCuspFullSource (p.1 + p.2)))
      ((volume.restrict (Ici a)).prod (volume.restrict (Ioi 0))) ∧
    Integrable (fun s => |causalRateKernel L N s| *
      ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s)) (volume.restrict (Ioi 0)) := by
  obtain ⟨C, A, hC, hA, hK⟩ := exists_abs_causalRateKernel_le L N
  set G := thetaPrimeDeletion S thetaCuspFullSource
  have hGc : Continuous G := continuous_thetaPrimeDeletion S continuous_thetaCuspFullSource
  have hFc : Continuous fun p : ℝ × ℝ => Real.exp (p.1 / 2) *
      (causalRateKernel L N p.2 * G (p.1 + p.2)) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (p.1 / 2)).mul
      (((continuous_causalRateKernel L N).comp continuous_snd).mul
        (hGc.comp (continuous_fst.add continuous_snd)))
  set M := A + 1 / 2
  set CM := ∫ y, Real.exp (M * |y|) * thetaCuspFullSource y
  have hCM : 0 ≤ CM := integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le
    (thetaCuspFullSource_pos y).le
  -- the inner integral over `x ≥ a` of the envelope
  have hinner : ∀ s : ℝ, 0 ≤ s → IntegrableOn (fun x => Real.exp (x / 2) * thetaCuspFullSource (x + s))
      (Ici a) ∧ ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s) ≤
        Real.exp (-(M * s)) * CM := by
    intro s hs
    have hI := ((integrable_exp_abs_mul_source M).comp_add_right s).integrableOn (s := Ici a)
    have hbd : ∀ x ∈ Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s) ≤
        Real.exp (-(M * s)) * (Real.exp (M * |x + s|) * thetaCuspFullSource (x + s)) := by
      intro x hx
      have hx0 : 0 ≤ x := ha.trans hx
      have hk := (thetaCuspFullSource_pos (x + s)).le
      rw [← mul_assoc, ← Real.exp_add, abs_of_nonneg (by linarith)]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hk
      simp only [M]
      nlinarith
    have hint : IntegrableOn (fun x => Real.exp (x / 2) * thetaCuspFullSource (x + s)) (Ici a) :=
      (hI.const_mul (Real.exp (-(M * s)))).mono'
        ((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).mul
          (continuous_thetaCuspFullSource.comp (continuous_id.add continuous_const))).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
          rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos _).le)]
          exact hbd x hx)
    refine ⟨hint, ?_⟩
    calc ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s)
        ≤ ∫ x in Ici a, Real.exp (-(M * s)) * (Real.exp (M * |x + s|) * thetaCuspFullSource (x + s)) :=
          setIntegral_mono_on hint (hI.const_mul _) measurableSet_Ici hbd
      _ ≤ ∫ x, Real.exp (-(M * s)) * (Real.exp (M * |x + s|) * thetaCuspFullSource (x + s)) :=
          setIntegral_le_integral ((integrable_exp_abs_mul_source M).comp_add_right s |>.const_mul _)
            (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos _).le))
      _ = Real.exp (-(M * s)) * CM := by
          rw [integral_const_mul]
          congr 1
          exact integral_add_right_eq_self (fun y => Real.exp (M * |y|) * thetaCuspFullSource y) s
  have hdecay : Integrable (fun s => C * CM * Real.exp (-(1 / 2 * s))) (volume.restrict (Ioi 0)) := by
    have := (integrableOn_natPow_mul_exp_neg_mul_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (C * CM)
    exact IntegrableOn.congr_fun this (fun s _ => by simp) measurableSet_Ioi
  have hsec : Integrable (fun s => |causalRateKernel L N s| *
      ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s)) (volume.restrict (Ioi 0)) := by
    refine hdecay.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    · refine ((continuous_causalRateKernel L N).abs.aestronglyMeasurable).mul ?_
      exact ((((by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (p.1 / 2)).mul
        (continuous_thetaCuspFullSource.comp (continuous_fst.add continuous_snd)))).stronglyMeasurable.integral_prod_left'
          (μ := volume.restrict (Ici a))).aestronglyMeasurable
    · have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
      obtain ⟨-, hle⟩ := hinner s hs0
      have hnn : 0 ≤ ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s) :=
        setIntegral_nonneg measurableSet_Ici fun x _ => mul_nonneg (Real.exp_pos _).le
          (thetaCuspFullSource_pos _).le
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hnn)]
      calc |causalRateKernel L N s| * ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s)
          ≤ (C * Real.exp (A * s)) * (Real.exp (-(M * s)) * CM) :=
            mul_le_mul (hK s hs0) hle hnn (by positivity)
        _ = C * CM * Real.exp (-(1 / 2 * s)) := by
            have he : Real.exp (A * s) * Real.exp (-(M * s)) = Real.exp (-(1 / 2 * s)) := by
              rw [← Real.exp_add]; simp only [M]; ring_nf
            rw [← he]; ring
  have hFbd : ∀ x s : ℝ, 0 ≤ x → 0 ≤ s → ‖Real.exp (x / 2) * (causalRateKernel L N s * G (x + s))‖ ≤
      |causalRateKernel L N s| * (Real.exp (x / 2) * thetaCuspFullSource (x + s)) := by
    intro x s hx hs
    have hG := thetaPrimeDeletion_source_mem hS (show 0 ≤ x + s by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hG.1]
    calc Real.exp (x / 2) * (|causalRateKernel L N s| * G (x + s))
        ≤ Real.exp (x / 2) * (|causalRateKernel L N s| * thetaCuspFullSource (x + s)) := by
          gcongr; exact hG.2
      _ = _ := by ring
  refine ⟨?_, hsec⟩
  rw [integrable_prod_iff' hFc.aestronglyMeasurable]
  refine ⟨ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_, ?_⟩
  · have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    exact ((hinner s hs0).1.const_mul |causalRateKernel L N s|).mono'
      (hFc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => hFbd x s (ha.trans hx) hs0)
  · refine hsec.mono' ((hFc.norm.stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Ici a))).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      ((hinner s hs0).1.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => hFbd x s (ha.trans hx) hs0)

/-- **The deleted flux.**  For `t > 1` and every finite set of primes,
`b_{D_S f_ε}(t) = (1 + εc) b_{D_S k}(t) + ε ∫₀^∞ K(s) e^{5s/2} b_{D_S k}(e^{2s} t) ds`. -/
theorem thetaNormalizedFlux_perturbedSource (L : List ℂ) (N : Polynomial ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ) {t : ℝ} (ht : 1 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion S (perturbedSource L N ε)) t =
      (1 + ε * causalRateConst L N) * thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) t +
        ε * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * (Real.exp (5 * s / 2) *
          thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t)) := by
  set a := Real.log t / 2
  have ha : 0 < a := by have := Real.log_pos ht; simp only [a]; linarith
  have ht0 : 0 < t := by linarith
  set G := thetaPrimeDeletion S thetaCuspFullSource
  obtain ⟨hprod, -⟩ := integrable_flux_kernel L N hS ha.le
  have hGint : IntegrableOn (fun x => Real.exp (x / 2) * G x) (Ici a) := by
    have := (integrable_exp_mul_thetaPrimeDeletion S (fun p hp => (hS p hp).pos) (1 / 2)).integrableOn
      (s := Ici a)
    exact IntegrableOn.congr_fun this (fun x _ => by simp only [G]; ring_nf) measurableSet_Ici
  have hsec := hprod.integral_prod_left
  have hsec' : IntegrableOn (fun x => Real.exp (x / 2) *
      ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * G (x + s)) (Ici a) := by
    refine IntegrableOn.congr_fun hsec (fun x _ => ?_) measurableSet_Ici
    simp only
    rw [integral_const_mul]
  have hLHS : ∫ x in Ici a, Real.exp (x / 2) * thetaPrimeDeletion S (perturbedSource L N ε) x =
      (1 + ε * causalRateConst L N) * (∫ x in Ici a, Real.exp (x / 2) * G x) +
        ε * ∫ x in Ici a, Real.exp (x / 2) * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * G (x + s) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hGint.const_mul _)
      (hsec'.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [thetaPrimeDeletion_perturbedSource L N hS ε (ha.le.trans hx)]
    ring
  have hswap : ∫ x in Ici a, Real.exp (x / 2) * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * G (x + s) =
      ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * ∫ x in Ici a, Real.exp (x / 2) * G (x + s) := by
    have h := integral_integral_swap (f := fun x s => Real.exp (x / 2) *
      (causalRateKernel L N s * G (x + s))) hprod
    calc ∫ x in Ici a, Real.exp (x / 2) * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * G (x + s)
        = ∫ x in Ici a, ∫ s in Ioi (0 : ℝ), Real.exp (x / 2) *
            (causalRateKernel L N s * G (x + s)) := by
          refine setIntegral_congr_fun measurableSet_Ici fun x _ => ?_
          rw [integral_const_mul]
      _ = ∫ s in Ioi (0 : ℝ), ∫ x in Ici a, Real.exp (x / 2) *
            (causalRateKernel L N s * G (x + s)) := h
      _ = _ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
          rw [← integral_const_mul]
          congr 1; funext x; ring
  have hinner : ∀ s : ℝ, t ^ (-(3 / 2 : ℝ)) * ∫ x in Ici a, Real.exp (x / 2) * G (x + s) =
      Real.exp (5 * s / 2) * thetaNormalizedFlux G (Real.exp (2 * s) * t) := fun s => by
    rw [← thetaNormalizedFlux_comp_add G s ht0]
    rfl
  rw [show thetaNormalizedFlux (thetaPrimeDeletion S (perturbedSource L N ε)) t =
      t ^ (-(3 / 2 : ℝ)) * ∫ x in Ici a, Real.exp (x / 2) *
        thetaPrimeDeletion S (perturbedSource L N ε) x from rfl, hLHS, hswap,
    show thetaNormalizedFlux G t = t ^ (-(3 / 2 : ℝ)) * ∫ x in Ici a, Real.exp (x / 2) * G x from rfl]
  simp_rw [← hinner]
  have hc : ∫ s in Ioi (0 : ℝ), causalRateKernel L N s *
      (t ^ (-(3 / 2 : ℝ)) * ∫ x in Ici a, Real.exp (x / 2) * G (x + s)) =
      t ^ (-(3 / 2 : ℝ)) * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s *
        ∫ x in Ici a, Real.exp (x / 2) * G (x + s) := by
    rw [← integral_const_mul]; congr 1; funext s; ring
  rw [hc]
  ring

/-! ## The cofinal limit -/

theorem thetaNormalizedFlux_thetaPrimeDeletion_le_source {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {u : ℝ} (hu : 0 < u) :
    thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) u ≤
      thetaNormalizedFlux thetaCuspFullSource u := by
  rw [thetaNormalizedFlux_thetaPrimeDeletion_eq hS hu, thetaNormalizedFlux_thetaCuspFullSource hu]
  exact (summable_thetaGaussFlux_atoms hu).indicator _ |>.tsum_le_tsum
    (fun n => Set.indicator_le_self' (fun m _ => by positivity) n) (summable_thetaGaussFlux_atoms hu)

/-- The seed-limit flux `B_ε(t) = (1 + εc) 2π e^{-πt} + ε ∫₀^∞ K(s) e^{5s/2} 2π e^{-π e^{2s} t} ds`. -/
def cofinalFlux (L : List ℂ) (N : Polynomial ℝ) (ε t : ℝ) : ℝ :=
  (1 + ε * causalRateConst L N) * (2 * Real.pi * Real.exp (-Real.pi * t)) +
    ε * ∫ s in Ioi (0 : ℝ), causalRateKernel L N s *
      (Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * t))))

/-- **Cofinal deletion.**  Along every exhaustion of the primes the deleted fluxes of `f_ε`
converge to `B_ε(t)` for `t > 1`. -/
theorem tendsto_flux_perturbedSource (L : List ℂ) (N : Polynomial ℝ) {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (ε : ℝ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun j => thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε)) t)
      atTop (𝓝 (cofinalFlux L N ε t)) := by
  have ht0 : 0 < t := by linarith
  set a := Real.log t / 2
  have ha : 0 < a := by have := Real.log_pos ht; simp only [a]; linarith
  simp_rw [thetaNormalizedFlux_perturbedSource L N (hS.prime _) ε ht]
  refine ((hS.tendsto_deletedFlux ht0).const_mul _).add (Tendsto.const_mul ε ?_)
  obtain ⟨-, hbound⟩ := integrable_flux_kernel L N (S := ∅) (by simp) ha.le
  have hshift : ∀ s : ℝ, Real.exp (5 * s / 2) * thetaNormalizedFlux thetaCuspFullSource
      (Real.exp (2 * s) * t) = t ^ (-(3 / 2 : ℝ)) *
        ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s) := fun s => by
    rw [← thetaNormalizedFlux_comp_add _ s ht0]; rfl
  refine tendsto_integral_of_dominated_convergence (fun s => t ^ (-(3 / 2 : ℝ)) *
    (|causalRateKernel L N s| * ∫ x in Ici a, Real.exp (x / 2) * thetaCuspFullSource (x + s)))
    (fun j => ((continuous_causalRateKernel L N).mul
      (continuous_shifted_deletedFlux_in_shift (hS.prime j) ht0)).aestronglyMeasurable)
    (hbound.const_mul _) (fun j => ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  · have hu : 0 < Real.exp (2 * s) * t := by positivity
    have h0 := thetaNormalizedFlux_thetaPrimeDeletion_nonneg (hS.prime j) hu
    have h1 := thetaNormalizedFlux_thetaPrimeDeletion_le_source (hS.prime j) hu
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h0]
    calc |causalRateKernel L N s| * (Real.exp (5 * s / 2) *
          thetaNormalizedFlux (thetaPrimeDeletion (S j) thetaCuspFullSource) (Real.exp (2 * s) * t))
        ≤ |causalRateKernel L N s| * (Real.exp (5 * s / 2) *
          thetaNormalizedFlux thetaCuspFullSource (Real.exp (2 * s) * t)) := by gcongr
      _ = _ := by rw [hshift]; ring
  · have hu : 0 < Real.exp (2 * s) * t := by positivity
    exact ((hS.tendsto_deletedFlux hu).const_mul _).const_mul _

/-! ## The signed seed measure -/

/-- The weight `e^{-π e^{2s}}` moving the seed flux from `u` to `1 + u`. -/
def seedShiftWeight (s : ℝ) : ℝ := Real.exp (-Real.pi * Real.exp (2 * s))

theorem seedShiftWeight_pos (s : ℝ) : 0 < seedShiftWeight s := Real.exp_pos _

theorem exp_mul_seedShiftWeight_le (A : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (A * s) * seedShiftWeight s ≤
      Real.exp ((A + 1) ^ 2 / (8 * Real.pi)) * Real.exp (-s) := by
  rw [seedShiftWeight, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * s by linarith)
  have hπ := Real.pi_pos
  have h1 : (A + 1) * s - 2 * Real.pi * s ^ 2 ≤ (A + 1) ^ 2 / (8 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (A + 1 - 4 * Real.pi * s)]
  nlinarith [mul_le_mul_of_nonneg_left hq hπ.le]

/-- One signed part (`σ = ±1`) of the translation measure behind `B_ε(1 + ·)`: an atom at `0` of
mass `(σ(1+εc))⁺ e^{-π}` and the density `(σεK)⁺ e^{-π e^{2s}}` on `s > 0`. -/
def seedPart (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (σ * (1 + ε * causalRateConst L N)) 0 * seedShiftWeight 0) •
      Measure.dirac 0 +
    (volume.restrict (Ioi 0)).withDensity fun s =>
      ENNReal.ofReal (max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s)

theorem measurable_seedPart_density (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) :
    Measurable fun s => ENNReal.ofReal (max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s) :=
  ENNReal.measurable_ofReal.comp ((((continuous_causalRateKernel L N).const_mul ε).const_mul σ).max
    continuous_const |>.mul (by unfold seedShiftWeight; fun_prop)).measurable

/-- A common envelope `C' e^{-s}` for the densities. -/
theorem exists_seedPart_density_le (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) (hσ : |σ| = 1) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s *
      Real.exp (B * s) ≤ C * Real.exp (-s) := by
  obtain ⟨C, A, hC, hA, hK⟩ := exists_abs_causalRateKernel_le L N
  refine ⟨|ε| * C * Real.exp ((A + B + 1) ^ 2 / (8 * Real.pi)), by positivity, fun s hs => ?_⟩
  have hmax : max (σ * (ε * causalRateKernel L N s)) 0 ≤ |ε| * (C * Real.exp (A * s)) := by
    refine max_le ?_ (by positivity)
    calc σ * (ε * causalRateKernel L N s) ≤ |σ * (ε * causalRateKernel L N s)| := le_abs_self _
      _ = |ε| * |causalRateKernel L N s| := by rw [abs_mul, abs_mul, hσ, one_mul]
      _ ≤ |ε| * (C * Real.exp (A * s)) := mul_le_mul_of_nonneg_left (hK s hs) (abs_nonneg _)
  have hw := exp_mul_seedShiftWeight_le (A + B) hs
  calc max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s * Real.exp (B * s)
      ≤ |ε| * (C * Real.exp (A * s)) * seedShiftWeight s * Real.exp (B * s) := by
        gcongr; exact (seedShiftWeight_pos s).le
    _ = |ε| * C * (Real.exp ((A + B) * s) * seedShiftWeight s) := by
        rw [add_mul, Real.exp_add]; ring
    _ ≤ |ε| * C * (Real.exp ((A + B + 1) ^ 2 / (8 * Real.pi)) * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

theorem integrableOn_seedPart_density_mul (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) (hσ : |σ| = 1)
    {D : ℝ} (B : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgb : ∀ s : ℝ, 0 ≤ s → |g s| ≤ D * Real.exp (B * s)) :
    IntegrableOn (fun s => max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s * g s)
      (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_seedPart_density_le L N ε σ hσ B
  have hexp := (integrableOn_natPow_mul_exp_neg_mul_Ioi 0 one_pos).const_mul (D * C)
  refine hexp.mono' (((((continuous_causalRateKernel L N).const_mul ε).const_mul σ).max
    continuous_const |>.mul (by unfold seedShiftWeight; fun_prop)).mul hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (le_max_right _ _)
    (seedShiftWeight_pos s).le)]
  have hD : 0 ≤ D := by
    have := (abs_nonneg (g 0)).trans (hgb 0 le_rfl)
    simpa using this
  calc max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s * |g s|
      ≤ max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s * (D * Real.exp (B * s)) :=
        mul_le_mul_of_nonneg_left (hgb s hs0) (mul_nonneg (le_max_right _ _)
          (seedShiftWeight_pos s).le)
    _ = D * (max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s * Real.exp (B * s)) := by
        ring
    _ ≤ D * (C * Real.exp (-s)) := mul_le_mul_of_nonneg_left (hb s hs0) hD
    _ = D * C * (s ^ 0 * Real.exp (-(1 * s))) := by simp; ring

theorem isFiniteMeasure_seedPart (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) (hσ : |σ| = 1) :
    IsFiniteMeasure (seedPart L N ε σ) := by
  have hfin : HasFiniteIntegral (fun s => max (σ * (ε * causalRateKernel L N s)) 0 *
      seedShiftWeight s) (volume.restrict (Ioi 0)) := by
    have h := integrableOn_seedPart_density_mul L N ε σ hσ (D := 1) 0 (g := fun _ => 1)
      continuous_const (fun s _ => by simp)
    simpa using h.hasFiniteIntegral
  haveI := isFiniteMeasure_withDensity_ofReal hfin
  unfold seedPart
  infer_instance

theorem seedPart_compl_Ici (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) :
    seedPart L N ε σ (Ici 0)ᶜ = 0 := by
  unfold seedPart
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ici.compl,
    withDensity_apply _ measurableSet_Ici.compl, Measure.restrict_restrict measurableSet_Ici.compl]
  have h2 : (Ici (0 : ℝ))ᶜ ∩ Ioi 0 = ∅ := by
    ext s; simp only [mem_inter_iff, mem_compl_iff, mem_Ici, mem_Ioi, mem_empty_iff_false,
      iff_false, not_and, not_le]; intro h h'; linarith
  rw [h2, Measure.restrict_empty, lintegral_zero_measure]
  simp [Set.indicator]

theorem integrable_exp_neg_half_seedPart (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) (hσ : |σ| = 1) :
    Integrable (fun s => Real.exp (-(s / 2))) (seedPart L N ε σ) := by
  haveI := isFiniteMeasure_seedPart L N ε σ hσ
  have hae : ∀ᵐ s ∂(seedPart L N ε σ), s ∈ Ici (0 : ℝ) := ae_iff.2 (seedPart_compl_Ici L N ε σ)
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop : Continuous fun s : ℝ =>
    Real.exp (-(s / 2))).aestronglyMeasurable ?_
  filter_upwards [hae] with s hs
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.2 (by have : (0 : ℝ) ≤ s := hs; linarith)

/-- The seed profile `e^{5s/2} 2π e^{-π e^{2s} u}`. -/
theorem abs_seedProfile_le {u : ℝ} (hu : 0 < u) (s : ℝ) :
    |Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * u)))| ≤
      2 * Real.pi * Real.exp (5 / 2 * s) := by
  rw [abs_of_pos (by positivity)]
  have h1 : Real.exp (-Real.pi * (Real.exp (2 * s) * u)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := Real.pi_pos; nlinarith [mul_pos (Real.exp_pos (2 * s)) hu])
  calc Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * u)))
      ≤ Real.exp (5 * s / 2) * (2 * Real.pi * 1) := by gcongr
    _ = 2 * Real.pi * Real.exp (5 / 2 * s) := by ring_nf

theorem thetaSeedFlux_seedPart (L : List ℂ) (N : Polynomial ℝ) (ε σ : ℝ) (hσ : |σ| = 1) {u : ℝ}
    (hu : 0 < u) :
    thetaSeedFlux (seedPart L N ε σ) u =
      max (σ * (1 + ε * causalRateConst L N)) 0 * (2 * Real.pi * Real.exp (-Real.pi * (1 + u))) +
        ∫ s in Ioi (0 : ℝ), max (σ * (ε * causalRateKernel L N s)) 0 *
          (Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * (1 + u))))) := by
  set g : ℝ → ℝ := fun s => Real.exp (5 * s / 2) * (2 * Real.pi *
    Real.exp (-Real.pi * (Real.exp (2 * s) * u)))
  have hgc : Continuous g := by simp only [g]; fun_prop
  have hdens := measurable_seedPart_density L N ε σ
  have hint2 : Integrable g ((volume.restrict (Ioi 0)).withDensity fun s =>
      ENNReal.ofReal (max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s)) := by
    rw [integrable_withDensity_iff hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have h := integrableOn_seedPart_density_mul L N ε σ hσ (D := 2 * Real.pi) (5 / 2) hgc
      (fun s _ => abs_seedProfile_le hu s)
    refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) (seedShiftWeight_pos s).le)]
    ring
  have hint1 : Integrable g (ENNReal.ofReal (max (σ * (1 + ε * causalRateConst L N)) 0 *
      seedShiftWeight 0) • Measure.dirac 0) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  unfold thetaSeedFlux seedPart
  rw [integral_add_measure hint1 hint2, integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) (seedShiftWeight_pos 0).le)]
  congr 1
  · simp only [g, seedShiftWeight, smul_eq_mul, mul_zero, Real.exp_zero, zero_div, one_mul]
    rw [show -Real.pi * (1 + u) = -Real.pi * 1 + -Real.pi * u by ring, Real.exp_add]
    ring_nf
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) (seedShiftWeight_pos s).le),
      smul_eq_mul, seedShiftWeight]
    have he : Real.exp (-Real.pi * Real.exp (2 * s)) * Real.exp (-Real.pi * (Real.exp (2 * s) * u)) =
        Real.exp (-Real.pi * (Real.exp (2 * s) * (1 + u))) := by
      rw [← Real.exp_add]; ring_nf
    rw [← he]
    ring

theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-1 * x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **The cofinal flux is a signed seed flux**: `B_ε(1 + u) = b_{seed,ν₁}(u) − b_{seed,ν₂}(u)`. -/
theorem cofinalFlux_eq_seedFlux_sub (L : List ℂ) (N : Polynomial ℝ) (ε : ℝ) {u : ℝ} (hu : 0 < u) :
    cofinalFlux L N ε (1 + u) =
      thetaSeedFlux (seedPart L N ε 1) u - thetaSeedFlux (seedPart L N ε (-1)) u := by
  have h1 : |(1 : ℝ)| = 1 := abs_one
  have hm1 : |(-1 : ℝ)| = 1 := by simp
  rw [thetaSeedFlux_seedPart L N ε 1 h1 hu, thetaSeedFlux_seedPart L N ε (-1) hm1 hu]
  set g : ℝ → ℝ := fun s => Real.exp (5 * s / 2) * (2 * Real.pi *
    Real.exp (-Real.pi * (Real.exp (2 * s) * (1 + u))))
  have hgc : Continuous g := by simp only [g]; fun_prop
  have hu1 : 0 < 1 + u := by linarith
  have hi : ∀ σ : ℝ, |σ| = 1 → IntegrableOn (fun s => max (σ * (ε * causalRateKernel L N s)) 0 *
      g s) (Ioi 0) := fun σ hσ => by
    have h := integrableOn_seedPart_density_mul L N ε σ hσ (D := 2 * Real.pi *
      Real.exp (Real.pi)) (5 / 2) (g := fun s => g s / seedShiftWeight s)
      (hgc.div (by unfold seedShiftWeight; fun_prop) fun s => (seedShiftWeight_pos s).ne')
      (fun s hs => by
        simp only [g, seedShiftWeight]
        rw [abs_of_pos (by positivity)]
        have he : Real.exp (5 * s / 2) * (2 * Real.pi *
            Real.exp (-Real.pi * (Real.exp (2 * s) * (1 + u)))) /
              Real.exp (-Real.pi * Real.exp (2 * s)) =
            2 * Real.pi * Real.exp (5 / 2 * s) * Real.exp (-Real.pi * (Real.exp (2 * s) * u)) := by
          rw [div_eq_iff (Real.exp_pos _).ne', mul_assoc (2 * Real.pi * Real.exp (5 / 2 * s)),
            ← Real.exp_add]
          ring_nf
        rw [he]
        have hle : Real.exp (-Real.pi * (Real.exp (2 * s) * u)) ≤ Real.exp Real.pi :=
          Real.exp_le_exp.2 (by nlinarith [mul_pos Real.pi_pos (mul_pos (Real.exp_pos (2 * s)) hu),
            Real.pi_pos])
        calc 2 * Real.pi * Real.exp (5 / 2 * s) * Real.exp (-Real.pi * (Real.exp (2 * s) * u))
            ≤ 2 * Real.pi * Real.exp (5 / 2 * s) * Real.exp Real.pi := by gcongr
          _ = _ := by ring)
    refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    field_simp [(seedShiftWeight_pos s).ne']
  unfold cofinalFlux
  rw [← integral_const_mul, add_sub_add_comm, ← sub_mul, ← integral_sub (hi 1 h1) (hi (-1) hm1)]
  simp only [one_mul]
  rw [max_sub_max_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [g]
  rw [← sub_mul, max_sub_max_neg]
  ring

/-! ## Failure of the all-sieve Bernstein property -/

section Failure

variable {L : List ℂ} (hL : ThetaDivisionList L) (hconj : (L.map (starRingEnd ℂ)).Perm L)
  {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length) (hN0 : N.eval 0 = 0) (hNne : N ≠ 0)

include hL hconj hN hN0 hNne

/-- **The cofinal flux is not completely monotone** on `(1, ∞)`: its rate measure would have to be
positive, but the continuous part `ε K(s) ds` changes sign arbitrarily late and the atom at `λ = π`
cannot mask it. -/
theorem not_completelyMonotoneOn_cofinalFlux {ε : ℝ} (hε : ε ≠ 0) :
    ¬ CompletelyMonotoneOn (fun u => cofinalFlux L N ε (1 + u)) := by
  intro hCM
  have h1 : |(1 : ℝ)| = 1 := abs_one
  have hm1 : |(-1 : ℝ)| = 1 := by simp
  haveI := isFiniteMeasure_seedPart L N ε 1 h1
  haveI := isFiniteMeasure_seedPart L N ε (-1) hm1
  have hCM' : CompletelyMonotoneOn fun u =>
      thetaSeedFlux (seedPart L N ε 1) u - thetaSeedFlux (seedPart L N ε (-1)) u :=
    hCM.congr_Ioi fun u hu => cofinalFlux_eq_seedFlux_sub L N ε hu
  have hle := le_of_completelyMonotoneOn_thetaSeedFlux_sub
    (integrable_exp_neg_half_seedPart L N ε 1 h1) (integrable_exp_neg_half_seedPart L N ε (-1) hm1)
    hCM'
  obtain ⟨s₁, hs₁, hneg⟩ : ∃ s, 0 < s ∧ ε * causalRateKernel L N s < 0 := by
    rcases lt_or_gt_of_ne hε with hε' | hε'
    · obtain ⟨s, hs, hK⟩ := (causalRateKernel_sign_changes hL hconj hN hN0 hNne 0).1
      exact ⟨s, hs, mul_neg_of_neg_of_pos hε' hK⟩
    · obtain ⟨s, hs, hK⟩ := (causalRateKernel_sign_changes hL hconj hN hN0 hNne 0).2
      exact ⟨s, hs, mul_neg_of_pos_of_neg hε' hK⟩
  set U : Set ℝ := {s | 0 < s ∧ ε * causalRateKernel L N s < 0}
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_id).inter
    (isOpen_lt ((continuous_causalRateKernel L N).const_mul ε) continuous_const)
  have hUm : MeasurableSet U := hUo.measurableSet
  have h0U : (0 : ℝ) ∉ U := fun h => lt_irrefl _ h.1
  have hUsub : U ⊆ Ioi 0 := fun s hs => hs.1
  have hpart : ∀ σ : ℝ, seedPart L N ε σ U = ∫⁻ s in U, ENNReal.ofReal
      (max (σ * (ε * causalRateKernel L N s)) 0 * seedShiftWeight s) := fun σ => by
    unfold seedPart
    rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hUm, withDensity_apply _ hUm,
      Measure.restrict_restrict hUm, Set.inter_eq_left.2 hUsub, Set.indicator_of_notMem h0U]
    simp
  have hpos0 : seedPart L N ε 1 U = 0 := by
    rw [hpart]
    refine (setLIntegral_congr_fun hUm fun s hs => ?_).trans lintegral_zero
    rw [one_mul, max_eq_right hs.2.le, zero_mul, ENNReal.ofReal_zero]
  have hnegpos : 0 < seedPart L N ε (-1) U := by
    rw [hpart, lintegral_pos_iff_support (measurable_seedPart_density L N ε (-1))]
    refine lt_of_lt_of_le ((hUo.measure_pos volume ⟨s₁, hs₁, hneg⟩)) ?_
    rw [Measure.restrict_apply' hUm]
    refine measure_mono fun s hs => ⟨?_, hs⟩
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (lt_max_of_lt_left (by linarith [hs.2])) (seedShiftWeight_pos s)
  have := (Measure.le_iff'.1 hle) U
  rw [hpos0] at this
  exact absurd (le_zero_iff.1 this) hnegpos.ne'

/-- **Eventual finite-depth witness.**  Along every exhaustion of the primes, one difference order
`k`, one step `δ` and one point `t > 1` witness the failure of complete monotonicity of every
sufficiently deep deleted flux of `f_ε = k + εu`. -/
theorem exists_allSieve_failure_witness {ε : ℝ} (hε : ε ≠ 0) {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) :
    ∃ (k : ℕ) (δ t : ℝ), 0 < δ ∧ 1 < t ∧ ∀ᶠ j in atTop, (-1 : ℝ) ^ k *
      (fwdDiff δ)^[k] (thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε))) t < 0 := by
  have h1 : |(1 : ℝ)| = 1 := abs_one
  have hm1 : |(-1 : ℝ)| = 1 := by simp
  haveI := isFiniteMeasure_seedPart L N ε 1 h1
  haveI := isFiniteMeasure_seedPart L N ε (-1) hm1
  have hcont : ContinuousOn (fun u => cofinalFlux L N ε (1 + u)) (Ioi 0) :=
    ((continuousOn_thetaSeedFlux (integrable_exp_neg_half_seedPart L N ε 1 h1)).sub
      (continuousOn_thetaSeedFlux (integrable_exp_neg_half_seedPart L N ε (-1) hm1))).congr
      fun u hu => cofinalFlux_eq_seedFlux_sub L N ε hu
  have hnot : ¬ CompletelyMonotoneDiff (fun u => cofinalFlux L N ε (1 + u)) := fun h =>
    not_completelyMonotoneOn_cofinalFlux hL hconj hN hN0 hNne hε ⟨h, hcont⟩
  unfold CompletelyMonotoneDiff at hnot
  simp only [not_forall, not_le] at hnot
  obtain ⟨k, δ, hδ, t, ht, hlt⟩ := hnot
  refine ⟨k, δ, 1 + t, hδ, by linarith, ?_⟩
  have hlim : Tendsto (fun j => (-1 : ℝ) ^ k * (fwdDiff δ)^[k]
      (thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε))) (1 + t)) atTop
      (𝓝 ((-1 : ℝ) ^ k * (fwdDiff δ)^[k] (fun u => cofinalFlux L N ε (1 + u)) t)) := by
    simp only [fwdDiff_iter_eq_sum_mul]
    refine (tendsto_finsetSum _ fun i _ => ?_).const_mul _
    have hiδ : (0 : ℝ) ≤ i * δ := by positivity
    have hpt : 1 < 1 + t + i * δ := by linarith
    have := (tendsto_flux_perturbedSource L N hS ε hpt).const_mul
      ((((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) : ℤ) : ℝ))
    simpa [add_assoc] using this
  exact hlim.eventually (gt_mem_nhds hlt)

/-- **All-sieve failure.**  For `ε ≠ 0`, along every exhaustion of the primes the deleted fluxes
of `f_ε` are eventually not completely monotone. -/
theorem eventually_not_completelyMonotoneOn_flux {ε : ℝ} (hε : ε ≠ 0) {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) :
    ∀ᶠ j in atTop, ¬ CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaPrimeDeletion (S j) (perturbedSource L N ε))) := by
  obtain ⟨k, δ, t, hδ, ht, hev⟩ := exists_allSieve_failure_witness hL hconj hN hN0 hNne hε hS
  filter_upwards [hev] with j hj hCM
  exact absurd (hCM.1 k δ hδ t (by linarith)) (not_le.2 hj)

end Failure

/-! ## The rate density and the exponential type -/

/-- The signed Gaussian-rate density `2π K(s) e^{5s/2}` at the rate `λ = π e^{2s}`. -/
def rateDensity (L : List ℂ) (N : Polynomial ℝ) (s : ℝ) : ℝ :=
  2 * Real.pi * causalRateKernel L N s * Real.exp (5 * s / 2)

/-- `B_ε` is the Laplace transform in the rate `λ = π e^{2s}` of the atom `(1 + εc) 2π δ_π` and the
signed density `ε · 2π K(s) e^{5s/2} ds`. -/
theorem cofinalFlux_eq_rate (L : List ℂ) (N : Polynomial ℝ) (ε t : ℝ) :
    cofinalFlux L N ε t = (1 + ε * causalRateConst L N) * (2 * Real.pi * Real.exp (-t * Real.pi)) +
      ε * ∫ s in Ioi (0 : ℝ), rateDensity L N s * Real.exp (-t * (Real.pi * Real.exp (2 * s))) := by
  unfold cofinalFlux rateDensity
  have h1 : Real.exp (-Real.pi * t) = Real.exp (-t * Real.pi) := by ring_nf
  have h2 : (∫ s in Ioi (0 : ℝ), causalRateKernel L N s *
      (Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * t))))) =
      ∫ s in Ioi (0 : ℝ), 2 * Real.pi * causalRateKernel L N s * Real.exp (5 * s / 2) *
        Real.exp (-t * (Real.pi * Real.exp (2 * s))) :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => by
      rw [show -Real.pi * (Real.exp (2 * s) * t) = -t * (Real.pi * Real.exp (2 * s)) by ring]
      ring
  rw [h1, h2]

/-- **Both signs at arbitrarily large rates.** -/
theorem rateDensity_sign_changes {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) (Λ : ℝ) :
    (∃ s, Λ < Real.pi * Real.exp (2 * s) ∧ 0 < rateDensity L N s) ∧
      ∃ s, Λ < Real.pi * Real.exp (2 * s) ∧ rateDensity L N s < 0 := by
  set s₀ := Real.log (|Λ| + 1) / 2
  have hbig : ∀ s, s₀ < s → Λ < Real.pi * Real.exp (2 * s) := fun s hs => by
    have h1 : Real.exp (2 * s₀) = |Λ| + 1 := by
      simp only [s₀]; rw [show 2 * (Real.log (|Λ| + 1) / 2) = Real.log (|Λ| + 1) by ring,
        Real.exp_log (by positivity)]
    have h2 : Real.exp (2 * s₀) < Real.exp (2 * s) := Real.exp_lt_exp.2 (by linarith)
    have h3 : 3 ≤ Real.pi := Real.pi_gt_three.le
    nlinarith [le_abs_self Λ, abs_nonneg Λ, Real.exp_pos (2 * s)]
  obtain ⟨⟨s₁, hs₁, hK₁⟩, ⟨s₂, hs₂, hK₂⟩⟩ := causalRateKernel_sign_changes hL hconj hN hN0 hNne s₀
  refine ⟨⟨s₁, hbig s₁ hs₁, ?_⟩, ⟨s₂, hbig s₂ hs₂, ?_⟩⟩
  · unfold rateDensity; have := Real.pi_pos; positivity
  · unfold rateDensity
    have := Real.pi_pos
    have h := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < 2 * Real.pi) hK₂
    exact mul_neg_of_neg_of_pos h (Real.exp_pos _)

theorem rateSymbol_pole_iff {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) (μ : ℂ) :
    meromorphicOrderAt (rateSymbol L e) μ < 0 ↔ μ ∈ (combKernel L e).support := by
  constructor
  · intro h
    by_contra hμ
    exact absurd (meromorphicOrderAt_rateSymbol_nonneg hL0 he hμ) (not_le.2 h)
  · intro hμ
    rw [meromorphicOrderAt_rateSymbol hL0 he hμ]
    exact WithTop.coe_lt_coe.2 (by omega)

/-- `r(−q²)` has the same order at `q` and `−q`. -/
theorem meromorphicOrderAt_rateSymbol_at_neg (L : List ℂ) (e : Polynomial ℂ) (μ : ℂ) :
    meromorphicOrderAt (rateSymbol L e) (-μ) = meromorphicOrderAt (rateSymbol L e) μ := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := rateSymbol L e) (g := fun q : ℂ => -q)
    (x := μ) analyticAt_id.neg (by simp)
  rw [← h]
  congr 1
  funext q
  exact rateSymbol_neg L e q

/-- The constant `c` is the constant part of `r`: `r(−σ²) → c` as `σ → ∞`. -/
theorem tendsto_rateSymbol_atTop {L : List ℂ} (hL : ThetaDivisionList L) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) :
    Tendsto (fun σ : ℝ => rateSymbol L e σ) atTop (𝓝 (combConst L e)) := by
  have hlim := (tendsto_laplace_atTop (combKernel L e)).const_add (combConst L e)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (listImBound L)] with σ hσ
  exact combConst_add_laplace_combKernel hL.ne_zero he fun β hβ =>
    (abs_im_le_listImBound hβ).trans_lt (by simpa using hσ)

/-- **Exponential type.**  Let `a` be the largest real part of a pole of `r(−q²)`.  Then `a ≥ 0`
and `limsup_{s→∞} log|K(s)|/s = a`; poles off the imaginary axis (off-line zeros) give `a > 0`. -/
theorem causalRateKernel_exponential_type {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧
      (∃ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 ∧ μ.re = a) ∧
      (∀ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 → μ.re ≤ a) ∧
      ((∃ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 ∧ μ.re ≠ 0) → 0 < a) ∧
      Filter.limsup (fun s : ℝ => Real.log |causalRateKernel L N s| / s) atTop = a := by
  set e := N.map (algebraMap ℝ ℂ)
  have hL0 := hL.ne_zero
  have hdeg : e.natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  have he0 : e.eval 0 = 0 := by
    simp only [e, Polynomial.eval_map, Polynomial.eval₂_at_zero, map_eq_zero]
    rwa [← Polynomial.coeff_zero_eq_eval_zero] at hN0
  set E := combKernel L e
  have hE : E ≠ 0 := combKernel_ne_zero hL0 hdeg he0 (Polynomial.map_ne_zero hNne)
  have hpole := rateSymbol_pole_iff hL0 hdeg
  obtain ⟨μ₁, hμ₁, hmax⟩ := Finset.exists_max_image E.support Complex.re
    (Finsupp.support_nonempty_iff.2 hE)
  have hsymm := neg_mem_support_combKernel hL0 hdeg hμ₁
  have ha0 : 0 ≤ μ₁.re := by
    have := hmax _ hsymm; simp only [Complex.neg_re] at this; linarith
  refine ⟨μ₁.re, ha0, ⟨μ₁, (hpole μ₁).2 hμ₁, rfl⟩, fun μ hμ => hmax μ ((hpole μ).1 hμ),
    fun ⟨μ, hμ, hre⟩ => ?_, ?_⟩
  · have h1 := hmax μ ((hpole μ).1 hμ)
    have h2 := hmax _ (neg_mem_support_combKernel hL0 hdeg ((hpole μ).1 hμ))
    simp only [Complex.neg_re] at h2
    rcases lt_or_gt_of_ne hre with h | h <;> linarith
  · have hnorm : ∀ s : ℝ, |causalRateKernel L N s| = ‖E.eval s‖ := fun s => by
      rw [combKernel_eval_eq_ofReal hL hconj hN, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [hnorm]
    exact QuasiPolynomial.limsup_log_norm_eval E ⟨μ₁, hμ₁, rfl⟩ hmax ha0

/-- **Critical-line zero division has exponential type zero.** -/
theorem causalRateKernel_exponential_type_critical {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) (hcrit : ∀ β ∈ L, β.im = 0) {N : Polynomial ℝ}
    (hN : N.natDegree ≤ L.length) (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) :
    Filter.limsup (fun s : ℝ => Real.log |causalRateKernel L N s| / s) atTop = 0 := by
  obtain ⟨a, ha0, ⟨μ, hμ, hre⟩, -, -, hlim⟩ :=
    causalRateKernel_exponential_type hL hconj hN hN0 hNne
  rw [hlim, ← hre]
  set e := N.map (algebraMap ℝ ℂ)
  have hdeg : e.natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  have hsupp : μ ∈ (combKernel L e).support := by
    by_contra h
    exact absurd (meromorphicOrderAt_rateSymbol_nonneg hL.ne_zero hdeg h) (not_le.2 hμ)
  obtain ⟨β, hβ, h | h⟩ := support_combKernel_subset L e hsupp
  · rw [h]; simp [Complex.mul_re, hcrit β hβ]
  · rw [h]; simp [Complex.mul_re, hcrit β hβ]

theorem re_mul_cexp_mul_I (c : ℂ) (ω s : ℝ) :
    (c * Complex.exp (ω * s * Complex.I)).re = c.re * Real.cos (ω * s) - c.im * Real.sin (ω * s) := by
  rw [show (ω : ℂ) * s * Complex.I = ((ω * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]
  ring

/-- **Leading oscillation.**  Let `a ≥ 0` be the largest real part of a pole of `r(−q²)` and
`m + 1` the largest pole order on the lines `Re q = ±a`.  Then
`K(s) = s^m e^{as} (Σ_top (A_μ cos(Im μ · s) + B_μ sin(Im μ · s)) + o(1))`, summed over the poles of
order `m + 1` on `Re q = a`, with `(A_μ, B_μ) ≠ 0`; the trigonometric sum does not tend to zero and
`limsup log|K(s)|/s = a`. -/
theorem causalRateKernel_top_asymptotics {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) :
    ∃ (a : ℝ) (m : ℕ) (top : Finset ℂ) (A B : ℂ → ℝ), 0 ≤ a ∧ top.Nonempty ∧
      (∀ μ, μ ∈ top ↔ meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ =
        ((-((m : ℤ) + 1) : ℤ) : WithTop ℤ) ∧ μ.re = a) ∧
      (∀ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 → μ.re ≤ a) ∧
      (∀ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 → |μ.re| = a →
        ((-((m : ℤ) + 1) : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ) ∧
      (∀ μ ∈ top, A μ ≠ 0 ∨ B μ ≠ 0) ∧
      Tendsto (fun s => causalRateKernel L N s / (s ^ m * Real.exp (a * s)) -
        ∑ μ ∈ top, (A μ * Real.cos (μ.im * s) + B μ * Real.sin (μ.im * s))) atTop (𝓝 0) ∧
      ¬ Tendsto (fun s => ∑ μ ∈ top, (A μ * Real.cos (μ.im * s) + B μ * Real.sin (μ.im * s)))
        atTop (𝓝 0) ∧
      Filter.limsup (fun s : ℝ => Real.log |causalRateKernel L N s| / s) atTop = a := by
  set e := N.map (algebraMap ℝ ℂ)
  have hL0 := hL.ne_zero
  have hdeg : e.natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  have he0 : e.eval 0 = 0 := by
    simp only [e, Polynomial.eval_map, Polynomial.eval₂_at_zero, map_eq_zero]
    rwa [← Polynomial.coeff_zero_eq_eval_zero] at hN0
  set E := combKernel L e
  have hE : E ≠ 0 := combKernel_ne_zero hL0 hdeg he0 (Polynomial.map_ne_zero hNne)
  have hc : QuasiPolynomial.conj E = E :=
    QuasiPolynomial.conj_eq_self_of_im_eval _ fun s _ => (combKernel_real hL hconj hN).2 s
  obtain ⟨a, m, top, hne, htop, hmax, hdegm, -, hlim, hnot⟩ :=
    QuasiPolynomial.exists_real_top_asymptotics E hE hc
  have hpole := rateSymbol_pole_iff hL0 hdeg
  have hord : ∀ μ ∈ E.support, meromorphicOrderAt (rateSymbol L e) μ =
      ((-(((E μ).natDegree : ℤ) + 1)) : ℤ) := fun μ hμ => meromorphicOrderAt_rateSymbol hL0 hdeg hμ
  obtain ⟨μ₀, hμ₀⟩ := hne
  have hμ₀' := (htop μ₀).1 hμ₀
  have ha0 : 0 ≤ a := by
    have := hmax _ (neg_mem_support_combKernel hL0 hdeg hμ₀'.1)
    simp only [Complex.neg_re] at this
    linarith [hμ₀'.2.1]
  have hK : ∀ s : ℝ, causalRateKernel L N s = (E.eval s).re := fun s => by
    rw [combKernel_eval_eq_ofReal hL hconj hN, Complex.ofReal_re]
  refine ⟨a, m, top, fun μ => ((E μ).leadingCoeff).re, fun μ => -((E μ).leadingCoeff).im, ha0,
    ⟨μ₀, hμ₀⟩, fun μ => ?_, fun μ hμ => hmax μ ((hpole μ).1 hμ), fun μ hμ hre => ?_,
    fun μ hμ => ?_, ?_, fun h => hnot (h.congr fun s => ?_), ?_⟩
  · rw [htop μ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rw [hord μ h1, h3], h2⟩
    · rintro ⟨h1, h2⟩
      have hs : μ ∈ E.support := (hpole μ).1 (by rw [h1]; exact WithTop.coe_lt_coe.2 (by omega))
      refine ⟨hs, h2, ?_⟩
      rw [hord μ hs] at h1
      have := WithTop.coe_injective h1
      omega
  · have hs := (hpole μ).1 hμ
    rcases (abs_eq ha0).1 hre with h | h
    · rw [hord μ hs]
      exact WithTop.coe_le_coe.2 (by have := hdegm μ hs h; omega)
    · have hs' := neg_mem_support_combKernel hL0 hdeg hs
      rw [← meromorphicOrderAt_rateSymbol_at_neg, hord _ hs']
      exact WithTop.coe_le_coe.2 (by have := hdegm (-μ) hs' (by simp [h]); omega)
  · have hc0 : (E μ).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.2 (Finsupp.mem_support_iff.1 ((htop μ).1 hμ).1)
    by_contra h
    simp only [not_or, not_not, neg_eq_zero] at h
    exact hc0 (Complex.ext h.1 h.2)
  · refine hlim.congr fun s => ?_
    rw [hK]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [re_mul_cexp_mul_I]
    ring
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [re_mul_cexp_mul_I]
    ring
  · have hnorm : ∀ s : ℝ, |causalRateKernel L N s| = ‖E.eval s‖ := fun s => by
      rw [combKernel_eval_eq_ofReal hL hconj hN, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [hnorm]
    exact QuasiPolynomial.limsup_log_norm_eval E ⟨μ₀, hμ₀'.1, hμ₀'.2.1⟩ hmax ha0

/-- **A single off-line quartet.**  If every divided zero is `α` or `ᾱ` with `Im α ≠ 0`, and
`m + 1` is the largest pole order of `r(−q²)`, then
`K(s) = s^m e^{|Im α| s} (A cos(Re α · s) + B sin(Re α · s) + o(1))` with `(A, B) ≠ 0`, and
`limsup log|K(s)|/s = |Im α| > 0`. -/
theorem causalRateKernel_single_quartet {α : ℂ} (hα : α.im ≠ 0) {L : List ℂ}
    (hL : ThetaDivisionList L) (hconj : (L.map (starRingEnd ℂ)).Perm L)
    (hsingle : ∀ β ∈ L, β = α ∨ β = starRingEnd ℂ α) {N : Polynomial ℝ}
    (hN : N.natDegree ≤ L.length) (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) :
    ∃ (m : ℕ) (A B : ℝ), (A ≠ 0 ∨ B ≠ 0) ∧
      (∃ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ =
        ((-((m : ℤ) + 1) : ℤ) : WithTop ℤ)) ∧
      (∀ μ, meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ < 0 →
        ((-((m : ℤ) + 1) : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) μ) ∧
      0 < |α.im| ∧
      Filter.limsup (fun s : ℝ => Real.log |causalRateKernel L N s| / s) atTop = |α.im| ∧
      Tendsto (fun s => causalRateKernel L N s / (s ^ m * Real.exp (|α.im| * s)) -
        (A * Real.cos (α.re * s) + B * Real.sin (α.re * s))) atTop (𝓝 0) := by
  set e := N.map (algebraMap ℝ ℂ)
  have hdeg : e.natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  obtain ⟨a, m, top, A, B, ha0, ⟨μ₀, hμ₀⟩, htop, -, hmult, -, hlim, hnot, hsup⟩ :=
    causalRateKernel_top_asymptotics hL hconj hN hN0 hNne
  have hpole := rateSymbol_pole_iff hL.ne_zero hdeg
  have hshape : ∀ μ, meromorphicOrderAt (rateSymbol L e) μ < 0 →
      |μ.re| = |α.im| ∧ (μ.im = α.re ∨ μ.im = -α.re) := fun μ hμ => by
    obtain ⟨β, hβ, h | h⟩ := support_combKernel_subset L e ((hpole μ).1 hμ) <;>
      rcases hsingle β hβ with rfl | rfl <;> subst h <;> simp [Complex.mul_re, Complex.mul_im]
  have htop_pole : ∀ μ ∈ top, meromorphicOrderAt (rateSymbol L e) μ < 0 := fun μ hμ => by
    rw [((htop μ).1 hμ).1]
    exact WithTop.coe_lt_coe.2 (by omega)
  have hμ₀' := (htop μ₀).1 hμ₀
  have ha : a = |α.im| := by
    rw [← (hshape μ₀ (htop_pole μ₀ hμ₀)).1, hμ₀'.2, abs_of_nonneg ha0]
  subst ha
  have hαre : α.re ≠ 0 := by
    obtain ⟨β, hβ, -⟩ := support_combKernel_subset L e ((hpole μ₀).1 (htop_pole μ₀ hμ₀))
    have := hL.1 β hβ
    rcases hsingle β hβ with rfl | rfl
    · exact this.ne'
    · simpa using this.ne'
  have hsum : ∀ s : ℝ, ∑ μ ∈ top, (A μ * Real.cos (μ.im * s) + B μ * Real.sin (μ.im * s)) =
      (∑ μ ∈ top, A μ) * Real.cos (α.re * s) +
        (∑ μ ∈ top, μ.im / α.re * B μ) * Real.sin (α.re * s) := fun s => by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rcases (hshape μ (htop_pole μ hμ)).2 with h | h
    · rw [h, div_self hαre]
      ring
    · rw [h, neg_mul, Real.cos_neg, Real.sin_neg, neg_div, div_self hαre]
      ring
  refine ⟨m, ∑ μ ∈ top, A μ, ∑ μ ∈ top, μ.im / α.re * B μ, ?_, ⟨μ₀, hμ₀'.1⟩,
    fun μ hμ => hmult μ hμ (hshape μ hμ).1, abs_pos.2 hα, hsup, hlim.congr fun s => by rw [hsum s]⟩
  by_contra h
  simp only [not_or, not_not] at h
  exact hnot ((tendsto_const_nhds (x := (0 : ℝ))).congr fun s => by rw [hsum s, h.1, h.2]; ring)

/-- **Positive type from an off-line pole.**  If `r(−q²)` has a pole at `±iα` with `Im α ≠ 0`,
then `limsup log|K(s)|/s > 0`. -/
theorem causalRateKernel_positive_type {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length)
    (hN0 : N.eval 0 = 0) (hNne : N ≠ 0) {α : ℂ} (hα : α.im ≠ 0)
    (hpole : meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) (Complex.I * α) < 0 ∨
      meromorphicOrderAt (rateSymbol L (N.map (algebraMap ℝ ℂ))) (-(Complex.I * α)) < 0) :
    0 < Filter.limsup (fun s : ℝ => Real.log |causalRateKernel L N s| / s) atTop := by
  obtain ⟨a, -, -, -, hpos, hlim⟩ := causalRateKernel_exponential_type hL hconj hN hN0 hNne
  rw [hlim]
  rcases hpole with h | h
  · exact hpos ⟨_, h, by simpa [Complex.mul_re] using hα⟩
  · exact hpos ⟨_, h, by simpa [Complex.mul_re] using hα⟩

/-- In the rate `λ = π e^{2s}` the growth `e^{as}` is the power `(λ/π)^{a/2}`. -/
theorem exp_mul_eq_rate_rpow (a s : ℝ) :
    Real.exp (a * s) = (Real.pi * Real.exp (2 * s) / Real.pi) ^ (a / 2) := by
  rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, ← Real.exp_mul]
  ring_nf

end

end RHTower
