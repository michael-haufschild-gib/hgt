import GaloisForLFunctions.BiScaleUncertainty.FactorialSourceWeilContrastAndDivisorResponseProducer
import GaloisForLFunctions.RHTower.CHMDChebyshevDiscrepancyDerivativeTransportLaw
import GaloisForLFunctions.RHTower.CHMDOddProfileArchAbsorptionAndPrimeChainBridge
import GaloisForLFunctions.RHTower.CHMDOddMonotoneProfilePrimeSignLaw

/-!
# Pillar XXXIX: CHMD Derivative-Transport Split, Reflected-Prime Collar Dominance & Unimodal Low-Prime Window Producer

This module develops **Pillar XXXIX** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), providing unconditional producer bounds for three key
CHMD steps:

1. **Tool 1 — CHMD Chebyshev-Discrepancy Pointwise Channel & Derivative-Transport Split (§1):**
   - For the classical $\sqrt{\cdot}$-weighted Chebyshev discrepancy
     $$\Delta(s) = \operatorname{chebyshevStep}(s) - 2 e^{s/2}$$
     (`RHTower.CHMDChebyshevTransport.chebyshevDiscrepancy s`), we establish the unconditional
     pointwise channel (`chebyshevDiscrepancy_bounds_of_nonneg`,
     `abs_chebyshevDiscrepancy_le_of_nonneg`):
     $$-2 e^{s/2} \;\le\; \Delta(s) \;\le\; (2\log 4 + 14) e^{s/2},
       \qquad |\Delta(s)| \;\le\; (2\log 4 + 16) e^{s/2} \quad (s \ge 0).$$
   - We prove half-line integrability of `kernelDeriv y s * chebyshevDiscrepancy s`
     (`integrableOn_kernelDeriv_mul_chebyshevDiscrepancy`) and the exact finite-window + tail
     decomposition (`integral_Ioi_kernelDeriv_mul_chebyshevDiscrepancy_split`) at any cutoff
     $L \ge 0$:
     $$\int_{s \in Ioi\,0} \partial_s K_y(s)\,\Delta(s)\,ds
       = \left(\int_{s \in Ioc\,0\,L} \partial_s K_y(s)\,\Delta(s)\,ds\right)
         + \left(\int_{s \in Ioi\,L} \partial_s K_y(s)\,\Delta(s)\,ds\right).$$

2. **Tool 3 — Reflected-Prime Collar Dominance & Positive Shift-Jump Completion for $f = m_a w$ (§2):**
   - For any secondary odd-profile test $f(x) = m_a(x) w(x)$ ($a > 0$, $w$ even), we prove that both
     the $\Theta$-Doob prime crossing energy `primeCrossing (oddPolarWeight a w) d` and the
     $m_a$-Doob prime collar difference
     `vonMangoldtAtom d * ∫_{x ∈ (0, log d)} oddProfileCollarDiffSq a w (log d) x` are non-negative
     and **individually bounded above** by the ground-state collar mixed integral
     (`oddProfileCollar_and_primeCrossing_le_mixed`):
     $$\operatorname{vonMangoldtAtom}\,d \int_0^{\log d} \operatorname{oddProfileCollarDiffSq}(a, w, \log d, x)\,dx
       \;\le\; \operatorname{vonMangoldtAtom}\,d \int_0^{\log d} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx,$$
     $$\operatorname{primeCrossing}(\operatorname{oddPolarWeight}\,a\,w,\,d)
       \;\le\; \operatorname{vonMangoldtAtom}\,d \int_0^{\log d} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx.$$
   - Adding the ground-state collar mixed integral to the full-line $m_a$-Doob shift jump turns the
     signed difference into the sum of two strictly non-negative energies
     (`oddProfileShiftJump_add_collarMixed_eq_two_Ioi_add_primeCrossing`,
     `oddProfileShiftJump_add_collarMixed_nonneg`):
     $$\operatorname{vonMangoldtAtom}\,d \int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, \log d, x)\,dx
       + \operatorname{vonMangoldtAtom}\,d \int_0^{\log d} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx$$
     $$= 2\,\operatorname{vonMangoldtAtom}\,d \int_0^\infty \operatorname{oddProfileShiftJump}(a, w, \log d, x)\,dx
       + \operatorname{primeCrossing}(\operatorname{oddPolarWeight}\,a\,w,\,d) \;\ge\; 0.$$

3. **Tool 4 — Unimodal Low-Prime Window Producer Lower Bound (§3):**
   - For every one-signed odd test $v \in C^2_c(\mathbb{R})$ supported in $(-L/2, L/2)$ whose Doob
     profile $g = \Theta|v|$ is antitone on $[c, L/2]$, we bound the low-prime finite window in
     `levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn` from below by dropping the
     non-negative opposite-side bonuses `0 ≤ oppositeSideBonus g n`
     (`levy_abs_add_bonus_sub_sum_sameSideCross_le_sourceEnergy_of_antitoneOn`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

open _root_.RHTower _root_.RHTower.CHMDChebyshevTransport _root_.RHTower.CHMDPolar
open _root_.RHTower.CHMDDoobGraph _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy
open _root_.RHTower.CHMDPrimeCuts _root_.RHTower.CHMDPrimeChainSource

/-! ## §1. CHMD Chebyshev-Discrepancy Pointwise Channel & Derivative-Transport Split -/

/-- **Unconditional Pointwise Channel for `chebyshevDiscrepancy` on `[0, ∞)`:**
For every $s \ge 0$,
$$-2 e^{s/2} \;\le\; \operatorname{chebyshevDiscrepancy}(s)
  \;\le\; (2\log 4 + 14) e^{s/2}.$$ -/
theorem chebyshevDiscrepancy_bounds_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    -2 * Real.exp (s / 2) ≤ chebyshevDiscrepancy s ∧
      chebyshevDiscrepancy s ≤ (2 * Real.log 4 + 14) * Real.exp (s / 2) := by
  have hlo := chebyshevStep_nonneg s
  have hhi := chebyshevStep_le hs
  unfold chebyshevDiscrepancy
  constructor <;> linarith

/-- **Unconditional Pointwise Absolute-Value Bound for `chebyshevDiscrepancy` on `[0, ∞)`:**
For every $s \ge 0$,
$$|\operatorname{chebyshevDiscrepancy}(s)|
  \;\le\; (2\log 4 + 16) e^{s/2}.$$ -/
theorem abs_chebyshevDiscrepancy_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    |chebyshevDiscrepancy s| ≤ (2 * Real.log 4 + 16) * Real.exp (s / 2) := by
  obtain ⟨hlo, hhi⟩ := chebyshevDiscrepancy_bounds_of_nonneg hs
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hexp : 0 < Real.exp (s / 2) := Real.exp_pos _
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-- **Pointwise Envelope Bound for the CHMD Derivative-Transport Integrand:**
For every $y : \mathbb{R}$ and $s \ge 0$,
$$|\operatorname{kernelDeriv}\,y\,s \cdot \operatorname{chebyshevDiscrepancy}(s)|
  \;\le\; (2\log 4 + 16)\,|\operatorname{kernelDeriv}\,y\,s|\,e^{s/2}.$$ -/
theorem abs_kernelDeriv_mul_chebyshevDiscrepancy_le_of_nonneg (y : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |kernelDeriv y s * chebyshevDiscrepancy s| ≤
      (2 * Real.log 4 + 16) * |kernelDeriv y s| * Real.exp (s / 2) := by
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left (abs_chebyshevDiscrepancy_le_of_nonneg hs)
    (abs_nonneg (kernelDeriv y s))
  linarith

/-- **Half-Line Integrability of the CHMD Derivative-Transport Integrand:**
For every $y : \mathbb{R}$, `s ↦ kernelDeriv y s * chebyshevDiscrepancy s` is integrable on
`Ioi 0`. -/
theorem integrableOn_kernelDeriv_mul_chebyshevDiscrepancy (y : ℝ) :
    IntegrableOn (fun s => kernelDeriv y s * chebyshevDiscrepancy s) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_kernelDeriv_mul_chebyshevStep y).sub
    (integrableOn_kernelDeriv_mul_two_exp_half y)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  dsimp only
  unfold chebyshevDiscrepancy
  ring

/-- **Exact Finite-Window + Exponential-Tail Split of the CHMD Derivative Pairing:**
For every $y : \mathbb{R}$ and every cutoff $L \ge 0$,
$$\int_{s \in Ioi\,0} \operatorname{kernelDeriv}\,y\,s \cdot \operatorname{chebyshevDiscrepancy}(s)\,ds
  = \left(\int_{s \in Ioc\,0\,L} \operatorname{kernelDeriv}\,y\,s \cdot \operatorname{chebyshevDiscrepancy}(s)\,ds\right)
    + \left(\int_{s \in Ioi\,L} \operatorname{kernelDeriv}\,y\,s \cdot \operatorname{chebyshevDiscrepancy}(s)\,ds\right).$$ -/
theorem integral_Ioi_kernelDeriv_mul_chebyshevDiscrepancy_split (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s) =
      (∫ s in Ioc (0 : ℝ) L, kernelDeriv y s * chebyshevDiscrepancy s) +
        ∫ s in Ioi L, kernelDeriv y s * chebyshevDiscrepancy s := by
  have hint := integrableOn_kernelDeriv_mul_chebyshevDiscrepancy y
  have hunion : Ioc (0 : ℝ) L ∪ Ioi L = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hL
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := Ioc_disjoint_Ioi le_rfl
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hL))]

/-! ## §2. Reflected-Prime Collar Dominance & Positive Shift-Jump Completion for $f = m_a w$ -/

/-- **Pointwise Non-Negativity of `phiDoobCollarSumSq`:** -/
theorem phiDoobCollarSumSq_nonneg (v : ℝ → ℝ) (t x : ℝ) :
    0 ≤ phiDoobCollarSumSq v t x := by
  unfold phiDoobCollarSumSq
  exact mul_nonneg
    (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos (t - x)).le)
    (sq_nonneg _)

/-- **Non-Negativity of `primeCrossing (oddPolarWeight a w) d`:**
For every continuous compactly supported even profile $w : \mathbb{R} \to \mathbb{R}$ and every
$d : \mathbb{N}$,
$$0 \;\le\; \operatorname{primeCrossing}(\operatorname{oddPolarWeight}\,a\,w,\,d).$$ -/
theorem primeCrossing_oddPolarWeight_nonneg (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    0 ≤ primeCrossing (oddPolarWeight a w) d := by
  rw [primeCrossing_oddPolarWeight_eq_collarSumSq a hw hwc heven d]
  exact mul_nonneg (vonMangoldtAtom_nonneg d)
    (setIntegral_nonneg measurableSet_Ioo fun x _ => phiDoobCollarSumSq_nonneg _ _ x)

/-- **Non-Negativity of the $m_a$-Doob Collar Difference Integral:**
For every $a > 0$, $w : \mathbb{R} \to \mathbb{R}$, and $t : \mathbb{R}$,
$$0 \;\le\; \int_{x \in Ioo\,0\,t} \operatorname{oddProfileCollarDiffSq}(a, w, t, x)\,dx.$$ -/
theorem integral_oddProfileCollarDiffSq_nonneg {a : ℝ} (ha : 0 < a)
    (w : ℝ → ℝ) (t : ℝ) :
    0 ≤ ∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x :=
  setIntegral_nonneg measurableSet_Ioo fun x hx => oddProfileCollarDiffSq_nonneg ha hx w

/-- **Individual Collar Dominance Bound (`oddProfileCollarDiffSq` and `primeCrossing` vs. `oddProfileCollarMixed`):**
For every $a > 0$, every continuous compactly supported even $w : \mathbb{R} \to \mathbb{R}$, and
every $d : \mathbb{N}$, both the $m_a$-Doob prime collar difference integral and the $\Theta$-Doob
prime crossing energy are individually bounded above by the ground-state collar mixed integral:
$$\operatorname{vonMangoldtAtom}\,d \int_{x \in Ioo\,0\,(\log d)} \operatorname{oddProfileCollarDiffSq}(a, w, \log d, x)\,dx
  \;\le\; \operatorname{vonMangoldtAtom}\,d \int_{x \in Ioo\,0\,(\log d)} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx$$
and
$$\operatorname{primeCrossing}(\operatorname{oddPolarWeight}\,a\,w,\,d)
  \;\le\; \operatorname{vonMangoldtAtom}\,d \int_{x \in Ioo\,0\,(\log d)} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx.$$ -/
theorem oddProfileCollar_and_primeCrossing_le_mixed {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarDiffSq a w (Real.log d) x) ≤
      vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarMixed a w (Real.log d) x) ∧
    primeCrossing (oddPolarWeight a w) d ≤
      vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarMixed a w (Real.log d) x) := by
  have heq := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a hw hwc heven d
  have hcross := primeCrossing_oddPolarWeight_nonneg a hw hwc heven d
  have hcol : 0 ≤ vonMangoldtAtom d *
      ∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x :=
    mul_nonneg (vonMangoldtAtom_nonneg d)
      (integral_oddProfileCollarDiffSq_nonneg ha w (Real.log d))
  exact ⟨by linarith, by linarith⟩

/-- **Exact Positive Shift-Jump Completion via Ground-State Collar Mixed Duality:**
For every continuous compactly supported even $w : \mathbb{R} \to \mathbb{R}$ and every $d : \mathbb{N}$,
adding the ground-state collar mixed integral to the full-line $m_a$-Doob shift jump eliminates the
negative origin-crossing collar and leaves twice the direct half-line shift jump plus the
$\Theta$-Doob prime crossing energy:
$$\operatorname{vonMangoldtAtom}\,d \int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, \log d, x)\,dx
  + \operatorname{vonMangoldtAtom}\,d \int_{x \in Ioo\,0\,(\log d)} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx$$
$$= 2\,\operatorname{vonMangoldtAtom}\,d \int_{x \in Ioi\,0} \operatorname{oddProfileShiftJump}(a, w, \log d, x)\,dx
  + \operatorname{primeCrossing}(\operatorname{oddPolarWeight}\,a\,w,\,d).$$ -/
theorem oddProfileShiftJump_add_collarMixed_eq_two_Ioi_add_primeCrossing (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    vonMangoldtAtom d * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
        vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfileCollarMixed a w (Real.log d) x) =
      2 * vonMangoldtAtom d * (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x) +
        primeCrossing (oddPolarWeight a w) d := by
  have hfold := integral_oddProfileShiftJump_eq_halfLine_of_even a hw hwc heven
    (Real.log_natCast_nonneg d)
  have hcol : (∫ x in Ioo (0 : ℝ) (Real.log d),
      oddProfile a x * oddProfile a (Real.log d - x) * (w x - w (Real.log d - x)) ^ 2) =
      ∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x := rfl
  rw [hcol] at hfold
  have hmix := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a hw hwc heven d
  linear_combination vonMangoldtAtom d * hfold + hmix

/-- **Strict Non-Negativity of the Collar-Completed $m_a$-Doob Shift Jump:**
For every $a > 0$, every continuous compactly supported even $w : \mathbb{R} \to \mathbb{R}$, and
every $d : \mathbb{N}$,
$$0 \;\le\; \operatorname{vonMangoldtAtom}\,d \int_{\mathbb{R}} \operatorname{oddProfileShiftJump}(a, w, \log d, x)\,dx
  + \operatorname{vonMangoldtAtom}\,d \int_{x \in Ioo\,0\,(\log d)} \operatorname{oddProfileCollarMixed}(a, w, \log d, x)\,dx.$$ -/
theorem oddProfileShiftJump_add_collarMixed_nonneg {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) (d : ℕ) :
    0 ≤ vonMangoldtAtom d * (∫ x : ℝ, oddProfileShiftJump a w (Real.log d) x) +
        vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
          oddProfileCollarMixed a w (Real.log d) x) := by
  rw [oddProfileShiftJump_add_collarMixed_eq_two_Ioi_add_primeCrossing a hw hwc heven d]
  have hdir : 0 ≤ ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      oddProfileShiftJump_nonneg_of_pos ha (mem_Ioi.mp hx) (Real.log_natCast_nonneg d) w
  have hcross := primeCrossing_oddPolarWeight_nonneg a hw hwc heven d
  have h1 : 0 ≤ 2 * vonMangoldtAtom d *
      ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x :=
    mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg d)) hdir
  linarith

/-! ## §3. Unimodal Low-Prime Window Producer Bound -/

/-- **Pointwise Lower Bound on `oppositeSideBonus g n - sameSideCross g n`:**
For any non-negative profile $g \ge 0$ and any $n : \mathbb{N}$,
$$-\operatorname{sameSideCross}(g, n)
  \;\le\; \operatorname{oppositeSideBonus}(g, n) - \operatorname{sameSideCross}(g, n).$$ -/
theorem neg_sameSideCross_le_oppositeSideBonus_sub {g : ℝ → ℝ}
    (hg : ∀ u, 0 ≤ g u) (n : ℕ) :
    -sameSideCross g n ≤ oppositeSideBonus g n - sameSideCross g n := by
  linarith [oppositeSideBonus_nonneg hg n]

/-- **Finite-Window Lower Bound on the Low-Prime Sum:**
For any non-negative profile $g \ge 0$ and any cutoff $N : \mathbb{N}$,
$$-\sum_{n \in \operatorname{range} N} \operatorname{sameSideCross}(g, n)
  \;\le\; \sum_{n \in \operatorname{range} N} (\operatorname{oppositeSideBonus}(g, n) - \operatorname{sameSideCross}(g, n)).$$ -/
theorem neg_sum_sameSideCross_le_sum_oppositeSideBonus_sub {g : ℝ → ℝ}
    (hg : ∀ u, 0 ≤ g u) (N : ℕ) :
    -(∑ n ∈ Finset.range N, sameSideCross g n) ≤
      ∑ n ∈ Finset.range N, (oppositeSideBonus g n - sameSideCross g n) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun n _ => neg_sameSideCross_le_oppositeSideBonus_sub hg n

/-- **Unimodal Prime-Sign Producer Lower Bound on `sourceEnergy`:**
For a one-signed odd test $v \in C^2_c(\mathbb{R})$ of support $(-L/2, L/2)$ whose Doob profile
$g = \Theta|v|$ is non-increasing on $[c, L/2]$, and any $N$ with
$\max(L/3, (L/2 + c)/2) \le \log N$,
$$\operatorname{weilLevyForm}(g) + 4\,\operatorname{crossSignBonus}(g)
  - \sum_{n \in \operatorname{range} N} \operatorname{sameSideCross}(g, n)
  \;\le\; \operatorname{sourceEnergy}(\operatorname{compactLift}\,v\,hv\,hvc).$$ -/
theorem levy_abs_add_bonus_sub_sum_sameSideCross_le_sourceEnergy_of_antitoneOn (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L c : ℝ} (hL : 0 < L)
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hmono : AntitoneOn (phiDoobTest fun y => |v y|) (Icc c (L / 2))) {N : ℕ}
    (hN : L / 3 ≤ Real.log N) (hNc : (L / 2 + c) / 2 ≤ Real.log N) :
    weilLevyForm (phiDoobTest fun y => |v y|) +
        4 * crossSignBonus (phiDoobTest fun y => |v y|) -
        ∑ n ∈ Finset.range N, sameSideCross (phiDoobTest fun y => |v y|) n ≤
      sourceEnergy (compactLift v hv hvc) := by
  have hg0 : ∀ s, 0 ≤ phiDoobTest (fun y => |v y|) s :=
    fun s => mul_nonneg (riemannKernelReal_pos s).le (abs_nonneg _)
  have h1 := levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn v hv hvc hodd hpos
    hL hsupp hmono hN hNc
  have h2 := neg_sum_sameSideCross_le_sum_oppositeSideBonus_sub hg0 N
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
