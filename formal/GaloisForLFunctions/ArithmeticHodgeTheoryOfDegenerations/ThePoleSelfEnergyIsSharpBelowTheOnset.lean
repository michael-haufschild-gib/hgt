import GaloisForLFunctions.BiScaleUncertainty.HighZerosCarryABoundedCriticalDeficit
import GaloisForLFunctions.RHTower.SubNyquistHodgeExclusion
import GaloisForLFunctions.SquareRootThreshold.ClusterProductHorizon
import GaloisForLFunctions.SquareRootThreshold.VisibilityTradeoffAndExcludedDepthLaw
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.DyadicPoleNodalRHEquivalence
import GaloisForLFunctions.RHTower.NicolasPrimorialInequalityRH
import GaloisForLFunctions.RHTower.LittlewoodWindowIdentity
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleTracePositivity
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary

/-!
# The pole self-energy is sharp below the onset aperture

The literal Weil self-energy of the exponential pole at aperture `s` is
`D(s) = ccmWeilPoleDiagonal s`; its sharp normalized value is the archimedean genus
`κ₀ = 2 + γ − log 4π` (`poleSharpConstant`). Exactly (`poleDiagonalExplicit_div_exp_sub_sharp_eq`),

`e^{−s} D(s) − κ₀ = −2 e^{−s} Φ(2s) − 2 e^{−2s} (log 2π − S(e^{2s})) + r(s)/e^s`,

with `Φ` the Weil lag function `Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`. So the pole self-energy is sharp exactly
when `Φ(2s)` has sub-`e^{s}` size.

Window positivity at half-width `a` excludes every zero of depth `|β − ½| ≥ ¼` up to height
`exp(a/K)` (`exists_abs_re_sub_half_lt_quarter_of_hodgeIndex`: the Nyquist horizon above height
`102`, the cluster-product horizon below it). The high zeros carry a bounded lag weight, so

* **Lag bound** (`exists_abs_weilLagFunctionReal_le_of_zetaWindowPositive`):
  `|Φ(L)| ≤ C e^{L/4}` whenever `K(L + 2) ≤ a`;
* **Mertens lag** (`exists_abs_mertensLagPrimitive_le_of_zetaWindowPositive`):
  `|Σ_{n≤x} Λ(n)/n − log x + γ − (ψ(x) − x)/x| ≤ C x^{−1/4}` for `log x ≤ a/K − 2`;
* **Sharp pole self-energy** (`exists_abs_poleDiagonal_sharp_of_le_onsetAperture`):
  `|e^{−s} D(s) − κ₀| ≤ C e^{−s/2}` whenever `K(2s + 2) ≤ a*(ζ)`.

The scale is single-exponential: the admissible apertures `s` are a fixed fraction of `a*(ζ)`.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open _root_.RHTower GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.WindowVisibilityLaw
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

/-! ### 1. Zeros of depth `¼` are excluded up to a single-exponential height -/

/-- `B log a ≤ a` as soon as `a ≥ (2B)²` and `a ≥ 1`, from `log a ≤ 2√a`. -/
private theorem mul_log_le_self_of_sq_le {B a : ℝ} (hB : 0 ≤ B) (ha : (2 * B) ^ 2 ≤ a)
    (ha1 : 1 ≤ a) : B * Real.log a ≤ a := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hlog : Real.log a ≤ 2 * Real.sqrt a := by
    have h1 := Real.log_sqrt ha0.le
    have h2 := Real.log_le_sub_one_of_pos hs
    linarith
  have hB2 : 2 * B ≤ Real.sqrt a := by
    have := Real.sqrt_le_sqrt ha
    rwa [Real.sqrt_sq (by linarith)] at this
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  calc B * Real.log a ≤ B * (2 * Real.sqrt a) := mul_le_mul_of_nonneg_left hlog hB
    _ = (2 * B) * Real.sqrt a := by ring
    _ ≤ Real.sqrt a * Real.sqrt a := mul_le_mul_of_nonneg_right hB2 hs.le
    _ = a := hsq

/-- **Depth-`¼` exclusion up to height `exp(a/K)`.** There are `K > 0` and `a₁` such that the
level-`a` Hodge index, `a ≥ a₁`, forces `|Re ρ − ½| < ¼` for every zero with
`K log(|Im ρ| + 3) ≤ a`. Above height `102` this is the Nyquist horizon at depth `¼`; below it,
the cluster-product horizon. -/
theorem exists_abs_re_sub_half_lt_quarter_of_hodgeIndex :
    ∃ K a₁ : ℝ, 0 < K ∧ ∀ a : ℝ, a₁ ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ ∈ zetaZeroConfig.carrier, K * Real.log (|ρ.im| + 3) ≤ a →
        |ρ.re - 1 / 2| < 1 / 4 := by
  obtain ⟨A₁, hA₁, hnyq⟩ := zeta_hodge_index_nyquist_horizon
  obtain ⟨A₂, hA₂, hclus⟩ := _root_.SquareRootThreshold.zeta_hodge_index_cluster_product_horizon
  have hlogK : 0 < Real.log (10 ^ 6 / (1 / 4) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2000 * A₁ * Real.log (10 ^ 6 / (1 / 4)),
    Real.exp 6 + 4 + (2 * (10 ^ 5 * A₂ * 408)) ^ 2, by positivity,
    fun a ha hH ρ hρ hsize => ?_⟩
  by_contra hge
  push_neg at hge
  have h3 := three_lt_abs_im_of_mem_zetaZeroConfig hρ
  have he6 : Real.exp 6 ≤ a := by nlinarith [sq_nonneg (2 * (10 ^ 5 * A₂ * 408))]
  have h4 : (4 : ℝ) ≤ a := by nlinarith [Real.exp_pos 6, sq_nonneg (2 * (10 ^ 5 * A₂ * 408))]
  rcases le_or_gt 102 |ρ.im| with h102 | h102
  · refine hnyq (1 / 4) (by norm_num) ρ hρ hge h102 a ?_ hH
    calc 2000 * A₁ * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / (1 / 4))
        = 2000 * A₁ * Real.log (10 ^ 6 / (1 / 4)) * Real.log (|ρ.im| + 3) := by ring
      _ ≤ a := hsize
  · refine hclus (1 / 4) (by norm_num) ρ hρ hge (by linarith) a he6 (by norm_num; linarith) ?_ hH
    have hl : Real.log (|ρ.im| + 306) ≤ 408 := by
      have := Real.log_le_sub_one_of_pos (show 0 < |ρ.im| + 306 by positivity)
      linarith
    have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hB : 0 ≤ 10 ^ 5 * A₂ * 408 := by positivity
    have hmain := mul_log_le_self_of_sq_le hB
      (by nlinarith [Real.exp_pos 6] : (2 * (10 ^ 5 * A₂ * 408)) ^ 2 ≤ a) (by linarith)
    have hA : 0 ≤ 10 ^ 5 * A₂ := by positivity
    calc 10 ^ 5 * A₂ * Real.log (|ρ.im| + 306) * Real.log a
        ≤ 10 ^ 5 * A₂ * 408 * Real.log a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hA) hla
      _ ≤ a := hmain

/-! ### 2. The lag function below the onset -/

/-- `log(|γ| + 3) ≤ L + 2` when `|γ| < e^L`, `L ≥ 0`. -/
private theorem log_abs_add_three_le {γ L : ℝ} (hL : 0 ≤ L) (hγ : |γ| < Real.exp L) :
    Real.log (|γ| + 3) ≤ L + 2 := by
  have he1 : 1 ≤ Real.exp L := Real.one_le_exp hL
  have hle : |γ| + 3 ≤ 4 * Real.exp L := by linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  calc Real.log (|γ| + 3) ≤ Real.log (4 * Real.exp L) :=
        Real.log_le_log (by positivity) hle
    _ = Real.log 4 + L := by rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp]
    _ ≤ L + 2 := by linarith

/-- **The lag function has rate `¼` below the onset.** There are `K > 0`, `a₁`, `C ≥ 0` such
that window positivity at `a ≥ a₁` gives `|Φ(L)| ≤ C e^{L/4}` for every `L ≥ 0` with
`K(L + 2) ≤ a`. The zeros below `e^L` have depth `< ¼`; those above carry a bounded weight. -/
theorem exists_abs_weilLagFunctionReal_le_of_zetaWindowPositive :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ a : ℝ, a₁ ≤ a → ZetaWindowPositive a →
      ∀ L : ℝ, 0 ≤ L → K * (L + 2) ≤ a →
        |weilLagFunctionReal L| ≤ C * Real.exp (L / 4) := by
  obtain ⟨K, a₁, hK, hzero⟩ := exists_abs_re_sub_half_lt_quarter_of_hodgeIndex
  obtain ⟨C₀, hC₀, hlow⟩ :=
    exists_abs_weilLagFunctionReal_sub_lowZeroLagSum_le (α := 1 / 2) (by norm_num) (by norm_num)
  have hW0 := lagWeightTotal_nonneg
  refine ⟨K, a₁, C₀ + lagWeightTotal, hK, by positivity, fun a ha hW L hL hKL => ?_⟩
  have hH := hodgeIndexAtLevel_of_zetaWindowPositive hW
  have hcut : L / (2 * (1 / 2 : ℝ)) = L := by ring
  -- every zero copy below the cutoff `e^L` has real part at most `3/4`
  have hre : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| < Real.exp (L / (2 * (1 / 2 : ℝ))) →
      (q.1 : ℂ).re ≤ 3 / 4 := by
    intro q hq
    rw [hcut] at hq
    have hsz : K * Real.log (|(q.1 : ℂ).im| + 3) ≤ a :=
      (mul_le_mul_of_nonneg_left (log_abs_add_three_le hL hq) hK.le).trans hKL
    have h := hzero a ha hH _ (xiZeroCopy_mem_zetaZeroConfig_carrier q) hsz
    linarith [(abs_lt.mp h).2]
  have hterm : ∀ q : XiZeroCopy,
      ‖(if |(q.1 : ℂ).im| < Real.exp (L / (2 * (1 / 2 : ℝ))) then
          Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) else 0)‖ ≤
        Real.exp (L / 4) * ‖lagWeight q‖ := by
    intro q
    split_ifs with h
    · rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp]
      have hr : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by
        simp [Complex.mul_re]
      rw [hr]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by nlinarith [hre q h])) (norm_nonneg _)
    · rw [norm_zero]
      positivity
  have hs : Summable fun q : XiZeroCopy =>
      ‖(if |(q.1 : ℂ).im| < Real.exp (L / (2 * (1 / 2 : ℝ))) then
          Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) else 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (summable_norm_lagWeight.mul_left _)
  have hnorm : ‖lowZeroLagSum (1 / 2) L‖ ≤ Real.exp (L / 4) * lagWeightTotal := by
    unfold lowZeroLagSum
    calc _ ≤ _ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' q : XiZeroCopy, Real.exp (L / 4) * ‖lagWeight q‖ :=
          hs.tsum_le_tsum hterm (summable_norm_lagWeight.mul_left _)
      _ = Real.exp (L / 4) * lagWeightTotal := by rw [tsum_mul_left]; rfl
  have hd := hlow L hL
  have hre_le : |(lowZeroLagSum (1 / 2) L).re| ≤ ‖lowZeroLagSum (1 / 2) L‖ :=
    Complex.abs_re_le_norm _
  have he1 : 1 ≤ Real.exp (L / 4) := Real.one_le_exp (by linarith)
  have hsplit : |weilLagFunctionReal L| ≤
      |weilLagFunctionReal L - (lowZeroLagSum (1 / 2) L).re| +
        |(lowZeroLagSum (1 / 2) L).re| := by
    have := abs_add_le (weilLagFunctionReal L - (lowZeroLagSum (1 / 2) L).re)
      (lowZeroLagSum (1 / 2) L).re
    rwa [sub_add_cancel] at this
  nlinarith

/-! ### 3. The Mertens lag primitive and the exact pole identity -/

/-- The Mertens lag primitive is the reciprocal-Mangoldt error minus the normalized Chebyshev
error: `v(T) = E_M(T) + γ − (ψ(e^T) − e^T)/e^T`. -/
theorem mertensLagPrimitive_eq_reciprocalMangoldtError {T : ℝ} (hT : 0 ≤ T) :
    mertensLagPrimitive T = reciprocalMangoldtError T + Real.eulerMascheroniConstant -
      (Chebyshev.psi (Real.exp T) - Real.exp T) / Real.exp T := by
  rw [mertensLagPrimitive_eq hT, reciprocalMangoldtError, reciprocalMangoldtCumulative]
  have hsum : (∑ k ∈ Finset.Icc 0 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro k hk hk2
    have hk1 : k ≤ 1 := by
      simp only [Finset.mem_Icc] at hk hk2
      omega
    interval_cases k <;> simp
  rw [hsum]
  have he := (Real.exp_pos T).ne'
  field_simp
  ring

/-- **Exact pole identity.** `e^{−s} D(s) − κ₀ = −2e^{−s}Φ(2s) − 2e^{−2s}(log 2π − S(e^{2s}))
+ r(s)/e^s`: the reciprocal-Mangoldt and Chebyshev errors of the pole diagonal combine into the
lag function. -/
theorem poleDiagonalExplicit_div_exp_sub_sharp_eq {s : ℝ} (hs : 0 < s) :
    poleDiagonalExplicit s / Real.exp s - poleSharpConstant =
      -(2 * Real.exp (-s) * weilLagFunctionReal (2 * s)) -
        2 * Real.exp (-(2 * s)) *
          (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp (2 * s))) +
        poleDiagonalRemainder s / Real.exp s := by
  have h2s : 0 < 2 * s := by linarith
  have hv := mertensLagPrimitive_eq_reciprocalMangoldtError h2s.le
  have hl := exp_mul_mertensLagPrimitive_eq h2s
  rw [show 2 * s / 2 = s by ring] at hl
  have hE : Real.exp (2 * s) = Real.exp s * Real.exp s := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos s
  have hMγ : reciprocalMangoldtError (2 * s) + Real.eulerMascheroniConstant =
      mertensLagPrimitive (2 * s) +
        (Chebyshev.psi (Real.exp (2 * s)) - Real.exp (2 * s)) / Real.exp (2 * s) := by
    rw [hv]; ring
  have hvv : mertensLagPrimitive (2 * s) =
      (Real.exp s * weilLagFunctionReal (2 * s) + Real.log (2 * Real.pi) -
        trivialZeroSeriesReal (Real.exp (2 * s))) / Real.exp (2 * s) := by
    rw [eq_div_iff (Real.exp_pos _).ne']
    linear_combination hl
  rw [poleDiagonalExplicit_eq_sharp s, hMγ, hvv, Real.exp_neg, Real.exp_neg, hE]
  field_simp
  ring

/-- The exact pole identity as a bound by the lag function. -/
theorem abs_poleDiagonalExplicit_div_exp_sub_sharp_le_lag {s : ℝ} (hs : 1 ≤ s) :
    |poleDiagonalExplicit s / Real.exp s - poleSharpConstant| ≤
      2 * Real.exp (-s) * |weilLagFunctionReal (2 * s)| +
        (10 * s + 24) * Real.exp (-(2 * s)) := by
  rw [poleDiagonalExplicit_div_exp_sub_sharp_eq (by linarith)]
  have hS := abs_trivialZeroSeriesReal_sub_log_two_pi_le
    (x := Real.exp (2 * s)) (Real.one_le_exp (by linarith))
  have hr := abs_poleDiagonalRemainder_le hs
  have hes := Real.exp_pos s
  have h2 : Real.exp (-(2 * s)) * Real.exp s = Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  have hrem : |poleDiagonalRemainder s / Real.exp s| ≤ (10 * s + 20) * Real.exp (-(2 * s)) := by
    rw [abs_div, abs_of_pos hes, div_le_iff₀ hes]
    calc |poleDiagonalRemainder s| ≤ (10 * s + 20) * Real.exp (-s) := hr
      _ = (10 * s + 20) * Real.exp (-(2 * s)) * Real.exp s := by rw [mul_assoc, h2]
  have h1 : |2 * Real.exp (-s) * weilLagFunctionReal (2 * s)| =
      2 * Real.exp (-s) * |weilLagFunctionReal (2 * s)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-s))]
  have hb : |2 * Real.exp (-(2 * s)) *
      (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp (2 * s)))| ≤
        4 * Real.exp (-(2 * s)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-(2 * s))), abs_sub_comm]
    nlinarith [Real.exp_pos (-(2 * s))]
  obtain ⟨a1, a2⟩ := abs_le.mp h1.le
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨c1, c2⟩ := abs_le.mp hrem
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### 4. Sharpness of the pole self-energy and of the Mertens lag below the onset -/

/-- `(10s + 24) e^{−2s} ≤ 34 e^{−s/2}` for `s ≥ 0`. -/
private theorem linear_mul_exp_neg_two_le {s : ℝ} (hs : 0 ≤ s) :
    (10 * s + 24) * Real.exp (-(2 * s)) ≤ 34 * Real.exp (-(s / 2)) := by
  have hsplit : Real.exp (-(2 * s)) = Real.exp (-(s / 2)) * Real.exp (-(3 * s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hgrow : 10 * s + 24 ≤ 34 * Real.exp (3 * s / 2) := by
    have := Real.add_one_le_exp (3 * s / 2)
    linarith
  have hinv : Real.exp (3 * s / 2) * Real.exp (-(3 * s / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hm := Real.exp_pos (-(s / 2))
  have hn := Real.exp_pos (-(3 * s / 2))
  rw [hsplit]
  calc (10 * s + 24) * (Real.exp (-(s / 2)) * Real.exp (-(3 * s / 2)))
      ≤ 34 * Real.exp (3 * s / 2) * (Real.exp (-(s / 2)) * Real.exp (-(3 * s / 2))) :=
        mul_le_mul_of_nonneg_right hgrow (by positivity)
    _ = 34 * Real.exp (-(s / 2)) * (Real.exp (3 * s / 2) * Real.exp (-(3 * s / 2))) := by ring
    _ = 34 * Real.exp (-(s / 2)) := by rw [hinv, mul_one]

/-- **The pole self-energy is sharp below the onset.** There are `K > 0`, `a₁`, `C ≥ 0` such that
window positivity at `a ≥ a₁` gives `|e^{−s} D(s) − κ₀| ≤ C e^{−s/2}` for every `s ≥ 1` with
`K(2s + 2) ≤ a`. -/
theorem exists_abs_poleDiagonal_sharp_of_zetaWindowPositive :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ a : ℝ, a₁ ≤ a → ZetaWindowPositive a →
      ∀ s : ℝ, 1 ≤ s → K * (2 * s + 2) ≤ a →
        |poleDiagonalExplicit s / Real.exp s - poleSharpConstant| ≤
          C * Real.exp (-(s / 2)) := by
  obtain ⟨K, a₁, C, hK, hC, hlag⟩ := exists_abs_weilLagFunctionReal_le_of_zetaWindowPositive
  refine ⟨K, a₁, 2 * C + 34, hK, by positivity, fun a ha hW s hs hKs => ?_⟩
  have hΦ := hlag a ha hW (2 * s) (by linarith) hKs
  have hmain := abs_poleDiagonalExplicit_div_exp_sub_sharp_le_lag hs
  have htail := linear_mul_exp_neg_two_le (s := s) (by linarith)
  have hprod : Real.exp (-s) * Real.exp (2 * s / 4) = Real.exp (-(s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hlagpart : 2 * Real.exp (-s) * |weilLagFunctionReal (2 * s)| ≤
      2 * C * Real.exp (-(s / 2)) := by
    calc 2 * Real.exp (-s) * |weilLagFunctionReal (2 * s)|
        ≤ 2 * Real.exp (-s) * (C * Real.exp (2 * s / 4)) :=
          mul_le_mul_of_nonneg_left hΦ (by positivity)
      _ = 2 * C * (Real.exp (-s) * Real.exp (2 * s / 4)) := by ring
      _ = 2 * C * Real.exp (-(s / 2)) := by rw [hprod]
  linarith

/-- **The Mertens lag decays at rate `x^{−1/4}` below the onset.** Under the constants of the lag
bound, `|v(L)| ≤ (C + 2) e^{−L/4}` for every `L > 0` with `K(L + 2) ≤ a`, where
`v(L) = Σ_{n ≤ e^L} Λ(n)/n − L + γ − (ψ(e^L) − e^L)/e^L`. -/
theorem exists_abs_mertensLagPrimitive_le_of_zetaWindowPositive :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ a : ℝ, a₁ ≤ a → ZetaWindowPositive a →
      ∀ L : ℝ, 0 < L → K * (L + 2) ≤ a →
        |mertensLagPrimitive L| ≤ C * Real.exp (-(L / 4)) := by
  obtain ⟨K, a₁, C, hK, hC, hlag⟩ := exists_abs_weilLagFunctionReal_le_of_zetaWindowPositive
  refine ⟨K, a₁, C + 2, hK, by positivity, fun a ha hW L hL hKL => ?_⟩
  have hΦ := hlag a ha hW L hL.le hKL
  have hid := exp_mul_mertensLagPrimitive_eq hL
  have hS := abs_trivialZeroSeriesReal_sub_log_two_pi_le
    (x := Real.exp L) (Real.one_le_exp hL.le)
  have hE := Real.exp_pos L
  -- `v(L) = e^{−L/2} Φ(L) + e^{−L}(log 2π − S(e^L))`
  have hv : mertensLagPrimitive L =
      Real.exp (-(L / 2)) * weilLagFunctionReal L +
        Real.exp (-L) * (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) := by
    have h1 : Real.exp (-(L / 2)) * Real.exp L = Real.exp (L / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
    apply mul_left_cancel₀ hE.ne'
    linear_combination hid - weilLagFunctionReal L * h1 -
      (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * h2
  have hprod : Real.exp (-(L / 2)) * Real.exp (L / 4) = Real.exp (-(L / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have hdecay : Real.exp (-L) ≤ Real.exp (-(L / 4)) := Real.exp_le_exp.mpr (by linarith)
  have hp1 : |Real.exp (-(L / 2)) * weilLagFunctionReal L| ≤ C * Real.exp (-(L / 4)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(L / 2)) * |weilLagFunctionReal L|
        ≤ Real.exp (-(L / 2)) * (C * Real.exp (L / 4)) :=
          mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le
      _ = C * (Real.exp (-(L / 2)) * Real.exp (L / 4)) := by ring
      _ = C * Real.exp (-(L / 4)) := by rw [hprod]
  have hp2 : |Real.exp (-L) * (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))| ≤
      2 * Real.exp (-(L / 4)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
    nlinarith [Real.exp_pos (-L)]
  rw [hv]
  exact (abs_add_le _ _).trans (by linarith)

/-- **Onset form.** With the constants of `exists_abs_poleDiagonal_sharp_of_zetaWindowPositive`,
the literal CCM pole self-energy satisfies `|e^{−s} D(s) − κ₀| ≤ C e^{−s/2}` at every aperture
`s ≥ 1` with `max(a₁, K(2s + 2)) ≤ a*(ζ) = onsetAperture ζ`. Under RH this holds at every `s ≥ 1`. -/
theorem exists_abs_poleDiagonal_sharp_of_le_onsetAperture :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ s : SuzukiPositiveAperture, 1 ≤ s.1 →
      ((max a₁ (K * (2 * s.1 + 2)) : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
        |ccmWeilPoleDiagonal s / Real.exp s.1 - poleSharpConstant| ≤
          C * Real.exp (-(s.1 / 2)) := by
  obtain ⟨K, a₁, C, hK, hC, h⟩ := exists_abs_poleDiagonal_sharp_of_zetaWindowPositive
  refine ⟨K, a₁, C, hK, hC, fun s hs hle => ?_⟩
  set a : ℝ := max a₁ (K * (2 * s.1 + 2))
  have ha0 : 0 ≤ a := (by positivity : (0 : ℝ) ≤ K * (2 * s.1 + 2)).trans (le_max_right _ _)
  have hW : ZetaWindowPositive a :=
    (windowPositiveAt_zeta_iff a).mp
      ((windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig ha0).mpr hle)
  rw [ccmWeilPoleDiagonal_eq_poleDiagonalExplicit]
  exact h a (le_max_left _ _) hW s.1 hs (le_max_right _ _)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
