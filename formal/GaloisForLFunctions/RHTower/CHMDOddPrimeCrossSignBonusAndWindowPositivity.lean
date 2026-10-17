import GaloisForLFunctions.RHTower.CHMDOddCrossSignBonus

/-!
# The exact prime cross-sign split on the one-signed odd cone

For an odd test `v` that is nonnegative on `[0,∞)`, the Doob profile `f = Θv` is nonpositive on the
left half-line and nonnegative on the right, and `g = Θ|v| = |f|` is even.  The prime cross term of
`n` pairs the points `x` and `x + log n`; splitting the line at `−log n` and `0` and folding by the
evenness of `g` gives, for every `n ≥ 2` and every support,

`−∫ phiDoobPrimeCross v n = 2Λ(n)/√n ∫_0^{log n} g(s) g(log n − s) ds − 4Λ(n)/√n ∫_0^∞ g(s) g(s + log n) ds`:

a nonnegative opposite-side bonus `B_n(g)` minus a same-side term `C_n(g)`.  When the support of
`v` lies in `(−L/2, L/2)` with `L ≤ 2 log n` the same-side term vanishes identically, and the bonus
vanishes once `log n ≥ L`.  On the window `L ≤ 2 log 2` only the primes `2` and `3` survive, and
the arithmetic Doob energy is the exact sum

`E(v) = Λ_∞(Θ|v|) + 4·bonus(Θ|v|) + B₂(Θ|v|) + B₃(Θ|v|)`

of the Lévy form of the nonnegative even test, the archimedean cross-sign bonus, and the two prime
bonuses, each of the last three nonnegative.  No positivity of `Λ_∞(Θ|v|)` is claimed.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-! ## The two prime channels of an even nonnegative profile -/

/-- The opposite-side prime bonus `B_n(g) = 2 (Λ(n)/√n) ∫_0^{log n} g(s) g(log n − s) ds`. -/
def oppositeSideBonus (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * vonMangoldtAtom n * ∫ s in (0 : ℝ)..Real.log n, g s * g (Real.log n - s)

/-- The same-side prime cross term `C_n(g) = 4 (Λ(n)/√n) ∫_0^∞ g(s) g(s + log n) ds`. -/
def sameSideCross (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  4 * vonMangoldtAtom n * ∫ s in Ioi (0 : ℝ), g s * g (s + Real.log n)

theorem oppositeSideBonus_nonneg {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (n : ℕ) :
    0 ≤ oppositeSideBonus g n := by
  unfold oppositeSideBonus
  refine mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)) ?_
  exact intervalIntegral.integral_nonneg (Real.log_natCast_nonneg n)
    fun s _ => mul_nonneg (hg s) (hg _)

theorem sameSideCross_nonneg {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (n : ℕ) :
    0 ≤ sameSideCross g n := by
  unfold sameSideCross
  refine mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n)) ?_
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => mul_nonneg (hg s) (hg _)

theorem vonMangoldtAtom_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : vonMangoldtAtom n = 0 := by
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-! ## Translation and reflection of half-line integrals -/

/-- `∫_ℓ^∞ h(s) ds = ∫_0^∞ h(u + ℓ) du`. -/
theorem setIntegral_Ioi_translate (h : ℝ → ℝ) (ℓ : ℝ) :
    ∫ s in Ioi ℓ, h s = ∫ u in Ioi (0 : ℝ), h (u + ℓ) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun s => (Ioi ℓ).indicator h s) ℓ]
  congr 1
  funext u
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases hu : 0 < u
  · rw [if_pos (by linarith), if_pos hu]
  · rw [if_neg (by linarith), if_neg hu]

/-! ## The exact split -/

theorem phiDoobPrimeCross_eq_mul (v : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    phiDoobPrimeCross v n x =
      2 * vonMangoldtAtom n * (phiDoobTest v x * phiDoobTest v (x + Real.log n)) := by
  unfold phiDoobPrimeCross phiDoobTest
  ring

/-- **Exact prime cross-sign split.** For odd `v ≥ 0` on `[0,∞)` with compact support and any
`n`, the negative of the cross term of `n` is the opposite-side bonus minus the same-side term of
the even profile `Θ|v|`. -/
theorem neg_integral_phiDoobPrimeCross_eq (v : ℝ → ℝ) (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    (n : ℕ) :
    -∫ x, phiDoobPrimeCross v n x =
      oppositeSideBonus (phiDoobTest fun y => |v y|) n -
        sameSideCross (phiDoobTest fun y => |v y|) n := by
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : (fun x => phiDoobPrimeCross v n x) = fun _ => 0 :=
      funext (phiDoobPrimeCross_eq_zero_of_lt_two v hn)
    rw [h0, integral_zero, neg_zero]
    unfold oppositeSideBonus sameSideCross
    rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
    ring
  set ℓ := Real.log n with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_natCast_nonneg n
  set f := phiDoobTest v with hf
  set g := phiDoobTest fun y => |v y| with hg
  have hfc : Continuous f := continuous_riemannKernelReal.mul hv
  have hfs : HasCompactSupport f := hvc.mul_left
  have hgc : Continuous g := continuous_riemannKernelReal.mul hv.abs
  have hgabs : ∀ x, g x = |f x| := fun x => (abs_phiDoobTest v x).symm
  have hgeven : ∀ x, g (-x) = g x := phiDoobTest_abs_even hodd
  have hfpos : ∀ x, 0 ≤ x → 0 ≤ f x := phiDoobTest_nonneg_of_nonneg hpos
  have hfneg : ∀ x, x ≤ 0 → f x ≤ 0 := phiDoobTest_nonpos_of_odd hodd hpos
  -- the integrand and its integrability
  set F : ℝ → ℝ := fun x => f x * f (x + ℓ) with hF
  have hFc : Continuous F := hfc.mul (hfc.comp (continuous_id.add continuous_const))
  have hFs : HasCompactSupport F := hfs.mul_right
  have hFint : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  set G : ℝ → ℝ := fun x => g x * g (x + ℓ) with hG
  have hGc : Continuous G := hgc.mul (hgc.comp (continuous_id.add continuous_const))
  have hcross : ∫ x, phiDoobPrimeCross v n x = 2 * vonMangoldtAtom n * ∫ x, F x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => phiDoobPrimeCross_eq_mul v n x)
  -- split the line at `0`
  have hsplit0 : ∫ x, F x = (∫ x in Iic (0 : ℝ), F x) + ∫ x in Ioi (0 : ℝ), F x :=
    (intervalIntegral.integral_Iic_add_Ioi hFint.integrableOn hFint.integrableOn).symm
  -- right half-line: both factors nonnegative
  have hright : ∫ x in Ioi (0 : ℝ), F x = ∫ x in Ioi (0 : ℝ), G x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := le_of_lt hx
    simp only [hF, hG, hgabs]
    rw [abs_of_nonneg (hfpos x hx0), abs_of_nonneg (hfpos _ (by linarith))]
  -- left half-line: split at `−ℓ`
  have hsplitL : ∫ x in Iic (0 : ℝ), F x =
      (∫ x in Iic (-ℓ), F x) + ∫ x in Ioc (-ℓ) 0, F x := by
    rw [← Iic_union_Ioc_eq_Iic (by linarith : -ℓ ≤ 0)]
    exact setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hFint.integrableOn hFint.integrableOn
  -- far left: both factors nonpositive, fold by evenness onto the right half-line
  have hfar : ∫ x in Iic (-ℓ), F x = ∫ x in Ioi (0 : ℝ), G x := by
    have h1 : ∫ x in Iic (-ℓ), F x = ∫ x in Iic (-ℓ), G x := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
      have hx : x ≤ -ℓ := hx
      simp only [hF, hG, hgabs]
      rw [abs_of_nonpos (hfneg x (by linarith)), abs_of_nonpos (hfneg _ (by linarith))]
      ring
    have h2 : ∫ x in Iic (-ℓ), G x = ∫ t in Ioi ℓ, G (-t) := by
      have := integral_comp_neg_Iic (-ℓ) (fun t => G (-t))
      simp only [neg_neg] at this
      exact this
    have h3 : ∫ t in Ioi ℓ, G (-t) = ∫ t in Ioi ℓ, g t * g (t - ℓ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hG]
      rw [hgeven, show -t + ℓ = -(t - ℓ) by ring, hgeven]
    have h4 : ∫ t in Ioi ℓ, g t * g (t - ℓ) = ∫ u in Ioi (0 : ℝ), G u := by
      rw [setIntegral_Ioi_translate (fun t => g t * g (t - ℓ)) ℓ]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      simp only [hG]
      rw [add_sub_cancel_right, mul_comm]
    rw [h1, h2, h3, h4]
  -- the crossing interval: opposite signs, fold onto `(0, ℓ)`
  have hmid : ∫ x in Ioc (-ℓ) 0, F x = -∫ s in (0 : ℝ)..ℓ, g s * g (ℓ - s) := by
    have h1 : ∫ x in Ioc (-ℓ) 0, F x = -∫ x in Ioc (-ℓ) 0, G x := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      simp only [hF, hG, hgabs]
      rw [abs_of_nonpos (hfneg x hx.2), abs_of_nonneg (hfpos _ (by linarith [hx.1]))]
      ring
    have h2 : ∫ x in Ioc (-ℓ) 0, G x = ∫ s in (0 : ℝ)..ℓ, g s * g (ℓ - s) := by
      rw [← intervalIntegral.integral_of_le (by linarith : -ℓ ≤ 0)]
      have := intervalIntegral.integral_comp_neg (a := 0) (b := ℓ) G
      rw [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hG]
      rw [hgeven, show -s + ℓ = ℓ - s by ring]
    rw [h1, h2]
  -- assemble
  rw [hcross, hsplit0, hsplitL, hfar, hmid, hright]
  unfold oppositeSideBonus sameSideCross
  simp only [hG, hg, hℓ]
  ring

/-! ## Window vanishing -/

/-- The same-side term vanishes once the support of `v` lies in `(−L/2, L/2)` with `L ≤ 2 log n`. -/
theorem sameSideCross_eq_zero_of_window {v : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) {n : ℕ} (hn : L ≤ 2 * Real.log n) :
    sameSideCross (phiDoobTest fun y => |v y|) n = 0 := by
  unfold sameSideCross
  have h : ∫ s in Ioi (0 : ℝ), phiDoobTest (fun y => |v y|) s *
      phiDoobTest (fun y => |v y|) (s + Real.log n) = 0 := by
    refine (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_).trans (integral_zero _ _)
    have hs0 : 0 < s := hs
    have hout : s + Real.log n ∉ Ioo (-(L / 2)) (L / 2) := by
      intro hmem
      linarith [hmem.2]
    show phiDoobTest (fun y => |v y|) s * phiDoobTest (fun y => |v y|) (s + Real.log n) = 0
    simp only [phiDoobTest]
    rw [hsupp _ hout, abs_zero, mul_zero, mul_zero]
  rw [h, mul_zero]

/-- The opposite-side bonus vanishes once `log n ≥ L`. -/
theorem oppositeSideBonus_eq_zero_of_le {v : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) {n : ℕ} (hn : L ≤ Real.log n) :
    oppositeSideBonus (phiDoobTest fun y => |v y|) n = 0 := by
  unfold oppositeSideBonus
  have hℓ0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h : ∫ s in (0 : ℝ)..Real.log n, phiDoobTest (fun y => |v y|) s *
      phiDoobTest (fun y => |v y|) (Real.log n - s) = 0 := by
    rw [intervalIntegral.integral_of_le hℓ0]
    refine (setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_).trans (integral_zero _ _)
    show phiDoobTest (fun y => |v y|) s * phiDoobTest (fun y => |v y|) (Real.log n - s) = 0
    simp only [phiDoobTest]
    by_cases hsL : s < L / 2
    · have hout : Real.log n - s ∉ Ioo (-(L / 2)) (L / 2) := by
        intro hmem
        linarith [hmem.2]
      rw [hsupp _ hout, abs_zero, mul_zero, mul_zero]
    · have hout : s ∉ Ioo (-(L / 2)) (L / 2) := fun hmem => hsL hmem.2
      rw [hsupp _ hout, abs_zero, mul_zero, zero_mul]
  rw [h, mul_zero]

/-! ## The window identity -/

/-- On the window `L ≤ 2 log 2`, every negative cross term is a bonus. -/
theorem neg_integral_phiDoobPrimeCross_eq_bonus_of_window (v : ℝ → ℝ) (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) (n : ℕ) :
    -∫ x, phiDoobPrimeCross v n x = oppositeSideBonus (phiDoobTest fun y => |v y|) n := by
  rw [neg_integral_phiDoobPrimeCross_eq v hv hvc hodd hpos n]
  rcases lt_or_ge n 2 with hn | hn
  · unfold sameSideCross
    rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
    ring
  · rw [sameSideCross_eq_zero_of_window hsupp (n := n) ?_, sub_zero]
    calc L ≤ 2 * Real.log 2 := hL
      _ ≤ 2 * Real.log n := by
        have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        linarith

/-- On the window `L ≤ 2 log 2` only the primes `2` and `3` carry a bonus. -/
theorem tsum_oppositeSideBonus_eq_two_add_three {v : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    (∑' n : ℕ, oppositeSideBonus (phiDoobTest fun y => |v y|) n) =
      oppositeSideBonus (phiDoobTest fun y => |v y|) 2 +
        oppositeSideBonus (phiDoobTest fun y => |v y|) 3 := by
  rw [tsum_eq_sum (s := {2, 3}) ?_, Finset.sum_pair (by norm_num)]
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rcases lt_or_ge n 2 with h2 | h2
  · unfold oppositeSideBonus
    rw [vonMangoldtAtom_eq_zero_of_lt_two h2]
    ring
  · have h4 : 4 ≤ n := by omega
    refine oppositeSideBonus_eq_zero_of_le hsupp ?_
    calc L ≤ 2 * Real.log 2 := hL
      _ = Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      _ ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h4)

/-- **The exact window identity.** For odd `v ≥ 0` on `[0,∞)` of class `C²` supported in
`(−L/2, L/2)` with `L ≤ 2 log 2`:
`E(v) = Λ_∞(Θ|v|) + 4·bonus(Θ|v|) + B₂(Θ|v|) + B₃(Θ|v|)`. -/
theorem sourceEnergy_eq_levy_abs_add_bonus_add_primes (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    sourceEnergy (compactLift v hv hvc) =
      weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) +
        (oppositeSideBonus (phiDoobTest fun y => |v y|) 2 +
          oppositeSideBonus (phiDoobTest fun y => |v y|) 3) := by
  rw [sourceEnergy_compactLift_eq_levy_sub_tsum_cross v hv hvc, levy_phiDoob_eq_abs_add_bonus v hv hvc hodd hpos,
    ← tsum_oppositeSideBonus_eq_two_add_three hsupp hL, sub_eq_add_neg, ← tsum_neg]
  congr 2
  funext n
  exact neg_integral_phiDoobPrimeCross_eq_bonus_of_window v hv.continuous hvc hodd hpos hsupp hL n

/-- **The two-leg sign law on the one-signed odd cone, for every support.** The arithmetic Doob
energy is the Lévy form of the even profile `Θ|v|`, plus the archimedean cross-sign bonus, plus the
series of prime bonuses minus prime same-side terms:
`E(v) = Λ_∞(Θ|v|) + 4·bonus(Θ|v|) + Σ_n (B_n(Θ|v|) − C_n(Θ|v|))`.
The primes enter the opposite-side convolution with the archimedean sign and the same-side
autocorrelation with the archimedean sign reversed. -/
theorem sourceEnergy_eq_levy_abs_add_bonus_add_tsum_split (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) :
    sourceEnergy (compactLift v hv hvc) =
      weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) +
        ∑' n : ℕ, (oppositeSideBonus (phiDoobTest fun y => |v y|) n -
          sameSideCross (phiDoobTest fun y => |v y|) n) := by
  rw [sourceEnergy_compactLift_eq_levy_sub_tsum_cross v hv hvc,
    levy_phiDoob_eq_abs_add_bonus v hv hvc hodd hpos, sub_eq_add_neg, ← tsum_neg]
  congr 2
  funext n
  exact neg_integral_phiDoobPrimeCross_eq v hv.continuous hvc hodd hpos n

/-- The three correction terms are nonnegative, so the energy dominates the Lévy form of `Θ|v|`
by the explicit nonnegative amount `4·bonus + B₂ + B₃`. -/
theorem levy_abs_add_corrections_le_sourceEnergy (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    weilLevyForm (phiDoobTest fun y => |v y|) ≤ sourceEnergy (compactLift v hv hvc) ∧
      0 ≤ 4 * crossSignBonus (phiDoobTest fun y => |v y|) +
        (oppositeSideBonus (phiDoobTest fun y => |v y|) 2 +
          oppositeSideBonus (phiDoobTest fun y => |v y|) 3) := by
  have hg : ∀ u, 0 ≤ phiDoobTest (fun y => |v y|) u :=
    fun u => mul_nonneg (riemannKernelReal_pos u).le (abs_nonneg _)
  have h2 := oppositeSideBonus_nonneg hg 2
  have h3 := oppositeSideBonus_nonneg hg 3
  have hb := crossSignBonus_nonneg (phiDoobTest fun y => |v y|)
  have hE := sourceEnergy_eq_levy_abs_add_bonus_add_primes v hv hvc hodd hpos hsupp hL
  constructor <;> linarith

end RHTower.CHMDPolar
