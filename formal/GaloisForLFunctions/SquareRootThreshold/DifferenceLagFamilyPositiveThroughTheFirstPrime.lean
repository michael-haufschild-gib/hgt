import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths
import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpFoldOddWindowPastSevenTwentieths

/-!
# The difference lag family is positive through the first prime

The one-parameter lag family tests `ζ` with the difference tests
`f_{w,v}(t) = κ_w(t + v/2) − κ_w(t − v/2)`; RH is `Re P_{w,v} ≥ 0` for every late lag, where
`P_{w,v}` is the explicit-formula functional with the prime sum cut to the dyadic window
`|log n − v| ≤ 2w` (`zeta_onLine_iff_lag_primeWindow_nonneg`). The aperture floors of
`ArithmeticCriticalityTheory` transfer to the family through the Rayleigh bridge
`Re P_{w,v} ≥ 2‖κ_w‖² μ(v/2 + w)` and stop at the all-profile window `v/2 + w ≤ 3/10`, short of
the first prime at `log 2/2`.

The difference test is **odd** (`twoBump_modScaledBump_zero_neg`), and the odd sector of the Weil
form of `ζ` is positive through `353/1000 > log 2/2` (`ArithmeticIncidencePositivity`: the atom
`Λ(2)/√2` is paid from the archimedean strip surplus). Composing the two:

* `one_div_500_mul_le_re_lagPrimeWindowRHS_of_le`: `Re P_{w,v} ≥ (1/500) ∫‖κ_w‖²` for every
  `2w < v` with `v/2 + w ≤ 353/1000`, that is for every lag `v ≤ 706/1000 − 2w`.
* `lagPrimeWindow_eq_singleton_two`: for `|v − log 2| ≤ 2w` and `w < 1/12` the window read by the
  test is exactly `{2}`; `firstPrime_atom_paid_on_lagFamily` writes the inequality there as
  `(log 2/√2) Re(k(log 2) + k(−log 2)) + (1/500)∫‖κ_w‖² ≤ Re(polar + archimedean)`, `k` the
  autocorrelation of `f_{w,v}`: the first prime atom is paid on the problem's own family.
* `one_div_500_mul_le_re_lagPrimeWindowRHS_of_near_log_two`: for `w ≤ 3/1000` every lag of the
  prime-`2` window `|v − log 2| ≤ 2w` is covered.
* `lt_of_re_lagPrimeWindowRHS_neg`: a negative lag of the difference family has
  `v/2 + w > 353/1000`; the lag-side mirror of "contact apertures exceed `3/10`".

What this does not give: the second prime window `log 3/2 ≈ 0.549` lies beyond the archimedean odd
ceiling near `0.375`, and nothing is said about late lags.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity GaloisForLFunctions.ArithmeticPositivityTheory

/-! ### Parity of the difference tests -/

/-- `κ_{w,γ}(−u) = conj κ_{w,γ}(u)`: the bump is real and even, the modulation is a phase. -/
theorem modScaledBump_neg (w γ u : ℝ) :
    modScaledBump w γ (-u) = conj (modScaledBump w γ u) := by
  unfold modScaledBump scaledBump weilBumpC
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, neg_div, weilBump.neg]
  congr 2
  simp [Complex.conj_I]

/-- The modulated difference test satisfies `f(−t) = −conj f(t)`: its real part is odd and its
imaginary part is even. -/
theorem twoBump_modScaledBump_neg (w γ v t : ℝ) :
    twoBump (modScaledBump w γ) v (-1) (-t) = -conj (twoBump (modScaledBump w γ) v (-1) t) := by
  rw [twoBump_apply, twoBump_apply, map_add, map_mul, map_neg, map_one, ← modScaledBump_neg,
    ← modScaledBump_neg, show -t + v / 2 = -(t - v / 2) by ring,
    show -t - v / 2 = -(t + v / 2) by ring]
  ring

/-- The unmodulated difference test `κ_w(t + v/2) − κ_w(t − v/2)` is real-valued. -/
theorem twoBump_modScaledBump_zero_conj (w v t : ℝ) :
    conj (twoBump (modScaledBump w 0) v (-1) t) = twoBump (modScaledBump w 0) v (-1) t := by
  rw [twoBump_apply, map_add, map_mul, map_neg, map_one]
  simp only [modScaledBump, scaledBump, weilBumpC, ofReal_zero, mul_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_mul, Complex.conj_ofReal]

/-- **The unmodulated difference test is odd.** -/
theorem twoBump_modScaledBump_zero_neg (w v t : ℝ) :
    twoBump (modScaledBump w 0) v (-1) (-t) = -twoBump (modScaledBump w 0) v (-1) t := by
  rw [twoBump_modScaledBump_neg, twoBump_modScaledBump_zero_conj]

/-! ### Odd complex tests through `353/1000` -/

/-- **Odd complex tests through `353/1000`.** Every odd complex `C²` test supported in
`[−353/1000, 353/1000]` has `Re W_ζ(f, f) ≥ (1/1000) ∫ |f|²`: the zero-side form splits as
`Ẑ(Re f) + Ẑ(Im f)`, both parts of an odd test are odd, and the odd window of
`ArithmeticIncidencePositivity` applies to each part. -/
theorem zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredFiftyThreeThousandths {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(353 / 1000)) (353 / 1000))
    (hodd : ∀ x, f (-x) = -f x) :
    1 / 1000 * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  have hzero : ∀ x, 353 / 1000 < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hfs hmem
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hImc : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have h1 := fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths hRe hRec
    (fun x => by simp [hodd x]) fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths hIm hImc
    (fun x => by simp [hodd x]) fun x hx => by simp [hzero x hx]
  have hint (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun x => g x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => g x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hgc.isCompact fun x hx =>
        subset_tsupport g (by simpa using hx)
    exact (hg.pow 2).integrable_of_hasCompactSupport hs
  have hsplit : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add (hint _ hRe.continuous hRec) (hint _ hIm.continuous hImc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc, hsplit, mul_add]
  exact add_le_add h1 h2

/-! ### The lag family through the first prime -/

/-- **The odd window on the difference lag family.** For `0 < w`, `0 ≤ v` and
`v/2 + w ≤ 353/1000`: `Re W_ζ(f_{w,v}, f_{w,v}) ≥ (1/1000) ∫ |f_{w,v}|²`. -/
theorem one_div_1000_mul_le_re_W_twoBump_of_le {w v : ℝ} (hw : 0 < w) (hv0 : 0 ≤ v)
    (hvw : v / 2 + w ≤ 353 / 1000) :
    1 / 1000 * ∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2 ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re := by
  refine zetaZeroConfig_re_W_ge_of_odd_aperture_le_threeHundredFiftyThreeThousandths
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    ((tsupport_twoBump_modScaledBump_subset hw hv0).trans ?_)
    (twoBump_modScaledBump_zero_neg w v)
  exact Icc_subset_Icc (by linarith) hvw

/-- **The lag family is positive through the first prime.** For `0 < w`, `2w < v` and
`v/2 + w ≤ 353/1000`: `Re P_{w,v} ≥ (1/500) ∫ ‖κ_w‖²`. The lags reach `v = 706/1000 − 2w`, past
`log 2`, so dyadic windows containing the prime `2` are included. -/
theorem one_div_500_mul_le_re_lagPrimeWindowRHS_of_le {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v)
    (hvw : v / 2 + w ≤ 353 / 1000) :
    1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hv0 : 0 ≤ v := by linarith
  have hw2 : 2 * w < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := one_div_1000_mul_le_re_W_twoBump_of_le hw hv0 hvw
  rw [integral_norm_sq_twoBump_modScaledBump_eq hw hv,
    zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at h
  linarith

/-- **A negative lag of the difference family lies past the first prime**: `Re P_{w,v} < 0` forces
`v/2 + w > 353/1000`. -/
theorem lt_of_re_lagPrimeWindowRHS_neg {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v)
    (hneg : (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1)))).re < 0) :
    353 / 1000 < v / 2 + w := by
  by_contra hle
  have h := one_div_500_mul_le_re_lagPrimeWindowRHS_of_le hw hv (not_lt.mp hle)
  have h0 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 500)
    (integral_norm_sq_modScaledBump_pos hw).le
  linarith

/-! ### The window at the first prime -/

/-- **The window at the first prime.** For `0 < w < 1/12` and `|v − log 2| ≤ 2w`, the dyadic
window `|log n − v| ≤ 2w` read by the test at lag `v` is exactly `{2}`: `log 3 − log 2 ≥ 1/3 > 4w`
keeps every `n ≥ 3` out, and `n ≤ 1` has `log n = 0`. -/
theorem lagPrimeWindow_eq_singleton_two {w v : ℝ} (hw : 0 < w) (hw' : w < 1 / 12)
    (hv : |v - Real.log 2| ≤ 2 * w) : lagPrimeWindow v w = {2} := by
  have hl2 := Real.log_two_gt_d9
  have hv' := abs_le.mp hv
  ext n
  simp only [lagPrimeWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hn⟩
    have hd : |Real.log n - Real.log 2| < 1 / 3 := by
      calc |Real.log n - Real.log 2| = |(Real.log n - v) + (v - Real.log 2)| := by congr 1; ring
        _ ≤ |Real.log n - v| + |v - Real.log 2| := abs_add_le _ _
        _ < 1 / 3 := by linarith
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · exfalso
      have h0 : Real.log n = 0 := by interval_cases n <;> simp
      rw [h0, zero_sub, abs_neg, abs_of_pos (by linarith)] at hd
      linarith
    · rcases Nat.lt_or_ge n 3 with h3 | h3
      · omega
      · exfalso
        have h3' : (3 : ℝ) ≤ n := by exact_mod_cast h3
        have hlog : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) h3'
        have h32 : 1 / 3 ≤ Real.log 3 - Real.log 2 := by
          rw [← Real.log_div (by norm_num) (by norm_num)]
          have := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num)
          norm_num at this ⊢
          exact this
        have := le_abs_self (Real.log n - Real.log 2)
        linarith
  · rintro rfl
    refine ⟨?_, ?_⟩
    · have : (2 : ℕ) ≤ ⌊Real.exp (v + 2 * w)⌋₊ := by
        apply Nat.le_floor
        rw [← Real.log_le_iff_le_exp (by norm_num)]
        push_cast
        linarith
      omega
    · push_cast
      rw [abs_sub_comm]
      exact hv

/-- **The first prime atom is paid on the lag family.** For `0 < w < 1/12`, `|v − log 2| ≤ 2w` and
`v/2 + w ≤ 353/1000`, the prime side of `P_{w,v}` is the single atom
`(log 2/√2)(k(log 2) + k(−log 2))`, `k` the autocorrelation of `f_{w,v}`, and the polar and
archimedean terms pay it with margin `(1/500) ∫ ‖κ_w‖²`. -/
theorem firstPrime_atom_paid_on_lagFamily {w v : ℝ} (hw : 0 < w) (hw' : w < 1 / 12)
    (hv : |v - Real.log 2| ≤ 2 * w) (hvw : v / 2 + w ≤ 353 / 1000) :
    Real.log 2 / Real.sqrt 2 *
        (EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))
            (Real.log 2) +
          EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))
            (-Real.log 2)).re +
        1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) (I / 2) +
        paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) (-I / 2) +
        (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1))) r * (EF.gammaBracket r : ℂ)).re := by
  set k := EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))
    with hk
  have hv' := abs_le.mp hv
  have h2v : 2 * w < v := by linarith [Real.log_two_gt_d9]
  have h := one_div_500_mul_le_re_lagPrimeWindowRHS_of_le hw h2v hvw
  rw [lagPrimeWindowRHS, lagPrimeWindow_eq_singleton_two hw hw' hv, Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h
  simp only [Nat.cast_ofNat, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul] at h ⊢
  linarith

/-- **The whole first-prime window of lags is covered.** For `0 < w ≤ 3/1000` and every lag
`|v − log 2| ≤ 2w` (the window read by the test contains the prime `2`):
`Re P_{w,v} ≥ (1/500) ∫ ‖κ_w‖²`. -/
theorem one_div_500_mul_le_re_lagPrimeWindowRHS_of_near_log_two {w v : ℝ} (hw : 0 < w)
    (hw' : w ≤ 3 / 1000) (hv : |v - Real.log 2| ≤ 2 * w) :
    1 / 500 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  have hl2 := Real.log_two_lt_d9
  have hv' := abs_le.mp hv
  exact one_div_500_mul_le_re_lagPrimeWindowRHS_of_le hw (by linarith [Real.log_two_gt_d9])
    (by linarith)

end GaloisForLFunctions.SquareRootThreshold
