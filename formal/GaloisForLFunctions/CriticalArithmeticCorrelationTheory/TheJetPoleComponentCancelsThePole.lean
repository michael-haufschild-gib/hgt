import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheReducedDivisorJetCostsItsDivisorMean
import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAndThePoleCancelOnTheTopBand
import GaloisForLFunctions.RHTower.CriticalGibbsPerronPolarization

/-!
# The pole component of the divisor jet cancels the pole

The divisor jet of a band `u = Σ_{m ≤ R} a_m v_m` has pole coordinate
`J₁ = Σ_m a_m Λ(m)/√φ(m)`, and the near Gram kernel `K₂ᵦ` carries it as `J₁ K₂ᵦ v₁`. Separately,
`⟨K₂ᵦ v₁, w⟩` and the pole term `P⟨Πũ, w⟩` (`P = a₋a₊/G` the exact pole coefficient, `ũ` the
pole-free part of `u`) are of size `c(log N)^{1/2}` per unit mass. Together they cancel:

* **The plain pole row** (`abs_plainRow_sub_le`): by the cell comparison and `t = n e^u`,
  `Σ_{j ≠ n} j^{-1/2} β(log j − log n) = √n a₋a₊ − G/√n + O((nw + 1)(G + A₁)/n^{3/2})`, since
  `∫ e^{u/2} β = a₋a₊`.
* **The row defect** `δ_n = (K₂ᵦ j^{-1/2})(n) − P√n` has `Σ_n δ_n² = O(1 + log c)`
  (`exists_sum_poleRowDefect_sq_le`): deep rows `2nw ≤ 1` give `P²n`, interior rows `O(1/n)`,
  and the `c + 1` rows at the top edge `O(c³/N)` each.
* **The pole mode against the band** (`inner_reducedBand_poleMode`): by the exact Ramanujan Gram,
  `√log N ⟨ũ, v₁⟩ = −J₁/√log N + (floor remainder)`.
* **The coherent identity** (`coherentPolePair_eq`): for `w ⊥ v₁`,
  `P⟨Πũ, w⟩ + J₁⟨K₂ᵦ v₁, w⟩ = J₁ (log N)^{-1/2} Σ_n w_n δ_n + (floor remainder)`, hence
  (`exists_coherentPolePair_sq_le`) its square is
  `O((1 + log R)(1 + log c)/log N · Σ(1 + log m)a_m² + c²R⁵/(N² log N) Σ a_m²)‖w‖²`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset intervalIntegral
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  SuccessorShellArithmetic

/-- The plain pole row integrand `t^{-1/2} β(log t − log n)`. -/
def plainRowIntegrand (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * bumpCorr g (Real.log t - Real.log n)

section PlainRow

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

theorem hasDerivAt_plainRowIntegrand {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (plainRowIntegrand (atomDilate φ w) n)
      ((t * Real.sqrt t)⁻¹ * (-(1 / 2) * bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog := Real.hasDerivAt_log ht.ne'
  have hinv := (Real.hasDerivAt_sqrt ht.ne').inv hs.ne'
  have hβ := (hasDerivAt_bumpCorr_atomDilate hφ hsupp hw (Real.log t - Real.log n)).comp t
    (hlog.sub_const (Real.log n))
  have h := hinv.mul hβ
  have hf : plainRowIntegrand (atomDilate φ w) n = (fun x => Real.sqrt x)⁻¹ *
      (bumpCorr (atomDilate φ w) ∘ fun x => Real.log x - Real.log n) := by
    funext x; simp only [plainRowIntegrand, Pi.mul_apply, Pi.inv_apply, Function.comp]
  rw [hf]
  refine h.congr_deriv ?_
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  simp only [Pi.inv_apply, Function.comp]
  field_simp
  rw [hsq]
  ring

/-- **The plain row integrand has derivative `O((G + A₁)/n^{3/2})` on `[n/2, 2n]`.** -/
theorem abs_deriv_plainRowIntegrand_le {w A₁ : ℝ} (hw : 0 < w)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁) {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) / 2) (2 * n)) :
    |(t * Real.sqrt t)⁻¹ * (-(1 / 2) * bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))| ≤
      ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * ((∫ u, atomDilate φ w u ^ 2) + A₁) := by
  have hn2 : (1 : ℝ) ≤ n / 2 := by
    rw [le_div_iff₀ two_pos]; exact_mod_cast (by omega : 1 * 2 ≤ n)
  have ht1 : 1 ≤ t := hn2.trans ht.1
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hgc : Continuous (atomDilate φ w) := hφ.continuous.comp (continuous_id.div_const w)
  have hgcs : HasCompactSupport (atomDilate φ w) := by
    refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc 0 w)) fun u hu => ?_
    apply hsupp
    intro h
    apply hu
    rw [Set.mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw] at h
    constructor <;> nlinarith only [h.1, h.2, hw]
  have hβ := abs_bumpCorr_le hgc hgcs (Real.log t - Real.log n)
  have hA := hA₁ ((Real.log t - Real.log n) / w)
  have hpos : 0 < t * Real.sqrt t := mul_pos ht0 (Real.sqrt_pos.mpr ht0)
  have hden : ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2)) ≤ t * Real.sqrt t :=
    mul_le_mul ht.1 (Real.sqrt_le_sqrt ht.1) (Real.sqrt_nonneg _) ht0.le
  have hinv : (t * Real.sqrt t)⁻¹ ≤ ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ :=
    inv_anti₀ (mul_pos (by positivity) (Real.sqrt_pos.mpr (by positivity))) hden
  have hbracket : |-(1 / 2) * bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
      deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)| ≤
      (∫ u, atomDilate φ w u ^ 2) + A₁ := by
    have h0 := abs_nonneg (bumpCorr (atomDilate φ w) (Real.log t - Real.log n))
    calc _ ≤ |-(1 / 2) * bumpCorr (atomDilate φ w) (Real.log t - Real.log n)| +
          |deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)| := abs_add_le _ _
      _ = (1 / 2) * |bumpCorr (atomDilate φ w) (Real.log t - Real.log n)| +
          |deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)| := by
        rw [abs_mul]; norm_num
      _ ≤ _ := by linarith only [hβ, hA, h0]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  exact mul_le_mul hinv hbracket (abs_nonneg _) (inv_nonneg.mpr (by positivity))

/-- **The substitution `t = n e^u`.** Over any interval containing the support of the row,
`∫ t^{-1/2} β(log t − log n) dt = √n ∫ e^{u/2} β`. -/
theorem integral_plainRowIntegrand {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ n * Real.exp (-w)) (hb : n * Real.exp w ≤ b) :
    ∫ t in a..b, plainRowIntegrand (atomDilate φ w) n t =
      Real.sqrt n * ∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u := by
  set β := bumpCorr (atomDilate φ w) with hβdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβc : Continuous β := continuous_bumpCorr_atomDilate hφ hsupp hw
  have hβ0 : ∀ u, w ≤ |u| → β u = 0 := fun u hu => bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw hu
  set a' := Real.log (a / n)
  set b' := Real.log (b / n)
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have ha' : a' ≤ -w := by
    rw [← Real.log_exp (-w)]
    exact Real.log_le_log (div_pos ha hn0) (by rw [div_le_iff₀ hn0]; linarith only [hab])
  have hb' : w ≤ b' := by
    rw [← Real.log_exp w]
    exact Real.log_le_log (Real.exp_pos w) (by rw [le_div_iff₀ hn0]; linarith only [hb])
  have hab' : a' ≤ b' := by linarith only [ha', hb', hw]
  have hsub := integral_comp_mul_deriv' (a := a') (b := b') (f := fun u => n * Real.exp u)
    (f' := fun u => n * Real.exp u) (g := plainRowIntegrand (atomDilate φ w) n)
    (fun u _ => (Real.hasDerivAt_exp u).const_mul _) (by fun_prop) (by
      rintro t ⟨u, -, rfl⟩
      have ht : (0 : ℝ) < n * Real.exp u := by positivity
      refine ContinuousAt.continuousWithinAt ?_
      unfold plainRowIntegrand
      exact (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr ht).ne').mul
        (hβc.continuousAt.comp ((Real.continuousAt_log ht.ne').sub continuousAt_const)))
  have hfa : (n : ℝ) * Real.exp a' = a := by
    simp only [a']; rw [Real.exp_log (div_pos ha hn0)]; field_simp
  have hfb : (n : ℝ) * Real.exp b' = b := by
    simp only [b']; rw [Real.exp_log (div_pos hb0 hn0)]; field_simp
  rw [hfa, hfb] at hsub
  rw [← hsub]
  have hpt : ∀ u, (plainRowIntegrand (atomDilate φ w) n ∘ fun u => (n : ℝ) * Real.exp u) u *
      ((n : ℝ) * Real.exp u) = Real.sqrt n * (Real.exp (u / 2) * β u) := by
    intro u
    have he : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
      rw [← Real.sqrt_sq (Real.exp_pos (u / 2)).le, sq, ← Real.exp_add, add_halves]
    have hlog : Real.log ((n : ℝ) * Real.exp u) = Real.log n + u := by
      rw [Real.log_mul hn0.ne' (Real.exp_pos u).ne', Real.log_exp]
    have hsq : Real.sqrt ((n : ℝ) * Real.exp u) = Real.sqrt n * Real.exp (u / 2) := by
      rw [Real.sqrt_mul hn0.le, he]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hex : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
      rw [← Real.exp_add, add_halves]
    simp only [Function.comp, plainRowIntegrand, hlog, hsq, add_sub_cancel_left]
    rw [← hβdef, hex]
    field_simp
    rw [Real.sq_sqrt hn0.le]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hab']
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  have hu' : w ≤ |u| := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hβ0 u hu', mul_zero]

/-- **The plain pole row is a lattice sum.** For a row whose window lies in `[1, N]`,
`Σ_{j ≠ n} j^{-1/2} β(log j − log n) = √n ∫ e^{u/2}β − G/√n + O((n(e^w − e^{−w}) + 2) K_n)`,
`K_n = ((n/2)√(n/2))⁻¹(G + A₁)`. -/
theorem abs_plainRow_sub_le {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁) {N n : ℕ} (hn4 : 4 ≤ n)
    (hnN : (n : ℝ) * Real.exp w ≤ N) :
    |(∑ j ∈ Icc 1 N, if j = n then 0 else
          (Real.sqrt j)⁻¹ * bumpCorr (atomDilate φ w) (Real.log j - Real.log n)) -
        Real.sqrt n * (∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u) +
        (∫ u, atomDilate φ w u ^ 2) / Real.sqrt n| ≤
      (n * (Real.exp w - Real.exp (-w)) + 2) *
        (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * ((∫ u, atomDilate φ w u ^ 2) + A₁)) := by
  set g := atomDilate φ w with hgdef
  set β := bumpCorr g with hβdef
  set G := ∫ u, g u ^ 2 with hGdef
  set P := ∫ u, Real.exp (u / 2) * β u
  set K := ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have := Real.add_one_le_exp (-w); linarith only [this, hw4]
  have hep : Real.exp w ≤ 4 / 3 := by
    have h1 : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith only [h1, hem, Real.exp_pos w]
  set A := ⌊(n : ℝ) * Real.exp (-w)⌋₊ with hAdef
  set B := ⌊(n : ℝ) * Real.exp w⌋₊ with hBdef
  have hAle : (A : ℝ) ≤ n * Real.exp (-w) := Nat.floor_le (by positivity)
  have hAgt : (n : ℝ) * Real.exp (-w) < A + 1 := Nat.lt_floor_add_one _
  have hBle : (B : ℝ) ≤ n * Real.exp w := Nat.floor_le (by positivity)
  have hBgt : (n : ℝ) * Real.exp w < B + 1 := Nat.lt_floor_add_one _
  have hAn : (n : ℝ) / 2 ≤ A := by nlinarith only [hAgt, hem, hn4R]
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ A := by linarith only [hAn, hn4R]
    exact_mod_cast this
  have hAB : A ≤ B + 1 := by
    have e1 : (n : ℝ) * Real.exp (-w) ≤ n :=
      mul_le_of_le_one_right hn0.le (Real.exp_le_one_iff.mpr (by linarith only [hw]))
    have e2 : (n : ℝ) ≤ n * Real.exp w :=
      le_mul_of_one_le_right hn0.le (Real.one_le_exp_iff.mpr hw.le)
    have : (A : ℝ) ≤ B + 1 := by linarith only [hAle, e1, e2, hBgt]
    exact_mod_cast this
  have hB2n : (B : ℝ) + 1 ≤ 2 * n := by nlinarith only [hBle, hep, hn4R]
  have hBN : B ≤ N := by
    have : (B : ℝ) ≤ N := hBle.trans hnN
    exact_mod_cast this
  have hnB : n ≤ B := by
    have e2 : (n : ℝ) ≤ n * Real.exp w :=
      le_mul_of_one_le_right hn0.le (Real.one_le_exp_iff.mpr hw.le)
    exact Nat.le_floor e2
  have hnN' : n ≤ N := hnB.trans hBN
  set m := B + 1 - A with hmdef
  have hmR : (m : ℝ) = B + 1 - A := by rw [hmdef, Nat.cast_sub hAB]; push_cast; ring
  -- the row as a lattice sum over the cells `A ≤ j ≤ B`
  have hrow : (∑ j ∈ Icc 1 N, if j = n then 0 else (Real.sqrt j)⁻¹ * β (Real.log j - Real.log n)) =
      ∑ k ∈ range m, plainRowIntegrand g n ((A : ℝ) + k) - G / Real.sqrt n := by
    have hsplit : ∀ j ∈ Icc 1 N,
        (if j = n then 0 else (Real.sqrt j)⁻¹ * β (Real.log j - Real.log n)) =
        plainRowIntegrand g n j - if j = n then G / Real.sqrt n else 0 := by
      intro j _
      unfold plainRowIntegrand
      split_ifs with h
      · subst h; rw [sub_self, bumpCorr_zero]; ring
      · ring
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, hnN'⟩
    rw [sum_congr rfl hsplit, sum_sub_distrib, sum_ite_eq' (Icc 1 N) n, if_pos hnI]
    congr 1
    have hsub : Icc A B ⊆ Icc 1 N := fun j hj =>
      mem_Icc.mpr ⟨hA1.trans (mem_Icc.mp hj).1, (mem_Icc.mp hj).2.trans hBN⟩
    rw [← sum_subset hsub fun j hjN hj => ?_]
    · rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      rfl
    · have hj1 := (mem_Icc.mp hjN).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      unfold plainRowIntegrand
      rw [bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw, mul_zero]
      simp only [mem_Icc, not_and_or, not_le] at hj
      rcases hj with hj | hj
      · have hlt : (j : ℝ) < n * Real.exp (-w) := by
          have : j + 1 ≤ A := hj
          have : (j : ℝ) + 1 ≤ A := by exact_mod_cast this
          linarith only [this, hAle]
        have := Real.log_lt_log hj0 hlt
        rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
        rw [abs_of_neg (by linarith only [this, hw])]
        linarith only [this]
      · have hlt : (n : ℝ) * Real.exp w < j := by
          have : B + 1 ≤ j := hj
          have : (B : ℝ) + 1 ≤ j := by exact_mod_cast this
          linarith only [this, hBgt]
        have := Real.log_lt_log (by positivity) hlt
        rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
        rw [abs_of_pos (by linarith only [this, hw])]
        linarith only [this]
  have hcells : (A : ℝ) + m = B + 1 := by rw [hmR]; ring
  have hderiv : ∀ t ∈ Set.Icc (A : ℝ) (A + m), HasDerivAt (plainRowIntegrand g n)
      ((t * Real.sqrt t)⁻¹ * (-(1 / 2) * β (Real.log t - Real.log n) +
        deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))) t := by
    intro t ht
    exact hasDerivAt_plainRowIntegrand hφ hsupp hw n (by linarith only [ht.1, hAn, hn4R])
  have hbound : ∀ t ∈ Set.Icc (A : ℝ) (A + m),
      |(t * Real.sqrt t)⁻¹ * (-(1 / 2) * β (Real.log t - Real.log n) +
        deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w))| ≤ K := by
    intro t ht
    refine abs_deriv_plainRowIntegrand_le hφ hsupp hw hA₁ (by omega) ⟨hAn.trans ht.1, ?_⟩
    rw [hcells] at ht; linarith only [ht.2, hB2n]
  have hcmp := abs_sum_sub_integral_le_of_deriv hderiv hbound
  have hint := integral_plainRowIntegrand hφ hsupp hw (by omega : 1 ≤ n) (a := A) (b := A + m)
    (by linarith only [hAn, hn4R]) hAle (by rw [hcells]; exact hBgt.le)
  rw [hint] at hcmp
  have hm : (m : ℝ) ≤ n * (Real.exp w - Real.exp (-w)) + 2 := by
    rw [hmR]; nlinarith only [hBle, hAgt]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hbound A ⟨le_rfl, by
    have := Nat.cast_nonneg (α := ℝ) m; linarith only [this]⟩)
  rw [hrow]
  calc _ = |∑ k ∈ range m, plainRowIntegrand g n ((A : ℝ) + k) - Real.sqrt n * P| := by
        congr 1; ring
    _ ≤ m * K := hcmp
    _ ≤ _ := mul_le_mul_of_nonneg_right hm hK0

end PlainRow

/-! ### The near Gram kernel on the pole profile -/

/-- The exact pole coefficient `a₋a₊/G` of the complete Weil matrix. -/
def exactPoleCoefficient (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
    atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) / (∫ u, atomDilate φ (c / N) u ^ 2)

theorem exactPoleCoefficient_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    exactPoleCoefficient φ c N =
      atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c / N := by
  unfold exactPoleCoefficient atomPoleErrorCoefficient; ring

/-- The near Gram kernel applied to the pole profile `j^{-1/2}`. -/
def nearPoleRow (φ : ℝ → ℝ) (c : ℝ) (N n : ℕ) : ℝ :=
  nearGram φ c N (fun j => (Real.sqrt j)⁻¹) n

/-- The defect of the near pole row against the exact pole coefficient. -/
def poleRowDefect (φ : ℝ → ℝ) (c : ℝ) (N n : ℕ) : ℝ :=
  nearPoleRow φ c N n - exactPoleCoefficient φ c N * Real.sqrt n

/-! ### Row counting -/

/-- The deep rows `2nw ≤ 1` have `Σ K n ≤ K/(4w²)`. -/
theorem sum_deep_rows_le {K w : ℝ} (hK : 0 ≤ K) (hw : 0 < w) (N : ℕ) :
    (∑ n ∈ Icc 1 N, if 2 * (n : ℝ) * w ≤ 1 then K * n else 0) ≤ K / (4 * w ^ 2) := by
  rw [← sum_filter]
  set a := ⌊(1 : ℝ) / (2 * w)⌋₊ with hadef
  have ha_le : (a : ℝ) ≤ 1 / (2 * w) := Nat.floor_le (by positivity)
  have hsub : (Icc 1 N).filter (fun n : ℕ => 2 * (n : ℝ) * w ≤ 1) ⊆ Icc 1 a := by
    intro n hn
    obtain ⟨hnI, hnd⟩ := mem_filter.mp hn
    refine mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, Nat.le_floor ?_⟩
    rw [le_div_iff₀ (by positivity)]; linarith
  calc _ ≤ ∑ n ∈ Icc 1 a, K * (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ Icc 1 a, K * (a : ℝ) := by
        refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ hK
        exact_mod_cast (mem_Icc.mp hn).2
    _ = K * ((a : ℝ) * a) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ K * ((1 / (2 * w)) * (1 / (2 * w))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ha_le ha_le (Nat.cast_nonneg _) (by positivity)) hK
    _ = K / (4 * w ^ 2) := by field_simp; ring

/-- The rows `2nw > 1` have harmonic mass `≤ 4(1 + log c)`, `w = c/N`, `8c ≤ N`. -/
theorem sum_mid_rows_inv_le {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c) (h8 : 8 * c ≤ N) :
    (∑ n ∈ Icc 1 N, if 1 < 2 * (n : ℝ) * (c / N) then 1 / (n : ℝ) else 0) ≤
      4 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by linarith
  set w := c / N with hwdef
  have hw : 0 < w := div_pos hc0 hN0
  rw [← sum_filter]
  set a := ⌊(1 : ℝ) / (2 * w)⌋₊ with hadef
  have ha_le : (a : ℝ) ≤ 1 / (2 * w) := Nat.floor_le (by positivity)
  have ha_gt : 1 / (2 * w) < a + 1 := Nat.lt_floor_add_one _
  have h1 : (1 : ℝ) / (2 * w) = N / (2 * c) := by rw [hwdef]; field_simp
  have h2 : (4 : ℝ) ≤ N / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  have ha1 : 1 ≤ a := by
    apply Nat.le_floor
    rw [Nat.cast_one, h1]; linarith
  have haN : a ≤ N := by
    have : (a : ℝ) ≤ N := by
      refine ha_le.trans ?_
      rw [h1, div_le_iff₀ (by positivity)]; nlinarith
    exact_mod_cast this
  have hsub : (Icc 1 N).filter (fun n : ℕ => 1 < 2 * (n : ℝ) * w) ⊆ Ioc a N := by
    intro n hn
    obtain ⟨hnI, hnd⟩ := mem_filter.mp hn
    refine mem_Ioc.mpr ⟨?_, (mem_Icc.mp hnI).2⟩
    have : (a : ℝ) < n := by
      refine lt_of_le_of_lt ha_le ?_
      rw [div_lt_iff₀ (by positivity)]; linarith
    exact_mod_cast this
  have htail := RHTower.CriticalGibbs.sum_Ioc_inv_le_log ha1 haN
  have ha_lb : (N : ℝ) / (4 * c) ≤ a := by
    rw [h1] at ha_gt
    have : (N : ℝ) / (4 * c) = (N / (2 * c)) / 2 := by field_simp; ring
    rw [this]; linarith
  have hlog_a : Real.log N - Real.log a ≤ Real.log 4 + Real.log c := by
    have := Real.log_le_log (by positivity) ha_lb
    rw [Real.log_div hN0.ne' (by positivity), Real.log_mul (by norm_num) hc0.ne'] at this
    linarith
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hlc := Real.log_nonneg hc1
  have := (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans htail
  linarith

/-- At most `c + 1` rows have `N < n e^{c/N}`. -/
theorem card_top_rows_le {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c) (h8 : 8 * c ≤ N) :
    ((((Icc 1 N).filter (fun n : ℕ => (N : ℝ) < n * Real.exp (c / N))).card : ℕ) : ℝ) ≤
      c + 1 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by linarith
  set w := c / N with hwdef
  set k := ⌈c⌉₊ with hk
  have hk_lt : (k : ℝ) < c + 1 := Nat.ceil_lt_add_one hc0.le
  have hk_ge : c ≤ k := Nat.le_ceil c
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hem := Real.add_one_le_exp (-w)
  have hprod : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h1 : (N : ℝ) - c = N * (1 - w) := by rw [hwdef]; field_simp
  have hNc : ((N : ℝ) - c) * Real.exp w ≤ N := by
    rw [h1, mul_assoc]
    have : (1 - w) * Real.exp w ≤ 1 := by nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
    nlinarith
  have hsub : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) < n * Real.exp w) ⊆ Ioc (N - k) N := by
    intro n hn
    obtain ⟨hnI, hnt⟩ := mem_filter.mp hn
    refine mem_Ioc.mpr ⟨?_, (mem_Icc.mp hnI).2⟩
    by_contra hle
    push Not at hle
    have hle' : (n : ℝ) ≤ N - c := by
      have : (n : ℝ) ≤ ((N - k : ℕ) : ℝ) := by exact_mod_cast hle
      rw [Nat.cast_sub hkN] at this; linarith
    have := mul_le_mul_of_nonneg_right hle' (Real.exp_pos w).le
    linarith
  have h1 := card_le_card hsub
  rw [Nat.card_Ioc, Nat.sub_sub_self hkN] at h1
  have : (((Icc 1 N).filter (fun n : ℕ => (N : ℝ) < n * Real.exp w)).card : ℝ) ≤ k := by
    exact_mod_cast h1
  linarith

/-- `(c + 1)·2((2R√(R/N))² + (Kw)²N) ≤ 2(64e⁶ + 2K²)` for `R = 2ce²`, `w = c/N`, `c⁴ ≤ N`. -/
theorem top_rows_cost_le {c K : ℝ} {N : ℕ} (hc1 : 1 ≤ c) (hN0 : (0 : ℝ) < N) (h4 : c ^ 4 ≤ N) :
    2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
        (K * (c / N)) ^ 2 * N) * (c + 1) ≤ 2 * (64 * Real.exp 6 + 2 * K ^ 2) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR0 : 0 < linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hsq : (2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 =
      4 * linearNearRowRadius c ^ 3 / N := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have he6 : Real.exp 2 ^ 3 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hval : 2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
        (K * (c / N)) ^ 2 * N) = (64 * Real.exp 6 * c ^ 3 + 2 * K ^ 2 * c ^ 2) / N := by
    rw [hsq]
    unfold linearNearRowRadius
    rw [← he6]
    field_simp
    ring
  rw [hval, div_mul_eq_mul_div, div_le_iff₀ hN0]
  have hc2 : c ^ 2 ≤ c ^ 3 := by nlinarith
  have hc3 : c ^ 3 ≤ c ^ 4 := by nlinarith
  have he : 0 ≤ Real.exp 6 := (Real.exp_pos 6).le
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have e1 : (64 * Real.exp 6 * c ^ 3 + 2 * K ^ 2 * c ^ 2) * (c + 1) ≤
      (64 * Real.exp 6 + 2 * K ^ 2) * (2 * c ^ 4) := by
    have a1 : c ^ 3 * (c + 1) ≤ 2 * c ^ 4 := by nlinarith
    have a2 : c ^ 2 * (c + 1) ≤ 2 * c ^ 4 := by nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ 64 * Real.exp 6)
    have b2 := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ 2 * K ^ 2)
    nlinarith
  have e2 : (64 * Real.exp 6 + 2 * K ^ 2) * (2 * c ^ 4) ≤ 2 * (64 * Real.exp 6 + 2 * K ^ 2) * N := by
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * (64 * Real.exp 6 + 2 * K ^ 2))
    nlinarith
  linarith

section PoleRow

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- The exact pole coefficient is `O(c/N)`. -/
theorem exists_abs_exactPoleCoefficient_le :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ {c : ℝ} {N : ℕ}, 0 < c → 1 ≤ N → c / N ≤ 1 →
      |exactPoleCoefficient φ c N| ≤ C_P * (c / N) := by
  have hK := atomPoleMomentErrorConstant_nonneg φ
  refine ⟨(∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) + atomPoleMomentErrorConstant φ,
    add_nonneg (div_nonneg (sq_nonneg _) hM.le) hK, ?_⟩
  intro c N hc hN hw1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc hN0
  have h := abs_dilated_pole_product_sub_le hφ hsupp hM hw0 hw1
  set w := c / N
  set main := w * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
  have hmain : 0 ≤ main := div_nonneg (mul_nonneg hw0.le (sq_nonneg _)) hM.le
  have hw2 : w ^ 2 ≤ w := by nlinarith
  unfold exactPoleCoefficient
  set P := atomExponentialMoment (atomDilate φ w) (-(1 / 2)) *
    atomExponentialMoment (atomDilate φ w) (1 / 2) / ∫ u, atomDilate φ w u ^ 2
  have htri : |P| ≤ |P - main| + main := by
    have := abs_add_le (P - main) main
    rw [sub_add_cancel, abs_of_nonneg hmain] at this
    exact this
  have hmain_eq : main = (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * w := by
    simp only [main]; ring
  have hKw := mul_le_mul_of_nonneg_left hw2 hK
  nlinarith

omit hM in
/-- `∫ e^{u/2} β = a₋a₊` for the dilated atom. -/
theorem integral_exp_half_mul_bumpCorr_atomDilate {w : ℝ} (hw : 0 < w) :
    ∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u =
      atomExponentialMoment (atomDilate φ w) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ w) (1 / 2) := by
  obtain ⟨hg, -, hgc⟩ := atomDilate_facts hφ hsupp hw
  rw [integral_exp_half_mul_bumpCorr hg.continuous hgc]
  unfold atomExponentialMoment
  congr 1
  · congr 1; funext u; congr 2; ring
  · congr 1; funext u; congr 2; ring

/-- The near pole row is the plain lattice row divided by the atom mass. -/
theorem nearPoleRow_eq {c : ℝ} {N : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (n : ℕ) :
    nearPoleRow φ c N n =
      (∑ j ∈ Icc 1 N, if j = n then 0 else
        (Real.sqrt j)⁻¹ * bumpCorr (atomDilate φ (c / N)) (Real.log j - Real.log n)) /
        (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  unfold nearPoleRow nearGram nearRowIndices
  rw [sum_filter, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_atomDilate_sq hw]
  by_cases hjn : j = n
  · simp [hjn]
  · rw [if_neg hjn]
    have hsym : shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) =
        shellAutocorr φ ((Real.log j - Real.log n) / (c / N)) := by
      rcases le_or_gt 0 (Real.log j - Real.log n) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, neg_div, shellAutocorr_neg]
    rw [bumpCorr_atomDilate_eq hw]
    by_cases hnear : |Real.log j - Real.log n| ≤ 2 * c / N
    · rw [if_pos ⟨hjn, hnear⟩, hsym]
      field_simp
    · rw [if_neg (fun h => hnear h.2)]
      have hz : shellAutocorr φ ((Real.log j - Real.log n) / (c / N)) = 0 := by
        apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
        rw [abs_div, abs_of_pos hw, le_div_iff₀ hw, one_mul]
        push Not at hnear
        have : c / N ≤ 2 * c / N := by
          rw [div_le_div_iff_of_pos_right hN0]; linarith
        linarith
      rw [hz]
      simp

omit hM in
/-- **Deep rows carry no near pole row.** If `2nw ≤ 1`, no `j ≠ n` lies within `w` of `n` in
logarithmic distance. -/
theorem nearPoleRow_eq_zero_of_deep {c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hdeep : 2 * n * (c / N) ≤ 1) : nearPoleRow φ c N n = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold nearPoleRow nearGram
  refine sum_eq_zero fun j hj => ?_
  obtain ⟨hjI, hjn, -⟩ := mem_filter.mp hj
  have hj1 := (mem_Icc.mp hjI).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have key : c / N ≤ |Real.log j - Real.log n| := by
    rcases lt_or_gt_of_ne hjn with hlt | hgt
    · -- `j ≤ n − 1`
      have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      have h := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
      rw [Real.log_div hj0.ne' hn0.ne'] at h
      have hfrac : (j : ℝ) / n ≤ 1 - c / N := by
        rw [div_le_iff₀ hn0]; nlinarith
      rw [abs_of_neg (by linarith)]
      linarith
    · have hjn' : (n : ℝ) + 1 ≤ j := by exact_mod_cast hgt
      have h := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
      rw [Real.log_div hn0.ne' hj0.ne'] at h
      have hfrac : (n : ℝ) / j ≤ 1 - c / N := by
        rw [div_le_iff₀ hj0]; nlinarith
      rw [abs_of_pos (by linarith)]
      linarith
  rw [shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (by
    rw [abs_div, abs_abs, abs_of_pos hw, le_div_iff₀ hw, one_mul]; exact key), zero_div, zero_mul]

/-- Every near pole row is at most `2R_c √(R_c/N)`. -/
theorem abs_nearPoleRow_le {c : ℝ} {N n : ℕ} (hc : 0 < c) (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1) :
    |nearPoleRow φ c N n| ≤
      2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N) := by
  have hN0 : (0 : ℝ) < N := by
    have := (mem_Icc.mp hn); exact_mod_cast (show 0 < N by omega)
  have hR0 : 0 < linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hterm : ∀ j ∈ nearRowIndices c N n,
      |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2) *
        (Real.sqrt j)⁻¹| ≤ Real.sqrt (linearNearRowRadius c / N) := by
    intro j hj
    have hjN := (nearRow_geometry_small_width hc hn hj hw).2.2
    have hj1 := (mem_Icc.mp (mem_filter.mp hj).1).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hA := abs_shellAutocorr_le hφ hsupp (|Real.log j - Real.log n| / (c / N))
    have hq : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hM, div_le_one hM]; exact hA
    have hs : (Real.sqrt j)⁻¹ ≤ Real.sqrt (linearNearRowRadius c / N) := by
      rw [← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      rw [inv_eq_one_div, div_le_div_iff₀ hj0 hN0]
      linarith
    rw [abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hj0))]
    calc _ ≤ 1 * Real.sqrt (linearNearRowRadius c / N) :=
          mul_le_mul hq hs (by positivity) zero_le_one
      _ = _ := one_mul _
  have hcard := card_nearRowIndices_le_small_width hc hn hw
  unfold nearPoleRow nearGram
  calc _ ≤ ∑ j ∈ nearRowIndices c N n, |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) /
          (∫ t, φ t ^ 2) * (Real.sqrt j)⁻¹| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ nearRowIndices c N n, Real.sqrt (linearNearRowRadius c / N) := sum_le_sum hterm
    _ = (nearRowIndices c N n).card * Real.sqrt (linearNearRowRadius c / N) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)

/-- **The pole row defect on an interior row.** For `4 ≤ n` and `n e^w ≤ N`,
`|poleRowDefect n + n^{-1/2}| ≤ (n(e^w − e^{−w}) + 2) K_n/G`. -/
theorem abs_poleRowDefect_add_le {A₁ : ℝ} (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (hw4 : c / N ≤ 1 / 4) (hn4 : 4 ≤ n)
    (hnN : (n : ℝ) * Real.exp (c / N) ≤ N) :
    |poleRowDefect φ c N n + (Real.sqrt n)⁻¹| ≤
      (n * (Real.exp (c / N) - Real.exp (-(c / N))) + 2) *
        (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ *
          ((∫ u, atomDilate φ (c / N) u ^ 2) + A₁)) / (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hrow := abs_plainRow_sub_le hφ hsupp hw hw4 hA₁ hn4 hnN
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hid : poleRowDefect φ c N n + (Real.sqrt n)⁻¹ =
      ((∑ j ∈ Icc 1 N, if j = n then 0 else
          (Real.sqrt j)⁻¹ * bumpCorr (atomDilate φ (c / N)) (Real.log j - Real.log n)) -
        Real.sqrt n * (∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ (c / N)) u) +
        (∫ u, atomDilate φ (c / N) u ^ 2) / Real.sqrt n) / (∫ u, atomDilate φ (c / N) u ^ 2) := by
    unfold poleRowDefect exactPoleCoefficient
    rw [nearPoleRow_eq hφ hsupp hM hc hN, integral_exp_half_mul_bumpCorr_atomDilate hφ hsupp hw]
    field_simp
  rw [hid, abs_div, abs_of_pos hG]
  exact div_le_div_of_nonneg_right hrow hG.le

/-- **Interior rows.** For `1 < 2nw`, `n e^w ≤ N`, `w ≤ 1/8`:
`|poleRowDefect n| ≤ (22 + 21 A₁/∫φ²)/√n`. -/
theorem abs_poleRowDefect_le_interior {A₁ : ℝ} (hA₀ : 0 ≤ A₁)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 1 ≤ N) (hw8 : c / N ≤ 1 / 8)
    (hmid : 1 < 2 * n * (c / N)) (hnN : (n : ℝ) * Real.exp (c / N) ≤ N) :
    |poleRowDefect φ c N n| ≤ (22 + 21 * A₁ / (∫ u, φ u ^ 2)) * (Real.sqrt n)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set w := c / N with hwdef
  have hw : 0 < w := div_pos hc hN0
  have hn4R : (4 : ℝ) < n := by
    by_contra h; push Not at h
    have : 2 * (n : ℝ) * w ≤ 2 * 4 * (1 / 8) := by
      apply mul_le_mul (by linarith) hw8 hw.le (by norm_num)
    linarith
  have hn4 : 4 ≤ n := by exact_mod_cast hn4R.le
  have hn0 : (0 : ℝ) < n := by linarith
  have hrow := abs_poleRowDefect_add_le hφ hsupp hM hA₁ hc hN (by linarith) hn4 hnN
  rw [← hwdef] at hrow
  set G := ∫ u, atomDilate φ w u ^ 2 with hGdef
  have hGw : G = w * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw
  have hG : 0 < G := by rw [hGw]; exact mul_pos hw hM
  set sn := Real.sqrt n with hsn
  have hs0 : 0 < sn := Real.sqrt_pos.mpr hn0
  have hss : sn * sn = n := Real.mul_self_sqrt hn0.le
  -- `e^w − e^{−w} ≤ 3w`
  have hem := Real.add_one_le_exp (-w)
  have hprod : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hep : Real.exp w ≤ 1 + 2 * w := by nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
  have hX : (n : ℝ) * (Real.exp w - Real.exp (-w)) + 2 ≤ 7 * n * w := by nlinarith
  -- `((n/2)√(n/2))⁻¹ ≤ 3/(n√n)`
  have hsq2 : Real.sqrt ((n : ℝ) / 2) * Real.sqrt 2 = sn := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ two_ne_zero]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hsq2' : 2 * sn / 3 ≤ Real.sqrt ((n : ℝ) / 2) := by
    have : Real.sqrt ((n : ℝ) / 2) * (3 / 2) ≥ sn := by
      rw [← hsq2]; exact mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
    linarith
  have hY : ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ ≤ 3 / (n * sn) := by
    rw [show 3 / ((n : ℝ) * sn) = ((n : ℝ) * sn / 3)⁻¹ by field_simp]
    apply inv_anti₀ (by positivity)
    nlinarith
  have hYpos : 0 < ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ := by positivity
  have hXY : ((n : ℝ) * (Real.exp w - Real.exp (-w)) + 2) *
      ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ ≤ 21 * w / sn := by
    have hX0 : 0 ≤ (n : ℝ) * (Real.exp w - Real.exp (-w)) + 2 := by
      have : Real.exp (-w) ≤ Real.exp w := Real.exp_le_exp.mpr (by linarith)
      nlinarith
    calc _ ≤ (7 * n * w) * (3 / (n * sn)) := mul_le_mul hX hY hYpos.le (by positivity)
      _ = 21 * w / sn := by field_simp; ring
  have hE : ((n : ℝ) * (Real.exp w - Real.exp (-w)) + 2) *
      (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)) / G ≤
      (21 + 21 * A₁ / (∫ u, φ u ^ 2)) * sn⁻¹ := by
    rw [← mul_assoc, mul_div_assoc]
    have hGA : (G + A₁) / G = 1 + A₁ / G := by field_simp
    rw [hGA]
    have hA1G : 0 ≤ A₁ / G := div_nonneg hA₀ hG.le
    calc _ ≤ 21 * w / sn * (1 + A₁ / G) :=
          mul_le_mul_of_nonneg_right hXY (by linarith)
      _ = (21 * w + 21 * A₁ / (∫ u, φ u ^ 2)) * sn⁻¹ := by
          rw [hGw]; field_simp
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hs0.le)
          have : w ≤ 1 := by linarith
          linarith
  have htri := abs_add_le (poleRowDefect φ c N n + sn⁻¹) (-sn⁻¹)
  rw [add_neg_cancel_right, abs_neg, abs_of_pos (inv_pos.mpr hs0)] at htri
  linarith

/-- Pointwise majorant of the squared pole row defect by the three row classes. -/
theorem poleRowDefect_sq_le_classes {A₁ C_P : ℝ} (hA₀ : 0 ≤ A₁)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {c : ℝ} {N n : ℕ} (hc0 : 0 < c) (hN1 : 1 ≤ N) (hw8 : c / N ≤ 1 / 8)
    (hPw : |exactPoleCoefficient φ c N| ≤ C_P * (c / N)) (hn : n ∈ Icc 1 N) :
    poleRowDefect φ c N n ^ 2 ≤
      (if 2 * (n : ℝ) * (c / N) ≤ 1 then (C_P * (c / N)) ^ 2 * n else 0) +
        (if 1 < 2 * (n : ℝ) * (c / N) then
          (22 + 21 * A₁ / (∫ u, φ u ^ 2)) ^ 2 * (1 / (n : ℝ)) else 0) +
        (if (N : ℝ) < n * Real.exp (c / N) then
          2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
            (C_P * (c / N)) ^ 2 * N) else 0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := by linarith
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hP2 : exactPoleCoefficient φ c N ^ 2 ≤ (C_P * (c / N)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hPw 2
  have hB3 : 0 ≤ 2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
      (C_P * (c / N)) ^ 2 * N) := by positivity
  have hCd : 0 ≤ (22 + 21 * A₁ / (∫ u, φ u ^ 2)) ^ 2 * (1 / (n : ℝ)) := by positivity
  by_cases hdeep : 2 * (n : ℝ) * (c / N) ≤ 1
  · have hz := nearPoleRow_eq_zero_of_deep hφ hsupp hc0 hN1 hn1 hdeep
    have hval : poleRowDefect φ c N n ^ 2 = exactPoleCoefficient φ c N ^ 2 * n := by
      unfold poleRowDefect; rw [hz]
      rw [show (0 - exactPoleCoefficient φ c N * Real.sqrt n) ^ 2 =
        exactPoleCoefficient φ c N ^ 2 * (Real.sqrt n) ^ 2 by ring, Real.sq_sqrt hn0.le]
    rw [if_pos hdeep, if_neg (not_lt.mpr hdeep), hval]
    have := mul_le_mul_of_nonneg_right hP2 hn0.le
    split_ifs <;> linarith
  · push Not at hdeep
    rw [if_neg (not_le.mpr hdeep), if_pos hdeep, zero_add]
    by_cases htop : (N : ℝ) < n * Real.exp (c / N)
    · rw [if_pos htop]
      have hrow := abs_nearPoleRow_le hφ hsupp hM hc0 hn hw1
      have hrow2 : nearPoleRow φ c N n ^ 2 ≤
          (2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hrow 2
      have hPn : (exactPoleCoefficient φ c N * Real.sqrt n) ^ 2 ≤ (C_P * (c / N)) ^ 2 * N := by
        rw [mul_pow, Real.sq_sqrt hn0.le]
        exact mul_le_mul hP2 hnN hn0.le (sq_nonneg _)
      have hval : poleRowDefect φ c N n ^ 2 ≤
          2 * (nearPoleRow φ c N n ^ 2 + (exactPoleCoefficient φ c N * Real.sqrt n) ^ 2) := by
        unfold poleRowDefect
        nlinarith [sq_nonneg (nearPoleRow φ c N n + exactPoleCoefficient φ c N * Real.sqrt n)]
      linarith
    · rw [if_neg htop, add_zero]
      push Not at htop
      have hb := abs_poleRowDefect_le_interior hφ hsupp hM hA₀ hA₁ hc0 hN1 hw8 hdeep htop
      have h2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs, mul_pow, inv_pow, Real.sq_sqrt hn0.le] at h2
      rw [one_div]; exact h2

/-- **The pole row defect has square sum `O(1 + log c)`.** -/
theorem exists_sum_poleRowDefect_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → 8 * c ≤ N → c ^ 4 ≤ N →
      (∑ n ∈ Icc 1 N, poleRowDefect φ c N n ^ 2) ≤ C * (1 + Real.log c) := by
  obtain ⟨A₁, hA₀, hA₁⟩ := exists_abs_deriv_shellAutocorr_le hφ hsupp
  obtain ⟨C_P, hCP, hP⟩ := exists_abs_exactPoleCoefficient_le hφ hsupp hM
  set C_d := 22 + 21 * A₁ / (∫ u, φ u ^ 2) with hCd
  set B₀ := 2 * (64 * Real.exp 6 + 2 * C_P ^ 2) with hB₀
  refine ⟨C_P ^ 2 / 4 + 4 * C_d ^ 2 + B₀, by positivity, ?_⟩
  intro c N hc1 h8 h4
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hw : 0 < c / N := div_pos hc0 hN0
  have hw8 : c / N ≤ 1 / 8 := by rw [div_le_iff₀ hN0]; linarith
  have hPw := hP hc0 hN1 (by linarith)
  refine (sum_le_sum fun n hn =>
    poleRowDefect_sq_le_classes hφ hsupp hM hA₀ hA₁ hc0 hN1 hw8 hPw hn).trans ?_
  rw [sum_add_distrib, sum_add_distrib]
  have hdeep := sum_deep_rows_le (sq_nonneg (C_P * (c / N))) hw N
  have hdeep' : (C_P * (c / N)) ^ 2 / (4 * (c / N) ^ 2) = C_P ^ 2 / 4 := by
    field_simp
  rw [hdeep'] at hdeep
  have hmid := sum_mid_rows_inv_le hc1 h8
  have hmid' : (∑ n ∈ Icc 1 N, if 1 < 2 * (n : ℝ) * (c / N) then C_d ^ 2 * (1 / (n : ℝ)) else 0) =
      C_d ^ 2 * ∑ n ∈ Icc 1 N, if 1 < 2 * (n : ℝ) * (c / N) then 1 / (n : ℝ) else 0 := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by split_ifs <;> simp
  have htop_eq : (∑ n ∈ Icc 1 N, if (N : ℝ) < n * Real.exp (c / N) then
        2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
          (C_P * (c / N)) ^ 2 * N) else 0) =
      (((Icc 1 N).filter (fun n : ℕ => (N : ℝ) < n * Real.exp (c / N))).card : ℝ) *
        (2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
          (C_P * (c / N)) ^ 2 * N)) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcard := card_top_rows_le hc1 h8
  have hcost := top_rows_cost_le (K := C_P) hc1 hN0 h4
  have hB3 : 0 ≤ 2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
      (C_P * (c / N)) ^ 2 * N) := by positivity
  have htop : (((Icc 1 N).filter (fun n : ℕ => (N : ℝ) < n * Real.exp (c / N))).card : ℝ) *
        (2 * ((2 * linearNearRowRadius c * Real.sqrt (linearNearRowRadius c / N)) ^ 2 +
          (C_P * (c / N)) ^ 2 * N)) ≤ B₀ := by
    calc _ ≤ (c + 1) * (2 * ((2 * linearNearRowRadius c *
          Real.sqrt (linearNearRowRadius c / N)) ^ 2 + (C_P * (c / N)) ^ 2 * N)) :=
          mul_le_mul_of_nonneg_right hcard hB3
      _ ≤ B₀ := by rw [hB₀]; linarith
  rw [hmid', htop_eq]
  have hlc := Real.log_nonneg hc1
  have hm2 := mul_le_mul_of_nonneg_left hmid (sq_nonneg C_d)
  have hB0 : 0 ≤ B₀ := by positivity
  have hCP2 : 0 ≤ C_P ^ 2 / 4 := by positivity
  nlinarith

end PoleRow

/-! ### The coherent pole pair -/

/-- The pole conductor of the divisor jet: `J₁ = Σ_m a_m Λ(m)/√φ(m)`. -/
theorem divisorJetCoeff_one_eq (R : ℕ) (a : ℕ → ℝ) :
    divisorJetCoeff R a 1 =
      ∑ m ∈ Icc 1 R, a m * (ArithmeticFunction.vonMangoldt m / Real.sqrt (m.totient : ℝ)) := by
  unfold divisorJetCoeff ramanujanJetConductorWeight
  refine sum_congr rfl fun m hm => ?_
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  rw [if_pos (Nat.mem_divisors.mpr ⟨one_dvd m, hm0.ne'⟩), Nat.div_one]
  by_cases h : 1 = m
  · subst h; simp
  · rw [if_neg h, zero_add, Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one]

theorem primeHorizonExtension_poleMode {N j : ℕ} (hj : j ∈ Icc 1 N) :
    primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j =
      (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt j)⁻¹ := by
  rw [primeHorizonExtension_normalizedRamanujan hj, ramanujanPoleProfile,
    normalizedRamanujanMode_one, one_div]

/-- The pairing with the pole mode is `(log N)^{-1/2}` times the harmonic sum. -/
theorem inner_poleMode_eq {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = (Real.sqrt (Real.log N))⁻¹ *
      SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) := by
  rw [normalizedRamanujanHorizonVector, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Real.sqrt (Real.log N))⁻¹ * ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n * x n = _
  congr 1
  unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun n _ => ?_
  simp only [ramanujanPoleProfile, normalizedRamanujanMode_one, primeHorizonExtension_coe]
  ring

/-- The near Gram kernel on the pole mode pairs through the near pole rows. -/
theorem inner_nearJet_poleMode (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N)
        (normalizedRamanujanHorizonVector 1 N), w⟫ =
      (Real.sqrt (Real.log N))⁻¹ * ∑ n ∈ Icc 1 N, primeHorizonExtension w n * nearPoleRow φ c N n := by
  have hK : nearDivisorJetKernelMatrix φ c N = horizonKernelMatrix (fun n j =>
      if j ∈ nearRowIndices c N n then
        shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2) else 0) N := rfl
  rw [hK, horizonKernelMatrix_bilinear, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  unfold nearPoleRow nearGram
  rw [mul_sum, mul_sum, nearRowIndices, sum_filter]
  refine sum_congr rfl fun j hj => ?_
  rw [primeHorizonExtension_poleMode hj]
  have hmem : (j ∈ (Icc 1 N).filter (fun j => j ≠ n ∧
      |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N)) ↔
      (j ≠ n ∧ |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N) := by
    rw [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
  by_cases hp : j ≠ n ∧ |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N
  · rw [if_pos (hmem.mpr hp), if_pos hp]; ring
  · rw [if_neg (fun h => hp (hmem.mp h)), if_neg hp]; ring

/-- The arithmetic pole kernel against a pole-orthogonal row factor. -/
theorem poleKernel_bilinear_eq {N : ℕ} (W U : ℕ → ℝ)
    (hW : SelectiveMultiscaleArithmeticPositivity.harmonicSum N W = 0) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, W n * U j * arithmeticPoleKernel n j) =
      (∑ n ∈ Icc 1 N, W n * Real.sqrt n) *
        SelectiveMultiscaleArithmeticPositivity.harmonicSum N U := by
  unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum at hW ⊢
  have hterm (n j : ℕ) : W n * U j * arithmeticPoleKernel n j =
      (W n * Real.sqrt n) * (U j / Real.sqrt j) + (W n / Real.sqrt n) * (U j * Real.sqrt j) := by
    unfold arithmeticPoleKernel; ring
  simp only [hterm, sum_add_distrib, ← mul_sum, ← sum_mul, hW, zero_mul, add_zero]

/-- `Λ(m)/φ(m) ≤ 2Λ(m)/m`. -/
theorem vonMangoldt_div_totient_le (m : ℕ) :
    ArithmeticFunction.vonMangoldt m / (m.totient : ℝ) ≤
      2 * (ArithmeticFunction.vonMangoldt m / m) := by
  by_cases hm : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have htot := Nat.totient_prime_pow hp hk
    have hpk0 : 0 < p ^ k := pow_pos hp.pos k
    have hpk : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hpk0
    have hφpos : (0 : ℝ) < ((p ^ k).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hpk0
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt (p ^ k) := ArithmeticFunction.vonMangoldt_nonneg
    have h2φ : ((p ^ k : ℕ) : ℝ) ≤ 2 * ((p ^ k).totient : ℝ) := by
      rw [htot]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [Nat.cast_sub hp.one_le]; push_cast
      rw [pow_succ]
      have : (0 : ℝ) ≤ (p : ℝ) ^ k' := by positivity
      nlinarith
    rw [div_le_iff₀ hφpos, mul_comm 2, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hpk]
    nlinarith
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm]; simp

/-- **Cauchy–Schwarz for the pole jet coefficient.** `J₁² ≤ 4 log R · Σ (1 + log m) a_m²`. -/
theorem divisorJetCoeff_one_sq_le (R : ℕ) (a : ℕ → ℝ) :
    divisorJetCoeff R a 1 ^ 2 ≤
      4 * Real.log R * ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
  rw [divisorJetCoeff_one_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R)
    (fun m => a m * Real.sqrt (ArithmeticFunction.vonMangoldt m))
    (fun m => Real.sqrt (ArithmeticFunction.vonMangoldt m) / Real.sqrt (m.totient : ℝ))
  have hterm : ∀ m ∈ Icc 1 R, a m * (ArithmeticFunction.vonMangoldt m /
      Real.sqrt (m.totient : ℝ)) = a m * Real.sqrt (ArithmeticFunction.vonMangoldt m) *
        (Real.sqrt (ArithmeticFunction.vonMangoldt m) / Real.sqrt (m.totient : ℝ)) := by
    intro m _
    have := Real.mul_self_sqrt (ArithmeticFunction.vonMangoldt_nonneg (n := m))
    calc a m * (ArithmeticFunction.vonMangoldt m / Real.sqrt (m.totient : ℝ)) =
        a m * ((Real.sqrt (ArithmeticFunction.vonMangoldt m) *
          Real.sqrt (ArithmeticFunction.vonMangoldt m)) / Real.sqrt (m.totient : ℝ)) := by
          rw [this]
      _ = _ := by ring
  rw [sum_congr rfl hterm]
  refine hcs.trans ?_
  have h1 : (∑ m ∈ Icc 1 R, (a m * Real.sqrt (ArithmeticFunction.vonMangoldt m)) ^ 2) ≤
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
    refine sum_le_sum fun m hm => ?_
    rw [mul_pow, Real.sq_sqrt ArithmeticFunction.vonMangoldt_nonneg]
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := m)
    nlinarith [sq_nonneg (a m)]
  have h2 : (∑ m ∈ Icc 1 R, (Real.sqrt (ArithmeticFunction.vonMangoldt m) /
      Real.sqrt (m.totient : ℝ)) ^ 2) ≤ 4 * Real.log R := by
    have hsum := sum_Icc_vonMangoldt_div_le R
    calc _ = ∑ m ∈ Icc 1 R, ArithmeticFunction.vonMangoldt m / (m.totient : ℝ) := by
          refine sum_congr rfl fun m _ => ?_
          rw [div_pow, Real.sq_sqrt ArithmeticFunction.vonMangoldt_nonneg,
            Real.sq_sqrt (Nat.cast_nonneg _)]
      _ ≤ ∑ m ∈ Icc 1 R, 2 * (ArithmeticFunction.vonMangoldt m / m) :=
          sum_le_sum fun m _ => vonMangoldt_div_totient_le m
      _ = 2 * ∑ m ∈ Icc 1 R, ArithmeticFunction.vonMangoldt m / m := (mul_sum ..).symm
      _ ≤ 4 * Real.log R := by linarith
  have hG0 : 0 ≤ ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_nonneg fun m _ => mul_nonneg (by linarith [Real.log_natCast_nonneg m]) (sq_nonneg _)
  have hA0 : 0 ≤ ∑ m ∈ Icc 1 R, (a m * Real.sqrt (ArithmeticFunction.vonMangoldt m)) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ m ∈ Icc 1 R, (Real.sqrt (ArithmeticFunction.vonMangoldt m) /
      Real.sqrt (m.totient : ℝ)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc _ ≤ (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * (4 * Real.log R) :=
        mul_le_mul h1 h2 hB0 hG0
    _ = _ := by ring

/-- The floor amplitude of a conductor is at most `m²`. -/
theorem floorAmplitude_le_sq {m : ℕ} (hm : 0 < m) : floorAmplitude m ≤ (m : ℝ) ^ 2 := by
  unfold floorAmplitude
  have hφ1 : (1 : ℝ) ≤ Real.sqrt (m.totient : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.totient_pos.mpr hm
  have hnum : (∑ d ∈ m.divisors, |(ArithmeticFunction.moebius (m / d) : ℝ)| * (d : ℝ)) ≤
      (m : ℝ) ^ 2 := by
    calc _ ≤ ∑ d ∈ m.divisors, (m : ℝ) := by
          refine sum_le_sum fun d hd => ?_
          have hdm : (d : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hd
          have hμ : |(ArithmeticFunction.moebius (m / d) : ℝ)| ≤ 1 := by
            have := ArithmeticFunction.abs_moebius_le_one (n := m / d)
            exact_mod_cast this
          nlinarith [abs_nonneg ((ArithmeticFunction.moebius (m / d) : ℝ)),
            (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      _ = (m.divisors.card : ℝ) * m := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * m := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg m)
          exact_mod_cast Nat.card_divisors_le_self m
      _ = (m : ℝ) ^ 2 := by ring
  have h0 : 0 ≤ ∑ d ∈ m.divisors, |(ArithmeticFunction.moebius (m / d) : ℝ)| * (d : ℝ) :=
    sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem floorAmplitude_one : floorAmplitude 1 = 1 := by
  simp [floorAmplitude]

/-- **The pole mode against a band without its pole conductor.** For `ã = a` off `m = 1`,
`⟨ũ, v₁⟩ = −J₁/log N + Σ_m ã_m F(m)`, `F` the floor-harmonic Gram remainder. -/
theorem inner_reducedBand_poleMode {R N : ℕ} (hRN : R ≤ N) (hL : 0 < Real.log N) (a : ℕ → ℝ) :
    ⟪∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector 1 N⟫ =
      -divisorJetCoeff R a 1 / Real.log N +
        ∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N := by
  rw [sum_inner, divisorJetCoeff_one_eq, neg_div, sum_div, ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
  rw [real_inner_smul_left]
  by_cases h1 : m = 1
  · subst h1; simp
  · rw [if_neg h1, normalizedRamanujanHorizonVector_gram_exact hm1 one_pos (by omega) hL,
      if_neg h1, if_pos (one_dvd m), Nat.totient_one, Nat.cast_one, Nat.div_one, one_div,
      Real.sqrt_inv]
    ring

/-- The floor-harmonic remainder against the pole mode is `≤ 4m²/(N log N)`. -/
theorem abs_conductorGramFloorError_one_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (hL : 0 < Real.log N) :
    |conductorGramFloorError m 1 N| ≤ 4 * (m : ℝ) ^ 2 / (N * Real.log N) := by
  have h := abs_conductorGramFloorError_le hm one_pos (by omega) hL
  rw [floorAmplitude_one, mul_one] at h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine h.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  have := floorAmplitude_le_sq hm
  linarith

/-- The floor remainder `ε = Σ_m ã_m F(m)` has `ε² ≤ 16R⁵/(N² log² N) Σ a_m²`. -/
theorem floorRemainder_sq_le {R N : ℕ} (hRN : R ≤ N) (hL : 0 < Real.log N) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N) ^ 2 ≤
      16 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N ^ 2) * ∑ m ∈ Icc 1 R, a m ^ 2 := by
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hL; exact absurd hL (lt_irrefl 0)
      · exact h
    exact_mod_cast this
  set K := 4 * (R : ℝ) ^ 2 / (N * Real.log N) with hK
  have hε_abs : |∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N| ≤
      K * ∑ m ∈ Icc 1 R, |a m| := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
    have hF := abs_conductorGramFloorError_one_le hm1 (hmR.trans hRN) hL
    have hm2 : (m : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (by exact_mod_cast hmR) 2
    have hF' : |conductorGramFloorError m 1 N| ≤ K :=
      hF.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    rw [abs_mul]
    have ha : |(if m = 1 then 0 else a m)| ≤ |a m| := by split_ifs <;> simp
    calc _ ≤ |a m| * K := mul_le_mul ha hF' (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hsumabs : (∑ m ∈ Icc 1 R, |a m|) ^ 2 ≤ R * ∑ m ∈ Icc 1 R, a m ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Icc 1 R) (f := fun m => |a m|)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel, sq_abs] using this
  have h1 := pow_le_pow_left₀ (abs_nonneg _) hε_abs 2
  rw [sq_abs, mul_pow] at h1
  refine h1.trans ?_
  have hc2 : K ^ 2 = 16 * (R : ℝ) ^ 4 / ((N : ℝ) ^ 2 * Real.log N ^ 2) := by
    rw [hK]; field_simp; ring
  rw [hc2]
  calc _ ≤ 16 * (R : ℝ) ^ 4 / ((N : ℝ) ^ 2 * Real.log N ^ 2) * (R * ∑ m ∈ Icc 1 R, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hsumabs (by positivity)
    _ = _ := by field_simp

/-- **The coherent identity.** The exact pole term on the pole-free band `ũ` plus the pole
component `J₁⟨K₂ᵦ v₁, w⟩` of the jet equals
`J₁ (log N)^{-1/2} Σ_n w_n δ_n + P (log N)^{1/2} ε Σ_n w_n √n`, `δ` the row defect. -/
theorem coherentPolePair_eq (φ : ℝ → ℝ) (c : ℝ) {R N : ℕ} (hRN : R ≤ N) (hN2 : 2 ≤ N)
    (hL : 0 < Real.log N) (a : ℕ → ℝ) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw1 : w ∈ (conductorSubspace 1 N)ᗮ) :
    exactPoleCoefficient φ c N *
        (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, primeHorizonExtension w n *
          primeHorizonExtension (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) •
            normalizedRamanujanHorizonVector m N) j * arithmeticPoleKernel n j) +
      divisorJetCoeff R a 1 * ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N)
        (normalizedRamanujanHorizonVector 1 N), w⟫ =
      divisorJetCoeff R a 1 * (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension w n * poleRowDefect φ c N n) +
        exactPoleCoefficient φ c N * Real.sqrt (Real.log N) *
          (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N) *
          (∑ n ∈ Icc 1 N, primeHorizonExtension w n * Real.sqrt n) := by
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hsLsq : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
    Real.mul_self_sqrt hL.le
  have hWh := harmonicSum_eq_zero_of_mem_orthog_one hN2 hw1
  have h1 := inner_poleMode_eq (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) •
    normalizedRamanujanHorizonVector m N)
  rw [inner_reducedBand_poleMode hRN hL a] at h1
  have hhs : SelectiveMultiscaleArithmeticPositivity.harmonicSum N
      (primeHorizonExtension (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) •
        normalizedRamanujanHorizonVector m N)) =
      Real.sqrt (Real.log N) * (-divisorJetCoeff R a 1 / Real.log N +
        ∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N) := by
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hsL0.ne', one_mul]
  rw [poleKernel_bilinear_eq _ _ hWh, inner_nearJet_poleMode, hhs]
  have hsplit : (∑ n ∈ Icc 1 N, primeHorizonExtension w n * poleRowDefect φ c N n) =
      (∑ n ∈ Icc 1 N, primeHorizonExtension w n * nearPoleRow φ c N n) -
        exactPoleCoefficient φ c N * ∑ n ∈ Icc 1 N, primeHorizonExtension w n * Real.sqrt n := by
    unfold poleRowDefect
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit]
  generalize (∑ n ∈ Icc 1 N, primeHorizonExtension w n * nearPoleRow φ c N n) = Y
  generalize (∑ n ∈ Icc 1 N, primeHorizonExtension w n * Real.sqrt n) = X
  generalize (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N) = E
  generalize divisorJetCoeff R a 1 = J
  generalize exactPoleCoefficient φ c N = P
  obtain ⟨t, ht⟩ : ∃ t, Real.sqrt (Real.log N) = t := ⟨_, rfl⟩
  rw [ht] at hsLsq hsL0 ⊢
  rw [← hsLsq]
  field_simp
  ring

theorem coherent_sq_arith {J D P E X t : ℝ} (ht : 0 < t) :
    (J * t⁻¹ * D + P * t * E * X) ^ 2 ≤
      2 * (J ^ 2 * D ^ 2) / t ^ 2 + 2 * (P ^ 2 * t ^ 2 * E ^ 2 * X ^ 2) := by
  set x := J * t⁻¹ * D
  set y := P * t * E * X
  have h : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have e1 : x ^ 2 = J ^ 2 * D ^ 2 / t ^ 2 := by simp only [x]; field_simp
  have e2 : y ^ 2 = P ^ 2 * t ^ 2 * E ^ 2 * X ^ 2 := by simp only [y]; ring
  rw [e1, e2] at h
  have e3 : 2 * (J ^ 2 * D ^ 2 / t ^ 2) = 2 * (J ^ 2 * D ^ 2) / t ^ 2 := by ring
  linarith

/-- **The coherent pole pair.** For a band `u = Σ_{m ≤ R} a_m v_m` with pole-free part `ũ` and
`w ⊥ V_R`: `(P⟨Πũ, w⟩ + J₁⟨K₂ᵦ v₁, w⟩)² ≤ C((1 + log R)(1 + log c)/log N · Σ(1 + log m)a_m² +
c²R⁵/(N² log N) · Σ a_m²)‖w‖²`, with `P` the exact pole coefficient and `Π` the pole kernel. -/
theorem exists_coherentPolePair_sq_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c : ℝ}, 2 ≤ R → R ≤ N → 0 < Real.log N → 1 ≤ c →
      8 * c ≤ N → c ^ 4 ≤ N → ∀ (a : ℕ → ℝ) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w ∈ (conductorSubspace R N)ᗮ →
      (exactPoleCoefficient φ c N *
          (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, primeHorizonExtension w n *
            primeHorizonExtension (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) •
              normalizedRamanujanHorizonVector m N) j * arithmeticPoleKernel n j) +
        divisorJetCoeff R a 1 * ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N)
          (normalizedRamanujanHorizonVector 1 N), w⟫) ^ 2 ≤
      C * ((1 + Real.log R) * (1 + Real.log c) / Real.log N *
            ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 +
          c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N) * ∑ m ∈ Icc 1 R, a m ^ 2) *
        ‖w‖ ^ 2 := by
  obtain ⟨C_d, hCd, hdef⟩ := exists_sum_poleRowDefect_sq_le hφ hsupp hM
  obtain ⟨C_P, hCP, hP⟩ := exists_abs_exactPoleCoefficient_le hφ hsupp hM
  refine ⟨8 * C_d + 32 * C_P ^ 2, by positivity, ?_⟩
  intro R N c hR hRN hL hc1 h8 h4 a w hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  rw [coherentPolePair_eq φ c hRN hN2 hL a hw1]
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hsL2 : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL.le
  refine (coherent_sq_arith hsL0).trans ?_
  rw [hsL2]
  set J := divisorJetCoeff R a 1
  set D := ∑ n ∈ Icc 1 N, primeHorizonExtension w n * poleRowDefect φ c N n
  set P := exactPoleCoefficient φ c N
  set E := ∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) * conductorGramFloorError m 1 N
  set X := ∑ n ∈ Icc 1 N, primeHorizonExtension w n * Real.sqrt n
  set L := Real.log N
  set G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  set A := ∑ m ∈ Icc 1 R, a m ^ 2
  have hW2 : (∑ n ∈ Icc 1 N, primeHorizonExtension w n ^ 2) = ‖w‖ ^ 2 :=
    sum_primeHorizonExtension_sq w
  have hD2 : D ^ 2 ≤ ‖w‖ ^ 2 * (C_d * (1 + Real.log c)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (primeHorizonExtension w)
      (poleRowDefect φ c N)
    rw [hW2] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hdef hc1 h8 h4) (sq_nonneg _))
  have hX2 : X ^ 2 ≤ ‖w‖ ^ 2 * (N : ℝ) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (primeHorizonExtension w)
      (fun n => Real.sqrt n)
    rw [hW2] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    calc (∑ n ∈ Icc 1 N, Real.sqrt n ^ 2) = ∑ n ∈ Icc 1 N, (n : ℝ) :=
          sum_congr rfl fun n _ => Real.sq_sqrt (Nat.cast_nonneg n)
      _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) := sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
      _ = (N : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hG0 : 0 ≤ G := sum_nonneg fun m _ => mul_nonneg (by linarith [Real.log_natCast_nonneg m])
    (sq_nonneg _)
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hJ2 : J ^ 2 ≤ 4 * (1 + Real.log R) * G := by
    have h := divisorJetCoeff_one_sq_le R a
    have hlR := Real.log_natCast_nonneg R
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hG0)
  have hP2 : P ^ 2 ≤ C_P ^ 2 * c ^ 2 / (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hP hc0 hN1 (by rw [div_le_iff₀ hN0]; linarith)) 2
    rw [sq_abs] at h
    exact h.trans_eq (by field_simp)
  have hE2 : E ^ 2 ≤ 16 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L ^ 2) * A := floorRemainder_sq_le hRN hL a
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hlR0 : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hw0 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  -- first piece
  have hfirst : 2 * (J ^ 2 * D ^ 2) / L ≤
      8 * C_d * ((1 + Real.log R) * (1 + Real.log c) / L * G) * ‖w‖ ^ 2 := by
    have hprod : J ^ 2 * D ^ 2 ≤ (4 * (1 + Real.log R) * G) * (‖w‖ ^ 2 * (C_d * (1 + Real.log c))) :=
      mul_le_mul hJ2 hD2 (sq_nonneg _) (by positivity)
    have e : 8 * C_d * ((1 + Real.log R) * (1 + Real.log c) / L * G) * ‖w‖ ^ 2 =
        2 * ((4 * (1 + Real.log R) * G) * (‖w‖ ^ 2 * (C_d * (1 + Real.log c)))) / L := by
      field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hL.le
  -- second piece
  have hsecond : 2 * (P ^ 2 * L * E ^ 2 * X ^ 2) ≤
      32 * C_P ^ 2 * (c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 := by
    have h1 : P ^ 2 * L ≤ C_P ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * L :=
      mul_le_mul_of_nonneg_right hP2 hL.le
    have h2 : P ^ 2 * L * E ^ 2 ≤
        C_P ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * L * (16 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L ^ 2) * A) :=
      mul_le_mul h1 hE2 (sq_nonneg _) (by positivity)
    have h3 : P ^ 2 * L * E ^ 2 * X ^ 2 ≤
        C_P ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * L * (16 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L ^ 2) * A) *
          (‖w‖ ^ 2 * (N : ℝ) ^ 2) :=
      mul_le_mul h2 hX2 (sq_nonneg _) (by positivity)
    have e : 32 * C_P ^ 2 * (c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 =
        2 * (C_P ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * L * (16 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L ^ 2) * A) *
          (‖w‖ ^ 2 * (N : ℝ) ^ 2)) := by
      field_simp; ring
    rw [e]; linarith
  have hT1 : 0 ≤ (1 + Real.log R) * (1 + Real.log c) / L * G := by positivity
  have hT2 : 0 ≤ c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A := by positivity
  have e3 : (8 * C_d + 32 * C_P ^ 2) * ((1 + Real.log R) * (1 + Real.log c) / L * G +
      c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 =
      8 * C_d * ((1 + Real.log R) * (1 + Real.log c) / L * G) * ‖w‖ ^ 2 +
        32 * C_P ^ 2 * (c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 +
        (8 * C_d * (c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 +
          32 * C_P ^ 2 * ((1 + Real.log R) * (1 + Real.log c) / L * G) * ‖w‖ ^ 2) := by ring
  have h5 : 0 ≤ 8 * C_d * (c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * L) * A) * ‖w‖ ^ 2 +
      32 * C_P ^ 2 * ((1 + Real.log R) * (1 + Real.log c) / L * G) * ‖w‖ ^ 2 := by positivity
  rw [e3]
  linarith

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
