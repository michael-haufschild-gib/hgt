import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy
import GaloisForLFunctions.RHTower.WeilPoleWeightForcedOne
import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral
import GaloisForLFunctions.RHTower.MarkovSpectralSecondMomentAndHalfL2SurplusPBAP

/-!
# The (pole, arch) moment region of blind positive-definite tests

For a nonnegative combination `c` of autocorrelations of `C²_c` tests, blind at every `±log n`
(`n ≥ 2`), put `P(c)` (pole term), `A_∞(c)` (archimedean term) and `N(c) = Σ c_f ‖f‖²` (the value
`g(0)`).  The moment region is `K = {(P/N, A_∞/N)}` (`momentRegion`).

* `K` is convex (`convex_momentRegion`) and lies in `{A_∞/N ≥ Ω(0)}` (`momentRegion_subset`,
  from `Ω ≥ Ω(0)` and Plancherel).
* Prime-blind positivity — equivalently RH — says exactly that `K` lies above the line
  `q = −p` (`primeBlindPositive_iff_momentRegion`, `riemannHypothesis_iff_momentRegion`), and then
  so does its closure.
* Under RH the null edge is approached from both sides of `p = 0`: for every `ε > 0` there are
  points of `K` with `p < 0` and with `p > 0` whose distance `q + p` above the line is below
  `ε|p|` (`exists_mem_momentRegion_pole_neg_of_riemannHypothesis`, `…_pos_…`).
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real
open Zeta23

namespace RHTower.BlindMomentRegion

open WeilOneSided

noncomputable section

/-- The pole term `Re(k̂(i/2) + k̂(−i/2))` of `k = f ⋆ f̃`. -/
def poleOf (f : WeilTestFn) : ℝ :=
  (paperFT (EF.weilTest f.1 f.1) (I / 2) + paperFT (EF.weilTest f.1 f.1) (-I / 2)).re

/-- The archimedean term `(1/2π) ∫ k̂ Ω`. -/
def archOf (f : WeilTestFn) : ℝ :=
  ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f.1 f.1) r * (EF.gammaBracket r : ℂ)).re

/-- The mass `‖f‖² = k(0)`. -/
def massOf (f : WeilTestFn) : ℝ := ∫ u, ‖f.1 u‖ ^ 2

theorem weilArchRe_eq (f : WeilTestFn) : weilArchRe (EF.weilTest f.1 f.1) = poleOf f + archOf f := by
  rw [weilArchRe, poleOf, archOf, Complex.add_re]

/-- Blindness of a combination at every `±log n`, `n ≥ 2`. -/
def IsBlind (c : WeilTestFn →₀ ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → linearCombination ℝ (fun f : WeilTestFn => logValue f.1 n) c = 0

/-- The moment region `{(P/N, A_∞/N)}`. -/
def momentRegion : Set (ℝ × ℝ) :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ IsBlind c ∧
    0 < linearCombination ℝ massOf c ∧
    x = (linearCombination ℝ poleOf c / linearCombination ℝ massOf c,
      linearCombination ℝ archOf c / linearCombination ℝ massOf c)}

theorem sum_eq_linearCombination (c : WeilTestFn →₀ ℝ) (g : WeilTestFn → ℝ) :
    (c.sum fun f t => t * g f) = linearCombination ℝ g c := by
  rw [linearCombination_apply]; simp only [smul_eq_mul]

/-- **Convexity.** -/
theorem convex_momentRegion : Convex ℝ momentRegion := by
  rintro x ⟨c₁, hc₁, hb₁, hN₁, rfl⟩ y ⟨c₂, hc₂, hb₂, hN₂, rfl⟩ a b ha hb hab
  set N₁ := linearCombination ℝ massOf c₁
  set N₂ := linearCombination ℝ massOf c₂
  refine ⟨(a / N₁) • c₁ + (b / N₂) • c₂, fun f => ?_, fun n hn => ?_, ?_, ?_⟩
  · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (div_nonneg ha hN₁.le) (hc₁ f))
      (mul_nonneg (div_nonneg hb hN₂.le) (hc₂ f))
  · rw [map_add, map_smul, map_smul, hb₁ n hn, hb₂ n hn, smul_zero, smul_zero, add_zero]
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, div_mul_cancel₀ _ hN₁.ne',
      div_mul_cancel₀ _ hN₂.ne', hab]
    exact one_pos
  · rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [div_mul_cancel₀ _ hN₁.ne', div_mul_cancel₀ _ hN₂.ne', hab, div_one, div_one]
    ext <;> simp <;> ring

/-- `A_∞(f) ≥ Ω(0) ‖f‖²`. -/
theorem gammaBracket_zero_mul_massOf_le (f : WeilTestFn) :
    EF.gammaBracket 0 * massOf f ≤ archOf f := by
  have hf := f.2.1
  have hfc := f.2.2
  have hpt : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc]; push_cast; ring
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
  have hintR : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest f.1 f.1) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hpt, Complex.ofReal_re]
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := RHTower.integrable_paperFT_norm_sq f
  have hplan := LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf hfc
  have harch : archOf f = 1 / (2 * π) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r := by
    rw [archOf]
    simp_rw [hpt]
    rw [integral_complex_ofReal, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [harch, massOf, ← hplan]
  have hmono : ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket 0 ≤
      ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r :=
    integral_mono (hsq.mul_const _) hintR fun r =>
      mul_le_mul_of_nonneg_left (ArchimedeanAnomaly.gammaBracket_zero_le r) (sq_nonneg _)
  rw [integral_mul_const] at hmono
  have hpos : 0 ≤ 1 / (2 * π) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hpos]

/-- **`K ⊆ {q ≥ Ω(0)}`.** -/
theorem momentRegion_subset {x : ℝ × ℝ} (hx : x ∈ momentRegion) : EF.gammaBracket 0 ≤ x.2 := by
  obtain ⟨c, hc, -, hN, rfl⟩ := hx
  simp only
  rw [le_div_iff₀ hN]
  rw [← sum_eq_linearCombination, ← sum_eq_linearCombination, Finsupp.sum, Finsupp.sum,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun f _ => by
    have := mul_le_mul_of_nonneg_left (gammaBracket_zero_mul_massOf_le f) (hc f)
    linarith

theorem massOf_eq_zero {f : WeilTestFn} (h : massOf f = 0) : f.1 = 0 := by
  have hc : Continuous fun u => ‖f.1 u‖ ^ 2 := f.2.1.continuous.norm.pow 2
  have hint : Integrable fun u => ‖f.1 u‖ ^ 2 :=
    hc.integrable_of_hasCompactSupport (f.2.2.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hint).mp h
  have heq : (fun u => ‖f.1 u‖ ^ 2) = fun _ => (0 : ℝ) :=
    Continuous.ae_eq_iff_eq volume hc continuous_const |>.mp hae
  funext u
  have := congrFun heq u
  simpa using this

theorem weilArchRe_eq_zero_of_massOf {f : WeilTestFn} (h : massOf f = 0) :
    weilArchRe (EF.weilTest f.1 f.1) = 0 := by
  have h0 := massOf_eq_zero h
  have hk : EF.weilTest f.1 f.1 = 0 := by
    rw [h0]; funext x; simp [EF.weilTest, convolution_def]
  rw [hk, weilArchRe]
  simp [paperFT]

theorem linearCombination_weilArchRe (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c =
      linearCombination ℝ poleOf c + linearCombination ℝ archOf c := by
  rw [← sum_eq_linearCombination, ← sum_eq_linearCombination, ← sum_eq_linearCombination,
    ← Finsupp.sum_add]
  congr 1
  funext f t
  rw [weilArchRe_eq]
  ring

theorem massOf_nonneg (f : WeilTestFn) : 0 ≤ massOf f := integral_nonneg fun _ => sq_nonneg _

theorem linearCombination_mass_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) :
    0 ≤ linearCombination ℝ massOf c := by
  rw [← sum_eq_linearCombination]
  exact Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (massOf_nonneg f)

/-- A massless nonnegative combination carries no pole and no archimedean energy. -/
theorem eq_zero_of_mass_eq_zero {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hN : linearCombination ℝ massOf c = 0) (g : WeilTestFn → ℝ)
    (hg : ∀ f : WeilTestFn, f.1 = 0 → g f = 0) : linearCombination ℝ g c = 0 := by
  rw [← sum_eq_linearCombination] at hN ⊢
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun f _ => mul_nonneg (hc f) (massOf_nonneg f)).mp hN
  refine Finset.sum_eq_zero fun f hf => ?_
  simp only
  rcases mul_eq_zero.mp (hterm f hf) with h | h
  · rw [h, zero_mul]
  · rw [hg f (massOf_eq_zero h), mul_zero]

theorem poleOf_eq_zero {f : WeilTestFn} (h : f.1 = 0) : poleOf f = 0 := by
  have hk : EF.weilTest f.1 f.1 = 0 := by rw [h]; funext x; simp [EF.weilTest, convolution_def]
  rw [poleOf, hk]; simp [paperFT]

theorem archOf_eq_zero {f : WeilTestFn} (h : f.1 = 0) : archOf f = 0 := by
  have hk : EF.weilTest f.1 f.1 = 0 := by rw [h]; funext x; simp [EF.weilTest, convolution_def]
  rw [archOf, hk]; simp [paperFT]

/-- **PBAP is the moment region lying above `q = −p`.** -/
theorem primeBlindPositive_iff_momentRegion :
    WeilOneSided.PrimeBlindPositive ↔ ∀ x ∈ momentRegion, -x.1 ≤ x.2 := by
  constructor
  · rintro hP x ⟨c, hc, hb, hN, rfl⟩
    have h := hP c hc fun n hn => by rw [sum_eq_linearCombination]; exact hb n hn
    rw [sum_eq_linearCombination, linearCombination_weilArchRe] at h
    simp only
    rw [neg_le_iff_add_nonneg, ← add_div]
    exact div_nonneg (by linarith) hN.le
  · intro hK c hc hnull
    rw [sum_eq_linearCombination, linearCombination_weilArchRe]
    have hb : IsBlind c := fun n hn => by rw [← sum_eq_linearCombination]; exact hnull n hn
    rcases (linearCombination_mass_nonneg hc).lt_or_eq with hN | hN
    · have h := hK _ ⟨c, hc, hb, hN, rfl⟩
      simp only at h
      rw [neg_le_iff_add_nonneg, ← add_div] at h
      exact (div_nonneg_iff.mp h).elim (fun h => by linarith [h.1])
        fun h => absurd h.2 (not_le.mpr hN)
    · rw [eq_zero_of_mass_eq_zero hc hN.symm poleOf fun f h => poleOf_eq_zero h,
        eq_zero_of_mass_eq_zero hc hN.symm archOf fun f h => archOf_eq_zero h, add_zero]

/-- **RH is the moment region lying above `q = −p`.** -/
theorem riemannHypothesis_iff_momentRegion :
    RiemannHypothesis ↔ ∀ x ∈ momentRegion, -x.1 ≤ x.2 :=
  riemannHypothesis_iff_primeBlindPositive_unconditional.trans primeBlindPositive_iff_momentRegion

/-- Under RH the closure of `K` also lies above `q = −p`. -/
theorem closure_momentRegion_of_riemannHypothesis (hRH : RiemannHypothesis) {x : ℝ × ℝ}
    (hx : x ∈ closure momentRegion) : -x.1 ≤ x.2 := by
  have hcl : IsClosed {x : ℝ × ℝ | -x.1 ≤ x.2} :=
    isClosed_le (continuous_fst.neg) continuous_snd
  exact closure_minimal (fun y hy => riemannHypothesis_iff_momentRegion.mp hRH y hy) hcl hx

theorem mass_pos_of_pole_ne {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hP : linearCombination ℝ poleOf c ≠ 0) : 0 < linearCombination ℝ massOf c := by
  rcases (linearCombination_mass_nonneg hc).lt_or_eq with hN | hN
  · exact hN
  · exact absurd (eq_zero_of_mass_eq_zero hc hN.symm poleOf fun f h => poleOf_eq_zero h) hP

/-- **The null edge toward negative pole** (`c* = 0` under RH): for every `ε > 0` some point of `K`
has `p < 0` and `0 ≤ q + p < ε|p|`. -/
theorem exists_mem_momentRegion_pole_neg_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) : ∃ x ∈ momentRegion, x.1 < 0 ∧ 0 ≤ x.1 + x.2 ∧ x.1 + x.2 < ε * |x.1| := by
  obtain ⟨c, hc, hnull, hP, hA0, hA⟩ := exists_blind_pole_neg_of_riemannHypothesis hRH hε
  have hpole : (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) =
      linearCombination ℝ poleOf c := sum_eq_linearCombination c poleOf
  rw [hpole] at hP hA
  rw [sum_eq_linearCombination, linearCombination_weilArchRe] at hA0 hA
  have hN := mass_pos_of_pole_ne hc hP.ne
  refine ⟨_, ⟨c, hc, fun n hn => by rw [← sum_eq_linearCombination]; exact hnull n hn, hN, rfl⟩,
    div_neg_of_neg_of_pos hP hN, ?_, ?_⟩
  · simp only; rw [← add_div]; exact div_nonneg hA0 hN.le
  · simp only
    rw [← add_div, abs_div, abs_of_pos hN, ← mul_div_assoc, div_lt_div_iff_of_pos_right hN]
    exact hA

/-- **The null edge toward positive pole** (`κ₊ = 0` under RH). -/
theorem exists_mem_momentRegion_pole_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) : ∃ x ∈ momentRegion, 0 < x.1 ∧ 0 ≤ x.1 + x.2 ∧ x.1 + x.2 < ε * x.1 := by
  obtain ⟨c, hc, hnull, hP, hA0, hA⟩ := exists_blind_pole_pos_of_riemannHypothesis hRH hε
  have hpole : (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) =
      linearCombination ℝ poleOf c := sum_eq_linearCombination c poleOf
  rw [hpole] at hP hA
  rw [sum_eq_linearCombination, linearCombination_weilArchRe] at hA0 hA
  have hN := mass_pos_of_pole_ne hc hP.ne'
  refine ⟨_, ⟨c, hc, fun n hn => by rw [← sum_eq_linearCombination]; exact hnull n hn, hN, rfl⟩,
    div_pos hP hN, ?_, ?_⟩
  · simp only; rw [← add_div]; exact div_nonneg hA0 hN.le
  · simp only
    rw [← add_div, ← mul_div_assoc, div_lt_div_iff_of_pos_right hN]
    exact hA

end

end RHTower.BlindMomentRegion
