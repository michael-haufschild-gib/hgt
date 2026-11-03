import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheDominationQuestionIsFirstOrder
import GaloisForLFunctions.ArithmeticCriticalityTheory.EvenWindowShiftedPairSelectivity
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions

/-!
# The Tate twist is the shifted pair

On a window the Tate flow is conjugation by `e^{kM}` (WTZ): the Tate twist `f ↦ f·n^{−k}` of an
arithmetic function is implemented by the exponential gauge `e^{ku}`. The **symmetric** reading of
dimension `k` is Weil's pairing of the two Tate twists of a test,

`Q^{(k)}(H) = W(e^{k·}H, e^{−k·}H)` (`tateTwistedForm`).

* **The Tate twist tilts the autocorrelation** (`weilTest_tateTwist`): the cross-correlation of
  `e^{k·}H` and `e^{−k·}H` is `e^{kx}` times the autocorrelation of `H`. On the jump measure
  `ω(t)dt + Σ Λ(n)n^{−1/2}δ_{log n}` this is exponential tilting (the Esscher transform): archimedean
  jumps and prime jumps of length `t` are reweighted by the same factor.
* **Lorentz form** (`tateTwistedForm_eq`): `Q^{(k)}(H) = Q(H cosh(k·)) − Q(H sinh(k·))`; the value at
  dimension zero is Weil's form (`tateTwistedForm_zero`), and the family is even in `k`
  (`tateTwistedForm_neg`) and translation invariant (`tateTwistedForm_comp_sub`).
* **It is the shifted pair** (`tateTwistedForm_eq_half_shiftedPairZeroForm`):
  `Q^{(k)} = ½ Ẑ_k`, the zero form of `Λ(s − k)Λ(s + k)`, whose zeros `ρ ± k` lie off the critical
  line. Symmetric Tate dimension is the depth of a fake.
* **Positivity does not survive into positive symmetric dimension** (`exists_window_tateTwistedForm_neg`,
  `shortWindow_tateTwisted_dichotomy`): on every window of positive length the twisted form is
  negative on some test in every large dimension (ACT's even selectivity of the shifted pair), while
  on windows of length `≤ 3/5` it is coercive at dimension zero. No positivity in large symmetric Tate
  dimension is available to descend to `k = 0`; dimension zero is a critical point of the family, not
  the limit of a positive one.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23 ComplexConjugate

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis

/-- The **Tate-twisted Weil pairing** `Q^{(k)}(H) = W(e^{k·}H, e^{−k·}H)`. -/
def tateTwistedForm (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  weilPair (fun u => H u * Real.exp (k * u)) (fun u => H u * Real.exp (-(k * u)))

/-- **The Tate twist tilts the autocorrelation**: `(e^{k·}H ⋆ e^{−k·}H)(x) = e^{kx}(H ⋆ H)(x)`. -/
theorem weilTest_tateTwist (H : ℝ → ℝ) (k x : ℝ) :
    EF.weilTest (cx fun u => H u * Real.exp (k * u)) (cx fun u => H u * Real.exp (-(k * u))) x =
      (Real.exp (k * x) : ℂ) * EF.weilTest (cx H) (cx H) x := by
  rw [RHTower.weilTest_apply, RHTower.weilTest_apply, ← integral_const_mul]
  congr 1
  funext u
  have he : Real.exp (k * u) * Real.exp (-(k * (u - x))) = Real.exp (k * x) := by
    rw [← Real.exp_add]; ring_nf
  have hr : H u * Real.exp (k * u) * (H (u - x) * Real.exp (-(k * (u - x)))) =
      Real.exp (k * x) * (H u * H (u - x)) := by
    rw [← he]; ring
  simp only [cx, Complex.conj_ofReal]
  exact_mod_cast hr

theorem mul_mem_realTests {H : ℝ → ℝ} (hH : H ∈ realTests) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    (fun u => H u * φ u) ∈ realTests :=
  ⟨hH.1.mul hφ, hH.2.mul_right⟩

/-- **Lorentz form of the twisted pairing**: `Q^{(k)}(H) = Q(H cosh(k·)) − Q(H sinh(k·))`. -/
theorem tateTwistedForm_eq {H : ℝ → ℝ} (hH : H ∈ realTests) (k : ℝ) :
    tateTwistedForm k H = weilQuad (fun u => H u * Real.cosh (k * u)) -
      weilQuad (fun u => H u * Real.sinh (k * u)) := by
  have hcm : (fun u => H u * Real.cosh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  have hsm : (fun u => H u * Real.sinh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  set c : ℝ → ℝ := fun u => H u * Real.cosh (k * u) with hc
  set s : ℝ → ℝ := fun u => H u * Real.sinh (k * u) with hs
  have hsm' : (-1 : ℝ) • s ∈ realTests := realTests.smul_mem _ hsm
  have hp : (fun u => H u * Real.exp (k * u)) = c + s := by
    funext u; simp only [hc, hs, Pi.add_apply, ← Real.cosh_add_sinh]; ring
  have hm : (fun u => H u * Real.exp (-(k * u))) = c + (-1 : ℝ) • s := by
    funext u
    simp only [hc, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Real.cosh_sub_sinh]
    ring
  have hcs : c + (-1 : ℝ) • s ∈ realTests := realTests.add_mem hcm hsm'
  rw [tateTwistedForm, hp, hm, weilPair_add_left hcm hsm hcs, weilPair_comm c,
    weilPair_comm s, weilPair_add_left hcm hsm' hcm, weilPair_add_left hcm hsm' hsm,
    weilPair_smul_left, weilPair_smul_left, weilPair_comm s c]
  show _ = weilPair c c - weilPair s s
  ring

/-- At dimension zero the twisted pairing is Weil's form. -/
theorem tateTwistedForm_zero (H : ℝ → ℝ) : tateTwistedForm 0 H = weilQuad H := by
  simp only [tateTwistedForm, zero_mul, neg_zero, Real.exp_zero, mul_one]
  rfl

/-- The twisted pairing is even in the dimension. -/
theorem tateTwistedForm_neg (k : ℝ) (H : ℝ → ℝ) : tateTwistedForm (-k) H = tateTwistedForm k H := by
  simp only [tateTwistedForm, neg_mul, neg_neg]
  exact weilPair_comm _ _

/-- Weil's pairing is translation invariant. -/
theorem weilPair_comp_sub (f g : ℝ → ℝ) (c : ℝ) :
    weilPair (fun u => f (u - c)) (fun u => g (u - c)) = weilPair f g := by
  unfold weilPair
  have h : EF.weilTest (cx fun u => f (u - c)) (cx fun u => g (u - c)) =
      EF.weilTest (cx f) (cx g) := by
    funext y
    have := weilTest_translate c c (cx f) (cx g) y
    simp only [sub_self, sub_zero] at this
    exact this
  rw [h]

/-- The twisted pairing is translation invariant: the gauge factors `e^{±kc}` cancel. -/
theorem tateTwistedForm_comp_sub {H : ℝ → ℝ} (k c : ℝ) :
    tateTwistedForm k (fun u => H (u - c)) = tateTwistedForm k H := by
  set F : ℝ → ℝ := fun u => H u * Real.exp (k * u) with hFdef
  set G : ℝ → ℝ := fun u => H u * Real.exp (-(k * u)) with hGdef
  have hF : (fun u => H (u - c) * Real.exp (k * u)) = Real.exp (k * c) • fun u => F (u - c) := by
    funext u
    simp only [hFdef, Pi.smul_apply, smul_eq_mul]
    rw [show k * u = k * c + k * (u - c) by ring, Real.exp_add]
    ring
  have hG : (fun u => H (u - c) * Real.exp (-(k * u))) =
      Real.exp (-(k * c)) • fun u => G (u - c) := by
    funext u
    simp only [hGdef, Pi.smul_apply, smul_eq_mul]
    rw [show -(k * u) = -(k * c) + -(k * (u - c)) by ring, Real.exp_add]
    ring
  show weilPair (fun u => H (u - c) * Real.exp (k * u)) (fun u => H (u - c) * Real.exp (-(k * u)))
    = weilPair F G
  rw [hF, hG, weilPair_smul_left, weilPair_comm, weilPair_smul_left, weilPair_comm,
    weilPair_comp_sub, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **The Tate-twisted pairing is half the zero form of the shifted pair** `Λ(s − k)Λ(s + k)`. -/
theorem tateTwistedForm_eq_half_shiftedPairZeroForm {H : ℝ → ℝ} (hH : H ∈ realTests) (k : ℝ) :
    tateTwistedForm k H = ArithmeticIncidencePositivity.shiftedPairZeroForm k H / 2 := by
  have hcm : (fun u => H u * Real.cosh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  have hsm : (fun u => H u * Real.sinh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  rw [tateTwistedForm_eq hH, ArithmeticIncidencePositivity.shiftedPairZeroForm,
    ← LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm hcm,
    ← LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm hsm]
  show _ = 2 * (weilPair _ _ - weilPair _ _) / 2
  rw [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
  rfl

theorem mem_realTests_of_isWindowTest {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    H ∈ realTests :=
  ⟨hH.contDiff, hH.hasCompactSupport⟩

/-- **Positivity fails in large symmetric Tate dimension on every window.** For every window length
`A > 0` there is `k₀` such that in every dimension `k ≥ k₀` some window test has `Q^{(k)}(H) < 0`. -/
theorem exists_window_tateTwistedForm_neg {A : ℝ} (hA : 0 < A) :
    ∃ k₀ : ℝ, ∀ k, k₀ ≤ k → ∃ H : ℝ → ℝ, IsWindowTest A H ∧ tateTwistedForm k H < 0 := by
  obtain ⟨a₀, ha₀⟩ := ArithmeticCriticalityTheory.exists_even_shiftedPairZeroForm_neg
    (half_pos hA)
  refine ⟨a₀, fun k hk => ?_⟩
  obtain ⟨F, hFd, hFc, -, hFs, hneg⟩ := ha₀ k hk
  refine ⟨fun u => F (u - -(A / 2)), ⟨hFd.comp (contDiff_id.sub contDiff_const), fun y hy => ?_⟩, ?_⟩
  · refine hFs _ ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl (by linarith))
  · rw [tateTwistedForm_comp_sub, tateTwistedForm_eq_half_shiftedPairZeroForm ⟨hFd, hFc⟩]
    linarith

/-- **Dichotomy on short windows.** On a window of length `0 < A ≤ 3/5` the twisted pairing is
coercive at dimension zero, `Q^{(0)}(H) ≥ ‖H‖²/5000`, and negative on some test in every large
dimension. -/
theorem shortWindow_tateTwisted_dichotomy {A : ℝ} (hA : 0 < A) (hA' : A ≤ 3 / 5) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → (1 / 5000 : ℝ) * (∫ u, H u ^ 2) ≤ tateTwistedForm 0 H) ∧
      ∃ k₀ : ℝ, ∀ k, k₀ ≤ k → ∃ H : ℝ → ℝ, IsWindowTest A H ∧ tateTwistedForm k H < 0 := by
  refine ⟨fun H hH => ?_, exists_window_tateTwistedForm_neg hA⟩
  set G : ℝ → ℝ := fun u => H (u - A / 2)
  have hG : G ∈ realTests := ⟨hH.contDiff.comp (contDiff_id.sub contDiff_const),
    HasCompactSupport.intro (isCompact_Icc (a := A / 2 - A) (b := A / 2)) fun u hu =>
      hH.vanish _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  have hsupp : tsupport G ⊆ Icc (-(3 / 10)) (3 / 10) := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - A / 2 ∈ Icc (-A) 0 := by
      by_contra h; exact hu (hH.vanish _ h)
    exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  have h := LatticeSectionTheory.WindowJumpCounts.weilPair_ge_of_le_threeTenths hG hsupp le_rfl
  have hn : (∫ u, G u ^ 2) = ∫ u, H u ^ 2 := integral_sub_right_eq_self (fun u => H u ^ 2) (A / 2)
  have hq : weilPair G G = weilQuad H := weilQuad_comp_sub H (A / 2)
  rw [tateTwistedForm_zero, ← hq, ← hn]
  exact h

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
