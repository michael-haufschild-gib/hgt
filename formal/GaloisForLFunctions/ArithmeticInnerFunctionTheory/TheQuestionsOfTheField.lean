import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheOuterPredictorReplacesTheGroundState
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheDatumIsTheSzegoThreshold
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheArithmeticBernsteinTheorem
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.PhaseLockingIsTorusPositivity
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.InverseScatteringWithPrimeData
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.EchoTrainsOnIndependentReflectors
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheEulerColumnsOfTheInnerField
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheZeroOneLawOfRecurrence
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowReadsTheResidue
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheForwardMapFromPrimesToReflectors
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.NearExtremalMollifiersAreRigid
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCalculusOfEulerColumns
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.CastelnuovoConstructsTheMollifierOfACurve
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ThePotentialPastTheBornRegime

/-!
# The questions of the field

The questions of the programme, each with the theorem that answers it. None of them produces a sign for `Spec ℤ`: each equivalence with RH is
stated as an equivalence.

* **When is a frustrated form nonnegative at zero slack?** (`question_one`, `question_one_specZ`) Exactly when, for every positive slack, its windows have outer predictors with positive margins. At slack zero
  the predictor is still outer on each positive window, with margins that tend to `0` for `Spec ℤ`.
* **What replaces Allegretto–Piepenbrink?** (`question_two`) The causal solution: zero-free in the closed disc in place of positive. On
  nonpositive couplings it is the positive supersolution; and it carries a Riemann hypothesis in every window.
* **Which cones are invariant under prime insertion with locked phases?** (`question_three`) The exponentially convex cone is invariant, and among amplitudes of left exponent below `½` it is the only cone
  on which all insertions at all prime sets and locked phases stay nonnegative.
* **When is an echo train passive?** (`question_four`) When each echo lies in its Schur band, and these bands are free coordinates. On independent reflectors size is exact; on commensurable
  reflectors the mass is unbounded.
* **Why is `(β, s) = (1, 0)` critical?** (`question_five`) `s` is an absolutely continuous density over a measure with no such density: `s > 0` is Szegő, `s < 0` is empty,
  and `s = 0` is the threshold, which is RH for all lattices. `β ≠ 1` loses the rigidity of the weights.
* **Can an arithmetic inner factor be finite and nontrivial?** (`question_six`) For a polynomial yes, for a Dirichlet polynomial never, and for `ζ` the answer is the second half of RH: inner field vanishing at infinity and recurrence.
* **How do reflectors depend on primes past the first echo?** (`question_seven`) Through the autocorrelation of the predictor test at `log n₀`: the tangent of the forward map is exact at every stage.
* **What plays the role of Castelnuovo?** (`question_eight`, `question_eight_curve`) Not the construction of a mollifier: its limit is forced to be `1/E`, with first coefficient `1 − γ`. Over a curve the family is the Euler logarithm damped by `ρ^k`, and Castelnuovo is the uniform bound on the dilation quotient that makes it near-extremal. Over `ℤ` that bound is the missing input.
* **How does the Gamma base pay the columns?** (`question_nine`) By size up to `log(b/2π) > 14√P log P`, and at each height of alignment `[B, BQ^{|S|}]` it has to exceed the aligned mass.
* **How does the potential depend on the data past the Born regime?** (`question_ten`) At the vacuum each reflector reads its own echo. In general the defect is bounded by the accumulated reflection `Π(1 + |γ_k|) − 1`, and the tangent of `q_n = −artanh γ_n` is exact at every positive stage.
-/

open Finset Filter Topology Set

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis Zeta23 _root_.RHTower

noncomputable section

variable {κ : ℤ → ℝ}

/-- A form is nonnegative iff all its positive slacks are positive definite. -/
theorem toeplitzForm_nonneg_iff_slack :
    (∀ n x, 0 ≤ toeplitzForm κ n x) ↔ ∀ s > 0, ∀ n, ToeplitzPosDef (withSlack κ s) (n + 1) := by
  constructor
  · intro h s hs n x hx
    rw [toeplitzForm_withSlack]
    have h1 : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by
        have : x i ≠ 0 := hi
        positivity⟩
    have := h (n + 1) x
    positivity
  · intro h n x
    by_contra hneg
    push Not at hneg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [toeplitzForm] at hneg
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set S := ∑ i, x i ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hSpos : 0 < S := by
      by_contra hS1
      have hS2 : S = 0 := le_antisymm (not_lt.mp hS1) hS0
      have hx0 : x = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).mp hS2 i (Finset.mem_univ i)
        simpa using this
      rw [hx0] at hneg
      simp [toeplitzForm] at hneg
    set s : ℝ := -toeplitzForm κ (m + 1) x / (2 * S) with hs
    have hspos : 0 < s := div_pos (by linarith) (by positivity)
    have hx : x ≠ 0 := fun h0 => by
      rw [h0] at hneg
      simp [toeplitzForm] at hneg
    have h1 := h s hspos m x hx
    rw [toeplitzForm_withSlack] at h1
    have h2 : s * S = -toeplitzForm κ (m + 1) x / 2 := by
      rw [hs]
      field_simp
    rw [← hS, h2] at h1
    linarith

/-- **Q1. A frustrated form is nonnegative iff every positive slack has outer predictors**: for every sign pattern. -/
theorem question_one (hκ : IsEvenSeq κ) :
    (∀ n, ToeplitzPosDef κ (n + 1) ↔ ∃ a : Fin n → ℝ, IsPredictor κ n a ∧ 0 < predErr κ n a ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) ∧
      ((∀ n x, 0 ≤ toeplitzForm κ n x) ↔ ∀ s > 0, ∀ n, ∃ a : Fin n → ℝ,
        IsPredictor (withSlack κ s) n a ∧ 0 < predErr (withSlack κ s) n a ∧
          ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) := by
  refine ⟨toeplitzPosDef_iff_exists_outer_predictor hκ, ?_⟩
  rw [toeplitzForm_nonneg_iff_slack]
  refine forall_congr' fun s => forall_congr' fun _ => forall_congr' fun n => ?_
  exact toeplitzPosDef_iff_exists_outer_predictor (withSlack_isEven hκ s) n

/-- **Q1 for `Spec ℤ`.** RH is the statement that every lattice has outer predictors, with reflection data
that are not square-summable and no room for negative slack. So the form is nonnegative at zero slack with vanishing innovation. -/
theorem question_one_specZ :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
      (∀ n : ℕ, ∃ a : Fin n → ℝ, IsPredictor (weilSeq φ h) n a ∧ 0 < predErr (weilSeq φ h) n a ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) ∧
      ¬Summable (fun k => reflCoeff (weilSeq φ h) k ^ 2) ∧
      ∀ s < 0, ∃ (n : ℕ) (x : Fin n → ℝ), toeplitzForm (withSlack (weilSeq φ h) s) n x < 0 := by
  rw [riemannHypothesis_iff_every_lattice_is_at_threshold]
  refine forall_congr' fun φ => forall_congr' fun hφ => forall_congr' fun _ =>
    forall_congr' fun h => forall_congr' fun hh => ?_
  have hκ := weilSeq_isEven φ h
  constructor
  · rintro ⟨hE, -, hns, hneg⟩
    exact ⟨fun n => (toeplitzPosDef_iff_exists_outer_predictor hκ n).mp
      ((toeplitzForm_posDef_iff hκ n).mpr fun k _ => hE k), hns, hneg⟩
  · rintro ⟨hP, hns, hneg⟩
    have hE : ∀ n, 0 < levinsonErr (weilSeq φ h) n := fun n =>
      (toeplitzForm_posDef_iff hκ n).mp
        ((toeplitzPosDef_iff_exists_outer_predictor hκ n).mpr (hP n)) n le_rfl
    refine ⟨hE, fun s hs => ?_, hns, hneg⟩
    have hT : ∀ n x, 0 ≤ toeplitzForm (weilSeq φ h) n x := by
      intro n x
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [toeplitzForm]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      by_cases hx : x = 0
      · rw [hx]
        simp [toeplitzForm]
      · exact ((toeplitzForm_posDef_iff hκ m).mpr fun k _ => hE k) x hx |>.le
    exact summable_reflCoeff_sq_withSlack hκ hT hs

/-- **Q2. What replaces Allegretto–Piepenbrink.** The causal solution of a positive window is zero-free in the closed disc,
its self-reciprocal companions have all zeros on the circle, and on nonpositive couplings it is a positive supersolution. -/
theorem question_two (hκ : IsEvenSeq κ) (n : ℕ) (h : ToeplitzPosDef κ (n + 1)) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → predPoly (levinsonPred κ n) z ≠ 0) ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ z : ℂ, paraPoly (levinsonPred κ n) ε z = 0 → ‖z‖ = 1) ∧
      ((∀ d : ℤ, d ≠ 0 → κ d ≤ 0) → ∀ k, 0 ≤ levinsonPred κ n k) := by
  have hz := predPoly_levinson_ne_zero hκ n h
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  refine ⟨hz, fun ε hε z hzero => paraPoly_zero_on_circle hz hε hzero, fun hZ k => ?_⟩
  have hpd : ToeplitzPosDef κ n := by
    have hp := levinson_isPredictor hκ (n := n) fun k hk => (hlow k hk.le).ne'
    exact ((posDef_succ_iff hκ hp).mp h).1
  exact predictor_nonneg_of_offDiag_nonpos hZ
    (levinson_isPredictor hκ fun k hk => (hlow k hk.le).ne') hpd k

/-- **Q3. The cone of locked prime insertion is the Laplace cone.** Among continuous amplitudes decaying at `+∞` and of left exponent below `½`,
nonnegativity of all insertions at all prime sets, all base points and all locked phases is exponential convexity. -/
theorem question_three {f : ℝ → ℝ} (hc : Continuous f) {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) {κ C : ℝ} (hκ : κ < 1 / 2)
    (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y)) :
    (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p → ∀ (x b : ℝ),
      0 ≤ torusSum (ampl f (fun i => Real.log (p i)) x) fun i => b * Real.log (p i)) ↔
      ∀ x₀, IsExpConvexFrom x₀ f := by
  rw [← torusPositive_iff_hankel_nonneg hc hκ₀ hd hκ hL]
  refine forall_congr' fun n => forall_congr' fun p => forall_congr' fun hp =>
    forall_congr' fun hinj => forall_congr' fun x => ?_
  obtain ⟨C₂, -, hC₂⟩ := hd x
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  exact (torusSum_nonneg_iff_locked (traceSummable_ampl hκ₀ hC₂ hℓ le_rfl)
    (isKroneckerFamily_log_primes p hp hinj)).symm

/-- **Q4. When is an echo train passive?** Each echo in its Schur band; the reflection data are free; size is exact on independent reflectors; the mass is unbounded on
commensurable ones. -/
theorem question_four :
    (∀ κ : ℤ → ℝ, IsEvenSeq κ → ((∀ n, ToeplitzPosDef κ (n + 1)) ↔ 0 < κ 0 ∧ ∀ n,
      levinsonErr κ n ≠ 0 ∧ |κ ((n : ℤ) + 1) - frozenPrediction κ n (levinsonPred κ n)| < levinsonErr κ n)) ∧
    (∀ (κ₀ : ℝ) (γ : ℕ → ℝ), 0 < κ₀ → (∀ n, |γ n| < 1) → ∃ κ : ℤ → ℝ, IsEvenSeq κ ∧ κ 0 = κ₀ ∧
      (∀ n, reflCoeff κ n = γ n) ∧ ∀ n, ToeplitzPosDef κ (n + 1)) ∧
    (∀ {n : ℕ} (c ℓ : Fin n → ℝ), IsKroneckerFamily ℓ →
      ((∀ b, 0 ≤ echoSymbol c ℓ b) ↔ 2 * ∑ i, |c i| ≤ 1)) ∧
    (∀ (ℓ₀ : ℝ) (N : ℕ), ∃ c : Fin N → ℝ, 2 * ∑ i, |c i| = N ∧
      ∀ b, 0 ≤ echoSymbol c (fun k : Fin N => ((k : ℕ) + 1 : ℝ) * ℓ₀) b) :=
  ⟨fun _ hκ => passive_iff_each_echo_in_band hκ,
    fun _ _ h0 hγ => exists_evenSeq_of_reflCoeff h0 hγ,
    fun _ _ hℓ => echoSymbol_nonneg_iff hℓ,
    exists_passive_commensurable_train⟩

open CriticalHardyTheoryOfTheWindowCone in
/-- **Q5. Why `(β, s) = (1, 0)`.** On the datum plane: at `β = 1`, negative `s` empties the cone from a finite window on, and `s = 0` keeps it nonempty at
every window iff RH. At `β = 0` the weights are no longer pinned. On a lattice, `s` is an absolutely continuous density, and the form sits at the threshold of Szegő's regime on every lattice iff RH. -/
theorem question_five :
    (∀ s, s < 0 → ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone 1 s c = ∅) ∧
    (RiemannHypothesis ↔ ∀ c, 3 / 10 ≤ c → (datumCone 1 0 c).Nonempty) ∧
    (∀ s, -EF.gammaBracket 0 < s → ∃ lam₁ lam₂ : ℕ → ℝ, lam₁ ≠ lam₂ ∧
      ∀ c, lam₁ ∈ datumCone 0 s c ∧ lam₂ ∈ datumCone 0 s c) ∧
    (RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
      (∀ n, 0 < levinsonErr (weilSeq φ h) n) ∧
        (∀ s > 0, Summable fun k => reflCoeff (withSlack (weilSeq φ h) s) k ^ 2) ∧
        ¬ Summable (fun k => reflCoeff (weilSeq φ h) k ^ 2) ∧
        ∀ s < 0, ∃ (n : ℕ) (x : Fin n → ℝ), toeplitzForm (withSlack (weilSeq φ h) s) n x < 0) :=
  ⟨datum_classification.1, datum_classification.2.1, datum_classification.2.2.2.2,
    riemannHypothesis_iff_every_lattice_is_at_threshold⟩

/-- **Q6. Can an arithmetic inner factor be finite and nontrivial?** The datum `s − ρ` has a finite inner factor and no arithmetic. A Dirichlet polynomial has inner degree `0` or `∞` in
every strip. A column beyond its threshold has infinitely many right zeros, and its inner mass at infinity is its Mahler measure. For `ζ`, a finite inner factor makes the
field vanish at infinity, and RH is that vanishing together with recurrence. -/
theorem question_six :
    (∀ ρ w : ℂ, 1 / 2 < ρ.re → 1 / 2 < w.re → w ≠ ρ →
      innerOf (fun s => s - ρ) w = greenKernel w ρ) ∧
    (∀ (S : Finset ℕ), (∀ n ∈ S, 1 ≤ n) → ∀ (a : ℕ → ℂ) (x₀ : ℂ), dirichletPoly S a x₀ ≠ 0 → ∀ c d : ℝ,
      (∀ s ∈ vStrip c d, dirichletPoly S a s ≠ 0) ∨ {s | s ∈ vStrip c d ∧ dirichletPoly S a s = 0}.Infinite) ∧
    (∀ (p : ℝ) (c : ℂ), 1 < p → Real.sqrt p < ‖c‖ → ∀ t : ℝ,
      Tendsto (fun σ : ℝ => innerOf (column p c) ((σ : ℂ) + t * Complex.I)) atTop
        (𝓝 (Real.log (‖c‖ / Real.sqrt p)))) ∧
    (RiemannHypothesis ↔
      (∀ h : ℝ, 0 < h → Tendsto (fun t : ℝ => innerField (((1 / 2 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 0)) ∧
        _root_.RHTower.ZetaZeroDiscWeaklyRecurrent) :=
  ⟨fun _ _ hρ hw hne => innerOf_linear hρ hw hne,
    fun S hS a _ hx₀ c d => dirichletPoly_zero_free_or_infinite S hS a hx₀ c d,
    fun _ _ hp hc t => tendsto_innerOf_column hp hc t,
    riemannHypothesis_iff_tendsto_innerField_and_recurrent⟩

/-- **Q7. The forward map past the first echo.** A prime power moves the margin of stage `n` by `−(2/√n₀) A_n(log n₀)`, with `A_n` the autocorrelation of the
predictor test, and the margin is concave in the weights. -/
theorem question_seven {φ : ℝ → ℝ} {h r : ℝ} (hφ₀ : φ ∈ realTests) (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0)
    (lam : ℕ → ℝ) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {n : ℕ} (hpd : ToeplitzPosDef (weilSeqW lam φ h) (n + 1)) :
    HasDerivAt (fun t => levinsonErr (weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h) n)
      (-(2 / Real.sqrt n₀) * autocorr (latticeTest φ h (levinsonVec (weilSeqW lam φ h) n)) (Real.log n₀)) 0 :=
  hasDerivAt_levinsonErr_autocorr hφ₀ hφ lam hn₀ hpd

/-- **Q8. The target of the mollifier is forced.** The excess of a budget controls the distance of `E M_Q` to `1` at every point, and the first coefficient of `Q`; RH is the existence of a family with excess tending to `0`, and its limit is `1/E`. -/
theorem question_eight :
    (∀ (Q : Polynomial ℂ), Q.coeff 0 = 0 → ∀ s : ℂ, 1 / 2 < s.re →
      ‖zetaEntire s / s * polyMollifier 1 Q s - 1‖ ^ 2 ≤ (budget 1 Q - 1) * (‖s - 1‖ ^ 2 / (2 * s.re - 1))) ∧
    (∀ (Q : Polynomial ℂ), Q.coeff 0 = 0 →
      ‖Q.coeff 1 - (1 - (Real.eulerMascheroniConstant : ℂ))‖ ^ 2 ≤ budget 1 Q - 1) ∧
    (RiemannHypothesis ↔ ∃ Q : ℕ → Polynomial ℂ, (∀ k, (Q k).coeff 0 = 0) ∧
      Tendsto (fun k => budget 1 (Q k)) atTop (𝓝 1) ∧
      ∀ s : ℂ, 1 / 2 < s.re → Tendsto (fun k => zetaEntire s / s * polyMollifier 1 (Q k) s) atTop (𝓝 1)) :=
  ⟨fun _ hQ _ hs => norm_sub_one_sq_le hQ hs, fun _ hQ => norm_coeff_one_add_le hQ,
    riemannHypothesis_iff_exists_near_extremal⟩

/-- **Q9. The Gamma base against the columns.** The base pays by size, and alignment below the base fails the current. -/
theorem question_nine {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) :
    (∀ b : ℝ, columnMass a S < Real.log (b / (2 * Real.pi)) / 2 → 0 < columnCurrent a S b) ∧
    (∀ {B : ℝ} {Q : ℕ}, 0 < B → 0 < Q →
      Real.log (B * (Q : ℝ) ^ S.card / (2 * Real.pi)) / 2 < alignedMass a S Q →
      ∃ b : ℝ, B ≤ b ∧ b ≤ B * (Q : ℝ) ^ S.card ∧ columnCurrent a S b < 0) :=
  ⟨fun _ hb => columnCurrent_pos_of_mass_lt ha hS hb,
    fun hB hQ hlt => exists_columnCurrent_neg ha hS hB hQ hlt⟩

/-- **Q8 over a curve.** Castelnuovo holds iff the damped Euler logarithms are near-extremal. -/
theorem question_eight_curve {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∀ S d, 0 ≤ D.spanDefect S d) ↔
      ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ N : ℕ, abelBudget D ρ N < 1 + ε :=
  hodgeIndex_iff_abelMollifiers D

/-- **Q10. The potential past the Born regime.** The Born tangent at the vacuum; the defect by the accumulated reflection; and the exact tangent of the potential at every positive stage. -/
theorem question_ten :
    (∀ (κ₀ : ℝ) (η : ℤ → ℝ) (n : ℕ), 0 < κ₀ → IsEvenSeq η →
      HasDerivAt (fun t => reflCoeff (tiltSeq (vacuum κ₀) η t) n) (η ((n : ℤ) + 1) / κ₀) 0) ∧
    (∀ (κ : ℤ → ℝ) (K : ℝ) (n : ℕ), 0 ≤ K → (∀ k : ℕ, k < n → |κ ((k : ℤ) + 1)| ≤ K) →
      |schurParam κ n - κ ((n : ℤ) + 1)| ≤ K * (∏ k ∈ Finset.range n, (1 + |reflCoeff κ k|) - 1)) ∧
    (∀ (κ η : ℤ → ℝ) (n : ℕ), IsEvenSeq κ → IsEvenSeq η → ToeplitzPosDef κ (n + 1) →
      reflCoeff κ n ∈ Set.Ioo (-1 : ℝ) 1 →
      HasDerivAt (fun t => latticeKick (tiltSeq κ η t) n)
        (-(((toeplitzForm η (n + 2) (collarVec κ n 1) - toeplitzForm η (n + 2) (collarVec κ n (-1))) / 4 -
          reflCoeff κ n * toeplitzForm η (n + 1) (levinsonVec κ n)) / levinsonErr κ n /
            (1 - reflCoeff κ n ^ 2))) 0) :=
  ⟨fun _ _ n h0 hη => hasDerivAt_reflCoeff_vacuum h0 hη n,
    fun _ _ _ hK0 hK => abs_schurParam_sub_le hK0 hK,
    fun _ _ _ hκ hη h hγ => hasDerivAt_latticeKick hκ hη h hγ⟩

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
