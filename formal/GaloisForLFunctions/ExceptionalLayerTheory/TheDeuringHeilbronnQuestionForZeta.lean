import GaloisForLFunctions.ExceptionalLayerTheory.NonrealZeroRepulsionAndCoMovingRemainders
import GaloisForLFunctions.ArithmeticPositiveDuality.ATwoScaleIntegerNormOneOff
import GaloisForLFunctions.HeckeKreinToeplitz.IndexIsEnergy

/-!
# The Deuring–Heilbronn question for `ζ`: orthogonal factorization, equivalences, and Euler-product independence

Suppose `AsymptoticAbscissaLaw` fails on a reflection-symmetric strip configuration `Z` (`ZeroConfig`),
so `Z` carries a nonempty finite top layer at `β = Θ(Z)` above its asymptotic abscissa `Θ_∞(Z) < Θ(Z)`
and above a remainder ceiling `Θ₂ < β`. Two Deuring–Heilbronn self-repulsion laws govern `Θ_∞(Z)`:

* **Asymptotic Deuring–Heilbronn** (`AsymptoticDeuringHeilbronn Z`): `¬ AbscissaLaw Z → ApproachesLine Z`
  (equivalently `(Θ(Z) - Θ_∞(Z))(Θ_∞(Z) - ½) = 0`, the limiting conclusion of any graded repulsion
  law `Θ_∞ - ½ ≤ f(β - Θ₂, γ)` whose right-hand side vanishes);
* **Extreme Deuring–Heilbronn** (`ExtremeDeuringHeilbronn Z`): `¬ AbscissaLaw Z → (rightOf Z 0).Finite`
  (every nonempty finite top layer forces all but finitely many zeros onto `Re s = ½`).

Main results:

1. **Exact equivalences and orthogonal factorization of `AbscissaLaw`**
   (`asymptoticDeuringHeilbronn_tfae`, `extremeDeuringHeilbronn_tfae`,
   `abscissaLaw_orthogonal_factorization_tfae`, `harmonicConfig_asymptotic_not_extreme_deuringHeilbronn`,
   `not_isAsymptotic_deuringHeilbronn`, `not_isLocalBelow_deuringHeilbronn`):
   `ExtremeDeuringHeilbronn Z` is unconditionally equivalent to `AbscissaLaw Z ↔ AbscissaLawAt Z 0`.
   Although `ExtremeDeuringHeilbronn ⊊ AsymptoticDeuringHeilbronn` strictly (`harmonicConfig`),
   intersecting *either* law with `LinearAbscissaLaw` yields `AbscissaLaw`:
   `AbscissaLaw Z ↔ LinearAbscissaLaw Z ∧ AsymptoticDeuringHeilbronn Z ↔ LinearAbscissaLaw Z ∧ ExtremeDeuringHeilbronn Z`.
   Neither Deuring–Heilbronn law is an asymptotic property (`IsAsymptotic`) or a bounded-height
   property (`IsLocalBelow`).
2. **Specialization to `ζ`, equivalence with `AAL ↔ B13`, graded corollaries, and symmetric shifts**
   (`zetaAsymptoticDeuringHeilbronn_tfae`, `zetaExtremeDeuringHeilbronn_tfae`,
   `asymptoticAbscissaLaw_orthogonal_factorization_tfae`,
   `zetaLinearAbscissaLaw_iff_b13_of_extremeDeuringHeilbronn`,
   `riemannHypothesis_tfae_of_extremeDeuringHeilbronn_and_b13`,
   `zetaZeroAbscissa_bound_of_graded_repulsion_and_linearAbscissaLawAt`,
   `symmetricShift_xi_violates_extremeDeuringHeilbronn_of_not_aal`):
   On `ζ`, `ZetaExtremeDeuringHeilbronn` (`¬ AsymptoticAbscissaLaw → FiniteOffLine`) is unconditionally
   equivalent to `AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis)` (`AAL ↔ B13`), collapses
   the strict gap between `ZetaLinearAbscissaLaw` and `FiniteOffLine → RiemannHypothesis`, and together
   with `FiniteOffLine → RiemannHypothesis` yields the nine-way equivalence of `RiemannHypothesis`
   with `ZerosApproachLine`, `FiniteOffLine`, `κ(K_ζ) < ∞`, bounded heat counts, finite critical
   source energy, `EventualHadamardPositivity`, `EventualFilteredCentralGapBudget`, and
   `FiniteDimensional ℝ oddBoundStateSpace`. Conversely, under `¬ AsymptoticAbscissaLaw`, every positive
   symmetric shift `ξ(s + a)ξ(s - a)` (`a > 0`) violates eventual-to-global rigidity while carrying
   infinitely many off-line zeros at `Re s = ½ + a > ½`.
3. **Orthogonal independence and refutation on positive integer-norm Euler products**
   (`oneOff_euler_product_extremeDeuringHeilbronn_not_linear`,
   `twoScale_euler_product_linear_not_asymptoticDeuringHeilbronn`,
   `no_sub_ceiling_graded_deuring_heilbronn_on_integer_norm_euler_products`):
   Convergent Euler products `∏_k (1 - q_k^{-s})^{-1} = ∑_n a_n n^{-s}` with natural norms `q_k ≥ 2`,
   natural coefficients `a_n`, linear counting `∑_{n<N} a_n ∼ A N` (`A > 0`), and nonvanishing
   analytic continuation across `Re s = ½` realize both `ExtremeDeuringHeilbronn ∧ ¬ LinearAbscissaLaw`
   and `LinearAbscissaLaw ∧ ¬ AsymptoticDeuringHeilbronn`, attaining `Θ_∞ = Θ₂` for every
   `½ < Θ₂ < β < 2/3` and `γ > 0` and refuting every graded bound `f(β - Θ₂, γ) < Θ₂ - ½`.
-/

set_option autoImplicit false

open Complex Set Filter Topology
open scoped BigOperators
open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ZeroConfigurationGeometry.ZetaAbscissa
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff
open _root_.RHTower _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse
open _root_.RHTower.DeBruijn _root_.RHTower.CHMDPolar
open _root_.RHTower.CrossRouteReceiverBridges

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### Deuring–Heilbronn laws and the orthogonal factorization of `AbscissaLaw` on `ZeroConfig` -/

/-- **Asymptotic Deuring–Heilbronn law on a strip configuration**: failure of `AbscissaLaw` (a
nonempty finite top layer above `Θ_∞`) forces the remaining zeros to approach the critical line
(`ApproachesLine Z`, i.e. `Θ_∞(Z) = ½`). -/
def AsymptoticDeuringHeilbronn (Z : ZeroConfig) : Prop :=
  ¬ AbscissaLaw Z → ApproachesLine Z

/-- **Extreme Deuring–Heilbronn law on a strip configuration**: failure of `AbscissaLaw` forces all
but finitely many zeros onto the critical line (`(rightOf Z 0).Finite`). -/
def ExtremeDeuringHeilbronn (Z : ZeroConfig) : Prop :=
  ¬ AbscissaLaw Z → (rightOf Z 0).Finite

theorem extremeDeuringHeilbronn_imp_asymptoticDeuringHeilbronn {Z : ZeroConfig}
    (hE : ExtremeDeuringHeilbronn Z) : AsymptoticDeuringHeilbronn Z := fun hnot h hh =>
  (hE hnot).subset fun z ⟨hz, hre⟩ => ⟨hz, by linarith⟩

/-- **Algebraic and abscissa equivalences of `AsymptoticDeuringHeilbronn`.** It cuts out the union of
the diagonal `Θ = Θ_∞` (`AbscissaLaw`) and the base edge `Θ_∞ = ½` (`ApproachesLine`) inside the
simplex `½ ≤ Θ_∞ ≤ Θ ≤ 1`. -/
theorem asymptoticDeuringHeilbronn_tfae (Z : ZeroConfig) :
    [AsymptoticDeuringHeilbronn Z,
      AbscissaLaw Z ∨ ApproachesLine Z,
      (zeroAbscissa Z - asymptoticAbscissa Z) * (asymptoticAbscissa Z - 1 / 2) = 0,
      1 / 2 < asymptoticAbscissa Z → zeroAbscissa Z = asymptoticAbscissa Z].TFAE := by
  tfae_have 1 ↔ 2 := by
    unfold AsymptoticDeuringHeilbronn
    tauto
  tfae_have 2 ↔ 3 := by
    rw [abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa,
      approachesLine_iff_asymptoticAbscissa_eq_half, mul_eq_zero, sub_eq_zero, sub_eq_zero,
      eq_comm (a := zeroAbscissa Z)]
  tfae_have 3 ↔ 4 := by
    rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · rintro (heq | h12) hgt
      · exact heq
      · linarith
    · intro himp
      rcases eq_or_lt_of_le (half_le_asymptoticAbscissa Z) with h12 | hgt
      · exact Or.inr h12.symm
      · exact Or.inl (himp hgt)
  tfae_finish

/-- **Exact characterization of `ExtremeDeuringHeilbronn`.** Failure of `AbscissaLaw` implies
finitely many off-line zeros if and only if `AbscissaLaw` is equivalent to its `h = 0` finite-stratum
specialization `AbscissaLawAt Z 0`. -/
theorem extremeDeuringHeilbronn_tfae (Z : ZeroConfig) :
    [ExtremeDeuringHeilbronn Z,
      AbscissaLaw Z ↔ AbscissaLawAt Z 0,
      AbscissaLawAt Z 0 → AbscissaLaw Z,
      AbscissaLaw Z ∨ (rightOf Z 0).Finite].TFAE := by
  tfae_have 1 ↔ 4 := by
    unfold ExtremeDeuringHeilbronn
    tauto
  tfae_have 4 → 3 := by
    rintro (hA | hfin) h0
    · exact hA
    · have hpure : Pure Z := (pure_iff_forall_re_le Z).mpr fun ρ hρ => by
        simpa using h0 hfin ρ hρ
      exact ((pure_iff_approachesLine_and_abscissaLaw Z).mp hpure).2
  tfae_have 3 → 2 := fun himp => ⟨fun hA => hA 0 le_rfl, himp⟩
  tfae_have 2 → 4 := by
    intro hiff
    by_cases hfin : (rightOf Z 0).Finite
    · exact Or.inr hfin
    · exact Or.inl (hiff.mpr fun h => absurd h hfin)
  tfae_finish

/-- **Orthogonal factorization of `AbscissaLaw`.** Although `ExtremeDeuringHeilbronn` is strictly
stronger than `AsymptoticDeuringHeilbronn`, intersecting *either* with `LinearAbscissaLaw` yields
`AbscissaLaw`. -/
theorem abscissaLaw_orthogonal_factorization_tfae (Z : ZeroConfig) :
    [AbscissaLaw Z,
      LinearAbscissaLaw Z ∧ AsymptoticDeuringHeilbronn Z,
      LinearAbscissaLaw Z ∧ ExtremeDeuringHeilbronn Z,
      AbscissaLawAt Z 0 ∧ ExtremeDeuringHeilbronn Z].TFAE := by
  tfae_have 1 → 3 := fun hA =>
    ⟨⟨2, (abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt Z).mp hA 2 one_lt_two⟩,
      fun hnot => absurd hA hnot⟩
  tfae_have 3 → 2 :=
    And.imp_right extremeDeuringHeilbronn_imp_asymptoticDeuringHeilbronn
  tfae_have 2 → 1 := by
    rintro ⟨hL, hADH⟩
    by_cases hA : AbscissaLaw Z
    · exact hA
    · exact (((linearAbscissaLaw_tfae Z).out 0 5).mp hL) (hADH hA)
  tfae_have 3 → 4 :=
    And.imp_left (abscissaLawAt_zero_of_linearAbscissaLaw Z)
  tfae_have 4 → 1 := by
    rintro ⟨h0, hEDH⟩
    exact (((extremeDeuringHeilbronn_tfae Z).out 0 2).mp hEDH) h0
  tfae_finish

/-- **Strict separation of `ExtremeDeuringHeilbronn` and `AsymptoticDeuringHeilbronn`.** The
accumulating configuration `harmonicConfig` satisfies `ApproachesLine` (hence
`AsymptoticDeuringHeilbronn`) while carrying infinitely many off-line zeros below `Θ = 5/6`
(violating `ExtremeDeuringHeilbronn`). -/
theorem harmonicConfig_asymptotic_not_extreme_deuringHeilbronn :
    AsymptoticDeuringHeilbronn harmonicConfig ∧ ¬ ExtremeDeuringHeilbronn harmonicConfig := by
  obtain ⟨hinf, -, hZAL, -, hnotL⟩ := harmonicConfig_separates_linearAbscissaLaw_from_finiteStratum
  have hnotA : ¬ AbscissaLaw harmonicConfig := fun hA =>
    hnotL ⟨2, (abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt harmonicConfig).mp hA 2 one_lt_two⟩
  exact ⟨fun _ => hZAL, fun hE => hinf (hE hnotA)⟩

/-- **Neither Deuring–Heilbronn law is an asymptotic property.** High-ordinate zero statistics cannot
detect a finite lower-ordinate top layer protruding above `Θ_∞ > ½`. -/
theorem not_isAsymptotic_deuringHeilbronn :
    ¬ IsAsymptotic AsymptoticDeuringHeilbronn ∧ ¬ IsAsymptotic ExtremeDeuringHeilbronn := by
  obtain ⟨Z₀, hA₀, -, -, hasymp, -⟩ :=
    exists_infinite_offLine_not_linearAbscissaLawAt_of_isAsymptotic_and_isLocalBelow 1
  have hnotA_of_notL1 : ∀ Z : ZeroConfig, ¬ LinearAbscissaLawAt Z 1 → ¬ AbscissaLaw Z := by
    intro Z hnotL1 hA
    apply hnotL1
    unfold LinearAbscissaLawAt
    rw [(abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa Z).mp hA, one_mul]
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · obtain ⟨Z', hADH', -, hnotZAL', hnotL1⟩ :=
      hasymp AsymptoticDeuringHeilbronn hP (fun hnot => absurd hA₀ hnot)
    exact hnotZAL' (hADH' (hnotA_of_notL1 Z' hnotL1))
  · obtain ⟨Z', hEDH', hinf', -, hnotL1⟩ :=
      hasymp ExtremeDeuringHeilbronn hP (fun hnot => absurd hA₀ hnot)
    exact hinf' (hEDH' (hnotA_of_notL1 Z' hnotL1))

/-- **Neither Deuring–Heilbronn law is a bounded-height property.** Verification up to any fixed
height `T₀` cannot rule out a top bump planted above `T₀` over an infinite `Θ_∞ > ½` remainder. -/
theorem not_isLocalBelow_deuringHeilbronn (T₀ : ℝ) :
    ¬ IsLocalBelow T₀ AsymptoticDeuringHeilbronn ∧ ¬ IsLocalBelow T₀ ExtremeDeuringHeilbronn := by
  obtain ⟨Z₀, hA₀, -, -, -, hloc⟩ :=
    exists_infinite_offLine_not_linearAbscissaLawAt_of_isAsymptotic_and_isLocalBelow 1
  have hnotA_of_notL1 : ∀ Z : ZeroConfig, ¬ LinearAbscissaLawAt Z 1 → ¬ AbscissaLaw Z := by
    intro Z hnotL1 hA
    apply hnotL1
    unfold LinearAbscissaLawAt
    rw [(abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa Z).mp hA, one_mul]
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · obtain ⟨Z', hADH', -, hnotZAL', hnotL1⟩ :=
      hloc T₀ AsymptoticDeuringHeilbronn hP (fun hnot => absurd hA₀ hnot)
    exact hnotZAL' (hADH' (hnotA_of_notL1 Z' hnotL1))
  · obtain ⟨Z', hEDH', hinf', -, hnotL1⟩ :=
      hloc T₀ ExtremeDeuringHeilbronn hP (fun hnot => absurd hA₀ hnot)
    exact hinf' (hEDH' (hnotA_of_notL1 Z' hnotL1))

/-! ### Specialization to `ζ`: `AAL ↔ B13`, graded corollaries, and symmetric shifts -/

/-- **Asymptotic Deuring–Heilbronn law for `ζ`**: `¬ AsymptoticAbscissaLaw → ZerosApproachLine`. -/
def ZetaAsymptoticDeuringHeilbronn : Prop :=
  ¬ AsymptoticAbscissaLaw → ZerosApproachLine

/-- **Extreme Deuring–Heilbronn law for `ζ`**: `¬ AsymptoticAbscissaLaw → FiniteOffLine`. -/
def ZetaExtremeDeuringHeilbronn : Prop :=
  ¬ AsymptoticAbscissaLaw → FiniteOffLine

theorem rightOf_zetaZeroConfig_zero_finite_iff :
    (rightOf zetaZeroConfig 0).Finite ↔ FiniteOffLine := by
  rw [← finite_copies_iff 0]
  simpa only [add_zero] using finite_re_gt_half_iff_finiteOffLine

theorem abscissaLawAt_zetaZeroConfig_zero_iff :
    AbscissaLawAt zetaZeroConfig 0 ↔ (FiniteOffLine → RiemannHypothesis) := by
  unfold AbscissaLawAt
  rw [rightOf_zetaZeroConfig_zero_finite_iff]
  refine imp_congr_right fun _ => ?_
  simp only [add_zero]
  rw [← pure_iff_forall_re_le, Pure, riemannHypothesis_iff_zetaZeroConfig_onLine]

theorem zetaAsymptoticDeuringHeilbronn_iff_config :
    ZetaAsymptoticDeuringHeilbronn ↔ AsymptoticDeuringHeilbronn zetaZeroConfig := by
  unfold ZetaAsymptoticDeuringHeilbronn AsymptoticDeuringHeilbronn
  rw [zetaZeroConfig_abscissaLaw_iff, zetaZeroConfig_approachesLine_iff]

theorem zetaExtremeDeuringHeilbronn_iff_config :
    ZetaExtremeDeuringHeilbronn ↔ ExtremeDeuringHeilbronn zetaZeroConfig := by
  unfold ZetaExtremeDeuringHeilbronn ExtremeDeuringHeilbronn
  rw [zetaZeroConfig_abscissaLaw_iff, rightOf_zetaZeroConfig_zero_finite_iff]

theorem zetaExtremeDeuringHeilbronn_imp_asymptoticDeuringHeilbronn
    (hE : ZetaExtremeDeuringHeilbronn) : ZetaAsymptoticDeuringHeilbronn := fun hnot =>
  zerosApproachLine_of_finiteOffLine (hE hnot)

/-- **Equivalences of `ZetaAsymptoticDeuringHeilbronn`.** -/
theorem zetaAsymptoticDeuringHeilbronn_tfae :
    [ZetaAsymptoticDeuringHeilbronn,
      AsymptoticAbscissaLaw ∨ ZerosApproachLine,
      (zetaZeroAbscissa - zetaAsymptoticAbscissa) * (zetaAsymptoticAbscissa - 1 / 2) = 0,
      1 / 2 < zetaAsymptoticAbscissa → zetaZeroAbscissa = zetaAsymptoticAbscissa].TFAE := by
  have hcfg := asymptoticDeuringHeilbronn_tfae zetaZeroConfig
  tfae_have 1 ↔ 2 := by
    rw [zetaAsymptoticDeuringHeilbronn_iff_config, ← zetaZeroConfig_abscissaLaw_iff,
      ← zetaZeroConfig_approachesLine_iff]
    exact hcfg.out 0 1
  tfae_have 2 ↔ 3 := by
    rw [← zetaZeroConfig_abscissaLaw_iff, ← zetaZeroConfig_approachesLine_iff,
      ← zeroAbscissa_zetaZeroConfig, ← asymptoticAbscissa_zetaZeroConfig]
    exact hcfg.out 1 2
  tfae_have 3 ↔ 4 := by
    rw [← zeroAbscissa_zetaZeroConfig, ← asymptoticAbscissa_zetaZeroConfig]
    exact hcfg.out 2 3
  tfae_finish

/-- **Exact solution of the extreme Deuring–Heilbronn equivalence for `ζ`.** The extreme implication
`¬ AsymptoticAbscissaLaw → FiniteOffLine` is unconditionally equivalent to
`AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis)`. -/
theorem zetaExtremeDeuringHeilbronn_tfae :
    [ZetaExtremeDeuringHeilbronn,
      AsymptoticAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis),
      (FiniteOffLine → RiemannHypothesis) → AsymptoticAbscissaLaw,
      AsymptoticAbscissaLaw ∨ FiniteOffLine].TFAE := by
  have hcfg := extremeDeuringHeilbronn_tfae zetaZeroConfig
  tfae_have 1 ↔ 2 := by
    rw [zetaExtremeDeuringHeilbronn_iff_config, ← zetaZeroConfig_abscissaLaw_iff,
      ← abscissaLawAt_zetaZeroConfig_zero_iff]
    exact hcfg.out 0 1
  tfae_have 2 ↔ 3 := by
    rw [← zetaZeroConfig_abscissaLaw_iff, ← abscissaLawAt_zetaZeroConfig_zero_iff]
    exact hcfg.out 1 2
  tfae_have 3 ↔ 4 := by
    rw [← zetaZeroConfig_abscissaLaw_iff, ← abscissaLawAt_zetaZeroConfig_zero_iff,
      ← rightOf_zetaZeroConfig_zero_finite_iff]
    exact hcfg.out 2 3
  tfae_finish

/-- **Orthogonal factorization of `AsymptoticAbscissaLaw` for `ζ`.** -/
theorem asymptoticAbscissaLaw_orthogonal_factorization_tfae :
    [AsymptoticAbscissaLaw,
      ZetaLinearAbscissaLaw ∧ ZetaAsymptoticDeuringHeilbronn,
      ZetaLinearAbscissaLaw ∧ ZetaExtremeDeuringHeilbronn,
      (FiniteOffLine → RiemannHypothesis) ∧ ZetaExtremeDeuringHeilbronn].TFAE := by
  have hcfg := abscissaLaw_orthogonal_factorization_tfae zetaZeroConfig
  tfae_have 1 ↔ 2 := by
    rw [← zetaZeroConfig_abscissaLaw_iff, zetaLinearAbscissaLaw_iff_config,
      zetaAsymptoticDeuringHeilbronn_iff_config]
    exact hcfg.out 0 1
  tfae_have 2 ↔ 3 := by
    rw [zetaLinearAbscissaLaw_iff_config, zetaAsymptoticDeuringHeilbronn_iff_config,
      zetaExtremeDeuringHeilbronn_iff_config]
    exact hcfg.out 1 2
  tfae_have 3 ↔ 4 := by
    rw [zetaLinearAbscissaLaw_iff_config, zetaExtremeDeuringHeilbronn_iff_config,
      ← abscissaLawAt_zetaZeroConfig_zero_iff]
    exact hcfg.out 2 3
  tfae_finish

/-- Under `ZetaExtremeDeuringHeilbronn`, the strict hierarchy between existential linear AAL
(`ZerosApproachLine → RiemannHypothesis`) and the finite-stratum implication
(`FiniteOffLine → RiemannHypothesis`) collapses to equivalence. -/
theorem zetaLinearAbscissaLaw_iff_b13_of_extremeDeuringHeilbronn
    (hEDH : ZetaExtremeDeuringHeilbronn) :
    ZetaLinearAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis) := by
  constructor
  · intro hL hfin
    have hAAL : AsymptoticAbscissaLaw :=
      (asymptoticAbscissaLaw_orthogonal_factorization_tfae.out 2 0).mp ⟨hL, hEDH⟩
    have hZAL : ZerosApproachLine := zerosApproachLine_of_finiteOffLine hfin
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZAL, hAAL⟩
  · intro hB13
    have hAAL : AsymptoticAbscissaLaw :=
      (zetaExtremeDeuringHeilbronn_tfae.out 0 2).mp hEDH hB13
    exact (asymptoticAbscissaLaw_orthogonal_factorization_tfae.out 0 2).mp hAAL |>.1

/-- Under `ZetaExtremeDeuringHeilbronn`, `RiemannHypothesis` splits into `ZerosApproachLine` and
`FiniteOffLine → RiemannHypothesis`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_b13_of_extremeDeuringHeilbronn
    (hEDH : ZetaExtremeDeuringHeilbronn) :
    RiemannHypothesis ↔ ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis) := by
  rw [riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw]
  exact and_congr_right' ((zetaExtremeDeuringHeilbronn_tfae.out 0 1).mp hEDH)

/-- **Nine-way collapse under `ZetaExtremeDeuringHeilbronn` and `FiniteOffLine → RiemannHypothesis`.** -/
theorem riemannHypothesis_tfae_of_extremeDeuringHeilbronn_and_b13
    (hEDH : ZetaExtremeDeuringHeilbronn) (hB13 : FiniteOffLine → RiemannHypothesis) :
    [RiemannHypothesis,
      ZerosApproachLine,
      FiniteOffLine,
      negIndex zetaKernel < ⊤,
      ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M,
      xiCriticalSourceEnergy ≠ ⊤,
      EventualHadamardPositivity,
      EventualFilteredCentralGapBudget,
      FiniteDimensional ℝ oddBoundStateSpace].TFAE := by
  have hAAL : AsymptoticAbscissaLaw :=
    (zetaExtremeDeuringHeilbronn_tfae.out 0 2).mp hEDH hB13
  have hfin_tfae := zetaKernel_finiteIndex_tfae Nat.prime_two Nat.prime_three (by norm_num)
  have hRH_ZAL : RiemannHypothesis ↔ ZerosApproachLine :=
    ⟨zerosApproachLine_of_riemannHypothesis, fun hZ =>
      riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hAAL⟩⟩
  have hRH_Fin : RiemannHypothesis ↔ FiniteOffLine := by
    refine ⟨fun hRH => Set.finite_empty.subset fun q hq => ?_, hB13⟩
    apply (show (xiSpectralPoint q).im ≠ 0 from hq)
    rw [spectral_im_eq, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]
  tfae_have 1 ↔ 2 := hRH_ZAL
  tfae_have 1 ↔ 3 := hRH_Fin
  tfae_have 3 ↔ 4 := (hfin_tfae.out 2 0).symm
  tfae_have 3 ↔ 5 := hfin_tfae.out 2 3
  tfae_have 1 ↔ 6 := by
    constructor
    · intro hRH
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (riemannHypothesis_iff_criticalEnergy_le_quantum.mp hRH)
    · intro hE
      exact hRH_Fin.mpr ((hfin_tfae.out 0 2).mp
        ((negIndex_zetaKernel_le_of_energy hE).trans_lt (WithTop.coe_lt_top _)))
  tfae_have 2 ↔ 7 := eventualHadamardPositivity_iff_zerosApproachLine.symm
  tfae_have 3 ↔ 8 := eventualFilteredCentralGapBudget_iff_finiteOffLine.symm
  tfae_have 3 ↔ 9 := finiteDimensional_oddBoundStateSpace_iff_finiteOffLine.symm
  tfae_finish

/-- **Graded repulsion + `ZetaLinearAbscissaLawAt C` self-improvement.** Any graded bound
`¬ AsymptoticAbscissaLaw → Θ_∞ - ½ ≤ B` combines with `ZetaLinearAbscissaLawAt C` (`C ≥ 0`) to force
`¬ AsymptoticAbscissaLaw → Θ - ½ ≤ C B`. -/
theorem zetaZeroAbscissa_bound_of_graded_repulsion_and_linearAbscissaLawAt {C B : ℝ}
    (hC : 0 ≤ C) (hL : ZetaLinearAbscissaLawAt C)
    (hgrad : ¬ AsymptoticAbscissaLaw → zetaAsymptoticAbscissa - 1 / 2 ≤ B) :
    ¬ AsymptoticAbscissaLaw → zetaZeroAbscissa - 1 / 2 ≤ C * B := fun hnot =>
  hL.trans (mul_le_mul_of_nonneg_left (hgrad hnot) hC)

/-- **Symmetric-shift obstruction to extreme Deuring–Heilbronn on `ξ` itself.** Whenever
`¬ AsymptoticAbscissaLaw`, every positive symmetric shift `ξ(s + a)ξ(s - a)` (`a > 0`) violates
eventual-to-global zero rigidity while carrying infinitely many off-line zeros at `Re s = ½ + a > ½`
coming from Hardy's critical-line zeros of `ξ`. -/
theorem symmetricShift_xi_violates_extremeDeuringHeilbronn_of_not_aal
    (hnot : ¬ AsymptoticAbscissaLaw) {a : ℝ} (ha : 0 < a) :
    (∃ σ : ℝ,
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, symmetricShiftProduct xi a z = 0 → T ≤ |z.im| → z.re ≤ σ) ∧
      ∃ z₀ : ℂ, symmetricShiftProduct xi a z₀ = 0 ∧ σ < z₀.re) ∧
    ∀ T : ℝ, 0 < T → ∃ z : ℂ,
      symmetricShiftProduct xi a z = 0 ∧ T < |z.im| ∧ z.re = 1 / 2 + a := by
  refine ⟨?_, fun T hT => ?_⟩
  · by_contra hall
    push Not at hall
    apply hnot ((asymptoticAbscissaLaw_iff_symmetricShift_eventualToGlobal ha.le).mpr fun σ hσ z hz => ?_)
    exact hall σ hσ z hz
  · obtain ⟨t, ht, hzero⟩ := exists_Xi_zero_gt T
    have hxi : xi ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
      rw [xi_eq_XiC_comp]
      have he : (((1 / 2 : ℂ) + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
        ring_nf; simp only [Complex.I_sq, mul_neg, mul_one, neg_neg]
      rw [he, XiC_ofReal, hzero, Complex.ofReal_zero]
    refine ⟨((1 / 2 : ℂ) + (t : ℂ) * I) + (a : ℂ),
      (symmetricShiftProduct_zero_translates xi a hxi).1, ?_, by simp⟩
    have him : (((1 / 2 : ℂ) + (t : ℂ) * I) + (a : ℂ)).im = t := by simp
    rw [him, abs_of_pos (hT.trans ht)]
    exact ht

/-! ### Orthogonal independence and refutation on positive integer-norm Euler products -/

/-- Reflection-symmetrized four-point strip configuration `{3/5 ± i γ, 2/5 ± i γ}`. -/
private def singleScalePairConfig (γ : ℝ) : ZeroConfig where
  carrier :=
    {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} ∪
      reflect '' {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I}
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip := by
    rintro z ((rfl | rfl) | ⟨w, rfl | rfl, rfl⟩)
    · simp; norm_num
    · simp; norm_num
    · rw [re_reflect]; simp; norm_num
    · rw [re_reflect]; simp; norm_num
  reflect_mem := by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact Or.inr ⟨z, hz, rfl⟩
    · rw [reflect_involutive w]
      exact Or.inl hw
  mult_reflect _ _ := rfl
  finite_window _ _ := by
    have hfin : ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ).Finite :=
      (finite_singleton _).insert _
    exact (hfin.union (hfin.image reflect)).subset inter_subset_left

/-- **Positive integer-norm Euler product satisfying `ExtremeDeuringHeilbronn` while violating
`LinearAbscissaLaw`.** -/
theorem oneOff_euler_product_extremeDeuringHeilbronn_not_linear {γ : ℝ} (hγ : 0 < γ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      ExtremeDeuringHeilbronn Z ∧
      AsymptoticDeuringHeilbronn Z ∧
      ApproachesLine Z ∧
      ¬ LinearAbscissaLaw Z ∧
      ¬ AbscissaLawAt Z 0 ∧
      ¬ AbscissaLaw Z := by
  obtain ⟨q, a, hq, F, A, hA, hEuler, hcount, hdiff, hzeros, hcrit⟩ :=
    exists_integer_norm_linear_count_one_off_across γ
  let Z : ZeroConfig := singleScalePairConfig γ
  have hfin_carrier : Z.carrier.Finite := by
    have hfin : ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ).Finite :=
      (finite_singleton _).insert _
    exact hfin.union (hfin.image reflect)
  have hfin0 : (rightOf Z 0).Finite := hfin_carrier.subset fun z hz => hz.1
  have hEDH : ExtremeDeuringHeilbronn Z := fun _ => hfin0
  have hADH : AsymptoticDeuringHeilbronn Z :=
    extremeDeuringHeilbronn_imp_asymptoticDeuringHeilbronn hEDH
  have hZAL : ApproachesLine Z := fun h _ => hfin_carrier.subset fun z hz => hz.1
  have hnot0 : ¬ AbscissaLawAt Z 0 := by
    intro h0
    have hmem : (3 / 5 : ℂ) + (γ : ℂ) * I ∈ Z.carrier := Or.inl (Or.inl rfl)
    have hle := h0 hfin0 _ hmem
    simp at hle
    linarith
  have hnotL : ¬ LinearAbscissaLaw Z := mt (abscissaLawAt_zero_of_linearAbscissaLaw Z) hnot0
  have hnotA : ¬ AbscissaLaw Z := fun hA => hnot0 (hA 0 le_rfl)
  have hright : {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} := by
    ext s
    have hF_iff : (1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0) ↔
        s ∈ ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ) := by
      constructor
      · rintro ⟨h12, h1, hz⟩
        have hs1 : s ≠ 1 := by intro he; rw [he] at h1; norm_num at h1
        have hmem : s ∈ {w : ℂ | 1 / 3 < w.re ∧ w ≠ 1 ∧ F w = 0} := ⟨by linarith, hs1, hz⟩
        rwa [hzeros] at hmem
      · intro hmem
        have hmem' : s ∈ {w : ℂ | 1 / 3 < w.re ∧ w ≠ 1 ∧ F w = 0} := by rwa [hzeros]
        rcases hmem with rfl | rfl <;> exact ⟨by simp; norm_num, by simp; norm_num, hmem'.2.2⟩
    simp only [mem_setOf_eq, hF_iff, Z, singleScalePairConfig, mem_union, mem_image]
    constructor
    · intro hs
      refine ⟨Or.inl hs, ?_⟩
      rcases hs with rfl | rfl <;> simp <;> norm_num
    · rintro ⟨hs | ⟨w, hw, rfl⟩, hre⟩
      · exact hs
      · rcases hw with rfl | rfl <;> rw [re_reflect] at hre <;> simp at hre <;> norm_num at hre
  have _ := hγ
  exact ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright,
    hEDH, hADH, hZAL, hnotL, hnot0, hnotA⟩

/-- **Positive integer-norm Euler product satisfying `LinearAbscissaLaw` while violating
`AsymptoticDeuringHeilbronn` and `ExtremeDeuringHeilbronn`.** For every `½ < θ ≤ θ₂ < β < 2/3` and
`γ > 0`, `(Θ, Θ₂, Θ_∞) = (β, θ₂, θ)` is realized on a convergent integer-norm Euler product with
linear coefficient counting and zero-free continuation across `Re s = ½`. -/
theorem twoScale_euler_product_linear_not_asymptoticDeuringHeilbronn
    {θ θ₂ β γ : ℝ} (h12 : 1 / 2 < θ) (hθ₂ : θ ≤ θ₂) (hβ : θ₂ < β) (h23 : β < 2 / 3)
    (hγ : 0 < γ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      {s ∈ Z.carrier | 1 / 2 < s.re ∧ |s.im| ≤ γ} =
        {(β : ℂ) + (γ : ℂ) * I, (β : ℂ) - (γ : ℂ) * I} ∧
      (∀ z ∈ Z.carrier, γ < |z.im| → z.re ≤ θ₂) ∧
      (∃ z ∈ Z.carrier, γ < |z.im| ∧ z.re = θ₂) ∧
      zeroAbscissa Z = β ∧
      asymptoticAbscissa Z = θ ∧
      LinearAbscissaLaw Z ∧
      AbscissaLawAt Z 0 ∧
      ¬ AsymptoticDeuringHeilbronn Z ∧
      ¬ ExtremeDeuringHeilbronn Z ∧
      ¬ AbscissaLaw Z := by
  obtain ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, htop, hrem_le, hrem_eq,
    hΘ, hΘ_inf, hlin, hnot_aal, hinf, hnot_zal⟩ :=
    exists_two_scale_integer_norm_euler_product h12 hθ₂ hβ h23 hγ
  have hlaw0 : AbscissaLawAt Z 0 := abscissaLawAt_zero_of_linearAbscissaLaw Z hlin
  have hnot_adh : ¬ AsymptoticDeuringHeilbronn Z := fun h => hnot_zal (h hnot_aal)
  have hnot_edh : ¬ ExtremeDeuringHeilbronn Z := fun h => hinf (h hnot_aal)
  exact ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, htop, hrem_le, hrem_eq,
    hΘ, hΘ_inf, hlin, hlaw0, hnot_adh, hnot_edh, hnot_aal⟩

/-- **Refutation of sub-ceiling graded Deuring–Heilbronn bounds on positive integer-norm Euler
products.** For every candidate bound `f : ℝ → ℝ → ℝ` and every `½ < θ₂ < β < 2/3`, `γ > 0` with
`f (β - θ₂) γ < θ₂ - ½`, there exists a positive integer-norm Euler product with linear coefficient
counting and critical-line continuation whose strip configuration `Z` has finite top layer `β ± i γ`,
sharp remainder ceiling `θ₂` above `γ`, `Θ(Z) = β`, `Θ_∞(Z) = θ₂ < β`, and
`f (β - θ₂) γ < Θ_∞(Z) - ½`. -/
theorem no_sub_ceiling_graded_deuring_heilbronn_on_integer_norm_euler_products
    (f : ℝ → ℝ → ℝ) {θ₂ β γ : ℝ} (h12 : 1 / 2 < θ₂) (hβ : θ₂ < β) (h23 : β < 2 / 3)
    (hγ : 0 < γ) (hf : f (β - θ₂) γ < θ₂ - 1 / 2) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      {s ∈ Z.carrier | 1 / 2 < s.re ∧ |s.im| ≤ γ} =
        {(β : ℂ) + (γ : ℂ) * I, (β : ℂ) - (γ : ℂ) * I} ∧
      (∀ z ∈ Z.carrier, γ < |z.im| → z.re ≤ θ₂) ∧
      (∃ z ∈ Z.carrier, γ < |z.im| ∧ z.re = θ₂) ∧
      zeroAbscissa Z = β ∧
      asymptoticAbscissa Z < zeroAbscissa Z ∧
      f (β - θ₂) γ < asymptoticAbscissa Z - 1 / 2 := by
  obtain ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, htop, hrem_le, hrem_eq,
    hΘ, hΘ_inf, -, -, -, -, -⟩ :=
    twoScale_euler_product_linear_not_asymptoticDeuringHeilbronn h12 le_rfl hβ h23 hγ
  refine ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, htop, hrem_le, hrem_eq,
    hΘ, ?_, ?_⟩
  · rw [hΘ, hΘ_inf]
    exact hβ
  · rw [hΘ_inf]
    exact hf

end GaloisForLFunctions.ExceptionalLayerTheory
