import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLinearAbscissaLawAndItsHierarchy
import GaloisForLFunctions.InfiniteRankWeilTheory.TheCrudeStepAndTheCount
import GaloisForLFunctions.InfiniteRankWeilTheory.TheFunctionalEquationAdmitsEveryFiniteLayer
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerNormOneOffHasLinearCounting

/-!
# The linear abscissa law in Weil towers: six-way TFAE for `ζ` and two-scale obstructions

For an indexed zero configuration `ρ : ι → ℂ`, let `LinearEventualToGlobalAt ρ C` assert that for
every `h ≥ 0`, finiteness of `{i : ½ + h < Re (ρ i)}` forces `Re (ρ i) ≤ ½ + C h` for all `i`.

* **Indexed configurations.** For every `C ≥ 0`, `RightRH ρ ↔ ZerosApproachLine ρ ∧ LinearEventualToGlobalAt ρ C`;
  for every real `C`, `ZerosApproachLine ρ` and `LinearEventualToGlobalAt ρ C` force `RightRH ρ`;
  and `AsymptoticAbscissaLaw ρ ↔ ∀ C > 1, LinearEventualToGlobalAt ρ C`.
* **Quantitative six-way equivalence for `ζ`.** For every slope `C ≥ 1` (`zetaLinearAbscissaLawAt_tfae`),
  `Θ − ½ ≤ C (Θ_∞ − ½)` is unconditionally equivalent to:
  1. the eventual-to-global zero bound `ZetaLinearEventualToGlobalAt C`;
  2. finite-rank Chebyshev self-improvement of `ψ(x) − x` at factor `C`;
  3. the continuous all-scale Weil lag bound `‖Φ(L)‖ ≤ M e^{C(Θ_∞ − ½) L}` (`L ≥ 0`);
  4. a thick-set Weil tower lag bound at one base `ℓ > 0` with exponent `C(Θ_∞ − ½) + ε`;
  5. a thick-set `primeDeviation` bound along `X = e^{νℓ}` at one base `ℓ > 0` with exponent
     `½ + C(Θ_∞ − ½) + ε`.
* **Two-scale functional-equation obstruction at positive asymptotic abscissa.** For `0 < a < b < ½`,
  `twoScaleCoshModel a Q` (`cosh(s − ½ − a) cosh(s − ½ + a) Π_{q ∈ Q} quartet q s`) is entire of
  order one, satisfies `G(1 − s) = G(s)` and `G(s̄) = conj G(s)`, has all zeros in `0 < Re s < 1`,
  violates `ZerosApproachLine` (`Θ_∞ = ½ + a > ½`), and places a finite quartet layer at `½ ± b`,
  defeating `LinearEventualToGlobalAt · C` for every prescribed `C : ℝ` (`b / a > C`).
* **Positive integer-norm Euler-product obstruction.** Every integer-norm Beurling one-off with
  linear counting satisfies `ZerosApproachLine` on `Re s > ½` and violates `LinearEventualToGlobalAt · C`
  for every `C : ℝ`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.ZeroConfigurationGeometry
open RHTower (XiZeroCopy weilLagFunction zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le)

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### Indexed configurations -/

section Indexed

variable {ι : Type*} (ρ : ι → ℂ)

/-- **Linear eventual-to-global law at slope `C`** for an indexed configuration `ρ : ι → ℂ`. -/
def LinearEventualToGlobalAt (C : ℝ) : Prop :=
  ∀ h : ℝ, 0 ≤ h → {i : ι | 1 / 2 + h < (ρ i).re}.Finite → ∀ i : ι, (ρ i).re ≤ 1 / 2 + C * h

/-- **Existential linear eventual-to-global law** for an indexed configuration. -/
def LinearEventualToGlobal : Prop :=
  ∃ C : ℝ, LinearEventualToGlobalAt ρ C

/-- Under `ZerosApproachLine ρ`, `LinearEventualToGlobalAt ρ C` at any real `C` forces `RightRH ρ`. -/
theorem rightRH_of_zerosApproachLine_of_linearEventualToGlobalAt {C : ℝ}
    (hZ : ZerosApproachLine ρ) (hL : LinearEventualToGlobalAt ρ C) : RightRH ρ := by
  intro i
  by_contra hgt
  push Not at hgt
  by_cases hC0 : C ≤ 0
  · set h : ℝ := ((ρ i).re - 1 / 2) / 2
    have hh : 0 < h := by dsimp [h]; linarith
    have hb := hL h hh.le (hZ h hh) i
    have hCh : C * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 hh.le
    linarith
  · push Not at hC0
    set h : ℝ := ((ρ i).re - 1 / 2) / (2 * C)
    have hh : 0 < h := div_pos (by linarith) (by positivity)
    have hb := hL h hh.le (hZ h hh) i
    have hCh : C * h = ((ρ i).re - 1 / 2) / 2 := by dsimp [h]; field_simp
    linarith

/-- **`RightRH` is `ZerosApproachLine` plus `LinearEventualToGlobalAt ρ C`** for every `C ≥ 0`. -/
theorem rightRH_iff_zerosApproachLine_and_linearEventualToGlobalAt {C : ℝ} (hC : 0 ≤ C) :
    RightRH ρ ↔ ZerosApproachLine ρ ∧ LinearEventualToGlobalAt ρ C := by
  constructor
  · intro hR
    refine ⟨fun h hh => finite_empty.subset fun i hi => ?_, fun h hh _ i => ?_⟩
    · have : 1 / 2 + h < (ρ i).re := hi
      linarith [hR i]
    · have h0 : 0 ≤ C * h := mul_nonneg hC hh
      linarith [hR i]
  · rintro ⟨hZ, hL⟩
    exact rightRH_of_zerosApproachLine_of_linearEventualToGlobalAt ρ hZ hL

/-- Under `ZerosApproachLine ρ`, existential `LinearEventualToGlobal ρ` is equivalent to `RightRH ρ`. -/
theorem rightRH_iff_linearEventualToGlobal_of_zerosApproachLine (hZ : ZerosApproachLine ρ) :
    RightRH ρ ↔ LinearEventualToGlobal ρ := by
  constructor
  · intro hR
    exact ⟨1, ((rightRH_iff_zerosApproachLine_and_linearEventualToGlobalAt ρ zero_le_one).mp hR).2⟩
  · rintro ⟨C, hL⟩
    exact rightRH_of_zerosApproachLine_of_linearEventualToGlobalAt ρ hZ hL

/-- **`AsymptoticAbscissaLaw ρ` is the `C ↓ 1` limit of `LinearEventualToGlobalAt ρ C`.** -/
theorem asymptoticAbscissaLaw_iff_forall_gt_one_linearEventualToGlobalAt :
    AsymptoticAbscissaLaw ρ ↔ ∀ C : ℝ, 1 < C → LinearEventualToGlobalAt ρ C := by
  constructor
  · intro hA C hC1 h hh hfin i
    have hb := hA h hh hfin i
    nlinarith
  · intro hall h hh hfin i
    rcases eq_or_lt_of_le hh with rfl | hhpos
    · have hb := hall 2 one_lt_two 0 le_rfl hfin i
      linarith
    · by_contra hgt
      push Not at hgt
      set C : ℝ := 1 + ((ρ i).re - (1 / 2 + h)) / (2 * h)
      have hC1 : 1 < C := by
        dsimp [C]
        have : 0 < ((ρ i).re - (1 / 2 + h)) / (2 * h) := div_pos (by linarith) (by linarith)
        linarith
      have hb := hall C hC1 h hh hfin i
      have hCh : C * h = h + ((ρ i).re - (1 / 2 + h)) / 2 := by
        dsimp [C]; field_simp; ring
      rw [hCh] at hb
      linarith

end Indexed

/-! ### Quantitative six-way TFAE for `ζ` at fixed slope `C ≥ 1` -/

/-- **Thick-set Weil tower lag bound implies `ZetaLinearAbscissaLawAt C`** (`C ≥ 1`). If at one
base `ℓ > 0` the Weil lag grows at most at rate `C (Θ_∞ − ½) + ε` along a thick set of levels for
every `ε > 0`, then `Θ − ½ ≤ C (Θ_∞ − ½)`. -/
theorem zetaLinearAbscissaLawAt_of_thick_lag_bound {C ℓ : ℝ} (hC1 : 1 ≤ C) (hℓ : 0 < ℓ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ G : Set ℕ, Thick G ∧ ∃ K : ℝ,
      ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤
        K * Real.exp ((C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * ν * ℓ)) :
    ZetaAbscissa.ZetaLinearAbscissaLawAt C := by
  by_contra hnot
  unfold ZetaAbscissa.ZetaLinearAbscissaLawAt at hnot
  push Not at hnot
  have h0 : 0 ≤ zetaAsymptoticAbscissa - 1 / 2 := sub_nonneg.mpr half_le_zetaAsymptoticAbscissa
  have hlt_abs : zetaAsymptoticAbscissa < RHTower.zetaZeroAbscissa := by nlinarith
  have hnotAAL : ¬ RHTower.AsymptoticAbscissaLaw := by
    rw [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa]
    exact hlt_abs.ne
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnotAAL
  obtain ⟨F, Θ₀, Θ₂, hFne, hΘ₀, hΘ₂, hF, hrest⟩ := hnotAAL
  have hΘ_eq : Θ₀ = RHTower.zetaZeroAbscissa := by
    refine le_antisymm ?_ ?_
    · obtain ⟨q₀, hq₀⟩ := hFne
      rw [← hF q₀ hq₀]
      exact RHTower.re_le_zetaZeroAbscissa (RHTower.riemannZeta_eq_zero_of_xiZeroCopy q₀)
    · refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hΘ₀.le fun q => ?_
      by_cases hq : q ∈ F
      · exact (hF q hq).le
      · exact (hrest q hq).trans hΘ₂.le
  rw [← hΘ_eq] at hnot
  obtain ⟨hlow, htop, hvis, hlt⟩ := zeta_window_data hℓ hFne hΘ₂ hF hrest
  set ε : ℝ := ((Θ₀ - 1 / 2) - C * (zetaAsymptoticAbscissa - 1 / 2)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨G, hG, K, hK⟩ := h ε hε
  set rate : ℝ := C * (zetaAsymptoticAbscissa - 1 / 2) + ε
  have hρR : Real.exp (rate * ℓ) < Real.exp (ℓ * (Θ₀ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by dsimp [rate, ε]; nlinarith)
  refine not_forall_mem_thick_norm_levelSum_le (frobTower ℓ zetaConfig) lagWeight
    summable_norm_lagWeight F (Real.exp_pos _) (Real.exp_pos _).le hlt hlow htop hvis
    (C := K) (Real.exp_pos _).le hρR hG (fun ν hν => ?_)
  have hb := hK ν hν
  rwa [weilLagFunction_mul_eq_levelSum, show rate * (ν : ℝ) * ℓ = ν * (rate * ℓ) by ring,
    Real.exp_nat_mul] at hb

/-- **Thick-set prime-deviation bound implies `ZetaLinearAbscissaLawAt C`** (`C ≥ 1`). -/
theorem zetaLinearAbscissaLawAt_of_thick_primeDeviation_bound {C ℓ : ℝ} (hC1 : 1 ≤ C) (hℓ : 0 < ℓ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ G : Set ℕ, Thick G ∧ ∃ K : ℝ, ∀ ν ∈ G, 1 ≤ ν →
      ‖primeDeviation (Real.exp (ν * ℓ))‖ ≤
        K * Real.exp ((1 / 2 + C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * (ν * ℓ))) :
    ZetaAbscissa.ZetaLinearAbscissaLawAt C := by
  refine zetaLinearAbscissaLawAt_of_thick_lag_bound hC1 hℓ fun ε hε => ?_
  obtain ⟨G, hG, K, hK⟩ := h ε hε
  refine ⟨G ∩ Set.Ici 1, thick_inter_Ici hG 1, K, fun ν hν => ?_⟩
  have hν1 : 1 ≤ ν := hν.2
  have hL : 0 < (ν : ℝ) * ℓ := mul_pos (by exact_mod_cast hν1) hℓ
  rw [norm_weilLagFunction_eq hL]
  have hb := hK ν hν.1 hν1
  calc Real.exp (-((ν : ℝ) * ℓ) / 2) * ‖primeDeviation (Real.exp (ν * ℓ))‖
      ≤ Real.exp (-((ν : ℝ) * ℓ) / 2) *
          (K * Real.exp ((1 / 2 + C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * (ν * ℓ))) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = K * Real.exp ((C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * ν * ℓ) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Quantitative six-way TFAE for `ZetaLinearAbscissaLawAt C`** (`C ≥ 1`). -/
theorem zetaLinearAbscissaLawAt_tfae {C : ℝ} (hC1 : 1 ≤ C) :
    [ZetaAbscissa.ZetaLinearAbscissaLawAt C,
      ZetaAbscissa.ZetaLinearEventualToGlobalAt C,
      ∀ h : ℝ, 0 ≤ h →
        (∃ (S : Finset ℂ) (d : ℂ → ℂ) (K x₀ : ℝ),
          ∀ x, x₀ ≤ x → ‖ZetaAbscissa.expSumError S d x‖ ≤ K * x ^ (1 / 2 + h)) →
        ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
          |RHTower.psiRemainder N| ≤ M * (N : ℝ) ^ (1 / 2 + C * h + ε),
      ∃ M : ℝ, ∀ L : ℝ, 0 ≤ L →
        ‖weilLagFunction L‖ ≤ M * Real.exp (C * (zetaAsymptoticAbscissa - 1 / 2) * L),
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Set ℕ, Thick G ∧ ∃ K : ℝ,
        ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤
          K * Real.exp ((C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * ν * ℓ),
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Set ℕ, Thick G ∧ ∃ K : ℝ,
        ∀ ν ∈ G, 1 ≤ ν → ‖primeDeviation (Real.exp (ν * ℓ))‖ ≤
          K * Real.exp ((1 / 2 + C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * (ν * ℓ))].TFAE := by
  have hC0 : 0 ≤ C := by linarith
  tfae_have 1 ↔ 2 := ZetaAbscissa.zetaLinearAbscissaLawAt_iff_eventualToGlobalAt hC0
  tfae_have 1 ↔ 3 := ZetaAbscissa.zetaLinearAbscissaLawAt_iff_chebyshevFiniteRank_selfImprovement hC0
  tfae_have 1 → 4 := by
    intro hL
    have hq : ∀ q : RHTower.XiZeroCopy,
        (q.1 : ℂ).re ≤ 1 / 2 + C * (zetaAsymptoticAbscissa - 1 / 2) := fun q => by
      have hre := RHTower.re_le_zetaZeroAbscissa (RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)
      unfold ZetaAbscissa.ZetaLinearAbscissaLawAt at hL
      linarith
    refine ⟨RHTower.lagWeightTotal, fun L hL0 => ?_⟩
    rw [RHTower.weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact RHTower.abs_weilLagFunctionReal_le_of_strip hq hL0
  tfae_have 4 → 5 := by
    rintro ⟨M, hM⟩
    refine ⟨1, one_pos, fun ε hε => ⟨Set.univ, thick_univ, max M 0, fun ν _ => ?_⟩⟩
    have hb := hM ((ν : ℝ) * 1) (by positivity)
    calc ‖weilLagFunction ((ν : ℝ) * 1)‖
        ≤ M * Real.exp (C * (zetaAsymptoticAbscissa - 1 / 2) * ((ν : ℝ) * 1)) := hb
      _ ≤ max M 0 * Real.exp (C * (zetaAsymptoticAbscissa - 1 / 2) * ((ν : ℝ) * 1)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max M 0 * Real.exp ((C * (zetaAsymptoticAbscissa - 1 / 2) + ε) * (ν : ℝ) * 1) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
          have : 0 ≤ ε * (ν : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg ν)
          nlinarith
  tfae_have 5 → 6 := by
    rintro ⟨ℓ, hℓ, hlag⟩
    refine ⟨ℓ, hℓ, fun ε hε => ?_⟩
    obtain ⟨G, hG, K, hK⟩ := hlag ε hε
    refine ⟨G, hG, K, fun ν hν hν1 => ?_⟩
    have hL : 0 < (ν : ℝ) * ℓ := mul_pos (by exact_mod_cast hν1) hℓ
    have heq := norm_weilLagFunction_eq hL
    have hb := hK ν hν
    rw [heq] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos (((ν : ℝ) * ℓ) / 2)).le
    have hlhs : Real.exp (((ν : ℝ) * ℓ) / 2) *
        (Real.exp (-((ν : ℝ) * ℓ) / 2) * ‖primeDeviation (Real.exp ((ν : ℝ) * ℓ))‖)
        = ‖primeDeviation (Real.exp ((ν : ℝ) * ℓ))‖ := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [hlhs] at hmul
    refine hmul.trans (le_of_eq ?_)
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  tfae_have 6 → 1 := by
    rintro ⟨ℓ, hℓ, hdev⟩
    exact zetaLinearAbscissaLawAt_of_thick_primeDeviation_bound hC1 hℓ hdev
  tfae_finish

/-! ### Two-scale functional-equation model at positive asymptotic abscissa -/

/-- **Two-scale cosh model**: off-line infinite background columns at `½ ± a` together with the
finite quartet layer `Q`. -/
def twoScaleCoshModel (a : ℝ) (Q : Finset ℂ) (s : ℂ) : ℂ :=
  Complex.cosh (s - 1 / 2 - a) * Complex.cosh (s - 1 / 2 + a) * ∏ q ∈ Q, quartet q s

/-- The `twoScaleCoshModel` is entire. -/
theorem differentiable_twoScaleCoshModel (a : ℝ) (Q : Finset ℂ) :
    Differentiable ℂ (twoScaleCoshModel a Q) := by
  unfold twoScaleCoshModel
  refine ((Complex.differentiable_cosh.comp ((differentiable_id.sub_const _).sub_const _)).mul
    (Complex.differentiable_cosh.comp ((differentiable_id.sub_const _).add_const _))).mul ?_
  have hfun : (fun s => ∏ q ∈ Q, quartet q s) = ∏ q ∈ Q, quartet q := by
    ext s; rw [Finset.prod_apply]
  rw [hfun]
  exact Differentiable.finsetProd fun q _ => differentiable_quartet q

/-- **Functional equation.** `G_{a,Q}(1 − s) = G_{a,Q}(s)`. -/
theorem twoScaleCoshModel_one_sub (a : ℝ) (Q : Finset ℂ) (s : ℂ) :
    twoScaleCoshModel a Q (1 - s) = twoScaleCoshModel a Q s := by
  unfold twoScaleCoshModel
  rw [show (1 - s - 1 / 2 - a : ℂ) = -(s - 1 / 2 + a) by ring,
    show (1 - s - 1 / 2 + a : ℂ) = -(s - 1 / 2 - a) by ring,
    Complex.cosh_neg, Complex.cosh_neg,
    mul_comm (Complex.cosh (s - 1 / 2 + a)) (Complex.cosh (s - 1 / 2 - a))]
  simp_rw [quartet_one_sub]

/-- **Reality.** `G_{a,Q}(s̄) = conj G_{a,Q}(s)`. -/
theorem twoScaleCoshModel_conj (a : ℝ) (Q : Finset ℂ) (s : ℂ) :
    twoScaleCoshModel a Q (starRingEnd ℂ s) = starRingEnd ℂ (twoScaleCoshModel a Q s) := by
  have h12 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have ha : starRingEnd ℂ (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  unfold twoScaleCoshModel
  rw [map_mul, map_mul, map_prod, ← Complex.cosh_conj, ← Complex.cosh_conj,
    map_sub, map_sub, map_add, map_sub, h12, ha]
  simp_rw [quartet_conj]

/-- **Order one.** `‖G_{a,Q}(s)‖ ≤ C (1 + ‖s‖)^{4 #Q} e^{2 ‖s‖}`. -/
theorem norm_twoScaleCoshModel_le (a : ℝ) (Q : Finset ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      ‖twoScaleCoshModel a Q s‖ ≤ C * (1 + ‖s‖) ^ (4 * Q.card) * Real.exp (2 * ‖s‖) := by
  have hcosh_shift : ∀ c : ℂ, ∀ s : ℂ, ‖Complex.cosh (s - c)‖ ≤ Real.exp ‖c‖ * Real.exp ‖s‖ := by
    intro c s
    have hcw : Complex.cosh (s - c) =
        (Complex.exp (s - c) + Complex.exp (-(s - c))) / 2 := by
      rw [← Complex.two_cosh]; ring
    have hb : ∀ w : ℂ, ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := fun w => by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm w)
    have h1 := hb (s - c)
    have h2 := hb (-(s - c))
    rw [norm_neg] at h2
    have hadd := (norm_add_le (Complex.exp (s - c)) (Complex.exp (-(s - c)))).trans
      (add_le_add h1 h2)
    have hexp : Real.exp ‖s - c‖ ≤ Real.exp ‖c‖ * Real.exp ‖s‖ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr ((norm_sub_le s c).trans (by linarith))
    rw [hcw, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  set K : ℝ := 2 + ∑ q ∈ Q, ‖q‖
  have hsum0 : 0 ≤ ∑ q ∈ Q, ‖q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  set A : ℝ := Real.exp ‖(1 / 2 + a : ℂ)‖ * Real.exp ‖(1 / 2 - a : ℂ)‖ * K ^ (4 * Q.card)
  refine ⟨A, by dsimp [A]; positivity, fun s => ?_⟩
  have hfac : ∀ x : ℂ, ‖x‖ ≤ K → ‖s - x‖ ≤ K * (1 + ‖s‖) := fun x hx => by
    have := norm_sub_le s x
    nlinarith [norm_nonneg s, hK1]
  have hq : ∀ q ∈ Q, ‖quartet q s‖ ≤ (K * (1 + ‖s‖)) ^ 4 := by
    intro q hqQ
    have hqK : ‖q‖ + 2 ≤ K := by
      have := Finset.single_le_sum (f := fun x : ℂ => ‖x‖) (fun x _ => norm_nonneg x) hqQ
      dsimp [K]; linarith
    have h1 : ‖q‖ ≤ K := by linarith [norm_nonneg q]
    have h2 : ‖starRingEnd ℂ q‖ ≤ K := by rw [Complex.norm_conj]; exact h1
    have h3 : ‖1 - q‖ ≤ K := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have h4 : ‖1 - starRingEnd ℂ q‖ ≤ K :=
      (norm_sub_le _ _).trans (by rw [norm_one, Complex.norm_conj]; linarith)
    unfold quartet
    rw [norm_mul, norm_mul, norm_mul,
      show (K * (1 + ‖s‖)) ^ 4 = (K * (1 + ‖s‖)) * (K * (1 + ‖s‖)) * (K * (1 + ‖s‖)) *
        (K * (1 + ‖s‖)) by ring]
    have hp : 0 ≤ K * (1 + ‖s‖) := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul (hfac _ h1) (hfac _ h2) (norm_nonneg _) hp)
      (hfac _ h3) (norm_nonneg _) (by positivity)) (hfac _ h4) (norm_nonneg _) (by positivity)
  have hprod : ‖∏ q ∈ Q, quartet q s‖ ≤ ((K * (1 + ‖s‖)) ^ 4) ^ Q.card := by
    rw [norm_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hq
  have hc1 : ‖Complex.cosh (s - 1 / 2 - a)‖ ≤ Real.exp ‖(1 / 2 + a : ℂ)‖ * Real.exp ‖s‖ := by
    simpa [sub_sub] using hcosh_shift (1 / 2 + a) s
  have hc2 : ‖Complex.cosh (s - 1 / 2 + a)‖ ≤ Real.exp ‖(1 / 2 - a : ℂ)‖ * Real.exp ‖s‖ := by
    have : s - 1 / 2 + (a : ℂ) = s - (1 / 2 - a) := by ring
    rw [this]
    exact hcosh_shift (1 / 2 - a) s
  unfold twoScaleCoshModel
  rw [norm_mul, norm_mul]
  calc ‖Complex.cosh (s - 1 / 2 - a)‖ * ‖Complex.cosh (s - 1 / 2 + a)‖ * ‖∏ q ∈ Q, quartet q s‖
      ≤ ((Real.exp ‖(1 / 2 + a : ℂ)‖ * Real.exp ‖s‖) *
          (Real.exp ‖(1 / 2 - a : ℂ)‖ * Real.exp ‖s‖)) * ((K * (1 + ‖s‖)) ^ 4) ^ Q.card :=
        mul_le_mul (mul_le_mul hc1 hc2 (norm_nonneg _) (by positivity)) hprod
          (norm_nonneg _) (by positivity)
    _ = A * (1 + ‖s‖) ^ (4 * Q.card) * Real.exp (2 * ‖s‖) := by
        dsimp [A]
        rw [← pow_mul, mul_pow, show 2 * ‖s‖ = ‖s‖ + ‖s‖ by ring, Real.exp_add]
        ring

theorem twoScaleCoshModel_eq_zero_iff (a : ℝ) (Q : Finset ℂ) (s : ℂ) :
    twoScaleCoshModel a Q s = 0 ↔
      Complex.cosh (s - 1 / 2 - a) = 0 ∨
      Complex.cosh (s - 1 / 2 + a) = 0 ∨
      ∃ q ∈ Q, s = q ∨ s = starRingEnd ℂ q ∨ s = 1 - q ∨ s = 1 - starRingEnd ℂ q := by
  unfold twoScaleCoshModel
  rw [mul_eq_zero, mul_eq_zero, Finset.prod_eq_zero_iff, or_assoc]
  refine or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl ?_))
  unfold quartet
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

/-- Indexed zero configuration of `twoScaleCoshModel a Q`. -/
def twoScaleCoshZeros (a : ℝ) (Q : Finset ℂ) :
    {s : ℂ // twoScaleCoshModel a Q s = 0} → ℂ :=
  fun s => s.1

/-- **Arbitrarily large abscissa ratio under the functional equation, order one, and reality, even
at strictly positive asymptotic abscissa.** For every prescribed `C : ℝ`, there exist `0 < a < ½`
and a finite set `Q` such that `twoScaleCoshModel a Q` has all zeros in `(0, 1) × ℝ`, violates
`ZerosApproachLine` (`Θ_∞ = ½ + a > ½`), and violates `LinearEventualToGlobalAt · C`. -/
theorem exists_twoScaleCoshModel_not_linearEventualToGlobalAt (C : ℝ) :
    ∃ (a : ℝ) (Q : Finset ℂ), 0 < a ∧ a < 1 / 2 ∧
      (∀ s : ℂ, twoScaleCoshModel a Q s = 0 → 0 < s.re ∧ s.re < 1) ∧
      ¬ ZerosApproachLine (twoScaleCoshZeros a Q) ∧
      {s : {s : ℂ // twoScaleCoshModel a Q s = 0} | 1 / 2 + a < s.1.re}.Finite ∧
      ¬ LinearEventualToGlobalAt (twoScaleCoshZeros a Q) C := by
  set M : ℝ := max C 1
  have hM1 : 1 ≤ M := le_max_right C 1
  have hMC : C ≤ M := le_max_left C 1
  set a : ℝ := 1 / (8 * M)
  have ha0 : 0 < a := div_pos one_pos (by positivity)
  have ha8 : a ≤ 1 / 8 := by
    dsimp [a]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have ha12 : a < 1 / 2 := by linarith
  set q₀ : ℂ := (3 / 4 : ℂ) + I
  set Q : Finset ℂ := {q₀}
  have hre_cosh_sub : ∀ s : ℂ, Complex.cosh (s - 1 / 2 - a) = 0 → s.re = 1 / 2 + a := by
    intro s hs
    have h := re_eq_half_of_cosh_eq_zero (s := s - a) (by simpa [sub_right_comm] using hs)
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    linarith
  have hre_cosh_add : ∀ s : ℂ, Complex.cosh (s - 1 / 2 + a) = 0 → s.re = 1 / 2 - a := by
    intro s hs
    have h := re_eq_half_of_cosh_eq_zero (s := s + a)
      (by simpa [show s + (a : ℂ) - 1 / 2 = s - 1 / 2 + a by ring] using hs)
    simp only [Complex.add_re, Complex.ofReal_re] at h
    linarith
  have hstrip : ∀ s : ℂ, twoScaleCoshModel a Q s = 0 → 0 < s.re ∧ s.re < 1 := by
    intro s hs
    rcases (twoScaleCoshModel_eq_zero_iff a Q s).mp hs with hc1 | hc2 | ⟨q, hq, hsq⟩
    · have := hre_cosh_sub s hc1; exact ⟨by linarith, by linarith⟩
    · have := hre_cosh_add s hc2; exact ⟨by linarith, by linarith⟩
    · rw [Finset.mem_singleton.mp hq] at hsq
      rcases hsq with rfl | rfl | rfl | rfl <;>
        simp [q₀] <;> constructor <;> norm_num
  have hcol_zero : ∀ n : ℤ,
      twoScaleCoshModel a Q ((1 / 2 + a : ℝ) + (Real.pi * (n + 1 / 2) : ℝ) * I) = 0 := by
    intro n
    refine (twoScaleCoshModel_eq_zero_iff a Q _).mpr (Or.inl ?_)
    have heq : (((1 / 2 + a : ℝ) : ℂ) + (Real.pi * (n + 1 / 2) : ℝ) * I) - 1 / 2 - a =
        (1 / 2 + (Real.pi * (n + 1 / 2) : ℝ) * I) - 1 / 2 := by push_cast; ring
    rw [heq]
    exact cosh_criticalZero n
  have hnotZAL : ¬ ZerosApproachLine (twoScaleCoshZeros a Q) := by
    intro hZ
    have hfin := hZ (a / 2) (half_pos ha0)
    let f : ℤ → {s : ℂ // twoScaleCoshModel a Q s = 0} := fun n =>
      ⟨((1 / 2 + a : ℝ) : ℂ) + (Real.pi * (n + 1 / 2) : ℝ) * I, hcol_zero n⟩
    have hinj : Function.Injective f := by
      intro m n hmn
      have him := congrArg (fun x => x.1.im) hmn
      simp only [f, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at him
      have hmnR : (m : ℝ) + 1 / 2 = (n : ℝ) + 1 / 2 :=
        mul_left_cancel₀ Real.pi_pos.ne' him
      exact Int.cast_injective (by linarith : (m : ℝ) = n)
    refine (infinite_range_of_injective hinj) (hfin.subset ?_)
    rintro _ ⟨n, rfl⟩
    show 1 / 2 + a / 2 < (f n).1.re
    simp only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith
  have hfin_a : {s : {s : ℂ // twoScaleCoshModel a Q s = 0} | 1 / 2 + a < s.1.re}.Finite := by
    set P : Set ℂ := ({q₀, starRingEnd ℂ q₀, 1 - q₀, 1 - starRingEnd ℂ q₀} : Set ℂ)
    refine ((Set.toFinite P).preimage Subtype.val_injective.injOn).subset fun s hs => ?_
    have hre : 1 / 2 + a < s.1.re := hs
    rcases (twoScaleCoshModel_eq_zero_iff a Q s.1).mp s.2 with hc1 | hc2 | ⟨q, hq, hsq⟩
    · have := hre_cosh_sub s.1 hc1; linarith
    · have := hre_cosh_add s.1 hc2; linarith
    · rw [Finset.mem_singleton.mp hq] at hsq
      exact hsq
  have hnotL : ¬ LinearEventualToGlobalAt (twoScaleCoshZeros a Q) C := by
    intro hL
    have hq₀_zero : twoScaleCoshModel a Q q₀ = 0 :=
      (twoScaleCoshModel_eq_zero_iff a Q q₀).mpr
        (Or.inr (Or.inr ⟨q₀, Finset.mem_singleton_self _, Or.inl rfl⟩))
    have hb := hL a ha0.le hfin_a ⟨q₀, hq₀_zero⟩
    have hq₀_re : (twoScaleCoshZeros a Q ⟨q₀, hq₀_zero⟩).re = 3 / 4 := by
      simp [twoScaleCoshZeros, q₀]
    rw [hq₀_re] at hb
    have hCa : C * a ≤ 1 / 8 := by
      calc C * a ≤ M * a := mul_le_mul_of_nonneg_right hMC ha0.le
        _ = 1 / 8 := by dsimp [a]; field_simp
    linarith
  exact ⟨a, Q, ha0, ha12, hstrip, hnotZAL, hfin_a, hnotL⟩

/-! ### Positive integer-norm Euler-product obstruction -/

open ArithmeticPositiveDuality.IntegerNormOneOff in
/-- **Positive Euler products with integer norms and linear counting violate linear AAL at every
slope `C : ℝ`.** -/
theorem integerNormOneOff_not_linearEventualToGlobal (γ : ℝ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      ZerosApproachLine (fun s : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} => (s : ℂ)) ∧
      ∀ C : ℝ, ¬ LinearEventualToGlobalAt
        (fun s : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} => (s : ℂ)) C := by
  obtain ⟨q, a, hq, F, A, hA, hF, hcnt, -, hzeros⟩ := exists_integer_norm_linear_count_one_off γ
  let ρ : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} → ℂ := fun s => (s : ℂ)
  have hZAL : ZerosApproachLine ρ := by
    intro h _
    refine ((Set.toFinite ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ)).preimage
      Subtype.val_injective.injOn).subset fun s _ => ?_
    have hs : (s : ℂ) ∈ {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} := s.2
    rwa [hzeros] at hs
  refine ⟨q, a, hq, F, A, hA, hF, hcnt, hZAL, fun C hL => ?_⟩
  have hR := rightRH_of_zerosApproachLine_of_linearEventualToGlobalAt ρ hZAL hL
  have hmem : (3 / 5 : ℂ) + (γ : ℂ) * I ∈ {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} := by
    rw [hzeros]; exact Set.mem_insert _ _
  have hb := hR ⟨_, hmem⟩
  simp only [ρ, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at hb
  norm_num at hb

end GaloisForLFunctions.InfiniteRankWeilTheory
