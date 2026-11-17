import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheMomentsOfTheStateHaveAPoleAtTheExponentOfEveryZero

/-!
# Without the abscissa law the window masses of the state have the rate of the zeros

Let \`Θ = sup Re ρ\` over the zeros of \`ζ\`, \`F\` the critical state, and at a base \`ℓ > 0\`

  \`m_ν = ∫_{−(ν+1)ℓ}^{−νℓ} |F(u)| e^{−8u} du\`

its window masses.

* **Upper bound, every state** (\`criticalState_windowMass_le\`): \`m_ν ≤ C_a e^{aνℓ}\` at every
  level for every \`a > Θ − ½\`. The moment \`∫ F² e^{−(16−2a)u}\` is finite and
  \`|F| e^{−8u} = (|F| e^{−(8−a)u}) e^{−au}\`.
* **Isolated top** (\`zetaZeroAbscissa_eq_of_isolatedTop\`). If the asymptotic abscissa law fails,
  its failure is an isolated finite top on \`Re = Θ₀ > ½\`; then \`Θ = Θ₀\` is attained.
* **Excursions at every rate below \`Θ − ½\`** (\`criticalState_syndetic_excursions_of_lt\`).
  Without the abscissa law, for every \`a < Θ − ½\` and \`C\`, every run of \`k\` consecutive levels far
  out contains a level with \`m_ν > C e^{aνℓ}\`, \`k\` the size of the top. A smooth bump on
  \`(−ℓ, 0)\` that isolates one top point turns the window pairing into a level sum of the tower
  \`e^{ℓ(ρ − ½)}\` whose top has modulus \`e^{ℓ(Θ − ½)}\`.

So without the abscissa law the exponential rate of the window masses is exactly \`Θ − ½\`
(\`criticalState_exact_window_rate_of_not_asymptoticAbscissaLaw\`). The regimes of the endpoint
moment separate (\`criticalState_endpoint_regimes\`): either \`∫ F² e^{−(17−2Θ)u} = ∞\`, or \`Θ\` is
not attained and the abscissa law holds.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset
open scoped ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### The top of the zeros -/

/-- An isolated top of the zero copies is the zero abscissa. -/
theorem zetaZeroAbscissa_eq_of_isolatedTop {S : Finset XiZeroCopy} {Θ Θ₂ : ℝ}
    (hSne : S.Nonempty) (hΘ : 1 / 2 < Θ) (hΘ₂ : Θ₂ < Θ)
    (hS : ∀ q ∈ S, (zetaConfig q).re = Θ) (hrest : ∀ q ∉ S, (zetaConfig q).re ≤ Θ₂) :
    zetaZeroAbscissa = Θ := by
  obtain ⟨q₀, hq₀⟩ := hSne
  have hle : ∀ q : XiZeroCopy, ((q.1 : ℂ)).re ≤ Θ := fun q => by
    by_cases hq : q ∈ S
    · exact (hS q hq).le
    · exact (hrest q hq).trans hΘ₂.le
  refine le_antisymm ?_ ?_
  · by_contra hlt
    obtain ⟨ρ, hζ, hρ⟩ := exists_zetaZero_lt_re (not_le.mp hlt)
    have h1 : ρ ≠ 1 := fun h => riemannZeta_ne_zero_of_one_le_re (by rw [h]; simp) hζ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_riemannZeta_eq_zero (by linarith) h1 hζ
    have := hle q
    rw [hq] at this
    linarith
  · have h := re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q₀)
    have h' : ((q₀.1 : ℂ)).re = Θ := hS q₀ hq₀
    linarith

/-- **Failure of the abscissa law attains the abscissa** above the critical line. -/
theorem exists_zetaZero_re_eq_abscissa_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa ∧ 1 / 2 < ρ.re := by
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  have habs := zetaZeroAbscissa_eq_of_isolatedTop hSne hΘ hΘ₂ hS hrest
  obtain ⟨q₀, hq₀⟩ := hSne
  have hre : ((q₀.1 : ℂ)).re = Θ := hS q₀ hq₀
  exact ⟨(q₀.1 : ℂ), riemannZeta_xiZeroCopy_eq_zero q₀, by rw [habs, hre], by rw [hre]; exact hΘ⟩

/-- **An unattained abscissa gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_zetaZeroAbscissa_not_attained
    (h : ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨ρ, hζ, hρ, -⟩ := exists_zetaZero_re_eq_abscissa_of_not_asymptoticAbscissaLaw hnot
  exact h ⟨ρ, hζ, hρ⟩

/-! ### Upper bound of the window masses -/

/-- **The window masses grow at most at every rate above \`Θ − ½\`.** For \`a > Θ − ½\` and base
\`ℓ > 0\`, \`∫_{−(ν+1)ℓ}^{−νℓ} |F| e^{−8u} ≤ C e^{aνℓ}\` at every level \`ν\`. -/
theorem criticalState_windowMass_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) :
    ∃ C : ℝ, ∀ ν : ℕ, (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u))) ≤ C * Real.exp (a * ν * ℓ) := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  set b : ℝ := 16 - 2 * a with hb
  have hint : Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) :=
    integrable_sq_mul_exp_of_lt_decayRate hW hthreshold hF (by rw [hb]; linarith)
  set M : ℝ := ∫ u, F u ^ 2 * Real.exp (-(b * u))
  refine ⟨Real.exp (a * ℓ) * ((ℓ + M) / 2), fun ν => ?_⟩
  set S : Set ℝ := Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ))
  set E : ℝ := Real.exp (a * (((ν + 1 : ℕ) : ℝ) * ℓ))
  set g : ℝ → ℝ := fun u => E / 2 * (1 + F u ^ 2 * Real.exp (-(b * u)))
  -- \`|F| e^{−8u} = (|F| e^{−bu/2}) e^{−au}\`, and \`2x ≤ 1 + x²\`.
  have hpt : ∀ u ∈ S, |F u| * Real.exp (-(8 * u)) ≤ g u := by
    intro u hu
    have hsplit : Real.exp (-(8 * u)) = Real.exp (-(b * u) / 2) * Real.exp (-(a * u)) := by
      rw [← Real.exp_add]; congr 1; rw [hb]; ring
    have hexp : Real.exp (-(a * u)) ≤ E := Real.exp_le_exp.mpr (by
      have h1 := hu.1
      have : -u ≤ ((ν + 1 : ℕ) : ℝ) * ℓ := by linarith
      nlinarith)
    have hsq : (|F u| * Real.exp (-(b * u) / 2)) ^ 2 = F u ^ 2 * Real.exp (-(b * u)) := by
      rw [mul_pow, sq_abs, sq (Real.exp _), ← Real.exp_add,
        show -(b * u) / 2 + -(b * u) / 2 = -(b * u) by ring]
    have hx : |F u| * Real.exp (-(b * u) / 2) ≤ (1 + F u ^ 2 * Real.exp (-(b * u))) / 2 := by
      nlinarith [sq_nonneg (|F u| * Real.exp (-(b * u) / 2) - 1)]
    calc |F u| * Real.exp (-(8 * u))
        = (|F u| * Real.exp (-(b * u) / 2)) * Real.exp (-(a * u)) := by rw [hsplit]; ring
      _ ≤ ((1 + F u ^ 2 * Real.exp (-(b * u))) / 2) * E :=
          mul_le_mul hx hexp (Real.exp_pos _).le (by positivity)
      _ = g u := by simp only [g]; ring
  have hSfin : volume S ≠ ⊤ := measure_Icc_lt_top.ne
  have hg : IntegrableOn g S :=
    ((integrableOn_const hSfin).add hint.integrableOn).const_mul _
  have h1 : (∫ u in S, |F u| * Real.exp (-(8 * u))) ≤ ∫ u in S, g u :=
    integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) hg
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hpt))
  have hvol : volume.real S = ℓ := by
    rw [Real.volume_real_Icc_of_le (by push_cast; nlinarith)]
    push_cast; ring
  have h2 : (∫ u in S, g u) ≤ E / 2 * (ℓ + M) := by
    simp only [g]
    rw [integral_const_mul, integral_add (integrableOn_const (C := (1 : ℝ)) hSfin) hint.integrableOn,
      setIntegral_const, hvol, smul_eq_mul, mul_one]
    refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (by positivity)
    exact setIntegral_le_integral hint (Eventually.of_forall fun u => by positivity)
  have hE : E = Real.exp (a * ℓ) * Real.exp (a * ν * ℓ) := by
    simp only [E]; rw [← Real.exp_add]; congr 1; push_cast; ring
  calc (∫ u in S, |F u| * Real.exp (-(8 * u))) ≤ E / 2 * (ℓ + M) := h1.trans h2
    _ = Real.exp (a * ℓ) * ((ℓ + M) / 2) * Real.exp (a * ν * ℓ) := by rw [hE]; ring

/-! ### Excursions at every rate below \`Θ − ½\` -/

/-- A smooth test on \`(−ℓ, 0)\` whose transform is \`1\` at one top point and \`0\` at the others;
the merged tower weight of the state at that point is then nonzero. -/
private theorem exists_topIsolatingBump {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {S : Finset XiZeroCopy} {Θ : ℝ} (hSne : S.Nonempty) (hΘ : 1 / 2 < Θ)
    (hS : ∀ q ∈ S, (zetaConfig q).re = Θ) :
    ∃ (ψ₀ : ℝ → ℂ) (B : ℝ) (q₀ : XiZeroCopy),
      ContDiff ℝ ∞ ψ₀ ∧ HasCompactSupport ψ₀ ∧ (∀ v, v ∉ Ioo (-ℓ) 0 → ψ₀ v = 0) ∧
      0 ≤ B ∧ (∀ v, ‖ψ₀ v‖ ≤ B) ∧ q₀ ∈ S ∧
      (∑ j ∈ S with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀,
        negativeHalfLineLaplace (cx F) (centredZero j) * laplaceTest ψ₀ (centredZero j)) ≠ 0 := by
  classical
  obtain ⟨q₀, hq₀⟩ := hSne
  let P : Finset ℂ := S.image centredZero
  let e : Fin P.card ≃ P := P.equivFin.symm
  have hinj : Function.Injective (fun k : Fin P.card => (e k : ℂ)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  let target : Fin P.card → ℂ := fun k => if (e k : ℂ) = centredZero q₀ then 1 else 0
  obtain ⟨ψ₀, hψ₀, hs₀, hsupp₀, hinterp⟩ :=
    exists_smooth_negInterval_interpolating hℓ (fun k => (e k : ℂ)) hinj target
  have hval : ∀ q ∈ S, laplaceTest ψ₀ (centredZero q) =
      if centredZero q = centredZero q₀ then 1 else 0 := by
    intro q hq
    have hmem : centredZero q ∈ P := mem_image_of_mem centredZero hq
    let k : Fin P.card := e.symm ⟨centredZero q, hmem⟩
    have hk : (e k : ℂ) = centredZero q := by simp [k]
    simpa [target, hk] using hinterp k
  obtain ⟨B₀, hB₀⟩ := hs₀.exists_bound_of_continuous hψ₀.continuous
  refine ⟨ψ₀, max B₀ 0, q₀, hψ₀, hs₀, hsupp₀, le_max_right _ _,
    fun v => (hB₀ v).trans (le_max_left _ _), hq₀, ?_⟩
  -- Only the copies of \`q₀\` itself survive in the merged weight.
  have h1 : ∀ j ∈ S.filter (fun j => frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀),
      negativeHalfLineLaplace (cx F) (centredZero j) * laplaceTest ψ₀ (centredZero j) =
        if centredZero j = centredZero q₀ then
          negativeHalfLineLaplace (cx F) (centredZero q₀) else 0 := by
    intro j hj
    rw [hval j (mem_filter.1 hj).1]
    split_ifs with hz
    · rw [hz, mul_one]
    · rw [mul_zero]
  have hfil : ((S.filter fun j => frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀).filter
      fun j => centredZero j = centredZero q₀) =
      S.filter fun j => centredZero j = centredZero q₀ := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hjS, _⟩, hjz⟩; exact ⟨hjS, hjz⟩
    · rintro ⟨hjS, hjz⟩
      have hcfg : zetaConfig j = zetaConfig q₀ := by
        change (j.1 : ℂ) = (q₀.1 : ℂ)
        change (j.1 : ℂ) - 1 / 2 = (q₀.1 : ℂ) - 1 / 2 at hjz
        linear_combination hjz
      exact ⟨⟨hjS, by simp [frobTower, hcfg]⟩, hjz⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, hfil]
  have hcard_pos : 0 < (S.filter fun j => centredZero j = centredZero q₀).card :=
    Finset.card_pos.2 ⟨q₀, mem_filter.2 ⟨hq₀, rfl⟩⟩
  have hre_pos : 0 ≤ (centredZero q₀).re := by
    have := hS q₀ hq₀
    change ((q₀.1 : ℂ)).re = Θ at this
    simp only [centredZero, Complex.sub_re, this]
    norm_num; linarith
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hcard_pos.ne')
    (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hre_pos)

/-- **Syndetic excursions at every rate below \`Θ − ½\`.** If the asymptotic abscissa law fails,
there is \`k ≥ 1\` (the size of the isolated top) such that for every base \`ℓ > 0\`, every
\`a < Θ − ½\` and every \`C\`, every run of \`k\` consecutive levels beyond some point contains \`ν\`
with \`C e^{aνℓ} < ∫_{−(ν+1)ℓ}^{−νℓ} |F| e^{−8u}\`. -/
theorem criticalState_syndetic_excursions_of_lt (hnot : ¬ RHTower.AsymptoticAbscissaLaw)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ k : ℕ, 0 < k ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ a : ℝ, a < zetaZeroAbscissa - 1 / 2 → ∀ C : ℝ,
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + k ∧
        C * Real.exp (a * ν * ℓ) <
          ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
            |F u| * Real.exp (-(8 * u)) := by
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  have habs := zetaZeroAbscissa_eq_of_isolatedTop hSne hΘ hΘ₂ hS hrest
  refine ⟨S.card, hSne.card_pos, fun ℓ hℓ a ha C => ?_⟩
  rw [habs] at ha
  set a' : ℝ := max a 0
  have ha'Θ : a' < Θ - 1 / 2 := max_lt ha (by linarith)
  obtain ⟨ψ₀, B, q₀, hψ₀, hs₀, hsupp₀, hB0, hbound, hq₀, hvis⟩ :=
    exists_topIsolatingBump hW hthreshold hF hℓ hSne hΘ hS
  have h0 : ∀ x, 0 < x → ψ₀ x = 0 := fun x hx =>
    hsupp₀ x fun hm => lt_irrefl (0 : ℝ) (hx.trans hm.2)
  let b : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ₀ (centredZero q)
  have hb : Summable fun q => ‖b q‖ :=
    (criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ₀ hs₀ h0).summable.norm
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  have haW : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  set K : ℝ := criticalAliasCoefficient W₀ * (B + 1)
  have hK : 0 < K := by positivity
  have hρR : Real.exp (a' * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  obtain ⟨M₀, hM₀⟩ := eventually_forall_window_exists_lt_norm_levelSum (frobTower ℓ zetaConfig) b
    hb S (Real.exp_pos _) (Real.exp_pos _).le hlt_norm hlow_norm (fun q hq _ => htop_norm q hq)
    ⟨q₀, hq₀, hvis⟩ (C := K * max C 0) (Real.exp_pos _).le hρR
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hM₀ M hM
  have hk_le : (S.image (frobTower ℓ zetaConfig)).card ≤ S.card := Finset.card_image_le
  refine ⟨ν, h1, by omega, ?_⟩
  rw [criticalState_levelSum_laplaceTest hW hthreshold hF hψ₀ hs₀ h0 hℓ.le ν,
    norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg haW.le,
    ← Real.exp_nat_mul, show (ν : ℝ) * (a' * ℓ) = a' * (ν : ℝ) * ℓ by ring] at h3
  have hp := norm_statePairing_shift_le hd (by linarith : 0 ≤ B + 1)
    (fun v => (hbound v).trans (by linarith)) hsupp₀ ν
  have h4 : K * max C 0 * Real.exp (a' * (ν : ℝ) * ℓ) <
      K * ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u)) :=
    h3.trans_le (by
      dsimp [K]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp haW.le)
  have h5 : max C 0 * Real.exp (a' * (ν : ℝ) * ℓ) <
      ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u)) := by
    rw [mul_assoc] at h4
    exact lt_of_mul_lt_mul_left h4 hK.le
  have hνℓ : (0 : ℝ) ≤ (ν : ℝ) * ℓ := by positivity
  calc C * Real.exp (a * ν * ℓ) ≤ max C 0 * Real.exp (a * ν * ℓ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (a' * ν * ℓ) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
        have := le_max_left a 0
        nlinarith
    _ < _ := h5

/-! ### The two regimes -/

/-- **E-M20: without the abscissa law the decay of the state is exact.** If the asymptotic
abscissa law fails, the abscissa \`Θ > ½\` is attained, the square moments are finite exactly for
\`b < 17 − 2Θ\`, and at every base the window masses \`∫_{−(ν+1)ℓ}^{−νℓ} |F| e^{−8u}\` have exact
exponential rate \`Θ − ½\`: below \`C e^{aνℓ}\` at every level for \`a > Θ − ½\`, above \`C e^{aνℓ}\`
in every run of \`k\` consecutive levels far out for \`a < Θ − ½\`. -/
theorem criticalState_exact_window_rate_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa ∧ 1 / 2 < ρ.re) ∧
      (∀ b : ℝ, (Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) ↔
        b < 17 - 2 * zetaZeroAbscissa) ∧
      (∀ ℓ : ℝ, 0 < ℓ → ∀ a : ℝ, zetaZeroAbscissa - 1 / 2 < a → ∃ C : ℝ, ∀ ν : ℕ,
        (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
          |F u| * Real.exp (-(8 * u))) ≤ C * Real.exp (a * ν * ℓ)) ∧
      ∃ k : ℕ, 0 < k ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ a : ℝ, a < zetaZeroAbscissa - 1 / 2 → ∀ C : ℝ,
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + k ∧
          C * Real.exp (a * ν * ℓ) <
            ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
              |F u| * Real.exp (-(8 * u)) := by
  obtain ⟨ρ, hζ, hρ, hρh⟩ := exists_zetaZero_re_eq_abscissa_of_not_asymptoticAbscissaLaw hnot
  exact ⟨⟨ρ, hζ, hρ, hρh⟩, integrable_sq_mul_exp_iff_of_attained hW hthreshold hF hζ hρ,
    fun ℓ hℓ a ha => criticalState_windowMass_le hW hthreshold hF hℓ ha,
    criticalState_syndetic_excursions_of_lt hnot hW hthreshold hF⟩

/-- **The endpoint moment separates the regimes.** Either the moment at the decay rate
\`∫ F² e^{−(17−2Θ)u}\` is infinite, or \`Θ\` is not attained and the asymptotic abscissa law
holds. -/
theorem criticalState_endpoint_regimes {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (¬ Integrable fun u => F u ^ 2 * Real.exp (-((17 - 2 * zetaZeroAbscissa) * u))) ∨
      ((¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa) ∧
        RHTower.AsymptoticAbscissaLaw) := by
  by_cases hatt : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa
  · obtain ⟨ρ, hζ, hρ⟩ := hatt
    exact Or.inl fun hint =>
      lt_irrefl _ ((integrable_sq_mul_exp_iff_of_attained hW hthreshold hF hζ hρ _).1 hint)
  · exact Or.inr ⟨hatt, asymptoticAbscissaLaw_of_zetaZeroAbscissa_not_attained hatt⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
