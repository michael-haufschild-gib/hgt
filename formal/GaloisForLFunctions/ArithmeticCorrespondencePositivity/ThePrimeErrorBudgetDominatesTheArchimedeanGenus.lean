import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorEnergyPaysTheCriticalZeros
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.XiDeck

/-!
# The prime-error budget dominates the archimedean genus

Over `𝔽_q` the prime-error slope of a curve is `Σ_β mult(β)² ≥ 2g` (P42): a budget is at least the
number of eigenvalues. Over `ℤ` the zeros are infinite in number, and their regularised count is
the archimedean genus `Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π` over the zeros of `ξ` with multiplicity
(`RHTower.tsum_inv_zero_mul_one_sub_zero`).

A **prime-error budget** is a linear log-energy
`∫_0^L e^{−u}(ψ(⌊e^u⌋) − ⌊e^u⌋)² du ≤ S L + B` for all `L ≥ 0`.

* **A prime-error budget is purity** (`riemannZeta_ne_zero_of_primeError_budget`). The Mellin
  pairing of `ψ(n) − n` is then holomorphic on `Re s > ½` and equals `−ζ′/ζ − ζ` off the zeros;
  a zero right of the line would be a pole of residue `−m_ρ`.
* **The budget dominates the genus** (`poleSharpConstant_le_of_primeError_budget`).
  `2 + γ − log 4π ≤ S`: on the critical line `1/(ρ(1 − ρ)) = 1/|ρ|²`, the `m_ρ` copies of a zero
  contribute `m_ρ/|ρ|² ≤ ‖m_ρ/ρ‖²`, and every finite sum of the latter is at most `S` (P41).
* **Unconditional form** (`not_forall_primeError_energy_le_of_lt_poleSharpConstant`).
  `limsup (log X)⁻¹ ∫_1^X (ψ(x) − x)²/x² dx ≥ 2 + γ − log 4π`.

So the budget of `ℤ` read on the prime error is at least `2λ₁ = 2 + γ − log 4π`, as the budget of a
curve is at least `2g`; the excess `Σ_ρ (m_ρ² − m_ρ)/|ρ|²` counts multiplicity, and equality
needs a simple spectrum and no mass at infinite height.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinPairing)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)

/-- A prime-error budget has nonnegative slope and may be taken with `B ≥ 0`. -/
theorem primeError_budget_normalize {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B) :
    0 ≤ S ∧
      ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + max B 0 := by
  refine ⟨?_, fun L hL => (hlin L hL).trans (by linarith [le_max_left B 0])⟩
  by_contra h
  exact not_forall_logEnergy_le_of_neg primeErrorRow (not_le.mp h) hlin

/-- A zero of `ζ` away from `1` has order at least one. -/
theorem one_le_toNat_analyticOrderAt_riemannZeta {ρ : ℂ} (hz : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have hA := analyticAt_riemannZeta_of_ne_one hρ1
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := fun h =>
    not_eventually_riemannZeta_eq_zero hρ1 (analyticOrderAt_eq_top.mp h)
  have h0 : analyticOrderAt riemannZeta ρ ≠ 0 := fun h => hA.analyticOrderAt_eq_zero.mp h hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at h0 ⊢
  rw [ENat.toNat_coe]
  exact Nat.one_le_iff_ne_zero.mpr fun h => h0 (by rw [h]; rfl)

/-- `0 < t < a` and `Q t < 1` for some `t`. -/
theorem exists_pos_lt_mul_lt_one {a Q : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q) :
    ∃ t : ℝ, 0 < t ∧ t < a ∧ Q * t < 1 := by
  have h0 : 0 < min (a / 2) (1 / (2 * (Q + 1))) := lt_min (by linarith) (by positivity)
  have h1 : min (a / 2) (1 / (2 * (Q + 1))) * (2 * (Q + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  exact ⟨min (a / 2) (1 / (2 * (Q + 1))), h0, (min_le_left _ _).trans_lt (by linarith),
    by nlinarith⟩

/-- **A prime-error budget is purity.** Under a linear prime-error log-energy, `ζ` has no zero right
of the critical line: the Mellin pairing of `ψ(n) − n` is continuous there and equals
`−ζ′/ζ − ζ`, which has a pole of residue `−m_ρ` at a zero. -/
theorem riemannZeta_ne_zero_of_primeError_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hz
  obtain ⟨hS0, hlin'⟩ := primeError_budget_normalize hlin
  have hκ : 0 < ρ.re - 1 / 2 := by linarith
  have hC : 0 ≤ S / (ρ.re - 1 / 2) + max B 0 :=
    add_nonneg (div_nonneg hS0 hκ.le) (le_max_right B 0)
  have hE := fun T => pronic_energy_le_of_linear hS0 (le_max_right B 0) hlin'
    (v := primeErrorRow) hκ T
  have hρ1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hz)
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ; linarith
  have hU : ∀ z : ℂ, ρ.re ≤ z.re → (1 + (ρ.re - 1 / 2)) / 2 < z.re := fun z hz => by linarith
  have hΦ := ArithmeticCorrelationGeometry.differentiableOn_complexMellinPairing_of_energy_growth
    primeErrorRow_zero hC hκ.le hE
  have hΦc : ContinuousAt (fun z => complexMellinPairing primeErrorRow z / z) ρ :=
    ((hΦ.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (hU ρ le_rfl))).continuousAt).div continuousAt_id hρ0
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hΦc 1 one_pos
  obtain ⟨η, hη, M, hp⟩ := exists_logDeriv_symbol_pole_bound hz hρ1 hρ0
  have hm := one_le_toNat_analyticOrderAt_riemannZeta hz hρ1
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  obtain ⟨t, ht0, hta, htQ⟩ := exists_pos_lt_mul_lt_one (a := min η δ)
    (Q := (|M| + (‖complexMellinPairing primeErrorRow ρ / ρ‖ + 1)) * ‖ρ‖) (lt_min hη hδ)
    (by positivity)
  have hzt : ‖(ρ + t) - ρ‖ = t := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hne : ρ + t ≠ ρ := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨hζz, hz1, hb⟩ := hp (ρ + t) (by rw [hzt]; exact hta.trans_le (min_le_left _ _)) hne
  rw [← complexMellinPairing_primeErrorRow_eq hC hκ.le hE
    (hU (ρ + t) (by simp; linarith)) hz1 hζz] at hb
  have hcl := hδ' (show dist (ρ + t) ρ < δ by
    rw [dist_eq_norm, hzt]; exact hta.trans_le (min_le_right _ _))
  rw [dist_eq_norm] at hcl
  have hK := norm_sub_norm_le (complexMellinPairing primeErrorRow (ρ + t) / (ρ + t))
    (complexMellinPairing primeErrorRow ρ / ρ)
  have hpole := norm_sub_norm_le
    (-(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ / ((ρ + t) - ρ))
    (complexMellinPairing primeErrorRow (ρ + t) / (ρ + t))
  rw [norm_sub_rev] at hpole
  have hval : ‖-(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ / ((ρ + t) - ρ)‖ =
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / (‖ρ‖ * t) := by
    rw [add_sub_cancel_left, norm_div, norm_div, norm_neg, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_div]
  rw [hval] at hpole
  have hle : ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / (‖ρ‖ * t) ≤
      |M| + (‖complexMellinPairing primeErrorRow ρ / ρ‖ + 1) := by
    linarith [le_abs_self M]
  rw [div_le_iff₀ (by positivity)] at hle
  have hm' : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by exact_mod_cast hm
  nlinarith

/-- **A prime-error budget implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_primeError_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B) :
    RiemannHypothesis :=
  _root_.RHTower.riemannHypothesis_iff_forall_zero_re_le_half.mpr fun _ hz => by
    by_contra h
    exact riemannZeta_ne_zero_of_primeError_budget hlin (not_le.mp h) hz

/-- Under RH every point of the `ξ` divisor is a critical zero of `ζ`. -/
theorem riemannZeta_eq_zero_and_re_of_xiDivisorSupport (hRH : RiemannHypothesis)
    (ρ : _root_.RHTower.XiDivisorSupport) :
    riemannZeta (ρ : ℂ) = 0 ∧ (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := _root_.RHTower.xi_divisor_support_re_mem_open_unit ρ
  have hne : (ρ : ℂ) ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  have hz : riemannZeta (ρ : ℂ) = 0 :=
    (_root_.RHTower.xi_eq_zero_iff h0 hne).mp (_root_.RHTower.xi_eq_zero_of_mem_divisor_support ρ)
  refine ⟨hz, hRH _ hz ?_ hne⟩
  rintro ⟨n, hn⟩
  rw [hn] at h0
  simp at h0
  linarith

/-- The `ξ`-divisor multiplicity is the order of `ζ`. -/
theorem xiSupportMultiplicity_eq_toNat_analyticOrderAt_riemannZeta
    (ρ : _root_.RHTower.XiDivisorSupport) :
    _root_.RHTower.xiSupportMultiplicity ρ = (analyticOrderAt riemannZeta (ρ : ℂ)).toNat := by
  rw [_root_.RHTower.xiSupportMultiplicity_eq_analyticOrderAt_toNat,
    _root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
      (_root_.RHTower.xi_divisor_support_re_mem_open_unit ρ)]

/-- On the critical line `1/(ρ(1 − ρ)) = 1/|ρ|²`. -/
theorem one_div_mul_one_sub_eq_of_re {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    (1 : ℂ) / (ρ * (1 - ρ)) = ((1 / ‖ρ‖ ^ 2 : ℝ) : ℂ) := by
  have hc : 1 - ρ = (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [hre]; norm_num
  rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Under RH the archimedean genus is the sum of `1/|ρ|²` over the copies of the zeros. -/
theorem poleSharpConstant_eq_tsum_of_riemannHypothesis (hRH : RiemannHypothesis) :
    _root_.RHTower.poleSharpConstant =
      ∑' q : _root_.RHTower.XiZeroCopy, 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← _root_.RHTower.tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_tsum]
  exact tsum_congr fun q =>
    one_div_mul_one_sub_eq_of_re (riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH q.1).2

/-- Under RH the copy sum `Σ_q 1/|ρ_q|²` converges. -/
theorem summable_inv_norm_sq_xiZeroCopy (hRH : RiemannHypothesis) :
    Summable fun q : _root_.RHTower.XiZeroCopy => 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
  refine _root_.RHTower.xiSpectralPoint_inv_sq_summable.of_nonneg_of_le (fun _ => by positivity)
    fun q => ?_
  have hre := (riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH q.1).2
  have h0 : (q.1 : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr (_root_.RHTower.xi_divisor_support_ne_half q.1)
  rw [_root_.RHTower.norm_xiSpectralPoint]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have h1 : ‖(q.1 : ℂ) - 1 / 2‖ ^ 2 = ((q.1 : ℂ).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hre]; ring
  have h2 : ‖(q.1 : ℂ)‖ ^ 2 = 1 / 4 + ((q.1 : ℂ).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre]; ring
  rw [h1, h2]; linarith

/-- The copies of finitely many zeros are counted by their multiplicities:
`Σ_{q ∈ F} 1/|ρ_q|² ≤ Σ_ρ m_ρ/|ρ|²` over the zeros carrying them. -/
theorem sum_copies_le_sum_order (F : Finset _root_.RHTower.XiZeroCopy) :
    ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2 ≤
      ∑ z ∈ (F.image Sigma.fst).map (Function.Embedding.subtype _),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) := by
  set T : Finset _root_.RHTower.XiDivisorSupport := F.image Sigma.fst with hT
  have hsub : F ⊆ T.sigma fun _ => Finset.univ := fun q hq =>
    Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ hq, Finset.mem_univ _⟩
  calc ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2
      ≤ ∑ q ∈ T.sigma (fun _ => Finset.univ), 1 / ‖(q.1 : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ ρ ∈ T, (_root_.RHTower.xiSupportMultiplicity ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        dsimp only
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rfl
    _ = ∑ z ∈ T.map (Function.Embedding.subtype _),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [xiSupportMultiplicity_eq_toNat_analyticOrderAt_riemannZeta]
        rfl

/-- **The prime-error budget dominates the archimedean genus.** Every slope `S` of a prime-error
budget satisfies `2 + γ − log 4π ≤ S`. -/
theorem poleSharpConstant_le_of_primeError_budget {S B : ℝ}
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B) :
    _root_.RHTower.poleSharpConstant ≤ S := by
  have hRH := riemannHypothesis_of_primeError_budget hlin
  have hcrit := riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH
  rw [poleSharpConstant_eq_tsum_of_riemannHypothesis hRH]
  refine Real.tsum_le_of_sum_le (fun _ => by positivity) fun F => ?_
  refine (sum_copies_le_sum_order F).trans ?_
  calc ∑ z ∈ (F.image Sigma.fst).map (Function.Embedding.subtype _),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2)
      ≤ ∑ z ∈ (F.image Sigma.fst).map (Function.Embedding.subtype _),
          ‖(((analyticOrderAt riemannZeta z).toNat : ℕ) : ℂ) / z‖ ^ 2 := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [norm_div, Complex.norm_natCast, div_pow, mul_one_div]
        gcongr
        rcases Nat.eq_zero_or_pos (analyticOrderAt riemannZeta z).toNat with h | h
        · rw [h]; simp
        · have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta z).toNat : ℝ) := by exact_mod_cast h
          nlinarith
    _ ≤ S := by
        by_contra h
        refine not_forall_primeError_energy_le_linear _ (fun z hz => ?_) (not_le.mp h) hlin
        obtain ⟨ρ, -, rfl⟩ := Finset.mem_map.mp hz
        exact hcrit ρ

/-- **Unconditional form.** For `S < 2 + γ − log 4π` the prime-error log-energy is not bounded by
`S L + B`: `limsup (log X)⁻¹ ∫_1^X (ψ(x) − x)²/x² dx ≥ 2 + γ − log 4π`. -/
theorem not_forall_primeError_energy_le_of_lt_poleSharpConstant {S B : ℝ}
    (hS : S < _root_.RHTower.poleSharpConstant) :
    ¬ ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B :=
  fun hlin => absurd (poleSharpConstant_le_of_primeError_budget hlin) (not_le.mpr hS)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
