import GaloisForLFunctions.RHTower.Sieve.MaynardPerronRelevantAggregate
import GaloisForLFunctions.RHTower.Sieve.MaynardLongAmplitudeExclusionTrimmed
import GaloisForLFunctions.RHTower.Sieve.MaynardMobiusAllShort

/-!
# Fixed-abscissa high-amplitude selection

Large values are selected from the Perron-visible aggregate at fixed abscissa `c`, with independent
Maynard amplitude `alpha`.  Above the long-factor deficit threshold, every selected core is
all-short; robust greedy grouping then produces a finite selection label with exponent
`alpha - c`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Selection remembers both eligibility and Perron visibility. -/
def IsHeathBrownPerronRelevantEligibleSelection
    (L X k : ℕ) {T0 t e : ℝ} (s : ℂ)
    (label : HeathBrownSelectionLabel L X k) : Prop :=
  IsHeathBrownBoxPerronRelevant X k label.1 ∧
    IsHeathBrownEligibleSelection L X k (T0 := T0) (t := t) (e := e) s label

/-- Perron-visible aggregate to robust group.  Shortness is required only for the selected box,
after its core lower bound has been established. -/
theorem exists_heathBrown_perronRelevant_eligible_robust_group_of_large
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (hV : 0 < V) (s : ℂ)
    (haggregate : V ≤
      ‖heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t s‖)
    (hshort : ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box →
      IsHeathBrownBoxPerronRelevant X k box →
      (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ →
      ∀ i : HeathBrownBoxFactorIndex k box.m,
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent box.a box.b box.q i) ≤ 2 * t)
    (hreserve : ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box →
      IsHeathBrownBoxPerronRelevant X k box →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤ V) :
    ∃ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxPerronRelevant X k box ∧
      ∃ u : Finset (HeathBrownBoxFactorIndex k box.m), u.Nonempty ∧
        let beta := ∑ i ∈ u,
          dyadicLogExponent T0
            (heathBrownBoxFactorExponent box.a box.b box.q i)
        t ≤ beta ∧ beta < 4 * t ∧
          u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k box.m) ∧
          ((groupedDyadicLower
            (fun i : {i // i ∈ u} =>
              heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) =
              T0 ^ beta ∧
          ((groupedDyadicLower
            (fun i : {i // i ∈ u} =>
              heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) ^ e ≤
            ‖∏ i : {i // i ∈ u}, LSeries
              (complexCoeff (arithmeticDyadicBlock
                (heathBrownFactorBase L X
                  (heathBrownBoxFactorKind k box.m i))
                (heathBrownBoxFactorExponent box.a box.b box.q i))) s‖ := by
  obtain ⟨box, helig, hrel, hterm⟩ :=
    exists_large_perronRelevant_eligible_heathBrownBox
      L X k hk T0 t s hV haggregate
  have hterm' : V ≤ heathBrownEligibleBoxCost L X k *
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
    dsimp [heathBrownBoxTerm] at hterm
    rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core] at hterm
    have hchoose : (k.choose box.m : ℝ) ≤ (2 ^ k : ℝ) := by
      exact_mod_cast Nat.choose_le_two_pow k box.m
    calc
      V ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((k.choose box.m : ℝ) *
            ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖) := hterm
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((2 ^ k : ℝ) *
            ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖) := by
        gcongr
      _ = heathBrownEligibleBoxCost L X k *
          ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
        simp [heathBrownEligibleBoxCost, mul_assoc]
  have hscaled := (hreserve box helig hrel).trans hterm'
  have hcost := heathBrownEligibleBoxCost_pos L X k hk
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤
          ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ :=
    (mul_le_mul_iff_right₀ hcost).mp hscaled
  have htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k box.m,
      dyadicLogExponent T0
        (heathBrownBoxFactorExponent box.a box.b box.q i) := by
    simpa [IsHeathBrownBoxEligible, heathBrownBoxTotalExponent] using helig
  obtain ⟨u, hu⟩ := exists_heathBrown_box_dyadic_robust_group
    L X k box.m box.a box.b box.q hT0 ht
      (hshort box helig hrel hcore) htotal s hcore
  exact ⟨box, helig, hrel, u, hu⟩

theorem exists_heathBrownPerronRelevantEligibleSelection_label
    (L X k : ℕ) (hk : 0 < k) {T0 t e V : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t) (hV : 0 < V) (s : ℂ)
    (haggregate : V ≤
      ‖heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t s‖)
    (hshort : ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box →
      IsHeathBrownBoxPerronRelevant X k box →
      (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ →
      ∀ i : HeathBrownBoxFactorIndex k box.m,
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent box.a box.b box.q i) ≤ 2 * t)
    (hreserve : ∀ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box →
      IsHeathBrownBoxPerronRelevant X k box →
        heathBrownEligibleBoxCost L X k *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤ V) :
    ∃ label : HeathBrownSelectionLabel L X k,
      IsHeathBrownPerronRelevantEligibleSelection L X k
        (T0 := T0) (t := t) (e := e) s label := by
  obtain ⟨box, helig, hrel, u, hune, hulower, huupper, hucard, hulength, hularge⟩ :=
    exists_heathBrown_perronRelevant_eligible_robust_group_of_large
      L X k hk hT0 ht hV s haggregate hshort hreserve
  let label : HeathBrownSelectionLabel L X k := ⟨box, u⟩
  refine ⟨label, hrel, helig, ?_⟩
  dsimp [IsHeathBrownAggregateSelection, label]
  exact ⟨hune, hulower, huupper, hucard, hulength, hularge⟩

/-- **Uniform high-amplitude coloring at fixed Perron abscissa.**  Every long zeta/log atom would
force `alpha ≤ 1-d`; above that boundary selected boxes are all-short and share finite labels. -/
theorem eventually_exists_canonical_sixty_perronRelevant_coloring_at_high_amplitude :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ c alpha V : ℝ, 0 ≤ c →
          1 - maynardLongGlobalAmplitudeDeficit < alpha → 0 < V →
          ∀ S : Finset ℕ, ∀ lam : ℕ → ℝ,
            (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
            (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
              ∀ r ∈ S,
                V ≤ ‖heathBrownPerronRelevantEligibleDyadicAggregate
                  L X 60 T (mu / 120)
                    ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
            (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
              ∀ box : HeathBrownBoxChoice L X 60,
                IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
                IsHeathBrownBoxPerronRelevant X 60 box →
                heathBrownEligibleBoxCost L X 60 *
                  (groupedDyadicLower
                    (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                      (alpha - c) ≤ V) →
            ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
              (L : ℝ) ≤ T ^ (2 * (mu / 120)) ∧
              ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
                ∀ r ∈ S,
                  IsHeathBrownPerronRelevantEligibleSelection L X 60
                    (T0 := T) (t := mu / 120) (e := alpha - c)
                    ((c : ℂ) + (lam r : ℝ) * Complex.I) (color r) := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_maynard_perronRelevant_eligible_long_factor_global_deficit]
      with T hready hlongExclude
  intro X hX mu hmu_lo hmu_hi hXscale c alpha V hc halpha hV
    S lam hband haggregate hreserve
  have ht : 0 < mu / 120 := by linarith
  have hX120 : (X : ℝ) ≤ T ^ (120 * (mu / 120)) := by
    have hexponent : 120 * (mu / 120) = mu := by ring
    rw [hexponent]
    exact hXscale
  obtain ⟨L, hL, hXL, hcut⟩ :=
    exists_maynardMoebiusCutoff_sixty hready.1 ht.le hX120
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hready.1 hL hcut i hi
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        IsHeathBrownPerronRelevantEligibleSelection L X 60
          (T0 := T) (t := mu / 120) (e := alpha - c)
          ((c : ℂ) + (lam r : ℝ) * Complex.I) label := by
    intro r hr
    apply exists_heathBrownPerronRelevantEligibleSelection_label
      L X 60 (by norm_num) hready.1 ht hV
        ((c : ℂ) + (lam r : ℝ) * Complex.I)
        (haggregate L hL hXL r hr)
    · intro box helig hrel hcore i
      by_contra hnot
      have hilong : 2 * (mu / 120) < dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) := lt_of_not_ge hnot
      have hkind := heathBrown_factorKind_eq_zeta_or_log_of_long
        box (hmobius box) i hilong
      have hdeficit := hlongExclude X hX mu hmu_lo hmu_hi hXscale
        L hL 60 box helig hrel c (lam r) alpha hc
          (hband r hr).1 (hband r hr).2 i hkind hilong hcore
      linarith
    · exact hreserve L hL hXL
  choose selected hselected using hpoint
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨L, hL, hXL, hcut, color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

end RHTower.Sieve
