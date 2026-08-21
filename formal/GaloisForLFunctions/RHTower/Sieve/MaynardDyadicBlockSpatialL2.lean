import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockObservation
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientSpatialBridge
import GaloisForLFunctions.RHTower.Sieve.MaynardPositiveMellinKernel
import GaloisForLFunctions.HTGeometry.BorelGrowthLemma

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set

private theorem arithmeticFunction_sum_apply_dyadicBlockL2
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

/-- Every nonzero coefficient in an observation cone lies above its physical lower edge. -/
theorem lowerSupport_heathBrownObservedEligiblePacket
    (L X k : ℕ) (T0 t N R : ℝ) {n : ℕ}
    (hn : complexCoeff
      (heathBrownObservedEligiblePacket L X k T0 t N R) n ≠ 0) :
    N / (2 ^ (2 * k) : ℝ) < (n : ℝ) := by
  classical
  by_contra hnot
  have hnUpper : (n : ℝ) ≤ N / (2 ^ (2 * k) : ℝ) := le_of_not_gt hnot
  have hpacket : heathBrownObservedEligiblePacket L X k T0 t N R n = 0 := by
    rw [heathBrownObservedEligiblePacket,
      arithmeticFunction_sum_apply_dyadicBlockL2]
    apply Finset.sum_eq_zero
    intro box _hbox
    by_cases hbox : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box
    · simp only [hbox]
      apply vanishesBelow_heathBrownDyadicTermBox
      have hlower := windowRelevant_heathBrownBox_coreLower_gt hbox.2.1
      have hnReal : (n : ℝ) <
          (heathBrownDyadicCoreLower
            (k - box.m) box.a box.b box.q : ℝ) := by
        rw [← groupedDyadicLower_heathBrownBoxFactorExponent]
        exact hnUpper.trans_lt hlower
      exact_mod_cast hnReal
    · simp [hbox]
  apply hn
  simp [complexCoeff_apply, hpacket]

/-- The observation-cone subpacket obeys the same fixed divisor-power coefficient envelope as the
complete window-relevant packet. -/
theorem norm_complexCoeff_heathBrownObservedEligiblePacket_le
    (L X k : ℕ) (T0 t N R : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖complexCoeff (heathBrownObservedEligiblePacket L X k T0 t N R) n‖ ≤
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
  classical
  have hdivNat : 1 ≤ n.divisors.card := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩)
  have hdiv : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by exact_mod_cast hdivNat
  have hterm : ∀ box : HeathBrownBoxChoice L X k,
      ‖(if IsHeathBrownBoxEligible L X k T0 t box ∧
            IsHeathBrownBoxObservedRelevant N R X k box then
          heathBrownDyadicTermBox L X k box.m box.a box.b box.q
        else 0) n‖ ≤
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
    intro box
    by_cases hbox : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box
    · simp only [hbox]
      have hbase :=
        norm_complexCoeff_heathBrownDyadicTermBox_le_divisors_pow_mul_log
          L X k box.m box.a box.b box.q hn
      have hchooseNat : k.choose box.m ≤ 2 ^ k := Nat.choose_le_two_pow k box.m
      have hchoose : (k.choose box.m : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast hchooseNat
      have hm : box.m < k := box.1.isLt
      have hexponent :
          (k - box.m) + (k - box.m - 1) + 2 ≤ 2 * k + 1 := by omega
      have hpow :
          (n.divisors.card : ℝ) ^
              ((k - box.m) + (k - box.m - 1) + 2) ≤
            (n.divisors.card : ℝ) ^ (2 * k + 1) :=
        pow_le_pow_right₀ hdiv hexponent
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      have hbaseReal :
          ‖heathBrownDyadicTermBox L X k box.m box.a box.b box.q n‖ ≤
            (k.choose box.m : ℝ) *
              ((n.divisors.card : ℝ) ^
                  ((k - box.m) + (k - box.m - 1) + 2) *
                Real.log (n : ℝ)) := by
        simpa [complexCoeff_apply, Complex.norm_real, Real.norm_eq_abs] using hbase
      exact hbaseReal.trans <| by
        exact mul_le_mul hchoose
          (mul_le_mul_of_nonneg_right hpow hlog)
          (mul_nonneg (pow_nonneg (by positivity) _) hlog)
          (by positivity)
    · have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      simp [hbox, mul_nonneg (pow_nonneg (by positivity) _) hlog]
  rw [complexCoeff_apply, heathBrownObservedEligiblePacket,
    arithmeticFunction_sum_apply_dyadicBlockL2, Complex.norm_real]
  calc
    ‖∑ box : HeathBrownBoxChoice L X k,
        (if IsHeathBrownBoxEligible L X k T0 t box ∧
              IsHeathBrownBoxObservedRelevant N R X k box then
            heathBrownDyadicTermBox L X k box.m box.a box.b box.q
          else 0) n‖ ≤
        ∑ box : HeathBrownBoxChoice L X k,
          ‖(if IsHeathBrownBoxEligible L X k T0 t box ∧
                IsHeathBrownBoxObservedRelevant N R X k box then
              heathBrownDyadicTermBox L X k box.m box.a box.b box.q
            else 0) n‖ := norm_sum_le _ _
    _ ≤ ∑ _box : HeathBrownBoxChoice L X k,
        (((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ))) := by
      exact Finset.sum_le_sum fun box _ => hterm box
    _ = (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Summed coefficient envelope for one fixed observation cone. -/
theorem sum_norm_complexCoeff_heathBrownObservedEligiblePacket_le_fixedPolylog
    (L X k : ℕ) (T0 t N R : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M,
        ‖complexCoeff (heathBrownObservedEligiblePacket L X k T0 t N R) n‖ ≤
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
          ((M : ℝ) *
            (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1)) := by
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  let C : ℝ := (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
    ((2 ^ k : ℕ) : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖complexCoeff (heathBrownObservedEligiblePacket L X k T0 t N R) n‖ ≤
        C * Real.log (M : ℝ) *
          (n.divisors.card : ℝ) ^ (2 * k + 1) := by
    intro n hnmem
    have hnIcc := Finset.mem_Icc.mp hnmem
    have hcoeff := norm_complexCoeff_heathBrownObservedEligiblePacket_le
      L X k T0 t N R hnIcc.1
    have hlog : Real.log (n : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast hnIcc.1) (by exact_mod_cast hnIcc.2)
    have hdiv0 : 0 ≤ (n.divisors.card : ℝ) ^ (2 * k + 1) := by positivity
    dsimp only [C]
    calc
      ‖complexCoeff (heathBrownObservedEligiblePacket L X k T0 t N R) n‖ ≤
          (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := hcoeff
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (M : ℝ)) := by
          gcongr
      _ = (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
              (n.divisors.card : ℝ) ^ (2 * k + 1) := by ring
  have hmoment := sum_card_divisors_pow_le_polylog (2 * k + 1) M hM
  calc
    ∑ n ∈ Finset.Icc 1 M,
        ‖complexCoeff (heathBrownObservedEligiblePacket L X k T0 t N R) n‖ ≤
        ∑ n ∈ Finset.Icc 1 M,
          C * Real.log (M : ℝ) *
            (n.divisors.card : ℝ) ^ (2 * k + 1) :=
      Finset.sum_le_sum hterm
    _ = C * Real.log (M : ℝ) *
        (∑ n ∈ Finset.Icc 1 M,
          (n.divisors.card : ℝ) ^ (2 * k + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ C * Real.log (M : ℝ) *
        ((M : ℝ) *
          (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1)) :=
      mul_le_mul_of_nonneg_left hmoment (mul_nonneg hC hlogM)
    _ = _ := rfl

/-- A fixed observation-cone aggregate has the same uniform fixed-polylog envelope as its ambient
window-relevant packet. -/
theorem norm_heathBrownObservedEligibleDyadicAggregate_le_fixedPolylog
    (L X k : ℕ) (hX : 1 ≤ X) (T0 t N R sigma y : ℝ)
    (hN : 0 < N) (hsigma : 0 ≤ sigma) :
    ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k N sigma := by
  let F := heathBrownObservedEligiblePacket L X k T0 t N R
  let M : ℕ := 2 ^ (2 * k) * X
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  have hM : 1 ≤ M := by
    dsimp only [M]
    simpa only [one_mul] using Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hD : 0 < D := by dsimp only [D]; positivity
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro hzero
      apply hn
      simp [complexCoeff_apply, hzero]
    dsimp only [F] at hnF
    exact upperSupported_heathBrownObservedEligiblePacket L X k T0 t N R n hnF
  have hweight : ∀ n ∈ Finset.Icc 1 M,
      ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) ≤
        D ^ (-sigma) * ‖complexCoeff F n‖ := by
    intro n hnmem
    by_cases hn : complexCoeff F n = 0
    · have hFn : F n = 0 := by
        rw [complexCoeff_apply] at hn
        exact Complex.ofReal_eq_zero.mp hn
      simp [hFn]
    · have hlower := lowerSupport_heathBrownObservedEligiblePacket
          L X k T0 t N R hn
      have hpow : (n : ℝ) ^ (-sigma) ≤ D ^ (-sigma) :=
        Real.rpow_le_rpow_of_nonpos hD hlower.le (by linarith)
      calc
        ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) ≤
            ‖complexCoeff F n‖ * D ^ (-sigma) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = D ^ (-sigma) * ‖complexCoeff F n‖ := by ring
  have hseries := norm_LSeries_le_sum_of_support hs0 hsupp sigma y
  rw [LSeries_heathBrownObservedEligiblePacket] at hseries
  calc
    ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤
        ∑ n ∈ Finset.Icc 1 M,
          ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) := hseries
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
          D ^ (-sigma) * ‖complexCoeff F n‖ := Finset.sum_le_sum hweight
    _ = D ^ (-sigma) *
        (∑ n ∈ Finset.Icc 1 M, ‖complexCoeff F n‖) := by
      rw [Finset.mul_sum]
    _ ≤ D ^ (-sigma) *
        ((Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
            ((M : ℝ) *
              (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_norm_complexCoeff_heathBrownObservedEligiblePacket_le_fixedPolylog
          L X k T0 t N R hM)
        (Real.rpow_nonneg hD.le _)
    _ = _ := rfl

/-- One fixed observation-cone aggregate is continuous on every vertical line. -/
theorem continuous_heathBrownObservedEligibleDyadicAggregate_line
    (L X k : ℕ) (T0 t N R sigma : ℝ) :
    Continuous (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
        ((sigma : ℂ) + (y : ℝ) * I)) := by
  let F := heathBrownObservedEligiblePacket L X k T0 t N R
  let M : ℕ := 2 ^ (2 * k) * X
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro h
      apply hn
      simp [complexCoeff_apply, h]
    exact upperSupported_heathBrownObservedEligiblePacket L X k T0 t N R n hnF
  have hcont := continuous_LSeries_line_of_support hzero hsupp sigma
  refine hcont.congr (fun y => ?_)
  exact LSeries_heathBrownObservedEligiblePacket L X k T0 t N R _

/-- One family of unit-cell maximizers controls the fixed observation-cone aggregate before the
physical base varies. -/
theorem exists_heathBrownObservedEligibleDyadicAggregate_unitCell_maximizers
    (L X k : ℕ) (T0 t N R : ℝ) :
    ∃ c : ℕ → ℝ,
      ∀ m : ℕ,
        c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
            ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
              ((1 : ℂ) + (c m : ℝ) * I)‖ := by
  let A : ℝ → ℂ := fun y =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t N R
      ((1 : ℂ) + (y : ℝ) * I)
  have hA : Continuous A :=
    continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t N R 1
  have hcell : ∀ m : ℕ, ∃ y ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
      IsMaxOn (fun z => ‖A z‖) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) y := by
    intro m
    refine isCompact_Icc.exists_isMaxOn ?_ hA.norm.continuousOn
    exact Set.nonempty_Icc.mpr (by linarith)
  choose c hcmem hcmax using hcell
  refine ⟨c, ?_⟩
  intro m
  refine ⟨hcmem m, ?_⟩
  intro u hu
  have hmu : (m : ℝ) + u ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
    constructor <;> linarith [hu.1, hu.2]
  exact hcmax m hmu

/-- Exact dyadic amplitude band of fixed unit-cell maxima. -/
def maynardUnitCellAmplitudeBand
    (U : Finset ℕ) (A : ℝ → ℂ) (c : ℕ → ℝ) (V : ℝ) : Finset ℕ :=
  U.filter fun m => V ≤ ‖A (c m)‖ ∧ ‖A (c m)‖ < 2 * V

theorem maynardUnitCellAmplitudeBand_subset
    (U : Finset ℕ) (A : ℝ → ℂ) (c : ℕ → ℝ) (V : ℝ) :
    maynardUnitCellAmplitudeBand U A c V ⊆ U := by
  exact Finset.filter_subset _ _

theorem maynardUnitCellAmplitudeBand_lower
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ} {V : ℝ}
    {m : ℕ} (hm : m ∈ maynardUnitCellAmplitudeBand U A c V) :
    V ≤ ‖A (c m)‖ := by
  exact (Finset.mem_filter.mp hm).2.1

theorem maynardUnitCellAmplitudeBand_upper
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ} {V : ℝ}
    {m : ℕ} (hm : m ∈ maynardUnitCellAmplitudeBand U A c V) :
    ‖A (c m)‖ ≤ 2 * V := by
  exact (Finset.mem_filter.mp hm).2.2.le

/-- Every capped non-base cell maximum belongs to one finite dyadic amplitude band. -/
theorem exists_mem_maynardUnitCellAmplitudeBand
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} {Q m : ℕ} (hv : 0 < v) (hmU : m ∈ U)
    (hlow : v ≤ ‖A (c m)‖)
    (hhigh : ‖A (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v) :
    ∃ q < Q, m ∈ maynardUnitCellAmplitudeBand U A c
      (((2 ^ q : ℕ) : ℝ) * v) := by
  have hx : 1 ≤ ‖A (c m)‖ / v := (le_div_iff₀ hv).2 (by simpa using hlow)
  obtain ⟨q, hqlo, hqhi⟩ :=
    GaloisForLFunctions.Nevanlinna.exists_dyadic_band hx
  have hpowcast : ∀ j : ℕ, (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := by
    intro j
    norm_cast
  have hloV : ((2 ^ q : ℕ) : ℝ) * v ≤ ‖A (c m)‖ := by
    rw [← hpowcast q]
    exact (le_div_iff₀ hv).1 hqlo
  have huppV : ‖A (c m)‖ < 2 * (((2 ^ q : ℕ) : ℝ) * v) := by
    have h := (div_lt_iff₀ hv).1 hqhi
    rw [pow_succ, hpowcast q] at h
    nlinarith
  have hqQ : q < Q := by
    by_contra hnot
    have hQq : Q ≤ q := Nat.le_of_not_gt hnot
    have hpNat : 2 ^ Q ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hQq
    have hp : ((2 ^ Q : ℕ) : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast hpNat
    have hcontra : ((2 ^ Q : ℕ) : ℝ) * v ≤ ‖A (c m)‖ :=
      (mul_le_mul_of_nonneg_right hp hv.le).trans hloV
    exact (not_lt_of_ge hcontra) hhigh
  refine ⟨q, hqQ, ?_⟩
  exact Finset.mem_filter.mpr ⟨hmU, hloV, huppV⟩

/-- Cells below the first dyadic threshold. -/
def maynardUnitCellBaseAmplitudeSet
    (U : Finset ℕ) (A : ℝ → ℂ) (c : ℕ → ℝ) (v : ℝ) : Finset ℕ :=
  U.filter fun m => ‖A (c m)‖ < v

/-- Union of the first `Q` half-open dyadic amplitude bands. -/
def maynardUnitCellAmplitudeBands
    (U : Finset ℕ) (A : ℝ → ℂ) (c : ℕ → ℝ)
    (v : ℝ) (Q : ℕ) : Finset ℕ :=
  (Finset.range Q).biUnion fun q =>
    maynardUnitCellAmplitudeBand U A c (((2 ^ q : ℕ) : ℝ) * v)

/-- Base layer and finitely many dyadic bands cover every capped cell maximum. -/
theorem maynardUnitCellBaseAmplitudeSet_union_bands_eq
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} {Q : ℕ} (hv : 0 < v)
    (hcap : ∀ m ∈ U, ‖A (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v) :
    maynardUnitCellBaseAmplitudeSet U A c v ∪
        maynardUnitCellAmplitudeBands U A c v Q = U := by
  classical
  apply Finset.Subset.antisymm
  · intro m hm
    rcases Finset.mem_union.mp hm with hbase | hbands
    · exact (Finset.mem_filter.mp hbase).1
    · rw [maynardUnitCellAmplitudeBands, Finset.mem_biUnion] at hbands
      obtain ⟨q, hq, hmBand⟩ := hbands
      exact maynardUnitCellAmplitudeBand_subset U A c
        (((2 ^ q : ℕ) : ℝ) * v) hmBand
  · intro m hmU
    by_cases hbase : ‖A (c m)‖ < v
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hmU, hbase⟩
    · have hlow : v ≤ ‖A (c m)‖ := le_of_not_gt hbase
      obtain ⟨q, hqQ, hmBand⟩ :=
        exists_mem_maynardUnitCellAmplitudeBand hv hmU hlow (hcap m hmU)
      apply Finset.mem_union.mpr
      right
      rw [maynardUnitCellAmplitudeBands, Finset.mem_biUnion]
      exact ⟨q, Finset.mem_range.mpr hqQ, hmBand⟩

/-- Distinct dyadic amplitude bands are disjoint. -/
theorem disjoint_maynardUnitCellAmplitudeBand_of_lt
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) {q r : ℕ} (hqr : q < r) :
    Disjoint
      (maynardUnitCellAmplitudeBand U A c (((2 ^ q : ℕ) : ℝ) * v))
      (maynardUnitCellAmplitudeBand U A c (((2 ^ r : ℕ) : ℝ) * v)) := by
  rw [Finset.disjoint_left]
  intro m hmq hmr
  have hu := (Finset.mem_filter.mp hmq).2.2
  have hl := (Finset.mem_filter.mp hmr).2.1
  have hpNat : 2 ^ (q + 1) ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : ((2 ^ (q + 1) : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
    exact_mod_cast hpNat
  have hthreshold :
      2 * (((2 ^ q : ℕ) : ℝ) * v) ≤ ((2 ^ r : ℕ) : ℝ) * v := by
    calc
      2 * (((2 ^ q : ℕ) : ℝ) * v) =
          ((2 ^ (q + 1) : ℕ) : ℝ) * v := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ ((2 ^ r : ℕ) : ℝ) * v :=
        mul_le_mul_of_nonneg_right hp hv.le
  exact (not_lt_of_ge (hthreshold.trans hl)) hu

/-- The base amplitude layer is disjoint from every positive dyadic band. -/
theorem disjoint_maynardUnitCellBaseAmplitudeSet_amplitudeBand
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) (q : ℕ) :
    Disjoint (maynardUnitCellBaseAmplitudeSet U A c v)
      (maynardUnitCellAmplitudeBand U A c (((2 ^ q : ℕ) : ℝ) * v)) := by
  rw [Finset.disjoint_left]
  intro m hbase hband
  have hu := (Finset.mem_filter.mp hbase).2
  have hl := (Finset.mem_filter.mp hband).2.1
  have hpNat : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by exact_mod_cast hpNat
  have hthreshold : v ≤ ((2 ^ q : ℕ) : ℝ) * v := by
    nlinarith
  exact (not_lt_of_ge (hthreshold.trans hl)) hu

/-- Physical selected-cell packets add exactly over disjoint cell families. -/
theorem maynardFixedAmbientPhysicalDefectPacket_union
    {S U : Finset ℕ} (hdisj : Disjoint S U)
    {a : ℝ → ℂ} (ha : Continuous a)
    {lambda N R H : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) :
    maynardFixedAmbientPhysicalDefectPacket (S ∪ U) a lambda N R H 1 =
      maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1 +
        maynardFixedAmbientPhysicalDefectPacket U a lambda N R H 1 := by
  classical
  have hbase : 0 < lambda * N := mul_pos hlambda hN
  have hwidthR : 0 < lambda * R := mul_pos hlambda hR
  have hwidthH : 0 < lambda * H := mul_pos hlambda hH
  have hKR := continuous_routeTNormalizedSmoothWindowMellin_line
    hbase hwidthR (by norm_num : (0 : ℝ) < 1)
  have hKH := continuous_routeTNormalizedSmoothWindowMellin_line
    hbase hwidthH (by norm_num : (0 : ℝ) < 1)
  have hcont : ∀ P : Finset ℕ, Continuous (fun u : ℝ =>
      ∑ m ∈ P, a ((m : ℝ) + u) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) * I)) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) * I)))) := by
    intro P
    apply continuous_finsetSum P
    intro m hm
    let shift : ℝ → ℝ := fun u => (m : ℝ) + u
    have hshift : Continuous shift := continuous_const.add continuous_id
    exact (ha.comp hshift).mul ((hKR.sub hKH).comp hshift)
  rw [maynardFixedAmbientPhysicalDefectPacket,
    maynardFixedAmbientPhysicalDefectPacket,
    maynardFixedAmbientPhysicalDefectPacket]
  simp_rw [Finset.sum_union hdisj]
  exact intervalIntegral.integral_add
    ((hcont S).intervalIntegrable 0 1) ((hcont U).intervalIntegrable 0 1)

theorem maynardUnitCellAmplitudeBands_succ
    (U : Finset ℕ) (A : ℝ → ℂ) (c : ℕ → ℝ)
    (v : ℝ) (Q : ℕ) :
    maynardUnitCellAmplitudeBands U A c v (Q + 1) =
      maynardUnitCellAmplitudeBands U A c v Q ∪
        maynardUnitCellAmplitudeBand U A c (((2 ^ Q : ℕ) : ℝ) * v) := by
  classical
  simp [maynardUnitCellAmplitudeBands, Finset.range_add_one, Finset.union_comm]

theorem disjoint_maynardUnitCellAmplitudeBands_next
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) (Q : ℕ) :
    Disjoint (maynardUnitCellAmplitudeBands U A c v Q)
      (maynardUnitCellAmplitudeBand U A c (((2 ^ Q : ℕ) : ℝ) * v)) := by
  classical
  rw [Finset.disjoint_left]
  intro m hbands hnext
  rw [maynardUnitCellAmplitudeBands, Finset.mem_biUnion] at hbands
  obtain ⟨q, hq, hmq⟩ := hbands
  have hqQ : q < Q := Finset.mem_range.mp hq
  exact Finset.disjoint_left.mp
    (disjoint_maynardUnitCellAmplitudeBand_of_lt hv hqQ) hmq hnext

theorem disjoint_maynardUnitCellBaseAmplitudeSet_bands
    {U : Finset ℕ} {A : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) (Q : ℕ) :
    Disjoint (maynardUnitCellBaseAmplitudeSet U A c v)
      (maynardUnitCellAmplitudeBands U A c v Q) := by
  classical
  rw [Finset.disjoint_left]
  intro m hbase hbands
  rw [maynardUnitCellAmplitudeBands, Finset.mem_biUnion] at hbands
  obtain ⟨q, hq, hmq⟩ := hbands
  exact Finset.disjoint_left.mp
    (disjoint_maynardUnitCellBaseAmplitudeSet_amplitudeBand hv q) hbase hmq

/-- The packet of all capped dyadic bands is exactly the finite sum of the individual fixed-band
packets. -/
theorem maynardFixedAmbientPhysicalDefectPacket_amplitudeBands_eq_sum
    {U : Finset ℕ} {Aline : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) (ha : Continuous Aline)
    {lambda N R H : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (Q : ℕ) :
    maynardFixedAmbientPhysicalDefectPacket
        (maynardUnitCellAmplitudeBands U Aline c v Q)
        Aline lambda N R H 1 =
      ∑ q ∈ Finset.range Q,
        maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellAmplitudeBand U Aline c
            (((2 ^ q : ℕ) : ℝ) * v)) Aline lambda N R H 1 := by
  induction Q with
  | zero =>
      simp [maynardUnitCellAmplitudeBands,
        maynardFixedAmbientPhysicalDefectPacket]
  | succ Q ih =>
      rw [show Q + 1 = Q.succ by omega,
        maynardUnitCellAmplitudeBands_succ]
      rw [maynardFixedAmbientPhysicalDefectPacket_union
        (disjoint_maynardUnitCellAmplitudeBands_next hv Q)
        ha hlambda hN hR hH, ih]
      rw [Finset.sum_range_succ]

/-- Exact base-plus-dyadic-band decomposition of a capped physical packet. -/
theorem maynardFixedAmbientPhysicalDefectPacket_eq_base_add_sum_amplitudeBands
    {U : Finset ℕ} {Aline : ℝ → ℂ} {c : ℕ → ℝ}
    {v : ℝ} (hv : 0 < v) {Q : ℕ}
    (hcap : ∀ m ∈ U, ‖Aline (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v)
    (ha : Continuous Aline) {lambda N R H : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) :
    maynardFixedAmbientPhysicalDefectPacket U Aline lambda N R H 1 =
      maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellBaseAmplitudeSet U Aline c v)
          Aline lambda N R H 1 +
        ∑ q ∈ Finset.range Q,
          maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellAmplitudeBand U Aline c
              (((2 ^ q : ℕ) : ℝ) * v)) Aline lambda N R H 1 := by
  have hcover := maynardUnitCellBaseAmplitudeSet_union_bands_eq hv hcap
  calc
    maynardFixedAmbientPhysicalDefectPacket U Aline lambda N R H 1 =
        maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellBaseAmplitudeSet U Aline c v ∪
            maynardUnitCellAmplitudeBands U Aline c v Q)
          Aline lambda N R H 1 := by rw [hcover]
    _ = maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellBaseAmplitudeSet U Aline c v)
          Aline lambda N R H 1 +
        maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellAmplitudeBands U Aline c v Q)
          Aline lambda N R H 1 :=
      maynardFixedAmbientPhysicalDefectPacket_union
        (disjoint_maynardUnitCellBaseAmplitudeSet_bands hv Q)
        ha hlambda hN hR hH
    _ = _ := by
      rw [maynardFixedAmbientPhysicalDefectPacket_amplitudeBands_eq_sum
        hv ha hlambda hN hR hH Q]

/-- A large capped packet with small base layer forces one fixed dyadic-band packet to remain
large, paying only the number of amplitude bands. -/
theorem exists_large_maynardFixedAmbientPhysicalDefectPacket_amplitudeBand
    {U : Finset ℕ} {Aline : ℝ → ℂ} {c : ℕ → ℝ}
    {v D : ℝ} (hv : 0 < v) {Q : ℕ} (hQ : 0 < Q)
    (hcap : ∀ m ∈ U, ‖Aline (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v)
    (ha : Continuous Aline) {lambda N R H : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hlarge : D ≤
      ‖maynardFixedAmbientPhysicalDefectPacket U Aline lambda N R H 1‖)
    (hbase :
      ‖maynardFixedAmbientPhysicalDefectPacket
        (maynardUnitCellBaseAmplitudeSet U Aline c v)
        Aline lambda N R H 1‖ < D / 2) :
    ∃ q < Q,
      D / 2 ≤ (Q : ℝ) *
        ‖maynardFixedAmbientPhysicalDefectPacket
          (maynardUnitCellAmplitudeBand U Aline c
            (((2 ^ q : ℕ) : ℝ) * v)) Aline lambda N R H 1‖ := by
  let F : ℕ → ℂ := fun q =>
    maynardFixedAmbientPhysicalDefectPacket
      (maynardUnitCellAmplitudeBand U Aline c
        (((2 ^ q : ℕ) : ℝ) * v)) Aline lambda N R H 1
  have hdecomp :=
    maynardFixedAmbientPhysicalDefectPacket_eq_base_add_sum_amplitudeBands
      hv hcap ha hlambda hN hR hH
  have hsumLarge : D / 2 ≤ ‖∑ q ∈ Finset.range Q, F q‖ := by
    have htri := norm_add_le
      (maynardFixedAmbientPhysicalDefectPacket
        (maynardUnitCellBaseAmplitudeSet U Aline c v)
        Aline lambda N R H 1)
      (∑ q ∈ Finset.range Q, F q)
    rw [hdecomp] at hlarge
    nlinarith
  have hnonempty : (Finset.range Q).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr hQ⟩
  obtain ⟨q, hq, hqLarge⟩ :=
    exists_mem_card_mul_norm_ge (Finset.range Q) hnonempty F hsumLarge
  refine ⟨q, Finset.mem_range.mp hq, ?_⟩
  simpa only [Finset.card_range, Nat.cast_ofNat, F] using hqLarge

/-- Restricted-volume Chebyshev law on an arbitrary ordered compact interval. -/
theorem maynard_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    (f : ℝ → ℂ) (hf : Continuous f) {a b A B : ℝ}
    (hab : a ≤ b) (hA : 0 < A)
    (hmean : (∫ t in a..b, ‖f t‖ ^ 2) ≤ B) :
    (volume.restrict (Set.Icc a b)).real {t | A ≤ ‖f t‖} ≤ B / A ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 2) μ := by
    exact (hf.norm.pow 2).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[μ] fun t : ℝ => ‖f t‖ ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg ‖f t‖
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    hnonneg hint (A ^ 2)
  have hset : {t : ℝ | A ^ 2 ≤ ‖f t‖ ^ 2} = {t : ℝ | A ≤ ‖f t‖} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hsq
      nlinarith [norm_nonneg (f t)]
    · intro h
      exact pow_le_pow_left₀ hA.le h 2
  rw [hset] at hmark
  have hintegral : (∫ t, ‖f t‖ ^ 2 ∂μ) ≤ B := by
    change (∫ t in Set.Icc a b, ‖f t‖ ^ 2) ≤ B
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    exact hmean
  apply (le_div_iff₀ (sq_pos_of_pos hA)).2
  simpa [μ, mul_comm] using hmark.trans hintegral

/-- Amplitude-sensitive spatial `L²` bound for one fixed observation cone.  This is Maynard's
critical `V² * |S|` estimate: only selected cells need the amplitude bound. -/
theorem integral_norm_sq_maynardDyadicBlockObservedPhysicalDefectPacket_le_card_of_selected_bound
    (L X k : ℕ) (T0 t : ℝ) {x N R H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hV0 : 0 ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ V) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S
          (fun y : ℝ =>
            heathBrownObservedEligibleDyadicAggregate L X k T0 t
              (x * N) (maynardDyadicBlockObservationRadius x N R)
              ((1 : ℂ) + (y : ℝ) * I))
          lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  have ha : Continuous a := by
    exact continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  have hbnd : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m u‖ ≤ 2 * V := by
    intro m hm u hu
    have haggregate : ‖a ((m : ℝ) + u)‖ ≤ V := hV m hm u hu
    have hKR0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hR
      (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
    have hKH0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hH
      (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKR0
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKH0
    have hkernel :
        ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 2 := by
      calc
        _ ≤ ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ +
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hKR hKH
        _ = 2 := by norm_num
    rw [maynardFixedAmbientDefectCellCoefficient, norm_mul]
    calc
      ‖a ((m : ℝ) + u)‖ *
          ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
          V * 2 := mul_le_mul haggregate hkernel (norm_nonneg _) hV0
      _ = 2 * V := by ring
  have hL2 := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card
    (x := x) (sigma := (1 : ℝ)) (A := 2 * V) (cellCount := cellCount)
    hx (by norm_num) (mul_nonneg (by norm_num) hV0)
    hN hR hH S hS a ha hbnd
  simpa only [a, sub_self, mul_zero, zero_add, Real.rpow_one] using hL2

/-- Amplitude-sensitive equation-(111) bad-base measure bound.  This is the exact form whose
`V²` factor cancels against Maynard's second selected-cell count. -/
theorem volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_card_of_selected_bound
    (L X k : ℕ) (T0 t : ℝ) {x N R H V A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (hA : 0 < A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ V) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  let b : ℕ → ℝ → ℂ :=
    maynardFixedAmbientDefectCellCoefficient a N R H 1
  let Q : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b 0
  let E : ℝ → ℂ := fun lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  have ha : Continuous a := by
    exact continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  have hb : ∀ m ∈ S, Continuous (b m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient
      ha hN hR hH (by norm_num) m
  have hQ : Continuous Q := by
    exact continuous_maynardUnitCellMellinPacketPosExtension S b 0 hb
  have hQE : ∀ lambda ∈ Set.Icc x (2 * x), Q lambda = E lambda := by
    intro lambda hlambda
    have hlambdaOne : 1 ≤ lambda := hx.trans hlambda.1
    have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaOne
    dsimp only [Q, E, b]
    rw [maynardUnitCellMellinPacketPosExtension_eq hlambdaOne]
    simpa using (maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
      S a lambda N R H 1 hlambdaPos hR hH).symm
  have hmeanE :=
    integral_norm_sq_maynardDyadicBlockObservedPhysicalDefectPacket_le_card_of_selected_bound
      L X k T0 t hx hN hR hH hV0 S hS hV
  have hmeanQ :
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) ≤
        4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) =
          ∫ lambda : ℝ in x..(2 * x), ‖E lambda‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro lambda hlambda
        rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
        change ‖Q lambda‖ ^ 2 = ‖E lambda‖ ^ 2
        rw [hQE lambda hlambda]
      _ ≤ _ := by simpa only [E, a] using hmeanE
  have hcheb := maynard_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    Q hQ (by linarith : x ≤ 2 * x) hA hmeanQ
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hae : {lambda | A ≤ ‖E lambda‖} =ᵐ[μ]
      {lambda | A ≤ ‖Q lambda‖} := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    apply propext
    change (A ≤ ‖E lambda‖) ↔ (A ≤ ‖Q lambda‖)
    rw [← hQE lambda hlambda]
  have hmeasure : μ.real {lambda | A ≤ ‖E lambda‖} =
      μ.real {lambda | A ≤ ‖Q lambda‖} := by
    rw [measureReal_def, measureReal_def, measure_congr hae]
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} =
        μ.real {lambda | A ≤ ‖E lambda‖} := by rfl
    _ = μ.real {lambda | A ≤ ‖Q lambda‖} := hmeasure
    _ ≤ _ := by simpa only [μ] using hcheb

/-- Equation-(111) for an exact dyadic band of common unit-cell maxima.  Band membership supplies
the lower amplitude consumed by selected-cell counts, while maximality supplies the whole-cell
upper amplitude needed by spatial `L²`. -/
theorem volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_amplitudeBand
    (L X k : ℕ) (T0 t : ℝ) {x N R H V A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV : 0 < V) (hA : 0 < A)
    (U : Finset ℕ) (hU : U ⊆ Finset.range cellCount) (c : ℕ → ℝ)
    (hmax : ∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (c m : ℝ) * I)‖) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellAmplitudeBand U
              (fun y : ℝ =>
                heathBrownObservedEligibleDyadicAggregate L X k T0 t
                  (x * N) (maynardDyadicBlockObservationRadius x N R)
                  ((1 : ℂ) + (y : ℝ) * I)) c V)
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (4 * V) ^ 2 *
        ((maynardUnitCellAmplitudeBand U
          (fun y : ℝ =>
            heathBrownObservedEligibleDyadicAggregate L X k T0 t
              (x * N) (maynardDyadicBlockObservationRadius x N R)
              ((1 : ℂ) + (y : ℝ) * I)) c V).card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  let S : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
  have hS : S ⊆ Finset.range cellCount :=
    (maynardUnitCellAmplitudeBand_subset U a c V).trans hU
  have hcell : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ 2 * V := by
    intro m hm u hu
    have hmU : m ∈ U := maynardUnitCellAmplitudeBand_subset U a c V hm
    exact (hmax m hmU u hu).trans
      (maynardUnitCellAmplitudeBand_upper (U := U) (A := a) (c := c) hm)
  have hmeasure :=
    volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_card_of_selected_bound
      L X k T0 t hx hN hR hH (show 0 ≤ 2 * V by positivity) hA S hS hcell
  simpa only [S, a, show 2 * (2 * V) = 4 * V by ring] using hmeasure

/-- Finite-union equation-(111): outside the base layer, every large full packet lies in one of
the fixed dyadic-band exceptional sets, and their measures sum with amplitude-sensitive cost. -/
theorem volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_and_base_small_le_sum_bands
    (L X k : ℕ) (T0 t : ℝ) {x N R H v D : ℝ}
    {cellCount Q : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hv : 0 < v) (hD : 0 < D) (hQ : 0 < Q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range cellCount) (c : ℕ → ℝ)
    (hmax : ∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (c m : ℝ) * I)‖)
    (hcap : ∀ m ∈ U,
      ‖heathBrownObservedEligibleDyadicAggregate L X k T0 t
        (x * N) (maynardDyadicBlockObservationRadius x N R)
        ((1 : ℂ) + (c m : ℝ) * I)‖ < ((2 ^ Q : ℕ) : ℝ) * v) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda |
          D ≤ ‖maynardFixedAmbientPhysicalDefectPacket U
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖ ∧
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet U
              (fun y : ℝ =>
                heathBrownObservedEligibleDyadicAggregate L X k T0 t
                  (x * N) (maynardDyadicBlockObservationRadius x N R)
                  ((1 : ℂ) + (y : ℝ) * I)) c v)
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖ < D / 2} ≤
      ∑ q ∈ Finset.range Q,
        (4 * (2 * x) *
          (4 * (((2 ^ q : ℕ) : ℝ) * v)) ^ 2 *
          ((maynardUnitCellAmplitudeBand U
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I)) c
              (((2 ^ q : ℕ) : ℝ) * v)).card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount))) /
            (D / (2 * (Q : ℝ))) ^ 2 := by
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  let base : Finset ℕ := maynardUnitCellBaseAmplitudeSet U a c v
  let band : ℕ → Finset ℕ := fun q =>
    maynardUnitCellAmplitudeBand U a c (((2 ^ q : ℕ) : ℝ) * v)
  let E : Finset ℕ → ℝ → ℂ := fun S lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  let bad : Set ℝ := {lambda | D ≤ ‖E U lambda‖ ∧ ‖E base lambda‖ < D / 2}
  let badBand : ℕ → Set ℝ := fun q =>
    {lambda | D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖}
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have ha : Continuous a := by
    exact continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hthreshold : 0 < D / (2 * (Q : ℝ)) := by positivity
  have hsub : ∀ᵐ lambda ∂μ,
      lambda ∈ bad → lambda ∈ ⋃ q ∈ Finset.range Q, badBand q := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    intro hlambdaBad
    have hlambdaPos : 0 < lambda :=
      lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)
    obtain ⟨q, hqQ, hqLarge⟩ :=
      exists_large_maynardFixedAmbientPhysicalDefectPacket_amplitudeBand
        (U := U) (Aline := a) (c := c) hv hQ (by simpa only [a] using hcap)
          ha hlambdaPos hN hR hH hlambdaBad.1 hlambdaBad.2
    have hqLarge' : D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖ := by
      rw [show D / (2 * (Q : ℝ)) = (D / 2) / (Q : ℝ) by field_simp]
      apply (div_le_iff₀ hQreal).2
      simpa only [E, band, a, mul_comm] using hqLarge
    apply Set.mem_iUnion_of_mem q
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr hqQ)
    exact hqLarge'
  have hmeasure : μ.real bad ≤ μ.real (⋃ q ∈ Finset.range Q, badBand q) := by
    have hmono : μ bad ≤ μ (⋃ q ∈ Finset.range Q, badBand q) :=
      measure_mono_ae hsub
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
  have hunion : μ.real (⋃ q ∈ Finset.range Q, badBand q) ≤
      ∑ q ∈ Finset.range Q, μ.real (badBand q) :=
    measureReal_biUnion_finset_le _ _
  have hbandMeasure : ∀ q ∈ Finset.range Q,
      μ.real (badBand q) ≤
        (4 * (2 * x) * (4 * (((2 ^ q : ℕ) : ℝ) * v)) ^ 2 *
          ((band q).card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount))) /
            (D / (2 * (Q : ℝ))) ^ 2 := by
    intro q hq
    have hVq : 0 < ((2 ^ q : ℕ) : ℝ) * v := by positivity
    have hqMeasure :=
      volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_amplitudeBand
        L X k T0 t hx hN hR hH hVq hthreshold U hU c hmax
    simpa only [μ, badBand, E, band, a] using hqMeasure
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda |
          D ≤ ‖maynardFixedAmbientPhysicalDefectPacket U
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖ ∧
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet U
              (fun y : ℝ =>
                heathBrownObservedEligibleDyadicAggregate L X k T0 t
                  (x * N) (maynardDyadicBlockObservationRadius x N R)
                  ((1 : ℂ) + (y : ℝ) * I)) c v)
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖ < D / 2} = μ.real bad := by rfl
    _ ≤ μ.real (⋃ q ∈ Finset.range Q, badBand q) := hmeasure
    _ ≤ ∑ q ∈ Finset.range Q, μ.real (badBand q) := hunion
    _ ≤ _ := Finset.sum_le_sum hbandMeasure

/-- Maynard's spatial `L²` bound instantiated with one fixed observation-cone aggregate throughout
the dyadic physical block.  Both cell set and Dirichlet polynomial are independent of the physical
dilation parameter. -/
theorem integral_norm_sq_maynardDyadicBlockObservedPhysicalDefectPacket_le_card
    (L X k : ℕ) (T0 t : ℝ) {x N R H : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hX : 1 ≤ X) (hN : 0 < N)
    (hR : 0 < R) (hH : 0 < H)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S
          (fun y : ℝ =>
            heathBrownObservedEligibleDyadicAggregate L X k T0 t
              (x * N) (maynardDyadicBlockObservationRadius x N R)
              ((1 : ℂ) + (y : ℝ) * I))
          lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) *
        (2 * heathBrownWindowRelevantFixedPolylogBound L X k (x * N) 1) ^ 2 *
        (S.card : ℝ) * (1 + 2 * (1 + Real.log cellCount)) := by
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k (x * N) 1
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxN : 0 < x * N := mul_pos hxpos hN
  have hPnonneg : 0 ≤ P := by
    have hbound := norm_heathBrownObservedEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t (x * N) (maynardDyadicBlockObservationRadius x N R)
        1 0 hxN (by norm_num)
    exact (norm_nonneg _).trans hbound
  have ha : Continuous a := by
    exact continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  have hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m v‖ ≤ 2 * P := by
    intro m hm v hv
    have haggregate : ‖a ((m : ℝ) + v)‖ ≤ P := by
      exact norm_heathBrownObservedEligibleDyadicAggregate_le_fixedPolylog
        L X k hX T0 t (x * N) (maynardDyadicBlockObservationRadius x N R)
          1 ((m : ℝ) + v) hxN (by norm_num)
    have hKR0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hR
      (s := (1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I)) (by simp)
    have hKH0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hH
      (s := (1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I)) (by simp)
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKR0
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKH0
    have hkernel :
        ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I)) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ ≤ 2 := by
      calc
        _ ≤ ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ +
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hKR hKH
        _ = 2 := by norm_num
    rw [maynardFixedAmbientDefectCellCoefficient, norm_mul]
    calc
      ‖a ((m : ℝ) + v)‖ *
          ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I)) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + v : ℝ) : ℂ) * I))‖ ≤
          P * 2 := mul_le_mul haggregate hkernel (norm_nonneg _) hPnonneg
      _ = 2 * P := by ring
  have hL2 := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card
    (x := x) (sigma := (1 : ℝ)) (A := 2 * P) (cellCount := cellCount)
    hx (by norm_num) (mul_nonneg (by norm_num) hPnonneg)
    hN hR hH S hS a ha hbnd
  simpa only [P, a, sub_self, mul_zero, zero_add, Real.rpow_one] using hL2

/-- Equation-(111) bad-base measure bound for one fixed observation cone and one fixed selected
unit-cell family.  No recut, coefficient, or cell set depends on the physical base. -/
theorem volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_card
    (L X k : ℕ) (T0 t : ℝ) {x N R H A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hX : 1 ≤ X) (hN : 0 < N)
    (hR : 0 < R) (hH : 0 < H) (hA : 0 < A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) *
        (2 * heathBrownWindowRelevantFixedPolylogBound L X k (x * N) 1) ^ 2 *
        (S.card : ℝ) * (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownObservedEligibleDyadicAggregate L X k T0 t
      (x * N) (maynardDyadicBlockObservationRadius x N R)
      ((1 : ℂ) + (y : ℝ) * I)
  let b : ℕ → ℝ → ℂ :=
    maynardFixedAmbientDefectCellCoefficient a N R H 1
  let Q : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b 0
  let E : ℝ → ℂ := fun lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxN : 0 < x * N := mul_pos hxpos hN
  have ha : Continuous a := by
    exact continuous_heathBrownObservedEligibleDyadicAggregate_line
      L X k T0 t (x * N) (maynardDyadicBlockObservationRadius x N R) 1
  have hb : ∀ m ∈ S, Continuous (b m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient
      ha hN hR hH (by norm_num) m
  have hQ : Continuous Q := by
    exact continuous_maynardUnitCellMellinPacketPosExtension S b 0 hb
  have hQE : ∀ lambda ∈ Set.Icc x (2 * x), Q lambda = E lambda := by
    intro lambda hlambda
    have hlambdaOne : 1 ≤ lambda := hx.trans hlambda.1
    have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaOne
    dsimp only [Q, E, b]
    rw [maynardUnitCellMellinPacketPosExtension_eq hlambdaOne]
    simpa using (maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
      S a lambda N R H 1 hlambdaPos hR hH).symm
  have hmeanE :=
    integral_norm_sq_maynardDyadicBlockObservedPhysicalDefectPacket_le_card
      L X k T0 t hx hX hN hR hH S hS
  have hmeanQ :
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) ≤
        4 * (2 * x) *
          (2 * heathBrownWindowRelevantFixedPolylogBound L X k (x * N) 1) ^ 2 *
          (S.card : ℝ) * (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) =
          ∫ lambda : ℝ in x..(2 * x), ‖E lambda‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro lambda hlambda
        rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
        change ‖Q lambda‖ ^ 2 = ‖E lambda‖ ^ 2
        rw [hQE lambda hlambda]
      _ ≤ _ := by simpa only [E, a] using hmeanE
  have hcheb := maynard_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    Q hQ (by linarith : x ≤ 2 * x) hA hmeanQ
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hae : {lambda | A ≤ ‖E lambda‖} =ᵐ[μ]
      {lambda | A ≤ ‖Q lambda‖} := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    apply propext
    change (A ≤ ‖E lambda‖) ↔ (A ≤ ‖Q lambda‖)
    rw [← hQE lambda hlambda]
  have hmeasure : μ.real {lambda | A ≤ ‖E lambda‖} =
      μ.real {lambda | A ≤ ‖Q lambda‖} := by
    rw [measureReal_def, measureReal_def, measure_congr hae]
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownObservedEligibleDyadicAggregate L X k T0 t
                (x * N) (maynardDyadicBlockObservationRadius x N R)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} =
        μ.real {lambda | A ≤ ‖E lambda‖} := by rfl
    _ = μ.real {lambda | A ≤ ‖Q lambda‖} := hmeasure
    _ ≤ _ := by simpa only [μ] using hcheb

/-- Amplitude-sensitive spatial `L²` estimate for any source line fixed before physical dilation.
This is the invariant content of Maynard's equation-(111) geometry. -/
theorem integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card_of_source_bound
    {x N R H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hV0 : 0 ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖a ((m : ℝ) + u)‖ ≤ V) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  have hbnd : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m u‖ ≤ 2 * V := by
    intro m hm u hu
    have haggregate : ‖a ((m : ℝ) + u)‖ ≤ V := hV m hm u hu
    have hKR0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hR
      (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
    have hKH0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hH
      (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKR0
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
      simpa using hKH0
    have hkernel :
        ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 2 := by
      calc
        _ ≤ ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ +
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hKR hKH
        _ = 2 := by norm_num
    rw [maynardFixedAmbientDefectCellCoefficient, norm_mul]
    calc
      ‖a ((m : ℝ) + u)‖ *
          ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
          V * 2 := mul_le_mul haggregate hkernel (norm_nonneg _) hV0
      _ = 2 * V := by ring
  have hL2 := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card
    (x := x) (sigma := (1 : ℝ)) (A := 2 * V) (cellCount := cellCount)
    hx (by norm_num) (mul_nonneg (by norm_num) hV0)
    hN hR hH S hS a ha hbnd
  simpa only [sub_self, mul_zero, zero_add, Real.rpow_one] using hL2

/-- Generic equation-(111): a fixed continuous source line with amplitude at most `V` on selected
unit cells has bad-base measure at most its spatial `L²` energy divided by `A²`. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_card_of_source_bound
    {x N R H V A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (hA : 0 < A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖a ((m : ℝ) + u)‖ ≤ V) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} ≤
      (4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let b : ℕ → ℝ → ℂ :=
    maynardFixedAmbientDefectCellCoefficient a N R H 1
  let Q : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b 0
  let E : ℝ → ℂ := fun lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  have hb : ∀ m ∈ S, Continuous (b m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient
      ha hN hR hH (by norm_num) m
  have hQ : Continuous Q := by
    exact continuous_maynardUnitCellMellinPacketPosExtension S b 0 hb
  have hQE : ∀ lambda ∈ Set.Icc x (2 * x), Q lambda = E lambda := by
    intro lambda hlambda
    have hlambdaOne : 1 ≤ lambda := hx.trans hlambda.1
    have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaOne
    dsimp only [Q, E, b]
    rw [maynardUnitCellMellinPacketPosExtension_eq hlambdaOne]
    simpa using (maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
      S a lambda N R H 1 hlambdaPos hR hH).symm
  have hmeanE :=
    integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card_of_source_bound
      hx hN hR hH hV0 S hS a ha hV
  have hmeanQ :
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) ≤
        4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) =
          ∫ lambda : ℝ in x..(2 * x), ‖E lambda‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro lambda hlambda
        rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
        change ‖Q lambda‖ ^ 2 = ‖E lambda‖ ^ 2
        rw [hQE lambda hlambda]
      _ ≤ _ := hmeanE
  have hcheb := maynard_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    Q hQ (by linarith : x ≤ 2 * x) hA hmeanQ
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hae : {lambda | A ≤ ‖E lambda‖} =ᵐ[μ]
      {lambda | A ≤ ‖Q lambda‖} := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    apply propext
    change (A ≤ ‖E lambda‖) ↔ (A ≤ ‖Q lambda‖)
    rw [← hQE lambda hlambda]
  have hmeasure : μ.real {lambda | A ≤ ‖E lambda‖} =
      μ.real {lambda | A ≤ ‖Q lambda‖} := by
    rw [measureReal_def, measureReal_def, measure_congr hae]
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} =
        μ.real {lambda | A ≤ ‖E lambda‖} := by rfl
    _ = μ.real {lambda | A ≤ ‖Q lambda‖} := hmeasure
    _ ≤ _ := by simpa only [μ] using hcheb

/-- One family of unit-cell maximizers controls the fixed left-base window-relevant aggregate
before the physical base varies. -/
theorem exists_heathBrownLeftWindowRelevantEligibleDyadicAggregate_unitCell_maximizers
    (L X k : ℕ) (T0 t x N : ℝ) :
    ∃ c : ℕ → ℝ,
      ∀ m : ℕ,
        c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
              ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
              ((1 : ℂ) + (c m : ℝ) * I)‖ := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
      ((1 : ℂ) + (y : ℝ) * I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t (x * N) 1
  have hcell : ∀ m : ℕ, ∃ y ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
      IsMaxOn (fun z => ‖a z‖) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) y := by
    intro m
    refine isCompact_Icc.exists_isMaxOn ?_ ha.norm.continuousOn
    exact Set.nonempty_Icc.mpr (by linarith)
  choose c hcmem hcmax using hcell
  refine ⟨c, ?_⟩
  intro m
  refine ⟨hcmem m, ?_⟩
  intro u hu
  have hmu : (m : ℝ) + u ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
    constructor <;> linarith [hu.1, hu.2]
  exact hcmax m hmu

/-- Amplitude-sensitive spatial `L²` bound for the fixed left-base window-relevant packet. -/
theorem integral_norm_sq_maynardDyadicBlockLeftWindowRelevantPhysicalDefectPacket_le_card_of_selected_bound
    (L X k : ℕ) (T0 t : ℝ) {x N R H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hV0 : 0 ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ V) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
              ((1 : ℂ) + (y : ℝ) * I))
          lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
      ((1 : ℂ) + (y : ℝ) * I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t (x * N) 1
  simpa only [a] using
    (integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card_of_source_bound
      hx hN hR hH hV0 S hS a ha (by simpa only [a] using hV))

/-- Equation-(111) bad-base bound for the fixed left-base window-relevant packet. -/
theorem volume_maynardDyadicBlockLeftWindowRelevantPhysicalDefectPacket_large_le_card_of_selected_bound
    (L X k : ℕ) (T0 t : ℝ) {x N R H V A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV0 : 0 ≤ V) (hA : 0 < A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤ V) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S
            (fun y : ℝ =>
              heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (2 * V) ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
      ((1 : ℂ) + (y : ℝ) * I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t (x * N) 1
  simpa only [a] using
    (volume_maynardFixedAmbientPhysicalDefectPacket_large_le_card_of_source_bound
      hx hN hR hH hV0 hA S hS a ha (by simpa only [a] using hV))

/-- Equation-(111) for one exact amplitude band of the fixed left-base packet.  These are the
literal selected cells consumed by the existing Route-T count capstone. -/
theorem volume_maynardDyadicBlockLeftWindowRelevantPhysicalDefectPacket_large_le_amplitudeBand
    (L X k : ℕ) (T0 t : ℝ) {x N R H V A : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV : 0 < V) (hA : 0 < A)
    (U : Finset ℕ) (hU : U ⊆ Finset.range cellCount) (c : ℕ → ℝ)
    (hmax : ∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
        ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I)‖ ≤
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
        ((1 : ℂ) + (c m : ℝ) * I)‖) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | A ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellAmplitudeBand U
              (fun y : ℝ =>
                heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
                  ((1 : ℂ) + (y : ℝ) * I)) c V)
            (fun y : ℝ =>
              heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
                ((1 : ℂ) + (y : ℝ) * I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (4 * V) ^ 2 *
        ((maynardUnitCellAmplitudeBand U
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
              ((1 : ℂ) + (y : ℝ) * I)) c V).card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount))) / A ^ 2 := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (x * N)
      ((1 : ℂ) + (y : ℝ) * I)
  let S : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
  have hS : S ⊆ Finset.range cellCount :=
    (maynardUnitCellAmplitudeBand_subset U a c V).trans hU
  have hcell : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
    intro m hm u hu
    have hmU : m ∈ U := maynardUnitCellAmplitudeBand_subset U a c V hm
    exact (hmax m hmU u hu).trans
      (maynardUnitCellAmplitudeBand_upper (U := U) (A := a) (c := c) hm)
  have hmeasure :=
    volume_maynardDyadicBlockLeftWindowRelevantPhysicalDefectPacket_large_le_card_of_selected_bound
      L X k T0 t hx hN hR hH (show 0 ≤ 2 * V by positivity) hA S hS
        (by simpa only [a] using hcell)
  simpa only [S, a, show 2 * (2 * V) = 4 * V by ring] using hmeasure

/-- Generic finite-union equation-(111).  Outside the base amplitude layer, every large fixed
source packet forces one dyadic amplitude-band packet to be large, and the exceptional measures
sum with the amplitude-sensitive `V² * card` cost. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_and_base_small_le_sum_bands
    {x N R H v D : ℝ} {cellCount Q : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hv : 0 < v) (hD : 0 < D) (hQ : 0 < Q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a) (c : ℕ → ℝ)
    (hmax : ∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ ‖a (c m)‖)
    (hcap : ∀ m ∈ U, ‖a (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda |
          D ≤ ‖maynardFixedAmbientPhysicalDefectPacket U a lambda N R H 1‖ ∧
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet U a c v)
            a lambda N R H 1‖ < D / 2} ≤
      ∑ q ∈ Finset.range Q,
        (4 * (2 * x) *
          (4 * (((2 ^ q : ℕ) : ℝ) * v)) ^ 2 *
          ((maynardUnitCellAmplitudeBand U a c
              (((2 ^ q : ℕ) : ℝ) * v)).card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount))) /
            (D / (2 * (Q : ℝ))) ^ 2 := by
  let base : Finset ℕ := maynardUnitCellBaseAmplitudeSet U a c v
  let band : ℕ → Finset ℕ := fun q =>
    maynardUnitCellAmplitudeBand U a c (((2 ^ q : ℕ) : ℝ) * v)
  let E : Finset ℕ → ℝ → ℂ := fun S lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  let bad : Set ℝ := {lambda | D ≤ ‖E U lambda‖ ∧ ‖E base lambda‖ < D / 2}
  let badBand : ℕ → Set ℝ := fun q =>
    {lambda | D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖}
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hthreshold : 0 < D / (2 * (Q : ℝ)) := by positivity
  have hsub : ∀ᵐ lambda ∂μ,
      lambda ∈ bad → lambda ∈ ⋃ q ∈ Finset.range Q, badBand q := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    intro hlambdaBad
    have hlambdaPos : 0 < lambda :=
      lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)
    obtain ⟨q, hqQ, hqLarge⟩ :=
      exists_large_maynardFixedAmbientPhysicalDefectPacket_amplitudeBand
        (U := U) (Aline := a) (c := c) hv hQ hcap
          ha hlambdaPos hN hR hH hlambdaBad.1 hlambdaBad.2
    have hqLarge' : D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖ := by
      rw [show D / (2 * (Q : ℝ)) = (D / 2) / (Q : ℝ) by field_simp]
      apply (div_le_iff₀ hQreal).2
      simpa only [E, band, mul_comm] using hqLarge
    apply Set.mem_iUnion_of_mem q
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr hqQ)
    exact hqLarge'
  have hmeasure : μ.real bad ≤ μ.real (⋃ q ∈ Finset.range Q, badBand q) := by
    have hmono : μ bad ≤ μ (⋃ q ∈ Finset.range Q, badBand q) :=
      measure_mono_ae hsub
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
  have hunion : μ.real (⋃ q ∈ Finset.range Q, badBand q) ≤
      ∑ q ∈ Finset.range Q, μ.real (badBand q) :=
    measureReal_biUnion_finset_le _ _
  have hbandMeasure : ∀ q ∈ Finset.range Q,
      μ.real (badBand q) ≤
        (4 * (2 * x) * (4 * (((2 ^ q : ℕ) : ℝ) * v)) ^ 2 *
          ((band q).card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount))) /
            (D / (2 * (Q : ℝ))) ^ 2 := by
    intro q hq
    let Vq : ℝ := ((2 ^ q : ℕ) : ℝ) * v
    have hVq : 0 < Vq := by dsimp only [Vq]; positivity
    have hbandU : band q ⊆ U :=
      maynardUnitCellAmplitudeBand_subset U a c Vq
    have hbandRange : band q ⊆ Finset.range cellCount := hbandU.trans hU
    have hcell : ∀ m ∈ band q, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * Vq := by
      intro m hm u hu
      exact (hmax m (hbandU hm) u hu).trans
        (maynardUnitCellAmplitudeBand_upper (U := U) (A := a) (c := c) hm)
    have hqMeasure :=
      volume_maynardFixedAmbientPhysicalDefectPacket_large_le_card_of_source_bound
        hx hN hR hH (show 0 ≤ 2 * Vq by positivity) hthreshold
          (band q) hbandRange a ha hcell
    simpa only [μ, badBand, E, band, Vq,
      show 2 * (2 * (((2 ^ q : ℕ) : ℝ) * v)) =
        4 * (((2 ^ q : ℕ) : ℝ) * v) by ring] using hqMeasure
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda |
          D ≤ ‖maynardFixedAmbientPhysicalDefectPacket U a lambda N R H 1‖ ∧
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet U a c v)
            a lambda N R H 1‖ < D / 2} = μ.real bad := by rfl
    _ ≤ μ.real (⋃ q ∈ Finset.range Q, badBand q) := hmeasure
    _ ≤ ∑ q ∈ Finset.range Q, μ.real (badBand q) := hunion
    _ ≤ _ := Finset.sum_le_sum hbandMeasure

end RHTower.Sieve
