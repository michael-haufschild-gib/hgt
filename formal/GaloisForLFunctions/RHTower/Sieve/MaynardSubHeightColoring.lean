import GaloisForLFunctions.RHTower.Sieve.MaynardSubHeightMass
import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantAggregate

/-!
# Generalized selected-polynomial coloring with over-height atoms

High-amplitude boxes need not be all-short.  The new selector first removes over-height atoms,
whose individual values are below their own amplitude threshold, and then groups the remaining
sub-height mass.  The selected literal group has exact mass in `[t,1+2t)` and retains the exact
large-value threshold.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Pointwise literal group selection from positive sub-height mass and over-height excision. -/
theorem exists_heathBrown_box_subHeight_group_of_mass
    (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {T t e : ℝ} (hT : 1 < T) (ht : 0 < t) (s : ℂ)
    (hmass : t ≤ ∑ i ∈ (Finset.univ.filter
        fun i : PositiveHeathBrownBoxFactorIndex box =>
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i))
    (hsmall : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      ‖heathBrownBoxFactorValue L X k box s i‖ ≤
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^ e)
    (hlarge :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k box.m), u.Nonempty ∧
      (∀ i ∈ u,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) ∧
      let beta := ∑ i ∈ u,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)
      t ≤ beta ∧ beta < 1 + 2 * t ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} =>
            heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) = T ^ beta ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} =>
            heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m i))
              (heathBrownBoxFactorExponent box.a box.b box.q i))) s‖ ∧
        (∃ j ∈ u, beta - 2 * t < dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ∧
        (beta < 1 ∨ ∃ j ∈ u, 1 - 2 * t <
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q j)) := by
  classical
  let q : HeathBrownBoxFactorIndex k box.m → ℕ :=
    heathBrownBoxFactorExponent box.a box.b box.q
  let w : HeathBrownBoxFactorIndex k box.m → ℝ := fun i =>
    dyadicLogExponent T (q i)
  let pos : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i => 1 ≤ q i
  have hpos (i : HeathBrownBoxFactorIndex k box.m) : i ∈ pos ↔ 1 ≤ q i := by
    simp [pos]
  let f : HeathBrownBoxFactorIndex k box.m → ℝ := fun i =>
    if w i < 1 then w i else 0
  have hsubtype := Finset.sum_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m => 1 ≤ q i)
    pos hpos f
  have hposEq :
      ∑ i ∈ (Finset.univ.filter
          fun i : PositiveHeathBrownBoxFactorIndex box => w i < 1), w i =
        ∑ i ∈ pos, f i := by
    calc
      ∑ i ∈ (Finset.univ.filter
          fun i : PositiveHeathBrownBoxFactorIndex box => w i < 1), w i =
          ∑ i : PositiveHeathBrownBoxFactorIndex box, f i := by
        rw [← Finset.sum_filter]
      _ = ∑ i ∈ pos, f i := by
        simpa [PositiveHeathBrownBoxFactorIndex, q] using hsubtype.symm
  have hf0 : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    split_ifs
    · exact dyadicLogExponent_nonneg hT (q i)
    · exact le_rfl
  have hposLe : ∑ i ∈ pos, f i ≤ ∑ i, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ pos)
      (fun i _hi _ => hf0 i)
  have hsubTotal : t ≤ ∑ i ∈ (Finset.univ.filter fun i => w i < 1), w i := by
    calc
      t ≤ ∑ i ∈ (Finset.univ.filter
          fun i : PositiveHeathBrownBoxFactorIndex box => w i < 1), w i := by
        simpa [w, q] using hmass
      _ = ∑ i ∈ pos, f i := hposEq
      _ ≤ ∑ i, f i := hposLe
      _ = ∑ i ∈ (Finset.univ.filter fun i => w i < 1), w i := by
        rw [← Finset.sum_filter]
  have hover : ∀ i : HeathBrownBoxFactorIndex k box.m,
      1 ≤ w i →
      ‖heathBrownBoxFactorValue L X k box s i‖ ≤
        (((2 ^ q i : ℕ) : ℝ)) ^ e := by
    intro i hi
    have hqi : 1 ≤ q i := by
      by_contra hnot
      have hq0 : q i = 0 := by omega
      have hw0 : w i = 0 := by simp [w, hq0, dyadicLogExponent, Real.logb]
      linarith
    exact hsmall ⟨i, by simpa [q] using hqi⟩ (by simpa [w, q] using hi)
  apply exists_heathBrown_box_subHeight_large_group_with_cap_witness
    L X k box.m box.a box.b box.q hT ht
      (by simpa [w, q] using hsubTotal) s
      (by simpa [w, q, heathBrownBoxFactorValue] using hover) hlarge

/-- Aggregate selector with no all-short hypothesis.  Every high-amplitude window-relevant
aggregate selects one literal sub-height group. -/
theorem eventually_exists_windowRelevant_subHeight_group :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ c y alpha V N0 : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          3 / 4 ≤ alpha → 0 < V →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant N0 X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box ∧
            IsHeathBrownBoxWindowRelevant N0 X 60 box ∧
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤
              ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
            ∃ u : Finset (HeathBrownBoxFactorIndex 60 box.m), u.Nonempty ∧
              (∀ i ∈ u,
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) ∧
              let beta := ∑ i ∈ u,
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i)
              mu / 120 ≤ beta ∧ beta < 1 + 2 * (mu / 120) ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} =>
                    heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) =
                    T ^ beta ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} =>
                    heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) ^
                      (alpha - c) ≤
                  ‖∏ i : {i // i ∈ u}, LSeries
                    (complexCoeff (arithmeticDyadicBlock
                      (heathBrownFactorBase L X
                        (heathBrownBoxFactorKind 60 box.m i))
                      (heathBrownBoxFactorExponent box.a box.b box.q i)))
                        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
                (∃ j ∈ u, beta - 2 * (mu / 120) < dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ∧
                (beta < 1 ∨ ∃ j ∈ u,
                  (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
                    heathBrownBoxFactorKind 60 box.m j = .log) ∧
                  1 - 2 * (mu / 120) < dyadicLogExponent T
                    (heathBrownBoxFactorExponent box.a box.b box.q j)) := by
  filter_upwards [eventually_maynard_perronRelevant_box_subHeight_mass,
    eventually_maynard_perronRelevant_box_overHeight_small,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hmassT hsmallT hT
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyhi
    halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hterm⟩ :=
    exists_large_windowRelevant_eligible_heathBrownBox
      L X 60 (by norm_num) T (mu / 120) N0
        ((c : ℂ) + (y : ℝ) * Complex.I) hV haggregate
  have hterm' : V ≤ heathBrownEligibleBoxCost L X 60 *
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
    dsimp [heathBrownBoxTerm] at hterm
    rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core] at hterm
    have hchoose : (Nat.choose 60 box.m : ℝ) ≤ (2 ^ (60 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_two_pow 60 box.m
    calc
      V ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          ((Nat.choose 60 box.m : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := hterm
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          ((2 ^ (60 : ℕ) : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := by gcongr
      _ = heathBrownEligibleBoxCost L X 60 *
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
        dsimp only [heathBrownEligibleBoxCost]
        ring
  have hscaled := (hreserve box helig hrel).trans hterm'
  have hcost := heathBrownEligibleBoxCost_pos L X 60 (by norm_num)
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
          (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ :=
    (mul_le_mul_iff_right₀ hcost).mp hscaled
  have hmass := hmassT X hX mu hmuLo hmuHi hXscale L hL box helig
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  have hsmall := hsmallT X hX mu hmuHi hXscale L hL box
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  obtain ⟨u, hune, husub, hulower, huupper, hulength, hularge,
      hulocal, huwitness⟩ :=
    exists_heathBrown_box_subHeight_group_of_mass
      L X 60 box hL hX hT
        (by linarith : 0 < mu / 120)
        ((c : ℂ) + (y : ℝ) * Complex.I) hmass hsmall hcore
  have huwitness' :
      (∑ i ∈ u, dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)) < 1 ∨
        ∃ j ∈ u,
          (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
            heathBrownBoxFactorKind 60 box.m j = .log) ∧
          1 - 2 * (mu / 120) < dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q j) := by
    rcases huwitness with hregular | ⟨j, hju, hjweight⟩
    · exact Or.inl hregular
    · right
      refine ⟨j, hju, ?_, hjweight⟩
      cases hkind : heathBrownBoxFactorKind 60 box.m j with
      | moebius =>
          have hjupper := hmobius box j hkind
          exfalso
          linarith
      | zeta => exact Or.inl rfl
      | log => exact Or.inr rfl
  exact ⟨box, helig, hrel, hcore, u, hune, husub, hulower, huupper,
    hulength, hularge, hulocal, huwitness'⟩

end RHTower.Sieve
