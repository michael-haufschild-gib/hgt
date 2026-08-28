import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthAlignedOrdinateShell
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL4
import GaloisForLFunctions.HTGeometry.ThreeCircles

noncomputable section
namespace RHTower.Sieve

open Complex Filter Set MeasureTheory

/-- Natural-cell rounding of the stopped real dyadic ordinate ladder. -/
def routeTNaturalizedOrdinateLadder (U V : ℝ) (j : ℕ) : ℕ :=
  ⌈routeTComparableWidthLadder U V j⌉₊

theorem routeTNaturalizedOrdinateLadder_initial
    {U : ℝ} {V : ℕ} (hUV : U ≤ (V : ℝ)) :
    routeTNaturalizedOrdinateLadder U V 0 = V := by
  rw [routeTNaturalizedOrdinateLadder, routeTComparableWidthLadder]
  simp only [pow_zero, Nat.cast_one, div_one, max_eq_right hUV, Nat.ceil_natCast]

theorem routeTNaturalizedOrdinateLadder_terminal
    {U V : ℝ} {n : ℕ}
    (hterminal : ∀ i, n ≤ i → routeTComparableWidthLadder U V i = U)
    {j : ℕ} (hj : n ≤ j) :
    routeTNaturalizedOrdinateLadder U V j = ⌈U⌉₊ := by
  rw [routeTNaturalizedOrdinateLadder, hterminal j hj]

theorem routeTNaturalizedOrdinateLadder_fullShell
    {U V : ℝ} {n j : ℕ} (hU : 2 ≤ U)
    (hshell : ∀ i < n,
      U ≤ routeTComparableWidthLadder U V (i + 1) ∧
      routeTComparableWidthLadder U V i =
        2 * routeTComparableWidthLadder U V (i + 1))
    (hj : j < n) :
    routeTNaturalizedOrdinateLadder U V (j + 1) + 2 ≤
        routeTNaturalizedOrdinateLadder U V j ∧
      routeTNaturalizedOrdinateLadder U V j ≤
        2 * routeTNaturalizedOrdinateLadder U V (j + 1) := by
  let x : ℝ := routeTComparableWidthLadder U V (j + 1)
  have hx : 2 ≤ x := hU.trans (hshell j hj).1
  have hx0 : 0 ≤ x := zero_le_two.trans hx
  have hdouble : routeTComparableWidthLadder U V j = 2 * x := hshell j hj |>.2
  have hceilx : (x : ℝ) ≤ (⌈x⌉₊ : ℕ) := Nat.le_ceil x
  have hceilxlt : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hceilDoubleLower : (2 * x : ℝ) ≤ (⌈2 * x⌉₊ : ℕ) := Nat.le_ceil (2 * x)
  have hgapReal : (((⌈x⌉₊ : ℕ) : ℝ) + 1) < ((⌈2 * x⌉₊ : ℕ) : ℝ) := by
    calc
      (((⌈x⌉₊ : ℕ) : ℝ) + 1) < x + 2 := by linarith
      _ ≤ 2 * x := by linarith
      _ ≤ ((⌈2 * x⌉₊ : ℕ) : ℝ) := hceilDoubleLower
  have hgapNat : ⌈x⌉₊ + 2 ≤ ⌈2 * x⌉₊ := by
    exact_mod_cast hgapReal
  have hceilDoubleUpper : ⌈2 * x⌉₊ ≤ 2 * ⌈x⌉₊ := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  simpa only [routeTNaturalizedOrdinateLadder, hdouble, x] using
    And.intro hgapNat hceilDoubleUpper

/-- Consecutive natural cells tile an arbitrary integer-endpoint interval. -/
theorem intervalIntegral_sum_Ico_unitCells_eq
    {f : ℝ → ℂ} (hf : Continuous f) {A B : ℕ} (hAB : A ≤ B) :
    (∫ v : ℝ in (0 : ℝ)..1, ∑ m ∈ Finset.Ico A B, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (A : ℝ)..(B : ℝ), f y := by
  have heq : (fun v : ℝ => ∑ m ∈ Finset.Ico A B, f ((m : ℝ) + v)) =
      fun v : ℝ =>
        (∑ m ∈ Finset.range B, f ((m : ℝ) + v)) -
          ∑ m ∈ Finset.range A, f ((m : ℝ) + v) := by
    funext v
    exact Finset.sum_Ico_eq_sub (fun m => f ((m : ℝ) + v)) hAB
  rw [heq]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral_sum_range_unitCells_eq hf B,
      intervalIntegral_sum_range_unitCells_eq hf A]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) (A : ℝ))
      (hf.intervalIntegrable (A : ℝ) (B : ℝ))]
    ring
  · exact (continuous_finsetSum (Finset.range B) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  · exact (continuous_finsetSum (Finset.range A) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1

/-- Fixed-ambient packet on an arbitrary natural cell interval is exactly its adjacent
ordinate integral. -/
theorem maynardFixedAmbientPhysicalDefectPacket_Ico_eq_intervalIntegral
    (a : ℝ → ℂ) (ha : Continuous a)
    (lambda N R H sigma : ℝ) {A B : ℕ} (hAB : A ≤ B)
    (hN : 0 < lambda * N) (hR : 0 < lambda * R)
    (hH : 0 < lambda * H) (hsigma : 0 < sigma) :
    maynardFixedAmbientPhysicalDefectPacket (Finset.Ico A B) a
        lambda N R H sigma =
      ∫ y : ℝ in (A : ℝ)..(B : ℝ),
        a y *
          (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
              ((sigma : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
              ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
  let f : ℝ → ℂ := fun y =>
    a y *
      (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((sigma : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
  have hf : Continuous f := by
    exact ha.mul
      ((continuous_routeTNormalizedSmoothWindowMellin_line hN hR hsigma).sub
        (continuous_routeTNormalizedSmoothWindowMellin_line hN hH hsigma))
  unfold maynardFixedAmbientPhysicalDefectPacket
  simpa only [f] using intervalIntegral_sum_Ico_unitCells_eq hf hAB

/-- Integer-cell high shell with source height matched to its natural lower endpoint. -/
def routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
    (L X k : ℕ) (T₀ mu₀ M N R H U V : ℝ) (j : ℕ) (lambda : ℝ) : ℂ :=
  let A := routeTNaturalizedOrdinateLadder U V (j + 1)
  let B := routeTNaturalizedOrdinateLadder U V j
  let T₁ : ℝ := A
  let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
  maynardFixedAmbientPhysicalDefectPacket (Finset.Ico A B)
    (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) M
        ((1 : ℂ) + (y : ℝ) * Complex.I))
    lambda N R H 1

/-- Naturalized high shell is simultaneously the exact adjacent interval used by the receiver
and the fixed integer-cell packet used by spatial `L²/L⁴`. -/
theorem routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_eq_interval
    (L X k : ℕ) {T₀ mu₀ M N R H U V lambda : ℝ} {j : ℕ}
    (horder : routeTNaturalizedOrdinateLadder U V (j + 1) ≤
      routeTNaturalizedOrdinateLadder U V j)
    (hlambda : 0 < lambda) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) :
    routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
        L X k T₀ mu₀ M N R H U V j lambda =
      let A := routeTNaturalizedOrdinateLadder U V (j + 1)
      let B := routeTNaturalizedOrdinateLadder U V j
      let T₁ : ℝ := A
      let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
      routeTFixedSourceAdjacentIntervalPacket L X k T₁ (mu₁ / 120) M
        (lambda * N) (lambda * R) (lambda * H) 1 A B := by
  let A := routeTNaturalizedOrdinateLadder U V (j + 1)
  let B := routeTNaturalizedOrdinateLadder U V j
  let T₁ : ℝ := A
  let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T₁ (mu₁ / 120) M 1
  have hpacket := maynardFixedAmbientPhysicalDefectPacket_Ico_eq_intervalIntegral
    a ha lambda N R H 1 horder (mul_pos hlambda hN) (mul_pos hlambda hR)
      (mul_pos hlambda hH) (by norm_num)
  simpa only [routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket,
    routeTFixedSourceAdjacentIntervalPacket, routeTFixedSourceAdjacentIntegrand,
    A, B, T₁, mu₁, a, Complex.ofReal_one] using hpacket

/-- Every naturalized high shell is a literal equation-(111) packet. -/
theorem integral_norm_sq_routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_le_card
    (L X k : ℕ) {T₀ mu₀ M N R H U V x W : ℝ} {j cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hW : 0 ≤ W)
    (hcells : Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j) ⊆ Finset.range cellCount)
    (hsource : ∀ m ∈ Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTNaturalizedOrdinateLadder U V j),
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k
            (routeTNaturalizedOrdinateLadder U V (j + 1))
            (routeTHeightMatchedExponent T₀ mu₀
                (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * Complex.I)‖ ≤ W) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
          L X k T₀ mu₀ M N R H U V j lambda‖ ^ 2) ≤
      4 * (2 * x) * (2 * W) ^ 2 *
        ((Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTNaturalizedOrdinateLadder U V j)).card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k
      (routeTNaturalizedOrdinateLadder U V (j + 1))
      (routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k (routeTNaturalizedOrdinateLadder U V (j + 1))
      (routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M 1
  simpa only [routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket, a] using
    (integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card_of_source_bound
      hx hN hR hH hW
      (Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j)) hcells a ha hsource)

/-- Every naturalized high shell also carries the exact equation-(112) `R*` control. -/
theorem integral_norm_four_routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_le_rstar
    (L X k : ℕ) {T₀ mu₀ M N R H U V x W : ℝ} {j cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hW : 0 ≤ W)
    (hcells : Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j) ⊆ Finset.range cellCount)
    (hsource : ∀ m ∈ Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTNaturalizedOrdinateLadder U V j),
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k
            (routeTNaturalizedOrdinateLadder U V (j + 1))
            (routeTHeightMatchedExponent T₀ mu₀
                (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * Complex.I)‖ ≤ W) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
          L X k T₀ mu₀ M N R H U V j lambda‖ ^ 4) ≤
      4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        (2 * W) ^ 4 *
          (maynardRStar
            ((Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
              (routeTNaturalizedOrdinateLadder U V j)).map
                maynardNatToIntEmbedding) : ℝ) := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k
      (routeTNaturalizedOrdinateLadder U V (j + 1))
      (routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k (routeTNaturalizedOrdinateLadder U V (j + 1))
      (routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M 1
  simpa only [routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket, a] using
    (integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar_of_source_bound
      hx hN hR hH hW
      (Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j)) hcells a ha hsource)

/-- A large fixed-source integral on naturalized ladder endpoints selects a large shell whose
source is exactly reparameterized at the shell's natural lower endpoint. -/
theorem exists_fixedSource_naturalized_ordinate_shell_norm_ge
    (L X k : ℕ) {T₀ mu₀ M N R H sigma U V B : ℝ} {n : ℕ}
    (hT₀ : 1 < T₀) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hsigma : 0 < sigma) (hU : 1 < U) (hUV : U ≤ V) (hn : 0 < n)
    (hB : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T₀ (mu₀ / 120) M N R H sigma
        (routeTNaturalizedOrdinateLadder U V n)
        (routeTNaturalizedOrdinateLadder U V 0)‖) :
    ∃ j ∈ Finset.range n,
      let T₁ : ℝ := routeTNaturalizedOrdinateLadder U V (j + 1)
      let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
      1 < T₁ ∧
      B / (n : ℝ) ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₁ (mu₁ / 120) M N R H sigma
          (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTNaturalizedOrdinateLadder U V j)‖ := by
  let E : ℕ → ℝ := fun j => routeTNaturalizedOrdinateLadder U V j
  let f : ℝ → ℂ := routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M N R H sigma
  let F : ℕ → ℂ := fun j => ∫ y in E n..E j, f y
  have hf : Continuous f :=
    continuous_routeTFixedSourceAdjacentIntegrand
      L X k T₀ (mu₀ / 120) M hN hR hH hsigma
  have hendpoint : B ≤ ‖F 0 - F n‖ := by
    dsimp only [F]
    rw [intervalIntegral.integral_same, sub_zero]
    simpa only [E, f, routeTFixedSourceAdjacentIntervalPacket] using hB
  obtain ⟨j, hj, hlarge⟩ := complex_widthLadder_norm_pigeonhole F hn hendpoint
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (μ := volume) (a := E n) (b := E (j + 1)) (c := E j)
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hdiff : F j - F (j + 1) = ∫ y in E (j + 1)..E j, f y := by
    dsimp only [F]
    rw [← hadd]
    ring
  rw [hdiff] at hlarge
  let T₁ : ℝ := E (j + 1)
  let mu₁ : ℝ := routeTHeightMatchedExponent T₀ mu₀ T₁
  have hrealMem := routeTComparableWidthLadder_mem (by linarith : 0 < U) hUV (j + 1)
  have hrealCeil : routeTComparableWidthLadder U V (j + 1) ≤ T₁ := by
    dsimp only [T₁, E, routeTNaturalizedOrdinateLadder]
    exact Nat.le_ceil _
  have hT₁ : 1 < T₁ := hU.trans_le (hrealMem.1.trans hrealCeil)
  have hmatch := routeTFixedSourceAdjacentIntervalPacket_heightMatched
    (L := L) (X := X) (k := k) (T₀ := T₀) (mu₀ := mu₀) (T₁ := T₁)
    (M := M) (N := N) (R := R) (H := H) (sigma := sigma)
    (a := E (j + 1)) (b := E j) hT₀ hT₁
  refine ⟨j, hj, ?_⟩
  dsimp only
  refine ⟨hT₁, ?_⟩
  rw [← hmatch]
  simpa only [T₁, mu₁, E, f, routeTFixedSourceAdjacentIntervalPacket] using hlarge

/-- Natural-cell low/high dichotomy.  Unlike the real-shell cover, every selected high member is
already a fixed integer-cell packet, so no endpoint trimming or moving cell family survives. -/
theorem fixedSource_fullNaturalInterval_bad_subset_low_union_naturalized_shells
    (L X k K : ℕ) {T₀ mu₀ M sigma D U : ℝ} {n : ℕ}
    (hT₀ : 1 < T₀) (hsigma : 0 < sigma)
    (hU : 1 < U) (hUK : U ≤ (K : ℝ)) (hn : 0 < n)
    {N R H : ℝ → ℝ} {P : Set ℝ}
    (hN : ∀ lambda ∈ P, 0 < N lambda)
    (hR : ∀ lambda ∈ P, 0 < R lambda)
    (hH : ∀ lambda ∈ P, 0 < H lambda)
    (hlarge : ∀ lambda ∈ P,
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
          sigma 0 K‖) :
    P ⊆
      {lambda | D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
          sigma 0 (routeTNaturalizedOrdinateLadder U K n)‖} ∪
      ⋃ j ∈ Finset.range n,
        {lambda |
          (D / 2) / (n : ℝ) ≤
            ‖routeTFixedSourceAdjacentIntervalPacket
              L X k
                (routeTNaturalizedOrdinateLadder U K (j + 1))
                (routeTHeightMatchedExponent T₀ mu₀
                    (routeTNaturalizedOrdinateLadder U K (j + 1)) / 120)
                M (N lambda) (R lambda) (H lambda) sigma
                (routeTNaturalizedOrdinateLadder U K (j + 1))
                (routeTNaturalizedOrdinateLadder U K j)‖} := by
  intro lambda hlambda
  let E : ℕ → ℝ := fun j => routeTNaturalizedOrdinateLadder U K j
  let f : ℝ → ℂ := routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma
  have hf : Continuous f := continuous_routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M (hN lambda hlambda) (hR lambda hlambda)
      (hH lambda hlambda) hsigma
  have hEzero : E 0 = K := by
    dsimp only [E]
    exact_mod_cast routeTNaturalizedOrdinateLadder_initial hUK
  have hsplit : routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 K =
      routeTFixedSourceAdjacentIntervalPacket
          L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 (E n) +
        routeTFixedSourceAdjacentIntervalPacket
          L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma (E n) (E 0) := by
    unfold routeTFixedSourceAdjacentIntervalPacket
    rw [hEzero]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 (E n)) (hf.intervalIntegrable (E n) K)).symm
  by_cases hlow : D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
        sigma 0 (E n)‖
  · apply Set.mem_union_left
    change D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
        sigma 0 (routeTNaturalizedOrdinateLadder U K n)‖
    simpa only [E] using hlow
  · apply Set.mem_union_right
    have htri := norm_add_le
      (routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 (E n))
      (routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma (E n) (E 0))
    have hhigh : D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
          sigma (E n) (E 0)‖ := by
      rw [← hsplit] at htri
      exact le_of_not_gt fun hlt => hlow (by linarith [hlarge lambda hlambda])
    obtain ⟨j, hj, _hT₁, hshell⟩ :=
      exists_fixedSource_naturalized_ordinate_shell_norm_ge
        L X k hT₀ (hN lambda hlambda) (hR lambda hlambda) (hH lambda hlambda)
          hsigma hU hUK hn (by simpa only [E] using hhigh)
    apply Set.mem_iUnion_of_mem j
    apply Set.mem_iUnion_of_mem hj
    change (D / 2) / (n : ℝ) ≤
      ‖routeTFixedSourceAdjacentIntervalPacket L X k
        (routeTNaturalizedOrdinateLadder U K (j + 1))
        (routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U K (j + 1)) / 120)
        M (N lambda) (R lambda) (H lambda) sigma
        (routeTNaturalizedOrdinateLadder U K (j + 1))
        (routeTNaturalizedOrdinateLadder U K j)‖
    simpa only [E] using hshell

/-- Canonical natural-shell schedule.  Eventually the exact cutoff `floor T` contains a dyadic
natural-cell ladder starting above `T^(8/11)`.  Every nonterminal member has integer endpoints,
length at least two, lies in `[T₁,2T₁]`, and its lower endpoint stays in the receiver's
height band `[T^(8/11),T]`. -/
theorem eventually_exists_routeT_canonicalNaturalizedOrdinateShellSchedule :
    ∀ᶠ T₀ : ℝ in Filter.atTop,
      ∃ n : ℕ, ∃ U : ℝ,
        0 < n ∧
        U = (routeTPrimeGapPacketCutoff T₀ : ℝ) / (((2 ^ n : ℕ) : ℝ)) ∧
        T₀ ^ (8 / 11 : ℝ) ≤ U ∧
        U < 2 * T₀ ^ (8 / 11 : ℝ) ∧
        U ≤ (routeTPrimeGapPacketCutoff T₀ : ℝ) ∧
        routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) 0 =
          routeTPrimeGapPacketCutoff T₀ ∧
        (∀ j < n,
          T₀ ^ (8 / 11 : ℝ) ≤
              routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) (j + 1) ∧
          routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) (j + 1) + 2 ≤
              routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) j ∧
          routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) j ≤
              2 * routeTNaturalizedOrdinateLadder U
                (routeTPrimeGapPacketCutoff T₀) (j + 1) ∧
          (routeTNaturalizedOrdinateLadder U
              (routeTPrimeGapPacketCutoff T₀) j : ℝ) ≤ T₀) ∧
        (∀ j, n ≤ j →
          routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T₀) j =
            ⌈U⌉₊) := by
  have hdom :=
    GaloisForLFunctions.HTGeometry.eventually_const_mul_rpow_le
      (c := (3 : ℝ)) (θ := (8 / 11 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1)
  let Tbase : ℝ := (2 : ℝ) ^ (11 / 8 : ℝ)
  filter_upwards [hdom, Filter.eventually_ge_atTop Tbase] with T₀ hdomT hT₀
  let A : ℝ := T₀ ^ (8 / 11 : ℝ)
  let K : ℕ := routeTPrimeGapPacketCutoff T₀
  have hTbase : 0 < Tbase := by dsimp only [Tbase]; positivity
  have hT₀0 : 0 < T₀ := hTbase.trans_le hT₀
  have hT₀one : 1 ≤ T₀ := by
    have hbaseOne : (1 : ℝ) ≤ Tbase := by
      dsimp only [Tbase]
      exact Real.one_le_rpow (by norm_num) (by norm_num)
    exact hbaseOne.trans hT₀
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAone : 1 ≤ A := by
    dsimp only [A]
    exact Real.one_le_rpow hT₀one (by norm_num)
  have hAtwo : 2 ≤ A := by
    have hpow := Real.rpow_le_rpow hTbase.le hT₀ (by norm_num : (0 : ℝ) ≤ 8 / 11)
    have hbasePow : Tbase ^ (8 / 11 : ℝ) = 2 := by
      dsimp only [Tbase]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rwa [hbasePow] at hpow
  have hfloor : (2 * A : ℝ) ≤ (K : ℝ) := by
    have hfloorNear := Nat.lt_floor_add_one T₀
    have hthree : 3 * A ≤ T₀ := by simpa only [A, one_mul] using hdomT
    dsimp only [K, routeTPrimeGapPacketCutoff]
    linarith
  obtain ⟨n, U, hn, hU, hAU, hUA, hUK, hshell, hterminal⟩ :=
    exists_routeT_dyadicallyAlignedOrdinateLowerCutoff hA hfloor
  have hUtwo : 2 ≤ U := hAtwo.trans hAU
  have hinitial : routeTNaturalizedOrdinateLadder U K 0 = K :=
    routeTNaturalizedOrdinateLadder_initial hUK
  have hKTop : (K : ℝ) ≤ T₀ := by
    dsimp only [K, routeTPrimeGapPacketCutoff]
    exact Nat.floor_le hT₀0.le
  have hfull : ∀ j < n,
      A ≤ routeTNaturalizedOrdinateLadder U K (j + 1) ∧
      routeTNaturalizedOrdinateLadder U K (j + 1) + 2 ≤
        routeTNaturalizedOrdinateLadder U K j ∧
      routeTNaturalizedOrdinateLadder U K j ≤
        2 * routeTNaturalizedOrdinateLadder U K (j + 1) ∧
      (routeTNaturalizedOrdinateLadder U K j : ℝ) ≤ T₀ := by
    intro j hj
    have hgeom := routeTNaturalizedOrdinateLadder_fullShell hUtwo hshell hj
    have hUpos : 0 < U := hA.trans_le hAU
    have hmemNext := routeTComparableWidthLadder_mem hUpos hUK (j + 1)
    have hmemJ := routeTComparableWidthLadder_mem hUpos hUK j
    have hceilNext : routeTComparableWidthLadder U K (j + 1) ≤
        (routeTNaturalizedOrdinateLadder U K (j + 1) : ℝ) := by
      exact Nat.le_ceil _
    have hnaturalTop : routeTNaturalizedOrdinateLadder U K j ≤ K := by
      apply Nat.ceil_le.mpr
      exact hmemJ.2
    refine ⟨hAU.trans (hmemNext.1.trans hceilNext), hgeom.1, hgeom.2, ?_⟩
    have hnaturalTopReal :
        (routeTNaturalizedOrdinateLadder U K j : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hnaturalTop
    exact hnaturalTopReal.trans hKTop
  have hterminalNatural : ∀ j, n ≤ j →
      routeTNaturalizedOrdinateLadder U K j = ⌈U⌉₊ := by
    intro j hj
    exact routeTNaturalizedOrdinateLadder_terminal hterminal hj
  exact ⟨n, U, hn, hU, hAU, hUA, hUK, hinitial, hfull, hterminalNatural⟩

/-- Literal fixed-width Route-T packet on one naturalized high shell.  Its source is frozen at the
natural lower endpoint and its cell family is an integer `Ico` fixed before `lambda` varies. -/
def routeTFixedWidthNaturalizedOrdinateShellPacket
    (T : ℝ) (L : ℕ) (H0 U : ℝ) (r j : ℕ) (lambda : ℝ) : ℂ :=
  routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
    L (routeTPrimeGapPacketSupport T) 60 T (8 / 5)
      (routeTPrimeGapPacketBase T) 1
      (routeTComparableWidthLadder H0 (1 / 4) r)
      (routeTComparableWidthLadder H0 (1 / 4) (r + 1))
      U (routeTPrimeGapPacketCutoff T) j lambda

/-- One literal fixed-width rung splits into a low packet and finitely many natural-cell high
shell packets.  This is the quantifier-correct bridge from the prime-free producer to the spatial
`L²/L⁴` interfaces. -/
theorem routeTFixedWidth_rung_bad_subset_low_union_naturalized_shells
    {T : ℝ} {L : ℕ} {H0 D U : ℝ} {r n : ℕ}
    (hT : 1 < T) (hH0 : 0 < H0)
    (hU : 1 < U) (hUK : U ≤ (routeTPrimeGapPacketCutoff T : ℝ)) (hn : 0 < n)
    (horder : ∀ j < n,
      routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1) ≤
        routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j) :
    {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T) ∧
        D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖} ⊆
      {lambda | D / 2 ≤
        ‖routeTFixedWidthLowOrdinatePacket T L H0 r
          (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) n) lambda‖} ∪
      ⋃ j ∈ Finset.range n,
        {lambda | (D / 2) / (n : ℝ) ≤
          ‖routeTFixedWidthNaturalizedOrdinateShellPacket
            T L H0 U r j lambda‖} := by
  let P : Set ℝ := {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
      (2 * routeTPrimeGapPacketBase T) ∧
    D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖}
  have hx : 0 < routeTPrimeGapPacketBase T := by
    unfold routeTPrimeGapPacketBase
    positivity
  have hN : ∀ lambda ∈ P, 0 < lambda := by
    intro lambda hlambda
    exact hx.trans_le hlambda.1.1
  have hR : ∀ lambda ∈ P,
      0 < lambda * routeTComparableWidthLadder H0 (1 / 4) r := by
    intro lambda hlambda
    exact mul_pos (hN lambda hlambda) (routeTComparableWidthLadder_pos hH0 r)
  have hH : ∀ lambda ∈ P,
      0 < lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1) := by
    intro lambda hlambda
    exact mul_pos (hN lambda hlambda)
      (routeTComparableWidthLadder_pos hH0 (r + 1))
  have hlarge : ∀ lambda ∈ P,
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L (routeTPrimeGapPacketSupport T) 60 T ((8 / 5 : ℝ) / 120)
        (routeTPrimeGapPacketBase T) lambda
        (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
        (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
        1 0 (routeTPrimeGapPacketCutoff T : ℝ)‖ := by
    intro lambda hlambda
    rw [show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num]
    rw [← routeTFixedWidthPhysicalDefectPacket_eq_fixedSourceInterval
      hH0 (hN lambda hlambda)]
    exact hlambda.2
  have hcover := fixedSource_fullNaturalInterval_bad_subset_low_union_naturalized_shells
    L (routeTPrimeGapPacketSupport T) 60 (routeTPrimeGapPacketCutoff T)
      hT (by norm_num) hU hUK hn
      (N := fun lambda => lambda)
      (R := fun lambda => lambda * routeTComparableWidthLadder H0 (1 / 4) r)
      (H := fun lambda => lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
      (P := P) hN hR hH hlarge
  intro lambda hlambda
  have hrefined := hcover hlambda
  rcases hrefined with hlow | hhigh
  · apply Set.mem_union_left
    simpa only [P, routeTFixedWidthLowOrdinatePacket,
      show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num] using hlow
  · apply Set.mem_union_right
    obtain ⟨j, hjrange⟩ := Set.mem_iUnion.mp hhigh
    obtain ⟨hj, hjlarge⟩ := Set.mem_iUnion.mp hjrange
    have hlambdaPos : 0 < lambda := hN lambda hlambda
    have hR0 : 0 < routeTComparableWidthLadder H0 (1 / 4) r :=
      routeTComparableWidthLadder_pos hH0 r
    have hH0' : 0 < routeTComparableWidthLadder H0 (1 / 4) (r + 1) :=
      routeTComparableWidthLadder_pos hH0 (r + 1)
    have heq := routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_eq_interval
      (L := L) (X := routeTPrimeGapPacketSupport T) (k := 60)
      (T₀ := T) (mu₀ := (8 / 5 : ℝ)) (M := routeTPrimeGapPacketBase T)
      (N := 1) (R := routeTComparableWidthLadder H0 (1 / 4) r)
      (H := routeTComparableWidthLadder H0 (1 / 4) (r + 1))
      (U := U) (V := routeTPrimeGapPacketCutoff T) (lambda := lambda) (j := j)
      (horder j (Finset.mem_range.mp hj)) hlambdaPos (by norm_num) hR0 hH0'
    apply Set.mem_iUnion_of_mem j
    apply Set.mem_iUnion_of_mem hj
    change (D / 2) / (n : ℝ) ≤
      ‖routeTFixedWidthNaturalizedOrdinateShellPacket T L H0 U r j lambda‖
    rw [routeTFixedWidthNaturalizedOrdinateShellPacket, heq]
    change (D / 2) / (n : ℝ) ≤
      ‖routeTFixedSourceAdjacentIntervalPacket
        L (routeTPrimeGapPacketSupport T) 60
        (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1))
        (routeTHeightMatchedExponent T (8 / 5)
          (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1)) / 120)
        (routeTPrimeGapPacketBase T) lambda
        (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
        (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1)) 1
        (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1))
        (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j)‖ at hjlarge
    simpa only [mul_one] using hjlarge

/-- Finite natural-cell low/high cover attached to one fixed physical width. -/
def routeTFixedWidthPrimeGapNaturalLowHighShellCover
    (T : ℝ) (L : ℕ) (H0 U : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ r ∈ Finset.range (routeTFixedWidthRungCount H0),
    ({lambda |
      (routeTFixedWidthPacketDefectFloor /
          (routeTFixedWidthRungCount H0 : ℝ)) / 2 ≤
        ‖routeTFixedWidthLowOrdinatePacket T L H0 r
          (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) n) lambda‖} ∪
      ⋃ j ∈ Finset.range n,
        {lambda |
          ((routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ)) / 2) / (n : ℝ) ≤
            ‖routeTFixedWidthNaturalizedOrdinateShellPacket
              T L H0 U r j lambda‖})

/-- Any fixed-width rung cover refines to the natural-cell low/high cover without introducing a
base-dependent shell or source choice. -/
theorem routeTFixedWidth_rung_cover_refines_to_naturalized_low_high_shell_cover
    {T : ℝ} {L Q n : ℕ} {H0 D U : ℝ} {P : Set ℝ}
    (hT : 1 < T) (hH0 : 0 < H0) (hU : 1 < U)
    (hUK : U ≤ (routeTPrimeGapPacketCutoff T : ℝ)) (hn : 0 < n)
    (horder : ∀ j < n,
      routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1) ≤
        routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j)
    (hPblock : P ⊆ Set.Icc (routeTPrimeGapPacketBase T)
      (2 * routeTPrimeGapPacketBase T))
    (hcover : P ⊆ ⋃ r ∈ Finset.range Q,
      {lambda | D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖}) :
    P ⊆ ⋃ r ∈ Finset.range Q,
      ({lambda | D / 2 ≤
        ‖routeTFixedWidthLowOrdinatePacket T L H0 r
          (routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) n) lambda‖} ∪
      ⋃ j ∈ Finset.range n,
        {lambda | (D / 2) / (n : ℝ) ≤
          ‖routeTFixedWidthNaturalizedOrdinateShellPacket
            T L H0 U r j lambda‖}) := by
  intro lambda hlambda
  obtain ⟨r, hrrange⟩ := Set.mem_iUnion.mp (hcover hlambda)
  obtain ⟨hr, hbad⟩ := Set.mem_iUnion.mp hrrange
  have hrefined := routeTFixedWidth_rung_bad_subset_low_union_naturalized_shells
    hT hH0 hU hUK hn horder
      (show lambda ∈ {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T) ∧
        D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖} from
        ⟨hPblock hlambda, hbad⟩)
  apply Set.mem_iUnion_of_mem r
  apply Set.mem_iUnion_of_mem hr
  exact hrefined

/-- **Canonical prime-free natural-shell cover.**  Eventually one Möbius cutoff and one
natural-cell dyadic ordinate schedule are fixed before physical width and base.  Every high shell
has length at least two, lies in its receiver band, and is already a literal spatial `L²/L⁴`
packet.  Thus all real-endpoint and moving-family residuals are absent from the prime-free cover. -/
theorem exists_eventually_routeT_fixedWidth_primeFree_subset_naturalized_low_high_shell_cover :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∃ L n : ℕ, ∃ U : ℝ,
          1 ≤ L ∧
          routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
          (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
          0 < n ∧
          T ^ (8 / 11 : ℝ) ≤ U ∧
          U < 2 * T ^ (8 / 11 : ℝ) ∧
          U ≤ (routeTPrimeGapPacketCutoff T : ℝ) ∧
          (∀ j < n,
            T ^ (8 / 11 : ℝ) ≤
                routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1) ∧
            routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1) + 2 ≤
                routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j ∧
            routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j ≤
                2 * routeTNaturalizedOrdinateLadder U
                  (routeTPrimeGapPacketCutoff T) (j + 1) ∧
            (routeTNaturalizedOrdinateLadder U
                (routeTPrimeGapPacketCutoff T) j : ℝ) ≤ T) ∧
          ∀ H0 : ℝ, 0 < H0 → H0 ≤ 1 / 4 →
            routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
            routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
              routeTFixedWidthPrimeGapNaturalLowHighShellCover T L H0 U n := by
  obtain ⟨C50, hC50, hwidthCover⟩ :=
    exists_eventually_routeT_fixedWidth_primeFree_subset_rung_union
  refine ⟨C50, hC50, ?_⟩
  filter_upwards [hwidthCover,
    eventually_exists_routeT_canonicalNaturalizedOrdinateShellSchedule,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hwidthT hschedule hT
  obtain ⟨L, hL, hXL, hLscale, hcover⟩ := hwidthT
  obtain ⟨n, U, hn, _hUeq, hUlower, hUupper, hUK, _hinitial,
    hfull, _hterminal⟩ := hschedule
  refine ⟨L, n, U, hL, hXL, hLscale, hn, hUlower, hUupper, hUK, hfull, ?_⟩
  intro H0 hH0 hH0quarter hpacketWidth
  have hUone : 1 < U := by
    have hpowOne : 1 < T ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hUlower
  have horder : ∀ j < n,
      routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) (j + 1) ≤
        routeTNaturalizedOrdinateLadder U (routeTPrimeGapPacketCutoff T) j := by
    intro j hj
    have hlen := (hfull j hj).2.1
    omega
  have hPblock : routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
      Set.Icc (routeTPrimeGapPacketBase T) (2 * routeTPrimeGapPacketBase T) := by
    intro lambda hlambda
    exact hlambda.1
  have hrefined :=
    routeTFixedWidth_rung_cover_refines_to_naturalized_low_high_shell_cover
      hT hH0 hUone hUK hn horder hPblock
        (hcover H0 hH0 hH0quarter hpacketWidth)
  simpa only [routeTFixedWidthPrimeGapNaturalLowHighShellCover] using hrefined

/-- On every canonical natural high shell, each exact amplitude band satisfies both parity
Maynard alternatives through the full `11/5` exponent range.  Integer endpoints supply the
receiver's unit-cell geometry directly; no adaptive real-cell extraction is used. -/
theorem eventually_routeT_canonicalNaturalShell_amplitudeBand_twoAlternative
    (q : ℕ) :
    ∀ᶠ T₀ : ℝ in Filter.atTop,
      ∀ {L A B : ℕ} {V : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T₀ →
      routeTPrimeGapPacketSupport T₀ < (L + 1) ^ 60 →
      (L : ℝ) ≤ T₀ ^ (2 / 75 : ℝ) →
      T₀ ^ (8 / 11 : ℝ) ≤ (A : ℝ) →
      (A : ℝ) ≤ T₀ → B ≤ 2 * A →
      0 < V →
      heathBrownEligibleBoxCost L (routeTPrimeGapPacketSupport T₀) 60 *
        (routeTPrimeGapPacketBase T₀ / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      let T₁ : ℝ := A
      let mu₁ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
      let source : ℝ → ℂ := fun y =>
        heathBrownWindowRelevantEligibleDyadicAggregate
          L (routeTPrimeGapPacketSupport T₀) 60 T₁ (mu₁ / 120)
            (routeTPrimeGapPacketBase T₀) ((1 : ℂ) + (y : ℝ) * Complex.I)
      let band := maynardUnitCellAmplitudeBand (Finset.Ico A B) source c V
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre band A).card : ℝ) T₁ (T₁ ^ mu₁)
            (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T₀) 60
              (routeTPrimeGapPacketBase T₀) V) ∧
        IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre band A).card : ℝ) T₁ (T₁ ^ mu₁)
            (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T₀) 60
              (routeTPrimeGapPacketBase T₀) V) := by
  obtain ⟨C, hreceiver⟩ := Filter.eventually_atTop.1
    (eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative_elevenFifths q)
  have hheight : ∀ᶠ T₀ : ℝ in Filter.atTop, C ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop C
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hheight, hbaseLarge, Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hheightT hbase hT₀
  intro L A B V hL hLX hXL hLscale hAlower hAupper hB hV hlow c hc
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let T₁ : ℝ := A
  let mu₁ : ℝ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
  let source : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T₁ (mu₁ / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT₀
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hAlower
  have hreceiverT := hreceiver T₁ (hheightT.trans hAlower)
    (L := L) (X := X) (K := A) (mu := mu₁) (N0 := M) (V := V)
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hsupport := routeTPrimeGapPacketSupport_comparable_eligibilityScale
    (by linarith : 0 < T₀) (by simpa only [M] using hM)
  have hexact : T₁ ^ mu₁ = T₀ ^ (8 / 5 : ℝ) := by
    dsimp only [mu₁]
    exact rpow_routeTHeightMatchedExponent hT₀ hT₁
  have hXscale : (X : ℝ) ≤ T₁ ^ mu₁ := by
    rw [hexact]
    simpa only [X] using hsupport.1
  have hmu : mu₁ ∈ Set.Icc (4 / 3 : ℝ) (11 / 5 : ℝ) := by
    dsimp only [mu₁, T₁]
    exact routeTHeightMatchedExponent_mem_fourThird_elevenFifths hT₀ hAlower hAupper
  have hLscaleShell : (L : ℝ) ≤ T₁ ^ (2 * (mu₁ / 120)) := by
    have hscaleEq : T₁ ^ (2 * (mu₁ / 120)) = T₀ ^ (2 / 75 : ℝ) := by
      calc
        T₁ ^ (2 * (mu₁ / 120)) = T₁ ^ (mu₁ * (1 / 60 : ℝ)) := by
          congr 1
          ring
        _ = (T₁ ^ mu₁) ^ (1 / 60 : ℝ) :=
          Real.rpow_mul (zero_le_one.trans hT₁.le) mu₁ (1 / 60 : ℝ)
        _ = (T₀ ^ (8 / 5 : ℝ)) ^ (1 / 60 : ℝ) := by rw [hexact]
        _ = T₀ ^ (2 / 75 : ℝ) := by
          rw [← Real.rpow_mul (zero_le_one.trans hT₀.le)]
          norm_num
    rw [hscaleEq]
    exact hLscale
  have hlowCutoff : (X : ℝ) / (2 ^ 120 : ℝ) ≤ M := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 120)).2
    have hXM : (X : ℝ) ≤ 4 * M := by
      calc
        (X : ℝ) ≤ T₀ ^ (8 / 5 : ℝ) := by simpa only [X] using hsupport.1
        _ = 4 * M := by
          dsimp only [M, routeTPrimeGapPacketBase]
          field_simp
    calc
      (X : ℝ) ≤ 4 * M := hXM
      _ ≤ M * (2 ^ 120 : ℝ) := by
        have hfour : (4 : ℝ) ≤ 2 ^ 120 := by norm_num
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour hM0
  have hMbase : 1 < M / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [M]
    linarith
  have hUrange : Finset.Ico A B ⊆ Finset.range (2 * A) := by
    intro m hm
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hm).2.trans_le hB)
  have hordinate : ∀ m ∈ Finset.Ico A B,
      T₁ ≤ c m ∧ c m ≤ 2 * T₁ := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    have hcm := hc m
    constructor
    · have hmAreal : (A : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmIco.1
      exact hmAreal.trans hcm.1
    · have hmB : m + 1 ≤ B := by omega
      have hmTop : ((m : ℝ) + 1) ≤ 2 * (A : ℝ) := by exact_mod_cast hmB.trans hB
      exact hcm.2.trans (by simpa only [T₁, Nat.cast_mul, Nat.cast_ofNat] using hmTop)
  simpa only [X, M, T₁, mu₁, source] using
    (hreceiverT hX hL (by simpa only [X] using hXL) hXscale hLscaleShell
      hmu.1 hmu.2 hlowCutoff hMbase hV (by simpa only [X, M] using hlow)
      (by exact le_rfl) (Finset.Ico A B) hUrange c hc hordinate)


end RHTower.Sieve
