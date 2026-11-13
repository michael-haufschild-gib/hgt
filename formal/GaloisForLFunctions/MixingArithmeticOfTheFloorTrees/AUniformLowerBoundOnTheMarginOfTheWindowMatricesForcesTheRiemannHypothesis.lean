import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheAntisymmetricStateOfTheTwoEndsIsBoundedBelowIffTheRiemannHypothesis
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleIsDecidedOnBlockAverages

/-!
# A uniform lower bound on the margin of the window matrices forces the Riemann hypothesis

At finite block size the margin of a window `(R, R + J]` is the second eigenvalue of its neutral
part `N_W`, the bound states beyond the first. RH holds iff every `N_W` with `R ≤ J` has exactly
one negative square (AGZ). Any uniform lower bound is enough:

  **RH iff for some `C` every `N_W + C` has at most one negative square**
  (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`),

i.e. iff the second eigenvalue of all window matrices is bounded below. In terms of the Doob chain
(`riemannHypothesis_iff_forall_doob_poincare_sub`): RH iff for some `C` the Poincaré constant of
every window is at least its binding energy minus `C`. The windows `(1, 2M]` suffice
(`riemannHypothesis_iff_initialWindow_margin_bddBelow`): they are the leading principal minors of
one infinite matrix, and RH is the statement that its second eigenvalue is finite. Together with
the bounded margin (`exists_doob_test_le`), RH says that the margin lies in `[0, c₀]`,
and the margin is unbounded below as soon as it is negative somewhere.

The proof runs in three steps.

* **Step packets** (`riemannHypothesis_iff_packetForm_stepPacket_bddBelow`): RH iff Weil's form on
  the step packets of all windows is at least `−D Σ σ²` for some `D`. A lower bound on the step
  packets passes to the comb at large block size (`eventually_combForm_blockFunction_ge_neg`),
  from the block functions to all divisors through the block averages
  (`frequently_combForm_ge_neg`), and to the zeros on the samples of a smooth packet
  (`neg_mul_le_zeroSum_of_frequently`). On the antisymmetric state of the two ends, moved into
  the window (`shiftedOdd`), the sum over the zeros is `2 Re S(0) − 2 Re S(v)` and the mass is
  bounded, so `S` is bounded above and Landau's argument gives RH.
* **Two deep bound states** (`exists_two_le_hermNegIndex_neutralWindow_add`): a step packet with
  `𝔚(σ) < −C Σ σ²` gives, on a window `(1, 2M]`, a plane on which `N + C` is negative. The plane
  is that of AGZ: the refinement of `σ`, a far dyadic window and the block one, whose pole
  pairings make a hyperbolic plane; the far window and the block one carry vanishing mass, so
  adding `C` times the mass moves the limit Gram matrix `diag(𝔚(σ), −2ℓ)` only in its first
  entry, to `𝔚(σ) + C Σ σ² < 0`.
-/

open Finset Filter Topology MeasureTheory Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.HodgeTheoryOfAFixedPart (blockIndex blockMean combForm sampleCoord)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### From step packets to the zeros, with a fixed lower bound -/

/-- If Weil's form is at least `−D Σ σ²` on the step packets of `J` blocks, then at all large block
sizes Weil's form on the comb is at least `−(D + η) Σ σ²` on every divisor constant on the
blocks. -/
theorem eventually_combForm_blockFunction_ge_neg {R J Q : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    {D η : ℝ} (hη : 0 < η)
    (hD : ∀ σ : ℕ → ℝ, -(D * ∑ j ∈ range J, σ j ^ 2) ≤ packetForm Q (stepPacket R J σ)) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      -(D + η) * ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) := by
  have hev := eventually_abs_combForm_nested_sub_le (s := range (J + 1)) (x := fun j => R + j)
    (X := R + J) (Q := Q) hR (nested_bounds R J) hQ (η := η / 4) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with B hB hB1 σ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB1
  have h := hB (nestedCoeff J σ)
  have hwin : (R + J) * B = R * B + B * J := by ring
  have hc : combForm (Ioc (R * B) (R * B + B * J)) (fun n => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n) =
      combForm (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) :=
    (combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn).symm
  rw [hwin, hc, ← stepPacket_eq_nested hR J σ] at h
  have hsq := mul_le_mul_of_nonneg_left (sum_nestedCoeff_sq_le J σ)
    (by positivity : (0 : ℝ) ≤ η / 4)
  have hpf := hD σ
  have hlow : -((D + η) * ∑ j ∈ range J, σ j ^ 2) ≤
      combForm (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B := by
    have h1 := (abs_le.mp h).1
    linarith
  rw [sum_blockFunction_sq (by omega) σ]
  have h3 := (le_div_iff₀ hB0).mp hlow
  linarith

/-- A lower bound on the block functions at infinitely many block sizes, for blocks of every
length, gives the lower bound on all divisors at infinitely many scales, up to any `η > 0`: the
form of a divisor is at least that of its block averages minus `η Σ c_n²`. -/
theorem frequently_combForm_ge_neg {K : ℕ} {D η : ℝ} (hD0 : 0 ≤ D) (hη : 0 < η)
    (h : ∀ R : ℕ, 0 < R → ∃ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      -D * ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), σ (blockIndex (R * B) B n) ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * (3 * K * R))) fun n => σ (blockIndex (R * B) B n)) :
    ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -(D + η) * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combForm (Ioc N (N + 3 * K * N)) c := by
  obtain ⟨R, hR, hred⟩ := HodgeTheoryOfAFixedPart.exists_blockSize_combForm_ge_blockMean
    (3 * K + 1) hη
  have hfreq := (h R hR).and_eventually (eventually_ge_atTop 1)
  have htend : Tendsto (fun B : ℕ => R * B) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_mul_of_pos_left B hR) tendsto_id
  refine htend.frequently (hfreq.mono fun B hB => ?_)
  obtain ⟨hσ, hB1⟩ := hB
  show ∀ c : ℕ → ℝ, -(D + η) * ∑ n ∈ Ioc (R * B) (R * B + 3 * K * (R * B)), c n ^ 2 ≤
    combForm (Ioc (R * B) (R * B + 3 * K * (R * B))) c
  intro c
  have hdiv : R * B / R = B := Nat.mul_div_cancel_left B hR
  have hwin : R * B + 3 * K * (R * B) = R * B + B * (3 * K * R) := by ring
  have h1 := hred (R * B) (3 * K * R) (Nat.le_mul_of_pos_right R hB1)
    (by rw [hdiv]; exact le_of_eq (by ring)) c
  rw [hdiv] at h1
  have h2 := hσ (blockMean (R * B) B (3 * K * R) c)
  have h3 := mul_le_mul_of_nonneg_left
    (HodgeTheoryOfAFixedPart.sum_blockMean_sq_le (by omega : 0 < B) (R * B) (3 * K * R) c) hD0
  rw [hwin]
  linarith

/-- A lower bound `−D Σ c_n²` on the comb at infinitely many scales gives `Z(f) ≥ −D ∫ f²` on
every smooth packet of the window. -/
theorem neg_mul_le_zeroSum_of_frequently {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {D : ℝ}
    (h : ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -D * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combForm (Ioc N (N + 3 * K * N)) c) :
    -D * ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 ≤ zeroSum f := by
  have hI := HodgeTheoryOfAFixedPart.tendsto_sum_sq_sampleCoord hf.continuous hK
  have hZ := HodgeTheoryOfAFixedPart.tendsto_combForm_sample hf hfc hK hsupp
  have key : 0 ≤ zeroSum f + D * ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 :=
    ge_of_tendsto_of_frequently (hZ.add (hI.const_mul D))
    (h.mono fun N hN => by
      have := hN (sampleCoord f N)
      show 0 ≤ combForm (Ioc N (N + 3 * K * N)) (sampleCoord f N) +
        D * ∑ n ∈ Ioc N (N + 3 * K * N), sampleCoord f N n ^ 2
      linarith)
  linarith

/-! ### The antisymmetric state inside the window of the comb -/

/-- The antisymmetric state of the two ends, translated to the right of `log 3`. -/
def shiftedOdd (v u : ℝ) : ℝ := twoEndOdd v (u - (Real.log 3 + 6 + |v| / 2))

theorem contDiff_shiftedOdd (v : ℝ) : ContDiff ℝ 2 (shiftedOdd v) :=
  (contDiff_twoEndOdd v).comp (contDiff_id.sub contDiff_const)

/-- The translated state lives in `[log 3 + 1, log 3 + 11 + |v|]`. -/
theorem shiftedOdd_eq_zero (v : ℝ) {u : ℝ}
    (hu : u ≤ Real.log 3 ∨ Real.log 3 + 12 + |v| ≤ u) : shiftedOdd v u = 0 := by
  refine twoEndOdd_eq_zero v ?_
  have hv := abs_nonneg v
  rcases hu with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  · exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem exists_log_le (v : ℝ) : ∃ K : ℕ, 1 ≤ K ∧ Real.log 3 + 12 + |v| ≤ Real.log K := by
  refine ⟨⌈Real.exp (Real.log 3 + 12 + |v|)⌉₊, Nat.ceil_pos.mpr (Real.exp_pos _), ?_⟩
  calc Real.log 3 + 12 + |v| = Real.log (Real.exp (Real.log 3 + 12 + |v|)) :=
        (Real.log_exp _).symm
    _ ≤ Real.log (⌈Real.exp (Real.log 3 + 12 + |v|)⌉₊ : ℕ) :=
        Real.log_le_log (Real.exp_pos _) (Nat.le_ceil _)

theorem hasCompactSupport_shiftedOdd (v : ℝ) : HasCompactSupport (shiftedOdd v) :=
  HasCompactSupport.intro (isCompact_Icc (a := Real.log 3) (b := Real.log 3 + 12 + |v|))
    fun u hu => shiftedOdd_eq_zero v (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le)

/-- On the translated state the sum over the zeros is `2 Re S(0) − 2 Re S(v)`: the sum over the
zeros is Weil's form, which is invariant under translation, and the state has no charges. -/
theorem zeroSum_shiftedOdd (v : ℝ) :
    zeroSum (shiftedOdd v) =
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re -
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re := by
  obtain ⟨Q₁, hQ₁⟩ := exists_range_twoEndOdd v
  obtain ⟨K, hK1, hK⟩ := exists_log_le v
  have hQs : ∀ n : ℕ, max Q₁ K < n → packetAutocorr (shiftedOdd v) (Real.log n) = 0 := by
    intro n hn
    have hKn : (K : ℝ) < n := by exact_mod_cast (le_max_right Q₁ K).trans_lt hn
    have hlog : Real.log K < Real.log n :=
      Real.log_lt_log (by exact_mod_cast (show 0 < K by omega)) hKn
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    refine packetAutocorr_eq_zero_of_vanishing_off (a := Real.log 3) (b := Real.log 3 + 12 + |v|)
      (fun u hu => shiftedOdd_eq_zero v ?_) (by linarith)
    rcases hu with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hQo : ∀ n : ℕ, max Q₁ K < n → packetAutocorr (twoEndOdd v) (Real.log n) = 0 :=
    fun n hn => hQ₁ n ((le_max_left Q₁ K).trans_lt hn)
  rw [zeroSum_eq_packetForm (contDiff_shiftedOdd v) (hasCompactSupport_shiftedOdd v) hQs,
    show shiftedOdd v = fun u => twoEndOdd v (u - (Real.log 3 + 6 + |v| / 2)) from rfl,
    packetForm_translate, ← neutralForm_twoEndOdd v hQo]
  unfold neutralForm
  rw [charge_twoEndOdd v, zero_mul, mul_zero, sub_zero]

theorem intervalIntegral_sq_le_integral {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {b : ℝ} (hb : 0 ≤ b) :
    ∫ u in (0 : ℝ)..b, g u ^ 2 ≤ ∫ u, g u ^ 2 := by
  have hc2 : Continuous fun u => g u ^ 2 := hg.pow 2
  have hint : Integrable fun u => g u ^ 2 :=
    hc2.integrable_of_hasCompactSupport (hgc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
  rw [intervalIntegral.integral_of_le hb]
  exact setIntegral_le_integral hint (Eventually.of_forall fun u => sq_nonneg (g u))

theorem integral_comp_sub_sq (g : ℝ → ℝ) (c : ℝ) : ∫ u, g (u - c) ^ 2 = ∫ u, g u ^ 2 :=
  integral_sub_right_eq_self (fun u => g u ^ 2) c

theorem intervalIntegral_shiftedOdd_sq_le (v : ℝ) (K : ℕ) :
    ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), shiftedOdd v u ^ 2 ≤
      4 * ∫ u, poleFreeProfile u ^ 2 := by
  have hpos : (0 : ℝ) ≤ Real.log (1 + ((3 * K : ℕ) : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ ((3 * K : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  calc ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), shiftedOdd v u ^ 2
      ≤ ∫ u, shiftedOdd v u ^ 2 :=
        intervalIntegral_sq_le_integral (contDiff_shiftedOdd v).continuous
          (hasCompactSupport_shiftedOdd v) hpos
    _ = ∫ u, twoEndOdd v u ^ 2 := integral_comp_sub_sq (twoEndOdd v) (Real.log 3 + 6 + |v| / 2)
    _ ≤ 4 * ∫ u, poleFreeProfile u ^ 2 := integral_twoEndOdd_sq_le v

/-! ### Step packets -/

/-- **A lower bound on Weil's form on the step packets forces RH.** If for some `D ≥ 0` Weil's
form on the step packets of every window `(R, (3K + 1)R]` is at least `−D Σ σ²`, the lag
structure of the pole-free profile is bounded above, and Landau's argument gives RH. -/
theorem riemannHypothesis_of_packetForm_stepPacket_ge {D : ℝ} (hD0 : 0 ≤ D)
    (h : ∀ K : ℕ, 1 ≤ K → ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      -(D * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
        packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ)) :
    RiemannHypothesis := by
  have hcomb : ∀ K : ℕ, 1 ≤ K → ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -((D + 1) + 1) * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤
        combForm (Ioc N (N + 3 * K * N)) c := by
    intro K hK
    refine frequently_combForm_ge_neg (by linarith) one_pos fun R hR => ?_
    exact (eventually_combForm_blockFunction_ge_neg (by omega) (le_of_eq (by ring)) one_pos
      (h K hK R (by omega))).frequently
  refine riemannHypothesis_of_lagStructure_le
    (M := 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re +
      (D + 1 + 1) * (4 * ∫ u, poleFreeProfile u ^ 2)) fun v _ => ?_
  obtain ⟨K, hK1, hK⟩ := exists_log_le v
  have hz := neg_mul_le_zeroSum_of_frequently (contDiff_shiftedOdd v)
    (hasCompactSupport_shiftedOdd v) hK1
    (fun u hu => shiftedOdd_eq_zero v (by
      rcases hu with h | h
      · exact Or.inl h
      · exact Or.inr (hK.trans h)))
    (hcomb K hK1)
  rw [zeroSum_shiftedOdd] at hz
  have hm := mul_le_mul_of_nonneg_left (intervalIntegral_shiftedOdd_sq_le v K)
    (show (0 : ℝ) ≤ D + 1 + 1 by linarith)
  linarith

/-- **RH iff Weil's form on the step packets is bounded below by a multiple of the mass.** -/
theorem riemannHypothesis_iff_packetForm_stepPacket_bddBelow :
    RiemannHypothesis ↔ ∃ D : ℝ, ∀ K : ℕ, 1 ≤ K → ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      -(D * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
        packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ) := by
  constructor
  · intro hRH
    refine ⟨0, fun K _ R hR σ => ?_⟩
    rw [zero_mul, neg_zero]
    exact packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR (le_of_eq (by ring)) σ
  · rintro ⟨D, hD⟩
    refine riemannHypothesis_of_packetForm_stepPacket_ge (abs_nonneg D) fun K hK R hR σ => ?_
    have h := hD K hK R hR σ
    have hs : 0 ≤ ∑ j ∈ range (3 * K * R), σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := mul_le_mul_of_nonneg_right (le_abs_self D) hs
    linarith

/-! ### Two bound states below `−C` -/

/-- The mass of the three vectors of the plane: they live on disjoint blocks, the refinement
keeps the mass of `σ`, the far window has mass `L/M` and the block one `1/L`. -/
theorem sum_probe_sq {R J L M : ℕ} (hR : 1 ≤ R) (hL : 2 ≤ L) (hLM : L * (R + J) ≤ M)
    (σ : ℕ → ℝ) (x₁ x₂ x₃ : ℝ) :
    ∑ b ∈ Ico 1 (M + M), probe R J L M σ x₁ x₂ x₃ b ^ 2 =
      x₁ ^ 2 * ∑ j ∈ range J, σ j ^ 2 + x₂ ^ 2 * ((L : ℝ) / M) + x₃ ^ 2 * (1 / (L : ℝ)) := by
  have hLR : 2 ≤ L * R := le_trans hL (Nat.le_mul_of_pos_right L (by omega))
  have hmul : L * (R + J) = L * R + L * J := Nat.mul_add L R J
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hsq2 : (Real.sqrt L / M) ^ 2 = L / (M : ℝ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hL0.le]
  have hsq3 : (1 / Real.sqrt L) ^ 2 = 1 / (L : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hL0.le]
  -- pointwise, the three pieces do not overlap
  have hpt : ∀ b ∈ Ico 1 (M + M), probe R J L M σ x₁ x₂ x₃ b ^ 2 =
      x₁ ^ 2 * (if b ∈ Ico (L * R) (L * R + L * J) then refineStep L σ (b - L * R) ^ 2 else 0) +
        x₂ ^ 2 * (if b ∈ Ico M (M + M) then (L : ℝ) / (M : ℝ) ^ 2 else 0) +
        x₃ ^ 2 * (if b ∈ Ico 1 2 then 1 / (L : ℝ) else 0) := by
    intro b _
    unfold probe
    by_cases h1 : b ∈ Ico (L * R) (L * R + L * J)
    · have h2 : b ∉ Ico M (M + M) := fun h => by
        rw [Finset.mem_Ico] at h h1
        omega
      have h3 : b ∉ Ico 1 2 := fun h => by
        rw [Finset.mem_Ico] at h h1
        omega
      simp only [if_pos h1, if_neg h2, if_neg h3]
      ring
    · by_cases h2 : b ∈ Ico M (M + M)
      · have h3 : b ∉ Ico 1 2 := fun h => by
          rw [Finset.mem_Ico] at h h2
          omega
        simp only [if_neg h1, if_pos h2, if_neg h3]
        rw [← hsq2]
        ring
      · by_cases h3 : b ∈ Ico 1 2
        · simp only [if_neg h1, if_neg h2, if_pos h3]
          rw [← hsq3]
          ring
        · simp only [if_neg h1, if_neg h2, if_neg h3]
          ring
  have hS₁ : Ico (L * R) (L * R + L * J) ⊆ Ico 1 (M + M) :=
    Finset.Ico_subset_Ico (by omega) (by omega)
  have hS₂ : Ico M (M + M) ⊆ Ico 1 (M + M) := Finset.Ico_subset_Ico (by omega) le_rfl
  have hS₃ : Ico 1 2 ⊆ Ico 1 (M + M) := Finset.Ico_subset_Ico le_rfl (by omega)
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS₁, Finset.inter_eq_right.mpr hS₂,
    Finset.inter_eq_right.mpr hS₃]
  have e1 : ∑ b ∈ Ico (L * R) (L * R + L * J), refineStep L σ (b - L * R) ^ 2 =
      ∑ j ∈ range J, σ j ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    simp only [Nat.add_sub_cancel_left]
    exact sum_refineStep_sq (by omega) J σ
  have e2 : ∑ _b ∈ Ico M (M + M), (L : ℝ) / (M : ℝ) ^ 2 = L / M := by
    rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
    field_simp
  rw [e1, e2, Ico_one_two, Finset.sum_singleton]

/-- The form of the neutral part plus `C` on a step function of the window `(1, 2M]`. -/
theorem sum_fin_neutralWindow_add_eq {M : ℕ} (hM : 1 ≤ M) (Q : ℕ) (C : ℝ) (Ψ : ℕ → ℝ) :
    ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
        Ψ (1 + (i : ℕ)) * Ψ (1 + (j : ℕ)) *
          (neutralWindow Q 1 (M + M - 1) + Matrix.diagonal fun _ => C :
            Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℝ) i j =
      rectSum (neutralBlock Q) (Ico 1 (M + M)) (Ico 1 (M + M)) Ψ Ψ +
        C * ∑ b ∈ Ico 1 (M + M), Ψ b ^ 2 := by
  have hdiag : ∀ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
      Ψ (1 + (i : ℕ)) * Ψ (1 + (j : ℕ)) * (Matrix.diagonal (fun _ => C) i j) =
        C * Ψ (1 + (i : ℕ)) ^ 2 := fun i => by
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [Matrix.diagonal_apply_eq]
    ring
  have hsplit : ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
      Ψ (1 + (i : ℕ)) * Ψ (1 + (j : ℕ)) *
        (neutralWindow Q 1 (M + M - 1) + Matrix.diagonal fun _ => C :
            Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℝ) i j =
      ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
          Ψ (1 + (i : ℕ)) * Ψ (1 + (j : ℕ)) * neutralWindow Q 1 (M + M - 1) i j +
        ∑ i : Fin (M + M - 1), C * Ψ (1 + (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hdiag i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.add_apply]
    ring
  have hmass : ∑ i : Fin (M + M - 1), Ψ (1 + (i : ℕ)) ^ 2 = ∑ b ∈ Ico 1 (M + M), Ψ b ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => Ψ (1 + i) ^ 2) (M + M - 1),
      Finset.sum_Ico_eq_sum_range]
  rw [hsplit, sum_fin_neutralWindow_eq_rectSum hM, ← Finset.mul_sum, hmass]

/-- **A step packet below `−C` times its mass gives two bound states below `−C`**: on the blocks
of a window `(1, 2M]` the neutral part plus `C` has two negative squares. -/
theorem exists_two_le_hermNegIndex_neutralWindow_add {R J Q₀ : ℕ} (hR : 1 ≤ R)
    (hQ₀ : R + J ≤ Q₀ * R) (σ : ℕ → ℝ) (C : ℝ)
    (hneg : 2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) +
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l) +
        C * ∑ j ∈ range J, σ j ^ 2 < 0) :
    ∃ M : ℕ, 1 ≤ M ∧ 2 ≤ hermNegIndex
      ((neutralWindow (M + M) 1 (M + M - 1) + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℂ) := by
  obtain ⟨c₁, hc₁⟩ : ∃ x, x = ∑ j ∈ range J, σ j := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ x, x = ∑ j ∈ range J, σ j * blockDegree (R + j) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ x, x = ∑ j ∈ range J, σ j ^ 2 := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ : ∃ x,
      x = ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l) := ⟨_, rfl⟩
  obtain ⟨nσ, hnσ⟩ : ∃ x, x = n₀ + C * S := ⟨_, rfl⟩
  obtain ⟨n₁, hn₁⟩ : ∃ x, x = neutralBlock 0 1 1 + C := ⟨_, rfl⟩
  have hℓ := blockDegree_one_pos
  obtain ⟨ℓ, hℓdef⟩ : ∃ x, x = blockDegree 1 := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ
  obtain ⟨κ, hκ⟩ : ∃ x, x = c₀ / ℓ := ⟨_, rfl⟩
  have hκℓ : κ * ℓ = c₀ := by rw [hκ]; exact div_mul_cancel₀ c₀ hℓ.ne'
  have hneg' : 2 * c₁ * c₀ + nσ < 0 := by
    rw [hc₁, hc₀, hnσ, hn₀, hS]
    linarith
  -- stage one: the scale `L` of the refinement
  have h33 : Tendsto (fun L : ℕ => n₁ / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat n₁
  have h13 : Tendsto (fun L : ℕ => liftFirst R J L σ) atTop (𝓝 (-(ℓ * c₁))) := by
    rw [hℓdef, hc₁]
    exact tendsto_liftFirst hR J σ
  have hc : ∀ x : ℝ, Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := fun _ => tendsto_const_nhds
  have hA₁ := tendsto_gramA c₁ κ (hc nσ) (hc 0) h33 (hc (-c₀)) h13 (hc (-ℓ))
  have hB₁ := tendsto_gramB c₁ κ (hc 0) h33 (hc (-c₀)) h13 (hc (-ℓ))
  have hC₁ := tendsto_gramC (hc 0) h33 (hc (-ℓ))
  have hAval : gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) = 2 * c₁ * c₀ + nσ := by
    unfold gramA
    ring
  have hBval : gramB c₁ κ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) = 0 := by
    unfold gramB
    linear_combination hκℓ
  have hCval : gramC 0 0 (-ℓ) = -2 * ℓ := by
    unfold gramC
    ring
  have hD₁ := (hA₁.mul hC₁).sub (hB₁.pow 2)
  have hDpos : 0 < gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) * gramC 0 0 (-ℓ) -
      gramB c₁ κ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) ^ 2 := by
    rw [hAval, hBval, hCval]
    nlinarith
  obtain ⟨L, hL2, hAL, hDL⟩ : ∃ L : ℕ, 2 ≤ L ∧
      gramA c₁ κ nσ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) < 0 ∧
      0 < gramA c₁ κ nσ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) * gramC 0 (n₁ / L) (-ℓ) -
        gramB c₁ κ 0 (n₁ / L) (-c₀) (liftFirst R J L σ) (-ℓ) ^ 2 := by
    have h1 := hA₁.eventually (Iio_mem_nhds (show gramA c₁ κ nσ 0 0 (-c₀) (-(ℓ * c₁)) (-ℓ) < 0 by
      rw [hAval]
      exact hneg'))
    have h2 := hD₁.eventually (Ioi_mem_nhds hDpos)
    obtain ⟨L, hL⟩ := ((eventually_ge_atTop 2).and (h1.and h2)).exists
    exact ⟨L, hL.1, hL.2.1, hL.2.2⟩
  have hL1 : 1 ≤ L := by omega
  -- stage two: the far window
  have h22 : Tendsto (fun M : ℕ => (L : ℝ) * n₁ / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h12 : Tendsto (fun M : ℕ => liftFar R J L M σ) atTop (𝓝 (-c₀)) := by
    rw [hc₀]
    exact tendsto_liftFar hR hL1 J σ
  have h23 : Tendsto (fun M : ℕ => farFirst L M) atTop (𝓝 (-ℓ)) := by
    rw [hℓdef]
    exact tendsto_farFirst hL1
  have hA₂ := tendsto_gramA c₁ κ (hc nσ) h22 (hc (n₁ / L)) h12 (hc (liftFirst R J L σ)) h23
  have hB₂ := tendsto_gramB c₁ κ h22 (hc (n₁ / L)) h12 (hc (liftFirst R J L σ)) h23
  have hC₂ := tendsto_gramC h22 (hc (n₁ / L)) h23
  have hD₂ := (hA₂.mul hC₂).sub (hB₂.pow 2)
  obtain ⟨M, hMge, hAM, hDM⟩ := ((eventually_ge_atTop (max 1 (max (L * (R + J)) Q₀))).and
    ((hA₂.eventually (Iio_mem_nhds hAL)).and (hD₂.eventually (Ioi_mem_nhds hDL)))).exists
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hMge
  have hLM : L * (R + J) ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans hMge
  have hQM : Q₀ ≤ M + M := (((le_max_right _ _).trans (le_max_right _ _)).trans hMge).trans
    (Nat.le_add_right M M)
  refine ⟨M, hM1, ?_⟩
  -- the plane spanned by `u₁ − c₁u₂ − κu₃` and `u₂ + u₃`
  refine two_le_hermNegIndex_of_plane _
    (fun i : Fin (M + M - 1) => probe R J L M σ 1 (-c₁) (-κ) (1 + (i : ℕ)))
    (fun i : Fin (M + M - 1) => probe R J L M σ 0 1 1 (1 + (i : ℕ))) fun s t hst => ?_
  have hW : ∀ b, s * probe R J L M σ 1 (-c₁) (-κ) b + t * probe R J L M σ 0 1 1 b =
      probe R J L M σ s (t - s * c₁) (t - s * κ) b := fun b => by
    unfold probe
    ring
  -- adding `C` times the mass shifts the entries `n₁` and `nσ` of the Gram matrix by `C`
  have hgoal : gramA c₁ κ
          (∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q₀ (R + j) (R + l))
          (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L) (liftFar R J L M σ)
          (liftFirst R J L σ) (farFirst L M) * s ^ 2 +
        2 * gramB c₁ κ (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L)
          (liftFar R J L M σ) (liftFirst R J L σ) (farFirst L M) * s * t +
        gramC (L * neutralBlock 0 1 1 / M) (neutralBlock 0 1 1 / L) (farFirst L M) * t ^ 2 +
        C * (s ^ 2 * ∑ j ∈ range J, σ j ^ 2 + (t - s * c₁) ^ 2 * ((L : ℝ) / M) +
          (t - s * κ) ^ 2 * (1 / (L : ℝ))) =
      gramA c₁ κ nσ (L * n₁ / M) (n₁ / L) (liftFar R J L M σ) (liftFirst R J L σ)
          (farFirst L M) * s ^ 2 +
        2 * gramB c₁ κ (L * n₁ / M) (n₁ / L) (liftFar R J L M σ) (liftFirst R J L σ)
          (farFirst L M) * s * t +
        gramC (L * n₁ / M) (n₁ / L) (farFirst L M) * t ^ 2 := by
    rw [hnσ, hn₀, hn₁, hS]
    unfold gramA gramB gramC
    ring
  show ∑ i : Fin (M + M - 1), ∑ j : Fin (M + M - 1),
      (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (i : ℕ)) + t * probe R J L M σ 0 1 1 (1 + (i : ℕ))) *
        (s * probe R J L M σ 1 (-c₁) (-κ) (1 + (j : ℕ)) +
          t * probe R J L M σ 0 1 1 (1 + (j : ℕ))) *
        (neutralWindow (M + M) 1 (M + M - 1) + Matrix.diagonal fun _ => C :
          Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℝ) i j < 0
  simp only [hW]
  rw [sum_fin_neutralWindow_add_eq hM1 (M + M) C, probe_form hR hQ₀ σ hL1 hM1 hLM hQM c₁ κ s t,
    sum_probe_sq hR hL2 hLM σ s (t - s * c₁) (t - s * κ)]
  exact lt_of_eq_of_lt hgoal (quad_neg_of_disc hAM hDM hst)

/-! ### The theorem -/

/-- A uniform lower bound on the margins of the windows `(1, 2M]` forces RH. -/
theorem riemannHypothesis_of_initialWindow_margin_bddBelow {C : ℝ}
    (hC : ∀ M : ℕ, 1 ≤ M →
      hermNegIndex ((neutralWindow (M + M) 1 (M + M - 1) + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℂ) ≤ 1) :
    RiemannHypothesis := by
  by_contra hRH
  rw [riemannHypothesis_iff_packetForm_stepPacket_bddBelow] at hRH
  push Not at hRH
  obtain ⟨K, -, R, hR, σ, hσ⟩ := hRH |C|
  rw [packetForm_stepPacket_eq_sum_blockMatrix hR, sum_blockMatrix_eq_charges_add_neutral] at hσ
  have hs : 0 ≤ ∑ j ∈ range (3 * K * R), σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hCs := mul_le_mul_of_nonneg_right (le_abs_self C) hs
  obtain ⟨M, hM, h2⟩ := exists_two_le_hermNegIndex_neutralWindow_add hR
    (Q₀ := 3 * K + 1) (J := 3 * K * R) (le_of_eq (by ring)) σ C (by linarith)
  have h1 := hC M hM
  omega

/-- **RH iff the margins of the window matrices are bounded below**: iff for some `C` the neutral
part of every window `(R, R + J]` with `R ≤ J`, plus `C`, has at most one negative square. -/
theorem riemannHypothesis_iff_neutralWindow_margin_bddBelow :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ Q R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  constructor
  · intro hRH
    refine ⟨0, fun Q R J hR hRJ hQ => ?_⟩
    have e : (neutralWindow Q R J + Matrix.diagonal fun _ => (0 : ℝ)) = neutralWindow Q R J := by
      rw [Matrix.diagonal_zero, add_zero]
    rw [e]
    exact (hermNegIndex_neutralWindow_eq_one_of_riemannHypothesis hRH hR hRJ hQ).le
  · rintro ⟨C, hC⟩
    exact riemannHypothesis_of_initialWindow_margin_bddBelow fun M hM =>
      hC (M + M) 1 (M + M - 1) le_rfl (by omega) (by omega)

/-- **The windows `(1, 2M]` suffice.** Contacts beyond the ratio of a window do not enter its
matrix (`neutralBlock_eq_of_le`), so these windows are the leading principal minors of one infinite
matrix: RH iff its second eigenvalue is finite. -/
theorem riemannHypothesis_iff_initialWindow_margin_bddBelow :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ M : ℕ, 1 ≤ M →
      hermNegIndex ((neutralWindow (M + M) 1 (M + M - 1) + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin (M + M - 1)) (Fin (M + M - 1)) ℂ) ≤ 1 := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := riemannHypothesis_iff_neutralWindow_margin_bddBelow.mp hRH
    exact ⟨C, fun M hM => hC (M + M) 1 (M + M - 1) le_rfl (by omega) (by omega)⟩
  · rintro ⟨C, hC⟩
    exact riemannHypothesis_of_initialWindow_margin_bddBelow hC

/-! ### The Doob chains -/

/-- Adding a constant to the diagonal does not change the Dirichlet form of the Doob chain. -/
theorem doobEnergy_add_diagonal {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (φ f : Fin n → ℝ) :
    doobEnergy (G + Matrix.diagonal fun _ => C) φ f = doobEnergy G φ f := by
  unfold doobEnergy doobConductance
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij
    ring
  · rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, add_zero]

/-- **RH iff the Poincaré inequality of every Doob chain holds up to a fixed additive loss**: for
some `C`, on every window `(R, R + J]` with `R ≤ J`, the Doob chain at a positive eigenvector
`N φ = λ φ` has `E(f) ≥ (μ − C) Σ φ² f²` on every centred `f`, `μ = −λ` the binding energy. The
loss is free: it forces the sharp inequality `E(f) ≥ μ Σ φ² f²`. -/
theorem riemannHypothesis_iff_forall_doob_poincare_sub :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ Q R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      ∀ φ : Fin J → ℝ, (∀ i, 0 < φ i) → ∀ lam : ℝ, neutralWindow Q R J *ᵥ φ = lam • φ →
        ∀ f : Fin J → ℝ, doobMean φ f = 0 →
          (-lam - C) * doobMass φ f ≤ doobEnergy (neutralWindow Q R J) φ f := by
  -- the matrix `N + C` has the same off-diagonal entries and the eigenvalue `λ + C` at `φ`
  have hshift : ∀ (Q R J : ℕ) (C : ℝ) (φ : Fin J → ℝ) (lam : ℝ),
      neutralWindow Q R J *ᵥ φ = lam • φ →
        (neutralWindow Q R J + Matrix.diagonal fun _ => C) *ᵥ φ = (lam + C) • φ := by
    intro Q R J C φ lam heig
    funext i
    simp only [Matrix.add_mulVec, heig, Pi.add_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hsymm : ∀ (Q R J : ℕ) (C : ℝ) (i j : Fin J),
      (neutralWindow Q R J + Matrix.diagonal fun _ => C : Matrix (Fin J) (Fin J) ℝ) i j =
        (neutralWindow Q R J + Matrix.diagonal fun _ => C : Matrix (Fin J) (Fin J) ℝ) j i :=
      fun Q R J C i j => by
    rw [Matrix.add_apply, Matrix.add_apply, neutralWindow_symm Q R J i j]
    by_cases hij : i = j
    · rw [hij]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  have hoff : ∀ (Q R J : ℕ) (C : ℝ) (i j : Fin J), i ≠ j →
      (neutralWindow Q R J + Matrix.diagonal fun _ => C : Matrix (Fin J) (Fin J) ℝ) i j ≤ 0 :=
      fun Q R J C i j hij => by
    rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, add_zero]
    exact (neutralWindow_neg_of_ne Q R hij).le
  rw [riemannHypothesis_iff_neutralWindow_margin_bddBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun Q R J hR hRJ hQ φ hφ lam heig f hf => ?_⟩
    have h := (hermNegIndex_le_one_iff_poincare (hsymm Q R J C) (hoff Q R J C) hφ
      (hshift Q R J C φ lam heig)).mp (hC Q R J hR hRJ hQ) f hf
    rw [doobEnergy_add_diagonal] at h
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C, fun Q R J hR hRJ hQ => ?_⟩
    obtain ⟨φ, hφ, lam, heig⟩ := exists_groundVector_neutralWindow Q R (hR.trans hRJ)
    refine (hermNegIndex_le_one_iff_poincare (hsymm Q R J C) (hoff Q R J C) hφ
      (hshift Q R J C φ lam heig)).mpr fun f hf => ?_
    rw [doobEnergy_add_diagonal]
    have h := hC Q R J hR hRJ hQ φ hφ lam heig f hf
    linarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
