import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRiemannHypothesisIsExactEventualCombPositivity
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleDecidesTheLimit
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity

/-!
# The ground energy of an aperture is the floor of Weil's form on the windows inside it

A window `(R, R + J]` lies inside the aperture `A` if `log((R + J)/R) < 2A`. Weil's form on its
step packets is the form of its block matrix. For every cutoff `Q ≥ e^{2A}`:

  **`c ≤ E(A)` iff `c Σ σ² ≤ 𝔚(σ)` on the step packets of every window inside the aperture, at
  every block size** (`stepFloor_iff_le_groundEnergy`).

The ground energy of the aperture is the greatest common floor of the block matrices of the
windows inside it (`stepFloor_iff_forall_blockWindow_form_ge`), and below every level above
`E(A)` some window inside the aperture, at some block size, carries a step packet
(`exists_stepPacket_lt_of_groundEnergy_lt`). The step packets of an aperture see its whole
spectrum bottom: no test of the aperture is lost in the passage to the matrices.

The direction from the ground energy to the windows is the transfer from the aperture. The
converse runs through the comb.

* **Block functions** (`eventually_combForm_blockFunction_ge`): a floor `c` on the step packets
  of `(R, R + J]` is, up to any `η > 0`, a floor of Weil's form on the comb `(RB, (R + J)B]` on
  the divisors constant on the blocks, for all large `B`.
* **All divisors** (`combForm_ge_blockMean_add_residual`,
  `eventually_combForm_ge_of_stepPacket_floor`): if `log R` exceeds `C_Q²/η + κ` by a constant
  of `Q`, the form of a divisor is at least the form of its block averages, minus `η` times
  their mass, plus `κ` times the mass of the rest. With `κ = |c|` and the orthogonality of the
  block projection the floor `c − 2η` holds on every divisor of the comb.
* **Samples** (`mul_integral_sq_le_zeroSum_of_eventually`): a `C²` packet in
  `(log 3, log 3 + ℓ)`, sampled at the scale `rB`, lives on the comb of the window
  `(3r, 3r + J]`, `J = ⌈3r(e^ℓ − 1)⌉`, which lies inside the aperture as soon as `2A' < ℓ < 2A`
  and `r` is large. The comb form tends to the sum over the zeros and the mass to `∫ f²`.
* **The closed aperture** (`le_groundEnergy_of_forall_weilFloor`): the floor on the tests of
  every smaller aperture is a floor of `E(A)`, by the continuity of the ground energy.

In terms of the overlap law of Weil's form: for `Q ≥ 2`,

  **`E(A) ≥ 0` iff on the two ends of every window `(R, 2(R + a) + b]` inside the aperture
  Weil's form dominates the form of the couplings in the Green matrix of Weil's form on the
  dyadic middle** (`groundEnergy_nonneg_iff_forall_weilSchur_nonneg`).

An overlap step in the normal form of Weil's form, taken at every block size, is the sign of
the ground energy of the aperture of its windows, no less and no more. For the neutral part
only one direction is known at one aperture: the ground energy is a gap on the charge-free
packets; one bound state of the neutral windows inside an aperture is not known to give the
sign, because the pole plane is not carried by the windows of the aperture.
-/

open Finset Filter Topology Matrix MeasureTheory
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
open GaloisForLFunctions.HodgeTheoryOfAFixedPart (blockIndex blockMean combForm sampleCoord
  crossConstant chebyshev formBilin degTwo)
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (weilQuad)
open _root_.RHTower (SuzukiPositiveAperture ccmRestrictedWeilGroundEnergy)

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Block averages with a residual -/

/-- **A divisor with a block-constant part, with the mass of the rest.** On a window of `J`
complete blocks of `B ≤ N` points and ratio at most `Q`, let `s` be constant on blocks and `z`
have vanishing block sums. If the margin `log(N/2π) − ρ` of the counterterm over the row is at
least `C_Q²/ε + κ`, then `𝔚(s + z) ≥ 𝔚(s) − ε Σ s_n² + κ Σ z_n²`. -/
theorem combForm_blockFunction_add_residual_ge {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (hQ : N + B * J ≤ Q * N) {ε κ : ℝ} (hε : 0 < ε)
    (hμ : crossConstant Q ^ 2 / ε + κ ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * B) + 2 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q))
    (σ z : ℕ → ℝ)
    (hzero : ∀ j : ℕ,
      ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), z n = 0) :
    combForm (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) -
        ε * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 +
        κ * ∑ n ∈ Ioc N (N + B * J), z n ^ 2 ≤
      combForm (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n) + z n) := by
  have hN : 0 < N := lt_of_lt_of_le hB hBN
  have hC := HodgeTheoryOfAFixedPart.crossConstant_pos Q
  have hz0 : 0 ≤ ∑ n ∈ Ioc N (N + B * J), z n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- coercivity on the divisors with vanishing block sums
  have hco : (crossConstant Q ^ 2 / ε + κ) * ∑ n ∈ Ioc N (N + B * J), z n ^ 2 ≤
      combForm (Ioc N (N + B * J)) z := by
    have hpair := HodgeTheoryOfAFixedPart.combPairing_le_of_blockSum_eq_zero hN hB hQ
      (Finset.Subset.refl _) z hzero
    rw [HodgeTheoryOfAFixedPart.combForm,
      HodgeTheoryOfAFixedPart.degTwo_eq_zero_of_blockSum_eq_zero N B _ z hzero,
      mul_zero, mul_zero, zero_sub]
    nlinarith only [hpair, mul_le_mul_of_nonneg_right hμ hz0]
  -- the cross term with the weights `ε/C` and `C/ε`
  have hcross := HodgeTheoryOfAFixedPart.two_mul_abs_formBilin_le hB hBN hQ σ z hzero
    (p := ε / crossConstant Q) (q := crossConstant Q / ε) (div_pos hε hC)
    (by rw [div_mul_div_comm, mul_comm ε, div_self (mul_pos hC hε).ne'])
  rw [HodgeTheoryOfAFixedPart.cross_weights hC.ne'] at hcross
  rw [HodgeTheoryOfAFixedPart.combForm_add (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z]
  have hneg := neg_abs_le (formBilin (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z)
  linarith only [hco, hcross, hneg]

/-- **Weil's form of a divisor is at least the form of its block averages, minus `ε` times their
mass, plus `κ` times the mass of the rest**, as soon as the margin `log(N/2π) − ρ` is at least
`C_Q²/ε + κ`. -/
theorem combForm_ge_blockMean_add_residual {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (hQ : N + B * J ≤ Q * N) {ε κ : ℝ} (hε : 0 < ε)
    (hμ : crossConstant Q ^ 2 / ε + κ ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * B) + 2 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q))
    (c : ℕ → ℝ) :
    combForm (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) -
        ε * ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 +
        κ * ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 ≤
      combForm (Ioc N (N + B * J)) c := by
  have h : combForm (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) -
      ε * ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 +
      κ * ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 ≤
      combForm (Ioc N (N + B * J))
        (fun n => blockMean N B J c (blockIndex N B n) +
          (c n - blockMean N B J c (blockIndex N B n))) :=
    combForm_blockFunction_add_residual_ge hB hBN hQ hε hμ (blockMean N B J c)
      (fun n => c n - blockMean N B J c (blockIndex N B n))
      (HodgeTheoryOfAFixedPart.sum_filter_sub_blockMean hB N J c)
  have he : (fun n => blockMean N B J c (blockIndex N B n) +
      (c n - blockMean N B J c (blockIndex N B n))) = c := by
    funext n
    ring
  rwa [he] at h

/-! ### From the step packets of a window to its comb -/

/-- **A floor on the step packets of a window is a floor on the block functions of its comb**, at
all large block sizes and up to any `η > 0`. -/
theorem eventually_combForm_blockFunction_ge {R J Q : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    {c η : ℝ} (hη : 0 < η)
    (hc : ∀ σ : ℕ → ℝ, c * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ)) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      (c - η) * ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) := by
  filter_upwards [HodgeTheoryOfAFixedPart.eventually_packetForm_stepPacket_le_combForm hR hQ hη,
    eventually_ge_atTop 1] with B hB hB1 σ
  have h := hB σ
  rw [sum_blockFunction_sq (by omega) σ] at h ⊢
  have hm := mul_le_mul_of_nonneg_left (hc σ) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  nlinarith only [h, hm]

/-- **A floor on the step packets of a window is a floor on every divisor of its comb**, at all
large block sizes and up to `2η`, once the window starts after `R` blocks with
`log R ≥ C_Q²/η + |c| + 3 + Q/4 + 2ψ(Q) + log 4π`. The floor of the block averages is the floor
of the step packets; the rest of the divisor has vanishing block sums and is paid by the
counterterm. -/
theorem eventually_combForm_ge_of_stepPacket_floor {R J Q : ℕ} (hR : 1 ≤ R)
    (hQ : R + J ≤ Q * R) {c η : ℝ} (hη : 0 < η)
    (hRlarge : crossConstant Q ^ 2 / η + |c| ≤
      Real.log R - (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)))
    (hc : ∀ σ : ℕ → ℝ, c * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ)) :
    ∀ᶠ B : ℕ in atTop, ∀ d : ℕ → ℝ,
      (c - 2 * η) * ∑ n ∈ Ioc (R * B) (R * B + B * J), d n ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * J)) d := by
  filter_upwards [eventually_combForm_blockFunction_ge hR hQ hη hc, eventually_ge_atTop 1]
    with B hB hB1 d
  have hBpos : 0 < B := by omega
  have hBN : B ≤ R * B := Nat.le_mul_of_pos_left B hR
  have hQ' : R * B + B * J ≤ Q * (R * B) := by
    have h1 : R * B + B * J = (R + J) * B := by ring
    have h2 : Q * (R * B) = Q * R * B := by ring
    rw [h1, h2]
    exact Nat.mul_le_mul_right B hQ
  have hdiv : R * B / R = B := Nat.mul_div_cancel_left B hR
  have hmargin := HodgeTheoryOfAFixedPart.log_sub_row_ge (N := R * B) (M := B * J) (Q := Q)
    (R := R) hR (Nat.le_mul_of_pos_right R hBpos) hQ'
  rw [hdiv] at hmargin
  have h1 := combForm_ge_blockMean_add_residual hBpos hBN hQ' hη (hRlarge.trans hmargin) d
  have h2 := hB (blockMean (R * B) B J d)
  have hres : 0 ≤ ∑ n ∈ Ioc (R * B) (R * B + B * J),
      (d n - blockMean (R * B) B J d (blockIndex (R * B) B n)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcz := mul_nonneg (show (0 : ℝ) ≤ |c| - c + 2 * η by linarith [le_abs_self c]) hres
  rw [HodgeTheoryOfAFixedPart.sum_sq_eq_blockMean_add_residual hBpos (R * B) J d]
  linarith only [h1, h2, hcz]

/-! ### From the comb to the smooth packets inside the window -/

/-- A square that vanishes off `[0, b]` has its integral on `[0, b]`. -/
theorem intervalIntegral_sq_eq_integral {f : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h0 : ∀ u, u ≤ 0 → f u = 0) (h1 : ∀ u, b < u → f u = 0) :
    ∫ u in (0 : ℝ)..b, f u ^ 2 = ∫ u, f u ^ 2 := by
  rw [intervalIntegral.integral_of_le hb]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with h | h
  · rw [h0 u h]
    ring
  · rw [h1 u h]
    ring

/-- The window `(3rB, (3r + J)B]` lies in the comb `(rB, (1 + 3K)rB]` of the samples. -/
theorem window_subset_sampleComb {K r J : ℕ} (hJK : 3 * r + J ≤ K * r) (B : ℕ) :
    Ioc (3 * r * B) (3 * r * B + B * J) ⊆ Ioc (r * B) (r * B + 3 * K * (r * B)) := by
  refine Finset.Ioc_subset_Ioc (Nat.mul_le_mul_right B (by omega)) ?_
  have h1 : 3 * r * B + B * J = (3 * r + J) * B := by ring
  have h2 : (3 * r + J) * B ≤ K * r * B := Nat.mul_le_mul_right B hJK
  have h3 : K * r * B ≤ r * B + 3 * K * (r * B) := by
    have h4 : K * r * B = K * (r * B) := by ring
    have h5 : K * (r * B) ≤ 3 * K * (r * B) := Nat.mul_le_mul_right (r * B) (by omega)
    rw [h4]
    exact h5.trans (Nat.le_add_left _ _)
  rw [h1]
  exact h2.trans h3

/-- The samples at the scale `rB` of a packet between `log 3` and `log((3r + J)/r)` vanish off
the window `(3rB, (3r + J)B]`. -/
theorem sampleCoord_eq_zero_off_window {f : ℝ → ℝ} {r J B : ℕ} (hr : 1 ≤ r) (hB : 1 ≤ B)
    (hlow : ∀ u, u ≤ Real.log 3 → f u = 0)
    (hhigh : ∀ u, Real.log (((3 * r + J : ℕ) : ℝ) / r) ≤ u → f u = 0) {n : ℕ}
    (hn : r * B < n) (hnW : n ∉ Ioc (3 * r * B) (3 * r * B + B * J)) :
    sampleCoord f (r * B) n = 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hratio0 : (0 : ℝ) < ((3 * r + J : ℕ) : ℝ) / r :=
    div_pos (by exact_mod_cast (by omega : 0 < 3 * r + J)) hr'
  have hN0 : (0 : ℝ) < ((r * B : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hr hB
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (by omega : 0 < n)
  have hval : degreeSample f (r * B) n = 0 := by
    unfold degreeSample
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hnW
    rcases hnW with h1 | h1
    · refine hlow _ (Real.log_le_log (div_pos hn0 hN0) ?_)
      rw [div_le_iff₀ hN0]
      have h2 : (n : ℝ) ≤ ((3 * r * B : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2 ⊢
      linarith
    · refine hhigh _ (Real.log_le_log hratio0 ?_)
      rw [div_le_div_iff₀ hr' hN0]
      have h2 : ((3 * r * B + B * J : ℕ) : ℝ) ≤ n := by exact_mod_cast h1.le
      push_cast at h2 ⊢
      nlinarith only [mul_le_mul_of_nonneg_left h2 hr'.le]
  unfold sampleCoord
  rw [hval, zero_div]

/-- **A floor on the combs of a window is a floor of the sum over the zeros on the smooth packets
inside it.** A `C²` packet between `log 3` and `log((3r + J)/r)`, sampled at the scale `rB`, lives
on the comb of the window `(3r, 3r + J]` of block size `B`; as `B → ∞` Weil's form on the samples
tends to the sum over the zeros and their mass to `∫ f²`. -/
theorem mul_integral_sq_le_zeroSum_of_eventually {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K r J : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hJK : 3 * r + J ≤ K * r) (hlow : ∀ u, u ≤ Real.log 3 → f u = 0)
    (hhigh : ∀ u, Real.log (((3 * r + J : ℕ) : ℝ) / r) ≤ u → f u = 0) {γ : ℝ}
    (h : ∀ᶠ B : ℕ in atTop, ∀ d : ℕ → ℝ,
      γ * ∑ n ∈ Ioc (3 * r * B) (3 * r * B + B * J), d n ^ 2 ≤
        combForm (Ioc (3 * r * B) (3 * r * B + B * J)) d) :
    γ * (∫ u, f u ^ 2) ≤ zeroSum f := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hratio0 : (0 : ℝ) < ((3 * r + J : ℕ) : ℝ) / r :=
    div_pos (by exact_mod_cast (by omega : 0 < 3 * r + J)) hr'
  have hratio : ((3 * r + J : ℕ) : ℝ) / r ≤ K := by
    rw [div_le_iff₀ hr']
    exact_mod_cast hJK
  -- the packet lives between `log 3` and `log K`
  have hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0 := by
    rintro u (hu | hu)
    · exact hlow u hu
    · exact hhigh u ((Real.log_le_log hratio0 hratio).trans hu)
  have htend : Tendsto (fun B : ℕ => r * B) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_mul_of_pos_left B hr) tendsto_id
  have hZ := (HodgeTheoryOfAFixedPart.tendsto_combForm_sample hf hfc hK hsupp).comp htend
  have hI := ((HodgeTheoryOfAFixedPart.tendsto_sum_sq_sampleCoord hf.continuous hK).comp
    htend).const_mul γ
  have hint : ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 = ∫ u, f u ^ 2 := by
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hK3 : (K : ℝ) ≤ 1 + ((3 * K : ℕ) : ℝ) := by
      push_cast
      linarith
    exact intervalIntegral_sq_eq_integral (Real.log_nonneg (by linarith))
      (fun u hu => hlow u (hu.trans h3.le))
      (fun u hu => hsupp u (Or.inr ((Real.log_le_log hK' hK3).trans hu.le)))
  rw [hint] at hI
  refine le_of_tendsto_of_tendsto hI hZ ?_
  filter_upwards [h, eventually_ge_atTop 1] with B hB hB1
  show γ * ∑ n ∈ Ioc (r * B) (r * B + 3 * K * (r * B)), sampleCoord f (r * B) n ^ 2 ≤
    combForm (Ioc (r * B) (r * B + 3 * K * (r * B))) (sampleCoord f (r * B))
  have hWS := window_subset_sampleComb hJK B
  have h0 : ∀ n ∈ Ioc (r * B) (r * B + 3 * K * (r * B)),
      n ∉ Ioc (3 * r * B) (3 * r * B + B * J) → sampleCoord f (r * B) n = 0 :=
    fun n hn hnW =>
      sampleCoord_eq_zero_off_window hr hB1 hlow hhigh (Finset.mem_Ioc.mp hn).1 hnW
  have hmass : ∑ n ∈ Ioc (r * B) (r * B + 3 * K * (r * B)), sampleCoord f (r * B) n ^ 2 =
      ∑ n ∈ Ioc (3 * r * B) (3 * r * B + B * J), sampleCoord f (r * B) n ^ 2 :=
    (Finset.sum_subset hWS fun n hn hnW => by rw [h0 n hn hnW]; ring).symm
  rw [combForm_of_subset hWS h0, hmass]
  exact hB _

/-! ### The floor of the step packets of an aperture -/

/-- Weil's form has the floor `c` on the step packets of the windows inside the aperture `A`, at
every block size. -/
def StepFloor (Q : ℕ) (A c : ℝ) : Prop :=
  ∀ R J : ℕ, 1 ≤ R → Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A → ∀ σ : ℕ → ℝ,
    c * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ)

/-- A window inside the aperture `A` has ratio less than every cutoff `Q ≥ e^{2A}`. -/
theorem window_lt_of_log_lt {R J Q : ℕ} (hR : 1 ≤ R) {A : ℝ}
    (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A) (hQ : Real.exp (2 * A) ≤ Q) :
    R + J < Q * R := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have h1 : ((R + J : ℕ) : ℝ) < Real.exp (2 * A + Real.log R) :=
    (Real.log_lt_iff_lt_exp hpos).mp (by linarith)
  rw [Real.exp_add, Real.exp_log hR'] at h1
  have h2 : ((R + J : ℕ) : ℝ) < ((Q * R : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact h1.trans_le (mul_le_mul_of_nonneg_right hQ hR'.le)
  exact_mod_cast h2

/-- **A window for a test.** For `0 ≤ ℓ < 2A` and every `T`, some window `(3r, 3r + J]` inside
the aperture `A` has `r ≥ e^T` and covers `(log 3, log 3 + ℓ)` at the scale `r`. -/
theorem exists_window_inside_aperture {A ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ < 2 * A) (T : ℝ) :
    ∃ r J : ℕ, 1 ≤ r ∧ Real.exp T ≤ r ∧
      Real.log ((3 * r + J : ℕ) : ℝ) - Real.log ((3 * r : ℕ) : ℝ) < 2 * A ∧
      Real.log 3 + ℓ ≤ Real.log (((3 * r + J : ℕ) : ℝ) / r) := by
  have hgap : 0 < Real.exp (2 * A) - Real.exp ℓ := sub_pos.mpr (Real.exp_lt_exp.mpr hℓ)
  have hexp : 0 ≤ Real.exp ℓ - 1 := by linarith [Real.add_one_le_exp ℓ]
  obtain ⟨r, hr1, hrT, hrgap⟩ : ∃ r : ℕ, 1 ≤ r ∧ Real.exp T ≤ r ∧
      1 / (Real.exp (2 * A) - Real.exp ℓ) ≤ r := by
    refine ⟨⌈max (Real.exp T) (1 / (Real.exp (2 * A) - Real.exp ℓ))⌉₊, ?_, ?_, ?_⟩
    · exact Nat.ceil_pos.mpr (lt_max_of_lt_left (Real.exp_pos T))
    · exact (le_max_left _ _).trans (Nat.le_ceil _)
    · exact (le_max_right _ _).trans (Nat.le_ceil _)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈3 * (r : ℝ) * (Real.exp ℓ - 1)⌉₊ := ⟨_, rfl⟩
  have hJlow : 3 * (r : ℝ) * (Real.exp ℓ - 1) ≤ J := by
    rw [hJ]
    exact Nat.le_ceil _
  have hJup : (J : ℝ) < 3 * (r : ℝ) * (Real.exp ℓ - 1) + 1 := by
    rw [hJ]
    exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) hexp)
  have hrg : 1 ≤ (r : ℝ) * (Real.exp (2 * A) - Real.exp ℓ) := by
    have h1 := mul_le_mul_of_nonneg_right hrgap hgap.le
    rwa [one_div, inv_mul_cancel₀ hgap.ne'] at h1
  have h3r : (0 : ℝ) < ((3 * r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 3 * r)
  have hwinR : ((3 * r + J : ℕ) : ℝ) < Real.exp (2 * A) * ((3 * r : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hJup, hrg]
  refine ⟨r, J, hr1, hrT, ?_, ?_⟩
  · have hpos : (0 : ℝ) < ((3 * r + J : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 3 * r + J)
    have h1 := Real.log_lt_log hpos hwinR
    rw [Real.log_mul (Real.exp_pos _).ne' h3r.ne', Real.log_exp] at h1
    linarith
  · rw [← Real.log_exp ℓ, ← Real.log_mul (by norm_num) (Real.exp_pos ℓ).ne']
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hr']
    push_cast
    nlinarith only [hJlow]

/-- **The step packets of the windows inside an aperture reach every test of a smaller
aperture.** A floor of Weil's form on the step packets of the windows inside `A`, at every block
size, is a floor on the `C²` tests of every aperture `A' < A`. -/
theorem WeilFloor.of_stepFloor {Q : ℕ} {A c : ℝ} (hQ : Real.exp (2 * A) ≤ Q)
    (h : StepFloor Q A c) {A' : ℝ} (hA' : 0 < A') (hA : A' < A) : WeilFloor A' c := by
  intro F hF hs
  have hFz : ∀ x, A' < |x| → F x = 0 := fun x hx => eq_zero_of_abs_gt_of_tsupport_subset hs hx
  have hFc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport F).trans hs)
  have hQ1 : 1 ≤ Q := by
    have h1 : (0 : ℝ) < Q := (Real.exp_pos _).trans_le hQ
    exact_mod_cast h1
  -- the test moved to `(log 3, log 3 + ℓ)`, `2A' < ℓ < 2A`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = A' + A := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = Real.log 3 + ℓ / 2 := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun u => F (u - τ) := ⟨_, rfl⟩
  have hfu : ∀ u, f u = F (u - τ) := fun u => by rw [hfdef]
  have hf : ContDiff ℝ 2 f := by
    rw [hfdef]
    exact hF.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f := by
    rw [hfdef]
    exact hFc.comp_homeomorph (Homeomorph.subRight τ)
  have hlow : ∀ u, u ≤ Real.log 3 → f u = 0 := fun u hu => by
    rw [hfu]
    exact hFz _ (lt_of_lt_of_le (by linarith) (neg_le_abs (u - τ)))
  have hhigh' : ∀ u, Real.log 3 + ℓ ≤ u → f u = 0 := fun u hu => by
    rw [hfu]
    exact hFz _ (lt_of_lt_of_le (by linarith) (le_abs_self (u - τ)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ u, f u ^ 2 := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun u => sq_nonneg _
  -- the floor up to `2η`, on a window that starts after `3r` blocks
  have key : ∀ η : ℝ, 0 < η → (c - 2 * η) * I ≤ zeroSum f := by
    intro η hη
    obtain ⟨r, J, hr1, hrT, hwin, hcover⟩ := exists_window_inside_aperture (A := A) (ℓ := ℓ)
      (by linarith) (by linarith) (crossConstant Q ^ 2 / η + |c| +
        (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)))
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
    have hQwin : 3 * r + J ≤ Q * (3 * r) := (window_lt_of_log_lt (by omega) hwin hQ).le
    have hJK : 3 * r + J ≤ 3 * Q * r := hQwin.trans (le_of_eq (by ring))
    -- the packet ends before the end of the window
    have hhigh : ∀ u, Real.log (((3 * r + J : ℕ) : ℝ) / r) ≤ u → f u = 0 :=
      fun u hu => hhigh' u (hcover.trans hu)
    have hRlarge : crossConstant Q ^ 2 / η + |c| ≤ Real.log ((3 * r : ℕ) : ℝ) -
        (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)) := by
      have h1 := (Real.le_log_iff_exp_le hr').mpr hrT
      have h2 : Real.log r ≤ Real.log ((3 * r : ℕ) : ℝ) :=
        Real.log_le_log hr' (by push_cast; linarith)
      linarith
    have hev := eventually_combForm_ge_of_stepPacket_floor (R := 3 * r) (J := J) (by omega)
      hQwin hη hRlarge (h (3 * r) J (by omega) hwin)
    rw [hI]
    exact mul_integral_sq_le_zeroSum_of_eventually hf hfc (K := 3 * Q) (by omega) hr1 hJK hlow
      hhigh hev
  -- `η → 0`
  have hfin : c * I ≤ zeroSum f := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hI1 : (0 : ℝ) < I + 1 := by linarith
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (I + 1)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have h2 : 2 * η * I ≤ ε := by
      have h3 : 2 * η * I = ε * (I / (I + 1)) := by
        rw [hηdef]
        field_simp
      rw [h3]
      exact mul_le_of_le_one_right hε.le ((div_le_one hI1).mpr (by linarith))
    linarith [key η hη]
  -- back to the test
  have hZ : zeroSum f = weilQuad F := by
    have h1 : zeroSum f = weilQuad f := by
      rw [ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hf hfc]
      rfl
    rw [h1, hfdef]
    exact SpacingScaleHarmonicAnalysis.weilQuad_comp_sub F τ
  have hmass : I = ∫ x, F x ^ 2 := by
    rw [hI]
    simp only [hfu]
    exact integral_sub_right_eq_self (fun u => F u ^ 2) τ
  rw [← hmass, ← hZ]
  exact hfin

/-! ### The closed aperture -/

/-- Apertures that increase to `A` from inside. -/
def innerAperture (A : SuzukiPositiveAperture) (n : ℕ) : SuzukiPositiveAperture :=
  ⟨A.1 * (1 - 1 / 2 * (1 / ((n : ℝ) + 1))), mul_pos A.2 (by
    have h : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith)⟩

theorem innerAperture_lt (A : SuzukiPositiveAperture) (n : ℕ) : (innerAperture A n).1 < A.1 := by
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h2 := mul_pos A.2 h1
  show A.1 * (1 - 1 / 2 * (1 / ((n : ℝ) + 1))) < A.1
  nlinarith only [h2]

theorem tendsto_innerAperture (A : SuzukiPositiveAperture) :
    Tendsto (innerAperture A) atTop (𝓝 A) := by
  rw [tendsto_subtype_rng]
  have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).const_mul A.1
  rw [mul_zero, sub_zero, mul_one] at h2
  exact h2

/-- **A floor on the tests of every smaller aperture is a floor of the ground energy**: the
ground energy is continuous in the aperture. -/
theorem le_groundEnergy_of_forall_weilFloor {A : SuzukiPositiveAperture} {c : ℝ}
    (h : ∀ A' : ℝ, 0 < A' → A' < A.1 → WeilFloor A' c) :
    c ≤ ccmRestrictedWeilGroundEnergy A :=
  ge_of_tendsto'
    ((_root_.RHTower.continuous_ccmRestrictedWeilGroundEnergy.tendsto A).comp
      (tendsto_innerAperture A))
    fun n => WeilFloor.le_groundEnergy (h _ (innerAperture A n).2 (innerAperture_lt A n))

/-! ### The dictionary at one aperture -/

/-- **A floor on the step packets of the windows inside an aperture is a floor of its ground
energy.** -/
theorem StepFloor.le_groundEnergy {Q : ℕ} {A : SuzukiPositiveAperture} {c : ℝ}
    (hQ : Real.exp (2 * A.1) ≤ Q) (h : StepFloor Q A.1 c) :
    c ≤ ccmRestrictedWeilGroundEnergy A :=
  le_groundEnergy_of_forall_weilFloor fun _ hA' hA => WeilFloor.of_stepFloor hQ h hA' hA

/-- The ground energy of an aperture is a floor on the step packets of the windows inside it. -/
theorem stepFloor_of_le_groundEnergy {Q : ℕ} {A : SuzukiPositiveAperture} {c : ℝ}
    (hQ : Real.exp (2 * A.1) ≤ Q) (hc : c ≤ ccmRestrictedWeilGroundEnergy A) :
    StepFloor Q A.1 c := by
  intro R J hR hwin σ
  have hlt : R + J < (Q + 1) * R := by
    have h1 := window_lt_of_log_lt hR hwin hQ
    rw [Nat.add_mul, one_mul]
    omega
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans
    (groundEnergy_mul_le_packetForm_stepPacket hR hwin hlt σ)

/-- **The ground energy of an aperture is the greatest floor of Weil's form on the step packets
of the windows inside it**, at every block size and for every cutoff `Q ≥ e^{2A}`. -/
theorem stepFloor_iff_le_groundEnergy {Q : ℕ} {A : SuzukiPositiveAperture}
    (hQ : Real.exp (2 * A.1) ≤ Q) (c : ℝ) :
    StepFloor Q A.1 c ↔ c ≤ ccmRestrictedWeilGroundEnergy A :=
  ⟨StepFloor.le_groundEnergy hQ, stepFloor_of_le_groundEnergy hQ⟩

/-- **Below every level above the ground energy some window inside the aperture carries a step
packet.** -/
theorem exists_stepPacket_lt_of_groundEnergy_lt {Q : ℕ} {A : SuzukiPositiveAperture}
    (hQ : Real.exp (2 * A.1) ≤ Q) {c : ℝ} (hc : ccmRestrictedWeilGroundEnergy A < c) :
    ∃ R J : ℕ, 1 ≤ R ∧ Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1 ∧
      ∃ σ : ℕ → ℝ, packetForm Q (stepPacket R J σ) < c * ∑ j ∈ range J, σ j ^ 2 := by
  by_contra hne
  refine absurd (StepFloor.le_groundEnergy hQ fun R J hR hwin σ => ?_) (not_le.mpr hc)
  by_contra hlt
  exact hne ⟨R, J, hR, hwin, σ, not_le.mp hlt⟩

/-- The floor of the step packets is the common floor of the block matrices of the windows
inside the aperture. -/
theorem stepFloor_iff_forall_blockWindow_form_ge (Q : ℕ) (A c : ℝ) :
    StepFloor Q A c ↔
      ∀ R J : ℕ, 1 ≤ R → Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A →
        ∀ x : Fin J → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (blockWindow Q R J *ᵥ x) := by
  constructor
  · intro h R J hR hwin x
    have h1 := h R J hR hwin (extendFin x)
    rw [packetForm_stepPacket_eq_blockWindow_form hR,
      ← dotProduct_self_eq_sum_range_extendFin] at h1
    have hx : (fun i : Fin J => extendFin x i) = x := funext fun i => extendFin_coe x i
    rwa [hx] at h1
  · intro h R J hR hwin σ
    have h1 := h R J hR hwin (fun i : Fin J => σ i)
    have hm : (fun i : Fin J => σ i) ⬝ᵥ (fun i : Fin J => σ i) = ∑ j ∈ range J, σ j ^ 2 := by
      rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun j => σ j ^ 2) J]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [packetForm_stepPacket_eq_blockWindow_form hR]
    rwa [hm] at h1

/-- **The ground energy of an aperture is the least eigenvalue of the block matrices of the
windows inside it**: `c ≤ E(A)` iff `c` is a floor of every such matrix, at every block size. -/
theorem le_groundEnergy_iff_forall_blockWindow_form_ge {Q : ℕ} {A : SuzukiPositiveAperture}
    (hQ : Real.exp (2 * A.1) ≤ Q) (c : ℝ) :
    c ≤ ccmRestrictedWeilGroundEnergy A ↔
      ∀ R J : ℕ, 1 ≤ R → Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1 →
        ∀ x : Fin J → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (blockWindow Q R J *ᵥ x) := by
  rw [← stepFloor_iff_le_groundEnergy hQ, stepFloor_iff_forall_blockWindow_form_ge]

/-! ### The overlap law of Weil's form at one aperture -/

/-- **The overlap law of Weil's form at one aperture is the sign of its ground energy.** For a
cutoff `Q ≥ max(2, e^{2A})`: `E(A) ≥ 0` iff on the two ends of every window `(R, 2(R + a) + b]`
inside the aperture, at every block size, Weil's form dominates the form of the couplings in the
Green matrix of Weil's form on the dyadic middle. Windows shorter than their left end are
positive without a hypothesis. -/
theorem groundEnergy_nonneg_iff_forall_weilSchur_nonneg {Q : ℕ} (hQ2 : 2 ≤ Q)
    {A : SuzukiPositiveAperture} (hQ : Real.exp (2 * A.1) ≤ Q) :
    0 ≤ ccmRestrictedWeilGroundEnergy A ↔
      ∀ R a b : ℕ, 1 ≤ R →
        Real.log ((R + (a + (R + a) + b) : ℕ) : ℝ) - Real.log R < 2 * A.1 →
        ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (weilSchur Q R a b *ᵥ e) := by
  rw [le_groundEnergy_iff_forall_blockWindow_form_ge hQ]
  constructor
  · intro h R a b hR hwin
    refine (forall_blockWindow_form_nonneg_iff_weilSchur Q R a b (by omega)).mp fun x => ?_
    have h1 := h R (a + (R + a) + b) hR hwin x
    rwa [zero_mul] at h1
  · intro h R J hR hwin x
    rw [zero_mul]
    by_cases hJ : R ≤ J
    · -- a window with a dyadic middle and an empty left end
      obtain ⟨b, rfl⟩ : ∃ b, J = 0 + (R + 0) + b := ⟨J - R, by omega⟩
      exact (forall_blockWindow_form_nonneg_iff_weilSchur Q R 0 b (by omega)).mpr
        (h R 0 b hR hwin) x
    · -- a window shorter than its left end
      have h1 := packetForm_stepPacket_ge_of_short hR (by omega : 50 * J ≤ 53 * R) hQ2
        (extendFin x)
      rw [packetForm_stepPacket_eq_blockWindow_form hR] at h1
      have hx : (fun i : Fin J => extendFin x i) = x := funext fun i => extendFin_coe x i
      rw [hx] at h1
      exact (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans h1

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
