import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.BezoutValuationIncidence.CoherentPrimeBlocksAndTheTypeIIWindowNoGo
import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleParityBlindnessOfThePronicGram
import GaloisForLFunctions.BezoutValuationIncidence.ResidueDiscrepancyIsTheExactCrossScaleLoss
import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheCrossScaleFunctional
import GaloisForLFunctions.BezoutValuationIncidence.SmoothLargeScaleRowsOfEveryOrder
import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeRowPassesTheCoherentBlockObstruction

/-!
# The Exact Floor of the Pronic Gram Reading and Its Faithful Completion

In `BezoutValuationIncidence`, cross-scale dispersion between a small-modulus prime row at scale `P`
and a large-scale row or pronic window at scale `X` (or `Q`) is measured in the exponent unit

`θ = 2 log P / log X ∈ [0, 2]`.

The receiver requires control up to the balanced scale `X ≍ P`, where `θ = 2`, whereas the trivial
quadratic horizon `X ≍ P²` corresponds to `θ = 1`. This module wires the cross-scale exponent unit `θ`
into the resolution-limit calculus of `TheResolutionLimitOfAReading` and establishes the complete
quantitative structure of the pronic Gram face:

1. **Calibration of the cross-scale exponent unit (`crossScaleExponent`).**
   `crossScaleExponent P X = 2 log P / log X` takes the value `2` at the linear receiver scale `X = P`,
   `1` at the quadratic Type-II horizon `X = P²`, `2 / α` at any power horizon `X = P^α`, and
   `2K / (K + 1)` at the `K`-kernel Euler-Maclaurin smoothness horizon `X = P^{(K+1)/K}`.

2. **The exact limit `2` of the sign-blind Type-II pronic Gram reading.**
   Under the sign-blind Type-II reading `typeIIGramReading`, which records the prime block `B`, the
   scale parameters `(p₀, J₀)`, and the coefficient magnitudes `|a_p|` (hence the diagonal `ℓ²` budget)
   without inter-prime phase signs, the coherent prime block `primeBlockPacket B` lies in the shadow of
   a dispersed datum with exponent `0`. Consequently, the resolution limit of `typeIIGramReading` in the
   exponent unit `θ ∈ [0, 2]` is **exactly `2`**, its resolution floor is **exactly `0`**, its
   resolution interval is **`Set.Icc 0 2`**, and no exponent bound `β < 2` is certified. Combining this with
   `exists_primeBlock_typeII_window_loss` produces an explicit prime-block witness at the resolution
   limit `2` whose pronic window energy is at least `(|B| / 2304) |B|` times the window pronic mass.

3. **The exact limit `2` of the rank-two readout reading.**
   Under the rank-two readout reading `rankTwoReadoutReading N d = (R(d.c'), H(d.c'))`, any readout-free
   barrier row `c'` (`R(c') = H(c') = 0`) lies in the shadow of the zero row. Hence the resolution
   limit of the readout reading in `θ ∈ [0, 2]` is **exactly `2`** and its resolution floor is **`0`**,
   realised arithmetically by the three-window coherent/anti-coherent barrier of
   `exists_readout_free_barrier`.

4. **The exact smoothness resolution ladder (`2K / (K + 1)` and `2 / (K + 1)`).**
   Refining the Gram reading by `L`-fold difference smoothness (`smoothnessNorm N L`, cancelling
   `K = L + 1` Euler-Maclaurin kernels) certifies the cross-scale exponent
   `smoothCertifiedExponent K = 2K / (K + 1)` and lowers the resolution limit of the unresolved
   exponent deficit from `2` along the strictly decreasing harmonic sequence
   `smoothUnresolvedLimit K = 2 / (K + 1) → 0` (`2` at `K = 0`, `1` at `K = 1`, `2/3` at the
   sharp-cutoff threshold `K = 2` where `θ = 4/3`, and `0` in the limit `K → ∞`).

5. **Faithful completion on the single-modulus Gram face and the arithmetic prime-row bypass.**
   The weighted residue-mass reading `residueMass N` is **exact and faithful** (`Faithful`) for the
   second-order Bernoulli cross-scale functional `bernoulliCrossScaleMain N c`, collapsing its
   resolution limit and floor to the exact value of the functional and bounding the shadow diameter of
   `rowBilinear N c` by the cubic remainder. Refining to the single-modulus `kernelStatistic N`
   collapses the shadow diameter to the fourth-order tail. Finally, while the worst-case Type-II shadow
   has resolution limit `2`, the actual arithmetic row `centredPrimeRow A H K` bypasses the coherent
   block obstruction unconditionally across the entire range `7/6 < θ < 2`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

noncomputable section
set_option autoImplicit false

/-! ## §1. Calibration of the cross-scale exponent unit `θ = 2 log P / log X` -/

/-- The cross-scale dispersion exponent `θ = 2 log P / log X` measuring the prime modulus scale `P`
against the pronic window or large-scale height `X`. -/
def crossScaleExponent (P X : ℝ) : ℝ :=
  2 * Real.log P / Real.log X

/-- At the linear receiver scale `X = P` (`P > 1`), the cross-scale exponent is `θ = 2`. -/
theorem crossScaleExponent_self {P : ℝ} (hP : 1 < P) :
    crossScaleExponent P P = 2 := by
  unfold crossScaleExponent
  have hlog : Real.log P ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hP)
  exact mul_div_cancel_right₀ 2 hlog

/-- At the quadratic Type-II horizon `X = P²` (`P > 1`), the cross-scale exponent is `θ = 1`. -/
theorem crossScaleExponent_sq {P : ℝ} (hP : 1 < P) :
    crossScaleExponent P (P ^ 2) = 1 := by
  unfold crossScaleExponent
  rw [Real.log_pow, Nat.cast_ofNat]
  have hlog : Real.log P ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hP)
  exact div_self (mul_ne_zero two_ne_zero hlog)

/-- At a general power horizon `X = P^α` (`P > 1`, `α ≠ 0`), the cross-scale exponent is `2 / α`. -/
theorem crossScaleExponent_rpow {P α : ℝ} (hP : 1 < P) (hα : α ≠ 0) :
    crossScaleExponent P (P ^ α) = 2 / α := by
  unfold crossScaleExponent
  rw [Real.log_rpow (by linarith)]
  have hlog : Real.log P ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hP)
  field_simp

/-- Inversely, the required horizon exponent `α = log X / log P` is `2 / θ`. -/
theorem crossScaleExponent_inv_mul_eq_log_ratio {P X : ℝ} (hP : 1 < P) (hX : 1 < X) :
    2 / crossScaleExponent P X = Real.log X / Real.log P := by
  unfold crossScaleExponent
  have hlogP : Real.log P ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hP)
  have hlogX : Real.log X ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hX)
  field_simp

/-! ## §2. The exact limit `2` of the sign-blind Type-II pronic Gram reading -/

/-- A datum on the Type-II pronic window face at prime block `B`, base prime scale `p₀`, short multiplier
scale `J₀`, coefficient packet `a : Nat.Primes → ℝ`, and unresolved cross-scale exponent `θ ∈ [0, 2]`. -/
structure PronicBlockGramDatum where
  B : Finset Nat.Primes
  p₀ : ℕ
  J₀ : ℕ
  a : Nat.Primes → ℝ
  θ : ℝ
  hθ_nonneg : 0 ≤ θ
  hθ_le_two : θ ≤ 2

/-- The sign-blind Type-II Gram reading records the prime support `B`, the window scale `(p₀, J₀)`,
and the pointwise coefficient magnitudes `|a p|` (which determine the diagonal `ℓ²` budget), but not
the inter-prime sign correlations or the unresolved exponent `θ`. -/
def typeIIGramReading (d : PronicBlockGramDatum) :
    Finset Nat.Primes × ℕ × ℕ × (Nat.Primes → ℝ) :=
  (d.B, d.p₀, d.J₀, fun p => |d.a p|)

/-- A dispersed datum at exponent `θ = 0` with given prime block `B`, scale `(p₀, J₀)`, and packet `a`. -/
def dispersedBlockDatum (B : Finset Nat.Primes) (p₀ J₀ : ℕ) (a : Nat.Primes → ℝ) :
    PronicBlockGramDatum where
  B := B
  p₀ := p₀
  J₀ := J₀
  a := a
  θ := 0
  hθ_nonneg := le_refl 0
  hθ_le_two := by norm_num

/-- The coherent prime-block datum at the maximal exponent `θ = 2`, carrying the unit-jump packet
`primeBlockPacket B` of the Type-II window no-go. -/
def coherentBlockDatum (B : Finset Nat.Primes) (p₀ J₀ : ℕ) : PronicBlockGramDatum where
  B := B
  p₀ := p₀
  J₀ := J₀
  a := primeBlockPacket B
  θ := 2
  hθ_nonneg := by norm_num
  hθ_le_two := le_refl 2

/-- For any packet `a` whose coefficient magnitudes on `B` match `primeBlockPacket B` (`|a p| = |primeBlockPacket B p|`),
the coherent prime-block datum at exponent `2` lies in the shadow of `dispersedBlockDatum B p₀ J₀ a`
under `typeIIGramReading`. -/
theorem coherentBlockDatum_mem_shadow_dispersed (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    {a : Nat.Primes → ℝ} (ha : ∀ p, |a p| = |primeBlockPacket B p|) :
    coherentBlockDatum B p₀ J₀ ∈ shadow typeIIGramReading (dispersedBlockDatum B p₀ J₀ a) := by
  rw [mem_shadow_iff]
  simp only [typeIIGramReading, coherentBlockDatum, dispersedBlockDatum, Prod.mk.injEq, true_and]
  funext p
  exact (ha p).symm

/-- **The exact resolution limit of the sign-blind Type-II Gram reading is `2`.**
In the cross-scale exponent unit `θ ∈ [0, 2]`, the sign-blind Type-II Gram reading cannot distinguish
a dispersed packet from the coherent prime block `primeBlockPacket B`, so its resolution limit is `2`. -/
theorem resolutionLimit_typeIIGramReading_eq_two (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    {a : Nat.Primes → ℝ} (ha : ∀ p, |a p| = |primeBlockPacket B p|) :
    resolutionLimit PronicBlockGramDatum.θ typeIIGramReading
      (dispersedBlockDatum B p₀ J₀ a) = 2 := by
  exact resolutionLimit_eq_of_mem_shadow_of_max
    (fun x => x.hθ_le_two)
    (coherentBlockDatum_mem_shadow_dispersed B p₀ J₀ ha)
    rfl

/-- **The exact resolution floor of the sign-blind Type-II Gram reading is `0`.** -/
theorem resolutionFloor_typeIIGramReading_eq_zero (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    (a : Nat.Primes → ℝ) :
    resolutionFloor PronicBlockGramDatum.θ typeIIGramReading
      (dispersedBlockDatum B p₀ J₀ a) = 0 := by
  unfold resolutionFloor
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨e, _, rfl⟩
      exact e.hθ_nonneg
    · exact ⟨dispersedBlockDatum B p₀ J₀ a, mem_shadow_self _ _, rfl⟩
  · apply le_csInf
    · exact ⟨0, dispersedBlockDatum B p₀ J₀ a, mem_shadow_self _ _, rfl⟩
    · rintro _ ⟨e, _, rfl⟩
      exact e.hθ_nonneg

/-- **The resolution interval of the sign-blind Type-II Gram reading is `Set.Icc 0 2`.** -/
theorem resolutionInterval_typeIIGramReading_eq (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    {a : Nat.Primes → ℝ} (ha : ∀ p, |a p| = |primeBlockPacket B p|) :
    resolutionInterval PronicBlockGramDatum.θ typeIIGramReading
      (dispersedBlockDatum B p₀ J₀ a) = Set.Icc 0 2 := by
  unfold resolutionInterval
  rw [resolutionFloor_typeIIGramReading_eq_zero,
    resolutionLimit_typeIIGramReading_eq_two B p₀ J₀ ha]

/-- **Certification threshold of the Type-II Gram reading.**
The sign-blind Type-II Gram reading certifies an upper bound `β` on `θ` if and only if `2 ≤ β`. -/
theorem certifies_typeIIGramReading_iff (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    {a : Nat.Primes → ℝ} (ha : ∀ p, |a p| = |primeBlockPacket B p|) (β : ℝ) :
    Certifies PronicBlockGramDatum.θ typeIIGramReading
      (dispersedBlockDatum B p₀ J₀ a) β ↔ 2 ≤ β := by
  constructor
  · intro h
    exact h (coherentBlockDatum B p₀ J₀) (coherentBlockDatum_mem_shadow_dispersed B p₀ J₀ ha)
  · intro h e _
    exact e.hθ_le_two.trans h

/-- No cross-scale exponent bound `β < 2` is certified by the sign-blind Type-II Gram reading. -/
theorem not_certifies_typeIIGramReading_of_lt_two (B : Finset Nat.Primes) (p₀ J₀ : ℕ)
    {a : Nat.Primes → ℝ} (ha : ∀ p, |a p| = |primeBlockPacket B p|) {β : ℝ} (hβ : β < 2) :
    ¬ Certifies PronicBlockGramDatum.θ typeIIGramReading
      (dispersedBlockDatum B p₀ J₀ a) β := by
  rw [certifies_typeIIGramReading_iff B p₀ J₀ ha]
  linarith

/-- **Concrete arithmetic witness at the resolution limit `2`.**
For every set `S` of primes in `(P, 2P]` (`P ≥ 3`, `J₀ > 0`, `4 J₀ ℓ ≤ P + 1`), there exists a prime
block `B ⊆ S` in a short interval `[p₀, p₀ + ℓ]` such that:
1. the sign-blind Type-II Gram reading at `(B, p₀, J₀)` has resolution limit `2` and floor `0`;
2. the coherent witness `coherentBlockDatum B p₀ J₀` lies in the shadow at `θ = 2`; and
3. its packet `primeBlockPacket B` forces pronic window energy at least `(|B| / 2304) |B|` times the
   window pronic mass, lower-bounding the full energy-centered pronic Gram `primePacketBilinear`. -/
theorem exists_primeBlock_witness_at_resolutionLimit_two (S : Finset Nat.Primes) {P ℓ J₀ : ℕ}
    (hP : 3 ≤ P) (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P) (hJ : 0 < J₀)
    (hJℓ : 4 * J₀ * ℓ ≤ P + 1) (hℓ : ℓ ≤ P + 1) :
    ∃ B ⊆ S, ∃ p₀ : ℕ, P < p₀ ∧ p₀ ≤ 2 * P ∧
      S.card / ((P - 1) / (ℓ + 1) + 1) ≤ B.card ∧
      resolutionLimit PronicBlockGramDatum.θ typeIIGramReading
        (dispersedBlockDatum B p₀ J₀ (primeBlockPacket B)) = 2 ∧
      resolutionFloor PronicBlockGramDatum.θ typeIIGramReading
        (dispersedBlockDatum B p₀ J₀ (primeBlockPacket B)) = 0 ∧
      coherentBlockDatum B p₀ J₀ ∈
        shadow typeIIGramReading (dispersedBlockDatum B p₀ J₀ (primeBlockPacket B)) ∧
      (B.card : ℝ) / 2304 * ((B.card : ℝ) *
          ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀), 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀),
          primePacketValue B (primeBlockPacket B) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧
      ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀),
          primePacketValue B (primeBlockPacket B) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        primePacketBilinear B B (primeBlockPacket B) (primeBlockPacket B) := by
  obtain ⟨B, hBS, p₀, hp₀1, hp₀2, hBcard, _, hwin, hgram⟩ :=
    exists_primeBlock_typeII_window_loss S hP hS hJ hJℓ hℓ
  refine ⟨B, hBS, p₀, hp₀1, hp₀2, hBcard,
    resolutionLimit_typeIIGramReading_eq_two B p₀ J₀ (fun _ => rfl),
    resolutionFloor_typeIIGramReading_eq_zero B p₀ J₀ (primeBlockPacket B),
    coherentBlockDatum_mem_shadow_dispersed B p₀ J₀ (fun _ => rfl),
    hwin, hgram⟩

/-! ## §3. The exact limit `2` of the rank-two readout reading -/

/-- A large-scale row datum at horizon `N`, carrying the row `c' : ℕ → ℝ` and its unresolved
cross-scale exponent `θ ∈ [0, 2]`. -/
structure ReadoutGramDatum where
  c' : ℕ → ℝ
  θ : ℝ
  hθ_nonneg : 0 ≤ θ
  hθ_le_two : θ ≤ 2

/-- The rank-two readout reading at horizon `N`, recording only the von Mangoldt readout `R(c')` and
the finite harmonic sum `H(c')` of the large-scale row. -/
def rankTwoReadoutReading (N : ℕ) (d : ReadoutGramDatum) : ℝ × ℝ :=
  (vonMangoldtReadout N d.c', finiteHarmonicSum N d.c')

/-- The zero-row datum at exponent `θ = 0`. -/
def zeroReadoutDatum : ReadoutGramDatum where
  c' := fun _ => 0
  θ := 0
  hθ_nonneg := le_refl 0
  hθ_le_two := by norm_num

/-- A barrier datum at exponent `θ = 2` associated with a large-scale row `c'`. -/
def barrierReadoutDatum (c' : ℕ → ℝ) : ReadoutGramDatum where
  c' := c'
  θ := 2
  hθ_nonneg := by norm_num
  hθ_le_two := le_refl 2

theorem vonMangoldtReadout_zero (N : ℕ) : vonMangoldtReadout N (fun _ => 0) = 0 := by
  simp [vonMangoldtReadout, selbergMultiplesCoord]

theorem finiteHarmonicSum_zero (N : ℕ) : finiteHarmonicSum N (fun _ => 0) = 0 := by
  simp [finiteHarmonicSum]

/-- Any large-scale row `c'` with vanishing rank-two readouts `R(c') = 0` and `H(c') = 0` places
`barrierReadoutDatum c'` (at `θ = 2`) in the shadow of `zeroReadoutDatum` (at `θ = 0`). -/
theorem barrierReadoutDatum_mem_shadow_zero (N : ℕ) {c' : ℕ → ℝ}
    (hR : vonMangoldtReadout N c' = 0) (hH : finiteHarmonicSum N c' = 0) :
    barrierReadoutDatum c' ∈ shadow (rankTwoReadoutReading N) zeroReadoutDatum := by
  rw [mem_shadow_iff]
  simp only [rankTwoReadoutReading, barrierReadoutDatum, zeroReadoutDatum,
    hR, hH, vonMangoldtReadout_zero, finiteHarmonicSum_zero]

/-- **The exact resolution limit of the rank-two readout reading is `2`.** -/
theorem resolutionLimit_rankTwoReadoutReading_eq_two (N : ℕ) :
    resolutionLimit ReadoutGramDatum.θ (rankTwoReadoutReading N) zeroReadoutDatum = 2 := by
  exact resolutionLimit_eq_of_mem_shadow_of_max
    (fun x => x.hθ_le_two)
    (barrierReadoutDatum_mem_shadow_zero N (vonMangoldtReadout_zero N) (finiteHarmonicSum_zero N))
    rfl

/-- **The exact resolution floor of the rank-two readout reading is `0`.** -/
theorem resolutionFloor_rankTwoReadoutReading_eq_zero (N : ℕ) :
    resolutionFloor ReadoutGramDatum.θ (rankTwoReadoutReading N) zeroReadoutDatum = 0 := by
  unfold resolutionFloor
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨e, _, rfl⟩
      exact e.hθ_nonneg
    · exact ⟨zeroReadoutDatum, mem_shadow_self _ _, rfl⟩
  · apply le_csInf
    · exact ⟨0, zeroReadoutDatum, mem_shadow_self _ _, rfl⟩
    · rintro _ ⟨e, _, rfl⟩
      exact e.hθ_nonneg

/-- **Three-window arithmetic barrier at the resolution limit `2` of the rank-two readout reading.**
For every modulus set `S ⊆ [512 H, D]` (`1 ≤ H`, `0 < D`) and `Q ≥ 150 D`, the three-window
construction of `exists_readout_free_barrier` produces a large-scale row
`c' = c₁ - a₂ c₂ - a₃ c₃` such that `barrierReadoutDatum c'` lies in the shadow of `zeroReadoutDatum`
at the resolution limit `θ = 2` while forcing `rowBilinear N c c' ≥ (1 / 200) (Σ c(d) d) (Σ |c'(n)| / n²)`. -/
theorem exists_readout_free_witness_at_resolutionLimit_two {S : Finset ℕ} {D H Q : ℕ}
    (hH : 1 ≤ H) (hD0 : 0 < D) (hS : ∀ d ∈ S, 512 * H ≤ d ∧ d ≤ D) (hQ : 150 * D ≤ Q) :
    ∃ n₁ n₂ n₃ : ℕ, Q ≤ n₂ ∧ n₂ + H ≤ n₁ ∧ n₁ + H ≤ n₃ ∧ n₃ < Q + 6 * D + 2 * H ∧
      ∃ S' ⊆ S, S.card ≤ 2 ^ 27 * S'.card ∧
        ∀ (N : ℕ) (c c₁ c₂ c₃ : ℕ → ℝ), (∀ d, c d ≠ 0 → d ∈ S') → (∀ d, 0 ≤ c d) →
          (∀ n, c₁ n ≠ 0 → n ∈ Ico n₁ (n₁ + H)) → (∀ n, 0 ≤ c₁ n) →
          (∀ n, c₂ n ≠ 0 → n ∈ Ico n₂ (n₂ + H)) → (∀ n, 0 ≤ c₂ n) →
          (∀ n, c₃ n ≠ 0 → n ∈ Ico n₃ (n₃ + H)) → (∀ n, 0 ≤ c₃ n) →
          0 < finiteHarmonicSum N c₂ → 0 < finiteHarmonicSum N c₃ →
          ∃ a₂ a₃ : ℝ, 0 ≤ a₂ ∧ 0 ≤ a₃ ∧
            barrierReadoutDatum (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) ∈
              shadow (rankTwoReadoutReading N) zeroReadoutDatum ∧
            resolutionLimit ReadoutGramDatum.θ (rankTwoReadoutReading N) zeroReadoutDatum = 2 ∧
            1 / 200 * (∑ d ∈ Icc 1 N, c d * d) *
                ∑ n ∈ Icc 1 N, |c₁ n - a₂ * c₂ n - a₃ * c₃ n| / (n : ℝ) ^ 2 ≤
              rowBilinear N c (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) := by
  obtain ⟨n₁, n₂, n₃, h1, h2, h3, h4, S', hS', hcard, hbar⟩ :=
    exists_readout_free_barrier hH hD0 hS hQ
  refine ⟨n₁, n₂, n₃, h1, h2, h3, h4, S', hS', hcard, ?_⟩
  intro N c c₁ c₂ c₃ hc hc0 hc₁ hc₁0 hc₂ hc₂0 hc₃ hc₃0 hH₂ hH₃
  obtain ⟨a₂, a₃, ha₂, ha₃, hHz, hRz, hbil⟩ :=
    hbar N c c₁ c₂ c₃ hc hc0 hc₁ hc₁0 hc₂ hc₂0 hc₃ hc₃0 hH₂ hH₃
  exact ⟨a₂, a₃, ha₂, ha₃, barrierReadoutDatum_mem_shadow_zero N hRz hHz,
    resolutionLimit_rankTwoReadoutReading_eq_two N, hbil⟩

/-! ## §4. The exact smoothness resolution ladder `2K / (K + 1)` and `2 / (K + 1)` -/

/-- The cross-scale exponent `θ_cert(K) = 2K / (K + 1)` certified when `K` consecutive Euler-Maclaurin
kernels cancel (`K = 0` for the rough Type-II baseline, `K = L + 1` for `L`-fold smoothness). -/
def smoothCertifiedExponent (K : ℕ) : ℝ :=
  2 * (K : ℝ) / ((K : ℝ) + 1)

/-- The unresolved cross-scale exponent deficit `2 - θ_cert(K) = 2 / (K + 1)` remaining after `K`
cancelled Euler-Maclaurin kernels. -/
def smoothUnresolvedLimit (K : ℕ) : ℝ :=
  2 / ((K : ℝ) + 1)

/-- At `K = 0` (no smoothness, rough Type-II baseline), the certified exponent is `0` and the
unresolved resolution limit is `2`. -/
theorem smoothCertifiedExponent_zero : smoothCertifiedExponent 0 = 0 := by
  simp [smoothCertifiedExponent]

theorem smoothUnresolvedLimit_zero : smoothUnresolvedLimit 0 = 2 := by
  simp [smoothUnresolvedLimit]

/-- At `K = 1` (flat large-scale row, first kernel cancelled), the certified exponent is `1` and the
unresolved resolution limit is `1`. -/
theorem smoothCertifiedExponent_one : smoothCertifiedExponent 1 = 1 := by
  norm_num [smoothCertifiedExponent]

theorem smoothUnresolvedLimit_one : smoothUnresolvedLimit 1 = 1 := by
  norm_num [smoothUnresolvedLimit]

/-- At `K = 2` (`C²`-smooth row / sharp-cutoff Type-I limit), the certified exponent is `4 / 3` and
the unresolved resolution limit is `2 / 3`. -/
theorem smoothCertifiedExponent_two : smoothCertifiedExponent 2 = 4 / 3 := by
  norm_num [smoothCertifiedExponent]

theorem smoothUnresolvedLimit_two : smoothUnresolvedLimit 2 = 2 / 3 := by
  norm_num [smoothUnresolvedLimit]

/-- At the `K`-kernel smoothness horizon `X = P^{(K+1)/K}` (`P > 1`, `K ≥ 1`), the cross-scale
exponent `crossScaleExponent P X` equals `smoothCertifiedExponent K = 2K / (K + 1)`. -/
theorem crossScaleExponent_smoothHorizon {P : ℝ} (hP : 1 < P) {K : ℕ} (hK : 1 ≤ K) :
    crossScaleExponent P (P ^ (((K : ℝ) + 1) / (K : ℝ))) = smoothCertifiedExponent K := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hK1 : ((K : ℝ) + 1) / (K : ℝ) ≠ 0 := div_ne_zero (by positivity) hK0
  rw [crossScaleExponent_rpow hP hK1, smoothCertifiedExponent]
  field_simp

/-- Conservation of the cross-scale exponent budget: for every kernel order `K`,
`smoothCertifiedExponent K + smoothUnresolvedLimit K = 2`. -/
theorem smoothCertifiedExponent_add_smoothUnresolvedLimit (K : ℕ) :
    smoothCertifiedExponent K + smoothUnresolvedLimit K = 2 := by
  unfold smoothCertifiedExponent smoothUnresolvedLimit
  have hK : (K : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem smoothCertifiedExponent_nonneg (K : ℕ) : 0 ≤ smoothCertifiedExponent K := by
  unfold smoothCertifiedExponent
  positivity

theorem smoothCertifiedExponent_lt_two (K : ℕ) : smoothCertifiedExponent K < 2 := by
  have h := smoothCertifiedExponent_add_smoothUnresolvedLimit K
  have hpos : 0 < smoothUnresolvedLimit K := by unfold smoothUnresolvedLimit; positivity
  linarith

theorem smoothUnresolvedLimit_pos (K : ℕ) : 0 < smoothUnresolvedLimit K := by
  unfold smoothUnresolvedLimit
  positivity

theorem smoothUnresolvedLimit_le_two (K : ℕ) : smoothUnresolvedLimit K ≤ 2 := by
  have h := smoothCertifiedExponent_add_smoothUnresolvedLimit K
  have h0 := smoothCertifiedExponent_nonneg K
  linarith

/-- Each additional cancelled kernel strictly increases the certified cross-scale exponent. -/
theorem strictMono_smoothCertifiedExponent : StrictMono smoothCertifiedExponent := by
  intro j k hjk
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt : (j : ℝ) < (k : ℝ) := Nat.cast_lt.mpr hjk
  unfold smoothCertifiedExponent
  rw [div_lt_div_iff₀ hj hk]
  linarith

/-- Each additional cancelled kernel strictly lowers the unresolved exponent limit from `2` toward `0`. -/
theorem strictAnti_smoothUnresolvedLimit : StrictAnti smoothUnresolvedLimit := by
  intro j k hjk
  have hj := smoothCertifiedExponent_add_smoothUnresolvedLimit j
  have hk := smoothCertifiedExponent_add_smoothUnresolvedLimit k
  have hlt := strictMono_smoothCertifiedExponent hjk
  linarith

/-- As the smoothness order `K → ∞`, the unresolved resolution limit tends to `0`. -/
theorem tendsto_smoothUnresolvedLimit_atTop :
    Tendsto smoothUnresolvedLimit atTop (nhds 0) := by
  unfold smoothUnresolvedLimit
  have h1 : Tendsto (fun K : ℕ => (K : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.div_atTop h1

/-- As the smoothness order `K → ∞`, the certified cross-scale exponent tends to the full receiver
threshold `2`. -/
theorem tendsto_smoothCertifiedExponent_atTop :
    Tendsto smoothCertifiedExponent atTop (nhds 2) := by
  have heq : smoothCertifiedExponent = fun K => 2 - smoothUnresolvedLimit K := by
    funext K
    linarith [smoothCertifiedExponent_add_smoothUnresolvedLimit K]
  rw [heq]
  simpa using tendsto_const_nhds.sub tendsto_smoothUnresolvedLimit_atTop

/-- A datum in the `K`-kernel smoothness class, carrying the kernel order `K` and a bounded
unresolved deficit `δ ∈ [0, smoothUnresolvedLimit K]` together with the certified exponent
`θ = 2 - δ ∈ [smoothCertifiedExponent K, 2]`. -/
structure SmoothGramDatum (K : ℕ) where
  θ : ℝ
  hθ_ge : smoothCertifiedExponent K ≤ θ
  hθ_le : θ ≤ 2

/-- The unresolved exponent deficit `δ = 2 - θ` of a smooth Gram datum at kernel order `K`. -/
def SmoothGramDatum.deficit {K : ℕ} (d : SmoothGramDatum K) : ℝ :=
  2 - d.θ

/-- The `K`-kernel smoothness reading on `SmoothGramDatum K` sees only the kernel class `K`. -/
def smoothKernelReading (K : ℕ) (_ : SmoothGramDatum K) : ℕ :=
  K

/-- The worst-case datum at kernel order `K`, sitting at the certified threshold `θ = 2K / (K + 1)`
with unresolved deficit `2 / (K + 1)`. -/
def boundarySmoothDatum (K : ℕ) : SmoothGramDatum K where
  θ := smoothCertifiedExponent K
  hθ_ge := le_refl _
  hθ_le := (smoothCertifiedExponent_lt_two K).le

/-- The fully dispersed datum at kernel order `K`, sitting at `θ = 2` with unresolved deficit `0`. -/
def dispersedSmoothDatum (K : ℕ) : SmoothGramDatum K where
  θ := 2
  hθ_ge := (smoothCertifiedExponent_lt_two K).le
  hθ_le := le_refl 2

/-- **The exact resolution floor of the `K`-kernel smoothness reading for `θ` is `2K / (K + 1)`.** -/
theorem resolutionFloor_smoothKernelReading_eq (K : ℕ) :
    resolutionFloor SmoothGramDatum.θ (smoothKernelReading K) (boundarySmoothDatum K) =
      smoothCertifiedExponent K := by
  unfold resolutionFloor
  apply le_antisymm
  · apply csInf_le
    · refine ⟨smoothCertifiedExponent K, ?_⟩
      rintro _ ⟨e, _, rfl⟩
      exact e.hθ_ge
    · exact ⟨boundarySmoothDatum K, mem_shadow_self _ _, rfl⟩
  · apply le_csInf
    · exact ⟨smoothCertifiedExponent K, boundarySmoothDatum K, mem_shadow_self _ _, rfl⟩
    · rintro _ ⟨e, _, rfl⟩
      exact e.hθ_ge

/-- **The exact resolution limit of the `K`-kernel smoothness reading for the unresolved deficit is
`2 / (K + 1)`.** -/
theorem resolutionLimit_smoothKernelReading_deficit_eq (K : ℕ) :
    resolutionLimit SmoothGramDatum.deficit (smoothKernelReading K) (dispersedSmoothDatum K) =
      smoothUnresolvedLimit K := by
  apply resolutionLimit_eq_of_mem_shadow_of_max
    (e := boundarySmoothDatum K)
  · intro x
    unfold SmoothGramDatum.deficit
    have hge := x.hθ_ge
    linarith [smoothCertifiedExponent_add_smoothUnresolvedLimit K]
  · rfl
  · unfold SmoothGramDatum.deficit boundarySmoothDatum
    linarith [smoothCertifiedExponent_add_smoothUnresolvedLimit K]

/-! ## §5. Faithful completions on the single-modulus Gram face and the arithmetic bypass -/

/-- The second-order Bernoulli cross-scale main functional at horizon `N` and small-scale row `c`. -/
def bernoulliCrossScaleMain (N : ℕ) (c c' : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)

/-- The Bernoulli cross-scale main functional factors purely through the weighted residue-mass
reading `residueMass N c'`. -/
theorem bernoulliCrossScaleMain_eq_of_residueMass_eq (N : ℕ) (c : ℕ → ℝ) {c'₁ c'₂ : ℕ → ℝ}
    (hmass : residueMass N c'₁ = residueMass N c'₂) :
    bernoulliCrossScaleMain N c c'₁ = bernoulliCrossScaleMain N c c'₂ := by
  unfold bernoulliCrossScaleMain
  rw [sum_comm, sum_comm (s := Icc 1 N) (t := Icc 1 N) (f := fun n d =>
    c'₂ n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2))]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have e : ∀ c' : ℕ → ℝ, ∑ n ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2) =
      c d / d * ∑ r ∈ range d, bernoulliKernel d r * residueMass N c' d r := fun c' => by
    rw [← sum_mul_bernoulliKernel_eq_residueMass hd0, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [e, e, hmass]

/-- Because `residueMass N` determines `bernoulliCrossScaleMain N c` on its whole shadow, its
resolution limit at every large-scale row `c'` equals `bernoulliCrossScaleMain N c c'`. -/
theorem resolutionLimit_residueMass_bernoulliCrossScaleMain (N : ℕ) (c c' : ℕ → ℝ) :
    resolutionLimit (bernoulliCrossScaleMain N c) (residueMass N) c' =
      bernoulliCrossScaleMain N c c' := by
  have hbdd : BddAbove (bernoulliCrossScaleMain N c '' shadow (residueMass N) c') :=
    ⟨bernoulliCrossScaleMain N c c', by
      rintro _ ⟨e, he, rfl⟩
      exact (bernoulliCrossScaleMain_eq_of_residueMass_eq N c he).le⟩
  refine le_antisymm ?_ (le_resolutionLimit hbdd)
  exact (certifies_iff_resolutionLimit_le hbdd).mp fun e he =>
    (bernoulliCrossScaleMain_eq_of_residueMass_eq N c he).le

/-- **Exact faithfulness of the residue-mass reading for the Bernoulli cross-scale functional.**
The reading `residueMass N` is unconditionally faithful (`Faithful`) for `bernoulliCrossScaleMain N c`. -/
theorem faithful_residueMass_bernoulliCrossScaleMain (N : ℕ) (c : ℕ → ℝ) :
    Faithful (bernoulliCrossScaleMain N c) (residueMass N) :=
  fun c' => resolutionLimit_residueMass_bernoulliCrossScaleMain N c c'

/-- Likewise, the resolution floor of `residueMass N` for `bernoulliCrossScaleMain N c` equals
`bernoulliCrossScaleMain N c c'`. -/
theorem resolutionFloor_residueMass_bernoulliCrossScaleMain (N : ℕ) (c c' : ℕ → ℝ) :
    resolutionFloor (bernoulliCrossScaleMain N c) (residueMass N) c' =
      bernoulliCrossScaleMain N c c' := by
  have hbb : BddBelow (bernoulliCrossScaleMain N c '' shadow (residueMass N) c') :=
    ⟨bernoulliCrossScaleMain N c c', by
      rintro _ ⟨e, he, rfl⟩
      exact (bernoulliCrossScaleMain_eq_of_residueMass_eq N c he).ge⟩
  have hba : BddAbove (bernoulliCrossScaleMain N c '' shadow (residueMass N) c') :=
    ⟨bernoulliCrossScaleMain N c c', by
      rintro _ ⟨e, he, rfl⟩
      exact (bernoulliCrossScaleMain_eq_of_residueMass_eq N c he).le⟩
  have h := (resolutionFloor_eq_resolutionLimit_iff hbb hba).mpr
    (fun e he => bernoulliCrossScaleMain_eq_of_residueMass_eq N c he)
  rw [h, resolutionLimit_residueMass_bernoulliCrossScaleMain]

/-- **Quantitative shadow-diameter bound for the completed residue-mass reading.**
For the combined reading `(vonMangoldtReadout N, finiteHarmonicSum N, residueMass N)` that sees the
rank-two readouts and the weighted residue masses, any two rows `c'₁, c'₂` in the same shadow have
cross-scale Grams `rowBilinear N c c'₁` and `rowBilinear N c c'₂` differing by at most the cubic tail
`(3 / 4) (Σ |c(d)| d²) (Σ |c'₁(n)| / n³ + Σ |c'₂(n)| / n³)`. -/
def completedResidueReading (N : ℕ) (c' : ℕ → ℝ) : ℝ × ℝ × (ℕ → ℕ → ℝ) :=
  (vonMangoldtReadout N c', finiteHarmonicSum N c', residueMass N c')

theorem abs_rowBilinear_sub_of_mem_shadow_completedResidueReading (N : ℕ) (c : ℕ → ℝ)
    {c'₁ c'₂ : ℕ → ℝ} (hshadow : c'₁ ∈ shadow (completedResidueReading N) c'₂) :
    |rowBilinear N c c'₁ - rowBilinear N c c'₂| ≤
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
        (∑ n ∈ Icc 1 N, |c'₁ n| / (n : ℝ) ^ 3 + ∑ n ∈ Icc 1 N, |c'₂ n| / (n : ℝ) ^ 3) := by
  rw [mem_shadow_iff] at hshadow
  simp only [completedResidueReading, Prod.mk.injEq] at hshadow
  obtain ⟨hR, hH, hmass⟩ := hshadow
  have h := abs_rowBilinear_sub_of_residueMass_eq N (c := c) (c'₁ := c'₁) (c'₂ := c'₂)
    (fun d _ _ r _ => congr_fun (congr_fun hmass d) r)
  rw [hR, hH] at h
  simpa using h

/-- **Quantitative shadow-diameter bound for the dual-norm kernel-statistic reading.**
When the reading is refined to the third-order `kernelStatistic N` together with the weighted inverse-square
sum `Σ c'(n) / n²` and the rank-two readouts, any two rows `c'₁, c'₂` in the same shadow have
cross-scale Grams against any prime-supported row `c` differing by at most the fourth-order tail
`6 (Σ |c(p)| p³) (Σ |c'₁(n)| / n⁴ + Σ |c'₂(n)| / n⁴)`. -/
def completedKernelStatisticReading (N : ℕ) (c' : ℕ → ℝ) : ℝ × ℝ × ℝ × (ℕ → ℝ) :=
  (vonMangoldtReadout N c', finiteHarmonicSum N c',
    ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2, kernelStatistic N c')

theorem abs_rowBilinear_sub_of_mem_shadow_completedKernelStatisticReading (N : ℕ)
    {c c'₁ c'₂ : ℕ → ℝ} (hc : ∀ d, c d ≠ 0 → d.Prime)
    (hshadow : c'₁ ∈ shadow (completedKernelStatisticReading N) c'₂) :
    |rowBilinear N c c'₁ - rowBilinear N c c'₂| ≤
      6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) *
        (∑ n ∈ Icc 1 N, |c'₁ n| / (n : ℝ) ^ 4 + ∑ n ∈ Icc 1 N, |c'₂ n| / (n : ℝ) ^ 4) := by
  rw [mem_shadow_iff] at hshadow
  simp only [completedKernelStatisticReading, Prod.mk.injEq] at hshadow
  obtain ⟨hR, hH, hS, hK⟩ := hshadow
  have h1 := abs_rowBilinear_sub_kernelStatistic_le N c'₁ hc
  have h2 := abs_rowBilinear_sub_kernelStatistic_le N c'₂ hc
  have hmain : equidistributedMain N c c'₁ = equidistributedMain N c c'₂ := by
    simp only [equidistributedMain, hS]
  have hstat : (∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c'₁ d) =
      ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c'₂ d := by
    simp only [hK]
  have heq : rowBilinear N c c'₁ - rowBilinear N c c'₂ =
      (rowBilinear N c c'₁ + rowMean N c * vonMangoldtReadout N c'₁ +
        rowBeta N c * finiteHarmonicSum N c'₁ - equidistributedMain N c c'₁ -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c'₁ d) -
      (rowBilinear N c c'₂ + rowMean N c * vonMangoldtReadout N c'₂ +
        rowBeta N c * finiteHarmonicSum N c'₂ - equidistributedMain N c c'₂ -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c'₂ d) := by
    rw [hR, hH, hmain, hstat]
    ring
  rw [heq]
  calc |_ - _| ≤ |_| + |_| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **The arithmetic bypass of the Type-II shadow in the cross-scale exponent range `7/6 < θ < 2`.**
Although the sign-blind Type-II reading (`typeIIGramReading`) and the rank-two readout reading
(`rankTwoReadoutReading`) both have worst-case resolution limit `2` on `[0, 2]`, the actual centred
prime row `centredPrimeRow A H K` is not an adversarial coherent block: for every short-interval
exponent `α ∈ (7/12, 1)` (governing `7/6 < θ < 2`) and every `ε ∈ (0, 1]`, its rank-two corrected
cross-scale Gram is unconditionally bounded by `16 ε` times the diagonal remainder product. -/
theorem centredPrimeRow_bypasses_resolutionLimit_two {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q₀ : ℕ, ∀ {N A H K P Q : ℕ} {c : ℕ → ℝ}, Q₀ ≤ Q → Q ≤ A → A + K * H ≤ 2 * Q →
      2 * Q ≤ N → 1 ≤ P → (2 * (Q : ℝ)) ^ α ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ α →
      (∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) →
      (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8 ≤ ε * P →
      3 * (P : ℝ) ≤ 2 * ε * Q →
      resolutionLimit ReadoutGramDatum.θ (rankTwoReadoutReading N) zeroReadoutDatum = 2 ∧
      |rowBilinear N c (centredPrimeRow A H K) +
          rowMean N c * vonMangoldtReadout N (centredPrimeRow A H K) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeRow A H K)| ≤
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_rowBilinear_centredPrimeRow_le hα hα1 hε hε1
  refine ⟨Q₀, fun hQ hA hAK hN hP hH1 hH2 hc hterm2 hterm3 =>
    ⟨resolutionLimit_rankTwoReadoutReading_eq_two _,
      hQ₀ hQ hA hAK hN hP hH1 hH2 hc hterm2 hterm3⟩⟩

end

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
