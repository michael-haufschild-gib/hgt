import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding
import GaloisForLFunctions.RHTower.WeilLevyBoundaryEscapeCollarPotential

/-!
# Reflected Origin-Crossing Killing Potential, Half-Line Escape Diagonalization at `t ≥ L`, and Disjoint-Support Prime-Doob Cancellation

Building on `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` and
`WeilLevyBoundaryEscapeCollarPotential`, this module establishes the structural half-line and
support-escape mechanisms for the Doob ground-state representation
`markovEnergy (Φ v) = phiDoobArchJumpEnergy v + (∑' n, ∫ phiDoobPrimeJump v n) - phiDoobCoshMass (v²)`:

1. **Section 1 (Full-Line Disjoint-Support Diagonalization at `t ≥ 2 L` and Exact Short-Support
   Prime-Doob Cancellation on `(-log 2 / 2, log 2 / 2)`):**
   - If `v` vanishes outside `(-L, L)` and `t ≥ 2 * L`, then `v x * v (x + t) = 0` for all `x ∈ ℝ`,
     so `phiDoobArchShiftJump v t x = Φ(x) Φ(x + t) (v(x)² + v(x + t)²)` (`phiDoobArchShiftJump_eq_diagonal_of_support_Ioo`).
   - For prime powers `n` with `2 * L ≤ log n`, `phiDoobPrimeCross v n x = 0` and
     `phiDoobPrimeJump v n x = phiDoobPrimeDiagonal v n x` (`phiDoobPrimeJump_eq_phiDoobPrimeDiagonal_of_support_Ioo`).
   - On `(-log 2 / 2, log 2 / 2)`, `phiDoobPrimeJump v n = phiDoobPrimeDiagonal v n` holds for
     **every** `n : ℕ`, so the prime Doob jumps sum to `mixedPhiArchRe (Φ v²) + phiDoobCoshMass (v²)`,
     cancelling `-phiDoobCoshMass (v²)` identically (`tsum_integral_phiDoobPrimeJump_eq_mixedPhiArchRe_add_phiDoobCoshMass_of_support_half_log_two`,
     `phiDoob_markovEnergy_eq_archJump_add_mixedPhiArchRe_of_support_half_log_two`).

2. **Section 2 (Half-Line `(0, ∞)` Reflecting-Wall Escape at `t ≥ L` for Odd `v`):**
   - For an **odd** function `v(-x) = -v(x)` vanishing outside `(-L, L)`, the origin `0` acts as a
     reflecting wall:
     * Every shift `t` from `x > 0` escapes the right boundary `+L` as soon as `x > max 0 (L - t)`
       (in particular for **all** `x > 0` whenever `t ≥ L`, half the full-line threshold `2 L`!).
     * Every shift `t` from `x < 0` that lands in `(0, L)` crosses the origin, so its overlap is
       packaged into the nonnegative sum square `(v u + v (t - u))² ≥ 0` on `Ioo 0 t`.
   - We prove the general right-escape decomposition (`integral_Ioi_phiDoobArchShiftJump_eq_interior_add_escape`,
     `integral_phiDoobArchShiftJump_eq_interior_add_escape_add_collar_of_odd`) and the half-threshold
     diagonalization (`integral_Ioi_phiDoobArchShiftJump_eq_diagonal_of_le_shift`,
     `integral_phiDoobArchShiftJump_eq_halfLine_diagonal_add_collar_of_odd`,
     `integral_phiDoobPrimeJump_eq_halfLine_diagonal_add_collar_of_odd`).
   - In particular, when `supp(v) ⊂ (-log 2, log 2)` and `v` is odd, **every** prime power `n ≥ 2`
     satisfies `log n ≥ log 2 = L`, so the half-line prime jump is 100% diagonal for all `n ≥ 2`
     (`integral_phiDoobPrimeJump_eq_halfLine_diagonal_add_collar_of_support_log_two`).

3. **Section 3 (Midpoint Reflection and Killing-Potential Decomposition of the Origin-Crossing
   Collar `(0, t)`):**
   - We define `phiDoobCollarSumSq`, `phiDoobCollarDiffSq`, and `phiDoobCollarKillingDensity`, and
     prove the reflection identity `∫_{x ∈ (0, t)} Φ(x)Φ(t-x) v(t-x)² = ∫_{x ∈ (0, t)} Φ(x)Φ(t-x) v(x)²`
     (`setIntegral_Ioo_collar_reflect_sq`) and the **Exact Collar Killing-Potential Identity**
     (`integral_phiDoobCollarSumSq_add_diffSq_eq_killing`):
     `∫_{x ∈ (0, t)} phiDoobCollarSumSq v t x + ∫_{x ∈ (0, t)} phiDoobCollarDiffSq v t x = ∫_{x ∈ (0, t)} 4 Φ(x)Φ(t-x) v(x)²`.
   - We prove the midpoint folding identities on `Ioo 0 (t / 2)`
     (`integral_phiDoobCollarSumSq_eq_two_mul_half`, `integral_phiDoobCollarDiffSq_eq_two_mul_half`).

4. **Section 4 (Reflected Archimedean Dirichlet + Killing Potential Decomposition on `(0, ∞)`):**
   - We prove the fundamental reflected algebraic identity
     `w_- (a - b)² + w_+ (a + b)² = (w_- - w_+)(a - b)² + 2 w_+ (a² + b²)`
     (`reflected_dirichlet_killing_pointwise`).
   - We prove strict antitonicity of `archLevyDensity` on `(0, ∞)` (`strictAntiOn_archLevyDensity`),
     define `reflectedArchLevyWeight x s := archLevyDensity s - archLevyDensity (s + 2 * x)`, and
     prove `0 < reflectedArchLevyWeight x s` for all `x > 0, s > 0` (`reflectedArchLevyWeight_pos`),
     yielding the manifestly nonnegative reflected Dirichlet + Killing decomposition
     (`archLevy_reflected_jump_add_collar_eq`, `reflectedArchLevy_dirichlet_term_nonneg`,
     `reflectedArchLevy_killing_term_nonneg`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate FourierTransform ContDiff
open Zeta23
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole LebesgueAtomWeil
open RHTower.NonnegativeCone RHTower.WeilLevyBoundaryEscape

/-! ## Section 1: Full-Line Disjoint-Support Diagonalization at `t ≥ 2 L` and Exact Short-Support Prime-Doob Cancellation on `(-log 2 / 2, log 2 / 2)` -/

/-- If `v` vanishes outside `Ioo (-L) L` and `2 * L ≤ t`, then `v x * v (x + t) = 0` for all `x ∈ ℝ`. -/
theorem mul_shift_eq_zero_of_support_Ioo {v : ℝ → ℝ} {L t : ℝ}
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (ht : 2 * L ≤ t) (x : ℝ) :
    v x * v (x + t) = 0 := by
  by_cases hx : x ∈ Ioo (-L) L
  · have hxt : x + t ∉ Ioo (-L) L := by
      intro hmem
      linarith [hx.1, hmem.2]
    rw [hsupp (x + t) hxt, mul_zero]
  · rw [hsupp x hx, zero_mul]

/-- If `v` vanishes outside `Ioo (-L) L` and `2 * L ≤ t`, then `(v x - v (x + t)) ^ 2 = v x ^ 2 + v (x + t) ^ 2`
for all `x ∈ ℝ`. -/
theorem sub_shift_sq_eq_add_sq_of_support_Ioo {v : ℝ → ℝ} {L t : ℝ}
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (ht : 2 * L ≤ t) (x : ℝ) :
    (v x - v (x + t)) ^ 2 = v x ^ 2 + v (x + t) ^ 2 := by
  have hmul := mul_shift_eq_zero_of_support_Ioo hsupp ht x
  calc
    (v x - v (x + t)) ^ 2 = v x ^ 2 + v (x + t) ^ 2 - 2 * (v x * v (x + t)) := by ring
    _ = v x ^ 2 + v (x + t) ^ 2 := by rw [hmul]; ring

/-- **Pointwise Disjoint-Support Diagonalization of `phiDoobArchShiftJump`**:
if `v` vanishes outside `Ioo (-L) L` and `2 * L ≤ t`, then for all `x ∈ ℝ`,
`phiDoobArchShiftJump v t x = Φ(x) Φ(x + t) (v(x)² + v(x + t)²)`. -/
theorem phiDoobArchShiftJump_eq_diagonal_of_support_Ioo {v : ℝ → ℝ} {L t : ℝ}
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (ht : 2 * L ≤ t) (x : ℝ) :
    phiDoobArchShiftJump v t x =
      riemannKernelReal x * riemannKernelReal (x + t) * (v x ^ 2 + v (x + t) ^ 2) := by
  unfold phiDoobArchShiftJump
  rw [sub_shift_sq_eq_add_sq_of_support_Ioo hsupp ht x]

/-- **Integral Disjoint-Support Diagonalization of `phiDoobArchShiftJump`**:
if `v ∈ C_c(ℝ)` vanishes outside `Ioo (-L) L` and `2 * L ≤ t`, then
`∫ x, phiDoobArchShiftJump v t x = ∫ x, Φ(x) (Φ(x + t) + Φ(x - t)) v(x)²`. -/
theorem integral_phiDoobArchShiftJump_eq_diagonal_of_support_Ioo {v : ℝ → ℝ} {L t : ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (ht : 2 * L ≤ t) :
    (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      ∫ x : ℝ, riemannKernelReal x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) *
        v x ^ 2 := by
  have hv2c : HasCompactSupport (fun x : ℝ => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx; simp [hx]
  have h1 : Integrable (fun x : ℝ => riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) := by
    have hcs : HasCompactSupport
        (fun x : ℝ => riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) := hv2c.mul_left
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
      (hv.pow 2)).integrable_of_hasCompactSupport hcs
  have h2' : Integrable
      (fun x : ℝ => riemannKernelReal x * riemannKernelReal (x + t) * v (x + t) ^ 2) := by
    have hv2t : HasCompactSupport (fun x : ℝ => v (x + t) ^ 2) :=
      hv2c.comp_homeomorph (Homeomorph.addRight t)
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
      ((hv.comp (continuous_id.add continuous_const)).pow 2)).integrable_of_hasCompactSupport
      hv2t.mul_left
  have h3 : Integrable
      (fun x : ℝ => riemannKernelReal x * riemannKernelReal (x - t) * v x ^ 2) := by
    have hcs : HasCompactSupport
        (fun x : ℝ => riemannKernelReal x * riemannKernelReal (x - t) * v x ^ 2) := hv2c.mul_left
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const))).mul
      (hv.pow 2)).integrable_of_hasCompactSupport hcs
  have hcongr : (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      ∫ x : ℝ, (riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2 +
        riemannKernelReal x * riemannKernelReal (x + t) * v (x + t) ^ 2) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [phiDoobArchShiftJump_eq_diagonal_of_support_Ioo hsupp ht x]
    ring
  have htr : (∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + t) * v (x + t) ^ 2) =
      ∫ u : ℝ, riemannKernelReal u * riemannKernelReal (u - t) * v u ^ 2 := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun u : ℝ => riemannKernelReal u * riemannKernelReal (u - t) * v u ^ 2) t
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [show x + t - t = x by ring]
    ring
  rw [hcongr, integral_add h1 h2', htr, ← integral_add h1 h3]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

/-- **Pointwise Prime-Doob Disjoint-Support Reduction**:
if `v` vanishes outside `Ioo (-L) L` and `2 * L ≤ Real.log n`, then for all `x ∈ ℝ`,
`phiDoobPrimeCross v n x = 0` and `phiDoobPrimeJump v n x = phiDoobPrimeDiagonal v n x`. -/
theorem phiDoobPrimeCross_and_jump_eq_of_support_Ioo {v : ℝ → ℝ} {L : ℝ} {n : ℕ}
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (hn : 2 * L ≤ Real.log n) (x : ℝ) :
    phiDoobPrimeCross v n x = 0 ∧
      phiDoobPrimeJump v n x =
        vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          (v x ^ 2 + v (x + Real.log n) ^ 2) := by
  have hmul := mul_shift_eq_zero_of_support_Ioo hsupp hn x
  constructor
  · unfold phiDoobPrimeCross
    calc
      2 * vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          v x * v (x + Real.log n) =
        2 * vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          (v x * v (x + Real.log n)) := by ring
      _ = 0 := by rw [hmul, mul_zero]
  · unfold phiDoobPrimeJump
    rw [sub_shift_sq_eq_add_sq_of_support_Ioo hsupp hn x]

/-- **Integral Prime-Doob Disjoint-Support Diagonalization**:
if `v ∈ C_c(ℝ)` vanishes outside `Ioo (-L) L` and `2 * L ≤ Real.log n`, then
`∫ x, phiDoobPrimeCross v n x = 0` and
`∫ x, phiDoobPrimeJump v n x = ∫ x, phiDoobPrimeDiagonal v n x`. -/
theorem integral_phiDoobPrimeJump_eq_diagonal_of_support_Ioo {v : ℝ → ℝ} {L : ℝ} {n : ℕ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hsupp : ∀ x ∉ Ioo (-L) L, v x = 0) (hn : 2 * L ≤ Real.log n) :
    (∫ x : ℝ, phiDoobPrimeCross v n x) = 0 ∧
      (∫ x : ℝ, phiDoobPrimeJump v n x) = ∫ x : ℝ, phiDoobPrimeDiagonal v n x := by
  have hcross0 : (∫ x : ℝ, phiDoobPrimeCross v n x) = 0 := by
    have hcongr : (∫ x : ℝ, phiDoobPrimeCross v n x) = ∫ _ : ℝ, (0 : ℝ) :=
      integral_congr_ae (Eventually.of_forall fun x =>
        (phiDoobPrimeCross_and_jump_eq_of_support_Ioo hsupp hn x).1)
    rw [hcongr, integral_zero]
  refine ⟨hcross0, ?_⟩
  rw [integral_phiDoobPrimeJump_eq_diagonal_sub_cross hv hvc n, hcross0, sub_zero]

/-- On `(-log 2 / 2, log 2 / 2)`, `∫ x, phiDoobPrimeJump v n x = ∫ x, phiDoobPrimeDiagonal v n x`
holds for **every** `n : ℕ`. -/
theorem integral_phiDoobPrimeJump_eq_diagonal_of_support_half_log_two {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hsupp : ∀ x : ℝ, Real.log 2 / 2 ≤ |x| → v x = 0) (n : ℕ) :
    (∫ x : ℝ, phiDoobPrimeJump v n x) = ∫ x : ℝ, phiDoobPrimeDiagonal v n x := by
  have hsupp_Ioo : ∀ x ∉ Ioo (-(Real.log 2 / 2)) (Real.log 2 / 2), v x = 0 := by
    intro x hx
    apply hsupp x
    rw [mem_Ioo, ← abs_lt, not_lt] at hx
    exact hx
  by_cases hn2 : 2 ≤ n
  · have hlog : 2 * (Real.log 2 / 2) ≤ Real.log n := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith [Real.log_le_log h2pos hle]
    exact (integral_phiDoobPrimeJump_eq_diagonal_of_support_Ioo hv hvc hsupp_Ioo hlog).2
  · have hvan : vonMangoldtAtom n = 0 := by
      unfold vonMangoldtAtom
      rw [if_neg hn2]
    have hj : (∫ x : ℝ, phiDoobPrimeJump v n x) = 0 := by
      have h : phiDoobPrimeJump v n = fun _ => 0 := by
        funext x; unfold phiDoobPrimeJump; rw [hvan]; ring
      rw [h, integral_zero]
    have hd : (∫ x : ℝ, phiDoobPrimeDiagonal v n x) = 0 := by
      have h : phiDoobPrimeDiagonal v n = fun _ => 0 := by
        funext x; unfold phiDoobPrimeDiagonal; rw [hvan]; ring
      rw [h, integral_zero]
    rw [hj, hd]

/-- **Short-Support Prime-Doob Sum Theorem**:
if `v ∈ C²_c(ℝ)` vanishes on `|x| ≥ log 2 / 2`, then the prime Doob jump series equals the full
prime diagonal series `mixedPhiArchRe (Φ v²) + phiDoobCoshMass (v²)`:
`∑' n, ∫ x, phiDoobPrimeJump v n x = mixedPhiArchRe (Φ v²) + phiDoobCoshMass (fun x => v x ^ 2)`. -/
theorem tsum_integral_phiDoobPrimeJump_eq_mixedPhiArchRe_add_phiDoobCoshMass_of_support_half_log_two
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hsupp : ∀ x : ℝ, Real.log 2 / 2 ≤ |x| → v x = 0) :
    (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) =
      mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) +
        phiDoobCoshMass (fun x => v x ^ 2) := by
  have htsum_eq : (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) =
      ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeDiagonal v n x :=
    tsum_congr (integral_phiDoobPrimeJump_eq_diagonal_of_support_half_log_two hv.continuous hvc hsupp)
  have hdiag : (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeDiagonal v n x) =
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2))) := by
    unfold atomPairing
    exact tsum_congr fun n =>
      (vonMangoldtAtom_mul_crossCorr_mixed_eq_integral_phiDoobPrimeDiagonal hv.continuous hvc n).symm
  rw [htsum_eq, hdiag, phiDoob_mixed_prime_pairing_eq_mixedPhiArchRe_add_phiDoobCoshMass hv hvc]

/-- **Short-Support Doob Ground-State Identity for `markovEnergy (Φ v)`**:
when `v ∈ C²_c(ℝ)` vanishes on `|x| ≥ log 2 / 2`, the BPY second moment `phiDoobCoshMass (v²)`
cancels identically against the prime Doob jumps, leaving:
`markovEnergy (Φ v) = phiDoobArchJumpEnergy v + mixedPhiArchRe (Φ v²)`. -/
theorem phiDoob_markovEnergy_eq_archJump_add_mixedPhiArchRe_of_support_half_log_two
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hsupp : ∀ x : ℝ, Real.log 2 / 2 ≤ |x| → v x = 0) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      phiDoobArchJumpEnergy v + mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) := by
  rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc,
    tsum_integral_phiDoobPrimeJump_eq_mixedPhiArchRe_add_phiDoobCoshMass_of_support_half_log_two
      hv hvc hsupp]
  ring

/-! ## Section 2: Half-Line `(0, ∞)` Reflecting-Wall Escape at `t ≥ L` for Odd `v` -/

/-- If `v` vanishes on `Ici L` and `t ≥ L`, then for every `x > 0`, `v (x + t) = 0` and
`phiDoobArchShiftJump v t x = Φ(x) Φ(x + t) v(x)²`. -/
theorem phiDoobArchShiftJump_eq_diagonal_of_le_shift_of_pos {v : ℝ → ℝ} {L t x : ℝ}
    (hsupp : ∀ y : ℝ, L ≤ y → v y = 0) (ht : L ≤ t) (hx : 0 < x) :
    phiDoobArchShiftJump v t x =
      riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2 := by
  unfold phiDoobArchShiftJump
  have hxt : L ≤ x + t := by linarith
  rw [hsupp (x + t) hxt, sub_zero]

/-- **Half-Threshold Diagonalization on `(0, ∞)`**:
if `v` vanishes on `Ici L` and `t ≥ L`, then on the positive half-line `Ioi 0`, the Doob shift jump
integral is purely diagonal:
`∫ x in Ioi 0, phiDoobArchShiftJump v t x = ∫ x in Ioi 0, Φ(x) Φ(x + t) v(x)²`. -/
theorem integral_Ioi_phiDoobArchShiftJump_eq_diagonal_of_le_shift {v : ℝ → ℝ} {L t : ℝ}
    (hsupp : ∀ y : ℝ, L ≤ y → v y = 0) (ht : L ≤ t) :
    (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) =
      ∫ x in Ioi (0 : ℝ), riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  exact phiDoobArchShiftJump_eq_diagonal_of_le_shift_of_pos hsupp ht hx

/-- **Reflecting-Wall Half-Threshold Decomposition for Odd `v` at `t ≥ L`**:
if `v ∈ C_c(ℝ)` is odd (`v(-x) = -v(x)`) and vanishes for `x ≥ L` (`L ≥ 0`), then for every shift
`t ≥ L` (starting at `L`, half the full-line diameter `2 L`), the full-line Doob jump equals the
purely diagonal half-line integral `2 ∫_{x > 0} Φ(x) Φ(x + t) v(x)²` plus the nonnegative
origin-crossing sum-square collar `∫_{x ∈ (0, t)} Φ(x) Φ(t - x) (v(x) + v(t - x))²`:
`∫_ℝ phiDoobArchShiftJump v t x = 2 ∫_{x > 0} Φ(x) Φ(x + t) v(x)² + ∫_{x ∈ (0, t)} Φ(x) Φ(t - x) (v(x) + v(t - x))²`. -/
theorem integral_phiDoobArchShiftJump_eq_halfLine_diagonal_add_collar_of_odd {v : ℝ → ℝ}
    {L t : ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hsupp : ∀ y : ℝ, L ≤ y → v y = 0)
    (hL : 0 ≤ L) (ht : L ≤ t) :
    (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      2 * (∫ x in Ioi (0 : ℝ), riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) +
        ∫ x in Ioo (0 : ℝ) t,
          riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2 := by
  rw [integral_phiDoobArchShiftJump_eq_halfLine_of_odd hv hvc hodd (le_trans hL ht),
    integral_Ioi_phiDoobArchShiftJump_eq_diagonal_of_le_shift hsupp ht]

/-- Corollary: for any odd `v ∈ C_c(ℝ)` vanishing on `Ici L` (`L ≥ 0`) and any shift `t ≥ L`,
`2 * ∫ x in Ioi 0, Φ(x) Φ(x + t) v(x)² ≤ ∫ x : ℝ, phiDoobArchShiftJump v t x`. -/
theorem two_mul_integral_Ioi_diagonal_le_phiDoobArchShiftJump_of_odd {v : ℝ → ℝ}
    {L t : ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hsupp : ∀ y : ℝ, L ≤ y → v y = 0)
    (hL : 0 ≤ L) (ht : L ≤ t) :
    2 * (∫ x in Ioi (0 : ℝ), riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) ≤
      ∫ x : ℝ, phiDoobArchShiftJump v t x := by
  rw [← integral_Ioi_phiDoobArchShiftJump_eq_diagonal_of_le_shift hsupp ht]
  exact two_mul_integral_Ioi_phiDoobArchShiftJump_le_of_odd hv hvc hodd (le_trans hL ht)

/-- **Prime Reflecting-Wall Half-Threshold Decomposition for Odd `v` (`L ≤ log n`)**:
if `v ∈ C_c(ℝ)` is odd and vanishes on `Ici L` (`L ≥ 0`), then for every `n : ℕ` with `L ≤ log n`,
`∫_ℝ phiDoobPrimeJump v n x = 2 * vonMangoldtAtom n * ∫_{x > 0} Φ(x) Φ(x + log n) v(x)² + vonMangoldtAtom n * ∫_{x ∈ (0, log n)} Φ(x) Φ(log n - x) (v(x) + v(log n - x))²`. -/
theorem integral_phiDoobPrimeJump_eq_halfLine_diagonal_add_collar_of_odd {v : ℝ → ℝ}
    {L : ℝ} {n : ℕ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hsupp : ∀ y : ℝ, L ≤ y → v y = 0)
    (hL : 0 ≤ L) (hn : L ≤ Real.log n) :
    (∫ x : ℝ, phiDoobPrimeJump v n x) =
      2 * vonMangoldtAtom n *
          (∫ x in Ioi (0 : ℝ),
            riemannKernelReal x * riemannKernelReal (x + Real.log n) * v x ^ 2) +
        vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
          riemannKernelReal x * riemannKernelReal (Real.log n - x) *
            (v x + v (Real.log n - x)) ^ 2 := by
  have heq : phiDoobPrimeJump v n =
      fun x : ℝ => vonMangoldtAtom n * phiDoobArchShiftJump v (Real.log n) x := by
    funext x; unfold phiDoobPrimeJump phiDoobArchShiftJump; ring
  rw [heq, integral_const_mul,
    integral_phiDoobArchShiftJump_eq_halfLine_diagonal_add_collar_of_odd hv hvc hodd hsupp hL hn]
  ring

/-- **Full-First-Cell (`L = log 2`) Prime Half-Line Diagonalization for Odd `v`**:
if `v ∈ C_c(ℝ)` is odd and vanishes for `x ≥ log 2` (twice the half-log-2 radius of Section 1!),
then for **every** `n : ℕ`, the half-line prime jump is 100% diagonal and the only prime overlap is
the nonnegative origin-crossing sum-square collar on `(0, log n)`:
`∫_ℝ phiDoobPrimeJump v n x = 2 * vonMangoldtAtom n * ∫_{x > 0} Φ(x) Φ(x + log n) v(x)² + vonMangoldtAtom n * ∫_{x ∈ (0, log n)} Φ(x) Φ(log n - x) (v(x) + v(log n - x))²`. -/
theorem integral_phiDoobPrimeJump_eq_halfLine_diagonal_add_collar_of_support_log_two {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hsupp : ∀ y : ℝ, Real.log 2 ≤ y → v y = 0) (n : ℕ) :
    (∫ x : ℝ, phiDoobPrimeJump v n x) =
      2 * vonMangoldtAtom n *
          (∫ x in Ioi (0 : ℝ),
            riemannKernelReal x * riemannKernelReal (x + Real.log n) * v x ^ 2) +
        vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
          riemannKernelReal x * riemannKernelReal (Real.log n - x) *
            (v x + v (Real.log n - x)) ^ 2 := by
  by_cases hn2 : 2 ≤ n
  · have hlog : Real.log 2 ≤ Real.log n := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact Real.log_le_log h2pos hle
    exact integral_phiDoobPrimeJump_eq_halfLine_diagonal_add_collar_of_odd
      hv hvc hodd hsupp (Real.log_nonneg (by norm_num)) hlog
  · have hvan : vonMangoldtAtom n = 0 := by
      unfold vonMangoldtAtom; rw [if_neg hn2]
    have hj : (∫ x : ℝ, phiDoobPrimeJump v n x) = 0 := by
      have h : phiDoobPrimeJump v n = fun _ => 0 := by
        funext x; unfold phiDoobPrimeJump; rw [hvan]; ring
      rw [h, integral_zero]
    rw [hj, hvan]
    ring

/-! ## Section 3: Midpoint Reflection and Killing-Potential Decomposition of the Origin-Crossing Collar `(0, t)` -/

/-- The origin-crossing collar sum-square integrand on `(0, t)`:
`phiDoobCollarSumSq v t x = Φ(x) Φ(t - x) (v(x) + v(t - x))²`. -/
def phiDoobCollarSumSq (v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2

/-- The origin-crossing collar difference-square integrand on `(0, t)`:
`phiDoobCollarDiffSq v t x = Φ(x) Φ(t - x) (v(x) - v(t - x))²`. -/
def phiDoobCollarDiffSq (v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (t - x) * (v x - v (t - x)) ^ 2

/-- The origin-crossing collar Killing-potential density on `(0, t)`:
`phiDoobCollarKillingDensity v t x = 4 * Φ(x) Φ(t - x) v(x)²`. -/
def phiDoobCollarKillingDensity (v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  4 * riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2

/-- Pointwise parallelogram decomposition of the collar integrands:
`phiDoobCollarSumSq v t x + phiDoobCollarDiffSq v t x = 2 * Φ(x) Φ(t - x) (v(x)² + v(t - x)²)`. -/
theorem phiDoobCollarSumSq_add_diffSq (v : ℝ → ℝ) (t x : ℝ) :
    phiDoobCollarSumSq v t x + phiDoobCollarDiffSq v t x =
      2 * riemannKernelReal x * riemannKernelReal (t - x) * (v x ^ 2 + v (t - x) ^ 2) := by
  unfold phiDoobCollarSumSq phiDoobCollarDiffSq
  ring

/-- Reflection identity on `Ioo 0 t` under `x ↦ t - x`:
for any `f : ℝ → ℝ` and `t : ℝ`,
`∫ x in Ioo 0 t, f (t - x) = ∫ x in Ioo 0 t, f x`. -/
theorem setIntegral_Ioo_reflect_self (f : ℝ → ℝ) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, f (t - x)) = ∫ x in Ioo (0 : ℝ) t, f x := by
  have hpre : (fun x : ℝ => -x + t) ⁻¹' Ioo (0 : ℝ) t = Ioo (0 : ℝ) t := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have hmeas : MeasurableSet (Ioo (0 : ℝ) t) := measurableSet_Ioo
  have h1 := integral_add_right_eq_self (μ := volume)
    (fun z : ℝ => (Ioo (0 : ℝ) t).indicator f z) t
  have h2 := integral_neg_eq_self (μ := volume)
    (fun x : ℝ => (Ioo (0 : ℝ) t).indicator f (x + t))
  rw [← integral_indicator hmeas, ← integral_indicator hmeas, ← h1, ← h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← Set.indicator_comp_right (fun x : ℝ => -x + t), hpre]
  exact congrArg (fun g => (Ioo (0 : ℝ) t).indicator g x) (funext fun z => congrArg f (by ring))

/-- By reflection `x ↦ t - x` on `Ioo 0 t`,
`∫ x in Ioo 0 t, Φ(x) Φ(t - x) v(t - x)² = ∫ x in Ioo 0 t, Φ(x) Φ(t - x) v(x)²`. -/
theorem setIntegral_Ioo_collar_reflect_sq (v : ℝ → ℝ) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, riemannKernelReal x * riemannKernelReal (t - x) * v (t - x) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2 := by
  let g : ℝ → ℝ := fun x => riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2
  have hrefl := setIntegral_Ioo_reflect_self g t
  rw [← hrefl]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  dsimp [g]
  rw [show t - (t - x) = x by ring]
  ring

/-- **Exact Collar Killing-Potential Identity**:
for any continuous `v : ℝ → ℝ` and any shift `t : ℝ`,
`∫_{x ∈ (0, t)} phiDoobCollarSumSq v t x + ∫_{x ∈ (0, t)} phiDoobCollarDiffSq v t x = ∫_{x ∈ (0, t)} phiDoobCollarKillingDensity v t x`. -/
theorem integral_phiDoobCollarSumSq_add_diffSq_eq_killing {v : ℝ → ℝ}
    (hv : Continuous v) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, phiDoobCollarSumSq v t x) +
        (∫ x in Ioo (0 : ℝ) t, phiDoobCollarDiffSq v t x) =
      ∫ x in Ioo (0 : ℝ) t, phiDoobCollarKillingDensity v t x := by
  have hsum_int : IntegrableOn (phiDoobCollarSumSq v t) (Ioo (0 : ℝ) t) := by
    unfold phiDoobCollarSumSq
    exact (((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.add (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hdiff_int : IntegrableOn (phiDoobCollarDiffSq v t) (Ioo (0 : ℝ) t) := by
    unfold phiDoobCollarDiffSq
    exact (((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.sub (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have h1_int : IntegrableOn
      (fun x : ℝ => riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2) (Ioo (0 : ℝ) t) :=
    (((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      (hv.pow 2)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have h2_int : IntegrableOn
      (fun x : ℝ => riemannKernelReal x * riemannKernelReal (t - x) * v (t - x) ^ 2)
      (Ioo (0 : ℝ) t) :=
    (((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.comp (continuous_const.sub continuous_id)).pow 2)).continuousOn.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  rw [← integral_add hsum_int hdiff_int]
  have hcongr : (∫ x in Ioo (0 : ℝ) t, (phiDoobCollarSumSq v t x + phiDoobCollarDiffSq v t x)) =
      2 * ((∫ x in Ioo (0 : ℝ) t, riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2) +
        ∫ x in Ioo (0 : ℝ) t, riemannKernelReal x * riemannKernelReal (t - x) * v (t - x) ^ 2) := by
    rw [← integral_add h1_int h2_int, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    rw [phiDoobCollarSumSq_add_diffSq v t x]
    ring
  rw [hcongr, setIntegral_Ioo_collar_reflect_sq v t]
  unfold phiDoobCollarKillingDensity
  have hkill : (∫ x in Ioo (0 : ℝ) t,
      4 * riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2) =
      4 * ∫ x in Ioo (0 : ℝ) t, riemannKernelReal x * riemannKernelReal (t - x) * v x ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => by ring
  rw [hkill]
  ring

/-- On `x ∈ Ioo 0 (t / 2)`, `phiDoobCollarDiffSq v t x = phiDoobArchShiftJump v (t - 2 * x) x`. -/
theorem phiDoobCollarDiffSq_eq_phiDoobArchShiftJump (v : ℝ → ℝ) (t x : ℝ) :
    phiDoobCollarDiffSq v t x = phiDoobArchShiftJump v (t - 2 * x) x := by
  unfold phiDoobCollarDiffSq phiDoobArchShiftJump
  rw [show x + (t - 2 * x) = t - x by ring]

/-- Reflection identity across the midpoint `t / 2` on `Ioo 0 t`:
for any `f : ℝ → ℝ` and `t : ℝ`,
`∫ x in Ioo (t / 2) t, f x = ∫ x in Ioo 0 (t / 2), f (t - x)`. -/
theorem setIntegral_Ioo_reflect_midpoint (f : ℝ → ℝ) (t : ℝ) :
    (∫ x in Ioo (t / 2) t, f x) = ∫ x in Ioo (0 : ℝ) (t / 2), f (t - x) := by
  have hpre : (fun x : ℝ => -x + t) ⁻¹' Ioo (t / 2) t = Ioo (0 : ℝ) (t / 2) := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have hmeas : MeasurableSet (Ioo (t / 2) t) := measurableSet_Ioo
  have h1 := integral_add_right_eq_self (μ := volume)
    (fun z : ℝ => (Ioo (t / 2) t).indicator f z) t
  have h2 := integral_neg_eq_self (μ := volume)
    (fun x : ℝ => (Ioo (t / 2) t).indicator f (x + t))
  rw [← integral_indicator hmeas, ← h1, ← h2, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← Set.indicator_comp_right (fun x : ℝ => -x + t), hpre]
  exact congrArg (fun g => (Ioo (0 : ℝ) (t / 2)).indicator g x)
    (funext fun z => congrArg f (by ring))

/-- **Midpoint Folding of `phiDoobCollarSumSq` on `(0, t / 2)`**:
for any continuous `v : ℝ → ℝ` and `t ≥ 0`,
`∫ x in Ioo 0 t, phiDoobCollarSumSq v t x = 2 * ∫ x in Ioo 0 (t / 2), phiDoobCollarSumSq v t x`. -/
theorem integral_phiDoobCollarSumSq_eq_two_mul_half {v : ℝ → ℝ}
    (hv : Continuous v) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (0 : ℝ) t, phiDoobCollarSumSq v t x) =
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarSumSq v t x := by
  have hsum_int : IntegrableOn (phiDoobCollarSumSq v t) (Icc (0 : ℝ) t) := by
    unfold phiDoobCollarSumSq
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.add (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc
  have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioc (t / 2) t = Ioc (0 : ℝ) t :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioc (t / 2) t) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
    setIntegral_union hdisj measurableSet_Ioc
      (hsum_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
      (hsum_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    setIntegral_Ioo_reflect_midpoint (phiDoobCollarSumSq v t) t]
  have hrefl : (∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarSumSq v t (t - x)) =
      ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarSumSq v t x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    unfold phiDoobCollarSumSq
    rw [show t - (t - x) = x by ring]
    ring
  rw [hrefl]
  ring

/-- **Midpoint Folding of `phiDoobCollarDiffSq` into `phiDoobArchShiftJump` on `(0, t / 2)`**:
for any continuous `v : ℝ → ℝ` and `t ≥ 0`,
`∫ x in Ioo 0 t, phiDoobCollarDiffSq v t x = 2 * ∫ x in Ioo 0 (t / 2), phiDoobArchShiftJump v (t - 2 * x) x`. -/
theorem integral_phiDoobCollarDiffSq_eq_two_mul_half {v : ℝ → ℝ}
    (hv : Continuous v) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (0 : ℝ) t, phiDoobCollarDiffSq v t x) =
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobArchShiftJump v (t - 2 * x) x := by
  have hdiff_int : IntegrableOn (phiDoobCollarDiffSq v t) (Icc (0 : ℝ) t) := by
    unfold phiDoobCollarDiffSq
    exact ((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      ((hv.sub (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc
  have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioc (t / 2) t = Ioc (0 : ℝ) t :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioc (t / 2) t) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  rw [← integral_Ioc_eq_integral_Ioo, ← hunion,
    setIntegral_union hdisj measurableSet_Ioc
      (hdiff_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
      (hdiff_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl))),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    setIntegral_Ioo_reflect_midpoint (phiDoobCollarDiffSq v t) t]
  have hrefl : (∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarDiffSq v t (t - x)) =
      ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarDiffSq v t x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    unfold phiDoobCollarDiffSq
    rw [show t - (t - x) = x by ring]
    ring
  rw [hrefl]
  have hcongr : (∫ x in Ioo (0 : ℝ) (t / 2), phiDoobCollarDiffSq v t x) =
      ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobArchShiftJump v (t - 2 * x) x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      phiDoobCollarDiffSq_eq_phiDoobArchShiftJump v t x
  rw [hcongr]
  ring

/-- **Exact Shift-by-Shift Half-Line Killing-Potential + Dirichlet Decomposition for Odd `v`**:
for any odd continuous compactly supported `v : ℝ → ℝ` and any shift `t ≥ 0`,
`∫_ℝ phiDoobArchShiftJump v t x = (∫_{x ∈ (0, t)} 4 Φ(x) Φ(t - x) v(x)²) + 2 (∫_{x > 0} phiDoobArchShiftJump v t x) - 2 (∫_{x ∈ (0, t / 2)} phiDoobArchShiftJump v (t - 2 * x) x)`. -/
theorem integral_phiDoobArchShiftJump_eq_killing_add_halfLine_sub_collarDiff_of_odd {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      (∫ x in Ioo (0 : ℝ) t, phiDoobCollarKillingDensity v t x) +
        2 * (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) -
        2 * ∫ x in Ioo (0 : ℝ) (t / 2), phiDoobArchShiftJump v (t - 2 * x) x := by
  have h1 := integral_phiDoobArchShiftJump_eq_halfLine_of_odd hv hvc hodd ht
  have h2 := integral_phiDoobCollarSumSq_add_diffSq_eq_killing hv t
  have h3 := integral_phiDoobCollarDiffSq_eq_two_mul_half hv ht
  change (∫ x : ℝ, phiDoobArchShiftJump v t x) =
    2 * (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) +
      ∫ x in Ioo (0 : ℝ) t, phiDoobCollarSumSq v t x at h1
  linarith

/-! ## Section 4: Strict Antitonicity of `archLevyDensity` and the Reflected Archimedean Dirichlet + Killing Potential Decomposition on `(0, ∞)` -/

/-- **Fundamental Reflected Dirichlet + Killing Potential Identity**:
for any weights `wMinus wPlus : ℝ` and any `a b : ℝ`,
`wMinus * (a - b) ^ 2 + wPlus * (a + b) ^ 2 = (wMinus - wPlus) * (a - b) ^ 2 + 2 * wPlus * (a ^ 2 + b ^ 2)`. -/
theorem reflected_dirichlet_killing_pointwise (wMinus wPlus a b : ℝ) :
    wMinus * (a - b) ^ 2 + wPlus * (a + b) ^ 2 =
      (wMinus - wPlus) * (a - b) ^ 2 + 2 * wPlus * (a ^ 2 + b ^ 2) := by
  ring

/-- `archLevyDensity` is strictly antitone on `(0, ∞)`:
if `0 < a` and `a < b`, then `archLevyDensity b < archLevyDensity a`. -/
theorem strictAntiOn_archLevyDensity : StrictAntiOn archLevyDensity (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  unfold archLevyDensity
  have hden_a : 0 < 1 - Real.exp (-2 * a) := by
    linarith [Real.exp_lt_one_iff.mpr (by linarith : -2 * a < 0)]
  have hden_b : 0 < 1 - Real.exp (-2 * b) := by
    linarith [Real.exp_lt_one_iff.mpr (by linarith : -2 * b < 0)]
  have hden_lt : 1 - Real.exp (-2 * a) < 1 - Real.exp (-2 * b) := by
    have hexp : Real.exp (-2 * b) < Real.exp (-2 * a) :=
      Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hnum_lt : Real.exp (-b / 2) < Real.exp (-a / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hnum_b_pos : 0 < Real.exp (-b / 2) := Real.exp_pos _
  calc
    Real.exp (-b / 2) / (1 - Real.exp (-2 * b)) <
        Real.exp (-b / 2) / (1 - Real.exp (-2 * a)) :=
      div_lt_div_of_pos_left hnum_b_pos hden_a hden_lt
    _ < Real.exp (-a / 2) / (1 - Real.exp (-2 * a)) :=
      div_lt_div_of_pos_right hnum_lt hden_a

/-- The reflected (Dirichlet-boundary) archimedean jump weight at position `x > 0` and shift `s > 0`:
`reflectedArchLevyWeight x s = archLevyDensity s - archLevyDensity (s + 2 * x)`. -/
def reflectedArchLevyWeight (x s : ℝ) : ℝ :=
  archLevyDensity s - archLevyDensity (s + 2 * x)

/-- For every `x > 0` and `s > 0`, `0 < reflectedArchLevyWeight x s`. -/
theorem reflectedArchLevyWeight_pos {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    0 < reflectedArchLevyWeight x s := by
  unfold reflectedArchLevyWeight
  have hs2x : s ∈ Ioi (0 : ℝ) := hs
  have hs2x' : s + 2 * x ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have hlt : s < s + 2 * x := by linarith
  exact sub_pos.mpr (strictAntiOn_archLevyDensity hs2x hs2x' hlt)

/-- **Pointwise Reflected Archimedean Jump + Killing Potential Identity**:
for any `v : ℝ → ℝ` and any `x s : ℝ`, pairing the intra-half-line jump at shift `s` with the
origin-crossing collar jump at shift `t = s + 2 * x` yields:
`2 * ω(s) * phiDoobArchShiftJump v s x + 2 * ω(s + 2 * x) * Φ(x) Φ(x + s) (v(x) + v(x + s))² = 2 * reflectedArchLevyWeight x s * phiDoobArchShiftJump v s x + 4 * ω(s + 2 * x) * Φ(x) Φ(x + s) (v(x)² + v(x + s)²)`. -/
theorem archLevy_reflected_jump_add_collar_eq (v : ℝ → ℝ) (x s : ℝ) :
    2 * archLevyDensity s * phiDoobArchShiftJump v s x +
        2 * archLevyDensity (s + 2 * x) *
          (riemannKernelReal x * riemannKernelReal (x + s) * (v x + v (x + s)) ^ 2) =
      2 * reflectedArchLevyWeight x s * phiDoobArchShiftJump v s x +
        4 * archLevyDensity (s + 2 * x) * riemannKernelReal x * riemannKernelReal (x + s) *
          (v x ^ 2 + v (x + s) ^ 2) := by
  unfold reflectedArchLevyWeight phiDoobArchShiftJump
  ring

/-- Nonnegativity of the reflected archimedean Dirichlet jump term on `x > 0, s > 0`. -/
theorem reflectedArchLevy_dirichlet_term_nonneg (v : ℝ → ℝ) {x s : ℝ}
    (hx : 0 < x) (hs : 0 < s) :
    0 ≤ 2 * reflectedArchLevyWeight x s * phiDoobArchShiftJump v s x := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (reflectedArchLevyWeight_pos hx hs).le)
    (phiDoobArchShiftJump_nonneg v s x)

/-- Nonnegativity of the reflected archimedean Killing-potential term on `x > 0, s ≥ 0`. -/
theorem reflectedArchLevy_killing_term_nonneg (v : ℝ → ℝ) {x s : ℝ}
    (hx : 0 < x) (hs : 0 ≤ s) :
    0 ≤ 4 * archLevyDensity (s + 2 * x) * riemannKernelReal x * riemannKernelReal (x + s) *
      (v x ^ 2 + v (x + s) ^ 2) := by
  have hs2x : 0 < s + 2 * x := by linarith
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (archLevyDensity_pos hs2x).le)
        (riemannKernelReal_pos x).le)
      (riemannKernelReal_pos (x + s)).le)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Pointwise lower bound: for any `x > 0` and `s > 0`, the combined intra-half-line +
origin-crossing archimedean jump dominates the reflected Killing potential
`4 * ω(s + 2 * x) * Φ(x) Φ(x + s) (v(x)² + v(x + s)²)`. -/
theorem reflectedArchLevy_killing_term_le_jump_add_collar (v : ℝ → ℝ) {x s : ℝ}
    (hx : 0 < x) (hs : 0 < s) :
    4 * archLevyDensity (s + 2 * x) * riemannKernelReal x * riemannKernelReal (x + s) *
        (v x ^ 2 + v (x + s) ^ 2) ≤
      2 * archLevyDensity s * phiDoobArchShiftJump v s x +
        2 * archLevyDensity (s + 2 * x) *
          (riemannKernelReal x * riemannKernelReal (x + s) * (v x + v (x + s)) ^ 2) := by
  rw [archLevy_reflected_jump_add_collar_eq]
  linarith [reflectedArchLevy_dirichlet_term_nonneg v hx hs]

end RHTower

end
