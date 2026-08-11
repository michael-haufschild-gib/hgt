import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution

/-!
# Source formation and harmonic refinement mechanics

The normalized Möbius ladder has a literal one-dimensional incidence geometry on every prime
exponent ray.  Adjacent source channels are oriented edges, consecutive edges conserve their
endpoint boundary, and a marked anchor together with edge responses reconstructs the full finite
history.

For real responses, refinement energy splits into endpoint energy and a nonnegative centered
excess.  On a prime radial character the first two-edge excess is a fourth power, so it vanishes
exactly at exponent zero.  These statements separate source generation, reconstruction, conserved
boundary response, and harmonic criticality inside one unconditional mechanism.
-/

open scoped BigOperators Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ArithmeticFunction
open scoped Moebius
open _root_.RHTower

/-- Oriented unit edge from exponent vertex `m` to exponent vertex `m + 1`. -/
def primeExponentEdge (m e : ℕ) : ℤ :=
  if e = m then 1 else if e = m + 1 then -1 else 0

/-- Dirac atom at one exponent vertex. -/
def exponentVertexAtom (m e : ℕ) : ℤ :=
  if e = m then 1 else 0

/-- Every exponent edge is the boundary difference of its two endpoint atoms. -/
theorem primeExponentEdge_eq_boundary (m e : ℕ) :
    primeExponentEdge m e = exponentVertexAtom m e - exponentVertexAtom (m + 1) e := by
  simp only [primeExponentEdge, exponentVertexAtom]
  by_cases hem : e = m
  · simp [hem]
  by_cases hems : e = m + 1
  · simp [hems]
  · simp [hem, hems]

/-- **Source-edge conservation.**  A consecutive block of fine exponent edges has exactly the
boundary of the coarse edge joining its two endpoints. -/
theorem sum_primeExponentEdge (m r e : ℕ) :
    ∑ j ∈ Finset.range r, primeExponentEdge (m + j) e =
      exponentVertexAtom m e - exponentVertexAtom (m + r) e := by
  simp_rw [primeExponentEdge_eq_boundary]
  have htel := Finset.sum_range_sub (fun j => exponentVertexAtom (m + j) e) r
  calc
    ∑ j ∈ Finset.range r,
        (exponentVertexAtom (m + j) e - exponentVertexAtom (m + j + 1) e) =
        -(∑ j ∈ Finset.range r,
          (exponentVertexAtom (m + j + 1) e - exponentVertexAtom (m + j) e)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            abel
    _ = -(exponentVertexAtom (m + r) e - exponentVertexAtom m e) := by
          simpa [Nat.add_assoc] using congrArg Neg.neg htel
    _ = exponentVertexAtom m e - exponentVertexAtom (m + r) e := by abel

/-- The difference of consecutive power-dilated Möbius channels is literally one exponent edge
on every prime-power ray. -/
theorem adjacent_mPart_moebius_apply_prime_pow
    {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (e : ℕ) :
    (mPart (m + 1) (μ : ArithmeticFunction ℤ) -
        mPart m (μ : ArithmeticFunction ℤ)) (p ^ e) =
      primeExponentEdge m e := by
  change mPart (m + 1) (μ : ArithmeticFunction ℤ) (p ^ e) -
      mPart m (μ : ArithmeticFunction ℤ) (p ^ e) = primeExponentEdge m e
  rw [mPart_moebius_apply_prime_pow (by omega : m + 1 ≠ 0) hp,
    mPart_moebius_apply_prime_pow hm hp]
  simp only [primeExponentEdge]
  by_cases he0 : e = 0
  · simp [he0, hm, Ne.symm hm]
  by_cases hem : e = m
  · simp [hem, hm]
  by_cases hems : e = m + 1
  · simp [hems, hm]
  · simp [he0, hem, hems]

/-- Every positive complete-resolution channel is a source-generated exponent edge on prime
powers. -/
theorem completeResolutionNormalizedArithmetic_prime_edge
    {K p : ℕ} (hK : K ≠ 0) (hp : p.Prime) (j e : ℕ) :
    completeResolutionNormalizedArithmetic K (j + 1) (p ^ e) =
      primeExponentEdge (K + j) e := by
  rw [completeResolutionNormalizedArithmetic]
  exact adjacent_mPart_moebius_apply_prime_pow (by omega) hp e

/-- At the canonical shell depth `12`, the literal finite-abscissa source has exactly the
prime-exponent edge coefficients.  This is the coefficient-level bridge from the arithmetic
resolution to the formation geometry. -/
theorem rankTwelveFiniteAbscissaSource_prime_edge
    {p : ℕ} (hp : p.Prime) (j e : ℕ) :
    (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1 (p ^ e) =
      (primeExponentEdge (12 + j) e : ℂ) := by
  rw [completeResolutionNormalizedFiniteAbscissaSource_val (by omega : 12 ≠ 0)]
  exact congrArg (fun x : ℤ => (x : ℂ))
    (completeResolutionNormalizedArithmetic_prime_edge
      (by omega : 12 ≠ 0) hp j e)

/-- **Source-native hypertranscendental formation.**  The faithful analytic realizations of the
literal normalized finite-abscissa sources at depth `12` have maximal countable differential rank
over the full zeta differential field.  Hypertranscendence therefore belongs to the generated
source-channel family itself, not to a chosen phase orbit. -/
theorem rankTwelveFiniteAbscissaSource_relativeDifferentialIndependent :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun j => finiteAbscissaLSeriesToUpperEndMero
        (completeResolutionNormalizedFiniteAbscissaSource 12 j)) := by
  have heq :
      (fun j => finiteAbscissaLSeriesToUpperEndMero
        (completeResolutionNormalizedFiniteAbscissaSource 12 j)) =
        completeResolutionUpperEndMultiplier 12 := by
    funext j
    exact (completeResolutionUpperEndMultiplier_eq_source 12 j).symm
  rw [heq]
  exact completeResolutionUpperEndMultiplier_relativeDifferentialIndependent 12 (by omega)

/-- **Joint reconstruction.**  One marked vertex and all consecutive edge responses reconstruct
the terminal value of every finite history in an additive group. -/
theorem marked_edge_reconstruction
    {A : Type*} [AddCommGroup A] (u : ℕ → A) (m r : ℕ) :
    u m + ∑ j ∈ Finset.range r, (u (m + j + 1) - u (m + j)) = u (m + r) := by
  have htel := Finset.sum_range_sub (fun j => u (m + j)) r
  simpa [Nat.add_assoc] using congrArg (fun z => u m + z) htel

/-- Mean response of a finite refinement block. -/
def refinementMean (d : ℕ → ℝ) (r : ℕ) : ℝ :=
  (r : ℝ)⁻¹ * ∑ j ∈ Finset.range r, d j

/-- **Refinement-energy conservation.**  Fine energy is coarse endpoint energy plus centered
fluctuation energy.  The second term is the exact nonharmonic refinement excess. -/
theorem refinement_energy_pythagoras
    (d : ℕ → ℝ) {r : ℕ} (hr : r ≠ 0) :
    ∑ j ∈ Finset.range r, (d j) ^ 2 =
      (∑ j ∈ Finset.range r, d j) ^ 2 / r +
        ∑ j ∈ Finset.range r, (d j - refinementMean d r) ^ 2 := by
  let S : ℝ := ∑ j ∈ Finset.range r, d j
  let a : ℝ := refinementMean d r
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hsum_centered : ∑ j ∈ Finset.range r, (d j - a) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp only [a, refinementMean, S]
    field_simp
    ring
  have ha : a = S / r := by
    dsimp only [a, refinementMean, S]
    rw [inv_mul_eq_div]
  have hexpand :
      ∑ j ∈ Finset.range r, (d j) ^ 2 =
        ∑ j ∈ Finset.range r, (d j - a) ^ 2 + (r : ℝ) * a ^ 2 := by
    calc
      ∑ j ∈ Finset.range r, (d j) ^ 2 =
          ∑ j ∈ Finset.range r, ((d j - a) + a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j ∈ Finset.range r, ((d j - a) ^ 2 + 2 * a * (d j - a) + a ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j ∈ Finset.range r, (d j - a) ^ 2 +
          2 * a * (∑ j ∈ Finset.range r, (d j - a)) + (r : ℝ) * a ^ 2 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ j ∈ Finset.range r, (d j - a) ^ 2 + (r : ℝ) * a ^ 2 := by
            rw [hsum_centered]
            ring
  change ∑ j ∈ Finset.range r, (d j) ^ 2 =
      S ^ 2 / r + ∑ j ∈ Finset.range r, (d j - a) ^ 2
  have hscalar : (r : ℝ) * (S / r) ^ 2 = S ^ 2 / r := by
    field_simp
  rw [hexpand, ha, hscalar]
  ring

/-- At two edges, nonharmonic energy is the square of the discrete Laplacian. -/
theorem twoEdge_refinement_energy_identity (u₀ u₁ u₂ : ℝ) :
    2 * ((u₁ - u₀) ^ 2 + (u₂ - u₁) ^ 2) - (u₂ - u₀) ^ 2 =
      (2 * u₁ - u₀ - u₂) ^ 2 := by
  ring

/-- A geometric response has fourth-power two-edge refinement excess. -/
theorem geometric_twoEdge_refinement_energy (q : ℝ) :
    2 * ((q - 1) ^ 2 + (q ^ 2 - q) ^ 2) - (q ^ 2 - 1) ^ 2 =
      (q - 1) ^ 4 := by
  ring

/-- Geometric two-edge refinement is harmonic exactly at the trivial character. -/
theorem geometric_twoEdge_refinement_energy_eq_zero_iff
    {q : ℝ} :
    2 * ((q - 1) ^ 2 + (q ^ 2 - q) ^ 2) - (q ^ 2 - 1) ^ 2 = 0 ↔
      q = 1 := by
  rw [geometric_twoEdge_refinement_energy]
  rw [pow_eq_zero_iff (by omega : 4 ≠ 0), sub_eq_zero]

/-- **Prime-radial criticality.**  For every prime base, the source-generated two-edge
refinement excess vanishes exactly at radial exponent zero. -/
theorem primeRadial_twoEdge_refinement_energy_eq_zero_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} :
    2 * ((((p : ℝ) ^ ν) - 1) ^ 2 +
        (((p : ℝ) ^ ν) ^ 2 - ((p : ℝ) ^ ν)) ^ 2) -
        (((p : ℝ) ^ ν) ^ 2 - 1) ^ 2 = 0 ↔ ν = 0 := by
  rw [geometric_twoEdge_refinement_energy_eq_zero_iff]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  simpa using (Real.rpow_right_inj hp0 hp1 (y := ν) (z := 0))

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators
open _root_.RHTower

/-! ## Polar character execution and recurrent variation history -/

/-- Coherent evaluation of one source exponent edge by a complex character. -/
def complexCharacterEdge (z : ℂ) (m : ℕ) : ℂ :=
  z ^ m - z ^ (m + 1)

/-- Character execution of the two marked coefficients of a source edge is exactly the coherent
edge response. -/
theorem primeExponentEdge_character_execution (z : ℂ) (m : ℕ) :
    (primeExponentEdge m m : ℂ) * z ^ m +
        (primeExponentEdge m (m + 1) : ℂ) * z ^ (m + 1) =
      complexCharacterEdge z m := by
  simp [primeExponentEdge, complexCharacterEdge]
  ring

/-- **Literal arithmetic-to-coherent fusion.**  Evaluating the two nonzero prime-power
coefficients of one normalized source channel by a complex exponent character gives the coherent
formation edge. -/
theorem rankTwelveSource_character_execution
    {p : ℕ} (hp : p.Prime) (z : ℂ) (j : ℕ) :
    (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
          (p ^ (12 + j)) * z ^ (12 + j) +
        (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
          (p ^ (12 + j + 1)) * z ^ (12 + j + 1) =
      complexCharacterEdge z (12 + j) := by
  rw [rankTwelveFiniteAbscissaSource_prime_edge hp,
    rankTwelveFiniteAbscissaSource_prime_edge hp]
  exact primeExponentEdge_character_execution z (12 + j)

/-- Successive coherent edge responses form a geometric progression. -/
theorem complexCharacterEdge_succ (z : ℂ) (m : ℕ) :
    complexCharacterEdge z (m + 1) = z * complexCharacterEdge z m := by
  simp only [complexCharacterEdge, pow_succ]
  ring

/-- **Character reconstruction.**  Any nonzero adjacent response pair recovers the full complex
character, including both its radial and phase coordinates. -/
theorem complexCharacterEdge_ratio
    (z : ℂ) (m : ℕ) (h : complexCharacterEdge z m ≠ 0) :
    complexCharacterEdge z (m + 1) / complexCharacterEdge z m = z := by
  rw [complexCharacterEdge_succ, div_eq_iff h]

/-- Coherent execution of a fine edge block is exactly its two-endpoint response. -/
theorem sum_complexCharacterEdge (z : ℂ) (m r : ℕ) :
    ∑ j ∈ Finset.range r, complexCharacterEdge z (m + j) =
      z ^ m - z ^ (m + r) := by
  simp only [complexCharacterEdge]
  have htel := Finset.sum_range_sub (fun j => z ^ (m + j)) r
  calc
    ∑ j ∈ Finset.range r, (z ^ (m + j) - z ^ (m + j + 1)) =
        -(∑ j ∈ Finset.range r, (z ^ (m + j + 1) - z ^ (m + j))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = -(z ^ (m + r) - z ^ m) := by
          simpa [Nat.add_assoc] using congrArg Neg.neg htel
    _ = z ^ m - z ^ (m + r) := by ring

/-- Positive variation execution retains the norm of every generated edge before cancellation. -/
def complexCharacterVariation (z : ℂ) (m r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, ‖complexCharacterEdge z (m + j)‖

/-- Every edge of the parity character has positive variation mass two. -/
theorem norm_complexCharacterEdge_neg_one (m : ℕ) :
    ‖complexCharacterEdge (-1) m‖ = 2 := by
  rw [complexCharacterEdge]
  simp [pow_succ]
  rw [← two_mul, norm_mul]
  simp

/-- Positive history of the parity character grows linearly with refinement depth. -/
theorem complexCharacterVariation_neg_one (m r : ℕ) :
    complexCharacterVariation (-1) m r = 2 * r := by
  simp [complexCharacterVariation, norm_complexCharacterEdge_neg_one]
  ring

/-- **Recurrent-shadow/open-history law.**  Every even parity block closes coherently while its
source-marked positive variation is `4n`. -/
theorem sum_complexCharacterEdge_neg_one_even (m n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), complexCharacterEdge (-1) (m + j) = 0 := by
  rw [sum_complexCharacterEdge]
  rw [show m + 2 * n = m + (2 * n) by rfl, pow_add]
  simp [pow_mul]

/-- **Polar criticality.**  After phase quotient, two-edge harmonic refinement vanishes exactly
when the complex character lies on the unit circle. -/
theorem complexCharacter_radial_energy_eq_zero_iff {z : ℂ} :
    2 * ((‖z‖ - 1) ^ 2 + (‖z‖ ^ 2 - ‖z‖) ^ 2) -
        (‖z‖ ^ 2 - 1) ^ 2 = 0 ↔ ‖z‖ = 1 := by
  exact geometric_twoEdge_refinement_energy_eq_zero_iff

/-! ## Bilateral reflection-formation admission -/

/-- Unweighted forward edge-energy density of a positive radial character. -/
def geometricRefinementEnergy (q : ℝ) (n : ℕ) : ℝ :=
  (q ^ (n + 1) - q ^ n) ^ 2

/-- Radial edge energy is a geometric progression with ratio `q²`. -/
theorem geometricRefinementEnergy_eq (q : ℝ) (n : ℕ) :
    geometricRefinementEnergy q n = (q - 1) ^ 2 * (q ^ 2) ^ n := by
  simp only [geometricRefinementEnergy, pow_succ]
  ring

/-- **One-sided formation admission.**  A nonnegative radial history has summable unweighted
edge energy exactly on the closed subunit interval. -/
theorem summable_geometricRefinementEnergy_iff {q : ℝ} (hq : 0 ≤ q) :
    Summable (geometricRefinementEnergy q) ↔ q ≤ 1 := by
  by_cases hq1 : q = 1
  · subst q
    constructor
    · intro _
      norm_num
    · intro _
      convert (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) using 1
      funext n
      simp [geometricRefinementEnergy]
  · have hc : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hq1)
    change Summable (fun n => geometricRefinementEnergy q n) ↔ q ≤ 1
    simp_rw [geometricRefinementEnergy_eq]
    rw [summable_mul_left_iff hc, summable_geometric_iff_norm_lt_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    constructor <;> intro h
    · nlinarith [sq_nonneg (q - 1)]
    · have hlt : q < 1 := lt_of_le_of_ne h hq1
      nlinarith [mul_nonneg hq hq]

/-- **Bilateral reflection-formation selection.**  A positive radial history and its reciprocal
reflection both have summable unweighted source-edge energy exactly at the unitary character. -/
theorem bilateral_geometricRefinementEnergy_summable_iff {q : ℝ} (hq : 0 < q) :
    (Summable (geometricRefinementEnergy q) ∧
        Summable (geometricRefinementEnergy q⁻¹)) ↔ q = 1 := by
  rw [summable_geometricRefinementEnergy_iff hq.le,
    summable_geometricRefinementEnergy_iff (inv_nonneg.mpr hq.le), inv_le_one₀ hq]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- Prime-radial bilateral admission selects exactly zero real drift. -/
theorem primeRadial_bilateral_geometricRefinementEnergy_summable_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} :
    (Summable (geometricRefinementEnergy ((p : ℝ) ^ ν)) ∧
        Summable (geometricRefinementEnergy (((p : ℝ) ^ ν)⁻¹))) ↔ ν = 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  rw [bilateral_geometricRefinementEnergy_summable_iff (Real.rpow_pos_of_pos hp0 ν)]
  simpa using (Real.rpow_right_inj hp0 hp1 (y := ν) (z := 0))

/-- **Closed five-shadow fusion certificate.**  One literal depth-`12` source simultaneously has
maximal differential formation rank, prime-exponent incidence, coherent character execution,
polar harmonic criticality, and recurrent coherent closure with open positive history.  Every
clause is universally quantified inside one premise-free proposition. -/
theorem rankTwelve_fiveShadow_fusion_certificate :
    DifferentialIndependent zetaUpperEndDifferentialField
        (fun j => finiteAbscissaLSeriesToUpperEndMero
          (completeResolutionNormalizedFiniteAbscissaSource 12 j)) ∧
      (∀ p : ℕ, p.Prime → ∀ j e : ℕ,
        (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1 (p ^ e) =
          (primeExponentEdge (12 + j) e : ℂ)) ∧
      (∀ p : ℕ, p.Prime → ∀ z : ℂ, ∀ j : ℕ,
        (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
              (p ^ (12 + j)) * z ^ (12 + j) +
            (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
              (p ^ (12 + j + 1)) * z ^ (12 + j + 1) =
          complexCharacterEdge z (12 + j)) ∧
      (∀ z : ℂ,
        (2 * ((‖z‖ - 1) ^ 2 + (‖z‖ ^ 2 - ‖z‖) ^ 2) -
            (‖z‖ ^ 2 - 1) ^ 2 = 0 ↔ ‖z‖ = 1)) ∧
      (∀ m n : ℕ,
        (∑ j ∈ Finset.range (2 * n), complexCharacterEdge (-1) (m + j) = 0) ∧
          complexCharacterVariation (-1) m (2 * n) = 4 * n) := by
  refine ⟨rankTwelveFiniteAbscissaSource_relativeDifferentialIndependent, ?_, ?_, ?_, ?_⟩
  · intro p hp j e
    exact rankTwelveFiniteAbscissaSource_prime_edge hp j e
  · intro p hp z j
    exact rankTwelveSource_character_execution hp z j
  · intro z
    exact complexCharacter_radial_energy_eq_zero_iff
  · intro m n
    refine ⟨sum_complexCharacterEdge_neg_one_even m n, ?_⟩
    rw [complexCharacterVariation_neg_one]
    norm_num [Nat.cast_mul]
    ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The physical prime receiver on the critical line -/

/-- **(FF.19).**  The physical receiver's two-edge refinement excess is the fourth power of its
radial defect. -/
theorem primeReceiver_twoEdge_refinement_energy (p : ℕ) (ρ : ℂ) :
    2 * ((((p : ℝ) ^ (2 * ρ.re - 1)) - 1) ^ 2 +
        (((p : ℝ) ^ (2 * ρ.re - 1)) ^ 2 - ((p : ℝ) ^ (2 * ρ.re - 1))) ^ 2) -
        (((p : ℝ) ^ (2 * ρ.re - 1)) ^ 2 - 1) ^ 2
      = (((p : ℝ) ^ (2 * ρ.re - 1)) - 1) ^ 4 :=
  geometric_twoEdge_refinement_energy _

/-- **(FF.20).**  For every prime base the physical receiver's two-edge refinement excess vanishes
exactly on the critical line.  This is a receiver classification, not a zero-location theorem: it
says nothing about which `ρ` are admitted. -/
theorem primeReceiver_twoEdge_refinement_energy_eq_zero_iff
    {p : ℕ} (hp : p.Prime) {ρ : ℂ} :
    2 * ((((p : ℝ) ^ (2 * ρ.re - 1)) - 1) ^ 2 +
        (((p : ℝ) ^ (2 * ρ.re - 1)) ^ 2 - ((p : ℝ) ^ (2 * ρ.re - 1))) ^ 2) -
        (((p : ℝ) ^ (2 * ρ.re - 1)) ^ 2 - 1) ^ 2 = 0 ↔ ρ.re = 1 / 2 := by
  rw [primeRadial_twoEdge_refinement_energy_eq_zero_iff hp]
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions.HTGeometry
