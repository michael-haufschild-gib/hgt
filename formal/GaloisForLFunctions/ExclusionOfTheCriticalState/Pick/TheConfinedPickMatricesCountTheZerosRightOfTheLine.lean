import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesDecideTheCriticalRatio
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShortWindowsInheritThePolarization
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# The confined Pick matrices count the zeros right of the line

The real Pick matrix of the confined form on nodes `p_i > 4` is
`(Q_R(e_{p_i}, e_{p_j})) = (K(p_i, p_j)) + a(R) (1/(p_i + p_j − 8))`: the bare probe kernel plus `a(R)` times
the Gram matrix of the probes in `L²(e^{−8u})` (`confinedProbeGram_eq`).

* **Monotone and bounded** (`hermNegIndex_confinedProbeGram_mono`, `hermNegIndex_confinedProbeGram_le`).
  The number of negative squares grows with the ratio and never exceeds the number of zeros of `ζ`
  right of the critical line.
* **The confined probe index law** (`confinedProbeIndex_law`). On a uniqueness set of nodes `> 4` (the
  integers `≥ 7`), some ratio and some real Pick matrix of `Q_R` carry `n` negative squares iff `ζ` has
  at least `n` zeros right of the line: as `R → ∞` the matrices converge to the bare probe kernel,
  whose index is the zero count (`probeIndex_law`), and the index is lower semicontinuous.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower HeckeKreinToeplitz

/-- The real Pick matrix of the confined form on the nodes `p`. -/
def confinedProbeGram (R : ℝ) {N : ℕ} (p : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (criticalHalfLineMixedEnergy R (probe (p i)) (probe (p j)) : ℂ)

/-- The Gram matrix `(1/(p_i + p_j − 8))` of the probes in `L²(e^{−8u})`. -/
def probeConfinementGram {N : ℕ} (p : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((1 / (p i + p j - 8) : ℝ) : ℂ)

theorem confinedProbeGram_eq (R : ℝ) {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k) :
    confinedProbeGram R p =
      probeGram p + ((criticalAliasCoefficient R : ℝ) : ℂ) • probeConfinementGram p := by
  ext i j
  have hh : ∀ k, (1 / 2 : ℝ) < p k := fun k => by linarith [hp k]
  simp only [confinedProbeGram, probeGram, probeConfinementGram, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [criticalHalfLineMixedEnergy_probe R (hp i) (hp j), bareMixedEnergy_probe (hh i) (hh j)]
  push_cast
  ring

/-- On real vectors the Hermitian form of a real matrix is the real quadratic form. -/
theorem hermQuad_ofReal_eq {N : ℕ} (g : Fin N → Fin N → ℝ) (c : Fin N → ℝ) :
    hermQuad (fun i j => (g i j : ℂ)) (fun i => (c i : ℂ)) = ∑ i, ∑ j, c i * g i j * c j := by
  simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The confinement Gram matrix is positive semidefinite. -/
theorem hermQuad_probeConfinementGram_nonneg {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k)
    (x : Fin N → ℂ) : 0 ≤ hermQuad (probeConfinementGram p) x := by
  have hreal : ∀ c : Fin N → ℝ, 0 ≤ hermQuad (probeConfinementGram p) (fun i => (c i : ℂ)) := by
    intro c
    rw [show probeConfinementGram p = fun i j => ((1 / (p i + p j - 8) : ℝ) : ℂ) from rfl,
      hermQuad_ofReal_eq]
    have h := sum_div_eq_integral_probeSum_sq hp c
    have hI : 0 ≤ ∫ u in Iio (0 : ℝ), probeSum p c u ^ 2 * Real.exp (-(8 * u)) :=
      setIntegral_nonneg measurableSet_Iio fun u _ => by positivity
    have e : ∑ i, ∑ j, c i * (1 / (p i + p j - 8)) * c j =
        ∑ i, ∑ j, c i * c j / (p i + p j - 8) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h]
    exact hI
  rw [hermQuad_eq_re_add_im (G := probeConfinementGram p) (fun i j => Complex.ofReal_im _)]
  exact add_nonneg (hreal _) (hreal _)

/-- The confined form dominates the bare kernel. -/
theorem hermQuad_probeGram_le_confinedProbeGram {R : ℝ} (hR : 0 < R) {N : ℕ} {p : Fin N → ℝ}
    (hp : ∀ k, 4 < p k) (x : Fin N → ℂ) :
    hermQuad (probeGram p) x ≤ hermQuad (confinedProbeGram R p) x := by
  rw [confinedProbeGram_eq R hp, hermQuad_add_smul]
  have := hermQuad_probeConfinementGram_nonneg hp x
  have ha := (criticalAliasCoefficient_positive hR).le
  nlinarith

/-- **Bounded by the zeros.** At every ratio the confined Pick matrix has at most as many negative
squares as `ζ` has zeros right of the line. -/
theorem hermNegIndex_confinedProbeGram_le {R : ℝ} (hR : 0 < R) {N : ℕ} {p : Fin N → ℝ}
    (hp : ∀ k, 4 < p k) :
    (hermNegIndex (confinedProbeGram R p) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard :=
  (ENat.coe_le_coe.mpr (hermNegIndex_le_of_hermQuad_le _ _
    (hermQuad_probeGram_le_confinedProbeGram hR hp))).trans
    (hermNegIndex_probeGram_le fun k => by linarith [hp k])

/-- **Monotone in the ratio.** -/
theorem hermNegIndex_confinedProbeGram_mono {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) {N : ℕ}
    {p : Fin N → ℝ} (hp : ∀ k, 4 < p k) :
    hermNegIndex (confinedProbeGram R p) ≤ hermNegIndex (confinedProbeGram S p) := by
  refine hermNegIndex_le_of_hermQuad_le _ _ fun x => ?_
  rw [confinedProbeGram_eq R hp, confinedProbeGram_eq S hp, hermQuad_add_smul, hermQuad_add_smul]
  have := hermQuad_probeConfinementGram_nonneg hp x
  have ha := criticalAliasCoefficient_antitone hR hRS
  nlinarith

theorem probeGram_isHermitian {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 / 2 < p k) :
    (probeGram p).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, probeGram, Complex.star_def, Complex.conj_ofReal]
  rw [bareMixedEnergy_probe_symm (hp j) (hp i)]

/-- **The confined probe index law.** On a uniqueness set of nodes `> 4`, some ratio and some real Pick
matrix of the confined form carry `n` negative squares iff `ζ` has at least `n` zeros right of the
critical line. -/
theorem confinedProbeIndex_law {S : Set ℝ} (hS4 : ∀ p ∈ S, 4 < p)
    (hU : IsRightProbeUniquenessSet S) (n : ℕ) :
    (∃ (R : ℝ) (_ : 0 < R) (N : ℕ) (p : Fin N → ℝ), (∀ i, p i ∈ S) ∧
        n ≤ hermNegIndex (confinedProbeGram R p)) ↔
      (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  constructor
  · rintro ⟨R, hR, N, p, hpS, hn⟩
    exact (ENat.coe_le_coe.mpr hn).trans
      (hermNegIndex_confinedProbeGram_le hR fun i => hS4 _ (hpS i))
  · intro hn
    obtain ⟨N, p, hpS, hpn⟩ := (probeIndex_law (fun q hq => by linarith [hS4 q hq]) hU n).mpr hn
    have hp4 : ∀ k, 4 < p k := fun k => hS4 _ (hpS k)
    have hconv : ∀ i j, Tendsto (fun R => confinedProbeGram R p i j) atTop
        (𝓝 (probeGram p i j)) := by
      intro i j
      have h := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_criticalAliasCoefficient_atTop).mul_const
        (probeConfinementGram p i j)
      rw [Complex.ofReal_zero, zero_mul] at h
      have h2 := h.const_add (probeGram p i j)
      rw [add_zero] at h2
      refine h2.congr' (Eventually.of_forall fun R => ?_)
      show probeGram p i j + ((criticalAliasCoefficient R : ℝ) : ℂ) * probeConfinementGram p i j =
        confinedProbeGram R p i j
      rw [confinedProbeGram_eq R hp4]
      rfl
    have hev := eventually_le_hermNegIndex
      (probeGram_isHermitian fun k => by linarith [hp4 k]) hconv
    obtain ⟨R, hR⟩ := (hev.and (eventually_gt_atTop 0)).exists
    exact ⟨R, hR.2, N, p, hpS, hpn.trans hR.1⟩

#print axioms confinedProbeIndex_law
#print axioms hermNegIndex_confinedProbeGram_mono

end GaloisForLFunctions.ExclusionOfTheCriticalState
