import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiHellingerGammaGradedVerticalObstruction
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetCompletedHellingerGammaIncidenceBridge

/-!
# Physical-jet-normalized Hellinger--Gamma vertical relation

The first nonzero Möbius--theta source jet canonically normalizes every completed
Hellinger--Gamma depth vertex to boundary charge one.  Adjacent depth cofaces are
therefore exact kernel vectors.  Nevertheless factorial Hellinger damping sends
the corresponding graded vertices to zero, so the algebraic graph has the
nonzero vertical limit `(0, 1)` and cannot be closed.

This is the concrete source-level obstruction to closing the Hodge marginal by
itself.  Any conservative Green descent must retain additional physical source
provenance in a joint carrier before taking graph closure.
-/

open Complex Set Finset Filter Topology

namespace RHTower

noncomputable section

namespace CompletedXiHellingerGammaPureHodgeCoface

open PrimitivePromotedHellingerGammaPureHodgeCoface

/-- Algebraic finite-depth tests before Hilbert completion. -/
abbrev HellingerGammaPureHodgeXiDepthTest
    (p q : Nat.Primes) (hpq : p ≠ q) :=
  ℕ →₀ HellingerGammaPureHodgeXiCofaceCompletion p q hpq

/-- Canonical grade-preserving inclusion of finite-depth tests in the `ℓ²` completion. -/
def hellingerGammaCompletedDepthTestToCompletion
    (p q : Nat.Primes) (hpq : p ≠ q) :
    HellingerGammaPureHodgeXiDepthTest p q hpq →ₗ[ℂ]
      HellingerGammaPureHodgeXiDepthCompletion p q hpq :=
  Finsupp.lsum ℂ fun n =>
    lp.lsingle
      (E := fun _ : ℕ => HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
      2 n

@[simp] theorem hellingerGammaCompletedDepthTestToCompletion_single
    (p q : Nat.Primes) (hpq : p ≠ q) (n : ℕ)
    (z : HellingerGammaPureHodgeXiCofaceCompletion p q hpq) :
    hellingerGammaCompletedDepthTestToCompletion p q hpq
        (Finsupp.single n z) = lp.single 2 n z := by
  simp [hellingerGammaCompletedDepthTestToCompletion]

@[simp] theorem hellingerGammaCompletedDepthTestToCompletion_apply
    (p q : Nat.Primes) (hpq : p ≠ q)
    (z : HellingerGammaPureHodgeXiDepthTest p q hpq) (n : ℕ) :
    hellingerGammaCompletedDepthTestToCompletion p q hpq z n = z n := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add i x z hi hx ih =>
      rw [map_add, hellingerGammaCompletedDepthTestToCompletion_single]
      simp [ih, Finsupp.single_apply, Pi.single, Function.update, eq_comm]

/-- Grade-`n` boundary normalized by the nonzero first physical source jet. -/
def thetaInternalJetHellingerGammaNormalizedHeadBoundary
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    HellingerGammaPureHodgeXiCofaceCompletion p q hpq →ₗ[ℂ] ℂ where
  toFun z :=
    (((hellingerGammaGaugedModularCoefficient (-a) p q n : ℂ) *
      thetaInternalJetLeadingSourceCoefficient rho)⁻¹) *
      deningerCalderonWittCrossPrimeXiIncidenceCompletionCoefficient
        p q hpq (thetaInternalJetLeadingZeroCopy rho) z.1
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- Finite-depth normalized boundary, summed over the retained Hellinger grades. -/
def thetaInternalJetHellingerGammaNormalizedDepthBoundary
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) :
    HellingerGammaPureHodgeXiDepthTest p q hpq →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun n =>
    thetaInternalJetHellingerGammaNormalizedHeadBoundary p q hpq a rho n

/-- Every physical-leading balanced depth vertex has normalized charge one. -/
theorem thetaInternalJetHellingerGammaNormalizedHeadBoundary_balanced
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    thetaInternalJetHellingerGammaNormalizedHeadBoundary p q hpq a rho n
        (hellingerGammaCompletedBalancedPrimitive hpq a n
          (thetaInternalJetLeadingCompletedIncidence p q hpq rho)) = 1 := by
  have hc : thetaInternalJetLeadingSourceCoefficient rho ≠ 0 :=
    thetaInternalJetLeadingSourceCoefficient_ne_zero rho
  have hg : (hellingerGammaGaugedModularCoefficient (-a) p q n : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr <|
      mul_ne_zero (hellingerEvenGammaResidueGauge_ne_zero n) (Real.exp_ne_zero _)
  change
    (((hellingerGammaGaugedModularCoefficient (-a) p q n : ℂ) *
      thetaInternalJetLeadingSourceCoefficient rho)⁻¹) *
        deningerCalderonWittCrossPrimeXiIncidenceCompletionCoefficient
          p q hpq (thetaInternalJetLeadingZeroCopy rho)
          ((hellingerGammaGaugedModularCoefficient (-a) p q n : ℂ) •
            thetaInternalJetLeadingCompletedIncidence p q hpq rho) = 1
  rw [map_smul, thetaInternalJetLeadingCompletedIncidence_coefficient]
  exact inv_mul_cancel₀ (mul_ne_zero hg hc)

/-- The global finite-depth boundary sends every normalized vertex to one. -/
theorem thetaInternalJetHellingerGammaNormalizedDepthBoundary_vertex
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    thetaInternalJetHellingerGammaNormalizedDepthBoundary p q hpq a rho
        (Finsupp.single n
          (hellingerGammaCompletedBalancedPrimitive hpq a n
            (thetaInternalJetLeadingCompletedIncidence p q hpq rho))) = 1 := by
  simp [thetaInternalJetHellingerGammaNormalizedDepthBoundary,
    thetaInternalJetHellingerGammaNormalizedHeadBoundary_balanced]

/-- Adjacent normalized Hellinger depth countertransport. -/
def thetaInternalJetHellingerGammaNormalizedDepthCoface
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    HellingerGammaPureHodgeXiDepthTest p q hpq :=
  Finsupp.single (n + 1)
      (hellingerGammaCompletedBalancedPrimitive hpq a (n + 1)
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho)) -
    Finsupp.single n
      (hellingerGammaCompletedBalancedPrimitive hpq a n
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho))

/-- Adjacent depth cofaces lie in the exact kernel of the normalized boundary. -/
theorem thetaInternalJetHellingerGammaNormalizedDepthBoundary_coface
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) (n : ℕ) :
    thetaInternalJetHellingerGammaNormalizedDepthBoundary p q hpq a rho
        (thetaInternalJetHellingerGammaNormalizedDepthCoface
          p q hpq a rho n) = 0 := by
  rw [thetaInternalJetHellingerGammaNormalizedDepthCoface, map_sub,
    thetaInternalJetHellingerGammaNormalizedDepthBoundary_vertex,
    thetaInternalJetHellingerGammaNormalizedDepthBoundary_vertex, sub_self]

/-- Algebraic graph of the physical-leading normalized boundary inside completion. -/
def thetaInternalJetHellingerGammaNormalizedBoundaryGraph
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) :
    Set (HellingerGammaPureHodgeXiDepthCompletion p q hpq × ℂ) :=
  Set.range fun z : HellingerGammaPureHodgeXiDepthTest p q hpq =>
    (hellingerGammaCompletedDepthTestToCompletion p q hpq z,
      thetaInternalJetHellingerGammaNormalizedDepthBoundary p q hpq a rho z)

/-- The normalized graph closure contains the nonzero vertical charge `(0, 1)`. -/
theorem thetaInternalJetHellingerGammaNormalizedBoundary_vertical_mem_closure
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) :
    ((0 : HellingerGammaPureHodgeXiDepthCompletion p q hpq), 1) ∈
      closure (thetaInternalJetHellingerGammaNormalizedBoundaryGraph
        p q hpq a rho) := by
  let z : ℕ → HellingerGammaPureHodgeXiDepthTest p q hpq := fun n =>
    Finsupp.single n
      (hellingerGammaCompletedBalancedPrimitive hpq a n
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho))
  have hfirst : Tendsto
      (fun n => hellingerGammaCompletedDepthTestToCompletion p q hpq (z n))
      atTop (𝓝 0) := by
    simpa [z, hellingerGammaCompletedGradedBalancedVertex] using
      (hellingerGammaCompletedGradedBalancedVertex_tendsto_zero hpq a
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho))
  have hsecond : Tendsto
      (fun n => thetaInternalJetHellingerGammaNormalizedDepthBoundary
        p q hpq a rho (z n)) atTop (𝓝 1) := by
    simp [z, thetaInternalJetHellingerGammaNormalizedDepthBoundary_vertex]
  apply mem_closure_of_tendsto (hfirst.prodMk_nhds hsecond)
  filter_upwards with n
  exact ⟨z n, rfl⟩

/-- The physical-leading normalized Hodge-marginal graph is not closed. -/
theorem thetaInternalJetHellingerGammaNormalizedBoundaryGraph_not_isClosed
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) :
    ¬ IsClosed (thetaInternalJetHellingerGammaNormalizedBoundaryGraph
      p q hpq a rho) := by
  intro hclosed
  have hmem := thetaInternalJetHellingerGammaNormalizedBoundary_vertical_mem_closure
    p q hpq a rho
  rw [hclosed.closure_eq] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz0 : hellingerGammaCompletedDepthTestToCompletion p q hpq z = 0 :=
    congrArg Prod.fst hz
  have hinj : Function.Injective
      (hellingerGammaCompletedDepthTestToCompletion p q hpq) := by
    intro u v huv
    apply Finsupp.ext
    intro n
    have h := congrArg
      (fun w : HellingerGammaPureHodgeXiDepthCompletion p q hpq => w n) huv
    simpa using h
  have zzero : z = 0 := hinj (by simpa using hz0)
  have hone : (0 : ℂ) = 1 := by
    simpa [zzero] using congrArg Prod.snd hz
  exact zero_ne_one hone

end CompletedXiHellingerGammaPureHodgeCoface

end

end RHTower
