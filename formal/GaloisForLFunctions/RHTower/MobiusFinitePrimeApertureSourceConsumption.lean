import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion

/-!
# Finite-prime aperture source consumption for the Möbius route

A finite Euler head is not an independent source of additive Möbius cancellation at its matching
resolution.  Once its aperture contains every prime through `N`, it already contains every prime
factor of every positive integer through `N`.  Its Möbius coefficients, Mertens partial sums, and
Mertens antidiagonal at `N` therefore agree exactly with the full source.

The final classification identifies the canonical cofinal-aperture `N^(2+o(1))` upper law with the
existing second-Cesàro source law.  It does not prove that open upper law; it proves that finite
Euler truncation cannot supply it without consuming the exact RH-strength source.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The canonical finite aperture containing every natural prime at most `N`. -/
def mobiusFinitePrimeAperture (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- Möbius coefficient retained exactly when all its prime factors lie in the finite aperture. -/
def finitePrimeApertureMobiusCoefficient
    (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n.primeFactors ⊆ S then mobiusComplexCoefficient n else 0

/-- Mertens partial sum formed from one finite-prime Euler aperture. -/
def finitePrimeApertureMobiusMertensPartialSum
    (S : Finset ℕ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), finitePrimeApertureMobiusCoefficient S n

/-- Additive self-convolution of finite-aperture Mertens partial sums. -/
def finitePrimeApertureMobiusMertensSelfConvolution
    (S : Finset ℕ) (N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    finitePrimeApertureMobiusMertensPartialSum S ab.1 *
      finitePrimeApertureMobiusMertensPartialSum S ab.2

/-- Covering every prime through `N` recovers each Möbius coefficient through `N`. -/
theorem finitePrimeApertureMobiusCoefficient_eq_of_covers
    {S : Finset ℕ} {N n : ℕ}
    (hcover : mobiusFinitePrimeAperture N ⊆ S) (hn : n ≤ N) :
    finitePrimeApertureMobiusCoefficient S n =
      mobiusComplexCoefficient n := by
  by_cases hn0 : n = 0
  · subst n
    simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  · rw [finitePrimeApertureMobiusCoefficient, if_pos]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpPrime, hpDvd, _hn0⟩ := hp
    have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd
    apply hcover
    rw [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpPrime⟩

/-- Prime coverage through `N` recovers every aperture partial sum with cutoff at most `N`. -/
theorem finitePrimeApertureMobiusMertensPartialSum_eq_of_covers
    {S : Finset ℕ} {N k : ℕ}
    (hcover : mobiusFinitePrimeAperture N ⊆ S) (hk : k ≤ N) :
    finitePrimeApertureMobiusMertensPartialSum S k =
      mobiusMertensPartialSum k := by
  rw [finitePrimeApertureMobiusMertensPartialSum, mobiusMertensPartialSum]
  apply Finset.sum_congr rfl
  intro n hn
  apply finitePrimeApertureMobiusCoefficient_eq_of_covers hcover
  rw [Finset.mem_range] at hn
  omega

/-- **Finite-prime aperture source-consumption law.**  Every aperture containing all primes
through additive resolution `N` gives the exact full Mertens self-convolution at `N`. -/
theorem finitePrimeApertureMobiusMertensSelfConvolution_eq_of_covers
    {S : Finset ℕ} {N : ℕ}
    (hcover : mobiusFinitePrimeAperture N ⊆ S) :
    finitePrimeApertureMobiusMertensSelfConvolution S N =
      mobiusMertensSelfConvolution N := by
  rw [finitePrimeApertureMobiusMertensSelfConvolution,
    mobiusMertensSelfConvolution]
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 = N :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [finitePrimeApertureMobiusMertensPartialSum_eq_of_covers hcover (by omega),
    finitePrimeApertureMobiusMertensPartialSum_eq_of_covers hcover (by omega)]

/-- At matching resolution, the canonical finite-prime aperture is exactly the twice-cumulative
additive Möbius triangle, not an approximation to it. -/
theorem canonicalFinitePrimeApertureMobiusMertensSelfConvolution_eq_secondCesaro
    (N : ℕ) :
    finitePrimeApertureMobiusMertensSelfConvolution
        (mobiusFinitePrimeAperture N) N =
      mobiusAdditiveTriangleSecondCesaro N := by
  rw [finitePrimeApertureMobiusMertensSelfConvolution_eq_of_covers
    (S := mobiusFinitePrimeAperture N) (N := N) (by exact Finset.Subset.rfl)]
  exact (mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution N).symm

/-- Canonical finite-prime-aperture formulation of the one-sided `N^(2+o(1))` source law. -/
def CanonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (finitePrimeApertureMobiusMertensSelfConvolution
      (mobiusFinitePrimeAperture N) N).re ≤
        C * ((N : ℝ) + 1) ^ (2 + ε)

/-- **Exact source classification.**  The canonical finite-Euler upper law is identical to the
open second-Cesàro Möbius source law; cofinal aperture growth supplies no additional averaging
parameter at matching resolution. -/
theorem canonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound_iff :
    CanonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound ↔
      MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    exact ⟨C, hC, fun N => by
      rw [← canonicalFinitePrimeApertureMobiusMertensSelfConvolution_eq_secondCesaro]
      exact hbound N⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    exact ⟨C, hC, fun N => by
      rw [canonicalFinitePrimeApertureMobiusMertensSelfConvolution_eq_secondCesaro]
      exact hbound N⟩

/-- Any proof of the canonical finite-prime-aperture upper law is already a proof of the exact
RH-strength second-Cesàro source law and therefore proves RH. -/
theorem canonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
    (hupper : CanonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
    (canonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound_iff.mp hupper)

end

end RHTower
