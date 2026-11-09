import GaloisForLFunctions.ArithmeticWeightTheory.TheBaireGenericFibreCarriesThePole
import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier

/-!
# The vertical Frobenius is equidistributed

Deligne's equidistribution theorem places the Frobenius classes of a family in its monodromy group
with Haar law. For the gauge family the special fibre `ζ` moves along the archimedean line
`x_t = (p^{it})_p`, and its window trace at `x_t` is the spline-smoothed prime sum of `ζ` at height
`t`. This file proves the corresponding law: at every fixed degree the vertical Frobenius classes
of `ζ` are distributed exactly as the Frobenius of the generic fibre.

**Theorem** (`tendsto_verticalAverage_fibreTrace`). For every continuous `φ : ℂ → ℂ`, window and
degree,

  `(1/2T) ∫_{−T}^{T} φ(T_{x_t}(u)) dt → ∫ φ(T_x(u)) dx`  as `T → ∞`.

**Proof.** The window trace reads finitely many prime coordinates, so it factors through the
restriction `G → (ℝ/ℤ)^{primes}`, a continuous surjective homomorphism of compact groups and hence
measure preserving (`measurePreserving_primeRestrict`). On the prime torus the frequencies `log p`
are rationally independent, and the Kronecker flow is uniquely ergodic
(`HTGeometry.hasHaarTimeAverage_of_continuous`).

Together with the Gaussian law of the generic fibre (`TheGenericFrobeniusIsGaussian`) this is the
Sato–Tate law of `ζ`'s vertical family at each fixed degree. The specialization it provides is in
law only: a single height, and a single zero, has measure zero.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry

/-- Reading the prime coordinates of a point of the gauge torus. -/
def primeRestrict : GaugeTorus →+ UnitAddTorus Nat.Primes where
  toFun x := fun p => x p
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_primeRestrict : Continuous primeRestrict :=
  continuous_pi fun p => continuous_apply (p : ℕ)

theorem surjective_primeRestrict : Function.Surjective primeRestrict := by
  classical
  intro y
  refine ⟨fun n => if h : n.Prime then y ⟨n, h⟩ else 0, ?_⟩
  funext p
  simp [primeRestrict, p.2]

/-- **The prime restriction is measure preserving.** -/
theorem measurePreserving_primeRestrict :
    MeasurePreserving primeRestrict gaugeHaar (HTGeometry.torusHaar Nat.Primes) :=
  primeRestrict.measurePreserving continuous_primeRestrict surjective_primeRestrict (by simp)

/-- A continuous observable of a finite prime window: `y ↦ φ(Σ_{p ∈ W} c_p e(y_p))`. -/
def windowObservable (φ : C(ℂ, ℂ)) (W : Finset ℕ) (c : ℕ → ℂ) : C(UnitAddTorus Nat.Primes, ℂ) :=
  ⟨fun y => φ (∑ p ∈ W.subtype Nat.Prime, c p * fourier 1 (y p)),
    φ.continuous.comp (continuous_finsetSum _ fun p _ =>
      continuous_const.mul ((fourier 1).continuous.comp (continuous_apply p)))⟩

/-- The observable read at the prime restriction of a fibre is `φ` of its twisted window sum. -/
theorem windowObservable_primeRestrict (φ : C(ℂ, ℂ)) {W : Finset ℕ} (hW : ∀ n ∈ W, n.Prime)
    (c : ℕ → ℂ) (x : GaugeTorus) :
    windowObservable φ W c (primeRestrict x) = φ (twistSum W c x) := by
  classical
  show φ (∑ p ∈ W.subtype Nat.Prime, c p * fourier 1 (x p)) = φ (∑ n ∈ W, c n * twist x n)
  congr 1
  rw [Finset.sum_subtype_eq_sum_filter (f := fun n => c n * fourier 1 (x n)),
    Finset.filter_true_of_mem hW]
  exact Finset.sum_congr rfl fun n hn => by rw [twist_eq_fourier_of_prime x (hW n hn)]

/-- The archimedean line restricts to the prime Kronecker flow. -/
theorem primeRestrict_clockPhasePoint (t : ℝ) :
    primeRestrict (HTGeometry.clockPhasePoint (fun n : ℕ => Real.log n) t) =
      HTGeometry.clockPhasePoint (fun p : Nat.Primes => Real.log (p : ℕ)) t := rfl

/-- **Equidistribution of the vertical Frobenius of a finite window.** -/
theorem tendsto_verticalAverage_twistSum (φ : C(ℂ, ℂ)) {W : Finset ℕ} (hW : ∀ n ∈ W, n.Prime)
    (c : ℕ → ℂ) :
    Tendsto (fun T : ℝ => (2 * T : ℂ)⁻¹ *
        ∫ t in -T..T, φ (twistSum W c (HTGeometry.clockPhasePoint (fun n : ℕ => Real.log n) t)))
      atTop (𝓝 (∫ x, φ (twistSum W c x) ∂gaugeHaar)) := by
  have hindep : HTGeometry.RationallyIndependentSequence (fun p : Nat.Primes => Real.log (p : ℕ)) :=
    HTGeometry.rationallyIndependentSequence_of_linearIndependent_int logPrime_linearIndependent_int
  have h := HTGeometry.hasHaarTimeAverage_of_continuous hindep (windowObservable φ W c)
  unfold HTGeometry.HasHaarTimeAverage HTGeometry.flowAverage at h
  -- the Haar integral on the prime torus pulls back to the gauge torus
  have hint : ∫ y, windowObservable φ W c y ∂(HTGeometry.torusHaar Nat.Primes) =
      ∫ x, φ (twistSum W c x) ∂gaugeHaar := by
    rw [← measurePreserving_primeRestrict.map_eq,
      integral_map continuous_primeRestrict.measurable.aemeasurable
        (windowObservable φ W c).continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun x => windowObservable_primeRestrict φ hW c x)
  rw [hint] at h
  refine h.congr fun T => ?_
  congr 2
  funext t
  rw [← primeRestrict_clockPhasePoint, windowObservable_primeRestrict φ hW c]

/-- **The vertical Frobenius of `ζ` has the generic law at every degree.** -/
theorem tendsto_verticalAverage_fibreTrace (φ : C(ℂ, ℂ)) (g : ℝ → ℝ) (R u : ℝ) :
    Tendsto (fun T : ℝ => (2 * T : ℂ)⁻¹ *
        ∫ t in -T..T, φ (fibreTrace g R u (HTGeometry.clockPhasePoint (fun n : ℕ => Real.log n) t)))
      atTop (𝓝 (∫ x, φ (fibreTrace g R u x) ∂gaugeHaar)) :=
  tendsto_verticalAverage_twistSum φ (fun _ hn => (Nat.mem_primesLE.mp hn).2) (windowWeight g u)

end GaloisForLFunctions.ArithmeticWeightTheory
