import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import GaloisForLFunctions.HTGeometry.PolynomialRelationDetector
import GaloisForLFunctions.HTGeometry.PrimeLogCauchyJetControllability
import GaloisForLFunctions.HTGeometry.PrimeLogGaugePerturbation
import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetPacket
import GaloisForLFunctions.HTGeometry.JetFactorialScale

/-!
# Positive polynomial escape for prime-log Herglotz jets

The prime-log Cauchy control map is surjective on every finite upper-half-plane jet packet.
Consequently every nonzero algebraic relation on such a packet can be broken by an arbitrarily
small finitely supported change of prime masses while all masses remain strictly positive.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Every fixed nonzero polynomial relation on a finite upper-half-plane Cauchy-jet packet is
locally escapable from every positive prime mass configuration. -/
theorem primeLogPositiveCauchyJet_escapes_mvPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (weight : Nat.Primes → ℝ) (hweight : ∀ p, 0 < weight p)
    (baseJet : (Σ i, Fin (orders i)) → ℂ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < weight p + ε * a p) ∧
      MvPolynomial.eval
        (baseJet + ε • cauchyJetRealLinearCombination nodes orders primeLogSupport a) P ≠ 0 := by
  exact surjective_positive_control_escapes_mvPolynomial
    (cauchyJetRealLinearCombination nodes orders primeLogSupport)
    (primeLogCauchyJetRealLinearCombination_surjective nodes hnodes hupper orders)
    weight hweight baseJet P hP hη

/-- The positive polynomial escape law for the actual dyadic prime masses of an arbitrary gauge. -/
theorem primeDyadicCauchyJet_escapes_mvPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (baseJet : (Σ i, Fin (orders i)) → ℂ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < primeDyadicWeight u p + ε * a p) ∧
      MvPolynomial.eval
        (baseJet + ε • cauchyJetRealLinearCombination nodes orders primeLogSupport a) P ≠ 0 := by
  exact primeLogPositiveCauchyJet_escapes_mvPolynomial nodes hnodes hupper orders
    (primeDyadicWeight u) (primeDyadicWeight_pos u) baseJet P hP hη

/-- Polynomial escape can be performed inside the space of bounded logarithmic gauges.  The new
gauge differs from the old one at only finitely many primes and represents the perturbed masses
exactly. -/
theorem primeDyadicCauchyJet_escapes_mvPolynomial_in_boundedGauge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (baseJet : (Σ i, Fin (orders i)) → ℂ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (baseJet + ε • cauchyJetRealLinearCombination nodes orders primeLogSupport a) P ≠ 0 := by
  obtain ⟨a, ε, hε, hεη, hpos, hescape⟩ :=
    primeDyadicCauchyJet_escapes_mvPolynomial nodes hnodes hupper orders u
      baseJet P hP hη
  obtain ⟨C', hC'⟩ := primeLogPerturbedGauge_bounded u a ε C hu
  refine ⟨a, ε, C', hε, hεη, ?_, hC', ?_,
    primeLogPerturbedGauge_changeSet_finite u a ε, hescape⟩
  · simpa [primeLogPerturbedMass] using hpos
  · intro p
    rw [primeDyadicWeight_perturbedGauge u a ε (by
      simpa [primeLogPerturbedMass] using hpos) p]
    rfl

/-- **Gauge-ball polynomial escape.** The escaping bounded gauge can be chosen uniformly as close
as prescribed to the original gauge at every prime coordinate. -/
theorem primeDyadicCauchyJet_escapes_mvPolynomial_in_gaugeBall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (baseJet : (Σ i, Fin (orders i)) → ℂ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (baseJet + ε • cauchyJetRealLinearCombination nodes orders primeLogSupport a) P ≠ 0 := by
  let L := cauchyJetRealLinearCombination nodes orders primeLogSupport
  obtain ⟨y, hy⟩ := exists_mvPolynomial_eval_ne_zero hP
  obtain ⟨a, ha⟩ :=
    (primeLogCauchyJetRealLinearCombination_surjective nodes hnodes hupper orders) (y - baseJet)
  obtain ⟨ρ, hρ, hρη, hρpos⟩ :=
    exists_small_positive_finsupp_perturbation
      (primeDyadicWeight u) (primeDyadicWeight_pos u) a hηTime
  obtain ⟨δ, hδ, hδgauge⟩ := primeLogPerturbedGauge_uniformly_small u a hηGauge
  obtain ⟨ε, hε, hεmin, hescape⟩ :=
    exists_small_real_line_eval_ne_zero P baseJet y hy (lt_min hρ hδ)
  have hερ : ε ≤ ρ := (hεmin.trans_le (min_le_left _ _)).le
  have hεδ : |ε| < δ := by
    rw [abs_of_pos hε]
    exact hεmin.trans_le (min_le_right _ _)
  have hpos : ∀ p, 0 < primeDyadicWeight u p + ε * a p :=
    positive_finsupp_perturbation_of_le
      (primeDyadicWeight u) (primeDyadicWeight_pos u) a hε.le hερ hρpos
  obtain ⟨C', hC'⟩ := primeLogPerturbedGauge_bounded u a ε C hu
  refine ⟨a, ε, C', hε, (hεmin.trans_le (min_le_left _ _)).trans hρη,
    ?_, hδgauge ε hεδ, hC', ?_, primeLogPerturbedGauge_changeSet_finite u a ε, ?_⟩
  · simpa [primeLogPerturbedMass] using hpos
  · intro p
    rw [primeDyadicWeight_perturbedGauge u a ε (by
      simpa [primeLogPerturbedMass] using hpos) p]
    rfl
  · have hcoord : baseJet + ε • L a =
        fun i => baseJet i + (ε : ℂ) * (y i - baseJet i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [show L a = y - baseJet by exact ha]
      simp
    rw [show cauchyJetRealLinearCombination nodes orders primeLogSupport = L by rfl]
    rw [hcoord]
    exact hescape

/-- **Polynomial-coefficient relation detector and escape.** Every nonzero polynomial relation in
a coefficient variable and finitely many translated jet variables has a nonzero detector at a
packet of distinct upper-half-plane nodes, and that detector can be escaped inside every bounded
prime-log gauge ball. -/
theorem primeDyadic_polynomialCoefficientRelation_has_gaugeBall_escape
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (baseJet : (Σ i, Fin (orders i)) → ℂ)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) (hQ : Q ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ z : ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun i => z + shift i) ∧
      (∀ i, 0 < (z + shift i).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (baseJet + ε • cauchyJetRealLinearCombination
          (fun i => z + shift i) orders primeLogSupport a)
        (specializePolynomialCoefficients z Q) ≠ 0 := by
  obtain ⟨z, hP, hnodes, hupper⟩ :=
    exists_upper_noncolliding_polynomial_detector shift hshift Q hQ
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hescape⟩ :=
    primeDyadicCauchyJet_escapes_mvPolynomial_in_gaugeBall
      (fun i => z + shift i) hnodes hupper orders u C hu baseJet
      (specializePolynomialCoefficients z Q) hP hηTime hηGauge
  exact ⟨z, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge, hbounded,
    hmass, hfinite, hescape⟩

/-- Polynomial escape for the actual normalized Cauchy-jet packet of the prime-log Herglotz
source.  The escaping vector in the abstract theorem is exactly the packet difference of the
perturbed and original gauges. -/
theorem primeDyadic_actualCauchyJetPacket_escapes_mvPolynomial_in_gaugeBall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (primeLogCauchyJetPacket (primeLogPerturbedGauge u a ε) nodes orders) P ≠ 0 := by
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hescape⟩ :=
    primeDyadicCauchyJet_escapes_mvPolynomial_in_gaugeBall
      nodes hnodes hupper orders u C hu (primeLogCauchyJetPacket u nodes orders)
      P hP hηTime hηGauge
  have huUpper : ∀ p, u p ≤ C := fun p => (le_abs_self (u p)).trans (hu p)
  have hpacket := primeLogCauchyJetPacket_perturbedGauge
    u C huUpper nodes hupper orders a ε (by simpa [primeLogPerturbedMass] using hpos)
  refine ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, ?_⟩
  rw [hpacket]
  exact hescape

/-- Every nonzero polynomial-coefficient relation on finitely many translated normalized jets of
the actual prime-log source is broken by a gauge in every bounded-gauge neighborhood. -/
theorem primeDyadic_actualPolynomialCoefficientRelation_has_gaugeBall_escape
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) (hQ : Q ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ z : ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun i => z + shift i) ∧
      (∀ i, 0 < (z + shift i).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (primeLogCauchyJetPacket (primeLogPerturbedGauge u a ε)
          (fun i => z + shift i) orders)
        (specializePolynomialCoefficients z Q) ≠ 0 := by
  obtain ⟨z, hP, hnodes, hupper⟩ :=
    exists_upper_noncolliding_polynomial_detector shift hshift Q hQ
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hescape⟩ :=
    primeDyadic_actualCauchyJetPacket_escapes_mvPolynomial_in_gaugeBall
      (fun i => z + shift i) hnodes hupper orders u C hu
      (specializePolynomialCoefficients z Q) hP hηTime hηGauge
  exact ⟨z, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge, hbounded,
    hfinite, hescape⟩

/-- Every nonzero polynomial in the actual iterated derivatives of finitely many prime-log
translates is broken by a gauge in every bounded-gauge neighborhood. -/
theorem primeDyadic_actualDifferentialJet_escapes_mvPolynomial_in_gaugeBall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) (hP : P ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (primeLogDifferentialJetPacket (primeLogPerturbedGauge u a ε) nodes orders) P ≠ 0 := by
  have hscaled : jetFactorialScale orders P ≠ 0 := jetFactorialScale_ne_zero orders hP
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hescape⟩ :=
    primeDyadic_actualCauchyJetPacket_escapes_mvPolynomial_in_gaugeBall
      nodes hnodes hupper orders u C hu (jetFactorialScale orders P) hscaled hηTime hηGauge
  have hu' : ∀ p, primeLogPerturbedGauge u a ε p ≤ C' := fun p =>
    (le_abs_self _).trans (hbounded p)
  have heval := eval_jetFactorialScale_primeLogCauchyJetPacket
    (primeLogPerturbedGauge u a ε) C' hu' nodes hupper orders P
  refine ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hfinite, ?_⟩
  rw [heval] at hescape
  exact hescape

/-- **Actual differential-relation escape.** Every nonzero polynomial-coefficient relation among
finitely many translated iterated derivatives of the prime-log Herglotz source has a nonzero
upper-half-plane detector and is broken inside every bounded-gauge neighborhood. -/
theorem primeDyadic_actualDifferentialRelation_has_gaugeBall_escape
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) (hQ : Q ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ z : ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun i => z + shift i) ∧
      (∀ i, 0 < (z + shift i).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (primeLogDifferentialJetPacket (primeLogPerturbedGauge u a ε)
          (fun i => z + shift i) orders)
        (specializePolynomialCoefficients z Q) ≠ 0 := by
  obtain ⟨z, hP, hnodes, hupper⟩ :=
    exists_upper_noncolliding_polynomial_detector shift hshift Q hQ
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hfinite, hescape⟩ :=
    primeDyadic_actualDifferentialJet_escapes_mvPolynomial_in_gaugeBall
      (fun i => z + shift i) hnodes hupper orders u C hu
      (specializePolynomialCoefficients z Q) hP hηTime hηGauge
  exact ⟨z, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge, hbounded,
    hfinite, hescape⟩

end GaloisForLFunctions.HTGeometry
