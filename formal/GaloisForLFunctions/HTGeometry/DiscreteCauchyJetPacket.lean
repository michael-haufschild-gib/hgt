import GaloisForLFunctions.HTGeometry.PrimeLogCauchyJetControllability
import GaloisForLFunctions.HTGeometry.PrimeLogGaugePerturbation

/-!
# Normalized jet packets of discrete Cauchy carriers

For a discrete Cauchy carrier, the normalized order-`j` jet at a node is the absolutely convergent
sum of the masses against `(support - node)⁻¹^(j+1)`.  These packets depend affinely on the mass.
In particular, a finitely supported mass perturbation changes the actual prime-log packet by
exactly the real Cauchy-jet control vector used in the polynomial escape theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized finite Cauchy-jet packet of a discrete real carrier.  Coordinate `(i,j)` is the
mass sum against `(support-node_i)⁻¹^(j+1)`. -/
def discreteCauchyJetPacket
    {ι κ : Type*} (support weight : κ → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ) :
    (Σ i, Fin (orders i)) → ℂ :=
  fun s => ∑' p, (weight p : ℂ) *
    cauchyJetColumn nodes orders (fun q => (support q : ℂ)) p s

/-- Absolute convergence of every normalized jet coordinate at upper-half-plane nodes. -/
theorem summable_discreteCauchyJetPacket_term
    {ι κ : Type*} (support weight : κ → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ)
    (hweight : Summable fun p => ‖(weight p : ℂ)‖)
    (hupper : ∀ i, 0 < (nodes i).im) (s : Σ i, Fin (orders i)) :
    Summable fun p => (weight p : ℂ) *
      cauchyJetColumn nodes orders (fun q => (support q : ℂ)) p s := by
  let z := nodes s.1
  let k := s.2.1 + 1
  have hmajor : Summable fun p => ‖(weight p : ℂ)‖ * ((z.im)⁻¹ ^ k) :=
    hweight.mul_right _
  apply Summable.of_norm_bounded hmajor
  intro p
  have hden : z.im ≤ ‖(support p : ℂ) - z‖ := by
    have him : |((support p : ℂ) - z).im| ≤ ‖(support p : ℂ) - z‖ :=
      Complex.abs_im_le_norm _
    have heq : ((support p : ℂ) - z).im = -z.im := by simp [Complex.sub_im]
    rw [heq, abs_neg, abs_of_pos (hupper s.1)] at him
    exact him
  simp only [cauchyJetColumn, z, k, norm_mul, norm_pow, norm_inv]
  gcongr
  exact hupper s.1

/-- **Affine normalized-jet law.** Adding a finitely supported real mass direction changes the
normalized packet by exactly the real Cauchy-jet control vector. -/
theorem discreteCauchyJetPacket_add_finsupp
    {ι κ : Type*} (support weight : κ → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ)
    (hweight : Summable fun p => ‖(weight p : ℂ)‖)
    (hupper : ∀ i, 0 < (nodes i).im)
    (a : κ →₀ ℝ) (ε : ℝ) :
    discreteCauchyJetPacket support (fun p => weight p + ε * a p) nodes orders =
      discreteCauchyJetPacket support weight nodes orders +
        ε • cauchyJetRealLinearCombination nodes orders support a := by
  funext s
  let K : κ → ℂ := fun p =>
    cauchyJetColumn nodes orders (fun q => (support q : ℂ)) p s
  have hbase : Summable fun p => (weight p : ℂ) * K p := by
    exact summable_discreteCauchyJetPacket_term support weight nodes orders hweight hupper s
  have hcorrSupport : Function.HasFiniteSupport
      (fun p => ((ε * a p : ℝ) : ℂ) * K p) := by
    apply a.support.finite_toSet.subset
    intro p hp
    by_contra hpa
    have ha : a p = 0 := by
      by_contra ha
      exact hpa (Finsupp.mem_support_iff.mpr ha)
    simp [ha] at hp
  have hcorr : Summable fun p => ((ε * a p : ℝ) : ℂ) * K p :=
    summable_of_hasFiniteSupport hcorrSupport
  change (∑' p, ((weight p + ε * a p : ℝ) : ℂ) * K p) =
    (∑' p, (weight p : ℂ) * K p) +
      (ε • cauchyJetRealLinearCombination nodes orders support a) s
  calc
    (∑' p, ((weight p + ε * a p : ℝ) : ℂ) * K p) =
        ∑' p, ((weight p : ℂ) * K p + ((ε * a p : ℝ) : ℂ) * K p) := by
      congr 1
      funext p
      push_cast
      ring
    _ = (∑' p, (weight p : ℂ) * K p) +
        ∑' p, ((ε * a p : ℝ) : ℂ) * K p := hbase.tsum_add hcorr
    _ = (∑' p, (weight p : ℂ) * K p) +
        ∑ p ∈ a.support, ((ε * a p : ℝ) : ℂ) * K p := by
      have hcorrTsum : (∑' p, ((ε * a p : ℝ) : ℂ) * K p) =
          ∑ p ∈ a.support, ((ε * a p : ℝ) : ℂ) * K p := by
        apply tsum_eq_sum (s := a.support)
        intro p hp
        have ha : a p = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hp
        simp [ha]
      rw [hcorrTsum]
    _ = (∑' p, (weight p : ℂ) * K p) +
        (ε • cauchyJetRealLinearCombination nodes orders support a) s := by
      simp only [Pi.smul_apply, cauchyJetRealLinearCombination,
        Finsupp.linearCombination_apply, Complex.real_smul]
      rw [Finsupp.sum]
      simp only [Pi.smul_apply, Finset.sum_apply, Complex.real_smul, K]
      rw [Finset.mul_sum]
      apply congrArg (fun t => (∑' p, (weight p : ℂ) * K p) + t)
      apply Finset.sum_congr rfl
      intro p hp
      push_cast
      ring

/-- The normalized packet of the actual dyadic prime-log Herglotz source. -/
def primeLogCauchyJetPacket
    {ι : Type*} (u : Nat.Primes → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ) :
    (Σ i, Fin (orders i)) → ℂ :=
  discreteCauchyJetPacket primeLogSupport (primeDyadicWeight u) nodes orders

/-- The order-zero normalized packet coordinate is exactly the prime-log Herglotz value. -/
theorem primeLogCauchyJetPacket_orderZero
    {ι : Type*} (u : Nat.Primes → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ)
    (i : ι) (hi : 0 < orders i) :
    primeLogCauchyJetPacket u nodes orders ⟨i, ⟨0, hi⟩⟩ =
      primeLogHerglotz u (nodes i) := by
  simp [primeLogCauchyJetPacket, discreteCauchyJetPacket, cauchyJetColumn,
    primeLogHerglotz, discreteHerglotz]

/-- A positive finite mass perturbation changes the actual prime-log normalized jet packet by
exactly the Cauchy control vector. -/
theorem primeLogCauchyJetPacket_perturbedGauge
    {ι : Type*} (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (a : Nat.Primes →₀ ℝ) (ε : ℝ)
    (hpos : ∀ p, 0 < primeLogPerturbedMass u a ε p) :
    primeLogCauchyJetPacket (primeLogPerturbedGauge u a ε) nodes orders =
      primeLogCauchyJetPacket u nodes orders +
        ε • cauchyJetRealLinearCombination nodes orders primeLogSupport a := by
  rw [primeLogCauchyJetPacket, primeLogCauchyJetPacket]
  have hweight : primeDyadicWeight (primeLogPerturbedGauge u a ε) =
      fun p => primeDyadicWeight u p + ε * a p := by
    funext p
    exact primeDyadicWeight_perturbedGauge u a ε hpos p
  rw [hweight]
  exact discreteCauchyJetPacket_add_finsupp primeLogSupport (primeDyadicWeight u)
    nodes orders (summable_norm_primeDyadicWeight u C hu) hupper a ε

end

end GaloisForLFunctions.HTGeometry
