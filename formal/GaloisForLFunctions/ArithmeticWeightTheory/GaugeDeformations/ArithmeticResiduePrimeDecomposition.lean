import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticResidueProfiles
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrincipalProfileScaling

/-!
# The arithmetic correction to the principal prime profile

Finite character inversion separates the actual residue-class prime sum
into its principal mean and a regular correction. Nonprincipal character
logarithms extend through one; the ramified primes contribute exactly the
difference between their chosen profiles and that mean. Both corrections
vanish at the common endpoint.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {q : ℕ} [NeZero q]

private theorem characterProfile_tube_mono {e d : ℝ} (hed : e ≤ d) :
    {s : ℂ | 1 - e < s.re ∧ |s.im| < e} ⊆ {s : ℂ | 1 - d < s.re ∧ |s.im| < d} := by
  intro s hs
  exact ⟨by linarith only [hs.1, hed], hs.2.trans_le hed⟩

/-- A finite nonprincipal character family has one common continuation tube. -/
private theorem exists_finite_characterProfile_continuation
    (P : DirichletCharacter ℂ q → ℂ → ℂ) {R : NNReal} (hR : 1 < (R : ℝ))
    (hP : ∀ χ, AnalyticOnNhd ℂ (P χ) (closedBall 0 R))
    (h1 : ∀ χ, χ ≠ 1 → P χ 1 = 1)
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ ≠ 1) :
    ∃ e : ℝ, 0 < e ∧ ∃ K : ℝ → ℂ → ℂ,
      (∀ t : ℝ, 0 ≤ t → AnalyticOnNhd ℂ (K t) {s | 1 - e < s.re ∧ |s.im| < e}) ∧
      ContinuousOn (fun v : ℝ × ℂ => K v.1 v.2)
        (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) ∧
      (∀ s : ℂ, K 0 s = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ s : ℂ, 1 < s.re →
        K t s = ∑ χ ∈ S, weightedProfilePrimeSum (fun p => χ p) (P χ) t s) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, zero_lt_one, fun _ _ => 0, fun _ _ => analyticOnNhd_const,
        continuousOn_const, fun _ => rfl, ?_⟩
      intro t ht s hs
      simp only [Finset.sum_empty]
  | @insert χ S hχS ih =>
      intro hS
      have hχ : χ ≠ 1 := hS χ (Finset.mem_insert_self χ S)
      obtain ⟨e, he, K, hKa, hKc, hK0, hKe⟩ :=
        exists_characterProfile_continuation hχ hR (hP χ) (h1 χ hχ)
      obtain ⟨d, hd, L, hLa, hLc, hL0, hLe⟩ :=
        ih (fun ψ hψ => hS ψ (Finset.mem_insert_of_mem hψ))
      have hsube := characterProfile_tube_mono (min_le_left e d)
      have hsubd := characterProfile_tube_mono (min_le_right e d)
      refine ⟨min e d, lt_min he hd, fun t s => K t s + L t s,
        fun t ht => ((hKa t ht).mono hsube).add ((hLa t ht).mono hsubd),
        (hKc.mono (fun v hv => ⟨hv.1, hsube hv.2⟩)).add
          (hLc.mono (fun v hv => ⟨hv.1, hsubd hv.2⟩)), ?_, ?_⟩
      · intro s
        rw [hK0 s, hL0 s, add_zero]
      · intro t ht s hs
        rw [hKe t ht s hs, hLe t ht s hs, Finset.sum_insert hχS]

/-- The ramified correction replaces the mean by the actual chosen profile. -/
def residueFiniteCorrection (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (t : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ residueRamifiedPrimes q,
    (analyticSmoothingPrimePhase (ρ p) p (t : ℂ) -
      analyticSmoothingPrimePhase (residueAverage Φ) p (t : ℂ)) * ((p : ℕ) : ℂ) ^ (-s)

theorem residueFiniteCorrection_zero {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h1 : residueAverage Φ 1 = -1) (hρ1 : ∀ p, (p : ℕ) ∣ q → ρ p 1 = -1) (s : ℂ) :
    residueFiniteCorrection Φ ρ 0 s = 0 := by
  unfold residueFiniteCorrection
  apply Finset.sum_eq_zero
  intro p hp
  rw [Complex.ofReal_zero, analyticSmoothingPrimePhase_zero, analyticSmoothingPrimePhase_zero,
    hρ1 p ((mem_residueRamifiedPrimes p).mp hp), h1, sub_self, zero_mul]

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
