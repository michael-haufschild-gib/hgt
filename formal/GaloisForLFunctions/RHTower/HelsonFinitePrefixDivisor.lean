import GaloisForLFunctions.RHTower.LocallyFiniteDivisorPresentation
import GaloisForLFunctions.HTGeometry.HelsonFiniteEulerGauge


/-!
# Arbitrarily long literal zeta prefixes with an off-line Helson divisor

This is a closed audit witness obtained from the existing published Helson prescribed-divisor
and finite Euler-gauge theorems. Every finite initial coefficient block can agree exactly with
zeta while a completely multiplicative unimodular ordinary Dirichlet series has one simple
off-line zero, and no other divisor, in the positive half-plane.

No functional equation or identification of the full coefficient sequence with zeta is claimed.
The conclusion records meromorphic orders, independently of point values at removable
singularities. This is not new mathematical knowledge or a proposed RH architecture.
-/

open Complex Filter Set GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Topology

noncomputable section
namespace RHTower.HelsonFinitePrefixDivisor

def rho : ℂ := 3 / 4 + Complex.I
def singleDivisor (z : ℂ) : ℤ := if z = rho then 1 else 0

theorem singleDivisor_locallyFinite : RHTower.LocallyFiniteDivisor singleDivisor := by
  intro R
  apply (Set.finite_singleton rho).subset
  intro z hz
  have h : z = rho := by
    by_contra h
    simpa [singleDivisor, h] using hz.1
  simpa using h

theorem singleDivisor_supported : ∀ z, singleDivisor z ≠ 0 → z.re < 1 := by
  intro z hz
  by_cases h : z = rho
  · subst z
    norm_num [rho]
  · simp [singleDivisor, h] at hz

/-- A finite Euler change can fix every initial coefficient while retaining the off-line
singleton divisor in the positive half-plane. An instance of published Helson flexibility,
not a new RH mechanism. -/
theorem finite_prefix_singleton_divisor :
    ∀ N : ℕ, ∃ (a : ℕ →*₀ ℂ) (W : ℂ → ℂ),
      (∀ n, n ≠ 0 → ‖a n‖ = 1) ∧
      (∀ n, 0 < n → n ≤ N → a n = 1) ∧
      MeromorphicOn W Set.univ ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s ∧
        W s = LSeries (fun n => a n) s) ∧
      (∀ z : ℂ, 0 < z.re →
        meromorphicOrderAt W z = ((singleDivisor z : ℤ) : WithTop ℤ)) := by
  classical
  intro N
  obtain ⟨χ, _, Z, hZmero, hZprod, hZord⟩ :=
    RHTower.exists_continuable_phase_with_prescribed_locallyFinite_divisor
      singleDivisor_locallyFinite singleDivisor_supported
  let u : ℕ → ℂ := fun n => if h : Nat.Prime n then (χ ⟨n, h⟩ : ℂ) else 1
  let v : ℕ → ℂ := fun n => if n ≤ N then 1 else u n
  have hu : ∀ p, Nat.Prime p → ‖u p‖ = 1 := by
    intro p hp
    simp only [u, dif_pos hp]
    exact (χ ⟨p, hp⟩).2
  have hv : ∀ p, Nat.Prime p → ‖v p‖ = 1 := by
    intro p hp
    dsimp [v]
    split_ifs <;> simp [hu p hp]
  have hSfin : {p : Nat.Primes | (p : ℕ) ≤ N}.Finite :=
    (Set.finite_Iic N).preimage
      (f := fun p : Nat.Primes => (p : ℕ))
      (Set.injOn_of_injective (fun p q h => Subtype.ext h))
  let P := hSfin.toFinset
  have hP : ∀ p : Nat.Primes, p ∉ P → u (p : ℕ) = v (p : ℕ) := by
    intro p hp
    have hpn : ¬ (p : ℕ) ≤ N := by
      intro hn
      exact hp (hSfin.mem_toFinset.mpr hn)
    simp [v, hpn]
  let G : ℂ → ℂ := finiteEulerGaugeRatio P
    (fun p : Nat.Primes => ((p : ℕ) : ℝ))
    (fun p : Nat.Primes => u (p : ℕ))
    (fun p : Nat.Primes => v (p : ℕ))
  have hGmero : MeromorphicOn G Set.univ := by
    intro z _
    apply MeromorphicAt.fun_prod
    intro p _
    have hdecay : MeromorphicAt (analyticPrimeDecay ((p : ℕ) : ℝ)) z :=
      ((differentiable_analyticPrimeDecay ((p : ℕ) : ℝ)).analyticAt z).meromorphicAt
    exact ((MeromorphicAt.const 1 z).sub
      ((MeromorphicAt.const (u (p : ℕ)) z).mul hdecay)).div
      ((MeromorphicAt.const 1 z).sub
        ((MeromorphicAt.const (v (p : ℕ)) z).mul hdecay))
  have hGdiff : DifferentiableOn ℂ G positiveHalfPlane :=
    differentiableOn_finiteEulerGaugeRatio_positiveHalfPlane P _
      (fun p _ => by exact_mod_cast p.2.one_lt) _ _ (fun p _ => hv p p.2)
  have hGne : ∀ z : ℂ, 0 < z.re → G z ≠ 0 := by
    intro z hz
    exact finiteEulerGaugeRatio_ne_zero P _
      (fun p _ => by exact_mod_cast p.2.one_lt) _ _
      (fun p _ => hu p p.2) (fun p _ => hv p p.2) hz
  refine ⟨phaseChar v, G * Z, ?_, ?_, hGmero.mul hZmero, ?_, ?_⟩
  · intro n hn
    exact norm_phaseChar_eq_one hv hn
  · intro n hn hnN
    rw [phaseChar_apply_of_ne_zero v hn.ne', Finsupp.prod]
    apply Finset.prod_eq_one
    intro p hp
    have hp' : p ∈ n.primeFactors := by rwa [Nat.support_factorization] at hp
    have hpn : p ≤ N := (Nat.le_of_mem_primeFactors hp').trans hnN
    simp [v, hpn]
  · intro s hs
    refine ⟨lSeriesSummable_phaseChar hv hs, ?_⟩
    have hχ : ∀ p : Nat.Primes, (χ p : ℂ) = u p := by
      intro p
      simp [u, p.2]
    have huSum : Z s = LSeries (fun n => phaseChar u n) s := by
      have hp := hasProd_phaseEuler hu hs
      have hp' : HasProd
          (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
          (LSeries (fun n => phaseChar u n) s) := by
        simpa only [hχ] using hp
      exact (hZprod s hs).unique hp'
    have hgauge := LSeries_phaseChar_eq_mul_finiteEulerGaugeRatio_of_eq_off_finset
      hu hv P hP hs
    change G s * Z s = _
    rw [huSum, mul_comm]
    exact hgauge.symm
  · intro z hz
    have hnhds : positiveHalfPlane ∈ 𝓝 z :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    exact (meromorphicOrderAt_mul_of_ne_zero (hGdiff.analyticAt hnhds) (hGne z hz)).trans
      (hZord z)

end RHTower.HelsonFinitePrefixDivisor
