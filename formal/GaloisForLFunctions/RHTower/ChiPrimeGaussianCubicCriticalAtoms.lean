import GaloisForLFunctions.RHTower.ChiRamanujanCriticalFiniteAtoms
import GaloisForLFunctions.RHTower.ChiRamanujanFiniteContractionProjectors
import GaloisForLFunctions.RHTower.ChiRamanujanPrimeOnlyThreeFrequency
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain

/-!
# The complete physical cubic as an exact critical rational atom action

The finite critical source selects prime logarithms throughout the full
integer band. A finite Fourier test contains the literal Gaussian, window,
reciprocal and oscillatory factors; rational translation projectors impose
both original equality exclusions. The identity holds at every real scale
at least one, without damping limits or an assumed cancellation estimate.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def ramanujanCriticalTripleAtomWeight (P : Finset ℕ) (a : RamanujanTriplePrimeOnlyAtomIndex P) : ℝ :=
  ramanujanCriticalPrimeAtomWeight P a.1 * ramanujanCriticalPrimeAtomWeight P a.2.1 *
    ramanujanCriticalPrimeAtomWeight P a.2.2

/-- The entire finite critical rational tensor acts on a test without any limit. -/
def ramanujanCriticalTripleAtomAction (P : Finset ℕ) : ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
    (ramanujanCriticalTripleAtomWeight P a : ℂ) * F (ramanujanTriplePrimeOnlyAtomNode a)
  map_add' F G := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

theorem ramanujanCriticalTripleAtomAction_nat_phase (M : ℕ) {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpM : p ≤ M) (hqM : q ≤ M) (hrM : r ≤ M) :
    ramanujanCriticalTripleAtomAction (Finset.range (M+1))
      (ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),(r : ℤ))) =
        (((if p.Prime then Real.log p else 0) * (if q.Prime then Real.log q else 0) *
          (if r.Prime then Real.log r else 0) : ℝ) : ℂ) := by
  classical
  change (∑ a : RamanujanTriplePrimeOnlyAtomIndex (Finset.range (M+1)),
    (ramanujanCriticalTripleAtomWeight (Finset.range (M+1)) a : ℂ) *
      ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),(r : ℤ)) (ramanujanTriplePrimeOnlyAtomNode a)) = _
  rw [Complex.ofReal_mul, Complex.ofReal_mul,
    ← sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hp hpM,
    ← sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hq hqM,
    ← sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hr hrM]
  conv_rhs => rw [mul_assoc]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  dsimp [ramanujanCriticalTripleAtomWeight, ramanujanTriplePrimeOnlyAtomNode,
    ramanujanTripleFourierPhase]
  push_cast
  ring

/-- A full finite Fourier test: its integer support carries no prime mask. -/
def ramanujanFiniteCubeTest (S : Finset ℕ) (c : ℕ → ℕ → ℕ → ℂ) : (ℝ × ℝ × ℝ) → ℂ :=
  ∑ r ∈ S, ∑ p ∈ S, ∑ q ∈ S,
    c p q r • ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),(r : ℤ))

theorem ramanujanCriticalTripleAtomAction_projected_cube (M : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 < n ∧ n ≤ M) (c : ℕ → ℕ → ℕ → ℂ) :
    ramanujanCriticalTripleAtomAction (Finset.range (M+1))
      (ramanujanNoncontractingProjector (M+1) (ramanujanFiniteCubeTest S c)) =
      ∑ r ∈ S, ∑ p ∈ S, ∑ q ∈ S,
        if p=r ∨ q=r then 0 else c p q r *
          (((if p.Prime then Real.log p else 0) * (if q.Prime then Real.log q else 0) *
            (if r.Prime then Real.log r else 0) : ℝ) : ℂ) := by
  classical
  unfold ramanujanFiniteCubeTest
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [ramanujanNoncontractingProjector_nat_phase M (hS p hp).2 (hS q hq).2 (hS r hr).2]
  by_cases h : p=r ∨ q=r
  · simp [h]
  · rw [if_neg h, if_neg h, ramanujanCriticalTripleAtomAction_nat_phase M
      (hS p hp).1 (hS q hq).1 (hS r hr).1 (hS p hp).2 (hS q hq).2 (hS r hr).2]
    rfl

/-- The actual all-integer physical Fourier test, with logarithms cancelled
only after the rational source has selected primes. -/
def primeGaussianCriticalFourierTest (N : ℝ) : (ℝ × ℝ × ℝ) → ℂ :=
  ramanujanFiniteCubeTest (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) (fun p q r =>
    primeGaussianCubicMainEntry N p q r /
      ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)))

/-- The complete original signed physical cubic is exactly a finite critical
rational atom action with both literal contraction projectors. -/
theorem primeGaussianCubicOffDiagonal_eq_criticalAtomAction {N : ℝ} (hN : 1 ≤ N) :
    primeGaussianCubicOffDiagonal N =
      ramanujanCriticalTripleAtomAction (Finset.range (⌊2*N⌋₊+1))
        (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (primeGaussianCriticalFourierTest N)) := by
  classical
  have hf : 1 ≤ ⌊N⌋₊ := by simpa using Nat.floor_mono hN
  have hS : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, 1 < n ∧ n ≤ ⌊2*N⌋₊ := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact ⟨lt_of_le_of_lt hf hn'.1, hn'.2⟩
  rw [primeGaussianCriticalFourierTest, ramanujanCriticalTripleAtomAction_projected_cube _ _ hS]
  symm
  unfold primeGaussianCubicOffDiagonal primeProfileBand
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrp : r.Prime
  · simp only [if_pos hrp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime
    · simp only [if_pos hpp]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqp : q.Prime
      · simp only [if_pos hqp]
        by_cases hm : p=r ∨ q=r
        · simp [hm]
        · have hl (n : ℕ) (hn : n.Prime) : (Real.log n : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
          simp only [if_neg hm, Complex.ofReal_mul]
          exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero (hl p hpp) (hl q hqp)) (hl r hrp))
      · simp [hqp]
    · simp [hpp]
  · simp [hrp]

end RHTower.BAGTrace
