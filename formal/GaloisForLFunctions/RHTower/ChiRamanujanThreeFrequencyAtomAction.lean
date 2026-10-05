import GaloisForLFunctions.RHTower.ChiRamanujanFiniteRationalAtoms
import GaloisForLFunctions.RHTower.ChiRamanujanThreeFrequencySource

/-!
# Joint limit of the literal three-frequency rational atom action

Finite signed divisor atoms are tested against the periodic Fourier series
of any Schwartz lattice profile. Exact finite-sum interchange identifies
the full atom tensor with its three independent Fourier multipliers.
The resulting joint limit is fixed-test convergence, not cubic cancellation.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology SchwartzMap
namespace RHTower.BAGTrace

abbrev RamanujanTripleAtomIndex (P : Finset ℕ) :=
  RamanujanAtomIndex P × RamanujanAtomIndex P × RamanujanAtomIndex P

def ramanujanTripleAtomNode {P : Finset ℕ} (a : RamanujanTripleAtomIndex P) : ℝ × ℝ × ℝ :=
  (ramanujanAtomNode a.1, ramanujanAtomNode a.2.1, ramanujanAtomNode a.2.2)

def ramanujanTripleAtomWeight (P : Finset ℕ) (ε : ℝ) (a : RamanujanTripleAtomIndex P) : ℝ :=
  ramanujanCompensatedAtomWeight P ε a.1 * ramanujanCompensatedAtomWeight P ε a.2.1 *
    ramanujanCompensatedAtomWeight P ε a.2.2

def ramanujanTripleFourierPhase (n : ℤ × ℤ × ℤ) (x : ℝ × ℝ × ℝ) : ℂ :=
  ramanujanFourierPhase n.1 x.1 * ramanujanFourierPhase n.2.1 x.2.1 *
    ramanujanFourierPhase n.2.2 x.2.2

/-- The periodic Fourier test is evaluated at every finite rational atom. -/
def ramanujanTriplePeriodicTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) (x : ℝ × ℝ × ℝ) : ℂ :=
  ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) * ramanujanTripleFourierPhase n x

/-- Literal finite signed rational-frequency action, before either limit. -/
def ramanujanTripleFiniteAtomAction (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) : ℂ :=
  ∑ a : RamanujanTripleAtomIndex P,
    (ramanujanTripleAtomWeight P ε a : ℂ) * ramanujanTriplePeriodicTest Φ (ramanujanTripleAtomNode a)

private theorem norm_triplePhase (n : ℤ × ℤ × ℤ) (x : ℝ × ℝ × ℝ) :
    ‖ramanujanTripleFourierPhase n x‖ = 1 := by
  simp only [ramanujanTripleFourierPhase, norm_mul, ramanujanFourierPhase,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Absolute convergence at every point, reusable for further finite rational atom sources. -/
theorem summable_ramanujanTriplePeriodicTest (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) (x : ℝ × ℝ × ℝ) :
    Summable (fun n : ℤ × ℤ × ℤ => Φ (ramanujanTripleLattice n) * ramanujanTripleFourierPhase n x) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) (summable_ramanujanTripleSchwartz_weighted Φ)
  rw [norm_mul, norm_triplePhase, mul_one]
  have hw : 1 ≤ ramanujanTripleWeight (ramanujanTripleLattice n) := by
    dsimp [ramanujanTripleWeight, ramanujanTripleLattice]
    calc
      (1 : ℝ) = 1*1*1 := by ring
      _ ≤ (1 + |(n.1 : ℝ)|) * (1 + |(n.2.1 : ℝ)|) * (1 + |(n.2.2 : ℝ)|) := by
        gcongr <;> linarith [abs_nonneg (n.1 : ℝ), abs_nonneg (n.2.1 : ℝ), abs_nonneg (n.2.2 : ℝ)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hw
    (norm_nonneg (Φ (ramanujanTripleLattice n)))

/-- The atom tensor has the product multiplier at every unrestricted Fourier triple. -/
theorem sum_ramanujanTripleAtomWeight_fourier (P : Finset ℕ) (ε : ℝ) (n : ℤ × ℤ × ℤ) :
    (∑ a : RamanujanTripleAtomIndex P,
      (ramanujanTripleAtomWeight P ε a : ℂ) * ramanujanTripleFourierPhase n (ramanujanTripleAtomNode a)) =
      (ramanujanTripleCompensatedCoeff P ε n : ℂ) := by
  classical
  rw [ramanujanTripleCompensatedCoeff, Complex.ofReal_mul, Complex.ofReal_mul,
    ← sum_ramanujanCompensatedAtomWeight_fourier P ε n.1,
    ← sum_ramanujanCompensatedAtomWeight_fourier P ε n.2.1,
    ← sum_ramanujanCompensatedAtomWeight_fourier P ε n.2.2]
  conv_rhs => rw [mul_assoc]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  dsimp [ramanujanTripleAtomWeight, ramanujanTripleFourierPhase, ramanujanTripleAtomNode]
  push_cast
  ring

/-- Exact atom/Fourier interchange, with summability derived from the actual Schwartz test. -/
theorem ramanujanTripleFiniteAtomAction_eq (P : Finset ℕ) (ε : ℝ)
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    ramanujanTripleFiniteAtomAction P ε Φ = ramanujanTripleCompensatedTest P ε Φ := by
  classical
  have hs (a : RamanujanTripleAtomIndex P) : Summable (fun n : ℤ × ℤ × ℤ =>
      (ramanujanTripleAtomWeight P ε a : ℂ) *
        (Φ (ramanujanTripleLattice n) * ramanujanTripleFourierPhase n (ramanujanTripleAtomNode a))) :=
    (summable_ramanujanTriplePeriodicTest Φ (ramanujanTripleAtomNode a)).mul_left _
  unfold ramanujanTripleFiniteAtomAction ramanujanTriplePeriodicTest
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun a _ => hs a)]
  apply tsum_congr
  intro n
  calc
    _ = Φ (ramanujanTripleLattice n) *
        ∑ a : RamanujanTripleAtomIndex P,
          (ramanujanTripleAtomWeight P ε a : ℂ) *
            ramanujanTripleFourierPhase n (ramanujanTripleAtomNode a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [sum_ramanujanTripleAtomWeight_fourier]

/-- Joint critical limit of the literal full three-frequency finite rational atoms.
No relation between prime cutoff and damping is imposed. The test is fixed. -/
theorem tendsto_ramanujanTripleFiniteAtomAction (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanTripleFiniteAtomAction z.1 z.2 Φ)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (ramanujanTripleMangoldtTest Φ)) := by
  simpa only [ramanujanTripleFiniteAtomAction_eq] using tendsto_ramanujanTripleCompensatedTest Φ

end RHTower.BAGTrace
