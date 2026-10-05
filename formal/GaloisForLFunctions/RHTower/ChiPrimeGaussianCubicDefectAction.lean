import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicIntegerDefect
import GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource

/-!
# Complete critical physical action in integer defect coordinates

Every literal critical atom has its exact numerator on the radical-square
grid. Both contraction translations are retained at their common denominator.
The full signed atom action is therefore an exact sum over integer defect
congruence fibres. An unconditional actual Schwartz family preserves every
lift, the physical cutoff, and the original negligible sharp/smooth error.
No signed asymptotic saving or unproved exchange with an integral is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators FourierTransform Topology ContDiff
namespace RHTower.BAGTrace

/-- Positive radical-square modulus of the literal critical source. -/
def bagCriticalGridLevel (P : Finset ℕ) : ℕ+ :=
  ⟨ramanujanGridModulus P, pow_pos
    (Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.pos)) 2⟩

/-- Integer numerator before reducing modulo the common denominator. -/
def bagCriticalAtomNumerator (P : Finset ℕ) (a : RamanujanPrimeOnlyAtomIndex P) : ℤ :=
  (a.1.2.val*(ramanujanGridModulus P/a.1.1.val)+
    a.2.2.val*(ramanujanGridModulus P/a.2.1.val^2) : ℕ)

private lemma grid_scale (Q : ℕ+) {d : ℕ} (hd : d ∣ (Q : ℕ)) (a : ℕ) :
    (a : ℝ)/d=(a*((Q : ℕ)/d) : ℕ)/(Q : ℝ) := by
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast Q.property.ne'
  rw [Nat.cast_mul,Nat.cast_div_charZero hd]
  field_simp

/-- Exact rational node; no representative or primitive-node restriction. -/
theorem bagCriticalAtomNumerator_node (P : Finset ℕ) (a : RamanujanPrimeOnlyAtomIndex P) :
    (bagCriticalAtomNumerator P a : ℝ)/(bagCriticalGridLevel P : ℝ)=
      ramanujanPrimeOnlyAtomNode a := by
  have hd : a.1.1.val ∣ ramanujanGridModulus P :=
    (Nat.dvd_of_mem_divisors a.1.1.property).trans (dvd_pow_self _ (by omega : 2 ≠ 0))
  have he : a.2.1.val^2 ∣ ramanujanGridModulus P :=
    pow_dvd_pow_of_dvd (Nat.dvd_of_mem_divisors a.2.1.property) 2
  rw [ramanujanPrimeOnlyAtomNode,ramanujanAtomNode,ramanujanSquareSieveAtomNode,
    grid_scale (bagCriticalGridLevel P) hd,grid_scale (bagCriticalGridLevel P) he]
  simp only [bagCriticalAtomNumerator,bagCriticalGridLevel,Nat.cast_add,Int.cast_add,
    Int.cast_natCast,add_div]
  rfl

def bagCriticalTripleNumerator (P : Finset ℕ) (a : RamanujanTriplePrimeOnlyAtomIndex P) :
    BAGIntegerTriple :=
  (bagCriticalAtomNumerator P a.1,bagCriticalAtomNumerator P a.2.1,
    bagCriticalAtomNumerator P a.2.2)

theorem bagCriticalTripleNumerator_node (P : Finset ℕ) (a : RamanujanTriplePrimeOnlyAtomIndex P) :
    bagGridShift (bagCriticalGridLevel P) (bagCriticalTripleNumerator P a)=
      ramanujanTriplePrimeOnlyAtomNode a := by
  simp only [bagGridShift,bagCriticalTripleNumerator,bagCriticalAtomNumerator_node,
    ramanujanTriplePrimeOnlyAtomNode]

/-- Every actual atom and both literal contraction projectors, in integer defect coordinates. -/
def bagCriticalDefectAction (P : Finset ℕ) (D : ℕ+)
    (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑ a : RamanujanTriplePrimeOnlyAtomIndex P, (ramanujanCriticalTripleAtomWeight P a : ℂ)*
    bagProjectedDefectTest (bagCriticalGridLevel P) D (bagCriticalTripleNumerator P a) f

theorem bagCriticalDefectAction_eq (P : Finset ℕ) (D : ℕ+)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    bagCriticalDefectAction P D f = ramanujanCriticalTripleAtomAction P
      (ramanujanNoncontractingProjector (D : ℕ) (bagLiftedFourierTest f)) := by
  simp only [bagCriticalDefectAction,bagProjectedDefectTest_eq,bagCriticalTripleNumerator_node]
  rfl

def bagPhysicalProjectorLevel (N : ℝ) : ℕ+ := ⟨⌊2*N⌋₊+1,Nat.succ_pos _⟩

theorem primeGaussianCubicSmoothedOffDiagonal_eq_defectAction {N : ℝ} (hN : 1 ≤ N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ)
    (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    primeGaussianCubicSmoothedOffDiagonal N η =
      bagCriticalDefectAction (Finset.range (⌊2*N⌋₊+1)) (bagPhysicalProjectorLevel N) A := by
  rw [bagCriticalDefectAction_eq]
  exact primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction hN hz A hA

/-- Unconditional actual family: full integer defect action and original negligible edge error. -/
theorem exists_bagCompleteIntegerDefectFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ Q : ℕ+, ∀ s : BAGIntegerTriple,
          Summable (fun w : BAGDefectIndex Q s => ‖(𝓕 (A N)) (bagDefectNode Q w.val)‖)) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N)=
          bagCriticalDefectAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (bagPhysicalProjectorLevel N) (A N)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-
          bagCriticalDefectAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (bagPhysicalProjectorLevel N) (A N)‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalFourierFamily
  have he : ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N (η N)=
        bagCriticalDefectAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
          (bagPhysicalProjectorLevel N) (A N) := by
    filter_upwards [hA,eventually_ge_atTop (1 : ℕ)] with N hreg hN
    exact primeGaussianCubicSmoothedOffDiagonal_eq_defectAction (by exact_mod_cast hN)
      hreg.2.2.2.1 (A N) hreg.2.2.2.2.2.1
  refine ⟨η,A,?_,?_⟩
  · filter_upwards [hA,he] with N hreg heq
    exact ⟨hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1,hreg.2.2.2.2.1,
      hreg.2.2.2.2.2.1,fun Q s => summable_norm_bagDefectLiftedTest Q s (A N),heq⟩
  · apply herr.congr'
    filter_upwards [he] with N heq
    rw [heq]

end RHTower.BAGTrace
