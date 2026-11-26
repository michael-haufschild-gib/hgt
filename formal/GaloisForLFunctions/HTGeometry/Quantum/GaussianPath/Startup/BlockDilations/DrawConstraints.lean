import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SelectedCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PhysicalRotation
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-! # Physical constraints stable under every packet dilation -/

open MeasureTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ}

/-- Squared disorder mass on selected physical couplings. -/
def energyOn (S : Finset (PathLabel n)) (x : PathLabel n→ℝ) := ∑ l ∈ S, (x l)^2

/-- Conditions on the longitudinal mass, total energy and energy near the seams. -/
def drawBounds (T : Finset (PathLabel n)) (m E B : ℝ) : Set (PathLabel n→ℝ) :=
  {x | m≤∑ i : Fin (n+2), |x (.inl (i,2))|} ∩ {x | energyOn univ x≤E} ∩ {x | energyOn T x≤B}

theorem measurable_drawBounds (T : Finset (PathLabel n)) (m E B : ℝ) :
    MeasurableSet (drawBounds T m E B) := by
  exact ((measurableSet_le measurable_const (by fun_prop)).inter
    (measurableSet_le (by unfold energyOn; fun_prop) measurable_const)).inter
    (measurableSet_le (by unfold energyOn; fun_prop) measurable_const)

/-- Contracting a pattern preserves both upper bounds. The absolute
longitudinal mass can decrease by at most the common dilation factor. -/
theorem drawBounds_precursor (S T : Finset (PathLabel n)) {a : ℝ} (ha : 1≤a)
    (m E B : ℝ) (x : PathLabel n→ℝ) :
    expand S a x∈drawBounds T m E B → x∈drawBounds T (m/a) E B := by
  have hp := zero_lt_one.trans_le ha
  have hcoord (i : PathLabel n) :
      |x i|≤|expand S a x i| ∧ |expand S a x i|≤a*|x i| := by
    have h := le_mul_of_one_le_left (abs_nonneg (x i)) ha
    by_cases hi : i∈S
    · simpa only [expand,if_pos hi,abs_mul,abs_of_pos hp] using And.intro h (le_refl (a*|x i|))
    · simpa only [expand,if_neg hi] using And.intro (le_refl |x i|) h
  have henergy (U : Finset (PathLabel n)) : energyOn U x≤energyOn U (expand S a x) := by
    apply sum_le_sum
    intro i _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord i).1 2
  rintro ⟨⟨hm,he⟩,hb⟩
  refine ⟨⟨(div_le_iff₀ hp).mpr ?_,(henergy univ).trans he⟩,(henergy T).trans hb⟩
  rw [mul_comm,Finset.mul_sum]
  exact hm.trans (sum_le_sum fun i _ => (hcoord (.inl (i,2))).2)

theorem total_energy (x : PathLabel n→ℝ) :
    ‖(WithLp.toLp 2 x : PathShell n)‖^2=energyOn univ x :=
  EuclideanSpace.real_norm_sq_eq _

theorem restricted_energy (T : Finset (PathLabel n)) (x : PathLabel n→ℝ) :
    ‖restrictShell T (WithLp.toLp 2 x)‖^2=energyOn T x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have h (i : PathLabel n) : ((restrictShell T (WithLp.toLp 2 x)).ofLp i)^2=
      if i∈T then (x i)^2 else 0 := by
    by_cases hi : i∈T <;> simp [restrictShell,hi]
  simp_rw [h]
  rw [←sum_filter]
  simp [energyOn]

/-- The coordinate dilation is exactly the physical modification of the
Hamiltonian used in the propagator comparison. -/
theorem expand_eq_dilateShell (S : Finset (PathLabel n)) (a : ℝ) (x : PathLabel n→ℝ) :
    (WithLp.toLp 2 (expand S (1+a) x) : PathShell n)=dilateShell S a (WithLp.toLp 2 x) := by
  apply WithLp.ofLp_injective 2
  funext i
  change (if i∈S then (1+a)*x i else x i)=x i+a*(if i∈S then x i else 0)
  by_cases hi : i∈S <;> simp [hi,add_mul]

/-- Draws whose physical propagator fits the chosen budget at one date. -/
def affordableDraw (n s : ℕ) (ε t : ℝ) : Set (PathLabel n→ℝ) :=
  {x | HasProjectiveCircuitApproximation (n+2) ε s
    (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x)) t)}

theorem measurable_affordableDraw (n s : ℕ) (ε t : ℝ) : MeasurableSet (affordableDraw n s ε t) := by
  have hH : Continuous (fun x : PathLabel n→ℝ => pathHamiltonian (WithLp.toLp 2 x)) := by
    simp only [pathHamiltonian_eq_sum]
    fun_prop
  simp only [affordableDraw,hasProjectiveCircuitApproximation_iff_infDist]
  exact (isClosed_le ((Metric.continuous_infDist_pt _).comp
    (continuous_unitaryEvolution.comp (hH.prodMk continuous_const))) continuous_const).measurableSet

#print axioms drawBounds_precursor
#print axioms measurable_affordableDraw
end
end GaloisForLFunctions.HTGeometry.BlockDilations
