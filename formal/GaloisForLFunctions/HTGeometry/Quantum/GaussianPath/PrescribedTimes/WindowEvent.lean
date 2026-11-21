import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-! # Closed events for an affordable visit at a prescribed laboratory time -/
open Set Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- Real disorder coordinates for an (n+2)-site prefix. -/
abbrev PrefixIndex (n : ℕ) := Fin (Fintype.card (ChainLabel (n+2)))

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The physical path generator in independent standard Gaussian coordinates. -/
def numberedGenerator (n : ℕ) (x : PrefixIndex n → ℝ) : Reg (n+2) :=
  ∑ l : PathLabel n, (x ((pathCoeffEquiv n).symm l):ℂ) • finitePauliMatrix (pathWord l)

theorem numberedGenerator_shell {n : ℕ} (u : PathShell n) :
    numberedGenerator n (fun i => u (pathCoeffEquiv n i)) = pathHamiltonian u := by
  rw [numberedGenerator,pathHamiltonian_eq_sum]
  simp only [Equiv.apply_symm_apply]

private theorem numberedGenerator_continuous (n : ℕ) : Continuous (numberedGenerator n) := by
  unfold numberedGenerator
  fun_prop

private theorem numberedGenerator_smul (n : ℕ) (a : ℝ) (x : PrefixIndex n → ℝ) :
    numberedGenerator n (a • x) = (a:ℂ) • numberedGenerator n x := by
  unfold numberedGenerator
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun l _ => by rw [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,smul_smul])

/-- Coefficients admitting a genuine circuit hit somewhere in a closed
observation interval, with time, gates and phase allowed to vary. -/
def prescribedWindowEvent (n s : ℕ) (t b : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∃ v ∈ Icc t (t+b), HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (unitaryEvolution (numberedGenerator n x) v)}

theorem measurable_prescribedWindowEvent (n s : ℕ) (t b : ℝ) :
    MeasurableSet (prescribedWindowEvent n s t b) := by
  let K := Icc t (t+b)
  letI : CompactSpace ↥K := inferInstanceAs (CompactSpace (Icc t (t+b)))
  let F (p : (PrefixIndex n → ℝ) × ↥K) := unitaryEvolution (numberedGenerator n p.1) p.2.val
  have hc : Continuous F := continuous_unitaryEvolution.comp
    (((numberedGenerator_continuous n).comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  let Z := {p | HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (F p)}
  have hZ : IsClosed Z := by
    simp only [Z,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le ((Metric.continuous_infDist_pt _).comp hc) continuous_const
  have he : prescribedWindowEvent n s t b = Prod.fst '' Z := by
    ext x
    constructor
    · rintro ⟨v,hv,hh⟩
      exact ⟨(x,⟨v,hv⟩),hh,rfl⟩
    · rintro ⟨⟨_,v⟩,hh,rfl⟩
      exact ⟨v.val,v.property,hh⟩
  rw [he]
  exact (isClosedMap_fst_of_compactSpace _ hZ).measurableSet

/-- A window hit after dilation of the coefficients is a physical hit
after dilation of both endpoints of the time window. -/
theorem dilation_window_hit {n s : ℕ} {t b a : ℝ} (ha : 0 < a) (x : PrefixIndex n → ℝ)
    (h : a • x ∈ prescribedWindowEvent n s t b) :
    ∃ v ∈ Icc (a*t) (a*t+a*b),
      HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (unitaryEvolution (numberedGenerator n x) v) := by
  obtain ⟨v,hv,hh⟩ := h
  refine ⟨a*v,⟨mul_le_mul_of_nonneg_left hv.1 ha.le,?_⟩,?_⟩
  · simpa only [mul_add] using mul_le_mul_of_nonneg_left hv.2 ha.le
  · simpa only [numberedGenerator_smul,unitaryEvolution_smul_generator] using hh

#print axioms measurable_prescribedWindowEvent
#print axioms dilation_window_hit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
