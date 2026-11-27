import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.CorrectedReporter
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Calibration.SmallAngles

/-! # A quadratic Choi signal at fixed coupling tolerance -/
open Finset Real Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance contractionAlgebra (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

/-- A uniform bound on the local mass times the calibration error makes
a contraction supported on the enlarged triple detect its quadratic signal.
The admissible perturbation does not shrink with the observation time. -/
theorem fixed_width_reporter {e f : Fin (n+1)} (hm : e.succ=f.castSucc) {i y : Fin (n+2)}
    (hi : i∈tripleSites e f) (hy : y∈tripleSites e f) (hiy : i≠y) (u : PathShell n)
    {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) :
    let S := incidentSites (tripleSites e f)
    let d := ‖pathHamiltonian (packetPerturbation e f u)‖
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    let U := unitaryEvolution (pathHamiltonian u) t
    4*d*(2*E+d)≤1/256 →
      ∃ K : Reg (n+2), IsSiteSupported S K ∧ ‖K‖≤1 ∧
        (sin t)^2/2≤‖K.trace/(Fintype.card (Fin (n+2)→Bool):ℂ)‖ ∧
        ‖star U*packetProbe e i*U*packetImage e f i-K‖≤(sin t)^2/16 := by
  intro S d E U hsmall
  let R := correctedReporter e f i u t
  let X := star U*packetProbe e i*U*packetImage e f i
  let ε := t^2*(4*d*(2*E+d))
  have hd : 0≤d := norm_nonneg _
  have hE : 0≤E := sum_nonneg fun _ _ => abs_nonneg _
  have hε : 0≤ε := mul_nonneg (sq_nonneg t) (mul_nonneg (mul_nonneg (by norm_num) hd)
    (add_nonneg (mul_nonneg zero_le_two hE) hd))
  have hX : X∈unitary (Reg (n+2)) := by
    have hu := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
    exact mul_mem (mul_mem (mul_mem (Unitary.star_mem hu) (finitePauliMatrix_mem_unitary _)) hu)
      (packetImage_unitary hm i)
  have hfit : ‖X-R‖≤ε := by
    have h := correctedReporter_error hm hi u t ht.1.le
    simpa only [norm_smul,norm_neg,Complex.norm_I,one_mul] using h
  have hsin := pow_le_pow_left₀ (half_pos ht.1).le (short_sine ht) 2
  have hsig : ε≤(sin t)^2/64 := by
    dsimp only [ε]
    linarith only [hsin,mul_le_mul_of_nonneg_left hsmall (sq_nonneg t)]
  have hε₁ : ε≤1/2 := by
    have h₂ := pow_le_pow_left₀ ht.1.le ht.2 2
    dsimp only [ε]
    linarith only [h₂,mul_le_mul_of_nonneg_left hsmall (sq_nonneg t),sq_nonneg t]
  let α := 1-ε
  let K := (α:ℂ) • R
  have ha : 1/2≤α := by dsimp only [α]; linarith only [hε₁]
  have ha₀ : 0≤α := (by norm_num : (0:ℝ)≤1/2).trans ha
  have ha₁ : α≤1 := sub_le_self _ hε
  have hn : ‖R‖≤1+ε := by
    have h := norm_add_le X (R-X)
    rw [show X+(R-X)=R by abel,CStarRing.norm_of_mem_unitary hX,norm_sub_rev R X] at h
    exact h.trans (add_le_add (le_refl 1) hfit)
  have hKn : ‖K‖≤1 := by
    change ‖(α:ℂ) • R‖≤1
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha₀]
    have h := mul_le_mul_of_nonneg_left hn ha₀
    dsimp only [α] at h ⊢
    linarith only [h,sq_nonneg ε]
  refine ⟨K,IsSiteSupported.complex_smul _ (correctedReporter_supported hm hi u t),hKn,?_,?_⟩
  · have htrace : (packetTest e f i t).trace/(Fintype.card (Fin (n+2)→Bool):ℂ)=(sin t:ℂ)^2 :=
      packet_transfer hm hi hy hiy t
    change (sin t)^2/2≤‖((α:ℂ) • R).trace/_‖
    rw [Matrix.trace_smul,smul_eq_mul,mul_div_assoc,show R.trace=(packetTest e f i t).trace from
      correctedReporter_trace hm hi u t,htrace,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg ha₀,←Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    linarith only [mul_le_mul_of_nonneg_right ha (sq_nonneg (sin t))]
  · have heq : R-K=(ε:ℂ) • R := by
      dsimp only [K,α]
      rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul,sub_sub_cancel]
    have htail : ‖R-K‖≤2*ε := by
      rw [heq,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hε]
      have h₂ : ‖R‖≤2 := by linarith only [hn,hε₁]
      exact (mul_le_mul_of_nonneg_left h₂ hε).trans_eq (mul_comm ..)
    have h := (norm_sub_le_norm_sub_add_norm_sub X R K).trans (add_le_add hfit htail)
    linarith only [h,hsig,sq_nonneg (sin t)]

#print axioms fixed_width_reporter
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
