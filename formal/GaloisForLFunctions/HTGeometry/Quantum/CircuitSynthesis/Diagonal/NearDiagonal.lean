import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw
import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw

/-! # Uniform circuit bounds near a simple computational-basis Hamiltonian -/
open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section

private abbrev UGroup (n : ℕ) := Matrix.unitaryGroup (Fin n → Bool) ℂ

/-- A compact unitary centralizer contained in an open set remains contained
there for all sufficiently small perturbations of the generator. -/
private theorem isOpen_centralizer_subset {n : ℕ} {G : Set (UGroup n)} (hG : IsOpen G) :
    IsOpen {A : Register n | ∀ V : UGroup n, A*(V : Register n) = (V : Register n)*A → V ∈ G} := by
  let Z : Set (Register n × UGroup n) :=
    {p | p.1*(p.2 : Register n) = (p.2 : Register n)*p.1} ∩ Prod.snd ⁻¹' Gᶜ
  have hval : Continuous (fun p : Register n × UGroup n => (p.2 : Register n)) :=
    continuous_subtype_val.comp continuous_snd
  have hZ : IsClosed Z := (isClosed_eq (continuous_fst.mul hval) (hval.mul continuous_fst)).inter
    (hG.isClosed_compl.preimage continuous_snd)
  have he : {A : Register n | ∀ V : UGroup n, A*(V : Register n) = (V : Register n)*A → V ∈ G} =
      (Prod.fst '' Z)ᶜ := by
    ext A
    constructor
    · rintro h ⟨⟨A,V⟩,⟨hcomm,hbad⟩,rfl⟩
      exact hbad (h V hcomm)
    · intro h V hcomm
      by_contra hbad
      exact h ⟨(A,V),⟨hcomm,hbad⟩,rfl⟩
  rw [he]
  exact (isClosedMap_fst_of_compactSpace _ hZ).isOpen_compl

private theorem phases_of_commuting_diagonal {n : ℕ} (d : (Fin n → Bool) → ℂ)
    (hd : Function.Injective d) (V : UGroup n)
    (hc : diagonal d*(V : Register n) = (V : Register n)*diagonal d) :
    ∃ w : (Fin n → Bool) → ℂ, (∀ i, ‖w i‖=1) ∧ (V : Register n) = diagonal w := by
  let w := fun i => (V : Register n) i i
  have he : (V : Register n) = diagonal w := by
    ext i j
    by_cases hij : i=j
    · subst j; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      have h := congrArg (fun A : Register n => A i j) hc
      change (diagonal d*(V : Register n)) i j = ((V : Register n)*diagonal d) i j at h
      rw [diagonal_mul,mul_diagonal] at h
      apply (mul_eq_zero.mp (show (d i-d j)*(V : Register n) i j=0 by linear_combination h)).resolve_left
      exact sub_ne_zero.mpr (fun hh => hij (hd hh))
  refine ⟨w,fun i => ?_,he⟩
  have hu := Matrix.mem_unitaryGroup_iff.mp V.property
  rw [he,Matrix.star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal] at hu
  have h := congrArg (fun A : Register n => ‖A i i‖) hu
  change ‖(diagonal _ : Register n) i i‖ = ‖(1 : Register n) i i‖ at h
  simp only [diagonal_apply_eq,one_apply_eq,Pi.star_apply,norm_mul,norm_star,norm_one] at h
  nlinarith only [h,norm_nonneg (w i)]

/-- Near each simple diagonal generator, every time evolution can be
approximated uniformly in time with (2n+1)2^n physical two-qubit gates. -/
theorem eventually_cheap_near_diagonal {n : ℕ} (hn : 2 ≤ n) (d : (Fin n → Bool) → ℂ)
    (hd : Function.Injective d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : Register n in 𝓝 (diagonal d), IsSelfAdjoint H → ∀ t : ℝ,
      HasProjectiveCircuitApproximation n ε (2^n*(2*n+1)) (unitaryEvolution H t) := by
  let G : Set (UGroup n) := ⋃ w : {w : (Fin n → Bool) → ℂ // ∀ i, ‖w i‖=1},
    (fun V : UGroup n => (V : Register n)) ⁻¹' Metric.ball (diagonal w.val) ε
  have hG : IsOpen G := isOpen_iUnion (fun w => Metric.isOpen_ball.preimage continuous_subtype_val)
  have hm (V : UGroup n) (hc : diagonal d*(V : Register n) = (V : Register n)*diagonal d) : V ∈ G := by
    obtain ⟨w,hw,he⟩ := phases_of_commuting_diagonal d hd V hc
    exact mem_iUnion.mpr ⟨⟨w,hw⟩, (show (V : Register n) ∈ Metric.ball (diagonal w) ε by
      rw [he]; exact Metric.mem_ball_self hε)⟩
  filter_upwards [(isOpen_centralizer_subset hG).mem_nhds hm] with H hH hHerm t
  let V : UGroup n := ⟨_,unitaryEvolution_mem_unitary hHerm t⟩
  have hV : V ∈ G := hH V (unitaryEvolution_commutes_generator H t)
  obtain ⟨w,hclose⟩ := mem_iUnion.mp hV
  have hnorm : ‖unitaryEvolution H t-diagonal w.val‖ < ε := by
    simpa only [Metric.mem_ball,dist_eq_norm] using (show (V : Register n) ∈ Metric.ball (diagonal w.val) ε from hclose)
  obtain ⟨z,hz,C,hC,he⟩ := diagonal_phases hn w.val w.property
  exact ⟨z,hz,C,hC,he ▸ hnorm.le⟩

#print axioms eventually_cheap_near_diagonal
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
