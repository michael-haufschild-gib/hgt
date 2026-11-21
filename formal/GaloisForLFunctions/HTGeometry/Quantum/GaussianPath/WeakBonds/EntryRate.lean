import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.PathGaps
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Physical return flux as a function of the Gaussian disorder coordinates -/
open Real Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
noncomputable section
open PrescribedTimes EmptyVisitFlux SharpOccupation

/-- The continuous empty-circuit entry flux for an (n+2)-site prefix at
physical error ε. -/
def emptyRate (n : ℕ) (ε : ℝ) (x : PrefixIndex n → ℝ) : ℝ :=
  let E := fun i => -(prefixGenerator n x).2.isHermitian.eigenvalues i
  (physicalArc ε)^(2^(n+2)-2:ℕ)*pairTurnRate E

/-- Every individual coupling, and even the full Euclidean norm, gives a
deterministic lower bound for the spectral entry flux. -/
theorem coefficient_rate_floor (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hr : ε < sqrt 2) :
    let D : ℕ := 2^(n+2)
    let J := Fintype.card (PathLabel n)
    let b := (physicalArc ε)^(D-2)*(D:ℝ)^2/(4*π*(J:ℝ))
    0 < b ∧ ∀ x : PrefixIndex n → ℝ, b*coefficientNorm x ≤ emptyRate n ε x := by
  intro D J b
  have hx := (physicalArc_spec hε hr).1.1
  have hj : (0:ℝ) < J := Nat.cast_pos.mpr Fintype.card_pos
  have hd : (0:ℝ) < D := by dsimp only [D]; positivity
  have hden : 0 < 4*π*(J:ℝ) := by positivity
  have hpow : 0 < (physicalArc ε)^(D-2) := pow_pos hx _
  have hb : 0 < b := div_pos (mul_pos hpow (sq_pos_of_pos hd)) hden
  refine ⟨hb,?_⟩
  intro x
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  let M := ∑ i : PrefixIndex n, |x i|
  have he : prefixGenerator n x = ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ := by
    apply Subtype.ext
    simpa only [prefixGenerator,u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
  have hmass : (∑ l : PathLabel n, |u l|)=M :=
    Equiv.sum_comp (pathCoeffEquiv n).symm (fun i => |x i|)
  have hnorm : coefficientNorm x ≤ M := by
    rw [coefficientNorm,EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_iff).mpr
    exact ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _,by
      simpa only [WithLp.ofLp_toLp,Real.norm_eq_abs] using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|) (fun _ _ => abs_nonneg _))⟩
  have hgap := FluxOccupation.path_pair_turn_lower u
  rw [hmass] at hgap
  rw [emptyRate,he]
  apply (mul_le_mul_of_nonneg_left hnorm hb.le).trans
  dsimp only [b]
  rw [div_mul_eq_mul_div,div_le_iff₀ hden]
  calc
    _ = (physicalArc ε)^(D-2)*((D:ℝ)^2*M) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hgap hpow.le).trans_eq (by ring)

/-- The rate is the limiting count of distinct continuous entries for the
same finite-dimensional Gaussian law used by the first-wait statistics. -/
theorem gaussian_prefix_entry_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let n := k+1
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      let E := fun i => -(prefixGenerator n x).2.isHermitian.eigenvalues i
      ∀ ε : ℝ, 0 < ε → ε < sqrt 2 →
        Tendsto (fun T : ℝ => ((entryDates E (physicalArc ε) T).card:ℝ)/T) atTop (𝓝 (emptyRate n ε x)) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hg k
  intro n x E ε hε hr
  let u := pathPauliDisorderShell ω n
  have he : prefixGenerator n x = ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ := by
    apply Subtype.ext
    exact numberedGenerator_shell u
  have hgen : MaximallyProjectiveEnergy E := by
    dsimp only [E]
    rw [he]
    exact maximallyProjectiveEnergy_neg (hg k)
  obtain ⟨hx,_⟩ := physicalArc_spec hε hr
  have h := entry_count_rate E hgen hx.1 hx.2
  simpa only [emptyRate,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using h

#print axioms coefficient_rate_floor
#print axioms gaussian_prefix_entry_rate
end
end GaloisForLFunctions.HTGeometry.WeakBonds
