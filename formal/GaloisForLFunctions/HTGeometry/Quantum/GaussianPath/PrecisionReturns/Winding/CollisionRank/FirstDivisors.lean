import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.GaussianForest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.DivisorEstimate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.LogRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ExponentTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GapSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ScalarStability
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw

/-! # Precision exponents of common factors at the first disconnected-circuit return -/

open Real Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
open SharpOccupation EmptyVisitFlux
noncomputable section

private theorem turns_ratio {I : Type*} {n : ℕ} (leaf root : Fin (n+1) → I) (E : I → ℝ) :
    forestRatio leaf root (fun i => -E i/(2*π))=forestRatio leaf root E := by
  funext j
  unfold forestRatio
  rw [←sub_div,←sub_div,neg_sub_neg,neg_sub_neg,
    div_div_div_cancel_right₀ (show (2:ℝ)*π ≠ 0 by positivity)]
  rw [←neg_sub (E (leaf j.succ)),←neg_sub (E (leaf 0)),neg_div_neg_eq]

/-- If l independent equal-residue constraints hold at a deep first return,
their common modulus has upper precision exponent (D−1−l)/l. The sites of
the residue classes and the observation origin may depend on the draw. -/
theorem gaussian_first_divisor_exponent :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ A > (0:ℝ), ∀ a > (0:ℝ), ∀ s : ℕ, s+1 < N → ∀ n : ℕ, 0 < n →
        ∀ leaf root : Fin (n+1) → (Fin N → Bool), Function.Injective leaf → (∀ i j, root i ≠ leaf j) →
          ∀ h : ℝ, (((D-2:ℕ):ℝ)-(n:ℝ))/((n:ℝ)+1) < h →
          ∀ᶠ ε in 𝓝[>] (0:ℝ),
            let v := firstVisit H a s ε
            let R := physicalArc (A*ε)
            (∃ b z, Anchored w v R b z) ∧
              ∀ b z, Anchored w v R b z → ∀ d : ℕ, 0 < d →
                (∀ i, (d:ℤ) ∣ z (leaf i)-z (root i)) → log (d:ℝ)/log (1/ε) < h := by
  filter_upwards [gaussian_gap_clock,DisconnectedReturns.gaussian_disconnected_scalar_return,
    gaussian_forest_ratios,gaussian_path_all_prefixes_maximally_projective] with ω hspec hstab hforest hsimple k
  intro N D H w
  obtain ⟨A,hA,hcontrol⟩ := hstab (k+1)
  refine ⟨A,hA,?_⟩
  intro a ha s hs n hn leaf root hi hd h hh
  let v := fun ε => firstVisit H a s ε
  let D' : ℝ := (D-2:ℕ)
  have hs' : s < k+1+1 := by dsimp only [N] at hs; omega
  have control := fun t ε => hcontrol t ε s hs'
  obtain ⟨e,hg,hy⟩ := hspec k
  have rate := exponent_of_scalar_control H e s hA control hg hy ha
  have hcard : 3 ≤ D := (by decide : 3 ≤ 2^3).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  change Tendsto (fun ε => log (v ε)/log (1/ε)) _ (𝓝 ((D-3+1:ℕ):ℝ)) at rate
  rw [show D-3+1=D-2 by omega] at rate
  obtain ⟨η,hη,hgap⟩ := choose_ratio_slack hn hh
  let b := ((n:ℝ))⁻¹+η
  have hb : 0 ≤ b := add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hη.le
  have hNV : ¬KleinbockMargulis.VWA (forestRatio leaf root w) := by
    dsimp only [w]
    rw [turns_ratio]
    exact hforest k n leaf root hn hi hd
  let g := w (leaf 0)-w (root 0)
  have hg' : g ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    change -_/ (2*π) = -_/ (2*π) at heq
    have hEE := neg_injective ((div_left_inj' (show (2:ℝ)*π ≠ 0 by positivity)).mp heq)
    exact hd 0 0 ((hsimple k).injective hEE).symm
  obtain ⟨C,hC⟩ := forest_divisor_estimate leaf root w hg' hNV hη
  have hcut := eventual_divisor_rate hb hA hgap rate C
  have hdate := modulus_window (m:=0) (show 0 < 1+1/|g| by positivity)
    (fun ε hε => ha.trans_le (firstVisit_isLeast H a s hε).1.1)
    (show ((0:ℕ):ℝ) < D' by dsimp only [D']; exact_mod_cast (show 0<D-2 by omega)) rate
  filter_upwards [hcut,hdate,Ioo_mem_nhdsGT (div_pos (sqrt_pos.mpr zero_lt_two) hA)] with ε hcut hv he
  intro t R
  rw [pow_zero,mul_one] at hv
  have ht : 1 ≤ t := (le_add_of_nonneg_right (one_div_nonneg.mpr (abs_nonneg g))).trans hv.le
  have ht' : 1 < t*|g| := (div_lt_iff₀ (abs_pos.mpr hg')).mp
    ((le_add_of_nonneg_left zero_le_one).trans_lt hv)
  have herr : A*ε ∈ Ioo (0:ℝ) (sqrt 2) := ⟨mul_pos hA he.1,by
    simpa only [mul_comm A] using (lt_div_iff₀ hA).mp he.2⟩
  have hR := (physicalArc_spec herr.1 herr.2).1
  have hR₁ : R ≤ 1 := hR.2.le.trans (by norm_num)
  have hfit := control t ε (firstVisit_isLeast H a s he.1).1.2
  refine ⟨(anchored_iff hR.1.le).mp ((physical_visit H herr.1 herr.2 t).mpr hfit),?_⟩
  intro base z hz d hd₀ hdiv
  have hlog := hC t R ht ⟨hR.1,hR₁⟩ (hR₁.trans_lt ht') base z hz d hd₀ hdiv
  apply hcut d
  apply hlog.trans
  have hbnd := (ShortTimeProducts.physical_arc_bounds herr.1 herr.2).2
  have hlog' := log_le_log hR.1 (hbnd.trans (half_le_self herr.1.le))
  linarith only [hlog']

#print axioms gaussian_first_divisor_exponent
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
