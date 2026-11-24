import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.StridedVisits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.WindowSize
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ExponentTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GapSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ScalarStability

/-! # Almost all eigenphase windings remain distinct at the first deep visit -/

open Real Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- On each typical prefix, at every budget below N−1, all sufficiently
deep first visits have a winding in an O(ε) arc. For every h up to 2^N−3,
every modulus at least K Q^h distinguishes more than h nonzero residues
among the 2^N winding coordinates. -/
theorem gaussian_first_visit_residues :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ A > (0:ℝ), ∃ K : ℕ, 1 < K ∧ ∀ a > (0:ℝ), ∀ s : ℕ, s+1 < N →
        ∀ᶠ ε in 𝓝[>] (0:ℝ),
          let v := firstVisit H a s ε
          let lo := K*(meshOrder ε)^(2^N-3)
          a*((2*lo:ℕ):ℝ) < v ∧ (∃ b z, Anchored w v (physicalArc (A*ε)) b z) ∧
            ∀ b z, Anchored w v (physicalArc (A*ε)) b z → ∀ h : ℕ, h ≤ 2^N-3 →
              ∀ d : ℕ, K*(meshOrder ε)^h ≤ d → h < (residues z d).card := by
  filter_upwards [gaussian_gap_clock,DisconnectedReturns.gaussian_disconnected_scalar_return] with ω hspec hstab k
  intro N H w
  obtain ⟨A,hA,hcontrol⟩ := hstab (k+1)
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 (π*A))
  have hKnat : 1 < K := by exact_mod_cast ((le_max_left ..).trans_lt hK : (1:ℝ) < K)
  have hKpos : (0:ℝ) < K := zero_lt_one.trans ((le_max_left ..).trans_lt hK)
  refine ⟨A,hA,K,hKnat,?_⟩
  intro a ha s hs
  have hs' : s < k+1+1 := by dsimp only [N] at hs; omega
  obtain ⟨e,hg,hy⟩ := hspec k
  have control := fun t ε => hcontrol t ε s hs'
  have hrate := exponent_of_scalar_control H e s hA control hg hy ha
  let m := 2^N-3
  have hwindow := modulus_window (m:=m) (mul_pos (mul_pos ha zero_lt_two) hKpos)
    (fun ε hε => ha.trans_le (firstVisit_isLeast H a s hε).1.1)
    (show (m:ℝ) < ((m+1:ℕ):ℝ) by exact_mod_cast Nat.lt_succ_self m) hrate
  filter_upwards [hwindow,Ioo_mem_nhdsGT (zero_lt_one' ℝ),
    Ioo_mem_nhdsGT (div_pos (sqrt_pos.mpr zero_lt_two) hA)] with ε hv hε hsmall
  intro v lo
  have he : ε ∈ Ioo (0:ℝ) (sqrt 2) := ⟨hε.1,hε.2.trans_le (one_le_sqrt.mpr (by norm_num))⟩
  have he' : A*ε ∈ Ioo (0:ℝ) (sqrt 2) := ⟨mul_pos hA hε.1,by
    simpa only [mul_comm A] using (lt_div_iff₀ hA).mp hsmall.2⟩
  have hr := (physicalArc_spec he'.1 he'.2).1.1
  have hfit := control v ε (firstVisit_isLeast H a s hε.1).1.2
  have hl := (anchored_iff hr.le).mp ((physical_visit H he'.1 he'.2 v).mpr hfit)
  have hdate : a*((2*lo:ℕ):ℝ) < v := by
    simpa only [lo,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hv
  refine ⟨hdate,hl,?_⟩
  intro b z hz h hh d hd
  obtain ⟨hQ,hgrid,_⟩ := meshOrder_bounds hε
  have hA' : A*π ≤ (K:ℝ) := by rw [mul_comm]; exact (le_max_right ..).trans hK.le
  have hcoef : A ≤ (K:ℝ)/π := (le_div_iff₀ pi_pos).mpr hA'
  have hR : physicalArc (A*ε) ≤ (K:ℝ)*(physicalArc ε/2) := calc
    _ ≤ A*ε/2 := (ShortTimeProducts.physical_arc_bounds he'.1 he'.2).2
    _ ≤ ((K:ℝ)/π)*ε/2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef hε.1.le) zero_le_two
    _ = (K:ℝ)*((ε/π)/2) := by ring
    _ ≤ _ := by gcongr; exact (ShortTimeProducts.physical_arc_bounds he.1 he.2).1
  have hlow : K*(meshOrder ε)^h ≤ lo := Nat.mul_le_mul_left K (Nat.pow_le_pow_right hQ hh)
  apply large_modulus_count H ha he hKnat hQ hgrid hr.le hR hd _ le_rfl hz
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 hlow)) ha.le).trans hdate.le

#print axioms gaussian_first_visit_residues
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
