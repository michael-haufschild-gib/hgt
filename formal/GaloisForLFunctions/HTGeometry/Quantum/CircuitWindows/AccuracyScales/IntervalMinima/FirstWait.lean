import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.LogarithmicGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.ScalarWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Relative stability of the actual first physical visit at a regular error -/

open Filter Set Real MeasureTheory
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals PrecisionReturns
noncomputable section

/-- From any sequence of origins fixed before the tolerance, including
the first robust crossings, tightening and loosening by the same
exponential precision give logarithmic first waits within D⁻ᵇ.
All gate budgets and their actual chronological first visits are included. -/
theorem gaussian_first_wait_tolerance (b : ℕ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℕ → ℝ, ∃ E : Set ℝ, dimH E=0 ∧
      ∀ e > (0:ℝ), e ∉ E → ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        let h := min (e/2) (1/(2:ℝ)^(c*N))
        ∀ s : ℕ, let x := firstVisit H (a k) s (e+h)-a k
          let y := firstVisit H (a k) s (e-h)-a k
          x ≤ y ∧ 1+y ≤ (1+x)*exp (1/(2:ℝ)^(b*N)) := by
  obtain ⟨C,hC⟩ := SpectralJets.HighPrecision.gaussian_fine_scalar_windows
  filter_upwards [hC] with ω hω a
  let M := C+b+2
  let B (k : ℕ) := M*(k+3)
  have hM : 0 < M := by dsimp only [M]; omega
  have hB : StrictMono B := fun i j hij => Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 3) hM
  have hn (k : ℕ) : k+3 ≤ B k := Nat.le_mul_of_pos_left _ hM
  obtain ⟨E,hE,hh⟩ := interval_clearance ω (fun k _ => a k) (fun k => logMesh (k+3) b) B hB hn
  refine ⟨E,hE,?_⟩
  intro e he hr
  obtain ⟨q,hq⟩ := hh e he hr
  obtain ⟨K,hK⟩ := exists_nat_gt (1/e)
  refine ⟨q*M,?_⟩
  filter_upwards [hω,hq,eventually_ge_atTop K] with k hfill hclear hk
  intro N H h s x y
  let D := 2^N
  have hpos : 0 < h := lt_min (half_pos he) (by positivity)
  have hle : h ≤ 1/(2:ℝ)^(q*B k) := by
    change min _ (1/(2:ℝ)^(q*M*N)) ≤ 1/(2:ℝ)^(q*(M*N))
    rw [Nat.mul_assoc]; exact min_le_right _ _
  have hup : 0 < e+h := add_pos he hpos
  have hlow : 0 < e-h := sub_pos.mpr ((min_le_left ..).trans_lt (half_lt_self he))
  let v := firstVisit H (a k) s (e+h)
  let w := firstVisit H (a k) s (e-h)
  obtain ⟨⟨hv,hfit⟩,hfirst⟩ := firstVisit_isLeast H (a k) s hup
  obtain ⟨⟨hw,hfit'⟩,hlater⟩ := firstVisit_isLeast H (a k) s hlow
  have mono : v ≤ w := by
    obtain ⟨z,hz,F,hF,herr⟩ := hfit'
    exact hfirst ⟨hw,z,hz,F,hF,herr.trans (by linarith only [hpos])⟩
  refine ⟨sub_le_sub_right mono _,?_⟩
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hKD : K ≤ 2^D := hk.trans ((show k ≤ N by dsimp only [N]; omega).trans
    ((Nat.lt_two_pow_self (n:=N)).le.trans (Nat.lt_two_pow_self (n:=D)).le))
  have hε : 1/(2:ℝ)^D ≤ e := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (1:ℝ)/e ≤ (2:ℝ)^D := hK.le.trans (by exact_mod_cast hKD)
    rw [div_le_iff₀ he] at hh
    simpa only [mul_comm] using hh
  obtain ⟨u,hu,z,hz,F,hF,herr⟩ := hfill (a k)
  have hvu : v ≤ u := hfirst ⟨hu.1,z,hz,F,hF.trans (Nat.zero_le _),herr.trans (hε.trans
    (le_add_of_nonneg_right hpos.le))⟩
  have hx : 0 ≤ x := sub_nonneg.mpr hv
  have hcap : x ≤ (2:ℝ)^(D^C) := by change v-a k ≤ _; linarith only [hvu,hu.2]
  obtain ⟨i,hi,hxi,hbound⟩ := round_wait hN C b hx hcap
  let T := logMesh N b i
  have hT : max T 0 = T := max_eq_left (hx.trans hxi)
  have hvI : v ∈ Icc (a k) (a k+max T 0) := by
    rw [hT]; exact ⟨hv,by change v-a k ≤ T at hxi; linarith only [hxi]⟩
  obtain ⟨z,hz,F,hF,herr⟩ := hfit
  obtain ⟨v',hv',z',hz',F',hF',herr'⟩ := hclear i hi s v hvI
    ⟨z,hz,F,hF,herr.trans (add_le_add_left hle _)⟩
  have hwv : w ≤ v' := hlater ⟨hv'.1,z',hz',F',hF',herr'.trans (sub_le_sub_left hle _)⟩
  have htime : v' ≤ a k+T := hv'.2.trans_eq (congrArg (a k+·) hT)
  change 1+(w-a k) ≤ _
  apply le_trans _ hbound
  change 1+(w-a k) ≤ 1+T
  linarith only [hwv,htime]

#print axioms gaussian_first_wait_tolerance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
