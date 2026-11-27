import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.StartupLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # The gate deficit on either side of the first low visit -/

open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- An incoming circuit shifts each minimum by at most its gate count
when the two sums of approximation errors fit the comparison tolerances. -/
private theorem transfer_minimum {N s i j : ℕ} (H : selfAdjoint (Reg N)) {v t e f : ℝ}
    (hlo : e+1/20≤f) (hhi : e+f≤1/4)
    (hv : HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val v))
    (hi : HasProjectiveCircuitApproximation N (1/20) i (unitaryEvolution H.val t))
    (hj : IsLeast {m | HasProjectiveCircuitApproximation N (1/4) m (unitaryEvolution H.val t)} j) :
    ∃ r : ℕ, IsLeast {m | HasProjectiveCircuitApproximation N f m (unitaryEvolution H.val (v+t))} r ∧
      r ≤ s+i ∧ j ≤ s+r := by
  classical
  let A (m : ℕ) := HasProjectiveCircuitApproximation N f m (unitaryEvolution H.val (v+t))
  obtain ⟨z,hz,D,hD,hfit⟩ := affordable_add_time H hv hi
  have hf : A (s+i) := ⟨z,hz,D,hD,hfit.trans hlo⟩
  let hex : ∃ m, A m := ⟨_,hf⟩
  let r := Nat.find hex
  have hr : IsLeast {m | A m} r := ⟨Nat.find_spec hex,fun _ hm => Nat.find_min' hex hm⟩
  refine ⟨r,hr,hr.2 hf,hj.2 ?_⟩
  have hvisit : HasProjectiveCircuitApproximation N f r (unitaryEvolution H.val (v+t)) := hr.1
  obtain ⟨w,hw,D',hD',h'⟩ := affordable_add_time H (hv.neg_time H) hvisit
  rw [show -v+(v+t)=t by ring] at h'
  exact ⟨w,hw,D',hD',h'.trans hhi⟩

/-- Every sufficiently precise scalar visit replays the startup deficit at
one tenth. More generally an incoming s-gate circuit costs at most s on
either side of the two deficit bounds. -/
theorem gaussian_visit_deficit :
    ∃ a>0, ∃ b>0, ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (t : ℝ), a≤K * |t| → K*t^2≤b → ∀ (s : ℕ) (v e f : ℝ), e+1/20≤f → e+f≤1/4 →
        HasProjectiveCircuitApproximation (n+2) e s (unitaryEvolution H.val v) →
        let h := (a/(K * |t|))^(1/10:ℝ)
        ∃ r : ℕ, IsLeast {m | HasProjectiveCircuitApproximation (n+2) f m
          (unitaryEvolution H.val (v+t))} r ∧ c*K*h^9-s≤K-1-r ∧ K-1-r≤C*K*h^9+s := by
  obtain ⟨a,ha,b,hb,c,hc,C,hC,hw⟩ := gaussian_startup_deficit
  refine ⟨a,ha,b,hb,c,hc,C,hC,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro K H t hstart htime s v e f he hf hv h
  obtain ⟨i,hi,hlo,_⟩ := hn t hstart htime (1/20) (by constructor <;> norm_num)
  obtain ⟨j,hj,_,hhi⟩ := hn t hstart htime (1/4) (by constructor <;> norm_num)
  obtain ⟨r,hr,h₁,h₂⟩ := transfer_minimum H he hf hv hi.1 hj
  have hi' : (r:ℝ)≤(s:ℝ)+(i:ℝ) := by exact_mod_cast h₁
  have hj' : (j:ℝ)≤(s:ℝ)+(r:ℝ) := by exact_mod_cast h₂
  change c*K*h^9≤K-1-i at hlo
  change K-1-j≤C*K*h^9 at hhi
  exact ⟨r,hr,by linarith only [hi',hlo],by linarith only [hj',hhi]⟩

/-- At the actual first low visit after the first near-Hilbert crossing,
the minimum gate count at either sign of the lag has the same ninth-power
deficit as at identity, up to the incoming gate budget. -/
theorem gaussian_first_dip_deficit :
    ∃ a>0, ∃ b>0, ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (t : ℝ), a≤K * |t| → K*t^2≤b → ∀ s : ℕ,
        let v := RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s
        let h := (a/(K * |t|))^(1/10:ℝ)
        ∃ r : ℕ, IsLeast {m | HasProjectiveCircuitApproximation (n+2) (3/20) m
          (unitaryEvolution H.val (v+t))} r ∧
          c*K*h^9-s≤K-1-r ∧ K-1-r≤C*K*h^9+s ∧
          ∀ l : ℕ, HasProjectiveCircuitApproximation (n+2) (1/10) l (unitaryEvolution H.val (v+t)) →
            K-1-l≤C*K*h^9+s := by
  obtain ⟨a,ha,b,hb,c,hc,C,hC,hw⟩ := gaussian_visit_deficit
  refine ⟨a,ha,b,hb,c,hc,C,hC,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro K H t hstart htime s v h
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  obtain ⟨r,hr,hlow,hupper⟩ := hn t hstart htime s v (1/10) (3/20) (by norm_num) (by norm_num) hv
  refine ⟨r,hr,hlow,hupper,?_⟩
  rintro l ⟨z,hz,D,hD,hfit⟩
  have hrl : r ≤ l := hr.2 ⟨z,hz,D,hD,hfit.trans (by norm_num : (1/10:ℝ)≤3/20)⟩
  linarith only [hupper,(Nat.cast_le (α:=ℝ)).mpr hrl]

#print axioms gaussian_visit_deficit
#print axioms gaussian_first_dip_deficit
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
