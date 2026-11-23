import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.FiniteSchedules.Clearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.BinaryCompiler

/-! # Same-error transport throughout an exponential physical interval -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
open MaximumIntervals
noncomputable section

private theorem grid_date {D : ℕ} (hD : 0 < D) (a v : ℝ) (hv : v ∈ Icc a (a+(D:ℝ))) :
    ∃ i < D, a+(i:ℝ) ≤ v ∧ v ≤ a+(i:ℝ)+1 := by
  by_cases h : v-a < (D:ℝ)
  · refine ⟨⌊v-a⌋₊,(Nat.floor_lt (sub_nonneg.mpr hv.1)).mpr h,?_,?_⟩
    · linarith only [Nat.floor_le (sub_nonneg.mpr hv.1)]
    · linarith only [Nat.lt_floor_add_one (v-a)]
  · refine ⟨D-1,by omega,?_,?_⟩
    all_goals rw [Nat.cast_sub (by omega : 1≤D),Nat.cast_one]
    · linarith only [le_of_not_gt h]
    · linarith only [hv.2]

/-- On each exponentially long observation, fits at any two dates use
the same tolerance. The extra gates cost at most a subexponential factor
times the physical volume swept between the dates. The starting dates
may be selected from the full frozen chain before choosing the error. -/
theorem gaussian_same_error_transport :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℕ → ℝ,
      let E := exceptionalTolerances (scheduleHeight ω fun k i => a k+(i:ℝ))
      dimH E=0 ∧ ∀ e > (0:ℝ), e∉E → ∃ C : ℕ, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        let I := Icc (a k) (a k+(2:ℝ)^N)
        ∀ v ∈ I, ∀ w ∈ I, ∀ s : ℕ, HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val v) →
          ∃ j : ℕ, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val w) ∧
            (j:ℝ) ≤ (s:ℝ)+(N:ℝ)*(4+|w-v|)*2^(5*(C*N).sqrt+17) := by
  filter_upwards [LocalPatches.gaussian_binary_precision_compiler] with ω hcompile
  intro a E
  let τ (k i : ℕ) : ℝ := a k+(i:ℝ)
  refine ⟨dimH_exceptionalTolerances _,?_⟩
  intro e he hre
  obtain ⟨c,hc⟩ := schedule_clearance ω τ e he hre
  refine ⟨c+3,?_⟩
  filter_upwards [hc,(tendsto_add_atTop_nat 1).eventually hcompile] with k hk hs
  intro N H I v hv w hw s hfit
  let D := 2^N
  let d := (c+3)*N
  let δ := 1/(2:ℝ)^(c*N)
  let F := (2:ℝ)^(5*d.sqrt+17)
  have hd : N ≤ d := by dsimp only [d]; rw [Nat.add_mul]; omega
  have hN : 0 < N := by dsimp only [N]; omega
  have hD : 0 < D := Nat.pow_pos (by decide) _
  have hD' : (D:ℝ)=(2:ℝ)^N := by simp only [D,Nat.cast_pow,Nat.cast_ofNat]
  have hN' : (N:ℝ) ≤ (D:ℝ) := by exact_mod_cast (Nat.lt_two_pow_self (n:=N)).le
  have hD₂ : (2:ℝ) ≤ D := by
    exact_mod_cast (show 2^1 ≤ 2^N from Nat.pow_le_pow_right (by decide) hN)
  have sim (t : ℝ) (ht : |t| ≤ (D:ℝ)) :
      ∃ l : ℕ, HasProjectiveCircuitApproximation N δ l (unitaryEvolution H.val t) ∧
        (l:ℝ) ≤ (N:ℝ)*(1+|t|)*F := by
    apply hs t (c*N) d hd
    have h₁ : 1+|t| ≤ (D:ℝ)^2 := by
      have h := mul_le_mul_of_nonneg_right hD₂ (Nat.cast_nonneg (α:=ℝ) D)
      nlinarith only [h,hD₂,ht]
    calc _ ≤ (2:ℝ)^(c*N)*((D:ℝ)*(D:ℝ)^2) := mul_le_mul_of_nonneg_left
           (mul_le_mul hN' h₁ (by positivity) (Nat.cast_nonneg D)) (by positivity)
         _ = _ := by
           rw [hD',show d=c*N+N+(N*2) by dsimp only [d]; rw [Nat.add_mul]; omega,
             pow_add (2:ℝ) (c*N+N) (N*2),pow_add (2:ℝ) (c*N) N,pow_mul (2:ℝ) N 2]
           ring
  have hv' : v ∈ Icc (a k) (a k+(D:ℝ)) := by rwa [hD']
  have hw' : w ∈ Icc (a k) (a k+(D:ℝ)) := by rwa [hD']
  obtain ⟨i,hi,hzv,hvz⟩ := grid_date hD (a k) v hv'
  let z := τ k i
  have hclose : |z-v| ≤ 1 := by rw [abs_of_nonpos (sub_nonpos.mpr hzv)]; linarith only [hvz]
  have hz : z ∈ Icc (a k) (a k+(D:ℝ)) :=
    ⟨le_add_of_nonneg_right (Nat.cast_nonneg i),add_le_add_right (by exact_mod_cast hi.le) _⟩
  have hoff : |w-z| ≤ (D:ℝ) := abs_le.mpr ⟨by linarith only [hw'.1,hz.2],by linarith only [hw'.2,hz.1]⟩
  obtain ⟨l,hl,hlprice⟩ := sim (z-v) (hclose.trans (by linarith only [hD₂]))
  obtain ⟨j,hj,hjprice⟩ := sim (w-z) hoff
  have hx := affordable_add_time H hfit hl
  rw [show v+(z-v)=z by ring] at hx
  have hy := affordable_add_time H (hk i hi (s+l) hx) hj
  rw [show τ k i+(w-z)=w by dsimp only [z]; ring,sub_add_cancel] at hy
  refine ⟨s+l+j,hy,?_⟩
  have hdist : |w-z| ≤ |w-v|+|z-v| := by
    have h := abs_add_le (w-v) (v-z)
    rwa [sub_add_sub_cancel,abs_sub_comm v z] at h
  have hstep : 1+|z-v|+(1+|w-z|) ≤ 4+|w-v| := by linarith only [hclose,hdist]
  have htotal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (α:=ℝ) N))
    (show 0 ≤ F by dsimp only [F]; positivity)
  push_cast
  change (s:ℝ)+l+j ≤ (s:ℝ)+N*(4+|w-v|)*F
  linarith only [hlprice,hjprice,htotal]

#print axioms gaussian_same_error_transport
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
