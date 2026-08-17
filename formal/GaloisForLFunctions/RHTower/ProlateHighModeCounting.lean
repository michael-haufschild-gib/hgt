import GaloisForLFunctions.RHTower.ProlateHighModeOrthogonalRayleigh

/-!
# Counting the modes above a Rayleigh threshold

An `(n+1)`-dimensional space of even trial functions whose Rayleigh quotients all exceed `−K`
produces `n+1` linearly independent even joint band/prolate modes above `−K`.

The induction is one step of the orthogonality machine.  Given `k ≤ n` modes already produced, the
`(n+1)` trial coefficients satisfy only `k` orthogonality conditions against them, so some nonzero
combination of the trials is orthogonal to all of them; its Rayleigh quotient still exceeds `−K`, so
it meets a mode above the threshold, and that mode cannot lie in the span of the previous ones.

This is the counting half of the min–max principle in the form an excited oscillator ladder needs:
with the rung-`n` Hermite trial space it bounds the `(n+1)`-st separation constant from above.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Finset

namespace RHTower

/-- Being the band class of an even joint mode with prolate eigenvalue above `−K`. -/
def IsHighModeClass (c K : ℝ) (w : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : Prop :=
  ∃ (lam eta : ℝ) (Phi : ℝ → ℝ) (hPhic : Continuous Phi), lam ≠ 0 ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
    (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
    (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) ∧
    -K < eta ∧ GaloisForLFunctions.RHTower.bandClass Phi hPhic = w

/-- The band class of a finite linear combination. -/
theorem bandClass_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i, Continuous (F i)) (a : ι → ℝ)
    (hsum : Continuous fun x => ∑ i ∈ s, a i * F i x) :
    GaloisForLFunctions.RHTower.bandClass (fun x => ∑ i ∈ s, a i * F i x) hsum
      = ∑ i ∈ s, a i • GaloisForLFunctions.RHTower.bandClass (F i) (hF i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
  | insert j s hj ih =>
      have hcont : Continuous fun x => ∑ i ∈ s, a i * F i x :=
        continuous_finsetSum s fun i _ => continuous_const.mul (hF i)
      have hjc : Continuous fun x => a j * F j x := continuous_const.mul (hF j)
      have hstep : (fun x => ∑ i ∈ insert j s, a i * F i x)
          = fun x => a j * F j x + ∑ i ∈ s, a i * F i x := by
        funext x
        rw [Finset.sum_insert hj]
      have hsum2 : Continuous fun x => a j * F j x + ∑ i ∈ s, a i * F i x := hjc.add hcont
      rw [Finset.sum_insert hj]
      calc GaloisForLFunctions.RHTower.bandClass (fun x => ∑ i ∈ insert j s, a i * F i x) hsum
          = GaloisForLFunctions.RHTower.bandClass
              (fun x => a j * F j x + ∑ i ∈ s, a i * F i x) hsum2 :=
            GaloisForLFunctions.RHTower.bandClass_congr _ _ hstep
        _ = GaloisForLFunctions.RHTower.bandClass (fun x => a j * F j x) hjc
              + GaloisForLFunctions.RHTower.bandClass (fun x => ∑ i ∈ s, a i * F i x) hcont :=
            GaloisForLFunctions.RHTower.bandClass_add hjc hcont hsum2
        _ = a j • GaloisForLFunctions.RHTower.bandClass (F j) (hF j)
              + ∑ i ∈ s, a i • GaloisForLFunctions.RHTower.bandClass (F i) (hF i) := by
            rw [GaloisForLFunctions.RHTower.bandClass_smul (hF j) (a j) hjc, ih hcont]

/-- **The counting theorem.**  An `(n+1)`-dimensional trial space above the threshold produces
`n+1` linearly independent modes above the threshold. -/
theorem exists_linearIndependent_highModeClasses {c K : ℝ} (hc0 : 0 < c) (n : ℕ)
    (G : Fin (n + 1) → ℝ → ℝ)
    (hGsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G i))
    (hGeven : ∀ i, Function.Even (G i))
    (hray : ∀ a : Fin (n + 1) → ℝ, a ≠ 0 →
      -K * (∫ x in (-1 : ℝ)..1, (∑ i, a i * G i x) * (∑ i, a i * G i x))
        < ∫ x in (-1 : ℝ)..1,
            prolateSLAction c (fun y => ∑ i, a i * G i y) x * (∑ i, a i * G i x)) :
    ∃ w : Fin (n + 1) → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1,
      LinearIndependent ℝ w ∧ ∀ i, IsHighModeClass c K (w i) := by
  classical
  set v : Fin (n + 1) → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
    fun i => GaloisForLFunctions.RHTower.bandClass (G i) (hGsm i).continuous with hv
  have main : ∀ k : ℕ, k ≤ n + 1 →
      ∃ w : Fin k → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1,
        LinearIndependent ℝ w ∧ ∀ i, IsHighModeClass c K (w i) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
    | succ k ih =>
        intro hk
        obtain ⟨w, hwindep, hwmode⟩ := ih (by omega)
        -- a trial combination orthogonal to the modes already found
        set comb : (Fin (n + 1) → ℝ) →ₗ[ℝ] GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
          Fintype.linearCombination ℝ v with hcomb
        set L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
          LinearMap.pi fun i => (innerSL ℝ (w i)).toLinearMap.comp comb with hL
        have hrank : Module.finrank ℝ (LinearMap.ker L) ≠ 0 := by
          have hrn := L.finrank_range_add_finrank_ker
          have hle : Module.finrank ℝ (LinearMap.range L) ≤ k := by
            have h1 : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (Fin k → ℝ) :=
              Submodule.finrank_le _
            simpa using h1
          have hdom : Module.finrank ℝ (Fin (n + 1) → ℝ) = n + 1 := by simp
          omega
        have hker : LinearMap.ker L ≠ ⊥ := by
          intro hbot
          rw [hbot] at hrank
          simp at hrank
        obtain ⟨a, hamem, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
        -- the trial function
        set g : ℝ → ℝ := fun x => ∑ i, a i * G i x with hg
        have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
          ContDiff.sum fun i _ => (contDiff_const).mul (hGsm i)
        have hgeven : Function.Even g := by
          intro x
          simp only [hg]
          exact Finset.sum_congr rfl fun i _ => by rw [hGeven i x]
        have hgclass : GaloisForLFunctions.RHTower.bandClass g hgsm.continuous = comb a := by
          rw [hcomb, Fintype.linearCombination_apply]
          exact bandClass_finsetSum Finset.univ G (fun i => (hGsm i).continuous) a hgsm.continuous
        -- orthogonality to the span of the modes found so far
        set W : Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :=
          Submodule.span ℝ (Set.range w) with hW
        have hgW : GaloisForLFunctions.RHTower.bandClass g hgsm.continuous ∈ Wᗮ := by
          rw [hW]
          refine (Submodule.mem_orthogonal _ _).2 ?_
          intro u hu
          induction hu using Submodule.span_induction with
          | mem x hx =>
              obtain ⟨i, rfl⟩ := hx
              have hker' : L a = 0 := hamem
              have hi := congrFun hker' i
              simpa [hL, hgclass] using hi
          | zero => simp
          | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
          | smul r x hx ihx => rw [real_inner_smul_left, ihx, mul_zero]
        -- a new mode outside that span
        obtain ⟨lam, eta, Phi, hPhic, hlam, hsm, hne, heven, hband, hprolate, hgt, hnotmem⟩ :=
          exists_high_mode_notMem_of_orthogonal_trial hc0 hgsm hgeven (hray a hane) W hgW
        refine ⟨Fin.cons (GaloisForLFunctions.RHTower.bandClass Phi hPhic) w, ?_, ?_⟩
        · exact hwindep.finCons hnotmem
        · intro i
          refine Fin.cases ?_ ?_ i
          · exact ⟨lam, eta, Phi, hPhic, hlam, hsm, hne, heven, hband, hprolate, hgt, rfl⟩
          · intro j
            simpa using hwmode j
  exact main (n + 1) le_rfl

end RHTower

end
