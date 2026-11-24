import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.TwoWirePhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.RobustReflection

/-! # Projective circuit entropy from a control choice on each target wire -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking
open DiagonalSynthesis SpectralSorting
noncomputable section
variable {m h : ℕ}

private def pairSign (p : Bool × Bool) : ℂ := if p.1 && p.2 then -1 else 1

/-- Each target takes a controlled-Z gate from its selected control. -/
def controlSign (f : Fin h → Fin m) (x : Fin (m+h) → Bool) : ℂ :=
  ∏ j, pairSign (x ((f j).castAdd h),x (Fin.natAdd m j))

def controlMatrix (f : Fin h → Fin m) : Register (m+h) := diagonal (controlSign f)

theorem realizes_controlMatrix (f : Fin h → Fin m) : Realizes h (controlMatrix f) := by
  have hc (j : Fin h) : (f j).castAdd h ≠ Fin.natAdd m j := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    omega
  simpa only [controlMatrix,controlSign,Finset.card_univ,Fintype.card_fin] using
    realizes_phase_product Finset.univ (fun j x => pairSign (x ((f j).castAdd h),x (Fin.natAdd m j)))
      (fun j _ => realizes_pair_phase _ _ (hc j) pairSign (fun p => by
        unfold pairSign; split <;> simp))

private def probe (i : Fin m) (j : Fin h) : Fin (m+h) → Bool :=
  Fin.addCases (fun a => decide (a=i)) (fun b => decide (b=j))

private theorem probe_sign (f : Fin h → Fin m) (i : Fin m) (j : Fin h) :
    controlSign f (probe i j)=if f j=i then -1 else 1 := by
  classical
  unfold controlSign
  rw [Finset.prod_eq_single j]
  · simp [pairSign,probe,Fin.addCases_left,Fin.addCases_right]
  · intro b _ hb
    simp [pairSign,probe,Fin.addCases_right,hb]
  · simp

private theorem sign_entry (f g : Fin h → Fin m) (z : ℂ) (x : Fin (m+h) → Bool) :
    ‖controlSign f x-z*controlSign g x‖ ≤ ‖controlMatrix f-z • controlMatrix g‖ := by
  simpa only [controlMatrix,Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,smul_eq_mul]
    using norm_entry_le_l2_opNorm (controlMatrix f-z • controlMatrix g) x x

/-- The empty bit string agrees for every codeword. A bit string with
one control and one target distinguishes any two different choices.
The two entries force projective separation at least √2. -/
theorem controlMatrix_separated {f g : Fin h → Fin m} (hfg : f≠g) (z : ℂ) (hz : ‖z‖=1) :
    Real.sqrt 2 ≤ ‖controlMatrix f-z • controlMatrix g‖ := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hfg
  let M := ‖controlMatrix f-z • controlMatrix g‖
  have ha : ‖(1:ℂ)-z‖≤M := by
    simpa [controlSign,pairSign] using sign_entry f g z (fun _ => false)
  have hb : ‖(1:ℂ)+z‖≤M := by
    have hh := sign_entry f g z (probe (f j) j)
    rw [probe_sign,if_pos rfl,probe_sign,if_neg hj.symm,mul_one] at hh
    simpa only [show (-1:ℂ)-z= -(1+z) by ring,norm_neg] using hh
  have hh := parallelogram_law_with_norm ℂ (1:ℂ) z
  rw [hz,norm_one] at hh
  refine Real.sqrt_le_iff.mpr ⟨norm_nonneg _,?_⟩
  linarith only [hh,pow_le_pow_left₀ (norm_nonneg _) ha 2,pow_le_pow_left₀ (norm_nonneg _) hb 2]

/-- Even arbitrary matrix centers with free global phases need at least
mʰ distinct elements to cover all h-gate circuits on m+h wires. -/
theorem circuit_net_card_lower {r : ℝ} (hr : 2*r<Real.sqrt 2) (net : Finset (Register (m+h)))
    (hnet : ∀ U : Register (m+h), Realizes h U →
      ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r) : m^h ≤ net.card := by
  classical
  by_contra! hsmall
  obtain ⟨f,hf⟩ := exists_projectively_far_from_small_net (controlMatrix (m:=m) (h:=h))
    _ r (fun hne => controlMatrix_separated hne) hr net
    (by simpa only [Fintype.card_fun,Fintype.card_fin] using hsmall)
  obtain ⟨W,hW,z,hz,he⟩ := hnet _ (realizes_controlMatrix f)
  exact (hf W hW z hz).not_ge he

#print axioms circuit_net_card_lower
end
end GaloisForLFunctions.HTGeometry.TimePacking
