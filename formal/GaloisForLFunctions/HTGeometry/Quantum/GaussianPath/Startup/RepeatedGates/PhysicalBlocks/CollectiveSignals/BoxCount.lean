import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.CompatibleCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.DisjointPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes

/-! # A lower bound on nonmerging gates from weak signals in disjoint boxes -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
open private box_controls from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes
noncomputable section

/-- On every chain, the number of calibrated packets times sin(t)⁸ is
bounded by the number of nonmerging calls in any fitting circuit. -/
theorem boxes_force_repeated_calls {n : ℕ} (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2))
    {t δ : ℝ} (hδ : 0≤δ) (hs : 0 < (sin t)^2) (herr : 252* |t| * δ≤(sin t)^2/4)
    (z : ℂ) (hz : ‖z‖=1)
    (he : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    ((goodBoxes (1/sqrt 2) δ ω ((n+1)/4)).card:ℝ)*(sin t)^8 ≤
      546*((redundant (circuitWord C):ℝ)+1) := by
  classical
  let F := goodBoxes (1/sqrt 2) δ ω ((n+1)/4)
  have hlen (k : F) : (k:ℕ) < (n+1)/4 := mem_range.mp (mem_filter.mp k.property).1
  let e (k : F) : Fin (n+1) := ⟨4*k.val+1,by have := hlen k; omega⟩
  let f (k : F) : Fin (n+1) := ⟨4*k.val+2,by have := hlen k; omega⟩
  let S k := tripleSites (e k) (f k)
  have hadj (k : F) : (e k).succ=(f k).castSucc := Fin.ext rfl
  have hsize (k : F) : 2 < (S k).card := by
    have h₁ := (e k).castSucc_lt_succ.ne
    have h₂ : (e k).castSucc≠(f k).succ := by
      intro h; have hh := congrArg Fin.val h; change 4*k.val+1=4*k.val+2+1 at hh; omega
    have h₃ : (e k).succ≠(f k).succ := by
      intro h; have hh := congrArg Fin.val h; change 4*k.val+1+1=4*k.val+2+1 at hh; omega
    simp [S,tripleSites,h₁,h₂,h₃]
  have idx (k : F) (a) (h : a∈S k) : a.val/4=k.val := by
    simp only [S,tripleSites,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl <;> dsimp only [e,f,Fin.val_succ,Fin.val_castSucc] <;> omega
  have hd (k l : F) (h : k≠l) : Disjoint (S k) (S l) :=
    disjoint_left.mpr fun a ha hb => h (Subtype.ext ((idx k a ha).symm.trans (idx l a hb)))
  let w := circuitWord C
  obtain ⟨T,_,x,y,hxy,hi,hcount⟩ := packet_selection w univ S (fun k _ => hsize k)
    (fun k _ l _ h => hd k l h)
  let v : Fin T.card ≃ T := T.equivFin.symm
  let j (a : Fin T.card) : F := (v a).val
  have hj (a) : j a∈T := (v a).property
  have hinj : Function.Injective j := Subtype.val_injective.comp v.injective
  have hbox (k : F) := box_controls (e:=e k) (f:=f k) (k:=k.val) rfl rfl
    (show goodBox (1/sqrt 2) δ ω k.val from (mem_filter.mp k.property).2)
    (show |1/sqrt 2-1/sqrt 2|≤δ by simpa only [sub_self,abs_zero] using hδ)
  have hbound := compatible_count (e ∘ j) (f ∘ j) (x ∘ j) (y ∘ j) (fun a => hadj (j a))
    (fun a b h => hd _ _ (hinj.ne h)) (fun a => (hxy _ (hj a)).1) (fun a => (hxy _ (hj a)).2.1)
    C (fun a => (hxy _ (hj a)).2.2) (fun a b h => hi _ (hj a) _ (hj b) (hinj.ne h))
    (pathPauliDisorderShell ω n) t (2*δ) (mul_nonneg two_pos.le hδ) hs
    (fun a => hbox (j a)) (by linarith only [herr]) z hz he
  let m : ℝ := T.card
  let R : ℝ := redundant w
  let s := (sin t)^4
  have hms : m*s≤16 := hbound
  have hs₀ : 0 ≤ s := by dsimp only [s]; positivity
  have hs₁ : s≤1 := by
    have hh := pow_le_one₀ (n:=4) (abs_nonneg (sin t)) (abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩)
    rwa [←abs_pow,abs_of_nonneg (by positivity : 0≤(sin t)^4)] at hh
  have hm₀ : 0 ≤ m := Nat.cast_nonneg _
  have hr₀ : 0≤R := Nat.cast_nonneg _
  have hms₀ := mul_nonneg hm₀ hs₀
  have hquad : m*(m+1)*s^2≤272 := by
    have hh := mul_self_le_mul_self hms₀ hms
    have hs' := mul_le_mul hms hs₁ hs₀ (by norm_num : (0:ℝ)≤16)
    linarith only [hh,hs']
  simp only [card_univ,Fintype.card_coe] at hcount
  have hc : (F.card:ℝ)≤2*R+(1+2*R)*(m*(m+1)) := by
    dsimp only [R,m]; exact_mod_cast hcount
  calc _ = (F.card:ℝ)*s^2 := by dsimp only [s,F]; ring
       _ ≤ (2*R+(1+2*R)*(m*(m+1)))*s^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
       _ ≤ 2*R+(1+2*R)*272 := by
         linarith only [mul_le_mul_of_nonneg_left hquad (by positivity : 0≤1+2*R),
           mul_le_mul_of_nonneg_left (pow_le_one₀ hs₀ hs₁ (n:=2)) (by positivity : 0≤2*R)]
       _ ≤ _ := by change _≤546*(R+1); linarith only

#print axioms boxes_force_repeated_calls
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
