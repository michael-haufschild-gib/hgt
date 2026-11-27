import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.LocalContraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality.PacketFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.PacketSelection

/-! # Repeated gate calls forced by a family of fixed-width triples -/
open Finset Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- A family of disjoint enlarged triples with controlled local
perturbations forces a number of nonmerging calls proportional to its
size times sin(t)⁴. The perturbation threshold is independent of t. -/
theorem fixed_triples_fourth_power {n : ℕ} {ι : Type*} [Fintype ι] (e f : ι→Fin (n+1))
    (hadj : ∀ a, (e a).succ=(f a).castSucc) (u : PathShell n)
    (C : TwoQubitCircuit (n+2)) {t : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (z : ℂ) (hz : ‖z‖=1) (he : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    let S a := tripleSites (e a) (f a)
    let N a := incidentSites (S a)
    let d a := ‖pathHamiltonian (packetPerturbation (e a) (f a) u)‖
    let E a := ∑ l∈(N a).biUnion pathIncidentLabels, |u l|
    (∀ a b, a≠b → Disjoint (N a) (N b)) → (∀ a, 4*d a*(2*E a+d a)≤1/256) →
      (Fintype.card ι:ℝ)*(sin t)^4≤514*((redundant (circuitWord C):ℝ)+1) := by
  classical
  intro S N d E hsep hcal
  let w := circuitWord C
  have hs (a : ι) : S a⊆N a := subset_union_left
  have hcard (a : ι) : 2<(S a).card := by rw [show (S a).card=3 from tripleSites_card (hadj a)]; decide
  obtain ⟨T,_,x,y,hxy,hi,hcount⟩ := ForestOrder.linear_packet_selection w univ S (fun a _ => hcard a)
    (fun a _ b _ hab => (hsep a b hab).mono (hs a) (hs b))
  let v : Fin T.card ≃ T := T.equivFin.symm
  let j (a : Fin T.card) : ι := (v a).val
  have hj (a : Fin T.card) : j a∈T := (v a).property
  have hinj : Function.Injective j := Subtype.val_injective.comp v.injective
  have hmiss (a : Fin T.card) := (hxy _ (hj a)).2.2
  have hne (a : Fin T.card) : x (j a)≠y (j a) := fun h => hmiss a (h ▸ knows_self _ _)
  choose K hKs hKn hmean hfit using fun a : Fin T.card =>
    fixed_width_reporter (hadj (j a)) (hxy _ (hj a)).1 (hxy _ (hj a)).2.1 (hne a) u ht (hcal (j a))
  have hr : 0<(sin t)^2/2 := half_pos (sq_pos_of_pos ((half_pos ht.1).trans_le (short_sine ht)))
  have hb := compatible_reporter_count (e ∘ j) (f ∘ j) (x ∘ j) (y ∘ j) (N ∘ j)
    (fun a => hadj (j a)) (fun a => hs (j a)) (fun a b hab => hsep _ _ (hinj.ne hab))
    (fun a => (hxy _ (hj a)).1) (fun a => (hxy _ (hj a)).2.1) C hmiss
    (fun a b hab => hi _ (hj a) _ (hj b) (hinj.ne hab))
    _ (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t) K _ hr hKn hKs hmean
    (fun a => (hfit a).trans (by linarith only [sq_nonneg (sin t)])) z hz he
  let m : ℝ := T.card
  let R : ℝ := redundant w
  have hms : m*((sin t)^2/2)^2≤16 := hb
  have hscale : m*(sin t)^4≤64 := by linarith only [hms]
  have hle : (sin t)^4≤1 := by
    simpa only [←abs_pow,abs_of_nonneg (pow_nonneg ((half_pos ht.1).trans_le (short_sine ht)).le 4)] using
      pow_le_one₀ (n:=4) (abs_nonneg (sin t)) (abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩)
  simp only [card_univ] at hcount
  have hc : (Fintype.card ι:ℝ)≤2*R+(1+2*R)*(4*m) := by
    dsimp only [R,m]
    exact_mod_cast hcount
  have hR : 0≤R := Nat.cast_nonneg _
  change (Fintype.card ι:ℝ)*(sin t)^4≤514*(R+1)
  linarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg ((half_pos ht.1).trans_le (short_sine ht)).le 4),
    mul_le_mul_of_nonneg_left hscale (by positivity : 0≤1+2*R),
    mul_le_mul_of_nonneg_left hle (by positivity : 0≤2*R)]

#print axioms fixed_triples_fourth_power
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
