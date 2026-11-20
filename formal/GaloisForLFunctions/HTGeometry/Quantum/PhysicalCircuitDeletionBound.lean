import GaloisForLFunctions.HTGeometry.Quantum.InverseBandwidthCircuitCost
import GaloisForLFunctions.HTGeometry.Quantum.DisjointSiteCircuitApproximation
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.HTGeometry.SiteFactorLeafTransport

/-!
# Circuit cost at a physical energy gap

Removing terms incident on the sites used by a putative shortcut leaves a
propagator supported on disjoint sites. At half the period of an energy
gap its distance from a scalar detects the total interaction mass removed.
-/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem supported_product {n : ℕ} {S : Finset (Fin n)} {X Y : Reg n}
    (hx : IsSiteSupported S X) (hy : IsSiteSupported S Y) : IsSiteSupported S (X*Y) := by
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hx
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hy
  have he : liftLocalMatrix S B * liftLocalMatrix S C = liftLocalMatrix S (B*C) := by
    let Φ := Matrix.reindexAlgEquiv ℂ ℂ (configurationSplitEquiv (fun _ : Fin n => Bool) S)
    apply Φ.injective
    rw [map_mul]
    change Matrix.reindex _ _ _ * Matrix.reindex _ _ _ = Matrix.reindex _ _ _
    simp only [reindex_liftLocalMatrix_eq_kronecker_one,← Matrix.mul_kronecker_mul,mul_one]
  rw [he]
  exact isSiteSupported_liftLocalMatrix S _

private theorem twoQubitLift_supported {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    IsSiteSupported {a,b} (twoQubitLift a b hab U).val := by
  let I := {i : Fin n // i ≠ a ∧ i ≠ b}
  let rest (x : Fin n → Bool) := fun i : I => x i.1
  have entry (x y : Fin n → Bool) : (twoQubitLift a b hab U).val x y =
      U.val (x a,x b) (y a,y b) * (1 : Matrix (I → Bool) _ ℂ) (rest x) (rest y) := rfl
  constructor
  · rintro x y ⟨i,hi,hxy⟩
    have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
    have hrest : rest x ≠ rest y := fun h => hxy (congrFun h ⟨i,hi'⟩)
    rw [entry,Matrix.one_apply_ne hrest,mul_zero]
  · intro x y x' y' hxx hyy ho ho'
    have hr (v w : Fin n → Bool) (h : ∀ i, i ∉ ({a,b} : Finset (Fin n)) → v i = w i) : rest v = rest w := by
      funext i
      exact h i.1 (by simpa using i.2)
    rw [entry,entry,hr x y ho,hr x' y' ho',Matrix.one_apply_eq,Matrix.one_apply_eq,
      hxx a (by simp),hxx b (by simp),hyy a (by simp),hyy b (by simp)]

/-- Any physical circuit is intrinsically supported on its touched sites,
even when the same qubit is reused in multiple gates. -/
theorem TwoQubitCircuit.isSiteSupported_touchedSites {n : ℕ} (C : TwoQubitCircuit n) :
    IsSiteSupported C.touchedSites C.eval.val := by
  let g (i : Fin C.gateCount) := C.architecture.gateLift i (C.gates i)
  have hg (i) : IsSiteSupported C.touchedSites (g i).val := by
    apply (twoQubitLift_supported _ _ (C.architecture.distinct i) (C.gates i)).mono
    have h1 : (C.architecture.sites i).1 ∈ C.touchedSites :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h2 : (C.architecture.sites i).2 ∈ C.touchedSites :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · rw [h]; exact h1
    · rw [Finset.mem_singleton.mp h]; exact h2
  have hp (l : List (Matrix.unitaryGroup (Fin n → Bool) ℂ))
      (hl : ∀ U ∈ l, IsSiteSupported C.touchedSites U.val) : IsSiteSupported C.touchedSites l.prod.val := by
    induction l with
    | nil => exact (isSiteSupported_one (B := fun _ : Fin n => Bool)).mono (Finset.empty_subset _)
    | cons a l ih =>
      exact supported_product (hl a List.mem_cons_self)
        (ih (fun U h => hl U (List.mem_cons_of_mem _ h)))
  apply hp ((List.ofFn g).reverse)
  intro U hu
  rw [List.mem_reverse,List.mem_ofFn] at hu
  obtain ⟨i,rfl⟩ := hu
  exact hg i

/-- At half the period of any chosen gap, a circuit pays for its error or
for the Hamiltonian interaction mass incident on the sites it uses. -/
theorem path_gap_circuit_deletion_floor {n : ℕ} (u : PathShell n)
    (i j : Fin (n+2) → Bool)
    (hgap : (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i ≠
      (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j)
    (C : TwoQubitCircuit (n+2)) (c : ℂ) :
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    let t := Real.pi/(E i-E j)
    let K := pathHamiltonianOnSites C.touchedSitesᶜ u
    1 ≤ ‖unitaryEvolution (pathHamiltonian u) t - c • (C.eval : Reg (n+2))‖ +
      2 * |t| * ‖pathHamiltonian u-K‖ := by
  let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let K : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites C.touchedSitesᶜ u⟩
  let E := H.2.isHermitian.eigenvalues
  let t := Real.pi/(E i-E j)
  obtain ⟨z,hz⟩ := truncated_local_evolution_scalar_bound disjoint_compl_left
    H K (pathHamiltonianOnSites_isSiteSupported C.touchedSitesᶜ u) _
    (C.isSiteSupported_touchedSites.complex_smul c) t
  exact (half_gap_time_scalar_error_ge_one H.2.isHermitian i j hgap z).trans hz

private def incident {n : ℕ} (v : Fin (n+2)) : PathLabel n → Prop
  | .inl (w,_) => w = v
  | .inr (e,_) => e.castSucc = v ∨ e.succ = v

private def incidentLabels {n : ℕ} (v : Fin (n+2)) : Finset (PathLabel n) := by
  classical
  exact Finset.univ.filter (incident v)

/-- Three onsite directions and at most nine Pauli couplings on either
incident edge meet a given site. Endpoints only decrease this count. -/
private theorem incidentLabels_card {n : ℕ} (v : Fin (n+2)) : (incidentLabels v).card ≤ 21 := by
  classical
  let code : PathLabel n → Fin 3 ⊕ ((Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3))
    | .inl (_,q) => .inl q
    | .inr (e,ab) => if e.castSucc = v then .inr (.inl ab) else .inr (.inr ab)
  have valid (l) (hl : l ∈ incidentLabels v) : incident v l := (Finset.mem_filter.mp hl).2
  have hinj : Set.InjOn code (↑(incidentLabels v)) := by
    intro l hl t ht eq
    have h := valid l hl
    have k := valid t ht
    rcases l with ⟨s,q⟩ | ⟨e,ab⟩ <;> rcases t with ⟨w,r⟩ | ⟨f,cd⟩
    · have hs : s = v := h
      have hw : w = v := k
      simpa [code,hs,hw] using eq
    · by_cases hf : f.castSucc = v <;> simp [code,hf] at eq
    · by_cases he : e.castSucc = v <;> simp [code,he] at eq
    · change e.castSucc = v ∨ e.succ = v at h
      change f.castSucc = v ∨ f.succ = v at k
      by_cases he : e.castSucc = v <;> by_cases hf : f.castSucc = v <;> simp [code,he,hf] at eq
      · have hef : e = f := Fin.castSucc_injective _ (he.trans hf.symm)
        simp [hef,eq]
      · have hef : e = f := Fin.succ_injective _ ((h.resolve_left he).trans (k.resolve_left hf).symm)
        simp [hef,eq]
  have hcard := Finset.card_le_card_of_injOn code (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_sum,Fintype.card_prod] using hcard

private theorem pathWord_none_of_not_incident {n : ℕ} (v : Fin (n+2)) (l : PathLabel n)
    (h : ¬incident v l) : pathWord l v = none := by
  rcases l with ⟨w,q⟩ | ⟨e,ab⟩
  · change ¬w = v at h
    simp [pathWord,onsiteWord,Ne.symm h]
  · change ¬(e.castSucc = v ∨ e.succ = v) at h
    rw [not_or] at h
    simp [pathWord,couplingWord,Ne.symm h.1,Ne.symm h.2]

/-- Removing all terms that meet a chosen gate support has squared operator
cost at most 21 times its size times the total squared coefficient norm. -/
theorem path_idle_deletion_norm_sq {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) :
    ‖pathHamiltonian u - pathHamiltonianOnSites Sᶜ u‖^2 ≤ 21*(S.card:ℝ)*‖u‖^2 := by
  classical
  let W := S.biUnion incidentLabels
  have hcard : W.card ≤ 21*S.card := calc
    _ ≤ ∑ v ∈ S, (incidentLabels v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, 21 := Finset.sum_le_sum fun v _ => incidentLabels_card v
    _ = _ := by simp [mul_comm]
  have hmiss (l) (hl : l ∉ W) : PathWordSupportedIn Sᶜ l := by
    intro v hv
    have hS : v ∈ S := by simpa using hv
    apply pathWord_none_of_not_incident
    intro hinc
    exact hl (Finset.mem_biUnion.mpr ⟨v,hS,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinc⟩⟩)
  have hbound : ‖pathHamiltonian u-pathHamiltonianOnSites Sᶜ u‖ ≤ ∑ l ∈ W, |u l| := by
    have h0 := norm_pathHamiltonian_sub_packetReference_le Sᶜ ∅ u 0
    have hR : pathHamiltonianPacketReference Sᶜ ∅ u 0 = pathHamiltonianOnSites Sᶜ u := by
      simp [pathHamiltonianPacketReference,pathHamiltonianOnSites]
    rw [hR] at h0
    apply h0.trans
    rw [Finset.sum_subset (Finset.subset_univ W) (fun l _ hl => by simp [pathPacketReferenceCoeff,hmiss l hl]) |>.symm]
    apply Finset.sum_le_sum
    intro l _
    by_cases hl : PathWordSupportedIn Sᶜ l <;> simp [pathPacketReferenceCoeff,hl]
  apply (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans
  have hcs := sq_sum_le_card_mul_sum_sq (s := W) (f := fun l => |u l|)
  apply hcs.trans
  have hsq : ∑ l ∈ W, |u l|^2 ≤ ‖u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) (fun _ _ _ => sq_nonneg _)).trans_eq
    simp [Real.norm_eq_abs]
  exact mul_le_mul (by exact_mod_cast hcard) hsq (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- At half the period of any energy gap, its squared width times the
squared approximation deficit is bounded by gate count times total
Pauli coefficient energy. The inequality includes a zero gap. -/
theorem path_half_gap_gate_count_bound {n : ℕ} (u : PathShell n)
    (i j : Fin (n+2) → Bool) (C : TwoQubitCircuit (n+2)) (c : ℂ) :
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    let d := E i - E j
    let err := ‖unitaryEvolution (pathHamiltonian u) (Real.pi/d) - c • (C.eval : Reg (n+2))‖
    (max 0 (1-err) * |d|)^2 ≤ 168 * Real.pi^2 * C.gateCount * ‖u‖^2 := by
  let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
  let d := E i - E j
  let err := ‖unitaryEvolution (pathHamiltonian u) (Real.pi/d) - c • (C.eval : Reg (n+2))‖
  let mass := ‖pathHamiltonian u - pathHamiltonianOnSites C.touchedSitesᶜ u‖
  change (max 0 (1-err) * |d|)^2 ≤ _
  have hlin : max 0 (1-err) * |d| ≤ (2*Real.pi) * mass := by
    by_cases hd : E i = E j
    · have hz : d = 0 := sub_eq_zero.mpr hd
      simp only [hz,abs_zero,mul_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)
    have h := path_gap_circuit_deletion_floor u i j hd C c
    change 1 ≤ err + 2 * |Real.pi / d| * mass at h
    rw [abs_div,abs_of_pos Real.pi_pos] at h
    have hdpos : 0 < |d| := abs_pos.mpr (sub_ne_zero.mpr hd)
    rw [max_mul_of_nonneg _ _ hdpos.le,zero_mul]
    refine max_le (mul_nonneg (by positivity) (norm_nonneg _)) ?_
    apply (le_div_iff₀ hdpos).mp
    calc
      1-err ≤ 2 * (Real.pi / |d|) * mass := by linarith only [h]
      _ = (2*Real.pi)*mass / |d| := by ring
  have hmass : mass^2 ≤ 21*(C.touchedSites.card:ℝ)*‖u‖^2 :=
    path_idle_deletion_norm_sq C.touchedSites u
  have hc : (C.touchedSites.card:ℝ) ≤ 2*C.gateCount := by exact_mod_cast C.card_touchedSites_le
  calc
    _ ≤ ((2*Real.pi)*mass)^2 :=
      pow_le_pow_left₀ (mul_nonneg (le_max_left _ _) (abs_nonneg _)) hlin _
    _ = (2*Real.pi)^2*mass^2 := mul_pow _ _ _
    _ ≤ (2*Real.pi)^2*(21*(2*C.gateCount)*‖u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply hmass.trans
      gcongr
    _ = _ := by ring

#print axioms path_idle_deletion_norm_sq
#print axioms path_gap_circuit_deletion_floor
#print axioms path_half_gap_gate_count_bound
end
end GaloisForLFunctions.HTGeometry
