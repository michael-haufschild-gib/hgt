import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Evolution
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.NearDiagonal
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Circuit caps for supported unitaries commuting with a nearly diagonal matrix -/
open Filter Topology Set Matrix Metric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section
open DiagonalSynthesis Subregister
private abbrev UGroup (n : ℕ) := Matrix.unitaryGroup (Fin n→Bool) ℂ

/-- Diagonal synthesis only needs the wires on which the phases depend. -/
theorem supported_diagonal {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (w : (Fin n→Bool)→ℂ) (hw : ∀ x, ‖w x‖=1)
    (hsupp : IsSiteSupported (A:=fun _ : Fin n => Bool) S (diagonal w)) :
    Realizes (2^S.card*(2*S.card+1)) (diagonal w) := by
  classical
  let e := S.equivFin.symm
  let loc (x : Fin n→Bool) (i : Fin S.card) := x (e i).val
  let extend (b : Fin S.card→Bool) := glueLocalConfiguration S (fun i => b (e.symm i)) (fun _ => false)
  let W (b : Fin S.card→Bool) := w (extend b)
  have hW (x : Fin n→Bool) : W (loc x)=w x := by
    have hh (i : Fin n) (hi : i∈S) : extend (loc x) i=x i := by
      simp only [extend,glueLocalConfiguration_mem _ _ _ hi,loc,Equiv.apply_symm_apply]
    simpa only [diagonal_apply_eq] using hsupp.2 (extend (loc x)) (extend (loc x)) x x hh hh
      (fun _ _ => rfl) (fun _ _ => rfl)
  have he : place e (diagonal W)=diagonal w := by
    ext x y
    by_cases hxy : x=y
    · subst y
      unfold place liftLocalMatrix
      rw [if_pos rfl]
      change (diagonal W) (loc x) (loc x)=(diagonal w) x x
      simpa only [diagonal_apply_eq] using hW x
    rw [diagonal_apply_ne _ hxy]
    unfold place liftLocalMatrix
    split
    next hout =>
      change (diagonal W) (loc x) (loc y)=0
      apply diagonal_apply_ne
      intro hloc
      apply hxy
      funext i
      by_cases hi : i∈S
      · simpa only [loc,Equiv.apply_symm_apply] using congrFun hloc (e.symm ⟨i,hi⟩)
      · exact congrFun hout ⟨i,hi⟩
    next => rfl
  exact he ▸ realizes_place e (diagonal_phases hS W (fun b => hw (extend b)))

private theorem closed_support {n : ℕ} (S : Finset (Fin n)) :
    IsClosed {A : Register n | IsSiteSupported (A:=fun _ : Fin n => Bool) S A} := by
  let L := liftLocalMatrixLinear (fun _ : Fin n => Bool) S
  have he : {A : Register n | IsSiteSupported (A:=fun _ : Fin n => Bool) S A} = (L.range : Set (Register n)) := by
    ext A
    constructor
    · intro h
      obtain ⟨B,hB⟩ := exists_liftLocalMatrix_of_isSiteSupported h
      exact ⟨B,hB.symm⟩
    · rintro ⟨B,rfl⟩
      exact isSiteSupported_liftLocalMatrix S B
  rw [he]
  exact Submodule.closed_of_finiteDimensional _

/-- Near a simple diagonal generator, every commuting unitary supported
on S is approximable by the diagonal budget of S, uniformly in time. -/
theorem eventually_cheap_supported {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (d : (Fin n→Bool)→ℂ) (hd : Function.Injective d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : Register n in 𝓝 (diagonal d), ∀ V : UGroup n,
      IsSiteSupported (A:=fun _ : Fin n => Bool) S V.val → H*V.val=V.val*H →
      HasProjectiveCircuitApproximation n ε (2^S.card*(2*S.card+1)) V.val := by
  let s := 2^S.card*(2*S.card+1)
  let A := phaseCircuitMatrixImageAtMost n s
  let Z : Set (Register n × UGroup n) := {p | p.1*p.2.val=p.2.val*p.1} ∩
    {p | IsSiteSupported (A:=fun _ : Fin n => Bool) S p.2.val} ∩ {p | ε ≤ infDist p.2.val A}
  have hc : Continuous (fun p : Register n × UGroup n => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hclosed : IsClosed Z := ((isClosed_eq (continuous_fst.mul hc) (hc.mul continuous_fst)).inter
    ((closed_support S).preimage hc)).inter (isClosed_le continuous_const ((continuous_infDist_pt _).comp hc))
  have hbase : diagonal d∉Prod.fst '' Z := by
    rintro ⟨⟨H,V⟩,⟨⟨hcomm,hsupp⟩,hfar⟩,rfl⟩
    let w := fun x => V.val x x
    have he : V.val=diagonal w := by
      ext i j
      by_cases hij : i=j
      · subst j; rw [diagonal_apply_eq]
      · rw [diagonal_apply_ne _ hij]
        have h := congrFun (congrFun hcomm i) j
        change (diagonal d*V.val) i j=(V.val*diagonal d) i j at h
        rw [diagonal_mul,mul_diagonal] at h
        exact (mul_eq_zero.mp (show (d i-d j)*V.val i j=0 by linear_combination h)).resolve_left
          (sub_ne_zero.mpr (hd.ne hij))
    have hnorm (i) : ‖w i‖=1 := by
      have hu := Matrix.mem_unitaryGroup_iff.mp V.property
      rw [he,Matrix.star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal] at hu
      have h := congrArg (fun U : Register n => ‖U i i‖) hu
      change ‖(diagonal _ : Register n) i i‖=‖(1 : Register n) i i‖ at h
      simp only [diagonal_apply_eq,one_apply_eq,Pi.star_apply,norm_mul,norm_star,norm_one] at h
      nlinarith only [h,norm_nonneg (w i)]
    have hfit := (supported_diagonal S hS w hnorm (he ▸ hsupp)).approx (le_refl (0:ℝ))
    have herr := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hfit
    rw [← he] at herr
    exact (hε.trans_le hfar).not_ge herr
  filter_upwards [(isClosedMap_fst_of_compactSpace _ hclosed).isOpen_compl.mem_nhds hbase] with H hH
  intro V hsupp hcomm
  apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
  exact (lt_of_not_ge fun hfar => hH ⟨(H,V),⟨⟨hcomm,hsupp⟩,hfar⟩,rfl⟩).le

#print axioms eventually_cheap_supported
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
