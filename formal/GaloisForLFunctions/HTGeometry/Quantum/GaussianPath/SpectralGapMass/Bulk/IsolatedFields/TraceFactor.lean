import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.Coefficients
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.DisjointLayers
import GaloisForLFunctions.RHTower.InverseSquareChainCubicProjectiveFirstReturnLaw

/-! # A cosine factor for each isolated spin missed by a circuit -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section
variable {n : ℕ}
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ
private def spin (i : Fin (n+2)) : Reg n := finitePauliMatrix (pathWord (.inl (i,2)))

private theorem packet_sum (S : Finset (Fin (n+2))) :
    pathHamiltonian (longitudinalPacket S 1)=∑ i ∈ S, spin i := by
  classical
  let p := longitudinalPacket S 1
  have hon (i : Fin (n+2)) :
      (∑ a : Fin 3, (p (.inl (i,a)):ℂ) • finitePauliMatrix (pathWord (.inl (i,a)))) =
        if i ∈ S then spin i else 0 := by
    by_cases hi : i ∈ S <;> simp [p,longitudinalPacket,hi,ite_smul,spin]
  have hoff (e : Fin (n+1) × Fin 3 × Fin 3) : p (.inr e)=0 := rfl
  change pathHamiltonian p=_
  rw [pathHamiltonian_eq_sum,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [hon,hoff,Complex.ofReal_zero,zero_smul,sum_const_zero,add_zero]
  rw [←Finset.sum_filter]
  simp

private theorem packet_trace (S : Finset (Fin (n+2))) (t : ℝ) :
    (unitaryEvolution (pathHamiltonian (longitudinalPacket S 1)) t).trace =
      (Fintype.card (Fin (n+2) → Bool):ℂ)*(Real.cos t:ℂ)^S.card := by
  let b : ℂ := -(t:ℂ)*Complex.I
  have hb : Complex.cosh b=(Real.cos t:ℂ) := by
    rw [show b=(-(t:ℂ))*Complex.I from rfl,Complex.cosh_mul_I,Complex.cos_neg,Complex.ofReal_cos]
  have he := SpectatorCost.disjoint_complex_partition S (fun i => {i}) spin (fun _ => b)
    (fun i _ j _ hij => Finset.disjoint_singleton.mpr hij)
    (fun i _ => finitePauliMatrix_isSiteSupported_of_eq_none _ _ (fun v hv => by
      simp only [pathWord,onsiteWord,if_neg (show v≠i from fun e => hv (mem_singleton.mpr e))]))
    (fun _ _ => finitePauliMatrix_mul_self _)
    (fun i _ => finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity (.inl (i,2))))
  rw [hb,prod_const] at he
  have hcoef (X : Reg n) : t • ((-Complex.I) • X)=b • X := by
    rw [←smul_assoc,Complex.real_smul,show (t:ℂ)*(-Complex.I)=b by dsimp only [b]; ring]
  rw [unitaryEvolution,packet_sum,Finset.smul_sum,Finset.smul_sum]
  simpa only [hcoef] using he

/-- Arbitrary gates on the complementary wires leave the selected
spins' exact normalized trace factor in the overlap. -/
theorem reference_overlap {S : Finset (Fin (n+2))} (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (hd : Disjoint S C.touchedSites) (t : ℝ) :
    ‖(C.eval.valᴴ*unitaryEvolution (pathHamiltonian (fieldReference u S)) t).trace‖ ≤
      (2:ℝ)^(n+2)*|Real.cos t|^S.card := by
  let p := longitudinalPacket S 1
  let U := unitaryEvolution (pathHamiltonianOnSites Sᶜ u) t
  let V := unitaryEvolution (pathHamiltonianOnSites S p) t
  let d : ℂ := Fintype.card (Fin (n+2) → Bool)
  have hd₀ : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hC := C.isSiteSupported_touchedSites.mono (show C.touchedSites ⊆ Sᶜ from
    fun _ hi => mem_compl.mpr (fun hs => disjoint_left.mp hd hs hi))
  have hU := isSiteSupported_unitaryEvolution (pathHamiltonianOnSites_isSiteSupported Sᶜ u) t
  have hV := isSiteSupported_unitaryEvolution (pathHamiltonianOnSites_isSiteSupported S p) t
  have hfac := SpanningDensity.FixedHorizon.disjoint_trace_product disjoint_compl_left
    (hC.conjTranspose.matrix_mul hU) hV
  have htr : V.trace=d*(Real.cos t:ℂ)^S.card := by
    dsimp only [V,p]
    rw [longitudinalPacket_restriction,packet_trace]
  change d*(C.eval.valᴴ*U*V).trace=(C.eval.valᴴ*U).trace*V.trace at hfac
  rw [htr] at hfac
  have he : (C.eval.valᴴ*U*V).trace=(C.eval.valᴴ*U).trace*(Real.cos t:ℂ)^S.card :=
    mul_left_cancel₀ hd₀ (hfac.trans (by ring))
  have hu : C.eval.valᴴ*U ∈ unitary _ := mul_mem (Unitary.star_mem C.eval.property)
    (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonianOnSites _ _) t)
  have hbound : ‖(C.eval.valᴴ*U).trace‖ ≤ (2:ℝ)^(n+2) := by
    simpa only [CStarRing.norm_of_mem_unitary hu,mul_one,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using
      _root_.RHTower.norm_trace_le_card_mul_l2OpNorm (C.eval.valᴴ*U)
  rw [fieldReference_generator,unitaryEvolution_pathHamiltonianPacketReference disjoint_compl_left,←mul_assoc]
  change ‖(C.eval.valᴴ*U*V).trace‖ ≤ _
  rw [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hbound (by positivity)

#print axioms reference_overlap
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
