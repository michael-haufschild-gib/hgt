import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LocalTests.Choi.CenteredCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PacketOverlap

/-! # Simultaneous missing signals on disjoint physical neighborhoods -/
open Matrix Finset GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
open FixedHorizon OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
open private centered_norm from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PacketOverlap
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem choi_difference {N : ℕ} (U V : Reg N) : ‖choiVector U-choiVector V‖≤‖U-V‖ := by
  have h : choiVector U-choiVector V=choiVector (U-V) := by ext p; simp [choiVector,sub_div]
  rw [h]
  exact norm_choiVector_le_l2_opNorm _

/-- Every local reporter which has zero mean on a candidate fit contributes
to one squared-error budget. No independence between circuit outputs is
required. Spatial separation enters only for the physical reporters K. -/
theorem localized_missing_count {N : ℕ} {ι : Type*} [Fintype ι] (S : ι→Finset (Fin N))
    (U V : Reg N) (hu : U∈unitary _) (P B K : ι→Reg N)
    (hP : ∀ i, (P i).IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    (hp : ∀ i, ‖P i‖≤1) (hb : ∀ i, ‖B i‖≤1) (hk : ∀ i, ‖K i‖≤1)
    (hs : ∀ i, IsSiteSupported (S i) (K i)) (hd : ∀ i j, i≠j → Disjoint (S i) (S j))
    {r δ ε : ℝ} (hr : 0<r) (hfit : ‖U-V‖≤ε)
    (hmean : ∀ i, r≤‖(K i).trace/(Fintype.card (Fin N→Bool):ℂ)‖)
    (hloc : ∀ i, ‖star U*P i*U*B i-K i‖≤δ)
    (hzero : ∀ i, (star V*P i*V*B i).trace=0)
    (hδ : δ≤r/8) (hε : ε≤1/8) (hsq : ε^2≤r/8) :
    (Fintype.card ι:ℝ)*(r/8)^2≤ε^2 := by
  let x := choiVector U
  let y := choiVector V
  let u i := choiVector (P i*U*B i)
  let v i := choiVector (P i*V*B i)
  let w i := choiVector (U*K i)
  let z i := w i-inner ℂ x (w i) • x
  have hid : Uᴴ*U=1 := (Unitary.mem_iff.mp hu).1
  have hx : ‖x‖=1 := norm_choiVector_eq_one Fintype.card_pos hid
  have he : ‖x-y‖≤ε := (choi_difference U V).trans hfit
  have hmove (i) : ‖u i-v i‖≤ε := by
    apply (choi_difference ..).trans
    rw [←sub_mul,←mul_sub]
    calc
      _ ≤ ‖P i*(U-V)‖*‖B i‖ := norm_mul_le ..
      _ ≤ ‖P i*(U-V)‖ := mul_le_of_le_one_right (norm_nonneg _) (hb i)
      _ ≤ ‖P i‖*‖U-V‖ := norm_mul_le ..
      _ ≤ ‖U-V‖ := mul_le_of_le_one_left (norm_nonneg _) (hp i)
      _ ≤ ε := hfit
  have hlocal (i) : ‖u i-w i‖≤δ := by
    apply (choi_difference ..).trans
    have h : P i*U*B i-U*K i=U*(star U*P i*U*B i-K i) := by
      rw [mul_sub,←mul_assoc U _ (B i),←mul_assoc U _ U,←mul_assoc U _ (P i),
        (show U*star U=1 from (Unitary.mem_iff.mp hu).2),one_mul]
    rw [h,CStarRing.norm_mem_unitary_mul _ hu]
    exact hloc i
  have zeroMean (i) : inner ℂ y (v i)=0 := by
    dsimp only [y,v]
    rw [inner_choiVector Fintype.card_pos]
    have hz := hzero i
    change (Vᴴ*P i*V*B i).trace=0 at hz
    rw [←mul_assoc,←mul_assoc,hz,zero_div]
  have score (i) : r/8≤‖inner ℂ (x-y) (z i)‖ := by
    have h : inner ℂ x (w i)=(K i).trace/(Fintype.card (Fin N→Bool):ℂ) := by
      dsimp only [x,w]
      rw [inner_choiVector Fintype.card_pos,←mul_assoc,hid,one_mul]
    apply centered_missing_projection x y (u i) (v i) (w i) hx he (hmove i) (hlocal i)
      (choi_test_transfer _ _ _ _ (hP i) (hB i)) (zeroMean i) _ hδ hε hsq
    rw [h]; exact hmean i
  have hnorm (i) : ‖z i‖≤1 := (centered_norm x (w i) hx).trans ((norm_choiVector_le_l2_opNorm _).trans
    ((CStarRing.norm_mem_unitary_mul _ hu).le.trans (hk i)))
  exact (orthogonal_projection_count z (x-y) (by positivity : 0<r/8) score hnorm
    (fun i j hij => disjoint_choi_fluctuations (hd i j hij) hid (hs i) (hs j))).trans
    (pow_le_pow_left₀ (norm_nonneg _) he 2)

#print axioms localized_missing_count
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
