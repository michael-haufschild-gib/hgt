import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.DisjointMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.ScoreOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CutMoments
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

/-! # Circuit overlap from spatially separated Heisenberg reporters -/
open Matrix GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
noncomputable section

private theorem centered_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x w : E) (hx : ‖x‖=1) : ‖w-inner ℂ x w • x‖ ≤ ‖w‖ := by
  let p := inner ℂ x w • x
  have hxx : inner ℂ x x=1 := by rw [inner_self_eq_norm_sq_to_K,hx]; norm_num
  have ho : inner ℂ p (w-p)=0 := by
    simp only [p,inner_smul_left,inner_sub_right,inner_smul_right,hxx,mul_one]
    ring
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (w-p) ho
  rw [show p+(w-p)=w by abel] at h
  change ‖w-p‖ ≤ ‖w‖
  nlinarith only [h,sq_nonneg ‖p‖,norm_nonneg w,norm_nonneg (w-p)]

variable {N m : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Disjoint local right actions approximate tests on the full evolution.
Each normalized trace of magnitude at least r contributes coherently after
a phase choice. The localization cost is independent of the test count
after division by m. -/
theorem packet_overlap (hm : 0 < m) (U V : Reg N) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (Y B K : Fin m → Reg N) (S : Fin m → Finset (Fin N))
    (hY : ∀ i, (Y i).IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    (hYn : ∀ i, ‖Y i‖ ≤ 1) (hBn : ∀ i, ‖B i‖ ≤ 1) (hKn : ∀ i, ‖K i‖ ≤ 1)
    (hs : ∀ i, IsSiteSupported (A:=fun _ : Fin N => Bool) (S i) (K i))
    (hd : ∀ i j, i≠j → Disjoint (S i) (S j))
    {r δ : ℝ} (hr : 0 < r)
    (hmean : ∀ i, r ≤ ‖(K i).trace/(Fintype.card (Fin N → Bool):ℂ)‖)
    (herr : ∀ i, ‖Uᴴ*Y i*U*B i-K i‖ ≤ δ)
    (ho : ∀ i j, i≠j → inner ℂ (choiVector (Y i*V*B i)) (choiVector (Y j*V*B j))=0) :
    (m:ℝ)*r*‖inner ℂ (choiVector U) (choiVector V)‖ ≤ 2*Real.sqrt m+m*δ := by
  let x := choiVector U
  let y := choiVector V
  let w i := choiVector (U*K i)
  let u i := choiVector (Y i*U*B i)
  let v i := choiVector (Y i*V*B i)
  let b i := inner ℂ x (w i)
  let c i := (‖b i‖:ℂ)/b i
  have hu : Uᴴ*U=1 := (Unitary.mem_iff.mp hU).1
  have hx : ‖x‖=1 := norm_choiVector_eq_one Fintype.card_pos hu
  have hy : ‖y‖=1 := norm_choiVector_eq_one Fintype.card_pos (Unitary.mem_iff.mp hV).1
  have hb (i) : r ≤ ‖b i‖ := by
    dsimp only [b,x,w]
    rw [inner_choiVector Fintype.card_pos,←mul_assoc,hu,one_mul]
    exact hmean i
  have hn (i) : b i ≠ 0 := norm_pos_iff.mp (hr.trans_le (hb i))
  have hc (i) : ‖c i‖=1 := by
    dsimp only [c]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (hn i))]
  have hcb (i) : c i*b i=(‖b i‖:ℂ) := div_mul_cancel₀ _ (hn i)
  have hw (i) : ‖w i‖ ≤ 1 := (norm_choiVector_le_l2_opNorm _).trans
    ((CStarRing.norm_mem_unitary_mul _ hU).le.trans (hKn i))
  have hv (i) : ‖v i‖ ≤ 1 := by
    calc ‖v i‖ ≤ ‖Y i*V*B i‖ := norm_choiVector_le_l2_opNorm _
         _ ≤ ‖Y i*V‖*‖B i‖ := norm_mul_le _ _
         _ = ‖Y i‖*‖B i‖ := by rw [CStarRing.norm_mul_mem_unitary _ hV]
         _ ≤ 1 := (mul_le_mul (hYn i) (hBn i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he (i) : ‖u i-w i‖ ≤ δ := by
    have es : u i-w i=choiVector (Y i*U*B i-U*K i) := by
      ext p
      simp [u,w,choiVector,sub_div]
    have hmat : Y i*U*B i-U*K i=U*(Uᴴ*Y i*U*B i-K i) := by
      rw [mul_sub,←mul_assoc U _ (B i),←mul_assoc U _ U,←mul_assoc U _ (Y i),
        (show U*Uᴴ=1 from (Unitary.mem_iff.mp hU).2),one_mul]
    rw [es]
    apply (norm_choiVector_le_l2_opNorm _).trans
    rw [hmat,CStarRing.norm_mem_unitary_mul _ hU]
    exact herr i
  let z i := c i • (w i-b i • x)
  refine overlap_of_localized_tests hm x y (fun i => c i • u i) (fun i => star (c i) • v i)
    z ?_ hx hy (fun i => ‖b i‖) hr hb ?_ ?_ ?_ ?_ ?_
  · intro i
    simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]
    rw [show inner ℂ (u i) y=inner ℂ x (v i) from choi_test_transfer _ _ _ _ (hY i) (hB i)]
  · intro i
    have h : c i • u i-(‖b i‖:ℂ) • x-z i=c i • (u i-w i) := by
      simp only [z,smul_sub,smul_smul,hcb]
      abel
    rw [h,norm_smul,hc,one_mul]
    exact he i
  · intro i
    dsimp only [z]
    rw [norm_smul,hc,one_mul]
    exact (centered_norm x (w i) hx).trans (hw i)
  · intro i
    rw [norm_smul,norm_star,hc,one_mul]
    exact hv i
  · intro i j hij
    have h := disjoint_choi_fluctuations (hd i j hij) hu (hs i) (hs j)
    change inner ℂ (w i-b i • x) (w j-b j • x)=0 at h
    simp only [z,inner_smul_left,inner_smul_right,h,mul_zero]
  · intro i j hij
    simp only [v,inner_smul_left,inner_smul_right,ho i j hij,mul_zero]

#print axioms packet_overlap
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
