import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.UnitaryMidpoint
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-! # Interpolation of an exact operator-norm fit inside one phase chart -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev cis (t : ℝ) := Complex.exp ((t:ℂ)*Complex.I)

/-- The diagonal time evolution after lifting and removing the common phase, in radians. -/
def anglePacket (θ : I → ℝ) : unitary (Mat I) :=
  ⟨diagonal fun i => cis (θ i),StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _
    (fun _ => Complex.norm_exp_ofReal_mul_I _)⟩

private theorem cis_add (s t : ℝ) : cis (s+t)=cis s*cis t := by
  simp only [cis,Complex.ofReal_add,add_mul,Complex.exp_add]

/-- Rotating to the midpoint packet reduces any chart of span at most π to
conjugate endpoints. Their unequal squared operator errors then average. -/
theorem angle_midpoint_square (W : unitary (Mat I)) (a b : I → ℝ) {p m : ℝ} (hcut : p^2+m^2<4)
    (hab : ∀ i, |b i-a i|≤π) (ha : ‖(anglePacket a).val-W.val‖ ≤ p) (hb : ‖(anglePacket b).val-W.val‖ ≤ m) :
    2*‖(anglePacket (fun i => (a i+b i)/2)).val-W.val‖^2≤p^2+m^2 := by
  let θ (i : I) := (a i+b i)/2
  let d (i : I) := (b i-a i)/2
  let M := anglePacket θ
  let V := M⁻¹*W
  have hMV : M.val*V.val=W.val := congrArg Subtype.val (mul_inv_cancel_left M W)
  have hleft (Z : Mat I) : ‖Z-V.val‖=‖M.val*Z-W.val‖ := by
    rw [←CStarRing.norm_mem_unitary_mul (Z-V.val) M.2,mul_sub,hMV]
  have hprod (g : I → ℝ) : M.val*(anglePacket g).val=(anglePacket fun i => θ i+g i).val := by
    change Matrix.diagonal (fun i => cis (θ i))*Matrix.diagonal (fun i => cis (g i))=
      Matrix.diagonal (fun i => cis (θ i+g i))
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact (cis_add _ _).symm
  have hconj (i : I) : conj (cis (d i))=cis (-d i) := by
    dsimp only [cis]
    rw [←Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,mul_neg,neg_mul]
  have hpos (i : I) : 0≤(cis (d i)).re := by
    rw [Complex.exp_ofReal_mul_I_re]
    have hh := abs_le.mp (hab i)
    apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> dsimp only [d] <;> linarith only [hh.1,hh.2]
  have hplus : (fun i => θ i+d i)=b := funext fun i => by dsimp only [θ,d]; ring
  have hminus : (fun i => θ i+ -d i)=a := funext fun i => by dsimp only [θ,d]; ring
  have hh := midpoint_square V (fun i => cis (d i)) (fun _ => Complex.norm_exp_ofReal_mul_I _) hpos
    (show m^2+p^2<4 by linarith only [hcut]) (by
    change ‖(anglePacket d).val-V.val‖ ≤ m
    rwa [hleft,hprod,hplus]) (by
    simp only [hconj]
    change ‖(anglePacket (fun i => -d i)).val-V.val‖ ≤ p
    rwa [hleft,hprod,hminus])
  rw [hleft,mul_one] at hh
  exact hh.trans_eq (add_comm ..)

private theorem angle_midpoint (W : unitary (Mat I)) (a b : I → ℝ) {ε : ℝ} (hε : ε^2<2)
    (hab : ∀ i, |b i-a i|≤π) (ha : ‖(anglePacket a).val-W.val‖≤ε) (hb : ‖(anglePacket b).val-W.val‖≤ε) :
    ‖(anglePacket (fun i => (a i+b i)/2)).val-W.val‖≤ε := by
  have h := angle_midpoint_square W a b (by linarith only [hε]) hab ha hb
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans ha)).mp (by linarith only [h])

/-- A closed subset of the unit interval containing its ends and all pair midpoints
contains the whole interval: a missing point would have a gap with attained ends. -/
private theorem fill_interval (S : Set ℝ) (hc : IsClosed S) (h0 : 0∈S) (h1 : 1∈S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a∈Icc (0:ℝ) 1 → b∈Icc (0:ℝ) 1 → (a+b)/2∈S) : Icc 0 1 ⊆ S := by
  intro y hy
  by_contra h
  let A := Icc 0 y ∩ S
  let B := Icc y 1 ∩ S
  have ha := (isCompact_Icc.inter_right hc : IsCompact A).isGreatest_sSup ⟨0,⟨le_rfl,hy.1⟩,h0⟩
  have hb := (isCompact_Icc.inter_right hc : IsCompact B).isLeast_sInf ⟨1,⟨hy.2,le_rfl⟩,h1⟩
  let a := sSup A
  let b := sInf B
  have hlt : a<y := lt_of_le_of_ne ha.1.1.2 (fun he => h (he ▸ ha.1.2))
  have hgt : y<b := lt_of_le_of_ne hb.1.1.1 (fun he => h (he.symm ▸ hb.1.2))
  have ha0 : 0≤a := ha.1.1.1
  have hb1 : b≤1 := hb.1.1.2
  have hs := hm a ha.1.2 b hb.1.2 ⟨ha0,hlt.le.trans hy.2⟩ ⟨hy.1.trans hgt.le,hb1⟩
  by_cases hside : (a+b)/2≤y
  · have hp : (a+b)/2≤a := ha.2 ⟨⟨by linarith only [ha0,hlt,hgt],hside⟩,hs⟩
    linarith only [hp,hlt,hgt]
  · have hp : b≤(a+b)/2 := hb.2 ⟨⟨le_of_not_ge hside,by linarith only [hb1,hlt,hgt]⟩,hs⟩
    linarith only [hp,hlt,hgt]

/-- On any real eigenphase segment of coordinate span at most π, the part fitting
a fixed laboratory unitary at the original operator error is convex. -/
theorem segment_fit (W : unitary (Mat I)) (a b : I → ℝ) {ε : ℝ} (hε : ε^2<2)
    (hab : ∀ i, |b i-a i|≤π) (ha : ‖(anglePacket a).val-W.val‖≤ε) (hb : ‖(anglePacket b).val-W.val‖≤ε) :
    ∀ t∈Icc (0:ℝ) 1, ‖(anglePacket fun i => a i+t*(b i-a i)).val-W.val‖≤ε := by
  let f (t : ℝ) (i : I) := a i+t*(b i-a i)
  let S : Set ℝ := {t | ‖(anglePacket (f t)).val-W.val‖≤ε}
  have hc : IsClosed S := by
    apply isClosed_le _ continuous_const
    unfold anglePacket f
    fun_prop
  have hb₁ : f 1=b := funext fun i => by dsimp only [f]; ring
  apply fill_interval S hc (by simpa only [S,mem_setOf_eq,f,zero_mul,add_zero] using ha)
    (by simpa only [S,mem_setOf_eq,hb₁] using hb)
  intro p hp q hq hpi hqi
  have hd (i : I) : |f q i-f p i|≤π := by
    rw [show f q i-f p i=(q-p)*(b i-a i) by dsimp only [f]; ring,abs_mul]
    have hh : |q-p|≤1 := abs_le.mpr ⟨by linarith only [hpi.2,hqi.1],by linarith only [hqi.2,hpi.1]⟩
    exact (mul_le_mul_of_nonneg_right hh (abs_nonneg _)).trans ((one_mul _).le.trans (hab i))
  have he : f ((p+q)/2)=(fun i => (f p i+f q i)/2) := funext fun i => by dsimp only [f]; ring
  change ‖(anglePacket (f ((p+q)/2))).val-W.val‖≤ε
  rw [he]
  exact angle_midpoint W _ _ hε hd hp hq

#print axioms segment_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
