import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Transverse
import GaloisForLFunctions.HTGeometry.NearUniformSeparatingCarrier
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-! # A simple diagonal carrier with a dominant field at any chosen site -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section
variable {n : ℕ}

private theorem axial_diag (q : Fin (n+2)) (l : PathLabel n) (h : IsDiagLabel l) : axial q l := by
  rcases l with ⟨i,p⟩|⟨e,p⟩
  · change p=2 at h
    subst p
    by_cases he : q=i <;> simp [axial,pathWord,onsiteWord,he]
  · change p=(2,2) at h
    subst p
    by_cases he : q=e.castSucc <;> by_cases hf : q=e.succ <;> simp [axial,pathWord,couplingWord,he,hf]

/-- The longitudinal carrier has gap at least 3 to the power −K, with all bulk
coefficients bounded by two and only one field of order K. -/
theorem quantitative_gapped_carrier (q : Fin (n+2)) :
    ∃ u : PathShell n, ∃ h > (0:ℝ), ∃ d : (Fin (n+2)→Bool)→ℝ,
      (∀ x y, x≠y → 1/(3:ℝ)^(n+2) ≤ |d x-d y|) ∧
      pathHamiltonian u=diagonal (fun x => (d x:ℂ)) ∧ core q u=u ∧
      ‖pathHamiltonian u-h • spin q‖+3=h ∧
      (∀ i : Fin (n+2), 1 ≤ u (.inl (i,2))) ∧ (∀ e : Fin (n+1), u (.inr (e,(2,2)))=1) ∧
      (∀ l, ¬IsDiagLabel l → u l=0) ∧
      h ≤ 2*(Fintype.card (PathLabel n):ℝ)+3 ∧
      ∀ l : PathLabel n, |u l| ≤ 2+(if l=.inl (q,2) then h else 0) := by
  classical
  let ε : ℝ := (1/2)/3^(n+2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hsmall : ε*3^(n+2)=1/2 := div_mul_cancel₀ _ (by positivity)
  let v := nearUniformCarrier n ε
  let E := pathDiagEnergy v
  let h := ‖pathHamiltonian v‖+3
  have hbound (x) : |E x| ≤ ‖pathHamiltonian v‖ := by
    calc
      _ = ‖pathHamiltonian v x x‖ := by
        rw [pathHamiltonian_eq_diagonal v (nearUniformCarrier_offDiag ε),diagonal_apply_eq,
          Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := norm_entry_le_l2_opNorm _ _ _
  have hh : 0 < h := by dsimp only [h]; positivity
  let lq : PathLabel n := .inl (q,2)
  let u : PathShell n := WithLp.toLp 2 fun l => v l+(if l=lq then h else 0)
  have hu (l) : u l=v l+(if l=lq then h else 0) := rfl
  have hz (l) (hl : ¬IsDiagLabel l) : u l=0 := by
    have hn : l≠lq := fun he => hl (he ▸ (show IsDiagLabel lq from rfl))
    rw [hu,if_neg hn,nearUniformCarrier_offDiag ε l hl,zero_add]
  have hcore : core q u=u := by
    suffices he : (core q u).ofLp=u.ofLp from congrArg (WithLp.toLp 2) he
    funext l
    by_cases hl : axial q l
    · exact restricted_eq u hl
    · exact (restricted_zero u hl).trans (hz l (fun hd => hl (axial_diag q l hd))).symm
  have hmat : pathHamiltonian u=pathHamiltonian v+h • spin q := by
    simp only [pathHamiltonian_eq_sum,hu,Complex.ofReal_add,add_smul,sum_add_distrib]
    congr 1
    calc
      _ = ∑ l : PathLabel n, if l=lq then (h:ℂ) • finitePauliMatrix (pathWord l) else 0 := by
        apply sum_congr rfl
        intro l _
        split_ifs <;> simp_all only [Complex.ofReal_zero,zero_smul]
      _ = _ := by rw [sum_ite_eq',if_pos (mem_univ lq)]; rfl
  have he (x) : pathDiagEnergy u x=E x+h*siteSign x q := by
    unfold pathDiagEnergy E
    simp only [pathDiagEnergy,hu,lq,Sum.inl.injEq,Prod.mk.injEq,and_true,
      Sum.inr_ne_inl,ite_false,add_zero,add_mul,sum_add_distrib]
    have hp : (∑ i : Fin (n+2), (if i=q then h else 0)*zSetSign {i} x)=h*siteSign x q := by
      simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,zSetSign_singleton_eq]
    rw [hp]; ring
  have hv (l : PathLabel n) : |v l| ≤ 2 := by
    by_cases hd : IsDiagLabel l
    · obtain ⟨hlo,hhi⟩ := nearUniformCarrier_coord_mem hε.le (hsmall.le.trans (by norm_num)) l hd
      exact (abs_of_nonneg (zero_le_one.trans hlo)).le.trans hhi
    · rw [show v l=0 from nearUniformCarrier_offDiag ε l hd,abs_zero]; norm_num
  refine ⟨u,h,hh,pathDiagEnergy u,?_,pathHamiltonian_eq_diagonal _ hz,hcore,?_,?_,?_,hz,?_,?_⟩
  · intro x y hn
    rw [he,he]
    by_cases hs : x q=y q
    · have heq := sub_eq_zero.mp ((siteSign_sub_eq_zero_iff q).mpr hs)
      rw [heq,add_sub_add_right_eq_sub]
      have hb := separation_nearUniformCarrier hε (hsmall.le.trans (by norm_num)) hn
      exact (show 1/(3:ℝ)^(n+2)=2*ε by dsimp only [ε]; ring).trans_le hb
    · have ht : |h*(siteSign x q-siteSign y q)| ≤
          |(E x+h*siteSign x q)-(E y+h*siteSign y q)|+|E y-E x| := by
        calc _ = |((E x+h*siteSign x q)-(E y+h*siteSign y q))+(E y-E x)| := by congr 1; ring
             _ ≤ _ := abs_add_le ..
      rw [abs_mul,abs_of_pos hh,abs_siteSign_sub_of_ne hs] at ht
      have hone := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3) (n:=n+2)
      have hg : 1/(3:ℝ)^(n+2) ≤ 1 := (div_le_one (by positivity)).mpr hone
      dsimp only [h] at ht
      linarith only [hg,ht,abs_sub (E y) (E x),hbound x,hbound y]
  · rw [hmat,add_sub_cancel_right]
  · intro i
    rw [hu]
    have h₁ := (nearUniformCarrier_coord_mem hε.le (hsmall.le.trans (by norm_num))
      (.inl (i,2)) (by rfl)).1
    have hpos : 0 ≤ (if (Sum.inl (i,2):PathLabel n)=lq then h else 0) := by split <;> positivity
    exact h₁.trans (le_add_of_nonneg_right hpos)
  · intro e
    rw [hu,if_neg (Sum.inr_ne_inl),add_zero,nearUniformCarrier_edge]
  · change ‖pathHamiltonian v‖+3 ≤ 2*(Fintype.card (PathLabel n):ℝ)+3
    apply add_le_add _ le_rfl
    rw [pathHamiltonian_eq_sum]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _ : PathLabel n, (2:ℝ) := sum_le_sum fun l _ => by
        simpa only [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs] using hv l
      _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul,mul_comm]
  · intro l
    rw [hu]
    have hn : 0 ≤ (if l=lq then h else 0) := by split <;> positivity
    exact (abs_add_le ..).trans (add_le_add (hv l) (abs_of_nonneg hn).le)

#print axioms quantitative_gapped_carrier
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
