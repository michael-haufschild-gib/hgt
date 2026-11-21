import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PhysicalRoots

/-! # Exponential rank at linear derivative order on a nearest-neighbour path -/
open Matrix Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

private theorem simple_right (n : ℕ) :
    ∀ᶠ v in 𝓝[>] (0:ℝ), (pathHamiltonian (splitShell n v)).charpoly.Separable := by
  obtain ⟨F,hF⟩ := split_simple_off_finite n
  have h0 : (0:ℂ) ∈ ((F.erase 0 : Finset ℂ) : Set ℂ)ᶜ := by simp
  have he := ((F.erase 0).finite_toSet.isClosed.isOpen_compl.mem_nhds h0)
  have ht : Tendsto (fun v : ℝ => (v:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      ((Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
  filter_upwards [ht he,self_mem_nhdsWithin] with v hv hv0
  apply hF
  intro hm
  exact hv (Finset.mem_erase.mpr ⟨Complex.ofReal_ne_zero.mpr (ne_of_gt hv0),hm⟩)

/-- At a simple physical path Hamiltonian there are 2^(N−1) independent eigenvalue
responses using only the N longitudinal fields. Every selected derivative has the
same even order, N−1 rounded up. Such pencils occur arbitrarily close to the
classical Ising point from the positive side. -/
theorem longitudinal_rank_right (n : ℕ) :
    ∀ᶠ v in 𝓝[>] (0:ℝ), (pathHamiltonian (splitShell n v)).charpoly.Separable ∧
      ∃ f : (Fin (n+1) → Bool) → (Fin (n+2) → ℂ) → ℂ,
        (∀ s, AnalyticAt ℂ (f s) 0 ∧
          ∀ᶠ h in 𝓝 0, matrixCharpolyRelation (fieldHamiltonian n v h,f s h) = 0) ∧
        Function.Injective (fun s => f s 0) ∧
        (Matrix.of fun a s => mixed (maskWord a) (f s) 0).det ≠ 0 := by
  classical
  obtain ⟨E,_,hE,hm⟩ := physical_minor_near_zero n
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds,simple_right n] with v hminor hsimple
  let e (i) := E i v
  have hinj : Function.Injective e := by
    rw [hE] at hsimple
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsimple
  let b (s : Fin (n+1) → Bool) := (e (representative s)+e (reverseSpins (representative s)))/2
  let r (s : Fin (n+1) → Bool) := (e (representative s)-e (reverseSpins (representative s)))/2
  have hr (s) : r s ≠ 0 := div_ne_zero (sub_ne_zero.mpr (hinj.ne (reversed_ne _))) (by norm_num)
  have hbr (s) : b s+r s = e (representative s) := by dsimp [b,r]; ring
  let p (s : Fin (n+1) → Bool) := physicalPolynomial v e s
  have hpart (s) : atUpper (MvPolynomial.pderiv none (p s)) ≠ 0 := by
    intro hz
    apply hminor
    apply Matrix.det_eq_zero_of_column_eq_zero s
    intro a
    have hlen : 2*(maskWord a).length ≠ 0 := by rw [maskWord_length]; omega
    change upperResponse (p s) (maskWord a)=0
    simp only [upperResponse,hz,zero_pow hlen,div_zero]
  have hconst (s) : atUpper (p s)=0 := by
    have h := eval_physicalPolynomial v e (hE v) s 0 1
    change r s^2*atUpper (p s) = 2*matrixCharpolyRelation (_,b s+r s*1) at h
    have hz : (pathHamiltonian (splitShell n v)).charpoly.eval (e (representative s))=0 := by
      rw [hE v,Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (representative s)) (by simp [e])
    rw [Matrix.eval_charpoly] at hz
    simp only [mul_one,hbr,smul_zero,fieldHamiltonian,fieldEnergy,Pi.zero_apply,mul_zero,
      Finset.sum_const_zero,Matrix.diagonal_zero,add_zero,matrixCharpolyRelation] at h
    rw [hz,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hr s))
  choose g hga hg1 hgz using fun s => upper_branch (p s) (hconst s) (hpart s)
  let f (s : Fin (n+1) → Bool) (h : Fin (n+2) → ℂ) := b s+r s*g s ((r s)⁻¹ • h)
  have hf0 (s) : f s 0 = e (representative s) := by simp only [f,smul_zero,hg1,mul_one,hbr]
  refine ⟨hsimple,f,fun s => ⟨?_,?_⟩,?_,?_⟩
  · unfold f
    apply analyticAt_const.add (analyticAt_const.mul _)
    exact (hga s).fun_comp_of_eq (analyticAt_id.const_smul _) (smul_zero _)
  · have ht : Tendsto (fun h : Fin (n+2) → ℂ => (r s)⁻¹ • h) (𝓝 0) (𝓝 0) := by
      simpa only [smul_zero] using ((continuous_const_smul (r s)⁻¹).continuousAt (x := (0:Fin (n+2) → ℂ))).tendsto
    filter_upwards [ht.eventually (hgz s)] with h hh
    have hi := eval_physicalPolynomial v e (hE v) s ((r s)⁻¹ • h) (g s ((r s)⁻¹ • h))
    change r s^2*onRoot (p s) (g s) ((r s)⁻¹ • h)=2*matrixCharpolyRelation (_,f s h) at hi
    rw [hh,mul_zero] at hi
    simpa only [smul_smul,mul_inv_cancel₀ (hr s),one_smul] using
      (mul_eq_zero.mp hi.symm).resolve_left (by norm_num : (2:ℂ)≠0)
  · intro s t hst
    rw [hf0,hf0] at hst
    have ht := hinj hst
    exact funext (fun i => by simpa [representative] using congrFun ht i.succ)
  · let m := n+1+(n+1)%2
    let M := Matrix.of fun a s : Fin (n+1) → Bool => upperResponse (p s) (maskWord a)
    let c (s) := r s*((r s)⁻¹)^m
    have he : (Matrix.of fun a s => mixed (maskWord a) (f s) 0) = M * diagonal c := by
      ext a s
      have hn : maskWord a ≠ [] := by
        intro h
        have hh := maskWord_length a
        rw [h,List.length_nil] at hh
        omega
      rw [Matrix.of_apply,Matrix.mul_diagonal]
      change mixed (maskWord a) (fun y => b s+r s*g s ((r s)⁻¹ • y)) 0 = upperResponse (p s) (maskWord a)*c s
      rw [mixed_physical _ _ _ hn,maskWord_length,upperResponse_eq_mixed _ _ _ (hga s) (hg1 s) (hgz s) (hpart s)]
      exact mul_comm _ _
    rw [he,Matrix.det_mul,Matrix.det_diagonal]
    exact mul_ne_zero hminor (Finset.prod_ne_zero_iff.mpr (fun s _ =>
      mul_ne_zero (hr s) (pow_ne_zero _ (inv_ne_zero (hr s)))))

#print axioms longitudinal_rank_right
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
