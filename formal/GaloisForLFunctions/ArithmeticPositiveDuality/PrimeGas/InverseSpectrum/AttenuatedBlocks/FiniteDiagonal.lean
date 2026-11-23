import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockPartition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.HeatSingularValues
import GaloisForLFunctions.HTGeometry.TopSumMajorization

/-! # Relative partition of a finitely modified positive heat diagonal -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set ContinuousLinearMap

private theorem approx_reordered (A : GasOp) (e : ℕ ≃ ℕ+) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (ha : Antitone w)
    (hd : ∀ (x : Gas) (n : ℕ), A x (e n) = (w n:ℂ)*x (e n)) (k : ℕ) : _root_.RHTower.approxNumber A k = w k := by
  let m (i : ℕ+) : ℂ := w (e.symm i)
  have hm (i : ℕ+) : ‖m i‖ = w (e.symm i) := (Complex.norm_real _).trans (Real.norm_of_nonneg (hw _))
  have hA : A = _root_.HTGeometry.ellTwoDiagonal m (fun i => (hm i).trans_le (ha (Nat.zero_le _))) := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    obtain ⟨n,rfl⟩ := e.surjective i
    change A x (e n) = m (e n)*x (e n)
    simp only [hd,m,e.symm_apply_apply]
  rw [hA]
  exact _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq e hm hw (fun {_ _} hij => ha hij) _

private theorem prefix_sorted {M : ℕ} (v : ℕ → ℝ) (ht : ∀ k, M ≤ k → v k = occupationWeight k)
    (hmin : ∀ i : Fin M, occupationWeight M ≤ v i.val) :
    ∃ π : Equiv.Perm ℕ, Antitone (v ∘ π) ∧ (∀ k, M ≤ k → π k = k) ∧
      ∀ f : ℝ → ℂ, (∑ i ∈ Finset.range M, f (v (π i))) = ∑ i ∈ Finset.range M, f (v i) := by
  let w (i : Fin M) := v i.val
  let p := HTGeometry.descPerm w
  let π := p.extendDomain Fin.equivSubtype
  have hi (i : Fin M) : π i.val = (p i).val := p.extendDomain_apply_image Fin.equivSubtype i
  have ho (k : ℕ) (hk : M ≤ k) : π k = k := p.extendDomain_apply_not_subtype Fin.equivSubtype (Nat.not_lt.mpr hk)
  have hs : Antitone (w ∘ p) := HTGeometry.antitone_sortDesc w
  refine ⟨π,?_,ho,?_⟩
  · intro i j hij
    change v (π j) ≤ v (π i)
    by_cases hj : j < M
    · have h (i : ℕ) (hi' : i < M) : π i = (p ⟨i,hi'⟩).val := hi ⟨i,hi'⟩
      rw [h j hj,h i (hij.trans_lt hj)]
      exact hs (show (⟨i,hij.trans_lt hj⟩ : Fin M) ≤ ⟨j,hj⟩ from hij)
    · have hj' := Nat.le_of_not_gt hj
      rw [ho j hj',ht j hj']
      by_cases hi' : i < M
      · rw [show π i = (p ⟨i,hi'⟩).val from hi ⟨i,hi'⟩]
        exact (occupationWeight_antitone hj').trans (hmin _)
      · have hM := Nat.le_of_not_gt hi'
        rw [ho i hM,ht i hM]
        exact occupationWeight_antitone hij
  · intro f
    calc
      _ = ∑ i : Fin M, f (v (π i.val)) := (Fin.sum_univ_eq_sum_range (fun k => f (v (π k))) M).symm
      _ = ∑ i : Fin M, f (v i.val) := by simpa only [hi] using Equiv.sum_comp p (fun i : Fin M => f (v i.val))
      _ = _ := Fin.sum_univ_eq_sum_range (fun k => f (v k)) M

/-- Sorting a finite altered prefix changes no complex power sum. Beyond the prefix the relative series cancels term by term. -/
theorem relativePartition_finite_diagonal {r M : ℕ} (A : GasOp) (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hd : ∀ (x : Gas) (k : ℕ), A x (number k) = (v k:ℂ)*x (number k))
    (ht : ∀ k, M ≤ k → v k = occupationWeight k) (hmin : ∀ i : Fin M, occupationWeight M ≤ v i.val)
    (b : SpectralBand r) (hb : ∀ k, (b k).val = _root_.RHTower.approxNumber A k) {z : ℂ} (hz : 0 < z.re) :
    relativePartition b z = ∑ k ∈ Finset.range M, ((occupationWeight k:ℂ)^z - (v k:ℂ)^z) := by
  obtain ⟨π,hπ,ho,hs⟩ := prefix_sorted v ht hmin
  let e : ℕ ≃ ℕ+ := π.trans (Equiv.ofBijective number ⟨number_injective,number_surjective⟩)
  have he (k : ℕ) : _root_.RHTower.approxNumber A k = v (π k) :=
    approx_reordered A e (v ∘ π) (fun n => hv _) hπ (fun x n => hd x (π n)) k
  have hdrop (k : ℕ) : complexDrop b k z = (occupationWeight k:ℂ)^z-(v (π k):ℂ)^z := by
    rw [complexDrop,hb,he]
  have hzero (n : ℕ) : complexDrop b (n+M) z = 0 := by
    rw [hdrop,ho _ (Nat.le_add_left M n),ht _ (Nat.le_add_left M n),sub_self]
  have h := (summable_complexDrop b hz).sum_add_tsum_nat_add M
  simp only [hzero,tsum_zero,add_zero] at h
  change _ = relativePartition b z at h
  rw [← h,Finset.sum_congr rfl (fun k _ => hdrop k),Finset.sum_sub_distrib,
    hs (fun x => (x:ℂ)^z),Finset.sum_sub_distrib]

#print axioms relativePartition_finite_diagonal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
