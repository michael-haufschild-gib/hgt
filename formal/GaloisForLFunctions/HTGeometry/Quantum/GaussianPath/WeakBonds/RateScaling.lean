import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.EntryRate
import GaloisForLFunctions.HTGeometry.HermitianEigenvalueScaling

/-! # The physical entry flux scales with the coupling norm -/
open Matrix Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes EmptyVisitFlux
noncomputable section

private theorem spectral_sum_congr {I : Type*} [Fintype I] (f g : I → ℝ)
    (h : Multiset.map f (Finset.univ : Finset I).val=Multiset.map g (Finset.univ : Finset I).val)
    (v : ℝ → ℝ) : ∑ i, v (f i)=∑ i, v (g i) := by
  have he := congrArg (fun s : Multiset ℝ => (s.map v).sum) h
  simpa only [Finset.sum_eq_multiset_sum,Multiset.map_map,Function.comp_apply] using he

/-- The rate uses the unordered spectrum. Positive rescaling therefore
multiplies the actual rate by the same factor even if the eigenvalue
labels chosen by diagonalization change. -/
theorem emptyRate_smul (n : ℕ) (ε : ℝ) (x : PrefixIndex n → ℝ) {q : ℝ} (hq : 0 < q) :
    emptyRate n ε (q • x)=q*emptyRate n ε x := by
  let H := prefixGenerator n x
  let K := prefixGenerator n (q • x)
  have he : K.val=(q:ℂ) • H.val := by
    change numberedGenerator n (q • x)=(q:ℂ) • numberedGenerator n x
    rw [numberedGenerator,numberedGenerator,Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,smul_smul]
  let hQ : ((q:ℂ) • H.val).IsHermitian := he ▸ K.2.isHermitian
  have hlabel := isHermitian_eigenvalues_congr K.2.isHermitian hQ he
  let E := H.2.isHermitian.eigenvalues
  let F := K.2.isHermitian.eigenvalues
  have hmass : Multiset.map F Finset.univ.val=Multiset.map (fun i => q*E i) Finset.univ.val := by
    dsimp only [F,E]
    rw [hlabel]
    exact multiset_map_eigenvalues_smul H.2.isHermitian q hQ
  let g (a b : ℝ) := max 0 (b-a)/(2*π)
  have hscale (a b : ℝ) : g (q*a) (q*b)=q*g a b := by
    dsimp only [g]
    rw [←mul_div_assoc,mul_max_of_nonneg _ _ hq.le,mul_zero,mul_sub]
  have hpair : pairTurnRate (fun j => -F j)=q*pairTurnRate (fun j => -E j) := by
    simp only [pairTurnRate,Fintype.sum_prod_type,neg_sub_neg]
    change (∑ i, ∑ j, g (F i) (F j))=q*∑ i, ∑ j, g (E i) (E j)
    calc
      _ = ∑ i, ∑ j, g (q*E i) (F j) := spectral_sum_congr _ _ hmass (fun z => ∑ j, g z (F j))
      _ = ∑ i, ∑ j, g (q*E i) (q*E j) := Finset.sum_congr rfl fun i _ => spectral_sum_congr _ _ hmass (g (q*E i))
      _ = _ := by simp only [hscale,Finset.mul_sum]
  change _*pairTurnRate (fun j => -F j)=q*(_*pairTurnRate (fun j => -E j))
  rw [hpair]
  ring

#print axioms emptyRate_smul
end
end GaloisForLFunctions.HTGeometry.WeakBonds
