import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.SupportedPhases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.ThreeBlocks
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection

/-! # Uniform circuit cost near a simple diagonal cut chain -/
open Filter Topology Set Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section
open DiagonalSynthesis
open PrescribedTimes

/-- Erasing an edge leaves precisely the packets on its two sides. -/
theorem cut_eq_packets {n : ℕ} (u : PathShell n) (a : Fin (n+1)) :
    pathHamiltonianCut u a=packet u (leftBlock a)+packet u (rightBlock a) := by
  let L := leftBlock a
  let R := rightBlock a
  have hsite (i : Fin (n+2)) (X : Register (n+2)) : X=(if i∈L then X else 0)+(if i∈R then X else 0) := by
    by_cases h : i ≤ a.castSucc <;> simp [L,R,leftBlock,rightBlock,h,lt_iff_not_ge]
  have hedge (g : Fin (n+1)) (X : Register (n+2)) :
      X=(if g.castSucc∈L ∧ g.succ∈L then X else 0)+(if g.castSucc∈R ∧ g.succ∈R then X else 0)+(if g=a then X else 0) := by
    have hl : (g.castSucc∈L ∧ g.succ∈L) ↔ g<a := by
      simp only [L,leftBlock,Finset.mem_Iic,Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ]; omega
    have hr : (g.castSucc∈R ∧ g.succ∈R) ↔ a<g := by
      simp only [R,rightBlock,Finset.mem_Ioi,Fin.lt_def,Fin.val_castSucc,Fin.val_succ]; omega
    rw [if_congr hl rfl rfl,if_congr hr rfl rfl]
    rcases lt_trichotomy g a with h|rfl|h
    · simp [h,h.ne,not_lt_of_gt h]
    · simp
    · simp [h,h.ne',not_lt_of_gt h]
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => hsite i (onsiteAt u i))
  have he := Finset.sum_congr (s₁:=Finset.univ) rfl (fun g _ => hedge g (edgePart u g))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs he
  have ho : onsitePart u=∑ i, onsiteAt u i := by simp only [onsitePart,onsiteAt,Fintype.sum_prod_type]
  rw [pathHamiltonianCut,pathHamiltonian,ho,hs,he]
  unfold packet
  dsimp only [L,R] at *
  abel

def blockCost (k : ℕ) := 2^k*(2*k+1)

/-- The same coefficient neighborhood works at every time. Only the
cut evolution is approximated here, independently on the two halves. -/
theorem cut_neighborhood {n : ℕ} (a : Fin (n+1))
    (hL : 2 ≤ (leftBlock a).card) (hR : 2 ≤ (rightBlock a).card)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    let x₀ := fun i => sepCarrier n A 0 (pathCoeffEquiv n i)
    ∃ r > 0, ∀ u : PathShell n, (∀ i, |u (pathCoeffEquiv n i)-x₀ i| < r) →
      ∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) ε
        (blockCost (leftBlock a).card+blockCost (rightBlock a).card) (unitaryEvolution (pathHamiltonianCut u a) t) := by
  intro x₀
  let u₀ := sepCarrier n A 0
  let d (i) := ((pathDiagEnergy u₀ i:ℝ):ℂ)
  let K (x : PrefixIndex n→ℝ) := numberedGenerator n x -
    ∑ ab : Fin 3 × Fin 3, (x ((pathCoeffEquiv n).symm (Sum.inr (a,ab))):ℂ) • finitePauliMatrix (couplingWord a ab)
  have hK (u : PathShell n) : K (fun i => u (pathCoeffEquiv n i))=pathHamiltonianCut u a := by
    simp only [K,numberedGenerator_shell,Equiv.apply_symm_apply,pathHamiltonianCut,edgePart]
  have hd : Function.Injective d := by
    intro i j he
    by_contra hn
    have h := abs_sub_pathDiagEnergy_sepCarrier_ge (n:=n) (A:=A) (b:=0) hA.le le_rfl hn
    have hh := Complex.ofReal_injective he
    change pathDiagEnergy u₀ i=pathDiagEnergy u₀ j at hh
    change 2*A-2*0*((n:ℝ)+1) ≤ |pathDiagEnergy u₀ i-pathDiagEnergy u₀ j| at h
    rw [hh,sub_self,abs_zero] at h
    linarith only [h,hA]
  have hbase : K x₀=diagonal d := by
    rw [hK,pathHamiltonianCut,pathHamiltonian_eq_diagonal u₀ (sepCarrier_offDiag A 0)]
    have he : edgePart u₀ a=0 := by
      apply Finset.sum_eq_zero
      intro ab _
      have h : u₀ (Sum.inr (a,ab))=0 := by change (if ab=(2,2) then (0:ℝ) else 0)=0; simp
      rw [h,Complex.ofReal_zero,zero_smul]
    rw [he,sub_zero]
  have hc : Continuous K := by unfold K numberedGenerator; fun_prop
  have hlim : Tendsto K (𝓝 x₀) (𝓝 (diagonal d)) := hbase ▸ hc.continuousAt
  let L := leftBlock a
  let R := rightBlock a
  have hdis : Disjoint L R := Finset.disjoint_left.mpr fun _ hl hr => (mem_Ioi.mp hr).not_ge (mem_Iic.mp hl)
  have hgood := hlim.eventually ((eventually_cheap_supported L hL d hd (half_pos hε)).and
    (eventually_cheap_supported R hR d hd (half_pos hε)))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨r,hr,fun u hu t => ?_⟩
  let x := fun i => u (pathCoeffEquiv n i)
  have hx : x∈Metric.ball x₀ r := (Metric.mem_ball).mpr ((dist_pi_lt_iff hr).mpr
    (fun i => by simpa only [Real.dist_eq] using hu i))
  obtain ⟨hleft,hright⟩ := hball hx
  let l := packet u L
  let b := packet u R
  let U := unitaryEvolution l t
  let V := unitaryEvolution b t
  have hu₁ := isSiteSupported_unitaryEvolution (packet_supported u L) t
  have hu₂ := isSiteSupported_unitaryEvolution (packet_supported u R) t
  have hsum : K x=l+b := (hK u).trans (cut_eq_packets u a)
  have hcomL : K x*U=U*K x := by
    rw [hsum,add_mul,mul_add,unitaryEvolution_commutes_generator l t,
      (commute_of_isSiteSupported_disjoint hdis.symm (packet_supported u R) hu₁).eq]
  have hcomR : K x*V=V*K x := by
    rw [hsum,add_mul,mul_add,unitaryEvolution_commutes_generator b t,
      (commute_of_isSiteSupported_disjoint hdis (packet_supported u L) hu₂).eq]
  have hLU := hleft ⟨U,unitaryEvolution_mem_unitary (packet_selfAdjoint u L) t⟩ hu₁ hcomL
  have hRV := hright ⟨V,unitaryEvolution_mem_unitary (packet_selfAdjoint u R) t⟩ hu₂ hcomR
  have hprod := LocalPatches.approx_product (unitaryEvolution_mem_unitary (packet_selfAdjoint u R) t) hLU hRV
  rw [cut_eq_packets,unitaryEvolution_add_of_isSiteSupported_disjoint hdis (packet_supported u L) (packet_supported u R)]
  exact (add_halves ε) ▸ hprod

#print axioms cut_neighborhood
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
