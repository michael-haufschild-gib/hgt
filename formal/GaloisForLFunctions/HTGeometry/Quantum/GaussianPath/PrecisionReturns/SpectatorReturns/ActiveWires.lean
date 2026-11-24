import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.SupportedDates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.OneGatePacket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PartitionClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GateFloor

/-! # Sharp first-return exponent at every active-register size -/

open Matrix Finset Set Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

private def bits {N : ℕ} (S : Finset (Fin N)) (x : Fin N→Bool) : S→Bool := fun i => x i.val

private theorem bits_surjective {N : ℕ} (S : Finset (Fin N)) : Function.Surjective (bits S) := by
  intro z
  refine ⟨(fun i => if h : i∈S then z ⟨i,h⟩ else false),?_⟩
  funext i
  simp only [bits,dif_pos i.property]

/-- A diagonal phase table on the selected bits acts as identity on
spectators. Repeated phases may have larger multiplicity. -/
private theorem diagonal_support {N : ℕ} (S : Finset (Fin N)) (p : (S→Bool)→ℂ) :
    IsSiteSupported S (diagonal (p ∘ bits S)) := by
  constructor
  · rintro x y ⟨i,_,hh⟩
    exact diagonal_apply_ne _ (fun he => hh (congrFun he i))
  intro x y u v hxu hyv hxy huv
  have heq (a b : Fin N→Bool) (hout : ∀ i, i∉S → a i=b i) : a=b ↔ bits S a=bits S b := by
    refine ⟨congrArg _,fun h => funext fun i => ?_⟩
    by_cases hi : i∈S
    · exact congrFun h ⟨i,hi⟩
    · exact hout i hi
  have h₁ : bits S x=bits S u := funext fun i => hxu _ i.property
  have h₂ : bits S y=bits S v := funext fun i => hyv _ i.property
  have hh : x=y ↔ u=v := by rw [heq _ _ hxy,heq _ _ huv,h₁,h₂]
  by_cases h : x=y
  · rw [h,hh.mp h,diagonal_apply_eq,diagonal_apply_eq]
    exact congrArg p h₂
  · rw [diagonal_apply_ne _ h,diagonal_apply_ne _ (mt hh.mpr h)]

/-- On a typical fixed prefix the first orbit point approximable in any
basis by a unitary on at most b<N wires has precision exponent
2ᴺ−2ᵇ−1. The observation origin can depend on the entire frozen chain. -/
theorem gaussian_active_wire_date :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ b : ℕ, b<N → ∀ a > (0:ℝ),
        Tendsto (fun ε => log (firstSupportedDate H a b ε)/log (1/ε))
          (𝓝[>] 0) (𝓝 ((2^N-2^b-1:ℕ):ℝ)) := by
  classical
  filter_upwards [gaussian_center_floor,gaussian_partition_clock] with ω hl hu k
  intro N H b hb a ha
  let n := 2^N-2^b-1
  have hD : (2:ℕ)^N=2*2^(k+2) := by change 2^(k+2+1)=_; rw [pow_succ,Nat.mul_comm]
  have hpow : (2:ℕ)^b ≤ 2^(k+2) := Nat.pow_le_pow_right (by decide) (by dsimp only [N] at hb; omega)
  have hM : 4 ≤ (2:ℕ)^(k+2) := (by decide : 4≤(2:ℕ)^2).trans
    (Nat.pow_le_pow_right (by decide) (show 2 ≤ k+2 by omega))
  have hn : 0<n := by dsimp only [n]; omega
  have hsize : 2^b+(n+1) ≤ 2^N := by dsimp only [n]; omega
  apply tendsto_order.mpr
  constructor
  · intro lo hlo
    filter_upwards [hl k a ha n (2^b) hn hsize lo hlo,self_mem_nhdsWithin] with ε hf (he : 0<ε)
    obtain ⟨hat,S,hS,V,B,hB,hfit⟩ := (firstSupportedDate_isLeast H a b he).1
    have hnormal : star B.val*B.val=B.val*star B.val := B.property.1.trans B.property.2.symm
    obtain ⟨f,hcard,hnear⟩ := centers_of_supported_fit H _ V hB hnormal he hfit
    exact hf _ hat f (hcard.trans (Nat.pow_le_pow_right (by decide) hS)) hnear
  intro upper hup
  obtain ⟨S,_,hS⟩ := exists_subset_card_eq (s:=(univ : Finset (Fin N))) (by simpa only [card_univ,Fintype.card_fin] using hb.le)
  have hJ : Fintype.card (S→Bool)=2^b := by rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,hS]
  have hnum : 2^N-Fintype.card (S→Bool)=n+1 := by rw [hJ]; dsimp only [n]; omega
  filter_upwards [hu k (S→Bool) (bits S) (bits_surjective S) n hn hnum a ha upper hup,
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hh he
  obtain ⟨t,hat,hlog,p,hp,hnear⟩ := hh
  let B : unitaryGroup (Fin N→Bool) ℂ := ⟨diagonal (p ∘ bits S),
    StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _ (fun i => hp (bits S i))⟩
  have hfit : t ∈ supportedDates H b ε :=
    ⟨S,hS.le,star H.2.isHermitian.eigenvectorUnitary,B,diagonal_support S p,diagonal_fit_in_energy_basis H t _ hnear⟩
  have hfirst := firstSupportedDate_isLeast H a b he.1
  exact (div_le_div_of_nonneg_right (log_le_log (ha.trans_le hfirst.1.1) (hfirst.2 ⟨hat,hfit⟩))
    (log_pos ((one_lt_div he.1).mpr he.2)).le).trans_lt hlog

#print axioms gaussian_active_wire_date
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
