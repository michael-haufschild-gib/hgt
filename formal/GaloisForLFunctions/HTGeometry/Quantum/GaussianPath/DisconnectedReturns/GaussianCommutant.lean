import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.PathWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.GenericRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.Coercivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # Generic joint commutant of a Gaussian path and its interactions across a cut -/
open Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
open UntouchedSites
variable {n : ℕ}

def selected (s : Finset (Fin (n+1))) : PathLabel n → Bool
  | .inl _ => false
  | .inr (e,_) => decide (e∈s)

theorem bondPart_eq_sum (u : PathShell n) (s : Finset (Fin (n+1))) :
    bondPart u s = ∑ l, (u l:ℂ) •
      (if selected s l then finitePauliMatrix (pathWord l) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [selected,Fintype.sum_prod_type,Bool.false_eq_true,if_false,smul_zero,
    Finset.sum_const_zero,zero_add,decide_eq_true_eq,pathWord]
  have hleft : bondPart u s = ∑ e, if e∈s then edgePart u e else 0 := by
    rw [←Finset.sum_filter]
    simp [bondPart]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : e∈s <;> simp [h,edgePart,Fintype.sum_prod_type]

private abbrev Index (n : ℕ) := Fin (Fintype.card (ChainLabel (n+2)))
private def word (i : Index n) := finitePauliMatrix (pathWord (pathCoeffEquiv n i))

private def test (P : Index n → Register (n+2)) (r : Fin (n+2)→Bool) (i : Index n) :
    (Matrix.entryLinearMap ℂ ℂ r r).ker →ₗ[ℂ] Register (n+2) :=
  (bracket (P i)).comp (Matrix.entryLinearMap ℂ ℂ r r).ker.subtype

private theorem test_sum (P : Index n → Register (n+2)) (r : Fin (n+2)→Bool)
    (x : Index n → ℝ) (U : (Matrix.entryLinearMap ℂ ℂ r r).ker) :
    pencil (test P r) x U =
      (∑ i, (x i:ℂ) • P i)*U.val-U.val*(∑ i, (x i:ℂ) • P i) := by
  rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  simp only [pencil,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.smul_mul,Matrix.mul_smul,←smul_sub]
  rfl

private theorem fixed_bonds_ae (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (r : Fin (n+2)→Bool) : ∀ᵐ ω ∂pathPauliDisorderLaw, let u := pathPauliDisorderShell ω n
      ∀ X : Register (n+2), Commute X (pathHamiltonian u) → Commute X (bondPart u s) →
        X=X r r • (1 : Register (n+2)) := by
  let E := (Matrix.entryLinearMap ℂ ℂ r r).ker
  let P (i : Index n) := if selected s (pathCoeffEquiv n i) then word i else 0
  let L (i : Index n) := (test word r i).prod (test P r i)
  have hsum (u : PathShell n) (Y : E) : pencil L (fun i => u (pathCoeffEquiv n i)) Y =
      (pathHamiltonian u*Y.val-Y.val*pathHamiltonian u,bondPart u s*Y.val-Y.val*bondPart u s) := by
    have hH := (pathCoeffEquiv n).sum_comp (fun l => (u l:ℂ) • finitePauliMatrix (pathWord l))
    have hB := (pathCoeffEquiv n).sum_comp (fun l => (u l:ℂ) •
      (if selected s l then finitePauliMatrix (pathWord l) else 0))
    rw [←pathHamiltonian_eq_sum] at hH
    rw [←bondPart_eq_sum] at hB
    change (∑ i, (u (pathCoeffEquiv n i):ℂ) • word i)=_ at hH
    change (∑ i, (u (pathCoeffEquiv n i):ℂ) • P i)=_ at hB
    rw [←hH,←hB,←test_sum word r,←test_sum P r]
    simp only [pencil,LinearMap.sum_apply,LinearMap.smul_apply]
    apply Prod.ext
    · change LinearMap.fst ℂ _ _ (∑ i, _) = _
      rw [map_sum]
      rfl
    · change LinearMap.snd ℂ _ _ (∑ i, _) = _
      rw [map_sum]
      rfl
  let w (i : Index n) := witness n (pathCoeffEquiv n i)
  have hw : Function.Injective (pencil L w) := by
    rw [←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro Y hY
    have hh := (hsum (witness n) Y).symm.trans hY
    have hc := witness_joint_scalar s hs r Y.val
      (sub_eq_zero.mp (congrArg Prod.fst hh)).symm (sub_eq_zero.mp (congrArg Prod.snd hh)).symm
    have hy : Y.val r r=0 := Y.property
    apply Subtype.ext
    change Y.val=0
    simpa only [hy,zero_smul] using hc
  have hac : centredProductGaussian (Index n) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous _ one_ne_zero (fun _ => 0)
  have hg := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae
    (hac.ae_le (pencil_ae_injective L w hw))
  filter_upwards [hg] with ω hω u X hX hB
  let Y := X-X r r • (1 : Register (n+2))
  have hm : Y∈E := by change Y r r=0; simp [Y]
  let Z : E := ⟨Y,hm⟩
  have hz (M : Register (n+2)) (h : Commute X M) : M*Y-Y*M=0 := by
    dsimp only [Y]
    rw [mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,h.eq,sub_self]
  have he : pencil L (fun i => u (pathCoeffEquiv n i)) Z=0 := by
    rw [hsum,hz _ hX,hz _ hB]; rfl
  have he' : Z=0 := hω (he.trans (map_zero _).symm)
  exact sub_eq_zero.mp (congrArg Subtype.val he')

/-- On every finite prefix of one draw, the Hamiltonian and the sum of
its interactions on any nonempty set of bonds have scalar joint commutant. -/
theorem gaussian_bond_joint_scalar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n, ∀ s : Finset (Fin (n+1)), s.Nonempty →
      let u := pathPauliDisorderShell ω n
      let r : Fin (n+2)→Bool := fun _ => false
      ∀ X : Register (n+2), Commute X (pathHamiltonian u) → Commute X (bondPart u s) →
        X=X r r • (1 : Register (n+2)) :=
  ae_all_iff.mpr fun n => ae_all_iff.mpr fun s => by
    by_cases hs : s.Nonempty
    · filter_upwards [fixed_bonds_ae s hs (fun _ => false)] with ω hω _
      exact hω
    · exact ae_of_all _ fun _ h => (hs h).elim

#print axioms gaussian_bond_joint_scalar
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
