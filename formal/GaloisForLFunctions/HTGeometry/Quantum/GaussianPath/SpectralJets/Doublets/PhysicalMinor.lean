import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.LimitingMinor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PathSymmetry
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.ContinuousLevels
import Mathlib.Topology.ContinuousMap.Algebra

/-! # A longitudinal spectral minor on the nearest-neighbour Ising pencil -/
open Matrix Filter Topology Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

def representative {n : ℕ} (s : Fin n → Bool) : Fin (n+1) → Bool := Fin.cons false s

def spinVector {n : ℕ} (s : Fin n → Bool) (i : Fin n) : ℂ := Walsh.boolSign (s i)

theorem spinVector_rep {n : ℕ} (s : Fin n → Bool) : spinVector (representative s) = orientedSpin s := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem spinVector_rev {n : ℕ} (s : Fin n → Bool) : spinVector (reverseSpins s) = -spinVector s := by
  funext i
  cases h : s i <;> simp [spinVector,reverseSpins,Walsh.boolSign,h]

theorem split_at_zero (n : ℕ) :
    pathHamiltonian (splitShell n 0) = diagonal (fun s => (bondEnergy s:ℂ)) := by
  simpa only [splitShell,sub_zero,one_smul,zero_smul,add_zero] using diagonal_ising n

theorem split_continuous (n : ℕ) : Continuous (fun v => pathHamiltonian (splitShell n v)) := by
  simp_rw [split_matrix]
  exact ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)

private theorem spectator_product_ne_zero {n : ℕ} (s : Fin (n+2) → Bool) :
    (2 * ∏ j ∈ (univ.erase s).erase (reverseSpins s), ((bondEnergy s:ℂ)-(bondEnergy j:ℂ))) ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hj' := mem_erase.mp hj
  have hjs := (mem_erase.mp hj'.2).1
  apply sub_ne_zero.mpr
  intro h
  have hg := bond_gap j s hjs hj'.1
  rw [Complex.ofReal_inj.mp h,sub_self,abs_zero] at hg
  norm_num at hg

/-- Polynomial belonging to one chosen member of a split pair; its root at zero field is 1. -/
def physicalPolynomial {n : ℕ} (v : ℝ) (E : (Fin (n+2) → Bool) → ℂ) (s : Fin (n+1) → Bool) :=
  let j := representative s
  let t := reverseSpins j
  pairPolynomial (pathHamiltonian (splitShell n v)) E spinVector j t ((E j+E t)/2) ((E j-E t)/2)

private def specialize (v : ℝ) : C(ℝ,ℂ) →+* ℂ where
  toFun f := f v
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- All sufficiently small transverse couplings have a nonsingular normalized response
minor of order N−1 rounded up to even. The labels and polynomial are those of the
original nearest-neighbour Hamiltonian. -/
theorem physical_minor_near_zero (n : ℕ) :
    ∃ E : (Fin (n+2) → Bool) → ℝ → ℂ, (∀ j, Continuous (E j)) ∧
      (∀ v, (pathHamiltonian (splitShell n v)).charpoly =
        ∏ j, (Polynomial.X-Polynomial.C (E j v))) ∧
      ∀ᶠ v in 𝓝 (0:ℝ), (Matrix.of fun a s : Fin (n+1) → Bool =>
        upperResponse (physicalPolynomial v (fun j => E j v) s) (maskWord a)).det ≠ 0 := by
  let H := fun v : ℝ => pathHamiltonian (splitShell n v)
  have hH := split_continuous n
  obtain ⟨L,hL,hL0,hchar⟩ := continuous_levels H hH
    (fun v => (isSelfAdjoint_pathHamiltonian (splitShell n v)).isHermitian) 0 bondEnergy (split_at_zero n)
  let E (j : Fin (n+2) → Bool) : C(ℝ,ℂ) := ⟨fun v => (L j v:ℂ),Complex.continuous_ofReal.comp (hL j)⟩
  let A : Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) C(ℝ,ℂ) :=
    Matrix.of fun i j => ⟨fun v => H v i j,(continuous_apply j).comp ((continuous_apply i).comp hH)⟩
  let u (j : Fin (n+2) → Bool) (i : Fin (n+2)) : C(ℝ,ℂ) := ContinuousMap.const ℝ (spinVector j i)
  let half : C(ℝ,ℂ) := ContinuousMap.const ℝ (2:ℂ)⁻¹
  let p (s : Fin (n+1) → Bool) :=
    let j := representative s
    let t := reverseSpins j
    pairPolynomial A E u j t ((E j+E t)*half) ((E j-E t)*half)
  have he (v : ℝ) (s) : MvPolynomial.map (specialize v) (p s) =
      physicalPolynomial v (fun j => E j v) s := by
    unfold p physicalPolynomial
    rw [map_pairPolynomial,map_mul,map_mul,map_add,map_sub,div_eq_mul_inv,div_eq_mul_inv]
    rfl
  let q (s : Fin (n+1) → Bool) := 2 * ∏ j ∈
    (univ.erase (representative s)).erase (reverseSpins (representative s)),
    ((bondEnergy (representative s):ℂ)-(bondEnergy j:ℂ))
  have hp (s) : MvPolynomial.map (specialize 0) (p s) = limitPoly (q s) (orientedSpin s) := by
    rw [he]
    let j := representative s
    let t := reverseSpins j
    have hb : bondEnergy t=bondEnergy j := by
      have hw := (walls_eq_iff t j).mpr (Or.inr rfl)
      simp only [bondEnergy,hw]
    have hE : (fun k => E k 0) = fun k => (bondEnergy k:ℂ) := by
      funext k
      exact congrArg Complex.ofReal (hL0 k)
    rw [hE]
    change pairPolynomial (H 0) _ _ j t _ _ = _
    have hmid : ((bondEnergy j:ℂ)+(bondEnergy t:ℂ))/2=(bondEnergy j:ℂ) := by rw [hb]; ring
    have hgap : ((bondEnergy j:ℂ)-(bondEnergy t:ℂ))/2=0 := by rw [hb,sub_self,zero_div]
    rw [show H 0=_ from split_at_zero n,hmid,hgap]
    rw [pairPolynomial_diagonal _ _ j t (reversed_ne j) (congrArg Complex.ofReal hb.symm) (spinVector_rev j)]
    rw [spinVector_rep]
    rfl
  refine ⟨fun j v => E j v,fun j => (E j).continuous,hchar,?_⟩
  simpa only [he] using eventually_upper_minor (n+1) p specialize (specialize 0)
    (fun f => f.continuous.continuousAt.tendsto) q (fun s => spectator_product_ne_zero (representative s)) hp

#print axioms physical_minor_near_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
