import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovHomogeneousMoments
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBlockProducts

/-!
# Binary chains inside multivariate homogeneous moments

For a shear in one horizontal direction, fix the exponents of the other
horizontal variables. The remaining homogeneous monomials form one binary
chain. Recursively choosing the fixed exponents enumerates every monomial
once, and the physical shear acts by the corresponding binomial block.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Choices of `r` untouched-variable exponents whose sum is at most `d`. -/
def HomogeneousChain : ℕ → ℕ → Type
  | 0, _ => PUnit
  | r + 1, d => Σ j : Fin (d + 1), HomogeneousChain r (d - j.val)

instance homogeneousChainFintype (r d : ℕ) : Fintype (HomogeneousChain r d) := by
  induction r generalizing d with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih =>
    letI : ∀ j : Fin (d + 1), Fintype (HomogeneousChain r (d - j.val)) := fun j => ih _
    exact inferInstanceAs (Fintype (Σ j : Fin (d + 1), HomogeneousChain r (d - j.val)))

/-- The degree left for the two variables on which the shear acts. -/
def chainDegree : {r d : ℕ} → HomogeneousChain r d → ℕ
  | 0, d, _ => d
  | _ + 1, _, a => chainDegree a.2

/-- The exponents of the variables fixed by the shear. -/
def chainExponent : {r d : ℕ} → HomogeneousChain r d → Fin r → ℕ
  | 0, _, _ => Fin.elim0
  | _ + 1, _, a => Fin.cons a.1.val (chainExponent a.2)

/-- The fixed exponents and the remaining binary degree add to the total degree. -/
theorem sum_chainExponent_add_degree (r d : ℕ) (a : HomogeneousChain r d) :
    (∑ i, chainExponent a i) + chainDegree a = d := by
  induction r generalizing d with
  | zero => simp [chainExponent, chainDegree]
  | succ r ih =>
    rcases a with ⟨j, a⟩
    change (∑ i : Fin (r + 1), Fin.cons j.val (chainExponent a) i) + chainDegree a = d
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h := ih (d - j.val) a
    have hj := j.isLt
    omega

/-- Distinct chains have distinct untouched-variable exponents. -/
theorem chainExponent_injective (r d : ℕ) :
    Function.Injective (chainExponent (r := r) (d := d)) := by
  induction r generalizing d with
  | zero => intro a b _; exact Subsingleton.elim (α := PUnit) a b
  | succ r ih =>
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Fin.ext (congrFun h 0)
    subst j
    have hab : chainExponent a = chainExponent b := by
      funext q
      exact congrFun h q.succ
    have he := ih (d - i.val) hab
    subst b
    rfl

/-- Every bounded tuple of untouched-variable exponents determines a chain. -/
theorem exists_chainExponent (r d : ℕ) (β : Fin r → ℕ) (hβ : ∑ i, β i ≤ d) :
    ∃ a : HomogeneousChain r d, chainExponent a = β := by
  induction r generalizing d with
  | zero => exact ⟨PUnit.unit, funext (fun i => Fin.elim0 i)⟩
  | succ r ih =>
    have hsum : β 0 + ∑ i : Fin r, β i.succ ≤ d := by
      simpa only [Fin.sum_univ_succ] using hβ
    let j : Fin (d + 1) := ⟨β 0, by omega⟩
    have ht : ∑ i : Fin r, β i.succ ≤ d - j.val := by
      dsimp only [j]
      omega
    obtain ⟨a, ha⟩ := ih (d - j.val) (fun i => β i.succ) ht
    refine ⟨⟨j, a⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun q => ?_) i
    · rfl
    · exact congrFun ha q

/-- The remaining binary degree is total degree minus the fixed exponents. -/
theorem chainDegree_eq_sub (r d : ℕ) (a : HomogeneousChain r d) :
    chainDegree a = d - ∑ i, chainExponent a i := by
  have h := sum_chainExponent_add_degree r d a
  omega

/-- Chains are exactly the bounded untouched-variable exponent tuples. -/
def chainEquivBounded (r d : ℕ) :
    HomogeneousChain r d ≃ {β : Fin r → ℕ // ∑ i, β i ≤ d} where
  toFun a := ⟨chainExponent a, by have h := sum_chainExponent_add_degree r d a; omega⟩
  invFun β := Classical.choose (exists_chainExponent r d β.val β.property)
  left_inv a := by
    apply chainExponent_injective r d
    exact Classical.choose_spec (exists_chainExponent r d (chainExponent a)
      (by have h := sum_chainExponent_add_degree r d a; omega))
  right_inv β := by
    apply Subtype.ext
    exact Classical.choose_spec (exists_chainExponent r d β.val β.property)

/-- The scalar moment coordinates of one chain. -/
def chainMoment (r d : ℕ) (y : Fin r → ℝ) (x z : ℝ) (a : HomogeneousChain r d) :
    Fin (chainDegree a + 1) → ℝ :=
  (∏ i, y i ^ chainExponent a i) • homogeneousMoment (chainDegree a) x z

/-- Every monomial of degree `d` occurs among the chain coordinates. -/
theorem chainMoment_exhaustive (r d : ℕ) (β : Fin r → ℕ) (p q : ℕ)
    (hdeg : (∑ i, β i) + p + q = d) :
    ∃ (a : HomogeneousChain r d) (j : Fin (chainDegree a + 1)),
      ∀ (y : Fin r → ℝ) (x z : ℝ),
        chainMoment r d y x z a j = (∏ i, y i ^ β i) * (x ^ p * z ^ q) := by
  obtain ⟨a, ha⟩ := exists_chainExponent r d β (by omega)
  have hd : chainDegree a = p + q := by
    have h := sum_chainExponent_add_degree r d a
    rw [ha] at h
    omega
  let j : Fin (chainDegree a + 1) := ⟨q, by omega⟩
  refine ⟨a, j, ?_⟩
  intro y x z
  have hp : chainDegree a - j.val = p := by dsimp only [j]; omega
  simp only [chainMoment, Pi.smul_apply, smul_eq_mul, homogeneousMoment, ha, hp]
  rfl

/-- The physical shear acts separately on every binary chain. -/
theorem shearLinear_chainMoment (r d : ℕ) (θ : ℝ) (y : Fin r → ℝ) (x z : ℝ)
    (a : HomogeneousChain r d) :
    Matrix.toLin' (shearBlock (chainDegree a + 1) θ) (chainMoment r d y x z a) =
      chainMoment r d y x (z + θ * x) a := by
  unfold chainMoment
  rw [map_smul, shearLinear_homogeneousMoment]

#print axioms sum_chainExponent_add_degree
#print axioms chainExponent_injective
#print axioms exists_chainExponent
#print axioms chainEquivBounded
#print axioms chainMoment_exhaustive
#print axioms shearLinear_chainMoment

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
