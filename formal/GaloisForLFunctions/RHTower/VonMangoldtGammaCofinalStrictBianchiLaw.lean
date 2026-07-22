import GaloisForLFunctions.RHTower.VonMangoldtGammaInfinitePointedWard
import GaloisForLFunctions.HTGeometry.DiscreteMomentHankel

/-!
# Strict cofinal pointed-Ward Bianchi law

The cofinal von Mangoldt--Gamma pointed-Ward Gram is not merely positive semidefinite.  Its raw
moments are the discrete moments of positive Euler weights at the logarithmic frequency nodes.
The powers of the prime `2` alone escape every finite node set with positive weight, so every
consecutive moment Hankel block is positive definite.  Every injectively depth-labelled Bianchi
Gram is a principal submatrix of such a block and is therefore positive definite as well.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

noncomputable section

/-- Degree-zero mass of the cofinal pointed raw Euler source. -/
def infiniteVonMangoldtGammaRawWeight (x : ℝ) (n : ℕ) : ℝ :=
  infiniteVonMangoldtGammaRawAtom x 0 n

/-- Logarithmic Euler frequency serving as the raw-moment node. -/
def infiniteVonMangoldtGammaRawNode (n : ℕ) : ℝ :=
  GaloisForLFunctions.RHTower.eulerGeneralizedFrequency n

/-- Every raw atom is its degree-zero weight times the corresponding node power. -/
theorem infiniteVonMangoldtGammaRawAtom_eq_weight_mul_node_pow
    (x : ℝ) (a n : ℕ) :
    infiniteVonMangoldtGammaRawAtom x a n =
      infiniteVonMangoldtGammaRawWeight x n *
        infiniteVonMangoldtGammaRawNode n ^ a := by
  simp [infiniteVonMangoldtGammaRawAtom, infiniteVonMangoldtGammaRawWeight,
    infiniteVonMangoldtGammaRawNode,
    GaloisForLFunctions.RHTower.eulerGeneralizedFrequency]

theorem infiniteVonMangoldtGammaRawWeight_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ infiniteVonMangoldtGammaRawWeight x n := by
  rw [infiniteVonMangoldtGammaRawWeight,
    infiniteVonMangoldtGammaRawAtom]
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le)
    (pow_nonneg (Real.log_pos
      (by exact_mod_cast (show 1 < n + 2 by omega))).le 0)

theorem infiniteVonMangoldtGammaRawNode_pos (n : ℕ) :
    0 < infiniteVonMangoldtGammaRawNode n := by
  exact GaloisForLFunctions.RHTower.eulerGeneralizedFrequency_zero_pos.trans_le
    (GaloisForLFunctions.RHTower.eulerGeneralizedFrequency_strictMono.monotone
      (Nat.zero_le n))

theorem summable_infiniteVonMangoldtGammaRawWeight_mul_node_abs_pow
    {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Summable (fun n ↦ infiniteVonMangoldtGammaRawWeight x n *
      |infiniteVonMangoldtGammaRawNode n| ^ a) := by
  refine (summable_infiniteVonMangoldtGammaRawAtom hx a).congr ?_
  intro n
  rw [infiniteVonMangoldtGammaRawAtom_eq_weight_mul_node_pow]
  rw [abs_of_pos (infiniteVonMangoldtGammaRawNode_pos n)]

/-- The dyadic prime-power ray gives positive raw mass outside every finite node set. -/
theorem infiniteVonMangoldtGammaRaw_infiniteSupport
    (x : ℝ) (F : Finset ℝ) :
    ∃ n : ℕ, infiniteVonMangoldtGammaRawNode n ∉ F ∧
      0 < infiniteVonMangoldtGammaRawWeight x n := by
  let ray : ℕ → ℝ := fun k ↦ ((k + 1 : ℕ) : ℝ) * Real.log 2
  have hray : Function.Injective ray := by
    intro k l hkl
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [ray] at hkl
    have hcast : (k : ℝ) = l := by
      push_cast at hkl
      nlinarith
    exact_mod_cast hcast
  have hrange : (Set.range ray).Infinite :=
    Set.infinite_range_of_injective hray
  have hex : ∃ k : ℕ, ray k ∉ F := by
    by_contra h
    apply hrange
    apply F.finite_toSet.subset
    rintro _ ⟨k, rfl⟩
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  obtain ⟨n, hnnode, hncoeff⟩ :=
    GaloisForLFunctions.RHTower.eulerGeneralizedCoefficient_ray_complete
      0 p (k + 1) (by omega)
  refine ⟨n, ?_, ?_⟩
  · rw [infiniteVonMangoldtGammaRawNode, hnnode]
    have hk' : ((k : ℝ) + 1) * Real.log 2 ∉ F := by
      simpa only [ray, Nat.cast_add, Nat.cast_one] using hk
    simpa [p] using hk'
  · rw [infiniteVonMangoldtGammaRawWeight,
      infiniteVonMangoldtGammaRawAtom_eq_eulerCoefficient]
    exact mul_pos (norm_pos_iff.mpr hncoeff) (Real.exp_pos _)

/-- Exact discrete-moment realization of every cofinal raw moment. -/
theorem infiniteVonMangoldtGammaRawMoment_eq_discreteMoment
    (x : ℝ) (a : ℕ) :
    infiniteVonMangoldtGammaRawMoment x a =
      ∑' n, infiniteVonMangoldtGammaRawWeight x n *
        infiniteVonMangoldtGammaRawNode n ^ a := by
  rw [infiniteVonMangoldtGammaRawMoment]
  apply tsum_congr
  intro n
  exact infiniteVonMangoldtGammaRawAtom_eq_weight_mul_node_pow x a n

/-- Every consecutive cofinal raw-moment Hankel block is positive definite. -/
theorem infiniteVonMangoldtGammaRawHankel_posDef
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (infiniteVonMangoldtGammaRawMoment x) n).PosDef := by
  have h := HTGeometry.discreteMomentHankel_posDef
    (infiniteVonMangoldtGammaRawWeight x)
    infiniteVonMangoldtGammaRawNode
    (infiniteVonMangoldtGammaRawWeight_nonneg x)
    (summable_infiniteVonMangoldtGammaRawWeight_mul_node_abs_pow hx)
    (infiniteVonMangoldtGammaRaw_infiniteSupport x) n
  convert h using 1
  ext i j
  simp only [HTGeometry.momentHankelMatrix]
  exact infiniteVonMangoldtGammaRawMoment_eq_discreteMoment x
    ((i : ℕ) + (j : ℕ))

/-- An injectively depth-labelled cofinal raw Gram is a strict principal Hankel submatrix. -/
theorem infiniteVonMangoldtGammaRawGram_posDef_of_injective
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ)
    (ha : Function.Injective a) :
    (infiniteVonMangoldtGammaRawGram x a).PosDef := by
  classical
  let K : ℕ := ∑ i : Fin n, (a i + 1)
  let e : Fin n → Fin K := fun i ↦ ⟨a i, by
    dsimp [K]
    have hi : a i + 1 ≤ ∑ j : Fin n, (a j + 1) :=
      Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a j + 1)) (Finset.mem_univ i)
    omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply ha
    exact congrArg Fin.val hij
  have hH := infiniteVonMangoldtGammaRawHankel_posDef hx K
  have hsub := hH.submatrix he
  convert hsub using 1

/-- **Universal strict cofinal Bianchi law.**  Positive displacement and distinct depth labels
make the analytic Euler realization of the pointed Gamma--Bianchi current positive definite. -/
theorem vonMangoldtGammaCofinalBianchiGram_posDef_of_injective
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ)
    (ha : Function.Injective a) :
    (vonMangoldtGammaCofinalBianchiGram x a).PosDef := by
  rw [← infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram hx a]
  exact infiniteVonMangoldtGammaRawGram_posDef_of_injective hx a ha

/-- Determinant form of the strict cofinal Bianchi law. -/
theorem det_vonMangoldtGammaCofinalBianchiGram_pos_of_injective
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ)
    (ha : Function.Injective a) :
    0 < (vonMangoldtGammaCofinalBianchiGram x a).det :=
  (vonMangoldtGammaCofinalBianchiGram_posDef_of_injective hx a ha).det_pos

end

end RHTower
