import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Instances.Complex

/-!
# Constitutive primitive-formation properness

Finite interpolation makes weighted polynomial source orbits dense in the full product observer.
For a canonical resolvent packet, the top divided difference is nonzero: an `N + 1` point packet is
outside every formation of degree `< N` but is realized at degree `≤ N`.  Thus product completion
is information-saturating while exact source formation depth remains proper.
-/

open Set Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weighted evaluation of a polynomial formation along an injective clock. -/
def weightedPolynomialOrbit {ι : Type*}
    (nodes : ι ↪ ℂ) (weights : ι → ℂˣ) (P : ℂ[X]) : ι → ℂ :=
  fun i => (weights i : ℂ) * P.eval (nodes i)

/-- Lagrange interpolant after removing the nowhere-zero source weights. -/
def weightedPolynomialInterpolant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (nodes : ι ↪ ℂ) (weights : ι → ℂˣ)
    (target : ι → ℂ) : ℂ[X] :=
  Lagrange.interpolate s nodes (fun i => target i / (weights i : ℂ))

/-- Every finite observer packet is reconstructed exactly by one weighted polynomial formation. -/
theorem weightedPolynomialInterpolant_eval {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (nodes : ι ↪ ℂ) (weights : ι → ℂˣ)
    (target : ι → ℂ) (i : ι) (hi : i ∈ s) :
    weightedPolynomialOrbit nodes weights
        (weightedPolynomialInterpolant s nodes weights target) i = target i := by
  rw [weightedPolynomialOrbit, weightedPolynomialInterpolant,
    Lagrange.eval_interpolate_at_node _ nodes.injective.injOn hi]
  field_simp

/-- **Product primitive saturation.** The weighted polynomial source orbit is dense in the full
product observer whenever its clock is injective and every source weight is a unit. -/
theorem weightedPolynomialOrbit_denseRange {ι : Type*}
    (nodes : ι ↪ ℂ) (weights : ι → ℂˣ) :
    DenseRange (weightedPolynomialOrbit nodes weights) := by
  classical
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨target, htarget⟩ := hUne
  have hUnhds : U ∈ 𝓝 target := hU.mem_nhds htarget
  rw [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hUnhds
  obtain ⟨s, V, hV, hVU⟩ := hUnhds
  let P := weightedPolynomialInterpolant s nodes weights target
  have hPV : weightedPolynomialOrbit nodes weights P ∈ Set.pi (s : Set ι) V := by
    intro i hi
    have his : i ∈ s := Finset.mem_coe.mp hi
    rw [weightedPolynomialInterpolant_eval s nodes weights target i his]
    exact mem_of_mem_nhds (hV i)
  exact ⟨weightedPolynomialOrbit nodes weights P, hVU hPV, ⟨P, rfl⟩⟩

/-- Top divided-difference functional on an `N + 1` node packet. -/
def packetDividedDifference (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ)
    (values : Fin (N + 1) → ℂ) : ℂ :=
  ∑ i, Lagrange.nodalWeight Finset.univ nodes i * values i

/-- A polynomial packet's top divided difference is its degree-`N` coefficient. -/
theorem packetDividedDifference_polynomial_eq_coeff (N : ℕ)
    (nodes : Fin (N + 1) ↪ ℂ) (P : ℂ[X])
    (hP : P.degree < N + 1) :
    packetDividedDifference N nodes (fun i => P.eval (nodes i)) = P.coeff N := by
  have h := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (v := fun i => (nodes i : ℂ)) nodes.injective.injOn (P := P) (by simpa using hP)
  simpa [packetDividedDifference, Lagrange.nodalWeight, div_eq_mul_inv,
    mul_comm] using h.symm

/-- Every formation below depth `N` is annihilated by the `N`-th divided difference. -/
theorem packetDividedDifference_polynomial_eq_zero_of_natDegree_lt
    (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ) (P : ℂ[X])
    (hP : P.natDegree < N) :
    packetDividedDifference N nodes (fun i => P.eval (nodes i)) = 0 := by
  rw [packetDividedDifference_polynomial_eq_coeff N nodes P]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt hP
  · calc
      P.degree ≤ P.natDegree := Polynomial.degree_le_natDegree
      _ < N := by exact_mod_cast hP
      _ < N + 1 := by exact_mod_cast Nat.lt_succ_self N

/-- Resolvent values at an injective clock; the non-pole condition is encoded in the type of `c`. -/
def resolventPacket (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) : Fin (N + 1) → ℂ :=
  fun i => (c.1 - nodes i)⁻¹

/-- Packet realizations by formations of strict depth below `N`. -/
def lowDepthPacketMap (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ) :
    {P : ℂ[X] // P.natDegree < N} → (Fin (N + 1) → ℂ) :=
  fun P i => P.1.eval (nodes i)

/-- Packet realizations by formations of depth at most `N`. -/
def atMostDepthPacketMap (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ) :
    {P : ℂ[X] // P.natDegree ≤ N} → (Fin (N + 1) → ℂ) :=
  fun P i => P.1.eval (nodes i)

/-- Divided difference of the resolvent packet. -/
def resolventDividedDifference (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) : ℂ :=
  ∑ i, Lagrange.nodalWeight Finset.univ nodes i * (c.1 - nodes i)⁻¹

/-- **Resolvent conservation identity.** The top divided difference is the reciprocal nodal
product, so it never vanishes. -/
theorem resolventDividedDifference_eq (N : ℕ) (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    resolventDividedDifference N nodes c = ∏ i, (c.1 - nodes i)⁻¹ := by
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))), c.1 ≠ nodes i := by
    intro i hi hci
    exact c.2 ⟨i, hci.symm⟩
  have hone := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (v := fun i => (nodes i : ℂ)) (r := (1 : Fin (N + 1) → ℂ)) hc
  rw [Lagrange.interpolate_one nodes.injective.injOn Finset.univ_nonempty,
    Polynomial.eval_one, Lagrange.eval_nodal] at hone
  simp only [Pi.one_apply, mul_one] at hone
  rw [resolventDividedDifference, Finset.prod_inv_distrib]
  exact eq_inv_of_mul_eq_one_right hone.symm

/-- Resolvent divided differences are nonzero at every finite packet size. -/
theorem resolventDividedDifference_ne_zero (N : ℕ)
    (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    resolventDividedDifference N nodes c ≠ 0 := by
  rw [resolventDividedDifference_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact inv_ne_zero (sub_ne_zero.mpr fun h => c.2 ⟨i, h.symm⟩)

/-- **Strict depth obstruction.** An `N + 1` point resolvent packet cannot be formed below depth
`N`. Injectivity and the non-pole condition are data, not theorem premises. -/
theorem resolventPacket_not_mem_range_lowDepthPacketMap (N : ℕ)
    (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    resolventPacket N nodes c ∉ Set.range (lowDepthPacketMap N nodes) := by
  rintro ⟨P, hP⟩
  have hzero := packetDividedDifference_polynomial_eq_zero_of_natDegree_lt
    N nodes P.1 P.2
  have hcongr := congrArg (packetDividedDifference N nodes) hP
  have hne := resolventDividedDifference_ne_zero N nodes c
  apply hne
  rw [resolventDividedDifference]
  change packetDividedDifference N nodes (resolventPacket N nodes c) = 0
  rw [← hcongr]
  exact hzero

/-- **Sharp formation upper bound.** The same resolvent packet is formed at depth at most `N`. -/
theorem resolventPacket_mem_range_atMostDepthPacketMap (N : ℕ)
    (nodes : Fin (N + 1) ↪ ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    resolventPacket N nodes c ∈ Set.range (atMostDepthPacketMap N nodes) := by
  let P := Lagrange.interpolate Finset.univ nodes (resolventPacket N nodes c)
  have hdegree := Lagrange.degree_interpolate_le
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (resolventPacket N nodes c) nodes.injective.injOn
  have hnat : P.natDegree ≤ N := by
    apply Polynomial.natDegree_le_of_degree_le
    simpa [P] using hdegree
  refine ⟨⟨P, hnat⟩, ?_⟩
  funext i
  exact Lagrange.eval_interpolate_at_node _ nodes.injective.injOn
    (Finset.mem_univ i)

end

end GaloisForLFunctions.HTGeometry
