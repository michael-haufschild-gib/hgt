import GaloisForLFunctions.HTGeometry.ElementaryOstrowski

open Polynomial
open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The trace coordinate of an algebraic additive primitive is fixed by an
arbitrary family of compatible automorphisms. No commutativity is required. -/
theorem automorphismFamily_algebraicPrimitive_traceCoordinate_fixed
    {I K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i x, sigma i (algebraMap K L x) =
      algebraMap K L (tau i x))
    {g : L} (hg : IsIntegral K g) (b : I → K)
    (hshift : ∀ i, sigma i g = g + algebraMap K L (b i)) :
    ∀ i, sigma i
      (g + algebraMap K L
        ((minpoly K g).nextCoeff / ((minpoly K g).natDegree : K))) =
      g + algebraMap K L
        ((minpoly K g).nextCoeff / ((minpoly K g).natDegree : K)) := by
  let P := minpoly K g
  have hPmonic : P.Monic := minpoly.monic hg
  have hPpos : 0 < P.natDegree := (minpoly.irreducible hg).natDegree_pos
  have hnK : (P.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr hPpos.ne'
  intro i
  have hcomp' : (algebraMap K L).comp (tau i).toRingHom =
      (sigma i).toRingHom.comp (algebraMap K L) := by
    ext x
    exact (hcomp i x).symm
  have hmap : P.map (tau i).toRingHom = minpoly K (sigma i g) := by
    exact minpoly_map_eq_of_ringEquiv_of_isIntegral hcomp' hg
  have hpoly : P.map (tau i).toRingHom =
      P.comp (X - Polynomial.C (b i)) := by
    rw [hmap, hshift, minpoly.add_algebraMap]
  have hnext := congrArg Polynomial.nextCoeff hpoly
  rw [Polynomial.nextCoeff_map (tau i).injective] at hnext
  have htaylor : P.comp (X - Polynomial.C (b i)) = P.taylor (-(b i)) := by
    simp [Polynomial.taylor_apply, sub_eq_add_neg]
  rw [htaylor, nextCoeff_taylor_of_monic P hPmonic hPpos] at hnext
  simp only [mul_neg] at hnext
  have hnext' : tau i P.nextCoeff =
      P.nextCoeff + -(P.natDegree : K) * b i := by
    simpa using hnext
  have hfrac : b i + tau i (P.nextCoeff / (P.natDegree : K)) =
      P.nextCoeff / (P.natDegree : K) := by
    rw [map_div₀ (tau i), map_natCast, hnext']
    field_simp
    ring
  rw [map_add, hshift, hcomp]
  simpa [P, add_assoc] using
    congrArg (fun z : K => g + algebraMap K L z) hfrac

theorem automorphismFamily_algebraicPrimitive_eq_base_add_fixed
    {I K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i x, sigma i (algebraMap K L x) =
      algebraMap K L (tau i x))
    {g : L} (hg : IsIntegral K g) (b : I → K)
    (hshift : ∀ i, sigma i g = g + algebraMap K L (b i)) :
    ∃ k : K, ∃ z : L, (∀ i, sigma i z = z) ∧
      g = algebraMap K L k + z := by
  let t : K :=
    (minpoly K g).nextCoeff / ((minpoly K g).natDegree : K)
  let z : L := g + algebraMap K L t
  have hz : ∀ i, sigma i z = z :=
    automorphismFamily_algebraicPrimitive_traceCoordinate_fixed
      tau sigma hcomp hg b hshift
  refine ⟨-t, z, hz, ?_⟩
  simp [z, t]

/-- Algebraic dependence under arbitrary compatible automorphisms gives a
nonzero fixed-field Kähler circuit. -/
theorem automorphismFamily_exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) = 0 := by
  classical
  let W : Submodule L (kappa →₀ L) :=
    LinearMap.ker (Finsupp.linearCombination L
      (fun k ↦ KaehlerDifferential.D K L (x k)))
  obtain ⟨u, hu0, hurel⟩ :=
    exists_nonzero_kaehler_relation_of_not_algebraicIndependent x hdep
  have huW : u ∈ W := LinearMap.mem_ker.mpr hurel
  have hW0 : W ≠ ⊥ := by
    intro hbot
    have : u ∈ (⊥ : Submodule L (kappa →₀ L)) := by
      simpa [hbot] using huW
    exact hu0 (by simpa using this)
  have hWstable : ∀ i v, v ∈ W →
      finsuppMapRangeRingEquiv sigma i v ∈ W := by
    intro i v hv
    exact kaehler_relationSpace_stable_of_base_shifts
      tau sigma hcomp x b hshift i v hv
  obtain ⟨c, hc0, hcW⟩ :=
    stable_finsupp_submodule_exists_nonzero_constant_vector
      sigma hfixed W hWstable hW0
  exact ⟨c, hc0, LinearMap.mem_ker.mp hcW⟩

theorem automorphismFamily_exists_nonzero_constant_algebraic_linearCombination
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      IsAlgebraic K
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) := by
  obtain ⟨c, hc0, hrel⟩ :=
    automorphismFamily_exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
      tau sigma hcomp hfixed x b hshift hdep
  refine ⟨c, hc0, isAlgebraic_of_kaehlerD_eq_zero ?_⟩
  rw [kaehlerD_constantCoefficient_linearCombination]
  exact hrel

/-- Noncommutative-family Ostrowski theorem. -/
theorem automorphismFamily_exists_nonzero_constant_simultaneous_telescoping
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧ ∃ k : K, ∀ i,
      tau i k - k =
        Finsupp.linearCombination K (b i)
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c) := by
  classical
  obtain ⟨c, hc0, hcalg⟩ :=
    automorphismFamily_exists_nonzero_constant_algebraic_linearCombination
      tau sigma hcomp hfixed x b hshift hdep
  let cL : kappa →₀ L := Finsupp.mapRange (algebraMap C L)
    (map_zero (algebraMap C L)) c
  let cK : kappa →₀ K := Finsupp.mapRange (algebraMap C K)
    (map_zero (algebraMap C K)) c
  let g : L := Finsupp.linearCombination L x cL
  let bsum : I → K := fun i ↦ Finsupp.linearCombination K (b i) cK
  have hshiftg : ∀ i, sigma i g = g + algebraMap K L (bsum i) := by
    intro i
    dsimp only [g]
    rw [ringEquiv_linearCombination]
    have hcmap :
        Finsupp.mapRange (sigma i) (map_zero (sigma i)) cL = cL := by
      ext j
      simp [cL, hCfixed]
    rw [hcmap]
    simp_rw [hshift]
    rw [finsupp_linearCombination_add_family]
    rw [algebraMap_constant_finsupp_linearCombination]
  have hgint : IsIntegral K g := hcalg.isIntegral
  obtain ⟨k, z, hzfix, hg⟩ :=
    automorphismFamily_algebraicPrimitive_eq_base_add_fixed
      tau sigma hcomp hgint bsum hshiftg
  refine ⟨c, hc0, k, ?_⟩
  intro i
  apply (algebraMap K L).injective
  have hleft : sigma i g - g = algebraMap K L (bsum i) := by
    rw [hshiftg i]
    abel
  have hright : sigma i g - g = algebraMap K L (tau i k - k) := by
    rw [hg, map_add, hcomp, hzfix i]
    simp only [map_sub]
    abel
  rw [← hright, hleft]

theorem automorphismFamily_algebraicIndependent_of_no_constant_simultaneous_telescoping
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) =
      x k + algebraMap K L (b i k))
    (hnot : ∀ c : kappa →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      tau i k - k ≠
        Finsupp.linearCombination K (b i)
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    AlgebraicIndependent K x := by
  by_contra hdep
  obtain ⟨c, hc0, k, hall⟩ :=
    automorphismFamily_exists_nonzero_constant_simultaneous_telescoping
      tau sigma hcomp hCfixed hfixed x b hshift hdep
  obtain ⟨i, hi⟩ := hnot c hc0 k
  exact hi (hall i)

theorem ringEquiv_differentialJet
    {I L : Type*} [Field L] [Differential L]
    (sigma : I → L ≃+* L)
    (hderiv : ∀ i x, sigma i x′ = (sigma i x)′)
    (i : I) (n : ℕ) (x : L) :
    sigma i (differentialJet n x) = differentialJet n (sigma i x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, hderiv, ih]

/-- Noncommutative-family differential Ostrowski criterion. -/
theorem automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L] [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i x, sigma i x′ = (sigma i x)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, sigma i (x k) =
      x k + algebraMap K L (b i k))
    (hnot : ∀ c : (kappa × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      tau i k - k ≠
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 (b i p.1))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    DifferentialIndependent K x := by
  let xJet : kappa × ℕ → L := fun p ↦ differentialJet p.2 (x p.1)
  let bJet : I → kappa × ℕ → K :=
    fun i p ↦ differentialJet p.2 (b i p.1)
  have hshiftJet : ∀ i p, sigma i (xJet p) =
      xJet p + algebraMap K L (bJet i p) := by
    intro i p
    dsimp only [xJet, bJet]
    rw [ringEquiv_differentialJet sigma hderiv, hshift]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  have hAI : AlgebraicIndependent K xJet :=
    automorphismFamily_algebraicIndependent_of_no_constant_simultaneous_telescoping
      tau sigma hcomp hCfixed hfixed xJet bJet hshiftJet (by
        intro c hc0 k
        simpa only [bJet] using hnot c hc0 k)
  exact hAI

end

end GaloisForLFunctions
