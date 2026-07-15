import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous polynomial equations for finite directional Kähler loci

The finite directional Kähler wedge expands over packets of ordered derivation words.  Its
coefficient vectors span a finite-dimensional space even when the ambient exterior power is
infinite-dimensional.  Coordinates in a basis of that span therefore turn wedge vanishing into a
finite family of homogeneous scalar polynomial equations of degree `n * (n + 1) / 2`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module MvPolynomial

variable {k K L ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [CharZero K] [Fintype ι]

omit [CharZero K] in
/-- Applying the universal Kähler derivation to a directional jet preserves its ordered-word
expansion because every direction coordinate lies in the base field. -/
theorem kaehlerD_directionalJet_eq_sum_words
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) (n : ℕ) :
    KaehlerDifferential.D K L (directionalJet δ c n x) =
      ∑ w : Fin n → ι,
        algebraMap k L (∏ r, c (w r)) •
          KaehlerDifferential.D K L (directionalWordDerivative δ x w) := by
  rw [directionalJet_eq_sum_words, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [IsScalarTower.algebraMap_smul L]
  exact (KaehlerDifferential.D K L).toLinearMap.map_smul_of_tower
    (∏ r, c (w r)) (directionalWordDerivative δ x w)

/-- A packet chooses one ordered derivation word for every jet order from `0` through `n`. -/
abbrev DirectionalWordPacket (ι : Type*) (n : ℕ) :=
  (j : Fin (n + 1)) → (Fin (j : ℕ) → ι)

/-- Exterior coefficient attached to one packet of ordered words. -/
def directionalKaehlerWordPacketCoefficient
    (δ : ι → Derivation k L L) (x : L) (n : ℕ)
    (w : DirectionalWordPacket ι n) : ⋀[L]^(n + 1) Ω[L⁄K] :=
  exteriorPower.ιMulti L (n + 1)
    (fun j => KaehlerDifferential.D K L
      (directionalWordDerivative δ x (w j)))

omit [CharZero K] in
/-- Exact vector-valued polynomial expansion of the finite directional Kähler wedge. -/
theorem directionalKaehlerWedge_eq_sum_wordPackets
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) (n : ℕ) :
    directionalKaehlerWedge (K := K) δ c x n =
      ∑ w : DirectionalWordPacket ι n,
        algebraMap k L (∏ j, ∏ r, c (w j r)) •
          directionalKaehlerWordPacketCoefficient (K := K) δ x n w := by
  rw [directionalKaehlerWedge]
  simp_rw [show ∀ j : Fin (n + 1),
      KaehlerDifferential.D K L (directionalJet δ c j x) =
        ∑ w : Fin (j : ℕ) → ι,
          algebraMap k L (∏ r, c (w r)) •
            KaehlerDifferential.D K L (directionalWordDerivative δ x w) by
    intro j
    exact kaehlerD_directionalJet_eq_sum_words δ c x j]
  calc
    _ = ∑ w : DirectionalWordPacket ι n,
        exteriorPower.ιMulti L (n + 1) (fun j =>
          algebraMap k L (∏ r, c (w j r)) •
            KaehlerDifferential.D K L
              (directionalWordDerivative δ x (w j))) := by
          exact (exteriorPower.ιMulti L (n + 1)).map_sum
            (fun j (w : Fin (j : ℕ) → ι) =>
              algebraMap k L (∏ r, c (w r)) •
                KaehlerDifferential.D K L (directionalWordDerivative δ x w))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [(exteriorPower.ιMulti L (n + 1)).map_smul_univ]
      rw [map_prod]
      rfl

/-- A finite vector-valued homogeneous polynomial over a field is the simultaneous zero locus of
finitely many homogeneous scalar polynomials.  Only the span of its coefficient vectors is used,
so the ambient module need not be finite-dimensional. -/
theorem exists_homogeneous_coordinate_polynomials
    {F α M σ : Type*} [Field F] [Fintype α]
    [AddCommGroup M] [Module F M]
    (q : α → MvPolynomial σ F) (v : α → M) (d : ℕ)
    (hq : ∀ a, MvPolynomial.IsHomogeneous (q a) d) :
    ∃ r : ℕ, ∃ P : Fin r → MvPolynomial σ F,
      (∀ j, MvPolynomial.IsHomogeneous (P j) d) ∧
      ∀ c : σ → F,
        (∀ j, MvPolynomial.eval c (P j) = 0) ↔
          ∑ a, MvPolynomial.eval c (q a) • v a = 0 := by
  classical
  let W : Submodule F M := Submodule.span F (Set.range v)
  letI : Module.Finite F W := by
    dsimp [W]
    exact FiniteDimensional.span_of_finite F (Set.finite_range v)
  let b : Basis (Fin (Module.finrank F W)) F W := Module.finBasis F W
  let vv : α → W := fun a => ⟨v a, Submodule.subset_span ⟨a, rfl⟩⟩
  let P : Fin (Module.finrank F W) → MvPolynomial σ F := fun j =>
    ∑ a, MvPolynomial.C (b.repr (vv a) j) * q a
  have hP : ∀ j, MvPolynomial.IsHomogeneous (P j) d := by
    intro j
    dsimp [P]
    apply MvPolynomial.IsHomogeneous.sum Finset.univ
    intro a ha
    simpa using (MvPolynomial.isHomogeneous_C σ (b.repr (vv a) j)).mul (hq a)
  refine ⟨Module.finrank F W, P, hP, ?_⟩
  intro c
  let z : W := ∑ a, MvPolynomial.eval c (q a) • vv a
  constructor
  · intro h
    have hzrepr : b.repr z = 0 := by
      ext j
      have hj := h j
      simpa [P, z, mul_comm] using hj
    have hz : z = 0 := b.repr.injective (by simpa using hzrepr)
    have hcoe := congrArg Subtype.val hz
    simpa [z, vv] using hcoe
  · intro hzero j
    have hz : z = 0 := by
      apply Subtype.ext
      simpa [z, vv] using hzero
    have hcoord := congrArg (fun y => b.repr y j) hz
    simpa [P, z, mul_comm] using hcoord

/-- Scalar monomial attached to an ordered-word packet. -/
def directionalWordPacketMonomial (n : ℕ) (w : DirectionalWordPacket ι n) :
    MvPolynomial ι k :=
  ∏ j, ∏ r, MvPolynomial.X (w j r)

omit [Fintype ι] in
@[simp]
theorem eval_directionalWordPacketMonomial
    (c : ι → k) (n : ℕ) (w : DirectionalWordPacket ι n) :
    MvPolynomial.eval c (directionalWordPacketMonomial (k := k) n w) =
      ∏ j, ∏ r, c (w j r) := by
  simp [directionalWordPacketMonomial]

omit [Fintype ι] in
/-- Every packet monomial has the triangular degree `0 + 1 + ... + n`. -/
theorem directionalWordPacketMonomial_isHomogeneous
    (n : ℕ) (w : DirectionalWordPacket ι n) :
    MvPolynomial.IsHomogeneous (directionalWordPacketMonomial (k := k) n w)
      (n * (n + 1) / 2) := by
  have hinner (j : Fin (n + 1)) :
      MvPolynomial.IsHomogeneous
        (∏ r, MvPolynomial.X (w j r) : MvPolynomial ι k) (j : ℕ) := by
    have h := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun r : Fin (j : ℕ) => MvPolynomial.X (w j r)) (fun _ => 1)
      (fun r _ => MvPolynomial.isHomogeneous_X k (w j r))
    simpa using h
  have houter := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j : Fin (n + 1) =>
      (∏ r, MvPolynomial.X (w j r) : MvPolynomial ι k))
    (fun j : Fin (n + 1) => (j : ℕ)) (fun j _ => hinner j)
  have hsum : (∑ j : Fin (n + 1), (j : ℕ)) = n * (n + 1) / 2 := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1), j :=
        Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (n + 1)
      _ = (n + 1) * n / 2 := Finset.sum_range_id (n + 1)
      _ = n * (n + 1) / 2 := by rw [Nat.mul_comm (n + 1) n]
  simpa [directionalWordPacketMonomial, hsum] using houter

/-- The finite directional Kähler locus is cut out by finitely many homogeneous scalar
polynomials of the exact triangular degree. -/
theorem exists_directionalKaehlerCoordinatePolynomials
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    ∃ r : ℕ, ∃ P : Fin r → MvPolynomial ι k,
      (∀ j, MvPolynomial.IsHomogeneous (P j) (n * (n + 1) / 2)) ∧
      ∀ c : ι → k,
        (∀ j, MvPolynomial.eval c (P j) = 0) ↔
          directionalKaehlerWedge (K := K) δ c x n = 0 := by
  let M := ⋀[L]^(n + 1) Ω[L⁄K]
  letI : Module k M := Module.compHom M (algebraMap k L)
  obtain ⟨r, P, hP, hzero⟩ :=
    exists_homogeneous_coordinate_polynomials
      (fun w : DirectionalWordPacket ι n =>
        directionalWordPacketMonomial (k := k) n w)
      (fun w : DirectionalWordPacket ι n =>
        directionalKaehlerWordPacketCoefficient (K := K) δ x n w)
      (n * (n + 1) / 2)
      (fun w => directionalWordPacketMonomial_isHomogeneous (k := k) n w)
  refine ⟨r, P, hP, ?_⟩
  intro c
  rw [hzero c]
  have hexpand := directionalKaehlerWedge_eq_sum_wordPackets
    (K := K) δ c x n
  rw [hexpand]
  have hsums :
      (∑ a : DirectionalWordPacket ι n,
          MvPolynomial.eval c (directionalWordPacketMonomial (k := k) n a) •
            directionalKaehlerWordPacketCoefficient (K := K) δ x n a) =
        ∑ w : DirectionalWordPacket ι n,
          algebraMap k L (∏ j, ∏ r, c (w j r)) •
            directionalKaehlerWordPacketCoefficient (K := K) δ x n w := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [eval_directionalWordPacketMonomial]
    rfl
  rw [hsums]

/-- Homogeneous scalar equations cut out exactly the algebraically dependent finite directional
jet packet. -/
theorem exists_directionalFiniteLawPolynomials
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    ∃ r : ℕ, ∃ P : Fin r → MvPolynomial ι k,
      (∀ j, MvPolynomial.IsHomogeneous (P j) (n * (n + 1) / 2)) ∧
      ∀ c : ι → k,
        (∀ j, MvPolynomial.eval c (P j) = 0) ↔
          ¬ AlgebraicIndependent K
            (fun j : Fin (n + 1) => directionalJet δ c j x) := by
  obtain ⟨r, P, hP, hzero⟩ :=
    exists_directionalKaehlerCoordinatePolynomials (K := K) δ x n
  refine ⟨r, P, hP, ?_⟩
  intro c
  rw [hzero c]
  exact directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent δ c x n

end

end GaloisForLFunctions.HTGeometry
