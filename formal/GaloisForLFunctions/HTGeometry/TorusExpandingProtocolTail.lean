import GaloisForLFunctions.HTGeometry.TorusProtocol
import GaloisForLFunctions.HTGeometry.TorusInvariantField
import GaloisForLFunctions.HTGeometry.TorusVelocityIndependence
import GaloisForLFunctions.HTGeometry.MultiplicativeProtocolAlgClosed

/-!
# The purely expanding torus protocol keeps only the velocity

A scalar torus protocol raises every coordinate of the palette to a power at each phase.  Its deck
group at depth `n` is the group of `N`-th roots of unity in every coordinate, `N` the accumulated
exponent, and the accumulated exponents grow without bound.  Roots of unity of unbounded order
separate the characters of any two distinct exponent vectors, so the scaling invariants collapse to
the velocity field: the whole reversible position is erased and only the Maurer--Cartan velocity
survives.

Together with the differential independence of the velocity coordinates and the triviality of the
intersection of the velocity field with the rational function field of the palette, this is the
rank-`r` form of the position/velocity splitting for a degree-expanding protocol.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Scalar

variable {r : ℕ}

/-- The exponent accumulated by the first `n` steps of a scalar torus protocol from phase `i`. -/
def scalarPrefixExponent (K : ℕ → ℕ) (i n : ℕ) : ℕ := ∏ t ∈ Finset.range n, K (i + t)

@[simp] theorem scalarPrefixExponent_zero (K : ℕ → ℕ) (i : ℕ) :
    scalarPrefixExponent K i 0 = 1 := by
  rw [scalarPrefixExponent, Finset.range_zero, Finset.prod_empty]

theorem scalarPrefixExponent_succ (K : ℕ → ℕ) (i n : ℕ) :
    scalarPrefixExponent K i (n + 1) = scalarPrefixExponent K (i + 1) n * K i := by
  have h1 : (∏ t ∈ Finset.range n, K (i + (t + 1))) = scalarPrefixExponent K (i + 1) n :=
    Finset.prod_congr rfl fun t _ ↦ by rw [show i + (t + 1) = i + 1 + t by omega]
  show (∏ t ∈ Finset.range (n + 1), K (i + t)) = _
  rw [Finset.prod_range_succ', h1]
  simp

/-- The scalar torus protocol raises every coordinate to a power. -/
def scalarStepMatrix (r : ℕ) (K : ℕ → ℕ) (j : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.diagonal fun _ ↦ ((K j : ℤ))

theorem scalarStep_ne_zero {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (j : ℕ) : K j ≠ 0 := by
  have := hK j
  omega

theorem det_scalarStepMatrix_ne_zero {K : ℕ → ℕ} (hK : ∀ j, K j ≠ 0) (j : ℕ) :
    (scalarStepMatrix r K j).det ≠ 0 := by
  rw [scalarStepMatrix, Matrix.det_diagonal, Finset.prod_const]
  exact pow_ne_zero _ (Int.natCast_ne_zero.mpr (hK j))

/-- The accumulated matrix of a scalar protocol is the accumulated exponent. -/
theorem prefixMatrix_scalarStepMatrix (K : ℕ → ℕ) (i n : ℕ) :
    prefixMatrix (scalarStepMatrix r K) i n
      = Matrix.diagonal fun _ ↦ ((scalarPrefixExponent K i n : ℤ)) := by
  induction n generalizing i with
  | zero =>
      rw [prefixMatrix_zero, scalarPrefixExponent_zero]
      simp
  | succ n ih =>
      rw [prefixMatrix_succ, ih (i + 1), scalarStepMatrix, Matrix.diagonal_mul_diagonal,
        scalarPrefixExponent_succ, Nat.cast_mul]

/-- The accumulated exponents of a degree-expanding scalar protocol grow at least geometrically. -/
theorem two_pow_le_scalarPrefixExponent {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i n : ℕ) :
    2 ^ n ≤ scalarPrefixExponent K i n := by
  induction n generalizing i with
  | zero => rw [scalarPrefixExponent_zero, pow_zero]
  | succ n ih =>
      rw [scalarPrefixExponent_succ, pow_succ]
      exact Nat.mul_le_mul (ih (i + 1)) (hK i)

theorem exists_scalarPrefixExponent_gt {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i B : ℕ) :
    ∃ n, B < scalarPrefixExponent K i n :=
  ⟨B, lt_of_lt_of_le (Nat.lt_two_pow_self) (two_pow_le_scalarPrefixExponent hK i B)⟩

end Scalar

section Separation

variable {C : Type u} [Field C] [IsAlgClosed C] [CharZero C] {r : ℕ}

/-- **A degree-expanding scalar protocol separates exponent vectors.**  The deck group at depth `n`
contains the `N`-th roots of unity in every coordinate for the accumulated exponent `N`, and those
exponents are unbounded, so two exponent vectors with the same character on the whole erased sector
are equal. -/
theorem scalarProtocol_separates [TopologicalSpace (Fin r → Cˣ)]
    [IsTopologicalGroup (Fin r → Cˣ)] [DiscreteTopology (Fin r → Cˣ)]
    {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i : ℕ) (e d : Fin r →₀ ℕ)
    (h : ∀ u ∈ erasedClosure (torusProtocolGroup C (scalarStepMatrix r K)) i,
      (∏ k, ((u k : C)) ^ e k) = ∏ k, ((u k : C)) ^ d k) :
    e = d := by
  classical
  ext k
  by_contra hk
  obtain ⟨n, hn⟩ := exists_scalarPrefixExponent_gt hK i (max (e k) (d k))
  set N : ℕ := scalarPrefixExponent K i n with hN
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hn
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosed C hNpos
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hNpos.ne'
  set u : Fin r → Cˣ := fun l ↦ if l = k then Units.mk0 ζ hζ0 else 1 with hu
  have hmemker : u ∈ (torusPowerHom C (fun _ : Fin r ↦ ((N : ℤ)))).ker := by
    rw [mem_ker_torusPowerHom_iff]
    intro l
    by_cases hl : l = k
    · apply Units.ext
      simp only [hu, if_pos hl, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one]
      rw [zpow_natCast]
      exact hζ.pow_eq_one
    · simp [hu, if_neg hl]
  have hmem : u ∈ erasedClosure (torusProtocolGroup C (scalarStepMatrix r K)) i := by
    refine Subgroup.le_topologicalClosure _ ?_
    rw [mem_erasedSector_iff]
    refine ⟨n, ?_⟩
    rw [prefixHom_torusProtocolGroup, prefixMatrix_scalarStepMatrix, torusMonomialHom_diagonal]
    exact hmemker
  have hval := h u hmem
  have hprod : ∀ g : Fin r →₀ ℕ, (∏ l, ((u l : C)) ^ g l) = ζ ^ g k := by
    intro g
    rw [Finset.prod_eq_single k]
    · simp only [hu, if_pos rfl, Units.val_mk0]
    · intro l _ hlk
      simp only [hu, if_neg hlk, Units.val_one, one_pow]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  rw [hprod e, hprod d] at hval
  exact hk (hζ.pow_inj (lt_of_le_of_lt (le_max_left _ _) hn)
    (lt_of_le_of_lt (le_max_right _ _) hn) hval)

end Separation

section Tail

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **The purely expanding torus protocol: only the velocity survives.**  The phase tail of a
degree-expanding scalar torus protocol is exactly the differential field generated by the
logarithmic derivatives of the palette. -/
theorem scalarTorusProtocol_nonautonomousTail_eq_torusVelocityField
    [TopologicalSpace (Fin r → Cˣ)] [IsTopologicalGroup (Fin r → Cˣ)]
    [DiscreteTopology (Fin r → Cˣ)]
    (hconst : ∀ c : C, c′ = 0) {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i : ℕ) :
    nonautonomousTail
        (torusProtocol hx hgen (scalarStepMatrix r K)
          (det_scalarStepMatrix_ne_zero (scalarStep_ne_zero hK))) i
      = torusVelocityField C x := by
  rw [torusProtocol_nonautonomousTail_eq_fixedField hx hgen (scalarStepMatrix r K)
    (det_scalarStepMatrix_ne_zero (scalarStep_ne_zero hK)) i]
  exact fixedField_torusScaleRep_eq_torusVelocityField hx hgen hconst _
    fun e d hed ↦ scalarProtocol_separates hK i e d hed

include hx hgen in
/-- **The rank-`r` position/velocity theorem for a degree-expanding scalar torus protocol.**  The
tail is the velocity field, its differential transcendence degree is the dimension `r` of the torus,
and it meets the rational function field of the position in the constants only. -/
theorem scalarTorusProtocol_velocity_only
    [TopologicalSpace (Fin r → Cˣ)] [IsTopologicalGroup (Fin r → Cˣ)]
    [DiscreteTopology (Fin r → Cˣ)]
    (hconst : ∀ c : C, c′ = 0) {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i : ℕ) :
    nonautonomousTail
        (torusProtocol hx hgen (scalarStepMatrix r K)
          (det_scalarStepMatrix_ne_zero (scalarStep_ne_zero hK))) i
        = torusVelocityField C x
      ∧ DifferentialIndependent C (fun k ↦ Differential.logDeriv (x k))
      ∧ torusVelocityField C x ⊓ IntermediateField.adjoin C (Set.range x)
          = (⊥ : IntermediateField C E) :=
  ⟨scalarTorusProtocol_nonautonomousTail_eq_torusVelocityField hx hgen hconst hK i,
    differentialIndependent_logDeriv hx,
    torusVelocityField_inf_adjoin_eq_bot hx hgen hconst⟩

end Tail

end

end GaloisForLFunctions.HTGeometry
