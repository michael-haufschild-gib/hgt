import GaloisForLFunctions.RHTower.SuzukiStrongResolventLimit
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation

/-!
# The edge-data interface for the normalized edge quotient

Everything in the passage from the strong resolvent limit to the normalized edge quotient is
proved: the strong limit itself, its transport to pairings, the quotient of limits, and the `-i`
normalization.  What a source must still supply is a single package of data — a bounded resolvent
coordinate, the vector its family is applied to, the two vectors against which the physical
numerator and denominator are paired, and the statement that those pairings take the central-jet
values.

`SuzukiEdgeData` names that package.  Given one, the normalized edge quotient converges to the
aperture average with no further hypotheses, so the remaining debt of the construction is exactly
the exhibition of such a structure.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- The data a source must supply for the normalized edge quotient: a bounded, self-adjoint,
injective resolvent coordinate with nonnegative bounded spectrum, a vector, the two pairing
vectors, and the two central-jet value equations. -/
structure SuzukiEdgeData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] where
  /-- The bounded resolvent coordinate. -/
  B : H →L[ℂ] H
  /-- The coordinate is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint B
  /-- The coordinate is injective. -/
  injective : Function.Injective B
  /-- A spectral bound. -/
  specBound : ℝ
  /-- The spectrum is nonnegative and bounded. -/
  spectrum_subset : spectrum ℝ B ⊆ Set.Icc 0 specBound
  /-- The vector the resolvent family is applied to. -/
  v : H
  /-- The vector pairing against the physical numerator. -/
  gnum : H
  /-- The vector pairing against the physical denominator. -/
  gden : H
  /-- The aperture. -/
  aperture : ℝ
  /-- The aperture is nonzero. -/
  aperture_ne : (aperture : ℂ) ≠ 0
  /-- The edge weight `cosh a`. -/
  edgeWeight : ℂ
  /-- The edge weight is nonzero. -/
  edgeWeight_ne : edgeWeight ≠ 0
  /-- The value of the primitive at twice the aperture. -/
  primitiveValue : ℂ
  /-- The numerator pairing is the endpoint-atom central jet. -/
  num_value : inner ℂ gnum v = Complex.I * (2 * edgeWeight) * primitiveValue
  /-- The denominator pairing is the edge-pair central jet. -/
  den_value : inner ℂ gden v = 4 * (aperture : ℂ) * edgeWeight

namespace SuzukiEdgeData

variable (d : SuzukiEdgeData H) (rho : ℝ)

/-- The resolvent family of the edge data, in the bounded coordinate. -/
def family (s : ℝ) : H :=
  cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) d.B d.v

/-- **The normalized edge quotient converges to the aperture average.**  Given edge data, no
further hypothesis is needed: this is the card's passage `(2) => (7),(6) => (8) => (10)`. -/
theorem tendsto_normalizedQuotient :
    Tendsto
      (fun s : ℝ => -Complex.I *
        (inner ℂ d.gnum (d.family rho s) / inner ℂ d.gden (d.family rho s)))
      atTop (𝓝 (d.primitiveValue / (2 * (d.aperture : ℂ)))) :=
  tendsto_normalizedEdgeQuotient_of_resolventFamily d.selfAdjoint d.injective
    d.spectrum_subset d.gnum d.gden d.v d.aperture_ne d.edgeWeight_ne d.num_value d.den_value

end SuzukiEdgeData

/-! ## The interface is inhabited

An interface no object satisfies asserts nothing.  The pairing vectors can always be produced from
a nonzero vector, so the diagonal instantiation supplies edge data outright. -/

omit [CompleteSpace H] [Nontrivial H] in
/-- Any prescribed pairing value against a nonzero vector is realised by some vector. -/
theorem exists_inner_eq {v : H} (hv : v ≠ 0) (a : ℂ) : ∃ g : H, inner ℂ g v = a := by
  have hn : (‖v‖ : ℂ) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))
  refine ⟨((starRingEnd ℂ) (a / (‖v‖ : ℂ) ^ (2 : ℕ))) • v, ?_⟩
  rw [inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply,
    inner_self_eq_norm_sq_to_K]
  exact div_mul_cancel₀ a hn

theorem lpSingle_ne_zero : lp.single 2 0 (1 : ℂ) ≠ (0 : _root_.RHTower.EllTwo) := by
  intro h
  have := congrArg (fun x : _root_.RHTower.EllTwo => (x : ℕ → ℂ) 0) h
  simp [lp.single_apply] at this

/-- **The edge-data interface is inhabited.**  The harmonic diagonal operator supplies the
coordinate, and the pairing vectors are produced from any nonzero vector. -/
theorem nonempty_suzukiEdgeData : Nonempty (SuzukiEdgeData _root_.RHTower.EllTwo) := by
  obtain ⟨gnum, hgnum⟩ :=
    exists_inner_eq lpSingle_ne_zero (Complex.I * (2 * 1) * 1)
  obtain ⟨gden, hgden⟩ :=
    exists_inner_eq lpSingle_ne_zero (4 * ((1 : ℝ) : ℂ) * 1)
  exact ⟨{ B := harmonicDiagonalOperator
           selfAdjoint := isSelfAdjoint_harmonicDiagonalOperator
           injective := injective_harmonicDiagonalOperator
           specBound := ‖harmonicDiagonalOperator‖
           spectrum_subset :=
             spectrum_diagonalOperator_ofReal_subset _ norm_harmonicMultiplier_le
               harmonicMultiplier_nonneg
           v := lp.single 2 0 (1 : ℂ)
           gnum := gnum
           gden := gden
           aperture := 1
           aperture_ne := by norm_num
           edgeWeight := 1
           edgeWeight_ne := one_ne_zero
           primitiveValue := 1
           num_value := hgnum
           den_value := hgden }⟩

/-! ## What the interface does and does not constrain

The value equations are not restrictions: for any admissible coordinate and any nonzero vector, the
pairing vectors realising *any* prescribed values exist.  So the interface constrains only the
resolvent coordinate and the vector, and the entire remaining debt of the construction is the
identification of `gnum` and `gden` with the source's physical numerator and denominator
functionals — not the values they take. -/

/-- **The value equations are free.**  Any admissible coordinate, nonzero vector, aperture, edge
weight and primitive value are realised by some edge data.  Satisfying the interface is therefore
not by itself evidence of anything: only the provenance of `gnum` and `gden` carries content. -/
theorem exists_suzukiEdgeData_of_operator {B : H →L[ℂ] H} (hsa : IsSelfAdjoint B)
    (hinj : Function.Injective B) {M : ℝ} (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    {v : H} (hv : v ≠ 0) {a : ℝ} (ha : (a : ℂ) ≠ 0) {c : ℂ} (hc : c ≠ 0) (P : ℂ) :
    ∃ d : SuzukiEdgeData H,
      d.B = B ∧ d.v = v ∧ d.aperture = a ∧ d.edgeWeight = c ∧ d.primitiveValue = P := by
  obtain ⟨gnum, hgnum⟩ := exists_inner_eq hv (Complex.I * (2 * c) * P)
  obtain ⟨gden, hgden⟩ := exists_inner_eq hv (4 * (a : ℂ) * c)
  exact ⟨{ B := B
           selfAdjoint := hsa
           injective := hinj
           specBound := M
           spectrum_subset := hspec
           v := v
           gnum := gnum
           gden := gden
           aperture := a
           aperture_ne := ha
           edgeWeight := c
           edgeWeight_ne := hc
           primitiveValue := P
           num_value := hgnum
           den_value := hgden },
    rfl, rfl, rfl, rfl, rfl⟩

end GaloisForLFunctions.RHTower
