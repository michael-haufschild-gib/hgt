import GaloisForLFunctions.HyperbolicArakelovTheory.TheFullAdelicDegreeConfiguration
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Prime adjacency on the adelic carrier

At each prime, the integral-projective orbit of `diag(1,p)K_p` consists of
`p+1` distinct vertices: `diag(1,p)K_p` and `[[p,-b],[0,1]]K_p`, with `b∈𝔽_p`.
Reduction of the first column proves exhaustiveness; the quadratic entry bound
for projectively integral matrices proves distinctness. Translation gives an
invariant, symmetric, loopless local correspondence on `PGL₂(ℚ_p)/K_p`.

Replacing one finite coordinate defines a prime adjacency sum on the full
adelic product. Equivariance makes it descend to the arithmetic quotient
constructed in `FullAdelic`. The sum runs over neighbours before taking orbit
classes, retaining multiplicities when distinct neighbours become identified.
These real linear operators preserve nonnegative functions, send `1` to `p+1`,
and commute at distinct primes. Neither a target pairing nor a diagonal value
enters their construction.

This supplies the finite-place operators on the actual carrier. An analytic
domain, a global Green kernel and its diagonal regularization are not asserted.
-/

set_option autoImplicit false
noncomputable section
open Matrix Set
open scoped Classical
namespace GaloisForLFunctions.HyperbolicArakelovTheory.AdelicAdjacency
open FullAdelic
local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

variable (p : {p : ℕ // p.Prime})

private theorem prime_ne_zero : (p.1 : ℚ_[p.1]) ≠ 0 := by exact_mod_cast p.2.ne_zero

private theorem norm_prime_lt_one : ‖(p.1 : ℚ_[p.1])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

/-- Reduction detects whether division by the prime remains integral. -/
theorem residue_zero_iff_div_integral (x : ℤ_[p.1]) :
    PadicInt.toZMod x = 0 ↔ ‖(x : ℚ_[p.1]) / (p.1 : ℚ_[p.1])‖ ≤ 1 := by
  have he : PadicInt.toZMod x = 0 ↔ (p.1 : ℤ_[p.1]) ∣ x := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  rw [he]
  constructor
  · rintro ⟨y, hy⟩
    have hc := congrArg (fun z : ℤ_[p.1] => (z : ℚ_[p.1])) hy
    rw [PadicInt.coe_mul, PadicInt.coe_natCast] at hc
    rw [hc, mul_div_cancel_left₀ _ (prime_ne_zero p)]
    exact y.2
  · intro hx
    let y : ℤ_[p.1] := ⟨(x : ℚ_[p.1]) / (p.1 : ℚ_[p.1]), hx⟩
    refine ⟨y, ?_⟩
    apply PadicInt.ext
    change (x : ℚ_[p.1]) = (p.1 : ℚ_[p.1]) * ((x : ℚ_[p.1]) / (p.1 : ℚ_[p.1]))
    field_simp [prime_ne_zero p]

/-- Integral entries and a unit determinant give an integral change of basis. -/
theorem integralPGL_of_entries_det_norm (g : LocalGL p)
    (hg : ∀ i j, ‖g i j‖ ≤ 1) (hd : ‖g.val.det‖ = 1) :
    ProjGenLinGroup.mk g ∈ integralPGL p := by
  let A : Matrix (Fin 2) (Fin 2) ℤ_[p.1] := fun i j => ⟨g i j, hg i j⟩
  have hdet : IsUnit A.det := by
    apply PadicInt.isUnit_iff.mpr
    rw [PadicInt.norm_def]
    convert hd using 1
    congr 1
  refine ⟨GeneralLinearGroup.mk'' A hdet, ?_⟩
  apply congrArg ProjGenLinGroup.mk
  apply GeneralLinearGroup.ext
  intro i j
  rfl

/-- The `p+1` right-coset representatives of the prime double coset. -/
def neighborRep : Option (ZMod p.1) → LocalGL p
  | none =>
    ⟨!![1, 0; 0, (p.1 : ℚ_[p.1])], !![1, 0; 0, (p.1 : ℚ_[p.1])⁻¹],
      by ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, prime_ne_zero p],
      by ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, prime_ne_zero p]⟩
  | some b =>
    ⟨!![(p.1 : ℚ_[p.1]), -(b.val : ℚ_[p.1]); 0, 1],
      !![(p.1 : ℚ_[p.1])⁻¹, (b.val : ℚ_[p.1]) / p.1; 0, 1],
      by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, prime_ne_zero p, div_eq_mul_inv]
        field_simp [prime_ne_zero p]
        ring,
      by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, prime_ne_zero p, div_eq_mul_inv]
        ring⟩

theorem neighborRep_det (i : Option (ZMod p.1)) : (neighborRep p i).val.det = p.1 := by
  cases i <;> simp [neighborRep, Matrix.det_fin_two]

def neighbor (i : Option (ZMod p.1)) : LocalVertex p :=
  QuotientGroup.mk (ProjGenLinGroup.mk (neighborRep p i))

private def turn (b : ZMod p.1) : GL (Fin 2) ℤ_[p.1] :=
  ⟨!![-(b.val : ℤ_[p.1]), -1; 1, 0], !![0, 1; -1, -(b.val : ℤ_[p.1])],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem integral_turn_val (b : ZMod p.1) :
    (integralMap p (turn p b)).val = !![-(b.val : ℚ_[p.1]), -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change -((b.val : ℤ_[p.1]) : ℚ_[p.1]) = -(b.val : ℚ_[p.1])
    rw [PadicInt.coe_natCast]
  · rfl
  · rfl
  · rfl

private theorem integralMap_entry (h : GL (Fin 2) ℤ_[p.1]) (i j : Fin 2) :
    (integralMap p h).val i j = (h i j : ℚ_[p.1]) := rfl

private theorem turn_mul_step (b : ZMod p.1) :
    integralMap p (turn p b) * neighborRep p none =
      neighborRep p (some b) * integralMap p (turn p 0) := by
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, integral_turn_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighborRep, Matrix.mul_apply, Fin.sum_univ_two]

theorem neighbor_mem_baseOrbit (i : Option (ZMod p.1)) :
    neighbor p i ∈ MulAction.orbit (integralPGL p) (neighbor p none) := by
  cases i with
  | none => exact MulAction.mem_orbit_self _
  | some b =>
    refine ⟨⟨ProjGenLinGroup.mk (integralMap p (turn p b)), ⟨turn p b, rfl⟩⟩, ?_⟩
    change (QuotientGroup.mk (ProjGenLinGroup.mk (integralMap p (turn p b)) *
      ProjGenLinGroup.mk (neighborRep p none)) : LocalVertex p) = neighbor p (some b)
    rw [← map_mul, turn_mul_step, map_mul]
    apply QuotientGroup.eq.mpr
    rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact (integralPGL p).inv_mem ⟨turn p 0, rfl⟩

private theorem transition_det_norm (h : GL (Fin 2) ℤ_[p.1]) (i : Option (ZMod p.1)) :
    ‖((neighborRep p i)⁻¹ * integralMap p h * neighborRep p none).val.det‖ = 1 := by
  have hp0 := prime_ne_zero p
  have he : ((neighborRep p i)⁻¹ * integralMap p h * neighborRep p none).val.det =
      (integralMap p h).val.det := by
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, Matrix.det_mul,
      Matrix.det_mul, GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv, neighborRep_det, neighborRep_det]
    field_simp
  rw [he, integralMap_det_norm]

private theorem transition_none_val (h : GL (Fin 2) ℤ_[p.1]) :
    ((neighborRep p none)⁻¹ * integralMap p h * neighborRep p none).val =
      !![(h 0 0 : ℚ_[p.1]), (h 0 1 : ℚ_[p.1]) * p.1;
         (h 1 0 : ℚ_[p.1]) / p.1, (h 1 1 : ℚ_[p.1])] := by
  change !![1, 0; 0, (p.1 : ℚ_[p.1])⁻¹] *
    (integralMap p h).val * !![1, 0; 0, (p.1 : ℚ_[p.1])] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      integralMap_entry, div_eq_mul_inv, mul_comm, prime_ne_zero p]

private theorem transition_some_val (h : GL (Fin 2) ℤ_[p.1]) (b : ZMod p.1) :
    ((neighborRep p (some b))⁻¹ * integralMap p h * neighborRep p none).val =
      !![((h 0 0 : ℚ_[p.1]) + (b.val : ℚ_[p.1]) * (h 1 0 : ℚ_[p.1])) / p.1,
          (h 0 1 : ℚ_[p.1]) + (b.val : ℚ_[p.1]) * (h 1 1 : ℚ_[p.1]);
         (h 1 0 : ℚ_[p.1]), (h 1 1 : ℚ_[p.1]) * p.1] := by
  change !![(p.1 : ℚ_[p.1])⁻¹, (b.val : ℚ_[p.1]) / p.1; 0, 1] *
    (integralMap p h).val * !![1, 0; 0, (p.1 : ℚ_[p.1])] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, integralMap_entry] <;>
      field_simp [prime_ne_zero p]

/-- Reduction of the first column identifies its unique neighbour class. -/
theorem integral_moves_step_to_neighbor (h : GL (Fin 2) ℤ_[p.1]) :
    ∃ i : Option (ZMod p.1),
      ProjGenLinGroup.mk (integralMap p h) • neighbor p none = neighbor p i := by
  by_cases hc : PadicInt.toZMod (h 1 0) = 0
  · refine ⟨none, ?_⟩
    have hint : ProjGenLinGroup.mk
        ((neighborRep p none)⁻¹ * integralMap p h * neighborRep p none) ∈ integralPGL p := by
      apply integralPGL_of_entries_det_norm p _ _ (transition_det_norm p h none)
      intro i j
      rw [transition_none_val]
      fin_cases i <;> fin_cases j
      · exact (h 0 0).2
      · change ‖(h 0 1 : ℚ_[p.1]) * p.1‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ (h 0 1).2 (norm_nonneg _) (norm_prime_lt_one p).le
      · exact (residue_zero_iff_div_integral p (h 1 0)).mp hc
      · exact (h 1 1).2
    symm
    apply QuotientGroup.eq.mpr
    simpa only [map_mul, map_inv, smul_eq_mul, mul_assoc] using hint
  · let b : ZMod p.1 := -PadicInt.toZMod (h 0 0) / PadicInt.toZMod (h 1 0)
    have hzero : PadicInt.toZMod (h 0 0 + (b.val : ℤ_[p.1]) * h 1 0) = 0 := by
      rw [map_add, map_mul, map_natCast, ZMod.natCast_zmod_val]
      dsimp only [b]
      rw [div_mul_cancel₀ _ hc, add_neg_cancel]
    have hdiv := (residue_zero_iff_div_integral p _).mp hzero
    refine ⟨some b, ?_⟩
    have hint : ProjGenLinGroup.mk
        ((neighborRep p (some b))⁻¹ * integralMap p h * neighborRep p none) ∈ integralPGL p := by
      apply integralPGL_of_entries_det_norm p _ _ (transition_det_norm p h (some b))
      intro i j
      rw [transition_some_val]
      fin_cases i <;> fin_cases j
      · change ‖((h 0 0 : ℚ_[p.1]) + (b.val : ℚ_[p.1]) * (h 1 0 : ℚ_[p.1])) / p.1‖ ≤ 1
        simpa only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_natCast] using hdiv
      · exact (show ‖((h 0 1 + (b.val : ℤ_[p.1]) * h 1 1 : ℤ_[p.1]) : ℚ_[p.1])‖ ≤ 1 from
          (h 0 1 + (b.val : ℤ_[p.1]) * h 1 1).2)
      · exact (h 1 0).2
      · change ‖(h 1 1 : ℚ_[p.1]) * p.1‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ (h 1 1).2 (norm_nonneg _) (norm_prime_lt_one p).le
    symm
    apply QuotientGroup.eq.mpr
    simpa only [map_mul, map_inv, smul_eq_mul, mul_assoc] using hint


private theorem norm_entry_le_one_of_projective (g : LocalGL p)
    (hg : ProjGenLinGroup.mk g ∈ integralPGL p) (hd : ‖g.val.det‖ = 1) (i j : Fin 2) :
    ‖g i j‖ ≤ 1 := by
  have h := quadratic_entry_bound p g hg i j
  rw [hd] at h
  nlinarith only [h, norm_nonneg (g i j)]

private theorem relative_det_norm (i j : Option (ZMod p.1)) :
    ‖((neighborRep p i)⁻¹ * neighborRep p j).val.det‖ = 1 := by
  rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, GeneralLinearGroup.coe_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, neighborRep_det, neighborRep_det,
    inv_mul_cancel₀ (prime_ne_zero p), norm_one]

theorem neighbor_injective : Function.Injective (neighbor p) := by
  intro i j hij
  have hmem : ProjGenLinGroup.mk ((neighborRep p i)⁻¹ * neighborRep p j) ∈ integralPGL p := by
    simpa only [map_mul, map_inv] using QuotientGroup.eq.mp hij
  have hb := norm_entry_le_one_of_projective p _ hmem (relative_det_norm p i j)
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b =>
      have h := hb 1 1
      change ‖((neighborRep p none).inv * (neighborRep p (some b)).val) 1 1‖ ≤ 1 at h
      simp [neighborRep, Matrix.mul_apply, Fin.sum_univ_two] at h
      exact False.elim ((not_le_of_gt p.2.one_lt) h)
  | some b =>
    cases j with
    | none =>
      have h := hb 0 0
      change ‖((neighborRep p (some b)).inv * (neighborRep p none).val) 0 0‖ ≤ 1 at h
      simp [neighborRep, Matrix.mul_apply, Fin.sum_univ_two] at h
      exact False.elim ((not_le_of_gt p.2.one_lt) h)
    | some c =>
      have h := hb 0 1
      have hdiv : ‖(((b.val : ℤ_[p.1]) - c.val : ℤ_[p.1]) : ℚ_[p.1]) /
          (p.1 : ℚ_[p.1])‖ ≤ 1 := by
        change ‖((neighborRep p (some b)).inv * (neighborRep p (some c)).val) 0 1‖ ≤ 1 at h
        simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
        change ‖(p.1 : ℚ_[p.1])⁻¹ * -(c.val : ℚ_[p.1]) +
          (b.val : ℚ_[p.1]) / p.1 * 1‖ ≤ 1 at h
        have he : (p.1 : ℚ_[p.1])⁻¹ * -(c.val : ℚ_[p.1]) +
            (b.val : ℚ_[p.1]) / p.1 * 1 =
            ((b.val : ℚ_[p.1]) - c.val) / p.1 := by ring
        rw [he] at h
        simpa only [PadicInt.coe_sub, PadicInt.coe_natCast] using h
      have hz := (residue_zero_iff_div_integral p _).mpr hdiv
      rw [map_sub, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hz
      exact congrArg some (sub_eq_zero.mp hz)

theorem baseOrbit_eq_range :
    MulAction.orbit (integralPGL p) (neighbor p none) = Set.range (neighbor p) := by
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨h, hh⟩ := k.property
    obtain ⟨i, hi⟩ := integral_moves_step_to_neighbor p h
    refine ⟨i, ?_⟩
    change neighbor p i = (k : LocalPGL p) • neighbor p none
    rw [← hh]
    exact hi.symm
  · rintro ⟨i, rfl⟩
    exact neighbor_mem_baseOrbit p i

private theorem fixes_base_iff (g : LocalPGL p) :
    g • baseVertex p = baseVertex p ↔ g ∈ integralPGL p := by
  change (QuotientGroup.mk (g * 1) : LocalVertex p) = QuotientGroup.mk 1 ↔ _
  rw [mul_one, QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff]

/-- Neighbours are translates of the standard lattice inclusion of index `p`. -/
def Adjacent (v w : LocalVertex p) : Prop :=
  ∃ g : LocalPGL p, g • baseVertex p = v ∧ g • neighbor p none = w

theorem adjacent_smul_iff (g : LocalPGL p) (v w : LocalVertex p) :
    Adjacent p (g • v) (g • w) ↔ Adjacent p v w := by
  constructor
  · rintro ⟨h, hv, hw⟩
    refine ⟨g⁻¹ * h, ?_, ?_⟩
    · rw [mul_smul, hv, inv_smul_smul]
    · rw [mul_smul, hw, inv_smul_smul]
  · rintro ⟨h, hv, hw⟩
    exact ⟨g * h, by rw [mul_smul, hv], by rw [mul_smul, hw]⟩

theorem adjacent_base_iff (v : LocalVertex p) :
    Adjacent p (baseVertex p) v ↔ v ∈ Set.range (neighbor p) := by
  rw [← baseOrbit_eq_range]
  constructor
  · rintro ⟨g, hg, hv⟩
    exact ⟨⟨g, (fixes_base_iff p g).mp hg⟩, hv⟩
  · rintro ⟨g, hv⟩
    exact ⟨g, (fixes_base_iff p g).mpr g.property, hv⟩

private theorem exists_frame (v : LocalVertex p) : ∃ g : LocalPGL p, g • baseVertex p = v := by
  induction v using Quotient.inductionOn with
  | h g =>
    refine ⟨g, ?_⟩
    change (QuotientGroup.mk (g * 1) : LocalVertex p) = QuotientGroup.mk g
    rw [mul_one]

private def frame (v : LocalVertex p) : LocalPGL p := Classical.choose (exists_frame p v)

private theorem frame_spec (v : LocalVertex p) : frame p v • baseVertex p = v :=
  Classical.choose_spec (exists_frame p v)

/-- The finite neighbour set is independent of the chosen lattice frame. -/
def neighbors (v : LocalVertex p) : Finset (LocalVertex p) := by
  classical
  exact Finset.univ.image (fun i : Option (ZMod p.1) => frame p v • neighbor p i)

theorem mem_neighbors (v w : LocalVertex p) : w ∈ neighbors p v ↔ Adjacent p v w := by
  classical
  constructor
  · intro hw
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hw
    have hh := (adjacent_smul_iff p (frame p v) (baseVertex p) (neighbor p i)).mpr
      ((adjacent_base_iff p _).mpr ⟨i, rfl⟩)
    rwa [frame_spec, hi] at hh
  · intro hw
    have h : Adjacent p (baseVertex p) ((frame p v)⁻¹ • w) := by
      have hh := (adjacent_smul_iff p (frame p v)⁻¹ v w).mpr hw
      have he : (frame p v)⁻¹ • v = baseVertex p := by
        exact (congrArg (fun u => (frame p v)⁻¹ • u) (frame_spec p v)).symm.trans
          (inv_smul_smul (frame p v) (baseVertex p))
      rwa [he] at hh
    obtain ⟨i, hi⟩ := (adjacent_base_iff p _).mp h
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ _, by rw [hi, smul_inv_smul]⟩

/-- Every local vertex has exactly `p+1` distinct neighbours. -/
theorem card_neighbors (v : LocalVertex p) : (neighbors p v).card = p.1 + 1 := by
  classical
  have hi : Function.Injective (fun i : Option (ZMod p.1) => frame p v • neighbor p i) :=
    (MulAction.injective (frame p v)).comp (neighbor_injective p)
  rw [neighbors, Finset.card_image_of_injective _ hi]
  simp

theorem neighbors_smul (g : LocalPGL p) (v : LocalVertex p) :
    neighbors p (g • v) = (neighbors p v).image (fun w => g • w) := by
  classical
  ext w
  rw [mem_neighbors]
  constructor
  · intro h
    refine Finset.mem_image.mpr ⟨g⁻¹ • w, (mem_neighbors p _ _).mpr ?_, ?_⟩
    · have hh := (adjacent_smul_iff p g⁻¹ (g • v) w).mpr h
      simpa only [inv_smul_smul] using hh
    · exact smul_inv_smul g w
  · rintro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact (adjacent_smul_iff p g v u).mpr ((mem_neighbors p _ _).mp hu)


private theorem step_ne_base : neighbor p none ≠ baseVertex p := by
  intro h
  have hm : ProjGenLinGroup.mk (neighborRep p none) ∈ integralPGL p := by
    have hh := QuotientGroup.eq.mp h
    exact (integralPGL p).inv_mem_iff.mp (by simpa only [mul_one] using hh)
  have hb := quadratic_entry_bound p (neighborRep p none) hm 0 0
  have hlt := norm_prime_lt_one p
  rw [neighborRep_det] at hb
  have hentry : neighborRep p none 0 0 = 1 := rfl
  rw [hentry, norm_one, one_pow] at hb
  exact (not_le_of_gt hlt) hb

private theorem flip_step :
    ProjGenLinGroup.mk (neighborRep p none * integralMap p (turn p 0) * neighborRep p none) =
      ProjGenLinGroup.mk (integralMap p (turn p 0)) := by
  symm
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (p.1 : ℚ_[p.1]) (prime_ne_zero p), ?_⟩
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, integral_turn_val, GeneralLinearGroup.coe_scalar]
  rw [Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neighborRep, Matrix.mul_apply, Fin.sum_univ_two]

/-- The prime lattice correspondence is undirected. -/
theorem adjacent_symm (v w : LocalVertex p) : Adjacent p v w → Adjacent p w v := by
  rintro ⟨g, hg, hw⟩
  let s := ProjGenLinGroup.mk (neighborRep p none * integralMap p (turn p 0))
  have hsbase : s • baseVertex p = neighbor p none := by
    change (QuotientGroup.mk (s * 1) : LocalVertex p) = _
    rw [mul_one]
    apply QuotientGroup.eq.mpr
    dsimp only [s]
    rw [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact (integralPGL p).inv_mem ⟨turn p 0, rfl⟩
  have hsstep : s • neighbor p none = baseVertex p := by
    change (QuotientGroup.mk (s * ProjGenLinGroup.mk (neighborRep p none)) : LocalVertex p) = _
    dsimp only [s]
    rw [← map_mul, flip_step]
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using (integralPGL p).inv_mem (show
      ProjGenLinGroup.mk (integralMap p (turn p 0)) ∈ integralPGL p from ⟨turn p 0, rfl⟩)
  exact ⟨g * s, by rw [mul_smul, hsbase, hw], by rw [mul_smul, hsstep, hg]⟩

theorem not_adjacent_self (v : LocalVertex p) : ¬Adjacent p v v := by
  rintro ⟨g, hg, hw⟩
  exact step_ne_base p ((MulAction.injective g) (hw.trans hg.symm))


/-- Replace one local lattice class, preserving finite support. -/
def replaceVertex (v : FiniteVertices) (w : LocalVertex p) : FiniteVertices := by
  classical
  refine ⟨Function.update v.1 p w, ?_⟩
  apply (v.2.insert p).subset
  intro q hq
  by_cases h : q = p
  · exact Or.inl h
  · exact Set.mem_insert_of_mem _ (by simpa [Function.update_of_ne h] using hq)

@[simp] theorem replaceVertex_at (v : FiniteVertices) (w : LocalVertex p) :
    (replaceVertex p v w).1 p = w := by
  classical
  simp [replaceVertex]

theorem replaceVertex_away (v : FiniteVertices) (w : LocalVertex p)
    (q : {p : ℕ // p.Prime}) (h : q ≠ p) :
    (replaceVertex p v w).1 q = v.1 q := by
  classical
  simp [replaceVertex, h]

theorem replaceVertex_injective (v : FiniteVertices) :
    Function.Injective (replaceVertex p v) := by
  intro w z h
  have he := congrArg (fun u : FiniteVertices => u.1 p) h
  simpa only [replaceVertex_at] using he

theorem smul_replaceVertex (a : FiniteAdelicGroup) (v : FiniteVertices) (w : LocalVertex p) :
    a • replaceVertex p v w = replaceVertex p (a • v) (a p • w) := by
  classical
  apply Subtype.ext
  funext q
  by_cases h : q = p
  · subst q
    change a p • (replaceVertex p v w).1 p = _
    simp only [replaceVertex_at]
  · change a q • (replaceVertex p v w).1 q = _
    rw [replaceVertex_away p v w q h, replaceVertex_away p (a • v) (a p • w) q h]
    rfl

def replacePoint (x : GlobalSpace) (w : LocalVertex p) : GlobalSpace :=
  (x.1, replaceVertex p x.2 w)

theorem smul_replacePoint (a : AdelicGroup) (x : GlobalSpace) (w : LocalVertex p) :
    a • replacePoint p x w = replacePoint p (a • x) (a.2 p • w) := by
  apply Prod.ext
  · rfl
  · exact smul_replaceVertex p a.2 x.2 w

/-- The local adjacency sum on the full adelic product. -/
def adjacencySum (F : GlobalSpace → ℝ) (x : GlobalSpace) : ℝ :=
  ∑ w ∈ neighbors p (x.2.1 p), F (replacePoint p x w)

/-- Local adjacency is equivariant under the actual adelic action. -/
theorem adjacencySum_smul (a : AdelicGroup) (F : GlobalSpace → ℝ) (x : GlobalSpace) :
    adjacencySum p F (a • x) = adjacencySum p (fun y => F (a • y)) x := by
  classical
  change (∑ w ∈ neighbors p (a.2 p • x.2.1 p), F (replacePoint p (a • x) w)) = _
  rw [neighbors_smul, Finset.sum_image (MulAction.injective (a.2 p)).injOn]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← smul_replacePoint]

/-- The orbit map to the arithmetic adelic carrier. -/
def carrierClass (x : GlobalSpace) : ConjugateCarrier := Quotient.mk _ x

theorem carrierClass_smul (g : conjugateArithmeticGroup) (x : GlobalSpace) :
    carrierClass (g • x) = carrierClass x := by
  apply Quotient.sound
  exact ⟨g, rfl⟩

/-- Hecke adjacency retains multiplicities by summing before taking orbit classes. -/
def primeOperator (F : ConjugateCarrier → ℝ) : ConjugateCarrier → ℝ :=
  Quotient.lift (adjacencySum p (F ∘ carrierClass)) (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    change adjacencySum p (F ∘ carrierClass) ((g : AdelicGroup) • y) = _
    rw [adjacencySum_smul]
    apply Finset.sum_congr rfl
    intro w hw
    exact congrArg F (carrierClass_smul g (replacePoint p y w)))

theorem primeOperator_apply (F : ConjugateCarrier → ℝ) (x : GlobalSpace) :
    primeOperator p F (carrierClass x) =
      ∑ w ∈ neighbors p (x.2.1 p), F (carrierClass (replacePoint p x w)) := rfl

/-- The unnormalised prime operator has the geometric valency `p+1`. -/
theorem primeOperator_one : primeOperator p (fun _ => 1) = fun _ => (p.1 + 1 : ℝ) := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    change (∑ w ∈ neighbors p (x.2.1 p), (1 : ℝ)) = _
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_neighbors, Nat.cast_add, Nat.cast_one]

/-- Prime adjacency as a real linear operator on functions on the carrier. -/
def primeLinearOperator : (ConjugateCarrier → ℝ) →ₗ[ℝ] (ConjugateCarrier → ℝ) where
  toFun := primeOperator p
  map_add' F G := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact Finset.sum_add_distrib
  map_smul' c F := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact (Finset.mul_sum _ _ _).symm

theorem primeOperator_nonneg (F : ConjugateCarrier → ℝ) (hF : ∀ q, 0 ≤ F q)
    (q : ConjugateCarrier) : 0 ≤ primeOperator p F q := by
  induction q using Quotient.inductionOn with
  | h x => exact Finset.sum_nonneg (fun w _ => hF (carrierClass (replacePoint p x w)))


/-- Changes at distinct finite places commute on the full adelic product. -/
theorem replacePoint_comm (q : {p : ℕ // p.Prime}) (hpq : p ≠ q)
    (x : GlobalSpace) (w : LocalVertex p) (z : LocalVertex q) :
    replacePoint q (replacePoint p x w) z = replacePoint p (replacePoint q x z) w := by
  classical
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact Function.update_comm hpq w z x.2.1

/-- Independent local adjacency sums commute before quotienting. -/
theorem adjacencySum_comm (q : {p : ℕ // p.Prime}) (hpq : p ≠ q)
    (F : GlobalSpace → ℝ) (x : GlobalSpace) :
    adjacencySum p (adjacencySum q F) x = adjacencySum q (adjacencySum p F) x := by
  classical
  unfold adjacencySum
  have heq (w : LocalVertex p) : (replacePoint p x w).2.1 q = x.2.1 q :=
    replaceVertex_away p x.2 w q hpq.symm
  have hep (z : LocalVertex q) : (replacePoint q x z).2.1 p = x.2.1 p :=
    replaceVertex_away q x.2 z p hpq
  simp only [heq, hep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  rw [replacePoint_comm p q hpq]

/-- Prime Hecke operators commute on the actual arithmetic quotient. -/
theorem primeOperator_comm (q : {p : ℕ // p.Prime}) (F : ConjugateCarrier → ℝ) :
    primeOperator p (primeOperator q F) = primeOperator q (primeOperator p F) := by
  by_cases hpq : p = q
  · subst q; rfl
  funext c
  induction c using Quotient.inductionOn with
  | h x => exact adjacencySum_comm p q hpq (F ∘ carrierClass) x


#print axioms card_neighbors
#print axioms neighbors_smul
#print axioms adjacent_symm
#print axioms not_adjacent_self
#print axioms primeOperator
#print axioms primeOperator_one
#print axioms primeLinearOperator
#print axioms primeOperator_comm
#print axioms primeOperator_nonneg

end GaloisForLFunctions.HyperbolicArakelovTheory.AdelicAdjacency
