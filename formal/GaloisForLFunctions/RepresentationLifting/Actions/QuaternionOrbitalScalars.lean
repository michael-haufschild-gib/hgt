import GaloisForLFunctions.HTGeometry.StokesResistance.SerreQ8GaloisApplication

/-!
# Orbital operators for the quaternionic Artin representation

The finite counting-measure analogue of Braverman–Kazhdan, Lemma 5.3
(arXiv:2610.17317), averages the conjugates of a group element. Its
scalar on the two-dimensional quaternionic carrier is its character
divided by two. More generally the conjugation average of any operator
is its half-trace. These formulas apply to the actual Serre Galois group.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open RHTower HTGeometry.StokesResistance
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- Pushforward of normalized group counting measure to the conjugates of an endomorphism. -/
abbrev orbitalAverage (ρ : Representation ℂ G V) : Module.End ℂ (Module.End ℂ V) :=
  finiteGroupAverage (Representation.linHom ρ ρ)

/-- Every orbital average commutes with the representation. -/
theorem orbitalAverage_commutes (ρ : Representation ℂ G V) (A : Module.End ℂ V) (g : G) :
    ρ g * orbitalAverage ρ A = orbitalAverage ρ A * ρ g := by
  have h := (finiteGroupAverage_mem_invariants (Representation.linHom ρ ρ) A) g
  change ρ g * orbitalAverage ρ A * ρ g⁻¹ = orbitalAverage ρ A at h
  have he := congrArg (fun Z : Module.End ℂ V => Z * ρ g) h
  simpa only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] using he

/-- Orbital averaging preserves the trace of every endomorphism, including singular ones. -/
theorem orbitalAverage_trace (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (orbitalAverage ρ A) = LinearMap.trace ℂ V A := by
  have ht (g : G) : LinearMap.trace ℂ V (Representation.linHom ρ ρ g A) =
      LinearMap.trace ℂ V A := by
    change LinearMap.trace ℂ V (ρ g * A * ρ g⁻¹) = _
    rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [orbitalAverage, finiteGroupAverage_apply, map_smul, map_sum]
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul,
    inv_mul_cancel_left₀ hn]

/-- The orbital operator at a group element is literally the normalized sum of its conjugates. -/
theorem orbitalAverage_group_element (ρ : Representation ℂ G V) (y : G) :
    orbitalAverage ρ (ρ y) =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ (g*y*g⁻¹) := by
  rw [orbitalAverage, finiteGroupAverage_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  change ρ g * ρ y * ρ g⁻¹ = _
  rw [map_mul, map_mul]

private theorem half_trace_of_scalar (A : Module.End ℂ Q8Carrier) (c : ℂ)
    (hc : ∀ v, A v = c • v) : A = (LinearMap.trace ℂ Q8Carrier A / 2) • 1 := by
  have he : A = c • 1 := LinearMap.ext hc
  rw [he, map_smul, LinearMap.trace_one]
  norm_num [Q8Carrier, Module.finrank_prod, smul_eq_mul]

/-- The literal quaternionic operator orbit has barycenter equal to half its trace times the identity. -/
theorem quaternionOrbitalAverage (A : Module.End ℂ Q8Carrier) :
    orbitalAverage deningerQ8Representation A = (LinearMap.trace ℂ Q8Carrier A / 2) • 1 := by
  obtain ⟨c,hc⟩ := deningerQ8_schur _ (orbitalAverage_commutes deningerQ8Representation A)
  simpa only [orbitalAverage_trace] using half_trace_of_scalar _ c hc

local notation "K3" => SerreQ8TopField
local instance : Fintype Gal(K3/ℚ) := Fintype.ofEquiv _ serreQ8_galoisEquivQ8.toEquiv.symm

/-- The same half-trace projection holds on the degree-eight Serre Galois field itself. -/
theorem serreGaloisOrbitalAverage (A : Module.End ℂ Q8Carrier) :
    orbitalAverage serreQ8ArtinRepresentation A = (LinearMap.trace ℂ Q8Carrier A / 2) • 1 := by
  obtain ⟨c,hc⟩ := serreQ8Artin_schur _ (orbitalAverage_commutes serreQ8ArtinRepresentation A)
  simpa only [orbitalAverage_trace] using half_trace_of_scalar _ c hc

/-- The eigenvalue of each normalized Galois orbital measure is the normalized Artin character. -/
theorem serreGalois_orbital_character (y : Gal(K3/ℚ)) :
    (Fintype.card Gal(K3/ℚ) : ℂ)⁻¹ • ∑ g : Gal(K3/ℚ), serreQ8ArtinRepresentation (g*y*g⁻¹) =
      (serreQ8ArtinRepresentation.character y / 2) • (1 : Module.End ℂ Q8Carrier) := by
  rw [← orbitalAverage_group_element, serreGaloisOrbitalAverage]
  rfl

/-- In the Serre Artin carrier orbital averaging discards exactly the trace-zero operators. -/
theorem serreGalois_orbital_kernel :
    (orbitalAverage serreQ8ArtinRepresentation).ker = (LinearMap.trace ℂ Q8Carrier).ker := by
  ext A
  change orbitalAverage serreQ8ArtinRepresentation A = 0 ↔ LinearMap.trace ℂ Q8Carrier A = 0
  rw [serreGaloisOrbitalAverage, smul_eq_zero, or_iff_left one_ne_zero, div_eq_zero_iff,
    or_iff_left (by norm_num : (2:ℂ) ≠ 0)]

/-- Two orbital measures act identically on the Artin carrier precisely when their characters agree. -/
theorem serreGalois_orbital_character_fibers (y z : Gal(K3/ℚ)) :
    orbitalAverage serreQ8ArtinRepresentation (serreQ8ArtinRepresentation y) =
      orbitalAverage serreQ8ArtinRepresentation (serreQ8ArtinRepresentation z) ↔
      serreQ8ArtinRepresentation.character y = serreQ8ArtinRepresentation.character z := by
  constructor
  · intro h
    change LinearMap.trace ℂ Q8Carrier (serreQ8ArtinRepresentation y) =
      LinearMap.trace ℂ Q8Carrier (serreQ8ArtinRepresentation z)
    simpa only [orbitalAverage_trace] using congrArg (LinearMap.trace ℂ Q8Carrier) h
  · intro h
    change LinearMap.trace ℂ Q8Carrier _ = LinearMap.trace ℂ Q8Carrier _ at h
    rw [serreGaloisOrbitalAverage, serreGaloisOrbitalAverage, h]

#print axioms orbitalAverage_commutes
#print axioms orbitalAverage_trace
#print axioms orbitalAverage_group_element
#print axioms quaternionOrbitalAverage
#print axioms serreGaloisOrbitalAverage
#print axioms serreGalois_orbital_character
#print axioms serreGalois_orbital_kernel
#print axioms serreGalois_orbital_character_fibers

end GaloisForLFunctions.RepresentationLifting
