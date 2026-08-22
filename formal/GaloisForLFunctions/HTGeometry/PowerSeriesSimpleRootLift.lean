import GaloisForLFunctions.HTGeometry.HenselDefectRoot

/-!
# Simple-root Hensel lifting over a power series ring

The deformation step of the generic-Galois-group construction needs exactly one form of Hensel's
lemma: a **simple** root of the residue polynomial lifts, uniquely, to a root over the power
series ring.  `HenselDefectRoot.exists_isRoot_of_defect` supplies existence at defect `r = 0`, and
`isRoot_unique_of_sq_dvd` supplies uniqueness; this file packages the two.

Uniqueness is what makes the lift *equivariant*: a coefficientwise automorphism of the base sends
the lift of a residue root to the lift of its image, because both are lifts of the same residue
root.

## Main results

* `exists_isRoot_powerSeries_of_isUnit_deriv` — existence of the lift.
* `existsUnique_isRoot_powerSeries_of_isUnit_deriv` — existence and uniqueness.
* `isRoot_map_powerSeries` — a coefficientwise ring map sends roots to roots of the mapped
  polynomial, so an automorphism fixing the coefficients permutes the roots.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Simple-root Hensel lifting.**  A root of the residue polynomial at which the derivative is a
unit lifts to a root over `PowerSeries R`. -/
theorem exists_isRoot_powerSeries_of_isUnit_deriv
    {G : Polynomial (PowerSeries R)} {y₀ : PowerSeries R}
    (hd : IsUnit ((Polynomial.derivative G).eval y₀))
    (hv : (PowerSeries.X : PowerSeries R) ∣ Polynomial.eval y₀ G) :
    ∃ y : PowerSeries R, G.IsRoot y ∧ (PowerSeries.X : PowerSeries R) ∣ (y - y₀) := by
  have h := exists_isRoot_of_defect (F := G) (y₀ := y₀) (r := 0)
    (u := (Polynomial.derivative G).eval y₀) hd (by simp) (by simpa using hv)
  simpa using h

/-- **The lift is unique.**  Two roots congruent to `y₀` modulo `X` coincide. -/
theorem existsUnique_isRoot_powerSeries_of_isUnit_deriv
    {G : Polynomial (PowerSeries R)} {y₀ : PowerSeries R}
    (hd : IsUnit ((Polynomial.derivative G).eval y₀))
    (hv : (PowerSeries.X : PowerSeries R) ∣ Polynomial.eval y₀ G) :
    ∃! y : PowerSeries R, G.IsRoot y ∧ (PowerSeries.X : PowerSeries R) ∣ (y - y₀) := by
  classical
  obtain ⟨y, hroot, hcong⟩ := exists_isRoot_powerSeries_of_isUnit_deriv hd hv
  refine ⟨y, ⟨hroot, hcong⟩, ?_⟩
  rintro y' ⟨hroot', hcong'⟩
  set d : PowerSeries R := (Polynomial.derivative G).eval y₀ with hdd
  have hd0 : d ≠ 0 := hd.ne_zero
  obtain ⟨w, hw⟩ := hd
  have hdinv : d * (↑w⁻¹ : PowerSeries R) = 1 := by
    have hww : (↑w : PowerSeries R) * (↑w⁻¹ : PowerSeries R) = 1 := w.mul_inv
    rwa [hw] at hww
  set z : PowerSeries R := (↑w⁻¹ : PowerSeries R) * (y - y₀) with hz
  set z' : PowerSeries R := (↑w⁻¹ : PowerSeries R) * (y' - y₀) with hz'
  have hyz : y₀ + d * z = y := by
    rw [hz, ← mul_assoc, hdinv, one_mul]
    ring
  have hyz' : y₀ + d * z' = y' := by
    rw [hz', ← mul_assoc, hdinv, one_mul]
    ring
  have hmem : z ∈ Ideal.span {(PowerSeries.X : PowerSeries R)} := by
    obtain ⟨c, hc⟩ := hcong
    exact Ideal.mem_span_singleton.2 ⟨(↑w⁻¹ : PowerSeries R) * c, by rw [hz, hc]; ring⟩
  have hmem' : z' ∈ Ideal.span {(PowerSeries.X : PowerSeries R)} := by
    obtain ⟨c, hc⟩ := hcong'
    exact Ideal.mem_span_singleton.2 ⟨(↑w⁻¹ : PowerSeries R) * c, by rw [hz', hc]; ring⟩
  have hzz : z' = z :=
    isRoot_unique_of_sq_dvd (Ideal.span {(PowerSeries.X : PowerSeries R)}) rfl hd0
      hmem' hmem (by rw [hyz']; exact hroot') (by rw [hyz]; exact hroot)
  rw [← hyz', ← hyz, hzz]

omit [IsDomain R] in
/-- A coefficientwise ring map sends a root to a root of the mapped polynomial; when the map fixes
the coefficients of `G` it therefore permutes the roots of `G`. -/
theorem isRoot_map_powerSeries {S : Type*} [CommRing S] (φ : PowerSeries R →+* S)
    {G : Polynomial (PowerSeries R)} {y : PowerSeries R} (h : G.IsRoot y) :
    (G.map φ).IsRoot (φ y) := by
  have := congrArg φ h
  simpa [Polynomial.eval_map, Polynomial.eval₂_at_apply] using this

/-! ### Equivariance of the lift

A coefficientwise automorphism that fixes the polynomial permutes its roots, and — because the
lift over a given residue root is *unique* — it sends the lift of `y₀` to the lift of `φ y₀`.
This is the mechanism that turns an automorphism of the residue field into a permutation of the
deformed roots.
-/

/-- **The lift is equivariant.** -/
theorem map_lift_eq (φ : R ≃+* R)
    {G : Polynomial (PowerSeries R)}
    (hG : G.map (PowerSeries.map (φ : R →+* R)) = G)
    {y₀ y y' : PowerSeries R}
    (hd : IsUnit ((Polynomial.derivative G).eval (PowerSeries.map (φ : R →+* R) y₀)))
    (hv : (PowerSeries.X : PowerSeries R) ∣
      Polynomial.eval (PowerSeries.map (φ : R →+* R) y₀) G)
    (hy : G.IsRoot y) (hyc : (PowerSeries.X : PowerSeries R) ∣ (y - y₀))
    (hy' : G.IsRoot y')
    (hyc' : (PowerSeries.X : PowerSeries R) ∣ (y' - PowerSeries.map (φ : R →+* R) y₀)) :
    PowerSeries.map (φ : R →+* R) y = y' := by
  have hXmap : PowerSeries.map (φ : R →+* R) (PowerSeries.X : PowerSeries R)
      = (PowerSeries.X : PowerSeries R) := by
    simp
  have hrootmap : G.IsRoot (PowerSeries.map (φ : R →+* R) y) := by
    have h := isRoot_map_powerSeries (PowerSeries.map (φ : R →+* R)) hy
    rwa [hG] at h
  have hcongmap : (PowerSeries.X : PowerSeries R) ∣
      (PowerSeries.map (φ : R →+* R) y - PowerSeries.map (φ : R →+* R) y₀) := by
    have hdvd := map_dvd (PowerSeries.map (φ : R →+* R)) hyc
    rw [hXmap, map_sub] at hdvd
    exact hdvd
  have huniq := existsUnique_isRoot_powerSeries_of_isUnit_deriv hd hv
  exact huniq.unique ⟨hrootmap, hcongmap⟩ ⟨hy', hyc'⟩

/-- **Transport of a residue permutation to the lifts.**  If the `d` roots of `G` are the lifts of
`d` residue roots `ρ k`, and the coefficientwise automorphism `φ` permutes the `ρ k` by `π`, then it
permutes the lifts by the same `π`. -/
theorem map_lift_eq_of_perm (φ : R ≃+* R) {G : Polynomial (PowerSeries R)}
    (hG : G.map (PowerSeries.map (φ : R →+* R)) = G)
    {d : ℕ} {ρ : Fin d → R} {y : Fin d → PowerSeries R}
    (hy : ∀ k, G.IsRoot (y k))
    (hyc : ∀ k, (PowerSeries.X : PowerSeries R) ∣ (y k - PowerSeries.C (ρ k)))
    (hdu : ∀ k, IsUnit ((Polynomial.derivative G).eval (PowerSeries.C (ρ k))))
    (hv : ∀ k, (PowerSeries.X : PowerSeries R) ∣ Polynomial.eval (PowerSeries.C (ρ k)) G)
    (π : Equiv.Perm (Fin d)) (hπ : ∀ k, φ (ρ k) = ρ (π k)) (k : Fin d) :
    PowerSeries.map (φ : R →+* R) (y k) = y (π k) := by
  have hmapC : PowerSeries.map (φ : R →+* R) (PowerSeries.C (ρ k))
      = PowerSeries.C (ρ (π k)) := by
    rw [PowerSeries.map_C]
    congr 1
    exact hπ k
  refine map_lift_eq φ hG (y₀ := PowerSeries.C (ρ k)) ?_ ?_ (hy k) (hyc k) (hy (π k)) ?_
  · rw [hmapC]
    exact hdu (π k)
  · rw [hmapC]
    exact hv (π k)
  · rw [hmapC]
    exact hyc (π k)

end GaloisForLFunctions.HTGeometry
