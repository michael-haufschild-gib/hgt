import GaloisForLFunctions.HTGeometry.HelsonEulerModification
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Helson zeta of a finitely modified phase

On the half plane of absolute convergence a Helson zeta function is the Euler product of its phase.
Changing the phase at finitely many primes multiplies that product, factor by factor, by the
correction quotients, and a family equal to one off a finite set has the finite product as its
infinite product.  So a finitely modified Helson zeta is the Riemann zeta function times a finite
Euler modification, and therefore continues meromorphically to the whole plane.

This is the dense half of the continuation seam, with no classical input: the Euler product is
mathlib's, and the meromorphy is the finite modification law.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- On the half plane of absolute convergence a prime power has norm below one. -/
theorem norm_prime_cpow_neg_lt_one {p : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    ‖((p : ℂ)) ^ (-s)‖ < 1 := by
  have hp : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.2.one_lt
  have hnorm : ‖((p : ℂ)) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos p.2.pos _
  rw [hnorm, Complex.neg_re]
  refine Real.rpow_lt_one_of_one_lt_of_neg hp ?_
  linarith

/-- The Euler denominator of a unimodular phase does not vanish on the half plane of absolute
convergence. -/
theorem one_sub_phase_prime_cpow_ne_zero {χ : Nat.Primes → ℂ} (hunit : ∀ p, ‖χ p‖ ≤ 1)
    {p : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have heq : χ p * (p : ℂ) ^ (-s) = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have hlt : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ p‖ * ‖((p : ℂ)) ^ (-s)‖ ≤ 1 * ‖((p : ℂ)) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hunit p) (norm_nonneg _)
      _ = ‖((p : ℂ)) ^ (-s)‖ := one_mul _
      _ < 1 := norm_prime_cpow_neg_lt_one hs
  rw [heq, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem one_sub_prime_cpow_ne_zero {p : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  have h := one_sub_phase_prime_cpow_ne_zero (χ := fun _ => (1 : ℂ)) (fun _ => by simp)
    (p := p) hs
  simpa using h

/-- **The Euler product of a finitely modified phase.**  It converges to the Riemann zeta function
times the finite Euler modification. -/
theorem hasProd_helsonEuler {χ : Nat.Primes → ℂ} (hunit : ∀ p, ‖χ p‖ ≤ 1)
    {P : Finset Nat.Primes} (hP : ∀ p, p ∉ P → χ p = 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹)
      (riemannZeta s * ∏ p ∈ P, eulerFactor ((p : ℂ)) (χ p) s) := by
  classical
  have hz := riemannZeta_eulerProduct_hasProd hs
  have hone : HasProd (fun p : Nat.Primes => eulerFactor ((p : ℂ)) (χ p) s)
      (∏ p ∈ P, eulerFactor ((p : ℂ)) (χ p) s) := by
    refine hasProd_prod_of_ne_finset_one ?_
    intro p hp
    rw [eulerFactor, hP p hp, one_mul]
    exact div_self (one_sub_prime_cpow_ne_zero hs)
  have hfun : ∀ p : Nat.Primes,
      (1 - (p : ℂ) ^ (-s))⁻¹ * eulerFactor ((p : ℂ)) (χ p) s
        = (1 - χ p * (p : ℂ) ^ (-s))⁻¹ := by
    intro p
    have h1 : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := one_sub_prime_cpow_ne_zero hs
    have h2 : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 :=
      one_sub_phase_prime_cpow_ne_zero hunit hs
    rw [eulerFactor]
    field_simp
  have hmul := hz.mul hone
  have hshape : (fun p : Nat.Primes =>
      (1 - (p : ℂ) ^ (-s))⁻¹ * eulerFactor ((p : ℂ)) (χ p) s)
      = fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹ := funext hfun
  rw [hshape] at hmul
  exact hmul

/-- **A finitely modified Helson zeta continues meromorphically to the whole plane.**  Its Euler
product on the half plane of absolute convergence is the boundary value of a function meromorphic
on `ℂ`. -/
theorem exists_meromorphicOn_helsonZeta_of_mem_finiteEulerStratum {χ : Nat.Primes → ℂ}
    (hunit : ∀ p, ‖χ p‖ ≤ 1) (hχ : χ ∈ finiteEulerStratum) :
    ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (F s) := by
  classical
  have hfin : {p : Nat.Primes | χ p ≠ 1}.Finite := by
    simpa [finiteEulerStratum, GaloisForLFunctions.finiteModification] using hχ
  have hP : ∀ p, p ∉ hfin.toFinset → χ p = 1 := by
    intro p hp
    by_contra hne
    exact hp (hfin.mem_toFinset.mpr hne)
  refine ⟨fun s => riemannZeta s * ∏ p ∈ hfin.toFinset, eulerFactor ((p : ℂ)) (χ p) s, ?_, ?_⟩
  · refine meromorphicOn_riemannZeta_mul_eulerModification _ _ _ ?_
    intro p _
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero
  · intro s hs
    exact hasProd_helsonEuler hunit hP hs

/-! ### The continuable stratum of the phase torus is dense -/

/-- The phase torus: one unimodular phase for each prime. -/
abbrev PhaseTorus : Type := Nat.Primes → {z : ℂ // ‖z‖ = 1}

/-- The trivial phase. -/
def trivialPhase : PhaseTorus := fun _ => ⟨1, by simp⟩

/-- The phases whose Helson zeta continues meromorphically to the whole plane. -/
def continuableStratum : Set PhaseTorus :=
  {χ | ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
    ∀ s : ℂ, 1 < s.re →
      HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * (p : ℂ) ^ (-s))⁻¹) (F s)}

/-- A finite modification of the trivial phase is continuable. -/
theorem mem_continuableStratum_of_finiteModification {χ : PhaseTorus}
    (hχ : χ ∈ GaloisForLFunctions.finiteModification
      (fun _ : Nat.Primes => {z : ℂ // ‖z‖ = 1}) trivialPhase) :
    χ ∈ continuableStratum := by
  classical
  have hfin : {p : Nat.Primes | (χ p : ℂ) ≠ 1}.Finite := by
    have hbase : {p : Nat.Primes | χ p ≠ trivialPhase p}.Finite := hχ
    refine hbase.subset ?_
    intro p hp hcon
    exact hp (by rw [hcon]; rfl)
  have hunit : ∀ p : Nat.Primes, ‖(χ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (χ p).2
  have hP : ∀ p, p ∉ hfin.toFinset → (χ p : ℂ) = 1 := by
    intro p hp
    by_contra hne
    exact hp (hfin.mem_toFinset.mpr hne)
  refine ⟨fun s => riemannZeta s
      * ∏ p ∈ hfin.toFinset, eulerFactor ((p : ℂ)) ((χ p : ℂ)) s, ?_, ?_⟩
  · refine meromorphicOn_riemannZeta_mul_eulerModification _ _ _ ?_
    intro p _
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero
  · intro s hs
    exact hasProd_helsonEuler hunit hP hs

/-- **The continuable stratum is dense in the phase torus.**  Every basic cylinder fixes only
finitely many prime phases; extending by the trivial phase gives a finite Euler modification of the
Riemann zeta function, which continues meromorphically to the whole plane. -/
theorem dense_continuableStratum : Dense continuableStratum := by
  refine Dense.mono ?_ (GaloisForLFunctions.dense_finiteModification trivialPhase)
  intro χ hχ
  exact mem_continuableStratum_of_finiteModification hχ

end GaloisForLFunctions.HTGeometry
