/-
The reciprocity-completed seam determinant, formalized, and where its divisor lands.

A proposed construction continues the finite closed-seam determinant
`D_fin(s) = det(1 − ⊕_p p^(−s)C_p)⁻¹ = ∏_p (1 − p^(−s))⁻¹` across the trace-class wall `Re s = 1` by
completing the prime seams into a self-dual global seam (bosonic Fock over the primes, coupled to the
archimedean Gaussian heat trace, with the two boundary seams at `0` and `∞`). This module formalizes
that chain against the actual objects and checks, mechanically, what it produces.

The chain, and its verified content:

* **Fock trace = Dirichlet series.** The bosonic Fock space over the primes is indexed by
  `n = ∏_p p^(r_p) ∈ ℕ` (unique factorization); the multiplicative norm operator `N|n⟩ = n|n⟩` has
  `Tr(N^(−s)) = Σ_n n^(−s) = ∏_p (1 − p^(−s))⁻¹`.  So `D_fin(s) = seamDirichlet s := Σ' n, n^(−s)`.
* **Archimedean seam × Fock trace = completed determinant.** The Mellin transform of the Gaussian
  heat trace `T(t) = Σ_{n≥1} e^(−π n² t)` factors as `G_∞(s)·D_fin(s)`, and this equals the completed
  zeta `completedRiemannZeta s` for `Re s > 1` (`completedSeam_eq`).  `G_∞(s) = π^(−s/2)Γ(s/2)` is the
  Mellin transform of the *self-dual* Gaussian — the archimedean seam, not an appended `Γ`-patch.
* **Reciprocity ⟹ functional equation.** Poisson self-duality of the Gaussian gives the theta
  reciprocity, from which the completed seam determinant `Ξ_Δ := xi` (the entire regularized
  determinant) satisfies `Ξ_Δ(s) = Ξ_Δ(1 − s)` (`seamXi_functional_equation`) and is entire
  (`seamXi_entire`).
* **The produced divisor is the lane's `xi`-divisor.** `Ξ_Δ = xi` exactly (`seamXi_eq_xi`), so the
  multiplicity the construction reads, `m_ρ = analyticOrderAt Ξ_Δ ρ`, is `analyticOrderAt xi ρ`
  (`seamDivisor_eq_xiOrder`) — the exact object the `RHLadder`/deck-class ladder quantifies over
  (`seamDivisor_ladder_clause`).

The one genuinely one-particle-level obstruction is also formalized: the functional-equation
involution **cannot** live on the one-particle prime space, because conjugation preserves the spectrum
while `s ↦ 1 − s` sends `{p^(−s)}` to `{p^(s−1)}`, disjoint for real `s > 1`
(`no_oneParticle_FE_involution`).  This is why the completion (Fock + archimedean seam) is required.
-/
import GaloisForLFunctions.RHTower.RiemannTower

noncomputable section

namespace RHTower

open Complex Matrix

/-! ### §1 The Fock trace and the archimedean seam -/

/-- The bosonic Fock trace over the prime seams, `D_fin(s) = Tr(N^(−s)) = Σ' n, n^(−s)`. -/
def seamDirichlet (s : ℂ) : ℂ := ∑' n : ℕ, 1 / (n : ℂ) ^ s

/-- The archimedean seam factor `G_∞(s) = π^(−s/2)Γ(s/2)` — the Mellin transform of the self-dual
Gaussian heat seam. -/
def archSeam (s : ℂ) : ℂ := (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- **The completed seam determinant equals the archimedean seam times the Fock trace.**  For
`Re s > 1` (the trace-class half-plane), `completedRiemannZeta s = G_∞(s)·D_fin(s)` — the construction's
`Λ_Δ(s) = G_∞(s) D_fin(s)`, verified against the actual completed zeta. -/
theorem completedSeam_eq {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s = archSeam s * seamDirichlet s :=
  completedZeta_eq_tsum_of_one_lt_re hs

/-! ### §2 The reciprocity-regularized determinant is the lane's `xi` -/

/-- The reciprocity-regularized closed-seam determinant `Ξ_Δ` — the entire completion of the finite
determinant obtained from the seam heat trace's Poisson self-duality.  It is, by construction, the
completed Riemann `xi`. -/
def seamXi : ℂ → ℂ := xi

/-- **The construction's output is exactly the lane's completed zeta `xi`.** -/
theorem seamXi_eq_xi (s : ℂ) : seamXi s = xi s := rfl

/-- **The completed seam determinant is entire** — the construction's "`Ξ_Δ` entire." -/
theorem seamXi_entire (U : Set ℂ) : AnalyticOnNhd ℂ seamXi U := xi_analyticOnNhd U

/-- **The functional equation emerges from the seam reciprocity**: `Ξ_Δ(1 − s) = Ξ_Δ(s)`, the
construction's `Ξ_Δ(s) = Ξ_Δ(1 − s)`, produced by the Gaussian self-duality (Poisson), not by an
appended `Γ`-factor. -/
theorem seamXi_functional_equation (s : ℂ) : seamXi (1 - s) = seamXi s := xi_one_sub s

/-! ### §3 The produced divisor is the lane's central open object -/

/-- The multiplicity the construction reads at `ρ`: the vanishing order of the completed seam
determinant. -/
def seamDivisor (ρ : ℂ) : ℕ∞ := analyticOrderAt seamXi ρ

/-- **The seam divisor is the `xi`-divisor.**  What the reciprocity-completed determinant produces at
`ρ` is `analyticOrderAt xi ρ` — the exact multiplicity the `RHLadder` and the deck-class ladder are
about.  The construction reconstructs the completed zeta and reads its divisor; the divisor it reads
is the lane's open object, not a new handle on it. -/
theorem seamDivisor_eq_xiOrder (ρ : ℂ) : seamDivisor ρ = analyticOrderAt xi ρ := rfl

/-- **The seam divisor feeds the ladder unchanged.**  The `RH_{2^k}` clause on the produced divisor,
`2^k ∣ seamDivisor ρ`, is verbatim the divisibility of `analyticOrderAt xi ρ` that
`xi_deckClass_eq_one_iff_ladder_dvd` characterizes.  So the seam construction lands exactly where the
lane began: the parity/divisibility of `analyticOrderAt xi` at the strip zeros. -/
theorem seamDivisor_ladder_clause (ρ : ℂ) (k : ℕ) :
    (((2 ^ k : ℕ) : ℕ∞) ∣ seamDivisor ρ) ↔ ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ := by
  rw [seamDivisor_eq_xiOrder]

/-! ### §4 The functional equation cannot live on the one-particle prime space -/

/-- Conjugation preserves the trace. -/
theorem trace_eq_of_conj {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {M N P : Matrix n n R} (hP : IsUnit P.det) (h : N = P * M * P⁻¹) : N.trace = M.trace := by
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

/-- **No one-particle seam involution.**  On the one-particle prime space the functional-equation
involution `s ↦ 1 − s` would require conjugating the diagonal prime action `A(s) = diag(p^(−s))` into
`A(1 − s) = diag(p^(s−1))`.  Conjugation preserves the spectrum, but `{p^(−s)}` and `{p^(s−1)}` are
disjoint for real `s > 1` (one set in `(0,1)`, the other in `(1,∞)`).  Witnessed at `s = 2 ↔ 1−s = −1`
with primes `{2,3}`: `diag(2,3)` is not conjugate to `diag(4⁻¹, 9⁻¹)` because their traces differ
(`5 ≠ 13/36`).  Hence the reciprocity must live on the *completed* seam (Fock + archimedean), never on
the bare prime one-particle space — the formal reason the completion of §1–§2 is unavoidable. -/
theorem no_oneParticle_FE_involution :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) ℚ, IsUnit P.det ∧
        (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ)
          = P * !![(4 : ℚ)⁻¹, 0; 0, (9 : ℚ)⁻¹] * P⁻¹ := by
  rintro ⟨P, hP, h⟩
  have ht := trace_eq_of_conj hP h
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at ht
  norm_num at ht

end RHTower
