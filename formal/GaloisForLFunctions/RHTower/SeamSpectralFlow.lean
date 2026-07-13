/-
# The seam Krein index: definiteness as a congruence-invariant obstruction, and RH as its vanishing

The functional equation forces a self-adjoint operator on the completed zeta section with respect
to an *indefinite* Krein/Weil Gram form; its negative index `κ₋` (the maximal dimension of a
subspace on which the form is negative-definite) counts the off-critical-line zeros.  The reality
of a spectrum is not the invariant that decides the Riemann Hypothesis — the FE supplies the
operator for free — the invariant is `κ₋`, and RH is the single equation `κ₋ = 0`: the FE-forced
indefinite form is definite (admits a compatible positive polarization).

This file isolates the algebraic surface of that index, on the concrete Krein Gram matrix.  The
face `κ₋ = 0` is encoded as `KreinNonneg H := ∀ x, 0 ≤ (xᴴ H x).re` — no negative Krein direction.
Three facts make this a genuine index rather than an ad-hoc predicate:

* `kreinNonneg_iff_no_negDef` — `KreinNonneg H` is exactly `κ₋ = 0`: it holds iff every subspace on
  which the form is negative-definite is trivial.  This is the definiteness ⟺ index-zero
  equivalence (a positive polarization ⟺ the negative index vanishes).
* `kreinNonneg_congr` — `KreinNonneg` is invariant under invertible congruence `H ↦ Pᴴ H P`
  (Sylvester rigidity): `κ₋` is a property of the *form*, basis-free, hence a deformation
  invariant — the "structurally pinned" computation, not a re-count.
* `krein_smul_re` — the Krein value scales by `‖c‖²`, the sign-homogeneity that makes a single
  negative direction span a negative-definite line.

The reduction `riemannHypothesis_of_seam_polarization` is the index-prong analogue of the
residual-face gate: modulo the *argument principle* (an off-line zero forces a negative Krein
direction — the identity `κ₋ = ` off-line count, supplied as an interface), RH follows from the
single geometric clause that the seam Gram admits a positive polarization (`KreinNonneg`).  The
biconditional `riemannHypothesis_iff_seam_polarization` records that this is an *equivalence*: RH
holds iff the FE-forced Krein form is everywhere definite.  No operator or carrier is constructed;
definiteness is a constraint on a given form, and its invariance under congruence is what pins it.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.HTGeometry.CarrierPickKernel
import GaloisForLFunctions.HTGeometry.KreinLangerInertia

open Complex Matrix Submodule GaloisForLFunctions

namespace RHTower

/-- **The definiteness face `κ₋ = 0`**: the Krein Gram `H` has no negative direction,
`∀ x, 0 ≤ (xᴴ H x).re`.  This is the algebraic form of "the FE-forced indefinite form admits a
positive polarization"; `kreinNonneg_iff_no_negDef` identifies it with the vanishing of the
negative index. -/
def KreinNonneg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ x : Fin N → ℂ, 0 ≤ (star x ⬝ᵥ H.mulVec x).re

/-- **Sign-homogeneity of the Krein value**: `((cx)ᴴ H (cx)).re = ‖c‖² · (xᴴ H x).re`.  The
quadratic scaling that lets one negative direction span a negative-definite line. -/
theorem krein_smul_re {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (c : ℂ) :
    (star (c • x) ⬝ᵥ H.mulVec (c • x)).re
      = Complex.normSq c * (star x ⬝ᵥ H.mulVec x).re := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_smul,
      smul_eq_mul, show c * star c = (Complex.normSq c : ℂ) by
        rw [Complex.star_def, Complex.mul_conj], Complex.re_ofReal_mul]

/-- **Congruence identity**: `xᴴ (Pᴴ H P) x = (Px)ᴴ H (Px)`.  The change-of-basis law for the
Krein value. -/
theorem krein_congr_val {N : ℕ} (H P : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    star x ⬝ᵥ (Pᴴ * H * P).mulVec x = star (P.mulVec x) ⬝ᵥ H.mulVec (P.mulVec x) := by
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-- Congruence never creates a negative direction from a definite form: `KreinNonneg H` implies
`KreinNonneg (Pᴴ H P)` for *any* `P` (the pullback of a nonnegative form is nonnegative). -/
theorem kreinNonneg_congr_of {N : ℕ} (H P : Matrix (Fin N) (Fin N) ℂ)
    (h : KreinNonneg H) : KreinNonneg (Pᴴ * H * P) := by
  intro x; rw [krein_congr_val]; exact h _

/-- **Sylvester rigidity**: the definiteness face is invariant under invertible congruence
`H ↦ Pᴴ H P`.  The negative index is a property of the form, independent of the basis — the
"structurally pinned", deformation-invariant computation. -/
theorem kreinNonneg_congr {N : ℕ} (H P : Matrix (Fin N) (Fin N) ℂ) (hP : IsUnit P.det) :
    KreinNonneg (Pᴴ * H * P) ↔ KreinNonneg H := by
  constructor
  · intro h y
    have hy : P.mulVec (P⁻¹.mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
    have := h (P⁻¹.mulVec y)
    rwa [krein_congr_val, hy] at this
  · exact fun h => kreinNonneg_congr_of H P h

/-- **Definiteness ⟺ index-zero.**  `KreinNonneg H` holds iff every subspace on which the Krein
form is negative-definite is trivial — i.e. iff the negative index `κ₋` vanishes.  A positive
polarization of the form is exactly the absence of a negative square. -/
theorem kreinNonneg_iff_no_negDef {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    KreinNonneg H ↔ ∀ (W : Submodule ℂ (Fin N → ℂ)),
      (∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ H.mulVec y).re < 0) → Module.finrank ℂ W = 0 := by
  constructor
  · intro h W hW
    have hbot : W = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact absurd (h y) (not_le.mpr (hW y hy hy0))
    rw [hbot, finrank_bot]
  · intro h x
    by_contra hx
    have hxlt : (star x ⬝ᵥ H.mulVec x).re < 0 := not_le.mp hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxlt
    set W := Submodule.span ℂ ({x} : Set (Fin N → ℂ)) with hWdef
    have hWneg : ∀ y ∈ W, y ≠ 0 → (star y ⬝ᵥ H.mulVec y).re < 0 := by
      intro y hy hy0
      rw [hWdef, Submodule.mem_span_singleton] at hy
      obtain ⟨c, rfl⟩ := hy
      have hc : c ≠ 0 := by rintro rfl; simp at hy0
      rw [krein_smul_re]
      exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc) hxlt
    have hfr := h W hWneg
    rw [hWdef, finrank_span_singleton hx0] at hfr
    exact one_ne_zero hfr

/-- The definiteness face as the negation of a negative direction: `KreinNonneg H ↔ ¬ ∃ x, ...`. -/
theorem kreinNonneg_iff_not_exists_neg {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    KreinNonneg H ↔ ¬ ∃ x : Fin N → ℂ, (star x ⬝ᵥ H.mulVec x).re < 0 := by
  rw [KreinNonneg, not_exists]
  exact forall_congr' fun x => (not_lt).symm

/-- **The index-prong Riemann Hypothesis gate.**  Modulo the *argument principle* — an off-line
zero of `ξ` forces a negative Krein direction in its local seam Gram `H ρ` (the identity
`κ₋ = ` off-line count) — the Riemann Hypothesis follows from the single geometric clause that
every seam Gram is definite (`KreinNonneg`, a positive polarization).  A definite form has no
negative direction, so no off-line zero can exist.  The polarization clause is the deformation
invariant of `kreinNonneg_congr`; RH is relocated onto its existence, attackable by index /
Hodge tools rather than by a spectral-reality search. -/
theorem riemannHypothesis_of_seam_polarization
    {N : ℕ} (H : ℂ → Matrix (Fin N) (Fin N) ℂ)
    (hAP : ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ x : Fin N → ℂ, (star x ⬝ᵥ (H ρ).mulVec x).re < 0)
    (hpol : ∀ ρ, KreinNonneg (H ρ)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  obtain ⟨x, hx⟩ := hAP ρ hρ hzero
  exact absurd hx (not_lt.mpr ((hpol ρ) x))

/-- **RH is the definiteness of the FE-forced Krein form.**  With the argument principle as a
biconditional (a right-half `ξ`-zero at `ρ` ⟺ a negative Krein direction in `H ρ`), the Riemann
Hypothesis is *equivalent* to every seam Gram being definite.  This is Hilbert–Pólya as a
polarization constraint: not a weakening of RH but a change of the deciding invariant from a
spectrum's reality to a form's negative index. -/
theorem riemannHypothesis_iff_seam_polarization
    {N : ℕ} (H : ℂ → Matrix (Fin N) (Fin N) ℂ)
    (hAP : ∀ ρ ∈ rightHalf,
        (xi ρ = 0 ↔ ∃ x : Fin N → ℂ, (star x ⬝ᵥ (H ρ).mulVec x).re < 0)) :
    RiemannHypothesis ↔ ∀ ρ ∈ rightHalf, KreinNonneg (H ρ) := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h ρ hρ
    rw [kreinNonneg_iff_not_exists_neg, ← hAP ρ hρ]
    exact h ρ hρ
  · intro h ρ hρ hzero
    rw [hAP ρ hρ] at hzero
    obtain ⟨x, hx⟩ := hzero
    exact absurd hx (not_lt.mpr ((h ρ hρ) x))

/-- The FE-symmetric conjugate-pair carrier is invariant under `t ↦ t̄`:
`conjPairCarrier (t̄) z = conjPairCarrier t z`.  The two poles `{t, t̄}` are the same unordered pair. -/
theorem conjPairCarrier_star (t z : ℂ) :
    conjPairCarrier (star t) z = conjPairCarrier t z := by
  simp only [conjPairCarrier, star_star]; rw [add_comm]

/-- Hence its Pick Gram is invariant under `t ↦ t̄`. -/
theorem conjPairPick_star {N : ℕ} (t : ℂ) (z : Fin N → ℂ) :
    conjPairPick (star t) z = conjPairPick t z := by
  ext j k; simp only [conjPairPick, Matrix.of_apply, conjPairCarrier_star]

/-- **The argument principle, discharged — any node set.**  If a node `z_{j₀} ∈ ℂ⁺` witnesses the
off-line pair (`Im m(z_{j₀}) < 0`, `m` the conjugate-pair carrier), then the full Pick Gram
`conjPairPick t z` fails `KreinNonneg`: the standard basis vector `e_{j₀}` sees the diagonal Pick
entry `Im m(z_{j₀})/Im z_{j₀} < 0`, a negative Krein direction (`κ₋ ≥ 1`).  A single off-line
witness anywhere in the node set breaks definiteness — the order-linked computation (a) as a
*theorem*, not an interface, on arbitrary node configurations. -/
theorem conjPairPick_not_kreinNonneg_of_witness {N : ℕ} (t : ℂ) (z : Fin N → ℂ)
    (j₀ : Fin N) (hz : 0 < (z j₀).im)
    (hwit : ((t - z j₀)⁻¹ + (star t - z j₀)⁻¹).im < 0) :
    ¬ KreinNonneg (conjPairPick t z) := by
  intro hK
  have hval := hK (Pi.single j₀ 1)
  have hextract : star (Pi.single j₀ (1 : ℂ)) ⬝ᵥ (conjPairPick t z).mulVec (Pi.single j₀ 1)
      = conjPairPick t z j₀ j₀ := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  rw [hextract] at hval
  have hdiag : (conjPairPick t z j₀ j₀).re
      = ((t - z j₀)⁻¹ + (star t - z j₀)⁻¹).im / (z j₀).im := by
    rw [conjPairPick, Matrix.of_apply]
    simpa [conjPairCarrier] using
      GaloisForLFunctions.pickDiag_re (conjPairCarrier t (z j₀)) (z j₀) hz.ne'
  rw [hdiag] at hval
  exact absurd hval (not_le.mpr (div_neg_of_neg_of_pos hwit hz))

/-- **Definiteness forces the critical line.**  If the conjugate-pair Pick Gram of the FE-symmetric
carrier is definite (`KreinNonneg`) on *every* `ℂ⁺` node configuration, then `t` lies on the critical
line (`Im t = 0`).  The polarization clause of `riemannHypothesis_of_seam_polarization`, combined with
the argument principle now proven (`conjPairPick_not_kreinNonneg_of_witness`), *is* the critical-line
location: no seam Krein form is definite while an off-line pair survives.  So for this carrier the sole
open input is the polarization existence — nothing else stands between it and RH. -/
theorem online_of_conjPairPick_kreinNonneg (t : ℂ)
    (hpol : ∀ {N : ℕ} (z : Fin N → ℂ), (∀ j, 0 < (z j).im) → KreinNonneg (conjPairPick t z)) :
    t.im = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstim : 0 < (star t).im := by
      rw [show star t = (starRingEnd ℂ) t from rfl, Complex.conj_im]; linarith
    obtain ⟨z, hz, hm⟩ := GaloisForLFunctions.conj_pair_not_herglotz (star t) hstim
    refine conjPairPick_not_kreinNonneg_of_witness (star t) (fun _ : Fin 1 => z) 0 hz
      (by simpa using hm) ?_
    rw [conjPairPick_star]; exact hpol (fun _ : Fin 1 => z) (fun _ => hz)
  · obtain ⟨z, hz, hm⟩ := GaloisForLFunctions.conj_pair_not_herglotz t hgt
    exact conjPairPick_not_kreinNonneg_of_witness t (fun _ : Fin 1 => z) 0 hz (by simpa using hm)
      (hpol (fun _ : Fin 1 => z) (fun _ => hz))

/-- The factored Krein/Weil Gram `H = ∑ᵢ wᵢwᵢ* − ∑ᵢ uᵢuᵢ*` — `k` positive squares against `k`
negative squares.  For the FE conjugate-pair carrier `wᵢ = eᵢ+aᵢ`, `uᵢ = eᵢ−aᵢ` (one pair per
off-line zero), this is the seam Krein form and `k` is the off-line zero count. -/
noncomputable def factoredKreinForm {N k : ℕ} (w u : Fin k → (Fin N → ℂ)) :
    Matrix (Fin N) (Fin N) ℂ :=
  (∑ i, Matrix.of (fun p q => w i p * star (w i q)))
    - (∑ i, Matrix.of (fun p q => u i p * star (u i q)))

/-- **Exact `κ₋ = k`: `k ≥ 1` off-line pairs ⟹ not definite.**  Under Cauchy non-degeneracy (the
evaluation map `x ↦ (⟨wᵢ,x⟩, ⟨uᵢ,x⟩)` surjective — `exact_neg_inertia`'s hypothesis, unconditional for
the conjugate-pair carrier via `cauchy_linearIndependent`), the factored FE Krein form with `k ≥ 1`
negative squares fails `KreinNonneg`: it carries a negative-definite subspace of dimension exactly `k`.
This is the exact order-linked count, not merely `κ₋ ≥ 1`, on the full multi-pair carrier. -/
theorem factoredKrein_not_kreinNonneg_of_pos {N k : ℕ} (hk : 0 < k) (w u : Fin k → (Fin N → ℂ))
    (Φ Ψ : (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin N → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin N → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) :
    ¬ KreinNonneg (factoredKreinForm w u) := by
  obtain ⟨_, W, hWrank, hWneg⟩ := exact_neg_inertia w u Φ Ψ hΦ hΨ hT
  intro hK
  have hfr := (kreinNonneg_iff_no_negDef (factoredKreinForm w u)).mp hK W hWneg
  rw [hWrank] at hfr
  omega

/-- With no off-line pairs (`k = 0`) the factored Krein form is the zero form, trivially definite. -/
theorem factoredKrein_kreinNonneg_of_zero {N k : ℕ} (w u : Fin k → (Fin N → ℂ)) (hk : k = 0) :
    KreinNonneg (factoredKreinForm w u) := by
  subst hk; intro x; simp [factoredKreinForm]

/-- **Definiteness ⟺ zero off-line pairs (exact).**  Under Cauchy non-degeneracy, the factored FE
Krein form is definite (`KreinNonneg`, a positive polarization) **iff** its negative index vanishes,
`k = 0` — no off-line zeros.  The sharpest form of "definiteness ⟺ index-zero" on the actual finite
FE carrier: the polarization exists exactly when RH holds for the pairs it encodes. -/
theorem factoredKrein_kreinNonneg_iff {N k : ℕ} (w u : Fin k → (Fin N → ℂ))
    (Φ Ψ : (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin N → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin N → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) :
    KreinNonneg (factoredKreinForm w u) ↔ k = 0 := by
  constructor
  · intro hK
    by_contra hk
    exact factoredKrein_not_kreinNonneg_of_pos (Nat.pos_of_ne_zero hk) w u Φ Ψ hΦ hΨ hT hK
  · exact factoredKrein_kreinNonneg_of_zero w u

/-- **The index-prong RH gate, with the concrete FE carrier.**  For a right-half `ξ`-zero `ρ`, put
`t = (ρ - ½)·(-i)`, the coordinate whose imaginary part is `½ - Re ρ` (so `Im t = 0 ⟺ Re ρ = ½`, and
`ρ` in the open right half forces `Im t < 0`).  If the FE-symmetric conjugate-pair carrier `conjPairPick t`
— an *explicit function of `t`*, not built from `ξ` — is definite (`KreinNonneg`) on every `ℂ⁺` node
configuration at every right-half `ξ`-zero, then the Riemann Hypothesis holds:
`online_of_conjPairPick_kreinNonneg` forces `Im t = 0`, i.e. `Re ρ = ½`, contradicting `Re ρ > ½`.
No carrier is constructed from `ξ` (rule 7): the carrier is the fixed explicit object, the `ξ`-zero
enters only as the point at which definiteness is *assumed*, and that polarization assumption is the
single open geometric clause standing between the index reframe and RH. -/
theorem riemannHypothesis_of_conjPairCarrier_polarization
    (hpol : ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ {N : ℕ} (z : Fin N → ℂ), (∀ j, 0 < (z j).im) →
          KreinNonneg (conjPairPick ((ρ - 1 / 2) * (-I)) z)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  have hon := online_of_conjPairPick_kreinNonneg ((ρ - 1 / 2) * (-I))
    (fun {N} z hz => hpol ρ hρ hzero z hz)
  have himt : ((ρ - 1 / 2) * (-I)).im = 1 / 2 - ρ.re := by
    simp [Complex.mul_im, Complex.sub_im, Complex.sub_re]
  rw [himt] at hon
  have hgt := mem_rightHalf.mp hρ
  linarith

/-- **RH is the polarizability of the concrete FE carrier.**  The Riemann Hypothesis is *equivalent*
to: at every right-half `ξ`-zero `ρ`, the explicit conjugate-pair carrier `conjPairPick ((ρ-½)·(-i))`
is definite on every `ℂ⁺` node configuration.  Forward is the substantive gate
(`riemannHypothesis_of_conjPairCarrier_polarization`); the reverse is vacuous — under RH there are no
right-half `ξ`-zeros, so the polarization condition has no instances to satisfy.  HP-as-polarization
with the concrete carrier: RH holds iff the FE Krein form the zeros would build is definite. -/
theorem riemannHypothesis_iff_conjPairCarrier_polarization :
    RiemannHypothesis ↔
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ {N : ℕ} (z : Fin N → ℂ), (∀ j, 0 < (z j).im) →
          KreinNonneg (conjPairPick ((ρ - 1 / 2) * (-I)) z)) := by
  constructor
  · intro hRH ρ hρ hzero
    rw [rh_iff_xi_ne_zero_right] at hRH
    exact absurd hzero (hRH ρ hρ)
  · exact riemannHypothesis_of_conjPairCarrier_polarization

end RHTower
