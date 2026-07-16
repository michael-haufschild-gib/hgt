import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.FieldConjectures
import GaloisForLFunctions.HTGeometry.LeeYangForcingThreshold

/-!
# The carrier interaction locus is purely marginal, and RH as marginality

Deform the FE conjugate-pair carrier off the critical line by a real coupling `y`: at
base point `x` the carrier parameter is `t = x + y i`, and the localization property
is `CarrierHerglotz t` (the carrier is Nevanlinna/Herglotz on `ℂ⁺`).  The locus of
localizing couplings is computed exactly:

* `carrierInteractionLocus_eq_singleton` — the locus is `{0}`: localization holds at
  the marginal coupling and nowhere else.  Consequently the locus **is** the
  singleton of its own threshold (`carrierInteractionLocus_eq_threshold`), it has
  empty interior (`interior_carrierInteractionLocus`), and the monotone forcing
  mechanism fails on it (`not_isForcingFamily_carrierInteractionLocus`):
  localization at the carrier is never forced with margin — it is achieved, if at
  all, exactly at the boundary.

The Riemann Hypothesis is then literally a marginality statement:

* `riemannHypothesis_iff_zero_coupling_marginal` — RH holds iff for every
  hypothetical `ξ`-zero in the open right half-plane the associated coupling
  `½ − Re ρ` lies in the marginal locus at base point `Im ρ`;
* `riemannHypothesis_iff_carrierHerglotz_at_zeros` — equivalently, iff the
  conjugate-pair carrier is Herglotz at the seam coordinate `(ρ − ½)·(−i)` of every
  such zero.

Both equivalences are unconditional; neither asserts RH.
-/

open Complex Set GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The interaction locus of the FE conjugate-pair carrier at base point `x`: the set
of couplings `y` for which the carrier with parameter `x + y i` is Herglotz on
`ℂ⁺`. -/
def carrierInteractionLocus (x : ℝ) : Set ℝ :=
  {y : ℝ | CarrierHerglotz ((x : ℂ) + (y : ℂ) * Complex.I)}

/-- **The locus is purely marginal**: localization holds exactly at coupling `0`. -/
theorem carrierInteractionLocus_eq_singleton (x : ℝ) :
    carrierInteractionLocus x = {0} := by
  ext y
  simp [carrierInteractionLocus, carrierHerglotz_iff_onLine, OnLine]

/-- The monotone forcing mechanism fails on the carrier locus: localization does not
persist under increased coupling, because the locus is a single point. -/
theorem not_isForcingFamily_carrierInteractionLocus (x : ℝ) :
    ¬ IsForcingFamily (carrierInteractionLocus x) := by
  rw [carrierInteractionLocus_eq_singleton]
  intro h
  have h1 : (1 : ℝ) ∈ ({0} : Set ℝ) :=
    h (Set.mem_singleton_iff.mpr rfl) zero_le_one
  simp at h1

/-- Localization at the carrier is never forced with margin: the locus has empty
interior. -/
theorem interior_carrierInteractionLocus (x : ℝ) :
    interior (carrierInteractionLocus x) = ∅ := by
  rw [carrierInteractionLocus_eq_singleton]
  exact interior_singleton 0

/-- The locus coincides with the singleton of its own threshold: the marginal point
is the only localizing coupling. -/
theorem carrierInteractionLocus_eq_threshold (x : ℝ) :
    carrierInteractionLocus x = {sInf (carrierInteractionLocus x)} := by
  rw [carrierInteractionLocus_eq_singleton, csInf_singleton]

/-- The seam coordinate `(ρ − ½)·(−i)` decomposes into base point `Im ρ` and coupling
`½ − Re ρ`. -/
theorem seam_coordinate_eq (ρ : ℂ) :
    (ρ - 1 / 2) * (-Complex.I)
      = ((ρ.im : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * Complex.I) := by
  have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h2]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]

/-- **RH as marginality of the zero couplings.** The Riemann Hypothesis holds iff for
every hypothetical `ξ`-zero in the open right half-plane the associated carrier
coupling `½ − Re ρ` lies in the (purely marginal) interaction locus at base point
`Im ρ`. -/
theorem riemannHypothesis_iff_zero_coupling_marginal :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        (1 / 2 - ρ.re) ∈ carrierInteractionLocus ρ.im := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h ρ hρ h0
    exact absurd h0 (h ρ hρ)
  · intro h ρ hρ h0
    have hm := h ρ hρ h0
    rw [carrierInteractionLocus_eq_singleton, mem_singleton_iff] at hm
    have hre := mem_rightHalf.mp hρ
    linarith

/-- **RH as carrier Herglotz-ness at the seam coordinates.** Equivalent packaging via
`seam_coordinate_eq`: RH holds iff the conjugate-pair carrier is Herglotz at the seam
coordinate of every hypothetical right-half `ξ`-zero. -/
theorem riemannHypothesis_iff_carrierHerglotz_at_zeros :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        CarrierHerglotz ((ρ - 1 / 2) * (-Complex.I)) := by
  rw [riemannHypothesis_iff_zero_coupling_marginal]
  refine forall_congr' fun ρ => forall_congr' fun hρ => forall_congr' fun h0 => ?_
  rw [seam_coordinate_eq ρ]
  exact Iff.rfl

end

end RHTower
