import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorVectorSourceField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamLaurentMaster

/-!
# A finite Laurent particular inverse of the vector–vector harmonic master source

The vector–vector harmonic master source is, after clearing `r²(r²−1)`, a two-term Laurent
polynomial `M₁/r + M₃/r³` with no growing part, so the sourced master equation at independent
source rate `s` and output angular eigenvalue `μ` has the explicit decaying particular field
`A/r + B/r³` (`vvLaurentMaster`). The third-power coefficient needs only the angular denominator
`2 − μ` (the lower Laurent resonance `μ − (2s+3)(2s+4)` cancels exactly against the source), the
first-power coefficient needs the resolvent at `λ₂ = (2s+1)(2s+2)`; both denominators are
discharged at every Xi occurrence, either physical branch and every nonpositive real angular
eigenvalue by the scalar–scalar module's bounds. The field is smooth on the exterior and supplies
the seven-row sourced reconstruction data (`vvLaurentMaster_sourcedData`). The first-power
coefficient `A` is the normalizable coefficient of this response: the vector–vector block radiates
without any forced growth.
-/

open GaloisForLFunctions.HTGeometry.TwistedRadial Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMScalarStream
noncomputable section
set_option autoImplicit false

/-- Coefficient of the third inverse power in the vector–vector particular master field. -/
def vvLaurentMasterB (s μ : ℂ) : ℂ :=
  ((-2 : ℂ) * s + (1 : ℂ) * s * μ + (23 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * μ + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (61 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * μ + (54 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * μ + (21 : ℂ) * s ^ (5 : ℕ) + (3 : ℂ) * s ^ (6 : ℕ)) / (2 - μ)

/-- The first-inverse-power coefficient of the cleared vector–vector master source, times `2 − μ`. -/
def vvLaurentSourceMiddle (s μ : ℂ) : ℂ :=
  ((12 : ℂ) * s + (-6 : ℂ) * s * μ + (-102 : ℂ) * s ^ (2 : ℕ) + (-17 : ℂ) * s ^ (2 : ℕ) * μ + (1 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-318 : ℂ) * s ^ (3 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) * μ + (-312 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) * μ + (-126 : ℂ) * s ^ (5 : ℕ) + (-18 : ℂ) * s ^ (6 : ℕ))

/-- Coefficient of the first inverse power, at independent rate and angular eigenvalue. -/
def vvLaurentMasterA (s μ : ℂ) : ℂ :=
  (-vvLaurentSourceMiddle s μ / (2 - μ) - 6 * vvLaurentMasterB s μ) / (μ - (2 * s + 1) * (2 * s + 2))

/-- The cleared vector–vector master source is a two-term Laurent polynomial. -/
theorem vvMasterSource_laurent (s μ r : ℂ) (hr : r ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (hμ : 2 - μ ≠ 0) :
    r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * vvMasterSource s r μ =
      vvLaurentSourceMiddle s μ / ((2 - μ) * r) -
        (μ - (2 * s + 3) * (2 * s + 4)) * vvLaurentMasterB s μ / r ^ (3 : ℕ) := by
  unfold vvMasterSource vvLaurentSourceMiddle vvLaurentMasterB
  field_simp
  ring

/-- A decaying two-term Laurent field and its derivative. -/
def laurentDecayField (A B : ℂ) (r : ℝ) : ℂ := A / r + B / (r : ℂ) ^ (3 : ℕ)
def laurentDecayFirst (A B : ℂ) (r : ℝ) : ℂ := -A / (r : ℂ) ^ (2 : ℕ) - 3 * B / (r : ℂ) ^ (4 : ℕ)

theorem hasDerivAt_laurentDecayField (A B : ℂ) {r : ℝ} (hr : (r : ℂ) ≠ 0) :
    HasDerivAt (laurentDecayField A B) (laurentDecayFirst A B r) r := by
  have hR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h := ((hasDerivAt_const r A).div hR hr).add
    ((hasDerivAt_const r B).div (hR.pow 3) (pow_ne_zero 3 hr))
  refine h.congr_deriv ?_
  simp only [laurentDecayFirst, Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_laurentDecayFirst (A B : ℂ) {r : ℝ} (hr : (r : ℂ) ≠ 0) :
    HasDerivAt (laurentDecayFirst A B) (2 * A / (r : ℂ) ^ (3 : ℕ) + 12 * B / (r : ℂ) ^ (5 : ℕ)) r := by
  have hR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h := ((hasDerivAt_const r (-A)).div (hR.pow 2) (pow_ne_zero 2 hr)).sub
    ((hasDerivAt_const r (3 * B)).div (hR.pow 4) (pow_ne_zero 4 hr))
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The twisted master operator on the decaying Laurent field. -/
theorem laurentDecayField_operator (s μ A B : ℂ) {r : ℝ} (hr1 : 1 < r) :
    (r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1) *
      (twist s (twist s (laurentDecayField A B)) r +
        2 * r / ((r : ℂ) ^ (2 : ℕ) - 1) * twist s (laurentDecayField A B) r +
        (μ / ((r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1)) - 4 * s ^ (2 : ℕ) / ((r : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * laurentDecayField A B r) =
      ((μ - (2 * s + 1) * (2 * s + 2)) * A + 6 * B) / r +
        (μ - (2 * s + 3) * (2 * s + 4)) * B / (r : ℂ) ^ (3 : ℕ) := by
  obtain ⟨hr, hf⟩ := exterior_ne r hr1
  have he : ∀ᶠ t in 𝓝 r, HasDerivAt (laurentDecayField A B) (laurentDecayFirst A B t) t := by
    filter_upwards [exterior_eventually hr1] with t ht
    exact hasDerivAt_laurentDecayField A B (exterior_ne t ht).1
  have ht := hasDerivAt_twist s hr hf he (hasDerivAt_laurentDecayFirst A B hr)
  rw [twist, ht.deriv]
  simp only [twist, (hasDerivAt_laurentDecayField A B hr).deriv, laurentDecayFirst, laurentDecayField]
  field_simp
  ring

/-- The explicit decaying particular master field of the vector–vector source. -/
def vvLaurentMaster (s μ : ℂ) : ℝ → ℂ :=
  laurentDecayField (vvLaurentMasterA s μ) (vvLaurentMasterB s μ)

theorem vvLaurentMaster_equation (s μ : ℂ) (hμ : 2 - μ ≠ 0)
    (hres : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) : VVMasterEquation s μ (vvLaurentMaster s μ) := by
  intro r hr1
  obtain ⟨hr, hf⟩ := exterior_ne r hr1
  have ho := laurentDecayField_operator s μ (vvLaurentMasterA s μ) (vvLaurentMasterB s μ) hr1
  have hs := vvMasterSource_laurent s μ r hr hf hμ
  have hA : (μ - (2 * s + 1) * (2 * s + 2)) * vvLaurentMasterA s μ + 6 * vvLaurentMasterB s μ =
      -vvLaurentSourceMiddle s μ / (2 - μ) := by
    unfold vvLaurentMasterA
    rw [mul_div_cancel₀ _ hres]
    ring
  rw [hA] at ho
  apply (mul_eq_zero.mp (show (r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1) *
      (twist s (twist s (vvLaurentMaster s μ)) r + 2 * r / ((r : ℂ) ^ (2 : ℕ) - 1) * twist s (vvLaurentMaster s μ) r +
        (μ / ((r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1)) - 4 * s ^ (2 : ℕ) / ((r : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * vvLaurentMaster s μ r +
        vvMasterSource s r μ) = 0 from ?_)).resolve_left (mul_ne_zero (pow_ne_zero 2 hr) hf)
  rw [mul_add, show vvLaurentMaster s μ = laurentDecayField (vvLaurentMasterA s μ) (vvLaurentMasterB s μ) from rfl,
    ho, hs]
  field_simp
  ring

/-- The particular field is smooth on the entire exterior. -/
theorem vvLaurentMaster_contDiffOn (s μ : ℂ) :
    ContDiffOn ℝ ∞ (vvLaurentMaster s μ) (Ioi 1) := by
  have hi : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ)) (Ioi 1) := contDiff_ofReal_real.contDiffOn
  have hn : ∀ r ∈ Ioi (1 : ℝ), (r : ℂ) ≠ 0 := fun r hr => (exterior_ne r hr).1
  have hA : ContDiffOn ℝ ∞ (fun _ : ℝ => vvLaurentMasterA s μ) (Ioi 1) := contDiffOn_const
  have hB : ContDiffOn ℝ ∞ (fun _ : ℝ => vvLaurentMasterB s μ) (Ioi 1) := contDiffOn_const
  change ContDiffOn ℝ ∞ (fun r : ℝ => vvLaurentMasterA s μ / (r : ℂ) +
    vvLaurentMasterB s μ / (r : ℂ) ^ (3 : ℕ)) (Ioi 1)
  simpa only [div_eq_mul_inv, Pi.inv_apply] using (hA.mul (hi.inv hn)).add
    (hB.mul ((hi.pow 3).inv (fun r hr => pow_ne_zero 3 (hn r hr))))

/-- All source and reconstruction regularity is supplied by the explicit particular field. -/
theorem vvLaurentMaster_sourcedData (s μ : ℂ) (hs : s ≠ 0) (hμ : 2 - μ ≠ 0)
    (hres : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) :
    SourcedMasterData s μ (vvLaurentMaster s μ)
      (vvSrcTT s μ) (vvSrcTR s μ) (vvSrcRR s μ) (vvSrcT s μ) (vvSrcR s μ) (vvSrcTF s μ) (vvSrcL s μ) :=
  vvSourcedMasterData s μ hs hμ _ (vvLaurentMaster_contDiffOn s μ)
    (vvLaurentMaster_equation s μ hμ hres)

/-- The normalizable coefficient of the vector–vector response needs the two angular resolvents
`(2 − μ)⁻¹` and `(μ − (2s+1)(2s+2))⁻¹` only, and is otherwise polynomial. -/
theorem vvLaurentMasterA_eq (s μ : ℂ) (hμ : 2 - μ ≠ 0) :
    vvLaurentMasterA s μ = ((-18 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * μ + (-24 : ℂ) * s ^ (3 : ℕ) + (-6 : ℂ) * s ^ (4 : ℕ)) / (μ - (2 * s + 1) * (2 * s + 2)) := by
  unfold vvLaurentMasterA vvLaurentSourceMiddle vvLaurentMasterB
  field_simp
  ring

end
end RHTower.D4BMScalarStream
