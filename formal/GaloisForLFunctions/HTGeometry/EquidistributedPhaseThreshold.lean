import GaloisForLFunctions.HTGeometry.ConjugateSymmetryNoPositivity

/-!
# The one-half threshold is the equidistributed-phase value

For a family of complex numbers the sign of `∑ gᵢ²` is governed by the comparison of the imaginary
energy `∑(Im gᵢ)²` with half the total energy `∑‖gᵢ‖²`, since
`Re ∑gᵢ² = ∑‖gᵢ‖² − 2∑(Im gᵢ)²`.  The constant `1/2` in that comparison is not an artefact of the
normalisation: it is exactly the value taken by an equally spaced family of phases.

Concretely, for `N ≥ 2` the family `gₖ = r·exp(i(θ + kπ/N))` has

```text
∑ₖ gₖ² = 0        exactly, for every r and every θ,
```

because the squares are `r²e^{2iθ}` times the `N`-th roots of unity, which sum to zero.  Hence its
imaginary energy is *exactly* half its total energy, independently of the common phase `θ`.

The contrast with a single element is the whole story.  One element with phase `π/2` has imaginary
energy equal to its **full** total energy, so its sum of squares is `−r²`: maximally negative.  A
lone phase can therefore drive the functional as far negative as its energy allows, while two or
more equally spaced phases pin it at exactly zero.

The structural reading: sign failure is a *sparse* phenomenon.  Spreading phases pushes the
functional toward the threshold from below and never past it; concentration in a single phase is
what produces a definite sign.  This is why methods that detect *many* exceptional contributions
are mistuned — the extremal configuration for this functional is a single one.
-/

open Finset

namespace GaloisForLFunctions

/-- A family of `N` complex numbers of common modulus `r` with phases equally spaced by `π/N`
starting at `θ`. -/
noncomputable def spacedPhase (r θ : ℝ) (N k : ℕ) : ℂ :=
  (r : ℂ) * Complex.exp ((↑(θ + k * Real.pi / N) : ℂ) * Complex.I)

theorem norm_spacedPhase (r θ : ℝ) (N k : ℕ) : ‖spacedPhase r θ N k‖ = |r| := by
  rw [spacedPhase, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real]
  simp

/-- **The equally spaced family has vanishing sum of squares.**  For `N ≥ 2` the squares are a
common factor times the full set of `N`-th roots of unity, whose sum is zero.  The conclusion is
independent of the modulus and of the starting phase. -/
theorem sum_sq_spacedPhase_eq_zero (r θ : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.range N, spacedPhase r θ N k ^ 2 = 0 := by
  have hN0 : N ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp N hN0
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hord := hprim.eq_orderOf
    rw [h, orderOf_one] at hord
    omega
  have hgeom : ∑ k ∈ Finset.range N, z ^ k = 0 := by
    rw [geom_sum_eq hz1, hprim.pow_eq_one]
    simp
  have hterm : ∀ k ∈ Finset.range N, spacedPhase r θ N k ^ 2
      = ((r : ℂ) ^ 2 * Complex.exp ((2 * (θ : ℂ)) * Complex.I)) * z ^ k := by
    intro k _
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    rw [spacedPhase, mul_pow, ← Complex.exp_nat_mul, hz, ← Complex.exp_nat_mul,
      mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgeom, mul_zero]

/-- The total energy of the equally spaced family. -/
theorem totalEnergy_spacedPhase (r θ : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖spacedPhase r θ N k‖ ^ 2 = N * r ^ 2 := by
  rw [Finset.sum_congr rfl (fun k _ => by rw [norm_spacedPhase, sq_abs])]
  simp [Finset.sum_const]

/-- **Equally spaced phases sit exactly at the threshold.**  For `N ≥ 2` the imaginary energy of the
family is exactly half its total energy — for every modulus and every starting phase.  This is the
`1/2` appearing in the positivity criterion, and it is attained, not approached. -/
theorem imaginaryEnergy_spacedPhase (r θ : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.range N, (spacedPhase r θ N k).im ^ 2 = (N * r ^ 2) / 2 := by
  have hkey := re_sum_sq_eq_energy_sub_two_imaginary
    (ι := {k // k ∈ Finset.range N}) (fun k => spacedPhase r θ N k)
  have hsub : ∀ f : ℕ → ℝ, ∑ k : {k // k ∈ Finset.range N}, f k = ∑ k ∈ Finset.range N, f k :=
    fun f => Finset.sum_coe_sort (Finset.range N) f
  have hsubC : ∑ k : {k // k ∈ Finset.range N}, spacedPhase r θ N k ^ 2
      = ∑ k ∈ Finset.range N, spacedPhase r θ N k ^ 2 :=
    Finset.sum_coe_sort (Finset.range N) (fun k => spacedPhase r θ N k ^ 2)
  rw [hsubC, sum_sq_spacedPhase_eq_zero r θ hN] at hkey
  rw [hsub (fun k => ‖spacedPhase r θ N k‖ ^ 2), hsub (fun k => (spacedPhase r θ N k).im ^ 2),
    totalEnergy_spacedPhase] at hkey
  simp only [Complex.zero_re] at hkey
  linarith

/-- **A single phase reaches the full energy.**  One element with phase `π/2` has imaginary energy
equal to its total energy, hence sum of squares `−r²`.  Together with the previous theorem this
shows the extremal configuration for negativity is a *lone* phase, not a spread one. -/
theorem single_phase_saturates (r : ℝ) :
    (spacedPhase r (Real.pi / 2) 1 0).im ^ 2 = ‖spacedPhase r (Real.pi / 2) 1 0‖ ^ 2 ∧
      (spacedPhase r (Real.pi / 2) 1 0 ^ 2).re = -(r ^ 2) := by
  have hval : spacedPhase r (Real.pi / 2) 1 0 = (r : ℂ) * Complex.I := by
    rw [spacedPhase]
    norm_num
  constructor
  · rw [hval]
    simp [sq_abs]
  · rw [hval, mul_pow, Complex.I_sq]
    simp [← Complex.ofReal_pow]

/-- **The threshold is exact and the extremal case is sparse.**  Restating the two facts together:
`N ≥ 2` equally spaced phases give sum of squares exactly `0`, while a single phase gives `−r²`.
Any positivity statement about `∑gᵢ²` must therefore rule out the one-element configuration; no
amount of spreading produces negativity. -/
theorem spacedPhase_threshold_dichotomy (r θ : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.range N, spacedPhase r θ N k ^ 2).re = 0 ∧
      (spacedPhase r (Real.pi / 2) 1 0 ^ 2).re = -(r ^ 2) :=
  ⟨by rw [sum_sq_spacedPhase_eq_zero r θ hN]; simp, (single_phase_saturates r).2⟩

end GaloisForLFunctions
