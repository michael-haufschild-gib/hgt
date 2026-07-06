/-
The mirror symmetry of the incidence carrier across the critical line, and what it
cannot decide.

Line reflection `s ↦ 1 − s̄` fixes the critical line and swaps the lateral edges at
abscissae `σ` and `1−σ`.  For a pencil whose members are equivariant under it (the
composite of the even functional equation and Schwarz reality), the incidence value at
the mirror point is the conjugate of the value at the point.  Two consequences, one on
each side of a dichotomy.

Blindness of mirror-symmetric certificates: the imaginary part is odd under reflection,
so band events on the `σ`-edge and on the `(1−σ)`-edge biject at the SAME heights, with
orientations reversed — an event family pooled over a mirror pair of edges is doubled and
its flux pairing exists unconditionally.  A parity certificate extracted from a
mirror-symmetric contour therefore carries no information: the functional equation pays
it in full, whatever the zero configuration.

Non-derivability on a single edge: the equivariance class does not determine the
endpoint-orientation datum.  Two entire carriers in the same class — both even under
`s ↦ 1−s`, both Schwarz-real — realise agreement and disagreement of the endpoint
orientations on the SAME edge, so no argument from the symmetry class alone can decide
the datum; it is a strictly finer boundary quantity.

The concrete carrier `completedGN` is equivariant on the strip, so its own pencil is
mirror-blind; the finite Euler head anchor is NOT equivariant — inserting it is exactly
what breaks the mirror symmetry of the anchored pencil.
-/
import GaloisForLFunctions.RHTower.EdgeEventLedger

open Complex Metric

namespace RHTower

/-! ### The reflection identity -/

/-- Line reflection `s ↦ 1 − s̄` swaps the lateral edges: the mirror edge point at
abscissa `1−σ` and height `τ` is the reflection of the edge point at `σ` and `τ`. -/
theorem stripPt_mirror (σ τ : ℝ) :
    stripPt (1 - σ) τ = 1 - (starRingEnd ℂ) (stripPt σ τ) := by
  unfold stripPt
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The incidence value conjugates under line reflection.**  If both pencil members are
equivariant under `s ↦ 1 − s̄` at `s` — the composite of the even functional equation and
Schwarz reality — then the incidence value at the reflected point is the conjugate of the
value at `s`. -/
theorem incidence_lineReflection {Λ₁ Λ₂ : ℂ → ℂ} {s : ℂ}
    (h1 : Λ₁ (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (Λ₁ s))
    (h2 : Λ₂ (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (Λ₂ s)) :
    incidence Λ₁ Λ₂ (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (incidence Λ₁ Λ₂ s) := by
  unfold incidence
  rw [h1, h2, map_div₀, map_neg]

/-- The imaginary part of the incidence carrier is ODD across the critical line: at the
mirror edge point it is the negative of its value at the edge point. -/
theorem im_incidence_mirror_edge {Λ₁ Λ₂ : ℂ → ℂ} {σ τ : ℝ}
    (h1 : Λ₁ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₁ (stripPt σ τ)))
    (h2 : Λ₂ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₂ (stripPt σ τ))) :
    (incidence Λ₁ Λ₂ (stripPt (1 - σ) τ)).im = -(incidence Λ₁ Λ₂ (stripPt σ τ)).im := by
  rw [stripPt_mirror, incidence_lineReflection h1 h2, Complex.conj_im]

/-- **Band events biject across the mirror** at the same heights: the incidence value is
real on the `σ`-edge exactly where it is real on the `(1−σ)`-edge. -/
theorem bandEvent_mirror_iff {Λ₁ Λ₂ : ℂ → ℂ} {σ τ : ℝ}
    (h1 : Λ₁ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₁ (stripPt σ τ)))
    (h2 : Λ₂ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₂ (stripPt σ τ))) :
    (incidence Λ₁ Λ₂ (stripPt (1 - σ) τ)).im = 0 ↔
      (incidence Λ₁ Λ₂ (stripPt σ τ)).im = 0 := by
  rw [im_incidence_mirror_edge h1 h2, neg_eq_zero]

/-- **Orientations reverse across the mirror**: the incidence value points up on the
mirror edge exactly where it points down on the edge. -/
theorem mirror_orientation_reversal {Λ₁ Λ₂ : ℂ → ℂ} {σ τ : ℝ}
    (h1 : Λ₁ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₁ (stripPt σ τ)))
    (h2 : Λ₂ (1 - (starRingEnd ℂ) (stripPt σ τ)) = (starRingEnd ℂ) (Λ₂ (stripPt σ τ))) :
    0 < (incidence Λ₁ Λ₂ (stripPt (1 - σ) τ)).im ↔
      (incidence Λ₁ Λ₂ (stripPt σ τ)).im < 0 := by
  rw [im_incidence_mirror_edge h1 h2]
  exact neg_pos

/-! ### The blindness horn: mirror-pooled certificates are free -/

/-- **A mirror-pooled event family is doubled and its pairing is free.**  Any `n` band
events on the `σ`-edge reflect to `n` band events on the `(1−σ)`-edge at the same
heights, and the pooled event list of the mirror pair carries paired flux
unconditionally: the functional equation supplies both the partner events and the
pairing, whatever the zero configuration.  A parity certificate over a mirror-symmetric
pair of edges asserts nothing. -/
theorem mirror_pool_fluxPaired {Λ₁ Λ₂ : ℂ → ℂ} {σ : ℝ} {n : ℕ} {e : Fin n → ℝ}
    (h1 : ∀ i, Λ₁ (1 - (starRingEnd ℂ) (stripPt σ (e i))) =
      (starRingEnd ℂ) (Λ₁ (stripPt σ (e i))))
    (h2 : ∀ i, Λ₂ (1 - (starRingEnd ℂ) (stripPt σ (e i))) =
      (starRingEnd ℂ) (Λ₂ (stripPt σ (e i))))
    (hev : ∀ i, (incidence Λ₁ Λ₂ (stripPt σ (e i))).im = 0) :
    (∀ i, (incidence Λ₁ Λ₂ (stripPt (1 - σ) (e i))).im = 0) ∧
      LedgerFluxPaired (List.replicate (n + n) 1) :=
  ⟨fun i => (bandEvent_mirror_iff (h1 i) (h2 i)).mpr (hev i),
    ledgerFluxPaired_replicate_one (nonempty_bandEdgePairing_of_even ⟨n, by ring⟩)⟩

/-! ### The concrete carrier is equivariant; its own pencil is mirror-blind -/

/-- The concrete carrier `completedGN` is line-reflection equivariant on the strip: the
even functional equation composed with Schwarz reality. -/
theorem completedGN_lineReflection {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedGN N (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (completedGN N s) := by
  have hconj0 : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  have hconj1 : ((starRingEnd ℂ) s).re < 1 := by rwa [Complex.conj_re]
  rw [completedGN_one_sub hconj0 hconj1, completedGN_conj]

/-- **The trivial pencil of the concrete carrier is mirror-blind on the strip**: the
imaginary part of its incidence value is odd across the critical line, so its band
events and orientations on the two mirror edges determine each other with no arithmetic
input.  The finite Euler head anchor is what breaks this symmetry in the anchored
pencil. -/
theorem completedGN_im_mirror_edge {N : ℕ} {σ τ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (incidence (fun _ => (1 : ℂ)) (completedGN N) (stripPt (1 - σ) τ)).im =
      -(incidence (fun _ => (1 : ℂ)) (completedGN N) (stripPt σ τ)).im := by
  refine im_incidence_mirror_edge (by simp) ?_
  exact completedGN_lineReflection (by rwa [stripPt_re]) (by rwa [stripPt_re])

/-! ### The non-derivability horn: the symmetry class does not decide the datum -/

/-- The imaginary part of `cosh` on the vertical decomposition. -/
theorem cosh_add_mul_I_im (x y : ℝ) :
    (Complex.cosh ((x : ℂ) + (y : ℂ) * I)).im = Real.sinh x * Real.sin y := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_sin]
  simp [Complex.sinh_ofReal_re, Complex.sin_ofReal_re]

/-- **The endpoint-orientation datum is not determined by the symmetry class.**  There
are two entire carriers in the same equivariance class — both even under `s ↦ 1−s`, both
Schwarz-real — and one edge on which the first realises endpoint-orientation agreement
and the second realises disagreement, all four endpoint values off the real axis.  No
derivation from the functional equation and reality alone can decide the datum: it is a
strictly finer boundary quantity than the symmetry class. -/
theorem hagree_not_determined_by_symmetry :
    ∃ (Λ₁ Λ Λ' : ℂ → ℂ) (σ a b : ℝ), a < b ∧
      (∀ s, Λ₁ (1 - s) = Λ₁ s) ∧
      (∀ s, Λ₁ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Λ₁ s)) ∧
      (∀ s, Λ (1 - s) = Λ s) ∧
      (∀ s, Λ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Λ s)) ∧
      (∀ s, Λ' (1 - s) = Λ' s) ∧
      (∀ s, Λ' ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Λ' s)) ∧
      Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (incidence Λ₁ Λ (stripPt σ a)).im ≠ 0 ∧
      (incidence Λ₁ Λ (stripPt σ b)).im ≠ 0 ∧
      (incidence Λ₁ Λ' (stripPt σ a)).im ≠ 0 ∧
      (incidence Λ₁ Λ' (stripPt σ b)).im ≠ 0 ∧
      (0 < (incidence Λ₁ Λ (stripPt σ a)).im ↔
        0 < (incidence Λ₁ Λ (stripPt σ b)).im) ∧
      ¬(0 < (incidence Λ₁ Λ' (stripPt σ a)).im ↔
        0 < (incidence Λ₁ Λ' (stripPt σ b)).im) := by
  -- the two carriers: cosh at horizontal frequencies 1 and 2 about the critical point
  have hval1 : ∀ τ : ℝ,
      incidence (fun _ => (1 : ℂ)) (fun s => -Complex.cosh (s - ((1/2 : ℝ) : ℂ)))
        (stripPt (3/4) τ) =
      Complex.cosh (((1/4 : ℝ) : ℂ) + (τ : ℂ) * I) := by
    intro τ
    have harg : stripPt (3/4) τ - ((1/2 : ℝ) : ℂ) = ((1/4 : ℝ) : ℂ) + (τ : ℂ) * I := by
      unfold stripPt
      push_cast
      ring
    simp only [incidence, neg_neg, div_one, harg]
  have hval2 : ∀ τ : ℝ,
      incidence (fun _ => (1 : ℂ))
        (fun s => -Complex.cosh (((2 : ℝ) : ℂ) * (s - ((1/2 : ℝ) : ℂ))))
        (stripPt (3/4) τ) =
      Complex.cosh (((1/2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I) := by
    intro τ
    have harg : ((2 : ℝ) : ℂ) * (stripPt (3/4) τ - ((1/2 : ℝ) : ℂ)) =
        ((1/2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I := by
      unfold stripPt
      push_cast
      ring
    simp only [incidence, neg_neg, div_one, harg]
  -- the four endpoint signs
  have hsinh1 : 0 < Real.sinh (1/4) := Real.sinh_pos_iff.mpr (by norm_num)
  have hsinh2 : 0 < Real.sinh (1/2) := Real.sinh_pos_iff.mpr (by norm_num)
  have hsina : 0 < Real.sin (Real.pi/3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsinb : 0 < Real.sin (2*Real.pi/3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsina2 : 0 < Real.sin (2 * (Real.pi/3)) := by
    have hrw : 2 * (Real.pi/3) = 2*Real.pi/3 := by ring
    rw [hrw]
    exact hsinb
  have hsinb2 : Real.sin (2 * (2*Real.pi/3)) < 0 := by
    have hrw : 2 * (2*Real.pi/3) = -(2*Real.pi/3) + 2*Real.pi := by ring
    rw [hrw, Real.sin_add_two_pi, Real.sin_neg]
    linarith
  refine ⟨fun _ => 1, fun s => -Complex.cosh (s - ((1/2 : ℝ) : ℂ)),
    fun s => -Complex.cosh (((2 : ℝ) : ℂ) * (s - ((1/2 : ℝ) : ℂ))),
    3/4, Real.pi/3, 2*Real.pi/3,
    by linarith [Real.pi_pos], fun s => rfl, fun s => by simp, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    show -Complex.cosh (1 - s - ((1/2 : ℝ) : ℂ)) = -Complex.cosh (s - ((1/2 : ℝ) : ℂ))
    rw [show (1 : ℂ) - s - ((1/2 : ℝ) : ℂ) = -(s - ((1/2 : ℝ) : ℂ)) by push_cast; ring,
      Complex.cosh_neg]
  · intro s
    show -Complex.cosh ((starRingEnd ℂ) s - ((1/2 : ℝ) : ℂ)) =
      (starRingEnd ℂ) (-Complex.cosh (s - ((1/2 : ℝ) : ℂ)))
    rw [map_neg, ← Complex.cosh_conj, map_sub, Complex.conj_ofReal]
  · intro s
    show -Complex.cosh (((2 : ℝ) : ℂ) * (1 - s - ((1/2 : ℝ) : ℂ))) =
      -Complex.cosh (((2 : ℝ) : ℂ) * (s - ((1/2 : ℝ) : ℂ)))
    rw [show ((2 : ℝ) : ℂ) * (1 - s - ((1/2 : ℝ) : ℂ)) =
        -(((2 : ℝ) : ℂ) * (s - ((1/2 : ℝ) : ℂ))) by push_cast; ring,
      Complex.cosh_neg]
  · intro s
    show -Complex.cosh (((2 : ℝ) : ℂ) * ((starRingEnd ℂ) s - ((1/2 : ℝ) : ℂ))) =
      (starRingEnd ℂ) (-Complex.cosh (((2 : ℝ) : ℂ) * (s - ((1/2 : ℝ) : ℂ))))
    rw [map_neg, ← Complex.cosh_conj, map_mul, map_sub, Complex.conj_ofReal,
      Complex.conj_ofReal]
  · exact (Complex.differentiable_cosh.comp (differentiable_id.sub_const _)).neg
  · exact (Complex.differentiable_cosh.comp
      ((differentiable_id.sub_const _).const_mul _)).neg
  · rw [hval1, cosh_add_mul_I_im]
    exact ne_of_gt (mul_pos hsinh1 hsina)
  · rw [hval1, cosh_add_mul_I_im]
    exact ne_of_gt (mul_pos hsinh1 hsinb)
  · rw [hval2, cosh_add_mul_I_im]
    exact ne_of_gt (mul_pos hsinh2 hsina2)
  · rw [hval2, cosh_add_mul_I_im]
    exact ne_of_lt (mul_neg_of_pos_of_neg hsinh2 hsinb2)
  · simp only [hval1, cosh_add_mul_I_im]
    exact iff_of_true (mul_pos hsinh1 hsina) (mul_pos hsinh1 hsinb)
  · simp only [hval2, cosh_add_mul_I_im]
    intro h
    have hb := h.mp (mul_pos hsinh2 hsina2)
    have hneg := mul_neg_of_pos_of_neg hsinh2 hsinb2
    linarith

end RHTower
