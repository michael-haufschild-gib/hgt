import Mathlib

/-!
# The cyclic phase of a Gram label

For a Hermitian matrix `G` with nonzero off-diagonal entries, the normalized entries
`u_{rs} = G_{rs} / ‖G_{rs}‖` lie on the unit circle and satisfy `u_{sr} = u_{rs}⁻¹`.  The oriented
triangle phase

`Ω(r,s,t) = G_{rs} G_{st} G_{tr} / ‖G_{rs} G_{st} G_{tr}‖ = u_{rs} u_{st} u_{tr}`

is invariant under independent phase gauges at the vertices, and satisfies the tetrahedral Bianchi
identity

`Ω(1,2,3) Ω(0,2,3)⁻¹ Ω(0,1,3) Ω(0,1,2)⁻¹ = 1`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

variable {ι : Type*}

/-- The normalized phase of a Gram entry. -/
noncomputable def gramPhase (G : Matrix ι ι ℂ) (r s : ι) : ℂ := G r s / (‖G r s‖ : ℂ)

/-- The oriented cyclic phase of a Gram-labelled triangle. -/
noncomputable def cyclicPhase (G : Matrix ι ι ℂ) (r s t : ι) : ℂ :=
  (G r s * G s t * G t r) / (‖G r s * G s t * G t r‖ : ℂ)

theorem norm_gramPhase (G : Matrix ι ι ℂ) {r s : ι} (h : G r s ≠ 0) :
    ‖gramPhase G r s‖ = 1 := by
  rw [gramPhase, norm_div, Complex.norm_real, norm_norm]
  exact div_self (norm_ne_zero_iff.2 h)

theorem gramPhase_ne_zero (G : Matrix ι ι ℂ) {r s : ι} (h : G r s ≠ 0) :
    gramPhase G r s ≠ 0 := by
  intro hz
  have := norm_gramPhase G h
  rw [hz, norm_zero] at this
  exact zero_ne_one this

/-- On a Hermitian label, reversing an edge inverts its phase. -/
theorem gramPhase_swap {G : Matrix ι ι ℂ} (hH : G.IsHermitian) {r s : ι} (h : G r s ≠ 0) :
    gramPhase G s r = (gramPhase G r s)⁻¹ := by
  have hsr : G s r = starRingEnd ℂ (G r s) := by
    have := congrFun (congrFun hH s) r
    simpa [Matrix.conjTranspose_apply] using this.symm
  have hconj : gramPhase G s r = starRingEnd ℂ (gramPhase G r s) := by
    rw [gramPhase, gramPhase, hsr, map_div₀, Complex.conj_ofReal]
    congr 1
    simp
  rw [hconj, ← Complex.inv_eq_conj (norm_gramPhase G h)]

/-- The cyclic phase is the product of the three normalized edge phases. -/
theorem cyclicPhase_eq_prod (G : Matrix ι ι ℂ) {r s t : ι} (hrs : G r s ≠ 0) (hst : G s t ≠ 0)
    (htr : G t r ≠ 0) :
    cyclicPhase G r s t = gramPhase G r s * gramPhase G s t * gramPhase G t r := by
  rw [cyclicPhase, gramPhase, gramPhase, gramPhase, norm_mul, norm_mul]
  push_cast
  field_simp

theorem cyclicPhase_ne_zero (G : Matrix ι ι ℂ) {r s t : ι} (hrs : G r s ≠ 0) (hst : G s t ≠ 0)
    (htr : G t r ≠ 0) : cyclicPhase G r s t ≠ 0 := by
  rw [cyclicPhase_eq_prod G hrs hst htr]
  exact mul_ne_zero (mul_ne_zero (gramPhase_ne_zero G hrs) (gramPhase_ne_zero G hst))
    (gramPhase_ne_zero G htr)

/-! ## Vertex phase gauges -/

/-- The Gram label produced by independent unit phase changes at the vertices. -/
noncomputable def gramGauge (lam : ι → ℂ) (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun r s => starRingEnd ℂ (lam r) * lam s * G r s

/-- **Gauge invariance of the cyclic phase.** -/
theorem cyclicPhase_gramGauge {lam : ι → ℂ} (hlam : ∀ r, ‖lam r‖ = 1) (G : Matrix ι ι ℂ)
    (r s t : ι) : cyclicPhase (gramGauge lam G) r s t = cyclicPhase G r s t := by
  have hunit : ∀ x : ι, starRingEnd ℂ (lam x) * lam x = 1 := by
    intro x
    have h1 : ‖lam x‖ = 1 := hlam x
    have hne : lam x ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at h1
      exact zero_ne_one h1
    rw [← Complex.inv_eq_conj h1, inv_mul_cancel₀ hne]
  have hprod : gramGauge lam G r s * gramGauge lam G s t * gramGauge lam G t r =
      G r s * G s t * G t r := by
    simp only [gramGauge]
    calc starRingEnd ℂ (lam r) * lam s * G r s * (starRingEnd ℂ (lam s) * lam t * G s t) *
          (starRingEnd ℂ (lam t) * lam r * G t r)
        = (starRingEnd ℂ (lam r) * lam r) * (starRingEnd ℂ (lam s) * lam s) *
            (starRingEnd ℂ (lam t) * lam t) * (G r s * G s t * G t r) := by ring
      _ = G r s * G s t * G t r := by rw [hunit r, hunit s, hunit t]; ring
  rw [cyclicPhase, cyclicPhase, hprod]

/-! ## The tetrahedral Bianchi identity -/

/-- **Bianchi identity for the cyclic phase.**  On a Hermitian Gram label with nonzero edges, the
alternating product of the four triangle phases of a tetrahedron is one. -/
theorem cyclicPhase_bianchi {G : Matrix ι ι ℂ} (hH : G.IsHermitian) {x₀ x₁ x₂ x₃ : ι}
    (h01 : G x₀ x₁ ≠ 0) (h02 : G x₀ x₂ ≠ 0) (h03 : G x₀ x₃ ≠ 0)
    (h12 : G x₁ x₂ ≠ 0) (h13 : G x₁ x₃ ≠ 0) (h23 : G x₂ x₃ ≠ 0) :
    cyclicPhase G x₁ x₂ x₃ * (cyclicPhase G x₀ x₂ x₃)⁻¹ * cyclicPhase G x₀ x₁ x₃ *
        (cyclicPhase G x₀ x₁ x₂)⁻¹ = 1 := by
  have hs : ∀ {r s : ι}, G r s ≠ 0 → G s r ≠ 0 := by
    intro r s h hz
    apply h
    have := congrFun (congrFun hH r) s
    rw [Matrix.conjTranspose_apply, hz] at this
    simpa using this.symm
  have h10 := hs h01
  have h20 := hs h02
  have h30 := hs h03
  have h21 := hs h12
  have h31 := hs h13
  have h32 := hs h23
  rw [cyclicPhase_eq_prod G h12 h23 h31, cyclicPhase_eq_prod G h02 h23 h30,
    cyclicPhase_eq_prod G h01 h13 h30, cyclicPhase_eq_prod G h01 h12 h20,
    gramPhase_swap hH h13, gramPhase_swap hH h03, gramPhase_swap hH h02]
  have n01 := gramPhase_ne_zero G h01
  have n02 := gramPhase_ne_zero G h02
  have n03 := gramPhase_ne_zero G h03
  have n12 := gramPhase_ne_zero G h12
  have n13 := gramPhase_ne_zero G h13
  have n23 := gramPhase_ne_zero G h23
  field_simp

end GaloisForLFunctions.HTGeometry.Interfinity
