/-
Attack-as-false on the weight-mismatch parity invariant (doc 89, route b).

The proposed moonshot: a ℤ₂-parity of the zero-quadruple `Q(ρ) = {ρ, 1−ρ, ρ̄, 1−ρ̄}` that is even iff
`Re ρ = ½`. It is REFUTED here. The two defining symmetries — functional equation `s ↦ 1−s` and Schwarz
reflection `s ↦ s̄` — each act on `Q` as a product of two transpositions (the Klein four-group, all EVEN
permutations); there is no 4-cycle. Equivalently, all four points carry EQUAL ξ-order, so the total
tower weight is `4·ord(ρ)` — ℤ₂-trivial for every `ρ`, on or off the line. The conjectured biconditional
fails in the off-line direction. The genuine on-line/off-line distinction is τ-fixedness under the
antiholomorphic involution `τ = lineReflect`, whose fixed locus is the critical line — but that is not a
mod-2 orbit invariant, so no parity obstruction exists at the single-zero-quadruple level.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.WindowRelation

open Complex

namespace RHTower

/-- **The four symmetric images of a ξ-zero all have equal order.** Functional equation
(`xi_orderAt_one_sub`) and Schwarz reflection (`xi_orderAt_conj`) give
`ord(ρ) = ord(1−ρ) = ord(ρ̄) = ord(1−ρ̄)`. -/
theorem xi_orderAt_quadruple_eq (ρ : ℂ) :
    analyticOrderAt xi (1 - ρ) = analyticOrderAt xi ρ ∧
    analyticOrderAt xi ((starRingEnd ℂ) ρ) = analyticOrderAt xi ρ ∧
    analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) = analyticOrderAt xi ρ := by
  refine ⟨xi_orderAt_one_sub ρ, xi_orderAt_conj ρ, ?_⟩
  rw [xi_orderAt_one_sub, xi_orderAt_conj]

/-- **The weight-mismatch parity invariant is REFUTED.** For a ξ-zero `ρ` of finite order `m`, the
total tower weight over its symmetric quadruple `{ρ, 1−ρ, ρ̄, 1−ρ̄}` equals `4m` — hence its ℤ₂-class is
`0` (even) for EVERY `ρ`, whether on or off the critical line. The conjectured biconditional
"parity even ⟺ Re ρ = ½" is false: the off-line direction also yields even, so the invariant carries
no information distinguishing on-line from off-line zeros. -/
theorem quadruple_weight_parity_refuted {ρ : ℂ} {m : ℕ}
    (hm : analyticOrderAt xi ρ = (m : ℕ∞)) :
    analyticOrderAt xi (1 - ρ) = (m : ℕ∞)
      ∧ analyticOrderAt xi ((starRingEnd ℂ) ρ) = (m : ℕ∞)
      ∧ analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) = (m : ℕ∞)
      ∧ Even (m + m + m + m) := by
  obtain ⟨h1, h2, h3⟩ := xi_orderAt_quadruple_eq ρ
  refine ⟨h1.trans hm, h2.trans hm, h3.trans hm, ?_⟩
  exact ⟨m + m, by ring⟩


/-- **The genuine distinction is τ-fixedness, not parity.** The antiholomorphic involution
`τ = lineReflect : s ↦ 1 − s̄` (= functional equation ∘ Schwarz) has fixed locus exactly the critical
line: `τ(ρ) = ρ ↔ Re ρ = ½`. RH ⟺ every ξ-zero is τ-fixed — but "τ-fixed" is not a mod-2 orbit
invariant, so no parity obstruction exists at the quadruple level. -/
theorem lineReflect_fixed_iff (ρ : ℂ) : lineReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  rw [lineReflect]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

end RHTower
