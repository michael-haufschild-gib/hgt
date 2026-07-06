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
import GaloisForLFunctions.RHTower.XiDeck

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


private theorem enat_coe_dvd_of_ne_zero {a b : ℕ} (ha : a ≠ 0)
    (h : ((a : ℕ∞)) ∣ (b : ℕ∞)) : a ∣ b := by
  obtain ⟨c, hc⟩ := h
  have hane : (a : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hcne : c ≠ ⊤ := by
    rintro rfl
    have htop : (a : ℕ∞) * ⊤ = ⊤ := WithTop.mul_eq_top_iff.mpr (Or.inl ⟨hane, rfl⟩)
    rw [htop] at hc
    exact (WithTop.natCast_ne_top b) hc
  lift c to ℕ using hcne with d
  exact ⟨d, by exact_mod_cast hc⟩

theorem not_rhLadder_of_rightHalf_zero {ρ : ℂ} (hρ : ρ ∈ rightHalf) (hzero : xi ρ = 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = (m : ℕ∞)) (hm1 : 1 ≤ m) {k : ℕ} (hk : m < 2 ^ k) :
    ¬ RHLadder k := by
  intro hlad
  have hdvd := hlad ρ hρ hzero
  rw [hm] at hdvd
  have hnatdvd : (2 ^ k : ℕ) ∣ m := enat_coe_dvd_of_ne_zero (by positivity) hdvd
  have := Nat.le_of_dvd hm1 hnatdvd
  omega

theorem not_forall_rhLadder_of_rightHalf_zero {ρ : ℂ} (hρ : ρ ∈ rightHalf) (hzero : xi ρ = 0) :
    ¬ (∀ k, RHLadder k) := by
  intro hlad
  set m : ℕ := (analyticOrderAt xi ρ).toNat with hmdef
  have hm : analyticOrderAt xi ρ = (m : ℕ∞) := (ENat.coe_toNat (xi_orderAt_ne_top ρ)).symm
  have hordne : analyticOrderAt xi ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    exact hordne (by rw [hm, h0, Nat.cast_zero]))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt m (by norm_num : (1 : ℕ) < 2)
  exact not_rhLadder_of_rightHalf_zero hρ hzero hm hm1 hk (hlad k)


private theorem enat_two_dvd_iff {x : ℕ∞} (hx : x ≠ ⊤) :
    ((2 : ℕ) : ℕ∞) ∣ x ↔ 2 ∣ x.toNat := by
  have hcoe : x = ((x.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hx).symm
  constructor
  · intro h
    rw [hcoe] at h
    obtain ⟨c, hc⟩ := h
    have hane : ((2 : ℕ) : ℕ∞) ≠ 0 := by norm_num
    have hcne : c ≠ ⊤ := by
      rintro rfl
      have htop : ((2 : ℕ) : ℕ∞) * ⊤ = ⊤ := WithTop.mul_eq_top_iff.mpr (Or.inl ⟨hane, rfl⟩)
      rw [htop] at hc
      exact (WithTop.natCast_ne_top x.toNat) hc
    lift c to ℕ using hcne with d
    exact ⟨d, by exact_mod_cast hc⟩
  · intro h
    rw [hcoe]
    exact Nat.cast_dvd_cast h

/-- **`RHLadder 1` is exactly: every right-half ξ-zero has EVEN vanishing order.** This is the honest
content of the first non-trivial rung; equivalently (`rhLadder_iff_root`) that ξ admits an analytic
square root on `Re s > ½`. Even-order forcing via reflection (`analyticOrderAt_even_of_reflection`)
requires ξ to be symmetric about the zero, i.e. `∀ s, ξ (2ρ − s) = ξ s`; ξ has that symmetry only at
the functional-equation fixed point `ρ = ½` (`xi_central_ladder_two`), which lies OUTSIDE `rightHalf`.
A right-half zero is a reflection fixed point of no ξ-symmetry, and the conjugate pairing gives
`ord ρ = ord (conj ρ)` without doubling a single order, so no even-order forcing is available. This
rung is open. -/
theorem rhLadder_one_iff_even_order :
    RHLadder 1 ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → Even (analyticOrderAt xi ρ).toNat := by
  unfold RHLadder
  simp only [pow_one]
  refine forall₃_congr (fun ρ _ _ => ?_)
  rw [enat_two_dvd_iff (xi_orderAt_ne_top ρ), even_iff_two_dvd]


end RHTower
