import GaloisForLFunctions.RHTower.DeningerDivisorFlow

/-!
# The displacement Ward identity for Deninger divisor gauges

The corpus isolates the Deninger lane's single open clause twice, in complementary axioms: on the
source/assembly model the debt is positivity with equivariance free, and on the divisor model the
debt is Frobenius/Hodge-star commutation with positivity free
(`DeningerArithmeticOrientedHodge`).  This file proves that the complementarity is not an accident
of two constructions but an exact identity valid for **every** gauge at once.

## The identity

For every anti-linear map `σ` on `H¹ = XiZeroCopy →₀ ℂ` — with no axioms at all: not injective,
not `σ² = -1`, arbitrary block-mixing — the cup pairing of the Frobenius commutation defect
against a divisor basis vector is proportional to the cup pairing of the gauge itself, and the
diagonal proportionality factor is exactly the critical-line displacement `1 - ρ - conj ρ
= -2 (Re ρ - 1/2)`:

`ψ(δ_q, [θ, σ] δ_r) = (λ_{Rq} - conj λ_r) · ψ(δ_q, σ δ_r)`.

For a linear gauge the factor is `λ_{Rq} - λ_r`, with diagonal `1 - 2ρ`.

## Consequences (all unconditional)

* **Per-zero purity from one Gram entry** — if some anti-linear gauge commutes with Frobenius at
  the single basis vector `δ_q` and its cup diagonal there is nonzero, then `Re ρ_q = 1/2`.  No
  positivity, no `σ² = -1`, no global package.
* **Equivariant invisibility** — every Frobenius-commuting anti-linear gauge has vanishing cup
  diagonal at every off-line zero: off-line zeros are diagonally invisible to the entire
  equivariant anti-linear gauge class.
* **Total linear blindness** — since `1/2` is not a Xi zero, every Frobenius-commuting *linear*
  gauge has vanishing cup diagonal at *every* zero.  The visibility locus of linear gauges is the
  point `1/2`; of anti-linear gauges, exactly the critical line.
* **The reflect gauge is the positivity-extremal point** — `σ_R x = conj ∘ x ∘ R` has cup
  diagonal identically `1` and commutation defect concentrated on one coefficient of size exactly
  `2 |Re ρ - 1/2|` per zero.
* **RH as a gauge statement** — `RiemannHypothesis` holds iff some anti-linear gauge commutes
  with Frobenius on basis vectors while its cup diagonal never vanishes.  This equivalence is a
  re-encoding and is labelled as such; the unconditional content is the preceding items.

No zero location, positivity premise, or RH assumption enters any proof except where
`RiemannHypothesis` is itself the stated hypothesis or conclusion.
-/

noncomputable section

open Complex

namespace RHTower

/-- Cup trace against a Frobenius image: `ψ(δ_q, θ y) = λ_{Rq} · ψ(δ_q, y)`, because the cup
functional `ψ(δ_q, ·)` reads only the reflected coefficient, on which the diagonal Frobenius acts
by the scalar `λ_{Rq}`. -/
theorem deningerDivisorCupTrace_single_theta (q : XiZeroCopy) (y : DeningerDivisorH1) :
    deningerDivisorCupTrace (Finsupp.single q 1) (deningerDivisorTheta y) =
      deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) *
        deningerDivisorCupTrace (Finsupp.single q 1) y := by
  rw [deningerDivisorCupTrace_single_left, deningerDivisorCupTrace_single_left]
  simp only [deningerDivisorTheta, finsuppDiagonal_apply]
  ring

/-- **The displacement Ward identity (anti-linear gauges).**  For every anti-linear `σ` — with no
axioms whatsoever — the cup pairing of the Frobenius commutation defect against `δ_q` is the cup
pairing of the gauge, scaled by `λ_{Rq} - conj λ_r`.  On the diagonal `r = q` the factor is
`1 - ρ - conj ρ = -2 (Re ρ - 1/2)`: the critical-line displacement. -/
theorem deningerDivisor_antilinearGauge_ward
    (σ : DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1) (q r : XiZeroCopy) (c : ℂ) :
    deningerDivisorCupTrace (Finsupp.single q 1)
        (deningerDivisorTheta (σ (Finsupp.single r c)) -
          σ (deningerDivisorTheta (Finsupp.single r c))) =
      (deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) -
          (starRingEnd ℂ) (deningerDivisorThetaEigen r)) *
        deningerDivisorCupTrace (Finsupp.single q 1) (σ (Finsupp.single r c)) := by
  have hθr : deningerDivisorTheta (Finsupp.single r c) =
      deningerDivisorThetaEigen r • Finsupp.single r c := by
    rw [deningerDivisorTheta_single, Finsupp.smul_single, smul_eq_mul]
  rw [map_sub, hθr, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul,
    deningerDivisorCupTrace_single_theta]
  ring

/-- **The displacement Ward identity (linear gauges).**  For every linear `T` the factor is
`λ_{Rq} - λ_r`, with diagonal `1 - 2ρ`. -/
theorem deningerDivisor_linearGauge_ward
    (T : Module.End ℂ DeningerDivisorH1) (q r : XiZeroCopy) (c : ℂ) :
    deningerDivisorCupTrace (Finsupp.single q 1)
        (deningerDivisorTheta (T (Finsupp.single r c)) -
          T (deningerDivisorTheta (Finsupp.single r c))) =
      (deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) -
          deningerDivisorThetaEigen r) *
        deningerDivisorCupTrace (Finsupp.single q 1) (T (Finsupp.single r c)) := by
  have hθr : deningerDivisorTheta (Finsupp.single r c) =
      deningerDivisorThetaEigen r • Finsupp.single r c := by
    rw [deningerDivisorTheta_single, Finsupp.smul_single, smul_eq_mul]
  rw [map_sub, hθr, map_smul, map_smul, smul_eq_mul,
    deningerDivisorCupTrace_single_theta]
  ring

/-- **Per-zero purity from a single Gram entry.**  If an anti-linear gauge commutes with Frobenius
at the one basis vector `δ_q` and its cup diagonal there is nonzero, the underlying Xi zero lies
on the critical line.  No positivity, no `σ² = -1`, no nondegeneracy, no global package. -/
theorem deningerDivisorThetaEigen_re_eq_half_of_antilinearGauge
    (σ : DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1) (q : XiZeroCopy)
    (hcomm : deningerDivisorTheta (σ (Finsupp.single q 1)) =
      σ (deningerDivisorTheta (Finsupp.single q 1)))
    (hdiag : deningerDivisorCupTrace (Finsupp.single q 1)
      (σ (Finsupp.single q 1)) ≠ 0) :
    (deningerDivisorThetaEigen q).re = 1 / 2 := by
  have hward := deningerDivisor_antilinearGauge_ward σ q q 1
  rw [hcomm, sub_self, map_zero] at hward
  have hfactor :
      deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) -
        (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 0 := by
    rcases mul_eq_zero.mp hward.symm with h | h
    · exact h
    · exact absurd h hdiag
  have hsum := deningerDivisorThetaEigen_add_reflect q
  have hconj :
      deningerDivisorThetaEigen q +
        (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 1 := by
    have hRq : deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
        (starRingEnd ℂ) (deningerDivisorThetaEigen q) := sub_eq_zero.mp hfactor
    rw [← hRq]
    exact hsum
  have hre := congrArg Complex.re hconj
  simp only [add_re, conj_re, one_re] at hre
  linarith

/-- **Equivariant invisibility.**  Every anti-linear gauge that commutes with Frobenius at `δ_q`
has vanishing cup diagonal there whenever the zero is off the critical line: off-line zeros are
diagonally invisible to the entire equivariant anti-linear gauge class. -/
theorem deningerDivisor_antilinearGauge_diag_eq_zero_of_offline
    (σ : DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1) (q : XiZeroCopy)
    (hoff : (deningerDivisorThetaEigen q).re ≠ 1 / 2)
    (hcomm : deningerDivisorTheta (σ (Finsupp.single q 1)) =
      σ (deningerDivisorTheta (Finsupp.single q 1))) :
    deningerDivisorCupTrace (Finsupp.single q 1) (σ (Finsupp.single q 1)) = 0 := by
  by_contra hdiag
  exact hoff
    (deningerDivisorThetaEigen_re_eq_half_of_antilinearGauge σ q hcomm hdiag)

/-- **Total linear blindness.**  Since `1/2` is not a Xi zero, every *linear* gauge that commutes
with Frobenius at `δ_q` has vanishing cup diagonal there — at every zero, unconditionally.  The
functional equation symmetry alone can never produce a nonzero diagonal; only anti-linearity can,
and only on the critical line. -/
theorem deningerDivisor_linearGauge_diag_eq_zero
    (T : Module.End ℂ DeningerDivisorH1) (q : XiZeroCopy)
    (hcomm : deningerDivisorTheta (T (Finsupp.single q 1)) =
      T (deningerDivisorTheta (Finsupp.single q 1))) :
    deningerDivisorCupTrace (Finsupp.single q 1) (T (Finsupp.single q 1)) = 0 := by
  have hward := deningerDivisor_linearGauge_ward T q q 1
  rw [hcomm, sub_self, map_zero] at hward
  rcases mul_eq_zero.mp hward.symm with h | h
  · exfalso
    have hsum := deningerDivisorThetaEigen_add_reflect q
    have hhalf : deningerDivisorThetaEigen q = 1 / 2 := by
      have hRq : deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
          deningerDivisorThetaEigen q := sub_eq_zero.mp h
      rw [hRq] at hsum
      linear_combination hsum / 2
    exact xi_divisor_support_ne_half q.1 hhalf
  · exact h

/-- The reflect gauge `σ_R x = conj ∘ x ∘ R`: coefficientwise conjugation transported along the
functional-equation reflection of the divisor.  This is the positivity-extremal gauge: its cup
diagonal is identically `1`. -/
def deningerDivisorReflectGauge :
    DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1 where
  toFun x :=
    Finsupp.equivMapDomain xiZeroCopyReflectEquiv
      (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) x)
  map_add' x y := by
    ext p
    simp [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply]
  map_smul' c x := by
    ext p
    simp [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply, smul_eq_mul]

/-- Functional-equation reflection of the divisor copies is an involution, so its inverse is
itself. -/
theorem xiZeroCopyReflectEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv.symm q = xiZeroCopyReflectEquiv q := by
  rw [Equiv.symm_apply_eq]
  exact (xiZeroCopyReflectEquiv_apply_apply q).symm

@[simp]
theorem deningerDivisorReflectGauge_apply (x : DeningerDivisorH1) (p : XiZeroCopy) :
    deningerDivisorReflectGauge x p =
      (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv p)) := by
  change (Finsupp.equivMapDomain xiZeroCopyReflectEquiv
    (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) x)) p = _
  rw [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply,
    xiZeroCopyReflectEquiv_symm_apply]

theorem deningerDivisorReflectGauge_single (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorReflectGauge (Finsupp.single r c) =
      Finsupp.single (xiZeroCopyReflectEquiv r) ((starRingEnd ℂ) c) := by
  change Finsupp.equivMapDomain xiZeroCopyReflectEquiv
      (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (Finsupp.single r c)) = _
  rw [Finsupp.mapRange_single, Finsupp.equivMapDomain_single]

/-- The reflect gauge has cup diagonal identically `1`: the positivity side is unconditional. -/
theorem deningerDivisorReflectGauge_diag (q : XiZeroCopy) :
    deningerDivisorCupTrace (Finsupp.single q 1)
      (deningerDivisorReflectGauge (Finsupp.single q 1)) = 1 := by
  rw [deningerDivisorReflectGauge_single, deningerDivisorCupTrace_single_left]
  simp

/-- Exact commutation defect of the reflect gauge: one coefficient, of size exactly the
critical-line displacement `|1 - ρ - conj ρ| = 2 |Re ρ - 1/2|`. -/
theorem deningerDivisorReflectGauge_defect (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single r c)) -
        deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single r c)) =
      Finsupp.single (xiZeroCopyReflectEquiv r)
        ((deningerDivisorThetaEigen (xiZeroCopyReflectEquiv r) -
            (starRingEnd ℂ) (deningerDivisorThetaEigen r)) * (starRingEnd ℂ) c) := by
  rw [deningerDivisorReflectGauge_single, deningerDivisorTheta_single,
    deningerDivisorTheta_single, deningerDivisorReflectGauge_single, map_mul,
    ← Finsupp.single_sub]
  congr 1
  ring

/-- Under RH every Frobenius eigenvalue satisfies `conj λ = 1 - λ`, so the reflect gauge commutes
with Frobenius on every basis vector. -/
theorem deningerDivisorReflectGauge_comm_of_riemannHypothesis
    (hRH : RiemannHypothesis) (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorTheta (deningerDivisorReflectGauge (Finsupp.single r c)) =
      deningerDivisorReflectGauge (deningerDivisorTheta (Finsupp.single r c)) := by
  have hdefect := deningerDivisorReflectGauge_defect r c
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH r
  have hre : (deningerDivisorThetaEigen r).re = 1 / 2 := by
    rw [deningerDivisorThetaEigen_eq, ht]
    simp
  have hconj : (starRingEnd ℂ) (deningerDivisorThetaEigen r) =
      1 - deningerDivisorThetaEigen r := by
    have hadd := Complex.add_conj (deningerDivisorThetaEigen r)
    rw [hre] at hadd
    have : deningerDivisorThetaEigen r +
        (starRingEnd ℂ) (deningerDivisorThetaEigen r) = 1 := by
      rw [hadd]
      norm_num
    linear_combination this
  have hfactor :
      deningerDivisorThetaEigen (xiZeroCopyReflectEquiv r) -
        (starRingEnd ℂ) (deningerDivisorThetaEigen r) = 0 := by
    rw [hconj]
    linear_combination deningerDivisorThetaEigen_add_reflect r
  have hzero : deningerDivisorTheta
        (deningerDivisorReflectGauge (Finsupp.single r c)) -
      deningerDivisorReflectGauge
        (deningerDivisorTheta (Finsupp.single r c)) = 0 := by
    rw [hdefect, hfactor, zero_mul, Finsupp.single_zero]
  exact sub_eq_zero.mp hzero

/-- Every zero on the critical line, packaged through the divisor endgame, is `RiemannHypothesis`. -/
theorem riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    (h : ∀ q : XiZeroCopy, (deningerDivisorThetaEigen q).re = 1 / 2) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  have hmem := mem_xi_divisor_support_of_eq_zero hzero
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) z :=
    xi_divisor_pos_on_support ⟨z, hmem⟩
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) z) := by omega
  have hre : z.re = 1 / 2 := h ⟨⟨z, hmem⟩, ⟨0, hn⟩⟩
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

/-- **RH as a gauge statement.**  The Riemann hypothesis holds iff some anti-linear gauge
commutes with Frobenius on every divisor basis vector while its cup diagonal never vanishes.
Forward: the reflect gauge, whose diagonal is identically `1`.  Backward: the displacement Ward
identity forces every zero onto the critical line.  This equivalence is a re-encoding of RH; the
unconditional content of this file is the Ward identity and the invisibility laws. -/
theorem riemannHypothesis_iff_exists_antilinearGauge :
    RiemannHypothesis ↔
      ∃ σ : DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1,
        (∀ q : XiZeroCopy,
          deningerDivisorTheta (σ (Finsupp.single q 1)) =
            σ (deningerDivisorTheta (Finsupp.single q 1))) ∧
        (∀ q : XiZeroCopy,
          deningerDivisorCupTrace (Finsupp.single q 1)
            (σ (Finsupp.single q 1)) ≠ 0) := by
  constructor
  · intro hRH
    refine ⟨deningerDivisorReflectGauge, fun q =>
      deningerDivisorReflectGauge_comm_of_riemannHypothesis hRH q 1, fun q => ?_⟩
    rw [deningerDivisorReflectGauge_diag]
    exact one_ne_zero
  · rintro ⟨σ, hcomm, hdiag⟩
    exact riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half fun q =>
      deningerDivisorThetaEigen_re_eq_half_of_antilinearGauge σ q (hcomm q) (hdiag q)

end RHTower
