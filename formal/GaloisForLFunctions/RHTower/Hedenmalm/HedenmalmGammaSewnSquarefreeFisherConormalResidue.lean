import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeXiConormalBridge
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivLocalForm

/-!
# Squarefree Fisher conormal residue and the source-incidence divisibility no-go

Let

`B(u) = Z_sq(sigma + u epsilon) / Z_sq(sigma)`

be the moving squarefree overlap and let

`F(u) = 2 (B'(u) + epsilon A_sq(sigma) B(u))`

be its division-free pointed Fisher numerator.  If the affine source line meets a strict-right
`xi` zero of multiplicity `m`, then `B` has order `m` while `F` has order `m - 1`.
Therefore the previously proposed holomorphic divisibility `F = B q` is impossible at every
actual strict-right zero, including multiple zeros.

The obstruction has a sharp positive survivor.  The meromorphic conormal `F / B` has a simple
pole whose normalized residue is exactly `2m`.  Thus source incidence does not land in the
overlap ideal: it lands in its one-dimensional conormal quotient and retains full multiplicity.
This is the oriented pre-divisor coordinate missing from reflection-even Route N reporters.

The final theorem is a closed, unconditional certificate quantified over every source line and
every strict-right `xi` zero.  No zero is selected as input to the theorem.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Universal division-free pointed Fisher numerator. -/
def pointedFisherNumerator (f : ℂ → ℂ) (c z : ℂ) : ℂ :=
  2 * (deriv f z + c * f z)

/-- At a finite positive-order zero, adding any analytic connection term `c f` cannot alter the
one-order conormal drop of `f'`; multiplication by two also preserves the order. -/
theorem analyticOrderAt_pointedFisherNumerator_eq_pred
    {f : ℂ → ℂ} {c a : ℂ} (hf : AnalyticAt ℂ f a)
    (hzero : f a = 0) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ k : ℕ,
      analyticOrderAt f a = (k + 1 : ℕ) ∧
      analyticOrderAt (pointedFisherNumerator f c) a = (k : ℕ) := by
  let m : ℕ := (analyticOrderAt f a).toNat
  have hmne : m ≠ 0 := by
    have hne : analyticOrderAt f a ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hf, hzero⟩
    intro hm
    rcases ENat.toNat_eq_zero.mp hm with hzero' | htop
    · exact hne hzero'
    · exact hfinite htop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hforder : analyticOrderAt f a = (k + 1 : ℕ) := by
    calc
      analyticOrderAt f a = (m : ℕ∞) := (ENat.coe_toNat hfinite).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv f) a = (k : ℕ) := by
    have h := analyticOrderAt_deriv_of_pos hf (n := k)
      (by simpa [Nat.cast_add, Nat.cast_one] using hforder)
    simpa using h
  let D : ℂ → ℂ := fun z => c * f z
  have hDgt : (k : ℕ∞) < analyticOrderAt D a := by
    by_cases hc : c = 0
    · subst c
      have hDtop : analyticOrderAt D a = ⊤ :=
        analyticOrderAt_eq_top.mpr
          (Filter.Eventually.of_forall (fun z => by simp [D]))
      rw [hDtop]
      exact ENat.coe_lt_top k
    · have hconst : analyticOrderAt (fun _ : ℂ => c) a = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hc)
      have hDorder : analyticOrderAt D a = (k + 1 : ℕ) := by
        change analyticOrderAt ((fun _ : ℂ => c) * f) a = _
        rw [analyticOrderAt_mul analyticAt_const hf, hconst, zero_add, hforder]
      rw [hDorder]
      exact_mod_cast Nat.lt_succ_self k
  have hsum : analyticOrderAt ((deriv f) + D) a = (k : ℕ) := by
    rw [analyticOrderAt_add_eq_left_of_lt (by simpa [hderiv] using hDgt), hderiv]
  have htwo : analyticOrderAt (fun _ : ℂ => (2 : ℂ)) a = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
  have hfun :
      pointedFisherNumerator f c =
        (fun _ : ℂ => (2 : ℂ)) * ((deriv f) + D) := by
    funext z
    simp only [pointedFisherNumerator, Pi.mul_apply, Pi.add_apply, D]
  refine ⟨k, hforder, ?_⟩
  rw [hfun,
    analyticOrderAt_mul analyticAt_const
      (hf.deriv.add (by dsimp [D]; fun_prop)),
    htwo, zero_add, hsum]

/-- The moving squarefree overlap is analytic whenever its shifted point is strict-right and not
the zeta pole. -/
theorem analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
    {sigma epsilon u : ℂ}
    (hshift : 1 / 2 < (sigma + u * epsilon).re)
    (hshift1 : sigma + u * epsilon ≠ 1) :
    AnalyticAt ℂ
      (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u := by
  have houter := analyticAt_squarefreePartition_of_half_lt_re hshift hshift1
  let g : ℂ → ℂ := fun v => sigma + v * epsilon
  have hgan : AnalyticAt ℂ g u := by dsimp [g]; fun_prop
  have hcomp0 : AnalyticAt ℂ
      (GaloisForLFunctions.squarefreePartition ∘ g) u :=
    AnalyticAt.comp (x := u) (f := g)
      (g := GaloisForLFunctions.squarefreePartition) houter hgan
  have hcomp : AnalyticAt ℂ
      (fun v : ℂ =>
        GaloisForLFunctions.squarefreePartition (sigma + v * epsilon)) u := by
    simpa [g, Function.comp_def] using hcomp0
  change AnalyticAt ℂ
    (fun v : ℂ =>
      GaloisForLFunctions.squarefreePartition (sigma + v * epsilon) /
        GaloisForLFunctions.squarefreePartition sigma) u
  exact hcomp.div_const

/-- A nonconstant affine source coordinate and a nonzero base normalization preserve the complete
squarefree divisor order. -/
theorem analyticOrderAt_squarefreeBoundaryOverlap_eq_squarefreePartition
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hshift : 1 / 2 < (sigma + u * epsilon).re)
    (hshift1 : sigma + u * epsilon ≠ 1) :
    analyticOrderAt
        (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
      analyticOrderAt GaloisForLFunctions.squarefreePartition
        (sigma + u * epsilon) := by
  let g : ℂ → ℂ := fun v => sigma + v * epsilon
  have hgan : AnalyticAt ℂ g u := by dsimp [g]; fun_prop
  have hgderiv : deriv g u ≠ 0 := by
    have hg' : HasDerivAt g epsilon u := by
      dsimp only [g]
      convert! (hasDerivAt_const (x := u) (c := sigma)).add
        ((hasDerivAt_id u).mul_const epsilon) using 1
      ring
    simpa [hg'.deriv] using hepsilon
  have hden : GaloisForLFunctions.squarefreePartition sigma ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero hsigma
  have hconstOrder : analyticOrderAt
      (fun _ : ℂ =>
        (GaloisForLFunctions.squarefreePartition sigma)⁻¹) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hden))
  have hfun :
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon =
        (GaloisForLFunctions.squarefreePartition ∘ g) *
          (fun _ : ℂ =>
            (GaloisForLFunctions.squarefreePartition sigma)⁻¹) := by
    funext v
    simp [GaloisForLFunctions.squarefreeBoundaryOverlap, g, div_eq_mul_inv]
  rw [hfun, analyticOrderAt_mul (by
        have houter := analyticAt_squarefreePartition_of_half_lt_re hshift hshift1
        exact AnalyticAt.comp (x := u) (f := g)
          (g := GaloisForLFunctions.squarefreePartition) houter hgan)
      analyticAt_const, hconstOrder, add_zero,
    analyticOrderAt_comp_of_deriv_ne_zero hgan hgderiv]

/-- The affine squarefree source overlap carries the complete `xi` divisor order throughout the
strict-right open critical strip. -/
theorem analyticOrderAt_squarefreeBoundaryOverlap_eq_xi_of_strictRightStrip
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hρhalf : 1 / 2 < rho.re) (hρone : rho.re < 1) :
    analyticOrderAt
        (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
      analyticOrderAt xi rho := by
  have hρne : rho ≠ 1 := by
    intro h
    rw [h] at hρone
    norm_num at hρone
  have hshift1 : sigma + u * epsilon ≠ 1 := by
    simpa [hcoord] using hρne
  rw [analyticOrderAt_squarefreeBoundaryOverlap_eq_squarefreePartition
      hsigma hepsilon (by simpa [hcoord] using hρhalf) hshift1,
    hcoord,
    analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
      hρhalf hρone]

/-- The pointed Fisher quotient has residue twice the finite analytic order.  The analytic
connection term contributes no residue. -/
theorem tendsto_pointedFisherQuotient_residue
    {f : ℂ → ℂ} {c a : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f a)
    (horder : analyticOrderAt f a = (d : ℕ)) :
    Tendsto
      (fun z => (z - a) * (pointedFisherNumerator f c z / f z))
      (𝓝[≠] a) (𝓝 (2 * (d : ℂ))) := by
  have hmeromorphicOrder : meromorphicOrderAt f a = (d : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, horder]
    simp
  have hres :=
    GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder
      hf.meromorphicAt hmeromorphicOrder
  have hscaled : Tendsto
      (fun z => 2 * ((z - a) * logDeriv f z))
      (𝓝[≠] a) (𝓝 (2 * (d : ℂ))) :=
    hres.const_mul 2
  have hreg : Tendsto (fun z : ℂ => (z - a) * (2 * c))
      (𝓝[≠] a) (𝓝 0) := by
    have hfull : Tendsto (fun z : ℂ => (z - a) * (2 * c))
        (𝓝 a) (𝓝 0) := by
      convert (continuousAt_id.sub_const a).mul_const (2 * c) using 1 <;> simp
    exact hfull.mono_left nhdsWithin_le_nhds
  have hsum := hscaled.add hreg
  have hlim : Tendsto
      (fun z =>
        2 * ((z - a) * logDeriv f z) + (z - a) * (2 * c))
      (𝓝[≠] a) (𝓝 (2 * (d : ℂ))) := by
    simpa using hsum
  have hfinite : analyticOrderAt f a ≠ ⊤ := by
    rw [horder]
    exact ENat.coe_ne_top d
  have hne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim (hfinite (analyticOrderAt_eq_top.mpr hzero))
    · exact hne
  refine hlim.congr' ?_
  filter_upwards [hne] with z hz
  simp only [pointedFisherNumerator, logDeriv_apply]
  field_simp [hz]

/-- **Squarefree Fisher conormal order law.**  At every strict-right `xi` zero of multiplicity
`k+1`, the division-free Fisher numerator has exact order `k`. -/
theorem analyticOrderAt_squarefreeFisherScore_eq_pred_of_strictRightXiZero
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hρhalf : 1 / 2 < rho.re) (hρone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ,
      analyticOrderAt
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
        (k + 1 : ℕ) ∧
      analyticOrderAt
          (GaloisForLFunctions.squarefreeFisherScore sigma epsilon) u =
        (k : ℕ) := by
  have hρne : rho ≠ 1 := by
    intro h
    rw [h] at hρone
    norm_num at hρone
  have hshift1 : sigma + u * epsilon ≠ 1 := by
    simpa [hcoord] using hρne
  have hBAn := analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
    (sigma := sigma) (epsilon := epsilon) (u := u)
    (by simpa [hcoord] using hρhalf) hshift1
  have hBOrder :
      analyticOrderAt
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
        analyticOrderAt xi rho := by
    rw [analyticOrderAt_squarefreeBoundaryOverlap_eq_squarefreePartition
        hsigma hepsilon (by simpa [hcoord] using hρhalf) hshift1,
      hcoord,
      analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
        hρhalf hρone]
  have hBzero :
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u = 0 := by
    rw [GaloisForLFunctions.squarefreeBoundaryOverlap, hcoord]
    have hsq : GaloisForLFunctions.squarefreePartition rho = 0 :=
      (squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip
        hρhalf hρone).mpr hzero
    rw [hsq, zero_div]
  have hBfinite : analyticOrderAt
      (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u ≠ ⊤ := by
    rw [hBOrder]
    exact xi_order_ne_top rho
  obtain ⟨k, hkB, hkF⟩ :=
    analyticOrderAt_pointedFisherNumerator_eq_pred
      hBAn hBzero hBfinite
        (c := epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma)
  refine ⟨k, hkB, ?_⟩
  have hfun :
      GaloisForLFunctions.squarefreeFisherScore sigma epsilon =
        pointedFisherNumerator
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon)
          (epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma) := by
    rfl
  rw [hfun]
  exact hkF

/-- **Old source-incidence gate is impossible.**  No analytic local multiplier can divide the
Fisher numerator by the squarefree overlap at an actual strict-right zero. -/
theorem no_analytic_squarefreeFisherScore_division_at_strictRightXiZero
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hρhalf : 1 / 2 < rho.re) (hρone : rho.re < 1)
    (hzero : xi rho = 0) :
    ¬ ∃ q : ℂ → ℂ, AnalyticAt ℂ q u ∧
      GaloisForLFunctions.squarefreeFisherScore sigma epsilon =ᶠ[𝓝 u]
        (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) * q := by
  have hρne : rho ≠ 1 := by
    intro h
    rw [h] at hρone
    norm_num at hρone
  have hshift1 : sigma + u * epsilon ≠ 1 := by
    simpa [hcoord] using hρne
  have hBAn := analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
    (sigma := sigma) (epsilon := epsilon) (u := u)
    (by simpa [hcoord] using hρhalf) hshift1
  obtain ⟨k, hkB, hkF⟩ :=
    analyticOrderAt_squarefreeFisherScore_eq_pred_of_strictRightXiZero
      hsigma hepsilon hcoord hρhalf hρone hzero
  rintro ⟨q, hq, heq⟩
  have horders := analyticOrderAt_congr heq
  rw [analyticOrderAt_mul hBAn hq, hkB, hkF] at horders
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
    calc
      ((k + 1 : ℕ) : ℕ∞) ≤
          ((k + 1 : ℕ) : ℕ∞) + analyticOrderAt q u :=
        self_le_add_right _ _
      _ = (k : ℕ∞) := horders.symm
  exact (Nat.not_succ_le_self k) (ENat.coe_le_coe.mp hle)

/-- **Positive survivor of failed divisibility.**  The Fisher conormal quotient has a simple-pole
residue `2(k+1)`, exactly twice the full `xi` multiplicity. -/
theorem tendsto_squarefreeFisherScore_div_overlap_residue_at_strictRightXiZero
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hρhalf : 1 / 2 < rho.re) (hρone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      Tendsto
        (fun v => (v - u) *
          (GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
            GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v))
        (𝓝[≠] u)
        (𝓝 (2 * ((k + 1 : ℕ) : ℂ))) := by
  have hρne : rho ≠ 1 := by
    intro h
    rw [h] at hρone
    norm_num at hρone
  have hshift1 : sigma + u * epsilon ≠ 1 := by
    simpa [hcoord] using hρne
  have hBAn := analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
    (sigma := sigma) (epsilon := epsilon) (u := u)
    (by simpa [hcoord] using hρhalf) hshift1
  have hBXiOrder :
      analyticOrderAt
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
        analyticOrderAt xi rho := by
    calc
      analyticOrderAt
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
          analyticOrderAt GaloisForLFunctions.squarefreePartition rho := by
        rw [analyticOrderAt_squarefreeBoundaryOverlap_eq_squarefreePartition
          hsigma hepsilon (by simpa [hcoord] using hρhalf) hshift1, hcoord]
      _ = analyticOrderAt xi rho :=
        analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
          hρhalf hρone
  obtain ⟨k, hkB, _hkF⟩ :=
    analyticOrderAt_squarefreeFisherScore_eq_pred_of_strictRightXiZero
      hsigma hepsilon hcoord hρhalf hρone hzero
  refine ⟨k, hBXiOrder.symm.trans hkB, ?_⟩
  have hres := tendsto_pointedFisherQuotient_residue
    (f := GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon)
    (c := epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma)
    hBAn hkB
  have hfun :
      GaloisForLFunctions.squarefreeFisherScore sigma epsilon =
        pointedFisherNumerator
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon)
          (epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma) := by
    rfl
  simpa [hfun] using hres

/-- Closed certificate for squarefree Fisher conormal incidence at every strict-right zero. -/
structure RouteNSquarefreeFisherConormalCertificate : Prop where
  divisorLanding :
    ∀ {sigma epsilon u rho : ℂ},
      1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
      1 / 2 < rho.re → rho.re < 1 →
      analyticOrderAt
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
        analyticOrderAt xi rho
  conormalOrderDrop :
    ∀ {sigma epsilon u rho : ℂ},
      1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
      1 / 2 < rho.re → rho.re < 1 → xi rho = 0 →
      ∃ k : ℕ,
        analyticOrderAt
            (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u =
          (k + 1 : ℕ) ∧
        analyticOrderAt
            (GaloisForLFunctions.squarefreeFisherScore sigma epsilon) u =
          (k : ℕ)
  noHolomorphicDivisibility :
    ∀ {sigma epsilon u rho : ℂ},
      1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
      1 / 2 < rho.re → rho.re < 1 → xi rho = 0 →
      ¬ ∃ q : ℂ → ℂ, AnalyticAt ℂ q u ∧
        GaloisForLFunctions.squarefreeFisherScore sigma epsilon =ᶠ[𝓝 u]
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) * q
  conormalResidue :
    ∀ {sigma epsilon u rho : ℂ},
      1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
      1 / 2 < rho.re → rho.re < 1 → xi rho = 0 →
      ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
        Tendsto
          (fun v => (v - u) *
            (GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
              GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v))
          (𝓝[≠] u)
          (𝓝 (2 * ((k + 1 : ℕ) : ℂ)))

/-- **Unconditional squarefree Fisher conormal law.** -/
theorem routeNSquarefreeFisherConormal_law :
    RouteNSquarefreeFisherConormalCertificate where
  divisorLanding :=
    analyticOrderAt_squarefreeBoundaryOverlap_eq_xi_of_strictRightStrip
  conormalOrderDrop :=
    analyticOrderAt_squarefreeFisherScore_eq_pred_of_strictRightXiZero
  noHolomorphicDivisibility :=
    no_analytic_squarefreeFisherScore_division_at_strictRightXiZero
  conormalResidue :=
    tendsto_squarefreeFisherScore_div_overlap_residue_at_strictRightXiZero

end

end RHTower
