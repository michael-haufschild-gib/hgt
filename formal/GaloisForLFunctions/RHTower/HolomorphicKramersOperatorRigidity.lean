import GaloisForLFunctions.RHTower.HolomorphicKramersFiberRigidity

/-!
# Fixed-fiber Kramers rigidity for bounded operator families

The two-by-two Kramers obstruction is dimension-free. Let `A(z)` be a bounded complex-linear
operator family whose every matrix coefficient is holomorphic. Suppose one fixed antiunitary
map `J` preserves inner products up to complex conjugation and commutes with `A(z)` in every
parameter fibre.

Then the coefficient paired with `x,y` through `Jx,Jy` is the pointwise complex conjugate of the
original coefficient. Both coefficients are holomorphic, so scalar open-mapping rigidity makes
the original coefficient constant. Inner-product separation then makes the full operator family
constant.

Thus no nonconstant bounded holomorphic determinant or Fredholm family can obtain Kramers
doubling from a fixed same-fibre antiunitary, in any Hilbert-space dimension. The same argument
also closes unbounded families on one fixed domain. A survivor must use parameter reversal or
genuinely parameter-dependent domains.
-/

open Complex Set

namespace RHTower

/-- A weakly holomorphic bounded-operator family commuting fibrewise with one fixed antiunitary
map is constant on a connected open parameter domain. The usual extra Kramers condition `J²=-1`
is not needed for this rigidity. -/
theorem weaklyHolomorphic_fixedAntiunitary_operator_constant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U : Set ℂ} {A : ℂ → H →L[ℂ] H} {J : H → H}
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hweak : ∀ x y : H,
      AnalyticOnNhd ℂ (fun z => inner ℂ x (A z y)) U)
    (hJinner : ∀ x y : H,
      inner ℂ (J x) (J y) = starRingEnd ℂ (inner ℂ x y))
    (hcomm : ∀ z ∈ U, ∀ y : H, A z (J y) = J (A z y)) :
    ∃ A₀ : H →L[ℂ] H, ∀ z ∈ U, A z = A₀ := by
  obtain ⟨z₀, hz₀⟩ := hUconn.nonempty
  refine ⟨A z₀, fun z hz => ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have hpair : ∀ w ∈ U,
      inner ℂ (J x) (A w (J y)) =
        starRingEnd ℂ (inner ℂ x (A w y)) := by
    intro w hw
    rw [hcomm w hw y, hJinner]
  obtain ⟨c, hc⟩ := holomorphic_conjugate_pair_constant
    hUopen hUconn (hweak x y) (hweak (J x) (J y)) hpair
  exact (hc z hz).trans (hc z₀ hz₀).symm

/-- Boundedness is unnecessary when the operator domain is fixed. Any weakly holomorphic
fixed-domain family commuting with fixed antiunitary maps on domain and codomain is pointwise
constant on that domain. -/
theorem weaklyHolomorphic_fixedDomain_fixedAntiunitary_constant
    {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U : Set ℂ} {A : ℂ → D → H} {JH : H → H} {JD : D → D}
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hweak : ∀ x : H, ∀ y : D,
      AnalyticOnNhd ℂ (fun z => inner ℂ x (A z y)) U)
    (hJinner : ∀ x y : H,
      inner ℂ (JH x) (JH y) = starRingEnd ℂ (inner ℂ x y))
    (hcomm : ∀ z ∈ U, ∀ y : D, A z (JD y) = JH (A z y)) :
    ∃ A₀ : D → H, ∀ z ∈ U, ∀ y, A z y = A₀ y := by
  obtain ⟨z₀, hz₀⟩ := hUconn.nonempty
  refine ⟨A z₀, fun z hz y => ?_⟩
  apply ext_inner_left ℂ
  intro x
  have hpair : ∀ w ∈ U,
      inner ℂ (JH x) (A w (JD y)) =
        starRingEnd ℂ (inner ℂ x (A w y)) := by
    intro w hw
    rw [hcomm w hw y, hJinner]
  obtain ⟨c, hc⟩ := holomorphic_conjugate_pair_constant
    hUopen hUconn (hweak x y) (hweak (JH x) (JD y)) hpair
  exact (hc z hz).trans (hc z₀ hz₀).symm

end RHTower
