import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation
import GaloisForLFunctions.RHTower.MobiusFixedCurrentVonMangoldt
import GaloisForLFunctions.RHTower.WoldSieveNormalConeVonMangoldt

/-!
# Wold--Euler activation holonomy

The one-sided zeta ratio

`ζ(s) / ζ(s + h)`

is the infinite-depth holonomy of the all-prime Wold activation.  At
zero activation its derivative is the von Mangoldt current, matching
the coefficientwise Wold normal derivative already proved in
`WoldSieveNormalConeVonMangoldt`.

The holonomy has an exact shifted cocycle and tends back to `ζ(s)` as
activation escapes to the far right.  These are unconditional
Euler-half-plane identities.  They do not assert that the completed
Gamma/co-Poisson transport is positive on a zeta-divisor conormal.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Infinite-depth Wold activation holonomy. -/
def woldActivationHolonomy (s h : ℂ) : ℂ :=
  riemannZeta s / riemannZeta (s + h)

/-- Zero activation is the identity in the Euler chamber. -/
@[simp]
theorem woldActivationHolonomy_zero {s : ℂ} (hs : 1 < s.re) :
    woldActivationHolonomy s 0 = 1 := by
  rw [woldActivationHolonomy, add_zero, div_self]
  exact riemannZeta_ne_zero_of_one_lt_re hs

/-- The first holonomy jet is exactly the von Mangoldt current. -/
theorem hasDerivAt_woldActivationHolonomy_zero
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (woldActivationHolonomy s) (vonMangoldtCurrent s) 0 := by
  change HasDerivAt
    (fun h : ℂ => riemannZeta s / riemannZeta (s + h))
    (vonMangoldtCurrent s) 0
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hζ :
      HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hshift : HasDerivAt (fun h : ℂ => s + h) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) 0).const_add s
  have hden :
      HasDerivAt (fun h : ℂ => riemannZeta (s + h))
        (deriv riemannZeta s) 0 := by
    change HasDerivAt (riemannZeta ∘ fun h : ℂ => s + h)
      (deriv riemannZeta s) 0
    have hζ' :
        HasDerivAt riemannZeta (deriv riemannZeta s) (s + 0) := by
      simpa using hζ
    simpa using hζ'.comp 0 hshift
  have hnum :
      HasDerivAt (fun _ : ℂ => riemannZeta s) 0 0 :=
    hasDerivAt_const (x := 0) (c := riemannZeta s)
  have hdiv :
      HasDerivAt
        (fun h : ℂ => riemannZeta s / riemannZeta (s + h))
        ((0 * riemannZeta (s + 0) -
          riemannZeta s * deriv riemannZeta s) /
            riemannZeta (s + 0) ^ 2) 0 := by
    exact hnum.div hden (by simpa using hz)
  convert hdiv using 1
  simp only [add_zero, zero_mul, zero_sub, vonMangoldtCurrent]
  field_simp

/-- Activation satisfies the exact translation cocycle wherever the
intermediate Euler value is nonzero. -/
theorem woldActivationHolonomy_cocycle
    {s h k : ℂ}
    (hs : 1 < s.re) (hh : 0 ≤ h.re) :
    woldActivationHolonomy s (h + k) =
      woldActivationHolonomy s h *
        woldActivationHolonomy (s + h) k := by
  have hz1 : riemannZeta (s + h) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  simp only [woldActivationHolonomy, add_assoc]
  field_simp [hz1]

/-- Infinite activation recovers zeta itself. -/
theorem tendsto_woldActivationHolonomy_nat_atTop
    (s : ℂ) :
    Tendsto
      (fun n : ℕ => woldActivationHolonomy s n)
      atTop (𝓝 (riemannZeta s)) := by
  have hre :
      Tendsto (fun n : ℕ => (s + (n : ℂ)).re)
        atTop atTop := by
    simp only [Complex.add_re, Complex.natCast_re]
    exact tendsto_atTop_add_const_left atTop s.re
      tendsto_natCast_atTop_atTop
  have hden :=
    (tendsto_riemannZeta_of_re_atTop hre).inv₀ one_ne_zero
  have hconst :
      Tendsto (fun _ : ℕ => riemannZeta s)
        atTop (𝓝 (riemannZeta s)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hden
  simpa [woldActivationHolonomy, div_eq_mul_inv] using hmul

/-- Exact coefficient/holonomy weld for the first Wold normal stratum. -/
structure WoldEulerActivationHolonomyCertificate (s : ℂ) : Prop where
  coefficientNormalJet :
    ∀ n : ℕ,
      HasDerivAt (woldIncidenceNormalFactor n)
        (ArithmeticFunction.vonMangoldt n) 0
  zeroFace : woldActivationHolonomy s 0 = 1
  currentJet :
    HasDerivAt (woldActivationHolonomy s) (vonMangoldtCurrent s) 0
  cocycle :
    ∀ {h k : ℂ}, 0 ≤ h.re →
      woldActivationHolonomy s (h + k) =
        woldActivationHolonomy s h *
          woldActivationHolonomy (s + h) k
  infiniteActivation :
    Tendsto
      (fun n : ℕ => woldActivationHolonomy s n)
      atTop (𝓝 (riemannZeta s))

/-- The Wold coefficient jet and zeta-ratio holonomy are one
unconditional Euler source law. -/
theorem woldEulerActivationHolonomy_law
    {s : ℂ} (hs : 1 < s.re) :
    WoldEulerActivationHolonomyCertificate s where
  coefficientNormalJet := hasDerivAt_woldIncidenceNormalFactor
  zeroFace := woldActivationHolonomy_zero hs
  currentJet := hasDerivAt_woldActivationHolonomy_zero hs
  cocycle := fun hh => woldActivationHolonomy_cocycle hs hh
  infiniteActivation := tendsto_woldActivationHolonomy_nat_atTop s

end

end RHTower
