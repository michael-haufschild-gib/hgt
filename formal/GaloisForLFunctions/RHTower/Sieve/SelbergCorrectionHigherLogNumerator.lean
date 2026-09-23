import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionHigherLogLocal
import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogNumerator
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogLocalIdentity

/-!
# Higher logarithmic numerator identity for the Selberg correction

After convolution with `(1-X/p)(1-Y/p)`, every positive logarithmic jet collapses to the three
monomials `X²Y`, `XY²`, and `X²Y²`.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def selbergCorrectionLogPowerNumerator (k p i j : ℕ) : ℝ :=
  (Real.log (p : ℝ) ^ k / (p : ℝ) ^ (2 : ℕ)) *
    ((if i = 2 then (1 : ℝ) else 0) * (if j = 1 then (1 : ℝ) else 0) +
      (if i = 1 then (1 : ℝ) else 0) * (if j = 2 then (1 : ℝ) else 0) -
      (2 : ℝ) ^ k *
        ((if i = 2 then (1 : ℝ) else 0) * (if j = 2 then (1 : ℝ) else 0)))

/-- Higher-order version of the differentiated correction numerator identity. -/
theorem additiveBivariateConvolution_selbergCorrectionLogPowerLocal_moebius
    (k : ℕ) {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    additiveBivariateConvolution (selbergCorrectionLogPowerLocal k p)
        (localMoebiusPairFactor p) i j =
      selbergCorrectionLogPowerNumerator k p i j := by
  let c : ℝ := Real.log (p : ℝ) ^ k / (p : ℝ) ^ (2 : ℕ)
  have hdecomp : selbergCorrectionLogPowerLocal k p = fun a b =>
      c * (geomTailTwo p a * geomTailOne p b) +
        c * (geomTailOne p a * geomTailTwo p b) -
        (c * (2 : ℝ) ^ k) * (geomTailTwo p a * geomTailTwo p b) := by
    funext a b
    rw [selbergCorrectionLogPowerLocal_eq_geomTails k hp.pos a b]
    dsimp [c]
    ring
  rw [hdecomp, additiveBivariateConvolution_sub_left,
    additiveBivariateConvolution_add_left]
  have hscale : ∀ (d : ℝ) (f : ℕ → ℕ → ℝ),
      additiveBivariateConvolution (fun a b => d * f a b)
          (localMoebiusPairFactor p) i j =
        d * additiveBivariateConvolution f (localMoebiusPairFactor p) i j := by
    intro d f
    rw [additiveBivariateConvolution, additiveBivariateConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  change
    additiveBivariateConvolution (fun a b => c * (geomTailTwo p a * geomTailOne p b))
        (localMoebiusPairFactor p) i j +
      additiveBivariateConvolution (fun a b => c * (geomTailOne p a * geomTailTwo p b))
        (localMoebiusPairFactor p) i j -
      additiveBivariateConvolution
        (fun a b => (c * (2 : ℝ) ^ k) * (geomTailTwo p a * geomTailTwo p b))
        (localMoebiusPairFactor p) i j = _
  rw [hscale, hscale, hscale]
  rw [show localMoebiusPairFactor p =
      fun a b => localMoebiusFactor p a * localMoebiusFactor p b from rfl]
  rw [additiveBivariateConvolution_product, additiveBivariateConvolution_product,
    additiveBivariateConvolution_product]
  simp_rw [additiveConvolution_geomTailTwo hp.pos,
    additiveConvolution_geomTailOne hp.pos]
  rw [selbergCorrectionLogPowerNumerator]
  dsimp [c]
  ring

end

end RHTower.Sieve
