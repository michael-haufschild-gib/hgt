import GaloisForLFunctions.HTGeometry.RittPoincareCocycle
import GaloisForLFunctions.HTGeometry.RittTreeChannelInterior

/-!
# No order-one relation for the clock of an interior tree channel

Combining the two halves: a first-order Ritt relation `(d y)^r = z^j A(y)` for a Poincaré function
of the tree channel map is a rational `(−r)`-differential invariant of that map, and an interior
channel map has none.  So the linearizing coordinate of an interior binary tree channel satisfies no
order-one algebraic differential equation of Ritt's shape — the algebraic obstruction that Ritt's
theorem converts into hypertranscendence.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

noncomputable section

/-- **No Ritt relation for the clock of an interior tree channel.** -/
theorem no_ritt_relation_treeRG_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    {L : Type*} [Field L] [Algebra ℂ L]
    (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L)
    {z y : L} {lam : ℂ} (hlam : lam ≠ 0) (hz : z ≠ 0)
    (hSz : S z = algebraMap ℂ L lam * z)
    (hdS : ∀ x : L, d (S x) = algebraMap ℂ L lam * S (d x))
    (hy : Transcendental ℂ y)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hSy : S y = ratFuncEval y hy (treeRG p (u : ℂ) (v : ℂ)))
    {A : RatFunc ℂ} (hA : A ≠ 0) {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d y) ^ r = z ^ j * ratFuncEval y hy A) : False := by
  have htrans := isRatAffineTransport_of_ritt_relation d S hlam hz hSz hdS hy hR hA hSy hr hritt
  exact treeRG_no_cocycle_interior hp hv huv hu (neg_ne_zero.mpr hr)
    (zpow_ne_zero (-(r + j)) hlam) hA htrans

/-- **No Ritt relation for the clock of an interior tree channel, contracting form.**  This is the
shape an analytic germ field at a repelling fixed point carries: the shift is `f(z) ↦ f(z/λ)` and
the Poincaré equation reads `y = R(T y)`. -/
theorem no_ritt_relation_treeRG_interior_contracting {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    {L : Type*} [Field L] [Algebra ℂ L]
    (d : Derivation ℂ L L) (T : L →ₐ[ℂ] L)
    {z y : L} {mu : ℂ} (hmu : mu ≠ 0) (hz : z ≠ 0)
    (hTz : T z = algebraMap ℂ L mu * z)
    (hdT : ∀ x : L, d (T x) = algebraMap ℂ L mu * T (d x))
    (hy : Transcendental ℂ y) (hTy : Transcendental ℂ (T y))
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hPoin : y = ratFuncEval (T y) hTy (treeRG p (u : ℂ) (v : ℂ)))
    {A : RatFunc ℂ} (hA : A ≠ 0) {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d y) ^ r = z ^ j * ratFuncEval y hy A) : False := by
  have htrans := isRatAffineTransport_of_ritt_relation_contracting d T hmu hz hTz hdT hy hTy
    hR hA hPoin hr hritt
  exact treeRG_no_cocycle_interior hp hv huv hu (neg_ne_zero.mpr hr)
    (zpow_ne_zero (r + j) hmu) hA htrans

end

end GaloisForLFunctions.HTGeometry
