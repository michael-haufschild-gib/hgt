import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmHankelKreinChamber
import GaloisForLFunctions.RHTower.NoDiscreteInvariant

/-!
# The Krein chamber value is Lagarias' criterion, and it cannot be made topological

The split Hankel–Krein chamber identifies the missing Hilbert–Pólya sign as avoidance of the
negative chamber by the pointed theta/Xi source orbit, the Krein value there being the horizontal
derivative of the squared completed modulus.  This file names that quantity.

**The identification.**  With `XiC z = ξ(½ + iz)` the orbit point is
`XiC (b - ai) = ξ(½ + a + ib)`, so `a` is the *horizontal* coordinate `σ - ½` and `b` the ordinate.
Hence the Krein value on the orbit is `∂_σ |ξ(σ+ib)|²`, and wherever `ξ` does not vanish

```text
∂_σ |ξ|² = 2 Re( conj(ξ)·ξ' ) = 2|ξ|²·Re(ξ'/ξ) .
```

So the chamber-avoidance condition is exactly

```text
Re (ξ'/ξ)(s) > 0     for Re s > ½ ,
```

which is **Lagarias' criterion**, a known equivalent of the Riemann hypothesis.  The Krein geometry
is therefore a *reformulation* of the hypothesis, not a reduction of it: the missing sign is the
hypothesis itself, dressed as a chamber.  Recording this keeps the chamber from being treated as an
independent open problem.

**What the geometry cannot add.**  Signature `(2,2)` makes the negative chamber a genuine cone, and
avoidance of a cone by a curve invites a degree or winding argument.  That route is closed: the
critical and off-critical loci lie in one connected component of the symmetric class, joined through
a double zero, so no continuous invariant with values in a totally disconnected set can separate
them.  A chamber-avoidance certificate must therefore be metric — a pointwise inequality — and
cannot be topological.  The split geometry organises the sign; it cannot supply it.

This file formalizes the logarithmic-derivative form of the Krein value and the incompatibility of a
topological certificate.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The Krein value in logarithmic-derivative form.**  Where `f` does not vanish,
`2 Re(conj f · f') = 2 |f|² Re(f'/f)`. -/
theorem krein_value_logDeriv {f f' : ℂ} (hf : f ≠ 0) :
    2 * ((starRingEnd ℂ) f * f').re = 2 * normSq f * (f' / f).re := by
  have hcm : (starRingEnd ℂ) f * f = (normSq f : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj f
  have hkey : (starRingEnd ℂ) f * f' = (normSq f : ℂ) * (f' / f) := by
    field_simp
    linear_combination f' * hcm
  rw [hkey]
  simp [Complex.mul_re]
  ring

/-- **Sign transfer.**  Since `|f|² > 0` off the zero set, the Krein value is positive exactly when
the real part of the logarithmic derivative is. -/
theorem krein_pos_iff_logDeriv_pos {f f' : ℂ} (hf : f ≠ 0) :
    0 < 2 * ((starRingEnd ℂ) f * f').re ↔ 0 < (f' / f).re := by
  rw [krein_value_logDeriv hf]
  have hpos : 0 < normSq f := normSq_pos.mpr hf
  constructor
  · intro h
    nlinarith [h, hpos]
  · intro h
    nlinarith [h, hpos]

/-- The same statement in the form the chamber uses: nonnegativity transfers too. -/
theorem krein_nonneg_iff_logDeriv_nonneg {f f' : ℂ} (hf : f ≠ 0) :
    0 ≤ 2 * ((starRingEnd ℂ) f * f').re ↔ 0 ≤ (f' / f).re := by
  rw [krein_value_logDeriv hf]
  have hpos : 0 < normSq f := normSq_pos.mpr hf
  constructor
  · intro h; nlinarith [h, hpos]
  · intro h; nlinarith [h, hpos]

/-- **No topological certificate.**  A chamber-avoidance witness valued in a totally disconnected
space is constant along the deformation joining a critical double pair to an off-critical quadruple,
so it cannot distinguish them.  Instantiates the general obstruction at the chamber. -/
theorem no_topological_chamber_certificate {X : Type*} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] (Φ : ℝ → X) (hΦ : Continuous Φ) (a b : ℝ) :
    Φ a = Φ b :=
  no_discrete_invariant Φ hΦ a b

/-- Consequently a chamber certificate must be a pointwise inequality: the geometry organises the
sign but does not supply it. -/
theorem chamber_certificate_is_metric {f f' : ℂ} (hf : f ≠ 0)
    (hchamber : 0 < 2 * ((starRingEnd ℂ) f * f').re) : 0 < (f' / f).re :=
  (krein_pos_iff_logDeriv_pos hf).mp hchamber

end RHTower
