/-
# The curvature tier of the reflection cocycle

The reflection cocycle `h_F(s) = F(1−s)/F(s)` (see `ReflectionCocycleClass`) carries the functional
equation as a computed weld class.  Its *rate-lattice* content — the class `weldClass(log Q)` — reads
only the exact conductor scale and is **zero** for `ζ`, whose cocycle is a pure archimedean Gamma
quotient.  So the rate lattice cannot tell a weld-trivial carrier from `ζ`: both have class zero.

This module builds the next invariant, one tier up, that does separate them: the **curvature** of the
reflection cocycle,
`κ_F(s) = (log h_F)''(s) = deriv (logDeriv (reflCocycle F)) s`.

* **Universality of the cocycle law.**  `reflCocycle_involution`: for any carrier nonzero at `s` and
  `1−s`, `h_F(s)·h_F(1−s) = 1`.  The reflection cocycle is a genuine reflection `1`-cocycle,
  intrinsic to every `F`; the name is earned, not postulated.
* **The conductor tier is flat.**  An exact-conductor member has cocycle the pure power
  `conductorCocycle Q s = Q^{2s−1}`.  Its logarithmic derivative is the **constant** doubled
  conductor rate `2·log Q` (`conductorCocycle_logDeriv`), so its curvature vanishes identically
  (`conductorCocycle_curvature_zero`).  Exact conductors live on the flat (zero-curvature) locus:
  their entire weld content is the rate `2 log Q`, already seen by the rate lattice.

The complementary fact — that the archimedean cocycle `Gammaℝ(s)/Gammaℝ(1−s)`, hence `ζ`'s reflection
cocycle on the strip, has **nonzero** curvature — places `ζ` off this flat locus: its weld is real but
lives one tier above the conductor lattice.  That separation is the archimedean-tier statement built
on top of this file.
-/
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The reflection cocycle is a genuine reflection 1-cocycle -/

/-- **The reflection-cocycle law.**  For any carrier `F` nonzero at `s` and at `1−s`, the reflection
cocycle satisfies `h_F(s)·h_F(1−s) = 1`.  Reflection is an involution, so composing the cocycle with
its reflected value telescopes: `F(1−s)/F(s) · F(s)/F(1−s) = 1`.  This holds for *every* carrier, with
no functional equation assumed — it is the intrinsic cocycle identity that names `reflCocycle`. -/
theorem reflCocycle_involution {F : ℂ → ℂ} {s : ℂ} (h1 : F s ≠ 0) (h2 : F (1 - s) ≠ 0) :
    reflCocycle F s * reflCocycle F (1 - s) = 1 := by
  simp only [reflCocycle, show (1 : ℂ) - (1 - s) = s from by ring]
  field_simp

/-! ### §2 The conductor cocycle and its flat rate -/

/-- The **conductor cocycle** of scale `Q`: the pure power `Q^{2s−1}` that the reflection cocycle of
an exact-conductor member collapses to (`reflCocycle_of_conductor`). -/
def conductorCocycle (Q : ℕ) : ℂ → ℂ := fun s => (Q : ℂ) ^ (2 * s - 1)

/-- The complex logarithm of a positive natural cast is the real logarithm. -/
theorem log_natCast_eq {Q : ℕ} (hQ : 1 ≤ Q) : Complex.log (Q : ℂ) = (Real.log Q : ℂ) := by
  have h : (Q : ℂ) = ((Q : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (Q : ℝ))]

/-- **The conductor cocycle has constant logarithmic derivative.**  For `Q ≥ 2`,
`logDeriv (conductorCocycle Q) s = 2·log Q` at every `s`: writing `Q^{2s−1} = exp((2s−1)·log Q)`, the
logarithmic derivative of an exponential of an affine argument is the constant slope `2·log Q` — the
doubled conductor rate, which is exactly the generator the rate lattice records. -/
theorem conductorCocycle_logDeriv {Q : ℕ} (hQ : 2 ≤ Q) (s : ℂ) :
    logDeriv (conductorCocycle Q) s = 2 * (Real.log Q : ℂ) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hfun : conductorCocycle Q
      = (fun z : ℂ => Complex.exp ((2 * z - 1) * Complex.log Q)) := by
    funext z; rw [conductorCocycle, Complex.cpow_def_of_ne_zero hQ0]; ring_nf
  have hd : HasDerivAt (fun z : ℂ => Complex.exp ((2 * z - 1) * Complex.log Q))
      (Complex.exp ((2 * s - 1) * Complex.log Q) * (2 * Complex.log Q)) s := by
    have hg : HasDerivAt (fun z : ℂ => (2 * z - 1) * Complex.log Q) (2 * Complex.log Q) s := by
      have h1 : HasDerivAt (fun z : ℂ => 2 * z - 1) 2 s := by
        simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const 1
      simpa using h1.mul_const (Complex.log Q)
    simpa using (Complex.hasDerivAt_exp ((2 * s - 1) * Complex.log Q)).comp s hg
  rw [hfun, logDeriv_apply, hd.deriv]
  have hval : Complex.exp ((2 * s - 1) * Complex.log Q) ≠ 0 := Complex.exp_ne_zero _
  rw [show Complex.exp ((2 * s - 1) * Complex.log Q) * (2 * Complex.log Q)
        = (2 * Complex.log Q) * Complex.exp ((2 * s - 1) * Complex.log Q) by ring,
      mul_div_assoc, div_self hval, mul_one, log_natCast_eq (by omega)]

/-- **The reflection curvature** of a carrier `F`: the second logarithmic derivative of its reflection
cocycle, `κ_F = deriv (logDeriv (reflCocycle F))`.  It is the tier-two weld invariant: it annihilates
every pure-conductor cocycle and detects genuinely archimedean welds. -/
def reflCurvature (F : ℂ → ℂ) : ℂ → ℂ := deriv (logDeriv (reflCocycle F))

/-- **The conductor cocycle is curvature-flat.**  For `Q ≥ 2` the reflection curvature of the
conductor cocycle vanishes identically: its logarithmic derivative is the constant `2·log Q`, whose
derivative is `0`.  Exact-conductor members carry no tier-two (archimedean) weld — their whole datum
is the rate `2 log Q`, already read by the rate lattice. -/
theorem conductorCocycle_curvature_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    deriv (logDeriv (conductorCocycle Q)) = (0 : ℂ → ℂ) := by
  have hconst : logDeriv (conductorCocycle Q) = (fun _ : ℂ => 2 * (Real.log Q : ℂ)) := by
    funext s; exact conductorCocycle_logDeriv hQ s
  rw [hconst]; funext s; simp

/-- **An exact-conductor member is curvature-flat where it is nonzero.** If `f` satisfies the
degree-zero equation `f s = Q^{1−2s}·f(1−s)` and is nonvanishing on an open set `U`, its
reflection cocycle agrees with the conductor cocycle throughout `U`, so on `U` the two logarithmic
derivatives coincide.  Combined with `conductorCocycle_curvature_zero`, the reflection curvature of `f`
vanishes on `U`: exact conductors sit on the flat locus of the curvature invariant. -/
theorem reflCocycle_eqOn_conductorCocycle {f : ℂ → ℂ} {Q : ℕ}
    (hfe : ∀ s, f s = (Q : ℂ) ^ (1 - 2 * s) * f (1 - s)) {U : Set ℂ} (hU : ∀ s ∈ U, f s ≠ 0) :
    Set.EqOn (reflCocycle f) (conductorCocycle Q) U := by
  intro s hs
  rw [conductorCocycle, reflCocycle_of_conductor hfe (hU s hs)]

end RHTower
