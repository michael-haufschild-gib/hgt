/-
# Combined germ-blindness: exact finite Euler data and the asymptotic tail, on one witness

Two independent blindness mechanisms are united here on a *single* carrier.  The finite-Euler head
`feBundle P` is divisor-inert on the strip (`FiniteEulerInert`): decorating a member by it changes no
strip vanishing order, so exact finite local Euler data carries no divisor constraint.  The
logarithmic-derivative tail is quartic-blind (`TailBlindness`): multiplying by the `V₄`-orbit quartic
of an off-line point leaves the asymptotic tail `deriv f / f` unchanged toward `re → ∞`, so an
asymptotic tiling condition sees no off-line surgery.

The doubly-decorated class `ShadowClass P F` collects the carriers that simultaneously carry the exact
`P`-Euler head (`FiniteEulerClass P`), stay eventually nonvanishing, and match a fixed tail reference
`F` (`DlogTail F`).  Its softness combines the two mechanisms on one witness: from any member `f₀`
that is nonvanishing at an off-line point `ρ`, one orbit-quartic multiplication `g = orbitQuartic ρ · f₀`
lands back in the *same* class — same finite exact Euler head, same asymptotic tail — yet raises the
order at `ρ` to `1`, so `g` carries off-line deck charge `−1` (`shadowClass_charged_witness`).  Taking
the finite Euler bundle itself as the base member (`ShadowClass P (feBundle P) (feBundle P)`, with
eventual nonvanishing on the right half-plane and the trivial self-tail) yields the capstone
`not_forcesRHParity_shadowClass`: the class matching exactly `feBundle P` in both its finite Euler data
and its logarithmic-derivative tail carries off-line charge, hence cannot force RH-grade parity.

No criterion that reads finite exact local Euler data joined with asymptotic tail data can force
RH-grade parity: both faces are simultaneously blind on a single object.  Any parity-forcing content of
the Euler germ is consumed only at the whole-object, non-asymptotic level — not in any finite truncation
and not in the asymptotic tail.
-/
import GaloisForLFunctions.RHTower.TailBlindness
import GaloisForLFunctions.RHTower.FiniteEulerInert

open Complex

namespace RHTower

/-! ### §1 The doubly-decorated class -/

/-- The **doubly-decorated class** `ShadowClass P F`: carriers that simultaneously carry the exact
finite `P`-Euler head, are eventually nonvanishing, and match the fixed logarithmic-derivative tail
reference `F`.  A member holds exact finite local Euler data *and* a prescribed asymptotic tail. -/
def ShadowClass (P : Finset ℕ) (F : ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  FiniteEulerClass P f ∧ EventuallyNonvanishing f ∧ DlogTail F f

/-! ### §2 The finite Euler bundle is a member of its own shadow class -/

/-- **The inverse Euler factor is zero-free on the left half-plane.**  For `Re w < 0` and `p > 1` one
has `‖exp(−w·log p)‖ = exp(−Re w·log p) > 1`, so `exp(−w·log p) ≠ 1` and `1 − exp(−w·log p) ≠ 0`.
This is the reflected companion of `eulerInvFactor_ne_zero` (which covers `Re w > 0`, norm `< 1`). -/
theorem eulerInvFactor_ne_zero_of_re_neg (p : ℕ) (hp : 1 < p) {w : ℂ} (hw : w.re < 0) :
    eulerInvFactor p w ≠ 0 := by
  intro h
  simp only [eulerInvFactor] at h
  have hE : Complex.exp (-(w * (Real.log p : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖Complex.exp (-(w * (Real.log p : ℂ)))‖ = 1 := by rw [hE, norm_one]
  rw [Complex.norm_exp] at hnorm
  have hre : (-(w * (Real.log p : ℂ))).re = -(w.re * Real.log p) := by
    rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre] at hnorm
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hgt : 1 < Real.exp (-(w.re * Real.log p)) := by
    rw [Real.one_lt_exp_iff]
    have : w.re * Real.log p < 0 := mul_neg_of_neg_of_pos hw hL
    linarith
  exact absurd hnorm (ne_of_gt hgt)

/-- **The finite Euler bundle is eventually nonvanishing.**  On the right half-plane `Re s ≥ 2` every
completed local factor `fePants p s = (1 − p^(−s))(1 − p^(−(1−s)))` is nonzero: the first factor
because `Re s > 0`, the mirror factor because `Re(1 − s) < 0`.  A finite product inherits this. -/
theorem eventuallyNonvanishing_feBundle (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) :
    EventuallyNonvanishing (feBundle P) := by
  refine ⟨2, fun s hs => ?_⟩
  unfold feBundle
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  show eulerInvFactor p s * eulerInvFactor p (1 - s) ≠ 0
  refine mul_ne_zero (eulerInvFactor_ne_zero p (hP p hp) (by linarith)) ?_
  refine eulerInvFactor_ne_zero_of_re_neg p (hP p hp) ?_
  rw [Complex.sub_re, Complex.one_re]; linarith

/-- Every function matches its own logarithmic-derivative tail: the difference `deriv f / f − deriv F / F`
is identically `0` when `F = f`, so `DlogTail f f` holds vacuously. -/
theorem dlogTail_self (F : ℂ → ℂ) : DlogTail F F := by
  intro ε hε
  refine ⟨0, fun s _ => ?_⟩
  rw [sub_self, norm_zero]; exact hε

/-- **Concrete tail-blindness for a finite Euler bundle.**  FE--Schwarz symmetry, eventual
nonvanishing, and logarithmic-derivative tail matching are all constructed for `feBundle P`, so
the generic tail-blindness theorem has no auxiliary interface premise left. -/
theorem not_forcesRHParity_feBundle_dlogTail {P : Finset ℕ}
    (hP : ∀ p ∈ P, 1 < p) :
    ¬ ForcesRHParity (fun f =>
      FESchwarz f ∧ EventuallyNonvanishing f ∧ DlogTail (feBundle P) f) :=
  not_forcesRHParity_of_dlogTail (feBundle P)
    (feBundle_fESchwarz P) (eventuallyNonvanishing_feBundle P hP) (dlogTail_self (feBundle P))

/-! ### §3 The combined charged witness -/

/-- **The shadow class plants off-line charge from any nonvanishing base member.**  Given a member
`f₀` of `ShadowClass P F` that is nonzero at an off-line, off-real point `ρ`, a single orbit-quartic
multiplication `g := orbitQuartic ρ · f₀` returns a member of the *same* class carrying off-line
charge.  The two decorations are simultaneously preserved: `g` still carries the exact `P`-Euler head
(`orbitQuartic ρ · G₀` is FE + Schwarz, so `feBundle P · (orbitQuartic ρ · G₀)` is a `FiniteEulerClass`
member), stays eventually nonvanishing (`eventuallyNonvanishing_orbitQuartic_mul`), and matches the
same tail `F` (`dlogTail_orbitQuartic_mul`).  Since `f₀ ρ ≠ 0` its order at `ρ` is `0`, so the quartic
raises the order of `g` at `ρ` to `1` — deck charge `(−1)^(1 : ℕ) = −1 ≠ 1`. -/
theorem shadowClass_charged_witness {P : Finset ℕ} {F f₀ : ℂ → ℂ}
    (hf₀ : ShadowClass P F f₀) {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0)
    (hf₀ρ : f₀ ρ ≠ 0) :
    ∃ g, ShadowClass P F g ∧ carrierCharge g 1 ρ ≠ 1 := by
  obtain ⟨⟨G₀, hG₀fes, hG₀eq⟩, hf₀nv, hf₀tail⟩ := hf₀
  have hf₀diff : Differentiable ℂ f₀ := by
    have hfe : f₀ = fun s => feBundle P s * G₀ s := funext hG₀eq
    rw [hfe]; exact (feBundle_fESchwarz P).1.mul hG₀fes.1
  have hf₀a : AnalyticAt ℂ f₀ ρ := hf₀diff.analyticAt ρ
  refine ⟨fun s => orbitQuartic ρ s * f₀ s, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨fun s => orbitQuartic ρ s * G₀ s, (fESchwarz_orbitQuartic ρ).mul hG₀fes, fun s => ?_⟩
    show orbitQuartic ρ s * f₀ s = feBundle P s * (orbitQuartic ρ s * G₀ s)
    rw [hG₀eq s]; ring
  · exact eventuallyNonvanishing_orbitQuartic_mul hf₀nv
  · exact dlogTail_orbitQuartic_mul hf₀diff hf₀nv hf₀tail
  · rw [carrierCharge_one_eq_neg_one_pow,
        analyticOrderAt_orbitQuartic_mul hre him hf₀a,
        analyticOrderAt_eq_zero.mpr (Or.inr hf₀ρ), add_zero, ENat.toNat_one]
    norm_num

/-! ### §4 The blindness capstone -/

/-- **The combined shadow class cannot force RH-grade parity.**  Take the finite Euler bundle itself as
the base member: `feBundle P` carries its own `P`-Euler head (decorate the constant `1`), is eventually
nonvanishing on the right half-plane (`eventuallyNonvanishing_feBundle`), and trivially matches its own
tail (`dlogTail_self`).  It is nonzero at the off-line strip point `⟨1/4, 1⟩` (`feBundle_ne_zero_on_strip`),
so `shadowClass_charged_witness` plants a member of the *same* class — matching `feBundle P` in both its
exact finite Euler data and its logarithmic-derivative tail — that carries off-line charge `−1`.  Through
`forcesRHParity_iff_categorical`, off-line charge excludes the categorical cell, so the class cannot force
RH-grade parity.  A parity-forcing criterion cannot factor through finite exact local data joined with
asymptotic tail data; the constraint content of the Euler germ is consumed only at the whole-object,
non-asymptotic level. -/
theorem not_forcesRHParity_shadowClass {P : Finset ℕ} (hP : ∀ p ∈ P, 1 < p) :
    ¬ ForcesRHParity (ShadowClass P (feBundle P)) := by
  rw [forcesRHParity_iff_categorical]
  intro hcat
  apply hcat
  have hre : (⟨1 / 4, 1⟩ : ℂ).re ≠ 1 / 2 := by show (1 / 4 : ℝ) ≠ 1 / 2; norm_num
  have him : (⟨1 / 4, 1⟩ : ℂ).im ≠ 0 := by show (1 : ℝ) ≠ 0; norm_num
  have h0 : 0 < (⟨1 / 4, 1⟩ : ℂ).re := by show (0 : ℝ) < 1 / 4; norm_num
  have h1 : (⟨1 / 4, 1⟩ : ℂ).re < 1 := by show (1 / 4 : ℝ) < 1; norm_num
  have hbase : ShadowClass P (feBundle P) (feBundle P) :=
    ⟨⟨fun _ => (1 : ℂ), fESchwarz_one, fun s => by rw [mul_one]⟩,
     eventuallyNonvanishing_feBundle P hP,
     dlogTail_self (feBundle P)⟩
  have hbaseρ : feBundle P (⟨1 / 4, 1⟩ : ℂ) ≠ 0 := feBundle_ne_zero_on_strip P hP h0 h1
  obtain ⟨g, hg, hgc⟩ := shadowClass_charged_witness hbase hre him hbaseρ
  exact ⟨(⟨1 / 4, 1⟩ : ℂ), hre, g, hg, hgc⟩

end RHTower
