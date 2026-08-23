import GaloisForLFunctions.RHTower.SelbergClass.AffineGammaPoleLattice
import GaloisForLFunctions.HTGeometry.EulerQGammaContinuation

/-!
# Every trivial zero of `ζ` is simple

`Γ_ℝ(s) = π^{-s/2}Γ(s/2)` has a simple pole at every point of the lattice `s = -2k` (`k : ℕ`), and
the completed zeta function `Λ = Γ_ℝ·ζ` is analytic and nonvanishing there for `k ≥ 1` — its value
is `Λ(1+2k)`, which is nonzero because `ζ` has no zero right of the one-line.  Reading
`ζ = Λ/Γ_ℝ` on a punctured neighbourhood therefore gives

`meromorphicOrderAt ζ (-2k) = 0 - (-1) = 1`:

every trivial zero is simple.  This is a gap in mathlib, which records the trivial zeros
(`riemannZeta_neg_two_mul_nat_add_one`) but not their order.

It is exactly what makes the trivial zeros contribute no residue to Burnol's contour integral: the
Mellin transform of a Sonine function vanishes there, and a simple zero of `ζ` in the denominator
cannot outweigh it.

## Main results

* `meromorphicOrderAt_gammaR` — `Γ_ℝ` has a simple pole at each `-2k`.
* `analyticAt_completedRiemannZeta`, `completedRiemannZeta_ne_zero_of_one_lt_re`
* `meromorphicOrderAt_riemannZeta_trivial` — **the trivial zeros are simple**.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The archimedean factor -/

/-- `Γ_ℝ` as a product of an analytic unit and an affine Gamma factor. -/
theorem gammaR_eq_mul :
    Complex.Gammaℝ
      = (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
          * (fun z : ℂ => Complex.Gamma (((1 / 2 : ℝ) : ℂ) * z + 0)) := by
  funext z
  simp only [Pi.mul_apply, Complex.Gammaℝ_def]
  congr 2
  push_cast
  ring

theorem analyticAt_piCpow (z₀ : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) z₀ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrw : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      = fun z : ℂ => Complex.exp ((-z / 2) * (Real.log Real.pi : ℂ)) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hπ)),
      ← Complex.ofReal_log hπ.le]
    ring_nf
  rw [hrw]
  refine AnalyticAt.cexp ?_
  exact (analyticAt_id.neg.div_const).mul analyticAt_const

theorem piCpow_ne_zero (z₀ : ℂ) : (Real.pi : ℂ) ^ (-z₀ / 2) ≠ 0 := by
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))

theorem meromorphicOrderAt_piCpow (z₀ : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) z₀ = 0 := by
  rw [(analyticAt_piCpow z₀).meromorphicOrderAt_eq,
    (analyticAt_piCpow z₀).analyticOrderAt_eq_zero.2 (piCpow_ne_zero z₀)]
  simp

/-- `Γ_ℝ` has a simple pole at every point `-2k` of its pole lattice. -/
theorem meromorphicOrderAt_gammaR (k : ℕ) :
    meromorphicOrderAt Complex.Gammaℝ (-(2 * (k : ℂ))) = (-1 : ℤ) := by
  have hb : ((1 : ℝ) / 2) ≠ 0 := by norm_num
  have hlat : (-(2 * (k : ℂ))) = affineGammaAddPole 0 (1 / 2) k := by
    rw [affineGammaAddPole]
    push_cast
    ring
  have hΓ : meromorphicOrderAt
      (fun z : ℂ => Complex.Gamma (((1 / 2 : ℝ) : ℂ) * z + 0)) (-(2 * (k : ℂ)))
        = (-1 : ℤ) :=
    (meromorphicOrderAt_gamma_affineAdd_eq_neg_one_iff 0 _ hb).2 ⟨k, hlat⟩
  have hmΓ : MeromorphicAt (fun z : ℂ => Complex.Gamma (((1 / 2 : ℝ) : ℂ) * z + 0))
      (-(2 * (k : ℂ))) := by
    refine GaloisForLFunctions.HTGeometry.meromorphicAt_comp_affine
      (a := ((1 / 2 : ℝ) : ℂ)) (b := 0) ?_ ?_
    · simp
    · exact Meromorphic.meromorphicAt Meromorphic.Gamma
  rw [gammaR_eq_mul, meromorphicOrderAt_mul (analyticAt_piCpow _).meromorphicAt hmΓ,
    meromorphicOrderAt_piCpow, hΓ]
  simp

/-! ## The completed zeta function at a trivial zero -/

theorem analyticAt_completedRiemannZeta {z₀ : ℂ} (h0 : z₀ ≠ 0) (h1 : z₀ ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta z₀ := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [ContinuousAt.eventually_ne (g := fun s : ℂ => s) continuousAt_id h0,
    ContinuousAt.eventually_ne (g := fun s : ℂ => s) continuousAt_id h1] with s hs0 hs1
  exact differentiableAt_completedZeta hs0 hs1

theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  intro hzero
  have := riemannZeta_def_of_ne_zero hs0
  rw [hzero, zero_div] at this
  exact riemannZeta_ne_zero_of_one_le_re hs this

/-! ## Simplicity of the trivial zeros -/

/-- **Every trivial zero of `ζ` is simple.**  A gap in mathlib. -/
theorem meromorphicOrderAt_riemannZeta_trivial {k : ℕ} (hk : k ≠ 0) :
    meromorphicOrderAt riemannZeta (-(2 * (k : ℂ))) = (1 : ℤ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hre : (-(2 * (k : ℂ))).re = -(2 * (k : ℝ)) := by simp
  have hrelt : (-(2 * (k : ℂ))).re < 0 := by rw [hre]; linarith
  have h0 : (-(2 * (k : ℂ))) ≠ 0 := by
    intro h; rw [h] at hrelt; simp at hrelt
  have h1 : (-(2 * (k : ℂ))) ≠ 1 := by
    intro h; rw [h] at hrelt; norm_num at hrelt
  -- the completed zeta is analytic and nonvanishing at the trivial zero
  have hΛana : AnalyticAt ℂ completedRiemannZeta (-(2 * (k : ℂ))) :=
    analyticAt_completedRiemannZeta h0 h1
  have hΛne : completedRiemannZeta (-(2 * (k : ℂ))) ≠ 0 := by
    rw [← completedRiemannZeta_one_sub]
    refine completedRiemannZeta_ne_zero_of_one_le_re ?_
    have hsub : (1 - -(2 * (k : ℂ))).re = 1 + 2 * (k : ℝ) := by
      rw [Complex.sub_re, Complex.one_re, hre]; ring
    rw [hsub]; linarith
  have hΛord : meromorphicOrderAt completedRiemannZeta (-(2 * (k : ℂ))) = (0 : ℤ) := by
    rw [hΛana.meromorphicOrderAt_eq, hΛana.analyticOrderAt_eq_zero.2 hΛne]
    simp
  -- meromorphy of the archimedean factor
  have hΓmero : MeromorphicAt Complex.Gammaℝ (-(2 * (k : ℂ))) := by
    rw [gammaR_eq_mul]
    refine MeromorphicAt.mul (analyticAt_piCpow _).meromorphicAt ?_
    refine GaloisForLFunctions.HTGeometry.meromorphicAt_comp_affine
      (a := ((1 / 2 : ℝ) : ℂ)) (b := 0) ?_ ?_
    · simp
    · exact Meromorphic.meromorphicAt Meromorphic.Gamma
  -- the identity `ζ = Λ / Γ_ℝ` near the trivial zero
  have hev : riemannZeta =ᶠ[𝓝[≠] (-(2 * (k : ℂ)))] completedRiemannZeta / Complex.Gammaℝ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [ContinuousAt.eventually_ne (g := fun s : ℂ => s) continuousAt_id h0]
      with s hs
    simpa using riemannZeta_def_of_ne_zero hs
  rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_div hΛana.meromorphicAt hΓmero,
    hΛord, meromorphicOrderAt_gammaR k]
  decide

end

end RHTower
