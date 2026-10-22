import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation

/-!
# The real-analytic Eisenstein series at the Gaussian point: orbifold criticality and the quartic
# Grössencharacter Hessian

For `Re s > 1` let `E(z,s) = ½ Σ_{(m,n) primitive} (y/((mx+n)² + m²y²))^s` (the corpus series
`d4BMRawEisensteinPoincareSeries`). At the orbifold point `i`:

* `hasDerivAt_horizontal_gaussianPoint`, `hasDerivAt_vertical_gaussianPoint`: both first
  derivatives vanish (sign flip `(m,n) ↦ (m,-n)` and swap `(m,n) ↦ (n,m)`).
* `secondJets_gaussianPoint`: the trace of the Hessian is `s(s-1)E(i,s)`, and the traceless part is
  `E_xx - E_yy = -(s(s+1)/2) Σ' Re((n+im)⁴)/(m²+n²)^{s+2}`. Up to `ζ(2s)` the lattice sum is
  `4 L(s, ψ⁴)` for the quartic Grössencharacter `ψ⁴(α) = (α/|α|)⁴` of `ℚ(i)`, while `E(i,s)` is
  `ζ_{ℚ(i)}(s)` up to the same factor.

Geometric reading (loop card `rh-geometric-topological-loop-2026-10-06`, G8/G9). On the critical
line `F_t = E*(·,½+it)` is real. The nodal set of `F_t` passes through `i` exactly at the critical
zeros of `ζ_{ℚ(i)}`. There it is an X-crossing whose orientation is the sign of the quartic
Hecke L-value, and it degenerates exactly when that L-value also vanishes. This module proves the
identities on the absolute-convergence region. Their use on the critical line needs the
meromorphic continuation of both sides, which is not formalized here.
-/

open Complex

namespace RHTower.GaussianPointEisenstein

noncomputable section

/-- The Gaussian CM point `i = 0 + 1·i`. -/
def gaussianPoint : D4BMUpperHalfPlaneCoordinate := ⟨0, 1, one_pos⟩

/-- Sign flip of the second coordinate of a primitive pair. -/
def negSnd (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair :=
  ⟨(p.pair.1, -p.pair.2), by simpa [Int.gcd_neg] using p.primitive⟩

/-- Swap of the two coordinates of a primitive pair. -/
def swap (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair :=
  ⟨(p.pair.2, p.pair.1), by simpa [Int.gcd_comm] using p.primitive⟩

lemma negSnd_involutive : Function.Involutive negSnd := by
  intro p; cases p; simp [negSnd]

lemma swap_involutive : Function.Involutive swap := by
  intro p; cases p; simp [swap]

lemma quadratic_gaussianPoint (p : ℤ × ℤ) :
    d4BMPoincareQuadratic gaussianPoint p = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  simp [d4BMPoincareQuadratic, gaussianPoint]

lemma quadratic_negSnd (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic gaussianPoint (negSnd p).pair =
      d4BMPoincareQuadratic gaussianPoint p.pair := by
  simp [quadratic_gaussianPoint, negSnd]

lemma quadratic_swap (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic gaussianPoint (swap p).pair =
      d4BMPoincareQuadratic gaussianPoint p.pair := by
  simp [quadratic_gaussianPoint, swap]; ring

lemma seed_negSnd (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed gaussianPoint s (negSnd p) = d4BMPoincareSeed gaussianPoint s p := by
  simp only [d4BMPoincareSeed, quadratic_negSnd]

lemma seed_swap (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed gaussianPoint s (swap p) = d4BMPoincareSeed gaussianPoint s p := by
  simp only [d4BMPoincareSeed, quadratic_swap]

lemma quadratic_ne_zero (p : D4BMPrimitiveIntegerPair) :
    (d4BMPoincareQuadratic gaussianPoint p.pair : ℂ) ≠ 0 := by
  exact_mod_cast (d4BMPoincareQuadratic_pos gaussianPoint p.pair p.pair_ne_zero).ne'

/-- **Orbifold criticality, horizontal direction.** -/
theorem horizontalFirstJet_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareHorizontalFirstJet gaussianPoint P = 0 := by
  set f : D4BMPrimitiveIntegerPair → ℂ :=
    fun p => d4BMPoincareSeedHorizontalFirstJet gaussianPoint P.s p with hf
  have hodd : ∀ p, f (negSnd p) = -f p := by
    intro p
    simp only [hf, d4BMPoincareSeedHorizontalFirstJet, seed_negSnd, quadratic_negSnd,
      d4BMPoincareHorizontalLinear]
    simp [negSnd, gaussianPoint]
    ring
  have hperm : ∑' p, f (negSnd p) = ∑' p, f p :=
    (Function.Involutive.toPerm negSnd negSnd_involutive).tsum_eq f
  have hzero : ∑' p, f p = 0 := by
    have h2 : ∑' p, f p = -∑' p, f p :=
      calc ∑' p, f p = ∑' p, f (negSnd p) := hperm.symm
        _ = ∑' p, -f p := by simp only [hodd]
        _ = -∑' p, f p := tsum_neg
    linear_combination h2 / 2
  simp [d4BMRawPoincareHorizontalFirstJet, ← hf, hzero]

lemma quadratic_gaussianPoint_complex (p : D4BMPrimitiveIntegerPair) :
    (d4BMPoincareQuadratic gaussianPoint p.pair : ℂ) =
      (p.pair.1 : ℂ) ^ 2 + (p.pair.2 : ℂ) ^ 2 := by
  rw [quadratic_gaussianPoint]; push_cast; ring

lemma sq_add_sq_ne_zero (p : D4BMPrimitiveIntegerPair) :
    (p.pair.1 : ℂ) ^ 2 + (p.pair.2 : ℂ) ^ 2 ≠ 0 := by
  rw [← quadratic_gaussianPoint_complex]; exact quadratic_ne_zero p

/-- **Orbifold criticality, vertical direction.** -/
theorem verticalFirstJet_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareVerticalFirstJet gaussianPoint P = 0 := by
  set f : D4BMPrimitiveIntegerPair → ℂ :=
    fun p => d4BMPoincareSeedVerticalFirstJet gaussianPoint P.s p with hf
  have hpair : ∀ p, f p + f (swap p) = 0 := by
    intro p
    have hQ := sq_add_sq_ne_zero p
    have hQ' : (p.pair.2 : ℂ) ^ 2 + (p.pair.1 : ℂ) ^ 2 ≠ 0 := by rwa [add_comm]
    simp only [hf, d4BMPoincareSeedVerticalFirstJet, seed_swap, quadratic_gaussianPoint_complex]
    simp only [swap, gaussianPoint, Complex.ofReal_one]
    field_simp
    ring
  have hfs : Summable f := summable_d4BMPoincareSeedVerticalFirstJet gaussianPoint P
  have e := Function.Involutive.toPerm swap swap_involutive
  have hperm : ∑' p, f (swap p) = ∑' p, f p :=
    (Function.Involutive.toPerm swap swap_involutive).tsum_eq f
  have hfs' : Summable fun p => f (swap p) :=
    (Function.Involutive.toPerm swap swap_involutive).summable_iff.mpr hfs
  have hsum : ∑' p, (f p + f (swap p)) = ∑' p, f p + ∑' p, f (swap p) :=
    hfs.tsum_add hfs'
  have hzero : ∑' p, f p = 0 := by
    simp only [hpair, tsum_zero, hperm] at hsum
    linear_combination -hsum / 2
  simp [d4BMRawPoincareVerticalFirstJet, ← hf, hzero]

/-- The quartic Grössencharacter summand `Re((n + i m)⁴) / (m² + n²)²` times the seed. -/
def quarticTerm (s : ℂ) (p : D4BMPrimitiveIntegerPair) : ℂ :=
  ((p.pair.1 : ℂ) ^ 4 - 6 * (p.pair.1 : ℂ) ^ 2 * (p.pair.2 : ℂ) ^ 2 + (p.pair.2 : ℂ) ^ 4) /
    ((p.pair.1 : ℂ) ^ 2 + (p.pair.2 : ℂ) ^ 2) ^ 2 * d4BMPoincareSeed gaussianPoint s p

/-- **Traceless Hessian at the Gaussian point.** The difference of the horizontal and vertical
second derivatives of the Eisenstein series at `i` is `-(s(s+1)/2)` times the quartic
Grössencharacter lattice sum `Σ' Re((n+im)⁴)/(m²+n²)^{s+2}` over primitive pairs. -/
theorem secondJet_sub_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareHorizontalSecondJet gaussianPoint P -
        d4BMRawPoincareVerticalSecondJet gaussianPoint P =
      -(P.s * (P.s + 1) / 2) * ∑' p, quarticTerm P.s p := by
  set g : D4BMPrimitiveIntegerPair → ℂ := fun p =>
    d4BMPoincareSeedHorizontalSecondJet gaussianPoint P.s p -
      d4BMPoincareSeedVerticalSecondJet gaussianPoint P.s p with hg
  have hpair : ∀ p, g p + g (swap p) = -(2 * P.s * (P.s + 1)) * quarticTerm P.s p := by
    intro p
    have hQ := sq_add_sq_ne_zero p
    have hQ' : (p.pair.2 : ℂ) ^ 2 + (p.pair.1 : ℂ) ^ 2 ≠ 0 := by rwa [add_comm]
    simp only [hg, quarticTerm, d4BMPoincareSeedHorizontalSecondJet,
      d4BMPoincareSeedVerticalSecondJet, seed_swap, quadratic_gaussianPoint_complex,
      d4BMPoincareHorizontalLinear]
    simp only [swap, gaussianPoint, Complex.ofReal_one, mul_zero, zero_add]
    push_cast
    field_simp
    ring
  have hHs := summable_d4BMPoincareSeedHorizontalSecondJet gaussianPoint P
  have hVs := summable_d4BMPoincareSeedVerticalSecondJet gaussianPoint P
  have hgs : Summable g := hHs.sub hVs
  have hperm : ∑' p, g (swap p) = ∑' p, g p :=
    (Function.Involutive.toPerm swap swap_involutive).tsum_eq g
  have hgs' : Summable fun p => g (swap p) :=
    (Function.Involutive.toPerm swap swap_involutive).summable_iff.mpr hgs
  have hsum : ∑' p, (g p + g (swap p)) = ∑' p, g p + ∑' p, g (swap p) :=
    hgs.tsum_add hgs'
  have hgsum : ∑' p, g p = -(P.s * (P.s + 1)) * ∑' p, quarticTerm P.s p := by
    simp only [hpair, hperm, tsum_mul_left] at hsum
    linear_combination -hsum / 2
  have hraw : d4BMRawPoincareHorizontalSecondJet gaussianPoint P -
      d4BMRawPoincareVerticalSecondJet gaussianPoint P = (1 / 2 : ℂ) * ∑' p, g p := by
    simp only [d4BMRawPoincareHorizontalSecondJet, d4BMRawPoincareVerticalSecondJet, hg]
    rw [hHs.tsum_sub hVs]
    ring
  rw [hraw, hgsum]
  ring

/-- The Eisenstein series is horizontally critical at `i`: actual derivative `0`. -/
theorem hasDerivAt_horizontal_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (fun x : ℝ => d4BMRawEisensteinPoincareSeries
      (d4BMHorizontalCoordinate gaussianPoint x) P) 0 0 := by
  have h := hasDerivAt_d4BMRawEisensteinPoincareSeries_horizontal gaussianPoint P
  rw [horizontalFirstJet_gaussianPoint P] at h
  simpa [gaussianPoint] using h

/-- The Eisenstein series is vertically critical at `i`: actual derivative `0`. -/
theorem hasDerivAt_vertical_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMRawPoincareVerticalSlice gaussianPoint P) 0 1 := by
  have h := hasDerivAt_d4BMRawPoincareVerticalSlice gaussianPoint P
  rw [verticalFirstJet_gaussianPoint P] at h
  simpa [gaussianPoint] using h

/-- Trace and traceless parts of the Hessian at `i`: the trace is fixed by the eigen-equation
`Δ E = s(s-1) E`, the traceless part by the quartic Grössencharacter sum. -/
theorem secondJets_gaussianPoint (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareHorizontalSecondJet gaussianPoint P +
        d4BMRawPoincareVerticalSecondJet gaussianPoint P =
      P.s * (P.s - 1) * d4BMRawEisensteinPoincareSeries gaussianPoint P ∧
    d4BMRawPoincareHorizontalSecondJet gaussianPoint P -
        d4BMRawPoincareVerticalSecondJet gaussianPoint P =
      -(P.s * (P.s + 1) / 2) * ∑' p, quarticTerm P.s p := by
  refine ⟨?_, secondJet_sub_gaussianPoint P⟩
  have h := d4BM_rawEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue gaussianPoint P
  simpa [gaussianPoint] using h

end

end RHTower.GaussianPointEisenstein
