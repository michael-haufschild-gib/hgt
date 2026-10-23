import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BezoutEffectivityAndTheBeurlingObstruction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HeckeIncidenceCartesianLaw

/-!
# The `λ`-Ring of the Scaling Surface: Adams Operations, Hecke Graphs, and Pole-Plane Splitting

In Weil's proof of the Riemann Hypothesis for a smooth projective curve `C / 𝔽_q`, the Frobenius
correspondences `Γ_m = (F^m × id)_* Δ` on `C × C` are the graphs of the Adams operations `ψ^m` on
the motive of `C`. Their intersection calculus rests on four algebraic identities before positivity
is invoked:

1. **Pole-plane projection and orthogonal splitting:** Every cycle class `x` splits orthogonally
   into its pole-plane component `P(x) = (x · V) H + (x · H) V ∈ ℝH ⊕ ℝV` and its primitive
   component `x° = x - P(x) ∈ {H, V}^⊥`, with `P(x) · P(y) = polar(x, y)` and
   `x° · y° = -defect(x, y)`.
2. **Adams action on the pole plane:** The `m`-th Frobenius correspondence fixes the horizontal
   fiber `V` (`ψ^m V = V`) and scales the vertical fiber `H` by the degree `q^m` (`ψ^m H = q^m H`);
   under the degree-normalized Adams operator `q^{-m/2} ψ^m`, the hyperbolic form on `ℝH ⊕ ℝV` is
   preserved isometrically (`H ↦ q^{m/2} H`, `V ↦ q^{-m/2} V`).
3. **Pullback and Lefschetz trace identity:** Two Frobenius graphs meet by relative pullback,
   `Γ_k · Γ_l = q^{min(k, l)} (Γ_{|k - l|} · Δ) = q^{min(k, l)} N_{|k - l|}`, where the Lefschetz
   number `N_m = Γ_m · Δ` splits additively into the pole trace `1 + q^m` and the primitive defect
   trace `-q^{m/2} defect(q^{-m/2} Γ_m, Δ)`.
4. **Universal `λ`-ring exponential:** Passing from Adams traces `j ↦ ψ_j` to symmetric powers via
   `σ_X(g) = exp(∑_{j ≥ 1} g(j) X^j / j)` turns the additive splitting of Lefschetz numbers into
   the multiplicative factorization `Z(C, X) = ((1 - X)(1 - qX))⁻¹ P_1(X)` in `ℂ⟦X⟧`.

This module constructs and formalizes unconditionally the corresponding `λ`-ring structure over `ℚ`
on the scaling surface (`scalingSurface`):

* **Orthogonal pole-plane projection (`PolarSurface.polarPart`):** On any `PolarSurface`, `polarPart`
  and `prim` form orthogonal idempotents decomposing `(E, pair)` into the hyperbolic pole plane
  `(ℝH ⊕ ℝV, polar)` and the primitive complement `(prim E, -defect)`.
* **Universal `λ`-ring exponential (`sigmaSeries`, `lambdaSeries`):** For any ghost-coordinate
  sequence `g : ℕ → ℂ`, the Newton–Witt recurrence defines `sigmaSeries g ∈ ℂ⟦X⟧` satisfying
  `HasGhost (sigmaSeries g) (ghostSeriesOf g)`. It is an exponential homomorphism
  `sigmaSeries (g₁ + g₂) = sigmaSeries g₁ * sigmaSeries g₂`, splits the pole trace `1 + q^j` off as
  `geom 1 * geom q`, and recovers `D.zetaSeries = D.poleZeta * D.hOnePoly` for every `CurveDatum`.
* **Calibration over `𝔽_q` (`CurveDatum.spanAdams`):** On the Frobenius span surface `D.windowSurface`,
  the normalized Frobenius shift `D.spanAdams m` acts on the pole plane by `(D.sqrtq⁻¹ ^ m, D.sqrtq ^ m)`,
  shifts Frobenius graph coordinates by `m` with weight `q^{-m/2}`, preserves `pair`, `polar`, and
  `defect` isometrically, and commutes with `polarPart` and `prim`.
* **Adams operations and Hecke correspondences over `ℚ` (`adamsOp`, `heckeCorrespondence`):**
  Logarithmic translation `scaleShift t f (u) = f(u - t)` preserves `realTests`, scales the pole
  pairings `(poleB, poleA)` by `(e^{-t/2}, e^{t/2})`, and translates the Weil cross-correlation
  `weilTest` by the lag difference (`weilTest_scaleShift_sub`), leaving `weilPair` and `localPair`
  translation-invariant. On `ScalingCycle`, the normalized Adams operator `adamsOp q = scalingAction (log q)`
  and unnormalized Hecke correspondence `heckeCorrespondence a = √a • adamsOp a` form exact
  multiplicative representations of `(ℝ_{>0}, ×)`. Every `adamsOp q` is an exact self-intersection,
  polar, and defect isometry of `scalingSurface` that commutes with `polarPart` and `prim`.
* **Hecke cycles as Frobenius graphs (`heckeCycle`, `arithLefschetz`):** The Hecke cycle
  `heckeCycle a g = heckeCorrespondence a (0, 0, g)` satisfies the rational-scale pullback identity
  `heckeCycle a g · heckeCycle b g = b * arithLefschetz (diagCycle g) (a / b)`. Along any prime
  tower `a = p^k`, `b = p^l`, this reduces to `p^{min(k, l)} arithLefschetz (diagCycle g) (p^{|k - l|})`,
  matching Weil's `Γ_k · Γ_l = q^{min(k, l)} N_{|k - l|}` verbatim. The arithmetic Lefschetz number
  splits orthogonally into `(a + 1) (x · H)(x · V)` on the pole plane and
  `-√a defect(adamsOp a x, x)` on the primitive complement, and `sigmaSeries` factors out the pole
  plane `geom 1 * geom q` along every geometric tower `q^j`.
* **Narrow-bump prime incidence (`weightedPrimeComb_scaleShift_eq_heckeIncidence`):** For integer
  Hecke scales `a, b ≥ 1`, cutoff `N ≥ max a b`, and a test bump `φ` supported in `[-δ, δ]` with
  `2δ < log(1 + 1/(max(a, b) N))`, the prime-comb pairing of `scaleShift (log a) φ` and
  `scaleShift (log b) φ` evaluates to `heckeIncidence a b * ∫ φ^2`, which by
  `HeckeIncidenceCartesianLaw` equals the single-prime Frobenius weight
  `towerWeight p |v_p(a) - v_p(b)| * ∫ φ^2` on matching prime axes and vanishes whenever `a` and `b`
  differ in two or more prime coordinates.
* **Zero-side eigenlaw, fake curves, non-`Λ` weights, and positive tests:** At every spectral mode
  `gammaOf ρ`, `scaleShift (log q)` multiplies `paperFT` by `q^{ρ - 1/2}` (reducing to `β_i^m` at
  curve zeros `q^{ρ - 1/2} = β_i`). The `λ`-ring splitting holds unconditionally for fake curves
  such as `goldenDatum` and is invariant under replacing `Λ` by any weight `lam : ℕ → ℝ`, while
  `adamsOp q` and `heckeCorrespondence q` preserve `posTestCone` with non-negative fiber
  intersections and non-negative prime-comb incidence.
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology BigOperators Finset PowerSeries Zeta23 RHTower
open RHTower.WeilSpectral
open scoped Pointwise ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Orthogonal Pole-Plane Splitting on an Abstract Polar Surface -/

namespace PolarSurface

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The pole-plane projection `P(x) = (x · V) H + (x · H) V` on a polar surface `S`, mapping any
cycle class into the hyperbolic plane `ℝH ⊕ ℝV`. -/
def polarPart (x : E) : E :=
  S.pair x S.V • S.H + S.pair x S.H • S.V

/-- Every cycle class decomposes into its pole-plane projection and its primitive part. -/
theorem polarPart_add_prim (x : E) : S.polarPart x + S.prim x = x := by
  simp only [polarPart, prim]
  abel

/-- The primitive projection is the complement `id - polarPart`. -/
theorem prim_eq_sub_polarPart (x : E) : S.prim x = x - S.polarPart x := by
  simp only [polarPart, prim, sub_sub]

@[simp]
theorem polarPart_zero : S.polarPart 0 = 0 := by
  simp [polarPart]

theorem polarPart_add (x y : E) :
    S.polarPart (x + y) = S.polarPart x + S.polarPart y := by
  simp only [polarPart, map_add, LinearMap.add_apply, add_smul]
  abel

theorem polarPart_smul (c : ℝ) (x : E) :
    S.polarPart (c • x) = c • S.polarPart x := by
  simp only [polarPart, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul, smul_add]

@[simp]
theorem polarPart_H : S.polarPart S.H = S.H := by
  simp [polarPart, S.pair_H_V, S.pair_H_H]

@[simp]
theorem polarPart_V : S.polarPart S.V = S.V := by
  simp [polarPart, S.pair_V_V, S.pair_V_H]

@[simp]
theorem prim_H : S.prim S.H = 0 := by
  rw [prim_eq_sub_polarPart, polarPart_H, sub_self]

@[simp]
theorem prim_V : S.prim S.V = 0 := by
  rw [prim_eq_sub_polarPart, polarPart_V, sub_self]

@[simp]
theorem pair_polarPart_H (x : E) : S.pair (S.polarPart x) S.H = S.pair x S.H := by
  simp [polarPart, S.pair_H_H, S.pair_V_H]

@[simp]
theorem pair_polarPart_V (x : E) : S.pair (S.polarPart x) S.V = S.pair x S.V := by
  simp [polarPart, S.pair_H_V, S.pair_V_V]

@[simp]
theorem polarPart_idem (x : E) : S.polarPart (S.polarPart x) = S.polarPart x := by
  rw [polarPart, pair_polarPart_V, pair_polarPart_H]
  rfl

@[simp]
theorem polarPart_prim (x : E) : S.polarPart (S.prim x) = 0 := by
  simp [polarPart, S.pair_prim_H, S.pair_prim_V]

@[simp]
theorem prim_polarPart (x : E) : S.prim (S.polarPart x) = 0 := by
  rw [prim_eq_sub_polarPart, polarPart_idem, sub_self]

@[simp]
theorem prim_idem (x : E) : S.prim (S.prim x) = S.prim x := by
  rw [prim_eq_sub_polarPart, polarPart_prim, sub_zero]

/-- The pole-plane projection is orthogonal to the primitive complement. -/
@[simp]
theorem pair_polarPart_prim (x y : E) : S.pair (S.polarPart x) (S.prim y) = 0 := by
  have hH : S.pair S.H (S.prim y) = 0 := by rw [S.pair_comm, S.pair_prim_H]
  have hV : S.pair S.V (S.prim y) = 0 := by rw [S.pair_comm, S.pair_prim_V]
  simp [polarPart, hH, hV]

@[simp]
theorem pair_prim_polarPart (x y : E) : S.pair (S.prim x) (S.polarPart y) = 0 := by
  rw [S.pair_comm, pair_polarPart_prim]

/-- On the pole plane, the intersection pairing equals the hyperbolic form `polar`. -/
theorem pair_polarPart (x y : E) :
    S.pair (S.polarPart x) (S.polarPart y) = S.polar x y := by
  simp only [polarPart, polar, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H]
  ring

/-- Orthogonal decomposition of the intersection pairing into the pole-plane pairing and the
primitive intersection pairing. -/
theorem pair_orthog_split (x y : E) :
    S.pair x y = S.pair (S.polarPart x) (S.polarPart y) + S.pair (S.prim x) (S.prim y) := by
  rw [pair_polarPart, S.pair_prim_prim, defect]
  ring

@[simp]
theorem defect_polarPart_left (x y : E) : S.defect (S.polarPart x) y = 0 := by
  rw [← neg_eq_zero, ← S.pair_prim_prim, prim_polarPart, map_zero, LinearMap.zero_apply]

@[simp]
theorem defect_polarPart_right (x y : E) : S.defect x (S.polarPart y) = 0 := by
  rw [← neg_eq_zero, ← S.pair_prim_prim, prim_polarPart, map_zero]

end PolarSurface

/-! ### 2. Universal `λ`-Ring Exponential and Ghost-Coordinate Splitting in `ℂ⟦X⟧` -/

/-- The ghost power series `∑_{j ≥ 1} g(j) X^j ∈ ℂ⟦X⟧` attached to an Adams-trace sequence
`g : ℕ → ℂ`. -/
def ghostSeriesOf (g : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun j => if j = 0 then 0 else g j

@[simp]
theorem constantCoeff_ghostSeriesOf (g : ℕ → ℂ) :
    constantCoeff (ghostSeriesOf g) = 0 := by
  simp [ghostSeriesOf]

@[simp]
theorem ghostSeriesOf_zero : ghostSeriesOf 0 = 0 := by
  ext n
  simp [ghostSeriesOf]

theorem ghostSeriesOf_add (g₁ g₂ : ℕ → ℂ) :
    ghostSeriesOf (g₁ + g₂) = ghostSeriesOf g₁ + ghostSeriesOf g₂ := by
  ext n
  simp only [ghostSeriesOf, coeff_mk, Pi.add_apply, map_add]
  split_ifs <;> ring

theorem ghostSeriesOf_neg (g : ℕ → ℂ) :
    ghostSeriesOf (-g) = -ghostSeriesOf g := by
  ext n
  simp only [ghostSeriesOf, coeff_mk, Pi.neg_apply, map_neg]
  split_ifs <;> ring

/-- Recursive Newton–Witt coefficients `σ_n(g)` of the universal `λ`-ring exponential
`exp(∑_{j ≥ 1} g(j) X^j / j)`: `σ_0(g) = 1` and
`(m + 1) σ_{m+1}(g) = ∑_{k=0}^m σ_k(g) g(m + 1 - k)`. -/
def sigmaCoeff (g : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 =>
    ((m : ℂ) + 1)⁻¹ *
      ∑ k : Fin (m + 1),
        have : k.1 < m + 1 := k.2
        sigmaCoeff g k.1 * g (m + 1 - k.1)

@[simp]
theorem sigmaCoeff_zero (g : ℕ → ℂ) : sigmaCoeff g 0 = 1 := by
  unfold sigmaCoeff
  rfl

theorem sigmaCoeff_succ (g : ℕ → ℂ) (m : ℕ) :
    sigmaCoeff g (m + 1) =
      ((m : ℂ) + 1)⁻¹ * ∑ k ∈ Finset.range (m + 1), sigmaCoeff g k * g (m + 1 - k) := by
  rw [sigmaCoeff]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => sigmaCoeff g k * g (m + 1 - k)) (m + 1)

/-- The universal symmetric-power generating series `σ_X(g) = exp(∑_{j ≥ 1} g(j) X^j / j) ∈ ℂ⟦X⟧`
reconstructing a `λ`-ring series from its Adams ghost coordinates `j ↦ g(j)`. -/
def sigmaSeries (g : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (sigmaCoeff g)

/-- The universal exterior-power generating series `λ_X(g) = σ_{-X}(-g) ∈ ℂ⟦X⟧` reconstructing the
`λ`-operations from the Adams ghost coordinates `j ↦ g(j)`. -/
def lambdaSeries (g : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => (-1 : ℂ) ^ n * sigmaCoeff (-g) n

@[simp]
theorem coeff_sigmaSeries (g : ℕ → ℂ) (n : ℕ) :
    coeff n (sigmaSeries g) = sigmaCoeff g n :=
  coeff_mk n (sigmaCoeff g)

@[simp]
theorem constantCoeff_sigmaSeries (g : ℕ → ℂ) :
    constantCoeff (sigmaSeries g) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_sigmaSeries, sigmaCoeff_zero]

private theorem sum_antidiagonal_eq_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (n : ℕ) :
    ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), f p.1 p.2 =
      ∑ i ∈ Finset.range (n + 1), f i (n - i) := by
  refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_range]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    omega
  · intro p hp q hq hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    apply Prod.ext hpq
    omega
  · intro i hi
    refine ⟨(i, n - i), ?_, rfl⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [Finset.mem_range] at hi
    omega
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    congr 2
    omega

/-- **Universal Newton–Witt identity:** for every sequence `g : ℕ → ℂ`, `sigmaSeries g` has ghost
series `ghostSeriesOf g` (`X (sigmaSeries g)' = sigmaSeries g * ghostSeriesOf g`). -/
theorem hasGhost_sigmaSeries (g : ℕ → ℂ) :
    HasGhost (sigmaSeries g) (ghostSeriesOf g) := by
  unfold HasGhost
  ext n
  rcases n with _ | m
  · rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul,
      constantCoeff_ghostSeriesOf, mul_zero]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_sigmaSeries, sigmaCoeff_succ]
    have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [mul_comm (((m : ℂ) + 1)⁻¹), mul_assoc, inv_mul_cancel₀ hm, mul_one,
      coeff_mul,
      sum_antidiagonal_eq_range
        (fun i j => coeff i (sigmaSeries g) * coeff j (ghostSeriesOf g)) (m + 1),
      Finset.sum_range_succ
        (fun i => coeff i (sigmaSeries g) * coeff (m + 1 - i) (ghostSeriesOf g)) (m + 1)]
    have hlast : coeff (m + 1) (sigmaSeries g) * coeff (m + 1 - (m + 1)) (ghostSeriesOf g) = 0 := by
      simp [ghostSeriesOf]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hsub : m + 1 - k ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hk)
    simp [coeff_sigmaSeries, ghostSeriesOf, hsub]

/-- Uniqueness of `sigmaSeries g` as the power series with constant term `1` and ghost series
`ghostSeriesOf g`. -/
theorem sigmaSeries_eq_of_hasGhost {F : ℂ⟦X⟧} {g : ℕ → ℂ}
    (hF : HasGhost F (ghostSeriesOf g)) (h0 : constantCoeff F = 1) :
    sigmaSeries g = F :=
  eq_of_hasGhost (hasGhost_sigmaSeries g) hF
    ((constantCoeff_sigmaSeries g).trans h0.symm) (constantCoeff_ghostSeriesOf g)

@[simp]
theorem sigmaSeries_zero : sigmaSeries 0 = 1 :=
  sigmaSeries_eq_of_hasGhost (by rw [ghostSeriesOf_zero]; exact hasGhost_one) (map_one constantCoeff)

/-- **Exponential homomorphism law of the universal `λ`-ring series:** addition of Adams ghost
coordinates corresponds to multiplication of symmetric-power series. -/
theorem sigmaSeries_add (g₁ g₂ : ℕ → ℂ) :
    sigmaSeries (g₁ + g₂) = sigmaSeries g₁ * sigmaSeries g₂ := by
  refine sigmaSeries_eq_of_hasGhost ?_ ?_
  · rw [ghostSeriesOf_add]
    exact hasGhost_mul (hasGhost_sigmaSeries g₁) (hasGhost_sigmaSeries g₂)
  · simp [map_mul]

/-- Inverting the sign of the Adams ghost coordinates inverts the symmetric-power series. -/
theorem sigmaSeries_mul_neg (g : ℕ → ℂ) :
    sigmaSeries g * sigmaSeries (-g) = 1 := by
  rw [← sigmaSeries_add, add_neg_cancel, sigmaSeries_zero]

/-- A pure power ghost `j ↦ a^j` (rank-one Adams eigenline) exponentiates to the geometric series
`(1 - aX)⁻¹`. -/
theorem sigmaSeries_pow (a : ℂ) :
    sigmaSeries (fun j => a ^ j) = geom a :=
  sigmaSeries_eq_of_hasGhost (hasGhost_geom a) (by simp [geom])

/-- **Pole-plane splitting in `ℂ⟦X⟧`:** any Adams trace sequence of the form `(1 + q^j) + g_prim(j)`
splits off the universal pole factor `((1 - X)(1 - qX))⁻¹ = geom 1 * geom q`. -/
theorem sigmaSeries_pole_split (q : ℂ) (g_prim : ℕ → ℂ) :
    sigmaSeries ((fun j => (1 : ℂ) + q ^ j) + g_prim) =
      (geom 1 * geom q) * sigmaSeries g_prim := by
  have h1 : (fun j : ℕ => (1 : ℂ) + q ^ j) = (fun j => (1 : ℂ) ^ j) + (fun j => q ^ j) := by
    ext j
    simp
  rw [sigmaSeries_add, h1, sigmaSeries_add, sigmaSeries_pow, sigmaSeries_pow]

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- For any curve datum `D`, the universal `λ`-ring exponential of the Frobenius point counts
`j ↦ N_j(D)` is the zeta series `D.zetaSeries`. -/
theorem sigmaSeries_pointCount :
    sigmaSeries (fun j => (D.pointCount j : ℂ)) = D.zetaSeries :=
  sigmaSeries_eq_of_hasGhost D.zetaSeries_hasGhost D.constantCoeff_zetaSeries

/-- For any curve datum `D`, the universal `λ`-ring exponential of the primitive `H¹` Frobenius
traces `j ↦ -∑_i α_i^j` is the spectral polynomial `D.hOnePoly = ∏_i (1 - α_i X)`. -/
theorem sigmaSeries_primTrace :
    sigmaSeries (fun j => -∑ i : ι, D.alpha i ^ j) = D.hOnePoly := by
  refine sigmaSeries_eq_of_hasGhost ?_ ?_
  · have hG : ghostSeriesOf (fun j => -∑ i : ι, D.alpha i ^ j) =
        ∑ i : ι, -geomTail (D.alpha i) := by
      ext j
      rcases j with _ | j
      · simp [ghostSeriesOf, geomTail]
      · simp [ghostSeriesOf, geomTail, Finset.sum_neg_distrib]
    rw [hG]
    exact hasGhost_prod Finset.univ (fun i : ι => 1 - C (D.alpha i) * X)
      (fun i : ι => -geomTail (D.alpha i)) (fun i _ => hasGhost_one_sub (D.alpha i))
  · simp [hOnePoly, map_prod]

/-- **Pole-plane factorization of the curve zeta series via `sigmaSeries`:** the `λ`-ring
exponential of `N_j(D) = (1 + q^j) - ∑_i α_i^j` factors into `D.poleZeta` times the `λ`-ring
exponential of the primitive traces. -/
theorem sigmaSeries_pointCount_split :
    sigmaSeries (fun j => (D.pointCount j : ℂ)) =
      D.poleZeta * sigmaSeries (fun j => -∑ i : ι, D.alpha i ^ j) := by
  rw [D.sigmaSeries_pointCount, D.sigmaSeries_primTrace, zetaSeries]

end CurveDatum

/-! ### 3. Calibration over `𝔽_q`: Adams Operations on the Frobenius Span Surface -/

/-- Right shift of a Frobenius-graph coefficient sequence by `m` steps:
`(spanShift m d)_k = d_{k - m}` for `k ≥ m` and `0` for `k < m`. -/
def spanShift (m : ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  if m ≤ k then d (k - m) else 0

/-- Right shift of a finite Frobenius window `S ⊆ ℕ` by `m`. -/
def windowShift (m : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.map ⟨fun k => k + m, fun _ _ h => Nat.add_right_cancel h⟩

@[simp]
theorem spanShift_zero (d : ℕ → ℝ) : spanShift 0 d = d := by
  ext k
  simp [spanShift]

@[simp]
theorem windowShift_zero (S : Finset ℕ) : windowShift 0 S = S := by
  ext k
  simp [windowShift]

theorem windowB_spanShift (m : ℕ) (S : Finset ℕ) (d : ℕ → ℝ) :
    windowB (windowShift m S) (spanShift m d) = windowB S d := by
  simp only [windowB, windowShift, Finset.sum_map, Function.Embedding.coeFn_mk, spanShift,
    le_add_iff_nonneg_left, zero_le, ↓reduceIte, Nat.add_sub_cancel]

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem windowA_spanShift (m : ℕ) (S : Finset ℕ) (d : ℕ → ℝ) :
    D.windowA (windowShift m S) (spanShift m d) = D.q ^ m * D.windowA S d := by
  simp only [windowA, windowShift, Finset.sum_map, Function.Embedding.coeFn_mk, spanShift,
    le_add_iff_nonneg_left, zero_le, ↓reduceIte, Nat.add_sub_cancel, pow_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem windowGraph_spanShift (m : ℕ) (S : Finset ℕ) (d₁ d₂ : ℕ → ℝ) :
    D.windowGraph (windowShift m S) (spanShift m d₁) (spanShift m d₂) =
      D.q ^ m * D.windowGraph S d₁ d₂ := by
  simp only [windowGraph, windowShift, Finset.sum_map, Function.Embedding.coeFn_mk, spanShift,
    le_add_iff_nonneg_left, zero_le, ↓reduceIte, Nat.add_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [graphPair, min_add_add_right, Nat.dist_add_add_right, pow_add]
  ring

/-- The degree-normalized `m`-th Adams operator on the Frobenius span cycle space over `𝔽_q`:
scales `H` by `q^{-m/2}`, scales `V` by `q^{m/2}`, and shifts each Frobenius graph coordinate by
`m` with normalization `q^{-m/2}`. -/
def spanAdams (m : ℕ) (x : SpanCycle) : SpanCycle :=
  (D.sqrtq⁻¹ ^ m * x.1, D.sqrtq ^ m * x.2.1, (D.sqrtq⁻¹ ^ m) • spanShift m x.2.2)

@[simp]
theorem spanAdams_H (m : ℕ) (S : Finset ℕ) :
    D.spanAdams m (D.windowSurface S).H =
      (D.sqrtq⁻¹ ^ m) • (D.windowSurface (windowShift m S)).H := by
  ext <;> simp [spanAdams, windowSurface, spanShift]

@[simp]
theorem spanAdams_V (m : ℕ) (S : Finset ℕ) :
    D.spanAdams m (D.windowSurface S).V =
      (D.sqrtq ^ m) • (D.windowSurface (windowShift m S)).V := by
  ext <;> simp [spanAdams, windowSurface, spanShift]

private theorem inv_sqrtq_pow_mul_sqrtq_pow (m : ℕ) :
    D.sqrtq⁻¹ ^ m * D.sqrtq ^ m = 1 := by
  have hpos : D.sqrtq ≠ 0 := ne_of_gt D.sqrtq_pos
  rw [← mul_pow, inv_mul_cancel₀ hpos, one_pow]

private theorem q_pow_eq_sqrtq_pow_sq (m : ℕ) :
    D.q ^ m = D.sqrtq ^ m * D.sqrtq ^ m := by
  rw [← mul_pow, ← sq, D.sqrtq_sq]

private theorem inv_sqrtq_pow_mul_q_pow (m : ℕ) :
    D.sqrtq⁻¹ ^ m * D.q ^ m = D.sqrtq ^ m := by
  rw [D.q_pow_eq_sqrtq_pow_sq, ← mul_assoc, D.inv_sqrtq_pow_mul_sqrtq_pow, one_mul]

private theorem inv_sqrtq_pow_sq_mul_q_pow (m : ℕ) :
    D.sqrtq⁻¹ ^ m * (D.sqrtq⁻¹ ^ m * D.q ^ m) = 1 := by
  rw [D.inv_sqrtq_pow_mul_q_pow, D.inv_sqrtq_pow_mul_sqrtq_pow]

/-- Intersection with `H` scales by `q^{m/2}` under `D.spanAdams m`. -/
theorem pair_spanAdams_H (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanAdams m x)
        (D.windowSurface (windowShift m S)).H =
      D.sqrtq ^ m * (D.windowSurface S).pair x (D.windowSurface S).H := by
  rw [D.windowSurface_pair_H, D.windowSurface_pair_H]
  simp only [spanAdams, D.windowA_smul, D.windowA_spanShift]
  calc D.sqrtq ^ m * x.2.1 + D.sqrtq⁻¹ ^ m * (D.q ^ m * D.windowA S x.2.2)
      = D.sqrtq ^ m * x.2.1 + (D.sqrtq⁻¹ ^ m * D.q ^ m) * D.windowA S x.2.2 := by ring
    _ = D.sqrtq ^ m * (x.2.1 + D.windowA S x.2.2) := by
          rw [D.inv_sqrtq_pow_mul_q_pow]; ring

/-- Intersection with `V` scales by `q^{-m/2}` under `D.spanAdams m`. -/
theorem pair_spanAdams_V (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanAdams m x)
        (D.windowSurface (windowShift m S)).V =
      D.sqrtq⁻¹ ^ m * (D.windowSurface S).pair x (D.windowSurface S).V := by
  rw [D.windowSurface_pair_V, D.windowSurface_pair_V]
  simp only [spanAdams, windowB_smul, windowB_spanShift]
  ring

/-- Over `𝔽_q`, the normalized Adams operator `D.spanAdams m` preserves the pole-plane form `polar`. -/
theorem polar_spanAdams (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).polar (D.spanAdams m x) (D.spanAdams m y) =
      (D.windowSurface S).polar x y := by
  simp only [PolarSurface.polar, D.pair_spanAdams_H, D.pair_spanAdams_V]
  have h1 := D.inv_sqrtq_pow_mul_sqrtq_pow m
  calc D.sqrtq ^ m * (D.windowSurface S).pair x (D.windowSurface S).H *
        (D.sqrtq⁻¹ ^ m * (D.windowSurface S).pair y (D.windowSurface S).V) +
      D.sqrtq⁻¹ ^ m * (D.windowSurface S).pair x (D.windowSurface S).V *
        (D.sqrtq ^ m * (D.windowSurface S).pair y (D.windowSurface S).H)
      = (D.sqrtq⁻¹ ^ m * D.sqrtq ^ m) *
          ((D.windowSurface S).pair x (D.windowSurface S).H *
            (D.windowSurface S).pair y (D.windowSurface S).V +
          (D.windowSurface S).pair x (D.windowSurface S).V *
            (D.windowSurface S).pair y (D.windowSurface S).H) := by ring
    _ = (D.windowSurface S).polar x y := by rw [h1, one_mul]; rfl

/-- Over `𝔽_q`, the normalized Adams operator `D.spanAdams m` is an exact intersection isometry. -/
theorem pair_spanAdams (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).pair (D.spanAdams m x) (D.spanAdams m y) =
      (D.windowSurface S).pair x y := by
  have hsymm : ∀ d₁ d₂, D.windowGraph (windowShift m S) d₁ (D.sqrtq⁻¹ ^ m • d₂) =
      D.sqrtq⁻¹ ^ m * D.windowGraph (windowShift m S) d₁ d₂ := by
    intro d₁ d₂
    rw [D.windowGraph_symm, D.windowGraph_smul_left, D.windowGraph_symm]
  simp only [windowSurface, spanAdams, windowPair_apply, windowPairFun,
    D.windowA_smul, D.windowA_spanShift, windowB_smul, windowB_spanShift,
    D.windowGraph_smul_left, hsymm, D.windowGraph_spanShift]
  have h1 := D.inv_sqrtq_pow_mul_sqrtq_pow m
  have h3 := D.inv_sqrtq_pow_sq_mul_q_pow m
  calc D.sqrtq⁻¹ ^ m * x.1 * (D.sqrtq ^ m * y.2.1) +
        D.sqrtq ^ m * x.2.1 * (D.sqrtq⁻¹ ^ m * y.1) +
        D.sqrtq⁻¹ ^ m * x.1 * (D.sqrtq⁻¹ ^ m * (D.q ^ m * D.windowA S y.2.2)) +
        D.sqrtq⁻¹ ^ m * y.1 * (D.sqrtq⁻¹ ^ m * (D.q ^ m * D.windowA S x.2.2)) +
        D.sqrtq ^ m * x.2.1 * (D.sqrtq⁻¹ ^ m * windowB S y.2.2) +
        D.sqrtq ^ m * y.2.1 * (D.sqrtq⁻¹ ^ m * windowB S x.2.2) +
        D.sqrtq⁻¹ ^ m * (D.sqrtq⁻¹ ^ m * (D.q ^ m * D.windowGraph S x.2.2 y.2.2))
      = (D.sqrtq⁻¹ ^ m * D.sqrtq ^ m) *
          (x.1 * y.2.1 + x.2.1 * y.1 + x.2.1 * windowB S y.2.2 + y.2.1 * windowB S x.2.2) +
        (D.sqrtq⁻¹ ^ m * (D.sqrtq⁻¹ ^ m * D.q ^ m)) *
          (x.1 * D.windowA S y.2.2 + y.1 * D.windowA S x.2.2 + D.windowGraph S x.2.2 y.2.2) := by
          ring
    _ = x.1 * y.2.1 + x.2.1 * y.1 +
        x.1 * D.windowA S y.2.2 + y.1 * D.windowA S x.2.2 +
        x.2.1 * windowB S y.2.2 + y.2.1 * windowB S x.2.2 +
        D.windowGraph S x.2.2 y.2.2 := by
          rw [h1, h3]
          ring

/-- Over `𝔽_q`, `D.spanAdams m` preserves the Hodge defect. -/
theorem defect_spanAdams (m : ℕ) (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface (windowShift m S)).defect (D.spanAdams m x) (D.spanAdams m y) =
      (D.windowSurface S).defect x y := by
  simp only [PolarSurface.defect, D.polar_spanAdams, D.pair_spanAdams]

/-- Over `𝔽_q`, the pole-plane projection commutes with `D.spanAdams m`. -/
theorem polarPart_spanAdams (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).polarPart (D.spanAdams m x) =
      D.spanAdams m ((D.windowSurface S).polarPart x) := by
  rw [PolarSurface.polarPart, PolarSurface.polarPart, D.pair_spanAdams_V, D.pair_spanAdams_H]
  ext <;> simp [windowSurface, spanAdams, spanShift]

/-- Over `𝔽_q`, the primitive projection commutes with `D.spanAdams m`. -/
theorem prim_spanAdams (m : ℕ) (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface (windowShift m S)).prim (D.spanAdams m x) =
      D.spanAdams m ((D.windowSurface S).prim x) := by
  rw [PolarSurface.prim, PolarSurface.prim, D.pair_spanAdams_V, D.pair_spanAdams_H]
  ext <;> simp [windowSurface, spanAdams, spanShift, mul_sub]

end CurveDatum

/-! ### 4. Adams Operations and Hecke Correspondences on the Scaling Surface over `ℚ` -/

/-- Logarithmic scale translation `(scaleShift t f)(u) = f(u - t)` on the real line. -/
def scaleShift (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => f (u - t)

@[simp]
theorem scaleShift_apply (t : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    scaleShift t f u = f (u - t) := rfl

@[simp]
theorem scaleShift_zero (f : ℝ → ℝ) : scaleShift 0 f = f := by
  ext u
  simp [scaleShift]

theorem scaleShift_add (s t : ℝ) (f : ℝ → ℝ) :
    scaleShift (s + t) f = scaleShift s (scaleShift t f) := by
  ext u
  simp only [scaleShift_apply]
  congr 1
  ring

@[simp]
theorem scaleShift_zero_fun (t : ℝ) : scaleShift t (0 : ℝ → ℝ) = 0 := rfl

theorem scaleShift_add_fun (t : ℝ) (f g : ℝ → ℝ) :
    scaleShift t (f + g) = scaleShift t f + scaleShift t g := rfl

theorem scaleShift_smul_fun (t c : ℝ) (f : ℝ → ℝ) :
    scaleShift t (c • f) = c • scaleShift t f := rfl

/-- Complexification commutes with logarithmic scale translation. -/
theorem cx_scaleShift (t : ℝ) (f : ℝ → ℝ) :
    cx (scaleShift t f) = fun u => cx f (u - t) := rfl

/-- Logarithmic scale translation preserves the smooth compactly supported test space `realTests`. -/
theorem scaleShift_mem (t : ℝ) {f : ℝ → ℝ} (hf : f ∈ realTests) :
    scaleShift t f ∈ realTests :=
  ⟨hf.1.comp (contDiff_id.sub contDiff_const), hf.2.comp_homeomorph (Homeomorph.subRight t)⟩

/-- Under `scaleShift t`, the horizontal pole functional `poleB f = ∫ f(u) e^{-u/2} du` scales by
`e^{-t/2}`. -/
theorem poleB_scaleShift (t : ℝ) (f : ℝ → ℝ) :
    poleB (scaleShift t f) = Real.exp (-t / 2) * poleB f := by
  simp only [poleB, scaleShift]
  have heq : (fun u => f (u - t) * Real.exp (-u / 2)) =
      fun u => Real.exp (-t / 2) * (f (u - t) * Real.exp (-(u - t) / 2)) := by
    ext u
    rw [show -u / 2 = -t / 2 + -(u - t) / 2 by ring, Real.exp_add]
    ring
  rw [heq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun v => f v * Real.exp (-v / 2)) t]

/-- Under `scaleShift t`, the vertical pole functional `poleA f = ∫ f(u) e^{u/2} du` scales by
`e^{t/2}`. -/
theorem poleA_scaleShift (t : ℝ) (f : ℝ → ℝ) :
    poleA (scaleShift t f) = Real.exp (t / 2) * poleA f := by
  simp only [poleA, scaleShift]
  have heq : (fun u => f (u - t) * Real.exp (u / 2)) =
      fun u => Real.exp (t / 2) * (f (u - t) * Real.exp ((u - t) / 2)) := by
    ext u
    rw [show u / 2 = t / 2 + (u - t) / 2 by ring, Real.exp_add]
    ring
  rw [heq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun v => f v * Real.exp (v / 2)) t]

/-- The Weil cross-correlation of two real functions as a real integral:
`EF.weilTest (cx f) (cx g) x = ∫ u, f(u) g(u - x) du`. -/
theorem weilTest_ofReal (f g : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (cx f) (cx g) x = ((∫ u, f u * g (u - x) : ℝ) : ℂ) := by
  rw [EF.weilTest, MeasureTheory.convolution_def, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, cx, Complex.conj_ofReal, neg_sub]
  push_cast
  ring

/-- **Weil cross-correlation translation identity:** shifting `f` by `s` and `g` by `t` shifts the
Weil cross-correlation `EF.weilTest (cx f) (cx g)` by `-s + t`. -/
theorem weilTest_scaleShift (s t : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (cx (scaleShift s f)) (cx (scaleShift t g)) x =
      EF.weilTest (cx f) (cx g) (x - s + t) := by
  rw [weilTest_ofReal, weilTest_ofReal]
  congr 1
  simp only [scaleShift]
  have heq : (fun u => f (u - s) * g (u - x - t)) =
      fun u => f (u - s) * g ((u - s) - (x - s + t)) := by
    ext u
    congr 2
    ring
  rw [heq, MeasureTheory.integral_sub_right_eq_self (fun v => f v * g (v - (x - s + t))) s]

/-- Shifting both arguments of `EF.weilTest` depends only on the relative lag `s - t`. -/
theorem weilTest_scaleShift_sub (s t : ℝ) (f g : ℝ → ℝ) :
    EF.weilTest (cx (scaleShift s f)) (cx (scaleShift t g)) =
      EF.weilTest (cx (scaleShift (s - t) f)) (cx g) := by
  ext x
  have h2 := weilTest_scaleShift (s - t) 0 f g x
  rw [scaleShift_zero] at h2
  rw [weilTest_scaleShift, h2]
  congr 1
  ring

/-- Simultaneous scale translation `scaleShift t` leaves `EF.weilTest` pointwise invariant. -/
@[simp]
theorem weilTest_scaleShift_same (t : ℝ) (f g : ℝ → ℝ) :
    EF.weilTest (cx (scaleShift t f)) (cx (scaleShift t g)) =
      EF.weilTest (cx f) (cx g) := by
  rw [weilTest_scaleShift_sub, sub_self, scaleShift_zero]

/-- Shifting `f` by `s` and `g` by `t` in `weilPair` reduces to the relative shift `s - t`. -/
theorem weilPair_scaleShift (s t : ℝ) (f g : ℝ → ℝ) :
    weilPair (scaleShift s f) (scaleShift t g) =
      weilPair (scaleShift (s - t) f) g := by
  simp only [weilPair, weilTest_scaleShift_sub s t f g]

/-- Simultaneous scale translation is an exact isometry of `weilPair`. -/
@[simp]
theorem weilPair_scaleShift_same (t : ℝ) (f g : ℝ → ℝ) :
    weilPair (scaleShift t f) (scaleShift t g) = weilPair f g := by
  rw [weilPair_scaleShift, sub_self, scaleShift_zero]

/-- Simultaneous scale translation preserves the local intersection pairing `localPair`. -/
@[simp]
theorem localPair_scaleShift_same (t : ℝ) (f g : ℝ → ℝ) :
    localPair (scaleShift t f) (scaleShift t g) = localPair f g := by
  simp only [localPair, poleB_scaleShift, poleA_scaleShift, weilPair_scaleShift_same]
  have hexp : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  calc Real.exp (-t / 2) * poleB f * (Real.exp (t / 2) * poleA g) +
        Real.exp (t / 2) * poleA f * (Real.exp (-t / 2) * poleB g) - weilPair f g
      = (Real.exp (-t / 2) * Real.exp (t / 2)) * (poleB f * poleA g + poleA f * poleB g) -
          weilPair f g := by ring
    _ = poleB f * poleA g + poleA f * poleB g - weilPair f g := by rw [hexp, one_mul]

/-- The additive scaling action on `ScalingCycle = ℝ × ℝ × realTests`: scales `H` by `e^{t/2}`,
scales `V` by `e^{-t/2}`, and translates the test function by `scaleShift t`. -/
def scalingAction (t : ℝ) : ScalingCycle →ₗ[ℝ] ScalingCycle where
  toFun x :=
    (Real.exp (t / 2) * x.1, Real.exp (-t / 2) * x.2.1,
      ⟨scaleShift t x.2.2.1, scaleShift_mem t x.2.2.2⟩)
  map_add' x y := by
    ext
    · simp [mul_add]
    · simp [mul_add]
    · rfl
  map_smul' c x := by
    ext
    · simp [mul_left_comm]
    · simp [mul_left_comm]
    · rfl

@[simp]
theorem scalingAction_zero : scalingAction 0 = LinearMap.id := by
  ext x <;> simp [scalingAction]

theorem scalingAction_add (s t : ℝ) (x : ScalingCycle) :
    scalingAction (s + t) x = scalingAction s (scalingAction t x) := by
  ext
  · simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, add_div, Real.exp_add, mul_assoc]
  · simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show -(s + t) / 2 = -s / 2 + -t / 2 by ring, Real.exp_add, mul_assoc]
  · simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, scaleShift_add]

/-- The degree-normalized Adams operation `ψ^q_norm = scalingAction (log q)` on the scaling surface
for a positive scale `q > 0`. -/
def adamsOp (q : ℝ) : ScalingCycle →ₗ[ℝ] ScalingCycle :=
  scalingAction (Real.log q)

/-- The unnormalized Hecke correspondence `T_a = √a • adamsOp a` on the scaling surface, matching
the Frobenius correspondence `Γ_m` of degree `a = q^m` over `𝔽_q`. -/
def heckeCorrespondence (a : ℝ) : ScalingCycle →ₗ[ℝ] ScalingCycle :=
  Real.sqrt a • adamsOp a

@[simp]
theorem adamsOp_one : adamsOp 1 = LinearMap.id := by
  simp [adamsOp]

theorem adamsOp_mul {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : ScalingCycle) :
    adamsOp (p * q) x = adamsOp p (adamsOp q x) := by
  rw [adamsOp, Real.log_mul (ne_of_gt hp) (ne_of_gt hq), scalingAction_add]
  rfl

theorem adamsOp_inv (q : ℝ) (x : ScalingCycle) :
    adamsOp q⁻¹ x = scalingAction (-Real.log q) x := by
  rw [adamsOp, Real.log_inv]

theorem adamsOp_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ScalingCycle) :
    adamsOp (a / b) x = scalingAction (Real.log a - Real.log b) x := by
  rw [adamsOp, Real.log_div (ne_of_gt ha) (ne_of_gt hb)]

theorem adamsOp_mul_inv {q : ℝ} (hq : 0 < q) (x : ScalingCycle) :
    adamsOp q (adamsOp q⁻¹ x) = x := by
  rw [← adamsOp_mul hq (inv_pos.mpr hq), mul_inv_cancel₀ (ne_of_gt hq), adamsOp_one,
    LinearMap.id_apply]

theorem adamsOp_pow {q : ℝ} (hq : 0 < q) (m : ℕ) (x : ScalingCycle) :
    adamsOp (q ^ m) x = (adamsOp q ^ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', adamsOp_mul hq (pow_pos hq m), ih]
    rfl

@[simp]
theorem heckeCorrespondence_one : heckeCorrespondence 1 = LinearMap.id := by
  simp [heckeCorrespondence]

theorem heckeCorrespondence_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ScalingCycle) :
    heckeCorrespondence (a * b) x = heckeCorrespondence a (heckeCorrespondence b x) := by
  simp only [heckeCorrespondence, LinearMap.smul_apply, map_smul, adamsOp_mul ha hb,
    Real.sqrt_mul (le_of_lt ha), smul_smul, mul_comm]

theorem heckeCorrespondence_pow {q : ℝ} (hq : 0 < q) (m : ℕ) (x : ScalingCycle) :
    heckeCorrespondence (q ^ m) x = (heckeCorrespondence q ^ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', heckeCorrespondence_mul hq (pow_pos hq m), ih]
    rfl

private theorem exp_half_log {q : ℝ} (hq : 0 < q) :
    Real.exp (Real.log q / 2) = Real.sqrt q := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
  ring_nf

private theorem exp_neg_half_log {q : ℝ} (hq : 0 < q) :
    Real.exp (-Real.log q / 2) = (Real.sqrt q)⁻¹ := by
  rw [neg_div, Real.exp_neg, exp_half_log hq]

/-- On the pole plane of `scalingSurface`, `adamsOp q` scales `H` by `√q`. -/
@[simp]
theorem adamsOp_H {q : ℝ} (hq : 0 < q) :
    adamsOp q scalingSurface.H = Real.sqrt q • scalingSurface.H := by
  ext <;> simp [adamsOp, scalingAction, scalingSurface, exp_half_log hq]

/-- On the pole plane of `scalingSurface`, `adamsOp q` scales `V` by `(√q)⁻¹`. -/
@[simp]
theorem adamsOp_V {q : ℝ} (hq : 0 < q) :
    adamsOp q scalingSurface.V = (Real.sqrt q)⁻¹ • scalingSurface.V := by
  ext <;> simp [adamsOp, scalingAction, scalingSurface, exp_neg_half_log hq]

/-- On the pole plane of `scalingSurface`, the Hecke correspondence `T_a` scales `H` by `a`
(`T_a H = a H`), matching `Γ_m H = q^m H` over `𝔽_q`. -/
@[simp]
theorem heckeCorrespondence_H {a : ℝ} (ha : 0 < a) :
    heckeCorrespondence a scalingSurface.H = a • scalingSurface.H := by
  rw [heckeCorrespondence, LinearMap.smul_apply, adamsOp_H ha, smul_smul,
    Real.mul_self_sqrt (le_of_lt ha)]

/-- On the pole plane of `scalingSurface`, the Hecke correspondence `T_a` fixes `V`
(`T_a V = V`), matching `Γ_m V = V` over `𝔽_q`. -/
@[simp]
theorem heckeCorrespondence_V {a : ℝ} (ha : 0 < a) :
    heckeCorrespondence a scalingSurface.V = scalingSurface.V := by
  have hsqrt : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  rw [heckeCorrespondence, LinearMap.smul_apply, adamsOp_V ha, smul_smul,
    mul_inv_cancel₀ hsqrt, one_smul]

theorem scalingSurface_pair_H (x : ScalingCycle) :
    scalingSurface.pair x scalingSurface.H = x.2.1 + poleB x.2.2 := by
  simp only [scalingSurface, scalingPair_apply, scalingPairFun, Submodule.coe_zero,
    poleB_zero, poleA_zero, localPair_zero_right]
  ring

theorem scalingSurface_pair_V (x : ScalingCycle) :
    scalingSurface.pair x scalingSurface.V = x.1 + poleA x.2.2 := by
  simp only [scalingSurface, scalingPair_apply, scalingPairFun, Submodule.coe_zero,
    poleB_zero, poleA_zero, localPair_zero_right]
  ring

/-- Intersection with `H` scales by `e^{-t/2}` under `scalingAction t`. -/
theorem pair_scalingAction_H (t : ℝ) (x : ScalingCycle) :
    scalingSurface.pair (scalingAction t x) scalingSurface.H =
      Real.exp (-t / 2) * scalingSurface.pair x scalingSurface.H := by
  rw [scalingSurface_pair_H, scalingSurface_pair_H]
  simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, poleB_scaleShift]
  ring

/-- Intersection with `V` scales by `e^{t/2}` under `scalingAction t`. -/
theorem pair_scalingAction_V (t : ℝ) (x : ScalingCycle) :
    scalingSurface.pair (scalingAction t x) scalingSurface.V =
      Real.exp (t / 2) * scalingSurface.pair x scalingSurface.V := by
  rw [scalingSurface_pair_V, scalingSurface_pair_V]
  simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, poleA_scaleShift]
  ring

theorem pair_adamsOp_H {q : ℝ} (hq : 0 < q) (x : ScalingCycle) :
    scalingSurface.pair (adamsOp q x) scalingSurface.H =
      (Real.sqrt q)⁻¹ * scalingSurface.pair x scalingSurface.H := by
  rw [adamsOp, pair_scalingAction_H, exp_neg_half_log hq]

theorem pair_adamsOp_V {q : ℝ} (hq : 0 < q) (x : ScalingCycle) :
    scalingSurface.pair (adamsOp q x) scalingSurface.V =
      Real.sqrt q * scalingSurface.pair x scalingSurface.V := by
  rw [adamsOp, pair_scalingAction_V, exp_half_log hq]

/-- Under the Hecke correspondence `T_a`, the horizontal degree `x · H` is preserved. -/
theorem pair_heckeCorrespondence_H {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    scalingSurface.pair (heckeCorrespondence a x) scalingSurface.H =
      scalingSurface.pair x scalingSurface.H := by
  have hsqrt : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  simp only [heckeCorrespondence, LinearMap.smul_apply, map_smul,
    smul_eq_mul, pair_adamsOp_H ha, ← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]

/-- Under the Hecke correspondence `T_a`, the vertical degree `x · V` scales by `a`. -/
theorem pair_heckeCorrespondence_V {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    scalingSurface.pair (heckeCorrespondence a x) scalingSurface.V =
      a * scalingSurface.pair x scalingSurface.V := by
  simp only [heckeCorrespondence, LinearMap.smul_apply, map_smul,
    smul_eq_mul, pair_adamsOp_V ha, ← mul_assoc, Real.mul_self_sqrt (le_of_lt ha)]

/-- `scalingAction t` preserves the pole-plane hyperbolic form `polar` on `scalingSurface`. -/
@[simp]
theorem polar_scalingAction (t : ℝ) (x y : ScalingCycle) :
    scalingSurface.polar (scalingAction t x) (scalingAction t y) =
      scalingSurface.polar x y := by
  simp only [PolarSurface.polar, pair_scalingAction_H, pair_scalingAction_V]
  have hexp : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  calc Real.exp (-t / 2) * scalingSurface.pair x scalingSurface.H *
        (Real.exp (t / 2) * scalingSurface.pair y scalingSurface.V) +
      Real.exp (t / 2) * scalingSurface.pair x scalingSurface.V *
        (Real.exp (-t / 2) * scalingSurface.pair y scalingSurface.H)
      = (Real.exp (-t / 2) * Real.exp (t / 2)) *
          (scalingSurface.pair x scalingSurface.H * scalingSurface.pair y scalingSurface.V +
           scalingSurface.pair x scalingSurface.V * scalingSurface.pair y scalingSurface.H) := by
          ring
    _ = scalingSurface.polar x y := by rw [hexp, one_mul]; rfl

/-- `scalingAction t` is an exact intersection isometry of `scalingSurface`. -/
@[simp]
theorem pair_scalingAction (t : ℝ) (x y : ScalingCycle) :
    scalingSurface.pair (scalingAction t x) (scalingAction t y) =
      scalingSurface.pair x y := by
  simp only [scalingSurface, scalingPair_apply, scalingPairFun, scalingAction,
    LinearMap.coe_mk, AddHom.coe_mk, poleB_scaleShift, poleA_scaleShift, localPair_scaleShift_same]
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  calc Real.exp (t / 2) * x.1 * (Real.exp (-t / 2) * y.2.1) +
        Real.exp (-t / 2) * x.2.1 * (Real.exp (t / 2) * y.1) +
        Real.exp (t / 2) * x.1 * (Real.exp (-t / 2) * poleB y.2.2) +
        Real.exp (-t / 2) * x.2.1 * (Real.exp (t / 2) * poleA y.2.2) +
        Real.exp (t / 2) * y.1 * (Real.exp (-t / 2) * poleB x.2.2) +
        Real.exp (-t / 2) * y.2.1 * (Real.exp (t / 2) * poleA x.2.2) +
        localPair x.2.2 y.2.2
      = (Real.exp (t / 2) * Real.exp (-t / 2)) *
          (x.1 * y.2.1 + x.2.1 * y.1 + x.1 * poleB y.2.2 + x.2.1 * poleA y.2.2 +
           y.1 * poleB x.2.2 + y.2.1 * poleA x.2.2) +
        localPair x.2.2 y.2.2 := by ring
    _ = x.1 * y.2.1 + x.2.1 * y.1 + x.1 * poleB y.2.2 + x.2.1 * poleA y.2.2 +
        y.1 * poleB x.2.2 + y.2.1 * poleA x.2.2 + localPair x.2.2 y.2.2 := by
        rw [hexp, one_mul]

/-- `scalingAction t` preserves the Hodge defect on `scalingSurface`. -/
@[simp]
theorem defect_scalingAction (t : ℝ) (x y : ScalingCycle) :
    scalingSurface.defect (scalingAction t x) (scalingAction t y) =
      scalingSurface.defect x y := by
  simp only [PolarSurface.defect, polar_scalingAction, pair_scalingAction]

/-- Adjointness of `scalingAction`: shifting `x` by `s` and `y` by `t` depends only on `s - t`. -/
theorem pair_scalingAction_sub (s t : ℝ) (x y : ScalingCycle) :
    scalingSurface.pair (scalingAction s x) (scalingAction t y) =
      scalingSurface.pair (scalingAction (s - t) x) y := by
  rw [← pair_scalingAction (-t) (scalingAction s x) (scalingAction t y),
    ← scalingAction_add, ← scalingAction_add, neg_add_cancel, scalingAction_zero,
    LinearMap.id_apply, show -t + s = s - t by ring]

theorem defect_scalingAction_sub (s t : ℝ) (x y : ScalingCycle) :
    scalingSurface.defect (scalingAction s x) (scalingAction t y) =
      scalingSurface.defect (scalingAction (s - t) x) y := by
  rw [← defect_scalingAction (-t) (scalingAction s x) (scalingAction t y),
    ← scalingAction_add, ← scalingAction_add, neg_add_cancel, scalingAction_zero,
    LinearMap.id_apply, show -t + s = s - t by ring]

/-- Every Adams operation `adamsOp q` preserves the pole-plane form `polar`. -/
@[simp]
theorem polar_adamsOp (q : ℝ) (x y : ScalingCycle) :
    scalingSurface.polar (adamsOp q x) (adamsOp q y) = scalingSurface.polar x y :=
  polar_scalingAction (Real.log q) x y

/-- Every Adams operation `adamsOp q` is an exact intersection isometry of `scalingSurface`. -/
@[simp]
theorem pair_adamsOp (q : ℝ) (x y : ScalingCycle) :
    scalingSurface.pair (adamsOp q x) (adamsOp q y) = scalingSurface.pair x y :=
  pair_scalingAction (Real.log q) x y

/-- Every Adams operation `adamsOp q` preserves the Hodge defect on `scalingSurface`. -/
@[simp]
theorem defect_adamsOp (q : ℝ) (x y : ScalingCycle) :
    scalingSurface.defect (adamsOp q x) (adamsOp q y) = scalingSurface.defect x y :=
  defect_scalingAction (Real.log q) x y

/-- Relative pullback law for `adamsOp`: `adamsOp a x · adamsOp b y = adamsOp (a / b) x · y`. -/
theorem pair_adamsOp_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ScalingCycle) :
    scalingSurface.pair (adamsOp a x) (adamsOp b y) =
      scalingSurface.pair (adamsOp (a / b) x) y := by
  rw [adamsOp, adamsOp, pair_scalingAction_sub, ← adamsOp_div ha hb]

/-- Adjoint of `adamsOp q` with respect to the intersection pairing is `adamsOp q⁻¹`. -/
theorem pair_adamsOp_adj (q : ℝ) (x y : ScalingCycle) :
    scalingSurface.pair (adamsOp q x) y = scalingSurface.pair x (adamsOp q⁻¹ y) := by
  rw [adamsOp, adamsOp_inv, ← pair_scalingAction (-Real.log q) (scalingAction (Real.log q) x) y,
    ← scalingAction_add, neg_add_cancel, scalingAction_zero, LinearMap.id_apply]

/-- **Pole-plane splitting under Adams operations:** `polarPart` commutes with `scalingAction t`. -/
theorem polarPart_scalingAction (t : ℝ) (x : ScalingCycle) :
    scalingSurface.polarPart (scalingAction t x) =
      scalingAction t (scalingSurface.polarPart x) := by
  rw [PolarSurface.polarPart, PolarSurface.polarPart, pair_scalingAction_V, pair_scalingAction_H]
  refine Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_))
  · simp [scalingSurface, scalingAction]
  · simp [scalingSurface, scalingAction]
  · ext u
    simp [scalingSurface, scalingAction]

/-- **Primitive-part splitting under Adams operations:** `prim` commutes with `scalingAction t`. -/
theorem prim_scalingAction (t : ℝ) (x : ScalingCycle) :
    scalingSurface.prim (scalingAction t x) =
      scalingAction t (scalingSurface.prim x) := by
  rw [PolarSurface.prim, PolarSurface.prim, pair_scalingAction_V, pair_scalingAction_H]
  refine Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_))
  · simp [scalingSurface, scalingAction, mul_sub]
  · simp [scalingSurface, scalingAction, mul_sub]
  · ext u
    simp [scalingSurface, scalingAction, scaleShift]

/-- `polarPart` commutes with every Adams operation `adamsOp q`. -/
theorem polarPart_adamsOp (q : ℝ) (x : ScalingCycle) :
    scalingSurface.polarPart (adamsOp q x) = adamsOp q (scalingSurface.polarPart x) :=
  polarPart_scalingAction (Real.log q) x

/-- `prim` commutes with every Adams operation `adamsOp q`. -/
theorem prim_adamsOp (q : ℝ) (x : ScalingCycle) :
    scalingSurface.prim (adamsOp q x) = adamsOp q (scalingSurface.prim x) :=
  prim_scalingAction (Real.log q) x

/-- `polarPart` commutes with every Hecke correspondence `heckeCorrespondence a`. -/
theorem polarPart_heckeCorrespondence (a : ℝ) (x : ScalingCycle) :
    scalingSurface.polarPart (heckeCorrespondence a x) =
      heckeCorrespondence a (scalingSurface.polarPart x) := by
  simp only [heckeCorrespondence, LinearMap.smul_apply, PolarSurface.polarPart_smul,
    polarPart_adamsOp]

/-- `prim` commutes with every Hecke correspondence `heckeCorrespondence a`. -/
theorem prim_heckeCorrespondence (a : ℝ) (x : ScalingCycle) :
    scalingSurface.prim (heckeCorrespondence a x) =
      heckeCorrespondence a (scalingSurface.prim x) := by
  simp only [heckeCorrespondence, LinearMap.smul_apply, PolarSurface.prim_eq_sub_polarPart,
    PolarSurface.polarPart_smul, polarPart_adamsOp, map_sub]

/-- Under `heckeCorrespondence a`, the intersection pairing scales by `a`. -/
theorem pair_heckeCorrespondence {a : ℝ} (ha : 0 ≤ a) (x y : ScalingCycle) :
    scalingSurface.pair (heckeCorrespondence a x) (heckeCorrespondence a y) =
      a * scalingSurface.pair x y := by
  simp only [heckeCorrespondence, LinearMap.smul_apply, map_smul, smul_eq_mul, pair_adamsOp,
    ← mul_assoc, Real.mul_self_sqrt ha]

/-- Under `heckeCorrespondence a`, the Hodge defect scales by `a`. -/
theorem defect_heckeCorrespondence {a : ℝ} (ha : 0 ≤ a) (x y : ScalingCycle) :
    scalingSurface.defect (heckeCorrespondence a x) (heckeCorrespondence a y) =
      a * scalingSurface.defect x y := by
  rw [← neg_inj, ← scalingSurface.pair_prim_prim, prim_heckeCorrespondence,
    prim_heckeCorrespondence, pair_heckeCorrespondence ha, scalingSurface.pair_prim_prim, mul_neg]

/-! ### 5. Hecke Cycles as Frobenius Graphs, Arithmetic Lefschetz Numbers, and Pole Splitting -/

/-- The arithmetic Lefschetz number `L(x, a) = T_a x · x` of a cycle class `x : ScalingCycle` at
scale `a > 0`, analogous to `N_m = Γ_m · Δ` on `C × C`. -/
def arithLefschetz (x : ScalingCycle) (a : ℝ) : ℝ :=
  scalingSurface.pair (heckeCorrespondence a x) x

/-- On the pole plane `ℝH ⊕ ℝV`, the arithmetic Lefschetz number at scale `a > 0` is
`(a + 1)(x · H)(x · V)`, matching the pole contribution `1 + q^m` when `(x · H)(x · V) = 1`. -/
theorem arithLefschetz_polarPart (x : ScalingCycle) {a : ℝ} (ha : 0 < a) :
    arithLefschetz (scalingSurface.polarPart x) a =
      (a + 1) * (scalingSurface.pair x scalingSurface.H * scalingSurface.pair x scalingSurface.V) := by
  rw [arithLefschetz, ← polarPart_heckeCorrespondence, scalingSurface.pair_polarPart,
    PolarSurface.polar, pair_heckeCorrespondence_H ha, pair_heckeCorrespondence_V ha]
  ring

/-- On the primitive complement `{H, V}^⊥`, the arithmetic Lefschetz number at scale `a` is
`-√a defect(adamsOp a x, x)`. -/
theorem arithLefschetz_prim (x : ScalingCycle) (a : ℝ) :
    arithLefschetz (scalingSurface.prim x) a =
      -Real.sqrt a * scalingSurface.defect (adamsOp a x) x := by
  rw [arithLefschetz, heckeCorrespondence, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, ← prim_adamsOp, scalingSurface.pair_prim_prim]
  ring

/-- **Orthogonal pole-plane splitting of the arithmetic Lefschetz number:** `L(x, a)` is the sum of
its pole-plane Lefschetz number and its primitive Lefschetz number. -/
theorem arithLefschetz_split (x : ScalingCycle) (a : ℝ) :
    arithLefschetz x a =
      arithLefschetz (scalingSurface.polarPart x) a + arithLefschetz (scalingSurface.prim x) a := by
  rw [arithLefschetz, scalingSurface.pair_orthog_split (heckeCorrespondence a x) x,
    polarPart_heckeCorrespondence, prim_heckeCorrespondence]
  rfl

/-- Explicit Lefschetz trace formula on `scalingSurface` for `a > 0`:
`L(x, a) = (a + 1)(x · H)(x · V) - √a defect(adamsOp a x, x)`. -/
theorem arithLefschetz_eq (x : ScalingCycle) {a : ℝ} (ha : 0 < a) :
    arithLefschetz x a =
      (a + 1) * (scalingSurface.pair x scalingSurface.H * scalingSurface.pair x scalingSurface.V) -
        Real.sqrt a * scalingSurface.defect (adamsOp a x) x := by
  rw [arithLefschetz_split, arithLefschetz_polarPart x ha, arithLefschetz_prim]
  ring

/-- **Tower `λ`-ring pole-plane factorization on `scalingSurface`:** for any cycle `x` of unit
polar degree `(x · H)(x · V) = 1` and any base scale `q > 0`, the universal `λ`-ring exponential
of the tower Lefschetz numbers `j ↦ L(x, q^j)` splits off the pole factor `geom 1 * geom q`. -/
theorem sigmaSeries_arithLefschetz_split (x : ScalingCycle)
    (hx : scalingSurface.pair x scalingSurface.H * scalingSurface.pair x scalingSurface.V = 1)
    {q : ℝ} (hq : 0 < q) :
    sigmaSeries (fun j => (arithLefschetz x (q ^ j) : ℂ)) =
      (geom 1 * geom (q : ℂ)) *
        sigmaSeries (fun j => (arithLefschetz (scalingSurface.prim x) (q ^ j) : ℂ)) := by
  have htrace :
      (fun j : ℕ => (arithLefschetz x (q ^ j) : ℂ)) =
        (fun j : ℕ => (1 : ℂ) + (q : ℂ) ^ j) +
          (fun j : ℕ => (arithLefschetz (scalingSurface.prim x) (q ^ j) : ℂ)) := by
    ext j
    simp only [Pi.add_apply, arithLefschetz_split x (q ^ j),
      arithLefschetz_polarPart x (pow_pos hq j), hx, mul_one]
    push_cast
    ring
  rw [htrace, sigmaSeries_pole_split]

/-- The diagonal cycle `Δ_g = (0, 0, g)` of a test profile `g ∈ realTests` on the scaling surface. -/
def diagCycle (g : realTests) : ScalingCycle :=
  (0, 0, g)

/-- The Hecke cycle `Γ_a(g) = T_a Δ_g = √a • adamsOp a (0, 0, g)` at scale `a` on the scaling
surface: the Frobenius graph of the Adams operation `adamsOp a`. -/
def heckeCycle (a : ℝ) (g : realTests) : ScalingCycle :=
  heckeCorrespondence a (diagCycle g)

@[simp]
theorem heckeCycle_one (g : realTests) : heckeCycle 1 g = diagCycle g := by
  simp [heckeCycle]

theorem heckeCycle_H {a : ℝ} (ha : 0 < a) (g : realTests) :
    scalingSurface.pair (heckeCycle a g) scalingSurface.H = poleB g.1 := by
  rw [heckeCycle, pair_heckeCorrespondence_H ha, scalingSurface_pair_H]
  simp [diagCycle]

theorem heckeCycle_V {a : ℝ} (ha : 0 < a) (g : realTests) :
    scalingSurface.pair (heckeCycle a g) scalingSurface.V = a * poleA g.1 := by
  rw [heckeCycle, pair_heckeCorrespondence_V ha, scalingSurface_pair_V]
  simp [diagCycle]

/-- For two diagonal cycles `Δ_f, Δ_g` shifted by `adamsOp a` and `adamsOp b`, the Hodge defect is
the shifted Weil pairing `weilPair (scaleShift (log a) f) (scaleShift (log b) g)`. -/
theorem defect_adamsOp_diagCycle (a b : ℝ) (f g : realTests) :
    scalingSurface.defect (adamsOp a (diagCycle f)) (adamsOp b (diagCycle g)) =
      weilPair (scaleShift (Real.log a) f.1) (scaleShift (Real.log b) g.1) := by
  have heq1 : adamsOp a (diagCycle f) =
      (0, 0, ⟨scaleShift (Real.log a) f.1, scaleShift_mem (Real.log a) f.2⟩) := by
    ext <;> simp [adamsOp, scalingAction, diagCycle]
  have heq2 : adamsOp b (diagCycle g) =
      (0, 0, ⟨scaleShift (Real.log b) g.1, scaleShift_mem (Real.log b) g.2⟩) := by
    ext <;> simp [adamsOp, scalingAction, diagCycle]
  rw [heq1, heq2, scalingSurface_defect_tests]

/-- Explicit arithmetic Lefschetz number of the diagonal cycle `Δ_g`:
`L(Δ_g, a) = (a + 1) poleB(g) poleA(g) - √a weilPair(scaleShift (log a) g, g)`. -/
theorem arithLefschetz_diagCycle (g : realTests) {a : ℝ} (ha : 0 < a) :
    arithLefschetz (diagCycle g) a =
      (a + 1) * (poleB g.1 * poleA g.1) -
        Real.sqrt a * weilPair (scaleShift (Real.log a) g.1) g.1 := by
  have hd : scalingSurface.defect (adamsOp a (diagCycle g)) (diagCycle g) =
      weilPair (scaleShift (Real.log a) g.1) g.1 := by
    simpa using defect_adamsOp_diagCycle a 1 g g
  rw [arithLefschetz_eq (diagCycle g) ha, hd, scalingSurface_pair_H, scalingSurface_pair_V]
  simp [diagCycle]

/-- **Rational-scale pullback / Lefschetz identity for Hecke cycles:** two Hecke cycles at positive
scales `a, b > 0` intersect as `Γ_a(g) · Γ_b(g) = b * L(Δ_g, a / b)`. -/
theorem pair_heckeCycle (g : realTests) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    scalingSurface.pair (heckeCycle a g) (heckeCycle b g) =
      b * arithLefschetz (diagCycle g) (a / b) := by
  simp only [heckeCycle, arithLefschetz, heckeCorrespondence, LinearMap.smul_apply, map_smul,
    smul_eq_mul]
  rw [pair_adamsOp_div ha hb, Real.sqrt_div (le_of_lt ha)]
  have hsqrt : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (le_of_lt hb)
  calc Real.sqrt b * (Real.sqrt a *
          scalingSurface.pair (adamsOp (a / b) (diagCycle g)) (diagCycle g))
      = (Real.sqrt b * Real.sqrt b) * (Real.sqrt a / Real.sqrt b *
          scalingSurface.pair (adamsOp (a / b) (diagCycle g)) (diagCycle g)) := by
          field_simp [hsqrt]
    _ = b * (Real.sqrt a / Real.sqrt b *
          scalingSurface.pair (adamsOp (a / b) (diagCycle g)) (diagCycle g)) := by
          rw [hsq]

/-- **Prime-tower Frobenius graph intersection law:** along any prime or real tower `p^k, p^l`
(`p > 0`), Hecke cycles intersect by `Γ_{p^k}(g) · Γ_{p^l}(g) = p^{min(k, l)} L(Δ_g, p^{|k - l|})`,
matching Weil's `CurveDatum.graphPair` (`Γ_k · Γ_l = q^{min(k, l)} N_{|k - l|}`) verbatim. -/
theorem pair_heckeCycle_pow (g : realTests) {p : ℝ} (hp : 0 < p) (k l : ℕ) :
    scalingSurface.pair (heckeCycle (p ^ k) g) (heckeCycle (p ^ l) g) =
      p ^ min k l * arithLefschetz (diagCycle g) (p ^ Nat.dist k l) := by
  rcases le_total k l with hkl | hlk
  · rw [scalingSurface.pair_comm, pair_heckeCycle g (pow_pos hp l) (pow_pos hp k),
      min_eq_left hkl, Nat.dist_eq_sub_of_le hkl, div_eq_mul_inv,
      ← pow_sub₀ p (ne_of_gt hp) hkl]
  · rw [pair_heckeCycle g (pow_pos hp k) (pow_pos hp l),
      min_eq_right hlk, Nat.dist_comm, Nat.dist_eq_sub_of_le hlk, div_eq_mul_inv,
      ← pow_sub₀ p (ne_of_gt hp) hlk]

/-- A finite linear combination `c_H H + c_V V + ∑_{a ∈ S} d(a) Γ_a(g)` of the pole plane and
Hecke cycles on the scaling surface. -/
def heckeSpanCycle (cH cV : ℝ) (S : Finset ℝ) (d : ℝ → ℝ) (g : realTests) : ScalingCycle :=
  cH • scalingSurface.H + cV • scalingSurface.V + ∑ a ∈ S, d a • heckeCycle a g

/-- The primitive projection of a Hecke span cycle kills `c_H H + c_V V` and projects each Hecke
cycle `Γ_a(g)` to its primitive component. -/
theorem prim_heckeSpanCycle (cH cV : ℝ) (S : Finset ℝ) (d : ℝ → ℝ) (g : realTests) :
    scalingSurface.prim (heckeSpanCycle cH cV S d g) =
      ∑ a ∈ S, d a • scalingSurface.prim (heckeCycle a g) := by
  have hlin : ∀ x y : ScalingCycle, scalingSurface.prim (x + y) =
      scalingSurface.prim x + scalingSurface.prim y := by
    intro x y
    rw [PolarSurface.prim_eq_sub_polarPart, PolarSurface.prim_eq_sub_polarPart,
      PolarSurface.prim_eq_sub_polarPart, PolarSurface.polarPart_add]
    abel
  have hsmul : ∀ (c : ℝ) (x : ScalingCycle), scalingSurface.prim (c • x) =
      c • scalingSurface.prim x := by
    intro c x
    rw [PolarSurface.prim_eq_sub_polarPart, PolarSurface.prim_eq_sub_polarPart,
      PolarSurface.polarPart_smul, smul_sub]
  rw [heckeSpanCycle, hlin, hlin, hsmul, hsmul, scalingSurface.prim_H, scalingSurface.prim_V]
  simp only [smul_zero, add_zero, zero_add]
  induction S using Finset.induction_on with
  | empty => simp [PolarSurface.prim_eq_sub_polarPart]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hlin, hsmul, ih]

/-- **Hecke span Hodge defect identity:** the Hodge defect of `c_H H + c_V V + ∑_{a ∈ S} d(a) Γ_a(g)`
is independent of the pole-plane coefficients `(c_H, c_V)` and equals the quadratic form in the
shifted test functions `scaleShift (log a) g`. -/
theorem defect_heckeSpanCycle (cH cV : ℝ) (S : Finset ℝ) (d : ℝ → ℝ) (g : realTests) :
    scalingSurface.defect (heckeSpanCycle cH cV S d g) (heckeSpanCycle cH cV S d g) =
      ∑ a ∈ S, ∑ b ∈ S,
        (d a * Real.sqrt a) * (d b * Real.sqrt b) *
          weilPair (scaleShift (Real.log a) g.1) (scaleShift (Real.log b) g.1) := by
  have hsmul : ∀ (c : ℝ) (x : ScalingCycle), scalingSurface.prim (c • x) =
      c • scalingSurface.prim x := by
    intro c x
    rw [PolarSurface.prim_eq_sub_polarPart, PolarSurface.prim_eq_sub_polarPart,
      PolarSurface.polarPart_smul, smul_sub]
  rw [← neg_inj, ← scalingSurface.pair_prim_prim, prim_heckeSpanCycle, map_sum]
  have hsum :
      (∑ b ∈ S, (scalingSurface.pair (∑ a ∈ S, d a • scalingSurface.prim (heckeCycle a g)))
        (d b • scalingSurface.prim (heckeCycle b g))) =
      ∑ a ∈ S, ∑ b ∈ S,
        scalingSurface.pair (d a • scalingSurface.prim (heckeCycle a g))
          (d b • scalingSurface.prim (heckeCycle b g)) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sum, LinearMap.sum_apply]
  rw [hsum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [heckeCycle, heckeCorrespondence, LinearMap.smul_apply, hsmul, map_smul,
    smul_eq_mul, scalingSurface.pair_prim_prim, defect_adamsOp_diagCycle]
  ring

/-! ### 6. Narrow-Bump Prime-Incidence Identity (`heckeIncidence` and Cartesian Factorization) -/

/-- If `φ : ℝ → ℝ` vanishes outside `[-δ, δ]` and `2δ < |x|`, then `EF.weilTest (cx φ) (cx φ) x = 0`. -/
theorem weilTest_eq_zero_of_support_radius {φ : ℝ → ℝ} {δ x : ℝ}
    (hφ : ∀ u, δ < |u| → φ u = 0) (hx : 2 * δ < |x|) :
    EF.weilTest (cx φ) (cx φ) x = 0 := by
  rw [weilTest_ofReal, ← Complex.ofReal_zero]
  congr 1
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : δ < |u|
  · simp [hφ u hu]
  · have hu' : |u| ≤ δ := le_of_not_gt hu
    have hux : δ < |u - x| := by
      have htri : |x| - |u| ≤ |u - x| := by
        rw [abs_sub_comm u x]
        exact abs_sub_abs_le_abs_sub x u
      linarith
    simp [hφ (u - x) hux]

/-- At zero lag `x = 0`, `EF.weilTest (cx φ) (cx φ) 0` is the `L^2` norm squared `∫ φ(u)^2 du`. -/
theorem weilTest_self_zero (φ : ℝ → ℝ) :
    EF.weilTest (cx φ) (cx φ) 0 = ((∫ u, φ u ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_ofReal]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp [sq]

/-- For positive integers `m < n`, `log(1 + 1 / n) ≤ log n - log m`. -/
theorem log_one_add_inv_le_log_sub {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    Real.log (1 + 1 / (n : ℝ)) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hmn1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  rw [← Real.log_div (ne_of_gt hn_pos) (ne_of_gt hm_pos)]
  refine Real.log_le_log (by positivity) ?_
  have hdiv : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n := by
    field_simp [ne_of_gt hn_pos]
  rw [hdiv, div_le_div_iff₀ hn_pos hm_pos]
  nlinarith

/-- For distinct positive integers `u ≠ v`, the logarithmic gap `|log u - log v|` is at least
`log(1 + 1 / max u v)`. -/
theorem log_one_add_inv_max_le_abs_log_sub {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u ≠ v) :
    Real.log (1 + 1 / ((max u v : ℕ) : ℝ)) ≤ |Real.log (u : ℝ) - Real.log (v : ℝ)| := by
  have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr (by omega)
  have hv_pos : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · have hmax : ((max u v : ℕ) : ℝ) = v := by exact_mod_cast max_eq_right (le_of_lt hlt)
    have hsub : Real.log (u : ℝ) - Real.log (v : ℝ) ≤ 0 := by
      linarith [Real.log_le_log hu_pos (Nat.cast_le.mpr (le_of_lt hlt))]
    rw [abs_of_nonpos hsub, neg_sub, hmax]
    exact log_one_add_inv_le_log_sub hu hlt
  · exact (huv rfl).elim
  · have hmax : ((max u v : ℕ) : ℝ) = u := by exact_mod_cast max_eq_left (le_of_lt hgt)
    have hsub : 0 ≤ Real.log (u : ℝ) - Real.log (v : ℝ) := by
      linarith [Real.log_le_log hv_pos (Nat.cast_le.mpr (le_of_lt hgt))]
    rw [abs_of_nonneg hsub, hmax]
    exact log_one_add_inv_le_log_sub hv hgt

/-- **Single-scale incidence evaluation for narrow Hecke bumps:** if `φ` is supported in
`[-δ, δ]` with `2δ < log(1 + 1 / max(a * n, b * n))`, then the lag-`log n` evaluation of
`scaleShift (log a) φ` against `scaleShift (log b) φ` equals `∫ φ^2` when `a = b * n` or
`b = a * n`, and `0` otherwise. -/
theorem weilTest_scaleShift_nat_eval {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n)
    {φ : ℝ → ℝ} {δ : ℝ} (hφ : ∀ u, δ < |u| → φ u = 0)
    (hδ₁ : 2 * δ < Real.log (1 + 1 / ((max (a * n) b : ℕ) : ℝ)))
    (hδ₂ : 2 * δ < Real.log (1 + 1 / ((max (b * n) a : ℕ) : ℝ))) :
    EF.weilTest (cx (scaleShift (Real.log a) φ)) (cx (scaleShift (Real.log b) φ))
        (Real.log n) +
      EF.weilTest (cx (scaleShift (Real.log a) φ)) (cx (scaleShift (Real.log b) φ))
        (-Real.log n) =
      (((if a = b * n then (1 : ℝ) else 0) + (if b = a * n then (1 : ℝ) else 0)) *
        ∫ u, φ u ^ 2 : ℝ) := by
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog_an : Real.log ((a * n : ℕ) : ℝ) = Real.log a + Real.log n := by
    push_cast
    exact Real.log_mul (ne_of_gt ha_pos) (ne_of_gt hn_pos)
  have hlog_bn : Real.log ((b * n : ℕ) : ℝ) = Real.log b + Real.log n := by
    push_cast
    exact Real.log_mul (ne_of_gt hb_pos) (ne_of_gt hn_pos)
  rw [weilTest_scaleShift, weilTest_scaleShift]
  have harg₁ : Real.log n - Real.log a + Real.log b =
      Real.log ((b * n : ℕ) : ℝ) - Real.log (a : ℝ) := by linarith
  have harg₂ : -Real.log n - Real.log a + Real.log b =
      Real.log (b : ℝ) - Real.log ((a * n : ℕ) : ℝ) := by linarith
  have ht₁ :
      EF.weilTest (cx φ) (cx φ) (Real.log n - Real.log a + Real.log b) =
        (((if a = b * n then (1 : ℝ) else 0) * ∫ u, φ u ^ 2 : ℝ) : ℂ) := by
    by_cases h1 : a = b * n
    · rw [if_pos h1, one_mul, harg₁, h1, sub_self, weilTest_self_zero]
    · rw [if_neg h1, zero_mul, Complex.ofReal_zero]
      refine weilTest_eq_zero_of_support_radius hφ ?_
      rw [harg₁]
      exact lt_of_lt_of_le hδ₂
        (log_one_add_inv_max_le_abs_log_sub (Nat.mul_le_mul hb hn) ha (Ne.symm h1))
  have ht₂ :
      EF.weilTest (cx φ) (cx φ) (-Real.log n - Real.log a + Real.log b) =
        (((if b = a * n then (1 : ℝ) else 0) * ∫ u, φ u ^ 2 : ℝ) : ℂ) := by
    by_cases h2 : b = a * n
    · rw [if_pos h2, one_mul, harg₂, h2, sub_self, weilTest_self_zero]
    · rw [if_neg h2, zero_mul, Complex.ofReal_zero]
      refine weilTest_eq_zero_of_support_radius hφ ?_
      rw [harg₂, abs_sub_comm]
      exact lt_of_lt_of_le hδ₁
        (log_one_add_inv_max_le_abs_log_sub (Nat.mul_le_mul ha hn) hb (Ne.symm h2))
  rw [ht₁, ht₂]
  push_cast
  ring

/-- A prime-power bilinear form on test functions weighted by an arbitrary arithmetic weight
`lam : ℕ → ℝ` over `n ∈ [2, N]` (for `lam = primeAtom`, each `n = p^m` carries the von Mangoldt
weight `log p / p^{m/2}`). -/
def weightedPrimeComb (lam : ℕ → ℝ) (N : ℕ) (f g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    lam n *
      (EF.weilTest (cx f) (cx g) (Real.log n) +
        EF.weilTest (cx f) (cx g) (-Real.log n)).re

private theorem sum_Icc_mul_eq_div_weight (lam : ℕ → ℝ) (h1 : lam 1 = 0)
    {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hbN : b ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, if b = a * n then lam n else 0) =
      if a ∣ b then lam (b / a) else 0 := by
  by_cases hdvd : a ∣ b
  · rw [if_pos hdvd]
    rcases hdvd with ⟨q, rfl⟩
    have hq_pos : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp at hb
      · exact hq
    rw [Nat.mul_div_cancel_left q (by omega : 0 < a)]
    by_cases hq2 : 2 ≤ q
    · have hqN : q ≤ N := le_trans (Nat.le_mul_of_pos_left q (by omega : 0 < a)) hbN
      have hmem : q ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨hq2, hqN⟩
      rw [Finset.sum_eq_single q]
      · simp
      · intro n _ hnq
        have hne : a * q ≠ a * n := fun h => hnq (Nat.mul_left_cancel (by omega : 0 < a) h).symm
        exact if_neg hne
      · intro hnot
        exact (hnot hmem).elim
    · have hq1 : q = 1 := by omega
      subst hq1
      rw [h1]
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hne : a * 1 ≠ a * n := by nlinarith
      exact if_neg hne
  · rw [if_neg hdvd]
    refine Finset.sum_eq_zero fun n _ => ?_
    have hne : b ≠ a * n := fun h => hdvd ⟨n, h⟩
    exact if_neg hne

/-- **General narrow-bump incidence identity for an arbitrary weight `lam : ℕ → ℝ`:**
for any arithmetic weight `lam : ℕ → ℝ` with `lam 1 = 0`, any positive integers `a, b ≥ 1`,
cutoff `N ≥ max a b`, and narrow test bump `φ` supported in `[-δ, δ]` with
`2δ < log(1 + 1 / (max a b * N))`, the `lam`-weighted prime-comb pairing of `scaleShift (log a) φ`
and `scaleShift (log b) φ` evaluates to the divisibility ratio weight
`((if a ∣ b then lam (b / a) else 0) + (if b ∣ a then lam (a / b) else 0)) * ∫ φ^2`. -/
theorem weightedPrimeComb_scaleShift_narrow_eval (lam : ℕ → ℝ) (h1 : lam 1 = 0)
    {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : max a b ≤ N)
    {φ : ℝ → ℝ} {δ : ℝ} (hφ : ∀ u, δ < |u| → φ u = 0)
    (hδ : 2 * δ < Real.log (1 + 1 / ((max a b * N : ℕ) : ℝ))) :
    weightedPrimeComb lam N (scaleShift (Real.log a) φ) (scaleShift (Real.log b) φ) =
      ((if a ∣ b then lam (b / a) else 0) + (if b ∣ a then lam (a / b) else 0)) *
        ∫ u, φ u ^ 2 := by
  have hstep :
      weightedPrimeComb lam N (scaleShift (Real.log a) φ) (scaleShift (Real.log b) φ) =
        ∑ n ∈ Finset.Icc 2 N,
          ((if a = b * n then lam n else 0) + (if b = a * n then lam n else 0)) *
            ∫ u, φ u ^ 2 := by
    unfold weightedPrimeComb
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hn1 : 1 ≤ n := by omega
    have h_bound₁ : max (a * n) b ≤ max a b * N :=
      max_le (Nat.mul_le_mul (le_max_left a b) hnN)
        (le_trans (le_max_right a b) (Nat.le_mul_of_pos_right _ (by omega : 0 < N)))
    have h_bound₂ : max (b * n) a ≤ max a b * N :=
      max_le (Nat.mul_le_mul (le_max_right a b) hnN)
        (le_trans (le_max_left a b) (Nat.le_mul_of_pos_right _ (by omega : 0 < N)))
    have hlog_mono : ∀ {u v : ℕ}, 1 ≤ u → u ≤ v →
        Real.log (1 + 1 / (v : ℝ)) ≤ Real.log (1 + 1 / (u : ℝ)) := by
      intro u v hu huv
      have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr (by omega)
      refine Real.log_le_log (by positivity) ?_
      linarith [one_div_le_one_div_of_le hu_pos (Nat.cast_le.mpr huv)]
    have hδ₁ : 2 * δ < Real.log (1 + 1 / ((max (a * n) b : ℕ) : ℝ)) :=
      lt_of_lt_of_le hδ (hlog_mono (le_trans hb (le_max_right _ _)) h_bound₁)
    have hδ₂ : 2 * δ < Real.log (1 + 1 / ((max (b * n) a : ℕ) : ℝ)) :=
      lt_of_lt_of_le hδ (hlog_mono (le_trans ha (le_max_right _ _)) h_bound₂)
    rw [weilTest_scaleShift_nat_eval ha hb hn1 hφ hδ₁ hδ₂, Complex.ofReal_re]
    split_ifs <;> ring
  rw [hstep, ← Finset.sum_mul, Finset.sum_add_distrib,
    sum_Icc_mul_eq_div_weight lam h1 hb ha (le_trans (le_max_left a b) hN),
    sum_Icc_mul_eq_div_weight lam h1 ha hb (le_trans (le_max_right a b) hN),
    add_comm (if b ∣ a then lam (a / b) else 0)]

/-- **Narrow-bump Hecke prime-incidence theorem (`weightedPrimeComb_scaleShift_eq_heckeIncidence`):**
for `lam = primeAtom` (the von Mangoldt prime-power weight `Λ(n)/√n`), positive integers `a, b ≥ 1`,
cutoff `N ≥ max a b`, and a narrow test bump `φ` supported in `[-δ, δ]` with
`2δ < log(1 + 1 / (max a b * N))`, the prime-comb pairing of the Hecke shifts
`scaleShift (log a) φ` and `scaleShift (log b) φ` evaluates to `heckeIncidence a b * ∫ φ(u)^2 du`.
Combined with `heckeIncidence_eq_towerWeight` and `heckeIncidence_eq_zero`
(`HeckeIncidenceCartesianLaw`), narrow Hecke cycles reproduce the single-prime Frobenius weight
`towerWeight p |v_p(a) - v_p(b)|` on matching prime axes and have zero prime incidence whenever
`a` and `b` differ in two or more primes. -/
theorem weightedPrimeComb_scaleShift_eq_heckeIncidence {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hN : max a b ≤ N) {φ : ℝ → ℝ} {δ : ℝ} (hφ : ∀ u, δ < |u| → φ u = 0)
    (hδ : 2 * δ < Real.log (1 + 1 / ((max a b * N : ℕ) : ℝ))) :
    weightedPrimeComb primeAtom N (scaleShift (Real.log a) φ) (scaleShift (Real.log b) φ) =
      heckeIncidence a b * ∫ u, φ u ^ 2 := by
  have h1 : primeAtom 1 = 0 := by simp [primeAtom]
  rw [weightedPrimeComb_scaleShift_narrow_eval primeAtom h1 ha hb hN hφ hδ]
  rfl

/-- **Single-prime tower incidence for narrow Hecke cycles:** if `a, b ≥ 1` agree at all primes
`r ≠ p`, then their narrow-bump prime-comb pairing equals the single-prime Frobenius weight
`towerWeight p |v_p(a) - v_p(b)| * ∫ φ^2`. -/
theorem weightedPrimeComb_scaleShift_eq_towerWeight {a b p N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hp : p.Prime) (h : ∀ r, r ≠ p → a.factorization r = b.factorization r)
    (hN : max a b ≤ N) {φ : ℝ → ℝ} {δ : ℝ} (hφ : ∀ u, δ < |u| → φ u = 0)
    (hδ : 2 * δ < Real.log (1 + 1 / ((max a b * N : ℕ) : ℝ))) :
    weightedPrimeComb primeAtom N (scaleShift (Real.log a) φ) (scaleShift (Real.log b) φ) =
      towerWeight p (Nat.dist (a.factorization p) (b.factorization p)) * ∫ u, φ u ^ 2 := by
  rw [weightedPrimeComb_scaleShift_eq_heckeIncidence ha hb hN hφ hδ,
    heckeIncidence_eq_towerWeight (by omega) (by omega) hp h]

/-- **Multi-prime orthogonality of narrow Hecke cycles:** if `a, b ≥ 1` differ in two or more
prime coordinates, then their narrow-bump prime-comb pairing vanishes. -/
theorem weightedPrimeComb_scaleShift_eq_zero_of_two_primes {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ p, p.Prime → ∃ r, r ≠ p ∧ a.factorization r ≠ b.factorization r)
    (hN : max a b ≤ N) {φ : ℝ → ℝ} {δ : ℝ} (hφ : ∀ u, δ < |u| → φ u = 0)
    (hδ : 2 * δ < Real.log (1 + 1 / ((max a b * N : ℕ) : ℝ))) :
    weightedPrimeComb primeAtom N (scaleShift (Real.log a) φ) (scaleShift (Real.log b) φ) = 0 := by
  rw [weightedPrimeComb_scaleShift_eq_heckeIncidence ha hb hN hφ hδ,
    heckeIncidence_eq_zero (by omega) (by omega) h, zero_mul]

/-! ### 7. Zero-Side Eigenlaw, Fake Curve Data, Non-`Λ` Weights, and Positive Tests -/

/-- **Zero-side Adams eigenlaw (`paperFT_scaleShift_gammaOf`):** under the logarithmic scale
translation `scaleShift (log q)` (`q > 0`), the Mellin–Fourier transform at a spectral point
`gammaOf ρ = -i(ρ - 1/2)` multiplies by the Frobenius eigenvalue `q^{ρ - 1/2}`. -/
theorem paperFT_scaleShift_gammaOf {q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) (ρ : ℂ) :
    paperFT (cx (scaleShift (Real.log q) f)) (gammaOf ρ) =
      (q : ℂ) ^ (ρ - 1 / 2) * paperFT (cx f) (gammaOf ρ) := by
  unfold paperFT gammaOf
  simp only [cx_scaleShift]
  have heq : (fun u : ℝ => cx f (u - Real.log q) *
        Complex.exp (Complex.I * ((ρ - 1 / 2) / Complex.I) * (u : ℂ))) =
      fun u : ℝ => (q : ℂ) ^ (ρ - 1 / 2) *
        (cx f (u - Real.log q) *
          Complex.exp (Complex.I * ((ρ - 1 / 2) / Complex.I) * ((u - Real.log q : ℝ) : ℂ))) := by
    ext u
    have hI : Complex.I * ((ρ - 1 / 2) / Complex.I) * (u : ℂ) =
        (ρ - 1 / 2) * (Real.log q : ℂ) +
          Complex.I * ((ρ - 1 / 2) / Complex.I) * ((u - Real.log q : ℝ) : ℂ) := by
      rw [mul_div_cancel₀ _ Complex.I_ne_zero, Complex.ofReal_sub]
      ring
    have hcpow : (q : ℂ) ^ (ρ - 1 / 2) = Complex.exp ((ρ - 1 / 2) * (Real.log q : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hq)),
        Complex.ofReal_log (le_of_lt hq), mul_comm]
    rw [hI, Complex.exp_add, hcpow]
    ring
  rw [heq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self
      (fun v : ℝ => cx f v * Complex.exp (Complex.I * ((ρ - 1 / 2) / Complex.I) * (v : ℂ)))
      (Real.log q)]

/-- At any curve zero `ρ` satisfying `q^{ρ - 1/2} = β` (such as `D.zetaZero i k`), the `m`-th
Adams operation `scaleShift (log (q^m))` multiplies the spectral mode `paperFT (cx f) (gammaOf ρ)`
by the `m`-th Frobenius eigenvalue power `β^m`. -/
theorem paperFT_scaleShift_pow_of_curveZero {q : ℝ} (hq : 0 < q) {ρ β : ℂ}
    (hβ : (q : ℂ) ^ (ρ - 1 / 2) = β) (m : ℕ) (f : ℝ → ℝ) :
    paperFT (cx (scaleShift (Real.log (q ^ m)) f)) (gammaOf ρ) =
      β ^ m * paperFT (cx f) (gammaOf ρ) := by
  rw [paperFT_scaleShift_gammaOf (pow_pos hq m), ← hβ]
  congr 1
  have h1 : (((q ^ m : ℝ) : ℂ)) ^ (ρ - 1 / 2) =
      Complex.exp ((ρ - 1 / 2) * ((Real.log (q ^ m) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (pow_pos hq m))),
      ← Complex.ofReal_log (le_of_lt (pow_pos hq m)), mul_comm]
  have h2 : ((q : ℂ) ^ (ρ - 1 / 2)) ^ m =
      Complex.exp ((m : ℂ) * ((ρ - 1 / 2) * ((Real.log q : ℝ) : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hq)),
      ← Complex.ofReal_log (le_of_lt hq), ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [h1, h2, Real.log_pow]
  push_cast
  ring_nf

/-- **What the `λ`-ring construction gives for fake curve data (`goldenDatum`):**
1. The universal `λ`-ring series of `goldenDatum` splits off the pole factor `goldenDatum.poleZeta`
   in `ℂ⟦X⟧`;
2. Every Frobenius Adams operator `goldenDatum.spanAdams m` is an exact intersection and defect
   isometry of `goldenDatum.windowSurface` commuting with `polarPart` and `prim`;
3. Yet `goldenDatum` violates unitarity / RH (`¬ ∀ i, ‖goldenDatum.β i‖ = 1`) and violates the
   Hodge index on its Frobenius span (`goldenDatum.spanDefect {0, 1} ... < 0`).
Thus the `λ`-ring exponential, Adams isometry, and pole-plane splitting are purely algebraic
structures that hold unconditionally on fake curve data without forcing positivity. -/
theorem goldenDatum_lambdaRing_and_not_unitary :
    (sigmaSeries (fun j => (goldenDatum.pointCount j : ℂ)) =
      goldenDatum.poleZeta *
        sigmaSeries (fun j => -∑ i : Fin 2, goldenDatum.alpha i ^ j)) ∧
    (∀ (m : ℕ) (S : Finset ℕ) (x y : SpanCycle),
      (goldenDatum.windowSurface (windowShift m S)).pair
        (goldenDatum.spanAdams m x) (goldenDatum.spanAdams m y) =
        (goldenDatum.windowSurface S).pair x y ∧
      (goldenDatum.windowSurface (windowShift m S)).polarPart (goldenDatum.spanAdams m x) =
        goldenDatum.spanAdams m ((goldenDatum.windowSurface S).polarPart x)) ∧
    ¬ ∀ i, ‖goldenDatum.β i‖ = 1 :=
  ⟨goldenDatum.sigmaSeries_pointCount_split,
   fun m S x y => ⟨goldenDatum.pair_spanAdams m S x y, goldenDatum.polarPart_spanAdams m S x⟩,
   goldenDatum_not_unitary⟩

/-- **What the `λ`-ring construction gives for a non-`Λ` weight (`lam : ℕ → ℝ`):**
for *every* arithmetic weight `lam`, logarithmic scale translation `scaleShift t` leaves the
`lam`-weighted prime-comb form invariant (`weightedPrimeComb_scaleShift_same`), and shifting `f`
by `s` and `g` by `t` depends only on `s - t`. Thus the Adams group action, its isometry property,
and the pole-plane splitting hold identically for any prime weight `lam`; the von Mangoldt weight
`Λ` is singled out only by matching the narrow-bump incidence to `-ζ'/ζ`
(`weightedPrimeComb_scaleShift_eq_heckeIncidence`) and by the signature of the `(H, V, Δ_1)` Gram
matrix (`one_positive_square_iff_vonMangoldt`). -/
theorem weightedPrimeComb_scaleShift (lam : ℕ → ℝ) (N : ℕ) (s t : ℝ) (f g : ℝ → ℝ) :
    weightedPrimeComb lam N (scaleShift s f) (scaleShift t g) =
      weightedPrimeComb lam N (scaleShift (s - t) f) g := by
  simp only [weightedPrimeComb, weilTest_scaleShift_sub s t f g]

@[simp]
theorem weightedPrimeComb_scaleShift_same (lam : ℕ → ℝ) (N : ℕ) (t : ℝ) (f g : ℝ → ℝ) :
    weightedPrimeComb lam N (scaleShift t f) (scaleShift t g) =
      weightedPrimeComb lam N f g := by
  rw [weightedPrimeComb_scaleShift, sub_self, scaleShift_zero]

/-- Scale translation preserves pointwise non-negativity of test functions. -/
theorem scaleShift_nonneg (t : ℝ) {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ scaleShift t f u :=
  hf (u - t)

/-- **What the `λ`-ring construction gives for positive tests (`posTestCone`):**
1. Every Adams operation `adamsOp q`Maps `posTestCone` into `posTestCone`;
2. Every Hecke correspondence `heckeCorrespondence a` (`a ≥ 0`) maps `posTestCone` into
   `posTestCone`;
3. For any two pointwise non-negative tests `f, g` and any scales `a, b : ℝ`, the Weil
   cross-correlation of their Adams translates is pointwise non-negative at every lag `x : ℝ`
   (`0 ≤ (EF.weilTest (cx (scaleShift a f)) (cx (scaleShift b g)) x).re`), so every non-negatively
   weighted prime-comb pairing `weightedPrimeComb lam N (scaleShift a f) (scaleShift b g)` is
   non-negative;
4. Yet `posTestCone` is an Adams-stable cone that fails `RiemannRochAxiom`
   (`posTestCone_not_riemannRoch`). -/
theorem adamsOp_mem_posTestCone (q : ℝ) {x : ScalingCycle} (hx : x ∈ posTestCone) :
    adamsOp q x ∈ posTestCone := by
  rcases hx with ⟨hx1, hx2, hx3⟩
  refine ⟨mul_nonneg (by positivity) hx1, mul_nonneg (by positivity) hx2, fun u => ?_⟩
  exact scaleShift_nonneg (Real.log q) hx3 u

theorem heckeCorrespondence_mem_posTestCone (a : ℝ) {x : ScalingCycle}
    (hx : x ∈ posTestCone) :
    heckeCorrespondence a x ∈ posTestCone := by
  rcases adamsOp_mem_posTestCone a hx with ⟨hx1, hx2, hx3⟩
  have hsqrt : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  exact ⟨mul_nonneg hsqrt hx1, mul_nonneg hsqrt hx2, fun u => mul_nonneg hsqrt (hx3 u)⟩

theorem re_weilTest_scaleShift_nonneg (a b : ℝ) {f g : ℝ → ℝ}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ u, 0 ≤ g u) (x : ℝ) :
    0 ≤ (EF.weilTest (cx (scaleShift a f)) (cx (scaleShift b g)) x).re := by
  rw [weilTest_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun u => mul_nonneg (scaleShift_nonneg a hf u) (scaleShift_nonneg b hg _)

theorem weightedPrimeComb_scaleShift_nonneg {lam : ℕ → ℝ}
    (hlam : ∀ n, 0 ≤ lam n) (N : ℕ) (a b : ℝ) {f g : ℝ → ℝ}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ u, 0 ≤ g u) :
    0 ≤ weightedPrimeComb lam N (scaleShift a f) (scaleShift b g) := by
  refine Finset.sum_nonneg fun n _ => ?_
  rw [Complex.add_re]
  exact mul_nonneg (hlam n)
    (add_nonneg (re_weilTest_scaleShift_nonneg a b hf hg _)
      (re_weilTest_scaleShift_nonneg a b hf hg _))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
