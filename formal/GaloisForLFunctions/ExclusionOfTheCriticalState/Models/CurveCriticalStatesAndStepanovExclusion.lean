import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheAcidTestPassesForCubicCharacters
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState

/-!
# Curve critical states and exclusion by Castelnuovo–Severi and native Stepanov

This module settles question `E-Q3` unconditionally for curve configurations over `𝔽_q` and cubic
character `L`-functions:

1. **Confined Frobenius half-line domain and ground-state dichotomy (`curveCriticalState_iff_not_unitary`,
   `exists_curveGroundState_of_not_unitary`).**
   For a curve datum `D` (`q > 1`, normalized Frobenius eigenvalues `β_i` closed under conjugation
   and functional equation `β_{fe i} · β_i = 1`) in the strip `‖β_i‖ < q^4` (in particular
   `‖β_i‖ ≤ √q`), the discrete half-line domain `H_D = {f : ℕ → ℝ | ∑ f(m)² q^{8m} < ∞}` carries
   the confinement form `W₈(f, g) = ∑ f(m) g(m) q^{8m}`, the half-line Laplace transform
   `L_D f(z) = ∑ f(m) z^{-m}` (`|z| > q^{-4}`), and the bare Weil / Castelnuovo–Severi form
   `B_D(f, g) = Re ∑_i L_D f(β_i) L_D g(β_i⁻¹) = ∑_{k,l} f(k) g(l) D.trace(|k - l|)`.
   Either every `β_i` is unitary (`B_D(f, f) = ∑_i ‖L_D f(β_i)‖² ≥ 0`, so no critical state exists
   at any `a > 0`), or `D` has a non-unitary Frobenius root, in which case `B_D` attains its
   strictly negative minimum `-a* < 0` on `{f ∈ H_D : W₈(f) = 1}` at a real ground state `f*`
   satisfying the variational bound `∀ h ∈ H_D, B_D(h, h) + a* W₈(h) ≥ 0` and the weak equation
   `∀ g ∈ H_D, B_D(f*, g) + a* W₈(f*, g) = 0`.

2. **Exact closed form and ECS laws of every curve critical state (`curveCriticalState_eq_sum`,
   `curveCriticalState_laplace_eq_rational`, `curveCriticalState_star_identity`,
   `curveCriticalState_zeroParseval`, `curveCriticalState_sees_outer_and_inner_root`,
   `goldenDatum_exists_criticalState_and_collar_blind`).**
   Every curve critical state `f` at `a > 0` has the exact closed form
   `f(m) = -(1/a) ∑_i L_D f(β_i) (β_i q^{-8})^m`, rational continuation
   `L_D f(z) = -(1/a) ∑_i z L_D f(β_i) / (z - β_i q^{-8})` with poles at the shifted Frobenius
   roots `β_i q^{-8}`, curve `(★)` (`-a L_D f(z q^{-8}) = ∑_i z L_D f(β_i) / (z - β_i)`), exact
   zero Parseval identity `∑_{‖β_i‖=1} ‖L_D f(β_i)‖² + ∑_{‖β_i‖≠1} Re(L_D f(β_i) L_D f(β_i⁻¹)) =
   -a W₈(f) < 0`, and simultaneously sees both an outer root `‖β_{i₀}‖ > 1` and its paired inner
   root `‖β_{fe i₀}‖ < 1`. On `goldenDatum` (`q = 5`, `β = (φ, φ⁻¹)`), a unit ground state exists
   and every discrete support point `u_m = -m log 5` (`m ≥ 1`) lies strictly left of the open
   collar `(-log 2, 0)`.

3. **Exact ECS identity violated by Castelnuovo–Severi (`hodgeIndex_violates_negative_bareForm`) vs.
   native Stepanov (`cubicStepanov_even_bound_excludes_outer_root`,
   `cubicKummerDatum_beyondWallContinuation_and_no_criticalState`).**
   * **Castelnuovo–Severi (`curve_hodgeIndex_tfae`)** excludes the critical state at the
     **negative bare-energy / negative zero-norm identity**: `hermNegIndex (D.spanGram (#ι)) = 0`
     (equivalently scaling-surface Weil positivity) forces `B_D(h, h) ≥ 0` on all of `H_D`,
     directly contradicting `B_D(f, f) = -a W₈(f) < 0`.
   * **Native Stepanov (`riemannHypothesis_cubicCharacter`)** has no intersection form; instead it
     excludes the critical state at **Stage 5 (beyond-the-wall prime-head continuation)**:
     its even-degree auxiliary-polynomial bound (`norm_rootEnumC_le`) forces `‖ω_i / √q‖ ≤ 1`
     (excluding any outer root), and together with the Gauss-sum determinant (`norm_prod_lRootsC`)
     yields `|D.trace n| ≤ 2(deg f - 1)` on the associated cubic Kummer datum, making the curve
     beyond-the-wall prime-head balance `Φ_D(h, z) = -∑_{n ≥ 1} D.trace(n) z^n ∑_{m < n} h(m) z^{-m}`
     holomorphic throughout the unit disc `{|z| < 1}` for every `h ∈ H_D` and directly refuting the
     seen-inner-root pole obstruction (`curveCriticalState_not_beyondWallContinuation`).
-/

noncomputable section

open Complex Finset Filter Topology Metric
open scoped ComplexConjugate Polynomial

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticCastelnuovoSeveri ExponentDynamicsOfTheCriticalStrip
open GaloisForLFunctions.RHTower.Hyperelliptic (rootEnum univ_map_rootEnum)
open GaloisForLFunctions.RHTower.WeilKloosterman (norm_le_of_power_sums_bound)
open HTGeometry (hermNegIndex hermQuad)

/-! ### 1. Confined Frobenius half-line domain, transform, and bare form -/

namespace CurveModels

section GeneralDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- Strip hypothesis ensuring all Frobenius eigenvalues and their functional-equation inverses lie
strictly inside the convergence annulus `{q^{-4} < |z| < q^4}` of `H_D`. Every datum in the
critical strip `‖β_i‖ ≤ √q` satisfies `InFourStrip`. -/
def InFourStrip : Prop := ∀ i : ι, ‖D.β i‖ < D.q ^ 4

theorem q_pos : 0 < D.q := lt_trans zero_lt_one D.one_lt_q

theorem q_pow_pos (k : ℕ) : 0 < D.q ^ k := pow_pos (q_pos D) k

theorem inFourStrip_of_strip (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) : InFourStrip D := by
  intro i
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.sqrtq ^ 2 = D.q := D.sqrtq_sq
  have hlt1 : D.sqrtq < D.q := by nlinarith [D.sqrtq_pos]
  have hlt4 : D.q < D.q ^ 4 := by
    have h2 : D.q < D.q ^ 2 := by nlinarith
    have h3 : D.q ^ 2 < D.q ^ 4 := by nlinarith
    linarith
  exact (hD i).trans_lt (hlt1.trans hlt4)

theorem inv_q_four_lt_norm_β (hD : InFourStrip D) (i : ι) : (D.q ^ 4)⁻¹ < ‖D.β i‖ := by
  have hfe : ‖D.β i‖⁻¹ = ‖D.β (D.fePerm i)‖ := (D.norm_β_fePerm i).symm
  have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (D.β_ne_zero i)
  have hlt : ‖D.β i‖⁻¹ < D.q ^ 4 := hfe ▸ hD (D.fePerm i)
  exact (inv_lt_comm₀ hpos (q_pow_pos D 4)).mp hlt

theorem β_fePerm_eq_inv (i : ι) : D.β (D.fePerm i) = (D.β i)⁻¹ :=
  eq_inv_of_mul_eq_one_left (D.β_fePerm i)

theorem β_fePerm_fePerm (i : ι) : D.β (D.fePerm (D.fePerm i)) = D.β i := by
  have h1 := D.β_fePerm (D.fePerm i)
  have h2 : D.β i * D.β (D.fePerm i) = 1 := (mul_comm _ _).trans (D.β_fePerm i)
  exact mul_right_cancel₀ (D.β_ne_zero (D.fePerm i)) (h1.trans h2.symm)

/-- The confined Frobenius half-line energy domain `H_D = {f : ℕ → ℝ | ∑_m f(m)² q^{8m} < ∞}`. -/
def CurveEnergyDomain (f : ℕ → ℝ) : Prop :=
  Summable fun m : ℕ => f m ^ 2 * D.q ^ (8 * m)

/-- The confinement bilinear form `W₈(f, g) = ∑_m f(m) g(m) q^{8m}`. -/
def curveConfinementPair (f g : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, f m * g m * D.q ^ (8 * m)

/-- The confinement quadratic norm `W₈(f) = ∑_m f(m)² q^{8m}`. -/
def curveConfinementMass (f : ℕ → ℝ) : ℝ :=
  curveConfinementPair D f f

/-- The discrete half-line Laplace transform `L_D f(z) = ∑_{m ≥ 0} f(m) (z⁻¹)^m`, corresponding to
`∫_{u < 0} F(u) e^{p u} du` at `u_m = -m log q` and `z = q^p`. -/
def curveLaplace (f : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, (f m : ℂ) * (z⁻¹) ^ m

/-- The curve bare Weil / Castelnuovo–Severi bilinear form
`B_D(f, g) = Re ∑_{i ∈ ι} L_D f(β_i) L_D g(β_i⁻¹)`. -/
def curveBareForm (f g : ℕ → ℝ) : ℝ :=
  (∑ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹).re

/-- A **curve critical state** at confinement parameter `a > 0` is a nonzero profile `f ∈ H_D`
satisfying the weak state equation `B_D(f, g) + a W₈(f, g) = 0` for all `g ∈ H_D`. -/
def IsCurveCriticalState (a : ℝ) (f : ℕ → ℝ) : Prop :=
  0 < a ∧ CurveEnergyDomain D f ∧ f ≠ 0 ∧
    ∀ g : ℕ → ℝ, CurveEnergyDomain D g →
      curveBareForm D f g + a * curveConfinementPair D f g = 0

theorem curveEnergyDomain_zero : CurveEnergyDomain D (fun _ => 0) := by
  simp [CurveEnergyDomain]

theorem curveEnergyDomain_const_mul {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) (c : ℝ) :
    CurveEnergyDomain D (fun m => c * f m) := by
  refine (hf.mul_left (c ^ 2)).congr fun m => ?_
  ring

theorem summable_mul_confinement {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f)
    (hg : CurveEnergyDomain D g) :
    Summable fun m : ℕ => |f m * g m| * D.q ^ (8 * m) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (q_pow_pos D _).le)
    (fun m => ?_) ((hf.add hg).div_const 2)
  have hq : 0 ≤ D.q ^ (8 * m) := (q_pow_pos D _).le
  rcases le_or_gt 0 (f m * g m) with h | h
  · rw [abs_of_nonneg h]
    nlinarith [sq_nonneg (f m - g m), hq]
  · rw [abs_of_neg h]
    nlinarith [sq_nonneg (f m + g m), hq]

theorem summable_pair_confinement {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f)
    (hg : CurveEnergyDomain D g) :
    Summable fun m : ℕ => f m * g m * D.q ^ (8 * m) := by
  refine Summable.of_norm_bounded (summable_mul_confinement D hf hg) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (q_pow_pos D _)]

theorem curveEnergyDomain_add {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f)
    (hg : CurveEnergyDomain D g) :
    CurveEnergyDomain D (fun m => f m + g m) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (q_pow_pos D _).le)
    (fun m => ?_) ((hf.add hg).mul_left 2)
  have hq : 0 ≤ D.q ^ (8 * m) := (q_pow_pos D _).le
  nlinarith [sq_nonneg (f m - g m), hq]

theorem curveEnergyDomain_sub {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f)
    (hg : CurveEnergyDomain D g) :
    CurveEnergyDomain D (fun m => f m - g m) := by
  simpa [sub_eq_add_neg, neg_one_mul] using
    curveEnergyDomain_add D hf (curveEnergyDomain_const_mul D hg (-1))

theorem curveEnergyDomain_of_support_lt {f : ℕ → ℝ} (n : ℕ) (hsupp : ∀ m, n ≤ m → f m = 0) :
    CurveEnergyDomain D f := by
  refine summable_of_ne_finset_zero (s := Finset.range n) fun m hm => ?_
  have hle : n ≤ m := not_lt.mp (by simpa [Finset.mem_range] using hm)
  simp [hsupp m hle]

/-- The Kronecker delta profile `δ_m` at half-line site `m`. -/
def siteDelta (m₀ : ℕ) : ℕ → ℝ := fun m => if m = m₀ then 1 else 0

theorem curveEnergyDomain_siteDelta (m₀ : ℕ) : CurveEnergyDomain D (siteDelta m₀) :=
  curveEnergyDomain_of_support_lt D (m₀ + 1) fun m hm => by
    simp [siteDelta, show m ≠ m₀ by omega]

theorem curveConfinementPair_comm (f g : ℕ → ℝ) :
    curveConfinementPair D f g = curveConfinementPair D g f := by
  unfold curveConfinementPair
  exact tsum_congr fun m => by ring

theorem curveConfinementPair_add_left {f₁ f₂ g : ℕ → ℝ} (hf₁ : CurveEnergyDomain D f₁)
    (hf₂ : CurveEnergyDomain D f₂) (hg : CurveEnergyDomain D g) :
    curveConfinementPair D (fun m => f₁ m + f₂ m) g =
      curveConfinementPair D f₁ g + curveConfinementPair D f₂ g := by
  unfold curveConfinementPair
  rw [← (summable_pair_confinement D hf₁ hg).tsum_add (summable_pair_confinement D hf₂ hg)]
  exact tsum_congr fun m => by ring

theorem curveConfinementPair_smul_left (c : ℝ) (f g : ℕ → ℝ) :
    curveConfinementPair D (fun m => c * f m) g = c * curveConfinementPair D f g := by
  unfold curveConfinementPair
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

theorem curveConfinementMass_nonneg (f : ℕ → ℝ) : 0 ≤ curveConfinementMass D f := by
  unfold curveConfinementMass curveConfinementPair
  exact tsum_nonneg fun m => mul_nonneg (mul_self_nonneg (f m)) (q_pow_pos D _).le

theorem curveConfinementMass_eq_zero_iff {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) :
    curveConfinementMass D f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    funext m₀
    by_contra hm
    have hpos : 0 < f m₀ ^ 2 * D.q ^ (8 * m₀) :=
      mul_pos (sq_pos_of_ne_zero hm) (q_pow_pos D _)
    have hle : f m₀ ^ 2 * D.q ^ (8 * m₀) ≤ curveConfinementMass D f := by
      unfold curveConfinementMass curveConfinementPair
      have heq : ∑' m : ℕ, f m * f m * D.q ^ (8 * m) = ∑' m : ℕ, f m ^ 2 * D.q ^ (8 * m) :=
        tsum_congr fun m => by ring
      rw [heq]
      simpa using hf.sum_le_tsum {m₀} fun m _ => mul_nonneg (sq_nonneg _) (q_pow_pos D _).le
    linarith
  · rintro rfl
    simp [curveConfinementMass, curveConfinementPair]

theorem curveConfinementPair_siteDelta_right (f : ℕ → ℝ) (m₀ : ℕ) :
    curveConfinementPair D f (siteDelta m₀) = f m₀ * D.q ^ (8 * m₀) := by
  unfold curveConfinementPair siteDelta
  rw [tsum_eq_single m₀]
  · simp
  · intro m hm; simp [hm]

/-- Absolute summability of `L_D f(z)` throughout `{|z| > q^{-4}}`. -/
theorem summable_norm_curveLaplace {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) {z : ℂ}
    (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    Summable fun m : ℕ => ‖(f m : ℂ) * (z⁻¹) ^ m‖ := by
  have hz_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr (q_pow_pos D 4)) hz
  set ρ : ℝ := (D.q ^ 4 * ‖z‖)⁻¹
  have hρ_pos : 0 < ρ := inv_pos.mpr (mul_pos (q_pow_pos D 4) hz_pos)
  have hρ_lt : ρ < 1 := by
    dsimp [ρ]
    have h1 : 1 < D.q ^ 4 * ‖z‖ := by
      have := (inv_lt_iff_one_lt_mul₀ (q_pow_pos D 4)).mp hz
      linarith
    exact inv_lt_one_of_one_lt₀ h1
  have hgeom : Summable fun m : ℕ => (ρ ^ 2) ^ m :=
    summable_geometric_of_lt_one (sq_nonneg ρ) (by nlinarith)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((hf.add hgeom).div_const 2)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_inv]
  have hid : |f m| * (‖z‖⁻¹) ^ m = (|f m| * (D.q ^ 4) ^ m) * ρ ^ m := by
    dsimp [ρ]
    rw [mul_inv, mul_pow, inv_pow (D.q ^ 4) m]
    calc |f m| * (‖z‖⁻¹) ^ m
        = |f m| * ((D.q ^ 4) ^ m * ((D.q ^ 4) ^ m)⁻¹) * (‖z‖⁻¹) ^ m := by
            rw [mul_inv_cancel₀ (pow_ne_zero m (q_pow_pos D 4).ne'), mul_one]
      _ = (|f m| * (D.q ^ 4) ^ m) * (((D.q ^ 4) ^ m)⁻¹ * (‖z‖⁻¹) ^ m) := by ring
  have hsq1 : (|f m| * (D.q ^ 4) ^ m) ^ 2 = f m ^ 2 * D.q ^ (8 * m) := by
    rw [mul_pow, sq_abs, ← pow_mul, ← pow_mul, show 4 * (m * 2) = 8 * m by ring]
  have hsq2 : (ρ ^ m) ^ 2 = (ρ ^ 2) ^ m := by rw [← pow_mul, mul_comm, pow_mul]
  rw [hid]
  nlinarith [sq_nonneg (|f m| * (D.q ^ 4) ^ m - ρ ^ m), hsq1, hsq2]

theorem summable_curveLaplace {f : ℕ → ℝ} (hf : CurveEnergyDomain D f) {z : ℂ}
    (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    Summable fun m : ℕ => (f m : ℂ) * (z⁻¹) ^ m :=
  (summable_norm_curveLaplace D hf hz).of_norm

theorem curveLaplace_conj (f : ℕ → ℝ) (z : ℂ) :
    conj (curveLaplace f z) = curveLaplace f (conj z) := by
  unfold curveLaplace
  rw [Complex.conj_tsum]
  refine tsum_congr fun m => ?_
  rw [map_mul, Complex.conj_ofReal, map_pow, map_inv₀]

theorem curveLaplace_add {f g : ℕ → ℝ} (hf : CurveEnergyDomain D f) (hg : CurveEnergyDomain D g)
    {z : ℂ} (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    curveLaplace (fun m => f m + g m) z = curveLaplace f z + curveLaplace g z := by
  unfold curveLaplace
  rw [← (summable_curveLaplace D hf hz).tsum_add (summable_curveLaplace D hg hz)]
  refine tsum_congr fun m => ?_
  push_cast; ring

theorem curveLaplace_const_mul (c : ℝ) (f : ℕ → ℝ) (z : ℂ) :
    curveLaplace (fun m => c * f m) z = (c : ℂ) * curveLaplace f z := by
  unfold curveLaplace
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  push_cast; ring

theorem curveLaplace_siteDelta (m₀ : ℕ) (z : ℂ) :
    curveLaplace (siteDelta m₀) z = (z⁻¹) ^ m₀ := by
  unfold curveLaplace siteDelta
  rw [tsum_eq_single m₀]
  · simp
  · intro m hm; simp [hm]

/-- Conjugation symmetry makes `∑_i L_D f(β_i) L_D g(β_i⁻¹)` purely real. -/
theorem sum_curveLaplace_eq_ofReal_bareForm (f g : ℕ → ℝ) :
    (∑ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹) =
      (curveBareForm D f g : ℂ) := by
  have hconj : conj (∑ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹) =
      ∑ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹ := by
    rw [map_sum]
    simp_rw [map_mul, curveLaplace_conj, map_inv₀, ← D.β_conjPerm]
    exact Equiv.sum_comp D.conjPerm fun i => curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹
  exact (Complex.conj_eq_iff_re.mp hconj).symm

/-- Exact Toeplitz expansion of the bare form:
`B_D(f, g) = ∑_k f(k) ∑_l g(l) D.trace(|k - l|)`. -/
theorem curveBareForm_eq_double_tsum (hD : InFourStrip D) {f g : ℕ → ℝ}
    (hf : CurveEnergyDomain D f) (hg : CurveEnergyDomain D g) :
    curveBareForm D f g =
      ∑' k : ℕ, ∑' l : ℕ, f k * g l * D.trace (Nat.dist k l) := by
  have hβ : ∀ i : ι, (D.q ^ 4)⁻¹ < ‖D.β i‖ := inv_q_four_lt_norm_β D hD
  have hβinv : ∀ i : ι, (D.q ^ 4)⁻¹ < ‖(D.β i)⁻¹‖ := fun i => by
    rw [norm_inv, ← D.norm_β_fePerm i]
    exact hβ (D.fePerm i)
  have hdist : ∀ k l : ℕ,
      (∑ i : ι, D.β (D.fePerm i) ^ k * D.β i ^ l) = (D.trace (Nat.dist k l) : ℂ) := by
    intro k l
    rw [← D.powerSum_eq_trace, D.powerSum_dist k l,
      ← Equiv.sum_comp D.fePerm (fun j => D.β j ^ k * D.β (D.fePerm j) ^ l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [β_fePerm_fePerm D i]
  have hfe_sum : ∀ k l : ℕ, ((f k * g l * D.trace (Nat.dist k l) : ℝ) : ℂ) =
      ∑ i : ι, (f k : ℂ) * (g l : ℂ) * (D.β (D.fePerm i) ^ k * D.β i ^ l) := by
    intro k l
    rw [← Finset.mul_sum, hdist k l]; push_cast; ring
  have hsum_inner : ∀ (i : ι) (k : ℕ),
      Summable fun l : ℕ => (f k : ℂ) * (g l : ℂ) * (D.β (D.fePerm i) ^ k * D.β i ^ l) := by
    intro i k
    refine ((summable_curveLaplace D hg (hβinv i)).mul_left
      ((f k : ℂ) * D.β (D.fePerm i) ^ k)).congr fun l => ?_
    simp only [inv_inv]; ring
  have hsum_outer : ∀ i : ι, Summable fun k : ℕ => ∑' l : ℕ,
      (f k : ℂ) * (g l : ℂ) * (D.β (D.fePerm i) ^ k * D.β i ^ l) := by
    intro i
    refine ((summable_curveLaplace D hf (hβ i)).mul_right
      (curveLaplace g (D.β i)⁻¹)).congr fun k => ?_
    unfold curveLaplace
    rw [inv_inv, ← β_fePerm_eq_inv D i, ← tsum_mul_left]
    exact tsum_congr fun l => by ring
  have hprod : (curveBareForm D f g : ℂ) =
      ∑' k : ℕ, ∑' l : ℕ, ((f k * g l * D.trace (Nat.dist k l) : ℝ) : ℂ) := by
    rw [← sum_curveLaplace_eq_ofReal_bareForm]
    have hterm : ∀ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹ =
        ∑' k : ℕ, ∑' l : ℕ,
          (f k : ℂ) * (g l : ℂ) * (D.β (D.fePerm i) ^ k * D.β i ^ l) := by
      intro i
      unfold curveLaplace
      rw [inv_inv, ← β_fePerm_eq_inv D i, ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      rw [← tsum_mul_left]
      exact tsum_congr fun l => by ring
    simp_rw [hterm]
    rw [← (hasSum_sum fun i (_ : i ∈ Finset.univ) => (hsum_outer i).hasSum).tsum_eq]
    refine tsum_congr fun k => ?_
    rw [← (hasSum_sum fun i (_ : i ∈ Finset.univ) => (hsum_inner i k).hasSum).tsum_eq]
    exact tsum_congr fun l => (hfe_sum k l).symm
  have hs_real_inner : ∀ k : ℕ, Summable fun l : ℕ => f k * g l * D.trace (Nat.dist k l) := by
    intro k
    rw [← Complex.summable_ofReal]
    simp_rw [hfe_sum k]
    exact summable_sum fun i _ => hsum_inner i k
  have hs_real_outer : Summable fun k : ℕ => ∑' l : ℕ, f k * g l * D.trace (Nat.dist k l) := by
    rw [← Complex.summable_ofReal]
    have houter_eq : ∀ k : ℕ,
        ((∑' l : ℕ, f k * g l * D.trace (Nat.dist k l) : ℝ) : ℂ) =
          ∑ i : ι, ((f k : ℂ) * ((D.β i)⁻¹) ^ k) * curveLaplace g (D.β i)⁻¹ := by
      intro k
      rw [Complex.ofReal_tsum]
      simp_rw [hfe_sum k]
      rw [(hasSum_sum fun i (_ : i ∈ Finset.univ) => (hsum_inner i k).hasSum).tsum_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold curveLaplace
      rw [inv_inv, ← β_fePerm_eq_inv D i, ← tsum_mul_left]
      exact tsum_congr fun l => by ring
    simp_rw [houter_eq]
    exact summable_sum fun i _ => (summable_curveLaplace D hf (hβ i)).mul_right _
  have hcast : (curveBareForm D f g : ℂ) =
      ((∑' k : ℕ, ∑' l : ℕ, f k * g l * D.trace (Nat.dist k l) : ℝ) : ℂ) := by
    rw [hprod, Complex.ofReal_tsum]
    exact tsum_congr fun k => (Complex.ofReal_tsum _).symm
  exact Complex.ofReal_injective hcast

theorem curveBareForm_comm (_hD : InFourStrip D) {f g : ℕ → ℝ}
    (_hf : CurveEnergyDomain D f) (_hg : CurveEnergyDomain D g) :
    curveBareForm D f g = curveBareForm D g f := by
  unfold curveBareForm
  congr 1
  rw [← Equiv.sum_comp D.fePerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [β_fePerm_eq_inv D i, inv_inv, mul_comm]

theorem curveBareForm_add_left (hD : InFourStrip D) {f₁ f₂ g : ℕ → ℝ}
    (hf₁ : CurveEnergyDomain D f₁) (hf₂ : CurveEnergyDomain D f₂) :
    curveBareForm D (fun m => f₁ m + f₂ m) g =
      curveBareForm D f₁ g + curveBareForm D f₂ g := by
  unfold curveBareForm
  rw [← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [curveLaplace_add D hf₁ hf₂ (inv_q_four_lt_norm_β D hD i), add_mul]

theorem curveBareForm_smul_left (c : ℝ) (f g : ℕ → ℝ) :
    curveBareForm D (fun m => c * f m) g = c * curveBareForm D f g := by
  unfold curveBareForm
  have h : (∑ i : ι, curveLaplace (fun m => c * f m) (D.β i) * curveLaplace g (D.β i)⁻¹) =
      (c : ℂ) * ∑ i : ι, curveLaplace f (D.β i) * curveLaplace g (D.β i)⁻¹ := by
    simp_rw [curveLaplace_const_mul, mul_assoc, ← Finset.mul_sum]
  rw [h, Complex.re_ofReal_mul]

/-- On finite windows `[0, n)`, `B_D(f, f)` coincides with `D.toeplitz (range n) f` and with
`hermQuad (D.spanGram n)`. -/
theorem curveBareForm_window_eq_toeplitz (n : ℕ) {f : ℕ → ℝ} (hsupp : ∀ m, n ≤ m → f m = 0) :
    curveBareForm D f f = D.toeplitz (Finset.range n) f ∧
      curveBareForm D f f = hermQuad (D.spanGram n) (fun k : Fin n => (f k : ℂ)) := by
  have hlap : ∀ z : ℂ, curveLaplace f z = ∑ k ∈ Finset.range n, (f k : ℂ) * (z⁻¹) ^ k := by
    intro z
    unfold curveLaplace
    refine tsum_eq_sum fun m hm => ?_
    have hle : n ≤ m := not_lt.mp (by simpa [Finset.mem_range] using hm)
    simp [hsupp m hle]
  have h1 : curveBareForm D f f = D.toeplitz (Finset.range n) f := by
    have hc : (curveBareForm D f f : ℂ) = (D.toeplitz (Finset.range n) f : ℂ) := by
      rw [← sum_curveLaplace_eq_ofReal_bareForm]
      simp_rw [hlap, inv_inv, ← β_fePerm_eq_inv D, Finset.sum_mul_sum]
      have hswap :
          (∑ i : ι, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            (f k : ℂ) * D.β (D.fePerm i) ^ k * ((f l : ℂ) * D.β i ^ l)) =
          ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∑ i : ι,
            (f k : ℂ) * D.β (D.fePerm i) ^ k * ((f l : ℂ) * D.β i ^ l) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
      rw [hswap, CurveDatum.toeplitz]
      push_cast
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have hdist : (∑ i : ι, D.β (D.fePerm i) ^ k * D.β i ^ l) = (D.trace (Nat.dist k l) : ℂ) := by
        rw [← D.powerSum_eq_trace, D.powerSum_dist k l,
          ← Equiv.sum_comp D.fePerm (fun j => D.β j ^ k * D.β (D.fePerm j) ^ l)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [β_fePerm_fePerm D i]
      calc (∑ i : ι, (f k : ℂ) * D.β (D.fePerm i) ^ k * ((f l : ℂ) * D.β i ^ l))
          = (f k : ℂ) * (f l : ℂ) * ∑ i : ι, D.β (D.fePerm i) ^ k * D.β i ^ l := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = (f k : ℂ) * (f l : ℂ) * (D.trace (Nat.dist k l) : ℂ) := by rw [hdist]
    exact Complex.ofReal_injective hc
  refine ⟨h1, ?_⟩
  rw [h1, ← D.hermQuad_spanGram_ofReal n f]

/-- When every Frobenius eigenvalue is unitary, `B_D(f, f) = ∑_i ‖L_D f(β_i)‖² ≥ 0`. -/
theorem curveBareForm_eq_sum_norm_sq_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) (f : ℕ → ℝ) :
    curveBareForm D f f = ∑ i : ι, ‖curveLaplace f (D.β i)‖ ^ 2 := by
  unfold curveBareForm
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinv : (D.β i)⁻¹ = conj (D.β i) := by
    have h1 : D.β i * conj (D.β i) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hU i]; norm_num
    exact (eq_inv_of_mul_eq_one_right h1).symm
  rw [hinv, ← curveLaplace_conj f (D.β i), Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- No curve critical state exists when every Frobenius root is unitary. -/
theorem not_isCurveCriticalState_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) (a : ℝ) (f : ℕ → ℝ) :
    ¬ IsCurveCriticalState D a f := by
  rintro ⟨ha, hf, hne, heq⟩
  have hself := heq f hf
  have hB : 0 ≤ curveBareForm D f f := by
    rw [curveBareForm_eq_sum_norm_sq_of_unitary D hU f]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 < curveConfinementMass D f :=
    lt_of_le_of_ne (curveConfinementMass_nonneg D f)
      (Ne.symm ((curveConfinementMass_eq_zero_iff D hf).not.mpr hne))
  have haW : 0 < a * curveConfinementMass D f := mul_pos ha hW
  unfold curveConfinementMass at haW
  linarith

/-! ### 2. Finite-rank attainment of the curve ground state and exact ECS laws -/

/-- The `2 · #ι` exponential generators in `H_D` representing `L_D · (β_i⁻¹)` against `W₈`. -/
private def frobGen (a : ι ⊕ ι) (m : ℕ) : ℝ :=
  match a with
  | Sum.inl i => (D.β i ^ m).re * (D.q ^ (8 * m))⁻¹
  | Sum.inr i => (D.β i ^ m).im * (D.q ^ (8 * m))⁻¹

private theorem curveEnergyDomain_frobGen (hD : InFourStrip D) (a : ι ⊕ ι) :
    CurveEnergyDomain D (frobGen D a) := by
  have hbound : ∀ i : ι, Summable fun m : ℕ => ((‖D.β i‖ ^ 2 * (D.q ^ 8)⁻¹)) ^ m := by
    intro i
    refine summable_geometric_of_lt_one (by positivity) ?_
    have hlt : ‖D.β i‖ ^ 2 < D.q ^ 8 := by
      have h1 := hD i
      have h0 := norm_nonneg (D.β i)
      have hsq : (D.q ^ 4) ^ 2 = D.q ^ 8 := by ring
      nlinarith
    exact (mul_inv_lt_iff₀ (q_pow_pos D 8)).mpr (by linarith)
  cases a with
  | inl i =>
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (q_pow_pos D _).le)
      (fun m => ?_) (hbound i)
    dsimp [frobGen]
    have hre : |(D.β i ^ m).re| ≤ ‖D.β i‖ ^ m :=
      (Complex.abs_re_le_norm _).trans_eq (norm_pow _ _)
    have hre2 : (D.β i ^ m).re ^ 2 ≤ (‖D.β i‖ ^ 2) ^ m := by
      have h1 : (D.β i ^ m).re ^ 2 ≤ (‖D.β i‖ ^ m) ^ 2 :=
        sq_le_sq.mpr (by rwa [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)])
      rwa [← pow_mul, mul_comm, pow_mul] at h1
    have hq_eq : ((D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m) = ((D.q ^ 8)⁻¹) ^ m := by
      have hne : D.q ^ (8 * m) ≠ 0 := (q_pow_pos D _).ne'
      rw [sq, mul_assoc, inv_mul_cancel₀ hne, mul_one, pow_mul, inv_pow]
    calc ((D.β i ^ m).re * (D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m)
        = (D.β i ^ m).re ^ 2 * (((D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m)) := by ring
      _ = (D.β i ^ m).re ^ 2 * ((D.q ^ 8)⁻¹) ^ m := by rw [hq_eq]
      _ ≤ (‖D.β i‖ ^ 2) ^ m * ((D.q ^ 8)⁻¹) ^ m :=
          mul_le_mul_of_nonneg_right hre2 (by positivity)
      _ = (‖D.β i‖ ^ 2 * (D.q ^ 8)⁻¹) ^ m := by rw [← mul_pow]
  | inr i =>
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (q_pow_pos D _).le)
      (fun m => ?_) (hbound i)
    dsimp [frobGen]
    have him : |(D.β i ^ m).im| ≤ ‖D.β i‖ ^ m :=
      (Complex.abs_im_le_norm _).trans_eq (norm_pow _ _)
    have him2 : (D.β i ^ m).im ^ 2 ≤ (‖D.β i‖ ^ 2) ^ m := by
      have h1 : (D.β i ^ m).im ^ 2 ≤ (‖D.β i‖ ^ m) ^ 2 :=
        sq_le_sq.mpr (by rwa [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)])
      rwa [← pow_mul, mul_comm, pow_mul] at h1
    have hq_eq : ((D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m) = ((D.q ^ 8)⁻¹) ^ m := by
      have hne : D.q ^ (8 * m) ≠ 0 := (q_pow_pos D _).ne'
      rw [sq, mul_assoc, inv_mul_cancel₀ hne, mul_one, pow_mul, inv_pow]
    calc ((D.β i ^ m).im * (D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m)
        = (D.β i ^ m).im ^ 2 * (((D.q ^ (8 * m))⁻¹) ^ 2 * D.q ^ (8 * m)) := by ring
      _ = (D.β i ^ m).im ^ 2 * ((D.q ^ 8)⁻¹) ^ m := by rw [hq_eq]
      _ ≤ (‖D.β i‖ ^ 2) ^ m * ((D.q ^ 8)⁻¹) ^ m :=
          mul_le_mul_of_nonneg_right him2 (by positivity)
      _ = (‖D.β i‖ ^ 2 * (D.q ^ 8)⁻¹) ^ m := by rw [← mul_pow]

private theorem curveLaplace_inv_eq_frobGen_pair (hD : InFourStrip D) {h : ℕ → ℝ}
    (hh : CurveEnergyDomain D h) (i : ι) :
    curveLaplace h (D.β i)⁻¹ =
      (curveConfinementPair D (frobGen D (Sum.inl i)) h : ℂ) +
        I * (curveConfinementPair D (frobGen D (Sum.inr i)) h : ℂ) := by
  have hs1 := summable_pair_confinement D (curveEnergyDomain_frobGen D hD (Sum.inl i)) hh
  have hs2 := summable_pair_confinement D (curveEnergyDomain_frobGen D hD (Sum.inr i)) hh
  unfold curveConfinementPair curveLaplace
  rw [Complex.ofReal_tsum, Complex.ofReal_tsum, ← tsum_mul_left,
    ← (Complex.summable_ofReal.mpr hs1).tsum_add ((Complex.summable_ofReal.mpr hs2).mul_left I)]
  refine tsum_congr fun m => ?_
  dsimp [frobGen]
  have hq : D.q ^ (8 * m) ≠ 0 := (q_pow_pos D _).ne'
  have hr1 : (D.β i ^ m).re * (D.q ^ (8 * m))⁻¹ * h m * D.q ^ (8 * m) =
      h m * (D.β i ^ m).re := by field_simp
  have hr2 : (D.β i ^ m).im * (D.q ^ (8 * m))⁻¹ * h m * D.q ^ (8 * m) =
      h m * (D.β i ^ m).im := by field_simp
  rw [inv_inv, hr1, hr2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring

private theorem curveBareForm_add_lin (hD : InFourStrip D) {u v : ℕ → ℝ}
    (hu : CurveEnergyDomain D u) (hv : CurveEnergyDomain D v) (t : ℝ) :
    curveBareForm D (fun m => u m + t * v m) (fun m => u m + t * v m) =
      curveBareForm D u u + 2 * t * curveBareForm D u v + t ^ 2 * curveBareForm D v v := by
  have htv : CurveEnergyDomain D (fun m => t * v m) := curveEnergyDomain_const_mul D hv t
  have huv : CurveEnergyDomain D (fun m => u m + t * v m) := curveEnergyDomain_add D hu htv
  rw [curveBareForm_add_left D hD hu htv, curveBareForm_smul_left,
    curveBareForm_comm D hD hu huv, curveBareForm_add_left D hD hu htv, curveBareForm_smul_left,
    curveBareForm_comm D hD hv huv, curveBareForm_add_left D hD hu htv, curveBareForm_smul_left,
    curveBareForm_comm D hD hv hu]
  ring

private theorem curveConfinementMass_add_lin {u v : ℕ → ℝ}
    (hu : CurveEnergyDomain D u) (hv : CurveEnergyDomain D v) (t : ℝ) :
    curveConfinementMass D (fun m => u m + t * v m) =
      curveConfinementMass D u + 2 * t * curveConfinementPair D u v +
        t ^ 2 * curveConfinementMass D v := by
  have htv : CurveEnergyDomain D (fun m => t * v m) := curveEnergyDomain_const_mul D hv t
  have huv : CurveEnergyDomain D (fun m => u m + t * v m) := curveEnergyDomain_add D hu htv
  unfold curveConfinementMass
  rw [curveConfinementPair_add_left D hu htv huv, curveConfinementPair_smul_left,
    curveConfinementPair_comm D u (fun m => u m + t * v m),
    curveConfinementPair_add_left D hu htv hu, curveConfinementPair_smul_left,
    curveConfinementPair_comm D v (fun m => u m + t * v m),
    curveConfinementPair_add_left D hu htv hv, curveConfinementPair_smul_left,
    curveConfinementPair_comm D v u]
  ring

/-- **Existence of the curve critical ground state.** Whenever `D` lies in `InFourStrip` and has a
non-unitary Frobenius eigenvalue, there exist `a* > 0` and a unit real profile `f* ∈ H_D`
(`W₈(f*) = 1`) minimizing `B_D` globally (`∀ h ∈ H_D, B_D(h, h) + a* W₈(h) ≥ 0`) and solving the
weak critical-state equation `IsCurveCriticalState D a* f*`. -/
theorem exists_curveGroundState_of_not_unitary (hD : InFourStrip D)
    (hnotU : ¬ ∀ i, ‖D.β i‖ = 1) :
    ∃ (a : ℝ) (f : ℕ → ℝ),
      curveConfinementMass D f = 1 ∧
      IsCurveCriticalState D a f ∧
      ∀ h : ℕ → ℝ, CurveEnergyDomain D h →
        0 ≤ curveBareForm D h h + a * curveConfinementMass D h := by
  classical
  -- Step 1: produce a real window vector `f₀ ∈ H_D` with `B_D(f₀, f₀) < 0`.
  have hnegIdx : 0 < hermNegIndex (D.spanGram (Fintype.card ι)) := by
    have hne0 : hermNegIndex (D.spanGram (Fintype.card ι)) ≠ 0 := fun h0 =>
      hnotU (D.unitary_iff_negIndex_spanGram_eq_zero.mpr h0)
    omega
  obtain ⟨W, hrank, hW⟩ :=
    HTGeometry.exists_isPosDefOn_finrank_eq_posIndex (-(D.spanGram (Fintype.card ι)))
  have hrank_pos : 0 < Module.finrank ℂ W := by
    change 0 < hermNegIndex (D.spanGram (Fintype.card ι)) at hnegIdx
    unfold hermNegIndex at hnegIdx
    omega
  obtain ⟨w_sub, hw_ne⟩ : ∃ w : W, w ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : Subsingleton W := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have := Module.finrank_zero_of_subsingleton (R := ℂ) (M := W)
    omega
  set z : Fin (Fintype.card ι) → ℂ := w_sub.1
  have hz_ne : z ≠ 0 := fun h => hw_ne (Subtype.ext h)
  have hz_neg : hermQuad (D.spanGram (Fintype.card ι)) z < 0 := by
    have hp := hW z w_sub.2 hz_ne
    rw [HTGeometry.hermQuad_neg] at hp
    linarith
  have hsplit_re_im : hermQuad (D.spanGram (Fintype.card ι)) z =
      hermQuad (D.spanGram (Fintype.card ι)) (fun k => ((z k).re : ℂ)) +
        hermQuad (D.spanGram (Fintype.card ι)) (fun k => ((z k).im : ℂ)) := by
    have h2 : 2 * hermQuad (D.spanGram (Fintype.card ι)) z =
        2 * (hermQuad (D.spanGram (Fintype.card ι)) (fun k => ((z k).re : ℂ)) +
          hermQuad (D.spanGram (Fintype.card ι)) (fun k => ((z k).im : ℂ))) := by
      have hdouble : ∀ g : Fin (Fintype.card ι) → Fin (Fintype.card ι) → ℝ,
          2 * (∑ k, ∑ l, g k l) = ∑ k, ∑ l, (g k l + g l k) := by
        intro g
        calc 2 * (∑ k, ∑ l, g k l)
            = (∑ k, ∑ l, g k l) + ∑ k, ∑ l, g k l := two_mul _
          _ = (∑ k, ∑ l, g k l) + ∑ k, ∑ l, g l k := congrArg (_ + ·) Finset.sum_comm
          _ = ∑ k, ((∑ l, g k l) + ∑ l, g l k) := (Finset.sum_add_distrib).symm
          _ = ∑ k, ∑ l, (g k l + g l k) :=
              Finset.sum_congr rfl fun k _ => (Finset.sum_add_distrib).symm
      simp only [hermQuad, Matrix.mulVec, dotProduct, CurveDatum.spanGram, Pi.star_apply,
        Complex.star_def]
      simp_rw [Finset.mul_sum, Complex.re_sum]
      rw [mul_add, hdouble, hdouble, hdouble, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Nat.dist_comm l k]
      simp [Complex.mul_re, Complex.mul_im]
      ring
    linarith
  obtain ⟨e_win, he_neg⟩ : ∃ e : Fin (Fintype.card ι) → ℝ,
      hermQuad (D.spanGram (Fintype.card ι)) (fun k => (e k : ℂ)) < 0 := by
    by_contra hnone
    push Not at hnone
    have h1 := hnone fun k => (z k).re
    have h2 := hnone fun k => (z k).im
    linarith
  set f₀ : ℕ → ℝ := fun m => if hm : m < Fintype.card ι then e_win ⟨m, hm⟩ else 0
  have hf₀_supp : ∀ m, Fintype.card ι ≤ m → f₀ m = 0 := fun m hm => by
    simp [f₀, not_lt.mpr hm]
  have hf₀_dom : CurveEnergyDomain D f₀ := curveEnergyDomain_of_support_lt D _ hf₀_supp
  have hf₀_neg : curveBareForm D f₀ f₀ < 0 := by
    rw [(curveBareForm_window_eq_toeplitz D (Fintype.card ι) hf₀_supp).2]
    have hfin : (fun k : Fin (Fintype.card ι) => (f₀ k : ℂ)) = fun k => (e_win k : ℂ) := by
      funext k; simp [f₀, k.isLt]
    rwa [hfin]
  -- Step 2: finite-dimensional Frobenius subspace `V₀` and Gram projection.
  let V₀ : Submodule ℝ (ℕ → ℝ) := Submodule.span ℝ (Set.range (frobGen D))
  haveI : FiniteDimensional ℝ V₀ :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range (frobGen D))
  have hV_dom : ∀ v : V₀, CurveEnergyDomain D v.1 := by
    intro v
    refine Submodule.span_induction (p := fun g _ => CurveEnergyDomain D g)
      (fun _ hx => ?_) (curveEnergyDomain_zero D)
      (fun _ _ _ _ hx hy => curveEnergyDomain_add D hx hy)
      (fun c _ _ hx => curveEnergyDomain_const_mul D hx c) v.2
    rcases hx with ⟨a, rfl⟩
    exact curveEnergyDomain_frobGen D hD a
  set d : ℕ := Module.finrank ℝ V₀
  let b : Module.Basis (Fin d) ℝ V₀ := Module.finBasis ℝ V₀
  let evalV (x : Fin d → ℝ) : V₀ := ∑ r : Fin d, x r • b r
  let evalB (x : Fin d → ℝ) : ℕ → ℝ := (evalV x).1
  have hevalB_apply : ∀ (x : Fin d → ℝ) (m : ℕ),
      evalB x m = ∑ r : Fin d, x r * (b r).1 m := by
    intro x m
    change ((∑ r : Fin d, x r • b r : V₀) : ℕ → ℝ) m = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rfl
  have hevalB_dom : ∀ x : Fin d → ℝ, CurveEnergyDomain D (evalB x) := fun x => hV_dom (evalV x)
  have hevalB_eq_zero_iff : ∀ x : Fin d → ℝ, evalB x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro h0
      have hv0 : evalV x = 0 := Subtype.ext h0
      exact Fintype.linearIndependent_iff.mp b.linearIndependent x hv0 |> fun h => funext h
    · rintro rfl
      funext m
      simp [hevalB_apply]
  let G : Matrix (Fin d) (Fin d) ℝ := fun r s => curveConfinementPair D (b r).1 (b s).1
  let Bmat : Matrix (Fin d) (Fin d) ℝ := fun r s => curveBareForm D (b r).1 (b s).1
  have hW_poly : ∀ (x : Fin d → ℝ) (g : ℕ → ℝ), CurveEnergyDomain D g →
      curveConfinementPair D (evalB x) g =
        ∑ r : Fin d, x r * curveConfinementPair D (b r).1 g := by
    intro x g hg
    have hind : ∀ S : Finset (Fin d),
        curveConfinementPair D (fun m => ∑ r ∈ S, x r * (b r).1 m) g =
          ∑ r ∈ S, x r * curveConfinementPair D (b r).1 g := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simp [curveConfinementPair]
      · intro r S hr ih
        have hS_dom : CurveEnergyDomain D (fun m => ∑ s ∈ S, x s * (b s).1 m) := by
          clear hr ih
          induction S using Finset.induction_on with
          | empty => simpa using curveEnergyDomain_zero D
          | insert s T hs ihT =>
            simpa [Finset.sum_insert hs] using
              curveEnergyDomain_add D (curveEnergyDomain_const_mul D (hV_dom (b s)) (x s)) ihT
        have hstep : (fun m => ∑ s ∈ insert r S, x s * (b s).1 m) =
            fun m => x r * (b r).1 m + ∑ s ∈ S, x s * (b s).1 m := by
          funext m; rw [Finset.sum_insert hr]
        rw [hstep, curveConfinementPair_add_left D
          (curveEnergyDomain_const_mul D (hV_dom (b r)) (x r)) hS_dom hg,
          curveConfinementPair_smul_left, Finset.sum_insert hr, ih]
    have heq : evalB x = fun m => ∑ r ∈ Finset.univ, x r * (b r).1 m := funext (hevalB_apply x)
    rw [heq]
    exact hind Finset.univ
  have hW_quad : ∀ x : Fin d → ℝ,
      curveConfinementMass D (evalB x) = ∑ r : Fin d, ∑ s : Fin d, x r * x s * G r s := by
    intro x
    unfold curveConfinementMass
    rw [hW_poly x (evalB x) (hevalB_dom x)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [curveConfinementPair_comm, hW_poly x (b r).1 (hV_dom (b r)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [G]
    rw [curveConfinementPair_comm D (b s).1 (b r).1]
    ring
  have hB_poly : ∀ (x : Fin d → ℝ) (g : ℕ → ℝ),
      curveBareForm D (evalB x) g = ∑ r : Fin d, x r * curveBareForm D (b r).1 g := by
    intro x g
    have hind : ∀ S : Finset (Fin d),
        curveBareForm D (fun m => ∑ r ∈ S, x r * (b r).1 m) g =
          ∑ r ∈ S, x r * curveBareForm D (b r).1 g := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simp [curveBareForm, curveLaplace]
      · intro r S hr ih
        have hS_dom : CurveEnergyDomain D (fun m => ∑ s ∈ S, x s * (b s).1 m) := by
          clear hr ih
          induction S using Finset.induction_on with
          | empty => simpa using curveEnergyDomain_zero D
          | insert s T hs ihT =>
            simpa [Finset.sum_insert hs] using
              curveEnergyDomain_add D (curveEnergyDomain_const_mul D (hV_dom (b s)) (x s)) ihT
        have hstep : (fun m => ∑ s ∈ insert r S, x s * (b s).1 m) =
            fun m => x r * (b r).1 m + ∑ s ∈ S, x s * (b s).1 m := by
          funext m; rw [Finset.sum_insert hr]
        rw [hstep, curveBareForm_add_left D hD
          (curveEnergyDomain_const_mul D (hV_dom (b r)) (x r)) hS_dom,
          curveBareForm_smul_left, Finset.sum_insert hr, ih]
    have heq : evalB x = fun m => ∑ r ∈ Finset.univ, x r * (b r).1 m := funext (hevalB_apply x)
    rw [heq]
    exact hind Finset.univ
  have hB_quad : ∀ x : Fin d → ℝ,
      curveBareForm D (evalB x) (evalB x) = ∑ r : Fin d, ∑ s : Fin d, x r * x s * Bmat r s := by
    intro x
    rw [hB_poly x (evalB x)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [curveBareForm_comm D hD (hV_dom (b r)) (hevalB_dom x), hB_poly x (b r).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [Bmat]
    rw [curveBareForm_comm D hD (hV_dom (b s)) (hV_dom (b r))]
    ring
  have hG_inj : Function.Injective G.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
    have hmass0 : curveConfinementMass D (evalB c) = 0 := by
      rw [hW_quad c]
      have hrow : ∀ r : Fin d, ∑ s : Fin d, G r s * c s = 0 := fun r => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hc r
      calc (∑ r : Fin d, ∑ s : Fin d, c r * c s * G r s)
          = ∑ r : Fin d, c r * ∑ s : Fin d, G r s * c s := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun s _ => by ring
        _ = 0 := by simp [hrow]
    exact (hevalB_eq_zero_iff c).mp ((curveConfinementMass_eq_zero_iff D (hevalB_dom c)).mp hmass0)
  have hG_surj : Function.Surjective G.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq
      (LinearEquiv.ofInjective G.mulVecLin hG_inj).finrank_eq.symm
  -- Orthogonal projection onto `V₀` preserves `B_D` and contracts `W₈`.
  have hproj : ∀ h : ℕ → ℝ, CurveEnergyDomain D h →
      ∃ c : Fin d → ℝ,
        curveBareForm D (evalB c) (evalB c) = curveBareForm D h h ∧
        curveConfinementMass D (evalB c) ≤ curveConfinementMass D h := by
    intro h hh
    obtain ⟨c, hc⟩ := hG_surj (fun r => curveConfinementPair D (b r).1 h)
    refine ⟨c, ?_, ?_⟩
    · set res : ℕ → ℝ := fun m => h m - evalB c m
      have hres_dom : CurveEnergyDomain D res := curveEnergyDomain_sub D hh (hevalB_dom c)
      have hres_basis : ∀ r : Fin d, curveConfinementPair D (b r).1 res = 0 := by
        intro r
        have hcr : ∑ s : Fin d, G r s * c s = curveConfinementPair D (b r).1 h :=
          congrFun hc r
        have hsub : (fun m => h m - evalB c m) = fun m => h m + (-1) * evalB c m := by
          funext m; ring
        rw [curveConfinementPair_comm D (b r).1 res,
          show res = fun m => h m + (-1) * evalB c m from hsub,
          curveConfinementPair_add_left D hh (curveEnergyDomain_const_mul D (hevalB_dom c) (-1))
            (hV_dom (b r)),
          curveConfinementPair_smul_left, hW_poly c (b r).1 (hV_dom (b r)),
          curveConfinementPair_comm D h (b r).1]
        have hsum_eq : (∑ s : Fin d, c s * curveConfinementPair D (b s).1 (b r).1) =
            ∑ s : Fin d, G r s * c s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          dsimp [G]
          rw [curveConfinementPair_comm D (b s).1 (b r).1]; ring
        linarith
      have hres_V : ∀ v : V₀, curveConfinementPair D v.1 res = 0 := by
        intro v
        have hv : v = evalV (b.repr v) := (b.sum_repr v).symm
        have hv1 : v.1 = evalB (b.repr v) := congrArg Subtype.val hv
        rw [hv1, hW_poly (b.repr v) res hres_dom]
        simp [hres_basis]
      have hlap_inv_eq : ∀ i : ι, curveLaplace (evalB c) (D.β i)⁻¹ = curveLaplace h (D.β i)⁻¹ := by
        intro i
        have hinl : curveConfinementPair D (frobGen D (Sum.inl i)) res = 0 :=
          hres_V ⟨frobGen D (Sum.inl i), Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩
        have hinr : curveConfinementPair D (frobGen D (Sum.inr i)) res = 0 :=
          hres_V ⟨frobGen D (Sum.inr i), Submodule.subset_span ⟨Sum.inr i, rfl⟩⟩
        have hsplit : h = fun m => evalB c m + res m := by funext m; dsimp [res]; ring
        have h1 : curveConfinementPair D (frobGen D (Sum.inl i)) h =
            curveConfinementPair D (frobGen D (Sum.inl i)) (evalB c) := by
          have := curveConfinementPair_add_left D (hevalB_dom c) hres_dom
            (curveEnergyDomain_frobGen D hD (Sum.inl i))
          rw [curveConfinementPair_comm D (frobGen D (Sum.inl i)) h, hsplit, this,
            curveConfinementPair_comm D (evalB c), curveConfinementPair_comm D res, hinl, add_zero]
        have h2 : curveConfinementPair D (frobGen D (Sum.inr i)) h =
            curveConfinementPair D (frobGen D (Sum.inr i)) (evalB c) := by
          have := curveConfinementPair_add_left D (hevalB_dom c) hres_dom
            (curveEnergyDomain_frobGen D hD (Sum.inr i))
          rw [curveConfinementPair_comm D (frobGen D (Sum.inr i)) h, hsplit, this,
            curveConfinementPair_comm D (evalB c), curveConfinementPair_comm D res, hinr, add_zero]
        rw [curveLaplace_inv_eq_frobGen_pair D hD (hevalB_dom c) i,
          curveLaplace_inv_eq_frobGen_pair D hD hh i, h1, h2]
      have hlap_eq : ∀ i : ι, curveLaplace (evalB c) (D.β i) = curveLaplace h (D.β i) := by
        intro i
        have hfe : D.β i = (D.β (D.fePerm i))⁻¹ := by
          rw [β_fePerm_eq_inv D i, inv_inv]
        rw [hfe, hlap_inv_eq (D.fePerm i)]
      unfold curveBareForm
      simp_rw [hlap_eq, hlap_inv_eq]
    · set res : ℕ → ℝ := fun m => h m - evalB c m
      have hres_dom : CurveEnergyDomain D res := curveEnergyDomain_sub D hh (hevalB_dom c)
      have hres_basis : ∀ r : Fin d, curveConfinementPair D (b r).1 res = 0 := by
        intro r
        have hcr : ∑ s : Fin d, G r s * c s = curveConfinementPair D (b r).1 h :=
          congrFun hc r
        have hsub : (fun m => h m - evalB c m) = fun m => h m + (-1) * evalB c m := by
          funext m; ring
        rw [curveConfinementPair_comm D (b r).1 res,
          show res = fun m => h m + (-1) * evalB c m from hsub,
          curveConfinementPair_add_left D hh (curveEnergyDomain_const_mul D (hevalB_dom c) (-1))
            (hV_dom (b r)),
          curveConfinementPair_smul_left, hW_poly c (b r).1 (hV_dom (b r)),
          curveConfinementPair_comm D h (b r).1]
        have hsum_eq : (∑ s : Fin d, c s * curveConfinementPair D (b s).1 (b r).1) =
            ∑ s : Fin d, G r s * c s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          dsimp [G]
          rw [curveConfinementPair_comm D (b s).1 (b r).1]; ring
        linarith
      have horth : curveConfinementPair D (evalB c) res = 0 := by
        rw [hW_poly c res hres_dom]
        simp [hres_basis]
      have hsplit : h = fun m => evalB c m + res m := by funext m; dsimp [res]; ring
      have hpyth : curveConfinementMass D h =
          curveConfinementMass D (evalB c) + curveConfinementMass D res := by
        have hlin := curveConfinementMass_add_lin D (hevalB_dom c) hres_dom 1
        simp only [one_mul, one_pow, horth, mul_zero, add_zero] at hlin
        rw [hsplit]
        exact hlin
      linarith [curveConfinementMass_nonneg D res]
  -- Step 3: minimize the Rayleigh quotient on the compact unit sphere of `Fin d → ℝ`.
  obtain ⟨c₀, hc₀_B, -⟩ := hproj f₀ hf₀_dom
  have hc₀_neg : curveBareForm D (evalB c₀) (evalB c₀) < 0 := hc₀_B.trans_lt hf₀_neg
  have hc₀_ne : c₀ ≠ 0 := by
    rintro rfl
    have h0 : evalB 0 = 0 := (hevalB_eq_zero_iff 0).mpr rfl
    simp [h0, curveBareForm, curveLaplace] at hc₀_neg
  set u₀ : Fin d → ℝ := (‖c₀‖⁻¹) • c₀
  have hu₀_mem : u₀ ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc₀_ne)]
  have hS_ne : (Metric.sphere (0 : Fin d → ℝ) 1).Nonempty := ⟨u₀, hu₀_mem⟩
  have hS_comp : IsCompact (Metric.sphere (0 : Fin d → ℝ) 1) := isCompact_sphere 0 1
  let rayleigh (x : Fin d → ℝ) : ℝ :=
    curveBareForm D (evalB x) (evalB x) / curveConfinementMass D (evalB x)
  have hW_pos_of_ne : ∀ {x : Fin d → ℝ}, x ≠ 0 → 0 < curveConfinementMass D (evalB x) := by
    intro x hx
    exact lt_of_le_of_ne (curveConfinementMass_nonneg D (evalB x))
      (Ne.symm ((curveConfinementMass_eq_zero_iff D (hevalB_dom x)).not.mpr
        ((hevalB_eq_zero_iff x).not.mpr hx)))
  have hray_cont : ContinuousOn rayleigh (Metric.sphere (0 : Fin d → ℝ) 1) := by
    have hcB : Continuous fun x : Fin d → ℝ => curveBareForm D (evalB x) (evalB x) := by
      simp_rw [hB_quad]
      fun_prop
    have hcW : Continuous fun x : Fin d → ℝ => curveConfinementMass D (evalB x) := by
      simp_rw [hW_quad]
      fun_prop
    refine hcB.continuousOn.div hcW.continuousOn fun x hx => ?_
    have hx_ne : x ≠ 0 := by
      rintro rfl; simp at hx
    exact (hW_pos_of_ne hx_ne).ne'
  obtain ⟨x_min, hx_mem, hx_min⟩ := hS_comp.exists_isMinOn hS_ne hray_cont
  have hray_smul : ∀ {x : Fin d → ℝ} {t : ℝ}, t ≠ 0 → rayleigh (t • x) = rayleigh x := by
    intro x t ht
    have hev : evalB (t • x) = fun m => t * evalB x m := by
      funext m; simp [hevalB_apply, Finset.mul_sum, mul_assoc]
    dsimp [rayleigh]
    rw [hev, curveBareForm_smul_left, curveBareForm_comm D hD (hevalB_dom x)
      (curveEnergyDomain_const_mul D (hevalB_dom x) t), curveBareForm_smul_left,
      curveBareForm_comm D hD (hevalB_dom x) (hevalB_dom x)]
    have hWm : curveConfinementMass D (fun m => t * evalB x m) =
        t ^ 2 * curveConfinementMass D (evalB x) := by
      unfold curveConfinementMass
      rw [curveConfinementPair_smul_left, curveConfinementPair_comm,
        curveConfinementPair_smul_left, curveConfinementPair_comm]
      ring
    rw [hWm]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    calc t * (t * curveBareForm D (evalB x) (evalB x)) / (t ^ 2 * curveConfinementMass D (evalB x))
        = (t ^ 2 * curveBareForm D (evalB x) (evalB x)) /
            (t ^ 2 * curveConfinementMass D (evalB x)) := by ring
      _ = curveBareForm D (evalB x) (evalB x) / curveConfinementMass D (evalB x) :=
          mul_div_mul_left _ _ ht2
  have hray_u₀ : rayleigh u₀ < 0 := by
    dsimp [u₀]
    rw [hray_smul (inv_ne_zero (norm_ne_zero_iff.mpr hc₀_ne))]
    exact div_neg_of_neg_of_pos hc₀_neg (hW_pos_of_ne hc₀_ne)
  have hray_min_neg : rayleigh x_min < 0 := (hx_min hu₀_mem).trans_lt hray_u₀
  set a_star : ℝ := -rayleigh x_min
  have ha_pos : 0 < a_star := neg_pos.mpr hray_min_neg
  have hx_ne : x_min ≠ 0 := by rintro rfl; simp at hx_mem
  set normW : ℝ := Real.sqrt (curveConfinementMass D (evalB x_min))
  have hnormW_pos : 0 < normW := Real.sqrt_pos.mpr (hW_pos_of_ne hx_ne)
  set f_star : ℕ → ℝ := fun m => normW⁻¹ * evalB x_min m
  have hf_dom : CurveEnergyDomain D f_star := curveEnergyDomain_const_mul D (hevalB_dom x_min) _
  have hf_mass : curveConfinementMass D f_star = 1 := by
    dsimp [f_star]
    unfold curveConfinementMass
    rw [curveConfinementPair_smul_left, curveConfinementPair_comm,
      curveConfinementPair_smul_left, curveConfinementPair_comm]
    have hpos_pair : 0 < curveConfinementPair D (evalB x_min) (evalB x_min) := hW_pos_of_ne hx_ne
    have hsq : normW ^ 2 = curveConfinementPair D (evalB x_min) (evalB x_min) :=
      Real.sq_sqrt hpos_pair.le
    calc normW⁻¹ * (normW⁻¹ * curveConfinementPair D (evalB x_min) (evalB x_min))
        = (normW ^ 2)⁻¹ * curveConfinementPair D (evalB x_min) (evalB x_min) := by ring
      _ = 1 := by rw [hsq, inv_mul_cancel₀ hpos_pair.ne']
  have hf_ne : f_star ≠ 0 := by
    intro h0
    have := (curveConfinementMass_eq_zero_iff D hf_dom).mpr h0
    linarith
  have hf_bare : curveBareForm D f_star f_star = -a_star := by
    dsimp [f_star, a_star, rayleigh]
    rw [curveBareForm_smul_left, curveBareForm_comm D hD (hevalB_dom x_min)
      (curveEnergyDomain_const_mul D (hevalB_dom x_min) normW⁻¹),
      curveBareForm_smul_left, curveBareForm_comm D hD (hevalB_dom x_min) (hevalB_dom x_min)]
    have hsq : normW ^ 2 = curveConfinementMass D (evalB x_min) :=
      Real.sq_sqrt (hW_pos_of_ne hx_ne).le
    rw [neg_neg, ← hsq]
    ring
  have hvar_V : ∀ c : Fin d → ℝ,
      0 ≤ curveBareForm D (evalB c) (evalB c) + a_star * curveConfinementMass D (evalB c) := by
    intro c
    by_cases hc0 : c = 0
    · subst hc0
      have h0 : evalB 0 = 0 := (hevalB_eq_zero_iff 0).mpr rfl
      simp [h0, curveBareForm, curveLaplace, curveConfinementMass, curveConfinementPair]
    · set u : Fin d → ℝ := (‖c‖⁻¹) • c
      have hu_mem : u ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc0)]
      have hle : -a_star ≤ rayleigh c := by
        have h1 : rayleigh x_min ≤ rayleigh u := hx_min hu_mem
        rw [hray_smul (inv_ne_zero (norm_ne_zero_iff.mpr hc0))] at h1
        dsimp [a_star]; linarith
      have hWc := hW_pos_of_ne hc0
      dsimp [rayleigh] at hle
      have := (le_div_iff₀ hWc).mp hle
      linarith
  have hvar_all : ∀ h : ℕ → ℝ, CurveEnergyDomain D h →
      0 ≤ curveBareForm D h h + a_star * curveConfinementMass D h := by
    intro h hh
    obtain ⟨c, hcB, hcW⟩ := hproj h hh
    have hv := hvar_V c
    have haW : a_star * curveConfinementMass D (evalB c) ≤ a_star * curveConfinementMass D h :=
      mul_le_mul_of_nonneg_left hcW ha_pos.le
    linarith
  -- Step 4: Euler–Lagrange weak equation from global variational minimality.
  have hweak : ∀ g : ℕ → ℝ, CurveEnergyDomain D g →
      curveBareForm D f_star g + a_star * curveConfinementPair D f_star g = 0 := by
    intro g hg
    set M : ℝ := curveBareForm D f_star g + a_star * curveConfinementPair D f_star g
    set Q : ℝ := curveBareForm D g g + a_star * curveConfinementMass D g
    have hQ_nn : 0 ≤ Q := hvar_all g hg
    have hquad_t : ∀ t : ℝ, 0 ≤ 2 * t * M + t ^ 2 * Q := by
      intro t
      have ht_dom : CurveEnergyDomain D (fun m => f_star m + t * g m) :=
        curveEnergyDomain_add D hf_dom (curveEnergyDomain_const_mul D hg t)
      have hv := hvar_all (fun m => f_star m + t * g m) ht_dom
      rw [curveBareForm_add_lin D hD hf_dom hg t,
        curveConfinementMass_add_lin D hf_dom hg t, hf_bare, hf_mass] at hv
      dsimp [M, Q]
      linarith
    by_contra hM_ne
    have hden : 0 < Q + 1 := by linarith
    have hbad := hquad_t (-M / (Q + 1))
    have hneg : 2 * (-M / (Q + 1)) * M + (-M / (Q + 1)) ^ 2 * Q < 0 := by
      have hid : 2 * (-M / (Q + 1)) * M + (-M / (Q + 1)) ^ 2 * Q =
          -(M ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
        field_simp
        ring
      rw [hid]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (mul_pos (sq_pos_of_ne_zero hM_ne) (by linarith)))
        (sq_pos_of_pos hden)
    linarith
  exact ⟨a_star, f_star, hf_mass, ⟨ha_pos, hf_dom, hf_ne, hweak⟩, hvar_all⟩

/-- **Curve critical-state dichotomy.** For `D` in `InFourStrip`, a curve critical state exists at
some `a > 0` if and only if `D` has at least one non-unitary Frobenius eigenvalue. -/
theorem curveCriticalState_iff_not_unitary (hD : InFourStrip D) :
    (∃ (a : ℝ) (f : ℕ → ℝ), IsCurveCriticalState D a f) ↔ ¬ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · rintro ⟨a, f, hf⟩ hU
    exact not_isCurveCriticalState_of_unitary D hU a f hf
  · intro hnotU
    obtain ⟨a, f, -, hf, -⟩ := exists_curveGroundState_of_not_unitary D hD hnotU
    exact ⟨a, f, hf⟩

/-- **Exact closed form of every curve critical state.** Every curve critical state `f` at `a > 0`
has the exact exponential representation
`(f m : ℂ) = -(1/a) ∑_{i ∈ ι} L_D f(β_i) · (β_i q^{-8})^m`. -/
theorem curveCriticalState_eq_sum {a : ℝ} {f : ℕ → ℝ} (hf : IsCurveCriticalState D a f) (m : ℕ) :
    (f m : ℂ) = -(1 / (a : ℂ)) *
      ∑ i : ι, curveLaplace f (D.β i) * (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) ^ m := by
  obtain ⟨ha, _, _, hweak⟩ := hf
  have hm := hweak (siteDelta m) (curveEnergyDomain_siteDelta D m)
  rw [curveConfinementPair_siteDelta_right] at hm
  have hmC : (curveBareForm D f (siteDelta m) : ℂ) +
      (a : ℂ) * (f m : ℂ) * ((D.q ^ (8 * m) : ℝ) : ℂ) = 0 := by
    exact_mod_cast (by linarith : curveBareForm D f (siteDelta m) + a * f m * D.q ^ (8 * m) = 0)
  rw [← sum_curveLaplace_eq_ofReal_bareForm] at hmC
  have hdel : ∀ i : ι, curveLaplace (siteDelta m) (D.β i)⁻¹ = D.β i ^ m := fun i => by
    rw [curveLaplace_siteDelta, inv_inv]
  simp_rw [hdel] at hmC
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hqC : ((D.q ^ (8 * m) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (q_pow_pos D _).ne'
  have hpow : ((D.q ^ (8 * m) : ℝ) : ℂ) = (((D.q ^ 8 : ℝ) : ℂ)) ^ m := by
    push_cast; rw [← pow_mul]
  have hsum_pow : (∑ i : ι, curveLaplace f (D.β i) * (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) ^ m) *
      ((D.q ^ (8 * m) : ℝ) : ℂ) =
      ∑ i : ι, curveLaplace f (D.β i) * D.β i ^ m := by
    rw [hpow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, mul_assoc, mul_assoc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero m (Complex.ofReal_ne_zero.mpr (q_pow_pos D 8).ne')), mul_one]
  have hkey : (a : ℂ) * ((f m : ℂ) * ((D.q ^ (8 * m) : ℝ) : ℂ)) =
      (a : ℂ) * ((-(1 / (a : ℂ)) *
        ∑ i : ι, curveLaplace f (D.β i) * (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) ^ m) *
        ((D.q ^ (8 * m) : ℝ) : ℂ)) := by
    calc (a : ℂ) * ((f m : ℂ) * ((D.q ^ (8 * m) : ℝ) : ℂ))
        = -(∑ i : ι, curveLaplace f (D.β i) * D.β i ^ m) := by linear_combination hmC
      _ = -(∑ i : ι, curveLaplace f (D.β i) * (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) ^ m) *
            ((D.q ^ (8 * m) : ℝ) : ℂ) := by rw [← hsum_pow, neg_mul]
      _ = (a : ℂ) * ((-(1 / (a : ℂ)) *
            ∑ i : ι, curveLaplace f (D.β i) * (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) ^ m) *
            ((D.q ^ (8 * m) : ℝ) : ℂ)) := by field_simp
  exact mul_right_cancel₀ hqC (mul_left_cancel₀ haC hkey)

/-- **Rational continuation of a curve critical state.** On `{|z| > q^{-4}}`,
`L_D f(z) = -(1/a) ∑_{i ∈ ι} z L_D f(β_i) / (z - β_i q^{-8})`, exposing simple poles at the
transported Frobenius eigenvalues `β_i q^{-8}` (`w = z_i - 8`). -/
theorem curveCriticalState_laplace_eq_rational (hD : InFourStrip D) {a : ℝ} {f : ℕ → ℝ}
    (hf : IsCurveCriticalState D a f) {z : ℂ} (hz : (D.q ^ 4)⁻¹ < ‖z‖) :
    curveLaplace f z = -(1 / (a : ℂ)) *
      ∑ i : ι, z * curveLaplace f (D.β i) / (z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) := by
  have hz_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr (q_pow_pos D 4)) hz
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz_pos
  have hgeom_i : ∀ i : ι,
      HasSum (fun m : ℕ => curveLaplace f (D.β i) *
          (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * z⁻¹) ^ m)
        (z * curveLaplace f (D.β i) / (z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹)) := by
    intro i
    set r : ℂ := D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * z⁻¹
    have hr_lt : ‖r‖ < 1 := by
      dsimp [r]
      rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (q_pow_pos D 8).le]
      have h1 : ‖D.β i‖ * (D.q ^ 8)⁻¹ < (D.q ^ 4)⁻¹ := by
        have hβ := hD i
        have hq4 := q_pow_pos D 4
        have hq8 : D.q ^ 8 = D.q ^ 4 * D.q ^ 4 := by ring
        rw [hq8, mul_inv, ← mul_assoc]
        have hlt1 : ‖D.β i‖ * (D.q ^ 4)⁻¹ < 1 :=
          (mul_inv_lt_iff₀ hq4).mpr (by linarith)
        nlinarith [inv_pos.mpr hq4]
      exact (mul_inv_lt_iff₀ hz_pos).mpr (by linarith [h1, hz])
    have h1r : 1 - r ≠ 0 := by
      intro h0
      have : r = 1 := by linear_combination -h0
      rw [this, norm_one] at hr_lt
      exact lt_irrefl _ hr_lt
    have hzr : z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ ≠ 0 := by
      intro h0
      apply h1r
      dsimp [r]
      have hz_eq : D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ = z := by linear_combination -h0
      rw [hz_eq, mul_inv_cancel₀ hz_ne, sub_self]
    have hg := (hasSum_geometric_of_norm_lt_one hr_lt).mul_left (curveLaplace f (D.β i))
    have hval : z * curveLaplace f (D.β i) / (z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) =
        curveLaplace f (D.β i) * (1 - r)⁻¹ := by
      rw [inv_eq_one_div (1 - r), mul_one_div, div_eq_div_iff hzr h1r]
      dsimp only [r]
      calc z * curveLaplace f (D.β i) * (1 - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * z⁻¹)
          = curveLaplace f (D.β i) * (z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * (z * z⁻¹)) := by ring
        _ = curveLaplace f (D.β i) * (z - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) := by
            rw [mul_inv_cancel₀ hz_ne, mul_one]
    exact hval ▸ hg
  have hsum_all := (hasSum_sum fun i (_ : i ∈ Finset.univ) => hgeom_i i).mul_left
    (-(1 / (a : ℂ)))
  have hterm : (fun m : ℕ => (f m : ℂ) * (z⁻¹) ^ m) =
      fun m : ℕ => -(1 / (a : ℂ)) *
        ∑ i : ι, curveLaplace f (D.β i) *
          (D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * z⁻¹) ^ m := by
    funext m
    rw [curveCriticalState_eq_sum D hf m, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_pow]
  unfold curveLaplace
  rw [hterm]
  exact hsum_all.tsum_eq

/-- **Curve `(★)` identity.** For `|z| > q^4`,
`-a · L_D f(z q^{-8}) = ∑_{i ∈ ι} z · L_D f(β_i) / (z - β_i)`. -/
theorem curveCriticalState_star_identity (hD : InFourStrip D) {a : ℝ} {f : ℕ → ℝ}
    (hf : IsCurveCriticalState D a f) {z : ℂ} (hz : D.q ^ 4 < ‖z‖) :
    -(a : ℂ) * curveLaplace f (z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) =
      ∑ i : ι, z * curveLaplace f (D.β i) / (z - D.β i) := by
  have hq8_pos : 0 < D.q ^ 8 := q_pow_pos D 8
  have hq8C : ((D.q ^ 8 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq8_pos.ne'
  have hz8 : (D.q ^ 4)⁻¹ < ‖z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hq8_pos.le]
    have hq8 : D.q ^ 8 = D.q ^ 4 * D.q ^ 4 := by ring
    have hq4 : 0 < D.q ^ 4 := q_pow_pos D 4
    rw [hq8, mul_inv]
    have h1 : 1 < ‖z‖ * (D.q ^ 4)⁻¹ := (lt_mul_inv_iff₀ hq4).mpr (by linarith)
    nlinarith [inv_pos.mpr hq4]
  rw [curveCriticalState_laplace_eq_rational D hD hf hz8]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hf.1.ne'
  have hcancel : -(a : ℂ) * (-(1 / (a : ℂ)) *
      ∑ i : ι, z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * curveLaplace f (D.β i) /
        (z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹)) =
      ∑ i : ι, z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * curveLaplace f (D.β i) /
        (z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹) := by
    field_simp
  rw [hcancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ - D.β i * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ =
      (z - D.β i) * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ := by ring
  rw [hsub, show z * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ * curveLaplace f (D.β i) =
    (z * curveLaplace f (D.β i)) * ((D.q ^ 8 : ℝ) : ℂ)⁻¹ by ring]
  exact mul_div_mul_right _ _ (inv_ne_zero hq8C)

/-- **Zero Parseval identity of a curve critical state.** Splitting `ι` into unitary (`‖β_i‖ = 1`)
and off-circle (`‖β_i‖ ≠ 1`) Frobenius eigenvalues gives
`∑_{‖β_i‖=1} ‖L_D f(β_i)‖² + ∑_{‖β_i‖≠1} Re(L_D f(β_i) L_D f(β_i⁻¹)) = -a W₈(f) < 0`. -/
theorem curveCriticalState_zeroParseval {a : ℝ} {f : ℕ → ℝ} (hf : IsCurveCriticalState D a f) :
    (∑ i ∈ Finset.univ.filter (fun i : ι => ‖D.β i‖ = 1), ‖curveLaplace f (D.β i)‖ ^ 2) +
      (∑ i ∈ Finset.univ.filter (fun i : ι => ‖D.β i‖ ≠ 1),
        (curveLaplace f (D.β i) * curveLaplace f (D.β i)⁻¹).re) =
      -a * curveConfinementMass D f ∧
    -a * curveConfinementMass D f < 0 := by
  classical
  obtain ⟨ha, hdom, hne, hweak⟩ := hf
  have hself := hweak f hdom
  have hW_pos : 0 < curveConfinementMass D f :=
    lt_of_le_of_ne (curveConfinementMass_nonneg D f)
      (Ne.symm ((curveConfinementMass_eq_zero_iff D hdom).not.mpr hne))
  have hB_eq : curveBareForm D f f = -a * curveConfinementMass D f := by
    unfold curveConfinementMass; linarith
  refine ⟨?_, by nlinarith⟩
  rw [← hB_eq]
  unfold curveBareForm
  rw [Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ι => ‖D.β i‖ = 1)]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 : ‖D.β i‖ = 1 := (Finset.mem_filter.mp hi).2
  have hinv : (D.β i)⁻¹ = conj (D.β i) := by
    have hm : D.β i * conj (D.β i) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num
    exact (eq_inv_of_mul_eq_one_right hm).symm
  rw [hinv, ← curveLaplace_conj f (D.β i), Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- **Simultaneously seen outer and inner Frobenius roots.** Every curve critical state `f` sees an
outer Frobenius root `β_{i₀}` (`‖β_{i₀}‖ > 1`) together with its functional-equation inner partner
`β_{fe i₀} = β_{i₀}⁻¹` (`‖β_{fe i₀}‖ < 1`), with `Re(L_D f(β_{i₀}) L_D f(β_{fe i₀})) < 0` and in
particular `L_D f(β_{i₀}) ≠ 0` and `L_D f(β_{fe i₀}) ≠ 0`. -/
theorem curveCriticalState_sees_outer_and_inner_root {a : ℝ} {f : ℕ → ℝ}
    (hf : IsCurveCriticalState D a f) :
    ∃ i₀ : ι, 1 < ‖D.β i₀‖ ∧ ‖D.β (D.fePerm i₀)‖ < 1 ∧
      (curveLaplace f (D.β i₀) * curveLaplace f (D.β (D.fePerm i₀))).re < 0 ∧
      curveLaplace f (D.β i₀) ≠ 0 ∧ curveLaplace f (D.β (D.fePerm i₀)) ≠ 0 := by
  classical
  obtain ⟨hpar, hneg⟩ := curveCriticalState_zeroParseval D hf
  have hon_nn : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : ι => ‖D.β i‖ = 1),
      ‖curveLaplace f (D.β i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hoff_neg : (∑ i ∈ Finset.univ.filter (fun i : ι => ‖D.β i‖ ≠ 1),
      (curveLaplace f (D.β i) * curveLaplace f (D.β i)⁻¹).re) < 0 := by linarith
  obtain ⟨i₁, hi₁_mem, hi₁_neg⟩ : ∃ i₁ ∈ Finset.univ.filter (fun i : ι => ‖D.β i‖ ≠ 1),
      (curveLaplace f (D.β i₁) * curveLaplace f (D.β i₁)⁻¹).re < 0 := by
    by_contra hall
    push Not at hall
    have := Finset.sum_nonneg hall
    linarith
  have hi₁_ne : ‖D.β i₁‖ ≠ 1 := (Finset.mem_filter.mp hi₁_mem).2
  rcases lt_or_gt_of_ne hi₁_ne with hlt | hgt
  · refine ⟨D.fePerm i₁, ?_, ?_, ?_, ?_, ?_⟩
    · rw [D.norm_β_fePerm]
      exact (one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero i₁))).mpr hlt
    · rwa [β_fePerm_fePerm D i₁]
    · rw [β_fePerm_fePerm D i₁, β_fePerm_eq_inv D i₁, mul_comm]
      exact hi₁_neg
    · intro h0
      rw [← β_fePerm_eq_inv D i₁, h0, mul_zero, Complex.zero_re] at hi₁_neg
      exact lt_irrefl _ hi₁_neg
    · intro h0
      rw [β_fePerm_fePerm D i₁] at h0
      rw [h0, zero_mul, Complex.zero_re] at hi₁_neg
      exact lt_irrefl _ hi₁_neg
  · refine ⟨i₁, hgt, ?_, ?_, ?_, ?_⟩
    · rw [D.norm_β_fePerm]
      exact inv_lt_one_of_one_lt₀ hgt
    · rwa [β_fePerm_eq_inv D i₁]
    · intro h0; rw [h0, zero_mul, Complex.zero_re] at hi₁_neg; exact lt_irrefl _ hi₁_neg
    · intro h0
      rw [β_fePerm_eq_inv D i₁] at h0
      rw [h0, mul_zero, Complex.zero_re] at hi₁_neg
      exact lt_irrefl _ hi₁_neg

/-! ### 3. Curve beyond-the-wall prime-head balance and seen-inner-root pole obstruction -/

/-- Discrete Lévy head `H_{D, n}(f, z) = ∑_{m < n} f(m) (z⁻¹)^m` at lag `n`. -/
def curveLevyHead (f : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n, (f m : ℂ) * (z⁻¹) ^ m

/-- Curve beyond-the-wall prime-pole balance
`Φ_D(f, z) = -∑_{n ≥ 0} D.trace(n) z^n H_{D, n}(f, z)` (`n = 0` vanishes identically). -/
def curveBeyondWallBalance (f : ℕ → ℝ) (z : ℂ) : ℂ :=
  -∑' n : ℕ, (D.trace n : ℂ) * z ^ n * curveLevyHead f z n

/-- **Curve beyond-the-wall prime continuation:** for every profile `h ∈ H_D`, there exists `r₀ > 0`
and a holomorphic function `H` on the unit disc `{|z| < 1}` (`Re p < 0`) agreeing with
`curveBeyondWallBalance D h` on `{|z| < r₀}`. -/
def CurveBeyondTheWallPrimeContinuation : Prop :=
  ∀ h : ℕ → ℝ, CurveEnergyDomain D h →
    ∃ (r₀ : ℝ) (H : ℂ → ℂ), 0 < r₀ ∧
      DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      Set.EqOn H (curveBeyondWallBalance D h) (Metric.ball 0 r₀)

private theorem sum_range_geometric_tail {α : Type*} [CommRing α] (A : ℕ → α) (w : α) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, A m * w ^ (n - m)) * (1 - w) =
      ∑ m ∈ Finset.range N, A m * (w - w ^ (N - m)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, Finset.sum_range_succ]
    have hlast : A N * (w - w ^ (N + 1 - N)) = 0 := by simp
    rw [hlast, add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_lt : m < N := Finset.mem_range.mp hm
    have hsub : N + 1 - m = (N - m) + 1 := by omega
    rw [hsub, pow_succ]
    ring

private theorem hasSum_frob_levyHead_single {A : ℕ → ℂ} {L : ℂ} (hA_sum : HasSum A L)
    (hA_norm : Summable fun m : ℕ => ‖A m‖) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => ∑ m ∈ Finset.range n, A m * w ^ (n - m)) (w / (1 - w) * L) := by
  set r : ℝ := ‖w‖
  have hr_nn : 0 ≤ r := norm_nonneg w
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hw
  have h1w_ne : 1 - w ≠ 0 := by
    intro h0
    have hw1 : w = 1 := by linear_combination -h0
    have hr1 : r = 1 := by dsimp [r]; rw [hw1, norm_one]
    linarith
  -- Step 1: absolute summability of the outer series by telescopic partial-sum bound.
  have hgn_norm : Summable fun n : ℕ => ‖∑ m ∈ Finset.range n, A m * w ^ (n - m)‖ := by
    refine summable_of_sum_range_le (c := (r / (1 - r)) * ∑' m : ℕ, ‖A m‖)
      (fun _ => norm_nonneg _) fun N => ?_
    have htri : ∑ n ∈ Finset.range N, ‖∑ m ∈ Finset.range n, A m * w ^ (n - m)‖ ≤
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, ‖A m‖ * r ^ (n - m) := by
      refine Finset.sum_le_sum fun n _ => ?_
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, norm_pow]
    have htel := sum_range_geometric_tail (fun m => ‖A m‖) r N
    have h1 : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, ‖A m‖ * r ^ (n - m)) * (1 - r) ≤
        r * ∑' m : ℕ, ‖A m‖ := by
      rw [htel]
      calc (∑ m ∈ Finset.range N, ‖A m‖ * (r - r ^ (N - m)))
          ≤ ∑ m ∈ Finset.range N, ‖A m‖ * r := by
            refine Finset.sum_le_sum fun m _ => ?_
            have hrp : 0 ≤ r ^ (N - m) := pow_nonneg hr_nn _
            exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ = r * ∑ m ∈ Finset.range N, ‖A m‖ := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ r * ∑' m : ℕ, ‖A m‖ :=
            mul_le_mul_of_nonneg_left
              (hA_norm.sum_le_tsum (Finset.range N) fun _ _ => norm_nonneg _) hr_nn
    have h2 : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, ‖A m‖ * r ^ (n - m) ≤
        (r / (1 - r)) * ∑' m : ℕ, ‖A m‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1r_pos]
      exact h1
    exact htri.trans h2
  -- Step 2: evaluate the partial sums as `N → ∞` via `sum_range_geometric_tail`.
  have hgn_sum : Summable fun n : ℕ => ∑ m ∈ Finset.range n, A m * w ^ (n - m) :=
    hgn_norm.of_norm
  suffices hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ∑ m ∈ Finset.range n, A m * w ^ (n - m)) atTop (𝓝 (w / (1 - w) * L)) by
    have heq := tendsto_nhds_unique hgn_sum.hasSum.tendsto_sum_nat hlim
    exact heq ▸ hgn_sum.hasSum
  have hrem_zero : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, A m * w ^ (N - m)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    -- Choose `M` so the tail `∑_{m ≥ M} ‖A m‖ < ε / 2`.
    have htail_tend : Tendsto (fun M : ℕ => (∑' m : ℕ, ‖A m‖) - ∑ m ∈ Finset.range M, ‖A m‖)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := ∑' m : ℕ, ‖A m‖)).sub hA_norm.hasSum.tendsto_sum_nat
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp htail_tend) (ε / 2) hε2
    have hM_bound : (∑' m : ℕ, ‖A m‖) - ∑ m ∈ Finset.range M, ‖A m‖ < ε / 2 := by
      have := hM M le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (sub_nonneg.mpr (hA_norm.sum_le_tsum (Finset.range M) fun _ _ => norm_nonneg _))] at this
      exact this
    set SA : ℝ := (∑' m : ℕ, ‖A m‖) + 1
    have hSA_pos : 0 < SA := add_pos_of_nonneg_of_pos (tsum_nonneg fun _ => norm_nonneg _) one_pos
    have hpow_zero : Tendsto (fun k : ℕ => SA * r ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr_nn hw).const_mul SA
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hpow_zero) (ε / 2) hε2
    refine ⟨M + K, fun N hN => ?_⟩
    rw [dist_zero_right]
    have hMN : M ≤ N := by omega
    have hsplit : Finset.range N = Finset.range M ∪ Finset.Ico M N := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le M) hMN).symm
    have hdisj : Disjoint (Finset.range M) (Finset.Ico M N) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      have := Finset.mem_range.mp hm1
      have := (Finset.mem_Ico.mp hm2).1
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hb1 : ‖∑ m ∈ Finset.range M, A m * w ^ (N - m)‖ < ε / 2 := by
      have h1 : ‖∑ m ∈ Finset.range M, A m * w ^ (N - m)‖ ≤
          SA * r ^ (N - M) := by
        calc ‖∑ m ∈ Finset.range M, A m * w ^ (N - m)‖
            ≤ ∑ m ∈ Finset.range M, ‖A m‖ * r ^ (N - m) := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
              rw [norm_mul, norm_pow]
          _ ≤ ∑ m ∈ Finset.range M, ‖A m‖ * r ^ (N - M) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hm_lt : m < M := Finset.mem_range.mp hm
              have hle_exp : N - M ≤ N - m := by omega
              rcases eq_or_lt_of_le hr_nn with hr0 | hr_pos
              · have hNM_pos : 0 < N - m := by omega
                rw [← hr0, zero_pow hNM_pos.ne', mul_zero]
                exact mul_nonneg (norm_nonneg _) (pow_nonneg le_rfl _)
              · exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_of_le_one hr_pos.le hw.le hle_exp) (norm_nonneg _)
          _ = (∑ m ∈ Finset.range M, ‖A m‖) * r ^ (N - M) := (Finset.sum_mul _ _ _).symm
          _ ≤ SA * r ^ (N - M) := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr_nn _)
              dsimp [SA]
              linarith [hA_norm.sum_le_tsum (Finset.range M) fun _ _ => norm_nonneg _]
      have h2 := hK (N - M) (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hSA_pos.le (pow_nonneg hr_nn _))] at h2
      exact lt_of_le_of_lt h1 h2
    have hb2 : ‖∑ m ∈ Finset.Ico M N, A m * w ^ (N - m)‖ < ε / 2 := by
      have h1 : ‖∑ m ∈ Finset.Ico M N, A m * w ^ (N - m)‖ ≤
          ∑ m ∈ Finset.Ico M N, ‖A m‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr_nn hw.le)
      have hunion_sum : (∑ m ∈ Finset.range M, ‖A m‖) + ∑ m ∈ Finset.Ico M N, ‖A m‖ ≤
          ∑' m : ℕ, ‖A m‖ := by
        rw [← Finset.sum_union hdisj, ← hsplit]
        exact hA_norm.sum_le_tsum (Finset.range N) fun _ _ => norm_nonneg _
      linarith
    calc ‖(∑ m ∈ Finset.range M, A m * w ^ (N - m)) +
            ∑ m ∈ Finset.Ico M N, A m * w ^ (N - m)‖
        ≤ ‖∑ m ∈ Finset.range M, A m * w ^ (N - m)‖ +
            ‖∑ m ∈ Finset.Ico M N, A m * w ^ (N - m)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hb1 hb2
      _ = ε := add_halves ε
  have hfn_eq : (fun N : ℕ => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n, A m * w ^ (n - m)) =
      fun N : ℕ => (w / (1 - w)) * (∑ m ∈ Finset.range N, A m) -
        (1 / (1 - w)) * (∑ m ∈ Finset.range N, A m * w ^ (N - m)) := by
    funext N
    apply mul_right_cancel₀ h1w_ne
    rw [sum_range_geometric_tail A w N]
    have hsplit_rhs : (∑ m ∈ Finset.range N, A m * (w - w ^ (N - m))) =
        w * (∑ m ∈ Finset.range N, A m) - ∑ m ∈ Finset.range N, A m * w ^ (N - m) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit_rhs]
    field_simp
  rw [hfn_eq]
  simpa using ((hA_sum.tendsto_sum_nat.const_mul (w / (1 - w))).sub
    (hrem_zero.const_mul (1 / (1 - w))))

/-- **Exact rational identity of `curveBeyondWallBalance`.** For every `h ∈ H_D` (`InFourStrip D`)
and every `z ∈ ℂ` strictly inside all Frobenius moduli (`∀ j : ι, ‖z‖ < ‖D.β j‖`),
`Φ_D(h, z) = ∑_{j ∈ ι} z · L_D h(β_j) / (z - β_j)`. -/
theorem curveBeyondWallBalance_eq_rational (hD : InFourStrip D) {h : ℕ → ℝ}
    (hh : CurveEnergyDomain D h) {z : ℂ} (hz : ∀ j : ι, ‖z‖ < ‖D.β j‖) :
    curveBeyondWallBalance D h z =
      ∑ j : ι, z * curveLaplace h (D.β j) / (z - D.β j) := by
  by_cases hz0 : z = 0
  · subst hz0
    unfold curveBeyondWallBalance curveLevyHead
    have h0 : (fun n : ℕ => (D.trace n : ℂ) * (0 : ℂ) ^ n *
        ∑ m ∈ Finset.range n, (h m : ℂ) * ((0 : ℂ)⁻¹) ^ m) = fun _ => 0 := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [zero_pow hn]
    rw [h0, tsum_zero, neg_zero]
    simp
  · have hsingle : ∀ i : ι,
        HasSum (fun n : ℕ => (D.β i * z) ^ n * curveLevyHead h z n)
          (D.β i * z / (1 - D.β i * z) * curveLaplace h (D.β i)⁻¹) := by
      intro i
      have hβinv : (D.q ^ 4)⁻¹ < ‖(D.β i)⁻¹‖ := by
        rw [norm_inv, ← D.norm_β_fePerm i]
        exact inv_q_four_lt_norm_β D hD (D.fePerm i)
      have hA_sum : HasSum (fun m : ℕ => (h m : ℂ) * D.β i ^ m) (curveLaplace h (D.β i)⁻¹) := by
        simpa [curveLaplace, inv_inv] using (summable_curveLaplace D hh hβinv).hasSum
      have hA_norm : Summable fun m : ℕ => ‖(h m : ℂ) * D.β i ^ m‖ := by
        simpa [inv_inv] using summable_norm_curveLaplace D hh hβinv
      have hw_lt : ‖D.β i * z‖ < 1 := by
        rw [norm_mul, ← inv_inv ‖D.β i‖, ← D.norm_β_fePerm i]
        have hpos : 0 < ‖D.β (D.fePerm i)‖ := norm_pos_iff.mpr (D.β_ne_zero _)
        rw [inv_mul_lt_iff₀ hpos, mul_one]
        exact hz (D.fePerm i)
      refine (hasSum_frob_levyHead_single hA_sum hA_norm hw_lt).congr_fun fun n => ?_
      unfold curveLevyHead
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_le : m ≤ n := (Finset.mem_range.mp hm).le
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm_le
      rw [Nat.add_sub_cancel_left, pow_add (D.β i * z) m k, mul_pow (D.β i) z m]
      have hz_inv : z ^ m * (z⁻¹) ^ m = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
      symm
      calc (h m : ℂ) * D.β i ^ m * (D.β i * z) ^ k
          = D.β i ^ m * (z ^ m * (z⁻¹) ^ m) * (D.β i * z) ^ k * (h m : ℂ) := by
              rw [hz_inv]; ring
        _ = D.β i ^ m * z ^ m * (D.β i * z) ^ k * ((h m : ℂ) * (z⁻¹) ^ m) := by ring
    have hsum_all := hasSum_sum fun i (_ : i ∈ Finset.univ) => hsingle i
    have hterm_eq : (fun n : ℕ => (D.trace n : ℂ) * z ^ n * curveLevyHead h z n) =
        fun n : ℕ => ∑ i : ι, (D.β i * z) ^ n * curveLevyHead h z n := by
      funext n
      rw [← D.powerSum_eq_trace, CurveDatum.powerSum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow]
    unfold curveBeyondWallBalance
    rw [hterm_eq, hsum_all.tsum_eq, ← Finset.sum_neg_distrib,
      ← Equiv.sum_comp D.fePerm (fun j => z * curveLaplace h (D.β j) / (z - D.β j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfe1 : D.β (D.fePerm i) = (D.β i)⁻¹ := eq_inv_of_mul_eq_one_left (D.β_fePerm i)
    rw [hfe1]
    have hβ0 : D.β i ≠ 0 := D.β_ne_zero i
    have hden1 : 1 - D.β i * z ≠ 0 := by
      intro h0
      have hw : D.β i * z = 1 := by linear_combination -h0
      have hnorm : ‖D.β i * z‖ = 1 := by rw [hw, norm_one]
      have hlt : ‖D.β i * z‖ < 1 := by
        rw [norm_mul, ← inv_inv ‖D.β i‖, ← D.norm_β_fePerm i]
        exact (inv_mul_lt_iff₀ (norm_pos_iff.mpr (D.β_ne_zero _))).mpr (by simpa using hz (D.fePerm i))
      linarith
    have hden2 : z - (D.β i)⁻¹ ≠ 0 := by
      intro h0
      apply hden1
      have hz_eq : z = (D.β i)⁻¹ := by linear_combination h0
      rw [hz_eq, mul_inv_cancel₀ hβ0, sub_self]
    rw [div_mul_eq_mul_div, ← neg_div, div_eq_div_iff hden1 hden2]
    calc -(D.β i * z * curveLaplace h (D.β i)⁻¹) * (z - (D.β i)⁻¹)
        = z * curveLaplace h (D.β i)⁻¹ * (1 - D.β i * z) -
            (1 - D.β i * (D.β i)⁻¹) * z * curveLaplace h (D.β i)⁻¹ := by ring
      _ = z * curveLaplace h (D.β i)⁻¹ * (1 - D.β i * z) := by
          rw [mul_inv_cancel₀ hβ0, sub_self, zero_mul, zero_mul, sub_zero]

/-- **Seen-inner-root pole obstruction (`curveCriticalState_not_beyondWallContinuation`).**
No curve critical state `f` on `D` (`InFourStrip D`) admits holomorphic continuation of
`curveBeyondWallBalance D f` from a neighborhood of `0` across the unit disc `{|z| < 1}`. -/
theorem curveCriticalState_not_beyondWallContinuation (hD : InFourStrip D) {a : ℝ} {f : ℕ → ℝ}
    (hf : IsCurveCriticalState D a f) :
    ¬ ∃ (r₀ : ℝ) (H : ℂ → ℂ), 0 < r₀ ∧
      DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      Set.EqOn H (curveBeyondWallBalance D f) (Metric.ball 0 r₀) := by
  classical
  rintro ⟨r₀, H, hr₀, hH_diff, hH_eq⟩
  obtain ⟨i₀, -, hlt_inner, -, -, hseen_inner⟩ := curveCriticalState_sees_outer_and_inner_root D hf
  set z_star : ℂ := D.β (D.fePerm i₀)
  have hz_star_ball : z_star ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right, z_star] using hlt_inner
  have hz_star_spec : z_star ∈ D.spectrum :=
    Finset.mem_image_of_mem _ (Finset.mem_univ (D.fePerm i₀))
  have hz_star_ne : z_star ≠ 0 := D.β_ne_zero (D.fePerm i₀)
  -- Clear denominators with `Q(z) = ∏_{w ∈ D.spectrum} (z - w)`.
  let Q (z : ℂ) : ℂ := ∏ w ∈ D.spectrum, (z - w)
  let Q_erase (w z : ℂ) : ℂ := ∏ u ∈ D.spectrum.erase w, (z - u)
  let R_poly (z : ℂ) : ℂ := ∑ j : ι, z * curveLaplace f (D.β j) * Q_erase (D.β j) z
  have hQ_diff : Differentiable ℂ Q := by
    intro z
    unfold Q
    fun_prop
  have hR_diff : Differentiable ℂ R_poly := by
    intro z
    unfold R_poly Q_erase
    fun_prop
  -- Choose `r₁ > 0` inside `min r₀ 1` and strictly below all `‖D.β j‖`.
  have hmin_β : ∃ b : ℝ, 0 < b ∧ ∀ j : ι, b ≤ ‖D.β j‖ := by
    refine ⟨(D.q ^ 4)⁻¹, inv_pos.mpr (q_pow_pos D 4), fun j => (inv_q_four_lt_norm_β D hD j).le⟩
  obtain ⟨b_min, hb_pos, hb_le⟩ := hmin_β
  set r₁ : ℝ := min (min r₀ 1) b_min
  have hr₁_pos : 0 < r₁ := lt_min (lt_min hr₀ one_pos) hb_pos
  have hr₁_le_one : r₁ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁_le_r₀ : r₁ ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hagree_ball : Set.EqOn (fun z => Q z * H z - R_poly z) 0 (Metric.ball 0 r₁) := by
    intro z hz
    have hz_norm : ‖z‖ < r₁ := by simpa [mem_ball, dist_zero_right] using hz
    have hz_r₀ : z ∈ Metric.ball (0 : ℂ) r₀ := by
      rw [mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz_norm hr₁_le_r₀
    have hz_β : ∀ j : ι, ‖z‖ < ‖D.β j‖ := fun j =>
      lt_of_lt_of_le (lt_of_lt_of_le hz_norm (min_le_right _ _)) (hb_le j)
    dsimp only
    rw [hH_eq hz_r₀, curveBeyondWallBalance_eq_rational D hD hf.2.1 hz_β, Finset.mul_sum]
    have hterms : (∑ j : ι, Q z * (z * curveLaplace f (D.β j) / (z - D.β j))) = R_poly z := by
      unfold R_poly
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj_spec : D.β j ∈ D.spectrum := Finset.mem_image_of_mem _ (Finset.mem_univ j)
      have hQ_fac : Q z = (z - D.β j) * Q_erase (D.β j) z :=
        (Finset.mul_prod_erase D.spectrum (fun u => z - u) hj_spec).symm
      have hne_j : z - D.β j ≠ 0 := by
        intro h0
        have heq : z = D.β j := by linear_combination h0
        have := hz_β j
        rw [heq] at this
        exact lt_irrefl _ this
      rw [hQ_fac]
      field_simp
    simp [hterms]
  have hdiff_comb : DifferentiableOn ℂ (fun z => Q z * H z - R_poly z) (Metric.ball 0 1) :=
    (hQ_diff.differentiableOn.mul hH_diff).sub hR_diff.differentiableOn
  have han_comb : AnalyticOnNhd ℂ (fun z => Q z * H z - R_poly z) (Metric.ball 0 1) :=
    hdiff_comb.analyticOnNhd isOpen_ball
  have hzero_on_disc : Set.EqOn (fun z => Q z * H z - R_poly z) 0 (Metric.ball 0 1) :=
    han_comb.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected
      (mem_ball_self one_pos)
      (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr₁_pos))
        fun z hz => hagree_ball hz)
  have hval_star := hzero_on_disc hz_star_ball
  have hQ_star : Q z_star = 0 :=
    Finset.prod_eq_zero hz_star_spec (sub_self z_star)
  have hR_star : R_poly z_star ≠ 0 := by
    unfold R_poly
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : ι => D.β j = z_star)]
    have hother : ∑ j ∈ Finset.univ.filter (fun j : ι => ¬ D.β j = z_star),
        z_star * curveLaplace f (D.β j) * Q_erase (D.β j) z_star = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : D.β j ≠ z_star := (Finset.mem_filter.mp hj).2
      have hmem_er : z_star ∈ D.spectrum.erase (D.β j) :=
        Finset.mem_erase.mpr ⟨hne.symm, hz_star_spec⟩
      have hQe0 : Q_erase (D.β j) z_star = 0 :=
        Finset.prod_eq_zero hmem_er (sub_self z_star)
      rw [hQe0, mul_zero]
    rw [hother, add_zero]
    have hsame : ∑ j ∈ Finset.univ.filter (fun j : ι => D.β j = z_star),
        z_star * curveLaplace f (D.β j) * Q_erase (D.β j) z_star =
        ((Finset.univ.filter (fun j : ι => D.β j = z_star)).card : ℂ) *
          (z_star * curveLaplace f z_star * Q_erase z_star z_star) := by
      calc ∑ j ∈ Finset.univ.filter (fun j : ι => D.β j = z_star),
            z_star * curveLaplace f (D.β j) * Q_erase (D.β j) z_star
          = ∑ _j ∈ Finset.univ.filter (fun j : ι => D.β j = z_star),
              z_star * curveLaplace f z_star * Q_erase z_star z_star := by
                refine Finset.sum_congr rfl fun j hj => ?_
                rw [(Finset.mem_filter.mp hj).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsame]
    have hcard_pos : 0 < (Finset.univ.filter (fun j : ι => D.β j = z_star)).card :=
      Finset.card_pos.mpr ⟨D.fePerm i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hcard_ne : ((Finset.univ.filter (fun j : ι => D.β j = z_star)).card : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcard_pos.ne'
    have hQe_ne : Q_erase z_star z_star ≠ 0 := by
      unfold Q_erase
      refine Finset.prod_ne_zero_iff.mpr fun u hu => ?_
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hu).symm
    exact mul_ne_zero hcard_ne
      (mul_ne_zero (mul_ne_zero hz_star_ne hseen_inner) hQe_ne)
  dsimp at hval_star
  rw [hQ_star, zero_mul, zero_sub, neg_eq_zero] at hval_star
  exact hR_star hval_star

/-- `CurveBeyondTheWallPrimeContinuation` excludes every curve critical state. -/
theorem not_isCurveCriticalState_of_beyondWallContinuation (hD : InFourStrip D)
    (hcont : CurveBeyondTheWallPrimeContinuation D) (a : ℝ) (f : ℕ → ℝ) :
    ¬ IsCurveCriticalState D a f := fun hf =>
  curveCriticalState_not_beyondWallContinuation D hD hf (hcont f hf.2.1)

/-! ### 4. Exact ECS identities violated by `curve_hodgeIndex_tfae` vs. `riemannHypothesis_cubicCharacter` -/

/-- **Which ECS identity Castelnuovo–Severi (`curve_hodgeIndex_tfae`) violates:**
Either Hodge-index condition in `curve_hodgeIndex_tfae` — Frobenius-window Hodge index
`hermNegIndex (D.spanGram (#ι)) = 0` or scaling-surface Weil positivity on smooth compactly
supported tests — forces `0 ≤ curveBareForm D h h` across the entire confined energy domain `H_D`,
directly violating the critical state's negative bare-energy / negative zero-norm identity
`curveBareForm D f f = -a W₈(f) < 0`. -/
theorem hodgeIndex_violates_negative_bareForm (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) :
    ((hermNegIndex (D.spanGram (Fintype.card ι)) = 0 ∨
        ∀ (n : ℕ) (φ : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (φ i)) →
          (∀ i, HasCompactSupport (φ i)) → hermNegIndex (zeroGram (D.curveConfig hD) φ) = 0) →
      (∀ h : ℕ → ℝ, 0 ≤ curveBareForm D h h) ∧
        ∀ (a : ℝ) (f : ℕ → ℝ), ¬ IsCurveCriticalState D a f) ∧
    (∀ (a : ℝ) (f : ℕ → ℝ), IsCurveCriticalState D a f →
      curveBareForm D f f = -a * curveConfinementMass D f ∧ curveBareForm D f f < 0) := by
  refine ⟨fun hHodge => ?_, fun a f hf => ?_⟩
  · have hU : ∀ i, ‖D.β i‖ = 1 := by
      rcases hHodge with hspan | hsurf
      · exact ((D.curve_hodgeIndex_tfae hD).out 1 0).mp hspan
      · exact ((D.curve_hodgeIndex_tfae hD).out 2 0).mp hsurf
    refine ⟨fun h => ?_, fun a f => not_isCurveCriticalState_of_unitary D hU a f⟩
    rw [curveBareForm_eq_sum_norm_sq_of_unitary D hU h]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · obtain ⟨ha, hdom, hne, hweak⟩ := hf
    have hself := hweak f hdom
    have hW : 0 < curveConfinementMass D f :=
      lt_of_le_of_ne (curveConfinementMass_nonneg D f)
        (Ne.symm ((curveConfinementMass_eq_zero_iff D hdom).not.mpr hne))
    have hB : curveBareForm D f f = -a * curveConfinementMass D f := by
      unfold curveConfinementMass; linarith
    exact ⟨hB, by nlinarith⟩

end GeneralDatum

/-! ### Explicit golden fake curve ground state and collar blindness (`q = 5`) -/

open Real in
/-- **Golden fake curve (`q = 5`, `β = (φ, φ⁻¹)`):**
1. Admits a unit confined half-line critical ground state `f*` at `a* > 0`, which sees both `φ > 1`
   and `φ⁻¹ < 1` and fails `CurveBeyondTheWallPrimeContinuation`;
2. Every non-wall discrete half-line site `u_m = -m log 5` (`m ≥ 1`) lies strictly left of the open
   collar `(-log 2, 0)` (`-m log 5 < -log 2`), witnessing T5 for `E-Q4`: smooth tests supported in
   `(-log 2, 0)` vanish identically on every half-line site `u_m` (`m ≥ 0`) of `goldenDatum`. -/
theorem goldenDatum_exists_criticalState_and_collar_blind :
    (∃ (a : ℝ) (f : ℕ → ℝ),
      curveConfinementMass goldenDatum f = 1 ∧
      IsCurveCriticalState goldenDatum a f ∧
      ¬ CurveBeyondTheWallPrimeContinuation goldenDatum) ∧
    ∀ m : ℕ, ∀ G : ℝ → ℝ,
      (∀ u, 0 ≤ u → G u = 0) → (∀ u, u ≤ -Real.log 2 → G u = 0) →
        G (-(m : ℝ) * Real.log goldenDatum.q) = 0 := by
  have hfour : InFourStrip goldenDatum := inFourStrip_of_strip goldenDatum goldenDatum_strip
  obtain ⟨a, f, hmass, hcrit, -⟩ :=
    exists_curveGroundState_of_not_unitary goldenDatum hfour goldenDatum_not_unitary
  refine ⟨⟨a, f, hmass, hcrit, fun hcont =>
    not_isCurveCriticalState_of_beyondWallContinuation goldenDatum hfour hcont a f hcrit⟩, ?_⟩
  intro m G hG0 hG2
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hG0 0 le_rfl]
  · apply hG2
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hlog : Real.log 2 < Real.log goldenDatum.q := by
      change Real.log 2 < Real.log 5
      exact Real.log_lt_log (by norm_num) (by norm_num)
    have hlog_pos : 0 < Real.log goldenDatum.q := goldenDatum.log_q_pos
    nlinarith

/-! ### Native Stepanov (`riemannHypothesis_cubicCharacter`): Stage-5 beyond-the-wall continuation -/

section CubicStepanov

variable {F : Type*} [Field F] [Fintype F]

/-- **First half of native Stepanov in ECS coordinates:**
Before invoking the Gauss-sum determinant, Stepanov's even-degree character-sum bound
(`norm_rootEnumC_le`) forces every normalized reciprocal root `ω / √|F|` (`ω ∈ lRootsC χ f`) to lie
in `{|z| ≤ 1}`, directly excluding any outer root `|ω / √|F|| > 1`. -/
theorem cubicStepanov_even_bound_excludes_outer_root {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (hχ3 : χ ^ 3 = 1) {NF : ℕ} (hqF : Fintype.card F = 3 * NF + 1) {P : F[X]}
    (hsq : Squarefree P) (hsplit : P.Splits) (hm : 0 < P.natDegree) :
    ∀ ω ∈ lRootsC χ P, ‖ω / (Real.sqrt (Fintype.card F) : ℂ)‖ ≤ 1 := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  intro ω hω
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Multiset.mem_toList.mpr hω)
  have hle := norm_rootEnumC_le (p := ringChar F) hχ hχ3 hqF hsq hsplit hm i
  have hiu : rootEnum (lRootsC χ P) i = ω := hi
  rw [hiu] at hle
  have hsq_pos : 0 < Real.sqrt (Fintype.card F) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsq_pos.le]
  exact (div_le_one hsq_pos).mpr hle

/-- The self-dual Kummer `CurveDatum` attached to a cubic character `χ` (`χ ≠ 1`, `χ³ = 1`) on `F`
(`|F| = 3 N_F + 1`) and a squarefree split polynomial `P ∈ F[X]` (`deg P > 0`, `χ^{deg P} ≠ 1`),
pairing the normalized reciprocal roots `ω_i / √|F|` (`ω_i ∈ lRootsC χ P`) with their conjugates. -/
def cubicKummerDatum {χ : MulChar F ℂ} (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1) {NF : ℕ}
    (hqF : Fintype.card F = 3 * NF + 1) {P : F[X]} (hsq : Squarefree P) (hsplit : P.Splits)
    (hm : 0 < P.natDegree) (hχm : χ ^ P.natDegree ≠ 1) :
    CurveDatum (Fin (lRootsC χ P).toList.length ⊕ Fin (lRootsC χ P).toList.length) where
  q := Fintype.card F
  one_lt_q := by exact_mod_cast Fintype.one_lt_card
  β
    | Sum.inl i => rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ)
    | Sum.inr i => conj (rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ))
  conjPerm := Equiv.sumComm _ _
  β_conjPerm x := by
    cases x with
    | inl i => rfl
    | inr i => exact (Complex.conj_conj _).symm
  fePerm := Equiv.sumComm _ _
  β_fePerm x := by
    have hrh := (riemannHypothesis_cubicCharacter.{_, 0} hχ hχ3 hqF hsq hsplit hm hχm).2.1
    have hsq_pos : 0 < Real.sqrt (Fintype.card F) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    have hnorm1 : ∀ i : Fin (lRootsC χ P).toList.length,
        ‖rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ)‖ = 1 := by
      intro i
      have hmem : rootEnum (lRootsC χ P) i ∈ lRootsC χ P :=
        Multiset.mem_toList.mp (List.get_mem _ _)
      rw [norm_div, hrh _ hmem, Complex.norm_real, Real.norm_of_nonneg hsq_pos.le,
        div_self hsq_pos.ne']
    cases x with
    | inl i =>
      simp only [Equiv.sumComm_apply, Sum.swap_inl]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm1 i]; norm_num
    | inr i =>
      simp only [Equiv.sumComm_apply, Sum.swap_inr]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm1 i]; norm_num

/-- For any `CurveDatum D` (`InFourStrip D`) whose trace is uniformly bounded (`|D.trace n| ≤ C`
for all `n ≥ 1`), the beyond-the-wall prime-head series `Φ_D(h, z)` converges absolutely and
holomorphically throughout the entire unit disc `{|z| < 1}` for every `h ∈ H_D`. -/
theorem curveBeyondWallContinuation_of_trace_bounded {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hD : InFourStrip D) {C : ℝ} (hC : ∀ n : ℕ, 1 ≤ n → |D.trace n| ≤ C) :
    CurveBeyondTheWallPrimeContinuation D := by
  intro h hh
  have hβ_ge_one : ∀ j : ι, 1 ≤ ‖D.β j‖ := by
    have hβ_le_one : ∀ j : ι, ‖D.β j‖ ≤ 1 := by
      have hbound : ∀ k : ℕ, 1 ≤ k →
          ‖∑ j ∈ Finset.univ, D.β j ^ k‖ ≤ max C 0 * (1 : ℝ) ^ k := by
        intro k hk
        rw [one_pow, mul_one]
        calc ‖∑ j ∈ Finset.univ, D.β j ^ k‖
            = ‖D.powerSum k‖ := rfl
          _ = |D.trace k| := by rw [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ C := hC k hk
          _ ≤ max C 0 := le_max_left _ _
      intro j
      exact norm_le_of_power_sums_bound Finset.univ D.β
        (C := max C 0) (ρ := 1) (m0 := 1) zero_le_one hbound j (Finset.mem_univ j)
    intro j
    have hfe := hβ_le_one (D.fePerm j)
    rw [D.norm_β_fePerm] at hfe
    exact (inv_le_one₀ (norm_pos_iff.mpr (D.β_ne_zero j))).mp hfe
  refine ⟨1, fun z => ∑ j : ι, z * curveLaplace h (D.β j) / (z - D.β j), one_pos, ?_, ?_⟩
  · intro z hz
    classical
    have hz_lt : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    have hdiff_sum : ∀ S : Finset ι,
        DifferentiableAt ℂ (fun w => ∑ j ∈ S, w * curveLaplace h (D.β j) / (w - D.β j)) z := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert j T hj ih =>
        have hne : z - D.β j ≠ 0 := by
          intro h0
          have heq : z = D.β j := by linear_combination h0
          have h1 := hβ_ge_one j
          rw [← heq] at h1
          linarith
        have hj_diff : DifferentiableAt ℂ
            (fun w => w * curveLaplace h (D.β j) / (w - D.β j)) z :=
          ((differentiableAt_id.mul (differentiableAt_const _)).div
            (differentiableAt_id.sub (differentiableAt_const _)) hne)
        have hfn : (fun w => ∑ i ∈ insert j T, w * curveLaplace h (D.β i) / (w - D.β i)) =
            ((fun w => w * curveLaplace h (D.β j) / (w - D.β j)) +
              fun w => ∑ i ∈ T, w * curveLaplace h (D.β i) / (w - D.β i)) := by
          funext w
          simp [Finset.sum_insert hj]
        rw [hfn]
        exact hj_diff.add ih
    exact (hdiff_sum Finset.univ).differentiableWithinAt
  · intro z hz
    have hz_lt : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    exact (curveBeyondWallBalance_eq_rational D hD hh fun j =>
      lt_of_lt_of_le hz_lt (hβ_ge_one j)).symm

/-- **Which ECS identity native Stepanov (`riemannHypothesis_cubicCharacter`) violates:**
For the cubic Kummer datum `D = cubicKummerDatum`, Stepanov's character-sum identity and square-root
bound give:
1. `D.trace n = -2 Re(extChar χ (E := E) P) / (√|F|)^n` for every degree-`n` extension `E / F`, with
   uniform square-root bound `|D.trace n| ≤ 2 (deg P - 1)` for all `n ≥ 1`;
2. **Stage-5 beyond-the-wall prime continuation** (`CurveBeyondTheWallPrimeContinuation D`): the
   prime-head series `curveBeyondWallBalance D h` converges holomorphically on the entire unit disc
   `{|z| < 1}` for every `h ∈ H_D` (violating `curveCriticalState_not_beyondWallContinuation`);
3. Complete exclusion of any curve critical state (`∀ a f, ¬ IsCurveCriticalState D a f`). -/
theorem cubicKummerDatum_beyondWallContinuation_and_no_criticalState
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1) {NF : ℕ}
    (hqF : Fintype.card F = 3 * NF + 1) {P : F[X]} (hsq : Squarefree P) (hsplit : P.Splits)
    (hm : 0 < P.natDegree) (hχm : χ ^ P.natDegree ≠ 1) :
    let D := cubicKummerDatum hχ hχ3 hqF hsq hsplit hm hχm
    (∀ (E : Type*) [Field E] [Fintype E] [Algebra F E],
      D.trace (Module.finrank F E) =
        -2 * (extChar χ (E := E) P).re /
          Real.sqrt (Fintype.card F) ^ Module.finrank F E) ∧
    (∀ n : ℕ, 1 ≤ n → |D.trace n| ≤ 2 * (P.natDegree - 1 : ℕ)) ∧
    CurveBeyondTheWallPrimeContinuation D ∧
    ∀ (a : ℝ) (f : ℕ → ℝ), ¬ IsCurveCriticalState D a f := by
  intro D
  obtain ⟨hcard, hnorm, hext⟩ := riemannHypothesis_cubicCharacter hχ hχ3 hqF hsq hsplit hm hχm
  have hsq_pos : 0 < Real.sqrt (Fintype.card F) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hU : ∀ x, ‖D.β x‖ = 1 := by
    intro x
    cases x with
    | inl i =>
      dsimp [D, cubicKummerDatum]
      have hmem : rootEnum (lRootsC χ P) i ∈ lRootsC χ P :=
        Multiset.mem_toList.mp (List.get_mem _ _)
      rw [norm_div, hnorm _ hmem, Complex.norm_real, Real.norm_of_nonneg hsq_pos.le,
        div_self hsq_pos.ne']
    | inr i =>
      dsimp [D, cubicKummerDatum]
      have hmem : rootEnum (lRootsC χ P) i ∈ lRootsC χ P :=
        Multiset.mem_toList.mp (List.get_mem _ _)
      rw [Complex.norm_conj, norm_div, hnorm _ hmem, Complex.norm_real,
        Real.norm_of_nonneg hsq_pos.le, div_self hsq_pos.ne']
  have hstrip : ∀ x, ‖D.β x‖ ≤ D.sqrtq := by
    intro x
    rw [hU x]
    have hq1 : 1 < D.q := D.one_lt_q
    have hsq_q : D.sqrtq ^ 2 = D.q := D.sqrtq_sq
    nlinarith [D.sqrtq_pos]
  have hfour : InFourStrip D := inFourStrip_of_strip D hstrip
  have htrace_bound : ∀ n : ℕ, 1 ≤ n → |D.trace n| ≤ 2 * (P.natDegree - 1 : ℕ) := by
    intro n _hn
    have hcard_fin : Fintype.card (Fin (lRootsC χ P).toList.length ⊕
        Fin (lRootsC χ P).toList.length) = 2 * (P.natDegree - 1) := by
      rw [Fintype.card_sum, Fintype.card_fin, Multiset.length_toList, hcard, two_mul]
    calc |D.trace n|
        = ‖D.powerSum n‖ := by rw [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ x, ‖D.β x ^ n‖ := norm_sum_le _ _
      _ = ∑ _x, (1 : ℝ) := Finset.sum_congr rfl fun x _ => by rw [norm_pow, hU x, one_pow]
      _ = 2 * (P.natDegree - 1 : ℕ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, hcard_fin]
          push_cast; ring
  have hcont : CurveBeyondTheWallPrimeContinuation D :=
    curveBeyondWallContinuation_of_trace_bounded D hfour htrace_bound
  refine ⟨fun E _ _ _ => ?_, htrace_bound, hcont,
    fun a f => not_isCurveCriticalState_of_beyondWallContinuation D hfour hcont a f⟩
  set n := Module.finrank F E
  have hsum_ω : ∑ i : Fin (lRootsC χ P).toList.length, rootEnum (lRootsC χ P) i ^ n =
      -extChar χ (E := E) P := by
    rw [hext E, neg_neg, Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← univ_map_rootEnum (lRootsC χ P)]
    rw [Multiset.map_map]
    rfl
  unfold CurveDatum.trace CurveDatum.powerSum
  rw [Fintype.sum_sum_type]
  have hl : (∑ i : Fin (lRootsC χ P).toList.length, D.β (Sum.inl i) ^ n) =
      (∑ i, rootEnum (lRootsC χ P) i ^ n) / ((Real.sqrt (Fintype.card F) ^ n : ℝ) : ℂ) := by
    dsimp [D, cubicKummerDatum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, Complex.ofReal_pow]
  have hr : (∑ i : Fin (lRootsC χ P).toList.length, D.β (Sum.inr i) ^ n) =
      conj ((∑ i, rootEnum (lRootsC χ P) i ^ n) / ((Real.sqrt (Fintype.card F) ^ n : ℝ) : ℂ)) := by
    dsimp [D, cubicKummerDatum]
    have hterm : ∀ i : Fin (lRootsC χ P).toList.length,
        conj (rootEnum (lRootsC χ P) i / (Real.sqrt (Fintype.card F) : ℂ)) ^ n =
          conj (rootEnum (lRootsC χ P) i ^ n) / ((Real.sqrt (Fintype.card F) ^ n : ℝ) : ℂ) := by
      intro i
      rw [map_div₀, Complex.conj_ofReal, div_pow, map_pow, Complex.ofReal_pow]
    simp_rw [hterm]
    rw [← Finset.sum_div, map_div₀, map_sum, Complex.conj_ofReal]
  rw [hl, hr, hsum_ω]
  set S := extChar χ (E := E) P
  set Rpow : ℝ := Real.sqrt (Fintype.card F) ^ n
  rw [map_div₀, map_neg, Complex.conj_ofReal, ← add_div, div_eq_mul_inv,
    ← Complex.ofReal_inv, mul_comm _ ((Rpow⁻¹ : ℝ) : ℂ), Complex.re_ofReal_mul]
  simp [div_eq_mul_inv]
  ring

end CubicStepanov

#print axioms exists_curveGroundState_of_not_unitary
#print axioms curveCriticalState_iff_not_unitary
#print axioms curveCriticalState_eq_sum
#print axioms curveCriticalState_laplace_eq_rational
#print axioms curveCriticalState_star_identity
#print axioms curveCriticalState_zeroParseval
#print axioms curveCriticalState_sees_outer_and_inner_root
#print axioms curveBeyondWallBalance_eq_rational
#print axioms curveCriticalState_not_beyondWallContinuation
#print axioms hodgeIndex_violates_negative_bareForm
#print axioms goldenDatum_exists_criticalState_and_collar_blind
#print axioms cubicStepanov_even_bound_excludes_outer_root
#print axioms cubicKummerDatum_beyondWallContinuation_and_no_criticalState

end CurveModels

end GaloisForLFunctions.ExclusionOfTheCriticalState


