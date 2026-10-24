import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverOfACurveIsAdmittedAboveTheZeroWidth
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The curve receiver is admitted exactly on zero chains

`TheReceiverOfACurveIsAdmittedAboveTheZeroWidth` admits the receiver of a curve model at every
damping above the zero width, and refutes admission below it at an eigenvalue no other eigenvalue
shadows. Here the admission set is determined for every eigenvalue configuration, shadowed ones and
multiplicities included. Write `S` for the eigenvalue
multiset and `ρ₀ = q^{−ε}`. Then (`curveReceiver_admits_iff`)

  the receiver is admitted at `ε`  ⟺  every `a` with `‖a‖ ≥ √q q^ε` satisfies
  `mult_S(a) ≤ mult_S(ρ₀a) + [a = q]`.

An eigenvalue `a` is a zero `ρ` of `ζ_C` with `q^ρ = a`, and `ρ₀a` is the zero `ρ − ε`. The
receiver reads `ζ_C(s)/ζ_C(s + ε)`: a pole of `1/ζ_C(s + ε)` right of the critical line is harmless
exactly when a zero of `ζ_C(s)` of at least its order cancels it, the eigenvalue `q` borrowing one
order from the pole of `ζ_C`. This is the curve form of the number-field law that an admitted
damping translates the zeros right of the line with multiplicity
(`ArithmeticContinuationAndCriticalEnergy.analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings`),
here as an equivalence. Consequences:

* `curveReceiver_admits_chainPair`: the two eigenvalues `a`, `q^{−ε}a` with
  `√q q^ε ≤ ‖a‖ < √q q^{2ε}` are admitted at `ε`, which lies below their zero width: a single
  admitted damping does not bound the width.

Necessity is algebraic. The source series `G` satisfies `G·A = N` for explicit polynomials
(`curveCentredSeries_mul_eq`); a root `1/β`, `|β|² ≥ q`, of higher order in `A` than in `N` survives as
`G·A₁ = N₁/(1 − βu)` with `N₁(1/β) ≠ 0`. The left side keeps the weighted `ℓ²` bound of the
energy (`weightedEnergy_mul_coe_le`), the right side has coefficients `βⁿN₁(1/β)`
(`coeff_coe_mul_geomSeries`). Sufficiency cancels every bad pole of `P·R` by a multiset matching
(`curveP_mul_curveDampedZinv_eq_of_chain`) and reruns the centring tail estimate with the surviving
growth `τ < √q`.
-/

open PowerSeries Finset Filter Topology
open scoped Classical

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

variable {m : ℕ}

/-! ## Linear factors as polynomials -/

/-- The linear polynomial `1 − cu`. -/
def linPoly (c : ℂ) : Polynomial ℂ := 1 - Polynomial.C c * Polynomial.X

theorem coe_linPoly (c : ℂ) : ((linPoly c : Polynomial ℂ) : PowerSeries ℂ) = 1 - C c * X := by
  simp only [linPoly, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X]

theorem eval_linPoly (c x : ℂ) : (linPoly c).eval x = 1 - c * x := by
  simp [linPoly]

theorem coe_linPoly_ne_zero (c : ℂ) : ((linPoly c : Polynomial ℂ) : PowerSeries ℂ) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  simp [coe_linPoly] at this

/-- The coercion of a multiset product of polynomials. -/
theorem coe_multiset_prod_map {ι : Type*} (M : Multiset ι) (f : ι → Polynomial ℂ) :
    (((M.map f).prod : Polynomial ℂ) : PowerSeries ℂ) =
      (M.map fun i => ((f i : Polynomial ℂ) : PowerSeries ℂ)).prod := by
  have h := map_multiset_prod (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) (M.map f)
  simpa [Multiset.map_map, Polynomial.coeToPowerSeries.ringHom_apply] using h

/-- A polynomial is the finite sum of its monomials, as a power series. -/
theorem coe_eq_sum_monomials (W : Polynomial ℂ) :
    ((W : Polynomial ℂ) : PowerSeries ℂ) =
      ∑ j ∈ range (W.natDegree + 1), C (W.coeff j) * X ^ j := by
  ext n
  rw [Polynomial.coeff_coe, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at h; omega)

/-- Coefficients of a series times a polynomial. -/
theorem coeff_mul_coe (G : PowerSeries ℂ) (W : Polynomial ℂ) (n : ℕ) :
    coeff n (G * (W : PowerSeries ℂ)) =
      ∑ j ∈ range (W.natDegree + 1), W.coeff j * (if j ≤ n then coeff (n - j) G else 0) := by
  rw [coe_eq_sum_monomials, mul_sum, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [show G * (C (W.coeff j) * X ^ j) = C (W.coeff j) * (X ^ j * G) by ring, coeff_C_mul,
    coeff_X_pow_mul']

/-- Beyond its degree a polynomial divided by `1 − βu` has coefficients `βⁿ N(1/β)`. -/
theorem coeff_coe_mul_geomSeries (N : Polynomial ℂ) {β : ℂ} (hβ : β ≠ 0) {n : ℕ}
    (hn : N.natDegree ≤ n) :
    coeff n ((N : PowerSeries ℂ) * geomSeries β) = β ^ n * N.eval β⁻¹ := by
  rw [mul_comm, coeff_mul_coe, Polynomial.eval_eq_sum_range, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  rw [if_pos hjn]
  simp only [geomSeries, coeff_mk]
  rw [pow_sub₀ β hβ hjn, inv_pow]
  ring

/-! ## Weighted energies -/

/-- A shifted partial sum of a nonnegative sequence is at most the unshifted one. -/
theorem sum_range_ite_shift_le (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (j D : ℕ) :
    ∑ n ∈ range (D + 1), (if j ≤ n then e (n - j) else 0) ≤ ∑ k ∈ range (D + 1), e k := by
  rcases le_or_gt j (D + 1) with hj | hj
  · rw [← sum_range_add_sum_Ico _ hj]
    have h0 : ∑ n ∈ range j, (if j ≤ n then e (n - j) else 0) = 0 :=
      sum_eq_zero fun n hn => if_neg (by have := mem_range.mp hn; omega)
    rw [h0, zero_add, sum_Ico_eq_sum_range]
    have h1 : ∑ k ∈ range (D + 1 - j), (if j ≤ j + k then e (j + k - j) else 0) =
        ∑ k ∈ range (D + 1 - j), e k :=
      sum_congr rfl fun k _ => by rw [if_pos (by omega), Nat.add_sub_cancel_left]
    rw [h1]
    exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun k _ _ => he k
  · have h0 : ∑ n ∈ range (D + 1), (if j ≤ n then e (n - j) else 0) = 0 :=
      sum_eq_zero fun n hn => if_neg (by have := mem_range.mp hn; omega)
    rw [h0]
    exact sum_nonneg fun k _ => he k

/-- **Multiplying by a polynomial keeps a weighted energy bounded.** If the partial sums of
`‖gₙ‖²/qⁿ` are at most `B`, those of `G·W` are at most `(Σⱼ‖Wⱼ‖²)(deg W + 1)B`. -/
theorem weightedEnergy_mul_coe_le {q : ℕ} (hq : 1 ≤ q) {G : PowerSeries ℂ} {B : ℝ}
    (hB : ∀ D, ∑ n ∈ range (D + 1), ‖coeff n G‖ ^ 2 / (q : ℝ) ^ n ≤ B) (W : Polynomial ℂ) (D : ℕ) :
    ∑ n ∈ range (D + 1), ‖coeff n (G * (W : PowerSeries ℂ))‖ ^ 2 / (q : ℝ) ^ n ≤
      (∑ j ∈ range (W.natDegree + 1), ‖W.coeff j‖ ^ 2) * ((W.natDegree + 1 : ℕ) * B) := by
  set d := W.natDegree
  set e : ℕ → ℝ := fun k => ‖coeff k G‖ ^ 2 / (q : ℝ) ^ k
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : ∀ k, 0 ≤ e k := fun k => by positivity
  set SW := ∑ j ∈ range (d + 1), ‖W.coeff j‖ ^ 2
  have hpt : ∀ n, ‖coeff n (G * (W : PowerSeries ℂ))‖ ^ 2 / (q : ℝ) ^ n ≤
      SW * ∑ j ∈ range (d + 1), (if j ≤ n then e (n - j) else 0) := by
    intro n
    set x : ℕ → ℝ := fun j => ‖(if j ≤ n then coeff (n - j) G else 0)‖
    have h1 : ‖coeff n (G * (W : PowerSeries ℂ))‖ ≤ ∑ j ∈ range (d + 1), ‖W.coeff j‖ * x j := by
      rw [coeff_mul_coe]
      exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => norm_mul _ _))
    have h2 := sum_mul_sq_le_sq_mul_sq (range (d + 1)) (fun j => ‖W.coeff j‖) x
    have h3 : ‖coeff n (G * (W : PowerSeries ℂ))‖ ^ 2 ≤ SW * ∑ j ∈ range (d + 1), x j ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    have h4 : ∀ j ∈ range (d + 1), x j ^ 2 / (q : ℝ) ^ n ≤ if j ≤ n then e (n - j) else 0 := by
      intro j _
      simp only [x, e]
      split_ifs with hjn
      · refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact pow_le_pow_right₀ hq1 (Nat.sub_le n j)
      · simp
    calc ‖coeff n (G * (W : PowerSeries ℂ))‖ ^ 2 / (q : ℝ) ^ n
        ≤ (SW * ∑ j ∈ range (d + 1), x j ^ 2) / (q : ℝ) ^ n :=
          div_le_div_of_nonneg_right h3 (by positivity)
      _ = SW * ∑ j ∈ range (d + 1), x j ^ 2 / (q : ℝ) ^ n := by
          rw [mul_div_assoc]; simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ SW * ∑ j ∈ range (d + 1), (if j ≤ n then e (n - j) else 0) :=
          mul_le_mul_of_nonneg_left (sum_le_sum h4) (sum_nonneg fun _ _ => by positivity)
  have hSW : 0 ≤ SW := sum_nonneg fun _ _ => by positivity
  calc ∑ n ∈ range (D + 1), ‖coeff n (G * (W : PowerSeries ℂ))‖ ^ 2 / (q : ℝ) ^ n
      ≤ ∑ n ∈ range (D + 1), SW * ∑ j ∈ range (d + 1), (if j ≤ n then e (n - j) else 0) :=
        sum_le_sum fun n _ => hpt n
    _ = SW * ∑ j ∈ range (d + 1), ∑ n ∈ range (D + 1), (if j ≤ n then e (n - j) else 0) := by
        rw [← mul_sum, sum_comm]
    _ ≤ SW * ∑ _j ∈ range (d + 1), B := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) hSW
        exact (sum_range_ite_shift_le e he j D).trans (hB D)
    _ = SW * ((d + 1 : ℕ) * B) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- A sequence with coefficients `βⁿc`, `|β|² ≥ q`, `c ≠ 0`, from some index on has unbounded
weighted energy. -/
theorem not_bdd_weightedEnergy_of_geometric {q : ℕ} (hq : 1 ≤ q) {F : PowerSeries ℂ} {β c : ℂ}
    {d : ℕ} (hc : c ≠ 0) (hβ : (q : ℝ) ≤ ‖β‖ ^ 2) (hF : ∀ n, d ≤ n → coeff n F = β ^ n * c) :
    ¬ ∃ B : ℝ, ∀ D, ∑ n ∈ range (D + 1), ‖coeff n F‖ ^ 2 / (q : ℝ) ^ n ≤ B := by
  rintro ⟨B, hB⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set κ := ‖c‖ ^ 2
  have hκ : 0 < κ := by positivity
  have hterm : ∀ n, d ≤ n → κ ≤ ‖coeff n F‖ ^ 2 / (q : ℝ) ^ n := by
    intro n hn
    rw [hF n hn, norm_mul, norm_pow, mul_pow, le_div_iff₀ (by positivity)]
    have h1 : (q : ℝ) ^ n ≤ (‖β‖ ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_pow_left₀ hq0.le hβ n
    have h2 : 0 ≤ κ := hκ.le
    calc κ * (q : ℝ) ^ n ≤ κ * (‖β‖ ^ n) ^ 2 := mul_le_mul_of_nonneg_left h1 h2
      _ = (‖β‖ ^ n) ^ 2 * ‖c‖ ^ 2 := by simp only [κ]; ring
  set N := ⌈B / κ⌉₊
  have hlow : ((N + 1 : ℕ) : ℝ) * κ ≤
      ∑ n ∈ range (d + N + 1), ‖coeff n F‖ ^ 2 / (q : ℝ) ^ n := by
    rw [← sum_range_add_sum_Ico _ (show d ≤ d + N + 1 by omega)]
    have h0 : 0 ≤ ∑ n ∈ range d, ‖coeff n F‖ ^ 2 / (q : ℝ) ^ n :=
      sum_nonneg fun _ _ => by positivity
    have h1 : ∑ _n ∈ Ico d (d + N + 1), κ ≤ ∑ n ∈ Ico d (d + N + 1), ‖coeff n F‖ ^ 2 / (q : ℝ) ^ n :=
      sum_le_sum fun n hn => hterm n (mem_Ico.mp hn).1
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
    rw [show d + N + 1 - d = N + 1 by omega] at h1
    linarith
  have hN : B / κ ≤ N := Nat.le_ceil _
  have := hB (d + N)
  have h2 : B < ((N + 1 : ℕ) : ℝ) * κ := by
    rw [div_le_iff₀ hκ] at hN; push_cast; nlinarith
  linarith

/-! ## The source identity -/

/-- The damping factor `ρ₀ = q^{−ε}` as a complex number. -/
def dampFactor (q : ℕ) (ε : ℝ) : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)

/-- The eigenvalue multiset of a curve model. -/
def eigenMultiset (α : Fin m → ℂ) : Multiset ℂ := (Finset.univ : Finset (Fin m)).val.map α

/-- **The zero-chain condition at damping `ε`.** Every eigenvalue `a` with `‖a‖ ≥ √q q^ε` is
followed by its damped translate `q^{−ε}a` with at least its multiplicity, the value `q` borrowing
one unit from the pole. -/
def ZeroChainCondition (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : Prop :=
  ∀ a : ℂ, Real.sqrt q * (q : ℝ) ^ ε ≤ ‖a‖ →
    (eigenMultiset α).count a ≤
      (eigenMultiset α).count (dampFactor q ε * a) + if a = (q : ℂ) then 1 else 0

/-- The damped eigenvalue polynomial `E(u) = Π(1 − ρ₀αᵢu)`. -/
def dampedEigenPoly (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : Polynomial ℂ :=
  ((eigenMultiset α).map fun a => linPoly (dampFactor q ε * a)).prod

theorem rescale_geomSeries (ρ a : ℂ) : rescale ρ (geomSeries a) = geomSeries (ρ * a) := by
  ext n
  simp [coeff_rescale, geomSeries, mul_pow]

/-- `P(u)` as the coerced eigenvalue polynomial. -/
theorem curveP_eq_coe (α : Fin m → ℂ) :
    curveP α = (((eigenMultiset α).map linPoly).prod : Polynomial ℂ) := by
  rw [coe_multiset_prod_map]
  simp only [coe_linPoly]
  rw [curveP, Finset.prod_eq_multiset_prod, eigenMultiset, Multiset.map_map]
  rfl

/-- The damped Möbius series in product form. -/
theorem curveDampedZinv_eq_prod (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) :
    curveDampedZinv q α ε = (1 - C (dampFactor q ε) * X) * (1 - C (dampFactor q ε * q) * X) *
      ((eigenMultiset α).map fun a => geomSeries (dampFactor q ε * a)).prod := by
  rw [curveDampedZinv, curveZinv, curvePinv, map_mul, map_mul, map_prod,
    rescale_one_sub_C_mul_X, rescale_one_sub_C_mul_X, Finset.prod_eq_multiset_prod, eigenMultiset,
    Multiset.map_map]
  simp only [Function.comp_def, rescale_geomSeries, mul_one, dampFactor]

theorem geomSeries_mul_one_sub (c : ℂ) : geomSeries c * (1 - C c * X) = 1 := by
  rw [mul_comm]; exact one_sub_mul_geomSeries c

/-- **The source identity.** `G·(1 − u)²(1 − qu)E(u) = P(u)((1 − ρ₀u)(1 − qρ₀u) − δE(u))`. -/
theorem curveCentredSeries_mul_eq (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) :
    curveCentredSeries q α ε *
        (((linPoly 1 ^ 2 * linPoly q * dampedEigenPoly q α ε : Polynomial ℂ)) : PowerSeries ℂ) =
      ((((eigenMultiset α).map linPoly).prod * (linPoly (dampFactor q ε) *
        linPoly (dampFactor q ε * q) - Polynomial.C (curveDensity q α ε) *
          dampedEigenPoly q α ε) : Polynomial ℂ) : PowerSeries ℂ) := by
  have hE : ((dampedEigenPoly q α ε : Polynomial ℂ) : PowerSeries ℂ) =
      ((eigenMultiset α).map fun a => 1 - C (dampFactor q ε * a) * X).prod := by
    simp only [dampedEigenPoly, coe_multiset_prod_map, coe_linPoly]
  have hΓE : ((eigenMultiset α).map fun a => geomSeries (dampFactor q ε * a)).prod *
      ((dampedEigenPoly q α ε : Polynomial ℂ) : PowerSeries ℂ) = 1 := by
    rw [hE, ← Multiset.prod_map_mul]
    simp only [geomSeries_mul_one_sub, Multiset.prod_map_one]
  have h1 := geomSeries_mul_one_sub 1
  have hq := geomSeries_mul_one_sub (q : ℂ)
  have hP := curveP_eq_coe α
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_C,
    coe_linPoly, ← hP]
  rw [curveCentredSeries, curveDampedZinv_eq_prod]
  calc geomSeries 1 * (geomSeries 1 * (curveP α * (geomSeries ↑q *
        ((1 - C (dampFactor q ε) * X) * (1 - C (dampFactor q ε * ↑q) * X) *
          ((eigenMultiset α).map fun a => geomSeries (dampFactor q ε * a)).prod -
            C (curveDensity q α ε))))) *
        ((1 - C 1 * X) ^ 2 * (1 - C ↑q * X) * ((dampedEigenPoly q α ε : Polynomial ℂ) :
          PowerSeries ℂ))
      = (geomSeries 1 * (1 - C 1 * X)) * (geomSeries 1 * (1 - C 1 * X)) *
          (geomSeries ↑q * (1 - C ↑q * X)) *
          (curveP α * ((1 - C (dampFactor q ε) * X) * (1 - C (dampFactor q ε * ↑q) * X) *
            (((eigenMultiset α).map fun a => geomSeries (dampFactor q ε * a)).prod *
              ((dampedEigenPoly q α ε : Polynomial ℂ) : PowerSeries ℂ)) -
            C (curveDensity q α ε) * ((dampedEigenPoly q α ε : Polynomial ℂ) : PowerSeries ℂ))) := by
        ring
    _ = curveP α * ((1 - C (dampFactor q ε) * X) * (1 - C (dampFactor q ε * ↑q) * X) -
          C (curveDensity q α ε) * ((dampedEigenPoly q α ε : Polynomial ℂ) : PowerSeries ℂ)) := by
        rw [h1, hq, hΓE]; simp only [one_mul, mul_one]

/-! ## Splitting a product at one root -/

theorem multiset_prod_linPoly_split (M : Multiset ℂ) (f : ℂ → ℂ) (b : ℂ) :
    (M.map fun x => linPoly (f x)).prod =
      linPoly (f b) ^ M.count b * ((M.filter (· ≠ b)).map fun x => linPoly (f x)).prod := by
  conv_lhs => rw [← Multiset.filter_add_not (· = b) M]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate]

theorem eval_prod_linPoly_ne_zero (M : Multiset ℂ) (f : ℂ → ℂ) (r : ℂ)
    (h : ∀ x ∈ M, 1 - f x * r ≠ 0) : ((M.map fun x => linPoly (f x)).prod).eval r ≠ 0 := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp h0
  simp only [Function.comp_apply, eval_linPoly] at hx0
  exact h x hx hx0

/-! ## Necessity -/

/-- **Below a broken zero chain the curve receiver is not admitted.** If some `a` with
`‖a‖ ≥ √q q^ε` has larger multiplicity than its damped translate `q^{−ε}a` (plus one when `a = q`),
the receiver energy is unbounded. No bound on the eigenvalues is needed. -/
theorem not_admits_of_chain_fails {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} {ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : Real.sqrt q * (q : ℝ) ^ ε ≤ ‖a‖)
    (hk : (eigenMultiset α).count (dampFactor q ε * a) + (if a = (q : ℂ) then 1 else 0) <
      (eigenMultiset α).count a) :
    ¬ ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  rintro ⟨B, hB⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set ρr := (q : ℝ) ^ (-ε)
  have hρr : 0 < ρr := Real.rpow_pos_of_pos hq0 _
  set ρ := dampFactor q ε
  have hρ : ρ = (ρr : ℂ) := rfl
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact_mod_cast hρr.ne'
  have hqε : (q : ℝ) ^ ε * ρr = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  have hs1 : 1 < Real.sqrt q := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hqε1 : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq1.le hε.le
  have ha1 : 1 < ‖a‖ := by nlinarith
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha1; linarith
  have hane1 : a ≠ 1 := by intro h; rw [h, norm_one] at ha1; linarith
  set β := ρ * a
  have hβ0 : β ≠ 0 := mul_ne_zero hρ0 ha0
  have hβnorm : Real.sqrt q ≤ ‖β‖ := by
    have : ‖β‖ = ρr * ‖a‖ := by
      simp only [β, norm_mul, hρ, Complex.norm_real, Real.norm_of_nonneg hρr.le]
    rw [this]
    calc Real.sqrt q = ρr * (Real.sqrt q * (q : ℝ) ^ ε) := by rw [mul_comm (Real.sqrt q), ← mul_assoc,
          mul_comm ρr, hqε, one_mul]
      _ ≤ ρr * ‖a‖ := mul_le_mul_of_nonneg_left ha hρr.le
  have hβsq : (q : ℝ) ≤ ‖β‖ ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hβnorm 2
    rwa [Real.sq_sqrt hq0.le] at h
  set r := β⁻¹
  have hβr : β * r = 1 := mul_inv_cancel₀ hβ0
  set S := eigenMultiset α
  set k := S.count a
  set l₀ := S.count β
  -- the two products split at the root `1/β`
  set E' := ((S.filter (· ≠ a)).map fun x => linPoly (ρ * x)).prod
  set P' := ((S.filter (· ≠ β)).map fun x => linPoly x).prod
  have hEsplit : dampedEigenPoly q α ε = linPoly β ^ k * E' :=
    multiset_prod_linPoly_split S (fun x => ρ * x) a
  have hPsplit : (S.map linPoly).prod = linPoly β ^ l₀ * P' :=
    multiset_prod_linPoly_split S (fun x => x) β
  have hE'r : E'.eval r ≠ 0 := by
    refine eval_prod_linPoly_ne_zero _ _ r fun x hx h0 => ?_
    have hxa : x ≠ a := (Multiset.mem_filter.mp hx).2
    apply hxa
    have : ρ * x * r = 1 := by linear_combination -h0
    have h2 : ρ * x * r * β = ρ * a := by rw [this, one_mul]
    rw [mul_assoc, mul_comm r β, hβr, mul_one] at h2
    exact mul_left_cancel₀ hρ0 h2
  have hP'r : P'.eval r ≠ 0 := by
    refine eval_prod_linPoly_ne_zero _ _ r fun x hx h0 => ?_
    have hxb : x ≠ β := (Multiset.mem_filter.mp hx).2
    apply hxb
    have : x * r = 1 := by linear_combination -h0
    calc x = x * r * β := by rw [mul_assoc, mul_comm r β, hβr, mul_one]
      _ = β := by rw [this, one_mul]
  have hlinr : (linPoly β).eval r = 0 := by rw [eval_linPoly, hβr, sub_self]
  set δ := curveDensity q α ε
  -- the surviving factor: `N = (1 − βu)^l N₁`, `A = (1 − βu)^{l+1} A₁`, `N₁(1/β) ≠ 0`
  obtain ⟨l, N₁, A₁, hN, hA, hN₁⟩ : ∃ (l : ℕ) (N₁ A₁ : Polynomial ℂ),
      (S.map linPoly).prod * (linPoly ρ * linPoly (ρ * q) - Polynomial.C δ * dampedEigenPoly q α ε) =
        linPoly β ^ l * N₁ ∧
      linPoly 1 ^ 2 * linPoly q * dampedEigenPoly q α ε = linPoly β ^ l * (linPoly β * A₁) ∧
      N₁.eval r ≠ 0 := by
    have hρr' : ρ * r = a⁻¹ := by
      simp only [r, β]; rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hρ0, one_mul]
    by_cases haq : a = (q : ℂ)
    · -- `a = q`: the pole factor `1 − qρ₀u` is the root factor itself
      rw [if_pos haq] at hk
      have hβq : ρ * q = β := by rw [← haq]
      obtain ⟨j, hj⟩ : ∃ j, k = l₀ + 1 + (j + 1) := ⟨k - l₀ - 2, by omega⟩
      refine ⟨l₀ + 1, P' * (linPoly ρ - Polynomial.C δ * (linPoly β ^ (l₀ + 1 + j) * E')),
        linPoly β ^ j * (linPoly 1 ^ 2 * linPoly q * E'), ?_, ?_, ?_⟩
      · rw [hPsplit, hEsplit, hβq, hj]; ring
      · rw [hEsplit, hj]; ring
      · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
          Polynomial.eval_pow, hlinr, Polynomial.eval_C, zero_pow (by omega), zero_mul, mul_zero,
          sub_zero, eval_linPoly, hρr']
        refine mul_ne_zero hP'r ?_
        intro h0
        apply hane1
        have : a⁻¹ = 1 := by linear_combination -h0
        exact inv_eq_one.mp this
    · rw [if_neg haq] at hk
      obtain ⟨j, hj⟩ : ∃ j, k = l₀ + (j + 1) := ⟨k - l₀ - 1, by omega⟩
      refine ⟨l₀, P' * (linPoly ρ * linPoly (ρ * q) - Polynomial.C δ * dampedEigenPoly q α ε),
        linPoly β ^ j * (linPoly 1 ^ 2 * linPoly q * E'), ?_, ?_, ?_⟩
      · rw [hPsplit]; ring
      · rw [hEsplit, hj]; ring
      · have hEr : (dampedEigenPoly q α ε).eval r = 0 := by
          rw [hEsplit, Polynomial.eval_mul, Polynomial.eval_pow, hlinr, zero_pow (by omega),
            zero_mul]
        rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, hEr,
          mul_zero, sub_zero, eval_linPoly, eval_linPoly, hρr']
        refine mul_ne_zero hP'r (mul_ne_zero ?_ ?_)
        · intro h0
          apply hane1
          have : a⁻¹ = 1 := by linear_combination -h0
          exact inv_eq_one.mp this
        · intro h0
          apply haq
          have h1 : ρ * q * r = 1 := by linear_combination -h0
          have h2 : ρ * q * r * β = ρ * a := by rw [h1, one_mul]
          rw [mul_assoc, mul_comm r β, hβr, mul_one] at h2
          exact (mul_left_cancel₀ hρ0 h2).symm
  -- in power series: cancel the common factor and divide by `1 − βu`
  set G := curveCentredSeries q α ε
  have hid := curveCentredSeries_mul_eq q α ε
  rw [hA, show ((S.map linPoly).prod * (linPoly (dampFactor q ε) * linPoly (dampFactor q ε * ↑q) -
      Polynomial.C (curveDensity q α ε) * dampedEigenPoly q α ε)) = linPoly β ^ l * N₁ from hN]
    at hid
  simp only [Polynomial.coe_mul, Polynomial.coe_pow] at hid
  have hcancel : G * ((linPoly β : PowerSeries ℂ) * (A₁ : PowerSeries ℂ)) = (N₁ : PowerSeries ℂ) := by
    have hne : ((linPoly β : Polynomial ℂ) : PowerSeries ℂ) ^ l ≠ 0 :=
      pow_ne_zero _ (coe_linPoly_ne_zero β)
    refine mul_left_cancel₀ hne ?_
    rw [← hid]; ring
  have hgeo : G * (A₁ : PowerSeries ℂ) = (N₁ : PowerSeries ℂ) * geomSeries β := by
    rw [← hcancel]
    have : (linPoly β : PowerSeries ℂ) * geomSeries β = 1 := by
      rw [coe_linPoly]; exact one_sub_mul_geomSeries β
    calc G * (A₁ : PowerSeries ℂ) = G * (A₁ : PowerSeries ℂ) * ((linPoly β : PowerSeries ℂ) *
          geomSeries β) := by rw [this, mul_one]
      _ = G * ((linPoly β : PowerSeries ℂ) * (A₁ : PowerSeries ℂ)) * geomSeries β := by ring
  -- the energy of `G·A₁` is bounded, its coefficients grow like `βⁿ`
  have hBG : ∀ D, ∑ n ∈ range (D + 1), ‖coeff n G‖ ^ 2 / (q : ℝ) ^ n ≤ B := fun D => by
    have := hB D
    simpa only [curveReceiverEnergy, coeff_curveCentredSeries, G] using this
  refine not_bdd_weightedEnergy_of_geometric (q := q) (by omega) hN₁ hβsq
    (F := G * (A₁ : PowerSeries ℂ)) (d := N₁.natDegree) (fun n hn => ?_)
    ⟨_, weightedEnergy_mul_coe_le (by omega) hBG A₁⟩
  rw [hgeo, coeff_coe_mul_geomSeries N₁ hβ0 hn]

/-! ## Sufficiency -/

/-- A finite multiset of reals below `c > 1` lies below some `τ ∈ [1, c)`. -/
theorem exists_le_of_multiset_lt {M : Multiset ℝ} {c : ℝ} (hc : 1 < c) (hM : ∀ x ∈ M, x < c) :
    ∃ τ, 1 ≤ τ ∧ τ < c ∧ ∀ x ∈ M, x ≤ τ := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨1, le_refl _, hc, by simp⟩
  | cons a M ih =>
      obtain ⟨τ, h1, h2, h3⟩ := ih fun x hx => hM x (Multiset.mem_cons_of_mem hx)
      refine ⟨max τ a, le_max_of_le_left h1, max_lt h2 (hM a (Multiset.mem_cons_self a M)),
        fun x hx => ?_⟩
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact le_max_right _ _
      · exact (h3 x hx).trans (le_max_left _ _)

/-- Coefficients of a product of geometric series over a multiset. -/
theorem norm_coeff_multiset_prod_geomSeries_le {M : Multiset ℂ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hM : ∀ g ∈ M, ‖g‖ ≤ τ) (n : ℕ) :
    ‖coeff n ((M.map geomSeries).prod)‖ ≤ ((n : ℝ) + 1) ^ Multiset.card M * τ ^ n := by
  induction M using Multiset.induction_on generalizing n with
  | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero, one_mul]
      split_ifs with h
      · subst h; simp
      · simp only [norm_zero]; positivity
  | cons a M ih =>
      have ha := hM a (Multiset.mem_cons_self a M)
      have hMs : ∀ g ∈ M, ‖g‖ ≤ τ := fun g hg => hM g (Multiset.mem_cons_of_mem hg)
      rw [Multiset.map_cons, Multiset.prod_cons, coeff_mul, Multiset.card_cons]
      calc ‖∑ p ∈ antidiagonal n, coeff p.1 (geomSeries a) * coeff p.2 ((M.map geomSeries).prod)‖
          ≤ ∑ p ∈ antidiagonal n, τ ^ p.1 * (((p.2 : ℝ) + 1) ^ Multiset.card M * τ ^ p.2) := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
            rw [norm_mul]
            refine mul_le_mul ?_ (ih hMs p.2) (norm_nonneg _) (pow_nonneg hτ _)
            simp only [geomSeries, coeff_mk, norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) ha _
        _ ≤ ∑ _p ∈ antidiagonal n, ((n : ℝ) + 1) ^ Multiset.card M * τ ^ n := by
            refine sum_le_sum fun p hp => ?_
            have hpn := mem_antidiagonal.mp hp
            have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
              have : p.2 ≤ n := by omega
              exact_mod_cast Nat.add_le_add_right this 1
            calc τ ^ p.1 * (((p.2 : ℝ) + 1) ^ Multiset.card M * τ ^ p.2)
                = ((p.2 : ℝ) + 1) ^ Multiset.card M * τ ^ (p.1 + p.2) := by rw [pow_add]; ring
              _ ≤ ((n : ℝ) + 1) ^ Multiset.card M * τ ^ n := by
                  rw [hpn]
                  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 _)
                    (pow_nonneg hτ _)
        _ = ((n : ℝ) + 1) ^ (Multiset.card M + 1) * τ ^ n := by
            rw [sum_const, Nat.card_antidiagonal, nsmul_eq_mul, pow_succ]
            push_cast; ring

/-- Multiplying by a polynomial costs the `ℓ¹` norm of its coefficients. -/
theorem norm_coeff_coe_mul_le (W : Polynomial ℂ) {F : PowerSeries ℂ} {K τ : ℝ} {k : ℕ}
    (hK : 0 ≤ K) (hτ : 1 ≤ τ) (hF : ∀ n, ‖coeff n F‖ ≤ K * ((n : ℝ) + 1) ^ k * τ ^ n) (n : ℕ) :
    ‖coeff n ((W : PowerSeries ℂ) * F)‖ ≤
      (∑ j ∈ range (W.natDegree + 1), ‖W.coeff j‖) * K * ((n : ℝ) + 1) ^ k * τ ^ n := by
  rw [mul_comm, coeff_mul_coe]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul, sum_mul, sum_mul]
  refine sum_le_sum fun j _ => ?_
  rw [norm_mul]
  have hb : ‖(if j ≤ n then coeff (n - j) F else 0)‖ ≤ K * ((n : ℝ) + 1) ^ k * τ ^ n := by
    split_ifs with hjn
    · refine (hF (n - j)).trans ?_
      have h1 : (((n - j : ℕ) : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ k :=
        pow_le_pow_left₀ (by positivity) (by
          have : ((n - j : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n j
          linarith) k
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) (pow_le_pow_right₀ hτ (Nat.sub_le n j))
        (by positivity) (by positivity)
    · simp only [norm_zero]; positivity
  calc ‖W.coeff j‖ * ‖(if j ≤ n then coeff (n - j) F else 0)‖
      ≤ ‖W.coeff j‖ * (K * ((n : ℝ) + 1) ^ k * τ ^ n) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖W.coeff j‖ * K * ((n : ℝ) + 1) ^ k * τ ^ n := by ring

/-- A polynomial factor keeps a zero sum at `u = 1/q`. -/
theorem summable_and_tsum_coe_mul {q : ℕ} (hq : 1 ≤ q) {Bs : PowerSeries ℂ} (W : Polynomial ℂ)
    (hs : Summable fun j => coeff j Bs / (q : ℂ) ^ j)
    (h0 : ∑' j, coeff j Bs / (q : ℂ) ^ j = 0) :
    Summable (fun j => coeff j ((W : PowerSeries ℂ) * Bs) / (q : ℂ) ^ j) ∧
      ∑' j, coeff j ((W : PowerSeries ℂ) * Bs) / (q : ℂ) ^ j = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set h : ℕ → ℂ := fun j => coeff j Bs / (q : ℂ) ^ j
  set g : ℕ → ℕ → ℂ := fun i j => if i ≤ j then h (j - i) else 0
  have hg : ∀ i, Summable (g i) ∧ ∑' j, g i j = 0 := by
    intro i
    have hshift : (fun j => g i (j + i)) = h := by
      funext j; simp only [g, if_pos (Nat.le_add_left i j), Nat.add_sub_cancel]
    have hsum : Summable (g i) := (summable_nat_add_iff i).mp (by rw [hshift]; exact hs)
    refine ⟨hsum, ?_⟩
    have := hsum.sum_add_tsum_nat_add i
    rw [hshift, h0, add_zero] at this
    rw [← this]
    exact sum_eq_zero fun j hj => if_neg (by have := mem_range.mp hj; omega)
  have he : (fun j => coeff j ((W : PowerSeries ℂ) * Bs) / (q : ℂ) ^ j) =
      fun j => ∑ i ∈ range (W.natDegree + 1), (W.coeff i / (q : ℂ) ^ i) * g i j := by
    funext j
    rw [mul_comm, coeff_mul_coe, sum_div]
    refine sum_congr rfl fun i _ => ?_
    simp only [g, h]
    split_ifs with hij
    · rw [show (q : ℂ) ^ j = (q : ℂ) ^ i * (q : ℂ) ^ (j - i) by
        rw [← pow_add, Nat.add_sub_cancel' hij]]
      field_simp
    · simp
  rw [he]
  refine ⟨summable_sum fun i _ => (hg i).1.mul_left _, ?_⟩
  rw [Summable.tsum_finsetSum fun i _ => (hg i).1.mul_left _]
  exact sum_eq_zero fun i _ => by rw [tsum_mul_left, (hg i).2, mul_zero]

/-- **The bad poles cancel on zero chains.** Under the zero-chain condition `P·R` is a polynomial
times the geometric series of the damped eigenvalues below the threshold. -/
theorem curveP_mul_curveDampedZinv_eq_of_chain {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ} {ε : ℝ}
    (hc : ZeroChainCondition q α ε) :
    ∃ H : Polynomial ℂ, curveP α * curveDampedZinv q α ε = (H : PowerSeries ℂ) *
      ((((eigenMultiset α).filter fun a => ¬ (Real.sqrt q * (q : ℝ) ^ ε ≤ ‖a‖)).map
        fun a => dampFactor q ε * a).map geomSeries).prod := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set ρ := dampFactor q ε
  have hρ0 : ρ ≠ 0 := by
    simp only [ρ, dampFactor]; exact_mod_cast (Real.rpow_pos_of_pos hq0 (-ε)).ne'
  set th := Real.sqrt q * (q : ℝ) ^ ε
  set S := eigenMultiset α
  set Bad := S.filter fun a => th ≤ ‖a‖
  set Good := S.filter fun a => ¬ (th ≤ ‖a‖)
  set T := Bad.map fun a => ρ * a
  have hinj : Function.Injective fun a : ℂ => ρ * a := fun x y hxy => mul_left_cancel₀ hρ0 hxy
  -- the matching `ρ₀·Bad ≤ S + {ρ₀ q}`
  have hT : T ≤ S + {ρ * (q : ℂ)} := by
    rw [Multiset.le_iff_count]
    intro x
    obtain ⟨y, rfl⟩ : ∃ y, x = ρ * y := ⟨ρ⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hρ0, one_mul]⟩
    rw [Multiset.count_map_eq_count' _ _ hinj, Multiset.count_add, Multiset.count_singleton,
      Multiset.count_filter]
    split_ifs with hy hyq
    · have := hc y hy
      have hyq' : y = (q : ℂ) := mul_left_cancel₀ hρ0 hyq
      rw [if_pos hyq'] at this; exact this
    · have := hc y hy
      have hyq' : y ≠ (q : ℂ) := fun h => hyq (by rw [h])
      rw [if_neg hyq'] at this; simpa using this
    · omega
    · omega
  obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.mp hT
  set lin' : ℂ → PowerSeries ℂ := fun c => 1 - C c * X
  have hP : curveP α = (S.map lin').prod := by
    rw [curveP, Finset.prod_eq_multiset_prod]
    simp only [S, eigenMultiset, Multiset.map_map]; rfl
  have hR := curveDampedZinv_eq_prod q α ε
  have hsplit : (S.map fun a => geomSeries (ρ * a)).prod =
      (T.map geomSeries).prod * ((Good.map fun a => ρ * a).map geomSeries).prod := by
    conv_lhs => rw [← Multiset.filter_add_not (fun a => th ≤ ‖a‖) S]
    rw [Multiset.map_add, Multiset.prod_add]
    simp only [T, Bad, Good, Multiset.map_map]; rfl
  have hPq : (S.map lin').prod * lin' (ρ * q) = (T.map lin').prod * (U.map lin').prod := by
    have h1 : ((S + {ρ * (q : ℂ)}).map lin').prod = (S.map lin').prod * lin' (ρ * q) := by
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_singleton, Multiset.prod_singleton]
    rw [← h1, hU, Multiset.map_add, Multiset.prod_add]
  have hTT : (T.map lin').prod * (T.map geomSeries).prod = 1 := by
    rw [← Multiset.prod_map_mul]
    simp only [lin', one_sub_mul_geomSeries, Multiset.prod_map_one]
  refine ⟨linPoly ρ * (U.map linPoly).prod, ?_⟩
  have hH : ((linPoly ρ * (U.map linPoly).prod : Polynomial ℂ) : PowerSeries ℂ) =
      lin' ρ * (U.map lin').prod := by
    rw [Polynomial.coe_mul, coe_linPoly, coe_multiset_prod_map]
    simp only [coe_linPoly, lin']
  set G' := ((Good.map fun a => ρ * a).map geomSeries).prod
  rw [hH, hP, hR, hsplit]
  calc (S.map lin').prod * ((1 - C ρ * X) * (1 - C (ρ * ↑q) * X) *
        ((T.map geomSeries).prod * G'))
      = lin' ρ * ((S.map lin').prod * lin' (ρ * q)) * (T.map geomSeries).prod * G' := by
        simp only [lin']; ring
    _ = lin' ρ * (U.map lin').prod * G' * ((T.map lin').prod * (T.map geomSeries).prod) := by
        rw [hPq]; ring
    _ = lin' ρ * (U.map lin').prod * G' := by rw [hTT, mul_one]

/-- A prefix sum costs one power of `n + 2`. -/
theorem norm_coeff_geomSeries_one_mul_le {F : PowerSeries ℂ} {K τ : ℝ} {j : ℕ} (hK : 0 ≤ K)
    (hτ : 1 ≤ τ) (hF : ∀ n, ‖coeff n F‖ ≤ K * ((n : ℝ) + 2) ^ j * τ ^ n) (n : ℕ) :
    ‖coeff n (geomSeries 1 * F)‖ ≤ K * ((n : ℝ) + 2) ^ (j + 1) * τ ^ n := by
  rw [coeff_geomSeries_one_mul]
  have hterm : ∀ k ∈ range (n + 1), ‖coeff k F‖ ≤ K * ((n : ℝ) + 2) ^ j * τ ^ n := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    refine (hF k).trans ?_
    have h1 : ((k : ℝ) + 2) ^ j ≤ ((n : ℝ) + 2) ^ j :=
      pow_le_pow_left₀ (by positivity)
        (by have h := (show (k : ℝ) ≤ n by exact_mod_cast hkn); linarith) j
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) (pow_le_pow_right₀ hτ hkn)
      (by positivity) (by positivity)
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, card_range, nsmul_eq_mul, pow_succ]
  have : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by push_cast; linarith
  calc ((n + 1 : ℕ) : ℝ) * (K * ((n : ℝ) + 2) ^ j * τ ^ n)
      ≤ ((n : ℝ) + 2) * (K * ((n : ℝ) + 2) ^ j * τ ^ n) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = K * (((n : ℝ) + 2) ^ j * ((n : ℝ) + 2)) * τ ^ n := by ring

/-- **Zero chains are admitted.** If every eigenvalue has modulus at most `q` and the zero-chain
condition holds at `ε > 0`, the curve receiver energy is bounded uniformly in the horizon. -/
theorem admits_of_zeroChain {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} (hα : ∀ i, ‖α i‖ ≤ q) {ε : ℝ}
    (hε : 0 < ε) (hc : ZeroChainCondition q α ε) :
    ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set s := Real.sqrt q
  have hs1 : 1 < s := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  set ρr := (q : ℝ) ^ (-ε)
  have hρr : 0 < ρr := Real.rpow_pos_of_pos hq0 _
  have hρr1 : ρr < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hqε : (q : ℝ) ^ ε * ρr = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  set ρ := dampFactor q ε
  have hρnorm : ∀ a : ℂ, ‖ρ * a‖ = ρr * ‖a‖ := fun a => by
    simp only [ρ, dampFactor, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  set th := s * (q : ℝ) ^ ε
  obtain ⟨H, hfac⟩ := curveP_mul_curveDampedZinv_eq_of_chain (by omega) hc
  set Good' := ((eigenMultiset α).filter fun a => ¬ (th ≤ ‖a‖)).map fun a => ρ * a
  -- the surviving growth `τ < √q`
  obtain ⟨τ, hτ1, hτs, hτ⟩ := exists_le_of_multiset_lt hs1 (M := Good'.map norm) (by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hg
    have hat : ‖a‖ < th := lt_of_not_ge (Multiset.mem_filter.mp ha).2
    rw [hρnorm]
    calc ρr * ‖a‖ < ρr * th := mul_lt_mul_of_pos_left hat hρr
      _ = s := by simp only [th]; rw [mul_comm s, ← mul_assoc, mul_comm ρr, hqε, one_mul])
  have hτg : ∀ g ∈ Good', ‖g‖ ≤ τ := fun g hg => hτ _ (Multiset.mem_map_of_mem _ hg)
  set k := Multiset.card Good'
  set K₁ := ∑ j ∈ range (H.natDegree + 1), ‖H.coeff j‖
  have hK₁ : 0 ≤ K₁ := sum_nonneg fun _ _ => norm_nonneg _
  have hPR : ∀ n, ‖coeff n (curveP α * curveDampedZinv q α ε)‖ ≤
      K₁ * ((n : ℝ) + 1) ^ k * τ ^ n := by
    intro n
    rw [hfac]
    have := norm_coeff_coe_mul_le H (F := (Good'.map geomSeries).prod) zero_le_one hτ1
      (fun n => by rw [one_mul]; exact norm_coeff_multiset_prod_geomSeries_le (by linarith) hτg n) n
    simpa only [mul_one] using this
  -- the centred numerator `P·(R − δ)` and its zero sum at `u = 1/q`
  set Bs := curveDampedZinv q α ε - C (curveDensity q α ε)
  set B' := curveP α * Bs
  have hαq : ∀ i, ‖α i‖ ≤ (q : ℝ) := hα
  obtain ⟨hBsum, hB0⟩ := summable_and_tsum_curveCentredSeries hq (t := q) hq1.le hαq (by
    calc (q : ℝ) * (q : ℝ) ^ (-ε) < (q : ℝ) * 1 := mul_lt_mul_of_pos_left hρr1 hq0
      _ = q := mul_one _)
  obtain ⟨hB'sum, hB'0⟩ := summable_and_tsum_coe_mul (by omega)
    (((eigenMultiset α).map linPoly).prod) hBsum hB0
  rw [← curveP_eq_coe] at hB'sum hB'0
  have hB'coeff : ∀ j, m < j → coeff j B' = coeff j (curveP α * curveDampedZinv q α ε) := by
    intro j hj
    simp only [B', Bs, mul_sub, map_sub]
    rw [show curveP α * C (curveDensity q α ε) = C (curveDensity q α ε) * curveP α by ring,
      coeff_C_mul, coeff_curveP_eq_zero α hj, mul_zero, sub_zero]
  -- the tail estimate beyond the degree of `P`
  set x := τ / q
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [div_lt_one hq0]
    calc τ < s := hτs
      _ ≤ s * s := le_mul_of_one_le_right (by linarith) hs1.le
      _ = q := hss
  set Sx := ∑' i : ℕ, ((i : ℝ) + ((1 : ℕ) : ℝ)) ^ k * x ^ i
  have hSx : 0 ≤ Sx := tsum_nonneg fun i => by positivity
  have hqk : ∀ k : ℕ, ‖(q : ℂ) ^ k‖ = (q : ℝ) ^ k := fun k => by
    rw [norm_pow, Complex.norm_natCast]
  have hCbig : ∀ n, m ≤ n → ‖coeff n (geomSeries q * B')‖ ≤ K₁ * Sx * x * ((n : ℝ) + 2) ^ k * τ ^ n := by
    intro n hn
    rw [coeff_geomSeries_mul_eq_neg_tail (by omega) hB'sum hB'0 n, norm_neg, norm_mul, hqk]
    have hbd : ∀ i, ‖coeff (i + (n + 1)) B' / (q : ℂ) ^ (i + (n + 1))‖ ≤
        K₁ * ((n : ℝ) + 2) ^ k * x ^ (n + 1) * (((i : ℝ) + ((1 : ℕ) : ℝ)) ^ k * x ^ i) := by
      intro i
      rw [hB'coeff _ (by omega), norm_div, hqk, div_le_iff₀ (by positivity)]
      have hpow : (((i + (n + 1) : ℕ) : ℝ) + 1) ^ k ≤ ((n : ℝ) + 2) ^ k * ((i : ℝ) + 1) ^ k := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) n]
      calc ‖coeff (i + (n + 1)) (curveP α * curveDampedZinv q α ε)‖
          ≤ K₁ * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ k * τ ^ (i + (n + 1)) := hPR _
        _ ≤ K₁ * (((n : ℝ) + 2) ^ k * ((i : ℝ) + 1) ^ k) * τ ^ (i + (n + 1)) := by gcongr
        _ = K₁ * ((n : ℝ) + 2) ^ k * x ^ (n + 1) *
              (((i : ℝ) + ((1 : ℕ) : ℝ)) ^ k * x ^ i) * (q : ℝ) ^ (i + (n + 1)) := by
            simp only [x]; rw [div_pow, div_pow, pow_add (q : ℝ)]; field_simp; push_cast
            rw [pow_add]; ring
    have hsum := (summable_add_pow_mul_geometric k 1 hx0 hx1).mul_left
      (K₁ * ((n : ℝ) + 2) ^ k * x ^ (n + 1))
    have hnorm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hsum
    have htail : ‖∑' i, coeff (i + (n + 1)) B' / (q : ℂ) ^ (i + (n + 1))‖ ≤
        K₁ * ((n : ℝ) + 2) ^ k * x ^ (n + 1) * Sx := by
      refine (norm_tsum_le_tsum_norm hnorm).trans ?_
      rw [← tsum_mul_left]
      exact hnorm.tsum_le_tsum hbd hsum
    calc (q : ℝ) ^ n * ‖∑' i, coeff (i + (n + 1)) B' / (q : ℂ) ^ (i + (n + 1))‖
        ≤ (q : ℝ) ^ n * (K₁ * ((n : ℝ) + 2) ^ k * x ^ (n + 1) * Sx) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = K₁ * Sx * x * ((n : ℝ) + 2) ^ k * τ ^ n := by
          simp only [x]; rw [div_pow, pow_succ]; field_simp; ring
  set Cs := ∑ n ∈ range m, ‖coeff n (geomSeries q * B')‖
  have hCs : 0 ≤ Cs := sum_nonneg fun _ _ => norm_nonneg _
  set K₂ := K₁ * Sx * x + Cs
  have hK₂ : 0 ≤ K₂ := by positivity
  have hC : ∀ n, ‖coeff n (geomSeries q * B')‖ ≤ K₂ * ((n : ℝ) + 2) ^ k * τ ^ n := by
    intro n
    have hge : 1 ≤ ((n : ℝ) + 2) ^ k * τ ^ n :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hτ1)
    rcases le_or_gt m n with hmn | hmn
    · calc ‖coeff n (geomSeries q * B')‖ ≤ K₁ * Sx * x * ((n : ℝ) + 2) ^ k * τ ^ n :=
            hCbig n hmn
        _ ≤ K₂ * ((n : ℝ) + 2) ^ k * τ ^ n := by
            have : K₁ * Sx * x ≤ K₂ := le_add_of_nonneg_right hCs
            nlinarith [mul_le_mul_of_nonneg_right this (by positivity :
              (0 : ℝ) ≤ ((n : ℝ) + 2) ^ k * τ ^ n)]
    · have h1 : ‖coeff n (geomSeries q * B')‖ ≤ Cs :=
        single_le_sum (f := fun n => ‖coeff n (geomSeries q * B')‖) (fun _ _ => norm_nonneg _)
          (mem_range.mpr hmn)
      have h2 : Cs ≤ K₂ := le_add_of_nonneg_left (by positivity)
      calc ‖coeff n (geomSeries q * B')‖ ≤ K₂ * 1 := by linarith
        _ ≤ K₂ * (((n : ℝ) + 2) ^ k * τ ^ n) := mul_le_mul_of_nonneg_left hge hK₂
        _ = K₂ * ((n : ℝ) + 2) ^ k * τ ^ n := by ring
  have hA1 := norm_coeff_geomSeries_one_mul_le hK₂ hτ1 hC
  have hA2 := norm_coeff_geomSeries_one_mul_le hK₂ hτ1 hA1
  have hAeq : ∀ n, curveCentredPrefix q α ε n =
      coeff n (geomSeries 1 * (geomSeries 1 * (geomSeries q * B'))) := by
    intro n
    rw [curveCentredPrefix_eq]
    congr 3
    simp only [B', Bs]; ring
  -- the energy
  set r := τ ^ 2 / q
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one hq0]
    calc τ ^ 2 < s ^ 2 := pow_lt_pow_left₀ hτs (by linarith) two_ne_zero
      _ = q := by rw [sq, hss]
  set G : ℕ → ℝ := fun n => K₂ ^ 2 * (((n : ℝ) + 2) ^ (2 * (k + 2)) * r ^ n)
  have hG : Summable G := (summable_add_pow_mul_geometric (2 * (k + 2)) 2 hr0 hr1).mul_left _
  refine ⟨∑' n, G n, fun D => ?_⟩
  refine le_trans ?_ (hG.sum_le_tsum (range (D + 1)) (fun n _ => by positivity))
  refine sum_le_sum fun n _ => ?_
  rw [hAeq, div_le_iff₀ (by positivity)]
  have hn := hA2 n
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc ‖coeff n (geomSeries 1 * (geomSeries 1 * (geomSeries q * B')))‖ ^ 2
      ≤ (K₂ * ((n : ℝ) + 2) ^ (k + 1 + 1) * τ ^ n) ^ 2 := hsq
    _ = G n * (q : ℝ) ^ n := by
        simp only [G, r]; rw [div_pow]; field_simp; ring

/-! ## The admission law -/

/-- **The curve receiver is admitted exactly on zero chains.** For eigenvalues of modulus at most
`q` and `ε > 0`, the receiver energy is bounded uniformly in the horizon iff every `a` with
`‖a‖ ≥ √q q^ε` satisfies `mult(a) ≤ mult(q^{−ε}a) + [a = q]`. -/
theorem curveReceiver_admits_iff {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} (hα : ∀ i, ‖α i‖ ≤ q)
    {ε : ℝ} (hε : 0 < ε) :
    (∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B) ↔ ZeroChainCondition q α ε := by
  constructor
  · intro hB a ha
    by_contra h
    exact not_admits_of_chain_fails hq hε ha (lt_of_not_ge h) hB
  · exact admits_of_zeroChain hq hα hε

/-! ## Admitted dampings below the width -/

/-- The admitted dampings of a curve model. -/
def curveReceiverDampings (q : ℕ) (α : Fin m → ℂ) : Set ℝ :=
  {ε | 0 < ε ∧ ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B}

/-- **Below the threshold of an eigenvalue an admitted damping is a chain resonance.** If the
receiver is admitted at `ε` and `a = αᵢ ≠ q` has `‖a‖ ≥ √q q^ε`, then `q^{−ε}a` is an eigenvalue. -/
theorem exists_eq_dampFactor_mul_of_admits {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} {ε : ℝ}
    (hε : 0 < ε) {i : Fin m} (hi : α i ≠ q) (hth : Real.sqrt q * (q : ℝ) ^ ε ≤ ‖α i‖)
    (hB : ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B) :
    ∃ j, α j = dampFactor q ε * α i := by
  by_contra h
  push Not at h
  have hcount : (eigenMultiset α).count (dampFactor q ε * α i) = 0 := by
    refine Multiset.count_eq_zero.mpr fun hm => ?_
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hm
    exact h j hj
  have hpos : 0 < (eigenMultiset α).count (α i) :=
    Multiset.count_pos.mpr (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  exact not_admits_of_chain_fails hq hε hth (by rw [hcount, if_neg hi]; simpa using hpos) hB

/-- **Finitely many admitted dampings below an eigenvalue's threshold.** For an eigenvalue
`αᵢ ≠ q`, the admitted dampings `ε` with `√q q^ε ≤ ‖αᵢ‖` lie in the finite set
`{log_q(‖αᵢ‖/‖αⱼ‖)}`. -/
theorem finite_curveReceiverDampings_below {q : ℕ} (hq : 2 ≤ q) (α : Fin m → ℂ) {i : Fin m}
    (hi : α i ≠ q) :
    {ε | ε ∈ curveReceiverDampings q α ∧ Real.sqrt q * (q : ℝ) ^ ε ≤ ‖α i‖}.Finite := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  refine (Set.finite_range fun j : Fin m => Real.logb q (‖α i‖ / ‖α j‖)).subset ?_
  rintro ε ⟨⟨hε, hB⟩, hth⟩
  obtain ⟨j, hj⟩ := exists_eq_dampFactor_mul_of_admits hq hε hi hth hB
  refine ⟨j, ?_⟩
  have hρr : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  have hai : 0 < ‖α i‖ := lt_of_lt_of_le (by positivity) hth
  have hnorm : ‖α j‖ = (q : ℝ) ^ (-ε) * ‖α i‖ := by
    rw [hj, norm_mul]
    simp only [dampFactor, Complex.norm_real]
    rw [Real.norm_of_nonneg hρr.le]
  have hratio : ‖α i‖ / ‖α j‖ = (q : ℝ) ^ ε := by
    rw [hnorm, Real.rpow_neg hq0.le]
    field_simp
  simp only [hratio, Real.logb_rpow hq0 hq1.ne']

/-- **Accumulated admission reads the width.** Every accumulation point `ε₀` of the admitted
dampings satisfies `‖αᵢ‖ ≤ √q q^{ε₀}` for every eigenvalue `αᵢ ≠ q`: isolated admitted dampings may
lie below the zero width, accumulating ones may not. -/
theorem norm_le_of_accPt_curveReceiverDampings {q : ℕ} (hq : 2 ≤ q) (α : Fin m → ℂ) {ε₀ : ℝ}
    (h : AccPt ε₀ (Filter.principal (curveReceiverDampings q α))) {i : Fin m} (hi : α i ≠ q) :
    ‖α i‖ ≤ Real.sqrt q * (q : ℝ) ^ ε₀ := by
  by_contra hlt
  push Not at hlt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcont : Continuous fun ε : ℝ => Real.sqrt q * (q : ℝ) ^ ε :=
    continuous_const.mul (continuous_const.rpow continuous_id fun _ => Or.inl hq0.ne')
  have hev : ∀ᶠ ε in 𝓝 ε₀, Real.sqrt q * (q : ℝ) ^ ε < ‖α i‖ :=
    hcont.continuousAt.eventually (gt_mem_nhds hlt)
  set F := {ε | ε ∈ curveReceiverDampings q α ∧ Real.sqrt q * (q : ℝ) ^ ε ≤ ‖α i‖}
  have hF : F.Finite := finite_curveReceiverDampings_below hq α hi
  have hev2 : ∀ᶠ ε in 𝓝 ε₀, ε ∉ F \ {ε₀} :=
    (hF.sdiff).isClosed.isOpen_compl.mem_nhds (fun hm => hm.2 rfl)
  rw [accPt_iff_frequently] at h
  refine (not_frequently.mpr ?_) h
  filter_upwards [hev, hev2] with ε h1 h2 h3
  exact h2 ⟨⟨h3.2, h1.le⟩, h3.1⟩

/-- **An admitted damping below the zero width.** The eigenvalues `a` and `q^{−ε}a` with
`√q q^ε ≤ ‖a‖ < √q q^{2ε}` and `‖a‖ ≤ q` are admitted at `ε`, although `a` lies right of the
critical line at depth `log_q(‖a‖/√q) ≥ ε`: the pole of `a` is cancelled by the zero `q^{−ε}a`. -/
theorem curveReceiver_admits_chainPair {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε) {a : ℂ}
    (ha : Real.sqrt q * (q : ℝ) ^ ε ≤ ‖a‖) (ha' : ‖a‖ < Real.sqrt q * (q : ℝ) ^ (2 * ε))
    (haq : ‖a‖ ≤ q) :
    ∃ B : ℝ, ∀ D, curveReceiverEnergy q ![a, dampFactor q ε * a] ε D ≤ B := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set ρr := (q : ℝ) ^ (-ε)
  have hρr : 0 < ρr := Real.rpow_pos_of_pos hq0 _
  have hρr1 : ρr < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  set ρ := dampFactor q ε
  have hρnorm : ‖ρ * a‖ = ρr * ‖a‖ := by
    rw [norm_mul]
    simp only [ρ, dampFactor, Complex.norm_real]
    rw [Real.norm_of_nonneg hρr.le]
  have hth0 : 0 < Real.sqrt q * (q : ℝ) ^ ε := by positivity
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; linarith
  have hρa_lt : ‖ρ * a‖ < Real.sqrt q * (q : ℝ) ^ ε := by
    rw [hρnorm]
    have h2 : (q : ℝ) ^ (2 * ε) = (q : ℝ) ^ ε * (q : ℝ) ^ ε := by
      rw [two_mul, Real.rpow_add hq0]
    have h3 : ρr * (q : ℝ) ^ ε = 1 := by
      rw [← Real.rpow_add hq0, neg_add_cancel, Real.rpow_zero]
    calc ρr * ‖a‖ < ρr * (Real.sqrt q * (q : ℝ) ^ (2 * ε)) := mul_lt_mul_of_pos_left ha' hρr
      _ = Real.sqrt q * (q : ℝ) ^ ε := by rw [h2]; linear_combination (Real.sqrt q * (q : ℝ) ^ ε) * h3
  have hne : a ≠ ρ * a := by
    intro h
    have : ‖a‖ = ‖ρ * a‖ := by rw [← h]
    rw [hρnorm] at this
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    nlinarith
  have hS : eigenMultiset ![a, ρ * a] = a ::ₘ {ρ * a} := by
    simp only [eigenMultiset, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero]
    rfl
  refine admits_of_zeroChain hq (fun i => ?_) hε fun x hx => ?_
  · fin_cases i
    · simpa using haq
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hρnorm]; nlinarith [norm_nonneg a]
  · have hxρ : x ≠ ρ * a := by
      intro h; rw [h] at hx; linarith
    rw [hS]
    by_cases hxa : x = a
    · subst hxa
      rw [Multiset.count_cons_self, Multiset.count_singleton, if_neg hxρ,
        Multiset.count_cons_of_ne hne.symm, Multiset.count_singleton_self]
      omega
    · rw [Multiset.count_cons_of_ne hxa, Multiset.count_singleton, if_neg hxρ]
      omega

end GaloisForLFunctions.ArithmeticCompensationTheory
