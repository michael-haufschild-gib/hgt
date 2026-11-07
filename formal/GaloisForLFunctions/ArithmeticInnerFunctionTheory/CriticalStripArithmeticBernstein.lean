import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheFixedBaseConeAndCriticalBernstein
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCalculusOfEulerColumns
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The critical-strip architecture of Arithmetic Bernstein (`κ ∈ [½, 1]`)

`TheArithmeticBernsteinTheorem` proves that below `κ < ½`, all-base torus positivity forces
exponential convexity (`IsExpConvexFrom`), while `TheFixedBaseConeAndCriticalBernstein` proves that
above the Euler abscissa `α > 1` small perturbations `e^{−αy} − ε · tentBump y` remain strictly
all-base torus-positive without being exponentially convex, whereas on `(0, 1]` they collapse already
at `x = 0`. This module resolves what happens across the critical strip `κ ∈ [½, 1]`:

1. **Exact intermediate transition of the Level-1 Hecke cone at `κ = ½`
   (`heckePositive_iff_expConvex_of_lt_half`, `exists_heckePositive_not_torusPositive_ge_half`).**
   Below `κ < ½`, all-base Level-1 Hecke positivity, all-base torus positivity, and exponential
   convexity coincide. At `κ = ½` itself — and for every `κ ≥ ½` — a weighted Schur bound with
   weights `p_i^{−1/2}` bounds the prime-pair operator of `tentBump` by `2√5 e^{−x/2} ∑ d_i²` with no
   logarithmic loss, so `e^{−κy} − ε · tentBump y` is all-base Level-1 Hecke positive while failing
   `IsExpConvexFrom 0` and (throughout `κ ∈ [½, 1]`) failing full torus positivity at `x = 0`.
   Thus `κ = ½` is the exact threshold of the `L²` prime-pair cone, whereas higher prime-power
   multiplicative correlations keep the full Euler-torus cone rigid across `[½, 1]`.

2. **`SU(2)` Poisson–Szegő kernel and complete-monotonicity module law
   (`hasSum_cosSum_mul_cosSum_geom`, `torusSum_mul_geom_eq_integral`,
   `IsAllBaseTorusPositive.mul_exp_neg`).**
   For `|r| < 1`, `∑'_{k : ℕ} r^k U_k(cos θ) U_k(cos φ)` sums to the positive kernel
   `(1 − r²) / ((1 − 2r cos(θ − φ) + r²)(1 − 2r cos(θ + φ) + r²)) > 0`. Pairing against Sato–Tate
   measure proves that both fixed-base and all-base torus-positive cones are closed under
   multiplication by `e^{−βy}` for every `β ≥ 0`.

3. **Critical-strip Mellin–Kronecker exponent collapse (`eq_zero_of_torusPositive_of_lt_min_one`).**
   Any continuous all-base torus-positive amplitude `f` with right decay `ExpDecayFrom 0 κ₀ f`
   (`κ₀ > 0`) and left growth `|f y| ≤ C e^{−κy}` on `(−∞, 0]` at any exponent `κ < min(1, κ₀)`
   (covering every `κ ∈ [½, 1)` whenever `κ₀ > κ`) vanishes identically: phase-locking
   `θ_p = t log p` on disjoint prime windows where `cos(t log p) ≤ −½` drives the Mellin–Euler
   ratio `∏(1 − p^{−σ}) → 0` for `0 < σ < 1`, annihilating the Fourier–Laplace transform of `f`.

4. **Oscillatory Bernstein dichotomy at `α = 1` (`oscillatory_bernstein_dichotomy`).**
   For `f(y) = e^{−αy}(1 + ε cos(ωy))` (`ω ≠ 0`), every `ε ≠ 0` violates all-base torus positivity
   throughout `0 < α ≤ 1` (including `α = ½` and `α = 1`), whereas for every `α > 1` small `|ε| > 0`
   gives strict all-base torus positivity without exponential convexity.

5. **Signed finite Laplace mixture dichotomy at `α = 1`
   (`laplaceMixture_torusPositive_iff_nonneg`, `exists_supercritical_laplaceMixture_not_expConvex`).**
   For strictly increasing exponents `0 < α₀ < … < α_{m−1} ≤ 1`, `∑_r c_r e^{−α_r y}` is all-base
   torus-positive if and only if every `c_r ≥ 0` (isolated at `θ_q = π` via uniform strict concavity
   of `−2 log(1 + q^{−α})` and `∑ q⁻¹ = ∞`). Above `1` (`1 < α₀ < α₁ < α₂`),
   `e^{−α₀ y} − ε e^{−α₁ y} + e^{−α₂ y}` is strictly all-base torus-positive for small `ε > 0` yet
   violates `IsExpConvexFrom 0` on a `3 × 3` Vandermonde–Hankel test.
-/

open Filter Topology MeasureTheory Set Finset Complex
open scoped Real ENNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum cosSum_add_two)
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### 1. All-base torus and Level-1 Hecke cones, and subcritical coincidence (`κ < ½`) -/

/-- All-base torus positivity across every finite tuple of distinct primes, base point, and phase. -/
def IsAllBaseTorusPositive (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
    ∀ (x : ℝ) (θ : Fin n → ℝ), 0 ≤ torusSum (ampl f (fun i => Real.log (p i)) x) θ

/-- All-base Level-1 Hecke positivity across every finite tuple of distinct primes and base point. -/
def IsAllBaseHeckePositive (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
    ∀ (x : ℝ) (d : Fin n → ℝ),
      0 ≤ f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + Real.log (p i) + Real.log (p j))

/-- Evaluating all-base torus positivity on the empty prime tuple yields pointwise nonnegativity. -/
theorem IsAllBaseTorusPositive.nonneg {f : ℝ → ℝ} (hf : IsAllBaseTorusPositive f) (y : ℝ) :
    0 ≤ f y := by
  have h := hf 0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) y Fin.elim0
  haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
  rw [torusSum, tsum_fintype] at h
  simpa [ampl, chiProd] using h

/-- Exponential convexity at all base points implies all-base torus positivity under right decay. -/
theorem isAllBaseTorusPositive_of_expConvex {f : ℝ → ℝ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) (hE : ∀ x₀, IsExpConvexFrom x₀ f) :
    IsAllBaseTorusPositive f := by
  intro n p hp _ x θ
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  exact (IsExpConvexFrom.torusSum hκ₀ (hE x) (hd x) hℓ θ).1.nonneg le_rfl

/-- All-base torus positivity implies all-base Level-1 Hecke positivity under right decay. -/
theorem IsAllBaseTorusPositive.isAllBaseHeckePositive {f : ℝ → ℝ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) (hf : IsAllBaseTorusPositive f) :
    IsAllBaseHeckePositive f := by
  intro n p hp hinj x d
  obtain ⟨C, -, hC⟩ := hd x
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  exact hecke_primes_nonneg (traceSummable_ampl hκ₀ hC hℓ le_rfl) (hf n p hp hinj x) d

/-- Below `κ < ½`, Level-1 Hecke positivity alone forces every real Hankel form to be nonnegative. -/
theorem hankel_nonneg_of_heckePositive {f : ℝ → ℝ} (hc : Continuous f) {κ C : ℝ} (hκ : κ < 1 / 2)
    (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y))
    (hpos : IsAllBaseHeckePositive f) (y : ℝ) (T : Finset ℝ) (c : ℝ → ℝ) :
    0 ≤ ∑ v ∈ T, ∑ w ∈ T, c v * c w * f (y + v + w) := by
  classical
  by_contra hneg
  push Not at hneg
  set A := ∑ v ∈ T, ∑ w ∈ T, c v * c w * f (y + v + w) with hA
  set η := -A with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set M := (∑ v ∈ T, |c v|) ^ 2 with hM
  have hM0 : 0 ≤ M := sq_nonneg _
  set δ := η / (4 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hL 0 le_rfl)
  set V : ℝ := ∑ v ∈ T, |v| + 1 with hV
  have hVv : ∀ v ∈ T, |v| + 1 ≤ V := fun v hv => by
    have := Finset.single_le_sum (f := fun v => |v|) (fun _ _ => abs_nonneg _) hv
    rw [hV]; linarith
  have huc := (isCompact_Icc (a := y - 2 * V) (b := y + 2 * V)).uniformContinuousOn_of_continuous
    hc.continuousOn
  obtain ⟨ε₀, hε₀, huc⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ0
  obtain ⟨g, hg, hgap⟩ := exists_gap T
  set ε := min (ε₀ / 4) (min (g / 2) (1 / 2))
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hε1 : ε ≤ ε₀ / 4 := min_le_left _ _
  have hε2 : ε ≤ g / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c₁, hc₁, X₀, hX₀, hwin⟩ := exists_card_primes_window_ge hε0
  set β : ℝ := 1 - 2 * κ with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set Ssq : ℝ := ∑ v ∈ T, c v ^ 2 with hSsq
  have hSsq0 : 0 ≤ Ssq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K₁ : ℝ := C * Real.exp (-κ * y) * (Ssq * Real.exp V / c₁) with hK₁
  have hcost : ∀ᶠ u : ℝ in atTop, K₁ * ((u + V) * Real.exp (-β * u)) < η / 4 := by
    have := (tendsto_add_mul_exp_neg hβ0 V).const_mul K₁
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := (hcost.and ((eventually_ge_atTop (Real.log X₀ + V)).and
    ((eventually_ge_atTop (y / 2)).and (eventually_ge_atTop V)))).exists
  have hx : y - 2 * u ≤ 0 := by linarith
  set X : ℝ → ℝ := fun v => Real.exp (u + v) with hXd
  have hXpos : ∀ v, 0 < X v := fun _ => Real.exp_pos _
  have hX0 : ∀ v ∈ T, X₀ ≤ X v := fun v hv => by
    have hv' := abs_le.mp ((le_add_of_nonneg_right zero_le_one).trans (hVv v hv))
    rw [hXd, ← Real.exp_log (by linarith : 0 < X₀)]
    exact Real.exp_le_exp.mpr (by linarith [hv'.1])
  set P : ℝ → Finset ℕ := fun v => primesInIoc ⌊X v⌋₊ ⌊Real.exp ε * X v⌋₊
  have hmemP : ∀ v q, q ∈ P v → q.Prime ∧ u + v < Real.log q ∧ Real.log q ≤ u + v + ε := by
    intro v q hq
    have hq' := Finset.mem_filter.mp hq
    have hI := Finset.mem_Ioc.mp hq'.1
    have h1 : X v < q := Nat.lt_of_floor_lt hI.1
    have h2 : (q : ℝ) ≤ Real.exp ε * X v :=
      (Nat.cast_le.mpr hI.2).trans (Nat.floor_le (by positivity))
    have hq0 : (0 : ℝ) < q := lt_trans (hXpos v) h1
    refine ⟨hq'.2, (Real.lt_log_iff_exp_lt hq0).mpr h1, (Real.log_le_iff_le_exp hq0).mpr ?_⟩
    exact h2.trans_eq (by rw [hXd, ← Real.exp_add]; ring_nf)
  have hdisj : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → Disjoint (P v) (P w) := by
    intro v hv w hw hvw
    rw [Finset.disjoint_left]
    intro q hq hq2
    obtain ⟨-, h1, h2⟩ := hmemP v q hq
    obtain ⟨-, h3, h4⟩ := hmemP w q hq2
    have h5 := hgap v hv w hw hvw
    have h6 : |v - w| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have hlogX : ∀ v ∈ T, 0 < u + v := fun v hv => by
    have := hVv v hv; have := neg_abs_le v; linarith
  have hcard : ∀ v ∈ T, c₁ * (X v / (u + v)) ≤ ((P v).card : ℝ) := fun v hv => by
    have h := hwin (X v) (hX0 v hv)
    rwa [hXd, Real.log_exp] at h
  have hcardpos : ∀ v ∈ T, 0 < (P v).card := fun v hv => by
    have h0 : 0 < c₁ * (X v / (u + v)) := mul_pos hc₁ (div_pos (hXpos v) (hlogX v hv))
    exact_mod_cast lt_of_lt_of_le h0 (hcard v hv)
  set dd : ℕ → ℝ := fun q => ∑ v ∈ T, if q ∈ P v then c v / (P v).card else 0
  have hddP : ∀ v ∈ T, ∀ q ∈ P v, dd q = c v / (P v).card := by
    intro v hv q hq
    dsimp only [dd]
    rw [Finset.sum_eq_single v]
    · simp [hq]
    · intro w hw hwv
      rw [if_neg]
      exact fun h => Finset.disjoint_left.mp (hdisj w hw v hv hwv) h hq
    · exact fun h => absurd hv h
  set Z : Finset ℕ := T.biUnion P with hZ
  have hPd : (T : Set ℝ).PairwiseDisjoint P := fun v hv w hw hvw => hdisj v hv w hw hvw
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  let p : Fin Z.card → ℕ := fun i => (e i : ℕ)
  have hpp : ∀ i, (p i).Prime := fun i => by
    obtain ⟨v, -, hqv⟩ := Finset.mem_biUnion.mp (e i).2
    exact (hmemP v _ hqv).1
  have hpinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hsumZ : ∀ G : ℕ → ℝ, ∑ i, G (p i) = ∑ v ∈ T, ∑ q ∈ P v, G q := fun G => by
    rw [Equiv.sum_comp e fun z : Z => G z, Finset.sum_coe_sort Z G, hZ, Finset.sum_biUnion hPd]
  set x : ℝ := y - 2 * u with hxd
  have hH := hpos Z.card p hpp hpinj x (fun i => dd (p i))
  have hdiag : f x * ∑ i, dd (p i) ^ 2 ≤ K₁ * ((u + V) * Real.exp (-β * u)) := by
    rw [hsumZ fun q => dd q ^ 2]
    have hsq : ∀ v ∈ T, ∑ q ∈ P v, dd q ^ 2 = c v ^ 2 / (P v).card := fun v hv => by
      have hc0 : ((P v).card : ℝ) ≠ 0 := by exact_mod_cast (hcardpos v hv).ne'
      rw [Finset.sum_congr rfl fun q hq => by rw [hddP v hv q hq], Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hsq]
    have hinv : ∀ v ∈ T, c v ^ 2 / (P v).card ≤
        c v ^ 2 * ((u + V) * Real.exp V * Real.exp (-u) / c₁) := fun v hv => by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hposw : 0 < c₁ * (X v / (u + v)) := mul_pos hc₁ (div_pos (hXpos v) (hlogX v hv))
      refine (inv_anti₀ hposw (hcard v hv)).trans ?_
      have hv1 := hVv v hv; have hv2 := neg_abs_le v; have hv3 := le_abs_self v
      have hexp : Real.exp (-(u + v)) ≤ Real.exp V * Real.exp (-u) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      have e1 : (c₁ * (X v / (u + v)))⁻¹ = (u + v) * Real.exp (-(u + v)) / c₁ := by
        simp only [hXd, Real.exp_neg]; have := hlogX v hv; field_simp
      rw [e1]
      refine div_le_div_of_nonneg_right ?_ hc₁.le
      calc (u + v) * Real.exp (-(u + v))
          ≤ (u + V) * (Real.exp V * Real.exp (-u)) :=
            mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith [hlogX v hv])
        _ = _ := by ring
    have hsumle : ∑ v ∈ T, c v ^ 2 / (P v).card ≤ Ssq * ((u + V) * Real.exp V * Real.exp (-u) / c₁) := by
      rw [hSsq, Finset.sum_mul]; exact Finset.sum_le_sum hinv
    have hsumnn : 0 ≤ ∑ v ∈ T, c v ^ 2 / (P v).card :=
      Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    have hexpx : Real.exp (-κ * x) = Real.exp (-κ * y) * Real.exp (2 * κ * u) := by
      rw [← Real.exp_add, hxd]; congr 1; ring
    calc f x * ∑ v ∈ T, c v ^ 2 / (P v).card
        ≤ (C * Real.exp (-κ * x)) * ∑ v ∈ T, c v ^ 2 / (P v).card :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hL x hx)) hsumnn
      _ ≤ (C * Real.exp (-κ * x)) * (Ssq * ((u + V) * Real.exp V * Real.exp (-u) / c₁)) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ = K₁ * ((u + V) * Real.exp (-β * u)) := by
          rw [hexpx, hK₁]
          have e3 : Real.exp (-β * u) = Real.exp (2 * κ * u) * Real.exp (-u) := by
            rw [← Real.exp_add, hβ]; congr 1; ring
          rw [e3]; field_simp
  have hdouble : ∑ i, ∑ j, dd (p i) * dd (p j) * f (x + Real.log (p i) + Real.log (p j)) ≤
      A + δ * M := by
    have h1 : ∑ i, ∑ j, dd (p i) * dd (p j) * f (x + Real.log (p i) + Real.log (p j)) =
        ∑ v ∈ T, ∑ w ∈ T, ∑ q ∈ P v, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r) := by
      have hin : ∀ q : ℕ, ∑ j, dd q * dd (p j) * f (x + Real.log q + Real.log (p j)) =
          ∑ w ∈ T, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r) := fun q =>
        hsumZ fun r => dd q * dd r * f (x + Real.log q + Real.log r)
      simp_rw [hin]
      rw [hsumZ fun q => ∑ w ∈ T, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r)]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [h1, hA]
    have hblock : ∀ v ∈ T, ∀ w ∈ T, ∑ q ∈ P v, ∑ r ∈ P w,
        dd q * dd r * f (x + Real.log q + Real.log r) ≤
        c v * c w * f (y + v + w) + |c v| * |c w| * δ := fun v hv w hw => by
      have hcongr : ∑ q ∈ P v, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r) =
          ∑ q ∈ P v, ∑ r ∈ P w, (c v / (P v).card) * (c w / (P w).card) *
            f (x + Real.log q + Real.log r) :=
        Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r hr => by
          rw [hddP v hv q hq, hddP w hw r hr]
      rw [hcongr]
      have hb := abs_block_sub_le (P v) (P w) (hcardpos v hv) (hcardpos w hw) (c v) (c w)
        (f (y + v + w)) δ (fun q r => f (x + Real.log q + Real.log r)) fun q hq r hr => by
          obtain ⟨-, h1, h2⟩ := hmemP v q hq
          obtain ⟨-, h3, h4⟩ := hmemP w r hr
          have hv1 := hVv v hv; have hw1 := hVv w hw
          have hv2 := le_abs_self v; have hv3 := neg_abs_le v
          have hw2 := le_abs_self w; have hw3 := neg_abs_le w
          have hA1 : x + Real.log q + Real.log r ∈ Icc (y - 2 * V) (y + 2 * V) :=
            ⟨by rw [hxd]; linarith, by rw [hxd]; linarith⟩
          have hA2 : y + v + w ∈ Icc (y - 2 * V) (y + 2 * V) := ⟨by linarith, by linarith⟩
          have hdist : dist (x + Real.log q + Real.log r) (y + v + w) < ε₀ := by
            rw [Real.dist_eq, abs_lt, hxd]; exact ⟨by linarith, by linarith⟩
          exact (Real.dist_eq _ _ ▸ huc _ hA1 _ hA2 hdist).le
      linarith [(abs_le.mp hb).2]
    refine (Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun w hw => hblock v hv w hw).trans ?_
    simp only [Finset.sum_add_distrib]
    have e4 : ∑ v ∈ T, ∑ w ∈ T, |c v| * |c w| * δ = δ * M := by
      rw [hM, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e4]
  have hδM : δ * M ≤ η / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hAη : A = -η := by rw [hη]; ring
  linarith

/-- **Subcritical coincidence (`κ < ½`).** Below left exponent `½`, Level-1 Hecke positivity
already equals exponential convexity (and hence coincides with full torus positivity). -/
theorem heckePositive_iff_expConvex_of_lt_half {f : ℝ → ℝ} (hc : Continuous f) {κ₀ : ℝ}
    (hκ₀ : 0 < κ₀) (hd : ∀ x, ExpDecayFrom x κ₀ f) {κ C : ℝ} (hκ : κ < 1 / 2)
    (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y)) :
    IsAllBaseHeckePositive f ↔ ∀ x₀, IsExpConvexFrom x₀ f := by
  constructor
  · intro hpos x₀ ι S t c' _
    classical
    have hreal : ∀ d : ι → ℝ, 0 ≤ ∑ i ∈ S, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) := fun d => by
      set T := S.image t
      set cc : ℝ → ℝ := fun v => ∑ i ∈ S with t i = v, d i with hcc
      have hH := hankel_nonneg_of_heckePositive hc hκ hL hpos x₀ T cc
      have hfib : ∀ G : ℝ → ℝ, ∑ i ∈ S, d i * G (t i) = ∑ v ∈ T, cc v * G v := fun G => by
        rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := t)
          (fun i hi => Finset.mem_image_of_mem t hi)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hcc, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
      have e : ∑ i ∈ S, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) =
          ∑ v ∈ T, ∑ w ∈ T, cc v * cc w * f (x₀ + v + w) := by
        have h1 : ∀ i, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) =
            d i * ∑ w ∈ T, cc w * f (x₀ + t i + w) := fun i => by
          rw [← hfib fun w => f (x₀ + t i + w), Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
        simp_rw [h1]
        rw [hfib fun v => ∑ w ∈ T, cc w * f (x₀ + v + w)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rwa [e]
    have hsplit : (∑ i ∈ S, ∑ j ∈ S, c' i * conj (c' j) * (f (x₀ + t i + t j) : ℂ)).re =
        ∑ i ∈ S, ∑ j ∈ S, (c' i).re * (c' j).re * f (x₀ + t i + t j) +
          ∑ i ∈ S, ∑ j ∈ S, (c' i).im * (c' j).im * f (x₀ + t i + t j) := by
      rw [Complex.re_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_mul_ofReal, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hsplit]
    exact add_nonneg (hreal fun i => (c' i).re) (hreal fun i => (c' i).im)
  · intro hE
    exact (isAllBaseTorusPositive_of_expConvex hκ₀ hd hE).isAllBaseHeckePositive hκ₀ hd

/-! ### 2. Exact intermediate transition at `κ = ½` -/

private theorem sum_inv_sqrt_Icc_le : ∀ K : ℕ,
    ∑ m ∈ Finset.Icc 1 K, (Real.sqrt (m : ℝ))⁻¹ ≤ 2 * Real.sqrt (K : ℝ)
  | 0 => by simp
  | K + 1 => by
    have hmem : K + 1 ∉ Finset.Icc 1 K := by simp
    have hins : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert hmem]
    have ih := sum_inv_sqrt_Icc_le K
    have hstep : (Real.sqrt ((K + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((K + 1 : ℕ) : ℝ) - Real.sqrt (K : ℝ)) := by
      set a := Real.sqrt ((K + 1 : ℕ) : ℝ)
      set b := Real.sqrt (K : ℝ)
      have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
      have hba : b ≤ a := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ K)
      have hsq_diff : (a - b) * (a + b) = 1 := by
        have h1 : a ^ 2 = (K : ℝ) + 1 := by
          simpa [a, Nat.cast_add, Nat.cast_one] using Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (K + 1 : ℕ))
        have h2 : b ^ 2 = (K : ℝ) := Real.sq_sqrt (Nat.cast_nonneg K)
        nlinarith
      rw [inv_le_iff_one_le_mul₀' ha_pos]
      nlinarith
    linarith

/-- Weighted Schur bound on the prime-pair operator of `tentBump` with weights `p_i^{−1/2}`:
no logarithmic factor appears, yielding `2√5 e^{−x/2} ∑_i d_i²` uniformly in `n, p, x`. -/
theorem abs_tentBump_prime_double_sum_le {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (x : ℝ) (d : Fin n → ℝ) :
    |∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))| ≤
      (if Real.log (5 / 4) ≤ x then 0 else 2 * Real.sqrt 5 * Real.exp (-x / 2)) * ∑ i, d i ^ 2 := by
  split_ifs with hx
  · have hzero : ∀ i j : Fin n, tentBump (x + Real.log (p i) + Real.log (p j)) = 0 := fun i j => by
      apply tentBump_eq_zero_of_ge_log_five
      have hp2_i : Real.log 2 ≤ Real.log (p i) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (hp i).two_le)
      have hp2_j : Real.log 2 ≤ Real.log (p j) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (hp j).two_le)
      have hlog54 : Real.log (5 / 4) + 2 * Real.log 2 = Real.log 5 := by
        rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      linarith
    simp [hzero]
  · classical
    set W : ℝ := Real.exp (-x)
    have hW_pos : 0 < W := Real.exp_pos _
    let ind : Fin n → Fin n → ℝ := fun i j =>
      if (p i : ℝ) * (p j : ℝ) ≤ 5 * W then 1 else 0
    have hterm_le : ∀ i j : Fin n,
        |d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))| ≤
          |d i| * |d j| * ind i j := fun i j => by
      by_cases hle : (p i : ℝ) * (p j : ℝ) ≤ 5 * W
      · simp only [ind, if_pos hle, mul_one, abs_mul, abs_of_nonneg (tentBump_nonneg _)]
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (tentBump_le_one _)
      · push Not at hle
        have hgt5 : Real.log 5 ≤ x + Real.log (p i) + Real.log (p j) := by
          have hpi0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
          have hpj0 : (0 : ℝ) < p j := by exact_mod_cast (hp j).pos
          have hexp_eq : Real.exp (x + Real.log (p i) + Real.log (p j)) =
              Real.exp x * ((p i : ℝ) * (p j : ℝ)) := by
            rw [add_assoc, Real.exp_add, Real.exp_add, Real.exp_log hpi0, Real.exp_log hpj0]
          have h5 : (5 : ℝ) ≤ Real.exp x * ((p i : ℝ) * (p j : ℝ)) := by
            have he1 : Real.exp x * W = 1 := by simp only [W, ← Real.exp_add]; simp
            nlinarith [Real.exp_pos x, hle]
          rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5), hexp_eq]
          exact h5
        simp [ind, if_neg (not_le.mpr hle), tentBump_eq_zero_of_ge_log_five hgt5]
    have hsum1 : |∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))| ≤
        ∑ i, ∑ j, |d i| * |d j| * ind i j := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm_le i j)
    have hamgm : ∀ i j : Fin n,
        2 * (|d i| * |d j| * ind i j) ≤
          (d i ^ 2 * Real.sqrt (p i : ℝ) * (Real.sqrt (p j : ℝ))⁻¹ +
            d j ^ 2 * Real.sqrt (p j : ℝ) * (Real.sqrt (p i : ℝ))⁻¹) * ind i j := fun i j => by
      have hind_nn : 0 ≤ ind i j := by simp only [ind]; split_ifs <;> norm_num
      rw [show 2 * (|d i| * |d j| * ind i j) = (2 * (|d i| * |d j|)) * ind i j by ring]
      refine mul_le_mul_of_nonneg_right ?_ hind_nn
      have hsi : 0 < Real.sqrt (p i : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hp i).pos)
      have hsj : 0 < Real.sqrt (p j : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hp j).pos)
      have hsq : 0 ≤ (|d i| * Real.sqrt (p i : ℝ) - |d j| * Real.sqrt (p j : ℝ)) ^ 2 := sq_nonneg _
      have hexp_sq : (|d i| * Real.sqrt (p i : ℝ) - |d j| * Real.sqrt (p j : ℝ)) ^ 2 =
          d i ^ 2 * (p i : ℝ) + d j ^ 2 * (p j : ℝ) -
            2 * (|d i| * |d j|) * (Real.sqrt (p i : ℝ) * Real.sqrt (p j : ℝ)) := by
        have h1 : (Real.sqrt (p i : ℝ)) ^ 2 = (p i : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
        have h2 : (Real.sqrt (p j : ℝ)) ^ 2 = (p j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
        have h3 : |d i| ^ 2 = d i ^ 2 := sq_abs _
        have h4 : |d j| ^ 2 = d j ^ 2 := sq_abs _
        nlinarith
      have hdiv : 2 * (|d i| * |d j|) ≤
          (d i ^ 2 * (p i : ℝ) + d j ^ 2 * (p j : ℝ)) / (Real.sqrt (p i : ℝ) * Real.sqrt (p j : ℝ)) := by
        rw [le_div_iff₀ (mul_pos hsi hsj)]; linarith
      refine hdiv.trans_eq ?_
      rw [div_eq_iff (mul_pos hsi hsj).ne']
      have h1 : Real.sqrt (p i : ℝ) * Real.sqrt (p i : ℝ) = (p i : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      have h2 : Real.sqrt (p j : ℝ) * Real.sqrt (p j : ℝ) = (p j : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      have hi_inv : (Real.sqrt (p i : ℝ))⁻¹ * Real.sqrt (p i : ℝ) = 1 := inv_mul_cancel₀ hsi.ne'
      have hj_inv : (Real.sqrt (p j : ℝ))⁻¹ * Real.sqrt (p j : ℝ) = 1 := inv_mul_cancel₀ hsj.ne'
      calc d i ^ 2 * (p i : ℝ) + d j ^ 2 * (p j : ℝ)
          = d i ^ 2 * (Real.sqrt (p i : ℝ) * Real.sqrt (p i : ℝ)) *
                ((Real.sqrt (p j : ℝ))⁻¹ * Real.sqrt (p j : ℝ)) +
              d j ^ 2 * (Real.sqrt (p j : ℝ) * Real.sqrt (p j : ℝ)) *
                ((Real.sqrt (p i : ℝ))⁻¹ * Real.sqrt (p i : ℝ)) := by
            rw [h1, h2, hi_inv, hj_inv]; ring
        _ = (d i ^ 2 * Real.sqrt (p i : ℝ) * (Real.sqrt (p j : ℝ))⁻¹ +
              d j ^ 2 * Real.sqrt (p j : ℝ) * (Real.sqrt (p i : ℝ))⁻¹) *
            (Real.sqrt (p i : ℝ) * Real.sqrt (p j : ℝ)) := by ring
    have hind_symm : ∀ i j : Fin n, ind j i = ind i j := fun i j => by
      simp only [ind, mul_comm (p j : ℝ) (p i : ℝ)]
    have hsum_symm : ∑ i, ∑ j, |d i| * |d j| * ind i j ≤
        ∑ i, d i ^ 2 * Real.sqrt (p i : ℝ) * ∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹ := by
      have h2sum : 2 * ∑ i, ∑ j, |d i| * |d j| * ind i j ≤
          ∑ i, ∑ j, (d i ^ 2 * Real.sqrt (p i : ℝ) * (Real.sqrt (p j : ℝ))⁻¹ * ind i j +
            d j ^ 2 * Real.sqrt (p j : ℝ) * (Real.sqrt (p i : ℝ))⁻¹ * ind i j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        linarith [hamgm i j]
      have hswap : (∑ i, ∑ j, d j ^ 2 * Real.sqrt (p j : ℝ) * (Real.sqrt (p i : ℝ))⁻¹ * ind i j) =
          ∑ i, ∑ j, d i ^ 2 * Real.sqrt (p i : ℝ) * (Real.sqrt (p j : ℝ))⁻¹ * ind i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hind_symm i j]
      have hsplit : (∑ i, ∑ j, (d i ^ 2 * Real.sqrt (p i : ℝ) * (Real.sqrt (p j : ℝ))⁻¹ * ind i j +
            d j ^ 2 * Real.sqrt (p j : ℝ) * (Real.sqrt (p i : ℝ))⁻¹ * ind i j)) =
          2 * ∑ i, d i ^ 2 * Real.sqrt (p i : ℝ) * ∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹ := by
        simp_rw [Finset.sum_add_distrib]
        rw [hswap, ← two_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    have hrow : ∀ i : Fin n,
        Real.sqrt (p i : ℝ) * (∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹) ≤
          2 * Real.sqrt 5 * Real.exp (-x / 2) := fun i => by
      set K : ℕ := ⌊5 * W / (p i : ℝ)⌋₊
      set S_i := Finset.univ.filter (fun j : Fin n => (p i : ℝ) * (p j : ℝ) ≤ 5 * W)
      have hfilter : (∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹) =
          ∑ j ∈ S_i, (Real.sqrt (p j : ℝ))⁻¹ := by
        simp only [ind, ite_mul, one_mul, zero_mul, S_i, Finset.sum_filter]
      have himg_sub : S_i.image p ⊆ Finset.Icc 1 K := fun m hm => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
        have hle := (Finset.mem_filter.mp hj).2
        have hpi0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
        have hpj_le : (p j : ℝ) ≤ 5 * W / (p i : ℝ) := by
          rw [le_div_iff₀ hpi0]; linarith
        exact Finset.mem_Icc.mpr ⟨(hp j).pos, Nat.le_floor hpj_le⟩
      have hsum_K : ∑ j ∈ S_i, (Real.sqrt (p j : ℝ))⁻¹ ≤ 2 * Real.sqrt (K : ℝ) := by
        have hinj_sum : ∑ j ∈ S_i, (Real.sqrt (p j : ℝ))⁻¹ =
            ∑ m ∈ S_i.image p, (Real.sqrt (m : ℝ))⁻¹ :=
          (Finset.sum_image (f := fun m : ℕ => (Real.sqrt (m : ℝ))⁻¹)
            fun a _ b _ hab => hinj hab).symm
        rw [hinj_sum]
        exact (Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans
          (sum_inv_sqrt_Icc_le K)
      have hpi0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hK_le : (K : ℝ) ≤ 5 * W / (p i : ℝ) :=
        Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) hW_pos.le) hpi0.le)
      rw [hfilter]
      calc Real.sqrt (p i : ℝ) * ∑ j ∈ S_i, (Real.sqrt (p j : ℝ))⁻¹
          ≤ Real.sqrt (p i : ℝ) * (2 * Real.sqrt (5 * W / (p i : ℝ))) :=
            mul_le_mul_of_nonneg_left (hsum_K.trans (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hK_le) two_pos.le)) (Real.sqrt_nonneg _)
        _ = 2 * (Real.sqrt (p i : ℝ) * Real.sqrt (5 * W / (p i : ℝ))) := by ring
        _ = 2 * Real.sqrt (5 * W) := by
            rw [← Real.sqrt_mul hpi0.le, mul_div_cancel₀ _ hpi0.ne']
        _ = 2 * Real.sqrt 5 * Real.exp (-x / 2) := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt W = Real.exp (-x / 2) by
              simp only [W]
              rw [← Real.sqrt_sq (Real.exp_pos (-x / 2)).le]
              congr 1
              rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
            ring
    refine hsum1.trans (hsum_symm.trans ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hdi : 0 ≤ d i ^ 2 := sq_nonneg _
    calc d i ^ 2 * Real.sqrt (p i : ℝ) * ∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹
        = d i ^ 2 * (Real.sqrt (p i : ℝ) * ∑ j, ind i j * (Real.sqrt (p j : ℝ))⁻¹) := by ring
      _ ≤ d i ^ 2 * (2 * Real.sqrt 5 * Real.exp (-x / 2)) := mul_le_mul_of_nonneg_left (hrow i) hdi
      _ = 2 * Real.sqrt 5 * Real.exp (-x / 2) * d i ^ 2 := by ring

/-- **Exact intermediate transition at `κ = ½`.** For every `κ ≥ ½` (including `κ = ½` itself),
small `tentBump` perturbations of `e^{−κy}` remain all-base Level-1 Hecke positive while violating
`IsExpConvexFrom 0`, and throughout `κ ∈ [½, 1]` they simultaneously violate `IsAllBaseTorusPositive`
at `x = 0`. -/
theorem exists_heckePositive_not_torusPositive_ge_half {κ : ℝ} (hκ : 1 / 2 ≤ κ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      let f : ℝ → ℝ := fun y => Real.exp (-κ * y) - ε * tentBump y
      Continuous f ∧
      (∀ x₀, ExpDecayFrom x₀ κ f) ∧
      (∀ y, y ≤ 0 → |f y| ≤ (1 + ε * (5 : ℝ) ^ κ) * Real.exp (-κ * y)) ∧
      IsAllBaseHeckePositive f ∧
      ¬ IsExpConvexFrom 0 f ∧
      (κ ≤ 1 → ¬ IsAllBaseTorusPositive f) := by
  have hκ0 : 0 < κ := by linarith
  set K_κ : ℝ := (5 : ℝ) ^ κ + 2 * Real.sqrt 5 * (5 / 4 : ℝ) ^ (κ - 1 / 2)
  have hK_pos : 0 < K_κ := by positivity
  set ε₀ : ℝ := (2 * K_κ)⁻¹
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, fun ε hε0 hε_le => ?_⟩
  intro f
  have hf_cont : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_tentBump)
  have hf_bd : ∀ y : ℝ, |f y| ≤ (1 + ε * (5 : ℝ) ^ κ) * Real.exp (-κ * y) := fun y => by
    have htri : |Real.exp (-κ * y) - ε * tentBump y| ≤ Real.exp (-κ * y) + ε * |tentBump y| := by
      have h := abs_sub_le (Real.exp (-κ * y)) 0 (ε * tentBump y)
      rwa [sub_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos hε0] at h
    calc |f y| ≤ Real.exp (-κ * y) + ε * ((5 : ℝ) ^ κ * Real.exp (-κ * y)) :=
          htri.trans (add_le_add_right (mul_le_mul_of_nonneg_left
            (tentBump_le_five_rpow_exp hκ0 y) hε0.le) _)
      _ = (1 + ε * (5 : ℝ) ^ κ) * Real.exp (-κ * y) := by ring
  refine ⟨hf_cont, fun x₀ => ⟨1 + ε * (5 : ℝ) ^ κ, by positivity, fun y _ => hf_bd y⟩,
    fun y _ => hf_bd y, ?_, ?_, ?_⟩
  · -- All-base Level-1 Hecke positivity
    intro n p hp hinj x d
    have hexp_hecke : Real.exp (-κ * x) * ∑ i, d i ^ 2 ≤
        Real.exp (-κ * x) * ∑ i, d i ^ 2 +
          ∑ i, ∑ j, d i * d j * Real.exp (-κ * (x + Real.log (p i) + Real.log (p j))) := by
      have hsq : ∑ i, ∑ j, d i * d j * Real.exp (-κ * (x + Real.log (p i) + Real.log (p j))) =
          Real.exp (-κ * x) * (∑ i, d i * Real.exp (-κ * Real.log (p i))) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have he : Real.exp (-κ * (x + Real.log (p i) + Real.log (p j))) =
            Real.exp (-κ * x) * Real.exp (-κ * Real.log (p i)) * Real.exp (-κ * Real.log (p j)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [he]; ring
      rw [hsq]
      linarith [mul_nonneg (Real.exp_pos (-κ * x)).le (sq_nonneg (∑ i, d i * Real.exp (-κ * Real.log (p i))))]
    have hpert_le : |tentBump x * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))| ≤
        K_κ * Real.exp (-κ * x) * ∑ i, d i ^ 2 := by
      have hd_nn : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hdiag_b : |tentBump x * ∑ i, d i ^ 2| ≤ (5 : ℝ) ^ κ * Real.exp (-κ * x) * ∑ i, d i ^ 2 := by
        rw [abs_mul, abs_of_nonneg hd_nn]
        exact mul_le_mul_of_nonneg_right (tentBump_le_five_rpow_exp hκ0 x) hd_nn
      have h2_b : |∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))| ≤
          2 * Real.sqrt 5 * (5 / 4 : ℝ) ^ (κ - 1 / 2) * Real.exp (-κ * x) * ∑ i, d i ^ 2 := by
        refine (abs_tentBump_prime_double_sum_le hp hinj x d).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hd_nn
        split_ifs with hx
        · positivity
        · push Not at hx
          have hexp_cmp : Real.exp (-x / 2) ≤ (5 / 4 : ℝ) ^ (κ - 1 / 2) * Real.exp (-κ * x) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 4), ← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith)
          calc 2 * Real.sqrt 5 * Real.exp (-x / 2)
              ≤ 2 * Real.sqrt 5 * ((5 / 4 : ℝ) ^ (κ - 1 / 2) * Real.exp (-κ * x)) :=
                mul_le_mul_of_nonneg_left hexp_cmp (by positivity)
            _ = _ := by ring
      refine (abs_add_le _ _).trans ?_
      calc |tentBump x * ∑ i, d i ^ 2| +
              |∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))|
          ≤ (5 : ℝ) ^ κ * Real.exp (-κ * x) * ∑ i, d i ^ 2 +
              2 * Real.sqrt 5 * (5 / 4 : ℝ) ^ (κ - 1 / 2) * Real.exp (-κ * x) * ∑ i, d i ^ 2 :=
            add_le_add hdiag_b h2_b
        _ = K_κ * Real.exp (-κ * x) * ∑ i, d i ^ 2 := by simp only [K_κ]; ring
    have hsplit_f : f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + Real.log (p i) + Real.log (p j)) =
        (Real.exp (-κ * x) * ∑ i, d i ^ 2 +
          ∑ i, ∑ j, d i * d j * Real.exp (-κ * (x + Real.log (p i) + Real.log (p j)))) -
        ε * (tentBump x * ∑ i, d i ^ 2 +
          ∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))) := by
      have hsum_f : (∑ i, ∑ j, d i * d j * f (x + Real.log (p i) + Real.log (p j))) =
          (∑ i, ∑ j, d i * d j * Real.exp (-κ * (x + Real.log (p i) + Real.log (p j)))) -
            ε * ∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by dsimp only [f]; ring
      rw [hsum_f]; dsimp only [f]; ring
    rw [hsplit_f]
    have hεK : ε * K_κ ≤ 1 / 2 := by
      have : ε ≤ (2 * K_κ)⁻¹ := hε_le
      calc ε * K_κ ≤ (2 * K_κ)⁻¹ * K_κ := mul_le_mul_of_nonneg_right this hK_pos.le
        _ = 1 / 2 := by field_simp [hK_pos.ne']
    have hd_nn : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 := (le_abs_self _).trans hpert_le
    have h2 : ε * (tentBump x * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j))) ≤
        (1 / 2) * (Real.exp (-κ * x) * ∑ i, d i ^ 2) := by
      calc ε * (tentBump x * ∑ i, d i ^ 2 +
              ∑ i, ∑ j, d i * d j * tentBump (x + Real.log (p i) + Real.log (p j)))
          ≤ ε * (K_κ * Real.exp (-κ * x) * ∑ i, d i ^ 2) := mul_le_mul_of_nonneg_left h1 hε0.le
        _ = (ε * K_κ) * (Real.exp (-κ * x) * ∑ i, d i ^ 2) := by ring
        _ ≤ (1 / 2) * (Real.exp (-κ * x) * ∑ i, d i ^ 2) :=
          mul_le_mul_of_nonneg_right hεK (mul_nonneg (Real.exp_pos _).le hd_nn)
    linarith [mul_nonneg (Real.exp_pos (-κ * x)).le hd_nn]
  · -- Violation of `IsExpConvexFrom 0` on `(log 2, log 3)`
    intro hconv
    let t : Fin 2 → ℝ := ![Real.log 2, Real.log 3]
    let c : Fin 2 → ℂ := ![(Real.exp (-κ * Real.log 3) : ℂ), -(Real.exp (-κ * Real.log 2) : ℂ)]
    have hform := hconv (Fin 2) Finset.univ t c fun i _ => by
      fin_cases i <;> exact Real.log_nonneg (by norm_num)
    have ht_22 : f (0 + t 0 + t 0) = Real.exp (-κ * (2 * Real.log 2)) - ε := by
      simp only [f, t, Matrix.cons_val_zero, zero_add, ← two_mul, tentBump_two_log_two, mul_one]
    have ht_23 : f (0 + t 0 + t 1) = Real.exp (-κ * (Real.log 2 + Real.log 3)) := by
      have hge5 : Real.log 5 ≤ Real.log 2 + Real.log 3 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      simp only [f, t, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add,
        tentBump_eq_zero_of_ge_log_five hge5, mul_zero, sub_zero]
    have ht_32 : f (0 + t 1 + t 0) = Real.exp (-κ * (Real.log 2 + Real.log 3)) := by
      rw [show 0 + t 1 + t 0 = 0 + t 0 + t 1 by ring, ht_23]
    have ht_33 : f (0 + t 1 + t 1) = Real.exp (-κ * (2 * Real.log 3)) := by
      have hge5 : Real.log 5 ≤ 2 * Real.log 3 := by
        have : 2 * Real.log 3 = Real.log 9 := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        rw [this]; exact Real.log_le_log (by norm_num) (by norm_num)
      simp only [f, t, Matrix.cons_val_one, Matrix.cons_val_zero, zero_add, ← two_mul,
        tentBump_eq_zero_of_ge_log_five hge5, mul_zero, sub_zero]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hform
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_neg, Complex.conj_ofReal, ht_22, ht_23, ht_32, ht_33] at hform
    have heq_re : (((Real.exp (-κ * Real.log 3) : ℂ) * (Real.exp (-κ * Real.log 3) : ℂ) *
          ((Real.exp (-κ * (2 * Real.log 2)) - ε : ℝ) : ℂ) +
        (Real.exp (-κ * Real.log 3) : ℂ) * -(Real.exp (-κ * Real.log 2) : ℂ) *
          (Real.exp (-κ * (Real.log 2 + Real.log 3)) : ℂ)) +
        (-(Real.exp (-κ * Real.log 2) : ℂ) * (Real.exp (-κ * Real.log 3) : ℂ) *
          (Real.exp (-κ * (Real.log 2 + Real.log 3)) : ℂ) +
        -(Real.exp (-κ * Real.log 2) : ℂ) * -(Real.exp (-κ * Real.log 2) : ℂ) *
          (Real.exp (-κ * (2 * Real.log 3)) : ℂ))).re =
        -ε * Real.exp (-κ * Real.log 3) ^ 2 := by
      have hprod1 : Real.exp (-κ * Real.log 3) * Real.exp (-κ * Real.log 3) *
          Real.exp (-κ * (2 * Real.log 2)) =
          Real.exp (-2 * κ * (Real.log 2 + Real.log 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hprod2 : Real.exp (-κ * Real.log 3) * Real.exp (-κ * Real.log 2) *
          Real.exp (-κ * (Real.log 2 + Real.log 3)) =
          Real.exp (-2 * κ * (Real.log 2 + Real.log 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hprod3 : Real.exp (-κ * Real.log 2) * Real.exp (-κ * Real.log 2) *
          Real.exp (-κ * (2 * Real.log 3)) =
          Real.exp (-2 * κ * (Real.log 2 + Real.log 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, Complex.ofReal_re]
      linarith [hprod1, hprod2, hprod3, sq (Real.exp (-κ * Real.log 3))]
    rw [heq_re] at hform
    have hneg : -ε * Real.exp (-κ * Real.log 3) ^ 2 < 0 := by
      have : 0 < ε * Real.exp (-κ * Real.log 3) ^ 2 :=
        mul_pos hε0 (pow_pos (Real.exp_pos _) 2)
      linarith
    linarith
  · -- Violation of `IsAllBaseTorusPositive` on `κ ∈ [½, 1]`
    intro hκ1 htorus
    obtain ⟨n, p, θ, hp, hinj, hneg⟩ := exists_prime_set_torusSum_neg_of_le_one hκ0 hκ1
      (fun y _ => mul_nonneg hε0.le (tentBump_nonneg y))
      (fun y hy => by rw [tentBump_eq_zero_of_ge_log_five hy, mul_zero])
      (by rw [tentBump_two_log_two, mul_one]; exact hε0)
    exact absurd (htorus n p hp hinj 0 θ) (not_le.mpr hneg)

/-! ### 3. `SU(2)` Poisson–Szegő kernel and complete-monotonicity module law -/

/-- The positive `SU(2)` Poisson–Szegő reproducing kernel for `|r| < 1`. -/
def su2PoissonKernel (r θ φ : ℝ) : ℝ :=
  (1 - r ^ 2) / ((1 - 2 * r * Real.cos (θ - φ) + r ^ 2) * (1 - 2 * r * Real.cos (θ + φ) + r ^ 2))

private theorem quad_cos_pos {r α : ℝ} (hr : |r| < 1) :
    0 < 1 - 2 * r * Real.cos α + r ^ 2 := by
  have hr1 := (abs_lt.mp hr).1
  have hr2 := (abs_lt.mp hr).2
  have hc1 := Real.neg_one_le_cos α
  have hc2 := Real.cos_le_one α
  rcases le_or_gt 0 r with hr0 | hr0
  · have hsq : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
    nlinarith
  · have hsq : 0 < (1 + r) ^ 2 := sq_pos_of_ne_zero (by linarith)
    nlinarith

theorem su2PoissonKernel_pos {r : ℝ} (hr : |r| < 1) (θ φ : ℝ) :
    0 < su2PoissonKernel r θ φ := by
  unfold su2PoissonKernel
  have hr2 : r ^ 2 < 1 := by
    have := abs_lt.mp hr
    nlinarith
  exact div_pos (by linarith) (mul_pos (quad_cos_pos hr) (quad_cos_pos hr))

/-- **Exact `SU(2)` Poisson–Szegő identity.** -/
theorem hasSum_cosSum_mul_cosSum_geom {r : ℝ} (hr : |r| < 1) (θ φ : ℝ) :
    HasSum (fun k : ℕ => r ^ k * cosSum θ k * cosSum φ k) (su2PoissonKernel r θ φ) := by
  set c₁ := 2 * Real.cos θ
  set c₂ := 2 * Real.cos φ
  set u : ℕ → ℝ := fun k => cosSum θ k * cosSum φ k
  have hnorm : ‖(‖r‖ : ℝ)‖ < 1 := by simpa [Real.norm_eq_abs] using hr
  have hsum_u : Summable (fun k : ℕ => r ^ k * u k) := by
    have h0 := summable_geometric_of_norm_lt_one hnorm
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
    have hmaj : Summable (fun k : ℕ =>
        (k : ℝ) ^ 2 * ‖r‖ ^ k + 2 * ((k : ℝ) ^ 1 * ‖r‖ ^ k) + ‖r‖ ^ k) :=
      (h2.add (h1.mul_left 2)).add h0
    refine Summable.of_norm_bounded hmaj fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_eq_abs (u k)]
    have hb : |u k| ≤ ((k : ℝ) + 1) ^ 2 := by
      dsimp only [u]
      rw [abs_mul, sq]
      exact mul_le_mul (abs_cosSum_le θ k) (abs_cosSum_le φ k) (abs_nonneg _) (by positivity)
    calc ‖r‖ ^ k * |u k| ≤ ‖r‖ ^ k * ((k : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg r) k)
      _ = (k : ℝ) ^ 2 * ‖r‖ ^ k + 2 * ((k : ℝ) ^ 1 * ‖r‖ ^ k) + ‖r‖ ^ k := by rw [pow_one]; ring
  -- Shift lemma for `∑' k, r^k * v k`
  have hshift : ∀ {v : ℕ → ℝ}, Summable (fun k => r ^ k * v k) →
      Summable (fun k => r ^ k * v (k + 1)) ∧
        (∑' k : ℕ, r ^ k * v k) = v 0 + r * ∑' k : ℕ, r ^ k * v (k + 1) := by
    intro v hv
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨summable_of_ne_finset_zero (s := {0}) fun k hk => ?_, ?_⟩
      · have hk0 : k ≠ 0 := fun h => hk (Finset.mem_singleton.mpr h)
        simp [zero_pow hk0]
      · rw [zero_mul, add_zero, tsum_eq_single 0]
        · simp
        · intro k hk; simp [zero_pow hk]
    · have hv1 : Summable (fun k : ℕ => r ^ (k + 1) * v (k + 1)) :=
        (summable_nat_add_iff 1).mpr hv
      have hv1' : Summable (fun k : ℕ => r ^ k * v (k + 1)) := by
        have := hv1.mul_left r⁻¹
        refine this.congr fun k => ?_
        rw [pow_succ']; field_simp [hr0]
      refine ⟨hv1', ?_⟩
      rw [hv.tsum_eq_zero_add, pow_zero, one_mul, ← tsum_mul_left]
      congr 1; exact tsum_congr fun k => by rw [pow_succ']; ring
  obtain ⟨hs1, heq0⟩ := hshift hsum_u
  obtain ⟨hs2, heq1⟩ := hshift hs1
  obtain ⟨hs3, heq2⟩ := hshift hs2
  obtain ⟨hs4, heq3⟩ := hshift hs3
  -- Fourth-order recurrence of `u k = cosSum θ k * cosSum φ k`
  have hrec : ∀ k : ℕ,
      u (k + 4) - c₁ * c₂ * u (k + 3) + (c₁ ^ 2 + c₂ ^ 2 - 2) * u (k + 2) -
        c₁ * c₂ * u (k + 1) + u k = 0 := fun k => by
    have step : ∀ α : ℝ,
        cosSum α (k + 2) = (2 * Real.cos α) * cosSum α (k + 1) - cosSum α k ∧
        cosSum α (k + 3) = ((2 * Real.cos α) ^ 2 - 1) * cosSum α (k + 1) -
          (2 * Real.cos α) * cosSum α k ∧
        cosSum α (k + 4) = ((2 * Real.cos α) ^ 3 - 2 * (2 * Real.cos α)) * cosSum α (k + 1) -
          ((2 * Real.cos α) ^ 2 - 1) * cosSum α k := fun α => by
      have h2 := cosSum_add_two α k
      have h3 := cosSum_add_two α (k + 1)
      have h4 := cosSum_add_two α (k + 2)
      refine ⟨h2, ?_, ?_⟩
      · rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega, h2] at h3
        linarith
      · have h3' : cosSum α (k + 3) = ((2 * Real.cos α) ^ 2 - 1) * cosSum α (k + 1) -
            (2 * Real.cos α) * cosSum α k := by
          rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega, h2] at h3
          linarith
        rw [show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega, h3', h2] at h4
        linarith
    obtain ⟨t2, t3, t4⟩ := step θ
    obtain ⟨p2, p3, p4⟩ := step φ
    dsimp only [u, c₁, c₂]
    rw [t2, t3, t4, p2, p3, p4]
    ring
  -- Initial values `u 0, u 1, u 2, u 3`
  have hu0 : u 0 = 1 := by simp [u, cosSum_zero]
  have hu1 : u 1 = c₁ * c₂ := by simp [u, c₁, c₂, cosSum_one]
  have hu2 : u 2 = (c₁ ^ 2 - 1) * (c₂ ^ 2 - 1) := by
    have hθ := cosSum_add_two θ 0
    have hφ := cosSum_add_two φ 0
    simp only [zero_add, cosSum_zero, cosSum_one] at hθ hφ
    dsimp only [u, c₁, c₂]; rw [hθ, hφ]; ring
  have hu3 : u 3 = (c₁ ^ 3 - 2 * c₁) * (c₂ ^ 3 - 2 * c₂) := by
    have hθ2 := cosSum_add_two θ 0
    have hθ3 := cosSum_add_two θ 1
    have hφ2 := cosSum_add_two φ 0
    have hφ3 := cosSum_add_two φ 1
    simp only [zero_add, cosSum_zero, cosSum_one] at hθ2 hφ2
    rw [show 1 + 2 = 3 by omega, show 1 + 1 = 2 by omega, hθ2, cosSum_one] at hθ3
    rw [show 1 + 2 = 3 by omega, show 1 + 1 = 2 by omega, hφ2, cosSum_one] at hφ3
    dsimp only [u, c₁, c₂]; rw [hθ3, hφ3]; ring
  set S := ∑' k : ℕ, r ^ k * u k
  set S₁ := ∑' k : ℕ, r ^ k * u (k + 1)
  set S₂ := ∑' k : ℕ, r ^ k * u (k + 2)
  set S₃ := ∑' k : ℕ, r ^ k * u (k + 3)
  set S₄ := ∑' k : ℕ, r ^ k * u (k + 4)
  have hcomb_tail : S₄ - c₁ * c₂ * S₃ + (c₁ ^ 2 + c₂ ^ 2 - 2) * S₂ - c₁ * c₂ * S₁ + S = 0 := by
    have ht1 : c₁ * c₂ * S₃ = ∑' k : ℕ, r ^ k * (c₁ * c₂ * u (k + 3)) := by
      rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
    have ht2 : (c₁ ^ 2 + c₂ ^ 2 - 2) * S₂ =
        ∑' k : ℕ, r ^ k * ((c₁ ^ 2 + c₂ ^ 2 - 2) * u (k + 2)) := by
      rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
    have ht3 : c₁ * c₂ * S₁ = ∑' k : ℕ, r ^ k * (c₁ * c₂ * u (k + 1)) := by
      rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
    have hs3' : Summable (fun k => r ^ k * (c₁ * c₂ * u (k + 3))) :=
      (hs3.mul_left (c₁ * c₂)).congr fun k => by ring
    have hs2' : Summable (fun k => r ^ k * ((c₁ ^ 2 + c₂ ^ 2 - 2) * u (k + 2))) :=
      (hs2.mul_left (c₁ ^ 2 + c₂ ^ 2 - 2)).congr fun k => by ring
    have hs1' : Summable (fun k => r ^ k * (c₁ * c₂ * u (k + 1))) :=
      (hs1.mul_left (c₁ * c₂)).congr fun k => by ring
    change (∑' k, r ^ k * u (k + 4)) - c₁ * c₂ * S₃ + (c₁ ^ 2 + c₂ ^ 2 - 2) * S₂ -
      c₁ * c₂ * S₁ + (∑' k, r ^ k * u k) = 0
    rw [ht1, ht2, ht3, ← hs4.tsum_sub hs3', ← (hs4.sub hs3').tsum_add hs2',
      ← ((hs4.sub hs3').add hs2').tsum_sub hs1',
      ← (((hs4.sub hs3').add hs2').sub hs1').tsum_add hsum_u]
    have hz : ∀ k : ℕ, r ^ k * u (k + 4) - r ^ k * (c₁ * c₂ * u (k + 3)) +
        r ^ k * ((c₁ ^ 2 + c₂ ^ 2 - 2) * u (k + 2)) - r ^ k * (c₁ * c₂ * u (k + 1)) +
        r ^ k * u k = 0 := fun k => by linear_combination r ^ k * hrec k
    simp [hz]
  have hD_fact : (1 - 2 * r * Real.cos (θ - φ) + r ^ 2) * (1 - 2 * r * Real.cos (θ + φ) + r ^ 2) =
      1 - c₁ * c₂ * r + (c₁ ^ 2 + c₂ ^ 2 - 2) * r ^ 2 - c₁ * c₂ * r ^ 3 + r ^ 4 := by
    rw [Real.cos_sub, Real.cos_add]
    have hss : (Real.sin θ * Real.sin φ) ^ 2 =
        (1 - Real.cos θ ^ 2) * (1 - Real.cos φ ^ 2) := by
      rw [mul_pow, Real.sin_sq, Real.sin_sq]
    dsimp only [c₁, c₂]
    linear_combination -4 * r ^ 2 * hss
  have hDS : ((1 - 2 * r * Real.cos (θ - φ) + r ^ 2) *
      (1 - 2 * r * Real.cos (θ + φ) + r ^ 2)) * S = 1 - r ^ 2 := by
    rw [hD_fact]
    change _ = _ at heq0 heq1 heq2 heq3
    rw [hu0] at heq0
    rw [hu1] at heq1
    rw [hu2] at heq2
    rw [hu3] at heq3
    linear_combination r ^ 4 * hcomb_tail +
      (1 - c₁ * c₂ * r + (c₁ ^ 2 + c₂ ^ 2 - 2) * r ^ 2 - c₁ * c₂ * r ^ 3) * heq0 +
      (r - c₁ * c₂ * r ^ 2 + (c₁ ^ 2 + c₂ ^ 2 - 2) * r ^ 3) * heq1 +
      (r ^ 2 - c₁ * c₂ * r ^ 3) * heq2 + r ^ 3 * heq3
  have hD_pos : 0 < (1 - 2 * r * Real.cos (θ - φ) + r ^ 2) *
      (1 - 2 * r * Real.cos (θ + φ) + r ^ 2) :=
    mul_pos (quad_cos_pos hr) (quad_cos_pos hr)
  have hS_eq : S = su2PoissonKernel r θ φ := by
    unfold su2PoissonKernel
    rw [eq_div_iff hD_pos.ne', mul_comm]
    exact hDS
  have hsum_u' : HasSum (fun k : ℕ => r ^ k * cosSum θ k * cosSum φ k) S := by
    simpa only [u, mul_assoc] using hsum_u.hasSum
  rwa [hS_eq] at hsum_u'

/-- Multi-index product of norm-summable series over `Fin n → ℕ`. -/
theorem hasSum_pi_prod_of_summable_norm {α : Type*} [NormedCommRing α] [CompleteSpace α]
    {n : ℕ} (g : Fin n → ℕ → α) (s : Fin n → α)
    (hnorm : ∀ i, Summable fun k => ‖g i k‖) (hs : ∀ i, HasSum (g i) (s i)) :
    Summable (fun k : Fin n → ℕ => ‖∏ i, g i (k i)‖) ∧
      HasSum (fun k : Fin n → ℕ => ∏ i, g i (k i)) (∏ i, s i) := by
  induction n with
  | zero =>
    haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨hasSum_fintype _ |>.summable,
      hasSum_single default fun b hb => absurd (Subsingleton.elim b default) hb⟩
  | succ n ih =>
    obtain ⟨hihn, hih⟩ := ih (fun i => g i.succ) (fun i => s i.succ)
      (fun i => hnorm i.succ) (fun i => hs i.succ)
    have hmn_norm : Summable (fun x : ℕ × (Fin n → ℕ) =>
        ‖g 0 x.1‖ * ‖∏ i : Fin n, g i.succ (x.2 i)‖) :=
      (hnorm 0).mul_of_nonneg hihn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hprod_norm : Summable (fun k : Fin (n + 1) → ℕ => ‖∏ i, g i (k i)‖) := by
      have hcomp := (consEquiv n).summable_iff.mpr hmn_norm
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hcomp
      simp only [Function.comp_apply, Fin.prod_univ_succ, consEquiv, Equiv.coe_fn_mk, Fin.tail]
      exact norm_mul_le _ _
    have hmul_sum : HasSum (fun x : ℕ × (Fin n → ℕ) =>
        g 0 x.1 * ∏ i : Fin n, g i.succ (x.2 i)) (s 0 * ∏ i : Fin n, s i.succ) := by
      have hsm : Summable (fun x : ℕ × (Fin n → ℕ) =>
          g 0 x.1 * ∏ i : Fin n, g i.succ (x.2 i)) :=
        Summable.of_norm_bounded hmn_norm fun x => norm_mul_le _ _
      rw [← (hs 0).tsum_eq, ← hih.tsum_eq, tsum_mul_tsum_of_summable_norm (hnorm 0) hihn]
      exact hsm.hasSum
    have h2 := (consEquiv n).hasSum_iff.mpr hmul_sum
    have e1 : (fun k : Fin (n + 1) → ℕ => ∏ i, g i (k i)) =
        (fun x : ℕ × (Fin n → ℕ) => g 0 x.1 * ∏ i : Fin n, g i.succ (x.2 i)) ∘ consEquiv n := by
      funext k
      simp only [Function.comp_apply, Fin.prod_univ_succ, consEquiv, Equiv.coe_fn_mk, Fin.tail]
    rw [e1, Fin.prod_univ_succ]
    exact ⟨hprod_norm, h2⟩

/-- **Coordinatewise contraction preserves torus positivity.** Multiplying a trace-summable
torus-positive array `a k` by `∏_i (r i)^{k_i}` (`|r i| < 1`) expresses the new torus sum as a
positive `SU(2)` Poisson–Szegő integral over `torusMeasure n`. -/
theorem torusSum_mul_geom_eq_integral {n : ℕ} {a : (Fin n → ℕ) → ℝ} (ha : TraceSummable a)
    {r : Fin n → ℝ} (hr : ∀ i, |r i| < 1) (θ : Fin n → ℝ) :
    TraceSummable (fun k => a k * ∏ i, r i ^ (k i)) ∧
      torusSum (fun k => a k * ∏ i, r i ^ (k i)) θ =
        ∫ φ, torusSum a φ * (∏ i, su2PoissonKernel (r i) (θ i) (φ i)) ∂(torusMeasure n) := by
  have hr_le : ∀ i, |r i| ≤ 1 := fun i => (hr i).le
  have hts_ar : TraceSummable (fun k => a k * ∏ i, r i ^ (k i)) := by
    refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (chiSize_nonneg _))
      (fun k => ?_) ha
    rw [abs_mul, Finset.abs_prod]
    have hp1 : ∏ i, |r i ^ (k i)| ≤ 1 := by
      refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => ?_
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hr_le i)
    calc |a k| * (∏ i, |r i ^ (k i)|) * chiSize k
        ≤ |a k| * 1 * chiSize k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)) (chiSize_nonneg k)
      _ = |a k| * chiSize k := by ring
  set b : (Fin n → ℕ) → ℝ := fun k => (∏ i, r i ^ (k i)) * chiProd θ k
  have hts_b : TraceSummable b := by
    have hg : ∀ i : Fin n, Summable (fun m : ℕ => ‖(|r i| ^ m * ((m : ℝ) + 1) ^ 2 : ℝ)‖) := fun i => by
      have hn : ‖|r i|‖ < 1 := by simpa using hr i
      have h0 := summable_geometric_of_norm_lt_one hn
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
      have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
      refine ((h2.add (h1.mul_left 2)).add h0).congr fun m => ?_
      rw [Real.norm_of_nonneg (by positivity), pow_one]; ring
    obtain ⟨hbn, -⟩ := hasSum_pi_prod_of_summable_norm
      (fun i m => |r i| ^ m * ((m : ℝ) + 1) ^ 2)
      (fun i => ∑' m : ℕ, |r i| ^ m * ((m : ℝ) + 1) ^ 2) hg (fun i => (hg i).of_norm.hasSum)
    refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (chiSize_nonneg _))
      (fun k => ?_) hbn
    dsimp only [b]
    rw [abs_mul, Finset.abs_prod, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
    have hc : |chiProd θ k| * chiSize k ≤ ∏ i, ((k i : ℝ) + 1) ^ 2 := by
      calc |chiProd θ k| * chiSize k ≤ chiSize k * chiSize k :=
            mul_le_mul_of_nonneg_right (abs_chiProd_le θ k) (chiSize_nonneg k)
        _ = ∏ i, ((k i : ℝ) + 1) ^ 2 := by simp only [chiSize, ← Finset.prod_mul_distrib, sq]
    calc (∏ i, |r i ^ (k i)|) * |chiProd θ k| * chiSize k
        = (∏ i, |r i| ^ (k i)) * (|chiProd θ k| * chiSize k) := by
          simp_rw [abs_pow]; ring
      _ ≤ (∏ i, |r i| ^ (k i)) * ∏ i, ((k i : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hc (Finset.prod_nonneg fun _ _ => by positivity)
      _ = ∏ i, (|r i| ^ (k i) * ((k i : ℝ) + 1) ^ 2) := Finset.prod_mul_distrib.symm
  have hb_sum : ∀ φ : Fin n → ℝ,
      torusSum b φ = ∏ i, su2PoissonKernel (r i) (θ i) (φ i) := fun φ => by
    have hg_norm : ∀ i : Fin n,
        Summable (fun m : ℕ => ‖r i ^ m * cosSum (θ i) m * cosSum (φ i) m‖) := fun i => by
      have hn : ‖(‖r i‖ : ℝ)‖ < 1 := by simpa [Real.norm_eq_abs] using hr i
      have h0 := summable_geometric_of_norm_lt_one hn
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
      have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
        ((h2.add (h1.mul_left 2)).add h0)
      rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs (cosSum _ _), Real.norm_eq_abs (cosSum _ _)]
      calc ‖r i‖ ^ m * |cosSum (θ i) m| * |cosSum (φ i) m|
          ≤ ‖r i‖ ^ m * ((m : ℝ) + 1) * ((m : ℝ) + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (abs_cosSum_le _ _) (by positivity))
              (abs_cosSum_le _ _) (abs_nonneg _) (by positivity)
        _ = (m : ℝ) ^ 2 * ‖r i‖ ^ m + 2 * ((m : ℝ) ^ 1 * ‖r i‖ ^ m) + ‖r i‖ ^ m := by
            rw [pow_one]; ring
    obtain ⟨-, hprod⟩ := hasSum_pi_prod_of_summable_norm
      (fun i m => r i ^ m * cosSum (θ i) m * cosSum (φ i) m)
      (fun i => su2PoissonKernel (r i) (θ i) (φ i)) hg_norm
      (fun i => hasSum_cosSum_mul_cosSum_geom (hr i) (θ i) (φ i))
    rw [torusSum, ← hprod.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [b, chiProd, ← Finset.prod_mul_distrib]
  refine ⟨hts_ar, ?_⟩
  have hpair := integral_torusSum_mul_torusSum ha hts_b
  simp_rw [hb_sum] at hpair
  rw [hpair, torusSum]
  exact tsum_congr fun k => by dsimp only [b]; ring

/-- **Complete-monotonicity module law for all-base and fixed-base torus positivity.**
Multiplying any torus-positive amplitude `f` by `e^{−βy}` (`β ≥ 0`) preserves torus positivity. -/
theorem torusPositiveAt_mul_exp_neg {n : ℕ} {f : ℝ → ℝ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    {ℓ : Fin n → ℝ} (hℓ : ∀ i, 0 < ℓ i) {x : ℝ} (hd : ExpDecayFrom x κ₀ f)
    (hpos : ∀ φ : Fin n → ℝ, 0 ≤ torusSum (ampl f ℓ x) φ) {β : ℝ} (hβ : 0 ≤ β) (θ : Fin n → ℝ) :
    0 ≤ torusSum (ampl (fun y => f y * Real.exp (-β * y)) ℓ x) θ := by
  rcases hβ.eq_or_lt with rfl | hβ_pos
  · simpa using hpos θ
  · obtain ⟨C, -, hC⟩ := hd
    have ha : TraceSummable (ampl f ℓ x) := traceSummable_ampl hκ₀ hC hℓ le_rfl
    let r : Fin n → ℝ := fun i => Real.exp (-β * ℓ i)
    have hr : ∀ i, |r i| < 1 := fun i => by
      simp only [r, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
    obtain ⟨-, hid⟩ := torusSum_mul_geom_eq_integral ha hr θ
    have hampl_eq : ∀ k : Fin n → ℕ,
        ampl (fun y => f y * Real.exp (-β * y)) ℓ x k * chiProd θ k =
          Real.exp (-β * x) * ((ampl f ℓ x k * ∏ i, r i ^ (k i)) * chiProd θ k) := fun k => by
      simp only [ampl, r]
      have hexp : Real.exp (-β * (x + ∑ i, (k i : ℝ) * ℓ i)) =
          Real.exp (-β * x) * ∏ i, Real.exp (-β * ℓ i) ^ (k i) := by
        rw [mul_add, Real.exp_add]
        congr 1
        rw [mul_sum, Real.exp_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hexp]; ring
    rw [torusSum]
    simp_rw [hampl_eq]
    rw [tsum_mul_left, ← torusSum, hid]
    refine mul_nonneg (Real.exp_pos _).le (integral_nonneg fun φ => ?_)
    exact mul_nonneg (hpos φ) (Finset.prod_nonneg fun i _ => (su2PoissonKernel_pos (hr i) _ _).le)

theorem IsAllBaseTorusPositive.mul_exp_neg {f : ℝ → ℝ} {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) (hf : IsAllBaseTorusPositive f) {β : ℝ} (hβ : 0 ≤ β) :
    IsAllBaseTorusPositive (fun y => f y * Real.exp (-β * y)) := by
  intro n p hp hinj x θ
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  exact torusPositiveAt_mul_exp_neg hκ₀ hℓ (hd x) (hf n p hp hinj x) hβ θ

/-! ### 4. Shared complex generating function and oscillatory prime-window driver -/

/-- Exact complex generating series of `cosSum θ k` inside the open unit disc. -/
theorem hasSum_cosSum_mul_pow_complex {z : ℂ} (hz : ‖z‖ < 1) (θ : ℝ) :
    Summable (fun k : ℕ => ‖(cosSum θ k : ℂ) * z ^ k‖) ∧
      HasSum (fun k : ℕ => (cosSum θ k : ℂ) * z ^ k)
        ((1 - z * Complex.exp ((θ : ℂ) * I))⁻¹ * (1 - z * Complex.exp (-((θ : ℂ) * I)))⁻¹) := by
  have hnorm_sum : Summable (fun k : ℕ => ‖(cosSum θ k : ℂ) * z ^ k‖) := by
    have hzn : ‖(‖z‖ : ℝ)‖ < 1 := by simpa using hz
    have h0 := summable_geometric_of_norm_lt_one hzn
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hzn
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (h1.add h0)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    calc |cosSum θ k| * ‖z‖ ^ k ≤ ((k : ℝ) + 1) * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right (abs_cosSum_le θ k) (pow_nonneg (norm_nonneg z) k)
      _ = (k : ℝ) ^ 1 * ‖z‖ ^ k + ‖z‖ ^ k := by rw [pow_one]; ring
  refine ⟨hnorm_sum, ?_⟩
  set u : ℂ := z * Complex.exp ((θ : ℂ) * I)
  set v : ℂ := z * Complex.exp (-((θ : ℂ) * I))
  have hu : ‖u‖ < 1 := by simp [u, hz]
  have hv : ‖v‖ < 1 := by
    have h1 : ‖Complex.exp (-((θ : ℂ) * I))‖ = 1 := by
      simpa using Complex.norm_exp_ofReal_mul_I (-θ)
    rw [show v = z * Complex.exp (-((θ : ℂ) * I)) from rfl, norm_mul, h1, mul_one]
    exact hz
  have hs_pair : Summable (fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2) := by
    have hgu := (summable_geometric_of_norm_lt_one hu).norm
    have hgv := (summable_geometric_of_norm_lt_one hv).norm
    exact Summable.of_norm_bounded
      (hgu.mul_of_nonneg hgv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      fun _ => norm_mul_le _ _
  have htsum_pair : (∑' p : ℕ × ℕ, u ^ p.1 * v ^ p.2) = (1 - u)⁻¹ * (1 - v)⁻¹ := by
    rw [← tsum_mul_tsum_of_summable_norm (summable_geometric_of_norm_lt_one hu).norm
      (summable_geometric_of_norm_lt_one hv).norm,
      tsum_geometric_of_norm_lt_one hu, tsum_geometric_of_norm_lt_one hv]
  have eq_anti : (∑' k : ℕ, (cosSum θ k : ℂ) * z ^ k) = ∑' p : ℕ × ℕ, u ^ p.1 * v ^ p.2 := by
    have eq1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq
      (fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2)
    have hs' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hs_pair
    have hsig : (∑' c : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n),
        u ^ (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c).1 *
          v ^ (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c).2) =
        ∑' k : ℕ, ∑' c : ↥(Finset.HasAntidiagonal.antidiagonal k),
          u ^ (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨k, c⟩).1 *
            v ^ (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd ⟨k, c⟩).2 :=
      Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hs'
    rw [← eq1, hsig]
    refine tsum_congr fun k => ?_
    rw [tsum_fintype]
    change _ = ∑ c : ↥(Finset.HasAntidiagonal.antidiagonal k), u ^ (c : ℕ × ℕ).1 * v ^ (c : ℕ × ℕ).2
    rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal k) (fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2),
      ofReal_cosSum_eq_sum_antidiagonal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [← hpk, pow_add]
    simp only [u, v, mul_pow, ← Complex.exp_nat_mul]
    have hexp : Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) =
        Complex.exp ((p.1 : ℂ) * ((θ : ℂ) * I)) * Complex.exp ((p.2 : ℂ) * -((θ : ℂ) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  rw [← htsum_pair, ← eq_anti]
  exact hnorm_sum.of_norm.hasSum

/-- Multi-index complex generating series of `chiProd θ k`. -/
theorem hasSum_chiProd_mul_pow_complex {n : ℕ} {z : Fin n → ℂ} (hz : ∀ i, ‖z i‖ < 1)
    (θ : Fin n → ℝ) :
    HasSum (fun k : Fin n → ℕ => (chiProd θ k : ℂ) * ∏ i, z i ^ (k i))
      (∏ i, ((1 - z i * Complex.exp ((θ i : ℂ) * I))⁻¹ *
        (1 - z i * Complex.exp (-((θ i : ℂ) * I)))⁻¹)) := by
  obtain ⟨-, hsum⟩ := hasSum_pi_prod_of_summable_norm
    (fun i m => (cosSum (θ i) m : ℂ) * z i ^ m)
    (fun i => (1 - z i * Complex.exp ((θ i : ℂ) * I))⁻¹ *
      (1 - z i * Complex.exp (-((θ i : ℂ) * I)))⁻¹)
    (fun i => (hasSum_cosSum_mul_pow_complex (hz i) (θ i)).1)
    (fun i => (hasSum_cosSum_mul_pow_complex (hz i) (θ i)).2)
  refine hsum.congr_fun fun k => ?_
  simp only [chiProd, Complex.ofReal_prod, Finset.prod_mul_distrib]

private theorem sum_inv_Icc_ge_log (m₀ : ℕ) : ∀ K : ℕ,
    Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) ≤
      ∑ m ∈ Finset.Icc m₀ (m₀ + K), ((m : ℝ) + 1)⁻¹
  | 0 => by
    simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
    have hpos : (0 : ℝ) < (m₀ : ℝ) + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos (show 0 < ((m₀ + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ) by positivity)
    have hsub : ((m₀ + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ) - 1 = ((m₀ : ℝ) + 1)⁻¹ := by
      push_cast; field_simp [hpos.ne']; ring
    linarith
  | K + 1 => by
    have hmem : m₀ + (K + 1) ∉ Finset.Icc m₀ (m₀ + K) := by simp
    have hins : Finset.Icc m₀ (m₀ + (K + 1)) = insert (m₀ + (K + 1)) (Finset.Icc m₀ (m₀ + K)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert hmem]
    have ih := sum_inv_Icc_ge_log m₀ K
    have hpos1 : (0 : ℝ) < ((m₀ + K + 2 : ℕ) : ℝ) := by positivity
    have hpos0 : (0 : ℝ) < ((m₀ + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((m₀ + (K + 1) + 2 : ℕ) : ℝ) := by positivity
    have hstep : Real.log (((m₀ + (K + 1) + 2 : ℕ) : ℝ) / ((m₀ + K + 2 : ℕ) : ℝ)) ≤
        (((m₀ + (K + 1) : ℕ) : ℝ) + 1)⁻¹ := by
      have h := Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
      have hsub : ((m₀ + (K + 1) + 2 : ℕ) : ℝ) / ((m₀ + K + 2 : ℕ) : ℝ) - 1 =
          (((m₀ + (K + 1) : ℕ) : ℝ) + 1)⁻¹ := by
        have hd : (((m₀ + K + 2 : ℕ) : ℝ)) = ((m₀ + (K + 1) : ℕ) : ℝ) + 1 := by push_cast; ring
        have hn : (((m₀ + (K + 1) + 2 : ℕ) : ℝ)) = (((m₀ + (K + 1) : ℕ) : ℝ) + 1) + 1 := by
          push_cast; ring
        rw [hd, hn]
        have hdp : (0 : ℝ) < ((m₀ + (K + 1) : ℕ) : ℝ) + 1 := by positivity
        field_simp [hdp.ne']; ring
      linarith
    have hlog_add : Real.log (((m₀ + (K + 1) + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) =
        Real.log (((m₀ + (K + 1) + 2 : ℕ) : ℝ) / ((m₀ + K + 2 : ℕ) : ℝ)) +
          Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_mul (div_pos hpos2 hpos1).ne' (div_pos hpos1 hpos0).ne']
      congr 1
      field_simp [hpos1.ne', hpos0.ne']
    linarith

/-- On disjoint oscillatory prime windows where `cos(t log p) ≤ −½`, the product `∏_i (1 − p_i^{−α})`
becomes arbitrarily small for every `α ∈ (0, 1]` and `t ≠ 0`. -/
theorem exists_primes_cos_le_neg_half_prod_lt {α t δ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (ht : t ≠ 0) (hδ : 0 < δ) :
    ∃ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) ∧ Function.Injective p ∧
      (∀ i, Real.cos (t * Real.log (p i)) ≤ -1 / 2) ∧
      (∏ i, (1 - (p i : ℝ) ^ (-α))) < δ := by
  classical
  set τ : ℝ := |t|
  have hτ0 : 0 < τ := abs_pos.mpr ht
  set ε : ℝ := 2 * π / (3 * τ)
  have hε0 : 0 < ε := by positivity
  obtain ⟨c₁, hc₁, X₀, hX₀, hwin⟩ := exists_card_primes_window_ge hε0
  set X : ℕ → ℝ := fun m => Real.exp ((2 * π * (m : ℝ) + 2 * π / 3) / τ)
  have hX_pos : ∀ m, 0 < X m := fun _ => Real.exp_pos _
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (τ * |Real.log X₀| / (2 * π) + 1)
  have hXm₀ : ∀ m, m₀ ≤ m → X₀ ≤ X m ∧ 0 < Real.log (X m) ∧
      Real.log (X m) ≤ (2 * π / τ) * ((m : ℝ) + 1) := fun m hm => by
    have hm_cast : (m₀ : ℝ) ≤ m := Nat.cast_le.mpr hm
    have hlog_eq : Real.log (X m) = (2 * π * (m : ℝ) + 2 * π / 3) / τ := Real.log_exp _
    have hπ0 : 0 < 2 * π := by positivity
    have hgt : |Real.log X₀| < (2 * π * (m : ℝ) + 2 * π / 3) / τ := by
      have h1 : τ * |Real.log X₀| < 2 * π * (m₀ : ℝ) := by
        have := (mul_lt_mul_of_pos_left hm₀ hπ0)
        have heq : 2 * π * (τ * |Real.log X₀| / (2 * π) + 1) = τ * |Real.log X₀| + 2 * π := by
          field_simp [hπ0.ne']
        linarith
      rw [lt_div_iff₀ hτ0]
      have hm_mul := mul_le_mul_of_nonneg_left hm_cast hπ0.le
      linarith [Real.pi_pos, show |Real.log X₀| * τ = τ * |Real.log X₀| by ring]
    have hX0_le : X₀ ≤ X m := by
      rw [← Real.exp_log (by linarith : 0 < X₀)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans hgt.le)
    refine ⟨hX0_le, ?_, ?_⟩
    · rw [hlog_eq]; positivity
    · rw [hlog_eq, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hτ0.le
      linarith [Real.pi_pos]
  set W : ℕ → Finset ℕ := fun m => primesInIoc ⌊X m⌋₊ ⌊Real.exp ε * X m⌋₊
  have hper : ∀ (x : ℝ) (k : ℕ), Real.cos (x + 2 * π * (k : ℝ)) = Real.cos x := by
    intro x k; induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, show x + 2 * π * ((k : ℝ) + 1) = (x + 2 * π * (k : ℝ)) + 2 * π by ring,
        Real.cos_add_two_pi, ih]
  have hmemW : ∀ m q, q ∈ W m → q.Prime ∧
      (2 * π * (m : ℝ) + 2 * π / 3) / τ < Real.log q ∧
      Real.log q ≤ (2 * π * (m : ℝ) + 4 * π / 3) / τ ∧
      (q : ℝ) ≤ Real.exp ε * X m ∧
      Real.cos (t * Real.log q) ≤ -1 / 2 := fun m q hq => by
    have hq' := Finset.mem_filter.mp hq
    have hI := Finset.mem_Ioc.mp hq'.1
    have h1 : X m < q := Nat.lt_of_floor_lt hI.1
    have h2 : (q : ℝ) ≤ Real.exp ε * X m :=
      (Nat.cast_le.mpr hI.2).trans (Nat.floor_le (by positivity))
    have hq0 : (0 : ℝ) < q := lt_trans (hX_pos m) h1
    have hlo : (2 * π * (m : ℝ) + 2 * π / 3) / τ < Real.log q :=
      (Real.lt_log_iff_exp_lt hq0).mpr h1
    have hhi : Real.log q ≤ (2 * π * (m : ℝ) + 4 * π / 3) / τ := by
      have hexp_eq : Real.exp ε * X m = Real.exp ((2 * π * (m : ℝ) + 4 * π / 3) / τ) := by
        simp only [X, ε, ← Real.exp_add]
        congr 1; field_simp [hτ0.ne']; ring
      exact ((Real.log_le_iff_le_exp hq0).mpr (h2.trans_eq hexp_eq))
    have hlo' : 2 * π * (m : ℝ) + 2 * π / 3 < τ * Real.log q := by
      linarith [(div_lt_iff₀ hτ0).mp hlo]
    have hhi' : τ * Real.log q ≤ 2 * π * (m : ℝ) + 4 * π / 3 := by
      linarith [(le_div_iff₀ hτ0).mp hhi]
    set v : ℝ := τ * Real.log q - 2 * π * (m : ℝ) - π
    have hv_abs : |v| ≤ π / 3 := abs_le.mpr ⟨by simp only [v]; linarith, by simp only [v]; linarith⟩
    have hcos_v : 1 / 2 ≤ Real.cos v := by
      have hv_eq : Real.cos v = Real.cos |v| := by
        rcases le_or_gt 0 v with hv0 | hv0
        · rw [abs_of_nonneg hv0]
        · rw [abs_of_neg hv0, Real.cos_neg]
      rw [hv_eq, ← Real.cos_pi_div_three]
      exact Real.antitoneOn_cos ⟨abs_nonneg v, by linarith [Real.pi_pos]⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩ hv_abs
    have hcos_τ : Real.cos (τ * Real.log q) ≤ -1 / 2 := by
      have he : τ * Real.log q = (v + π) + 2 * π * (m : ℝ) := by simp only [v]; ring
      rw [he, hper, Real.cos_add_pi]
      linarith
    have hcos_t : Real.cos (t * Real.log q) = Real.cos (τ * Real.log q) := by
      simp only [τ]
      rcases le_or_gt 0 t with ht0 | ht0
      · rw [abs_of_nonneg ht0]
      · rw [abs_of_neg ht0, show (-t) * Real.log q = -(t * Real.log q) by ring, Real.cos_neg]
    exact ⟨hq'.2, hlo, hhi, h2, hcos_t ▸ hcos_τ⟩
  have hdisj : ∀ m₁ m₂ : ℕ, m₁ ≠ m₂ → Disjoint (W m₁) (W m₂) := by
    intro m₁ m₂ hne
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨-, hlo1, hhi1, -, -⟩ := hmemW m₁ q hq1
    obtain ⟨-, hlo2, hhi2, -, -⟩ := hmemW m₂ q hq2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm12 : (m₁ : ℝ) + 1 ≤ m₂ := by exact_mod_cast hlt
      have hcmp : (2 * π * (m₁ : ℝ) + 4 * π / 3) / τ < (2 * π * (m₂ : ℝ) + 2 * π / 3) / τ :=
        div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hτ0
      linarith
    · have hm21 : (m₂ : ℝ) + 1 ≤ m₁ := by exact_mod_cast hgt
      have hcmp : (2 * π * (m₂ : ℝ) + 4 * π / 3) / τ < (2 * π * (m₁ : ℝ) + 2 * π / 3) / τ :=
        div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hτ0
      linarith
  set γ : ℝ := c₁ * Real.exp (-ε) * (τ / (2 * π))
  have hγ_pos : 0 < γ := by positivity
  have hW_sum : ∀ m, m₀ ≤ m → γ * ((m : ℝ) + 1)⁻¹ ≤ ∑ q ∈ W m, (q : ℝ) ^ (-α) := fun m hm => by
    obtain ⟨hX0_le, hlog_pos, hlog_le⟩ := hXm₀ m hm
    have hcard := hwin (X m) hX0_le
    have hterm_ge : ∀ q ∈ W m, (Real.exp ε * X m)⁻¹ ≤ (q : ℝ) ^ (-α) := fun q hq => by
      obtain ⟨hqp, -, -, hq_le, -⟩ := hmemW m q hq
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqp.pos
      have hinv_le : (Real.exp ε * X m)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq_pos hq_le
      have hrpow_ge : (q : ℝ)⁻¹ ≤ (q : ℝ) ^ (-α) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      exact hinv_le.trans hrpow_ge
    have hsum1 : ((W m).card : ℝ) * (Real.exp ε * X m)⁻¹ ≤ ∑ q ∈ W m, (q : ℝ) ^ (-α) := by
      have := Finset.sum_le_sum hterm_ge
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hlog_inv : (τ / (2 * π)) * ((m : ℝ) + 1)⁻¹ ≤ (Real.log (X m))⁻¹ := by
      have hpos_rhs : 0 < (2 * π / τ) * ((m : ℝ) + 1) := by positivity
      have := inv_anti₀ hlog_pos hlog_le
      refine le_trans ?_ this
      rw [mul_inv, inv_div]
    calc γ * ((m : ℝ) + 1)⁻¹
        = (c₁ * X m * ((τ / (2 * π)) * ((m : ℝ) + 1)⁻¹)) * (Real.exp ε * X m)⁻¹ := by
          simp only [γ, Real.exp_neg]
          have hXm_ne := (hX_pos m).ne'
          have he_ne := (Real.exp_pos ε).ne'
          field_simp [hXm_ne, he_ne]
      _ ≤ (c₁ * X m * (Real.log (X m))⁻¹) * (Real.exp ε * X m)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog_inv (by positivity)) (by positivity)
      _ = (c₁ * (X m / Real.log (X m))) * (Real.exp ε * X m)⁻¹ := by ring
      _ ≤ ((W m).card : ℝ) * (Real.exp ε * X m)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ∑ q ∈ W m, (q : ℝ) ^ (-α) := hsum1
  obtain ⟨K, hK⟩ := exists_nat_gt (((m₀ + 1 : ℕ) : ℝ) * Real.exp ((|Real.log δ| + 1) / γ))
  set I_K := Finset.Icc m₀ (m₀ + K)
  set Z := I_K.biUnion W
  have hPd : (I_K : Set ℕ).PairwiseDisjoint W := fun a _ b _ hab => hdisj a b hab
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  let p : Fin Z.card → ℕ := fun i => (e i : ℕ)
  have hp : ∀ i, (p i).Prime := fun i => by
    obtain ⟨m, -, hqm⟩ := Finset.mem_biUnion.mp (e i).2
    exact (hmemW m _ hqm).1
  have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hcos : ∀ i, Real.cos (t * Real.log (p i)) ≤ -1 / 2 := fun i => by
    obtain ⟨m, -, hqm⟩ := Finset.mem_biUnion.mp (e i).2
    exact (hmemW m _ hqm).2.2.2.2
  refine ⟨Z.card, p, hp, hinj, hcos, ?_⟩
  have hprod_exp : (∏ i, (1 - (p i : ℝ) ^ (-α))) ≤ Real.exp (-∑ i, (p i : ℝ) ^ (-α)) := by
    have hfac : ∀ i : Fin Z.card,
        0 ≤ 1 - (p i : ℝ) ^ (-α) ∧ 1 - (p i : ℝ) ^ (-α) ≤ Real.exp (-(p i : ℝ) ^ (-α)) := fun i => by
      have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
      have hr_lt : (p i : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      exact ⟨by linarith, by linarith [Real.add_one_le_exp (-(p i : ℝ) ^ (-α))]⟩
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => (hfac i).1) (fun i _ => (hfac i).2)
  have hsum_Z : (∑ i, (p i : ℝ) ^ (-α)) = ∑ m ∈ I_K, ∑ q ∈ W m, (q : ℝ) ^ (-α) := by
    rw [Equiv.sum_comp e (fun z : Z => ((z : ℕ) : ℝ) ^ (-α)),
      Finset.sum_coe_sort Z (fun q : ℕ => (q : ℝ) ^ (-α)), Finset.sum_biUnion hPd]
  have hsum_big : |Real.log δ| + 1 < ∑ i, (p i : ℝ) ^ (-α) := by
    rw [hsum_Z]
    have h1 : γ * ∑ m ∈ I_K, ((m : ℝ) + 1)⁻¹ ≤ ∑ m ∈ I_K, ∑ q ∈ W m, (q : ℝ) ^ (-α) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m hm => hW_sum m (Finset.mem_Icc.mp hm).1
    have h2 : γ * Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) ≤
        γ * ∑ m ∈ I_K, ((m : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_inv_Icc_ge_log m₀ K) hγ_pos.le
    have hK' : ((m₀ + 1 : ℕ) : ℝ) * Real.exp ((|Real.log δ| + 1) / γ) < ((m₀ + K + 2 : ℕ) : ℝ) := by
      have : (K : ℝ) ≤ ((m₀ + K + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ m₀ + K + 2)
      linarith
    have hm0_pos : (0 : ℝ) < ((m₀ + 1 : ℕ) : ℝ) := by positivity
    have hdiv_gt : Real.exp ((|Real.log δ| + 1) / γ) <
        ((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ) := (lt_div_iff₀ hm0_pos).mpr (by linarith)
    have hlog_gt : (|Real.log δ| + 1) / γ <
        Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) := by
      have := Real.log_lt_log (Real.exp_pos _) hdiv_gt
      rwa [Real.log_exp] at this
    have hmul_gt : |Real.log δ| + 1 <
        γ * Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) := by
      have := mul_lt_mul_of_pos_left hlog_gt hγ_pos
      rwa [mul_div_cancel₀ _ hγ_pos.ne'] at this
    linarith
  have hexp_lt : Real.exp (-∑ i, (p i : ℝ) ^ (-α)) < δ := by
    rw [← Real.exp_log hδ]
    refine Real.exp_lt_exp.mpr ?_
    have := neg_le_abs (Real.log δ)
    linarith
  exact hprod_exp.trans_lt hexp_lt

/-- Phase-locked single-prime Euler factor estimate when `cos ψ ≤ −½` and `0 ≤ r < 1`. -/
private theorem euler_factor_phaseLock_bounds {r ψ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcos : Real.cos ψ ≤ -1 / 2) :
    1 + r ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((ψ : ℂ) * I)‖ ^ 2 ∧
    1 + r ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((-ψ : ℝ) * I)‖ ^ 2 ∧
    ‖((1 : ℂ) - (r : ℂ)) * ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * ψ : ℝ) * I))‖ ≤
      (1 - r) * (1 + r) ∧
    ‖((1 : ℂ) - (r : ℂ)) * ((1 : ℂ) - (r : ℂ) * Complex.exp ((-2 * ψ : ℝ) * I))‖ ≤
      (1 - r) * (1 + r) := by
  have hsq : ∀ α : ℝ, Real.cos α ≤ -1 / 2 →
      1 + r ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((α : ℂ) * I)‖ ^ 2 := fun α hα => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_sub]
    have htrig := Real.sin_sq_add_cos_sq α
    have hcalc : (1 - r * Real.cos α) * (1 - r * Real.cos α) +
        -(r * Real.sin α) * -(r * Real.sin α) = 1 - 2 * r * Real.cos α + r ^ 2 := by
      linear_combination r ^ 2 * htrig
    rw [hcalc]
    nlinarith [sq_nonneg r]
  have hprod : ∀ β : ℝ,
      ‖((1 : ℂ) - (r : ℂ)) * ((1 : ℂ) - (r : ℂ) * Complex.exp ((β : ℂ) * I))‖ ≤
        (1 - r) * (1 + r) := fun β => by
    rw [norm_mul]
    have h1 : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    have h2 : ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((β : ℂ) * I)‖ ≤ 1 + r := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr0]
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  refine ⟨hsq ψ hcos, ?_, ?_, ?_⟩
  · simpa using hsq (-ψ) (by rwa [Real.cos_neg])
  · simpa using hprod (2 * ψ)
  · simpa using hprod (-2 * ψ)

/-! ### 5. Critical-strip Mellin–Kronecker exponent collapse (`κ < min(1, κ₀)`) -/

/-- **Critical-strip Mellin–Kronecker exponent collapse.**
Any continuous all-base torus-positive amplitude `f` with right decay `ExpDecayFrom 0 κ₀ f` (`κ₀ > 0`)
and left growth `|f y| ≤ C e^{−κy}` on `(−∞, 0]` at any exponent `κ < min(1, κ₀)` (covering every
`κ ∈ [½, 1)` whenever `κ₀ > κ`) vanishes identically. -/
theorem eq_zero_of_torusPositive_of_lt_min_one {f : ℝ → ℝ} (hc : Continuous f)
    (hpos : IsAllBaseTorusPositive f) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (hd : ExpDecayFrom 0 κ₀ f)
    {κ C : ℝ} (hκ : κ < min 1 κ₀) (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y)) :
    f = 0 := by
  have hf_nn : ∀ y, 0 ≤ f y := hpos.nonneg
  have hmin_pos : 0 < min 1 κ₀ := lt_min one_pos hκ₀
  have hmax_lt : max κ 0 < min 1 κ₀ := max_lt hκ hmin_pos
  set σ : ℝ := (max κ 0 + min 1 κ₀) / 2
  have hσ_pos : 0 < σ := by simp only [σ]; linarith [le_max_right κ 0]
  have hσ_lt_one : σ < 1 := by simp only [σ]; linarith [min_le_left 1 κ₀]
  have hσ_lt_κ₀ : σ < κ₀ := by simp only [σ]; linarith [min_le_right 1 κ₀]
  have hκ_lt_σ : κ < σ := by simp only [σ]; linarith [le_max_left κ 0]
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := hd
  have hC_nn : 0 ≤ C := by simpa using (abs_nonneg (f 0)).trans (hL 0 le_rfl)
  set η : ℝ := min (κ₀ - σ) (σ - κ)
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  set M_bd : ℝ := C₀ + C + 1
  have hM_pos : 0 < M_bd := by positivity
  -- Integrability of `y ↦ f y * e^{σ y}` via two-sided exponential domination
  have hdom_pt : ∀ y : ℝ, f y * Real.exp (σ * y) ≤ M_bd * Real.exp (-η * |y|) := fun y => by
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      have hf_le : f y ≤ C₀ * Real.exp (-κ₀ * y) := (le_abs_self _).trans (hC₀ y hy)
      have hexp_le : Real.exp (-κ₀ * y) * Real.exp (σ * y) ≤ Real.exp (-η * y) := by
        rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
        have : η ≤ κ₀ - σ := min_le_left _ _
        nlinarith
      calc f y * Real.exp (σ * y)
          ≤ C₀ * (Real.exp (-κ₀ * y) * Real.exp (σ * y)) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hf_le (Real.exp_pos _).le
        _ ≤ C₀ * Real.exp (-η * y) := mul_le_mul_of_nonneg_left hexp_le hC₀_pos
        _ ≤ M_bd * Real.exp (-η * y) :=
            mul_le_mul_of_nonneg_right (by simp only [M_bd]; linarith) (Real.exp_pos _).le
    · rw [abs_of_neg hy]
      have hf_le : f y ≤ C * Real.exp (-κ * y) := (le_abs_self _).trans (hL y hy.le)
      have hexp_le : Real.exp (-κ * y) * Real.exp (σ * y) ≤ Real.exp (-η * -y) := by
        rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
        have : η ≤ σ - κ := min_le_right _ _
        nlinarith
      calc f y * Real.exp (σ * y)
          ≤ C * (Real.exp (-κ * y) * Real.exp (σ * y)) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hf_le (Real.exp_pos _).le
        _ ≤ C * Real.exp (-η * -y) := mul_le_mul_of_nonneg_left hexp_le hC_nn
        _ ≤ M_bd * Real.exp (-η * -y) :=
            mul_le_mul_of_nonneg_right (by simp only [M_bd]; linarith) (Real.exp_pos _).le
  have hint_maj : Integrable (fun y : ℝ => M_bd * Real.exp (-η * |y|)) := by
    have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hη_pos).const_mul M_bd
    exact h.congr (Eventually.of_forall fun y => by simp)
  have hint_real : Integrable (fun y : ℝ => f y * Real.exp (σ * y)) := by
    refine hint_maj.mono' (hc.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hf_nn y) (Real.exp_pos _).le)]
    exact hdom_pt y
  -- Fourier–Laplace transform `Φ t = ∫ y, (f y : ℂ) * exp((σ + i t) y)`
  let Φ : ℝ → ℂ := fun t =>
    ∫ y : ℝ, (f y : ℂ) * Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (y : ℂ))
  have hint_Φ : ∀ t : ℝ,
      Integrable (fun y : ℝ => (f y : ℂ) * Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (y : ℂ))) ∧
      (∀ y : ℝ, ‖(f y : ℂ) * Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (y : ℂ))‖ =
        f y * Real.exp (σ * y)) := fun t => by
    have hnorm_eq : ∀ y : ℝ,
        ‖(f y : ℂ) * Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (y : ℂ))‖ =
          f y * Real.exp (σ * y) := fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf_nn y), Complex.norm_exp]
      congr 2
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im]
      ring
    refine ⟨hint_real.mono' ?_ (Eventually.of_forall fun y => (hnorm_eq y).le), hnorm_eq⟩
    exact ((Complex.continuous_ofReal.comp hc).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  set I₀ : ℝ := ∫ y : ℝ, f y * Real.exp (σ * y)
  have hI₀_nn : 0 ≤ I₀ := integral_nonneg fun y => mul_nonneg (hf_nn y) (Real.exp_pos _).le
  -- Vanishing of `Φ t` for all `t ≠ 0`
  have hΦ_zero_ne : ∀ t : ℝ, t ≠ 0 → Φ t = 0 := fun t ht => by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    obtain ⟨n, p, hp, hinj, hcos, hprod_lt⟩ :=
      exists_primes_cos_le_neg_half_prod_lt hσ_pos hσ_lt_one.le ht (div_pos hε (by positivity : 0 < I₀ + 1))
    set ℓ : Fin n → ℝ := fun i => Real.log (p i)
    have hℓ : ∀ i, 0 < ℓ i := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    set θ : Fin n → ℝ := fun i => t * ℓ i
    -- Fubini-Tonelli evaluation of `∫ torusSum(ampl f ℓ x) θ * exp((σ + i s) x) dx`
    have hf_sigma_bd : ∀ y : ℝ, |f y| ≤ M_bd * Real.exp (-σ * y) := fun y => by
      rw [abs_of_nonneg (hf_nn y)]
      have h1 := hdom_pt y
      have h2 : Real.exp (-η * |y|) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := abs_nonneg y; nlinarith)
      have h3 : f y * Real.exp (σ * y) ≤ M_bd :=
        h1.trans (mul_le_of_le_one_right hM_pos.le h2)
      calc f y = (f y * Real.exp (σ * y)) * Real.exp (-σ * y) := by
            rw [mul_assoc, ← Real.exp_add]; simp
        _ ≤ M_bd * Real.exp (-σ * y) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    have hts_σ : TraceSummable (fun k : Fin n → ℕ => Real.exp (-σ * ∑ i, (k i : ℝ) * ℓ i)) := by
      have h0 : TraceSummable (ampl (fun y => Real.exp (-σ * y)) ℓ 0) :=
        traceSummable_ampl hσ_pos
          (fun y (_ : 0 ≤ y) => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ (le_rfl : (0 : ℝ) ≤ 0)
      exact h0.congr fun k => by simp [ampl]
    have hmellin_ident : ∀ s : ℝ,
        (∫ x : ℝ, (torusSum (ampl f ℓ x) θ : ℂ) *
            Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ))) =
          Φ s * ∏ i, ((1 - Complex.exp (-(((σ : ℂ) + (s : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp ((θ i : ℂ) * I))⁻¹ *
            (1 - Complex.exp (-(((σ : ℂ) + (s : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp (-((θ i : ℂ) * I)))⁻¹) := fun s => by
      let F_k : (Fin n → ℕ) → ℝ → ℂ := fun k x =>
        (f (x + ∑ i, (k i : ℝ) * ℓ i) * chiProd θ k : ℝ) *
          Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ))
      let z : Fin n → ℂ := fun i => Complex.exp (-(((σ : ℂ) + (s : ℂ) * I) * (ℓ i : ℂ)))
      have hz : ∀ i, ‖z i‖ < 1 := fun i => by
        simp only [z, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.add_re,
          Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im,
          Complex.ofReal_im, mul_zero, add_zero, sub_zero]
        exact Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
      have hFk_eq : ∀ (k : Fin n → ℕ) (x : ℝ),
          F_k k x = ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)) *
            ((f (x + ∑ i, (k i : ℝ) * ℓ i) : ℂ) *
              Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * ((x + ∑ i, (k i : ℝ) * ℓ i : ℝ) : ℂ))) := by
        intro k x
        simp only [F_k, z, ← Complex.exp_nat_mul, ← Complex.exp_sum]
        push_cast
        have hexp : Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ)) =
            (Complex.exp (∑ i, (k i : ℂ) * -(((σ : ℂ) + (s : ℂ) * I) * (ℓ i : ℂ)))) *
              Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * ((x : ℂ) + ∑ i, (k i : ℂ) * (ℓ i : ℂ))) := by
          rw [← Complex.exp_add]
          congr 1
          rw [mul_add, mul_sum]
          have hsum_neg : (∑ i, (k i : ℂ) * -(((σ : ℂ) + (s : ℂ) * I) * (ℓ i : ℂ))) +
              ∑ i, (((σ : ℂ) + (s : ℂ) * I)) * ((k i : ℂ) * (ℓ i : ℂ)) = 0 := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_eq_zero fun i _ => by ring
          linear_combination -hsum_neg
        rw [hexp]; ring
      have hFk_int : ∀ k, Integrable (F_k k) := fun k => by
        have hi := ((hint_Φ s).1.comp_add_right (∑ i, (k i : ℝ) * ℓ i)).const_mul
          ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i))
        exact hi.congr (Eventually.of_forall fun x => (hFk_eq k x).symm)
      have hFk_int_val : ∀ k, (∫ x, F_k k x) =
          Φ s * ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)) := fun k => by
        simp_rw [hFk_eq k]
        rw [integral_const_mul,
          integral_add_right_eq_self
            (fun y : ℝ => (f y : ℂ) * Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (y : ℂ)))
            (∑ i, (k i : ℝ) * ℓ i), mul_comm]
      have hFk_norm_sum : Summable (fun k => ∫ x, ‖F_k k x‖) := by
        have hnorm_val : ∀ k, (∫ x, ‖F_k k x‖) =
            |chiProd θ k| * Real.exp (-σ * ∑ i, (k i : ℝ) * ℓ i) * I₀ := fun k => by
          have hpt : ∀ x : ℝ, ‖F_k k x‖ =
              (|chiProd θ k| * Real.exp (-σ * ∑ i, (k i : ℝ) * ℓ i)) *
                (f (x + ∑ i, (k i : ℝ) * ℓ i) * Real.exp (σ * (x + ∑ i, (k i : ℝ) * ℓ i))) := fun x => by
            dsimp only [F_k]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf_nn _),
              Complex.norm_exp]
            have hre_exp : ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ)).re = σ * x := by
              simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
                Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im]
              ring
            rw [hre_exp]
            have hexp_split : Real.exp (σ * x) =
                Real.exp (-σ * ∑ i, (k i : ℝ) * ℓ i) *
                  Real.exp (σ * (x + ∑ i, (k i : ℝ) * ℓ i)) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [hexp_split]; ring
          simp_rw [hpt]
          rw [integral_const_mul,
            integral_add_right_eq_self (fun y : ℝ => f y * Real.exp (σ * y))]
        simp_rw [hnorm_val]
        refine Summable.mul_right I₀ ?_
        refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) hts_σ
        dsimp only
        rw [abs_of_pos (Real.exp_pos _), mul_comm |chiProd θ k|]
        exact mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (Real.exp_pos _).le
      have hFub := hasSum_integral_of_summable_integral_norm hFk_int hFk_norm_sum
      have htsum_pt : ∀ x : ℝ,
          (∑' k, F_k k x) =
            (torusSum (ampl f ℓ x) θ : ℂ) *
              Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ)) := fun x => by
        have hts_x : TraceSummable (ampl f ℓ x) :=
          traceSummable_ampl hσ_pos (fun y _ => hf_sigma_bd y) hℓ le_rfl
        have hsum_r : HasSum (fun k => ampl f ℓ x k * chiProd θ k) (torusSum (ampl f ℓ x) θ) :=
          (summable_term hts_x θ).hasSum
        have hsum_c : HasSum (fun k => F_k k x)
            ((torusSum (ampl f ℓ x) θ : ℂ) *
              Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ))) := by
          have := (Complex.hasSum_ofReal.mpr hsum_r).mul_right
            (Complex.exp ((((σ : ℂ) + (s : ℂ) * I)) * (x : ℂ)))
          exact this.congr_fun fun k => by simp [F_k, ampl]
        exact hsum_c.tsum_eq
      simp_rw [hFk_int_val, htsum_pt] at hFub
      have hchi := (hasSum_chiProd_mul_pow_complex hz θ).mul_left (Φ s)
      exact hFub.unique hchi
    -- Compare `s = t` against `s = 0` using `torusSum ≥ 0`
    have hid_t := hmellin_ident t
    have hid_0 := hmellin_ident 0
    set W_t : ℂ := ∏ i, ((1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
        Complex.exp ((θ i : ℂ) * I)) *
      (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
        Complex.exp (-((θ i : ℂ) * I))))
    have hWt_inv : (∏ i, ((1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
          Complex.exp ((θ i : ℂ) * I))⁻¹ *
        (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
          Complex.exp (-((θ i : ℂ) * I)))⁻¹)) * W_t = 1 := by
      simp only [W_t, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have hne : ∀ sgn : ℂ, ‖sgn‖ = 1 →
          1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) * sgn ≠ 0 := fun sgn hsgn h0 => by
        have h1 : ‖Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) * sgn‖ < 1 := by
          rw [norm_mul, hsgn, mul_one, Complex.norm_exp]
          simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
            Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im,
            mul_zero, add_zero, sub_zero]
          exact Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
        have h2 : (1 : ℝ) = ‖Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) * sgn‖ := by
          have := sub_eq_zero.mp h0; rw [← this, norm_one]
        linarith
      have hne1 := hne _ (Complex.norm_exp_ofReal_mul_I (θ i))
      have hne2 := hne _ (by simpa using Complex.norm_exp_ofReal_mul_I (-θ i))
      calc (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp ((θ i : ℂ) * I))⁻¹ *
            (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp (-((θ i : ℂ) * I)))⁻¹ *
            ((1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp ((θ i : ℂ) * I)) *
              (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp (-((θ i : ℂ) * I))))
          = ((1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp ((θ i : ℂ) * I))⁻¹ *
              (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp ((θ i : ℂ) * I))) *
            ((1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp (-((θ i : ℂ) * I)))⁻¹ *
              (1 - Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
                Complex.exp (-((θ i : ℂ) * I)))) := by ring
        _ = 1 * 1 := by rw [inv_mul_cancel₀ hne1, inv_mul_cancel₀ hne2]
        _ = 1 := mul_one 1
    have hΦt_eq : Φ t = W_t * ∫ x : ℝ, (torusSum (ampl f ℓ x) θ : ℂ) *
        Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (x : ℂ)) := by
      have := congrArg (· * W_t) hid_t
      rw [mul_assoc, hWt_inv, mul_one, mul_comm] at this
      exact this.symm
    have hint_le : ‖∫ x : ℝ, (torusSum (ampl f ℓ x) θ : ℂ) *
        Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (x : ℂ))‖ ≤
        I₀ * ∏ i, ‖(1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2 := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      have hpt_n : ∀ x : ℝ, ‖(torusSum (ampl f ℓ x) θ : ℂ) *
          Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (x : ℂ))‖ =
          torusSum (ampl f ℓ x) θ * Real.exp (σ * x) := fun x => by
        have hnn_G : 0 ≤ torusSum (ampl f ℓ x) θ := hpos n p hp hinj x θ
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn_G, Complex.norm_exp]
        congr 2
        simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.ofReal_im]
        ring
      simp_rw [hpt_n]
      have h0_eq : ∀ x : ℝ, ((torusSum (ampl f ℓ x) θ * Real.exp (σ * x) : ℝ) : ℂ) =
          (torusSum (ampl f ℓ x) θ : ℂ) *
            Complex.exp ((((σ : ℂ) + ((0 : ℝ) : ℂ) * I)) * (x : ℂ)) := fun x => by
        simp [Complex.ofReal_mul, Complex.ofReal_exp]
      have hre0 := congrArg Complex.re hid_0
      simp_rw [← h0_eq] at hre0
      rw [integral_complex_ofReal, Complex.ofReal_re] at hre0
      rw [hre0]
      have hΦ0 : Φ 0 = (I₀ : ℂ) := by
        simp only [Φ, I₀]
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [Complex.ofReal_mul, Complex.ofReal_exp]
      have hprod0 : (∏ i, ((1 - Complex.exp (-(((σ : ℂ) + ((0 : ℝ) : ℂ) * I) * (ℓ i : ℂ))) *
            Complex.exp ((θ i : ℂ) * I))⁻¹ *
          (1 - Complex.exp (-(((σ : ℂ) + ((0 : ℝ) : ℂ) * I) * (ℓ i : ℂ))) *
            Complex.exp (-((θ i : ℂ) * I)))⁻¹)) =
          ((∏ i, ‖(1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        set w_i : ℂ := (1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) * Complex.exp ((θ i : ℂ) * I)
        have hconj : (1 - Complex.exp (-(((σ : ℂ) + ((0 : ℝ) : ℂ) * I) * (ℓ i : ℂ))) *
            Complex.exp (-((θ i : ℂ) * I))) = conj w_i := by
          simp only [w_i, Complex.ofReal_zero, zero_mul, add_zero, map_sub, map_one, map_mul,
            Complex.conj_ofReal, ← Complex.exp_conj]
          congr 2
          · rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, neg_mul, ← Complex.ofReal_exp]
          · simp [Complex.conj_I]
        have hw1 : (1 - Complex.exp (-(((σ : ℂ) + ((0 : ℝ) : ℂ) * I) * (ℓ i : ℂ))) *
            Complex.exp ((θ i : ℂ) * I)) = w_i := by
          simp only [w_i, Complex.ofReal_zero, zero_mul, add_zero]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, neg_mul, ← Complex.ofReal_exp]
        rw [hw1, hconj, ← mul_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          ← Complex.ofReal_inv, inv_pow]
      rw [hΦ0, hprod0, ← Complex.ofReal_mul, Complex.ofReal_re]
    -- Phase-locked cancellation bound `‖W_t‖ * ∏_i ‖...‖⁻² ≤ ∏_i (1 - p_i^{−σ})`
    have hratio_le : ‖W_t‖ * (∏ i, ‖(1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) *
        Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2) ≤ ∏ i, (1 - (p i : ℝ) ^ (-σ)) := by
      rw [norm_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
      set r_i : ℝ := (p i : ℝ) ^ (-σ)
      have hp_pos : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
      have hr0 : 0 ≤ r_i := by positivity
      have hr1 : r_i < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      have hexp_r : Real.exp (-σ * ℓ i) = r_i := by
        simp only [r_i, ℓ]; rw [Real.rpow_def_of_pos hp_pos]; congr 1; ring
      obtain ⟨hd1, -, -, hn2⟩ := euler_factor_phaseLock_bounds hr0 hr1 (hcos i)
      have hfac1 : Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
          Complex.exp ((θ i : ℂ) * I) = (r_i : ℂ) := by
        rw [← Complex.exp_add]
        have he : -(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ)) + (θ i : ℂ) * I =
            ((-σ * ℓ i : ℝ) : ℂ) := by simp only [θ]; push_cast; ring
        rw [he, ← Complex.ofReal_exp, hexp_r]
      have hfac2 : Complex.exp (-(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ))) *
          Complex.exp (-((θ i : ℂ) * I)) = (r_i : ℂ) * Complex.exp ((-2 * θ i : ℝ) * I) := by
        rw [← Complex.exp_add]
        have he : -(((σ : ℂ) + (t : ℂ) * I) * (ℓ i : ℂ)) + -((θ i : ℂ) * I) =
            ((-σ * ℓ i : ℝ) : ℂ) + ((-2 * θ i : ℝ) : ℂ) * I := by simp only [θ]; push_cast; ring
        rw [he, Complex.exp_add, ← Complex.ofReal_exp, hexp_r]
      rw [hfac1, hfac2, hexp_r, inv_pow]
      have hinv_le : (‖(1 : ℂ) - (r_i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2)⁻¹ ≤ (1 + r_i)⁻¹ :=
        inv_anti₀ (by linarith) (by simpa [θ, ℓ] using hd1)
      have hn2' : ‖((1 : ℂ) - (r_i : ℂ)) * ((1 : ℂ) - (r_i : ℂ) *
          Complex.exp ((-2 * θ i : ℝ) * I))‖ ≤ (1 - r_i) * (1 + r_i) := by
        simpa [θ, ℓ] using hn2
      calc ‖((1 : ℂ) - (r_i : ℂ)) * ((1 : ℂ) - (r_i : ℂ) * Complex.exp ((-2 * θ i : ℝ) * I))‖ *
              (‖(1 : ℂ) - (r_i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2)⁻¹
          ≤ ((1 - r_i) * (1 + r_i)) * (1 + r_i)⁻¹ :=
            mul_le_mul hn2' hinv_le (by positivity) (by nlinarith)
        _ = 1 - r_i := by field_simp [show (1 + r_i : ℝ) ≠ 0 by linarith]
    calc ‖Φ t‖ = ‖W_t‖ * ‖∫ x : ℝ, (torusSum (ampl f ℓ x) θ : ℂ) *
            Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (x : ℂ))‖ := by rw [hΦt_eq, norm_mul]
      _ ≤ ‖W_t‖ * (I₀ * ∏ i, ‖(1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) *
            Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hint_le (norm_nonneg _)
      _ = I₀ * (‖W_t‖ * ∏ i, ‖(1 : ℂ) - (Real.exp (-σ * ℓ i) : ℂ) *
            Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2) := by ring
      _ ≤ I₀ * ∏ i, (1 - (p i : ℝ) ^ (-σ)) := mul_le_mul_of_nonneg_left hratio_le hI₀_nn
      _ ≤ (I₀ + 1) * ∏ i, (1 - (p i : ℝ) ^ (-σ)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (Finset.prod_nonneg fun i _ => ?_)
          have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
          linarith [Real.rpow_lt_one_of_one_lt_of_neg hp1 (show -σ < 0 by linarith)]
      _ ≤ ε := by
          have := mul_lt_mul_of_pos_left hprod_lt (show 0 < I₀ + 1 by positivity)
          rw [mul_div_cancel₀ _ (by positivity)] at this
          exact this.le
  -- Continuity of `Φ` along `t_k = (k + 1)⁻¹ → 0` forces `I₀ = 0` and hence `f = 0`
  have hΦ0_zero : Φ 0 = 0 := by
    let F_seq : ℕ → ℝ → ℂ := fun k y =>
      (f y : ℂ) * Complex.exp ((((σ : ℂ) + ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) * I)) * (y : ℂ))
    have htend_inv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hmeas : ∀ k, AEStronglyMeasurable (F_seq k) volume := fun k =>
      (hint_Φ (((k : ℝ) + 1)⁻¹)).1.aestronglyMeasurable
    have hbd : ∀ k, ∀ᵐ y ∂volume, ‖F_seq k y‖ ≤ f y * Real.exp (σ * y) := fun k =>
      Eventually.of_forall fun y => ((hint_Φ (((k : ℝ) + 1)⁻¹)).2 y).le
    have hlim : ∀ᵐ y ∂volume, Tendsto (fun k => F_seq k y) atTop
        (𝓝 ((f y : ℂ) * Complex.exp ((((σ : ℂ) + ((0 : ℝ) : ℂ) * I)) * (y : ℂ)))) := by
      refine Eventually.of_forall fun y => ?_
      have hc_t : Continuous (fun t : ℝ =>
          (f y : ℂ) * Complex.exp ((((σ : ℂ) + (t : ℂ) * I)) * (y : ℂ))) := by fun_prop
      exact (hc_t.tendsto 0).comp htend_inv
    have hdom := tendsto_integral_of_dominated_convergence (fun y => f y * Real.exp (σ * y))
      hmeas hint_real hbd hlim
    have hseq_zero : (fun k : ℕ => ∫ y, F_seq k y) = fun _ => 0 := by
      funext k
      exact hΦ_zero_ne (((k : ℝ) + 1)⁻¹) (by positivity)
    rw [hseq_zero] at hdom
    exact tendsto_nhds_unique hdom tendsto_const_nhds
  have hI₀_eq : I₀ = 0 := by
    have hΦ0 : Φ 0 = (I₀ : ℂ) := by
      simp only [Φ, I₀]
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [Complex.ofReal_mul, Complex.ofReal_exp]
    rw [hΦ0] at hΦ0_zero
    exact Complex.ofReal_eq_zero.mp hΦ0_zero
  have hae : (fun y : ℝ => f y * Real.exp (σ * y)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun y => mul_nonneg (hf_nn y) (Real.exp_pos _).le) hint_real).mp hI₀_eq
  have hfeq : (fun y : ℝ => f y * Real.exp (σ * y)) = 0 :=
    Measure.eq_of_ae_eq hae (hc.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      continuous_zero
  funext y
  have hy := congrFun hfeq y
  simp only [Pi.zero_apply, mul_eq_zero] at hy
  exact hy.resolve_right (Real.exp_pos _).ne'

/-! ### 6. Oscillatory Bernstein dichotomy at `α = 1` -/

/-- Exact torus evaluation of the damped oscillatory mode `y ↦ e^{−αy} cos(ωy)` (`α > 0`). -/
theorem torusSum_ampl_exp_neg_mul_cos {n : ℕ} {α : ℝ} (hα : 0 < α) (ω : ℝ) {ℓ : Fin n → ℝ}
    (hℓ : ∀ i, 0 < ℓ i) (x : ℝ) (θ : Fin n → ℝ) :
    torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y)) ℓ x) θ =
      Real.exp (-α * x) *
        (Complex.exp (((ω * x : ℝ) : ℂ) * I) *
          ∏ i, ((1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp ((θ i : ℂ) * I))⁻¹ *
            (1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ))) *
              Complex.exp (-((θ i : ℂ) * I)))⁻¹)).re := by
  let z : Fin n → ℂ := fun i => Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ)))
  have hz : ∀ i, ‖z i‖ < 1 := fun i => by
    simp only [z, Complex.norm_exp, Complex.mul_re, Complex.add_re, Complex.neg_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.neg_im, Complex.ofReal_im, mul_zero, add_zero, sub_zero, neg_zero]
    exact Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
  have hc := ((hasSum_chiProd_mul_pow_complex hz θ).mul_left
    (Complex.exp (((ω * x : ℝ) : ℂ) * I))).mul_left ((Real.exp (-α * x) : ℝ) : ℂ)
  have hre : HasSum
      (fun k : Fin n → ℕ =>
        (((Real.exp (-α * x) : ℝ) : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) *
          ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)))).re)
      (((Real.exp (-α * x) : ℝ) : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) *
        ∏ i, ((1 - z i * Complex.exp ((θ i : ℂ) * I))⁻¹ *
          (1 - z i * Complex.exp (-((θ i : ℂ) * I)))⁻¹))).re := by
    simpa only [HasSum, Function.comp_def, Complex.re_sum] using
      (Complex.continuous_re.tendsto _).comp hc
  rw [Complex.re_ofReal_mul] at hre
  have hterm : ∀ k : Fin n → ℕ,
      (((Real.exp (-α * x) : ℝ) : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) *
        ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)))).re =
        ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y)) ℓ x k * chiProd θ k := fun k => by
    set y_k : ℝ := x + ∑ i, (k i : ℝ) * ℓ i
    have hz_prod : (Complex.exp (((ω * x : ℝ) : ℂ) * I) * ∏ i, z i ^ (k i)) =
        ((Real.exp (-α * ∑ i, (k i : ℝ) * ℓ i) : ℝ) : ℂ) *
          Complex.exp (((ω * y_k : ℝ) : ℂ) * I) := by
      simp only [z, ← Complex.exp_nat_mul, ← Complex.exp_sum, ← Complex.exp_add]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      simp only [y_k]
      push_cast
      rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      have hs : (∑ i, (k i : ℂ) * (((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ))) -
          (∑ i, -(α : ℂ) * ((k i : ℂ) * (ℓ i : ℂ)) +
            ∑ i, (ω : ℂ) * ((k i : ℂ) * (ℓ i : ℂ)) * I) = 0 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_eq_zero fun i _ => by ring
      linear_combination hs
    have h1 : (((Real.exp (-α * x) : ℝ) : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) *
        ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)))) =
        ((Real.exp (-α * y_k) * chiProd θ k : ℝ) : ℂ) *
          Complex.exp (((ω * y_k : ℝ) : ℂ) * I) := by
      rw [show Complex.exp (((ω * x : ℝ) : ℂ) * I) * ((chiProd θ k : ℂ) * ∏ i, z i ^ (k i)) =
          (chiProd θ k : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * ∏ i, z i ^ (k i)) by ring,
        hz_prod]
      have hexp_yk : Real.exp (-α * y_k) = Real.exp (-α * x) *
          Real.exp (-α * ∑ i, (k i : ℝ) * ℓ i) := by
        simp only [y_k]; rw [← Real.exp_add]; congr 1; ring
      rw [hexp_yk]; push_cast; ring
    rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    simp only [ampl, y_k]; ring
  simp_rw [hterm] at hre
  exact hre.tsum_eq

/-- Uniform positive lower bound on `torusSum` of `e^{−αy}` for `α > 1`, independent of `n, p, θ`. -/
theorem torusSum_exp_neg_ge_euler_floor {α : ℝ} (hα : 1 < α) {n : ℕ} {p : Fin n → ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (x : ℝ) (θ : Fin n → ℝ) :
    Real.exp (-2 * ∑' m : ℕ, ((m : ℝ) ^ α)⁻¹) * Real.exp (-α * x) ≤
      torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) θ := by
  have hα0 : 0 < α := by linarith
  have hsum_α : Summable (fun m : ℕ => ((m : ℝ) ^ α)⁻¹) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hα
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
  rw [torusSum_ampl_exp_neg hα0 hℓ x θ, mul_comm _ (Real.exp (-α * x))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hterm_ge : ∀ i : Fin n,
      Real.exp (-2 * (((p i : ℝ) ^ α)⁻¹)) ≤
        ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2 := fun i => by
    have hp_pos : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hexp_p : Real.exp (-α * Real.log (p i)) = ((p i : ℝ) ^ α)⁻¹ := by
      rw [← Real.rpow_neg hp_pos.le, Real.rpow_def_of_pos hp_pos]; congr 1; ring
    have hnorm_le : ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ≤
        Real.exp (((p i : ℝ) ^ α)⁻¹) := by
      calc ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖
          ≤ ‖(1 : ℂ)‖ + ‖(Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ :=
            norm_sub_le _ _
        _ = 1 + ((p i : ℝ) ^ α)⁻¹ := by
            rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (Real.exp_pos _).le, hexp_p]
        _ ≤ Real.exp (((p i : ℝ) ^ α)⁻¹) := by linarith [Real.add_one_le_exp (((p i : ℝ) ^ α)⁻¹)]
    have hnorm_pos : 0 < ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ := by
      have hsub := norm_sub_norm_le (1 : ℂ)
        ((Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I))
      rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le] at hsub
      have hexp_lt : Real.exp (-α * Real.log (p i)) < 1 :=
        Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
      linarith
    have hinv := pow_le_pow_left₀ (by positivity) (inv_anti₀ hnorm_pos hnorm_le) 2
    have hexp2 : (Real.exp (((p i : ℝ) ^ α)⁻¹))⁻¹ ^ 2 = Real.exp (-2 * (((p i : ℝ) ^ α)⁻¹)) := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rwa [hexp2] at hinv
  have hprod_exp : Real.exp (-2 * ∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) ≤
      ∏ i : Fin n, ‖1 - (Real.exp (-α * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2 := by
    rw [mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun i _ => hterm_ge i
  have hsum_le : (∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) ≤ ∑' m : ℕ, ((m : ℝ) ^ α)⁻¹ := by
    rw [(Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ α)⁻¹) fun i _ j _ hij => hinj hij).symm]
    exact hsum_α.sum_le_tsum (Finset.univ.image p) fun m _ => by positivity
  exact (Real.exp_le_exp.mpr (by linarith)).trans hprod_exp

/-- Uniform upper bound on complex Euler reciprocal factors `(1 − z)⁻¹` for `α > 1`, `p_i` prime. -/
private theorem norm_inv_sub_prime_exp_le {α : ℝ} (hα : 1 < α) {q : ℕ} (hq : q.Prime)
    {w : ℂ} (hw : ‖w‖ = Real.exp (-α * Real.log q)) :
    ‖(1 - w)⁻¹‖ ≤ Real.exp (2 * ((q : ℝ) ^ α)⁻¹) := by
  set u : ℝ := ((q : ℝ) ^ α)⁻¹
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hexp_u : Real.exp (-α * Real.log q) = u := by
    simp only [u]; rw [← Real.rpow_neg hq_pos.le, Real.rpow_def_of_pos hq_pos]; congr 1; ring
  have hu0 : 0 ≤ u := by positivity
  have hu_half : u ≤ 1 / 2 := by
    simp only [u]
    have h2pow : (2 : ℝ) ≤ (q : ℝ) ^ α := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα.le
        _ ≤ (q : ℝ) ^ α := Real.rpow_le_rpow (by norm_num) hq2 (by linarith)
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2pow
  have hsub : 1 - u ≤ ‖1 - w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    rwa [norm_one, hw, hexp_u] at h
  have h1u_pos : 0 < 1 - u := by linarith
  rw [norm_inv]
  refine (inv_anti₀ h1u_pos hsub).trans ?_
  rw [inv_le_iff_one_le_mul₀' h1u_pos]
  have hexp_2u : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hquad : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
  exact hquad.trans (mul_le_mul_of_nonneg_left hexp_2u h1u_pos.le)

/-- **Oscillatory Bernstein dichotomy at `α = 1`.**
For `f(y) = e^{−αy}(1 + ε cos(ωy))` (`ω ≠ 0`), every `ε ≠ 0` violates all-base torus positivity
throughout `0 < α ≤ 1` (including `α = ½` and `α = 1`), whereas for every `α > 1` small `|ε| > 0`
gives strict all-base torus positivity while violating `IsExpConvexFrom 0`. -/
theorem oscillatory_bernstein_dichotomy {ω : ℝ} (hω : ω ≠ 0) :
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ ε : ℝ, ε ≠ 0 →
      ¬ IsAllBaseTorusPositive (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y)))) ∧
    (∀ α : ℝ, 1 < α → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
      (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
        ∀ (x : ℝ) (θ : Fin n → ℝ),
          0 < torusSum (ampl (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y)))
            (fun i => Real.log (p i)) x) θ) ∧
      ¬ IsExpConvexFrom 0 (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y)))) := by
  -- Shared linearity of `torusSum` for `e^{−αy}(1 + ε cos(ωy))` when `α > 0`
  have hlin_osc : ∀ {α : ℝ} (hα0 : 0 < α) (ε : ℝ) {n : ℕ} {p : Fin n → ℕ}
      (hp : ∀ i, (p i).Prime) (x : ℝ) (θ : Fin n → ℝ),
      torusSum (ampl (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y)))
          (fun i => Real.log (p i)) x) θ =
        torusSum (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) θ +
          ε * torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
            (fun i => Real.log (p i)) x) θ := by
    intro α hα0 ε n p hp x θ
    have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    have hts1 : TraceSummable (ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα0 (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
    have hts2 : TraceSummable (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
        (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα0 (fun y _ => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _), one_mul]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) hℓ le_rfl
    have hpt : ∀ k,
        ampl (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y))) (fun i => Real.log (p i)) x k *
            chiProd θ k =
          ampl (fun y => Real.exp (-α * y)) (fun i => Real.log (p i)) x k * chiProd θ k +
            ε * (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
              (fun i => Real.log (p i)) x k * chiProd θ k) := fun k => by
      simp only [ampl]; ring
    rw [torusSum, torusSum, torusSum]
    simp_rw [hpt]
    rw [Summable.tsum_add (summable_term hts1 θ) ((summable_term hts2 θ).mul_left ε), tsum_mul_left]
  refine ⟨fun α hα0 hα1 ε hε hpos => ?_, fun α hα => ?_⟩
  · -- Part 1: `0 < α ≤ 1`, `ε ≠ 0`
    have hε_abs : 0 < |ε| := abs_pos.mpr hε
    obtain ⟨n, p, hp, hinj, hcos, hprod_lt⟩ :=
      exists_primes_cos_le_neg_half_prod_lt hα0 hα1 hω (half_pos hε_abs)
    set ℓ : Fin n → ℝ := fun i => Real.log (p i)
    have hℓ : ∀ i, 0 < ℓ i := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    set θ : Fin n → ℝ := fun i => -ω * ℓ i
    let z : Fin n → ℂ := fun i => Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ)))
    set W : ℂ := ∏ i, ((1 - z i * Complex.exp ((θ i : ℂ) * I)) *
      (1 - z i * Complex.exp (-((θ i : ℂ) * I))))
    set Z : ℂ := ∏ i, ((1 - z i * Complex.exp ((θ i : ℂ) * I))⁻¹ *
      (1 - z i * Complex.exp (-((θ i : ℂ) * I)))⁻¹)
    have hWZ : W * Z = 1 := by
      simp only [W, Z, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have hne : ∀ sgn : ℂ, ‖sgn‖ = 1 → 1 - z i * sgn ≠ 0 := fun sgn hsgn h0 => by
        have h1 : ‖z i * sgn‖ < 1 := by
          rw [norm_mul, hsgn, mul_one]; simp only [z, Complex.norm_exp, Complex.mul_re,
            Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im, mul_zero, add_zero,
            sub_zero, neg_zero]
          exact Real.exp_lt_one_iff.mpr (by have := hℓ i; nlinarith)
        have h2 : (1 : ℝ) = ‖z i * sgn‖ := by have := sub_eq_zero.mp h0; rw [← this, norm_one]
        linarith
      have hne1 := hne _ (Complex.norm_exp_ofReal_mul_I (θ i))
      have hne2 := hne _ (by simpa using Complex.norm_exp_ofReal_mul_I (-θ i))
      field_simp [hne1, hne2]
    have hZ_ne : Z ≠ 0 := right_ne_zero_of_mul_eq_one hWZ
    have hZ_pos : 0 < ‖Z‖ := norm_pos_iff.mpr hZ_ne
    have hWZ_norm : ‖W‖ * ‖Z‖ = 1 := by rw [← norm_mul, hWZ, norm_one]
    set A₀ : ℝ := ∏ i, ‖(1 : ℂ) - (Real.exp (-α * ℓ i) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2
    have hWA₀_le : ‖W‖ * A₀ ≤ ∏ i, (1 - (p i : ℝ) ^ (-α)) := by
      simp only [W, A₀]
      rw [norm_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
      set r_i : ℝ := (p i : ℝ) ^ (-α)
      have hp_pos : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hp1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
      have hr0 : 0 ≤ r_i := by positivity
      have hr1 : r_i < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      have hexp_r : Real.exp (-α * ℓ i) = r_i := by
        simp only [r_i, ℓ]; rw [Real.rpow_def_of_pos hp_pos]; congr 1; ring
      obtain ⟨-, hd2, hn1, -⟩ := euler_factor_phaseLock_bounds hr0 hr1 (hcos i)
      have hfac1 : z i * Complex.exp ((θ i : ℂ) * I) = (r_i : ℂ) := by
        simp only [z, θ]; rw [← Complex.exp_add]
        have he : (((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ)) + ((-ω * ℓ i : ℝ) : ℂ) * I =
            ((-α * ℓ i : ℝ) : ℂ) := by push_cast; ring
        rw [he, ← Complex.ofReal_exp, hexp_r]
      have hfac2 : z i * Complex.exp (-((θ i : ℂ) * I)) =
          (r_i : ℂ) * Complex.exp ((2 * (ω * ℓ i) : ℝ) * I) := by
        simp only [z, θ]; rw [← Complex.exp_add]
        have he : (((-α : ℂ) + (ω : ℂ) * I) * (ℓ i : ℂ)) + -(((-ω * ℓ i : ℝ) : ℂ) * I) =
            ((-α * ℓ i : ℝ) : ℂ) + ((2 * (ω * ℓ i) : ℝ) : ℂ) * I := by push_cast; ring
        rw [he, Complex.exp_add, ← Complex.ofReal_exp, hexp_r]
      rw [hfac1, hfac2, hexp_r, inv_pow]
      have hinv_le : (‖(1 : ℂ) - (r_i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2)⁻¹ ≤ (1 + r_i)⁻¹ :=
        inv_anti₀ (by linarith) (by simpa [θ, ℓ] using hd2)
      have hn1' : ‖((1 : ℂ) - (r_i : ℂ)) * ((1 : ℂ) - (r_i : ℂ) *
          Complex.exp ((2 * (ω * ℓ i) : ℝ) * I))‖ ≤ (1 - r_i) * (1 + r_i) := by
        simpa [ℓ] using hn1
      calc ‖((1 : ℂ) - (r_i : ℂ)) * ((1 : ℂ) - (r_i : ℂ) * Complex.exp ((2 * (ω * ℓ i) : ℝ) * I))‖ *
              (‖(1 : ℂ) - (r_i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2)⁻¹
          ≤ ((1 - r_i) * (1 + r_i)) * (1 + r_i)⁻¹ :=
            mul_le_mul hn1' hinv_le (by positivity) (by nlinarith)
        _ = 1 - r_i := by field_simp [show (1 + r_i : ℝ) ≠ 0 by linarith]
    have hA₀_lt : A₀ < |ε| * ‖Z‖ := by
      have h1 : A₀ ≤ (∏ i, (1 - (p i : ℝ) ^ (-α))) * ‖Z‖ := by
        calc A₀ = A₀ * (‖W‖ * ‖Z‖) := by rw [hWZ_norm, mul_one]
          _ = (‖W‖ * A₀) * ‖Z‖ := by ring
          _ ≤ (∏ i, (1 - (p i : ℝ) ^ (-α))) * ‖Z‖ :=
            mul_le_mul_of_nonneg_right hWA₀_le hZ_pos.le
      have h2 : (∏ i, (1 - (p i : ℝ) ^ (-α))) * ‖Z‖ < (|ε| / 2) * ‖Z‖ :=
        mul_lt_mul_of_pos_right hprod_lt hZ_pos
      linarith [mul_pos hε_abs hZ_pos]
    -- Choose base point `x` to anti-align `exp(i ω x)` with `(ε : ℂ) * Z`
    set u_c : ℂ := (ε : ℂ) * Z
    set x : ℝ := (π - Complex.arg u_c) / ω
    have hphase_re : ε * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re = -(|ε| * ‖Z‖) := by
      have hωx : ω * x = π - Complex.arg u_c := mul_div_cancel₀ _ hω
      have hre1 : ε * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re =
          (Complex.exp (((ω * x : ℝ) : ℂ) * I) * u_c).re := by
        simp only [u_c]
        rw [show Complex.exp (((ω * x : ℝ) : ℂ) * I) * ((ε : ℂ) * Z) =
            (ε : ℂ) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z) by ring, Complex.re_ofReal_mul]
      rw [hre1, hωx]
      have hpolar := Complex.norm_mul_exp_arg_mul_I u_c
      have hprod_u : Complex.exp (((π - Complex.arg u_c : ℝ) : ℂ) * I) * u_c = -(‖u_c‖ : ℂ) := by
        calc Complex.exp (((π - Complex.arg u_c : ℝ) : ℂ) * I) * u_c
            = Complex.exp (((π - Complex.arg u_c : ℝ) : ℂ) * I) *
                ((‖u_c‖ : ℂ) * Complex.exp ((Complex.arg u_c : ℂ) * I)) := by rw [hpolar]
          _ = (‖u_c‖ : ℂ) * (Complex.exp (((π - Complex.arg u_c : ℝ) : ℂ) * I) *
                Complex.exp ((Complex.arg u_c : ℂ) * I)) := by ring
          _ = (‖u_c‖ : ℂ) * Complex.exp ((π : ℂ) * I) := by
              rw [← Complex.exp_add]; congr 2; push_cast; ring
          _ = -(‖u_c‖ : ℂ) := by rw [Complex.exp_pi_mul_I]; ring
      rw [hprod_u, Complex.neg_re, Complex.ofReal_re]
      simp only [u_c, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hval : torusSum (ampl (fun y => Real.exp (-α * y) * (1 + ε * Real.cos (ω * y)))
        ℓ x) θ < 0 := by
      rw [hlin_osc hα0 ε hp x θ, torusSum_ampl_exp_neg hα0 hℓ x θ,
        torusSum_ampl_exp_neg_mul_cos hα0 ω hℓ x θ]
      have heq : Real.exp (-α * x) * A₀ +
          ε * (Real.exp (-α * x) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re) =
          Real.exp (-α * x) * (A₀ - |ε| * ‖Z‖) := by
        calc Real.exp (-α * x) * A₀ +
              ε * (Real.exp (-α * x) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re)
            = Real.exp (-α * x) * (A₀ + ε * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re) := by ring
          _ = Real.exp (-α * x) * (A₀ - |ε| * ‖Z‖) := by rw [hphase_re]; ring
      change Real.exp (-α * x) * A₀ +
          ε * (Real.exp (-α * x) * (Complex.exp (((ω * x : ℝ) : ℂ) * I) * Z).re) < 0
      rw [heq]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)
    exact absurd (hpos n p hp hinj x θ) (not_le.mpr hval)
  · -- Part 2: `α > 1`
    have hα0 : 0 < α := by linarith
    have hsum_α : Summable (fun m : ℕ => ((m : ℝ) ^ α)⁻¹) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hα
    set S_α : ℝ := ∑' m : ℕ, ((m : ℝ) ^ α)⁻¹
    set c_α : ℝ := Real.exp (-2 * S_α)
    set K_α : ℝ := Real.exp (4 * S_α)
    set ε₀ : ℝ := c_α / (2 * K_α)
    have hε₀ : 0 < ε₀ := by positivity
    refine ⟨ε₀, hε₀, fun ε hε hε_le => ⟨fun n p hp hinj x θ => ?_, ?_⟩⟩
    · have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
      have hfloor := torusSum_exp_neg_ge_euler_floor hα hp hinj x θ
      have hosc_bd : |torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
          (fun i => Real.log (p i)) x) θ| ≤ K_α * Real.exp (-α * x) := by
        rw [torusSum_ampl_exp_neg_mul_cos hα0 ω hℓ x θ, abs_mul, abs_of_pos (Real.exp_pos _),
          mul_comm K_α]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
        have hfac_le : ∀ i : Fin n,
            ‖(1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (Real.log (p i) : ℂ))) *
                Complex.exp ((θ i : ℂ) * I))⁻¹ *
              (1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (Real.log (p i) : ℂ))) *
                Complex.exp (-((θ i : ℂ) * I)))⁻¹‖ ≤
              Real.exp (4 * ((p i : ℝ) ^ α)⁻¹) := fun i => by
          rw [norm_mul]
          have hw_n : ∀ sgn : ℂ, ‖sgn‖ = 1 →
              ‖Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (Real.log (p i) : ℂ))) * sgn‖ =
                Real.exp (-α * Real.log (p i)) := fun sgn hsgn => by
            rw [norm_mul, hsgn, mul_one, Complex.norm_exp]
            simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
              Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.neg_im,
              Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero, neg_zero]
          have hb1 := norm_inv_sub_prime_exp_le hα (hp i) (hw_n _ (Complex.norm_exp_ofReal_mul_I (θ i)))
          have hb2 := norm_inv_sub_prime_exp_le hα (hp i)
            (hw_n _ (by simpa using Complex.norm_exp_ofReal_mul_I (-θ i)))
          calc _ ≤ Real.exp (2 * ((p i : ℝ) ^ α)⁻¹) * Real.exp (2 * ((p i : ℝ) ^ α)⁻¹) :=
                mul_le_mul hb1 hb2 (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp (4 * ((p i : ℝ) ^ α)⁻¹) := by rw [← Real.exp_add]; congr 1; ring
        have hprod_le : (∏ i, ‖(1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (Real.log (p i) : ℂ))) *
              Complex.exp ((θ i : ℂ) * I))⁻¹ *
            (1 - Complex.exp ((((-α : ℂ) + (ω : ℂ) * I) * (Real.log (p i) : ℂ))) *
              Complex.exp (-((θ i : ℂ) * I)))⁻¹‖) ≤
            Real.exp (4 * ∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) := by
          rw [mul_sum, Real.exp_sum]
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hfac_le i
        have hsum_le : (∑ i : Fin n, ((p i : ℝ) ^ α)⁻¹) ≤ S_α := by
          rw [(Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ α)⁻¹) fun i _ j _ hij => hinj hij).symm]
          exact hsum_α.sum_le_tsum (Finset.univ.image p) fun m _ => by positivity
        exact hprod_le.trans (Real.exp_le_exp.mpr (by linarith))
      rw [hlin_osc hα0 ε hp x θ]
      have hK_ne : K_α ≠ 0 := (Real.exp_pos (4 * S_α)).ne'
      have hpert_abs : |ε * torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
          (fun i => Real.log (p i)) x) θ| ≤ (c_α / 2) * Real.exp (-α * x) := by
        rw [abs_mul]
        calc |ε| * |torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
                (fun i => Real.log (p i)) x) θ|
            ≤ ε₀ * (K_α * Real.exp (-α * x)) :=
              mul_le_mul hε_le hosc_bd (abs_nonneg _) hε₀.le
          _ = (c_α / 2) * Real.exp (-α * x) := by
              simp only [ε₀]; field_simp [hK_ne]
      have hlow : -((c_α / 2) * Real.exp (-α * x)) ≤
          ε * torusSum (ampl (fun y => Real.exp (-α * y) * Real.cos (ω * y))
            (fun i => Real.log (p i)) x) θ := by
        linarith [(abs_le.mp hpert_abs).1]
      change c_α * Real.exp (-α * x) ≤ _ at hfloor
      have hpos_half : 0 < (c_α / 2) * Real.exp (-α * x) := by positivity
      linarith
    · -- Failure of `IsExpConvexFrom 0` via a `2 × 2` Hankel form
      intro hEC
      set Ω : ℝ := |ω|
      have hΩ : 0 < Ω := abs_pos.mpr hω
      have hcos_Ω : ∀ y : ℝ, Real.cos (ω * y) = Real.cos (Ω * y) := fun y => by
        simp only [Ω]
        rcases le_or_gt 0 ω with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_neg h0, show (-ω) * y = -(ω * y) by ring, Real.cos_neg]
      rcases lt_or_gt_of_ne hε with hε_neg | hε_pos
      · -- `ε < 0`: test at `t = (0, π / |ω|)` with `c = (1, −e^{α π / |ω|})`
        let t : Fin 2 → ℝ := ![0, π / Ω]
        let c : Fin 2 → ℂ := ![1, -(Real.exp (α * (π / Ω)) : ℂ)]
        have hval := hEC (Fin 2) Finset.univ t c fun i _ => by
          fin_cases i <;> simp [t]; positivity
        rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hval
        simp only [t, c, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_add, add_zero, map_one, map_neg, Complex.conj_ofReal, hcos_Ω] at hval
        have hc0 : Real.cos (Ω * 0) = 1 := by simp
        have hc1 : Real.cos (Ω * (π / Ω)) = -1 := by
          rw [mul_div_cancel₀ _ hΩ.ne', Real.cos_pi]
        have hc2 : Real.cos (Ω * (π / Ω + π / Ω)) = 1 := by
          have : Ω * (π / Ω + π / Ω) = 2 * π := by field_simp [hΩ.ne']; ring
          rw [this, Real.cos_two_pi]
        have hexp1 : Real.exp (α * (π / Ω)) * Real.exp (-α * (π / Ω)) = 1 := by
          rw [← Real.exp_add]; simp
        have hexp2 : Real.exp (α * (π / Ω)) * Real.exp (α * (π / Ω)) *
            Real.exp (-α * (π / Ω + π / Ω)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        rw [hc0, hc1, hc2] at hval
        simp only [mul_zero, Real.exp_zero, one_mul, mul_one, mul_neg,
          ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_add,
          Complex.ofReal_re] at hval
        nlinarith [hexp1, hexp2]
      · -- `ε > 0`: test at `t = (π / (2|ω|), 3π / (2|ω|))` with `c = (e^{α t₀}, −e^{α t₁})`
        let t : Fin 2 → ℝ := ![π / (2 * Ω), 3 * π / (2 * Ω)]
        let c : Fin 2 → ℂ := ![(Real.exp (α * (π / (2 * Ω))) : ℂ),
          -(Real.exp (α * (3 * π / (2 * Ω))) : ℂ)]
        have hval := hEC (Fin 2) Finset.univ t c fun i _ => by
          fin_cases i <;> simp [t] <;> positivity
        rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hval
        simp only [t, c, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_add, map_neg, Complex.conj_ofReal, hcos_Ω] at hval
        have hc00 : Real.cos (Ω * (π / (2 * Ω) + π / (2 * Ω))) = -1 := by
          have : Ω * (π / (2 * Ω) + π / (2 * Ω)) = π := by field_simp [hΩ.ne']; ring
          rw [this, Real.cos_pi]
        have hc01 : Real.cos (Ω * (π / (2 * Ω) + 3 * π / (2 * Ω))) = 1 := by
          have : Ω * (π / (2 * Ω) + 3 * π / (2 * Ω)) = 2 * π := by field_simp [hΩ.ne']; ring
          rw [this, Real.cos_two_pi]
        have hc10 : Real.cos (Ω * (3 * π / (2 * Ω) + π / (2 * Ω))) = 1 := by
          have : Ω * (3 * π / (2 * Ω) + π / (2 * Ω)) = 2 * π := by field_simp [hΩ.ne']; ring
          rw [this, Real.cos_two_pi]
        have hc11 : Real.cos (Ω * (3 * π / (2 * Ω) + 3 * π / (2 * Ω))) = -1 := by
          have : Ω * (3 * π / (2 * Ω) + 3 * π / (2 * Ω)) = π + 2 * π := by
            field_simp [hΩ.ne']; ring
          rw [this, Real.cos_add_two_pi, Real.cos_pi]
        have hexp00 : Real.exp (α * (π / (2 * Ω))) * Real.exp (α * (π / (2 * Ω))) *
            Real.exp (-α * (π / (2 * Ω) + π / (2 * Ω))) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        have hexp01 : Real.exp (α * (π / (2 * Ω))) * Real.exp (α * (3 * π / (2 * Ω))) *
            Real.exp (-α * (π / (2 * Ω) + 3 * π / (2 * Ω))) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        have hexp10 : Real.exp (α * (3 * π / (2 * Ω))) * Real.exp (α * (π / (2 * Ω))) *
            Real.exp (-α * (3 * π / (2 * Ω) + π / (2 * Ω))) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        have hexp11 : Real.exp (α * (3 * π / (2 * Ω))) * Real.exp (α * (3 * π / (2 * Ω))) *
            Real.exp (-α * (3 * π / (2 * Ω) + 3 * π / (2 * Ω))) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        rw [hc00, hc01, hc10, hc11] at hval
        simp only [mul_one, mul_neg, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
          ← Complex.ofReal_add, Complex.ofReal_re] at hval
        nlinarith [hexp00, hexp01, hexp10, hexp11]

/-! ### 7. Signed finite Laplace mixture dichotomy at `α = 1` -/

/-- Arbitrarily large partial sums of prime reciprocals on `{q prime | 5 ≤ q}`. -/
theorem exists_finset_primes_ge_five_sum_gt (B : ℝ) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ 5 ≤ q) ∧ B < ∑ q ∈ S, (q : ℝ)⁻¹ := by
  classical
  have hdiv : ¬ Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := Nat.Primes.not_summable_one_div
  have hunb : ∃ T : Finset Nat.Primes, B + 2 < ∑ p ∈ T, (1 / (p : ℝ)) := by
    by_contra hle
    push Not at hle
    exact hdiv (summable_of_sum_le (fun p => by positivity) hle)
  obtain ⟨T, hT⟩ := hunb
  let S₀ : Finset ℕ := T.image Subtype.val
  have hsum_eq : (∑ p ∈ T, (1 / (p : ℝ))) = ∑ q ∈ S₀, (q : ℝ)⁻¹ := by
    rw [Finset.sum_image (f := fun q : ℕ => (q : ℝ)⁻¹) fun a _ b _ hab => Subtype.ext hab]
    exact Finset.sum_congr rfl fun p _ => one_div _
  rw [hsum_eq] at hT
  set S := S₀.filter (fun q => 5 ≤ q)
  have hS_prop : ∀ q ∈ S, q.Prime ∧ 5 ≤ q := fun q hq => by
    obtain ⟨hq0, h5⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq0
    exact ⟨p.2, h5⟩
  have hsmall : ∑ q ∈ S₀.filter (fun q => ¬(5 ≤ q)), (q : ℝ)⁻¹ ≤ 2 := by
    have hsub : S₀.filter (fun q => ¬(5 ≤ q)) ⊆ ({2, 3} : Finset ℕ) := by
      intro q hq
      obtain ⟨hq0, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq0
      have hp2 := p.2.two_le
      have hp4 : p.1 ≠ 4 := fun h4 => by
        have hp_pr := p.2; rw [h4] at hp_pr; exact absurd hp_pr (by decide)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [Finset.sum_pair (by decide)]
    norm_num
  have hsplit := Finset.sum_filter_add_sum_filter_not S₀ (fun q => 5 ≤ q) (fun q : ℕ => (q : ℝ)⁻¹)
  exact ⟨S, hS_prop, by linarith⟩

private theorem antitoneOn_Icc_of_hasDerivAt_nonpos {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc a b, f' x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  have hmono : MonotoneOn (fun z => -f z) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := fun z => -f' z)
      (fun z hz => ((hf z hz).continuousAt.neg).continuousWithinAt) ?_ ?_
    · intro z hz
      rw [interior_Icc] at hz
      exact ((hf z (Ioo_subset_Icc_self hz)).neg).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      linarith [hf' z (Ioo_subset_Icc_self hz)]
  intro x hx y hy hxy
  have := hmono hx hy hxy
  linarith

/-- Uniform quadratic concavity bound for `t ↦ −2 log(1 + q^{−t})` on `[0, 1]` when `q ≥ 5`. -/
private theorem log_euler_pi_concavity_le {q : ℕ} (hq5 : 5 ≤ q) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (-2 * Real.log (1 + Real.exp (-t * Real.log q))) -
      (-2 * Real.log (1 + Real.exp (-s * Real.log q))) -
        (2 * Real.log q / (Real.exp (s * Real.log q) + 1)) * (t - s) ≤
      -(t - s) ^ 2 / (4 * (q : ℝ)) := by
  set L : ℝ := Real.log q
  have hq_pos : (0 : ℝ) < q := by positivity
  have hL_ge_one : 1 ≤ L := by
    have he5 : Real.exp 1 ≤ (q : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (5 : ℝ) ≤ q := by exact_mod_cast hq5
      linarith
    have := Real.log_le_log (Real.exp_pos 1) he5
    rwa [Real.log_exp] at this
  set u : ℝ → ℝ := fun x => -2 * Real.log (1 + Real.exp (-x * L))
  set u' : ℝ → ℝ := fun x => 2 * L * (Real.exp (x * L) + 1)⁻¹
  set u'' : ℝ → ℝ := fun x => -2 * L ^ 2 * Real.exp (x * L) / (Real.exp (x * L) + 1) ^ 2
  let g : ℝ → ℝ := fun x => u x - u s - u' s * (x - s) + (x - s) ^ 2 / (4 * (q : ℝ))
  let g' : ℝ → ℝ := fun x => u' x - u' s + (x - s) / (2 * (q : ℝ))
  let g'' : ℝ → ℝ := fun x => u'' x + 1 / (2 * (q : ℝ))
  have hu_deriv : ∀ x : ℝ, HasDerivAt u (u' x) x := fun x => by
    have h1 : HasDerivAt (fun x => -x * L) (-L) x := by
      simpa using (hasDerivAt_id x).neg.mul_const L
    have h2 : HasDerivAt (fun x => 1 + Real.exp (-x * L)) (Real.exp (-x * L) * (-L)) x := by
      simpa using (Real.hasDerivAt_exp (-x * L)).comp x h1 |>.const_add 1
    have h3 : HasDerivAt (fun x => Real.log (1 + Real.exp (-x * L)))
        ((Real.exp (-x * L) * (-L)) / (1 + Real.exp (-x * L))) x :=
      h2.log (by positivity)
    have h4 := h3.const_mul (-2 : ℝ)
    refine h4.congr_deriv ?_
    dsimp only [u']
    have he_inv : Real.exp (-x * L) * Real.exp (x * L) = 1 := by rw [← Real.exp_add]; simp
    have hd2 : (Real.exp (x * L) + 1) ≠ 0 := by positivity
    have hden : (Real.exp (x * L) + 1) * Real.exp (-x * L) = 1 + Real.exp (-x * L) := by
      linear_combination he_inv
    rw [← hden]
    field_simp [hd2, (Real.exp_pos (-x * L)).ne']
  have hu'_deriv : ∀ x : ℝ, HasDerivAt u' (u'' x) x := fun x => by
    have h1 : HasDerivAt (fun x => x * L) L x := by simpa using (hasDerivAt_id x).mul_const L
    have h2 : HasDerivAt (fun x => Real.exp (x * L) + 1) (Real.exp (x * L) * L) x := by
      simpa [Function.comp_def] using ((Real.hasDerivAt_exp (x * L)).comp x h1).add_const 1
    have h3 : HasDerivAt (fun x => (Real.exp (x * L) + 1)⁻¹)
        (-(Real.exp (x * L) * L) / (Real.exp (x * L) + 1) ^ 2) x :=
      h2.inv (by positivity)
    refine (h3.const_mul (2 * L)).congr_deriv ?_
    dsimp only [u'']; ring
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (g' x) x := fun x => by
    have hlin : HasDerivAt (fun x => u' s * (x - s)) (u' s) x := by
      simpa using ((hasDerivAt_id x).sub_const s).const_mul (u' s)
    have hquad : HasDerivAt (fun x => (x - s) ^ 2 / (4 * (q : ℝ))) ((x - s) / (2 * (q : ℝ))) x := by
      have hsub : HasDerivAt (fun x => x - s) 1 x := (hasDerivAt_id x).sub_const s
      have hp := (hsub.pow 2).div_const (4 * (q : ℝ))
      refine hp.congr_deriv ?_
      field_simp [hq_pos.ne']; ring
    exact (((hu_deriv x).sub_const (u s)).sub hlin).add hquad
  have hg'_deriv : ∀ x : ℝ, HasDerivAt g' (g'' x) x := fun x => by
    have hlin : HasDerivAt (fun x => (x - s) / (2 * (q : ℝ))) (1 / (2 * (q : ℝ))) x :=
      (((hasDerivAt_id x).sub_const s).div_const (2 * (q : ℝ))).congr_deriv (by ring)
    exact ((hu'_deriv x).sub_const (u' s)).add hlin
  have hg''_nonpos : ∀ x ∈ Icc (0 : ℝ) 1, g'' x ≤ 0 := fun x hx => by
    set Z : ℝ := Real.exp (x * L)
    have hZ_lo : 1 ≤ Z := Real.one_le_exp (mul_nonneg hx.1 (by linarith))
    have hZ_hi : Z ≤ q := by
      rw [← Real.exp_log hq_pos]
      exact Real.exp_le_exp.mpr (by nlinarith [hx.2])
    have hq1 : (1 : ℝ) ≤ q := by linarith
    have hquad_Z : (Z + 1) ^ 2 ≤ 4 * (q : ℝ) * Z := by
      have hid : 4 * (q : ℝ) * Z - (Z + 1) ^ 2 =
          Z * ((q : ℝ) - Z) + (Z - 1) * (3 * (q : ℝ) - 2) + 3 * ((q : ℝ) - 1) := by ring
      nlinarith
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hnum_ge : (Z + 1) ^ 2 ≤ 4 * (q : ℝ) * (L ^ 2 * Z) := by
      calc (Z + 1) ^ 2 ≤ 4 * (q : ℝ) * Z := hquad_Z
        _ ≤ 4 * (q : ℝ) * (L ^ 2 * Z) := by nlinarith
    dsimp only [g'', u'']
    change -2 * L ^ 2 * Z / (Z + 1) ^ 2 + 1 / (2 * (q : ℝ)) ≤ 0
    have hd_pos : 0 < (Z + 1) ^ 2 * (2 * (q : ℝ)) := by positivity
    have hcomb : -2 * L ^ 2 * Z / (Z + 1) ^ 2 + 1 / (2 * (q : ℝ)) =
        ((Z + 1) ^ 2 - 4 * (q : ℝ) * (L ^ 2 * Z)) / ((Z + 1) ^ 2 * (2 * (q : ℝ))) := by
      field_simp [(show Z + 1 ≠ 0 by positivity), hq_pos.ne']; ring
    rw [hcomb]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd_pos.le
  have hg'_anti : AntitoneOn g' (Icc (0 : ℝ) 1) :=
    antitoneOn_Icc_of_hasDerivAt_nonpos (fun x hx => hg'_deriv x) hg''_nonpos
  have hg_s : g s = 0 := by simp [g]
  have hg'_s : g' s = 0 := by simp [g']
  have hg_le : g t ≤ 0 := by
    rcases le_total s t with hst | hts
    · have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
      have hanti := antitoneOn_Icc_of_hasDerivAt_nonpos (a := s) (b := t)
        (fun x hx => hg_deriv x) (fun x hx => by
          have := hg'_anti hs (hsub hx) hx.1
          linarith [hg'_s])
      simpa [hg_s] using hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    · have hsub : Icc t s ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩
      have hanti := antitoneOn_Icc_of_hasDerivAt_nonpos (a := t) (b := s)
        (f := fun x => -g x) (f' := fun x => -g' x)
        (fun x _ => (hg_deriv x).neg) (fun x hx => by
          have := hg'_anti (hsub hx) hs hx.2
          linarith [hg'_s])
      have := hanti ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
      linarith [hg_s]
  dsimp only [g, u, u'] at hg_le
  rw [div_eq_mul_inv (2 * L), neg_div]
  linarith

/-- **Signed finite Laplace mixture dichotomy on `(0, 1]`.**
For strictly increasing exponents `0 < α₀ < … < α_{m−1} ≤ 1`, a finite linear combination
`∑_r c_r e^{−α_r y}` is all-base torus-positive if and only if every coefficient `c_r` is
nonnegative (and hence if and only if it is exponentially convex). -/
theorem laplaceMixture_torusPositive_iff_nonneg {m : ℕ} {α c : Fin m → ℝ}
    (hmono : StrictMono α) (hα0 : ∀ r, 0 < α r) (hα1 : ∀ r, α r ≤ 1) :
    IsAllBaseTorusPositive (fun y => ∑ r, c r * Real.exp (-α r * y)) ↔ ∀ r, 0 ≤ c r := by
  -- Shared torus-sum evaluation of `∑_r c_r e^{−α_r y}`
  have htorus_sum : ∀ {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, (p i).Prime) (x : ℝ) (θ : Fin n → ℝ),
      torusSum (ampl (fun y => ∑ r, c r * Real.exp (-α r * y)) (fun i => Real.log (p i)) x) θ =
        ∑ r, c r * torusSum (ampl (fun y => Real.exp (-α r * y)) (fun i => Real.log (p i)) x) θ := by
    intro n p hp x θ
    have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    have hsum_r : ∀ r : Fin m,
        Summable (fun k => c r * (ampl (fun y => Real.exp (-α r * y))
          (fun i => Real.log (p i)) x k * chiProd θ k)) := fun r =>
      (summable_term (traceSummable_ampl (hα0 r)
        (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl) θ).mul_left (c r)
    rw [torusSum]
    have hpt : ∀ k, ampl (fun y => ∑ r, c r * Real.exp (-α r * y)) (fun i => Real.log (p i)) x k *
          chiProd θ k =
        ∑ r, c r * (ampl (fun y => Real.exp (-α r * y)) (fun i => Real.log (p i)) x k *
          chiProd θ k) := fun k => by
      simp only [ampl, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp_rw [hpt]
    rw [Summable.tsum_finsetSum fun r _ => hsum_r r]
    exact Finset.sum_congr rfl fun r _ => by rw [tsum_mul_left, ← torusSum]
  constructor
  · intro hpos r₁
    by_contra hneg_r₁
    push Not at hneg_r₁
    by_cases hother : ∀ r, r ≠ r₁ → c r = 0
    · -- Single nonzero mode: evaluate `hpos.nonneg 0`
      have h0 := hpos.nonneg 0
      rw [Finset.sum_eq_single r₁ (fun r _ hr => by simp [hother r hr])
        (fun h => absurd (Finset.mem_univ r₁) h)] at h0
      simp only [mul_zero, Real.exp_zero, mul_one] at h0
      linarith
    · push Not at hother
      obtain ⟨r₂, hr₂_ne, _⟩ := hother
      set U_other := Finset.univ.erase r₁
      have hU_nonempty : U_other.Nonempty := ⟨r₂, Finset.mem_erase.mpr ⟨hr₂_ne, Finset.mem_univ _⟩⟩
      obtain ⟨r_min, hr_min_mem, hr_min_le⟩ :=
        U_other.exists_min_image (fun r => (α r - α r₁) ^ 2) hU_nonempty
      set gap : ℝ := (α r_min - α r₁) ^ 2
      have hgap_pos : 0 < gap := by
        have hne : r_min ≠ r₁ := (Finset.mem_erase.mp hr_min_mem).1
        have hα_ne : α r_min ≠ α r₁ := hmono.injective.ne hne
        exact sq_pos_of_ne_zero (sub_ne_zero.mpr hα_ne)
      set C_tot : ℝ := ∑ r ∈ U_other, |c r| + 1
      have hC_pos : 0 < C_tot := by
        have : 0 ≤ ∑ r ∈ U_other, |c r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        simp only [C_tot]; linarith
      set B : ℝ := (4 / gap) * (|Real.log (-c r₁ / (2 * C_tot))| + 1)
      obtain ⟨S, hS, hB⟩ := exists_finset_primes_ge_five_sum_gt B
      let e : Fin S.card ≃ S := S.equivFin.symm
      let p : Fin S.card → ℕ := fun i => (e i : ℕ)
      have hp : ∀ i, (p i).Prime := fun i => (hS _ (e i).2).1
      have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
      have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
      let θ : Fin S.card → ℝ := fun _ => π
      -- Evaluate `torusSum` of `e^{−α y}` at `θ = π` as `exp(L_S(α, x))`
      let L_S : ℝ → ℝ → ℝ := fun β x =>
        -β * x + ∑ q ∈ S, (-2 * Real.log (1 + Real.exp (-β * Real.log q)))
      have htorus_pi : ∀ (β : ℝ), 0 < β → ∀ x : ℝ,
          torusSum (ampl (fun y => Real.exp (-β * y)) (fun i => Real.log (p i)) x) θ =
            Real.exp (L_S β x) := fun β hβ x => by
        rw [torusSum_ampl_exp_neg hβ hℓ x θ]
        simp only [L_S, Real.exp_add, Real.exp_sum]
        congr 1
        have hprod_pt : (∏ i, ‖1 - (Real.exp (-β * Real.log (p i)) : ℂ) *
            Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2) =
            ∏ i, Real.exp (-2 * Real.log (1 + Real.exp (-β * Real.log (e i : ℕ)))) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [θ, p, Complex.exp_pi_mul_I, mul_neg, mul_one, sub_neg_eq_add]
          have hnorm : ‖(1 : ℂ) + (Real.exp (-β * Real.log (e i : ℕ)) : ℂ)‖ =
              1 + Real.exp (-β * Real.log (e i : ℕ)) := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
              Real.norm_of_nonneg (by positivity)]
          rw [hnorm]
          have hd_pos : 0 < 1 + Real.exp (-β * Real.log (e i : ℕ)) := by positivity
          rw [show -2 * Real.log (1 + Real.exp (-β * Real.log (e i : ℕ))) =
              -(2 * Real.log (1 + Real.exp (-β * Real.log (e i : ℕ)))) by ring,
            Real.exp_neg, show (2 : ℝ) * Real.log (1 + Real.exp (-β * Real.log (e i : ℕ))) =
              Real.log ((1 + Real.exp (-β * Real.log (e i : ℕ))) ^ 2) by
              rw [Real.log_pow]; norm_num,
            Real.exp_log (pow_pos hd_pos 2), inv_pow]
        rw [hprod_pt, Equiv.prod_comp e (fun z : S =>
          Real.exp (-2 * Real.log (1 + Real.exp (-β * Real.log (z : ℕ))))),
          Finset.prod_coe_sort S (fun q : ℕ =>
            Real.exp (-2 * Real.log (1 + Real.exp (-β * Real.log q))))]
      set x_S : ℝ := ∑ q ∈ S, 2 * Real.log q / (Real.exp (α r₁ * Real.log q) + 1)
      have hdiff_le : ∀ r ∈ U_other,
          L_S (α r) x_S - L_S (α r₁) x_S ≤ -(gap / 4) * ∑ q ∈ S, (q : ℝ)⁻¹ := fun r hr => by
        have hgap_r : gap ≤ (α r - α r₁) ^ 2 := hr_min_le r hr
        have hrewrite : L_S (α r) x_S - L_S (α r₁) x_S =
            ∑ q ∈ S, ((-2 * Real.log (1 + Real.exp (-α r * Real.log q))) -
              (-2 * Real.log (1 + Real.exp (-α r₁ * Real.log q))) -
              (2 * Real.log q / (Real.exp (α r₁ * Real.log q) + 1)) * (α r - α r₁)) := by
          simp only [L_S, x_S]
          have hlin_x : -α r * (∑ q ∈ S, 2 * Real.log q / (Real.exp (α r₁ * Real.log q) + 1)) -
              (-α r₁ * (∑ q ∈ S, 2 * Real.log q / (Real.exp (α r₁ * Real.log q) + 1))) =
              -∑ q ∈ S, (2 * Real.log q / (Real.exp (α r₁ * Real.log q) + 1)) * (α r - α r₁) := by
            rw [← sub_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun q _ => by ring
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          linarith
        rw [hrewrite, Finset.mul_sum]
        refine Finset.sum_le_sum fun q hq => ?_
        have hq5 : 5 ≤ q := (hS q hq).2
        have hconc := log_euler_pi_concavity_le hq5
          ⟨(hα0 r₁).le, hα1 r₁⟩ ⟨(hα0 r).le, hα1 r⟩
        have hstep : -(α r - α r₁) ^ 2 / (4 * (q : ℝ)) ≤ -(gap / 4) * (q : ℝ)⁻¹ := by
          have hq_pos : (0 : ℝ) < q := by positivity
          rw [show -(gap / 4) * (q : ℝ)⁻¹ = -gap / (4 * (q : ℝ)) by ring]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        exact hconc.trans hstep
      have hexp_small : ∀ r ∈ U_other,
          Real.exp (L_S (α r) x_S - L_S (α r₁) x_S) < -c r₁ / (2 * C_tot) := fun r hr => by
        have h1 := hdiff_le r hr
        have h2 : -(gap / 4) * ∑ q ∈ S, (q : ℝ)⁻¹ < -(gap / 4) * B := by
          have := mul_lt_mul_of_pos_left hB (div_pos hgap_pos (by norm_num : (0 : ℝ) < 4))
          linarith
        have h3 : -(gap / 4) * B = -(|Real.log (-c r₁ / (2 * C_tot))| + 1) := by
          simp only [B]; field_simp [hgap_pos.ne']
        have hpos_rhs : 0 < -c r₁ / (2 * C_tot) := div_pos (by linarith) (by positivity)
        rw [← Real.exp_log hpos_rhs]
        refine Real.exp_lt_exp.mpr ?_
        have := neg_le_abs (Real.log (-c r₁ / (2 * C_tot)))
        linarith
      -- Assemble `torusSum < 0`
      have hval_neg : torusSum (ampl (fun y => ∑ r, c r * Real.exp (-α r * y))
          (fun i => Real.log (p i)) x_S) θ < 0 := by
        rw [htorus_sum hp x_S θ]
        have hpt_r : ∀ r : Fin m,
            c r * torusSum (ampl (fun y => Real.exp (-α r * y)) (fun i => Real.log (p i)) x_S) θ =
              Real.exp (L_S (α r₁) x_S) *
                (c r * Real.exp (L_S (α r) x_S - L_S (α r₁) x_S)) := fun r => by
          rw [htorus_pi (α r) (hα0 r) x_S]
          have : Real.exp (L_S (α r) x_S) =
              Real.exp (L_S (α r₁) x_S) * Real.exp (L_S (α r) x_S - L_S (α r₁) x_S) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
        simp_rw [hpt_r, ← Finset.mul_sum]
        refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₁)]
        simp only [sub_self, Real.exp_zero, mul_one]
        have hsum_other : (∑ r ∈ U_other, c r * Real.exp (L_S (α r) x_S - L_S (α r₁) x_S)) ≤
            -c r₁ / 2 := by
          calc (∑ r ∈ U_other, c r * Real.exp (L_S (α r) x_S - L_S (α r₁) x_S))
              ≤ ∑ r ∈ U_other, |c r| * Real.exp (L_S (α r) x_S - L_S (α r₁) x_S) := by
                refine Finset.sum_le_sum fun r _ => ?_
                exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
            _ ≤ ∑ r ∈ U_other, |c r| * (-c r₁ / (2 * C_tot)) := by
                refine Finset.sum_le_sum fun r hr => ?_
                exact mul_le_mul_of_nonneg_left (hexp_small r hr).le (abs_nonneg _)
            _ = (∑ r ∈ U_other, |c r|) * (-c r₁ / (2 * C_tot)) := (Finset.sum_mul _ _ _).symm
            _ ≤ C_tot * (-c r₁ / (2 * C_tot)) :=
                mul_le_mul_of_nonneg_right (by simp only [C_tot]; linarith)
                  (div_nonneg (by linarith) (by positivity))
            _ = -c r₁ / 2 := by field_simp [hC_pos.ne']
        linarith
      exact absurd (hpos S.card p hp hinj x_S θ) (not_le.mpr hval_neg)
  · intro hc_nn n p hp _ x θ
    rw [htorus_sum hp x θ]
    have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    refine Finset.sum_nonneg fun r _ => mul_nonneg (hc_nn r) ?_
    rw [torusSum_ampl_exp_neg (hα0 r) hℓ x θ]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => by positivity)

/-- **Supercritical failure of Laplace-mixture Bernstein (`1 < α₀ < α₁ < α₂`).**
Above `1`, subtracting a small middle exponential `e^{−α₀ y} − ε e^{−α₁ y} + e^{−α₂ y}` remains
strictly all-base torus-positive while violating `IsExpConvexFrom 0`. -/
theorem exists_supercritical_laplaceMixture_not_expConvex {α₀ α₁ α₂ : ℝ}
    (h1 : 1 < α₀) (h01 : α₀ < α₁) (h12 : α₁ < α₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
        ∀ (x : ℝ) (θ : Fin n → ℝ),
          0 < torusSum (ampl (fun y => Real.exp (-α₀ * y) - ε * Real.exp (-α₁ * y) +
            Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x) θ) ∧
      ¬ IsExpConvexFrom 0 (fun y => Real.exp (-α₀ * y) - ε * Real.exp (-α₁ * y) +
        Real.exp (-α₂ * y)) := by
  have hα₀_pos : 0 < α₀ := by linarith
  have hα₁_gt1 : 1 < α₁ := by linarith
  have hα₁_pos : 0 < α₁ := by linarith
  have hα₂_gt1 : 1 < α₂ := by linarith
  have hα₂_pos : 0 < α₂ := by linarith
  have hsum_α₁ : Summable (fun m : ℕ => ((m : ℝ) ^ α₁)⁻¹) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr hα₁_gt1
  set c_min : ℝ := min (Real.exp (-2 * ∑' m : ℕ, ((m : ℝ) ^ α₀)⁻¹))
    (Real.exp (-2 * ∑' m : ℕ, ((m : ℝ) ^ α₂)⁻¹))
  have hc_pos : 0 < c_min := lt_min (Real.exp_pos _) (Real.exp_pos _)
  set K₁ : ℝ := Real.exp (4 * ∑' m : ℕ, ((m : ℝ) ^ α₁)⁻¹)
  have hK₁_pos : 0 < K₁ := Real.exp_pos _
  set ε₀ : ℝ := c_min / (2 * K₁)
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, fun ε hε0 hε_le => ⟨fun n p hp hinj x θ => ?_, ?_⟩⟩
  · have hℓ : ∀ i, 0 < Real.log (p i) := fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)
    have hts0 : TraceSummable (ampl (fun y => Real.exp (-α₀ * y)) (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα₀_pos (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
    have hts1 : TraceSummable (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα₁_pos (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
    have hts2 : TraceSummable (ampl (fun y => Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x) :=
      traceSummable_ampl hα₂_pos (fun y _ => by rw [abs_of_pos (Real.exp_pos _), one_mul]) hℓ le_rfl
    have hlin : torusSum (ampl (fun y => Real.exp (-α₀ * y) - ε * Real.exp (-α₁ * y) +
          Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x) θ =
        torusSum (ampl (fun y => Real.exp (-α₀ * y)) (fun i => Real.log (p i)) x) θ -
          ε * torusSum (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x) θ +
          torusSum (ampl (fun y => Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x) θ := by
      have hpt : ∀ k, ampl (fun y => Real.exp (-α₀ * y) - ε * Real.exp (-α₁ * y) +
            Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x k * chiProd θ k =
          (ampl (fun y => Real.exp (-α₀ * y)) (fun i => Real.log (p i)) x k * chiProd θ k -
            ε * (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x k * chiProd θ k)) +
            ampl (fun y => Real.exp (-α₂ * y)) (fun i => Real.log (p i)) x k * chiProd θ k :=
        fun k => by simp only [ampl]; ring
      rw [torusSum, torusSum, torusSum, torusSum]
      simp_rw [hpt]
      rw [Summable.tsum_add ((summable_term hts0 θ).sub ((summable_term hts1 θ).mul_left ε))
        (summable_term hts2 θ),
        Summable.tsum_sub (summable_term hts0 θ) ((summable_term hts1 θ).mul_left ε),
        tsum_mul_left]
    rw [hlin]
    have hmin0 : c_min ≤ Real.exp (-2 * ∑' m : ℕ, ((m : ℝ) ^ α₀)⁻¹) := min_le_left _ _
    have hfloor0 := (mul_le_mul_of_nonneg_right hmin0 (Real.exp_pos (-α₀ * x)).le).trans
      (torusSum_exp_neg_ge_euler_floor h1 hp hinj x θ)
    have hmin2 : c_min ≤ Real.exp (-2 * ∑' m : ℕ, ((m : ℝ) ^ α₂)⁻¹) := min_le_right _ _
    have hfloor2 := (mul_le_mul_of_nonneg_right hmin2 (Real.exp_pos (-α₂ * x)).le).trans
      (torusSum_exp_neg_ge_euler_floor hα₂_gt1 hp hinj x θ)
    -- Upper bound on `torusSum` of `e^{−α₁ y}`
    have hceil1 : torusSum (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x) θ ≤
        K₁ * Real.exp (-α₁ * x) := by
      rw [torusSum_ampl_exp_neg hα₁_pos hℓ x θ, mul_comm K₁]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hfac_le : ∀ i : Fin n,
          ‖1 - (Real.exp (-α₁ * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2 ≤
            Real.exp (4 * ((p i : ℝ) ^ α₁)⁻¹) := fun i => by
        have hw : ‖(Real.exp (-α₁ * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ =
            Real.exp (-α₁ * Real.log (p i)) := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le]
        have hb := norm_inv_sub_prime_exp_le hα₁_gt1 (hp i) hw
        rw [norm_inv] at hb
        calc ‖1 - (Real.exp (-α₁ * Real.log (p i)) : ℂ) * Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2
            ≤ Real.exp (2 * ((p i : ℝ) ^ α₁)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
          _ = Real.exp (4 * ((p i : ℝ) ^ α₁)⁻¹) := by
              rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hprod_le : (∏ i, ‖1 - (Real.exp (-α₁ * Real.log (p i)) : ℂ) *
          Complex.exp ((θ i : ℂ) * I)‖⁻¹ ^ 2) ≤
          Real.exp (4 * ∑ i : Fin n, ((p i : ℝ) ^ α₁)⁻¹) := by
        rw [mul_sum, Real.exp_sum]
        exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => hfac_le i
      have hsum_le : (∑ i : Fin n, ((p i : ℝ) ^ α₁)⁻¹) ≤ ∑' m : ℕ, ((m : ℝ) ^ α₁)⁻¹ := by
        rw [(Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ α₁)⁻¹) fun i _ j _ hij => hinj hij).symm]
        exact hsum_α₁.sum_le_tsum (Finset.univ.image p) fun m _ => by positivity
      exact hprod_le.trans (Real.exp_le_exp.mpr (by linarith))
    have hexp_mid : Real.exp (-α₁ * x) ≤ Real.exp (-α₀ * x) + Real.exp (-α₂ * x) := by
      rcases le_or_gt 0 x with hx | hx
      · have : Real.exp (-α₁ * x) ≤ Real.exp (-α₀ * x) := Real.exp_le_exp.mpr (by nlinarith)
        linarith [Real.exp_pos (-α₂ * x)]
      · have : Real.exp (-α₁ * x) ≤ Real.exp (-α₂ * x) := Real.exp_le_exp.mpr (by nlinarith)
        linarith [Real.exp_pos (-α₀ * x)]
    have hmid_le : ε * torusSum (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x) θ ≤
        (c_min / 2) * (Real.exp (-α₀ * x) + Real.exp (-α₂ * x)) := by
      calc ε * torusSum (ampl (fun y => Real.exp (-α₁ * y)) (fun i => Real.log (p i)) x) θ
          ≤ ε₀ * (K₁ * Real.exp (-α₁ * x)) :=
            mul_le_mul hε_le hceil1 (mul_nonneg (Real.exp_pos _).le
              (Finset.prod_nonneg fun _ _ => by positivity) |>.trans
              (torusSum_ampl_exp_neg hα₁_pos hℓ x θ).symm.le) hε₀.le
        _ = (c_min / 2) * Real.exp (-α₁ * x) := by simp only [ε₀]; field_simp [hK₁_pos.ne']
        _ ≤ (c_min / 2) * (Real.exp (-α₀ * x) + Real.exp (-α₂ * x)) :=
            mul_le_mul_of_nonneg_left hexp_mid (by positivity)
    have hpos_sum : 0 < (c_min / 2) * (Real.exp (-α₀ * x) + Real.exp (-α₂ * x)) := by positivity
    linarith
  · -- Failure of `IsExpConvexFrom 0` on `(0, 1, 2)` via Vandermonde annihilation of `α₀, α₂`
    intro hEC
    set r₀ : ℝ := Real.exp (-α₀)
    set r₁ : ℝ := Real.exp (-α₁)
    set r₂ : ℝ := Real.exp (-α₂)
    let t : Fin 3 → ℝ := ![0, 1, 2]
    let d : Fin 3 → ℝ := ![r₀ * r₂, -(r₀ + r₂), 1]
    let c : Fin 3 → ℂ := fun i => (d i : ℂ)
    have hval := hEC (Fin 3) Finset.univ t c fun i _ => by
      fin_cases i <;> simp [t]
    have hmode_sum : ∀ (β : ℝ),
        (∑ i : Fin 3, ∑ j : Fin 3, d i * d j * Real.exp (-β * (0 + t i + t j))) =
          ((Real.exp (-β) - r₀) * (Real.exp (-β) - r₂)) ^ 2 := fun β => by
      rw [Fin.sum_univ_three]
      simp only [Fin.sum_univ_three, t, d, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_add, add_zero]
      have he0 : Real.exp (-β * 0) = 1 := by simp
      have he1 : Real.exp (-β * 1) = Real.exp (-β) := by simp
      have he2 : Real.exp (-β * (1 + 1)) = Real.exp (-β) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have he2' : Real.exp (-β * 2) = Real.exp (-β) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have he3 : Real.exp (-β * (1 + 2)) = Real.exp (-β) ^ 3 := by
        rw [pow_succ, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have he3' : Real.exp (-β * (2 + 1)) = Real.exp (-β) ^ 3 := by
        rw [pow_succ, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have he4 : Real.exp (-β * (2 + 2)) = Real.exp (-β) ^ 4 := by
        rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, sq, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      rw [he0, he1, he2, he2', he3, he3', he4]
      ring
    have hre_eq : (∑ i : Fin 3, ∑ j : Fin 3, c i * conj (c j) *
        ((Real.exp (-α₀ * (0 + t i + t j)) - ε * Real.exp (-α₁ * (0 + t i + t j)) +
          Real.exp (-α₂ * (0 + t i + t j)) : ℝ) : ℂ)).re =
        -ε * ((r₁ - r₀) * (r₁ - r₂)) ^ 2 := by
      have h1 : (∑ i : Fin 3, ∑ j : Fin 3, c i * conj (c j) *
          ((Real.exp (-α₀ * (0 + t i + t j)) - ε * Real.exp (-α₁ * (0 + t i + t j)) +
            Real.exp (-α₂ * (0 + t i + t j)) : ℝ) : ℂ)).re =
          (∑ i : Fin 3, ∑ j : Fin 3, d i * d j * Real.exp (-α₀ * (0 + t i + t j))) -
            ε * (∑ i : Fin 3, ∑ j : Fin 3, d i * d j * Real.exp (-α₁ * (0 + t i + t j))) +
            (∑ i : Fin 3, ∑ j : Fin 3, d i * d j * Real.exp (-α₂ * (0 + t i + t j))) := by
        simp only [c, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.re_sum,
          Complex.ofReal_re]
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
        congr 1
        · congr 1
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h1, hmode_sum α₀, hmode_sum α₁, hmode_sum α₂]
      simp only [r₀, r₁, r₂, sub_self, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      ring
    rw [hre_eq] at hval
    have hr₀_ne : r₁ - r₀ ≠ 0 := sub_ne_zero.mpr (Real.exp_injective.ne (by linarith))
    have hr₂_ne : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr (Real.exp_injective.ne (by linarith))
    have hsq_pos : 0 < ((r₁ - r₀) * (r₁ - r₂)) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hr₀_ne hr₂_ne)
    nlinarith

#print axioms heckePositive_iff_expConvex_of_lt_half
#print axioms exists_heckePositive_not_torusPositive_ge_half
#print axioms hasSum_cosSum_mul_cosSum_geom
#print axioms torusSum_mul_geom_eq_integral
#print axioms IsAllBaseTorusPositive.mul_exp_neg
#print axioms eq_zero_of_torusPositive_of_lt_min_one
#print axioms oscillatory_bernstein_dichotomy
#print axioms laplaceMixture_torusPositive_iff_nonneg
#print axioms exists_supercritical_laplaceMixture_not_expConvex

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
