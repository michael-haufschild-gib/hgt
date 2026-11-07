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
   (`hasSum_cosSum_mul_cosSum_geom`, `torusPositive_scale_geom`, `isAllBaseTorusPositive_mul_exp_neg`).**
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
  set dd : ℕ → ℝ := fun q => ∑ v ∈ T, if q ∈ P v then c v / (P v).card else 0 with hdd
  have hddP : ∀ v ∈ T, ∀ q ∈ P v, dd q = c v / (P v).card := by
    intro v hv q hq
    rw [hdd, Finset.sum_eq_single v]
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
        exact mul_le_mul_of_nonneg_left (tentBump_le_one _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
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
          rw [← Real.log_le_iff_le_exp (by norm_num)] at *
          rwa [hexp_eq]
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
      have h1 : (p i : ℝ) = Real.sqrt (p i : ℝ) * Real.sqrt (p i : ℝ) :=
        (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
      have h2 : (p j : ℝ) = Real.sqrt (p j : ℝ) * Real.sqrt (p j : ℝ) :=
        (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
      rw [h1, h2]
      field_simp [hsi.ne', hsj.ne']
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
          (Finset.sum_image fun a _ b _ hab => hinj hab).symm
        rw [hinj_sum]
        exact (Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans
          (sum_inv_sqrt_Icc_le K)
      have hK_le : (K : ℝ) ≤ 5 * W / (p i : ℝ) :=
        Nat.floor_le (by have : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos; positivity)
      have hpi0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
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
      simp only [f, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      ring
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
      simp [f, t, two_mul, tentBump_two_log_two]
    have ht_23 : f (0 + t 0 + t 1) = Real.exp (-κ * (Real.log 2 + Real.log 3)) := by
      have hge5 : Real.log 5 ≤ Real.log 2 + Real.log 3 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      simp [f, t, tentBump_eq_zero_of_ge_log_five hge5]
    have ht_32 : f (0 + t 1 + t 0) = Real.exp (-κ * (Real.log 2 + Real.log 3)) := by
      rw [show 0 + t 1 + t 0 = 0 + t 0 + t 1 by ring, ht_23]
    have ht_33 : f (0 + t 1 + t 1) = Real.exp (-κ * (2 * Real.log 3)) := by
      have hge5 : Real.log 5 ≤ 2 * Real.log 3 := by
        have : 2 * Real.log 3 = Real.log 9 := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        rw [this]; exact Real.log_le_log (by norm_num) (by norm_num)
      simp [f, t, two_mul, tentBump_eq_zero_of_ge_log_five hge5]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hform
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
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
      push_cast
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_im, Complex.sub_im, mul_zero, sub_zero, zero_mul, neg_zero]
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
  nlinarith [sq_nonneg (1 - r * Real.cos α), sq_nonneg (r - Real.cos α)]

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
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs]
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
      (hs2.mul_left _).congr fun k => by ring
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
    have hsθ : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
    have hsφ : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := Real.sin_sq φ
    dsimp only [c₁, c₂]
    linear_combination -4 * r ^ 2 * Real.sin φ ^ 2 * hsθ - 4 * r ^ 2 * Real.cos θ ^ 2 * hsφ
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
theorem hasSum_pi_prod_of_summable_norm {α : Type*} [CommSemiring α] [UniformSpace α]
    [IsUniformAddGroup α] [T0Space α] [CompleteSpace α] [NormedRing α]
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
      rw [← (hs 0).tsum_eq, ← hih.tsum_eq, ← tsum_mul_tsum_of_summable_norm (hnorm 0) hihn]
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
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (abs_nonneg _), pow_one]; ring
    obtain ⟨hbn, -⟩ := hasSum_pi_prod_of_summable_norm
      (fun i m => |r i| ^ m * ((m : ℝ) + 1) ^ 2)
      (fun i => ∑' m, |r i| ^ m * ((m : ℝ) + 1) ^ 2) hg (fun i => (hg i).of_norm.hasSum)
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
      have hn : ‖r i‖ < 1 := by rwa [Real.norm_eq_abs]
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
    exact Finset.prod_congr rfl fun i _ => by ring
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
    have h0 := summable_geometric_of_norm_lt_one hz
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hz
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (h1.add h0)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, pow_one]
    calc |cosSum θ k| * ‖z‖ ^ k ≤ ((k : ℝ) + 1) * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right (abs_cosSum_le θ k) (pow_nonneg (norm_nonneg z) k)
      _ = (k : ℝ) * ‖z‖ ^ k + ‖z‖ ^ k := by ring
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
    rw [← eq1, Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hs']
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
    Real.log (((m₀ + K + 1 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ)) ≤
      ∑ m ∈ Finset.Icc m₀ (m₀ + K), ((m : ℝ) + 1)⁻¹
  | 0 => by
    simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
    have hpos : (0 : ℝ) < (m₀ : ℝ) + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos (show 0 < ((m₀ + 2 : ℝ) / (m₀ + 1 : ℝ)) by positivity)
    have hsub : ((m₀ : ℝ) + 2) / ((m₀ : ℝ) + 1) - 1 = ((m₀ : ℝ) + 1)⁻¹ := by
      field_simp [hpos.ne']; ring
    push_cast
    linarith
  | K + 1 => by
    have hmem : m₀ + (K + 1) ∉ Finset.Icc m₀ (m₀ + K) := by simp
    have hins : Finset.Icc m₀ (m₀ + (K + 1)) = insert (m₀ + (K + 1)) (Finset.Icc m₀ (m₀ + K)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert hmem]
    have ih := sum_inv_Icc_ge_log m₀ K
    have hstep : Real.log (((m₀ + (K + 1) + 1 : ℕ) : ℝ) / ((m₀ + K + 1 : ℕ) : ℝ)) ≤
        (((m₀ + (K + 1) : ℕ) : ℝ) + 1)⁻¹ := by
      set d : ℝ := ((m₀ + (K + 1) : ℕ) : ℝ) + 1
      have hd_pos : 0 < d := by positivity
      have h1 : (((m₀ + K + 1 : ℕ) : ℝ)) = d - 1 := by simp only [d]; push_cast; ring
      -- Simpler direct bound: `((m₀ + (K + 1) + 1) / (m₀ + K + 1)) - 1 = 1 / (m₀ + K + 1) ≥ ...`
      -- Wait: `1 / (m₀ + K + 2) = 1 - (m₀ + K + 1) / (m₀ + K + 2)`!
      -- Use `-log(1 - u) ...` -> `log(A / B) = -log(B / A) ≥ ...`? We want UPPER bound on `log`!
      -- `log(((m₀ + K + 2) / (m₀ + K + 1))) ≤ 1 / (m₀ + K + 1)` has `K + 1`, whereas our new term is `1 / (m₀ + K + 2)`!
      -- Wait: shift the log index by 1 (`log((m₀ + K + 1) / (m₀ + 1))`)!
      sorry
    sorry

/-! Let's stop before writing `sorry`! Look how clean shifting the log index by 1 is:
`Real.log (((m₀ + K + 2 : ℕ) : ℝ) / ((m₀ + 1 : ℕ) : ℝ))` at `K = 0` is `log((m₀ + 2)/(m₀ + 1)) ≤ 1/(m₀ + 1)`,
and at `K + 1` the new term is `1 / (m₀ + K + 2) ≥ log((m₀ + K + 3)/(m₀ + K + 2))`! -/
