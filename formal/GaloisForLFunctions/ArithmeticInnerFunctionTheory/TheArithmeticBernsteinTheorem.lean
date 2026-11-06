import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheTorusWallsOfPrimeInsertion
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.RHTower.MobiusPrimeApertureDifferentialOrder

/-!
# An arithmetic Bernstein theorem: the largest insertion cone

Which amplitudes have nonnegative insertions at every prime set, phase and base point? The exponentially convex ones, and only those.

**Theorem** (`isExpConvex_of_torusPositive`). Let `f` be continuous on `ℝ`, of exponential decay at `+∞`, and
`|f(y)| ≤ C e^{κ|y|}` at `−∞` with `κ < ½`. If `f` has nonnegative torus sums on every finite set of primes at every base point, then every
Hankel form `Σ c_v c_w f(y + v + w)` is nonnegative. With `IsExpConvexFrom.torusSum` this classifies the cone
(`torusPositive_iff_expConvex`): by Bernstein–Widder, its members are the Laplace mixtures.

**Mechanism.** Against the Sato–Tate measures, the Hecke form on the primes of a window is
`f(x) Σ d_p² + Σ_{p,q} d_p d_q f(x + log p + log q)`. Spread a coefficient `c_v` over the primes near `e^{u+v}`, `x = y − 2u`: the double sum tends to the Hankel form
of `f` at `y`, and the diagonal cost is `f(y − 2u) Σ_v c_v²/#primes`, of size `e^{2κu}·u e^{−u}`. It vanishes exactly for
`κ < ½`. The critical exponent is the density of the primes: `Σ_p p^{−2s}` diverges at `s = ½`.

So phase locking at a fixed amplitude cannot enlarge the Laplace cone. The theta amplitude `A` of route TH, which is log-concave, grows
at exactly the critical rate `e^{|x|/2}` on the left.
-/

open Filter Topology Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Primes in multiplicative windows -/

/-- **Primes in `(X, e^ε X]`.** By the prime number theorem there are at least `c X / log X` of them. -/
theorem exists_card_primes_window_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X, X₀ ≤ X →
      c * (X / Real.log X) ≤ ((primesInIoc ⌊X⌋₊ ⌊Real.exp ε * X⌋₊).card : ℝ) := by
  set lam : ℝ := Real.exp ε with hlam
  have hlam1 : 1 < lam := Real.one_lt_exp_iff.mpr hε
  have hR := _root_.RHTower.tendsto_primeCounting_ratio
  have hscale : Tendsto (fun X : ℝ => lam * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have hR2 := hR.comp hscale
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hq : Tendsto (fun X : ℝ => Real.log X / Real.log (lam * X)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun X : ℝ => (Real.log lam / Real.log X + 1)⁻¹) atTop (𝓝 (0 + 1)⁻¹) :=
      ((tendsto_const_nhds.div_atTop hlog).add tendsto_const_nhds).inv₀ (by norm_num)
    have h2 : (0 + 1 : ℝ)⁻¹ = 1 := by norm_num
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with X hX
    have hl : 0 < Real.log X := Real.log_pos hX
    rw [Real.log_mul (by linarith) (by linarith)]
    have hl2 : 0 < Real.log lam := Real.log_pos hlam1
    field_simp
  -- `(π(λX) − π(X)) log X / X → λ − 1`
  have hmain : Tendsto (fun X : ℝ =>
      ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) / ((lam * X) / Real.log (lam * X))) * lam *
        (Real.log X / Real.log (lam * X)) - (Nat.primeCounting ⌊X⌋₊ : ℝ) / (X / Real.log X)) atTop
      (𝓝 (1 * lam * 1 - 1)) :=
    ((hR2.mul_const lam).mul hq).sub hR
  have hgoal : (1 : ℝ) * lam * 1 - 1 = lam - 1 := by ring
  rw [hgoal] at hmain
  have hev := hmain.eventually (lt_mem_nhds (show (lam - 1) / 2 < lam - 1 by linarith))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop 1))
  refine ⟨(lam - 1) / 2, by linarith, max X₁ 2, by
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun X hX => ?_⟩
  obtain ⟨h1, hX1⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hX0 : 0 < X := by linarith
  have hfloor : ⌊X⌋₊ ≤ ⌊lam * X⌋₊ := Nat.floor_le_floor (by nlinarith)
  rw [card_primesInIoc hfloor]
  have hYpos : 0 < lam * X := by positivity
  have hlY : 0 < Real.log (lam * X) := Real.log_pos (by nlinarith)
  have e : ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) / ((lam * X) / Real.log (lam * X))) * lam *
      (Real.log X / Real.log (lam * X)) - (Nat.primeCounting ⌊X⌋₊ : ℝ) / (X / Real.log X) =
      ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊) * (Real.log X / X) := by
    field_simp
  rw [e] at h1
  have hfrac : 0 < X / Real.log X := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1.le hfrac.le
  have e2 : ((Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊) * (Real.log X / X) *
      (X / Real.log X) = (Nat.primeCounting ⌊lam * X⌋₊ : ℝ) - Nat.primeCounting ⌊X⌋₊ := by
    field_simp
  rw [e2] at h2
  exact h2

/-! ### The Hecke form on primes -/

variable {n : ℕ}

theorem ampl_zero (f : ℝ → ℝ) (ℓ : Fin n → ℝ) (x : ℝ) : ampl f ℓ x 0 = f x := by
  simp [ampl]

theorem ampl_unit_add_unit (f : ℝ → ℝ) (ℓ : Fin n → ℝ) (x : ℝ) (i j : Fin n) :
    ampl f ℓ x (unitIdx i + unitIdx j) = f (x + ℓ i + ℓ j) := by
  have e : ∑ k, (((unitIdx i + unitIdx j) k : ℕ) : ℝ) * ℓ k = ℓ i + ℓ j := by
    simp only [unitIdx, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
  rw [ampl, e, add_assoc]

/-- The Hecke form with no constant term: `f(x) Σ d_i² + Σ_{i,j} d_i d_j f(x + ℓ_i + ℓ_j) ≥ 0`. -/
theorem hecke_primes_nonneg {f : ℝ → ℝ} {ℓ : Fin n → ℝ} {x : ℝ}
    (ha : TraceSummable (ampl f ℓ x)) (hpos : ∀ θ, 0 ≤ torusSum (ampl f ℓ x) θ) (d : Fin n → ℝ) :
    0 ≤ f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) := by
  have h := hecke_level_one ha hpos 0 d
  have e : heckeOne (ampl f ℓ x) 0 d =
      f x * ∑ i, d i ^ 2 + ∑ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) := by
    rw [heckeOne]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, zero_add,
      ampl_zero, ampl_unit_add_unit]
    have hsplit : ∀ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) = d i ^ 2 * f (x + ℓ i + ℓ i) +
        ∑ j ∈ Finset.univ.erase i, d i * d j * f (x + ℓ i + ℓ j) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    have hS : ∑ i, ∑ j, d i * d j * f (x + ℓ i + ℓ j) = ∑ i, (d i ^ 2 * f (x + ℓ i + ℓ i) +
        ∑ j ∈ Finset.univ.erase i, d i * d j * f (x + ℓ i + ℓ j)) :=
      Finset.sum_congr rfl fun i _ => hsplit i
    have hL : ∑ i, d i ^ 2 * (f x + f (x + ℓ i + ℓ i)) =
        ∑ i, f x * d i ^ 2 + ∑ i, d i ^ 2 * f (x + ℓ i + ℓ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hS, Finset.sum_add_distrib, Finset.mul_sum, hL]
    ring
  rw [e] at h
  exact h

/-! ### Blocks -/

/-- Averaging over two finite sets. -/
theorem abs_block_sub_le {α : Type*} (P Q : Finset α) (hP : 0 < P.card) (hQ : 0 < Q.card)
    (a b L δ : ℝ) (F : α → α → ℝ) (hF : ∀ q ∈ P, ∀ r ∈ Q, |F q r - L| ≤ δ) :
    |∑ q ∈ P, ∑ r ∈ Q, (a / P.card) * (b / Q.card) * F q r - a * b * L| ≤ |a| * |b| * δ := by
  have hPc : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hQc : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hPp : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hQp : (0 : ℝ) < Q.card := by exact_mod_cast hQ
  have e : a * b * L = ∑ q ∈ P, ∑ r ∈ Q, (a / P.card) * (b / Q.card) * L := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [e, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ q ∈ P, |∑ r ∈ Q, (a / P.card) * (b / Q.card) * F q r -
      ∑ r ∈ Q, (a / P.card) * (b / Q.card) * L| ≤ |a| / P.card * (|b| * δ) := by
    intro q hq
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hr : ∀ r ∈ Q, |(a / P.card) * (b / Q.card) * F q r - (a / P.card) * (b / Q.card) * L| ≤
        |a| / P.card * (|b| / Q.card) * δ := by
      intro r hr
      rw [← mul_sub, abs_mul, abs_mul, abs_div, abs_div, Nat.abs_cast, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hF q hq r hr) (by positivity)
    refine (Finset.sum_le_sum hr).trans (le_of_eq ?_)
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- A finite set of reals has a positive gap. -/
theorem exists_gap (T : Finset ℝ) : ∃ g : ℝ, 0 < g ∧ ∀ v ∈ T, ∀ w ∈ T, v ≠ w → g ≤ |v - w| := by
  classical
  by_cases hS : (T.offDiag.image fun q : ℝ × ℝ => |q.1 - q.2|).Nonempty
  · set S := T.offDiag.image fun q : ℝ × ℝ => |q.1 - q.2| with hSdef
    refine ⟨S.min' hS, ?_, fun v hv w hw hvw => ?_⟩
    · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp (S.min'_mem hS)
      rw [← hqe]
      have := (Finset.mem_offDiag.mp hq).2.2
      exact abs_pos.mpr (sub_ne_zero.mpr this)
    · exact S.min'_le _ (Finset.mem_image.mpr ⟨(v, w), Finset.mem_offDiag.mpr ⟨hv, hw, hvw⟩, rfl⟩)
  · refine ⟨1, one_pos, fun v hv w hw hvw => ?_⟩
    exact absurd ⟨_, Finset.mem_image.mpr ⟨(v, w), Finset.mem_offDiag.mpr ⟨hv, hw, hvw⟩, rfl⟩⟩ hS

/-- `(u + V) e^{−βu} → 0`. -/
theorem tendsto_add_mul_exp_neg {β : ℝ} (hβ : 0 < β) (V : ℝ) :
    Tendsto (fun u : ℝ => (u + V) * Real.exp (-β * u)) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hβ)
  have h2 : Tendsto (fun u : ℝ => Real.exp (-β * u)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
    refine this.congr fun u => ?_
    simp only [Function.comp, id]
    congr 1
    ring
  have h3 := (h1.const_mul β⁻¹).add (h2.const_mul V)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun u => ?_
  simp only [Function.comp, id, pow_one]
  have e : Real.exp (-(β * u)) = Real.exp (-β * u) := by
    congr 1
    ring
  rw [e]
  field_simp

/-! ### The theorem -/

/-- **The Hankel forms of a torus-positive amplitude are nonnegative.** -/
theorem hankel_nonneg_of_torusPositive {f : ℝ → ℝ} (hc : Continuous f) {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) {κ C : ℝ} (hκ : κ < 1 / 2)
    (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y))
    (hpos : ∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
      ∀ (x : ℝ) (θ : Fin n → ℝ), 0 ≤ torusSum (ampl f (fun i => Real.log (p i)) x) θ)
    (y : ℝ) (T : Finset ℝ) (c : ℝ → ℝ) :
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
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hL 0 le_rfl)
    simpa using h
  set V : ℝ := ∑ v ∈ T, |v| + 1 with hV
  have hV1 : 1 ≤ V := by
    have : 0 ≤ ∑ v ∈ T, |v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hV]
    linarith
  have hVv : ∀ v ∈ T, |v| + 1 ≤ V := fun v hv => by
    have := Finset.single_le_sum (f := fun v => |v|) (fun _ _ => abs_nonneg _) hv
    rw [hV]
    linarith
  -- uniform continuity on the compact range of the arguments
  have huc := (isCompact_Icc (a := y - 2 * V) (b := y + 2 * V)).uniformContinuousOn_of_continuous
    hc.continuousOn
  obtain ⟨ε₀, hε₀, huc⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ0
  obtain ⟨g, hg, hgap⟩ := exists_gap T
  set ε := min (ε₀ / 4) (min (g / 2) (1 / 2)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hε1 : ε ≤ ε₀ / 4 := min_le_left _ _
  have hε2 : ε ≤ g / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c₁, hc₁, X₀, hX₀, hwin⟩ := exists_card_primes_window_ge hε0
  -- the diagonal cost vanishes
  set β : ℝ := 1 - 2 * κ with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set Ssq : ℝ := ∑ v ∈ T, c v ^ 2 with hSsq
  have hSsq0 : 0 ≤ Ssq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K₁ : ℝ := C * Real.exp (-κ * y) * (Ssq * Real.exp V / c₁) with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hcost : ∀ᶠ u : ℝ in atTop, K₁ * ((u + V) * Real.exp (-β * u)) < η / 4 := by
    have := (tendsto_add_mul_exp_neg hβ0 V).const_mul K₁
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := (hcost.and ((eventually_ge_atTop (Real.log X₀ + V)).and
    ((eventually_ge_atTop (y / 2)).and (eventually_ge_atTop V)))).exists
  have hx : y - 2 * u ≤ 0 := by linarith
  -- the prime windows
  set X : ℝ → ℝ := fun v => Real.exp (u + v) with hXd
  have hXpos : ∀ v, 0 < X v := fun v => Real.exp_pos _
  have hX0 : ∀ v ∈ T, X₀ ≤ X v := fun v hv => by
    have hv' := abs_le.mp ((le_add_of_nonneg_right zero_le_one).trans (hVv v hv))
    have hX₀pos : 0 < X₀ := by linarith
    rw [hXd, ← Real.exp_log hX₀pos]
    exact Real.exp_le_exp.mpr (by linarith [hv'.1])
  set P : ℝ → Finset ℕ := fun v => primesInIoc ⌊X v⌋₊ ⌊Real.exp ε * X v⌋₊ with hP
  have hmemP : ∀ v q, q ∈ P v → q.Prime ∧ u + v < Real.log q ∧ Real.log q ≤ u + v + ε := by
    intro v q hq
    have hq' := Finset.mem_filter.mp hq
    have hI := Finset.mem_Ioc.mp hq'.1
    have h1 : X v < q := Nat.lt_of_floor_lt hI.1
    have h2 : (q : ℝ) ≤ Real.exp ε * X v :=
      (Nat.cast_le.mpr hI.2).trans (Nat.floor_le (by have := hXpos v; positivity))
    have hq0 : (0 : ℝ) < q := lt_trans (hXpos v) h1
    refine ⟨hq'.2, ?_, ?_⟩
    · rw [Real.lt_log_iff_exp_lt hq0]
      exact h1
    · rw [Real.log_le_iff_le_exp hq0]
      refine h2.trans (le_of_eq ?_)
      rw [hXd, ← Real.exp_add]
      congr 1
      ring
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
    have hv' := abs_le.mp ((le_add_of_nonneg_right zero_le_one).trans (hVv v hv))
    have hv1 : 1 ≤ V - |v| := by linarith [hVv v hv]
    have := neg_abs_le v
    linarith
  have hcard : ∀ v ∈ T, c₁ * (X v / (u + v)) ≤ ((P v).card : ℝ) := fun v hv => by
    have h := hwin (X v) (hX0 v hv)
    have e : Real.log (X v) = u + v := by rw [hXd]; exact Real.log_exp _
    rwa [e] at h
  have hcardpos : ∀ v ∈ T, 0 < (P v).card := fun v hv => by
    have h := hcard v hv
    have h0 : 0 < c₁ * (X v / (u + v)) := mul_pos hc₁ (div_pos (hXpos v) (hlogX v hv))
    exact_mod_cast lt_of_lt_of_le h0 h
  -- the coefficients on the primes
  set dd : ℕ → ℝ := fun q => ∑ v ∈ T, if q ∈ P v then c v / (P v).card else 0 with hdd
  have hddP : ∀ v ∈ T, ∀ q ∈ P v, dd q = c v / (P v).card := by
    intro v hv q hq
    rw [hdd]
    simp only
    rw [Finset.sum_eq_single v]
    · simp [hq]
    · intro w hw hwv
      have := Finset.disjoint_left.mp (hdisj w hw v hv hwv)
      rw [if_neg]
      exact fun h => this h hq
    · exact fun h => absurd hv h
  set Z : Finset ℕ := T.biUnion P with hZ
  have hPd : (T : Set ℝ).PairwiseDisjoint P := fun v hv w hw hvw => hdisj v hv w hw hvw
  have hZprime : ∀ q ∈ Z, q.Prime := fun q hq => by
    obtain ⟨v, -, hqv⟩ := Finset.mem_biUnion.mp hq
    exact (hmemP v q hqv).1
  let e : Fin Z.card ≃ Z := Z.equivFin.symm
  let p : Fin Z.card → ℕ := fun i => (e i : ℕ)
  have hpp : ∀ i, (p i).Prime := fun i => hZprime _ (e i).2
  have hpinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hsumZ : ∀ G : ℕ → ℝ, ∑ i, G (p i) = ∑ v ∈ T, ∑ q ∈ P v, G q := by
    intro G
    have h1 : ∑ i, G (p i) = ∑ z : Z, G z := Equiv.sum_comp e fun z : Z => G z
    rw [h1, Finset.sum_coe_sort Z G, hZ, Finset.sum_biUnion hPd]
  set x : ℝ := y - 2 * u with hxd
  obtain ⟨C₂, -, hC₂⟩ := hd x
  have hℓ : ∀ i, 0 < Real.log (p i) := fun i =>
    Real.log_pos (by exact_mod_cast (hpp i).one_lt)
  have hH := hecke_primes_nonneg (f := f) (ℓ := fun i => Real.log (p i)) (x := x)
    (traceSummable_ampl hκ₀ hC₂ hℓ le_rfl) (hpos _ p hpp hpinj x) (fun i => dd (p i))
  -- the diagonal
  have hdiag : f x * ∑ i, dd (p i) ^ 2 ≤ K₁ * ((u + V) * Real.exp (-β * u)) := by
    rw [hsumZ fun q => dd q ^ 2]
    have hsq : ∀ v ∈ T, ∑ q ∈ P v, dd q ^ 2 = c v ^ 2 / (P v).card := by
      intro v hv
      have hc0 : ((P v).card : ℝ) ≠ 0 := by exact_mod_cast (hcardpos v hv).ne'
      rw [Finset.sum_congr rfl fun q hq => by rw [hddP v hv q hq]]
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hsq]
    have hinv : ∀ v ∈ T, c v ^ 2 / (P v).card ≤
        c v ^ 2 * ((u + V) * Real.exp V * Real.exp (-u) / c₁) := by
      intro v hv
      have hn := hcard v hv
      have hn0 : (0 : ℝ) < (P v).card := by exact_mod_cast hcardpos v hv
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hlow : c₁ * (X v / (u + v)) ≤ (P v).card := hn
      have hposw : 0 < c₁ * (X v / (u + v)) := mul_pos hc₁ (div_pos (hXpos v) (hlogX v hv))
      refine (inv_anti₀ hposw hlow).trans ?_
      have hv1 := hVv v hv
      have hv2 := neg_abs_le v
      have hv3 := le_abs_self v
      have hup : u + v ≤ u + V := by linarith
      have hexp : Real.exp (-(u + v)) ≤ Real.exp V * Real.exp (-u) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have e1 : (c₁ * (X v / (u + v)))⁻¹ = (u + v) * Real.exp (-(u + v)) / c₁ := by
        simp only [hXd, Real.exp_neg]
        have := hlogX v hv
        field_simp
      rw [e1]
      refine div_le_div_of_nonneg_right ?_ hc₁.le
      calc (u + v) * Real.exp (-(u + v)) ≤ (u + V) * (Real.exp V * Real.exp (-u)) :=
            mul_le_mul hup hexp (Real.exp_pos _).le (by linarith [hlogX v hv])
        _ = _ := by ring
    have hsumle : ∑ v ∈ T, c v ^ 2 / (P v).card ≤ Ssq * ((u + V) * Real.exp V * Real.exp (-u) / c₁) := by
      rw [hSsq, Finset.sum_mul]
      exact Finset.sum_le_sum hinv
    have hsumnn : 0 ≤ ∑ v ∈ T, c v ^ 2 / (P v).card :=
      Finset.sum_nonneg fun v _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    have hfx : f x ≤ C * Real.exp (-κ * x) := (le_abs_self _).trans (hL x hx)
    have hexpx : Real.exp (-κ * x) = Real.exp (-κ * y) * Real.exp (2 * κ * u) := by
      rw [← Real.exp_add, hxd]
      congr 1
      ring
    have hu0 : 0 ≤ u + V := by linarith
    calc f x * ∑ v ∈ T, c v ^ 2 / (P v).card
        ≤ (C * Real.exp (-κ * x)) * ∑ v ∈ T, c v ^ 2 / (P v).card :=
          mul_le_mul_of_nonneg_right hfx hsumnn
      _ ≤ (C * Real.exp (-κ * x)) * (Ssq * ((u + V) * Real.exp V * Real.exp (-u) / c₁)) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ = K₁ * ((u + V) * Real.exp (-β * u)) := by
          rw [hexpx, hK₁]
          have e3 : Real.exp (-β * u) = Real.exp (2 * κ * u) * Real.exp (-u) := by
            rw [← Real.exp_add, hβ]
            congr 1
            ring
          rw [e3]
          field_simp
  -- the double sum
  have hdouble : ∑ i, ∑ j, dd (p i) * dd (p j) * f (x + Real.log (p i) + Real.log (p j)) ≤
      A + δ * M := by
    have h1 : ∑ i, ∑ j, dd (p i) * dd (p j) * f (x + Real.log (p i) + Real.log (p j)) =
        ∑ v ∈ T, ∑ w ∈ T, ∑ q ∈ P v, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r) := by
      have hin : ∀ q : ℕ, ∑ j, dd q * dd (p j) * f (x + Real.log q + Real.log (p j)) =
          ∑ w ∈ T, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r) := fun q =>
        hsumZ fun r => dd q * dd r * f (x + Real.log q + Real.log r)
      simp_rw [hin]
      rw [hsumZ fun q => ∑ w ∈ T, ∑ r ∈ P w, dd q * dd r * f (x + Real.log q + Real.log r)]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm]
    rw [h1, hA]
    have hblock : ∀ v ∈ T, ∀ w ∈ T, ∑ q ∈ P v, ∑ r ∈ P w,
        dd q * dd r * f (x + Real.log q + Real.log r) ≤
        c v * c w * f (y + v + w) + |c v| * |c w| * δ := by
      intro v hv w hw
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
          have hv1 := hVv v hv
          have hw1 := hVv w hw
          have hv2 := le_abs_self v
          have hv3 := neg_abs_le v
          have hw2 := le_abs_self w
          have hw3 := neg_abs_le w
          have hA1 : x + Real.log q + Real.log r ∈ Icc (y - 2 * V) (y + 2 * V) := by
            constructor <;> rw [hxd] <;> linarith
          have hA2 : y + v + w ∈ Icc (y - 2 * V) (y + 2 * V) := by
            constructor <;> linarith
          have hdist : dist (x + Real.log q + Real.log r) (y + v + w) < ε₀ := by
            rw [Real.dist_eq, abs_lt, hxd]
            constructor <;> linarith
          have := huc _ hA1 _ hA2 hdist
          rw [Real.dist_eq] at this
          exact this.le
      have := (abs_le.mp hb).2
      linarith
    have hsum := Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun w hw => hblock v hv w hw
    refine hsum.trans ?_
    simp only [Finset.sum_add_distrib]
    have e4 : ∑ v ∈ T, ∑ w ∈ T, |c v| * |c w| * δ = δ * M := by
      rw [hM, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [e4]
  have hδM : δ * M ≤ η / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hAη : A = -η := by rw [hη]; ring
  linarith

/-- **The arithmetic Bernstein theorem.** Under the growth hypotheses, torus positivity on every
finite set of primes and at every base point is exponential convexity. -/
theorem torusPositive_iff_hankel_nonneg {f : ℝ → ℝ} (hc : Continuous f) {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hd : ∀ x, ExpDecayFrom x κ₀ f) {κ C : ℝ} (hκ : κ < 1 / 2)
    (hL : ∀ y, y ≤ 0 → |f y| ≤ C * Real.exp (-κ * y)) :
    (∀ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) → Function.Injective p →
      ∀ (x : ℝ) (θ : Fin n → ℝ), 0 ≤ torusSum (ampl f (fun i => Real.log (p i)) x) θ) ↔
      ∀ x₀, IsExpConvexFrom x₀ f := by
  constructor
  · intro hpos x₀ ι S t c' _
    classical
    -- the real and imaginary parts of the coefficients, grouped by the value of `t`
    have hreal : ∀ d : ι → ℝ, 0 ≤ ∑ i ∈ S, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) := by
      intro d
      set T := S.image t with hT
      set cc : ℝ → ℝ := fun v => ∑ i ∈ S with t i = v, d i with hcc
      have hH := hankel_nonneg_of_torusPositive hc hκ₀ hd hκ hL hpos x₀ T cc
      have hfib : ∀ G : ℝ → ℝ, ∑ i ∈ S, d i * G (t i) = ∑ v ∈ T, cc v * G v := by
        intro G
        rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := t)
          (fun i hi => Finset.mem_image_of_mem t hi)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hcc, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
      have e : ∑ i ∈ S, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) =
          ∑ v ∈ T, ∑ w ∈ T, cc v * cc w * f (x₀ + v + w) := by
        have h1 : ∀ i, ∑ j ∈ S, d i * d j * f (x₀ + t i + t j) =
            d i * ∑ w ∈ T, cc w * f (x₀ + t i + w) := by
          intro i
          rw [← hfib fun w => f (x₀ + t i + w), Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        simp_rw [h1]
        rw [hfib fun v => ∑ w ∈ T, cc w * f (x₀ + v + w)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [e]
      exact hH
    have hsym : ∀ i j, f (x₀ + t i + t j) = f (x₀ + t j + t i) := fun i j => by
      congr 1
      ring
    have hsplit : (∑ i ∈ S, ∑ j ∈ S, c' i * (starRingEnd ℂ) (c' j) * (f (x₀ + t i + t j) : ℂ)).re =
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
  · intro hE n p hp hinj x θ
    obtain ⟨C₂, -, hC₂⟩ := id (hd x)
    have hℓ : ∀ i, 0 < Real.log (p i) := fun i =>
      Real.log_pos (by exact_mod_cast (hp i).one_lt)
    exact (IsExpConvexFrom.torusSum hκ₀ (hE x) (hd x) hℓ θ).1.nonneg le_rfl

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
