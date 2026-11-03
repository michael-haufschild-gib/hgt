import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedDirectionsCarryNoNegativeSquares

/-!
# The conductor decomposition holds on a growing range

Along the critical curve `c⁸/log N → K` the tilted-spline form on the window of conductor `m`
(`conductorWindow`: the untwisted window `h` at `m = 1`, the Ramanujan window `c_m g` at `m ≥ 2`) has
second order

* `κ Q(H) + (7J(1)/K)‖H‖²_{−8}` on conductor one (Weil's form plus the conductor-one count),
* `(7φ(m)J(m)/K)‖G‖²_{−8}` on conductor `m ≥ 2` (the conductor-`m` count),

and the pairing of two different conductors tends to `0` (`tendsto_layerPair_conductorWindow`):
the second-order form is the orthogonal sum `conductorLimit`.

**Uniformity on a growing range** (`exists_uniform_conductor_range`): there is `M(N) → ∞` such that,
uniformly in the coefficients `b`,
`|q_N(Σ_{m ≤ M(N)} b_m x_m) − Σ_{m ≤ M(N)} b_m² λ_m| ≤ ε Σ_{m ≤ M(N)} b_m²` eventually, for every
`ε > 0` — mixed terms between conductors vanish uniformly on the whole range. The mechanism: the form
is the quadratic form of a bilinear pairing (`layerForm_sum`), every Gram entry converges, the
entrywise error `D_k(N) = Σ_{m,m' ≤ k}|B_N(m,m') − λ_m δ_{mm'}|` tends to `0` for each `k`, and a
diagonal choice `M(N)` (`exists_tendsto_diagonal`) keeps `D_{M(N)}(N) → 0`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-! ### A diagonal choice of range -/

/-- If `f k N → 0` for every `k`, then `f (M N) N → 0` for some `M(N) → ∞`. -/
theorem exists_tendsto_diagonal {f : ℕ → ℕ → ℝ} (hlim : ∀ k, Tendsto (f k) atTop (𝓝 0)) :
    ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧ Tendsto (fun N => f (M N) N) atTop (𝓝 0) := by
  have hev : ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, |f k N| < 1 / ((k : ℝ) + 1) := fun k => by
    have h := (hlim k).eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
    exact ⟨N₀, fun N hN => by simpa [Real.dist_eq] using hN₀ N hN⟩
  choose T hT using hev
  -- a strictly larger threshold `T' k ≥ k`
  set T' : ℕ → ℕ := fun k => (∑ j ∈ range (k + 1), T j) + k with hT'
  have hTle : ∀ k, T k ≤ T' k := fun k =>
    (single_le_sum (fun j _ => Nat.zero_le (T j)) (self_mem_range_succ k)).trans (Nat.le_add_right _ _)
  have hkle : ∀ k, k ≤ T' k := fun k => Nat.le_add_left _ _
  set M : ℕ → ℕ := fun N => Nat.findGreatest (fun k => T' k ≤ N) N with hM
  have hMge : ∀ k N, T' k ≤ N → k ≤ M N := fun k N h =>
    Nat.le_findGreatest (P := fun k => T' k ≤ N) ((hkle k).trans h) h
  have hMtop : Tendsto M atTop atTop :=
    tendsto_atTop.mpr fun k => eventually_atTop.mpr ⟨T' k, fun N hN => hMge k N hN⟩
  refine ⟨M, hMtop, ?_⟩
  have hinv : Tendsto (fun N => 1 / ((M N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hMtop))
  refine squeeze_zero_norm' ?_ hinv
  filter_upwards [eventually_ge_atTop (T' 0)] with N hN
  have hP : T' (M N) ≤ N := Nat.findGreatest_spec (P := fun k => T' k ≤ N) ((hkle 0).trans hN) hN
  exact (hT (M N) N ((hTle (M N)).trans hP)).le

/-! ### The windows and their pairing -/

variable {h g : ℝ → ℝ} {A : ℝ}

/-- The window of conductor `m`: untwisted `h` at `m = 1`, Ramanujan-twisted `c_m g` at `m ≥ 2`. -/
def conductorWindow (h g : ℝ → ℝ) (m N : ℕ) : ℕ → ℝ :=
  if m = 1 then horizonWeights h N else twistedWeights g (ramTwist m) N

/-- The tilted-spline atom at overlap `c`. -/
abbrev splineAtom (c : ℝ) (N : ℕ) : ℝ → ℝ := atomDilate tiltedUnitSpline (c / N)

/-- The normalized Weil pairing `c⁻¹ W(T_x, T_y)/∫φ_N²` of two weight vectors. -/
def layerPair (c : ℝ) (N : ℕ) (x y : ℕ → ℝ) : ℝ :=
  c⁻¹ * (weilPair (atomicTest N x (splineAtom c N)) (atomicTest N y (splineAtom c N)) /
    ∫ u, splineAtom c N u ^ 2)

/-- The normalized form `q_N(x) = c⁻¹ Q(T_x)/∫φ_N²`. -/
def layerForm (c : ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  c⁻¹ * (weilQuad (atomicTest N x (splineAtom c N)) / ∫ u, splineAtom c N u ^ 2)

theorem layerForm_eq_layerPair (c : ℝ) (N : ℕ) (x : ℕ → ℝ) : layerForm c N x = layerPair c N x x :=
  rfl

theorem atomicTest_mem_realTests {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    atomicTest N x (splineAtom c N) ∈ realTests :=
  ⟨contDiff_atomicTest_dilate contDiff_tiltedUnitSpline N x c,
    hasCompactSupport_atomicTest_dilate tiltedUnitSpline_support N x hc hN⟩

theorem atomicTest_smul_weights (N : ℕ) (b : ℝ) (x : ℕ → ℝ) (f : ℝ → ℝ) :
    atomicTest N (fun n => b * x n) f = b • atomicTest N x f := by
  funext u
  simp only [atomicTest, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem atomicTest_sum_weights (N : ℕ) (S : Finset ℕ) (x : ℕ → ℕ → ℝ) (f : ℝ → ℝ) :
    atomicTest N (fun n => ∑ m ∈ S, x m n) f = ∑ m ∈ S, atomicTest N (x m) f := by
  funext u
  simp only [atomicTest, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem weilPair_smul_right' (b : ℝ) (f g : ℝ → ℝ) : weilPair f (b • g) = b * weilPair f g := by
  rw [weilPair_comm, weilPair_smul_left, weilPair_comm]

/-- `W(Σ_i u_i, v) = Σ_i W(u_i, v)` on tests. -/
theorem weilPair_finset_sum_left (S : Finset ℕ) {u : ℕ → ℝ → ℝ} (hu : ∀ i, u i ∈ realTests)
    {v : ℝ → ℝ} (hv : v ∈ realTests) : weilPair (∑ i ∈ S, u i) v = ∑ i ∈ S, weilPair (u i) v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := weilPair_smul_left 0 (0 : ℝ → ℝ) v
    rwa [zero_smul, zero_mul] at this
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      weilPair_add_left (hu i) (realTests.sum_mem fun j _ => hu j) hv, ih]

/-- **The form is the quadratic form of the pairing on finite combinations.** -/
theorem layerForm_sum {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (S : Finset ℕ) (b : ℕ → ℝ)
    (x : ℕ → ℕ → ℝ) :
    layerForm c N (fun n => ∑ m ∈ S, b m * x m n) =
      ∑ m ∈ S, ∑ m' ∈ S, b m * b m' * layerPair c N (x m) (x m') := by
  set T : ℕ → ℝ → ℝ := fun m => atomicTest N (x m) (splineAtom c N) with hT
  have hTm : ∀ m, T m ∈ realTests := fun m => atomicTest_mem_realTests hc hN (x m)
  have hbT : ∀ m, b m • T m ∈ realTests := fun m => realTests.smul_mem (b m) (hTm m)
  have hsum : atomicTest N (fun n => ∑ m ∈ S, b m * x m n) (splineAtom c N) = ∑ m ∈ S, b m • T m := by
    rw [atomicTest_sum_weights N S (fun m n => b m * x m n)]
    exact Finset.sum_congr rfl fun m _ => atomicTest_smul_weights N (b m) (x m) _
  have hmem : ∑ m ∈ S, b m • T m ∈ realTests := realTests.sum_mem fun m _ => hbT m
  rw [layerForm_eq_layerPair, layerPair, hsum, weilPair_finset_sum_left S hbT hmem]
  simp only [layerPair, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [weilPair_comm, weilPair_finset_sum_left S hbT (hbT m)]
  simp only [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [weilPair_smul_left, weilPair_smul_right', weilPair_comm]
  ring

theorem layerPair_comm (c : ℝ) (N : ℕ) (x y : ℕ → ℝ) : layerPair c N x y = layerPair c N y x := by
  rw [layerPair, layerPair, weilPair_comm]

/-- Polarization: `B(x, y) = (q(x + y) − q(x) − q(y))/2`. -/
theorem layerPair_eq_polar {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x y : ℕ → ℝ) :
    layerPair c N x y = (layerForm c N (fun n => x n + y n) - layerForm c N x - layerForm c N y) / 2 := by
  have hx := atomicTest_mem_realTests hc hN x
  have hy := atomicTest_mem_realTests hc hN y
  have hadd : atomicTest N (fun n => x n + y n) (splineAtom c N) =
      atomicTest N x (splineAtom c N) + atomicTest N y (splineAtom c N) := by
    rw [← atomicTest_weights_add]; rfl
  have hxy := realTests.add_mem hx hy
  simp only [layerForm_eq_layerPair, layerPair, hadd]
  rw [weilPair_add_left hx hy hxy, weilPair_comm _ (atomicTest N x _ + _),
    weilPair_add_left hx hy hx, weilPair_comm _ (atomicTest N x _ + _), weilPair_add_left hx hy hy,
    weilPair_comm (atomicTest N y _) (atomicTest N x _)]
  ring

/-! ### The limit pairing -/

/-- The conductor-one value `κ Q(H) + (7J(1)/K)‖H‖²_{−8}`. -/
def untwistedLimit (h : ℝ → ℝ) (K : ℝ) : ℝ :=
  (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
    7 * tiltedJordanOne / K * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2

/-- The conductor-`m` count `(7φ(m)J(m)/K)‖G‖²_{−8}`. -/
def twistedCount (g : ℝ → ℝ) (K : ℝ) (m : ℕ) : ℝ :=
  7 * ((m.totient : ℝ) * ArithmeticDegenerationTheory.jordanCoefficient m) / K *
    ∫ y, Real.exp (-(8 * y)) * halfWeight g y ^ 2

/-- The limit of the second-order form: diagonal in the conductor. -/
def conductorLimit (h g : ℝ → ℝ) (K : ℝ) (m : ℕ) : ℝ :=
  if m = 1 then untwistedLimit h K else twistedCount g K m

theorem weilQuad_halfWeight_zero : weilQuad (halfWeight (fun _ => (0 : ℝ))) = 0 := by
  have hz : halfWeight (fun _ => (0 : ℝ)) = (0 : ℝ) • halfWeight (fun _ => (0 : ℝ)) := by
    funext y; simp [halfWeight]
  show weilPair _ _ = 0
  rw [hz, weilPair_smul_left, zero_mul]

theorem ramComb_single (m : ℕ) (n : ℕ) : ramComb {m} (fun _ => 1) n = ramTwist m n := by
  simp [ramComb]

variable (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A)
  (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hgsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
  {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
  (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
include hh hg hA hsupp hgsupp hc1 hK hcrit

omit hh hsupp in
/-- The graded limit of a Ramanujan window with window `k`, in the notation of this module. -/
theorem tendsto_layerForm_graded {k : ℝ → ℝ} (hk : ContDiff ℝ 2 k)
    (hksupp : ∀ y, y ∉ Set.Icc (-A) 0 → k y = 0) {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) :
    Tendsto (fun N => layerForm (c N) N (fun n => horizonWeights k N n +
        twistedWeights g (ramComb S fun _ => 1) N n)) atTop
      (𝓝 (untwistedLimit k K + ∑ m ∈ S, twistedCount g K m)) := by
  have hlim := graded_ramComb_criticalCurve_exact hk hg hA hksupp hgsupp hc1 hK hcrit hS (fun _ => 1)
  have e : untwistedLimit k K + ∑ m ∈ S, twistedCount g K m =
      (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight k) +
        7 * tiltedJordanOne / K * (∫ y, Real.exp (-(8 * y)) * halfWeight k y ^ 2) +
        7 * (∑ m ∈ S, (fun _ => (1 : ℝ)) m ^ 2 * ((m.totient : ℝ) *
          ArithmeticDegenerationTheory.jordanCoefficient m)) / K *
            ∫ y, Real.exp (-(8 * y)) * halfWeight g y ^ 2 := by
    simp only [untwistedLimit, twistedCount, one_pow, one_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [e]
  exact hlim

/-- The zero window. -/
theorem tendsto_layerForm_twisted {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) :
    Tendsto (fun N => layerForm (c N) N (twistedWeights g (ramComb S fun _ => 1) N)) atTop
      (𝓝 (∑ m ∈ S, twistedCount g K m)) := by
  have hlim := tendsto_layerForm_graded hg hA hgsupp hc1 hK hcrit
    (k := fun _ => 0) contDiff_const (fun _ _ => rfl) hS
  have hu : untwistedLimit (fun _ => (0 : ℝ)) K = 0 := by
    rw [untwistedLimit, weilQuad_halfWeight_zero]
    simp [halfWeight]
  rw [hu, zero_add] at hlim
  refine hlim.congr fun N => ?_
  congr 1
  funext n
  simp [horizonWeights]

omit hh hg hA hsupp hgsupp hK hcrit in
/-- Polarization of three graded limits. -/
theorem tendsto_layerPair_of_forms {x y : ℕ → ℕ → ℝ} {Lx Ly Lxy : ℝ}
    (h1 : Tendsto (fun N => layerForm (c N) N (x N)) atTop (𝓝 Lx))
    (h2 : Tendsto (fun N => layerForm (c N) N (y N)) atTop (𝓝 Ly))
    (h3 : Tendsto (fun N => layerForm (c N) N (fun n => x N n + y N n)) atTop (𝓝 Lxy)) :
    Tendsto (fun N => layerPair (c N) N (x N) (y N)) atTop (𝓝 ((Lxy - Lx - Ly) / 2)) := by
  refine ((h3.sub h1).sub h2).div_const 2 |>.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (layerPair_eq_polar (by linarith [hc1 N]) hN (x N) (y N)).symm

omit hg hgsupp in
/-- The untwisted window: Weil's form plus the conductor-one count. -/
theorem tendsto_layerForm_untwisted :
    Tendsto (fun N => layerForm (c N) N (horizonWeights h N)) atTop (𝓝 (untwistedLimit h K)) :=
  horizon_layer_criticalCurve_exact hh hA hsupp hc1 hK hcrit

theorem tendsto_layerForm_conductor {j : ℕ} (hj : 1 < j) :
    Tendsto (fun N => layerForm (c N) N (twistedWeights g (ramTwist j) N)) atTop
      (𝓝 (twistedCount g K j)) := by
  have := tendsto_layerForm_twisted hh hg hA hsupp hgsupp hc1 hK hcrit (S := {j}) (by simpa using hj)
  rw [Finset.sum_singleton] at this
  refine this.congr fun N => ?_
  congr 1
  funext n
  simp only [twistedWeights, ramComb_single]

/-- Untwisted against conductor `j ≥ 2`: the mixed pairing vanishes. -/
theorem tendsto_layerPair_untwisted_conductor {j : ℕ} (hj : 1 < j) :
    Tendsto (fun N => layerPair (c N) N (horizonWeights h N) (twistedWeights g (ramTwist j) N))
      atTop (𝓝 0) := by
  have h3 := tendsto_layerForm_graded hg hA hgsupp hc1 hK hcrit hh hsupp (S := {j})
    (by simpa using hj)
  rw [Finset.sum_singleton] at h3
  have h3' : Tendsto (fun N => layerForm (c N) N (fun n => horizonWeights h N n +
      twistedWeights g (ramTwist j) N n)) atTop (𝓝 (untwistedLimit h K + twistedCount g K j)) := by
    refine h3.congr fun N => ?_
    congr 1
    funext n
    simp only [twistedWeights, ramComb_single]
  have := tendsto_layerPair_of_forms hc1 (tendsto_layerForm_untwisted hh hA hsupp hc1 hK hcrit)
    (tendsto_layerForm_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hj) h3'
  rwa [show (untwistedLimit h K + twistedCount g K j - untwistedLimit h K - twistedCount g K j) / 2
    = 0 by ring] at this

/-- Two different conductors `j, j' ≥ 2`: the mixed pairing vanishes. -/
theorem tendsto_layerPair_conductor_conductor {j j' : ℕ} (hj : 1 < j) (hj' : 1 < j')
    (hne : j ≠ j') :
    Tendsto (fun N => layerPair (c N) N (twistedWeights g (ramTwist j) N)
      (twistedWeights g (ramTwist j') N)) atTop (𝓝 0) := by
  have hS : ∀ m ∈ ({j, j'} : Finset ℕ), 1 < m := by
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hj
    · rw [Finset.mem_singleton.mp hm]; exact hj'
  have h3 := tendsto_layerForm_twisted hh hg hA hsupp hgsupp hc1 hK hcrit hS
  rw [Finset.sum_pair hne] at h3
  have h3' : Tendsto (fun N => layerForm (c N) N (fun n => twistedWeights g (ramTwist j) N n +
      twistedWeights g (ramTwist j') N n)) atTop (𝓝 (twistedCount g K j + twistedCount g K j')) := by
    refine h3.congr fun N => ?_
    congr 1
    funext n
    simp only [twistedWeights, ramComb, Finset.sum_pair hne, one_mul, mul_add]
  have := tendsto_layerPair_of_forms hc1
    (tendsto_layerForm_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hj)
    (tendsto_layerForm_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hj') h3'
  rwa [show (twistedCount g K j + twistedCount g K j' - twistedCount g K j - twistedCount g K j') / 2
    = 0 by ring] at this

/-- **The Gram entries converge to the orthogonal sum**: for conductors `m, m' ≥ 1`,
`B_N(x_m, x_{m'}) → δ_{mm'} λ_m`. -/
theorem tendsto_layerPair_conductorWindow {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    Tendsto (fun N => layerPair (c N) N (conductorWindow h g m N) (conductorWindow h g m' N)) atTop
      (𝓝 (if m = m' then conductorLimit h g K m else 0)) := by
  rcases hm.eq_or_lt with rfl | hm1 <;> rcases hm'.eq_or_lt with rfl | hm1'
  · simp only [conductorWindow, conductorLimit, if_true]
    exact tendsto_layerForm_untwisted hh hA hsupp hc1 hK hcrit
  · simp only [conductorWindow, if_true, if_neg hm1'.ne', if_neg hm1'.ne]
    exact tendsto_layerPair_untwisted_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hm1'
  · simp only [conductorWindow, if_true, if_neg hm1.ne']
    refine (tendsto_layerPair_untwisted_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hm1).congr
      fun N => layerPair_comm _ _ _ _
  · simp only [conductorWindow, if_neg hm1.ne', if_neg hm1'.ne']
    by_cases he : m = m'
    · subst he
      simp only [if_true, conductorLimit, if_neg hm1.ne']
      exact tendsto_layerForm_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hm1
    · rw [if_neg he]
      exact tendsto_layerPair_conductor_conductor hh hg hA hsupp hgsupp hc1 hK hcrit hm1 hm1' he

/-- **The conductor decomposition is uniform on a growing range.** There is `M(N) → ∞` such that for
every `ε > 0`, eventually, for all coefficients `b`,
`|q_N(Σ_{m ≤ M(N)} b_m x_m) − Σ_{m ≤ M(N)} b_m² λ_m| ≤ ε Σ_{m ≤ M(N)} b_m²`, where `x_1` is the
untwisted window (`λ_1 = κ Q(H) + (7J(1)/K)‖H‖²_{−8}`) and `x_m`, `m ≥ 2`, the Ramanujan windows
(`λ_m = (7φ(m)J(m)/K)‖G‖²_{−8}`): Weil's form on the untwisted window, the counts on the twisted ones,
and no mixed terms, uniformly over all conductors `≤ M(N)`. -/
theorem exists_uniform_conductor_range :
    ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧ ∀ ε > 0, ∀ᶠ N in atTop, ∀ b : ℕ → ℝ,
      |layerForm (c N) N (fun n => ∑ m ∈ Icc 1 (M N), b m * conductorWindow h g m N n) -
          ∑ m ∈ Icc 1 (M N), b m ^ 2 * conductorLimit h g K m| ≤
        ε * ∑ m ∈ Icc 1 (M N), b m ^ 2 := by
  set Δ : ℕ → ℕ → ℕ → ℝ := fun N m m' => layerPair (c N) N (conductorWindow h g m N)
    (conductorWindow h g m' N) - if m = m' then conductorLimit h g K m else 0 with hΔ
  set D : ℕ → ℕ → ℝ := fun k N => ∑ m ∈ Icc 1 k, ∑ m' ∈ Icc 1 k, |Δ N m m'| with hD
  have hΔlim : ∀ m, 1 ≤ m → ∀ m', 1 ≤ m' → Tendsto (fun N => |Δ N m m'|) atTop (𝓝 0) :=
    fun m hm m' hm' => by
      have h2 := ((tendsto_layerPair_conductorWindow hh hg hA hsupp hgsupp hc1 hK hcrit hm hm').sub_const
        (if m = m' then conductorLimit h g K m else 0)).abs
      rw [sub_self, abs_zero] at h2
      exact h2
  have hDlim : ∀ k, Tendsto (D k) atTop (𝓝 0) := fun k => by
    have hs := tendsto_finsetSum (Icc 1 k) fun m hm => tendsto_finsetSum (Icc 1 k) fun m' hm' =>
      hΔlim m (Finset.mem_Icc.mp hm).1 m' (Finset.mem_Icc.mp hm').1
    simp only [Finset.sum_const_zero] at hs
    exact hs
  obtain ⟨M, hM, hDM⟩ := exists_tendsto_diagonal hDlim
  refine ⟨M, hM, fun ε hε => ?_⟩
  filter_upwards [eventually_ge_atTop 1, (hDM.eventually (gt_mem_nhds hε))] with N hN hDε b
  have hc0 : 0 < c N := by linarith [hc1 N]
  set S := Icc 1 (M N) with hSdef
  have hDS : D (M N) N = ∑ m ∈ S, ∑ m' ∈ S, |Δ N m m'| := rfl
  have hq := layerForm_sum hc0 hN S b (fun m => conductorWindow h g m N)
  have hdiag : ∑ m ∈ S, b m ^ 2 * conductorLimit h g K m =
      ∑ m ∈ S, ∑ m' ∈ S, b m * b m' * (if m = m' then conductorLimit h g K m else 0) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m (fun m' _ hm' => by rw [if_neg (Ne.symm hm'), mul_zero])
      (fun h => absurd hm h), if_pos rfl]
    ring
  rw [hq, hdiag, ← Finset.sum_sub_distrib]
  have hb : ∀ m ∈ S, ∀ m' ∈ S, |b m * b m'| ≤ ∑ l ∈ S, b l ^ 2 := fun m hm m' hm' => by
    have h1 : b m ^ 2 ≤ ∑ l ∈ S, b l ^ 2 :=
      Finset.single_le_sum (f := fun l => b l ^ 2) (fun l _ => sq_nonneg _) hm
    have h2 : b m' ^ 2 ≤ ∑ l ∈ S, b l ^ 2 :=
      Finset.single_le_sum (f := fun l => b l ^ 2) (fun l _ => sq_nonneg _) hm'
    rw [abs_mul]
    nlinarith [abs_nonneg (b m), abs_nonneg (b m'), sq_abs (b m), sq_abs (b m'),
      two_mul_le_add_sq |b m| |b m'|]
  have hB : 0 ≤ ∑ l ∈ S, b l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  calc |∑ m ∈ S, (∑ m' ∈ S, b m * b m' * layerPair (c N) N (conductorWindow h g m N)
          (conductorWindow h g m' N) -
        ∑ m' ∈ S, b m * b m' * (if m = m' then conductorLimit h g K m else 0))|
      = |∑ m ∈ S, ∑ m' ∈ S, b m * b m' * Δ N m m'| := by
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m' _ => by simp only [hΔ]; ring
    _ ≤ ∑ m ∈ S, ∑ m' ∈ S, |b m * b m' * Δ N m m'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ m ∈ S, ∑ m' ∈ S, (∑ l ∈ S, b l ^ 2) * |Δ N m m'| :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hb m hm m' hm') (abs_nonneg _)
    _ = (∑ l ∈ S, b l ^ 2) * D (M N) N := by
        rw [hDS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => (Finset.mul_sum _ _ _).symm
    _ ≤ (∑ l ∈ S, b l ^ 2) * ε := mul_le_mul_of_nonneg_left hDε.le hB
    _ = ε * ∑ l ∈ S, b l ^ 2 := mul_comm _ _

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
