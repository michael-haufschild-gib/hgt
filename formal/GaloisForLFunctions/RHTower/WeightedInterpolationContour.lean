import GaloisForLFunctions.RHTower.SubNyquistInterpolationTest

/-!
# Weighted interpolation profiles and their contour bound

The construction of `SubNyquistInterpolationTest` with the weight `Ŵ^N` replaced by an arbitrary
entire weight `Ψ` with real structure: `p` interpolates `±i/(P Ψ)` at the nodes, `Q = P·p`, and
`Φ = Ψ·Q` is `±i` at the nodes and `0` at the killed points.

The contour bound (`norm_wProfile_le`) holds at every point `x` outside the two rectangles
`[-X, X] × ±[y₀, 1]` at distance `≥ d` from their sides: if `|P ω| ≥ λ` and `|Ψ| ≥ c` on the
sides and `|P(x) ω(x)| ≤ M`, then `|Φ(x)| ≤ 2 (M/(λ d)) |Ψ(x)|/c`.  The point `x` may lie between
the rectangles, on the real axis, which is where the weight `cos(a'x) Ŵ(x)^N` suppresses the
critical zeros.
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial Lagrange
open scoped ComplexConjugate Interval

noncomputable section
namespace RHTower

open Zeta23 HTGeometry

/-- The interpolation data `±i / (P(t) Ψ(t))`, `+` below the real axis. -/
def wData (K : Finset ℂ) (Ψ : ℂ → ℂ) (t : ℂ) : ℂ :=
  (if t.im < 0 then I else -I) / ((killPoly K).eval t * Ψ t)

/-- The Lagrange interpolant of the weighted data at the nodes `S`. -/
def wPoly (K S : Finset ℂ) (Ψ : ℂ → ℂ) : ℂ[X] := interpolate S id (wData K Ψ)

/-- `Q = P · p`. -/
def wQ (K S : Finset ℂ) (Ψ : ℂ → ℂ) : ℂ[X] := killPoly K * wPoly K S Ψ

/-- The weighted profile `Φ = Ψ · Q`. -/
def wProfile (K S : Finset ℂ) (Ψ : ℂ → ℂ) (x : ℂ) : ℂ := Ψ x * (wQ K S Ψ).eval x

theorem wProfile_killed (K S : Finset ℂ) (Ψ : ℂ → ℂ) {r : ℂ} (hr : r ∈ K) :
    wProfile K S Ψ r = 0 ∧ wProfile K S Ψ (conj r) = 0 := by
  unfold wProfile wQ
  rw [eval_mul, eval_mul, eval_killPoly, eval_killPoly]
  constructor
  · rw [Finset.prod_eq_zero hr (by ring)]; ring
  · rw [Finset.prod_eq_zero hr (by rw [sub_self, mul_zero])]; ring

/-- At a node, `Φ = ±i`. -/
theorem wProfile_node {K S : Finset ℂ} {Ψ : ℂ → ℂ} {s : ℂ} (hs : s ∈ S)
    (hP : (killPoly K).eval s ≠ 0) (hΨ : Ψ s ≠ 0) :
    wProfile K S Ψ s = if s.im < 0 then I else -I := by
  unfold wProfile wQ wPoly
  have h := eval_interpolate_at_node (wData K Ψ) (Set.injOn_id _) hs
  simp only [id] at h
  rw [eval_mul, h]
  simp only [wData]
  field_simp

theorem natDegree_wQ_lt (K S : Finset ℂ) (Ψ : ℂ → ℂ) (hS : S.Nonempty) :
    (wQ K S Ψ).natDegree < 2 * K.card + S.card := by
  unfold wQ
  have hdeg := degree_interpolate_lt (s := S) (v := id) (wData K Ψ) (Set.injOn_id _)
  by_cases hp : wPoly K S Ψ = 0
  · rw [hp, mul_zero, natDegree_zero]
    have := hS.card_pos
    omega
  · rw [natDegree_mul (killPoly_ne_zero K) hp, natDegree_killPoly]
    have : (wPoly K S Ψ).natDegree < S.card := (natDegree_lt_iff_degree_lt hp).mpr hdeg
    omega

/-- **Real coefficients.**  With nodes closed under conjugation and off the real axis and a weight
with real structure, `Q` has real coefficients. -/
theorem wQ_real {K S : Finset ℂ} {Ψ : ℂ → ℂ} (hΨ : ∀ z, conj (Ψ (conj z)) = Ψ z)
    (hSc : ∀ s ∈ S, conj s ∈ S) (hSim : ∀ s ∈ S, s.im ≠ 0) :
    ∀ n, conj ((wQ K S Ψ).coeff n) = (wQ K S Ψ).coeff n := by
  set p := wPoly K S Ψ
  have hdata : ∀ s ∈ S, conj (wData K Ψ (conj s)) = wData K Ψ s := by
    intro s hs
    unfold wData
    rw [map_div₀, map_mul, hΨ, Complex.conj_im]
    have hPc : conj ((killPoly K).eval (conj s)) = (killPoly K).eval s := by
      rw [eval_killPoly, eval_killPoly, map_prod]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [map_mul, map_sub, map_sub, Complex.conj_conj, Complex.conj_conj]
      ring
    rw [hPc]
    congr 1
    rcases lt_or_gt_of_ne (hSim s hs) with h | h
    · rw [if_neg (by linarith), if_pos h, map_neg, Complex.conj_I, neg_neg]
    · rw [if_pos (by linarith), if_neg (by linarith), Complex.conj_I]
  have hmap : p.map (starRingEnd ℂ) = p := by
    have hdeg : (p.map (starRingEnd ℂ)).degree < S.card := by
      rw [degree_map]
      exact degree_interpolate_lt _ (Set.injOn_id _)
    have heval : ∀ s ∈ S, (p.map (starRingEnd ℂ)).eval (id s) = wData K Ψ s := by
      intro s hs
      rw [id, eval_map_starRingEnd]
      have := eval_interpolate_at_node (wData K Ψ) (Set.injOn_id _) (hSc s hs)
      simp only [id] at this
      simp only [p, wPoly]
      rw [this, hdata s hs]
    exact eq_interpolate_of_eval_eq _ (Set.injOn_id _) hdeg heval
  refine coeff_real_of_map_conj ?_
  unfold wQ
  rw [Polynomial.map_mul, map_conj_killPoly, hmap]

/-! ### The contour bound -/

open scoped Classical in
/-- **One rectangle, weighted.**  As `norm_rect_part_le`, for an entire weight `Ψ` nonvanishing on
the rectangle, with `|x - t| ≥ d` on `∂R`: the part of `Ψ(x) P(x) p(x)` carried by the nodes inside
`R` is at most `(M/(λ d)) |Ψ(x)|/c`. -/
theorem norm_rect_part_le_w {K S : Finset ℂ} {Ψ : ℂ → ℂ} {z w x σ : ℂ} {lam M c d : ℝ}
    (hσ : ‖σ‖ = 1) (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (hper : 2 * (|w.re - z.re| + |w.im - z.im|) ≤ 2 * Real.pi)
    (hΨd : Differentiable ℂ Ψ) (hΨR : ∀ t ∈ Rectangle z w, Ψ t ≠ 0)
    (hK : ∀ r ∈ K, r ∉ Rectangle z w ∧ conj r ∉ Rectangle z w)
    (hnode : ∀ s ∈ S, Rectangle z w ∈ 𝓝 s ∨ s ∉ Rectangle z w) (hSne : S.Nonempty)
    (hx : x ∉ Rectangle z w) (hc : 0 < c) (hlam : 0 < lam) (hd : 0 < d)
    (hborder : ∀ t ∈ RectangleBorder z w,
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ ∧ c ≤ ‖Ψ t‖ ∧ d ≤ ‖x - t‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖Ψ x * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rectangle z w),
          nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * Ψ s))‖
      ≤ M / (lam * d) * (‖Ψ x‖ / c) := by
  set U : Set ℂ := {t : ℂ | (killPoly K).eval t ≠ 0} ∩ {t : ℂ | Ψ t ≠ 0} with hU
  have hUo : IsOpen U :=
    (isOpen_ne_fun (Polynomial.continuous _) continuous_const).inter
      (isOpen_ne_fun hΨd.continuous continuous_const)
  have hRU : Rectangle z w ⊆ U := by
    intro t ht
    refine ⟨killPoly_eval_ne_zero fun r hr => ⟨?_, ?_⟩, hΨR t ht⟩
    · intro h; rw [h] at ht; exact (hK r hr).1 ht
    · intro h; rw [h] at ht; exact (hK r hr).2 ht
  set G : ℂ → ℂ := fun t => σ / ((killPoly K).eval t * Ψ t) with hG
  have hGd : DifferentiableOn ℂ G U := by
    refine (differentiableOn_const σ).div ?_ fun t ht => mul_ne_zero ht.1 ht.2
    exact ((Polynomial.differentiable _).mul hΨd).differentiableOn
  have hcont := sum_nodalWeight_inside_eq_rectangleIntegral (s := S) (v := id)
    (Set.injOn_id _) hSne hUo hRU hGd hzw hzw' (fun s hs => hnode s hs) hx
  simp only [id] at hcont
  have hsum : ∑ s ∈ S.filter (fun s => s ∈ Rectangle z w),
      nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * Ψ s)) =
      RectangleIntegral' (fun t => G t / ((x - t) * eval t (nodal S id))) z w := by
    rw [← hcont]
  rw [hsum]
  set A := Ψ x * (killPoly K).eval x * eval x (nodal S id) with hA
  set Rb := M / (lam * d) * (‖Ψ x‖ / c) with hRb
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hRb0 : 0 ≤ Rb := by rw [hRb]; positivity
  have hpt : ∀ t ∈ RectangleBorder z w, ‖A * (G t / ((x - t) * eval t (nodal S id)))‖ ≤ Rb := by
    intro t ht
    obtain ⟨hlt, hΨt, hxtd⟩ := hborder t ht
    have hPω : 0 < ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ := lt_of_lt_of_le hlam hlt
    have hPt : 0 < ‖(killPoly K).eval t‖ := by
      rcases (norm_nonneg ((killPoly K).eval t)).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hPω; exact absurd hPω (lt_irrefl _)
    have hωt : 0 < ‖eval t (nodal S id)‖ := by
      rcases (norm_nonneg (eval t (nodal S id))).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hPω; exact absurd hPω (lt_irrefl _)
    have hΨt0 : 0 < ‖Ψ t‖ := lt_of_lt_of_le hc hΨt
    have hxt0 : 0 < ‖x - t‖ := lt_of_lt_of_le hd hxtd
    have hnorm : ‖A * (G t / ((x - t) * eval t (nodal S id)))‖ =
        ‖Ψ x‖ * ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ /
          (‖(killPoly K).eval t‖ * ‖Ψ t‖ * ‖x - t‖ * ‖eval t (nodal S id)‖) := by
      simp only [hA, hG, norm_mul, norm_div, hσ]
      field_simp
    rw [hnorm, div_le_iff₀ (by positivity)]
    have hML : 0 ≤ M / (lam * d) := div_nonneg hM0 (by positivity)
    calc ‖Ψ x‖ * ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖
        ≤ ‖Ψ x‖ * M := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hM (by positivity)
      _ = M / (lam * d) * (‖Ψ x‖ / c) * (lam * c * d) := by field_simp
      _ ≤ M / (lam * d) * (‖Ψ x‖ / c) *
            ((‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖) * ‖Ψ t‖ * ‖x - t‖) := by
          gcongr
      _ = Rb * (‖(killPoly K).eval t‖ * ‖Ψ t‖ * ‖x - t‖ * ‖eval t (nodal S id)‖) := by
          rw [hRb]; ring
  have hRI : RectangleIntegral' (fun t => A * (G t / ((x - t) * eval t (nodal S id)))) z w =
      A * RectangleIntegral' (fun t => G t / ((x - t) * eval t (nodal S id))) z w := by
    rw [RectangleIntegral', RectangleIntegral', rectangleIntegral_const_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [← hRI, RectangleIntegral', norm_smul]
  have hbd := norm_rectangleIntegral_le hpt
  have h2pi : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2pi]
  calc 1 / (2 * Real.pi) * ‖RectangleIntegral (fun t => A * (G t / ((x - t) *
        eval t (nodal S id)))) z w‖
      ≤ 1 / (2 * Real.pi) * (2 * (|w.re - z.re| + |w.im - z.im|) * Rb) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (2 * Real.pi * Rb) := by gcongr
    _ = Rb := by field_simp

open scoped Classical in
/-- **One horizontal band, weighted.**  The rectangle `[-X, X] × [a, b]`, lying in
`y₀ ≤ |Im t| ≤ 1` with its horizontal sides on `|Im t| ∈ {y₀, 1}`, carries at most
`(M/(λ d)) |Ψ(x)|/c` of `Φ(x)` for `x` outside it. -/
theorem norm_band_part_le_w {K S : Finset ℂ} {Ψ : ℂ → ℂ} {x σ : ℂ} {X a b y₀ lam M c d : ℝ}
    (hσ : ‖σ‖ = 1) (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hab : a ≤ b) (hba : b - a ≤ 1)
    (hband : ∀ y : ℝ, a ≤ y → y ≤ b → y₀ ≤ |y| ∧ |y| ≤ 1)
    (ha : |a| = y₀ ∨ |a| = 1) (hb : |b| = y₀ ∨ |b| = 1) (hSne : S.Nonempty)
    (hS : ∀ s ∈ S, |s.re| < X ∧ ((a < s.im ∧ s.im < b) ∨ s.im < a ∨ b < s.im))
    (hK : ∀ r ∈ K, X < |r.re| ∨ r.im < a ∨ b < r.im)
    (hKc : ∀ r ∈ K, X < |(conj r).re| ∨ (conj r).im < a ∨ b < (conj r).im)
    (hΨd : Differentiable ℂ Ψ)
    (hΨ0 : ∀ t : ℂ, |t.re| ≤ X → y₀ ≤ |t.im| → |t.im| ≤ 1 → Ψ t ≠ 0)
    (hxR : X < |x.re| ∨ x.im < a ∨ b < x.im) (hc : 0 < c) (hlam : 0 < lam) (hd : 0 < d)
    (hborder : ∀ t : ℂ, (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1)) →
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ ∧ c ≤ ‖Ψ t‖ ∧ d ≤ ‖x - t‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖Ψ x * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rectangle ⟨-X, a⟩ ⟨X, b⟩),
          nodalWeight S id s * (x - s)⁻¹ * (σ / ((killPoly K).eval s * Ψ s))‖
      ≤ M / (lam * d) * (‖Ψ x‖ / c) := by
  set z : ℂ := ⟨-X, a⟩ with hz
  set w : ℂ := ⟨X, b⟩ with hw
  have hmemR : ∀ t : ℂ, t ∈ Rectangle z w ↔ (-X ≤ t.re ∧ t.re ≤ X) ∧ (a ≤ t.im ∧ t.im ≤ b) := by
    intro t
    rw [Rectangle, Complex.mem_reProdIm, hz, hw]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith), Set.uIcc_of_le hab, Set.mem_Icc]
  have hout : ∀ q : ℂ, (X < |q.re| ∨ q.im < a ∨ b < q.im) → q ∉ Rectangle z w := by
    intro q hq hqR
    rw [hmemR] at hqR
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hqR
    have := abs_le.mpr ⟨h1, h2⟩
    rcases hq with hq | hq | hq <;> linarith
  have hΨR : ∀ t ∈ Rectangle z w, Ψ t ≠ 0 := by
    intro t ht
    rw [hmemR] at ht
    obtain ⟨hre, hi1, hi2⟩ := ht
    exact hΨ0 t (abs_le.mpr ⟨hre.1, hre.2⟩) (hband t.im hi1 hi2).1 (hband t.im hi1 hi2).2
  have hnode : ∀ s ∈ S, Rectangle z w ∈ 𝓝 s ∨ s ∉ Rectangle z w := by
    intro s hs
    obtain ⟨hre, hband' | hlow | hhigh⟩ := hS s hs
    · left
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hz, hw]
      simp only [Set.uIoo_of_le (show -X ≤ X by linarith), Set.uIoo_of_le hab, Set.mem_Ioo]
      have := abs_lt.mp hre
      exact ⟨⟨this.1, this.2⟩, hband'.1, hband'.2⟩
    · right; exact hout s (Or.inr (Or.inl hlow))
    · right; exact hout s (Or.inr (Or.inr hhigh))
  have hper : 2 * (|w.re - z.re| + |w.im - z.im|) ≤ 2 * Real.pi := by
    have h1 : w.re - z.re = 2 * X := by rw [hz, hw]; ring
    have h2 : w.im - z.im = b - a := rfl
    rw [h1, h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith [Real.pi_gt_three]
  refine norm_rect_part_le_w hσ (show z.re ≤ w.re by show -X ≤ X; linarith) hab hper hΨd hΨR
    (fun r hr => ⟨hout r (hK r hr), hout _ (hKc r hr)⟩) hnode hSne (hout x hxR) hc hlam hd
    (fun t ht => hborder t ?_) hM
  have htR := (hmemR t).mp (rectangleBorder_subset_rectangle z w ht)
  obtain ⟨⟨htr1, htr2⟩, hti1, hti2⟩ := htR
  have htabs : |t.re| ≤ X := abs_le.mpr ⟨htr1, htr2⟩
  rcases ht with ((h | h) | h) | h
  · right
    refine ⟨htabs, ?_⟩
    have : t.im = a := (Complex.mem_reProdIm.mp h).2
    rw [this]; exact ha
  · left
    have : t.re = -X := (Complex.mem_reProdIm.mp h).1
    rw [this, abs_neg, abs_of_pos hX0]
    exact ⟨rfl, hband t.im hti1 hti2⟩
  · right
    refine ⟨htabs, ?_⟩
    have : t.im = b := (Complex.mem_reProdIm.mp h).2
    rw [this]; exact hb
  · left
    have : t.re = X := (Complex.mem_reProdIm.mp h).1
    rw [this, abs_of_pos hX0]
    exact ⟨rfl, hband t.im hti1 hti2⟩

/-- **The weighted contour bound.**  Let the nodes lie in `|Re s| < X`, `y₀ < |Im s| < 1`, every
killed point satisfy `|Re r| > X`, `|Im r| < y₀` or `|Im r| > 1`, and `x` lie outside the
rectangles `[-X, X] × ±[y₀, 1]`.  If `|P ω| ≥ λ`, `|Ψ| ≥ c` and `|x - t| ≥ d` on their sides and
`|P(x) ω(x)| ≤ M`, then `|Φ(x)| ≤ 2 (M/(λ d)) |Ψ(x)|/c`. -/
theorem norm_wProfile_le {K S : Finset ℂ} {Ψ : ℂ → ℂ} {X y₀ lam M c d : ℝ} {x : ℂ}
    (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2)
    (hS : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| < 1)
    (hK : ∀ r ∈ K, X < |r.re| ∨ |r.im| < y₀ ∨ 1 < |r.im|)
    (hxR : X < |x.re| ∨ |x.im| < y₀ ∨ 1 < |x.im|)
    (hΨd : Differentiable ℂ Ψ)
    (hΨ0 : ∀ t : ℂ, |t.re| ≤ X → y₀ ≤ |t.im| → |t.im| ≤ 1 → Ψ t ≠ 0)
    (hc : 0 < c) (hlam : 0 < lam) (hd : 0 < d)
    (hborder : ∀ t : ℂ, (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1)) →
      lam ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ ∧ c ≤ ‖Ψ t‖ ∧ d ≤ ‖x - t‖)
    (hM : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M) :
    ‖wProfile K S Ψ x‖ ≤ 2 * (M / (lam * d) * (‖Ψ x‖ / c)) := by
  classical
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    rw [wProfile, wQ, wPoly, interpolate_empty, mul_zero, eval_zero, mul_zero, norm_zero]
    positivity
  have hxS : ∀ s ∈ S, x ≠ id s := by
    intro s hs h
    obtain ⟨h1, h2, h3⟩ := hS s hs
    simp only [id] at h
    rw [h] at hxR
    rcases hxR with h' | h' | h' <;> linarith
  set Rp : Set ℂ := Rectangle ⟨-X, y₀⟩ ⟨X, 1⟩ with hRp
  set Rm : Set ℂ := Rectangle ⟨-X, -1⟩ ⟨X, -y₀⟩ with hRm
  have hmemRp : ∀ s ∈ S, s ∈ Rp ↔ 0 < s.im := by
    intro s hs
    obtain ⟨hre, him, him'⟩ := hS s hs
    rw [hRp, Rectangle, Complex.mem_reProdIm]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith),
      Set.uIcc_of_le (show y₀ ≤ 1 by linarith), Set.mem_Icc]
    have hre' := abs_le.mp hre.le
    have hi := abs_lt.mp him'
    constructor
    · rintro ⟨-, h, -⟩; linarith
    · intro h
      rw [abs_of_pos h] at him
      exact ⟨hre', by linarith, by linarith⟩
  have hmemRm : ∀ s ∈ S, s ∈ Rm ↔ s.im < 0 := by
    intro s hs
    obtain ⟨hre, him, him'⟩ := hS s hs
    rw [hRm, Rectangle, Complex.mem_reProdIm]
    simp only [Set.uIcc_of_le (show -X ≤ X by linarith),
      Set.uIcc_of_le (show (-1 : ℝ) ≤ -y₀ by linarith), Set.mem_Icc]
    have hre' := abs_le.mp hre.le
    have hi := abs_lt.mp him'
    constructor
    · rintro ⟨-, -, h⟩; linarith
    · intro h
      rw [abs_of_neg h] at him
      exact ⟨hre', by linarith, by linarith⟩
  have hsplit : eval x (wPoly K S Ψ) = eval x (nodal S id) *
      ((∑ s ∈ S.filter (fun s => s ∈ Rp),
          nodalWeight S id s * (x - s)⁻¹ * (-I / ((killPoly K).eval s * Ψ s))) +
        ∑ s ∈ S.filter (fun s => s ∈ Rm),
          nodalWeight S id s * (x - s)⁻¹ * (I / ((killPoly K).eval s * Ψ s))) := by
    rw [wPoly, eval_interpolate_not_at_node _ hxS]
    congr 1
    simp only [id]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun s => s ∈ Rp)]
    congr 1
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_filter] at hs
      have h := (hmemRp s hs.1).mp hs.2
      rw [wData, if_neg (by linarith)]
    · have hf : S.filter (fun s => s ∉ Rp) = S.filter (fun s => s ∈ Rm) := by
        refine Finset.filter_congr fun s hs => ?_
        rw [hmemRp s hs, hmemRm s hs]
        have := (hS s hs).2.1
        constructor
        · intro h
          rcases lt_trichotomy s.im 0 with h' | h' | h'
          · exact h'
          · rw [h', abs_zero] at this; linarith
          · exact absurd h' h
        · intro h h'; linarith
      rw [hf]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_filter] at hs
      have h := (hmemRm s hs.1).mp hs.2
      rw [wData, if_pos h]
  have hΦ : wProfile K S Ψ x =
      Ψ x * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rp),
          nodalWeight S id s * (x - s)⁻¹ * (-I / ((killPoly K).eval s * Ψ s)) +
      Ψ x * (killPoly K).eval x * eval x (nodal S id) *
        ∑ s ∈ S.filter (fun s => s ∈ Rm),
          nodalWeight S id s * (x - s)⁻¹ * (I / ((killPoly K).eval s * Ψ s)) := by
    rw [wProfile, wQ, eval_mul, hsplit]
    ring
  have hKc : ∀ r ∈ K, X < |(conj r).re| ∨ |(conj r).im| < y₀ ∨ 1 < |(conj r).im| := by
    intro r hr
    rw [Complex.conj_im, Complex.conj_re, abs_neg]
    exact hK r hr
  have hsplitK : ∀ q : ℂ, (X < |q.re| ∨ |q.im| < y₀ ∨ 1 < |q.im|) →
      (X < |q.re| ∨ q.im < y₀ ∨ 1 < q.im) ∧ (X < |q.re| ∨ q.im < -1 ∨ -y₀ < q.im) := by
    intro q hq
    rcases hq with h | h | h
    · exact ⟨Or.inl h, Or.inl h⟩
    · have := abs_lt.mp h
      exact ⟨Or.inr (Or.inl this.2), Or.inr (Or.inr this.1)⟩
    · rcases lt_or_ge 0 q.im with h' | h'
      · rw [abs_of_pos h'] at h
        exact ⟨Or.inr (Or.inr h), Or.inr (Or.inr (by linarith))⟩
      · rw [abs_of_nonpos h'] at h
        exact ⟨Or.inr (Or.inl (by linarith)), Or.inr (Or.inl (by linarith))⟩
  have hp := norm_band_part_le_w (K := K) (S := S) (Ψ := Ψ) (x := x) (σ := -I) (X := X)
    (a := y₀) (b := 1) (y₀ := y₀) (by rw [norm_neg, Complex.norm_I]) hX0 hX (by linarith)
    (by linarith) (fun y h1 h2 => by rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩)
    (Or.inl (abs_of_pos hy0)) (Or.inr abs_one) hSne
    (fun s hs => by
      obtain ⟨hre, him, him'⟩ := hS s hs
      refine ⟨hre, ?_⟩
      have hi := abs_lt.mp him'
      rcases lt_or_ge 0 s.im with h | h
      · rw [abs_of_pos h] at him
        exact Or.inl ⟨him, by linarith⟩
      · rw [abs_of_nonpos h] at him
        exact Or.inr (Or.inl (by linarith)))
    (fun r hr => (hsplitK r (hK r hr)).1) (fun r hr => (hsplitK _ (hKc r hr)).1) hΨd hΨ0
    (hsplitK x hxR).1 hc hlam hd hborder hM
  have hm := norm_band_part_le_w (K := K) (S := S) (Ψ := Ψ) (x := x) (σ := I) (X := X)
    (a := -1) (b := -y₀) (y₀ := y₀) Complex.norm_I hX0 hX (by linarith) (by linarith)
    (fun y h1 h2 => by rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩)
    (Or.inr (by rw [abs_neg, abs_one])) (Or.inl (by rw [abs_neg, abs_of_pos hy0])) hSne
    (fun s hs => by
      obtain ⟨hre, him, him'⟩ := hS s hs
      refine ⟨hre, ?_⟩
      have hi := abs_lt.mp him'
      rcases lt_or_ge s.im 0 with h | h
      · rw [abs_of_neg h] at him
        exact Or.inl ⟨by linarith, by linarith⟩
      · rw [abs_of_nonneg h] at him
        exact Or.inr (Or.inr (by linarith)))
    (fun r hr => (hsplitK r (hK r hr)).2) (fun r hr => (hsplitK _ (hKc r hr)).2) hΨd hΨ0
    (hsplitK x hxR).2 hc hlam hd hborder hM
  rw [hΦ]
  refine (norm_add_le _ _).trans ?_
  linarith

end RHTower
