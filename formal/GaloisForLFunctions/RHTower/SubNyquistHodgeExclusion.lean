import GaloisForLFunctions.RHTower.SubNyquistInterpolationTest
import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion
import GaloisForLFunctions.HTGeometry.ForwardDifferenceProductSelection

/-!
# Sub-Nyquist Hodge exclusion

Let `Z` be a zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and let `ρ₀` be a
zero with `|β₀ - ½| ≥ δ > 0` at height `|γ₀| ≥ 102`.  Let `n` be the number of distinct zeros
with `γ₀ - 100 < γ ≤ γ₀ + 100`.  The level-`a` Hodge index (Weil positivity on `C²` tests
supported in `[-a, a]` whose transforms vanish at `±i/2`) fails as soon as

> `4((n + 1) log(10⁶/δ) + log(A₀(|γ₀| + 3))) ≤ a`

(`not_hodgeIndex_below_nyquist_horizon`).  For `ζ` the window count is `O(log |γ₀|)`, so the
level-`a` Hodge index excludes zeros of depth `δ` up to height
`exp(a/(2000 A₀ log(10⁶/δ))) - 3` (`zeta_hodge_index_nyquist_horizon`).

The level is linear in `n` with no power of `log a`.  The Nyquist lattice of
`ClusterRobustHodgeExclusion` (`not_forall_hodge_exclusion_sublinear_level`) satisfies the Hodge
index with `n ≤ 2000 a`, so the linear dependence on the window count is sharp up to the constant
and the factor `log(10⁶/δ)`.

**The test.**  With window coordinates `x_ρ = γ_ρ - γ₀ - i(β_ρ - ½)`, the transform of the test
is `Ŵ(x)^N Q(x)/lc(Q)`, `Q = P·p`, where

* the *nodes* are the window values in `[-X, X] × ±(y₀, 1)`, and `p` interpolates
  `±i/(P Ŵ^N)` there, so every node contributes exactly `-m_ρ/lc(Q)²` to the Weil form;
* the *killed* values are the other window values and the polar point `-γ₀ + i/2`, and `P`
  vanishes there.

No cluster estimate is needed: the deep zero is a node like every other deep zero of the window.
The zeros outside the window are bounded by the contour formula of `SubNyquistInterpolationTest`,
which needs only a lower bound for `|P ω|` on the sides of the two rectangles.  That bound comes
from the product selection of `HTGeometry.ForwardDifferenceProductSelection`: the sides `X` and
`y₀` are grid points at which `Π |X - |Re v||` and `Π |y₀ - |Im v||` are at least
`(1/(8e))^{|V|}` and `(δ/(8e))^{|V|}` (`subNyquist_selection`), and a window value is a root of
`P ω` of multiplicity at most two (`sq_prod_le_killPoly_nodal`).  The loss is
`(16e(H + 1)/δ)^{4n}`, a constant to the power `n`, where a gap selection among `n` points would
lose `n^{O(n)}`.
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial Lagrange
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 HTGeometry

/-! ### Products over the window values -/

/-- Reindexing a product over a conjugation-closed set by conjugation. -/
theorem prod_conj_eq_of_conj_mem {K : Finset ℂ} (hK : ∀ r ∈ K, conj r ∈ K) (f : ℂ → ℝ) :
    ∏ r ∈ K, f (conj r) = ∏ r ∈ K, f r :=
  Finset.prod_nbij' (fun r => conj r) (fun r => conj r) (fun r hr => hK r hr)
    (fun r hr => hK r hr) (fun r _ => Complex.conj_conj r) (fun r _ => Complex.conj_conj r)
    (fun _ _ => rfl)

/-- **Multiplicity bound.**  If the window values `V` split into nodes `S` and killed points `Kw`,
the killed points closed under conjugation and the nodes within `R ≥ 1` of `t`, then
`(Π_V |t - v|)² ≤ R^{|V|} |P_{Kw}(t)| |ω_S(t)|`: every value is a root of `P ω` of multiplicity at
most two. -/
theorem sq_prod_le_killPoly_nodal {V S Kw : Finset ℂ} (hV : V = S ∪ Kw) (hdisj : Disjoint S Kw)
    (hKc : ∀ r ∈ Kw, conj r ∈ Kw) {t : ℂ} {R : ℝ} (hR : 1 ≤ R) (hSR : ∀ s ∈ S, ‖t - s‖ ≤ R) :
    (∏ v ∈ V, ‖t - v‖) ^ 2 ≤
      R ^ V.card * (‖(killPoly Kw).eval t‖ * ‖eval t (nodal S id)‖) := by
  have hP : ‖(killPoly Kw).eval t‖ = (∏ r ∈ Kw, ‖t - r‖) ^ 2 := by
    rw [norm_eval_killPoly, Finset.prod_mul_distrib,
      prod_conj_eq_of_conj_mem hKc (fun r => ‖t - r‖), sq]
  have hω : ‖eval t (nodal S id)‖ = ∏ s ∈ S, ‖t - s‖ := norm_eval_nodal S t
  have hSle : ∏ s ∈ S, ‖t - s‖ ≤ R ^ V.card := by
    calc ∏ s ∈ S, ‖t - s‖ ≤ ∏ _s ∈ S, R :=
          Finset.prod_le_prod (fun s _ => norm_nonneg _) hSR
      _ = R ^ S.card := Finset.prod_const R
      _ ≤ R ^ V.card := pow_le_pow_right₀ hR (Finset.card_le_card (by
          rw [hV]; exact Finset.subset_union_left))
  rw [hV, Finset.prod_union hdisj, hP, hω, Finset.card_union_of_disjoint hdisj]
  have hS0 : 0 ≤ ∏ s ∈ S, ‖t - s‖ := Finset.prod_nonneg fun s _ => norm_nonneg _
  have hK0 : 0 ≤ ∏ r ∈ Kw, ‖t - r‖ := Finset.prod_nonneg fun r _ => norm_nonneg _
  rw [← Finset.card_union_of_disjoint hdisj, ← hV]
  calc ((∏ s ∈ S, ‖t - s‖) * ∏ r ∈ Kw, ‖t - r‖) ^ 2
      = (∏ s ∈ S, ‖t - s‖) * (∏ s ∈ S, ‖t - s‖) * (∏ r ∈ Kw, ‖t - r‖) ^ 2 := by ring
    _ ≤ R ^ V.card * (∏ s ∈ S, ‖t - s‖) * (∏ r ∈ Kw, ‖t - r‖) ^ 2 := by gcongr
    _ = R ^ V.card * ((∏ r ∈ Kw, ‖t - r‖) ^ 2 * ∏ s ∈ S, ‖t - s‖) := by ring

/-- Upper bound for `|P_{Kw}(x) ω_S(x)|` when every root is within `B ≥ 1` of `x`. -/
theorem killPoly_nodal_le {S Kw : Finset ℂ} {x : ℂ} {B : ℝ} {n : ℕ} (hB : 1 ≤ B)
    (hK : ∀ r ∈ Kw, ‖x - r‖ ≤ B ∧ ‖x - conj r‖ ≤ B) (hS : ∀ s ∈ S, ‖x - s‖ ≤ B)
    (hcard : Kw.card + S.card ≤ n) :
    ‖(killPoly Kw).eval x‖ * ‖eval x (nodal S id)‖ ≤ B ^ (2 * n) := by
  rw [norm_eval_killPoly, norm_eval_nodal]
  have h1 : ∏ r ∈ Kw, (‖x - r‖ * ‖x - conj r‖) ≤ ∏ _r ∈ Kw, B ^ 2 :=
    Finset.prod_le_prod (fun r _ => by positivity) fun r hr => by
      rw [sq]; exact mul_le_mul (hK r hr).1 (hK r hr).2 (norm_nonneg _) (by linarith)
  have h2 : ∏ s ∈ S, ‖x - s‖ ≤ ∏ _s ∈ S, B :=
    Finset.prod_le_prod (fun s _ => norm_nonneg _) hS
  rw [Finset.prod_const] at h1 h2
  calc (∏ r ∈ Kw, (‖x - r‖ * ‖x - conj r‖)) * ∏ s ∈ S, ‖x - s‖
      ≤ (B ^ 2) ^ Kw.card * B ^ S.card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun s _ => norm_nonneg _) (by positivity)
    _ = B ^ (2 * Kw.card + S.card) := by rw [← pow_mul, ← pow_add]
    _ ≤ B ^ (2 * n) := pow_le_pow_right₀ hB (by omega)

/-! ### The contour -/

/-- On the sides `|Re t| = X`, `y₀ ≤ |Im t| ≤ 1` and `|Im t| ∈ {y₀, 1}`, `|Re t| ≤ X`, the product
`Π_V |t - v|` is at least `(δ/(8e))^{|V|}`, given the one-dimensional products at `X` and `y₀`. -/
theorem prod_norm_sub_ge_on_sides {V : Finset ℂ} {X y₀ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hV : ∀ v ∈ V, |v.im| ≤ 1 / 2)
    (hXp : (1 / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, abs (X - |v.re|))
    (hyp : (δ / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, abs (y₀ - |v.im|))
    {t : ℂ} (ht : (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
      (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) :
    (δ / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, ‖t - v‖ := by
  have he : 0 < 2 * Real.exp 1 := by positivity
  have hδe : δ / 4 / (2 * Real.exp 1) ≤ 1 / 4 / (2 * Real.exp 1) := by gcongr
  have hδe0 : 0 ≤ δ / 4 / (2 * Real.exp 1) := by positivity
  rcases ht with ⟨hre, -, -⟩ | ⟨-, him | him⟩
  · refine le_trans (pow_le_pow_left₀ hδe0 hδe _) (hXp.trans ?_)
    refine Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => ?_
    rw [← hre]
    refine (abs_abs_sub_abs_le_abs_sub t.re v.re).trans ?_
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  · refine hyp.trans ?_
    refine Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => ?_
    rw [← him]
    refine (abs_abs_sub_abs_le_abs_sub t.im v.im).trans ?_
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  · rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun v _ => hδe0) fun v hv => ?_
    have h1 : |t.im| - |v.im| ≤ ‖t - v‖ := by
      refine (le_abs_self _).trans ((abs_abs_sub_abs_le_abs_sub t.im v.im).trans ?_)
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 : δ / 4 / (2 * Real.exp 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ he]
      have := Real.add_one_le_exp 1
      nlinarith
    linarith [hV v hv]

/-- **Contour selection.**  For finitely many window values `v` with `|Im v| ≤ ½` and a depth
`0 < δ ≤ 1`, there are `X ∈ [½, ¾]` and `y₀ ∈ [δ/4, δ/2]`, attained by no `|Re v|`, resp.
`|Im v|`, such that `Π_V |t - v| ≥ (δ/(8e))^{|V|}` on the sides of the rectangles
`[-X, X] × ±[y₀, 1]`.  Both coordinates come from the forward-difference product selection. -/
theorem subNyquist_selection {V : Finset ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hV : ∀ v ∈ V, |v.im| ≤ 1 / 2) :
    ∃ X y₀ : ℝ, 1 / 2 ≤ X ∧ X ≤ 3 / 4 ∧ δ / 4 ≤ y₀ ∧ y₀ ≤ δ / 2 ∧
      (∀ v ∈ V, |v.re| ≠ X ∧ |v.im| ≠ y₀) ∧
      ∀ t : ℂ, ((|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) →
        (δ / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, ‖t - v‖ := by
  obtain ⟨X, ⟨hX1, hX2⟩, hXp⟩ := exists_mem_Icc_prod_abs_sub_ge V (fun v => |v.re|) (1 / 2)
    (L := 1 / 4) (by norm_num)
  obtain ⟨y₀, ⟨hy1, hy2⟩, hyp⟩ := exists_mem_Icc_prod_abs_sub_ge V (fun v => |v.im|) (δ / 4)
    (L := δ / 4) (by positivity)
  have hne : ∀ {f : ℂ → ℝ} {b : ℝ}, 0 < b → b ^ V.card ≤ ∏ v ∈ V, f v → ∀ v ∈ V, f v ≠ 0 := by
    intro f b hb h
    have hpos : 0 < ∏ v ∈ V, f v := lt_of_lt_of_le (pow_pos hb _) h
    exact Finset.prod_ne_zero_iff.mp hpos.ne'
  have hXn := hne (by positivity) hXp
  have hyn := hne (by positivity) hyp
  refine ⟨X, y₀, hX1, by linarith, hy1, by linarith, fun v hv => ⟨?_, ?_⟩, fun t ht =>
    prod_norm_sub_ge_on_sides hδ hδ1 hV hXp hyp ht⟩
  · intro h; apply hXn v hv; rw [h, sub_self, abs_zero]
  · intro h; apply hyn v hv; rw [h, sub_self, abs_zero]

/-- **The border bound.**  With the window values split into nodes and conjugation-closed killed
points as in `subNyquist_selection`, and a polar point `p` with `|Re p| ≥ H + 2`,
`|P(t) ω(t)| ≥ (δ/(16e))^{2n}` on the sides of the rectangles, `P = P_{Kw ∪ {p}}`. -/
theorem border_lower_bound {V S Kw : Finset ℂ} {X y₀ δ H : ℝ} {p : ℂ} {n : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : X ≤ 3 / 4) (hy₀ : y₀ ≤ 1) (hH : 0 ≤ H)
    (hVSK : V = S ∪ Kw) (hdisj : Disjoint S Kw) (hKc : ∀ r ∈ Kw, conj r ∈ Kw)
    (hS : ∀ s ∈ S, |s.re| < X ∧ |s.im| ≤ 1 / 2) (hVre : ∀ v ∈ V, |v.re| ≤ H)
    (hp : H + 2 ≤ |p.re|) (hcard : V.card ≤ n)
    (hside : ∀ t : ℂ, ((|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) →
        (δ / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, ‖t - v‖)
    (t : ℂ) (ht : (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) :
    (δ / (16 * Real.exp 1)) ^ (2 * n) ≤
      ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖ := by
  have htre : |t.re| ≤ X := by
    rcases ht with h | h
    · exact h.1.le
    · exact h.1
  have htim : |t.im| ≤ 1 := by
    rcases ht with h | ⟨-, h | h⟩
    · exact h.2.2
    · rw [h]; exact hy₀
    · rw [h]
  have hSR : ∀ s ∈ S, ‖t - s‖ ≤ 4 := by
    intro s hs
    have h1 := Complex.norm_le_abs_re_add_abs_im (t - s)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub t.re s.re
    have h3 := abs_sub t.im s.im
    linarith [(hS s hs).1, (hS s hs).2]
  have hsq := sq_prod_le_killPoly_nodal hVSK hdisj hKc (by norm_num : (1 : ℝ) ≤ 4) hSR
  have hlow := hside t ht
  set b := δ / 4 / (2 * Real.exp 1) with hb
  have hb0 : 0 ≤ b := by positivity
  have hpow : (b ^ V.card) ^ 2 ≤ (∏ v ∈ V, ‖t - v‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow 2
  have hpK : p ∉ Kw := by
    intro h
    have := hVre p (by rw [hVSK]; exact Finset.mem_union_right _ h)
    linarith
  have hPins : ‖(killPoly (insert p Kw)).eval t‖ =
      ‖t - p‖ * ‖t - conj p‖ * ‖(killPoly Kw).eval t‖ := by
    rw [norm_eval_killPoly, norm_eval_killPoly, Finset.prod_insert hpK]
  have hfar : ∀ q : ℂ, H + 2 ≤ |q.re| → 1 ≤ ‖t - q‖ := by
    intro q hq
    have h1 := Complex.abs_re_le_norm (t - q)
    rw [Complex.sub_re] at h1
    have h2 := abs_sub_abs_le_abs_sub q.re t.re
    rw [abs_sub_comm] at h2
    linarith
  have hp1 := hfar p hp
  have hp2 := hfar (conj p) (by rw [Complex.conj_re]; exact hp)
  have hPK : ‖(killPoly Kw).eval t‖ ≤ ‖(killPoly (insert p Kw)).eval t‖ := by
    rw [hPins]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hp1 hp2)
  have hκ1 : δ / (16 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Real.add_one_le_exp 1
    linarith
  have e : (δ / (16 * Real.exp 1)) ^ 2 = b ^ 2 / 4 := by
    rw [hb]; field_simp; ring
  have h4 : (0 : ℝ) < 4 ^ V.card := by positivity
  calc (δ / (16 * Real.exp 1)) ^ (2 * n)
      ≤ (δ / (16 * Real.exp 1)) ^ (2 * V.card) :=
        pow_le_pow_of_le_one (by positivity) hκ1 (by omega)
    _ = (b ^ V.card) ^ 2 / 4 ^ V.card := by
        rw [pow_mul, e, div_pow, ← pow_mul, ← pow_mul, mul_comm V.card 2]
    _ ≤ (∏ v ∈ V, ‖t - v‖) ^ 2 / 4 ^ V.card := div_le_div_of_nonneg_right hpow h4.le
    _ ≤ ‖(killPoly Kw).eval t‖ * ‖eval t (nodal S id)‖ := by
        rw [div_le_iff₀ h4]; linarith
    _ ≤ ‖(killPoly (insert p Kw)).eval t‖ * ‖eval t (nodal S id)‖ :=
        mul_le_mul_of_nonneg_right hPK (norm_nonneg _)

/-! ### The tail -/

/-- `168 e^{1/2}/(cos 1 · w₁)`, the decay constant of `Ŵ/(cos 1 · w₁)` in the strip. -/
def unitDecayRatio : ℝ := Real.exp (1 / 2) * 168 / unitHatFloor

theorem unitDecayRatio_pos : 0 < unitDecayRatio := by
  unfold unitDecayRatio; have := unitHatFloor_pos; positivity

/-- In the strip `|Im x| ≤ ½`, `|Ŵ(x)|/(cos 1 · w₁) ≤ K₁/(1 + |Re x|)²`. -/
theorem norm_unitHat_div_le {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖unitHat x‖ / unitHatFloor ≤ unitDecayRatio / (1 + |x.re|) ^ 2 := by
  have hW : ContDiff ℝ 2 (fun u => ((sinhTestWeight 1 u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff 1)
  have hWs : ∀ u, (fun u => ((sinhTestWeight 1 u : ℝ) : ℂ)) u ≠ 0 → |u| ≤ 1 := fun u hu =>
    sinhTestWeight_supp zero_le_one u (fun h => hu (by simp [h]))
  have hdec := norm_paperFT_le_decay hW hWs x
  change _ ≤ Real.exp _ * (4 * testNorm (sinhTestWeight 1)) / _ at hdec
  have hc := unitHatFloor_pos
  have hD : 0 < (1 + |x.re|) ^ 2 := by positivity
  have hE : Real.exp (|x.im| * 1) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hT : 4 * testNorm (sinhTestWeight 1) ≤ 168 := by linarith [testNorm_unitWeight_le]
  have hT0 := testNorm_nonneg (sinhTestWeight 1)
  have hnum : Real.exp (|x.im| * 1) * (4 * testNorm (sinhTestWeight 1)) ≤ Real.exp (1 / 2) * 168 :=
    mul_le_mul hE hT (by positivity) (by positivity)
  unfold unitDecayRatio
  rw [div_le_div_iff₀ hc hD]
  have h1 : ‖unitHat x‖ * (1 + |x.re|) ^ 2 ≤ Real.exp (1 / 2) * 168 := by
    rw [← le_div_iff₀ hD]
    exact hdec.trans (div_le_div_of_nonneg_right hnum hD.le)
  calc ‖unitHat x‖ * (1 + |x.re|) ^ 2 ≤ Real.exp (1 / 2) * 168 := h1
    _ = Real.exp (1 / 2) * 168 / unitHatFloor * unitHatFloor := by field_simp

theorem interp_tail_identity (P H κ K D : ℝ) (n N : ℕ) (hκ : κ ≠ 0) (hD : D ≠ 0) :
    2 * ((P * D) ^ 2 * ((H + 1) * D) ^ (2 * n) / κ ^ (2 * n) * (K / D ^ 2) ^ N) * D ^ (2 * N) =
      2 * P ^ 2 * ((H + 1) / κ) ^ (2 * n) * K ^ N * D ^ (2 * n + 2) := by
  rw [div_pow, div_pow, ← pow_mul, mul_pow, mul_pow, pow_add]
  field_simp

/-- **The profile away from the window.**  In the situation of `border_lower_bound`, with the
nodes in `|Re s| < X`, `y₀ < |Im s| ≤ ½` and every killed window value outside
`[-X, X] × ±[y₀, 1]`, the interpolation profile satisfies, for `|Re x| ≥ H`, `|Im x| ≤ ½`,
`|Φ(x)|² (1 + |Re x|)^{4N - 4n - 4} ≤ 4 (|Re p| + 1)⁴ (16e(H + 1)/δ)^{4n} K₁^{2N}`. -/
theorem norm_sq_interpProfile_far {V S Kw : Finset ℂ} {p x : ℂ} {N n : ℕ} {X y₀ δ H : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX0 : 0 < X) (hX : X ≤ 3 / 4) (hy0 : 0 < y₀) (hy : y₀ ≤ 1 / 2)
    (hH : 2 ≤ H) (hVSK : V = S ∪ Kw) (hdisj : Disjoint S Kw) (hKc : ∀ r ∈ Kw, conj r ∈ Kw)
    (hS : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2)
    (hK : ∀ r ∈ Kw, X < |r.re| ∨ |r.im| < y₀)
    (hVb : ∀ v ∈ V, |v.re| ≤ H ∧ |v.im| ≤ 1 / 2)
    (hp : H + 2 ≤ |p.re|) (hpim : |p.im| ≤ 1 / 2) (hcard : V.card ≤ n) (hNn : 2 * n + 2 ≤ N)
    (hside : ∀ t : ℂ, ((|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
        (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1))) →
        (δ / 4 / (2 * Real.exp 1)) ^ V.card ≤ ∏ v ∈ V, ‖t - v‖)
    (hx : H ≤ |x.re|) (hxi : |x.im| ≤ 1 / 2) :
    ‖interpProfile (insert p Kw) S N x‖ ^ 2 * (1 + |x.re|) ^ (4 * N - 4 * n - 4) ≤
      4 * (|p.re| + 1) ^ 4 * ((H + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) *
        unitDecayRatio ^ (2 * N) := by
  set K := insert p Kw with hKdef
  set κ := δ / (16 * Real.exp 1) with hκ
  have hκ0 : 0 < κ := by positivity
  set D := 1 + |x.re| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg x.re]
  have hD0 : 0 < D := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hKmem : ∀ r ∈ K, X < |r.re| ∨ |r.im| < y₀ ∨ 1 < |r.im| := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · left; linarith
    · rcases hK r hr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hSmem : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| < 1 := fun s hs =>
    ⟨(hS s hs).1, (hS s hs).2.1, by linarith [(hS s hs).2.2]⟩
  have hborder : ∀ t : ℂ, (|t.re| = X ∧ y₀ ≤ |t.im| ∧ |t.im| ≤ 1) ∨
      (|t.re| ≤ X ∧ (|t.im| = y₀ ∨ |t.im| = 1)) →
      κ ^ (2 * n) ≤ ‖(killPoly K).eval t‖ * ‖eval t (nodal S id)‖ := by
    intro t ht
    exact border_lower_bound hδ hδ1 hX (by linarith) hH0 hVSK hdisj hKc
      (fun s hs => ⟨(hS s hs).1, (hS s hs).2.2⟩) (fun v hv => (hVb v hv).1) hp hcard hside t ht
  -- the numerator
  have hpK : p ∉ Kw := by
    intro h
    have := (hVb p (by rw [hVSK]; exact Finset.mem_union_right _ h)).1
    linarith
  have hnear : ∀ v ∈ V, ‖x - v‖ ≤ (H + 1) * D := by
    intro v hv
    have h1 := Complex.norm_le_abs_re_add_abs_im (x - v)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub x.re v.re
    have h3 := abs_sub x.im v.im
    have := hVb v hv
    nlinarith [abs_nonneg x.re]
  have hpolar : ∀ q : ℂ, |q.re| = |p.re| → |q.im| ≤ 1 / 2 → ‖x - q‖ ≤ (|p.re| + 1) * D := by
    intro q hq hqi
    have h1 := Complex.norm_le_abs_re_add_abs_im (x - q)
    rw [Complex.sub_re, Complex.sub_im] at h1
    have h2 := abs_sub x.re q.re
    have h3 := abs_sub x.im q.im
    nlinarith [abs_nonneg x.re, abs_nonneg p.re]
  have hB1 : 1 ≤ (H + 1) * D := by nlinarith
  have hKV : ∀ r ∈ Kw, r ∈ V := fun r hr => by rw [hVSK]; exact Finset.mem_union_right _ hr
  have hSV : ∀ s ∈ S, s ∈ V := fun s hs => by rw [hVSK]; exact Finset.mem_union_left _ hs
  have hcard' : Kw.card + S.card ≤ n := by
    have := Finset.card_union_of_disjoint hdisj
    rw [← hVSK] at this
    omega
  have hPw := killPoly_nodal_le (S := S) (Kw := Kw) (x := x) hB1
    (fun r hr => ⟨hnear r (hKV r hr), hnear _ (hKV _ (hKc r hr))⟩) (fun s hs => hnear s (hSV s hs))
    hcard'
  have hPins : ‖(killPoly K).eval x‖ = ‖x - p‖ * ‖x - conj p‖ * ‖(killPoly Kw).eval x‖ := by
    rw [hKdef, norm_eval_killPoly, norm_eval_killPoly, Finset.prod_insert hpK]
  have hxp := hpolar p rfl hpim
  have hxp' := hpolar (conj p) (by rw [Complex.conj_re])
    (by rw [Complex.conj_im, abs_neg]; exact hpim)
  set M := ((|p.re| + 1) * D) ^ 2 * ((H + 1) * D) ^ (2 * n) with hM
  have hMb : ‖(killPoly K).eval x‖ * ‖eval x (nodal S id)‖ ≤ M := by
    rw [hPins, hM, mul_assoc, sq]
    have h0 : 0 ≤ ‖(killPoly Kw).eval x‖ * ‖eval x (nodal S id)‖ := by positivity
    calc ‖x - p‖ * ‖x - conj p‖ * (‖(killPoly Kw).eval x‖ * ‖eval x (nodal S id)‖)
        ≤ ((|p.re| + 1) * D) * ((|p.re| + 1) * D) * ((H + 1) * D) ^ (2 * n) := by
          gcongr
      _ = _ := by ring
  have hx' : X + 1 ≤ |x.re| := by linarith
  have hΦ := norm_interpProfile_le (K := K) (S := S) (N := N) (X := X) (y₀ := y₀)
    (lam := κ ^ (2 * n)) (M := M) hX0 hX hy0 hy hSmem hKmem hx' (pow_pos hκ0 _) hborder hMb
  have hc := unitHatFloor_pos
  have hK₁ := unitDecayRatio_pos
  have hWN : (‖unitHat x‖ / unitHatFloor) ^ N ≤ (unitDecayRatio / D ^ 2) ^ N :=
    pow_le_pow_left₀ (by positivity) (norm_unitHat_div_le hxi) N
  set A := 2 * (|p.re| + 1) ^ 2 * ((H + 1) / κ) ^ (2 * n) * unitDecayRatio ^ N with hA
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hstep : ‖interpProfile K S N x‖ * D ^ (2 * N) ≤ A * D ^ (2 * n + 2) := by
    have h1 : ‖interpProfile K S N x‖ ≤ 2 * (M / κ ^ (2 * n) * (unitDecayRatio / D ^ 2) ^ N) :=
      hΦ.trans (by gcongr)
    have e : 2 * (M / κ ^ (2 * n) * (unitDecayRatio / D ^ 2) ^ N) * D ^ (2 * N) =
        A * D ^ (2 * n + 2) := by
      rw [hM, hA]
      exact interp_tail_identity _ _ _ _ _ n N hκ0.ne' hD0.ne'
    calc ‖interpProfile K S N x‖ * D ^ (2 * N)
        ≤ 2 * (M / κ ^ (2 * n) * (unitDecayRatio / D ^ 2) ^ N) * D ^ (2 * N) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = A * D ^ (2 * n + 2) := e
  have hsq : ‖interpProfile K S N x‖ ^ 2 * D ^ (4 * N) ≤ A ^ 2 * D ^ (4 * n + 4) := by
    have := pow_le_pow_left₀ (by positivity) hstep 2
    calc ‖interpProfile K S N x‖ ^ 2 * D ^ (4 * N)
        = (‖interpProfile K S N x‖ * D ^ (2 * N)) ^ 2 := by ring
      _ ≤ (A * D ^ (2 * n + 2)) ^ 2 := this
      _ = A ^ 2 * D ^ (4 * n + 4) := by ring
  have hsplit : D ^ (4 * N) = D ^ (4 * N - 4 * n - 4) * D ^ (4 * n + 4) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← mul_assoc] at hsq
  have hfin := le_of_mul_le_mul_right hsq (by positivity)
  refine hfin.trans (le_of_eq ?_)
  rw [hA, hκ]
  have he : (H + 1) / (δ / (16 * Real.exp 1)) = (H + 1) * (16 * Real.exp 1) / δ := by
    field_simp
  rw [he]
  ring

/-! ### The exclusion theorem -/

theorem reflect_re' (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re := by
  simp [Zeta23.reflect]

theorem reflect_im' (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im := by
  simp [Zeta23.reflect]

/-- **Summation.**  Let `Φ` be the profile of a real test at the window coordinates, with Weil
summand `m_ρ Φ(ρ)²/q²`.  If `Φ² = -1` or `Φ = 0` at the window zeros, `Φ² = -1` at `ρ₀` and at
its reflection, and `|Φ|² (1 + |γ - γ₀|)^{3+E} ≤ C₁` at the zeros outside the window, then
`C₁ · 24 A₀ log(|γ₀| + 3) < 2 (1 + H)^E` forces `Re W < 0`. -/
theorem re_W_neg_of_window_profile (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {H : ℝ} (hH : 0 < H) {Wn : Finset ℂ}
    (hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ ρ₀.im - H < ρ.im ∧ ρ.im ≤ ρ₀.im + H)
    (hρ₀W : ρ₀ ∈ Wn) {f : ℝ → ℂ} {Φ : ℂ → ℂ} {q : ℝ} (hq : q ≠ 0)
    (hre_s : ∀ ρ : ℂ, (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * (Φ ρ ^ 2).re / q ^ 2)
    (hnorm_s : ∀ ρ : ℂ, ‖Z.Wsummand f f ρ‖ = (Z.mult ρ : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2)
    (hwin_norm : ∀ ρ ∈ Wn, ‖Φ ρ‖ ^ 2 ≤ 1) (hwin_re : ∀ ρ ∈ Wn, (Φ ρ ^ 2).re ≤ 0)
    {C₁ : ℝ} {E : ℕ} (hC₁0 : 0 ≤ C₁)
    (hfar : ∀ ρ ∈ Z.carrier, ρ ∉ Wn →
      H ≤ |ρ.im - ρ₀.im| ∧ ‖Φ ρ‖ ^ 2 * (1 + |ρ.im - ρ₀.im|) ^ (3 + E) ≤ C₁)
    (hΦ₀ : Φ ρ₀ ^ 2 = -1) (hΦ₁ : Φ (Zeta23.reflect ρ₀) ^ 2 = -1)
    (hbig : C₁ * (24 * A₀ * Real.log (|ρ₀.im| + 3)) < 2 * (1 + H) ^ E) :
    (Z.W f f).re < 0 := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₀
  have hH1 : 0 < 1 + H := by linarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hρ₁W : Zeta23.reflect ρ₀ ∈ Wn :=
    (hWn _).mpr ⟨Z.reflect_mem ρ₀ hρ₀, by rw [reflect_im']; linarith,
      by rw [reflect_im']; linarith⟩
  have hbound : ∀ ρ : Z.carrier, ‖Z.Wsummand f f ρ‖ ≤
      (C₁ + (1 + H) ^ 3) / q ^ 2 * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
    intro ρ
    rw [hnorm_s]
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    obtain ⟨D, hD⟩ : ∃ D, D = 1 + |(ρ : ℂ).im - γ₀| := ⟨_, rfl⟩
    rw [← hD]
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - γ₀)]
    have hD3 : 0 < D ^ 3 := by positivity
    have key : ‖Φ ρ‖ ^ 2 ≤ (C₁ + (1 + H) ^ 3) / D ^ 3 := by
      rw [le_div_iff₀ hD3]
      by_cases hW : (ρ : ℂ) ∈ Wn
      · obtain ⟨-, h1, h2⟩ := (hWn _).mp hW
        have hDH : D ≤ 1 + H := by
          have := abs_le.mpr (⟨by linarith, by linarith⟩ : -H ≤ (ρ : ℂ).im - γ₀ ∧
            (ρ : ℂ).im - γ₀ ≤ H)
          rw [hD]; linarith
        have h3 := hwin_norm _ hW
        have h4 : D ^ 3 ≤ (1 + H) ^ 3 := pow_le_pow_left₀ (by linarith) hDH 3
        calc ‖Φ ρ‖ ^ 2 * D ^ 3 ≤ 1 * (1 + H) ^ 3 :=
              mul_le_mul h3 h4 (by positivity) zero_le_one
          _ ≤ C₁ + (1 + H) ^ 3 := by linarith
      · obtain ⟨-, hb⟩ := hfar _ ρ.2 hW
        rw [← hD] at hb
        have : ‖Φ ρ‖ ^ 2 * D ^ 3 ≤ ‖Φ ρ‖ ^ 2 * D ^ (3 + E) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 (by omega)) (by positivity)
        have : (0 : ℝ) ≤ (1 + H) ^ 3 := by positivity
        linarith
    calc (Z.mult (ρ : ℂ) : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2
        ≤ (Z.mult (ρ : ℂ) : ℝ) * ((C₁ + (1 + H) ^ 3) / D ^ 3) / q ^ 2 := by gcongr
      _ = _ := by ring
  have hsum := Summable.of_norm_bounded (hwsum.mul_left ((C₁ + (1 + H) ^ 3) / q ^ 2)) hbound
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = C₁ / q ^ 2 / (1 + H) ^ E := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (div_nonneg hC₁0 hq2.le) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : Z.carrier → ℝ, ∀ ρ, T ρ = if (ρ : ℂ) ∈ Wn then 0 else
      c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
    ⟨fun ρ => if (ρ : ℂ) ∈ Wn then 0 else c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3),
      fun ρ => rfl⟩
  have hunit : ∀ ρ : Z.carrier, 0 ≤ (Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hTle : ∀ ρ, T ρ ≤ c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
    intro ρ
    rw [hT]
    split_ifs
    · exact mul_nonneg hc0 (hunit ρ)
    · exact le_rfl
  have hT0 : ∀ ρ, 0 ≤ T ρ := by
    intro ρ
    rw [hT]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hc0 (hunit ρ)
  have hTsum : Summable T := Summable.of_nonneg_of_le hT0 hTle (hwsum.mul_left _)
  set ρ₀ₛ : Z.carrier := ⟨ρ₀, hρ₀⟩ with hρ₀ₛ
  set ρ₁ₛ : Z.carrier := ⟨Zeta23.reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ with hρ₁ₛ
  have hne : ρ₁ₛ ≠ ρ₀ₛ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [hρ₀ₛ, hρ₁ₛ, reflect_re', hre] at this
    linarith
  have hm₀ : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hdeep : ∀ ρ' : ℂ, Φ ρ' ^ 2 = -1 → (1 : ℝ) ≤ Z.mult ρ' →
      (Z.mult ρ' : ℝ) * (Φ ρ' ^ 2).re / q ^ 2 ≤ -(1 / q ^ 2) := by
    intro ρ' h hm
    rw [h, Complex.neg_re, Complex.one_re, mul_neg, mul_one, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right hm hq2.le)
  have hpt : ∀ ρ : Z.carrier, (Z.Wsummand f f ρ).re ≤
      (if ρ = ρ₀ₛ then -(1 / q ^ 2) else 0) + (if ρ = ρ₁ₛ then -(1 / q ^ 2) else 0) + T ρ := by
    intro ρ
    rw [hre_s]
    by_cases h0 : ρ = ρ₀ₛ
    · have h1 : ρ ≠ ρ₁ₛ := fun h => hne (h ▸ h0)
      rw [if_pos h0, if_neg h1]
      have hTz : T ρ = 0 := by rw [hT, h0]; exact if_pos hρ₀W
      rw [hTz, h0, add_zero, add_zero]
      exact hdeep ρ₀ hΦ₀ hm₀
    by_cases h1 : ρ = ρ₁ₛ
    · rw [if_neg h0, if_pos h1]
      have hTz : T ρ = 0 := by rw [hT, h1]; exact if_pos hρ₁W
      rw [hTz, h1, zero_add, add_zero]
      exact hdeep _ hΦ₁ (by rw [Z.mult_reflect ρ₀ hρ₀]; exact hm₀)
    rw [if_neg h0, if_neg h1, zero_add, zero_add]
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    by_cases hW : (ρ : ℂ) ∈ Wn
    · have hTz : T ρ = 0 := by rw [hT]; exact if_pos hW
      rw [hTz]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hm (hwin_re _ hW))
        hq2.le
    · have hTv : T ρ = c * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) := by
        rw [hT]; exact if_neg hW
      rw [hTv, hc]
      obtain ⟨hfarH, hb⟩ := hfar _ ρ.2 hW
      obtain ⟨D, hD⟩ : ∃ D, D = 1 + |(ρ : ℂ).im - γ₀| := ⟨_, rfl⟩
      rw [← hD] at hb ⊢
      have hD1 : 1 + H ≤ D := by rw [hD]; linarith
      have hD0 : 0 < D := by linarith
      have hDE : (1 + H) ^ E * D ^ 3 ≤ D ^ (3 + E) := by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH1.le hD1 E) (by positivity)
      have hF : ‖Φ ρ‖ ^ 2 ≤ C₁ / ((1 + H) ^ E * D ^ 3) := by
        rw [le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left hDE (by positivity)).trans hb
      have hre_le : (Φ ρ ^ 2).re ≤ ‖Φ ρ‖ ^ 2 := by
        rw [← norm_pow]; exact Complex.re_le_norm _
      calc (Z.mult (ρ : ℂ) : ℝ) * (Φ ρ ^ 2).re / q ^ 2
          ≤ (Z.mult (ρ : ℂ) : ℝ) * (C₁ / ((1 + H) ^ E * D ^ 3)) / q ^ 2 := by
            gcongr; exact hre_le.trans hF
        _ = _ := by field_simp
  have hW := re_W_le_of_pointwise Z f hsum ρ₀ₛ ρ₁ₛ (1 / q ^ 2) hTsum hpt
  have hTle' : ∑' ρ, T ρ ≤ c * (24 * A₀ * Real.log (|γ₀| + 3)) := by
    calc ∑' ρ, T ρ ≤ ∑' ρ : Z.carrier, c *
          ((Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) :=
          Summable.tsum_le_tsum hTle hTsum (hwsum.mul_left _)
      _ = c * ∑' ρ : Z.carrier, (Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 :=
          tsum_mul_left
      _ ≤ c * (24 * A₀ * Real.log (|γ₀| + 3)) := mul_le_mul_of_nonneg_left hwle hc0
  have hHE : 0 < (1 + H) ^ E := by positivity
  have hkey : c * (24 * A₀ * Real.log (|γ₀| + 3)) < 2 * (1 / q ^ 2) := by
    rw [hc, div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    calc C₁ * (24 * A₀ * Real.log (|γ₀| + 3)) < 2 * (1 + H) ^ E := hbig
      _ = 2 * (1 / q ^ 2) * (q ^ 2 * (1 + H) ^ E) := by field_simp
  linarith

/-- **Sub-Nyquist Hodge exclusion.**  Let `Z` be a zero configuration with local count
`N(t, t+1] ≤ A₀ log(|t| + 3)` and `ρ₀ = ½ + δ + iγ₀` a zero with `δ > 0` and `|γ₀| ≥ H + 2`,
`H ≥ 2`.  If the window `γ₀ - H < Im ρ ≤ γ₀ + H` holds at most `n` distinct zeros,
`2n + 2 ≤ N ≤ a`, and
`48 A₀ log(|γ₀| + 3) (|γ₀| + 1)⁴ (16e(H + 1)/δ)^{4n} K₁^{2N} < (1 + H)^{4N - 4n - 7}`,
`K₁ = 168 e^{1/2}/(cos 1 · w₁)`, then the level-`a` Hodge index fails.

The test has transform `Ŵ(z - γ₀)^N Q(z - γ₀)/lc(Q)`, where `Q = P·p` with `P` vanishing at the
killed window values and at the polar point, and `p` the Lagrange interpolant of `±i/(P Ŵ^N)` at
the nodes, the window values in `[-X, X] × ±(y₀, 1)`.  Every node contributes `-m_ρ/lc(Q)²`,
every killed value `0`.  The contour `X`, `y₀` is chosen by forward differences so that
`|P ω| ≥ (δ/(16e))^{2n}` on it, and the contour formula for the interpolant bounds the zeros
outside the window with a loss `(16e(H + 1)/δ)^{4n}`, with no dependence on how the window zeros
cluster. -/
theorem exists_hodge_violation_subNyquist (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {H a : ℝ} (hH : 2 ≤ H) (hγ : H + 2 ≤ |ρ₀.im|) {N n : ℕ} (hNa : (N : ℝ) ≤ a)
    (hn : (Z.finite_window (ρ₀.im - H) (ρ₀.im + H)).toFinset.card ≤ n) (hNn : 2 * n + 2 ≤ N)
    (hbig : 48 * A₀ * Real.log (|ρ₀.im| + 3) * (|ρ₀.im| + 1) ^ 4 *
        ((H + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) * unitDecayRatio ^ (2 * N) <
      (1 + H) ^ (4 * N - 4 * n - 7)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  set γ₀ := ρ₀.im with hγ₀
  have hst := Z.strip ρ₀ hρ₀
  have hδ2 : δ ≤ 1 / 2 := by linarith [hst.2]
  have hH0 : 0 ≤ H := by linarith
  set Wn := (Z.finite_window (γ₀ - H) (γ₀ + H)).toFinset with hWndef
  have hWn : ∀ ρ, ρ ∈ Wn ↔ ρ ∈ Z.carrier ∧ γ₀ - H < ρ.im ∧ ρ.im ≤ γ₀ + H := by
    intro ρ; rw [hWndef, Set.Finite.mem_toFinset]; rfl
  -- window coordinates
  have hξre : ∀ ρ : ℂ, (gammaOf ρ - γ₀).re = ρ.im - γ₀ := fun ρ => by
    simp [WeilEF.gammaOf_re]
  have hξim : ∀ ρ : ℂ, (gammaOf ρ - γ₀).im = 1 / 2 - ρ.re := fun ρ => by
    simp [WeilEF.gammaOf_im]
  have hξrefl : ∀ ρ : ℂ, gammaOf (Zeta23.reflect ρ) - γ₀ = conj (gammaOf ρ - γ₀) := by
    intro ρ
    apply Complex.ext
    · rw [hξre, Complex.conj_re, hξre, reflect_im']
    · rw [hξim, Complex.conj_im, hξim, reflect_re']; ring
  set V := Wn.image (fun ρ => gammaOf ρ - γ₀) with hV
  have hVmem : ∀ v, v ∈ V ↔ ∃ ρ ∈ Wn, gammaOf ρ - γ₀ = v := fun v => by
    rw [hV, Finset.mem_image]
  have hVc : ∀ v ∈ V, conj v ∈ V := by
    intro v hv
    obtain ⟨ρ, hρ, rfl⟩ := (hVmem v).mp hv
    obtain ⟨hρZ, h1, h2⟩ := (hWn ρ).mp hρ
    refine (hVmem _).mpr ⟨Zeta23.reflect ρ, (hWn _).mpr ⟨Z.reflect_mem ρ hρZ, ?_, ?_⟩, hξrefl ρ⟩
    · rw [reflect_im']; exact h1
    · rw [reflect_im']; exact h2
  have hVb : ∀ v ∈ V, |v.re| ≤ H ∧ |v.im| ≤ 1 / 2 := by
    intro v hv
    obtain ⟨ρ, hρ, rfl⟩ := (hVmem v).mp hv
    obtain ⟨hρZ, h1, h2⟩ := (hWn ρ).mp hρ
    have hs := Z.strip ρ hρZ
    rw [hξre, hξim]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hVcard : V.card ≤ n := Finset.card_image_le.trans hn
  have hρ₀W : ρ₀ ∈ Wn := (hWn ρ₀).mpr ⟨hρ₀, by linarith, by linarith⟩
  have hx₀ : gammaOf ρ₀ - γ₀ = -(I * δ) :=
    (gammaOf_sub_of_re_im (ρ := ρ₀) (γ₀ := γ₀) rfl hre).1
  have hx₀V : -(I * (δ : ℂ)) ∈ V := (hVmem _).mpr ⟨ρ₀, hρ₀W, hx₀⟩
  -- the contour
  obtain ⟨X, y₀, hX1, hX2, hy1, hy2, hVne, hside⟩ :=
    subNyquist_selection (V := V) hδ (by linarith) (fun v hv => (hVb v hv).2)
  have hX0 : 0 < X := by linarith
  have hy0 : 0 < y₀ := by linarith
  set S := V.filter (fun v => |v.re| < X ∧ y₀ < |v.im|) with hSdef
  set Kw := V.filter (fun v => ¬ (|v.re| < X ∧ y₀ < |v.im|)) with hKwdef
  have hVSK : V = S ∪ Kw := (Finset.filter_union_filter_not_eq _ V).symm
  have hdisj : Disjoint S Kw := Finset.disjoint_filter_filter_not V V _
  have hconjabs : ∀ v : ℂ, |(conj v).re| = |v.re| ∧ |(conj v).im| = |v.im| := fun v => by
    rw [Complex.conj_re, Complex.conj_im, abs_neg]; exact ⟨rfl, rfl⟩
  have hKc : ∀ r ∈ Kw, conj r ∈ Kw := by
    intro r hr
    rw [hKwdef, Finset.mem_filter] at hr ⊢
    rw [(hconjabs r).1, (hconjabs r).2]
    exact ⟨hVc r hr.1, hr.2⟩
  have hSc : ∀ s ∈ S, conj s ∈ S := by
    intro s hs
    rw [hSdef, Finset.mem_filter] at hs ⊢
    rw [(hconjabs s).1, (hconjabs s).2]
    exact ⟨hVc s hs.1, hs.2⟩
  have hSg : ∀ s ∈ S, |s.re| < X ∧ y₀ < |s.im| ∧ |s.im| ≤ 1 / 2 := by
    intro s hs
    rw [hSdef, Finset.mem_filter] at hs
    exact ⟨hs.2.1, hs.2.2, (hVb s hs.1).2⟩
  have hKg : ∀ r ∈ Kw, X < |r.re| ∨ |r.im| < y₀ := by
    intro r hr
    rw [hKwdef, Finset.mem_filter] at hr
    obtain ⟨hne1, hne2⟩ := hVne r hr.1
    rw [not_and_or, not_lt, not_lt] at hr
    rcases hr.2 with h | h
    · exact Or.inl (lt_of_le_of_ne h (Ne.symm hne1))
    · exact Or.inr (lt_of_le_of_ne h hne2)
  have hSim : ∀ s ∈ S, s.im ≠ 0 := by
    intro s hs h
    have := (hSg s hs).2.1
    rw [h, abs_zero] at this
    linarith
  have hx₀S : -(I * (δ : ℂ)) ∈ S := by
    rw [hSdef, Finset.mem_filter]
    refine ⟨hx₀V, ?_, ?_⟩
    · simp; linarith
    · simp [abs_of_pos hδ]; linarith
  have hSne : S.Nonempty := ⟨_, hx₀S⟩
  -- the polar point
  set p : ℂ := ⟨-γ₀, 1 / 2⟩ with hpdef
  have hp : H + 2 ≤ |p.re| := by simp only [hpdef, abs_neg]; exact hγ
  have hpim : |p.im| ≤ 1 / 2 := by simp [hpdef]
  have hpK : p ∉ Kw := by
    intro h
    have := (hVb p (by rw [hVSK]; exact Finset.mem_union_right _ h)).1
    linarith
  set K := insert p Kw with hKdef
  set Q := interpQ K S N with hQdef
  have hKcard : K.card = Kw.card + 1 := Finset.card_insert_of_notMem hpK
  have hcardVS : S.card + Kw.card = V.card := by
    rw [hVSK, Finset.card_union_of_disjoint hdisj]
  -- the values at the window
  have hPs : ∀ s ∈ S, (killPoly K).eval s ≠ 0 := by
    intro s hs
    obtain ⟨h1, h2, -⟩ := hSg s hs
    have hfar : ∀ q : ℂ, (X < |q.re| ∨ |q.im| < y₀) → s ≠ q := by
      intro q hq hsq
      rw [← hsq] at hq
      rcases hq with h | h <;> linarith
    refine killPoly_eval_ne_zero fun r hr => ?_
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨hfar _ (Or.inl (by linarith)),
        hfar _ (Or.inl (by rw [(hconjabs _).1]; linarith))⟩
    · exact ⟨hfar r (hKg r hr), hfar _ (by rw [(hconjabs r).1, (hconjabs r).2]; exact hKg r hr)⟩
  have hWs' : ∀ s ∈ S, unitHat s ≠ 0 := fun s hs =>
    unitHat_ne_zero (by linarith [(hSg s hs).1])
  have hnodeval : ∀ s ∈ S, interpProfile K S N s = if s.im < 0 then I else -I :=
    fun s hs => interpProfile_node hs (hPs s hs) (hWs' s hs)
  have hnodesq : ∀ s ∈ S, interpProfile K S N s ^ 2 = -1 := by
    intro s hs
    rw [hnodeval s hs]
    split_ifs
    · rw [sq, Complex.I_mul_I]
    · rw [neg_sq, sq, Complex.I_mul_I]
  have hkill : ∀ r ∈ Kw, interpProfile K S N r = 0 :=
    fun r hr => (interpProfile_killed K S N (Finset.mem_insert_of_mem hr)).1
  have hQ0 : Q ≠ 0 := by
    intro h
    have hv := hnodeval _ hx₀S
    rw [interpProfile, ← hQdef, h, eval_zero, mul_zero] at hv
    have him : (-(I * (δ : ℂ))).im < 0 := by simp; linarith
    rw [if_pos him] at hv
    exact Complex.I_ne_zero hv.symm
  have hdeg : Q.natDegree + 1 ≤ N := by
    have : Q.natDegree < 2 * K.card + S.card := natDegree_interpQ_lt K S N hSne
    rw [hKcard] at this
    omega
  have hQreal := interpQ_real (K := K) (N := N) hSc hSim
  set ℓ := Q.leadingCoeff with hℓ
  have hℓ0 : ℓ ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hℓr : (ℓ.re : ℂ) = ℓ := Complex.conj_eq_iff_re.mp (hQreal Q.natDegree)
  set q := ℓ.re with hq
  have hq0 : q ≠ 0 := by
    intro h; apply hℓ0; rw [← hℓr, h, Complex.ofReal_zero]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0
  have hprof : ∀ x, polyProfile (sinhTestWeight 1) N Q x = interpProfile K S N x / ℓ := by
    intro x
    rw [polyProfile_eq _ N hQ0, interpProfile, ← hQdef, mul_div_assoc]
    rfl
  -- the test
  obtain ⟨hfc, hfs, hff⟩ := polyTest_props (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
    (sinhTestWeight_supp zero_le_one) γ₀ hdeg
  have hpolar : Q.eval p = 0 ∧ Q.eval (conj p) = 0 := by
    rw [hQdef, interpQ, eval_mul, eval_mul, eval_killPoly, eval_killPoly]
    constructor
    · rw [Finset.prod_eq_zero (Finset.mem_insert_self p Kw) (by ring), zero_mul]
    · rw [Finset.prod_eq_zero (Finset.mem_insert_self p Kw) (by rw [sub_self, mul_zero]),
        zero_mul]
  refine ⟨polyTest γ₀ (sinhTestWeight 1) N Q, hfc, ?_, ?_, ?_, ?_⟩
  · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have := hfs u hu
    linarith
  · refine polyTest_polar_zero (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) γ₀ hQ0 hdeg ?_
    have e : I / 2 - (γ₀ : ℂ) = p := by apply Complex.ext <;> simp [hpdef]
    rw [e]; exact hpolar.1
  · refine polyTest_polar_zero (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) γ₀ hQ0 hdeg ?_
    have e : -(I / 2) - (γ₀ : ℂ) = conj p := by apply Complex.ext <;> simp [hpdef]
    rw [e]; exact hpolar.2
  -- the Weil form
  set f := polyTest γ₀ (sinhTestWeight 1) N Q with hf
  set Φ : ℂ → ℂ := fun ρ => interpProfile K S N (gammaOf ρ - γ₀) with hΦ
  have hWs : ∀ ρ : ℂ, Z.Wsummand f f ρ = (Z.mult ρ : ℂ) * (Φ ρ / ℓ) ^ 2 := by
    intro ρ
    rw [hf, Wsummand_polyTest (sinhTestWeight_contDiff 1) (sinhTestWeight_even 1)
      (sinhTestWeight_supp zero_le_one) Z γ₀ hQ0 hQreal hdeg ρ, hprof]
  have hre_s : ∀ ρ : ℂ, (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * (Φ ρ ^ 2).re / q ^ 2 := by
    intro ρ
    have e : (Z.mult ρ : ℂ) * (Φ ρ / ℓ) ^ 2 = (((Z.mult ρ : ℝ) / q ^ 2 : ℝ) : ℂ) * Φ ρ ^ 2 := by
      rw [← hℓr]; push_cast; field_simp
    rw [hWs, e, Complex.re_ofReal_mul]; ring
  have hnorm_s : ∀ ρ : ℂ, ‖Z.Wsummand f f ρ‖ = (Z.mult ρ : ℝ) * ‖Φ ρ‖ ^ 2 / q ^ 2 := by
    intro ρ
    rw [hWs, ← hℓr, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, div_pow, sq_abs]
    ring
  have hq2 : 0 < q ^ 2 := by positivity
  -- window values: `Φ² = -1` at nodes, `Φ = 0` at killed values
  have hwin : ∀ ρ ∈ Wn, (Φ ρ ^ 2 = -1 ∨ Φ ρ = 0) := by
    intro ρ hρ
    have hv : gammaOf ρ - γ₀ ∈ V := (hVmem _).mpr ⟨ρ, hρ, rfl⟩
    rw [hVSK, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact Or.inl (hnodesq _ hv)
    · exact Or.inr (hkill _ hv)
  have hwin_norm : ∀ ρ ∈ Wn, ‖Φ ρ‖ ^ 2 ≤ 1 := by
    intro ρ hρ
    rcases hwin ρ hρ with h | h
    · rw [← norm_pow, h, norm_neg, norm_one]
    · rw [h, norm_zero]; norm_num
  have hwin_re : ∀ ρ ∈ Wn, (Φ ρ ^ 2).re ≤ 0 := by
    intro ρ hρ
    rcases hwin ρ hρ with h | h
    · rw [h]; norm_num
    · rw [h]; simp
  -- the far zeros
  set C₁ := 4 * (|γ₀| + 1) ^ 4 * ((H + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) *
    unitDecayRatio ^ (2 * N) with hC₁
  have hC₁0 : 0 ≤ C₁ := by have := unitDecayRatio_pos; rw [hC₁]; positivity
  have hfarρ : ∀ ρ ∈ Z.carrier, ρ ∉ Wn →
      H ≤ |ρ.im - γ₀| ∧ ‖Φ ρ‖ ^ 2 * (1 + |ρ.im - γ₀|) ^ (4 * N - 4 * n - 4) ≤ C₁ := by
    intro ρ hρZ hρW
    have hfarH : H ≤ |ρ.im - γ₀| := by
      have hnot : ¬ (γ₀ - H < ρ.im ∧ ρ.im ≤ γ₀ + H) := fun h => hρW ((hWn _).mpr ⟨hρZ, h⟩)
      rw [not_and_or, not_lt, not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    refine ⟨hfarH, ?_⟩
    have hs := Z.strip ρ hρZ
    have hxi : |(gammaOf ρ - γ₀).im| ≤ 1 / 2 := by
      rw [hξim]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hb := norm_sq_interpProfile_far (V := V) (S := S) (Kw := Kw) (p := p) (N := N) (n := n)
      hδ (by linarith) hX0 (by linarith) hy0 (by linarith) hH hVSK hdisj hKc hSg hKg hVb hp hpim
      hVcard hNn hside (x := gammaOf ρ - γ₀) (by rw [hξre]; exact hfarH) hxi
    rw [hξre] at hb
    have hpre : |p.re| = |γ₀| := by simp [hpdef]
    rw [hpre] at hb
    exact hb
  have hρ₁W : Zeta23.reflect ρ₀ ∈ Wn :=
    (hWn _).mpr ⟨Z.reflect_mem ρ₀ hρ₀, by rw [reflect_im']; linarith,
      by rw [reflect_im']; linarith⟩
  have hΦ₀ : Φ ρ₀ ^ 2 = -1 := by
    simp only [hΦ]; rw [hx₀]; exact hnodesq _ hx₀S
  have hΦ₁ : Φ (Zeta23.reflect ρ₀) ^ 2 = -1 := by
    simp only [hΦ]; rw [hξrefl, hx₀]; exact hnodesq _ (hSc _ hx₀S)
  have hE3 : 4 * N - 4 * n - 4 = 3 + (4 * N - 4 * n - 7) := by omega
  refine re_W_neg_of_window_profile Z hA₀ hloc hρ₀ (δ := δ) (by linarith) hre (by linarith) hWn
    hρ₀W (Φ := Φ) (q := q) hq0 hre_s hnorm_s hwin_norm hwin_re
    (C₁ := C₁) (E := 4 * N - 4 * n - 7) hC₁0 (fun ρ hρZ hρW => by
      obtain ⟨h1, h2⟩ := hfarρ ρ hρZ hρW
      rw [hE3] at h2
      exact ⟨h1, h2⟩) hΦ₀ hΦ₁ ?_
  rw [hC₁]
  nlinarith [hbig]

/-! ### The Nyquist horizon -/

theorem unitDecayRatio_le : unitDecayRatio ≤ 1400 := by
  have hcos : (1 : ℝ) / 2 ≤ Real.cos 1 := by
    have := Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ)); norm_num at this ⊢; linarith
  have hw := unitWeightFloor_ge
  have hc : (24 / 100 : ℝ) ≤ unitHatFloor := by
    unfold unitHatFloor
    nlinarith [unitWeightFloor_pos]
  have he := exp_one_half_lt_two
  unfold unitDecayRatio
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (1 / 2)]

theorem nyquist_numeric_bounds : (48 : ℝ) ≤ Real.exp 4 ∧ Real.exp 3 ≤ 49 ∧
    (101 : ℝ) ^ 2 * (16 * Real.exp 1) ≤ 10 ^ 6 ∧ Real.exp 10 ≤ 2 * 10 ^ 6 := by
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  have e : ∀ k : ℕ, Real.exp k = Real.exp 1 ^ k := fun k => by rw [← Real.exp_nat_mul, mul_one]
  have lo : ∀ k : ℕ, (2.7182818283 : ℝ) ^ k ≤ Real.exp k := fun k => by
    rw [e k]; exact pow_le_pow_left₀ (by norm_num) he.le k
  have hi : ∀ k : ℕ, Real.exp k ≤ (2.7182818286 : ℝ) ^ k := fun k => by
    rw [e k]; exact pow_le_pow_left₀ (Real.exp_pos 1).le he'.le k
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := lo 4; norm_num at this ⊢; linarith
  · have := hi 3; norm_num at this ⊢; linarith
  · nlinarith
  · have := hi 10; norm_num at this ⊢; linarith

/-- **The size condition at level `a`.**  If
`4((n + 1) log(10⁶/δ) + log(A₀(|γ| + 3))) ≤ a`, then `N = ⌊a⌋` satisfies `2n + 2 ≤ N` and the
condition of `exists_hodge_violation_subNyquist` with window half-width `100`. -/
theorem nyquist_horizon_condition {A₀ δ a γ : ℝ} {n : ℕ} (hA₀ : 1 ≤ A₀) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2)
    (hsize : 4 * ((n + 1) * Real.log (10 ^ 6 / δ) + Real.log (A₀ * (|γ| + 3))) ≤ a) :
    2 * n + 2 ≤ ⌊a⌋₊ ∧
      48 * A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 *
        ((100 + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) * unitDecayRatio ^ (2 * ⌊a⌋₊) <
      (1 + 100) ^ (4 * ⌊a⌋₊ - 4 * n - 7) := by
  obtain ⟨h48, h49, h101, h10⟩ := nyquist_numeric_bounds
  have h5 := exp_numeric_bounds.1
  set Λ := Real.log (10 ^ 6 / δ) with hΛ
  set G := Real.log (A₀ * (|γ| + 3)) with hG
  set N := ⌊a⌋₊ with hNdef
  have hγ3 : 3 ≤ |γ| + 3 := by linarith [abs_nonneg γ]
  have hΛ10 : 10 ≤ Λ := by
    have h : Real.exp 10 ≤ 10 ^ 6 / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    have := Real.log_le_log (Real.exp_pos 10) h
    rwa [Real.log_exp] at this
  have hG0 : 0 ≤ G := Real.log_nonneg (by nlinarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 4 * ((n + 1) * Λ + G) ≤ a := hsize
  have ha0 : 0 ≤ a := by nlinarith
  have hN : a - 1 < N := by
    have := Nat.lt_floor_add_one a
    rw [← hNdef] at this
    linarith
  have hNn : 2 * n + 2 ≤ N := by
    have : ((2 * n + 2 : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast this
  refine ⟨hNn, ?_⟩
  have hcore : 39 + 5 * G + 4 * n * Λ < 3 * N := by nlinarith
  -- the factors
  set K₁ := unitDecayRatio with hK₁
  have hK₁0 := unitDecayRatio_pos
  have hK₁le := unitDecayRatio_le
  have hL0 : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith)
  have hLle : Real.log (|γ| + 3) ≤ |γ| + 3 := by
    have := Real.log_le_sub_one_of_pos (show 0 < |γ| + 3 by linarith); linarith
  have hexpG : Real.exp G = A₀ * (|γ| + 3) := Real.exp_log (by positivity)
  have hexpΛ : Real.exp Λ = 10 ^ 6 / δ := Real.exp_log (by positivity)
  have hb : A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 ≤ Real.exp (5 * G) := by
    have h1 : A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 ≤ (A₀ * (|γ| + 3)) * (|γ| + 3) ^ 4 := by
      have : (|γ| + 1) ^ 4 ≤ (|γ| + 3) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have hA0 : 0 ≤ A₀ := by linarith
      calc A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 ≤ A₀ * (|γ| + 3) * (|γ| + 3) ^ 4 := by
            gcongr
        _ = _ := by ring
    have h2 : (|γ| + 3) ^ 4 ≤ (A₀ * (|γ| + 3)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 4
    calc A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 ≤ (A₀ * (|γ| + 3)) * (|γ| + 3) ^ 4 := h1
      _ ≤ (A₀ * (|γ| + 3)) * (A₀ * (|γ| + 3)) ^ 4 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp G ^ 5 := by rw [hexpG]; ring
      _ = Real.exp (5 * G) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : ((100 + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) * (101 : ℝ) ^ (4 * n) ≤
      Real.exp (4 * n * Λ) := by
    rw [← mul_pow]
    have : (100 + 1) * (16 * Real.exp 1) / δ * 101 ≤ 10 ^ 6 / δ := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hδ.le
      nlinarith
    calc ((100 + 1) * (16 * Real.exp 1) / δ * 101) ^ (4 * n) ≤ (10 ^ 6 / δ) ^ (4 * n) :=
          pow_le_pow_left₀ (by positivity) this _
      _ = Real.exp Λ ^ (4 * n) := by rw [hexpΛ]
      _ = Real.exp (4 * n * Λ) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hd : (101 : ℝ) ^ 7 ≤ Real.exp 35 := by
    calc (101 : ℝ) ^ 7 ≤ Real.exp 5 ^ 7 := pow_le_pow_left₀ (by norm_num) h5 7
      _ = Real.exp 35 := by rw [← Real.exp_nat_mul]; norm_num
  have he : K₁ ^ (2 * N) ≤ (1400 : ℝ) ^ (2 * N) := pow_le_pow_left₀ hK₁0.le hK₁le _
  have hf : Real.exp (3 * N) ≤ (49 : ℝ) ^ N := by
    rw [show (3 : ℝ) * N = N * 3 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 3).le h49 N
  have hg : (49 : ℝ) ^ N * (1400 : ℝ) ^ (2 * N) ≤ (101 : ℝ) ^ (4 * N) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) N
  -- assemble
  have hP : (0 : ℝ) < 101 ^ (4 * n + 7) := by positivity
  have hRHS : ((1 : ℝ) + 100) ^ (4 * N - 4 * n - 7) * 101 ^ (4 * n + 7) = 101 ^ (4 * N) := by
    rw [show (1 : ℝ) + 100 = 101 by norm_num, ← pow_add]
    congr 1; omega
  rw [← mul_lt_mul_iff_of_pos_right hP, hRHS]
  have hA0 : 0 ≤ A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 := by
    have : 0 ≤ A₀ := by linarith
    positivity
  calc 48 * A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4 *
        ((100 + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) * K₁ ^ (2 * N) * 101 ^ (4 * n + 7)
      = 48 * (A₀ * Real.log (|γ| + 3) * (|γ| + 1) ^ 4) *
          (((100 + 1) * (16 * Real.exp 1) / δ) ^ (4 * n) * (101 : ℝ) ^ (4 * n)) *
          (101 : ℝ) ^ 7 * K₁ ^ (2 * N) := by rw [pow_add]; ring
    _ ≤ Real.exp 4 * Real.exp (5 * G) * Real.exp (4 * n * Λ) * Real.exp 35 *
          (1400 : ℝ) ^ (2 * N) := by gcongr
    _ = Real.exp (39 + 5 * G + 4 * n * Λ) * (1400 : ℝ) ^ (2 * N) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ < Real.exp (3 * N) * (1400 : ℝ) ^ (2 * N) := by
          gcongr
    _ ≤ (49 : ℝ) ^ N * (1400 : ℝ) ^ (2 * N) := by gcongr
    _ ≤ 101 ^ (4 * N) := hg

/-- **Hodge index below the Nyquist horizon.**  Let `Z` have local count
`N(t, t+1] ≤ A₀ log(|t| + 3)` and let `ρ₀` be a zero with `|β₀ - ½| ≥ δ > 0` and `|γ₀| ≥ 102`.
If at most `n` distinct zeros satisfy `γ₀ - 100 < γ ≤ γ₀ + 100`, and
`4((n + 1) log(10⁶/δ) + log(A₀(|γ₀| + 3))) ≤ a`, then the level-`a` Hodge index fails.

The level is linear in the window count, with no power of `log a`: by
`not_forall_hodge_exclusion_sublinear_level` no bound `n ≤ c·a` with `c ≥ 2000` forces a
violation, so the linear dependence on `n` is sharp up to the constant and the factor
`log(10⁶/δ)`. -/
theorem not_hodgeIndex_below_nyquist_horizon (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : δ ≤ |ρ₀.re - 1 / 2|)
    (hγ : 102 ≤ |ρ₀.im|) {n : ℕ} (hn : Z.Nd (ρ₀.im - 100) (ρ₀.im + 100) ≤ n) {a : ℝ}
    (hsize : 4 * ((n + 1) * Real.log (10 ^ 6 / δ) + Real.log (A₀ * (|ρ₀.im| + 3))) ≤ a) :
    ¬ HodgeIndexAtLevel Z a := by
  intro hodge
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ Z.carrier, σ.re = 1 / 2 + |ρ₀.re - 1 / 2| ∧
      σ.im = ρ₀.im := by
    rcases le_or_gt (1 / 2) ρ₀.re with h | h
    · exact ⟨ρ₀, hρ₀, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
    · refine ⟨Zeta23.reflect ρ₀, Z.reflect_mem ρ₀ hρ₀, ?_, reflect_im' ρ₀⟩
      rw [abs_of_neg (by linarith), reflect_re']; ring
  set δ' := |ρ₀.re - 1 / 2| with hδ'
  have hδ'0 : 0 < δ' := lt_of_lt_of_le hδ hre
  have hst := Z.strip σ hσ
  have hδ'2 : δ' ≤ 1 / 2 := by linarith [hst.2]
  have hΛ : Real.log (10 ^ 6 / δ') ≤ Real.log (10 ^ 6 / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hδ hre)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsize' : 4 * ((n + 1) * Real.log (10 ^ 6 / δ') + Real.log (A₀ * (|σ.im| + 3))) ≤ a := by
    rw [hσim]
    have : (n + 1 : ℝ) * Real.log (10 ^ 6 / δ') ≤ (n + 1) * Real.log (10 ^ 6 / δ) :=
      mul_le_mul_of_nonneg_left hΛ (by linarith)
    linarith
  obtain ⟨hNn, hbig⟩ := nyquist_horizon_condition hA₀ hδ'0 hδ'2 hsize'
  have ha0 : 0 ≤ a := by
    have hG : 0 ≤ Real.log (A₀ * (|σ.im| + 3)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg σ.im])
    have hL : 0 ≤ Real.log (10 ^ 6 / δ') :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ'0]; linarith)
    nlinarith
  have hn' : (Z.finite_window (σ.im - 100) (σ.im + 100)).toFinset.card ≤ n := by
    have e : (Z.finite_window (σ.im - 100) (σ.im + 100)).toFinset.card =
        Z.Nd (σ.im - 100) (σ.im + 100) :=
      (Set.ncard_eq_toFinset_card (Z.window _ _) (Z.finite_window _ _)).symm
    rw [e, hσim]
    exact hn
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := exists_hodge_violation_subNyquist Z hA₀ hloc hσ hδ'0
    hσre (H := 100) (by norm_num) (by rw [hσim]; linarith) (Nat.floor_le ha0) hn' hNn hbig
  exact absurd (hodge f hf hfs hp hm) (not_le.mpr hneg)

/-- **The Nyquist horizon for `ζ`.**  There is `A₀` such that for every `δ > 0`, every zero `ρ`
of `ζ` with `|β - ½| ≥ δ` and `|γ| ≥ 102`, and every level
`a ≥ 2000 A₀ log(|γ| + 3) log(10⁶/δ)`, the level-`a` Hodge index fails.  Equivalently, the Hodge
index at level `a` excludes zeros of depth `δ` up to height `exp(a/(2000 A₀ log(10⁶/δ))) - 3`. -/
theorem zeta_hodge_index_nyquist_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.re - 1 / 2| →
      102 ≤ |ρ.im| → ∀ a : ℝ, 2000 * A₀ * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / δ) ≤ a →
        ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun δ hδ ρ hρ hre hγ a hsize => ?_⟩
  set L := Real.log (|ρ.im| + 3) with hL
  set Λ := Real.log (10 ^ 6 / δ) with hΛ
  have hst := zetaZeroConfig.strip ρ hρ
  have hδ2 : δ ≤ 1 / 2 := by
    refine hre.trans ?_
    rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hΛ1 : 1 ≤ Λ := by
    have h : Real.exp 1 ≤ 10 ^ 6 / δ := by
      rw [le_div_iff₀ hδ]; have := Real.exp_one_lt_d9; nlinarith
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hcount := Nd_le_of_local_count zetaZeroConfig hA₀ hloc (ρ.im - 100) 200
  have hwin : ρ.im - 100 + ((200 : ℕ) : ℝ) = ρ.im + 100 := by push_cast; ring
  rw [hwin] at hcount
  have hcountL : (zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100) : ℝ) ≤ 400 * (A₀ * L) := by
    refine hcount.trans ?_
    have hlog : Real.log (|ρ.im - 100| + ((200 : ℕ) : ℝ) + 3) ≤ 2 * L := by
      rw [hL, ← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      have h1 := abs_sub ρ.im 100
      have h2 : |(100 : ℝ)| = 100 := abs_of_pos (by norm_num)
      push_cast
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [abs_nonneg ρ.im]
    have hA0 : 0 ≤ A₀ := by linarith
    push_cast at hlog ⊢
    nlinarith
  refine not_hodgeIndex_below_nyquist_horizon zetaZeroConfig hA₀ hloc hρ hδ hre hγ
    (n := zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100)) le_rfl ?_
  have hA0 : 0 < A₀ := by linarith
  have hG : Real.log (A₀ * (|ρ.im| + 3)) ≤ A₀ + L := by
    rw [Real.log_mul hA0.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos hA0
    linarith
  set nn := (zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := Nat.cast_nonneg _
  have hAL : 1 ≤ A₀ * L := by nlinarith
  have hALΛ : 1 ≤ A₀ * L * Λ := by nlinarith
  have h1 : (nn + 1) * Λ ≤ (400 * (A₀ * L) + 1) * Λ :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : A₀ ≤ A₀ * L * Λ := by nlinarith
  have h3 : L ≤ A₀ * L * Λ := by nlinarith
  have h4 : Λ ≤ A₀ * L * Λ := by nlinarith
  nlinarith

/-- **Exponential depth law for `ζ`.**  There is `A₀` such that the level-`a` Hodge index forces
every zero of `ζ` with `|γ| ≥ 102` to lie within `10⁶ e^{-a/(2000 A₀ log(|γ| + 3))}` of the critical
line.  At a fixed height the admissible depth decays exponentially in the level. -/
theorem zeta_depth_lt_of_hodgeIndex :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ ∈ zetaZeroConfig.carrier, 102 ≤ |ρ.im| →
        |ρ.re - 1 / 2| < 10 ^ 6 * Real.exp (-(a / (2000 * A₀ * Real.log (|ρ.im| + 3)))) := by
  obtain ⟨A₀, hA₀, hhor⟩ := zeta_hodge_index_nyquist_horizon
  refine ⟨A₀, hA₀, fun a hodge ρ hρ hγ => ?_⟩
  set δ := |ρ.re - 1 / 2| with hδdef
  have hL : 0 < Real.log (|ρ.im| + 3) := Real.log_pos (by linarith [abs_nonneg ρ.im])
  have hK : 0 < 2000 * A₀ * Real.log (|ρ.im| + 3) := by positivity
  have hE : 0 < 10 ^ 6 * Real.exp (-(a / (2000 * A₀ * Real.log (|ρ.im| + 3)))) := by positivity
  rcases (abs_nonneg (ρ.re - 1 / 2)).lt_or_eq with hδ | hδ
  · have hδ0 : 0 < δ := hδ
    by_contra hge
    push Not at hge
    have hlog : Real.log (10 ^ 6 / δ) ≤ a / (2000 * A₀ * Real.log (|ρ.im| + 3)) := by
      have h1 : 10 ^ 6 / δ ≤ Real.exp (a / (2000 * A₀ * Real.log (|ρ.im| + 3))) := by
        rw [div_le_iff₀ hδ0]
        have h2 : Real.exp (a / (2000 * A₀ * Real.log (|ρ.im| + 3))) *
            Real.exp (-(a / (2000 * A₀ * Real.log (|ρ.im| + 3)))) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (a / (2000 * A₀ * Real.log (|ρ.im| + 3)))]
      calc Real.log (10 ^ 6 / δ) ≤ Real.log (Real.exp (a / (2000 * A₀ * Real.log (|ρ.im| + 3)))) :=
            Real.log_le_log (by positivity) h1
        _ = _ := Real.log_exp _
    rw [le_div_iff₀ hK] at hlog
    have hsize : 2000 * A₀ * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / δ) ≤ a := by linarith
    exact hhor δ hδ0 ρ hρ le_rfl hγ a hsize hodge
  · have : δ = 0 := by rw [hδdef]; exact hδ.symm
    rw [this]; exact hE

end RHTower
