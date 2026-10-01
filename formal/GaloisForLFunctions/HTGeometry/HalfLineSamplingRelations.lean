import GaloisForLFunctions.HTGeometry.HalfLineSamplingLowerBound
import GaloisForLFunctions.HTGeometry.SamplingDominatedFunctional

/-!
# Linear relations among node values on the half line

On a space `E` of functions on `(0,∞)` with `∫|F'|² ≤ K²∫x²|F|²`, a supercritical node sequence
`p` controls the weighted norm (`sampling_lower_bound`), and the weighted norm controls each point
value (`|F(x)|² ≤ 2x⁻²∫x²|F|² + 2∫|F'|²`). Hence each evaluation `F ↦ F(x)` is dominated by the
sampling norm and is therefore a fixed `ℓ²`-type combination of node values:
`F(x) = Σ_j γ_j F(p_j)` for all `F ∈ E`, with `|γ_j|² ≤ M(p_{j+1}+1)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Pointwise bound on the half line: `|F(x)|² ≤ 2x⁻² ∫x²|F|² + 2∫|F'|²` for `x > 0`. -/
theorem norm_sq_le_of_hasDerivAt_Ioi {F F' : ℝ → ℂ} (hF : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hF'c : ContinuousOn F' (Ioi 0))
    (hXF : IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0))
    (hF'2 : IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ‖F x‖ ^ 2 ≤ 2 * (x ^ 2)⁻¹ * (∫ y in Ioi 0, y ^ 2 * ‖F y‖ ^ 2) + 2 * ∫ y in Ioi 0, ‖F' y‖ ^ 2 := by
  set I := ∫ y in Ioi (0 : ℝ), y ^ 2 * ‖F y‖ ^ 2 with hI
  set J := ∫ y in Ioi (0 : ℝ), ‖F' y‖ ^ 2 with hJ
  have hFc : ContinuousOn F (Icc x (x + 1)) := fun y hy =>
    (hF y (lt_of_lt_of_le hx hy.1)).continuousAt.continuousWithinAt
  have hpt : ∀ t ∈ Ioc x (x + 1), ‖F x‖ ^ 2 ≤ 2 * ‖F t‖ ^ 2 + 2 * J := by
    intro t ht
    have hinc := norm_sub_sq_le_of_hasDerivAt ht.1.le
      (fun y hy => hF y (lt_of_lt_of_le hx hy.1))
      (hF'c.mono (fun y hy => lt_of_lt_of_le hx hy.1))
    have hsub : ∫ y in Ioc x t, ‖F' y‖ ^ 2 ≤ J :=
      setIntegral_mono_set hF'2 (Eventually.of_forall fun y => by positivity)
        (Eventually.of_forall fun y hy => lt_of_lt_of_le hx (le_of_lt hy.1))
    have hI0 : 0 ≤ ∫ y in Ioc x t, ‖F' y‖ ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun y _ => by positivity)
    have h2 : ‖F t - F x‖ ^ 2 ≤ J := by
      calc ‖F t - F x‖ ^ 2 ≤ (t - x) * ∫ y in Ioc x t, ‖F' y‖ ^ 2 := hinc
        _ ≤ 1 * J := by
          apply mul_le_mul (by linarith [ht.2]) hsub hI0 (by norm_num)
        _ = J := one_mul J
    have htri : ‖F x‖ ≤ ‖F t‖ + ‖F t - F x‖ := by
      calc ‖F x‖ = ‖F t - (F t - F x)‖ := by ring_nf
        _ ≤ ‖F t‖ + ‖F t - F x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (F x), norm_nonneg (F t), norm_nonneg (F t - F x),
      sq_nonneg (‖F t‖ - ‖F t - F x‖)]
  have hint1 : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ioc x (x + 1)) :=
    (((hFc.norm).pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hmeas : (volume (Ioc x (x + 1))).toReal = 1 := by simp
  have hstep1 : ‖F x‖ ^ 2 ≤ ∫ t in Ioc x (x + 1), (2 * ‖F t‖ ^ 2 + 2 * J) := by
    have hc : ∫ _t in Ioc x (x + 1), ‖F x‖ ^ 2 = ‖F x‖ ^ 2 := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]; ring_nf
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (measure_Ioc_lt_top).ne)
      ((hint1.const_mul 2).add (integrableOn_const (measure_Ioc_lt_top).ne)) measurableSet_Ioc hpt
  have hstep2 : ∫ t in Ioc x (x + 1), (2 * ‖F t‖ ^ 2 + 2 * J)
      = 2 * (∫ t in Ioc x (x + 1), ‖F t‖ ^ 2) + 2 * J := by
    have hadd := integral_add (μ := volume.restrict (Ioc x (x + 1)))
      (f := fun t => 2 * ‖F t‖ ^ 2) (g := fun _ => 2 * J) (hint1.const_mul 2)
      (integrableOn_const (measure_Ioc_lt_top).ne)
    rw [hadd, integral_const_mul, setIntegral_const, Real.volume_real_Ioc_of_le (by linarith),
      smul_eq_mul]
    ring
  have hstep3 : ∫ t in Ioc x (x + 1), ‖F t‖ ^ 2 ≤ (x ^ 2)⁻¹ * I := by
    have hxx : 0 < x ^ 2 := by positivity
    have hmono : ∫ t in Ioc x (x + 1), ‖F t‖ ^ 2
        ≤ ∫ t in Ioc x (x + 1), (x ^ 2)⁻¹ * (t ^ 2 * ‖F t‖ ^ 2) := by
      refine setIntegral_mono_on hint1 ((hXF.mono_set ?_).const_mul _) measurableSet_Ioc ?_
      · exact fun t ht => lt_trans hx ht.1
      · intro t ht
        have ht2 : x ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hx.le ht.1.le 2
        rw [← mul_assoc]
        have : 1 ≤ (x ^ 2)⁻¹ * t ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hxx]; linarith
        nlinarith [norm_nonneg (F t), sq_nonneg ‖F t‖]
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set hXF (Eventually.of_forall fun y => by positivity)
      (Eventually.of_forall fun y hy => lt_trans hx hy.1)
  calc ‖F x‖ ^ 2 ≤ 2 * (∫ t in Ioc x (x + 1), ‖F t‖ ^ 2) + 2 * J := hstep1.trans hstep2.le
    _ ≤ 2 * ((x ^ 2)⁻¹ * I) + 2 * J := by linarith
    _ = 2 * (x ^ 2)⁻¹ * I + 2 * J := by ring

/-- **Sampling relations on the half line.** Let `E` be a space of functions on `(0,∞)` with
square-integrable derivative and `∫|F'|² ≤ K²∫x²|F|²`, and let `p` be a supercritical node
sequence with `1 - ((1+ε)²(a/2π)² + 2p₀⁴)K² > 0` along which every `F ∈ E` is square summable
with the weights `max(p_j,p_{j+1})`. Then every point evaluation `F ↦ F(x)`, `x > 0`, is a fixed
linear combination of the node values: `F(x) = Σ γ_j F(p_j)` on `E`, with
`|γ_j|² ≤ M (p_{j+1} + 1)`. -/
theorem exists_sampling_relation (E : Submodule ℂ (ℝ → ℂ)) {K : ℝ}
    (hE : ∀ F ∈ E, ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧
      ContinuousOn F' (Ioi 0) ∧ IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2)
    {p : ℕ → ℝ} (hp : StrictMono p) (hp0 : 0 < p 0) (hpinf : Tendsto p atTop atTop)
    {ε a : ℝ} (hε : 0 < ε) (hgap : ∀ j, max |p j| |p (j + 1)| * (p (j + 1) - p j) ≤ a / 2)
    (hbr : 0 < 1 - ((1 + ε) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * p 0 ^ 4) * K ^ 2)
    (hsum : ∀ F ∈ E, Summable fun j => max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2))
    {x : ℝ} (hx : 0 < x) :
    ∃ γ : ℕ → ℂ, ∃ M : ℝ, (∀ j, ‖γ j‖ ^ 2 ≤ M * (p (j + 1) + 1)) ∧
      ∀ F ∈ E, Summable (fun j => γ j * F (p j)) ∧ F x = ∑' j, γ j * F (p j) := by
  set B := 1 - ((1 + ε) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * p 0 ^ 4) * K ^ 2 with hB
  set Kε := (1 + ε⁻¹) * (2 + 2 * (1 + ε) / Real.pi ^ 2) with hKε
  have hKε0 : 0 ≤ Kε := by positivity
  have hpos : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp0 (hp.monotone (Nat.zero_le j))
  have hm : ∀ j, max |p j| |p (j + 1)| = p (j + 1) := by
    intro j
    rw [abs_of_pos (hpos j), abs_of_pos (hpos (j + 1))]
    exact max_eq_right (hp (Nat.lt_succ_self j)).le
  have ha : 0 ≤ a := by
    have h1 := hgap 0
    rw [hm 0] at h1
    have : 0 < p 1 * (p 1 - p 0) := mul_pos (hpos 1) (sub_pos.mpr (hp Nat.zero_lt_one))
    linarith
  -- single-index weights
  set m : ℕ → ℝ := fun j => p (j + 1) with hmdef
  set m' : ℕ → ℝ := fun j => if j = 0 then 0 else p j with hm'def
  set w : ℕ → ℝ := fun j => Kε * (a / 2) * (m j + m' j) + (if j = 0 then 2 * p 0 ^ 3 else 0)
    with hw
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    have h1 : 0 ≤ m j := (hpos _).le
    have h2 : 0 ≤ m' j := by simp only [hm'def]; split_ifs; exacts [le_rfl, (hpos _).le]
    have h3 : 0 ≤ (if j = 0 then 2 * p 0 ^ 3 else 0) := by
      split_ifs; exacts [by have := hpos 0; positivity, le_rfl]
    simp only [hw]; positivity
  have hwle : ∀ j, w j ≤ (Kε * a + 2 * p 0 ^ 3) * (p (j + 1) + 1) := by
    intro j
    have hpj : p j ≤ p (j + 1) := (hp (Nat.lt_succ_self j)).le
    have h1 : m' j ≤ p (j + 1) := by
      simp only [hm'def]; split_ifs; exacts [(hpos _).le, hpj]
    have h3 : (if j = 0 then 2 * p 0 ^ 3 else 0) ≤ 2 * p 0 ^ 3 := by
      split_ifs; exacts [le_rfl, by have := hpos 0; positivity]
    have hp1 := hpos (j + 1)
    have hp03 : 0 ≤ 2 * p 0 ^ 3 := by have := hpos 0; positivity
    simp only [hw, hmdef]
    have : Kε * (a / 2) * (p (j + 1) + m' j) ≤ Kε * a * (p (j + 1) + 1) := by
      have hKa : 0 ≤ Kε * a := mul_nonneg hKε0 ha
      nlinarith
    nlinarith
  -- the weighted sampling identity and lower bound
  have hlow : ∀ F ∈ E, Summable (fun j => w j * ‖F (p j)‖ ^ 2) ∧
      B * ∫ y in Ioi 0, y ^ 2 * ‖F y‖ ^ 2 ≤ ∑' j, w j * ‖F (p j)‖ ^ 2 := by
    intro F hFE
    obtain ⟨F', hF, hF'c, hXF, hF'2, hK⟩ := hE F hFE
    have hs := hsum F hFE
    simp_rw [hm] at hs
    have hs1 : Summable fun j => p (j + 1) * ‖F (p j)‖ ^ 2 :=
      hs.of_nonneg_of_le (fun j => mul_nonneg (hpos _).le (by positivity))
        (fun j => mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖F (p (j + 1))‖])
          (hpos _).le)
    have hs2 : Summable fun j => p (j + 1) * ‖F (p (j + 1))‖ ^ 2 :=
      hs.of_nonneg_of_le (fun j => mul_nonneg (hpos _).le (by positivity))
        (fun j => mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖F (p j)‖]) (hpos _).le)
    have hs3 : Summable fun j => m' j * ‖F (p j)‖ ^ 2 := by
      rw [← summable_nat_add_iff 1]
      simpa [hm'def] using hs2
    have hshift : ∑' j, m' j * ‖F (p j)‖ ^ 2 = ∑' j, p (j + 1) * ‖F (p (j + 1))‖ ^ 2 := by
      rw [hs3.tsum_eq_zero_add]
      simp [hm'def]
    have hsw : Summable fun j => w j * ‖F (p j)‖ ^ 2 := by
      have : (fun j => w j * ‖F (p j)‖ ^ 2) = fun j => Kε * (a / 2) * (m j * ‖F (p j)‖ ^ 2
          + m' j * ‖F (p j)‖ ^ 2) + (if j = 0 then 2 * p 0 ^ 3 * ‖F (p 0)‖ ^ 2 else 0) := by
        funext j; simp only [hw]; split_ifs with h <;> simp [h] <;> ring
      rw [this]
      exact ((hs1.add hs3).mul_left _).add (summable_of_ne_finset_zero (s := {0})
        (fun j hj => by simp at hj; simp [hj]))
    refine ⟨hsw, ?_⟩
    have hlb := sampling_lower_bound hF hF'c hXF hF'2 hK hp hp0 hpinf hε hgap
      (by simpa only [hm] using hsum F hFE)
    simp_rw [hm] at hlb
    have hT : ∑' j, p (j + 1) * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2)
        = ∑' j, m j * ‖F (p j)‖ ^ 2 + ∑' j, m' j * ‖F (p j)‖ ^ 2 := by
      rw [hshift, ← hs1.tsum_add hs2]
      congr 1; funext j; ring
    have hW : ∑' j, w j * ‖F (p j)‖ ^ 2
        = Kε * (a / 2) * (∑' j, m j * ‖F (p j)‖ ^ 2 + ∑' j, m' j * ‖F (p j)‖ ^ 2)
          + 2 * p 0 ^ 3 * ‖F (p 0)‖ ^ 2 := by
      have e : (fun j => w j * ‖F (p j)‖ ^ 2) = fun j => Kε * (a / 2) * (m j * ‖F (p j)‖ ^ 2
          + m' j * ‖F (p j)‖ ^ 2) + (if j = 0 then 2 * p 0 ^ 3 * ‖F (p 0)‖ ^ 2 else 0) := by
        funext j; simp only [hw]; split_ifs with h <;> simp [h] <;> ring
      rw [e, Summable.tsum_add ((hs1.add hs3).mul_left _) (summable_of_ne_finset_zero (s := {0})
        (fun j hj => by simp at hj; simp [hj])), tsum_mul_left, hs1.tsum_add hs3,
        tsum_ite_eq]
    rw [hW, ← hT]
    simpa only [hB, hKε] using hlb
  -- the abstract representation
  let S : ℕ → E →ₗ[ℂ] ℂ := fun j =>
    ((Real.sqrt (w j) : ℝ) : ℂ) • ((LinearMap.proj (R := ℂ) (φ := fun _ : ℝ => ℂ) (p j)) ∘ₗ E.subtype)
  have hSj : ∀ (F : E) j, S j F = ((Real.sqrt (w j) : ℝ) : ℂ) * (F : ℝ → ℂ) (p j) := fun F j => rfl
  have hSn : ∀ (F : E) j, ‖S j F‖ ^ 2 = w j * ‖(F : ℝ → ℂ) (p j)‖ ^ 2 := by
    intro F j
    rw [hSj, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw0 j)]
  let φ : E →ₗ[ℂ] ℂ := (LinearMap.proj (R := ℂ) (φ := fun _ : ℝ => ℂ) x) ∘ₗ E.subtype
  have hφ : ∀ F : E, φ F = (F : ℝ → ℂ) x := fun F => rfl
  set C := (2 * (x ^ 2)⁻¹ + 2 * K ^ 2) / B with hC
  have hdom : ∀ F : E, ‖φ F‖ ^ 2 ≤ C * ∑' j, ‖S j F‖ ^ 2 := by
    intro F
    obtain ⟨F', hF, hF'c, hXF, hF'2, hK⟩ := hE F F.2
    obtain ⟨-, hl⟩ := hlow F F.2
    have hpw := norm_sq_le_of_hasDerivAt_Ioi hF hF'c hXF hF'2 hx
    simp_rw [hSn, hφ]
    set I := ∫ y in Ioi (0 : ℝ), y ^ 2 * ‖(F : ℝ → ℂ) y‖ ^ 2
    have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun y _ => by positivity)
    have h1 : ‖(F : ℝ → ℂ) x‖ ^ 2 ≤ (2 * (x ^ 2)⁻¹ + 2 * K ^ 2) * I := by nlinarith
    have h2 : I ≤ (∑' j, w j * ‖(F : ℝ → ℂ) (p j)‖ ^ 2) / B := by
      rw [le_div_iff₀ hbr]; linarith
    have hc0 : 0 ≤ 2 * (x ^ 2)⁻¹ + 2 * K ^ 2 := by positivity
    calc ‖(F : ℝ → ℂ) x‖ ^ 2 ≤ (2 * (x ^ 2)⁻¹ + 2 * K ^ 2) * I := h1
      _ ≤ (2 * (x ^ 2)⁻¹ + 2 * K ^ 2) * ((∑' j, w j * ‖(F : ℝ → ℂ) (p j)‖ ^ 2) / B) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ = C * ∑' j, w j * ‖(F : ℝ → ℂ) (p j)‖ ^ 2 := by rw [hC]; ring
  have hSsum : ∀ F : E, Summable fun j => ‖S j F‖ ^ 2 := by
    intro F; simp_rw [hSn]; exact (hlow F F.2).1
  obtain ⟨β, hβ, hrep⟩ := exists_coeff_of_dominated S hSsum φ hdom
  set Bβ := ∑' j, ‖β j‖ ^ 2 with hBβ
  refine ⟨fun j => β j * ((Real.sqrt (w j) : ℝ) : ℂ), Bβ * (Kε * a + 2 * p 0 ^ 3), ?_, ?_⟩
  · intro j
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw0 j)]
    have hb : ‖β j‖ ^ 2 ≤ Bβ := hβ.le_tsum j (fun i _ => by positivity)
    have hB0 : 0 ≤ Bβ := tsum_nonneg fun i => by positivity
    calc ‖β j‖ ^ 2 * w j ≤ Bβ * ((Kε * a + 2 * p 0 ^ 3) * (p (j + 1) + 1)) :=
          mul_le_mul hb (hwle j) (hw0 j) hB0
      _ = _ := by ring
  · intro F hFE
    have hr := hrep ⟨F, hFE⟩
    simp only [hφ, hSj] at hr
    refine ⟨?_, ?_⟩
    · refine Summable.of_norm_bounded ((hβ.add (hlow F hFE).1).div_const 2) (fun j => ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hsq : Real.sqrt (w j) ^ 2 = w j := Real.sq_sqrt (hw0 j)
      nlinarith [sq_nonneg (‖β j‖ - Real.sqrt (w j) * ‖F (p j)‖), norm_nonneg (β j),
        Real.sqrt_nonneg (w j), norm_nonneg (F (p j))]
    · rw [hr]
      congr 1; funext j; ring

end GaloisForLFunctions.HTGeometry
