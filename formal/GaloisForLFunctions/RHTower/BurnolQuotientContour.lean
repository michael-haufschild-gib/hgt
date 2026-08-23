import GaloisForLFunctions.RHTower.BurnolMoebiusLine
import GaloisForLFunctions.RHTower.BurnolRectangleSum
import GaloisForLFunctions.RHTower.BurnolResidueSeries
import GaloisForLFunctions.RHTower.BurnolReflectionStability

/-!
# The contour for `M(f)/ζ`

Burnol's Proposition 5.4 integrates `M(f)(s)/ζ(s)` — no `Z` parameter — around rectangles with
vertical sides `Re s = −1` and `Re s = 2` and horizontal sides at the selected heights.  The only
residues are at the nontrivial zeros: `0`, `1` and the trivial zeros are regular exactly as in
Theorem 5.2, and the rectangle `[−1,2]` meets no trivial zero at all.

## Main results

* `burnolQuotient`, `meromorphicOrderAt_burnolQuotient`
* `rectangleIntegral'_burnolQuotient_extendedMellin`
* `tendsto_hIntegral_burnolQuotient`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Burnol's second integrand: the quotient by `ζ`. -/
def burnolQuotient (G : ℂ → ℂ) : ℂ → ℂ := fun s => G s * (riemannZeta s)⁻¹

theorem analyticAt_burnolQuotient {G : ℂ → ℂ} {s : ℂ} (hG : AnalyticAt ℂ G s)
    (hζ : riemannZeta s ≠ 0) (hs1 : s ≠ 1) : AnalyticAt ℂ (burnolQuotient G) s := by
  have hζa : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
  exact hG.mul (hζa.inv hζ)

theorem meromorphicAt_burnolQuotient {G : ℂ → ℂ} {s : ℂ} (hG : MeromorphicAt G s) :
    MeromorphicAt (burnolQuotient G) s :=
  hG.mul (meromorphicAt_riemannZeta_everywhere s).inv

theorem meromorphicOrderAt_burnolQuotient {G : ℂ → ℂ} {p : ℂ} (hG : MeromorphicAt G p) :
    meromorphicOrderAt (burnolQuotient G) p
      = meromorphicOrderAt G p - meromorphicOrderAt riemannZeta p := by
  have hζm : MeromorphicAt riemannZeta p := meromorphicAt_riemannZeta_everywhere p
  have hfun : burnolQuotient G = G / riemannZeta := by
    funext u
    rw [burnolQuotient, Pi.div_apply, div_eq_mul_inv]
  rw [hfun, meromorphicOrderAt_div hG hζm]

/-- The vanishing criterion, exactly as for the `Z`-integrand. -/
theorem laurentCoeff_burnolQuotient_eq_zero_of_order_ge {G : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hG : MeromorphicAt G p)
    (hζord : meromorphicOrderAt riemannZeta p = (m : WithTop ℤ))
    (hGord : (m : WithTop ℤ) ≤ meromorphicOrderAt G p) :
    laurentCoeff (burnolQuotient G) p (-1) = 0 := by
  refine laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg (meromorphicAt_burnolQuotient hG) ?_
    (by norm_num)
  rw [meromorphicOrderAt_burnolQuotient hG, hζord]
  exact withTop_sub_nonneg_of_le hGord

/-! ## The horizontal edges -/

theorem tendsto_hIntegral_burnolQuotient {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    {C A b : ℝ} {k₀ : ℕ} (hC : 0 < C) (hA : 0 < A) (hb : 2 ≤ b)
    {ε : ℝ} (hε : |ε| = 1)
    (hzeta : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A)
    {x₁ x₂ : ℝ} (hx₁ : -b ≤ x₁) (hx₁' : x₁ ≤ b) (hx₂ : -b ≤ x₂) (hx₂' : x₂ ≤ b) :
    Tendsto (fun k : ℕ => HIntegral (burnolQuotient G) x₁ x₂ (ε * T k)) atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (A + 1)
  obtain ⟨Tg, Cg, hCg0, hGb⟩ := hG (-b) b N
  set D : ℝ := 2 * b * (Cg * C) with hDdef
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hneg : A - (N : ℝ) < 0 := by
    have : A + 1 ≤ (N : ℝ) := hN
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun k : ℕ => D * (T k) ^ (A - (N : ℝ))) atTop (𝓝 0) := by
    have hrpow : Tendsto (fun x : ℝ => x ^ (A - (N : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := -(A - (N : ℝ))) (by linarith)
      refine h.congr fun x => ?_
      rw [neg_neg]
    have := (hrpow.comp htop).const_mul D
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun k => norm_nonneg _) ?_
  filter_upwards [Filter.eventually_ge_atTop k₀, htop.eventually_ge_atTop (max Tg 1)] with k hk hTk
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hTg : Tg ≤ T k := le_trans (le_max_left _ _) hTk
  have hbound : ∀ σ ∈ Set.uIoc x₁ x₂,
      ‖burnolQuotient G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I)‖ ≤ Cg * C * (T k) ^ (A - (N : ℝ)) := by
    intro σ hσ
    rw [Set.mem_uIoc] at hσ
    have hσ1 : -b ≤ σ := by rcases hσ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hσ2 : σ ≤ b := by rcases hσ with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
    set s : ℂ := (σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I with hs
    have hsre : s.re = σ := by rw [hs]; simp
    have hsim : s.im = ε * T k := by rw [hs]; simp
    have habs : |ε * T k| = T k := by
      rw [abs_mul, hε, one_mul, abs_of_nonneg hTk0.le]
    have h1 : ‖G s‖ ≤ Cg * (1 + |s.im|) ^ (-(N : ℝ)) := by
      refine hGb s (by rw [hsre]; linarith) (by rw [hsre]; linarith) ?_
      rw [hsim, habs]
      exact hTg
    have h2 : ‖(riemannZeta s)⁻¹‖ ≤ C * (T k) ^ A := hzeta k hk σ hσ1 hσ2
    have hpowG : (1 + |s.im|) ^ (-(N : ℝ)) ≤ (T k) ^ (-(N : ℝ)) := by
      rw [hsim, habs]
      exact Real.rpow_le_rpow_of_nonpos hTk0 (by linarith)
        (neg_nonpos.2 (Nat.cast_nonneg N))
    have hmul : (T k) ^ (-(N : ℝ)) * (T k) ^ A = (T k) ^ (A - (N : ℝ)) := by
      rw [← Real.rpow_add hTk0]
      congr 1
      ring
    rw [burnolQuotient, norm_mul]
    calc ‖G s‖ * ‖(riemannZeta s)⁻¹‖
        ≤ (Cg * (1 + |s.im|) ^ (-(N : ℝ))) * (C * (T k) ^ A) := by
          refine mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (Cg * (T k) ^ (-(N : ℝ))) * (C * (T k) ^ A) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hpowG hCg0
      _ = Cg * C * ((T k) ^ (-(N : ℝ)) * (T k) ^ A) := by ring
      _ = Cg * C * (T k) ^ (A - (N : ℝ)) := by rw [hmul]
  have hlen : |x₂ - x₁| ≤ 2 * b := by
    rw [abs_le]
    constructor <;> linarith
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hcoef : (0 : ℝ) ≤ Cg * C * (T k) ^ (A - (N : ℝ)) := by positivity
  calc ‖HIntegral (burnolQuotient G) x₁ x₂ (ε * T k)‖
      ≤ Cg * C * (T k) ^ (A - (N : ℝ)) * |x₂ - x₁| := hkey
    _ ≤ Cg * C * (T k) ^ (A - (N : ℝ)) * (2 * b) := mul_le_mul_of_nonneg_left hlen hcoef
    _ = D * (T k) ^ (A - (N : ℝ)) := by rw [hDdef]; ring

/-! ## The rectangle -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- **Only the nontrivial zeros contribute**: the rectangle `[−1,2] × [−T,T]` meets no trivial
zero, and `0`, `1` are regular points of `M(f)/ζ`. -/
theorem rectangleIntegral'_burnolQuotient_extendedMellin (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {T : ℝ} (hT : 0 < T)
    (hTz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T) :
    RectangleIntegral' (burnolQuotient (extendedMellinContinuation a c d f))
        ((-1 : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + ((T : ℝ) : ℂ) * I)
      = ∑ ρ ∈ nontrivialZeroFinset T,
          laurentCoeff (burnolQuotient (extendedMellinContinuation a c d f)) ρ (-1) := by
  classical
  set G : ℂ → ℂ := extendedMellinContinuation a c d f with hGdef
  set z : ℂ := (-1 : ℂ) + ((-T : ℝ) : ℂ) * I with hzdef
  set w : ℂ := (2 : ℂ) + ((T : ℝ) : ℂ) * I with hwdef
  have hzre : z.re = -1 := by rw [hzdef]; simp
  have hzim : z.im = -T := by rw [hzdef]; simp
  have hwre : w.re = 2 := by rw [hwdef]; simp
  have hwim : w.im = T := by rw [hwdef]; simp
  have hle_re : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have hle_im : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ p : ℂ, p ∈ Rectangle z w ↔ -1 ≤ p.re ∧ p.re ≤ 2 ∧ -T ≤ p.im ∧ p.im ≤ T := by
    intro p
    rw [mem_Rect hle_re hle_im, hzre, hzim, hwre, hwim]
  have hnbhd_of : ∀ p : ℂ, -1 < p.re → p.re < 2 → -T < p.im → p.im < T →
      Rectangle z w ∈ 𝓝 p := by
    intro p h1 h2 h3 h4
    rw [rectangle_mem_nhds_iff, mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIoo_of_le (by linarith : (-1:ℝ) ≤ 2), Set.uIoo_of_le (by linarith : -T ≤ T)]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  -- the pole set
  set P : Finset ℂ := insert (0 : ℂ) (insert (1 : ℂ) (zetaZeroFinset z w)) with hPdef
  have hstrip : ∀ p ∈ zetaZeroFinset z w, 0 < p.re ∧ p.re < 1 := by
    intro p hp
    rw [mem_zetaZeroFinset] at hp
    obtain ⟨hrect, hzero⟩ := hp
    rw [hmem] at hrect
    rcases riemannZeta_zero_trivial_or_mem_strip hzero with ⟨n, hn⟩ | hstr
    · exfalso
      have hre : p.re = -(2 * ((n : ℝ) + 1)) := by rw [hn]; simp
      have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 := hrect.1
      rw [hre] at h1
      linarith
    · exact hstr
  have hnbhd : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [hPdef, Finset.mem_insert, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hzf
    · refine hnbhd_of _ (by simp) (by simp) ?_ ?_
      · simp; linarith
      · simp; linarith
    · refine hnbhd_of _ (by simp) (by simp) ?_ ?_
      · simp; linarith
      · simp; linarith
    · obtain ⟨h1, h2⟩ := hstrip p hzf
      rw [mem_zetaZeroFinset] at hzf
      obtain ⟨hrect, hzero⟩ := hzf
      rw [hmem] at hrect
      have habs : |p.im| ≠ T := hTz p hzero h1 h2
      refine hnbhd_of _ (by linarith) (by linarith) ?_ ?_
      · rcases lt_or_eq_of_le hrect.2.2.1 with h | h
        · exact h
        · exact absurd (by rw [← h, abs_of_nonpos (by linarith)]; ring) habs
      · rcases lt_or_eq_of_le hrect.2.2.2 with h | h
        · exact h
        · exact absurd (by rw [h, abs_of_nonneg (by linarith)]) habs
  have hmero : ∀ p ∈ P, MeromorphicAt (burnolQuotient G) p := by
    intro p _
    exact meromorphicAt_burnolQuotient (meromorphicAt_extendedMellinContinuation ha hev hc hd p)
  have hoff : ∀ s ∈ Rectangle z w, s ∉ P → AnalyticAt ℂ (burnolQuotient G) s := by
    intro s hs hsP
    rw [hPdef, Finset.mem_insert, Finset.mem_insert] at hsP
    push Not at hsP
    obtain ⟨hs0, hs1, hszf⟩ := hsP
    have hζ : riemannZeta s ≠ 0 := by
      intro hzero
      exact hszf (mem_zetaZeroFinset.2 ⟨hs, hzero⟩)
    exact analyticAt_burnolQuotient
      (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hs0 hs1) hζ hs1
  rw [rectangleIntegral'_eq_sum_laurentCoeff hle_re hle_im hnbhd hmero hoff]
  -- split off the regular points
  set q : ℂ → Prop := fun p => riemannZeta p = 0 ∧ 0 < p.re ∧ p.re < 1 with hqdef
  have hfilter : P.filter q = nontrivialZeroFinset T := by
    ext ρ
    rw [Finset.mem_filter, mem_nontrivialZeroFinset]
    constructor
    · rintro ⟨hmemP, hzero, h1, h2⟩
      refine ⟨hzero, h1, h2, ?_⟩
      rw [hPdef, Finset.mem_insert, Finset.mem_insert] at hmemP
      rcases hmemP with rfl | rfl | hzf
      · simp at h1
      · simp at h2
      · rw [mem_zetaZeroFinset, hmem] at hzf
        have habs : |ρ.im| ≠ T := hTz ρ hzero h1 h2
        rcases lt_or_eq_of_le hzf.1.2.2.2 with h | h
        · rcases lt_or_eq_of_le hzf.1.2.2.1 with h' | h'
          · rw [abs_lt]; exact ⟨h', h⟩
          · exact absurd (by rw [← h', abs_of_nonpos (by linarith)]; ring) habs
        · exact absurd (by rw [h, abs_of_nonneg (by linarith)]) habs
    · rintro ⟨hzero, h1, h2, him⟩
      have hmemZF : ρ ∈ zetaZeroFinset z w := by
        refine mem_zetaZeroFinset.2 ⟨?_, hzero⟩
        rw [hmem]
        have habs := abs_lt.1 him
        exact ⟨by linarith, by linarith, habs.1.le, habs.2.le⟩
      refine ⟨?_, hzero, h1, h2⟩
      rw [hPdef, Finset.mem_insert, Finset.mem_insert]
      exact Or.inr (Or.inr hmemZF)
  have hzeroSum : ∑ p ∈ P.filter (fun p => ¬ q p),
      laurentCoeff (burnolQuotient G) p (-1) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hmemP, hnq⟩ := hp
    rw [hPdef, Finset.mem_insert, Finset.mem_insert] at hmemP
    rcases hmemP with rfl | rfl | hzf
    · refine laurentCoeff_burnolQuotient_eq_zero_of_order_ge
        (meromorphicAt_extendedMellinContinuation ha hev hc hd 0)
        meromorphicOrderAt_riemannZeta_zero_point ?_
      exact zero_le_meromorphicOrderAt_extendedMellinContinuation_zero ha hev hc hd
    · refine laurentCoeff_burnolQuotient_eq_zero_of_order_ge
        (meromorphicAt_extendedMellinContinuation ha hev hc hd 1)
        GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one ?_
      exact neg_one_le_meromorphicOrderAt_extendedMellinContinuation_one ha hev hc hd
    · obtain ⟨h1, h2⟩ := hstrip p hzf
      rw [mem_zetaZeroFinset] at hzf
      exact absurd ⟨hzf.2, h1, h2⟩ hnq
  rw [← Finset.sum_filter_add_sum_filter_not P q, hfilter, hzeroSum, add_zero]

end

end RHTower
