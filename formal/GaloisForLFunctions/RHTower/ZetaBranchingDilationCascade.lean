import GaloisForLFunctions.RHTower.ZetaDilationCascade

/-!
# The branching dilation cascade

Receivers whose Euler product carries several dilated zeta factors, such as squarefull numbers with
`ζ(2s)ζ(3s)/ζ(6s)`, turn a power bound into a branching law: every zero `ρ` in a band has
`ζ(ρ/k) = 0` for at least one dilation `k` from a set `K`. Reflection then gives the zero `1 - ρ/k`,
so the zero set would be invariant under the iterated function system `{z ↦ 1 - z/k : k ∈ K}`.

**Theorem** (`riemannZeta_ne_zero_of_branching`). Let `0 < a ≤ b < 1`, let every `k ∈ K` satisfy
`k ≥ κ > 1`, and let the closed band `[a, b]` of real parts be invariant under every map
`x ↦ 1 - x/k`, `k ∈ K`. If every zero with `a ≤ Re ρ ≤ b` has `ζ(ρ/k) = 0` for some `k ∈ K`, then
`ζ` has no zero with `a ≤ Re s ≤ b`.

**Proof.** Choose a branch at each step. The orbit stays in the band, and its imaginary parts shrink
by a factor `≤ 1/κ` per step. A subsequence converges to a real point of `[a, b] ⊂ (0, 1)`, where
`ζ ≠ 0`, while `ζ` vanishes along the orbit.
-/

open Filter Topology Complex

namespace RHTower.DilationCascade

noncomputable section

/-- **Branching dilation cascade.** -/
theorem riemannZeta_ne_zero_of_branching {a b κ : ℝ} {K : Set ℝ} (ha : 0 < a) (hb : b < 1)
    (hκ : 1 < κ) (hKκ : ∀ k ∈ K, κ ≤ k)
    (hinv : ∀ k ∈ K, ∀ x : ℝ, a ≤ x → x ≤ b → a ≤ 1 - x / k ∧ 1 - x / k ≤ b)
    (hbranch : ∀ ρ : ℂ, riemannZeta ρ = 0 → a ≤ ρ.re → ρ.re ≤ b →
      ∃ k ∈ K, riemannZeta (ρ / k) = 0)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) : riemannZeta s ≠ 0 := by
  intro hz
  have hκ0 : 0 < κ := by linarith
  set P : ℂ → Prop := fun z => riemannZeta z = 0 ∧ a ≤ z.re ∧ z.re ≤ b with hP
  -- one step of the cascade
  have hstep : ∀ z : ℂ, P z → ∃ w : ℂ, P w ∧ |w.im| ≤ |z.im| / κ := by
    rintro z ⟨hz0, hza, hzb⟩
    obtain ⟨k, hkK, hk0⟩ := hbranch z hz0 hza hzb
    have hk : κ ≤ k := hKκ k hkK
    have hkpos : 0 < k := by linarith
    have hdre : (z / k).re = z.re / k := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]
    have hdim : (z / k).im = z.im / k := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_im]
    have hre0 : 0 < (z / k).re := by rw [hdre]; exact div_pos (by linarith) hkpos
    have hre1 : (z / k).re < 1 := by
      rw [hdre, div_lt_one hkpos]; linarith
    refine ⟨1 - z / k, ⟨(riemannZeta_one_sub_eq_zero_iff hre0 hre1).mpr hk0, ?_, ?_⟩, ?_⟩
    · have := (hinv k hkK z.re hza hzb).1
      simp only [Complex.sub_re, Complex.one_re, hdre]; exact this
    · have := (hinv k hkK z.re hza hzb).2
      simp only [Complex.sub_re, Complex.one_re, hdre]; exact this
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, hdim, abs_div,
        abs_of_pos hkpos]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hκ0 hk
  -- the orbit
  classical
  let next : ℂ → ℂ := fun z => if h : P z then Classical.choose (hstep z h) else z
  have hnext : ∀ z, P z → P (next z) ∧ |(next z).im| ≤ |z.im| / κ := by
    intro z hzP
    simp only [next, dif_pos hzP]
    exact Classical.choose_spec (hstep z hzP)
  set orb : ℕ → ℂ := fun j => next^[j] s with horb
  have hPorb : ∀ j, P (orb j) ∧ |(orb j).im| ≤ |s.im| / κ ^ j := by
    intro j
    induction j with
    | zero => exact ⟨⟨hz, h1, h2⟩, by simp [horb]⟩
    | succ j ih =>
      have hs : orb (j + 1) = next (orb j) := by
        simp only [horb]; rw [Function.iterate_succ_apply']
      obtain ⟨hP', him⟩ := hnext (orb j) ih.1
      rw [hs]
      refine ⟨hP', him.trans ?_⟩
      rw [pow_succ, ← div_div]
      exact div_le_div_of_nonneg_right ih.2 hκ0.le
  -- a convergent subsequence
  have hbdd : Bornology.IsBounded {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ |s.im|} := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |s.im|)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |s.im| := by
          have : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
          linarith [hz.2.2]
  have hmem : ∀ j, orb j ∈ {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ |s.im|} := by
    intro j
    obtain ⟨⟨_, hra, hrb⟩, him⟩ := hPorb j
    refine ⟨hra, hrb, him.trans ?_⟩
    exact div_le_self (abs_nonneg _) (one_le_pow₀ (by linarith))
  obtain ⟨z₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd hmem
  -- the limit is real and lies in the band
  have him0 : Tendsto (fun j => |(orb (φ j)).im|) atTop (𝓝 0) := by
    have hgeom : Tendsto (fun j : ℕ => |s.im| / κ ^ (φ j)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / κ)
        (by rw [div_lt_one hκ0]; exact hκ)).comp hφ.tendsto_atTop
      have h' := h.const_mul |s.im|
      rw [mul_zero] at h'
      refine h'.congr fun j => ?_
      simp only [Function.comp_apply, one_div, inv_pow]
      ring
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => (hPorb (φ j)).2) hgeom
  have hz₀im : z₀.im = 0 := by
    have h := (Complex.continuous_im.tendsto z₀).comp hlim
    have h' : Tendsto (fun j => |(orb (φ j)).im|) atTop (𝓝 |z₀.im|) :=
      (continuous_abs.tendsto _).comp h
    exact abs_eq_zero.mp (tendsto_nhds_unique h' him0)
  have hz₀re : a ≤ z₀.re ∧ z₀.re ≤ b := by
    have h := (Complex.continuous_re.tendsto z₀).comp hlim
    exact ⟨ge_of_tendsto h (Eventually.of_forall fun j => (hPorb (φ j)).1.2.1),
      le_of_tendsto h (Eventually.of_forall fun j => (hPorb (φ j)).1.2.2)⟩
  -- `ζ` vanishes at the limit
  have hz₀1 : z₀ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hz₀re; linarith [hz₀re.2]
  have hcont : ContinuousAt riemannZeta z₀ := (differentiableAt_riemannZeta hz₀1).continuousAt
  have hval : Tendsto (fun j => riemannZeta (orb (φ j))) atTop (𝓝 (riemannZeta z₀)) :=
    hcont.tendsto.comp hlim
  have hzero : Tendsto (fun j => riemannZeta (orb (φ j))) atTop (𝓝 0) := by
    simp only [fun j => (hPorb (φ j)).1.1]; exact tendsto_const_nhds
  have hζz₀ : riemannZeta z₀ = 0 := tendsto_nhds_unique hval hzero
  have hreal : z₀ = ((z₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz₀im])
  rw [hreal] at hζz₀
  exact riemannZeta_ofReal_ne_zero (by linarith [hz₀re.1]) (by linarith [hz₀re.2]) hζz₀

end

end RHTower.DilationCascade
