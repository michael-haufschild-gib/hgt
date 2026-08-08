/-
The real-axis growth of ξ, and the resulting unconditional off-line reflection wall.

The reflection `s ↦ b − s` fixes `b/2`; its fixed point lies **off** the critical line exactly when
`Re b ≠ 1`.  `SeamOfflineReflection` reduces "no off-line reflection" to the aperiodicity hypothesis
`hap`; here that hypothesis is discharged for the *entire* completed zeta ξ itself, for the case the
geometry cares about (an off-line fixed point), by proving ξ grows on the real axis.

* `gammaR_norm_tendsto_atTop` — `‖Γℝ(σ₀ + 2n)‖ → ∞`.  From the recursion `Γℝ(s+2) = (s/2π)·Γℝ(s)`,
  once `s ≥ 4π` the factor exceeds `2`, so the values double each step; no Stirling asymptotic is
  needed, only that `Γℝ > 0` and the two-step multiplier grows.
* `one_le_re_riemannZeta_ofReal` — `1 ≤ Re ζ(σ)` for real `σ > 1`, from the Dirichlet series whose
  `n = 1` term is `1` and whose terms are nonnegative reals.
* `xi_norm_tendsto_atTop` — `‖ξ(σ₀ + 2n)‖ → ∞`, via `ξ = ½·s(s−1)·Λ` and `Λ = ζ·Γℝ`: the polynomial
  and `ζ` factors are `≥ 1`, so `‖ξ‖ ≥ ‖Γℝ‖ → ∞`.
* `xi_not_real_periodic_pos` — ξ has no positive real period: a period would make the continuous
  `σ ↦ ξ(σ)` bounded, contradicting the growth.
* `xi_reflection_center_re_eq_one` — **the wall, unconditional.**  Any reflection `s ↦ b − s` fixing
  ξ has `Re b = 1`: its fixed point `b/2` lies on the critical line.  A center off the line induces,
  via the functional equation and Schwarz reality `ξ(s̄) = ξ(s)⁻` (giving the conjugate period), a
  nonzero *real* period, which the growth forbids.

Thus the FE is the only reflection of ξ reaching off the line — unconditionally, no longer resting on
`hap`.  The transcendental growth of the completed zeta is exactly what the entire model must spend to
recover the rigidity the meromorphic Λ gets for free from its pole.
-/
import GaloisForLFunctions.RHTower.SeamOfflineReflection
import GaloisForLFunctions.RHTower.Reflection

open Complex Real Filter Topology

namespace RHTower

/-! ### §1 `Γℝ` grows super-exponentially on the real axis -/

/-- `‖Γℝ(σ₀ + 2n)‖ → ∞` for `σ₀ ≥ 4π`.  The functional recursion `Γℝ(s+2) = (s/2π)·Γℝ(s)` gives a
two-step multiplier `≥ 2` once `s ≥ 4π`, so the values at least double each step. -/
theorem gammaR_norm_tendsto_atTop (σ₀ : ℝ) (hσ : 4 * π ≤ σ₀) :
    Tendsto (fun n : ℕ => ‖Gammaℝ ((σ₀ : ℂ) + 2 * n)‖) atTop atTop := by
  have hπ : 0 < π := Real.pi_pos
  have hσ0 : 0 < σ₀ := lt_of_lt_of_le (by positivity) hσ
  have hposr : ∀ n : ℕ, (0:ℝ) < σ₀ + 2 * (n:ℝ) := fun n => by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  set a : ℕ → ℝ := fun n => ‖Gammaℝ ((σ₀ : ℂ) + 2 * n)‖ with ha
  have hre : ∀ n : ℕ, 0 < ((σ₀ : ℂ) + 2 * n).re := fun n => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
    have := hposr n; linarith
  have hpos : ∀ n, 0 < a n := fun n => norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (hre n))
  have hrec : ∀ n : ℕ, a (n+1) = a n * ((σ₀ + 2*n)/(2*π)) := by
    intro n
    have hne : ((σ₀ : ℂ) + 2 * n) ≠ 0 := fun h => by have := hre n; rw [h] at this; simp at this
    have hstep : ((σ₀:ℂ) + 2 * ((n:ℂ)+1)) = ((σ₀:ℂ) + 2 * n) + 2 := by ring
    have hga := Gammaℝ_add_two hne
    have h1 : ‖((σ₀:ℂ) + 2 * (n:ℂ))‖ = σ₀ + 2*(n:ℝ) := by
      have he : ((σ₀:ℂ) + 2 * (n:ℂ)) = (((σ₀ + 2*(n:ℝ)) : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real]; exact Real.norm_of_nonneg (hposr n).le
    have h3 : ‖((π:ℝ):ℂ)‖ = π := by rw [Complex.norm_real]; exact Real.norm_of_nonneg hπ.le
    simp only [ha]
    push_cast
    rw [hstep, hga,
      show Gammaℝ (↑σ₀ + 2 * ↑n) * (↑σ₀ + 2 * ↑n) / 2 / ↑π
        = Gammaℝ (↑σ₀ + 2 * ↑n) * ((↑σ₀ + 2 * ↑n) / 2 / ↑π) by ring, norm_mul]
    congr 1
    rw [norm_div, norm_div, h1, h3, show ‖(2:ℂ)‖ = 2 by norm_num, div_div]
  have hdouble : ∀ n, 2 * a n ≤ a (n+1) := by
    intro n
    rw [hrec n]
    have hfac : (2:ℝ) ≤ (σ₀ + 2*n)/(2*π) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hσ]
    nlinarith [hpos n]
  have hgeom : ∀ n, 2^n * a 0 ≤ a n := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      calc 2^(k+1) * a 0 = 2 * (2^k * a 0) := by ring
        _ ≤ 2 * a k := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) k, hpos 0]
        _ ≤ a (k+1) := hdouble k
  apply tendsto_atTop_mono hgeom
  apply Tendsto.atTop_mul_const (hpos 0)
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-! ### §2 `ζ(σ) ≥ 1` on the real axis -/

/-- `1 ≤ Re ζ(σ)` for real `σ > 1`: the `n = 1` term of the Dirichlet series is `1` and all terms are
nonnegative reals. -/
theorem one_le_re_riemannZeta_ofReal (σ : ℝ) (h : 1 < σ) : (1:ℝ) ≤ (riemannZeta (σ:ℂ)).re := by
  have hs : (1:ℝ) < ((σ:ℂ)).re := by simpa using h
  have hσ0 : (σ:ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hsum : Summable (fun n : ℕ => 1 / (n:ℂ)^(σ:ℂ)) := summable_one_div_nat_cpow.mpr h
  have hz : riemannZeta (σ:ℂ) = ∑' n : ℕ, 1 / (n:ℂ)^(σ:ℂ) := zeta_eq_tsum_one_div_nat_cpow hs
  rw [hz, re_tsum hsum]
  have hg0 : ∀ n : ℕ, 0 ≤ (1 / (n:ℂ)^(σ:ℂ)).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Complex.zero_cpow hσ0]
    · have hbase : ((n:ℂ))^(σ:ℂ) = (((n:ℝ)^σ : ℝ) : ℂ) := by
        rw [ofReal_cpow (Nat.cast_nonneg n) σ]; push_cast; ring
      rw [hbase, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity
  have hsumre : Summable (fun n : ℕ => (1 / (n:ℂ)^(σ:ℂ)).re) := hsum.mapL Complex.reCLM
  have h1 : (1 / ((1:ℕ):ℂ)^(σ:ℂ)).re = 1 := by simp [Complex.one_cpow]
  have hle := Summable.le_tsum hsumre 1 (fun j _ => hg0 j)
  rwa [h1] at hle

/-! ### §3 `ξ = ½·s(s−1)·Λ`, and `ξ` grows on the real axis -/

/-- Off the poles `{0, 1}`, the entire completion equals `½·s(s−1)` times the meromorphic completed
zeta: `ξ(s) = ½·s(s−1)·Λ(s)`. -/
theorem xi_eq_half_mul_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s :=
  xi_eq_half_mul h0 h1

/-- `‖ξ(σ₀ + 2n)‖ → ∞` for `σ₀ ≥ 4π`.  With `ξ = ½·s(s−1)·ζ·Γℝ`, the polynomial and `ζ` factors are
`≥ 1` on the real axis, so `‖ξ‖ ≥ ‖Γℝ‖ → ∞`. -/
theorem xi_norm_tendsto_atTop (σ₀ : ℝ) (hσ : 4 * π ≤ σ₀) :
    Tendsto (fun n : ℕ => ‖xi ((σ₀ : ℂ) + 2 * n)‖) atTop atTop := by
  have hπ : 0 < π := Real.pi_pos
  refine tendsto_atTop_mono ?_ (gammaR_norm_tendsto_atTop σ₀ hσ)
  intro n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  set σ : ℝ := σ₀ + 2*n with hσdef
  have hσ1 : 1 < σ := by nlinarith [Real.pi_gt_three]
  have hσ2 : 2 ≤ σ := by nlinarith [Real.pi_gt_three]
  have hcast : ((σ₀ : ℂ) + 2 * (n:ℂ)) = (σ:ℂ) := by rw [hσdef]; push_cast; ring
  rw [hcast]
  have h0 : (σ:ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have h1 : (σ:ℂ) ≠ 1 := by
    rw [← Complex.ofReal_one]; simp only [ne_eq, Complex.ofReal_inj]; linarith
  have hre : (0:ℝ) < (σ:ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hLam : completedRiemannZeta (σ:ℂ) = riemannZeta (σ:ℂ) * Gammaℝ (σ:ℂ) := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp [Gammaℝ_ne_zero_of_re_pos hre]
  rw [xi_eq_half_mul_completed h0 h1, hLam,
    show (σ:ℂ)*((σ:ℂ)-1)/2 * (riemannZeta (σ:ℂ) * Gammaℝ (σ:ℂ))
      = ((σ:ℂ)*((σ:ℂ)-1)/2 * riemannZeta (σ:ℂ)) * Gammaℝ (σ:ℂ) by ring, norm_mul]
  have hcoef : (1:ℝ) ≤ ‖(σ:ℂ)*((σ:ℂ)-1)/2 * riemannZeta (σ:ℂ)‖ := by
    rw [norm_mul]
    have hz : (1:ℝ) ≤ ‖riemannZeta (σ:ℂ)‖ :=
      le_trans (one_le_re_riemannZeta_ofReal σ hσ1) (Complex.re_le_norm _)
    have hp : (1:ℝ) ≤ ‖(σ:ℂ)*((σ:ℂ)-1)/2‖ := by
      have he : (σ:ℂ)*((σ:ℂ)-1)/2 = (((σ*(σ-1)/2 : ℝ)):ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_of_nonneg (by nlinarith [hσ2])]
      nlinarith [hσ2]
    nlinarith [norm_nonneg (riemannZeta (σ:ℂ)), norm_nonneg ((σ:ℂ)*((σ:ℂ)-1)/2)]
  nlinarith [norm_nonneg (Gammaℝ (σ:ℂ)), hcoef]

/-! ### §4 ξ has no real period -/

/-- ξ has no positive real period: continuity plus a period would bound `σ ↦ ξ(σ)` on the real axis,
contradicting `xi_norm_tendsto_atTop`. -/
theorem xi_not_real_periodic_pos {τ : ℝ} (hτ : 0 < τ) (hp : ∀ s, xi (s + (τ:ℂ)) = xi s) : False := by
  set F : ℝ → ℂ := fun σ => xi (σ:ℂ) with hF
  have hFper : Function.Periodic F τ := by
    intro σ
    simp only [hF]
    rw [show ((σ+τ : ℝ):ℂ) = (σ:ℂ)+(τ:ℂ) by push_cast; ring]; exact hp _
  have hFcont : Continuous F := xi_differentiable.continuous.comp Complex.continuous_ofReal
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := τ)).exists_bound_of_continuousOn
    hFcont.continuousOn
  have hbound : ∀ σ : ℝ, ‖F σ‖ ≤ M := by
    intro σ
    obtain ⟨y, hy, hFy⟩ := hFper.exists_mem_Ico₀ hτ σ
    rw [hFy]; exact hM y ⟨hy.1, le_of_lt hy.2⟩
  have hgrow : Tendsto (fun n : ℕ => ‖F (4*π + 2*n)‖) atTop atTop := by
    have := xi_norm_tendsto_atTop (4*π) (le_refl _)
    refine this.congr (fun n => ?_)
    simp only [hF]
    rw [show ((4*π + 2*(n:ℝ) : ℝ):ℂ) = ((4*π:ℝ):ℂ) + 2*(n:ℂ) by push_cast; ring]
  obtain ⟨n, hn⟩ := (tendsto_atTop.mp hgrow (M+1)).exists
  exact absurd (hbound (4*π + 2*n)) (by linarith)

/-! ### §5 The unconditional off-line reflection wall -/

/-- The conjugate of a period is a period, via Schwarz reality `ξ(s̄) = ξ(s)⁻`. -/
theorem xi_period_conj {ω : ℂ} (hp : ∀ s, xi (s + ω) = xi s) :
    ∀ s, xi (s + (starRingEnd ℂ) ω) = xi s := by
  intro s
  have e1 : xi ((starRingEnd ℂ) s + ω) = xi ((starRingEnd ℂ) s) := hp _
  have hconj : (starRingEnd ℂ) (s + (starRingEnd ℂ) ω) = (starRingEnd ℂ) s + ω := by
    simp [map_add]
  calc xi (s + (starRingEnd ℂ) ω)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (xi (s + (starRingEnd ℂ) ω))) := (Complex.conj_conj _).symm
    _ = (starRingEnd ℂ) (xi ((starRingEnd ℂ) (s + (starRingEnd ℂ) ω))) := by rw [← xi_conj]
    _ = (starRingEnd ℂ) (xi ((starRingEnd ℂ) s + ω)) := by rw [hconj]
    _ = (starRingEnd ℂ) (xi ((starRingEnd ℂ) s)) := by rw [e1]
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (xi s)) := by rw [xi_conj]
    _ = xi s := Complex.conj_conj _

/-- The sum of two periods is a period. -/
theorem xi_period_add {ω₁ ω₂ : ℂ} (hp1 : ∀ s, xi (s + ω₁) = xi s) (hp2 : ∀ s, xi (s + ω₂) = xi s) :
    ∀ s, xi (s + (ω₁ + ω₂)) = xi s := by
  intro s
  rw [show s + (ω₁ + ω₂) = (s + ω₁) + ω₂ by ring, hp2 (s + ω₁)]
  exact hp1 s

/-- The negation of a period is a period. -/
theorem xi_period_neg {ω : ℂ} (hp : ∀ s, xi (s + ω) = xi s) : ∀ s, xi (s + (-ω)) = xi s := by
  intro s
  have h := hp (s + -ω)
  rw [show s + -ω + ω = s by ring] at h
  exact h.symm

/-- **The reflection rigidity of ξ, unconditional.**  Any reflection `s ↦ b − s` under which ξ is
invariant has `Re b = 1`: its fixed point `b/2` lies on the critical line.  Off the line, the
reflection would combine with the functional equation and Schwarz reality to give ξ a nonzero real
period, which `xi_not_real_periodic_pos` forbids. -/
theorem xi_reflection_center_re_eq_one {b : ℂ} (hb : ∀ s, xi (b - s) = xi s) : b.re = 1 := by
  by_contra hne
  have hper : ∀ s, xi (s + (1 - b)) = xi s := fun s => two_center_symmetry_periodic hb xi_one_sub s
  have hperc : ∀ s, xi (s + (starRingEnd ℂ) (1 - b)) = xi s := xi_period_conj hper
  have hsum : ∀ s, xi (s + ((1 - b) + (starRingEnd ℂ) (1 - b))) = xi s := xi_period_add hper hperc
  set τ : ℝ := 2 - 2 * b.re with hτdef
  have hτ0 : τ ≠ 0 := fun h => hne (by rw [hτdef] at h; linarith)
  have hcast : ((1 - b) + (starRingEnd ℂ) (1 - b)) = (τ:ℂ) := by
    have hre : τ = 2 * (1 - b).re := by
      rw [hτdef]; simp only [Complex.sub_re, Complex.one_re]; ring
    rw [hre]; exact Complex.add_conj (1 - b)
  rw [hcast] at hsum
  rcases lt_or_gt_of_ne hτ0 with hlt | hgt
  · have hsumn : ∀ s, xi (s + ((-τ:ℝ):ℂ)) = xi s := by
      intro s
      have h := xi_period_neg hsum s
      rw [show ((-τ:ℝ):ℂ) = -(τ:ℂ) by push_cast; ring]
      exact h
    exact xi_not_real_periodic_pos (by linarith) hsumn
  · exact xi_not_real_periodic_pos hgt hsum

/-- **The fixed point of any reflection of ξ lies on the critical line.**  `(b/2).re = 1/2` for any
reflection `s ↦ b − s` fixing ξ — the functional equation, ramified at `1/2`, is the only reflection
symmetry ξ possesses, now with no aperiodicity hypothesis. -/
theorem xi_reflection_fixed_point_on_line {b : ℂ} (hb : ∀ s, xi (b - s) = xi s) :
    (b / 2).re = 1 / 2 := by
  rw [Complex.div_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, xi_reflection_center_re_eq_one hb]
  norm_num

end RHTower
