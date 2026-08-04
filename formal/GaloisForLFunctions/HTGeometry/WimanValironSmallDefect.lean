import GaloisForLFunctions.HTGeometry.WimanValironSelection
import GaloisForLFunctions.HTGeometry.WimanValironCleanBound
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics
import GaloisForLFunctions.HTGeometry.CentralIndexDivergence

/-!
# The Wiman--Valiron estimate with a small defect

Everything assembles.  The parameter selection produces admissible data beyond every bound, the
closed form turns the estimate into two explicit powers of the sampling scale, and the asymptotic
comparisons make both powers small compared with the central index.  The result is the
Wiman--Valiron theorem in the form a composition-growth argument uses: for a transcendental entire
function and every `ε > 0`, there are radii beyond every bound at which

  `‖z f'(z)/f(z) - nu(|z|)‖ ≤ ε * nu(|z|)`.

The exponent pair `(α, β)` is free subject to `0 < α < β/2`, `β < 2/3` and `1 + α < 2β` — for
instance `α = 1/4`, `β = 13/20`.
-/

open MeasureTheory Complex Set Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The reciprocal of the sampling window is at most `16 t`. -/
theorem two_div_window_le {t α β : ℝ} (ht1 : 1 ≤ t) (hαβ : α ≤ β) :
    2 / (t ^ (-α) * t ^ β / (8 * t)) ≤ 16 * t := by
  have htpos : (0 : ℝ) < t := by linarith
  have h1 : t ^ (-α) * t ^ β = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  have h2 : t ^ (β - α - 1) * t ^ (1 : ℝ) = t ^ (β - α) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [Real.rpow_one] at h2
  have hH : t ^ (-α) * t ^ β / (8 * t) = t ^ (β - α - 1) / 8 := by
    rw [h1, ← h2]
    field_simp
  have hneg : t ^ (β - α - 1) = (t ^ (1 + α - β))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt htpos)]
    congr 1
    ring
  have hxpos : (0 : ℝ) < t ^ (1 + α - β) := Real.rpow_pos_of_pos htpos _
  have hval : 2 / (t ^ (β - α - 1) / 8) = 16 * t ^ (1 + α - β) := by
    rw [hneg]
    field_simp
    norm_num
  have hpow : t ^ (1 + α - β) ≤ t := by
    have h3 : t ^ (1 + α - β) ≤ t ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    rwa [Real.rpow_one] at h3
  rw [hH, hval]
  linarith

/-- **Wiman--Valiron with a small defect, and a maximum term beating every power of the central
index.**  For a transcendental entire power series, every `ε, ε₂ > 0`, every exponent `dpow` and
every bound `R`, there is a radius `e^y` with `y ≥ R` and a point `z` on that circle at which the
logarithmic derivative differs from the central index by at most `ε` times the central index, and at
which `nu^dpow` is at most `ε₂` times the modulus of the function.  The second conclusion is what
kills the lower-degree terms of an algebraic differential equation, and it needs no finite-order
input: the window itself forces the maximum term to grow by `exp(nu H)`, which beats any power of
`nu`. -/
theorem exists_radius_defect_le_eps
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β / 2) (hβ23 : β < 2 / 3) (hlow : 1 + α < 2 * β)
    {ε ε₂ : ℝ} (hε : 0 < ε) (hε₂ : 0 < ε₂) (dpow : ℕ) (R : ℝ) :
    ∃ y, R ≤ y ∧ ∃ z : ℂ, ‖z‖ = Real.exp y ∧
      maxTerm a (Real.exp y) ≤ ‖coeffFun a z‖ ∧
      ((centralIndex a (Real.exp y) : ℝ)) ^ dpow ≤ ε₂ * ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ ε * (centralIndex a (Real.exp y) : ℝ) := by
  have hβ0 : (0 : ℝ) < β := by linarith
  have hβ1 : β ≤ 1 := by linarith
  have hβα : (0 : ℝ) < β - α := by linarith
  -- the constant floor of the maximum term
  obtain ⟨-, -, hc₀⟩ := exists_maxTerm_eq ha (by norm_num : (0 : ℝ) < 1) hn₀
  -- the eventual parameter conditions
  have htail := eventually_tail_condition hα hβ1 hlow
  have hsmallness := eventually_smallness hα hβ23 hαβ hε
  have hpowexp := eventually_mul_rpow_le_exp_rpow (C := 2 ^ dpow / (ε₂ * maxTerm a 1))
    (c := 1 / 16) (δ := β - α) (p := (dpow : ℝ)) (by norm_num) hβα
  obtain ⟨T₀, hT₀⟩ :=
    eventually_atTop.mp (htail.and (hsmallness.and (hpowexp.and (eventually_ge_atTop (2 : ℝ)))))
  -- a bound beyond which the central index is large
  have hdiv : Tendsto (fun x : ℝ => ((centralIndex a (Real.exp x) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_centralIndex_atTop ha htrans).comp
      Real.tendsto_exp_atTop)
  obtain ⟨R'', hR''⟩ := eventually_atTop.mp (hdiv.eventually_ge_atTop T₀)
  -- the scale rule
  have hpos : ∀ t : ℝ, 1 ≤ t → 0 < t ^ β := fun t ht => Real.rpow_pos_of_pos (by linarith) β
  have hle2 : ∀ t : ℝ, 1 ≤ t → t ^ β ≤ 2 * t := by
    intro t ht
    have h1 : t ^ β ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rw [Real.rpow_one] at h1
    linarith
  have hone : ∀ t : ℝ, 1 ≤ t → 1 ≤ 2 * t ^ β := by
    intro t ht
    have h0 : t ^ (0 : ℝ) ≤ t ^ β := Real.rpow_le_rpow_of_exponent_le ht (le_of_lt hβ0)
    rw [Real.rpow_zero] at h0
    linarith
  obtain ⟨x, d, s, H, L, h, N, hxR', hxd, hH, hs, hN0, hsdef, hHdef, hN2, hN4, hLdef, hhdef,
      hdouble, y, hy, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_selected ha hn₀ hα (fun t : ℝ => t ^ β) hpos hle2 hone
      (max (max R R'') 0)
  subst hsdef
  -- the scale of the selected radius
  have hν0 : (0 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxR'' : R'' ≤ x :=
    le_trans (le_max_right R R'') (le_trans (le_max_left (max R R'') 0) hxR')
  have hx0 : (0 : ℝ) ≤ x := le_trans (le_max_right (max R R'') 0) hxR'
  have hT : T₀ ≤ ((centralIndex a (Real.exp x) : ℕ) : ℝ) := hR'' x hxR''
  have ht2' : T₀ ≤ ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  obtain ⟨htail', hsmall', hpow', ht2⟩ := hT₀ _ ht2'
  have ht1 : (1 : ℝ) ≤ ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have htpos : (0 : ℝ) < ((centralIndex a (Real.exp x) : ℝ)) + 1 := by linarith
  have hs1 : (1 : ℝ) ≤ (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β := by
    have h0 : (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (0 : ℝ)
        ≤ (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β :=
      Real.rpow_le_rpow_of_exponent_le ht1 (le_of_lt hβ0)
    rwa [Real.rpow_zero] at h0
  -- the tail condition in terms of the selected window
  have htailH : (1 + 4 / H) ^ 3
      * Real.exp (-((((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β * H / 2)) ≤ 1 := by
    rw [hHdef]
    exact htail'
  -- the closed form
  have hclean := wiman_valiron_tail_bound_le_clean (N := N)
    (nu := (centralIndex a (Real.exp y) : ℝ)) hs1 hH hLdef hhdef hN2 hN4 (Nat.cast_nonneg _) htailH
  -- the logarithm argument is at most `21 (nu + 1)`
  have hwindow : 2 / H ≤ 16 * (((centralIndex a (Real.exp x) : ℝ)) + 1) := by
    rw [hHdef]
    exact two_div_window_le ht1 (by linarith)
  have hyd : y ≤ d + 2 * H := by
    have h1 := hy.2
    linarith
  have hνy : ((centralIndex a (Real.exp y) : ℝ))
      ≤ ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)) := monotone_centralIndex_exp ha hn₀ hyd
  have hAbound : ((centralIndex a (Real.exp y) : ℝ))
        + 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β + 1 + 2 / H
      ≤ 21 * (((centralIndex a (Real.exp x) : ℝ)) + 1) := by
    have hsharp : (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β
        ≤ ((centralIndex a (Real.exp x) : ℝ)) + 1 := by
      have h1 : (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β
          ≤ (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 hβ1
      rwa [Real.rpow_one] at h1
    linarith
  have hA1 : (1 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℝ))
      + 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β + 1 + 2 / H := by
    have h1 : (0 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (((centralIndex a (Real.exp x) : ℝ)) + 1) ^ β := hpos _ ht1
    have h3 : (0 : ℝ) < 2 / H := by positivity
    linarith
  have hsmallH := hsmall' _ hA1 hAbound
  rw [← hHdef] at hsmallH
  -- the central index only grows
  have hxy : x ≤ y := by
    have h1 := hy.1
    linarith
  have hνxy : ((centralIndex a (Real.exp x) : ℝ)) ≤ ((centralIndex a (Real.exp y) : ℝ)) :=
    monotone_centralIndex_exp ha hn₀ hxy
  have hεmono : ε * ((((centralIndex a (Real.exp x) : ℝ)) + 1) - 1)
      ≤ ε * ((centralIndex a (Real.exp y) : ℝ)) := by
    have heq : (((centralIndex a (Real.exp x) : ℝ)) + 1) - 1
        = ((centralIndex a (Real.exp x) : ℝ)) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hνxy (le_of_lt hε)
  -- the maximum term grows across the window
  have hc0x : maxTerm a 1 ≤ maxTerm a (Real.exp x) :=
    maxTerm_mono ha one_pos (Real.one_le_exp hx0)
  obtain ⟨-, -, hμy0⟩ := exists_maxTerm_eq ha (Real.exp_pos y) hn₀
  have hsub := centralIndex_mul_le_log_maxTerm_exp_sub ha hn₀ hxy
  have hyx : H ≤ y - x := by
    have h1 := hy.1
    linarith
  have hstepν : ((centralIndex a (Real.exp x) : ℝ)) * H
      ≤ ((centralIndex a (Real.exp x) : ℝ)) * (y - x) :=
    mul_le_mul_of_nonneg_left hyx hν0
  have hlogc : Real.log (maxTerm a 1) ≤ Real.log (maxTerm a (Real.exp x)) :=
    Real.log_le_log hc₀ hc0x
  have hgrow : maxTerm a 1 * Real.exp (((centralIndex a (Real.exp x) : ℝ)) * H)
      ≤ maxTerm a (Real.exp y) := by
    have hle : Real.log (maxTerm a 1) + ((centralIndex a (Real.exp x) : ℝ)) * H
        ≤ Real.log (maxTerm a (Real.exp y)) := by linarith
    have hexp := Real.exp_le_exp.mpr hle
    rwa [Real.exp_add, Real.exp_log hc₀, Real.exp_log hμy0] at hexp
  refine ⟨y, ?_, z, hz, hfz, ?_, ?_⟩
  · have h2 : R ≤ x :=
      le_trans (le_max_left R R'') (le_trans (le_max_left (max R R'') 0) hxR')
    have h3 := hy.1
    linarith
  · -- the power of the central index is beaten by the modulus
    have hνy2 : ((centralIndex a (Real.exp y) : ℝ))
        ≤ 2 * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) := by linarith
    have hpowmono : ((centralIndex a (Real.exp y) : ℝ)) ^ dpow
        ≤ (2 * ((((centralIndex a (Real.exp x) : ℝ)) + 1))) ^ dpow := by
      have h0 : (0 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℕ) : ℝ) := Nat.cast_nonneg _
      gcongr
    have hcast : ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ ((dpow : ℕ) : ℝ)
        = ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ dpow := Real.rpow_natCast _ dpow
    rw [hcast] at hpow'
    have hεc : (0 : ℝ) < ε₂ * maxTerm a 1 := by positivity
    have hmul : (2 : ℝ) ^ dpow * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ dpow
        ≤ ε₂ * maxTerm a 1
          * Real.exp (1 / 16 * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ (β - α)) := by
      calc (2 : ℝ) ^ dpow * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ dpow
          = ε₂ * maxTerm a 1 * (2 ^ dpow / (ε₂ * maxTerm a 1)
              * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ dpow) := by
            field_simp
        _ ≤ ε₂ * maxTerm a 1
            * Real.exp (1 / 16 * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ (β - α)) :=
          mul_le_mul_of_nonneg_left hpow' (le_of_lt hεc)
    have hexpmono : Real.exp (1 / 16 * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ (β - α))
        ≤ Real.exp (((centralIndex a (Real.exp x) : ℝ)) * H) := by
      refine Real.exp_le_exp.mpr ?_
      have hwin := sub_one_mul_window_ge (t := (((centralIndex a (Real.exp x) : ℝ)) + 1))
        (α := α) (β := β) ht2
      rw [← hHdef] at hwin
      have heq : (((centralIndex a (Real.exp x) : ℝ)) + 1) - 1
          = ((centralIndex a (Real.exp x) : ℝ)) := by ring
      rw [heq] at hwin
      linarith
    have hfinal2 : (2 * ((((centralIndex a (Real.exp x) : ℝ)) + 1))) ^ dpow
        ≤ ε₂ * maxTerm a (Real.exp y) := by
      have hexpand : (2 * ((((centralIndex a (Real.exp x) : ℝ)) + 1))) ^ dpow
          = (2 : ℝ) ^ dpow * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ dpow := by
        rw [mul_pow]
      rw [hexpand]
      have hchain : ε₂ * maxTerm a 1
          * Real.exp (1 / 16 * ((((centralIndex a (Real.exp x) : ℝ)) + 1)) ^ (β - α))
          ≤ ε₂ * (maxTerm a 1 * Real.exp (((centralIndex a (Real.exp x) : ℝ)) * H)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hexpmono (le_of_lt hεc)
      have h2 : ε₂ * (maxTerm a 1 * Real.exp (((centralIndex a (Real.exp x) : ℝ)) * H))
          ≤ ε₂ * maxTerm a (Real.exp y) := mul_le_mul_of_nonneg_left hgrow (le_of_lt hε₂)
      linarith
    have h3 : ε₂ * maxTerm a (Real.exp y) ≤ ε₂ * ‖coeffFun a z‖ :=
      mul_le_mul_of_nonneg_left hfz (le_of_lt hε₂)
    linarith
  · linarith [hbound, hclean, hsmallH, hεmono]

/-- **The exponent constraints are satisfiable.**  Taking `α = 1/4` and `β = 13/20` discharges all
four, so the estimate holds with no exponent parameters at all. -/
theorem exists_radius_defect_le_eps_of_transcendental
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) {ε ε₂ : ℝ} (hε : 0 < ε) (hε₂ : 0 < ε₂) (dpow : ℕ)
    (R : ℝ) :
    ∃ y, R ≤ y ∧ ∃ z : ℂ, ‖z‖ = Real.exp y ∧
      maxTerm a (Real.exp y) ≤ ‖coeffFun a z‖ ∧
      ((centralIndex a (Real.exp y) : ℝ)) ^ dpow ≤ ε₂ * ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ ε * (centralIndex a (Real.exp y) : ℝ) :=
  exists_radius_defect_le_eps ha hn₀ htrans (α := 1 / 4) (β := 13 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hε₂ dpow R

/-- **The Wiman point also dominates every power of the radius.**  Pushing the bound `R` out makes
the modulus of the function at the selected point exceed any prescribed multiple of any prescribed
power of the radius, so an algebraic differential equation divided by a power of the solution loses
every term of lower total degree. -/
theorem exists_radius_dominates_and_defect_le_eps
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) {ε ε₂ : ℝ} (hε : 0 < ε) (hε₂ : 0 < ε₂)
    (k dpow : ℕ) (C R : ℝ) :
    ∃ y, R ≤ y ∧ ∃ z : ℂ, ‖z‖ = Real.exp y ∧
      C * ‖z‖ ^ k ≤ ‖coeffFun a z‖ ∧
      ((centralIndex a (Real.exp y) : ℝ)) ^ dpow ≤ ε₂ * ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ ε * (centralIndex a (Real.exp y) : ℝ) := by
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp
    ((tendsto_maxTerm_div_pow_atTop ha htrans k).eventually_ge_atTop C)
  obtain ⟨y, hy, z, hz, hfz, hpow, hbound⟩ :=
    exists_radius_defect_le_eps_of_transcendental ha hn₀ htrans hε hε₂ dpow
      (max R (Real.log (max r₀ 1)))
  refine ⟨y, le_trans (le_max_left _ _) hy, z, hz, ?_, hpow, hbound⟩
  have hyge : Real.log (max r₀ 1) ≤ y := le_trans (le_max_right _ _) hy
  have hmax1 : (0 : ℝ) < max r₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hexp : max r₀ 1 ≤ Real.exp y := by
    calc max r₀ 1 = Real.exp (Real.log (max r₀ 1)) := (Real.exp_log hmax1).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hyge
  have hr : r₀ ≤ Real.exp y := le_trans (le_max_left _ _) hexp
  have hdom := hr₀ (Real.exp y) hr
  have hpowpos : (0 : ℝ) < (Real.exp y) ^ k := pow_pos (Real.exp_pos y) k
  rw [le_div_iff₀ hpowpos] at hdom
  rw [hz]
  linarith [hfz, hdom]

end GaloisForLFunctions.HTGeometry
