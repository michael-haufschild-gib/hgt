/-
Crease holonomy: cumulative sign transport of `ξ` along the critical line, and the resulting
ledger evaluation of the per-window equivariant-root obstruction.

On the critical line `s = ½+iτ` the completed object `ξ` is real (functional equation plus Schwarz
reflection coincide there), so where it does not vanish it carries a sign.  Between two anchors the
real restriction changes sign exactly once per odd on-line vanishing order enclosed: the segment
factors as `ξ(linePt τ) = (∏_{τ'} (linePt τ − linePt τ')^{m τ'})·h(linePt τ)` with `h` continuous
and nonvanishing on the segment, the imaginary shift `linePt τ − linePt τ' = (τ−τ')·i` turns the
product into a real amplitude times a constant phase, and each interior zero contributes one sign
flip.  Anchored at the centre `½`, where `ξ` is a strictly positive real (arithmetic of the
coefficients), the sign at height `τ` is therefore `+` exactly when the cumulative on-line order in
`(0, τ)` is even.

Feeding this into the per-window equivariant `2^k`-th root criterion of the boundary loop replaces
its two analytic coordinates by pure ledger data: an equivariant root exists iff `2^k` divides the
enclosed order sum (the deck charge) and the cumulative on-line order up to the window's upper
crossing is even (the seam sign, read off parity).
-/
import GaloisForLFunctions.RHTower.WindingXiCircle
import GaloisForLFunctions.HTGeometry.Peeling
import GaloisForLFunctions.RHTower.SeamSignParity
import GaloisForLFunctions.RHTower.RealRootTower
import GaloisForLFunctions.RHTower.RiemannTower

open Complex

namespace RHTower

/-- The line parametrisation is injective: `linePt τ = ½ + τ·i` has imaginary part `τ`. -/
private theorem linePt_injective : Function.Injective linePt := by
  intro a b h
  have h2 := congrArg Complex.im h
  simpa [linePt, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_im, Complex.ofReal_re] using h2

/-- **Global multi-peeling of `ξ` through a finite set of on-line points.**  For any finite set `zs`
of real heights, `ξ` factors globally as `ξ s = (∏_{τ' ∈ zs} (s − linePt τ')^{ord_{linePt τ'} ξ})·h s`
with `h` entire, nonvanishing at each peeled point `linePt τ'`, and carrying the same vanishing order
as `ξ` at every point off the peeled set.  Iterated single-zero peeling (`exists_peel`); the order
bookkeeping keeps the induction hypotheses alive, and `ξ` has finite order everywhere
(`xi_order_ne_top`). -/
private theorem xi_line_peel_finset (zs : Finset ℝ) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Set.univ ∧
      (∀ τ' ∈ zs, h (linePt τ') ≠ 0) ∧
      (∀ σ : ℂ, (∀ τ' ∈ zs, σ ≠ linePt τ') → analyticOrderAt h σ = analyticOrderAt xi σ) ∧
      (∀ s : ℂ, xi s =
        (∏ τ' ∈ zs, (s - linePt τ') ^ (analyticOrderAt xi (linePt τ')).toNat) * h s) := by
  classical
  induction zs using Finset.induction_on with
  | empty =>
      refine ⟨xi, xi_analyticOnNhd_univ, ?_, ?_, ?_⟩
      · intro τ' hτ'; exact absurd hτ' (Finset.notMem_empty τ')
      · intro σ _; rfl
      · intro s; simp
  | insert ρ s hρs ih =>
      obtain ⟨h₁, hh₁an, hh₁ne, hh₁ord, hh₁fact⟩ := ih
      have hρne : ∀ τ' ∈ s, linePt ρ ≠ linePt τ' := by
        intro τ' hτ' heq
        have hτρ : ρ = τ' := linePt_injective heq
        subst hτρ; exact hρs hτ'
      have hordρ : analyticOrderAt h₁ (linePt ρ) = analyticOrderAt xi (linePt ρ) :=
        hh₁ord (linePt ρ) hρne
      have hm : analyticOrderAt h₁ (linePt ρ)
          = ((analyticOrderAt xi (linePt ρ)).toNat : ℕ∞) := by
        rw [hordρ, ENat.coe_toNat (xi_order_ne_top (linePt ρ))]
      obtain ⟨h₂, hh₂an, hh₂ne, hh₂fact, hh₂ord⟩ :=
        exists_peel isOpen_univ hh₁an (Set.mem_univ (linePt ρ)) hm
      refine ⟨h₂, hh₂an, ?_, ?_, ?_⟩
      · intro τ' hτ'
        rcases Finset.mem_insert.mp hτ' with rfl | hτ's
        · exact hh₂ne
        · have hne : linePt τ' ≠ linePt ρ := (hρne τ' hτ's).symm
          have hord2 : analyticOrderAt h₂ (linePt τ') = analyticOrderAt h₁ (linePt τ') :=
            hh₂ord (linePt τ') (Set.mem_univ _) hne
          have hord2z : analyticOrderAt h₂ (linePt τ') = 0 := by
            rw [hord2, analyticOrderAt_eq_zero.mpr (Or.inr (hh₁ne τ' hτ's))]
          exact (analyticOrderAt_eq_zero.mp hord2z).resolve_left
            (not_not.mpr (hh₂an (linePt τ') (Set.mem_univ _)))
      · intro σ hσ
        have hσρ : σ ≠ linePt ρ := hσ ρ (Finset.mem_insert_self ρ s)
        have hσs : ∀ τ' ∈ s, σ ≠ linePt τ' := fun τ' hτ' => hσ τ' (Finset.mem_insert_of_mem hτ')
        rw [hh₂ord σ (Set.mem_univ _) hσρ, hh₁ord σ hσs]
      · intro s'
        rw [Finset.prod_insert hρs, hh₁fact s', hh₂fact s' (Set.mem_univ _)]
        ring

/-! ### §1 Finiteness of the on-line zeros in a window -/

/-- **The on-line zeros of `ξ` in a height window are finite.**  The vertical segment
`{linePt t | t ∈ [τ₁, τ₂]}` lies in a closed ball, where `ξ` has finitely many zeros
(`xi_zeros_closedBall_finite`); the injective pullback `t ↦ linePt t` transports finiteness to the
height set. -/
theorem xi_line_zeros_finite (τ₁ τ₂ : ℝ) :
    {t ∈ Set.Icc τ₁ τ₂ | xi (linePt t) = 0}.Finite := by
  have hBfin := xi_zeros_closedBall_finite (linePt τ₁) (|τ₂ - τ₁|)
  refine Set.Finite.of_finite_image ?_ (linePt_injective.injOn)
  refine hBfin.subset ?_
  rintro z ⟨t, ⟨htIcc, htz⟩, rfl⟩
  refine ⟨?_, htz⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : linePt t - linePt τ₁ = ((t - τ₁ : ℝ) : ℂ) * I := by
    unfold linePt; rw [Complex.ofReal_sub]; ring
  rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨h1, h2⟩ := htIcc
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - τ₁), abs_of_nonneg (by linarith : (0:ℝ) ≤ τ₂ - τ₁)]
  linarith

/-! ### §2 The on-segment factorisation -/

/-- **On-segment factorisation of `ξ`.**  Given the finite set `zs` of on-line zero heights strictly
inside `(τ₁, τ₂)` and nonvanishing endpoints, `ξ` factors as
`ξ s = (∏_{τ' ∈ zs} (s − linePt τ')^{ord_{linePt τ'} ξ})·h s` for an entire cofactor `h` that is
nonvanishing at every point of the closed segment `{linePt t | t ∈ [τ₁, τ₂]}`.  Off-segment zeros of
`ξ` may remain in `h`; only the on-segment (interior on-line) zeros are peeled. -/
theorem xi_line_multi_peel {τ₁ τ₂ : ℝ} {zs : Finset ℝ}
    (hzs : ∀ τ', τ' ∈ zs ↔ τ' ∈ Set.Ioo τ₁ τ₂ ∧ xi (linePt τ') = 0)
    (hend₁ : xi (linePt τ₁) ≠ 0) (hend₂ : xi (linePt τ₂) ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Set.univ ∧
      (∀ t ∈ Set.Icc τ₁ τ₂, h (linePt t) ≠ 0) ∧
      (∀ s : ℂ, xi s =
        (∏ τ' ∈ zs, (s - linePt τ') ^ (analyticOrderAt xi (linePt τ')).toNat) * h s) := by
  obtain ⟨h, hhan, hhne, hhord, hhfact⟩ := xi_line_peel_finset zs
  refine ⟨h, hhan, ?_, hhfact⟩
  intro t ht
  obtain ⟨htl, htr⟩ := ht
  by_cases hxt : xi (linePt t) = 0
  · by_cases htio : t ∈ Set.Ioo τ₁ τ₂
    · exact hhne t ((hzs t).mpr ⟨htio, hxt⟩)
    · exfalso
      rcases eq_or_lt_of_le htl with hτ1 | hτ1
      · rw [← hτ1] at hxt; exact hend₁ hxt
      · rcases eq_or_lt_of_le htr with hτ2 | hτ2
        · rw [hτ2] at hxt; exact hend₂ hxt
        · exact htio ⟨hτ1, hτ2⟩
  · intro hh0
    apply hxt
    rw [hhfact (linePt t), hh0, mul_zero]

/-! ### §3 Cumulative sign transport -/

/-- **The seam sign reads the cumulative on-line order parity.**  For `0 < τ` with `ξ(linePt τ) ≠ 0`,
the real part of `ξ` at height `τ` is positive iff the cumulative on-line vanishing order in `(0, τ)`
is even.  The sign at height `τ` is transported from the anchor `½`, where `ξ` is a strictly positive
real, and flips once per odd on-line order enclosed (`line_sign_flip_iff_odd_total_order`); reality of
`ξ` on the line makes the endpoint real parts nonzero, so the sign is exactly the parity complement
of the enclosed flips. -/
theorem xi_line_sign_iff_even_cumulative_order {τ : ℝ} (hτ : 0 < τ)
    (hne : xi (linePt τ) ≠ 0) {Z : Finset ℝ}
    (hZ : ∀ t, t ∈ Z ↔ t ∈ Set.Ioo 0 τ ∧ xi (linePt t) = 0) :
    0 < (xi (linePt τ)).re ↔
      Even (∑ τ' ∈ Z, (analyticOrderAt xi (linePt τ')).toNat) := by
  have hl0 : linePt 0 = (((1 : ℝ) / 2 : ℝ) : ℂ) := by unfold linePt; push_cast; ring
  have h0pos : 0 < (xi (linePt 0)).re := by
    rw [hl0]; exact xi_pos_on_real_anchor (by norm_num) (by norm_num)
  have hend0 : xi (linePt 0) ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at h0pos; exact lt_irrefl 0 h0pos
  obtain ⟨h, hhan, hhne, hhfact⟩ :=
    xi_line_multi_peel (τ₁ := 0) (τ₂ := τ) (zs := Z) hZ hend0 hne
  have hreal : ∀ u : ℝ, (xi (linePt u)).im = 0 := fESchwarz_real_on_line xi_fESchwarz
  have hlinePtc : Continuous linePt := by
    unfold linePt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hhcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun x => (hhan x (Set.mem_univ x)).continuousAt
  have hhc : Continuous fun u : ℝ => h (linePt u) := hhcont.comp hlinePtc
  have hflip := line_sign_flip_iff_odd_total_order
    (f := xi) (h := h) (zs := Z) (m := fun τ' => (analyticOrderAt xi (linePt τ')).toNat)
    (τ₁ := 0) (τ₂ := τ) hτ
    (fun τ' hτ'z => Set.mem_Ioo.mp ((hZ τ').mp hτ'z).1)
    (fun u _ => hhfact (linePt u)) hhc hhne (fun u _ => hreal u)
  have hab_iff : (xi (linePt 0)).re * (xi (linePt τ)).re < 0
      ↔ (xi (linePt τ)).re < 0 := by
    constructor
    · intro hab
      rcases mul_neg_iff.mp hab with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact hb
      · exact absurd ha (not_lt.mpr h0pos.le)
    · intro hb; exact mul_neg_of_pos_of_neg h0pos hb
  have hbodd : (xi (linePt τ)).re < 0
      ↔ Odd (∑ τ' ∈ Z, (analyticOrderAt xi (linePt τ')).toNat) := hab_iff.symm.trans hflip
  have hbne : (xi (linePt τ)).re ≠ 0 := fun h0 => hne (Complex.ext h0 (hreal τ))
  constructor
  · intro hpos
    rw [← Nat.not_odd_iff_even, ← hbodd]
    exact not_lt.mpr hpos.le
  · intro heven
    have hnb : ¬ ((xi (linePt τ)).re < 0) :=
      fun hb => (Nat.not_odd_iff_even.mpr heven) (hbodd.mp hb)
    exact lt_of_le_of_ne (not_lt.mp hnb) (Ne.symm hbne)

/-! ### §4 Ledger evaluation of the per-window equivariant-root obstruction -/

/-- **The per-window equivariant `2^k`-root of `ξ` in ledger coordinates.**  For a line-centred window
of radius `r` about `linePt τ₀` with `ξ` nonvanishing on the boundary sphere and at the upper crossing
`linePt (τ₀+r)`, an equivariant `2^k`-th root of the boundary loop exists iff two ledger conditions
hold: `2^k` divides the enclosed order sum `∑_{w} ord_w ξ` (the deck charge, via
`windingNumber_xi_circle`), and the cumulative on-line vanishing order in `(0, τ₀+r)` is even (the seam
sign, via cumulative sign transport).  Both analytic coordinates of `xi_window_equivariant_root_iff`
are thereby replaced by discrete divisor data. -/
theorem xi_window_tower_iff_ledger (τ₀ : ℝ) {r : ℝ} (k : ℕ) (hk : k ≠ 0)
    (hr : 0 < r) (hτ₀ : 0 ≤ τ₀)
    (havoid : ∀ z, ‖z - linePt τ₀‖ = r → xi z ≠ 0)
    (hanchor : xi (linePt (τ₀ + r)) ≠ 0)
    {W : Finset ℂ} {Z : Finset ℝ}
    (hW : ∀ w, w ∈ W ↔ ‖w - linePt τ₀‖ < r ∧ xi w = 0)
    (hZ : ∀ t, t ∈ Z ↔ t ∈ Set.Ioo 0 (τ₀ + r) ∧ xi (linePt t) = 0) :
    (∃ V : ℝ → ℂ, Continuous V ∧ (∀ θ, V θ ≠ 0) ∧ V 0 = V (2 * Real.pi) ∧
      (∀ θ, V (Real.pi - θ) = (starRingEnd ℂ) (V θ)) ∧
      (∀ θ, (V θ) ^ (2 ^ k) = xi (linePt τ₀ + ↑r * exp (I * ↑θ))))
    ↔ ((2 ^ k : ℤ) ∣ ∑ w ∈ W, ((analyticOrderAt xi w).toNat : ℤ) ∧
        Even (∑ τ' ∈ Z, (analyticOrderAt xi (linePt τ')).toNat)) := by
  have hnv : ∀ θ : ℝ, xi (linePt τ₀ + ↑r * exp (I * ↑θ)) ≠ 0 := by
    intro θ
    refine havoid _ ?_
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, mul_one,
      abs_of_nonneg hr.le]
  have hbase := xi_window_equivariant_root_iff τ₀ k hk hnv
  obtain ⟨t, htmem, htwind⟩ := windingNumber_xi_circle (linePt τ₀) hr havoid
  have htW : t = W := by
    apply Finset.ext; intro w; rw [htmem w, hW w]
  have hτr : 0 < τ₀ + r := by linarith
  have hsign := xi_line_sign_iff_even_cumulative_order (τ := τ₀ + r) hτr hanchor hZ
  rw [hbase, htwind, htW, hsign]

end RHTower
