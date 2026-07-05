/-
The arithmetic-germ packaging (MWM lane, W2g — task #137; doc 21 §3).

On `farHalf = {Re s > 1}` ξ is nonvanishing (`xi_ne_zero_of_one_lt_re`, the Euler
side), so analytic `2^k`-th roots of ξ exist there and are unique up to a `2^k`-th
root of unity (`pow_root_unique`). Doc 21 identifies this germ with the Euler-product
binomial Dirichlet series (ζ-dressing of `∏ (1 − p^{−s})^{−1/2^k}`) on `Re s > 1`
[KNOWN, paper register]; banked here is the abstract statement:

* `exists_farHalf_root` — the level-`k` germ exists.
* `rhLadder_iff_germ_extends` — **RH_{2^k} ⟺ every level-`k` root germ on
  `Re s > 1` extends analytically to `Re s > 1/2`**, the extension still a root and
  agreeing with the germ. Each rung of the ladder is a continuation statement about
  one arithmetically-given object: the constraint is continuability across the zero
  field, not any estimate.
-/
import GaloisForLFunctions.RHTower.RootExistence
import GaloisForLFunctions.RHTower.FarFieldAnchor

namespace RHTower

open Complex Metric

/-- The far half-plane `Re s > 1`, where the Euler product converges. -/
def farHalf : Set ℂ := {s : ℂ | 1 < s.re}

theorem mem_farHalf {s : ℂ} : s ∈ farHalf ↔ 1 < s.re := Iff.rfl

theorem isOpen_farHalf : IsOpen farHalf :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_farHalf : Convex ℝ farHalf := convex_halfSpace_re_gt 1

theorem two_mem_farHalf : (2 : ℂ) ∈ farHalf := by
  rw [mem_farHalf]
  norm_num

theorem farHalf_subset_rightHalf : farHalf ⊆ rightHalf := by
  intro s hs
  rw [mem_rightHalf]
  have := mem_farHalf.mp hs
  linarith

/-- **The germ exists at every level**: ξ has an analytic `2^k`-th root on
`Re s > 1` (no hypothesis — this is the Euler side's free gift). -/
theorem exists_farHalf_root (k : ℕ) :
    ∃ g₁, AnalyticOnNhd ℂ g₁ farHalf ∧ ∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s := by
  refine (exists_root_iff_orders_dvd (pow_pos two_pos k) isOpen_farHalf convex_farHalf
    two_mem_farHalf (xi_analyticOnNhd _) xi_two_ne_zero ?_).mpr ?_
  · intro R
    refine Set.Finite.subset Set.finite_empty ?_
    rintro s ⟨⟨hs, -⟩, h0⟩
    exact absurd h0 (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hs))
  · intro ρ hρ h0
    exact absurd h0 (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hρ))

/-- **Ladder ⟺ germ extension.** Level `k` of the RH ladder holds iff every analytic
`2^k`-th root germ of ξ on `Re s > 1` extends to an analytic root on `Re s > 1/2`
agreeing with the germ. -/
theorem rhLadder_iff_germ_extends (k : ℕ) :
    RHLadder k ↔
      ∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
        ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s) ∧
          Set.EqOn g g₁ farHalf := by
  constructor
  · intro hlad g₁ hg₁ hg₁n
    obtain ⟨h, hh, hhn⟩ := (rhLadder_iff_root k).mp hlad
    have hh2 : h 2 ≠ 0 := by
      intro h0
      have h2 := hhn 2 (farHalf_subset_rightHalf two_mem_farHalf)
      rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at h2
      exact xi_two_ne_zero h2.symm
    have hg₁2 : g₁ 2 ≠ 0 := by
      intro h0
      have h2 := hg₁n 2 two_mem_farHalf
      rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at h2
      exact xi_two_ne_zero h2.symm
    set ω : ℂ := h 2 / g₁ 2 with hω
    have hωpow : ω ^ 2 ^ k = 1 := by
      rw [hω, div_pow, hhn 2 (farHalf_subset_rightHalf two_mem_farHalf),
        hg₁n 2 two_mem_farHalf, div_self xi_two_ne_zero]
    have hroot : ∀ s ∈ rightHalf, (ω⁻¹ * h s) ^ 2 ^ k = xi s := by
      intro s hs
      rw [mul_pow, inv_pow, hωpow, inv_one, one_mul, hhn s hs]
    refine ⟨fun s => ω⁻¹ * h s, ?_, hroot, ?_⟩
    · intro s hs
      exact analyticAt_const.mul (hh s hs)
    · refine pow_root_unique (pow_pos two_pos k) isOpen_farHalf
        convex_farHalf.isPreconnected
        (fun s hs => analyticAt_const.mul (hh s (farHalf_subset_rightHalf hs)))
        hg₁ (fun s hs => hroot s (farHalf_subset_rightHalf hs)) hg₁n
        two_mem_farHalf xi_two_ne_zero ?_
      show ω⁻¹ * h 2 = g₁ 2
      rw [hω, inv_div, div_mul_cancel₀ _ hh2]
  · intro hext
    obtain ⟨g₁, hg₁, hg₁n⟩ := exists_farHalf_root k
    obtain ⟨g, hg, hgn, -⟩ := hext g₁ hg₁ hg₁n
    exact (rhLadder_iff_root k).mpr ⟨g, hg, hgn⟩

end RHTower

namespace RHTower

open Complex Metric

/-- **RH iff every dyadic Euler-side germ can be continued.** The far-half
`2^k` roots exist unconditionally from the zero-free Euler side. RH is exactly the
statement that, at every finite dyadic level, these arithmetically given germs
continue to analytic roots on `Re s > 1/2`; no coherence of the continued roots is
assumed. -/
theorem rh_iff_all_farHalf_germs_extend_all_levels :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
        ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s) ∧
          Set.EqOn g g₁ farHalf := by
  constructor
  · intro hRH k
    exact (rhLadder_iff_germ_extends k).mp ((rh_iff_forall_ladder.mp hRH) k)
  · intro hext
    rw [rh_iff_exists_roots_all_two_powers]
    intro k
    obtain ⟨g₁, hg₁, hg₁n⟩ := exists_farHalf_root k
    obtain ⟨g, hg, hgn, -⟩ := hext k g₁ hg₁ hg₁n
    exact ⟨g, hg, hgn⟩

/-- **RH iff one dyadic Euler-side germ continues at each level.** Since the
far-half germ exists unconditionally, the universal germ-extension criterion has a
certificate form: for every `k`, it is enough to exhibit one far-half `2^k` root and
one analytic continuation of it to the right half-plane. -/
theorem rh_iff_exists_farHalf_germ_extension_all_levels :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∃ g₁ g,
        AnalyticOnNhd ℂ g₁ farHalf ∧ (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) ∧
        AnalyticOnNhd ℂ g rightHalf ∧ (∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s) ∧
          Set.EqOn g g₁ farHalf := by
  constructor
  · intro hRH k
    obtain ⟨g₁, hg₁, hg₁n⟩ := exists_farHalf_root k
    obtain ⟨g, hg, hgn, heq⟩ :=
      (rh_iff_all_farHalf_germs_extend_all_levels.mp hRH) k g₁ hg₁ hg₁n
    exact ⟨g₁, g, hg₁, hg₁n, hg, hgn, heq⟩
  · intro hext
    rw [rh_iff_exists_roots_all_two_powers]
    intro k
    obtain ⟨g₁, g, hg₁, hg₁n, hg, hgn, heq⟩ := hext k
    exact ⟨g, hg, hgn⟩

end RHTower
