import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity
import GaloisForLFunctions.Bottcher.EntireGrowthFromFE

/-!
# task02 §2 — even holomorphic on a disk of radius `>1` extends to an entire function

The analytic core of the connected-case natural-boundary argument.  Its reusable crux is
`exists_analytic_factor_of_even`: an even holomorphic function on `ball 0 R` factors analytically
through squaring on `ball 0 (R²)` (mathlib lacks this).  With it, the Böttcher functional equation
`h(t²)=h(t)²+c·t²` bootstraps a holomorphic `h` on `ball 0 ρ` (`ρ>1`) outward to `ball 0 (ρ²)`,
then — by iteration and gluing — to an entire function, at which point §3 (`EntireGrowthFromFE`)
finishes the classification `c ∈ {0,-2}`.
-/

open Complex Metric Set Filter Topology

namespace Bottcher

/-- **Even analytic factors through squaring.**  If `g` is holomorphic on `ball 0 R` and even there,
then there is a holomorphic `k` on `ball 0 (R²)` with `g z = k (z²)` for `z ∈ ball 0 R`.  Take
`k(s) = g(√s)`; it is holomorphic off `0` (two square-root branches, bridged by evenness) and the
singularity at `0` is removable. -/
theorem exists_analytic_factor_of_even {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (heven : ∀ z ∈ ball 0 R, g (-z) = g z) :
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k (ball 0 (R ^ (2 : ℕ))) ∧ ∀ z ∈ ball 0 R, k (z ^ (2 : ℕ)) = g z := by
  classical
  -- the principal square root
  set sq : ℂ → ℂ := fun s => s ^ ((2 : ℂ)⁻¹) with hsqdef
  have hsq2 : ∀ s : ℂ, (sq s) ^ (2 : ℕ) = s := by
    intro s
    have h := Complex.cpow_nat_inv_pow s (n := 2) two_ne_zero
    rw [Nat.cast_ofNat] at h
    simpa only [hsqdef] using h
  have hnorm_sq : ∀ s : ℂ, ‖sq s‖ ^ (2 : ℕ) = ‖s‖ := by
    intro s; rw [← norm_pow, hsq2]
  have hsq_mem : ∀ s : ℂ, ‖s‖ < R ^ (2 : ℕ) → sq s ∈ ball (0 : ℂ) R := by
    intro s hs
    rw [mem_ball_zero_iff]
    nlinarith [hnorm_sq s, norm_nonneg (sq s), sq_nonneg (‖sq s‖ - R)]
  -- the exponent 1/2 has positive real part
  have hre : (0 : ℝ) < ((2 : ℂ)⁻¹).re := by
    rw [Complex.inv_re]; norm_num [Complex.normSq]
  -- differentiability of k = g ∘ sq at nonzero points
  set k : ℂ → ℂ := fun s => g (sq s) with hkdef
  have hDiff_ne : ∀ s : ℂ, s ≠ 0 → ‖s‖ < R ^ (2 : ℕ) → DifferentiableAt ℂ k s := by
    intro s hs0 hsR
    have hgd : DifferentiableAt ℂ g (sq s) :=
      hg.differentiableAt (isOpen_ball.mem_nhds (hsq_mem s hsR))
    by_cases hsl : s ∈ slitPlane
    · -- principal branch is analytic at s
      have hcpow : DifferentiableAt ℂ sq s := by
        rw [hsqdef]
        exact (Complex.hasStrictDerivAt_cpow_const hsl).hasDerivAt.differentiableAt
      exact hgd.comp s hcpow
    · -- s is a negative real: use the rotated branch  b(w) = I·(-w)^{1/2}
      have hs_re : s.re ≤ 0 ∧ s.im = 0 := by
        simp only [Complex.slitPlane, Set.mem_setOf_eq, not_or, not_lt] at hsl
        exact ⟨hsl.1, not_not.mp hsl.2⟩
      have hsre : s.re < 0 := by
        rcases lt_or_eq_of_le hs_re.1 with h | h
        · exact h
        · exact absurd (Complex.ext (by simp [h]) (by simp [hs_re.2])) hs0
      have hnsl : (-s) ∈ slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; rw [Complex.neg_re]; linarith
      set b : ℂ → ℂ := fun w => Complex.I * (-w) ^ ((2 : ℂ)⁻¹) with hbdef
      have hb2 : ∀ w : ℂ, (b w) ^ (2 : ℕ) = w := by
        intro w
        rw [hbdef, mul_pow, Complex.I_sq]
        have hcp := Complex.cpow_nat_inv_pow (-w) (n := 2) two_ne_zero
        rw [Nat.cast_ofNat] at hcp
        rw [hcp]; ring
      have hbdiff : DifferentiableAt ℂ b s := by
        rw [hbdef]
        have hcpow : DifferentiableAt ℂ (fun u : ℂ => u ^ ((2 : ℂ)⁻¹)) (-s) :=
          (Complex.hasStrictDerivAt_cpow_const hnsl).hasDerivAt.differentiableAt
        exact (hcpow.comp s differentiableAt_id.neg).const_mul Complex.I
      have hgd_b : DifferentiableAt ℂ g (b s) := by
        apply hg.differentiableAt (isOpen_ball.mem_nhds _)
        rw [mem_ball_zero_iff]
        have hnb : ‖b s‖ ^ (2 : ℕ) = ‖s‖ := by rw [← norm_pow, hb2]
        nlinarith [hnb, norm_nonneg (b s), sq_nonneg (‖b s‖ - R)]
      -- k =ᶠ g ∘ b near s
      have hcongr : k =ᶠ[𝓝 s] fun w => g (b w) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hsR)] with w hw
        rw [mem_ball_zero_iff] at hw
        have hsqw : sq w ∈ ball (0 : ℂ) R := hsq_mem w hw
        have hbw : b w ∈ ball (0 : ℂ) R := by
          rw [mem_ball_zero_iff]
          have hnb : ‖b w‖ ^ (2 : ℕ) = ‖w‖ := by rw [← norm_pow, hb2]
          nlinarith [hnb, norm_nonneg (b w), sq_nonneg (‖b w‖ - R)]
        -- (sq w)² = w = (b w)² ⟹ sq w = ± b w
        have hfac : (sq w - b w) * (sq w + b w) = 0 := by
          have h1 := hsq2 w; have h2 := hb2 w; linear_combination h1 - h2
        rcases mul_eq_zero.mp hfac with h | h
        · have : sq w = b w := by linear_combination h
          rw [hkdef]; simp only; rw [this]
        · have : sq w = - b w := by linear_combination h
          rw [hkdef]; simp only [this]
          rw [heven (b w) hbw]
      exact (hgd_b.comp s hbdiff).congr_of_eventuallyEq hcongr
  -- assemble DifferentiableOn on the whole ball
  refine ⟨k, ?_, ?_⟩
  · intro s hs
    rw [mem_ball_zero_iff] at hs
    by_cases hs0 : s = 0
    · subst hs0
      -- removable singularity at 0
      have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ k z := by
        have hmem : ball (0 : ℂ) (R ^ (2 : ℕ)) ∈ 𝓝[≠] (0 : ℂ) :=
          mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (by simpa using by positivity))
        filter_upwards [self_mem_nhdsWithin, hmem] with z hz hzb
        exact hDiff_ne z hz (mem_ball_zero_iff.mp hzb)
      have hcont : ContinuousAt k 0 := by
        have hsqc : ContinuousAt sq 0 := by
          rw [hsqdef]
          exact continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) hre
        have hgc : ContinuousAt g (sq 0) := by
          apply (hg.differentiableAt (isOpen_ball.mem_nhds _)).continuousAt
          rw [mem_ball_zero_iff]
          have : sq 0 = 0 := by rw [hsqdef]; simp [Complex.zero_cpow]
          rw [this]; simpa using hR
        exact hgc.comp hsqc
      exact ((analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hev
        hcont).differentiableAt).differentiableWithinAt
    · exact (hDiff_ne s hs0 hs).differentiableWithinAt
  · intro z hz
    rw [mem_ball_zero_iff] at hz
    -- k(z²) = g(sq(z²)) and sq(z²) = ±z
    have hzsq : ‖z ^ (2 : ℕ)‖ < R ^ (2 : ℕ) := by
      rw [norm_pow]
      nlinarith [norm_nonneg z, hz, hR]
    have hfac : (sq (z ^ (2 : ℕ)) - z) * (sq (z ^ (2 : ℕ)) + z) = 0 := by
      have := hsq2 (z ^ (2 : ℕ)); linear_combination this
    rw [hkdef]; simp only
    rcases mul_eq_zero.mp hfac with h | h
    · have : sq (z ^ (2 : ℕ)) = z := by linear_combination h
      rw [this]
    · have : sq (z ^ (2 : ℕ)) = -z := by linear_combination h
      rw [this, heven z (mem_ball_zero_iff.mpr hz)]

/-- One outward-doubling extension step. -/
theorem even_holo_extension_step {c : ℂ} {ρ : ℝ} (hρ : 1 < ρ) {g : ℂ → ℂ}
    (hgd : DifferentiableOn ℂ g (ball 0 ρ))
    (hge : ∀ z ∈ ball 0 ρ, g (-z) = g z)
    (hgfe : ∀ t ∈ ball 0 1, g (t ^ (2 : ℕ)) = (g t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hg0 : g 0 = 1) :
    ∃ g' : ℂ → ℂ, DifferentiableOn ℂ g' (ball 0 (ρ ^ (2 : ℕ))) ∧
      (∀ z ∈ ball 0 (ρ ^ (2 : ℕ)), g' (-z) = g' z) ∧
      (∀ t ∈ ball 0 1, g' (t ^ (2 : ℕ)) = (g' t) ^ (2 : ℕ) + c * t ^ (2 : ℕ)) ∧
      g' 0 = 1 ∧ EqOn g' g (ball 0 ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hρρ2 : ρ ≤ ρ ^ (2 : ℕ) := by nlinarith
  have hball1 : ball (0 : ℂ) 1 ⊆ ball 0 ρ := ball_subset_ball hρ.le
  -- neg preserves membership in a ball about 0
  have hneg : ∀ {r : ℝ} {z : ℂ}, z ∈ ball (0 : ℂ) r → -z ∈ ball (0 : ℂ) r := by
    intro r z hz; rw [mem_ball_zero_iff] at *; simpa using hz
  -- G = g² + c·id² is even and holomorphic on ball ρ
  set G : ℂ → ℂ := fun t => (g t) ^ (2 : ℕ) + c * t ^ (2 : ℕ) with hGdef
  have hGd : DifferentiableOn ℂ G (ball 0 ρ) :=
    (hgd.pow 2).add ((differentiableOn_const c).mul ((differentiableOn_id).pow 2))
  have hGe : ∀ z ∈ ball 0 ρ, G (-z) = G z := by
    intro z hz; simp only [hGdef]; rw [hge z hz]; ring
  obtain ⟨k, hkd, hkfac⟩ := exists_analytic_factor_of_even hρ0 hGd hGe
  -- k = g on ball 1
  have hkg1 : ∀ s ∈ ball (0 : ℂ) 1, k s = g s := by
    intro s hs
    rw [mem_ball_zero_iff] at hs
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq s (n := 2) (by norm_num)
    have hznorm : ‖z‖ < 1 := by
      have : ‖z‖ ^ (2 : ℕ) = ‖s‖ := by rw [← hz, norm_pow]
      nlinarith [norm_nonneg z, this, hs]
    have hz1 : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; exact hznorm
    have hzρ : z ∈ ball (0 : ℂ) ρ := hball1 hz1
    calc k s = k (z ^ (2 : ℕ)) := by rw [hz]
      _ = G z := hkfac z hzρ
      _ = (g z) ^ (2 : ℕ) + c * z ^ (2 : ℕ) := rfl
      _ = g (z ^ (2 : ℕ)) := (hgfe z hz1).symm
      _ = g s := by rw [hz]
  -- identity theorem: k = g on ball ρ
  have hkA : AnalyticOnNhd ℂ k (ball 0 ρ) :=
    (hkd.mono (ball_subset_ball hρρ2)).analyticOnNhd isOpen_ball
  have hgA : AnalyticOnNhd ℂ g (ball 0 ρ) := hgd.analyticOnNhd isOpen_ball
  have hev0 : k =ᶠ[𝓝 (0 : ℂ)] g :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hkg1
  have hEqOn : EqOn k g (ball 0 ρ) :=
    hkA.eqOn_of_preconnected_of_eventuallyEq hgA (convex_ball 0 ρ).isPreconnected
      (mem_ball_self hρ0) hev0
  refine ⟨k, hkd, ?_, ?_, ?_, hEqOn⟩
  · -- even on ball ρ²
    have hknegd : DifferentiableOn ℂ (fun z => k (-z)) (ball 0 (ρ ^ (2 : ℕ))) :=
      hkd.comp (differentiable_id.neg.differentiableOn) (fun z hz => hneg hz)
    have hkA2 : AnalyticOnNhd ℂ k (ball 0 (ρ ^ (2 : ℕ))) := hkd.analyticOnNhd isOpen_ball
    have hknegA : AnalyticOnNhd ℂ (fun z => k (-z)) (ball 0 (ρ ^ (2 : ℕ))) :=
      hknegd.analyticOnNhd isOpen_ball
    have hkeq_ρ : ∀ z ∈ ball (0 : ℂ) ρ, k (-z) = k z := by
      intro z hz
      rw [hEqOn (hneg hz), hge z hz, hEqOn hz]
    have hev0' : (fun z => k (-z)) =ᶠ[𝓝 (0 : ℂ)] k :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hρ0)) hkeq_ρ
    have : EqOn (fun z => k (-z)) k (ball 0 (ρ ^ (2 : ℕ))) :=
      hknegA.eqOn_of_preconnected_of_eventuallyEq hkA2 (convex_ball 0 (ρ ^ (2 : ℕ))).isPreconnected
        (mem_ball_self (by positivity)) hev0'
    intro z hz; exact this hz
  · -- FE on ball 1
    intro t ht
    have ht2 : t ^ (2 : ℕ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at ht ⊢
      rw [norm_pow]; nlinarith [norm_nonneg t, ht]
    rw [hkg1 t ht, hkg1 (t ^ (2 : ℕ)) ht2]
    exact hgfe t ht
  · -- value at 0
    rw [hEqOn (mem_ball_self hρ0), hg0]

/-- **task02 §2 endpoint.**  If `h` is holomorphic and even on `ball 0 ρ` with `ρ > 1`, satisfies the
Böttcher functional equation on `ball 0 1`, and `h 0 = 1`, then `c ∈ {0, -2}`.  The disk hypothesis
is bootstrapped to an entire even solution (doubling ladder + gluing), and §3 finishes. -/
theorem c_mem_of_even_holo_ball {h : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hhd : DifferentiableOn ℂ h (ball 0 ρ))
    (hhe : ∀ z ∈ ball 0 ρ, h (-z) = h z)
    (hhfe : ∀ t ∈ ball 0 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hh0 : h 0 = 1) :
    c = 0 ∨ c = -2 := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set rn : ℕ → ℝ := fun n => ρ ^ (2 ^ n) with hrndef
  have hrn0 : rn 0 = ρ := by simp [hrndef]
  have hrn_gt1 : ∀ n, 1 < rn n := by
    intro n; simp only [hrndef]
    calc (1 : ℝ) < ρ := hρ
      _ = ρ ^ (1 : ℕ) := (pow_one ρ).symm
      _ ≤ ρ ^ (2 ^ n) := pow_le_pow_right₀ hρ.le Nat.one_le_two_pow
  have hrn_sq : ∀ n, rn (n + 1) = (rn n) ^ (2 : ℕ) := by
    intro n; simp only [hrndef]; rw [pow_succ, pow_mul]
  have hrn_mono : ∀ {m n : ℕ}, m ≤ n → rn m ≤ rn n := by
    intro m n hmn; simp only [hrndef]
    exact pow_le_pow_right₀ hρ.le (Nat.pow_le_pow_right (by norm_num) hmn)
  have hrn_unb : ∀ x : ℝ, ∃ n, x < rn n := by
    intro x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x hρ
    exact ⟨k, by calc x < ρ ^ k := hk
      _ ≤ ρ ^ (2 ^ k) := pow_le_pow_right₀ hρ.le (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = rn k := rfl⟩
  have hball1_sub : ∀ n, ball (0 : ℂ) 1 ⊆ ball 0 (rn n) := fun n => ball_subset_ball (hrn_gt1 n).le
  -- per-level extension of h
  have hlevel : ∀ n, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball 0 (rn n)) ∧ (∀ z ∈ ball 0 (rn n), g (-z) = g z) ∧
      (∀ t ∈ ball 0 1, g (t ^ (2 : ℕ)) = (g t) ^ (2 : ℕ) + c * t ^ (2 : ℕ)) ∧ g 0 = 1 ∧ EqOn g h (ball 0 1) := by
    intro n
    induction n with
    | zero =>
        refine ⟨h, ?_, ?_, hhfe, hh0, fun z _ => rfl⟩
        · rw [hrn0]; exact hhd
        · rw [hrn0]; exact hhe
    | succ n ih =>
        obtain ⟨g, hgd, hge, hgfe, hg0, hgh⟩ := ih
        obtain ⟨g', hg'd, hg'e, hg'fe, hg'0, hEq⟩ :=
          even_holo_extension_step (hrn_gt1 n) hgd hge hgfe hg0
        rw [hrn_sq n]
        exact ⟨g', hg'd, hg'e, hg'fe, hg'0, fun z hz => by rw [hEq (hball1_sub n hz), hgh hz]⟩
  choose gseq hgd hge hgfe hg0 hgh using hlevel
  -- levels agree on the smaller ball
  have hagree : ∀ m n, EqOn (gseq m) (gseq n) (ball 0 (rn (min m n))) := by
    intro m n
    have hAm : AnalyticOnNhd ℂ (gseq m) (ball 0 (rn (min m n))) :=
      ((hgd m).mono (ball_subset_ball (hrn_mono (min_le_left _ _)))).analyticOnNhd isOpen_ball
    have hAn : AnalyticOnNhd ℂ (gseq n) (ball 0 (rn (min m n))) :=
      ((hgd n).mono (ball_subset_ball (hrn_mono (min_le_right _ _)))).analyticOnNhd isOpen_ball
    have hev : gseq m =ᶠ[𝓝 (0 : ℂ)] gseq n :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos))
        (fun z hz => by rw [hgh m hz, hgh n hz])
    exact hAm.eqOn_of_preconnected_of_eventuallyEq hAn (convex_ball 0 (rn (min m n))).isPreconnected
      (mem_ball_self (by linarith [hrn_gt1 (min m n)])) hev
  -- glue into an entire H
  set N : ℂ → ℕ := fun z => Nat.find (hrn_unb ‖z‖) with hNdef
  have hNspec : ∀ z, ‖z‖ < rn (N z) := fun z => Nat.find_spec (hrn_unb ‖z‖)
  set H : ℂ → ℂ := fun z => gseq (N z) z with hHdef
  have hH_eq : ∀ m : ℕ, ∀ z ∈ ball (0 : ℂ) (rn m), H z = gseq m z := by
    intro m z hz
    rw [mem_ball_zero_iff] at hz
    have hNzm : N z ≤ m := Nat.find_min' (hrn_unb ‖z‖) hz
    have hzin : z ∈ ball (0 : ℂ) (rn (min (N z) m)) := by
      rw [min_eq_left hNzm, mem_ball_zero_iff]; exact hNspec z
    exact hagree (N z) m hzin
  -- H is entire
  have hHdiff : Differentiable ℂ H := by
    intro z
    obtain ⟨m, hm⟩ := hrn_unb ‖z‖
    have hzm : z ∈ ball (0 : ℂ) (rn m) := by rw [mem_ball_zero_iff]; exact hm
    have hDon : DifferentiableOn ℂ H (ball 0 (rn m)) :=
      (hgd m).congr (fun w hw => hH_eq m w hw)
    exact hDon.differentiableAt (isOpen_ball.mem_nhds hzm)
  -- H agrees with h on ball ρ = ball (rn 0)
  have hHh : ∀ z ∈ ball (0 : ℂ) ρ, H z = h z := by
    intro z hz
    rw [← hrn0] at hz
    rw [hH_eq 0 z hz]
    -- gseq 0 = h on ball ρ via identity theorem
    have hA0 : AnalyticOnNhd ℂ (gseq 0) (ball 0 ρ) := by
      rw [← hrn0]; exact (hgd 0).analyticOnNhd isOpen_ball
    have hAh : AnalyticOnNhd ℂ h (ball 0 ρ) := hhd.analyticOnNhd isOpen_ball
    have hev : gseq 0 =ᶠ[𝓝 (0 : ℂ)] h :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) (hgh 0)
    exact hA0.eqOn_of_preconnected_of_eventuallyEq hAh (convex_ball 0 ρ).isPreconnected
      (mem_ball_self hρ0) hev (by rw [hrn0] at hz; exact hz)
  -- identity-theorem extension from ball 1 to all of ℂ
  have entire_ext : ∀ {f₁ f₂ : ℂ → ℂ}, Differentiable ℂ f₁ → Differentiable ℂ f₂ →
      (∀ z ∈ ball (0 : ℂ) 1, f₁ z = f₂ z) → ∀ z, f₁ z = f₂ z := by
    intro f₁ f₂ hf₁ hf₂ hfg z
    have hA₁ : AnalyticOnNhd ℂ f₁ univ := hf₁.differentiableOn.analyticOnNhd isOpen_univ
    have hA₂ : AnalyticOnNhd ℂ f₂ univ := hf₂.differentiableOn.analyticOnNhd isOpen_univ
    have hev : f₁ =ᶠ[𝓝 (0 : ℂ)] f₂ :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hfg
    exact hA₁.eqOn_of_preconnected_of_eventuallyEq hA₂ isPreconnected_univ (mem_univ 0) hev
      (mem_univ z)
  have hball1_subρ : ball (0 : ℂ) 1 ⊆ ball 0 ρ := ball_subset_ball hρ.le
  -- H even everywhere
  have hHeven : ∀ z, H (-z) = H z := by
    apply entire_ext (hHdiff.comp differentiable_neg) hHdiff
    intro z hz
    simp only [Function.comp_apply]
    have hzρ : z ∈ ball (0 : ℂ) ρ := hball1_subρ hz
    have hnegρ : -z ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_neg]; rwa [mem_ball_zero_iff] at hzρ
    rw [hHh (-z) hnegρ, hHh z hzρ, hhe z hzρ]
  -- H satisfies the functional equation everywhere
  have hHfe : ∀ z, H (z ^ (2 : ℕ)) = (H z) ^ (2 : ℕ) + c * z ^ (2 : ℕ) := by
    apply entire_ext (hHdiff.comp (differentiable_pow 2))
      ((hHdiff.pow 2).add ((differentiable_const c).mul (differentiable_pow 2)))
    intro z hz
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    have hz2 : z ^ (2 : ℕ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at hz ⊢; rw [norm_pow]; nlinarith [norm_nonneg z, hz]
    rw [hHh (z ^ (2 : ℕ)) (hball1_subρ hz2), hHh z (hball1_subρ hz), hhfe z hz]
  -- H 0 = 1
  have hH0 : H 0 = 1 := by rw [hHh 0 (mem_ball_self hρ0), hh0]
  exact c_mem_of_entire_even_functional_eq' hHdiff hHeven hHfe hH0

end Bottcher
