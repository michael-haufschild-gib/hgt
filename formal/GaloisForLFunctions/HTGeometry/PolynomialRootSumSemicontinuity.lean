import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer

/-!
# Weighted root sums are lower semicontinuous under locally uniform convergence

Let `f ≠ 0` be a complex polynomial and `F n` complex polynomials whose evaluations converge to
`f` locally uniformly on `ℂ`.  For a continuous weight `Ψ ≥ 0`,

`Σ_{roots w of f} Ψ(w) ≤ liminf_n Σ_{roots w of F n} Ψ(w)`;

in particular an eventual bound `Σ_{roots of F n} Ψ ≤ K` passes to the limit
(`sum_roots_le_of_tendstoLocallyUniformly`).

**Proof.**  Fix `ε > 0`.  Around each distinct root `e` of `f` take a disc so small that the discs
are disjoint, `f` has no other zero on the closed disc, and `Ψ ≥ Ψ(e) − ε` on it
(`exists_isolating_discs_weight`).  By the argument principle the approximants eventually have
exactly `mult_e` roots in the disc (`eventually_zeroSumBall_eq_of_tendstoLocallyUniformly`).
Since `Ψ ≥ 0`, the roots outside the discs only add, so
`Σ_{roots of F n} Ψ ≥ Σ_e mult_e (Ψ(e) − ε) = Σ_{roots of f} Ψ − ε·deg f`.
-/

open Polynomial Complex Metric Set Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Isolating discs adapted to a continuous weight.** -/
theorem exists_isolating_discs_weight {B : ℂ[X]} (hB : B ≠ 0) {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℂ → ℝ, ∀ e ∈ B.roots.toFinset,
      0 < r e ∧
      (∀ e' ∈ B.roots.toFinset, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e'))) ∧
      (∀ w ∈ sphere e (r e), B.eval w ≠ 0) ∧
      zeroSumBall (fun y => B.eval y) e (r e) = (B.rootMultiplicity e : ℂ) ∧
      (∀ w ∈ ball e (r e), Ψ e - ε ≤ Ψ w) := by
  classical
  set R := B.roots.toFinset
  obtain ⟨d, hd, hsep⟩ : ∃ d > 0, ∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → d ≤ dist e e' := by
    rcases (R.offDiag).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun e he₁ e' he' hne => ?_⟩
      have : (e, e') ∈ R.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne⟩
      rw [he] at this; simp at this
    · refine ⟨R.offDiag.inf' hne (fun pr => dist pr.1 pr.2), ?_, fun e he₁ e' he' hne' => ?_⟩
      · refine (Finset.lt_inf'_iff hne).mpr fun pr hpr => ?_
        obtain ⟨-, -, hpr⟩ := Finset.mem_offDiag.mp hpr
        exact dist_pos.mpr hpr
      · have hmem : (e, e') ∈ R.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne'⟩
        exact Finset.inf'_le (fun pr : ℂ × ℂ => dist pr.1 pr.2) hmem
  have hcont : ∀ e : ℂ, ∃ δ > 0, ∀ w, dist w e < δ → Ψ e - ε ≤ Ψ w := by
    intro e
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hΨ e ε hε
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := h w hw
    rw [Real.dist_eq, abs_lt] at this
    linarith
  choose δ hδ hδΨ using hcont
  refine ⟨fun e => min (d / 3) (δ e), fun e he => ?_⟩
  have hr : 0 < min (d / 3) (δ e) := lt_min (by linarith) (hδ e)
  have hroot : ∀ w, B.eval w = 0 → w ∈ R := fun w hw =>
    Multiset.mem_toFinset.mpr ((mem_roots hB).mpr hw)
  have honly : ∀ w, dist w e ≤ min (d / 3) (δ e) → B.eval w = 0 → w = e := by
    intro w hw hw0
    by_contra hne
    have := hsep w (hroot w hw0) e he hne
    have h3 : min (d / 3) (δ e) ≤ d / 3 := min_le_left _ _
    linarith
  refine ⟨hr, fun e' he' hne => ?_, fun w hw hw0 => ?_, ?_, fun w hw => ?_⟩
  · refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have := min_le_left (d / 3) (δ e)
    have := min_le_left (d / 3) (δ e')
    linarith
  · have hwe := honly w (le_of_eq (mem_sphere.mp hw)) hw0
    rw [hwe, mem_sphere, dist_self] at hw
    linarith
  · obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hr
      (by linarith : min (d / 3) (δ e) < 2 * min (d / 3) (δ e))
      isOpen_univ (Set.subset_univ _) B.differentiable.differentiableOn (fun w hw hw0 => by
        have hwe := honly w (le_of_eq (mem_sphere.mp hw)) hw0
        rw [hwe, mem_sphere, dist_self] at hw
        linarith)
    have he0 : B.eval e = 0 := (mem_roots hB).mp (Multiset.mem_toFinset.mp he)
    have hZ : Z = {e} := by
      ext w
      rw [Finset.mem_singleton]
      constructor
      · intro hw
        exact honly w (le_of_lt (mem_ball.mp (hZb w hw))) ((hZz w (hZb w hw)).mpr hw)
      · rintro rfl
        exact (hZz w (mem_ball_self hr)).mp he0
    rw [hZs, hZ, Finset.sum_singleton, zeroMult_eval_eq_rootMultiplicity hB]
  · exact hδΨ e w (lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _))

/-- **Lower semicontinuity of weighted root sums.** -/
theorem sum_roots_le_of_tendstoLocallyUniformly {f : ℂ[X]} (hf : f ≠ 0) {F : ℕ → ℂ[X]}
    (hconv : TendstoLocallyUniformly (fun n z => (F n).eval z) (fun z => f.eval z) atTop)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ w, 0 ≤ Ψ w) {K : ℝ}
    (hK : ∀ᶠ n in atTop, ((F n).roots.map Ψ).sum ≤ K) :
    (f.roots.map Ψ).sum ≤ K := by
  classical
  by_contra hcon
  push Not at hcon
  set S := (f.roots.map Ψ).sum
  set c : ℝ := (Multiset.card f.roots : ℝ) + 1
  have hc : 0 < c := by positivity
  set ε := (S - K) / (2 * c)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  obtain ⟨r, hr⟩ := exists_isolating_discs_weight hf hΨ hε
  set R := f.roots.toFinset
  have hev : ∀ e ∈ R, ∀ᶠ n in atTop,
      zeroSumBall (fun z => (F n).eval z) e (r e) = (f.rootMultiplicity e : ℂ) ∧
        ∀ w ∈ sphere e (r e), (F n).eval w ≠ 0 := by
    intro e he
    obtain ⟨hr0, -, hsph, hcount, -⟩ := hr e he
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun n => (F n).differentiable) f.differentiable hconv hr0
      (by linarith : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere f.continuous hconv hr0.le hsph
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  obtain ⟨n, hn, hKn⟩ := (((Filter.eventually_all_finset R).mpr hev).and hK).exists
  -- the approximant's root sum is at least the disc contributions
  have hnonneg : 0 ≤ ((F n).roots.map Ψ).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx; exact hΨ0 w
  rcases R.eq_empty_or_nonempty with hR | hR
  · have hroots : f.roots = 0 := Multiset.toFinset_eq_empty.mp hR
    have : S = 0 := by simp [S, hroots]
    linarith
  obtain ⟨e₀, he₀⟩ := hR
  have hFn : F n ≠ 0 := by
    intro h0
    obtain ⟨hr0, -, -, -, -⟩ := hr e₀ he₀
    have hw : e₀ + (r e₀ : ℂ) ∈ sphere e₀ (r e₀) := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr0]
    exact (hn e₀ he₀).2 _ hw (by rw [h0, eval_zero])
  have hZ : ∀ e ∈ R, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ ρ ∈ Z, (F n).eval ρ = 0) ∧
      ∑ ρ ∈ Z, (F n).roots.count ρ = f.rootMultiplicity e := by
    intro e he
    obtain ⟨hr0, -, -, -, -⟩ := hr e he
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hr0
      (by linarith : r e < 2 * r e) isOpen_univ (Set.subset_univ _)
      (F n).differentiable.differentiableOn (hn e he).2
    refine ⟨Z, hZb, fun ρ hρ => (hZz ρ (hZb ρ hρ)).mpr hρ, ?_⟩
    have h := hZs
    rw [(hn e he).1] at h
    have h' : ((∑ ρ ∈ Z, zeroMult (fun y : ℂ => (F n).eval y) ρ : ℕ) : ℂ) =
        (f.rootMultiplicity e : ℂ) := by push_cast; exact h.symm
    have h'' : ∑ ρ ∈ Z, zeroMult (fun y : ℂ => (F n).eval y) ρ = f.rootMultiplicity e := by
      exact_mod_cast h'
    rw [← h'']
    exact Finset.sum_congr rfl fun ρ _ => by
      rw [count_roots, zeroMult_eval_eq_rootMultiplicity hFn]
  choose! Z hZball hZzero hZcount using hZ
  have hpd : (R : Set ℂ).PairwiseDisjoint Z := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    obtain ⟨-, hdisj, -, -, -⟩ := hr e he
    exact (Set.disjoint_left.mp (hdisj e' he' hne)) (hZball e he z hz) (hZball e' he' z hz')
  have hsub : R.biUnion Z ⊆ (F n).roots.toFinset := by
    intro z hz
    obtain ⟨e, he, hz⟩ := Finset.mem_biUnion.mp hz
    exact Multiset.mem_toFinset.mpr ((mem_roots hFn).mpr (hZzero e he z hz))
  have hlow : ∑ e ∈ R, (f.rootMultiplicity e : ℝ) * (Ψ e - ε) ≤ ((F n).roots.map Ψ).sum := by
    rw [Finset.sum_multiset_map_count]
    calc ∑ e ∈ R, (f.rootMultiplicity e : ℝ) * (Ψ e - ε)
        = ∑ e ∈ R, ∑ ρ ∈ Z e, ((F n).roots.count ρ : ℝ) * (Ψ e - ε) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [← Finset.sum_mul, ← hZcount e he]; push_cast; ring
      _ ≤ ∑ e ∈ R, ∑ ρ ∈ Z e, ((F n).roots.count ρ : ℝ) * Ψ ρ := by
          refine Finset.sum_le_sum fun e he => Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨-, -, -, -, hΨe⟩ := hr e he
          exact mul_le_mul_of_nonneg_left (hΨe ρ (hZball e he ρ hρ)) (by positivity)
      _ = ∑ ρ ∈ R.biUnion Z, ((F n).roots.count ρ : ℝ) * Ψ ρ := (Finset.sum_biUnion hpd).symm
      _ ≤ ∑ ρ ∈ (F n).roots.toFinset, (F n).roots.count ρ • Ψ ρ := by
          rw [Finset.sum_congr rfl fun ρ _ => (nsmul_eq_mul ((F n).roots.count ρ) (Ψ ρ)).symm]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ =>
            nsmul_nonneg (hΨ0 ρ) _
  have hS : S = ∑ e ∈ R, (f.rootMultiplicity e : ℝ) * Ψ e := by
    simp only [S]
    rw [Finset.sum_multiset_map_count]
    exact Finset.sum_congr rfl fun e _ => by rw [count_roots, nsmul_eq_mul]
  have hmult : ∑ e ∈ R, (f.rootMultiplicity e : ℝ) ≤ c := by
    have : ∑ e ∈ R, (f.rootMultiplicity e : ℝ) = (Multiset.card f.roots : ℝ) := by
      rw [← Multiset.toFinset_sum_count_eq]; push_cast
      exact Finset.sum_congr rfl fun e _ => by rw [count_roots]
    simp only [c]; linarith
  have hsplit : ∑ e ∈ R, (f.rootMultiplicity e : ℝ) * (Ψ e - ε) =
      S - ε * ∑ e ∈ R, (f.rootMultiplicity e : ℝ) := by
    rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hεc : ε * c = (S - K) / 2 := by simp only [ε]; field_simp
  have : ε * ∑ e ∈ R, (f.rootMultiplicity e : ℝ) ≤ ε * c := mul_le_mul_of_nonneg_left hmult hε.le
  linarith

end

end GaloisForLFunctions.HTGeometry
