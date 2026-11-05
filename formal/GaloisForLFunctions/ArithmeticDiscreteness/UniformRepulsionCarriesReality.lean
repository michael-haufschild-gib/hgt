import GaloisForLFunctions.ZeroConfigurationGeometry.RealityLeavesOnlyThroughCollision

/-!
# Uniform repulsion carries reality; integral families do not move

The deformation half of the discreteness route, tested in finite dimension.

* **Integral families are constant** (`eq_of_continuousOn_intValued`, `eq_of_continuousOn_intCoeff`).
  A continuous family of polynomials with integer coefficients over a preconnected parameter set is
  constant. An integral structure of bounded degree therefore cannot vary along a continuous
  deformation: integrality produces no repulsion *along a path*.
* **Roots near a real-rooted member are nearly real** (`eventually_abs_im_lt`). If `P t₀` is
  real-rooted of full degree, every complex root of `P t` has `|Im z| < ε` for `t` near `t₀`:
  `|lc| ∏ |z − r| = |P t₀(z) − P t(z)|` is small, while `|z − r| ≥ |Im z|`.
* **Uniform repulsion carries reality** (`splits_of_uniform_repulsion`). Along a continuous real
  family of fixed degree on `[0, 1]`, if `P 0` is real-rooted and distinct complex roots of every
  `P t` stay at distance `≥ d > 0`, every `P t` is real-rooted: a non-real root `z` near reality
  would pair with `z̄` at distance `2|Im z| < d`.
* **Loss of reality forces vanishing separation** (`exists_near_collision_of_not_splits`).

So uniform collide-or-repel along a path is a collision-free statement that needs no integrality,
and an integral path is constant. For the heat path of `ζ` the corresponding statement is the
absence of collisions, i.e. RH.
-/

open Polynomial Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-! ### Integral families are constant -/

/-- An integer-valued continuous function on a preconnected set is constant. -/
theorem eq_of_continuousOn_intValued {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {c : X → ℝ} (hc : ContinuousOn c S)
    (hint : ∀ x ∈ S, ∃ k : ℤ, c x = k) {x y : X} (hx : x ∈ S) (hy : y ∈ S) : c x = c y := by
  have key : ∀ a ∈ S, ∀ b ∈ S, c a < c b → False := by
    intro a ha b hb hlt
    obtain ⟨k, hk⟩ := hint a ha
    obtain ⟨l, hl⟩ := hint b hb
    have hkl : k + 1 ≤ l := by
      have : (k : ℝ) < l := by rw [← hk, ← hl]; exact hlt
      exact Int.add_one_le_of_lt (by exact_mod_cast this)
    have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
    obtain ⟨w, hw, hcw⟩ := hS.intermediate_value ha hb hc
      ⟨(by rw [hk]; linarith : c a ≤ (k : ℝ) + 1 / 2), (by rw [hl]; linarith : (k : ℝ) + 1 / 2 ≤ c b)⟩
    obtain ⟨m, hm⟩ := hint w hw
    have h2 : (2 * m : ℤ) = 2 * k + 1 := by
      have : (2 * (m : ℝ)) = 2 * k + 1 := by rw [← hm, hcw]; ring
      exact_mod_cast this
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x hx y hy h
  · exact key y hy x hx h

/-- **Integral families are constant.** A family of real polynomials with integer coefficients,
each coefficient continuous on a preconnected set `S`, is constant on `S`. -/
theorem eq_of_continuousOn_intCoeff {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {P : X → ℝ[X]} (hc : ∀ j, ContinuousOn (fun t => (P t).coeff j) S)
    (hint : ∀ t ∈ S, ∀ j, ∃ k : ℤ, (P t).coeff j = k) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    P x = P y :=
  Polynomial.ext fun j => eq_of_continuousOn_intValued hS (hc j) (fun t ht => hint t ht j) hx hy

/-! ### Roots near a real-rooted member -/

theorem pow_card_le_prod_norm (s : Multiset ℝ) (z : ℂ) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ r ∈ s, m ≤ ‖z - (r : ℂ)‖) :
    m ^ Multiset.card s ≤ (s.map fun r => ‖z - (r : ℂ)‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ, mul_comm]
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun r hr => h r (Multiset.mem_cons_of_mem hr)) (pow_nonneg hm _) (norm_nonneg _)

theorem aeval_eq_leadingCoeff_mul_prod {p : ℝ[X]} (hp : p.Splits) (z : ℂ) :
    (aeval z p : ℂ) = (p.leadingCoeff : ℂ) * ((p.roots.map fun a : ℝ => z - (a : ℂ)).prod) := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [map_mul, map_multiset_prod, Multiset.map_map]
  simp

/-- A perturbation of the coefficients moves values by at most `(Σ|Δ_j|) max(1,|z|)^n`. -/
theorem norm_aeval_sub_le {p p' : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hp' : p'.natDegree ≤ n)
    (z : ℂ) :
    ‖(aeval z p' : ℂ) - aeval z p‖ ≤
      (∑ j ∈ Finset.range (n + 1), |p'.coeff j - p.coeff j|) * max 1 ‖z‖ ^ n := by
  have hd : (p' - p).natDegree < n + 1 :=
    Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le hp' hp))
  rw [← map_sub, aeval_eq_sum_range' hd, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [norm_smul, norm_pow, coeff_sub, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖z‖ ^ j ≤ max 1 ‖z‖ ^ j := pow_le_pow_left₀ (norm_nonneg z) (le_max_right _ _) j
    _ ≤ max 1 ‖z‖ ^ n := pow_le_pow_right₀ (le_max_left _ _)
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- **Roots near a real-rooted member are nearly real.** -/
theorem eventually_abs_im_lt {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j) {t₀ : ℝ} (hsplit : (P t₀).Splits)
    (hlead : (P t₀).coeff n ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ z : ℂ, (aeval z (P t) : ℂ) = 0 → |z.im| < ε := by
  set p := P t₀ with hp
  have hdegp : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero (hdeg t₀) hlead
  have hc : p.leadingCoeff ≠ 0 := by rw [leadingCoeff, hdegp]; exact hlead
  have hc0 : 0 < |p.leadingCoeff| := abs_pos.mpr hc
  have hcard : Multiset.card p.roots = n := by rw [← hdegp]; exact (splits_iff_card_roots.mp hsplit)
  set ρ : ℝ := 1 + (p.roots.map fun r => |r|).sum with hρ
  have hrρ : ∀ r ∈ p.roots, |r| + 1 ≤ ρ := by
    intro r hr
    have := Multiset.single_le_sum (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx; exact abs_nonneg y) _
      (Multiset.mem_map_of_mem (fun r => |r|) hr)
    linarith
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (p.roots.map fun r => |r|).sum :=
      Multiset.sum_nonneg fun x hx => by obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx; exact abs_nonneg y
    linarith
  set θ : ℝ := min (|p.leadingCoeff| / 2 ^ n) (|p.leadingCoeff| * ε ^ n / (2 * ρ) ^ n) with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) (by positivity)
  set δ : ℝ → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), |(P t).coeff j - p.coeff j| with hδ
  have hδc : Continuous δ :=
    continuous_finsetSum _ fun j _ => ((hcont j).sub continuous_const).abs
  have hδ0 : δ t₀ = 0 := by simp [hδ, hp]
  have hev : ∀ᶠ t in 𝓝 t₀, δ t < θ := by
    have := hδc.continuousAt (x := t₀)
    rw [ContinuousAt, hδ0] at this
    exact this.eventually (gt_mem_nhds hθ0)
  filter_upwards [hev] with t ht z hz
  have hval : ‖(p.leadingCoeff : ℂ)‖ * (p.roots.map fun r => ‖z - (r : ℂ)‖).prod ≤
      δ t * max 1 ‖z‖ ^ n := by
    have h := norm_aeval_sub_le (hdeg t₀) (hdeg t) z
    rw [hz, zero_sub, norm_neg, aeval_eq_leadingCoeff_mul_prod hsplit, norm_mul,
      ZeroConfigurationGeometry.norm_multiset_prod_map, Multiset.map_map] at h
    exact h
  rw [Complex.norm_real, Real.norm_eq_abs] at hval
  have hδt0 : 0 ≤ δ t := Finset.sum_nonneg fun j _ => abs_nonneg _
  by_cases hbig : 2 * ρ ≤ ‖z‖
  · exfalso
    have hz2 : 2 ≤ ‖z‖ := by linarith
    have hzpos : 0 < ‖z‖ := by linarith
    have hlow : (‖z‖ / 2) ^ n ≤ (p.roots.map fun r => ‖z - (r : ℂ)‖).prod := by
      rw [← hcard]
      refine pow_card_le_prod_norm _ z (by positivity) fun r hr => ?_
      have h1 := norm_sub_norm_le z (r : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      have := hrρ r hr
      linarith
    have hmax : max 1 ‖z‖ = ‖z‖ := max_eq_right (by linarith)
    rw [hmax] at hval
    have h3 : |p.leadingCoeff| * (‖z‖ / 2) ^ n ≤ δ t * ‖z‖ ^ n :=
      (mul_le_mul_of_nonneg_left hlow (abs_nonneg _)).trans hval
    rw [div_pow] at h3
    have hzn : 0 < ‖z‖ ^ n := pow_pos hzpos n
    have h4 : |p.leadingCoeff| / 2 ^ n ≤ δ t := by
      rw [div_le_iff₀ (by positivity)]
      have : |p.leadingCoeff| * ‖z‖ ^ n ≤ δ t * 2 ^ n * ‖z‖ ^ n := by
        have h5 := h3
        rw [mul_div_assoc', div_le_iff₀ (by positivity)] at h5
        linarith
      exact le_of_mul_le_mul_right (by linarith) hzn
    have := min_le_left (|p.leadingCoeff| / 2 ^ n) (|p.leadingCoeff| * ε ^ n / (2 * ρ) ^ n)
    linarith
  · push Not at hbig
    have hlow : |z.im| ^ n ≤ (p.roots.map fun r => ‖z - (r : ℂ)‖).prod := by
      rw [← hcard]
      refine pow_card_le_prod_norm _ z (abs_nonneg _) fun r _ => ?_
      have := abs_im_le_norm (z - (r : ℂ))
      rwa [sub_im, ofReal_im, sub_zero] at this
    have hmax : max 1 ‖z‖ ^ n ≤ (2 * ρ) ^ n :=
      pow_le_pow_left₀ (by positivity) (max_le (by linarith) hbig.le) n
    have h3 : |p.leadingCoeff| * |z.im| ^ n ≤ δ t * (2 * ρ) ^ n :=
      ((mul_le_mul_of_nonneg_left hlow (abs_nonneg _)).trans hval).trans
        (mul_le_mul_of_nonneg_left hmax hδt0)
    have hθle : θ ≤ |p.leadingCoeff| * ε ^ n / (2 * ρ) ^ n := min_le_right _ _
    have h4 : δ t * (2 * ρ) ^ n < |p.leadingCoeff| * ε ^ n := by
      have h2ρ : 0 < (2 * ρ) ^ n := by positivity
      have : δ t < |p.leadingCoeff| * ε ^ n / (2 * ρ) ^ n := ht.trans_le hθle
      rwa [lt_div_iff₀ h2ρ] at this
    have h5 : |z.im| ^ n < ε ^ n := by
      have := h3.trans_lt h4
      exact lt_of_mul_lt_mul_left this hc0.le
    exact lt_of_pow_lt_pow_left₀ n hε.le h5

/-! ### Uniform repulsion carries reality -/

theorem aeval_conj_eq (p : ℝ[X]) (z : ℂ) :
    (aeval ((starRingEnd ℂ) z) p : ℂ) = (starRingEnd ℂ) (aeval z p) := by
  have := aeval_algHom_apply (Complex.conjAe.toAlgHom) z p
  simpa using this

/-- Near a real-rooted member the family stays real-rooted, under uniform repulsion. -/
theorem eventually_splits_of_repulsion {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j) {t₀ : ℝ} (hsplit : (P t₀).Splits)
    (hlead : (P t₀).coeff n ≠ 0) {S : Set ℝ} {d : ℝ} (hd : 0 < d)
    (hrep : ∀ t ∈ S, ∀ z w : ℂ, (aeval z (P t) : ℂ) = 0 → (aeval w (P t) : ℂ) = 0 → z ≠ w →
      d ≤ ‖z - w‖) :
    ∀ᶠ t in 𝓝 t₀, t ∈ S → (P t).Splits := by
  filter_upwards [eventually_abs_im_lt hdeg hcont hsplit hlead (half_pos hd)] with t ht htS
  refine HTGeometry.splits_of_forall_complex_root_real n _ (hdeg t) fun z hz => ?_
  by_contra him
  have hzc : (aeval ((starRingEnd ℂ) z) (P t) : ℂ) = 0 := by rw [aeval_conj_eq, hz, map_zero]
  have hne : z ≠ (starRingEnd ℂ) z := fun h => him (conj_eq_iff_im.mp h.symm)
  have h1 := hrep t htS z _ hz hzc hne
  rw [sub_conj, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_two] at h1
  linarith [ht z hz]

/-- **Uniform repulsion carries reality.** Along a continuous family of real polynomials of degree
`≤ n` with nonvanishing `n`-th coefficient on `[0, 1]`, if `P 0` is real-rooted and distinct
complex roots of each `P t`, `t ∈ [0, 1]`, are at distance `≥ d > 0`, then every `P t` is
real-rooted. No integrality is used. -/
theorem splits_of_uniform_repulsion {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) (h0 : (P 0).Splits) {d : ℝ} (hd : 0 < d)
    (hrep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z w : ℂ, (aeval z (P t) : ℂ) = 0 → (aeval w (P t) : ℂ) = 0 →
      z ≠ w → d ≤ ‖z - w‖) :
    ∀ t ∈ Icc (0 : ℝ) 1, (P t).Splits := by
  by_contra hall
  push Not at hall
  obtain ⟨t₁, ht₁, hn₁⟩ := hall
  set N := {t ∈ Icc (0 : ℝ) 1 | ¬ (P t).Splits} with hN
  have hN1 : t₁ ∈ N := ⟨ht₁, hn₁⟩
  have hNb : BddBelow N := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf N with hτ
  have hτ0 : 0 ≤ τ := le_csInf ⟨t₁, hN1⟩ fun t ht => ht.1.1
  have hτ1 : τ ≤ 1 := (csInf_le hNb hN1).trans ht₁.2
  have hbelow : ∀ s ∈ Ico 0 τ, (P s).Splits := fun s hs => by
    by_contra h
    exact absurd (csInf_le hNb ⟨⟨hs.1, by linarith [hs.2]⟩, h⟩) (not_le.mpr hs.2)
  have hτs : (P τ).Splits := by
    rcases hτ0.lt_or_eq with hpos | h
    · have hcl := ZeroConfigurationGeometry.isClosed_splits hdeg hcont hlead
      have hsub : Ico 0 τ ⊆ Icc (0 : ℝ) 1 ∩ {t | (P t).Splits} := fun s hs =>
        ⟨⟨hs.1, by linarith [hs.2]⟩, hbelow s hs⟩
      have hmem : τ ∈ closure (Ico 0 τ) := by
        rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      exact (hcl.closure_subset_iff.mpr hsub hmem).2
    · rw [← h]; exact h0
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_splits_of_repulsion hdeg hcont hτs (hlead τ ⟨hτ0, hτ1⟩) hd hrep)
  have : τ + η ≤ τ := le_csInf ⟨t₁, hN1⟩ fun t ht => by
    by_contra hlt
    push Not at hlt
    have htτ : τ ≤ t := csInf_le hNb ht
    exact ht.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) ht.1)
  linarith

/-- **Loss of reality forces vanishing separation.** If `P 0` is real-rooted and `P 1` is not,
then for every `d > 0` some `P t`, `t ∈ [0, 1]`, has two distinct complex roots closer than `d`. -/
theorem exists_near_collision_of_not_splits {P : ℝ → ℝ[X]} {n : ℕ}
    (hdeg : ∀ t, (P t).natDegree ≤ n) (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) (h0 : (P 0).Splits) (h1 : ¬ (P 1).Splits)
    {d : ℝ} (hd : 0 < d) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ z w : ℂ, (aeval z (P t) : ℂ) = 0 ∧ (aeval w (P t) : ℂ) = 0 ∧ z ≠ w ∧
      ‖z - w‖ < d := by
  by_contra hno
  push Not at hno
  exact h1 (splits_of_uniform_repulsion hdeg hcont hlead h0 hd
    (fun t ht z w hz hw hne => hno t ht z w hz hw hne) 1 ⟨zero_le_one, le_rfl⟩)

end GaloisForLFunctions.ArithmeticDiscreteness
