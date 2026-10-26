import GaloisForLFunctions.MultiplicativePositivityGeometry.CharacterFamilies
import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass

/-!
# The zero-mass law on every abelian group

Let `φ` be an even positive-definite function on an additive commutative group `Γ` with `φ ≤ 0`
off the origin. Then for every finite set `S` of nonzero points (`total_offOrigin_mass_le`)

  `Σ_{p ∈ S} −φ(p) ≤ φ(0)`.

No discreteness, torsion-freeness or rank is assumed. The proof sums the Gram form with unit
coefficients over the Følner sets `F_N = {Σ_{s ∈ S} n_s s : 0 ≤ n_s < N}`, whose sizes grow
polynomially: at a slow step every `p ∈ S` is the difference of at least `(1 − ε)|F_N|` pairs.

Specializations:
* on `ℝ`, symmetric sets `±Z` give the boundary zero-mass law `Σ_{z>0} −D(z) ≤ D(0)/2`;
* on a finite group the bound is attained by `|Γ| δ₀ − 1`;
* **families** (`family_capacity`): on `G × ℝ`, `G` finite, an integer joint divisor with pole
  order `k`, no off-origin pole and zero multiplicities `m(p)` has `Σ_{p ≠ 0} m(p) ≤ k`. A zero at
  `(g, u)` comes with its conjugate `(−g, −u)`; when `2g = 0` and `u = 0` the two coincide. A
  self-conjugate zero costs one unit of pole order and every other zero pair costs two. So odd pole
  order leaves room for exactly one unpaired unit, which is where the exceptional real-character
  zero of a simple pole sits.
-/

open Finset Filter

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {Γ : Type*} [AddCommGroup Γ]

/-- The Følner set `{Σ_{s ∈ S} n_s s : 0 ≤ n_s < N}` in an abelian group. -/
noncomputable def abFolnerSet [DecidableEq Γ] (S : Finset Γ) (N : ℕ) : Finset Γ :=
  (Fintype.piFinset fun _ : S => range N).image fun n => ∑ s : S, n s • (s : Γ)

section Folner

variable [DecidableEq Γ]

theorem card_abFolnerSet_le (S : Finset Γ) (N : ℕ) : (abFolnerSet S N).card ≤ N ^ S.card := by
  unfold abFolnerSet
  refine card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
    Fintype.card_coe]

theorem zero_mem_abFolnerSet (S : Finset Γ) {N : ℕ} (hN : 1 ≤ N) : (0 : Γ) ∈ abFolnerSet S N := by
  unfold abFolnerSet
  refine Finset.mem_image.mpr ⟨fun _ => 0, ?_, by simp⟩
  simp only [Fintype.mem_piFinset, Finset.mem_range]
  intro
  omega

theorem abFolnerSet_mono (S : Finset Γ) (N : ℕ) : abFolnerSet S N ⊆ abFolnerSet S (N + 1) := by
  unfold abFolnerSet
  refine Finset.image_subset_image fun n hn => ?_
  simp only [Fintype.mem_piFinset, Finset.mem_range] at hn ⊢
  intro z
  have := hn z
  omega

theorem add_mem_abFolnerSet {S : Finset Γ} {N : ℕ} {p : Γ} (hp : p ∈ S) {x : Γ}
    (hx : x ∈ abFolnerSet S N) : x + p ∈ abFolnerSet S (N + 1) := by
  unfold abFolnerSet at hx ⊢
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨fun w => n w + if (w : Γ) = p then 1 else 0, ?_, ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_range] at hn ⊢
    intro w
    have := hn w
    split_ifs <;> omega
  · simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨p, hp⟩]
    · simp
    · intro w _ hw
      rw [if_neg fun h => hw (Subtype.ext h)]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- At least `2|F_N| − |F_{N+1}|` points `y ∈ F_N` have `y + p ∈ F_N`. -/
theorem card_abShift_mem_ge {S : Finset Γ} {N : ℕ} {p : Γ} (hp : p ∈ S) :
    2 * ((abFolnerSet S N).card : ℝ) - (abFolnerSet S (N + 1)).card ≤
      ((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := abFolnerSet S N)
    (fun y => y + p ∈ abFolnerSet S N)
  have hbad : ((abFolnerSet S N).filter fun y => ¬ (y + p ∈ abFolnerSet S N)).card ≤
      (abFolnerSet S (N + 1) \ abFolnerSet S N).card := by
    refine Finset.card_le_card_of_injOn (fun y => y + p) (fun y hy => ?_) ?_
    · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      exact ⟨add_mem_abFolnerSet hp hy.1, hy.2⟩
    · intro a _ b _ h
      simpa using h
  have hle : (abFolnerSet S N).card ≤ (abFolnerSet S (N + 1)).card :=
    Finset.card_le_card (abFolnerSet_mono S N)
  have hsd := Finset.card_sdiff_of_subset (abFolnerSet_mono S N)
  have h1 : (((abFolnerSet S N).filter fun y => ¬ (y + p ∈ abFolnerSet S N)).card : ℝ) ≤
      (abFolnerSet S (N + 1)).card - (abFolnerSet S N).card := by
    rw [← Nat.cast_sub hle]
    exact_mod_cast hbad.trans hsd.le
  have h2 : (((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card : ℝ) +
      ((abFolnerSet S N).filter fun y => ¬ (y + p ∈ abFolnerSet S N)).card =
        (abFolnerSet S N).card := by exact_mod_cast hsplit
  linarith

/-- Polynomial growth: some step of the Følner sequence grows by at most `1 + ε`. -/
theorem exists_abFolner_step (S : Finset Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, 1 ≤ N ∧ ((abFolnerSet S (N + 1)).card : ℝ) ≤ (1 + ε) * (abFolnerSet S N).card := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ N : ℕ, (1 + ε) ^ N ≤ ((abFolnerSet S (N + 1)).card : ℝ) := by
    intro N
    induction N with
    | zero =>
      simp only [pow_zero, zero_add]
      exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_abFolnerSet S le_rfl⟩ : 0 < _)
    | succ N ih =>
      have h := hcon (N + 1) (by omega)
      calc (1 + ε) ^ (N + 1) = (1 + ε) * (1 + ε) ^ N := by ring
        _ ≤ (1 + ε) * ((abFolnerSet S (N + 1)).card : ℝ) := by gcongr
        _ ≤ ((abFolnerSet S (N + 1 + 1)).card : ℝ) := h.le
  have hpoly : ∀ N : ℕ, ((abFolnerSet S (N + 1)).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ S.card :=
    fun N => by exact_mod_cast card_abFolnerSet_le S (N + 1)
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt S.card
    (show (1 : ℝ) < 1 + ε by linarith)
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (1 + ε) by positivity))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  have h := hn₀ (n₀ + 1) (by omega)
  rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ] at h
  have h2 : ((n₀ + 1 : ℕ) : ℝ) ^ S.card < (1 + ε) ^ n₀ := by
    have h3 : ((n₀ + 1 : ℕ) : ℝ) ^ S.card * (1 + ε) < (1 + ε) ^ n₀ * (1 + ε) := by linarith
    exact lt_of_mul_lt_mul_right h3 (by linarith)
  linarith [hgrow n₀, hpoly n₀]

end Folner

/-- Pairs differing by `p ∈ S`, counted through `p`. -/
theorem sum_sum_ite_sub_eq [DecidableEq Γ] (F S : Finset Γ) (φ : Γ → ℝ) :
    ∑ x ∈ F, ∑ y ∈ F, (if x - y ∈ S then φ (x - y) else 0) =
      ∑ p ∈ S, φ p * ((F.filter fun y => y + p ∈ F).card : ℝ) := by
  rw [Finset.sum_comm]
  have hinner : ∀ y, ∑ x ∈ F, (if x - y ∈ S then φ (x - y) else 0) =
      ∑ p ∈ S, (if y + p ∈ F then φ p else 0) := by
    intro y
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => x - y) (fun p => y + p) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by simpa using hx.1⟩
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.2, by simpa using hp.1⟩
    · intro x _
      simp
    · intro p _
      simp
    · intro x _
      rfl
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The zero-mass law on an abelian group.** A positive-definite `φ ≤ 0` off the origin has total
mass at most `φ(0)` on every finite set of nonzero points. -/
theorem total_offOrigin_mass_le {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hnp : ∀ p, p ≠ 0 → φ p ≤ 0)
    {S : Finset Γ} (hS : (0 : Γ) ∉ S) : ∑ p ∈ S, -φ p ≤ φ 0 := by
  classical
  set M := ∑ p ∈ S, φ p with hM
  -- Each pair contributes `φ 0`, `φ p` for `p ∈ S`, or something nonpositive.
  have hpt : ∀ x y : Γ, φ (x - y) ≤ (if x = y then φ 0 else 0) +
      (if x - y ∈ S then φ (x - y) else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [hS]
    · rw [if_neg hxy, zero_add]
      split_ifs with h
      · exact le_rfl
      · exact hnp _ (sub_ne_zero.mpr hxy)
  have hgram : ∀ N : ℕ, 0 ≤ ((abFolnerSet S N).card : ℝ) * φ 0 +
      ∑ p ∈ S, φ p * ((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card := by
    intro N
    have h0 := hφ.sum_finset_nonneg (abFolnerSet S N)
    have hle : ∑ x ∈ abFolnerSet S N, ∑ y ∈ abFolnerSet S N, φ (x - y) ≤
        ∑ x ∈ abFolnerSet S N, ∑ y ∈ abFolnerSet S N,
          ((if x = y then φ 0 else 0) + (if x - y ∈ S then φ (x - y) else 0)) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
    have hdiag : ∑ x ∈ abFolnerSet S N, ∑ y ∈ abFolnerSet S N, (if x = y then φ 0 else 0) =
        ((abFolnerSet S N).card : ℝ) * φ 0 := by
      rw [Finset.sum_congr rfl fun x hx => by rw [Finset.sum_ite_eq, if_pos hx],
        Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.sum_add_distrib] at hle
    rw [hdiag, sum_sum_ite_sub_eq] at hle
    linarith
  by_contra hcon
  push Not at hcon
  have hMneg : φ 0 < -M := by
    rw [hM, ← Finset.sum_neg_distrib]
    exact hcon
  have hφ0 := hφ.apply_zero_nonneg
  have hMpos : 0 < -M := by linarith
  set ε := (-M - φ 0) / (2 * (-M)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN1, hN⟩ := exists_abFolner_step S hε0
  have hg := hgram N
  have hFpos : (0 : ℝ) < (abFolnerSet S N).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_abFolnerSet S hN1⟩
  have hcnt : ∀ p ∈ S, φ p * ((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card ≤
      φ p * ((1 - ε) * (abFolnerSet S N).card) := by
    intro p hp
    have hc := card_abShift_mem_ge (N := N) hp
    have hφp := hnp p (fun h => hS (h ▸ hp))
    have : (1 - ε) * ((abFolnerSet S N).card : ℝ) ≤
        ((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card := by linarith
    exact mul_le_mul_of_nonpos_left this hφp
  have hsum : ∑ p ∈ S, φ p * ((abFolnerSet S N).filter fun y => y + p ∈ abFolnerSet S N).card ≤
      (1 - ε) * (abFolnerSet S N).card * M := by
    calc _ ≤ ∑ p ∈ S, φ p * ((1 - ε) * (abFolnerSet S N).card) := Finset.sum_le_sum hcnt
      _ = (1 - ε) * (abFolnerSet S N).card * M := by
        rw [hM, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
  have hmul : 0 ≤ ((abFolnerSet S N).card : ℝ) * (φ 0 + (1 - ε) * M) := by nlinarith
  have h' := (mul_nonneg_iff_of_pos_left hFpos).mp hmul
  have hMne : M ≠ 0 := (by linarith : M < 0).ne
  have e : (1 - ε) * (-M) = (-M + φ 0) / 2 := by
    rw [hε]
    field_simp
    ring
  nlinarith

/-- **Integer capacity.** An integer-valued positive-definite `φ` with `φ(0) = k` and `φ ≤ 0` off
the origin has at most `k` points off the origin in its support. -/
theorem card_offOrigin_support_le {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hnp : ∀ p, p ≠ 0 → φ p ≤ 0)
    (hint : ∀ p, ∃ n : ℤ, φ p = n) {S : Finset Γ} (hS : (0 : Γ) ∉ S)
    (hzero : ∀ p ∈ S, φ p ≠ 0) : (S.card : ℝ) ≤ φ 0 := by
  have hone : ∀ p ∈ S, (1 : ℝ) ≤ -φ p := fun p hp => by
    obtain ⟨n, hn⟩ := hint p
    have hneg : φ p < 0 := lt_of_le_of_ne (hnp p fun h => hS (h ▸ hp)) (hzero p hp)
    rw [hn] at hneg ⊢
    have hn' : n < 0 := by exact_mod_cast hneg
    have : n ≤ -1 := by omega
    have : (n : ℝ) ≤ -1 := by exact_mod_cast this
    linarith
  calc (S.card : ℝ) = ∑ _p ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ S, -φ p := Finset.sum_le_sum hone
    _ ≤ φ 0 := total_offOrigin_mass_le hφ hnp hS

/-- **Finite groups.** The Gram form over the whole group gives `Σ_p φ(p) ≥ 0`; the zero-mass law
is attained by `|Γ| δ₀ − 1`. -/
theorem finite_group_mass_sum [Fintype Γ] {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) :
    0 ≤ ∑ p, φ p := by
  classical
  have h := hφ.sum_finset_nonneg (Finset.univ : Finset Γ)
  have : ∑ x : Γ, ∑ y : Γ, φ (x - y) = Fintype.card Γ * ∑ p, φ p := by
    rw [Finset.sum_comm]
    have hy : ∀ y : Γ, ∑ x : Γ, φ (x - y) = ∑ p, φ p := fun y =>
      Fintype.sum_equiv (Equiv.subRight y) _ _ fun x => rfl
    simp_rw [hy]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [this] at h
  have hpos : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h

/-- **Family capacity.** On `G × ℝ`, a joint divisor with pole order `k`, no off-origin pole and
integer orders has total zero multiplicity at most `k` over all points off the origin; a
self-conjugate point `(h, 0)`, `2h = 0`, is counted once and every other zero together with its
conjugate twice. -/
theorem family_capacity {G : Type*} [AddCommGroup G] {𝒟 : G × ℝ → ℝ} (hD : IsEvenPosDef 𝒟)
    (hnp : ∀ p, p ≠ 0 → 𝒟 p ≤ 0) {S : Finset (G × ℝ)} (hS : (0 : G × ℝ) ∉ S) :
    ∑ p ∈ S, -𝒟 p ≤ 𝒟 0 :=
  total_offOrigin_mass_le hD hnp hS

/-- **Paired versus self-conjugate zeros.** Under the hypotheses of the zero-mass law, a zero at a
point `p` with `p ≠ −p` has order at most `φ(0)/2`, while a zero at a point of order two has order
at most `φ(0)`. -/
theorem zero_order_le_of_pair {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hnp : ∀ q, q ≠ 0 → φ q ≤ 0)
    {p : Γ} (hp : p ≠ 0) :
    (p + p ≠ 0 → 2 * -φ p ≤ φ 0) ∧ (p + p = 0 → -φ p ≤ φ 0) := by
  classical
  constructor
  · intro h2
    have hpn : p ≠ -p := fun h => h2 (by nth_rewrite 2 [h]; exact add_neg_cancel p)
    have hS : (0 : Γ) ∉ ({p, -p} : Finset Γ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hp, fun h => hp (neg_eq_zero.mp h.symm)⟩
    have h := total_offOrigin_mass_le hφ hnp hS
    rw [Finset.sum_pair hpn, hφ.even] at h
    linarith
  · intro _
    have hS : (0 : Γ) ∉ ({p} : Finset Γ) := by simpa using Ne.symm hp
    simpa using total_offOrigin_mass_le hφ hnp hS

end GaloisForLFunctions.MultiplicativePositivityGeometry
