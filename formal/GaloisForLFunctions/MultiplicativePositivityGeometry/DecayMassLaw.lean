import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass

/-!
# The decay-exponent mass law: boundary forcing without boundary limits

The boundary divisor is a limit; the decay-exponent law needs only one-sided growth bounds. For an
Euler product with nonnegative log-coefficients, `u ↦ log |Z(1 + x + iu)|` is a cosine trace with
nonnegative weights (`Λ(n)/log n · n^{−1−x}`), hence positive definite for every `x > 0`. Write
`L(x) = log(1/x)`. Suppose

* the pole has growth exponent at most `k`: `log |Z(1 + x)| ≤ (k + ε) L(x)` eventually;
* there are no other boundary poles: `log |Z(1 + x + iv)| ≤ ε L(x)` eventually, `v ≠ 0`;
* the height `z` carries decay exponent `α_z ≥ 0`: `log |Z(1 + x + iz)| ≤ (−α_z + ε) L(x)`.

Then (`decay_mass_law`) `Σ_{z ∈ Z} α_z ≤ k/2` for every finite set `Z` of positive heights. No
meromorphic continuation, no existence of boundary limits and no integrality are used: the law is a
statement about boundary decay rates.

* **Hölder barrier** (`holder_barrier`). With a simple pole (`k = 1`) no boundary point decays
  faster than `x^{1/2}`: a nonnegative Euler product whose modulus is Hölder of exponent `θ > 1/2`
  up to `Re s = 1` has no zeros there. The half-zero datum `ζ(s)/√(ζ(s+i)ζ(s−i))` has decay
  exponent exactly `1/2`.
* **Count bound** (`card_decay_zeros_le`). If every zero decays with exponent at least `θ > 0`,
  at most `k/(2θ)` positive heights carry zeros.

For Beurling systems whose integer count has error `O(x / log^γ x)`, `γ > 1`, the zeta function is
Hölder of exponent `γ − 1` up to the line, so each boundary zero decays with exponent at least
`γ − 1`; the barrier gives Beurling's threshold `γ > 3/2 = 1 + 1/2`, and below it at most
`1/(2(γ − 1))` zero heights.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- **The decay-exponent mass law.** -/
theorem decay_mass_law {T : ℝ → ℝ → ℝ} (hT : ∀ x, 0 < x → IsEvenPosDef (T x)) {L : ℝ → ℝ}
    (hL : Tendsto L (𝓝[>] 0) atTop) {k : ℝ}
    (h0 : ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x 0 ≤ (k + ε) * L x)
    (hoff : ∀ v, v ≠ 0 → ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x v ≤ ε * L x)
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) {α : ℝ → ℝ} (hα : ∀ z ∈ Z, 0 ≤ α z)
    (hz : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x z ≤ (-α z + ε) * L x) :
    ∑ z ∈ Z, α z ≤ k / 2 := by
  classical
  set A := ∑ z ∈ Z, α z with hA
  by_contra hcon
  push Not at hcon
  have hA0 : 0 ≤ A := Finset.sum_nonneg hα
  -- A Følner step slow enough that `2(1 − ε')A > k`.
  set ε' := (2 * A - k) / (4 * A) with hε'
  have hApos : 0 < A := by
    by_contra h
    push Not at h
    have : A = 0 := le_antisymm h hA0
    -- then `k < 0`, contradicting the nonnegativity of `T x 0` for large `L`.
    have hk : k < 0 := by linarith
    obtain ⟨x, hx1, hx2, hx3⟩ := ((h0 (-k / 2) (by linarith)).and
      ((hL.eventually (eventually_gt_atTop 0)).and eventually_mem_nhdsWithin)).exists
    have hpd := (hT x (Set.mem_Ioi.mp hx3)).apply_zero_nonneg
    nlinarith [hx1, hx2, hpd]
  have hε'0 : 0 < ε' := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN1, hN⟩ := exists_folner_step Z hε'0
  set F := folnerSet Z N
  have hF : (0 : ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_folnerSet Z hN1⟩
  -- The bound once every difference in `F − F` satisfies its growth condition with `ε`.
  set D := (F ×ˢ F).image fun p => p.1 - p.2
  set ε := (2 * (1 - ε') * A - k) / (2 * (1 + 2 * Z.card + F.card)) with hε
  have hgap : 0 < 2 * (1 - ε') * A - k := by
    rw [hε']
    field_simp
    nlinarith
  have hε0 : 0 < ε := div_pos hgap (by positivity)
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ 0 < L x ∧ T x 0 ≤ (k + ε) * L x ∧
      (∀ z ∈ Z, T x z ≤ (-α z + ε) * L x) ∧
      (∀ v ∈ D, v ≠ 0 → T x v ≤ ε * L x) := by
    refine (eventually_mem_nhdsWithin.mono fun x hx => Set.mem_Ioi.mp hx).and
      ((hL.eventually (eventually_gt_atTop 0)).and
      ((h0 ε hε0).and (((Filter.eventually_all_finset Z).mpr fun z hz' => hz z hz' ε hε0).and
        ((Filter.eventually_all_finset D).mpr fun v _ => ?_))))
    by_cases hv : v = 0
    · exact Eventually.of_forall fun _ h => absurd hv h
    · exact (hoff v hv ε hε0).mono fun _ h _ => h
  obtain ⟨x, hx0, hLx, hT0, hTz, hTv⟩ := hev.exists
  have hpd := hT x hx0
  -- Pointwise bound on the Gram terms.
  have hpt : ∀ a ∈ F, ∀ b ∈ F, T x (a - b) ≤ (if a = b then T x 0 else 0) +
      (if a - b ∈ Z then (-α (a - b) + ε) * L x else 0) +
      (if b - a ∈ Z then (-α (b - a) + ε) * L x else 0) + ε * L x := by
    intro a ha b hb
    have hεL : 0 ≤ ε * L x := mul_nonneg hε0.le hLx.le
    by_cases hab : a = b
    · subst hab
      have h0Z : (0 : ℝ) ∉ Z := fun h => lt_irrefl 0 (hZ 0 h)
      rw [sub_self, if_pos rfl, if_neg h0Z]
      linarith
    · rw [if_neg hab]
      by_cases h1 : a - b ∈ Z
      · have h2 : b - a ∉ Z := fun h => by
          have := hZ _ h
          have := hZ _ h1
          linarith
        rw [if_pos h1, if_neg h2]
        linarith [hTz _ h1]
      · rw [if_neg h1]
        by_cases h2 : b - a ∈ Z
        · rw [if_pos h2, show a - b = -(b - a) by ring, (hT x hx0).even]
          linarith [hTz _ h2]
        · rw [if_neg h2]
          have hmem : a - b ∈ D := Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩,
            rfl⟩
          linarith [hTv _ hmem (sub_ne_zero.mpr hab)]
  have hgram := hpd.sum_finset_nonneg F
  have hsum : ∑ a ∈ F, ∑ b ∈ F, T x (a - b) ≤ ∑ a ∈ F, ∑ b ∈ F,
      ((if a = b then T x 0 else 0) +
        (if a - b ∈ Z then (-α (a - b) + ε) * L x else 0) +
        (if b - a ∈ Z then (-α (b - a) + ε) * L x else 0) + ε * L x) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpt a ha b hb
  have hdiag : ∑ a ∈ F, ∑ b ∈ F, (if a = b then T x 0 else 0) = (F.card : ℝ) * T x 0 := by
    rw [Finset.sum_congr rfl fun a ha => by rw [Finset.sum_ite_eq, if_pos ha],
      Finset.sum_const, nsmul_eq_mul]
  have h1 := sum_sum_ite_mem F Z (fun z => (-α z + ε) * L x)
  have h2 : ∑ a ∈ F, ∑ b ∈ F, (if b - a ∈ Z then (-α (b - a) + ε) * L x else 0) =
      ∑ z ∈ Z, (-α z + ε) * L x * ((F.filter fun y => y + z ∈ F).card : ℝ) := by
    rw [Finset.sum_comm]
    exact sum_sum_ite_mem F Z (fun z => (-α z + ε) * L x)
  have hconst : ∑ a ∈ F, ∑ b ∈ F, ε * L x = (F.card : ℝ) ^ 2 * (ε * L x) := by
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  simp only [Finset.sum_add_distrib] at hsum
  rw [hdiag, h1, h2, hconst] at hsum
  -- Each shift count lies in `[(1 − ε')|F|, |F|]`.
  have hcnt : ∀ z ∈ Z, (-α z + ε) * L x * ((F.filter fun y => y + z ∈ F).card : ℝ) ≤
      L x * (-α z * (1 - ε') * F.card + ε * F.card) := by
    intro z hz'
    set c := ((F.filter fun y => y + z ∈ F).card : ℝ)
    have hlo : (1 - ε') * F.card ≤ c := by linarith [card_shift_mem_ge (N := N) hz']
    have hhi : c ≤ F.card := Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hαz := hα z hz'
    have : (-α z + ε) * c ≤ -α z * (1 - ε') * F.card + ε * F.card := by nlinarith
    nlinarith
  have hZsum := Finset.sum_le_sum hcnt
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_const, nsmul_eq_mul] at hZsum
  have hsimp : ∑ i ∈ Z, -α i = -A := by rw [Finset.sum_neg_distrib]
  rw [hsimp] at hZsum
  -- Assemble: `0 ≤ L |F| (k + ε − 2(1 − ε')A + 2ε|Z| + ε|F|)`.
  have hT0F := mul_le_mul_of_nonneg_left hT0 hF.le
  have e : L x * F.card * (k + ε - 2 * (1 - ε') * A + 2 * ε * Z.card + ε * F.card) =
      F.card * ((k + ε) * L x) + 2 * (L x * (-A * (1 - ε') * F.card + Z.card * (ε * F.card))) +
        (F.card : ℝ) ^ 2 * (ε * L x) := by ring
  have key : 0 ≤ L x * F.card * (k + ε - 2 * (1 - ε') * A + 2 * ε * Z.card + ε * F.card) := by
    rw [e]
    linarith [hgram, hsum, hZsum, hT0F]
  have hpos : 0 < L x * F.card := mul_pos hLx hF
  have key' := (mul_nonneg_iff_of_pos_left hpos).mp key
  have hεval : ε * (1 + 2 * Z.card + F.card) = (2 * (1 - ε') * A - k) / 2 := by
    rw [hε]
    field_simp
  nlinarith

/-- **Hölder barrier.** With a simple pole, no boundary height decays with exponent above `1/2`. -/
theorem holder_barrier {T : ℝ → ℝ → ℝ} (hT : ∀ x, 0 < x → IsEvenPosDef (T x)) {L : ℝ → ℝ}
    (hL : Tendsto L (𝓝[>] 0) atTop)
    (h0 : ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x 0 ≤ (1 + ε) * L x)
    (hoff : ∀ v, v ≠ 0 → ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x v ≤ ε * L x)
    {z θ : ℝ} (hz0 : 0 < z) (hθ : 0 ≤ θ)
    (hz : ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x z ≤ (-θ + ε) * L x) : θ ≤ 1 / 2 := by
  have h := decay_mass_law hT hL h0 hoff (Z := {z}) (by simpa using hz0) (α := fun _ => θ)
    (by simpa using hθ) (by simpa using hz)
  simpa using h

/-- **Count bound.** If every zero decays with exponent at least `θ > 0`, at most `k/(2θ)` positive
heights carry zeros. -/
theorem card_decay_zeros_le {T : ℝ → ℝ → ℝ} (hT : ∀ x, 0 < x → IsEvenPosDef (T x)) {L : ℝ → ℝ}
    (hL : Tendsto L (𝓝[>] 0) atTop) {k : ℝ}
    (h0 : ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x 0 ≤ (k + ε) * L x)
    (hoff : ∀ v, v ≠ 0 → ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x v ≤ ε * L x)
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) {θ : ℝ} (hθ : 0 < θ)
    (hz : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ x in 𝓝[>] 0, T x z ≤ (-θ + ε) * L x) :
    (Z.card : ℝ) * θ ≤ k / 2 := by
  have h := decay_mass_law hT hL h0 hoff hZ (α := fun _ => θ) (fun _ _ => hθ.le) hz
  simpa [Finset.sum_const, nsmul_eq_mul] using h

end GaloisForLFunctions.MultiplicativePositivityGeometry
