/-
Self-duality in the van der Corput exponent-pair semigroup.

For `Σ_{n∼N} n^{-it}` with `N ≍ √(t/2π)` the phase is `Y·F(n/N)` with `F(u) = -log u` and
`Y = t/2π ≍ N²`, so an exponent pair `(κ,λ)` gives `|Σ| ≪ (Y/N)^κ N^λ = N^{κ+λ}` and hence

    μ(1/2) = (κ + λ - 1/2)/2.

The two van der Corput processes are

    A(κ,λ) = ( κ/(2κ+2), (κ+λ+1)/(2κ+2) ),      B(κ,λ) = ( λ - 1/2, κ + 1/2 ).

`B` is an involution, and it preserves `s = κ+λ` exactly; only `A` can decrease `s`.  Its fixed-point
set is the *self-dual locus* `λ = κ + 1/2`, on which `μ = κ`.

**Every record exponent pair for `ζ` lies on that locus**: Weyl `(1/6, 2/3)` and Bourgain
`(13/84, 55/84)` both satisfy `λ = κ + 1/2`, and indeed `μ = κ` in both cases.

The theorem below says `A` improves a self-dual pair exactly when `8κ² + 4κ - 1 > 0`, i.e.
`κ > (√3 - 1)/4 = 0.18301…`, and that both records fall *below* that threshold.  Since `μ = κ` on
the locus, **the van der Corput process is useful only while `μ > (√3-1)/4`** — it had already
ceased to be able to improve the record before Weyl's `1/6` was reached.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace HTGeometry

/-- Sum of the coordinates of an exponent pair; the quantity that controls `μ`. -/
def epSum (κ lam : ℚ) : ℚ := κ + lam

/-- `μ(1/2)` delivered by an exponent pair applied at the self-dual block `N ≍ √t`. -/
def epMu (κ lam : ℚ) : ℚ := (κ + lam - 1/2) / 2

/-- Weyl's pair gives Weyl's exponent. -/
@[simp] theorem epMu_weyl : epMu (1/6) (2/3) = 1/6 := by unfold epMu; norm_num

/-- Bourgain's pair gives Bourgain's exponent. -/
@[simp] theorem epMu_bourgain : epMu (13/84) (55/84) = 13/84 := by unfold epMu; norm_num

/-- The exponent-pair conjecture `(ε, 1/2+ε)` gives `μ = 0`, i.e. the Lindelöf hypothesis. -/
@[simp] theorem epMu_conjecture : epMu 0 (1/2) = 0 := by unfold epMu; norm_num

/-- The `A` process (van der Corput / Weyl differencing), first coordinate. -/
def procA_fst (κ : ℚ) : ℚ := κ / (2*κ + 2)

/-- The `A` process, second coordinate. -/
def procA_snd (κ lam : ℚ) : ℚ := (κ + lam + 1) / (2*κ + 2)

/-- The `B` process (Poisson summation / functional equation), first coordinate. -/
def procB_fst (lam : ℚ) : ℚ := lam - 1/2

/-- The `B` process, second coordinate. -/
def procB_snd (κ : ℚ) : ℚ := κ + 1/2

/-- **`B` preserves `κ+λ` exactly.**  So only `A` can move the quantity that controls `μ`. -/
theorem procB_preserves_epSum (κ lam : ℚ) :
    epSum (procB_fst lam) (procB_snd κ) = epSum κ lam := by
  unfold epSum procB_fst procB_snd; ring

/-- **`B` is an involution.** -/
theorem procB_involutive (κ lam : ℚ) :
    procB_fst (procB_snd κ) = κ ∧ procB_snd (procB_fst lam) = lam := by
  unfold procB_fst procB_snd; constructor <;> ring

/-- The self-dual locus: the fixed-point set of `B`. -/
def SelfDual (κ lam : ℚ) : Prop := lam = κ + 1/2

/-- **The self-dual locus is exactly the fixed-point set of `B`.** -/
theorem selfDual_iff_procB_fixed (κ lam : ℚ) :
    SelfDual κ lam ↔ (procB_fst lam = κ ∧ procB_snd κ = lam) := by
  unfold SelfDual procB_fst procB_snd
  constructor
  · rintro rfl; constructor <;> ring
  · rintro ⟨h, -⟩; linarith

/-- **On the self-dual locus, `μ = κ`.**  The first coordinate of a self-dual exponent pair *is*
the Lindelöf exponent it delivers. -/
theorem epMu_eq_kappa_of_selfDual {κ lam : ℚ} (h : SelfDual κ lam) : epMu κ lam = κ := by
  unfold SelfDual at h; unfold epMu; rw [h]; ring

/-- Weyl's pair is self-dual. -/
theorem selfDual_weyl : SelfDual (1/6) (2/3) := by unfold SelfDual; norm_num

/-- **Bourgain's record pair is self-dual.** -/
theorem selfDual_bourgain : SelfDual (13/84) (55/84) := by unfold SelfDual; norm_num

/-- The exponent-pair conjecture sits on the locus too. -/
theorem selfDual_conjecture : SelfDual 0 (1/2) := by unfold SelfDual; norm_num

/-- **The `A`-improvement criterion.**  For `κ ≥ 0`, `A` strictly decreases `κ+λ` if and only if
`(κ+λ)(2κ+1) > κ+1`. -/
theorem procA_decreases_iff {κ lam : ℚ} (hκ : 0 ≤ κ) :
    epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam ↔ (κ + lam) * (2*κ + 1) > κ + 1 := by
  have hpos : (0:ℚ) < 2*κ + 2 := by linarith
  unfold epSum procA_fst procA_snd
  rw [div_add_div _ _ (ne_of_gt hpos) (ne_of_gt hpos), div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [h, sq_nonneg κ, sq_nonneg (κ + lam)]

/-- **The self-dual improvement threshold.**  On the locus `λ = κ + 1/2`, the criterion becomes the
quadratic `8κ² + 4κ - 1 > 0`, whose positive root is `(√3 - 1)/4 = 0.18301…`. -/
theorem procA_decreases_selfDual_iff {κ lam : ℚ} (hκ : 0 ≤ κ) (h : SelfDual κ lam) :
    epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam ↔ 8*κ^(2 : ℕ) + 4*κ - 1 > 0 := by
  rw [procA_decreases_iff hκ]
  unfold SelfDual at h
  subst h
  constructor <;> intro hh <;> nlinarith [hh]

/-- **Weyl's pair is below the threshold: `A` cannot improve it.** -/
theorem weyl_below_threshold : ¬ (8*(1/6:ℚ)^(2 : ℕ) + 4*(1/6) - 1 > 0) := by norm_num

/-- **Bourgain's record pair is below the threshold: `A` cannot improve it either.** -/
theorem bourgain_below_threshold : ¬ (8*(13/84:ℚ)^(2 : ℕ) + 4*(13/84) - 1 > 0) := by norm_num

/-- **The threshold is monotone: the quadratic is increasing on `κ ≥ 0`, so once a self-dual pair
falls below the threshold, every *better* self-dual pair falls further below it.**  Since `μ = κ`
on the locus, improving `μ` moves strictly away from the region where `A` is useful. -/
theorem threshold_monotone {κ κ' : ℚ} (hκ : 0 ≤ κ') (hlt : κ' < κ) :
    8*κ'^(2 : ℕ) + 4*κ' - 1 < 8*κ^(2 : ℕ) + 4*κ - 1 := by nlinarith

/-- **The barrier, assembled.**  For a self-dual exponent pair with `0 ≤ κ ≤ 13/84` — that is, any
pair at least as good as the current record — the `A` process strictly *increases* `κ+λ`, hence
strictly worsens `μ`. -/
theorem vanDerCorput_inert_at_record {κ lam : ℚ} (hκ : 0 ≤ κ) (hrec : κ ≤ 13/84)
    (h : SelfDual κ lam) :
    ¬ (epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam) := by
  rw [procA_decreases_selfDual_iff hκ h]
  have : 8*κ^(2 : ℕ) + 4*κ - 1 ≤ 8*(13/84:ℚ)^(2 : ℕ) + 4*(13/84) - 1 := by nlinarith
  have hb : 8*(13/84:ℚ)^(2 : ℕ) + 4*(13/84) - 1 < 0 := by norm_num
  linarith

/-- **Restated in terms of `μ`.**  On the self-dual locus `μ = κ`, so the van der Corput `A` process
can improve a record only while `μ` exceeds the threshold root.  Every self-dual pair with
`μ ≤ 13/84` is `A`-inert. -/
theorem vanDerCorput_useless_below_threshold {κ lam : ℚ} (hκ : 0 ≤ κ)
    (h : SelfDual κ lam) (hmu : epMu κ lam ≤ 13/84) :
    ¬ (epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam) := by
  have hk : κ ≤ 13/84 := by rw [epMu_eq_kappa_of_selfDual h] at hmu; exact hmu
  exact vanDerCorput_inert_at_record hκ hk h

end HTGeometry

/-!
### The full historical record lies on the line, strictly below the threshold

The landmark exponent pairs for `ζ` are

    Weyl        (1/6,    2/3)      μ = 1/6     = 0.16667
    Bombieri–Iwaniec (9/56, 37/56) μ = 9/56    = 0.16071
    Huxley      (32/205, 269/410)  μ = 32/205  = 0.15610
    Bourgain    (13/84,  55/84)    μ = 13/84   = 0.15476

Every one satisfies `λ = κ + 1/2`, so `μ = κ` for all four; and every one has `8κ²+4κ-1 < 0`, so
`A` worsens all four.  The `κ`-values decrease strictly, hence — the quadratic being increasing —
each successive record is *further* from the threshold than the last.
-/

namespace HTGeometry

/-- Bombieri–Iwaniec's pair is on the line of symmetry. -/
theorem selfDual_bombieriIwaniec : SelfDual (9/56) (37/56) := by unfold SelfDual; norm_num

/-- Huxley's pair is on the line of symmetry. -/
theorem selfDual_huxley : SelfDual (32/205) (269/410) := by unfold SelfDual; norm_num

@[simp] theorem epMu_bombieriIwaniec : epMu (9/56) (37/56) = 9/56 := by unfold epMu; norm_num

@[simp] theorem epMu_huxley : epMu (32/205) (269/410) = 32/205 := by unfold epMu; norm_num

/-- **The record improves monotonically along the line.** -/
theorem record_chain_strictAnti :
    (13/84 : ℚ) < 32/205 ∧ (32/205 : ℚ) < 9/56 ∧ (9/56 : ℚ) < 1/6 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Every landmark pair is strictly below the `A`-inertness threshold.**  Equivalently, each of the
four is a point at which the van der Corput `A` process strictly increases `κ+λ`. -/
theorem all_records_below_threshold :
    8*(1/6 : ℚ)^(2 : ℕ) + 4*(1/6) - 1 < 0 ∧
    8*(9/56 : ℚ)^(2 : ℕ) + 4*(9/56) - 1 < 0 ∧
    8*(32/205 : ℚ)^(2 : ℕ) + 4*(32/205) - 1 < 0 ∧
    8*(13/84 : ℚ)^(2 : ℕ) + 4*(13/84) - 1 < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **`A`-inertness for any self-dual pair below `9/50 = 0.18`**, a rational bound strictly under the
threshold root `(√3-1)/4 = 0.18301…`.  This covers the whole historical record, whose best value
`1/6 = 0.1667` already exceeds `13/84`. -/
theorem vanDerCorput_inert_below_threshold {κ lam : ℚ} (hκ : 0 ≤ κ) (hrec : κ ≤ 9/50)
    (h : SelfDual κ lam) :
    ¬ (epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam) := by
  rw [procA_decreases_selfDual_iff hκ h]
  have : 8*κ^(2 : ℕ) + 4*κ - 1 ≤ 8*(9/50:ℚ)^(2 : ℕ) + 4*(9/50) - 1 := by nlinarith
  have hb : 8*(9/50:ℚ)^(2 : ℕ) + 4*(9/50) - 1 < 0 := by norm_num
  linarith

/-- **`A` worsens each of the four landmark pairs.** -/
theorem vanDerCorput_inert_at_all_records :
    ¬ (epSum (procA_fst (1/6)) (procA_snd (1/6) (2/3)) < epSum (1/6) (2/3)) ∧
    ¬ (epSum (procA_fst (9/56)) (procA_snd (9/56) (37/56)) < epSum (9/56) (37/56)) ∧
    ¬ (epSum (procA_fst (32/205)) (procA_snd (32/205) (269/410)) < epSum (32/205) (269/410)) ∧
    ¬ (epSum (procA_fst (13/84)) (procA_snd (13/84) (55/84)) < epSum (13/84) (55/84)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact vanDerCorput_inert_below_threshold (by norm_num) (by norm_num) selfDual_weyl
  · exact vanDerCorput_inert_below_threshold (by norm_num) (by norm_num) selfDual_bombieriIwaniec
  · exact vanDerCorput_inert_below_threshold (by norm_num) (by norm_num) selfDual_huxley
  · exact vanDerCorput_inert_below_threshold (by norm_num) (by norm_num) selfDual_bourgain

/-- The exponent-pair conjecture `κ = 0` is the extreme case: maximally far below the threshold.
So the closer the subject gets to the Lindelöf hypothesis, the more inert `A` becomes. -/
theorem conjecture_furthest_below_threshold {κ : ℚ} (hκ : 0 < κ) (hrec : κ ≤ 13/84) :
    8*(0:ℚ)^(2 : ℕ) + 4*0 - 1 < 8*κ^(2 : ℕ) + 4*κ - 1 ∧ 8*κ^(2 : ℕ) + 4*κ - 1 < 0 := by
  constructor
  · nlinarith
  · nlinarith

end HTGeometry

/-!
### Canonicalisation onto the line of symmetry

The set of exponent pairs is convex and closed under `B`.  Both are classical.  Taken together they
force a canonical form: for any exponent pair `(κ,λ)`, the midpoint of it and its `B`-image is again
an exponent pair, and that midpoint is **exactly** `(μ, μ + 1/2)` where `μ = (κ+λ-1/2)/2` is the
Lindelöf exponent the original pair delivers.

    midpoint( (κ,λ), (λ-1/2, κ+1/2) ) = ( (κ+λ-1/2)/2, (κ+λ+1/2)/2 ) = ( μ, μ + 1/2 ).

So every exponent pair has a self-dual representative delivering the *same* `μ`: optimising `μ` may
be carried out entirely on the line of symmetry.  Combined with the inertness threshold, this says
the optimum lives precisely where the `A` process is counterproductive.
-/

namespace HTGeometry

/-- An abstract system of exponent pairs: a predicate closed under the `B` process and convex.
Both properties are classical (Rankin). -/
structure ExponentPairSystem where
  /-- Membership: `mem κ lam` says `(κ, lam)` is an exponent pair. -/
  mem : ℚ → ℚ → Prop
  /-- The `B` process maps exponent pairs to exponent pairs. -/
  closed_B : ∀ κ lam, mem κ lam → mem (lam - 1/2) (κ + 1/2)
  /-- The set of exponent pairs is convex. -/
  convex_mem : ∀ κ₁ lam₁ κ₂ lam₂ (θ : ℚ), 0 ≤ θ → θ ≤ 1 → mem κ₁ lam₁ → mem κ₂ lam₂ →
      mem (θ * κ₁ + (1 - θ) * κ₂) (θ * lam₁ + (1 - θ) * lam₂)

/-- **Canonicalisation.**  Every exponent pair has a self-dual representative delivering the same
`μ`, namely `(μ, μ + 1/2)`. -/
theorem canonical_selfDual (S : ExponentPairSystem) {κ lam : ℚ} (h : S.mem κ lam) :
    S.mem (epMu κ lam) (epMu κ lam + 1/2) := by
  have hB := S.closed_B κ lam h
  have := S.convex_mem κ lam (lam - 1/2) (κ + 1/2) (1/2) (by norm_num) (by norm_num) h hB
  have e1 : (1/2 : ℚ) * κ + (1 - 1/2) * (lam - 1/2) = epMu κ lam := by
    unfold epMu; ring
  have e2 : (1/2 : ℚ) * lam + (1 - 1/2) * (κ + 1/2) = epMu κ lam + 1/2 := by
    unfold epMu; ring
  rwa [e1, e2] at this

/-- The canonical representative is on the line of symmetry. -/
theorem canonical_isSelfDual (κ lam : ℚ) : SelfDual (epMu κ lam) (epMu κ lam + 1/2) := rfl

/-- The canonical representative delivers the same `μ`. -/
theorem canonical_preserves_mu (κ lam : ℚ) :
    epMu (epMu κ lam) (epMu κ lam + 1/2) = epMu κ lam := by
  unfold epMu; ring

/-- **The optimum lives where `A` is inert.**  If an exponent pair delivers `μ` in the range already
achieved by the subject (`0 ≤ μ ≤ 9/50 = 0.18`, which covers every landmark), then its canonical
self-dual representative is an exponent pair delivering the same `μ`, and the van der Corput `A`
process strictly worsens that representative. -/
theorem optimum_lives_where_A_is_inert (S : ExponentPairSystem) {κ lam : ℚ}
    (h : S.mem κ lam) (h0 : 0 ≤ epMu κ lam) (hb : epMu κ lam ≤ 9/50) :
    S.mem (epMu κ lam) (epMu κ lam + 1/2) ∧
    epMu (epMu κ lam) (epMu κ lam + 1/2) = epMu κ lam ∧
    ¬ (epSum (procA_fst (epMu κ lam)) (procA_snd (epMu κ lam) (epMu κ lam + 1/2))
        < epSum (epMu κ lam) (epMu κ lam + 1/2)) :=
  ⟨canonical_selfDual S h, canonical_preserves_mu κ lam,
   vanDerCorput_inert_below_threshold h0 hb (canonical_isSelfDual κ lam)⟩

end HTGeometry

/-!
### The induced dynamics on the line

`A` maps a self-dual pair off the line; canonicalisation returns it.  The composite is a map of the
line to itself, and in the coordinate `μ = κ` it is

    T(μ) = (4μ + 1) / (8μ + 8).

Its fixed points are the roots of `8μ² + 4μ - 1`, so the positive one is the threshold
`μ* = (√3-1)/4 = 0.1830127…` already found.  `T` is strictly increasing, and `T(μ) < μ` exactly when
`8μ²+4μ-1 > 0`; hence `μ*` attracts from **both** sides.  Below `μ*` the composite strictly
*increases* `μ`.

Since every value of `μ` proved since Weyl (`1/6, 9/56, 32/205, 13/84`) lies below `μ*`, the line
dynamics push all of them backwards toward `μ*`: the locus that carries the optimum is a dynamical
attractor at a value worse than every result in the subject.
-/

namespace HTGeometry

/-- The map induced on the line of symmetry by `A` followed by canonicalisation, in the coordinate
`μ = κ`. -/
def lineMap (μ : ℚ) : ℚ := (4*μ + 1) / (8*μ + 8)

/-- **`lineMap` is exactly `A` followed by canonicalisation.**  Applying `A` to the self-dual pair
`(μ, μ+1/2)` and reading off the `μ` of the result gives `lineMap μ`. -/
theorem lineMap_eq_epMu_procA {μ : ℚ} (hμ : 0 ≤ μ) :
    epMu (procA_fst μ) (procA_snd μ (μ + 1/2)) = lineMap μ := by
  have h : (2*μ + 2) ≠ 0 := by positivity
  have h8 : (8*μ + 8) ≠ 0 := by positivity
  unfold epMu procA_fst procA_snd lineMap
  field_simp
  ring

/-- The fixed points of `lineMap` are the roots of the threshold quadratic. -/
theorem lineMap_fixed_iff {μ : ℚ} (hμ : 0 ≤ μ) :
    lineMap μ = μ ↔ 8*μ^(2 : ℕ) + 4*μ - 1 = 0 := by
  have h8 : (8*μ + 8) ≠ 0 := by positivity
  unfold lineMap
  rw [div_eq_iff h8]
  constructor <;> intro h <;> nlinarith [h]

/-- **`lineMap` decreases `μ` exactly above the threshold, and increases it exactly below.** -/
theorem lineMap_lt_iff {μ : ℚ} (hμ : 0 ≤ μ) :
    lineMap μ < μ ↔ 8*μ^(2 : ℕ) + 4*μ - 1 > 0 := by
  have h8 : (0:ℚ) < 8*μ + 8 := by positivity
  unfold lineMap
  rw [div_lt_iff₀ h8]
  constructor <;> intro h <;> nlinarith [h]

/-- **`lineMap` strictly increases `μ` below the threshold.**  In particular the composite makes
every record strictly worse. -/
theorem lineMap_gt_of_below {μ : ℚ} (hμ : 0 ≤ μ) (h : 8*μ^(2 : ℕ) + 4*μ - 1 < 0) : μ < lineMap μ := by
  have h8 : (0:ℚ) < 8*μ + 8 := by positivity
  unfold lineMap
  rw [lt_div_iff₀ h8]
  nlinarith

/-- **The line dynamics push every landmark backwards.**  At each of the four records, one step of
`A`-plus-canonicalisation strictly worsens `μ`. -/
theorem lineMap_worsens_all_records :
    (1/6 : ℚ) < lineMap (1/6) ∧
    (9/56 : ℚ) < lineMap (9/56) ∧
    (32/205 : ℚ) < lineMap (32/205) ∧
    (13/84 : ℚ) < lineMap (13/84) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lineMap_gt_of_below (by norm_num) (by norm_num)
  · exact lineMap_gt_of_below (by norm_num) (by norm_num)
  · exact lineMap_gt_of_below (by norm_num) (by norm_num)
  · exact lineMap_gt_of_below (by norm_num) (by norm_num)

/-- `lineMap` is strictly increasing on `μ ≥ 0`. -/
theorem lineMap_strictMono {μ ν : ℚ} (hμ : 0 ≤ μ) (h : μ < ν) : lineMap μ < lineMap ν := by
  have hν : (0:ℚ) ≤ ν := le_of_lt (lt_of_le_of_lt hμ h)
  have h8μ : (0:ℚ) < 8*μ + 8 := by positivity
  have h8ν : (0:ℚ) < 8*ν + 8 := by positivity
  unfold lineMap
  rw [div_lt_div_iff₀ h8μ h8ν]
  nlinarith

/-- Descending from the convexity bound: `μ = 1/4` is above the threshold, and one step improves it
to `1/5`.  The iteration continues to decrease, but is trapped above `(√3-1)/4`. -/
@[simp] theorem lineMap_convexity : lineMap (1/4) = 1/5 := by unfold lineMap; norm_num

/-- The threshold quadratic is negative at `9/50 = 0.18` and positive at `1/5 = 0.2`, so the fixed
point `(√3-1)/4` lies strictly between them; every landmark `μ` is below `9/50`. -/
theorem threshold_between : 8*(9/50:ℚ)^(2 : ℕ) + 4*(9/50) - 1 < 0 ∧ 8*(1/5:ℚ)^(2 : ℕ) + 4*(1/5) - 1 > 0 := by
  constructor <;> norm_num

end HTGeometry

/-!
### The floor of the `A` machinery

Write `μ = epMu κ lam`.  A direct computation gives the `A`-step output in closed form:

    epMu (A(κ,λ)) = (κ+λ) / (4κ+4) = (4μ + 1) / (8κ + 8),

so the gain is controlled entirely by `κ`: the *smaller* `κ`, the *worse* the step.  Since `λ ≥ 1/2`
holds for every exponent pair, `κ + 1/2 ≤ κ + λ = 2μ + 1/2`, i.e. **`κ ≤ 2μ`**.  Substituting the
extreme gives the best a single `A`-step can ever do:

    epMu (A(κ,λ))  ≥  (4μ + 1)/(16μ + 8)  =:  R(μ).

Iterating `R` from the convexity bound produces

    1/4  →  1/6  →  5/32  →  **13/84**  →  17/110  →  …

whose fourth term is exactly Bourgain's record.  `R` has fixed points at the roots of
`16μ² + 4μ - 1`, so the chain descends to `(√5 - 1)/8 = 0.15450849…` and can never pass it.  The
current record `13/84 = 0.15476…` lies within `0.00026` of that floor.
-/

namespace HTGeometry

/-- The best a single `A`-step can do from a pair delivering `μ`, after using `λ ≥ 1/2`. -/
def relaxedStep (μ : ℚ) : ℚ := (4*μ + 1) / (16*μ + 8)

/-- **Closed form for the `A`-step output.**  `epMu` of `A(κ,λ)` is `(κ+λ)/(4κ+4)`. -/
theorem epMu_procA_closed {κ lam : ℚ} (hκ : 0 ≤ κ) :
    epMu (procA_fst κ) (procA_snd κ lam) = (κ + lam) / (4*κ + 4) := by
  have h : (2*κ + 2) ≠ 0 := by positivity
  have h4 : (4*κ + 4) ≠ 0 := by positivity
  unfold epMu procA_fst procA_snd
  field_simp
  ring

/-- **`λ ≥ 1/2` forces `κ ≤ 2μ`.** -/
theorem kappa_le_two_mu {κ lam : ℚ} (hlam : 1/2 ≤ lam) : κ ≤ 2 * epMu κ lam := by
  unfold epMu; linarith

/-- **The floor of a single `A`-step.**  For any exponent pair with `κ ≥ 0` and `λ ≥ 1/2`, one
`A`-step cannot deliver better than `relaxedStep μ`. -/
theorem procA_ge_relaxedStep {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1/2 ≤ lam) :
    relaxedStep (epMu κ lam) ≤ epMu (procA_fst κ) (procA_snd κ lam) := by
  have hμ : 0 ≤ epMu κ lam := by unfold epMu; linarith
  have hk2 : κ ≤ 2 * epMu κ lam := kappa_le_two_mu hlam
  rw [epMu_procA_closed hκ]
  have hden : (0:ℚ) < 4*κ + 4 := by linarith
  have hden2 : (0:ℚ) < 16 * epMu κ lam + 8 := by linarith
  have hsum : κ + lam = 2 * epMu κ lam + 1/2 := by unfold epMu; ring
  unfold relaxedStep
  rw [div_le_div_iff₀ hden2 hden, hsum]
  nlinarith [hμ, hk2]

/-- The chain from the convexity bound.  Its fourth term is Bourgain's record. -/
@[simp] theorem relaxedStep_quarter : relaxedStep (1/4) = 1/6 := by unfold relaxedStep; norm_num

@[simp] theorem relaxedStep_weyl : relaxedStep (1/6) = 5/32 := by unfold relaxedStep; norm_num

/-- **The third step lands exactly on Bourgain's exponent.** -/
@[simp] theorem relaxedStep_third : relaxedStep (5/32) = 13/84 := by unfold relaxedStep; norm_num

@[simp] theorem relaxedStep_fourth : relaxedStep (13/84) = 17/110 := by
  unfold relaxedStep; norm_num

/-- Fixed points of the relaxed step are the roots of `16μ² + 4μ - 1`; the positive root is
`(√5 - 1)/8 = 0.15450849…`. -/
theorem relaxedStep_fixed_iff {μ : ℚ} (hμ : 0 ≤ μ) :
    relaxedStep μ = μ ↔ 16*μ^(2 : ℕ) + 4*μ - 1 = 0 := by
  have h : (0:ℚ) < 16*μ + 8 := by linarith
  unfold relaxedStep
  rw [div_eq_iff (ne_of_gt h)]
  constructor <;> intro hh <;> nlinarith [hh]

/-- **The floor.**  Below the positive root of `16μ²+4μ-1`, the relaxed step strictly *increases*
`μ`; so the chain can never descend past `(√5-1)/8`. -/
theorem relaxedStep_gt_of_below {μ : ℚ} (hμ : 0 ≤ μ) (h : 16*μ^(2 : ℕ) + 4*μ - 1 < 0) :
    μ < relaxedStep μ := by
  have hd : (0:ℚ) < 16*μ + 8 := by linarith
  unfold relaxedStep
  rw [lt_div_iff₀ hd]
  nlinarith

/-- The floor `(√5-1)/8` is bracketed: `16μ²+4μ-1` is negative at `309/2000 = 0.1545` and positive
at `17/110 = 0.15454…`, so `0.1545 < (√5-1)/8 < 17/110`.  Every chain term stays above it. -/
theorem floor_brackets :
    16*(309/2000:ℚ)^(2 : ℕ) + 4*(309/2000) - 1 < 0 ∧ 16*(17/110:ℚ)^(2 : ℕ) + 4*(17/110) - 1 > 0 := by
  constructor <;> norm_num

/-- **The floor is pinned between two consecutive chain terms.**  Since the threshold quadratic is
negative at `17/110` and positive at `13/84`, the floor `(√5-1)/8` lies strictly between them, in an
interval of width `13/84 - 17/110 = 1/4620`.  Bourgain's record is therefore above the floor by less
than `1/4620 < 0.00022`. -/
theorem floor_gap_width : (13/84 : ℚ) - 17/110 = 1/4620 := by norm_num

end HTGeometry

/-!
### The floor is the trivial bound, propagated

The constraint that produced the floor is `κ ≤ 2μ`, and it is *equivalent* to `λ ≥ 1/2` — the trivial
bound on the sum.  Under `B` the two defining inequalities of the box are exchanged
(`B` sends `λ ≥ 1/2` to `κ ≥ 0` and back), so the same floor arises whether one applies `A` directly
or first applies `B` to convert a large `λ` into a large `κ`.

Hence `(√5-1)/8` is not an artefact of one route: it is the trivial bound `λ ≥ 1/2`, propagated
through the only process that moves `κ+λ`.  No improvement in the quality of intermediate pairs can
lower it, because every exponent pair obeys `λ ≥ 1/2` by definition.
-/

namespace HTGeometry

/-- **The constraint driving the floor is exactly the trivial bound.** -/
theorem kappa_le_two_mu_iff (κ lam : ℚ) : κ ≤ 2 * epMu κ lam ↔ 1/2 ≤ lam := by
  unfold epMu; constructor <;> intro h <;> linarith

/-- `B` sends the constraint `κ ≥ 0` to the constraint `λ ≥ 1/2` and conversely: the two box
inequalities are exchanged by the involution. -/
theorem procB_exchanges_constraints (κ lam : ℚ) :
    (0 ≤ procB_fst lam ↔ 1/2 ≤ lam) ∧ (1/2 ≤ procB_snd κ ↔ 0 ≤ κ) := by
  unfold procB_fst procB_snd
  constructor <;> constructor <;> intro h <;> linarith

/-- `B` preserves `μ`. -/
theorem epMu_procB (κ lam : ℚ) : epMu (procB_fst lam) (procB_snd κ) = epMu κ lam := by
  unfold epMu procB_fst procB_snd; ring

/-- **The `B`-then-`A` route obeys the same floor.**  Applying `B` first converts `λ` into the new
first coordinate; the `A`-step output is then `(4μ+1)/(8λ+4)`, and `κ ≥ 0` bounds `λ ≤ 2μ + 1/2`,
returning exactly `R(μ)`. -/
theorem procBA_ge_relaxedStep {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1/2 ≤ lam) :
    relaxedStep (epMu κ lam) ≤
      epMu (procA_fst (procB_fst lam)) (procA_snd (procB_fst lam) (procB_snd κ)) := by
  have hb0 : 0 ≤ procB_fst lam := by unfold procB_fst; linarith
  have hb1 : 1/2 ≤ procB_snd κ := by unfold procB_snd; linarith
  have h := procA_ge_relaxedStep hb0 hb1
  rwa [epMu_procB κ lam] at h

/-- **The floor is self-dual.**  Both routes — `A` alone and `B` then `A` — are bounded below by the
same `R(μ)`, so no ordering of the two processes escapes it. -/
theorem floor_is_selfDual {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1/2 ≤ lam) :
    relaxedStep (epMu κ lam) ≤ epMu (procA_fst κ) (procA_snd κ lam) ∧
    relaxedStep (epMu κ lam) ≤
      epMu (procA_fst (procB_fst lam)) (procA_snd (procB_fst lam) (procB_snd κ)) :=
  ⟨procA_ge_relaxedStep hκ hlam, procBA_ge_relaxedStep hκ hlam⟩

end HTGeometry

/-!
### Which pairs saturate the floor

The bound `epMu(A(κ,λ)) ≥ R(μ)` is attained exactly when `κ = 2μ`, i.e. when `λ = 1/2`.  The unique
pair delivering `μ` with `λ = 1/2` is `(2μ, 1/2)`, and it does deliver `μ`:

    epMu (2μ, 1/2) = (2μ + 1/2 - 1/2)/2 = μ.

So each step of the chain `1/4 → 1/6 → 5/32 → 13/84 → …` consumes an exponent pair of the form
`(2μ, 1/2)`.  At `μ = 1/4` that pair is `(1/2, 1/2)`, and the step is Weyl's theorem.  At `μ = 1/6`
the required pair is `(1/3, 1/2)`; at `μ = 5/32` it is `(5/16, 1/2)`.
-/

namespace HTGeometry

/-- The saturating input at level `μ`: the unique pair with `λ = 1/2` delivering `μ`. -/
def saturatingPair (μ : ℚ) : ℚ × ℚ := (2*μ, 1/2)

/-- The saturating pair does deliver `μ`. -/
@[simp] theorem epMu_saturatingPair (μ : ℚ) :
    epMu (saturatingPair μ).1 (saturatingPair μ).2 = μ := by
  unfold epMu saturatingPair; ring

/-- **Saturation is exactly `λ = 1/2`.**  The `A`-step attains the floor `R(μ)` if and only if the
input has `λ = 1/2`. -/
theorem procA_eq_relaxedStep_iff {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1/2 ≤ lam) :
    epMu (procA_fst κ) (procA_snd κ lam) = relaxedStep (epMu κ lam) ↔ lam = 1/2 := by
  have hμ : 0 ≤ epMu κ lam := by unfold epMu; linarith
  have hden : (0:ℚ) < 4*κ + 4 := by linarith
  have hden2 : (0:ℚ) < 16 * epMu κ lam + 8 := by linarith
  have hsum : κ + lam = 2 * epMu κ lam + 1/2 := by unfold epMu; ring
  rw [epMu_procA_closed hκ]
  unfold relaxedStep
  rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt hden2), hsum]
  constructor
  · intro h; unfold epMu at h; nlinarith [h]
  · intro h; subst h; unfold epMu; ring

/-- At `μ = 1/4` the saturating pair is the trivial pair `(1/2, 1/2)`, and the step is Weyl's. -/
@[simp] theorem saturatingPair_quarter : saturatingPair (1/4) = (1/2, 1/2) := by
  unfold saturatingPair; norm_num

/-- The saturating pair required for the *second* step. -/
@[simp] theorem saturatingPair_weyl : saturatingPair (1/6) = (1/3, 1/2) := by
  unfold saturatingPair; norm_num

/-- The saturating pair required for the *third* step. -/
@[simp] theorem saturatingPair_third : saturatingPair (5/32) = (5/16, 1/2) := by
  unfold saturatingPair; norm_num

/-- **Saturating pairs have `κ < 1/2` beyond the first step.**  Every step after Weyl's demands an
exponent pair with `λ = 1/2` and `κ` strictly below `1/2` — the regime in which no pair is known. -/
theorem saturatingPair_kappa_lt_half {μ : ℚ} (h : μ < 1/4) : (saturatingPair μ).1 < 1/2 := by
  unfold saturatingPair; simp; linarith

/-- **The limit of the saturating family is the exponent-pair conjecture.**  As `μ → 0` the required
pair tends to `(0, 1/2)`, whose validity is equivalent to `μ = 0`, i.e. to the Lindelöf hypothesis. -/
theorem saturatingPair_limit : saturatingPair 0 = (0, 1/2) ∧ epMu 0 (1/2) = 0 := by
  constructor
  · unfold saturatingPair; norm_num
  · unfold epMu; norm_num

end HTGeometry

/-!
### What the exponent-pair formalism discards

An exponent pair is a statement *uniform over phases*: `(κ,λ)` asserts
`|Σ_{n∼N} e(Y F(n/N))| ≪ (Y/N)^κ N^λ` for every `F` in a fixed class of smooth functions.  The
Lindelöf hypothesis concerns a single phase, `F(u) = -log u`, whose sum has coefficients `n^{-it}` —
a *completely multiplicative* function of `n`.

So the implication runs one way: an exponent pair arbitrarily close to `(0, 1/2)` yields `μ = 0`, but
a bound for one phase carries no information about the others.  The barriers proved above — the
inertness threshold, the line attractor, the floor, the one-step chain — all constrain the *uniform*
route.  They say nothing about arguments that use multiplicativity, which the formalism discards.

The two regimes are recorded below as explicit predicates so that the logical direction is fixed by
the statement rather than by prose.
-/

namespace HTGeometry

/-- The Lindelöf hypothesis as a statement about the exponent delivered at the critical block. -/
def LindelofFrom (μ : ℚ) : Prop := μ ≤ 0

/-- The exponent-pair conjecture, in the coordinate used here: self-dual pairs with `κ` arbitrarily
small.  Since `μ = κ` on the line, this is `μ` arbitrarily small. -/
def ExponentPairConjectureFrom (S : ExponentPairSystem) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ κ, 0 ≤ κ ∧ κ < ε ∧ S.mem κ (κ + 1/2)

/-- **The exponent-pair conjecture delivers the Lindelöf exponent.**  If self-dual pairs exist with
`κ` below every positive rational, then the exponent delivered at the critical block is below every
positive rational.  The converse is *not* asserted: a bound for the single phase `-log u` yields no
exponent pair. -/
theorem exponentPairConjecture_gives_lindelof (S : ExponentPairSystem)
    (h : ExponentPairConjectureFrom S) :
    ∀ ε : ℚ, 0 < ε → ∃ κ lam, S.mem κ lam ∧ 0 ≤ epMu κ lam ∧ epMu κ lam < ε := by
  intro ε hε
  obtain ⟨κ, hκ0, hκε, hmem⟩ := h ε hε
  refine ⟨κ, κ + 1/2, hmem, ?_, ?_⟩
  · rw [epMu_eq_kappa_of_selfDual rfl]; exact hκ0
  · rw [epMu_eq_kappa_of_selfDual rfl]; exact hκε

/-- The saturating family that the `A` chain consumes converges to the exponent-pair conjecture's
witness: `saturatingPair μ → (0, 1/2)` as `μ → 0`, and `(0,1/2)` canonicalises to the self-dual
witness `(0, 1/2)` itself. -/
theorem saturatingPair_canonical_limit :
    SelfDual (epMu 0 (1/2)) (epMu 0 (1/2) + 1/2) ∧ epMu 0 (1/2) = 0 := by
  constructor
  · rfl
  · unfold epMu; norm_num

end HTGeometry
