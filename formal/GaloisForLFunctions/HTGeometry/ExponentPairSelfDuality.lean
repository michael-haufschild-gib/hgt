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
    epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam ↔ 8*κ^2 + 4*κ - 1 > 0 := by
  rw [procA_decreases_iff hκ]
  unfold SelfDual at h
  subst h
  constructor <;> intro hh <;> nlinarith [hh]

/-- **Weyl's pair is below the threshold: `A` cannot improve it.** -/
theorem weyl_below_threshold : ¬ (8*(1/6:ℚ)^2 + 4*(1/6) - 1 > 0) := by norm_num

/-- **Bourgain's record pair is below the threshold: `A` cannot improve it either.** -/
theorem bourgain_below_threshold : ¬ (8*(13/84:ℚ)^2 + 4*(13/84) - 1 > 0) := by norm_num

/-- **The threshold is monotone: the quadratic is increasing on `κ ≥ 0`, so once a self-dual pair
falls below the threshold, every *better* self-dual pair falls further below it.**  Since `μ = κ`
on the locus, improving `μ` moves strictly away from the region where `A` is useful. -/
theorem threshold_monotone {κ κ' : ℚ} (hκ : 0 ≤ κ') (hlt : κ' < κ) :
    8*κ'^2 + 4*κ' - 1 < 8*κ^2 + 4*κ - 1 := by nlinarith

/-- **The barrier, assembled.**  For a self-dual exponent pair with `0 ≤ κ ≤ 13/84` — that is, any
pair at least as good as the current record — the `A` process strictly *increases* `κ+λ`, hence
strictly worsens `μ`. -/
theorem vanDerCorput_inert_at_record {κ lam : ℚ} (hκ : 0 ≤ κ) (hrec : κ ≤ 13/84)
    (h : SelfDual κ lam) :
    ¬ (epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam) := by
  rw [procA_decreases_selfDual_iff hκ h]
  have : 8*κ^2 + 4*κ - 1 ≤ 8*(13/84:ℚ)^2 + 4*(13/84) - 1 := by nlinarith
  have hb : 8*(13/84:ℚ)^2 + 4*(13/84) - 1 < 0 := by norm_num
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
    8*(1/6 : ℚ)^2 + 4*(1/6) - 1 < 0 ∧
    8*(9/56 : ℚ)^2 + 4*(9/56) - 1 < 0 ∧
    8*(32/205 : ℚ)^2 + 4*(32/205) - 1 < 0 ∧
    8*(13/84 : ℚ)^2 + 4*(13/84) - 1 < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **`A`-inertness for any self-dual pair below `9/50 = 0.18`**, a rational bound strictly under the
threshold root `(√3-1)/4 = 0.18301…`.  This covers the whole historical record, whose best value
`1/6 = 0.1667` already exceeds `13/84`. -/
theorem vanDerCorput_inert_below_threshold {κ lam : ℚ} (hκ : 0 ≤ κ) (hrec : κ ≤ 9/50)
    (h : SelfDual κ lam) :
    ¬ (epSum (procA_fst κ) (procA_snd κ lam) < epSum κ lam) := by
  rw [procA_decreases_selfDual_iff hκ h]
  have : 8*κ^2 + 4*κ - 1 ≤ 8*(9/50:ℚ)^2 + 4*(9/50) - 1 := by nlinarith
  have hb : 8*(9/50:ℚ)^2 + 4*(9/50) - 1 < 0 := by norm_num
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
    8*(0:ℚ)^2 + 4*0 - 1 < 8*κ^2 + 4*κ - 1 ∧ 8*κ^2 + 4*κ - 1 < 0 := by
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
    lineMap μ = μ ↔ 8*μ^2 + 4*μ - 1 = 0 := by
  have h8 : (8*μ + 8) ≠ 0 := by positivity
  unfold lineMap
  rw [div_eq_iff h8]
  constructor <;> intro h <;> nlinarith [h]

/-- **`lineMap` decreases `μ` exactly above the threshold, and increases it exactly below.** -/
theorem lineMap_lt_iff {μ : ℚ} (hμ : 0 ≤ μ) :
    lineMap μ < μ ↔ 8*μ^2 + 4*μ - 1 > 0 := by
  have h8 : (0:ℚ) < 8*μ + 8 := by positivity
  unfold lineMap
  rw [div_lt_iff₀ h8]
  constructor <;> intro h <;> nlinarith [h]

/-- **`lineMap` strictly increases `μ` below the threshold.**  In particular the composite makes
every record strictly worse. -/
theorem lineMap_gt_of_below {μ : ℚ} (hμ : 0 ≤ μ) (h : 8*μ^2 + 4*μ - 1 < 0) : μ < lineMap μ := by
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
theorem threshold_between : 8*(9/50:ℚ)^2 + 4*(9/50) - 1 < 0 ∧ 8*(1/5:ℚ)^2 + 4*(1/5) - 1 > 0 := by
  constructor <;> norm_num

end HTGeometry
