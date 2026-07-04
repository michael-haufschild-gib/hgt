/-
The signed relay ledger (doc 77 §5): the cascade walk continued THROUGH the
absorbing barrier.

`DepthUpdate` licenses the signed coordinate: the pair's configuration is read
off the sign of the signed squared depth — positive: off-line pair; nonpositive:
on-line pair. Absorption and relay (re-creation) are the same walker crossing 0.
This module upgrades `SweepCascade`'s one-way bookkeeping (`SurvivesFrom` /
`KilledFrom`) to the two-way walk and proves the relay re-cut's combinatorial
core:

* `signedDepth` — prefix depths over the push list (defined for every index;
  beyond the list the walk is constant, so no length bookkeeping is needed).
* `exists_last_nonpos_between` — discrete first passage with a last-crossing
  witness: a nonpositive start and a positive end sandwich a LAST nonpositive
  index; it is an upcrossing, and the walk is positive strictly after it.
* `run_bounded_of_excursionBound` — (EXC-ℓ) ⟹ no continuous off-line run
  longer than ℓ: continuous forced presence past ℓ levels is impossible.
  The deep-pair contradiction shape.
* `exists_upcross_chain` — presence at levels separated by ≥ ℓ forces strictly
  increasing upcrossings, one per level.
* `card_upcross_ge_of_spread` / `spread_lt_of_upcross_budget` — the counting
  form and the budget form: an upcrossing budget R forbids (R+1)-fold
  ℓ-separated presence. The marginal-regime contradiction shape, the formal
  consumption point for (CR-density) × (XLD) sub-criticality.
* `survivesFrom_iff_forall_signedDepth_pos` — the old one-way ledger is
  exactly "off-line at every prefix".

The analytic supplies for (EXC-ℓ) and the budget are the named open inputs
(doc 77 §§1–3): the half-law + (SURV-EQ) discrepancy for the rates, (XLD)
sub-criticality for the chain tail. Nothing here consumes them silently.
-/
import Mathlib
import GaloisForLFunctions.RHTower.SweepCascade

noncomputable section

namespace RHTower

/-- Signed prefix depth after the first `m` pushes (constant past the list end). -/
def signedDepth (D₀ : ℝ) (pushes : List ℝ) (m : ℕ) : ℝ :=
  depthAfter D₀ (pushes.take m)

@[simp] theorem signedDepth_zero (D₀ : ℝ) (pushes : List ℝ) :
    signedDepth D₀ pushes 0 = D₀ := rfl

theorem signedDepth_cons_succ (D₀ q : ℝ) (qs : List ℝ) (m : ℕ) :
    signedDepth D₀ (q :: qs) (m + 1) = signedDepth (D₀ + q) qs m := rfl

/-- The walker lifts off the line at step `m`: on-line at `m`, off-line at `m+1`. -/
def UpcrossAt (D₀ : ℝ) (pushes : List ℝ) (m : ℕ) : Prop :=
  signedDepth D₀ pushes m ≤ 0 ∧ 0 < signedDepth D₀ pushes (m + 1)

/-- **(EXC-ℓ)**: every lift-off re-absorbs within ℓ entries — the ephemerality
hypothesis (measured: doc 53 §3, doc 76 §5; analytic supply = the drift/dip
tier + the half-law rates of doc 77). -/
def ExcursionBound (D₀ : ℝ) (pushes : List ℝ) (ℓ : ℕ) : Prop :=
  ∀ m, UpcrossAt D₀ pushes m →
    ∃ j, 1 ≤ j ∧ j ≤ ℓ ∧ signedDepth D₀ pushes (m + 1 + j) ≤ 0

/-- Discrete first passage with a last-crossing witness: between a nonpositive
index `s` and a positive index `n` sits a LAST nonpositive index `m`; the walk
is positive on all of `(m, n]`. -/
theorem exists_last_nonpos_between {D₀ : ℝ} {pushes : List ℝ} :
    ∀ {n s : ℕ}, s ≤ n → signedDepth D₀ pushes s ≤ 0 →
      0 < signedDepth D₀ pushes n →
      ∃ m, s ≤ m ∧ m < n ∧ signedDepth D₀ pushes m ≤ 0 ∧
        ∀ k, m < k → k ≤ n → 0 < signedDepth D₀ pushes k := by
  intro n
  induction n with
  | zero =>
      intro s hs hnp hpos
      have hs0 : s = 0 := Nat.le_zero.mp hs
      subst hs0
      exact absurd hpos (not_lt.mpr hnp)
  | succ n ih =>
      intro s hs hnp hpos
      by_cases hsn : s ≤ n
      · by_cases hmid : signedDepth D₀ pushes n ≤ 0
        · refine ⟨n, hsn, Nat.lt_succ_self n, hmid, ?_⟩
          intro k hk hk'
          have hkeq : k = n + 1 := le_antisymm hk' hk
          rw [hkeq]
          exact hpos
        · have hposn : 0 < signedDepth D₀ pushes n := lt_of_not_ge hmid
          obtain ⟨m, hm₁, hm₂, hm₃, hm₄⟩ := ih hsn hnp hposn
          refine ⟨m, hm₁, Nat.lt_succ_of_lt hm₂, hm₃, ?_⟩
          intro k hk hk'
          rcases eq_or_lt_of_le hk' with heq | hlt
          · rw [heq]
            exact hpos
          · exact hm₄ k hk (Nat.lt_succ_iff.mp hlt)
      · have hseq : s = n + 1 := le_antisymm hs (lt_of_not_ge hsn)
        subst hseq
        exact absurd hpos (not_lt.mpr hnp)

/-- **The deep-pair contradiction shape**: under (EXC-ℓ) and an on-line start,
no continuous off-line run exceeds ℓ levels — forced presence at every level
of an interval longer than ℓ is impossible. -/
theorem run_bounded_of_excursionBound {D₀ : ℝ} {pushes : List ℝ} {ℓ : ℕ}
    (hD₀ : D₀ ≤ 0) (hexc : ExcursionBound D₀ pushes ℓ) {s e : ℕ} (hse : s ≤ e)
    (hrun : ∀ m, s ≤ m → m ≤ e → 0 < signedDepth D₀ pushes m) :
    e < s + ℓ := by
  obtain ⟨m₀, -, hm₀s, hm₀np, hm₀pos⟩ :=
    exists_last_nonpos_between (Nat.zero_le s)
      (by simpa using hD₀) (hrun s le_rfl hse)
  have hup : UpcrossAt D₀ pushes m₀ :=
    ⟨hm₀np, hm₀pos (m₀ + 1) (Nat.lt_succ_self m₀) (Nat.succ_le_of_lt hm₀s)⟩
  obtain ⟨j, hj1, hjℓ, hjnp⟩ := hexc m₀ hup
  have hallpos : ∀ k, m₀ < k → k ≤ e → 0 < signedDepth D₀ pushes k := by
    intro k hk hk'
    by_cases hks : k ≤ s
    · exact hm₀pos k hk hks
    · exact hrun k (le_of_lt (lt_of_not_ge hks)) hk'
  have hgt : e < m₀ + 1 + j := by
    by_contra hle
    exact absurd (hallpos (m₀ + 1 + j) (by omega) (not_lt.mp hle))
      (not_lt.mpr hjnp)
  omega

/-- **The upcross chain**: presence at `k+1` levels with consecutive gaps ≥ ℓ
forces `k+1` strictly increasing upcrossings, each below its level; the walk is
positive strictly after the top one up to the top level. -/
theorem exists_upcross_chain {D₀ : ℝ} {pushes : List ℝ} {ℓ : ℕ}
    (hD₀ : D₀ ≤ 0) (hexc : ExcursionBound D₀ pushes ℓ) :
    ∀ (k : ℕ) (levels : ℕ → ℕ),
      (∀ i, i < k → levels i + ℓ ≤ levels (i + 1)) →
      (∀ i, i ≤ k → 0 < signedDepth D₀ pushes (levels i)) →
      ∃ u : ℕ → ℕ,
        (∀ i, i ≤ k → UpcrossAt D₀ pushes (u i) ∧ u i < levels i) ∧
        (∀ i j, i < j → j ≤ k → u i < u j) ∧
        (∀ m, u k < m → m ≤ levels k → 0 < signedDepth D₀ pushes m) := by
  intro k
  induction k with
  | zero =>
      intro levels _ hpres
      obtain ⟨m₀, -, hm₀lt, hm₀np, hm₀pos⟩ :=
        exists_last_nonpos_between (Nat.zero_le _)
          (by simpa using hD₀) (hpres 0 le_rfl)
      refine ⟨fun _ => m₀, ?_, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        exact ⟨⟨hm₀np, hm₀pos (m₀ + 1) (Nat.lt_succ_self m₀)
          (Nat.succ_le_of_lt hm₀lt)⟩, hm₀lt⟩
      · intro i j hij hj
        exact absurd (lt_of_lt_of_le hij hj) (Nat.not_lt_zero i)
      · exact fun m hm hm' => hm₀pos m hm hm'
  | succ k ih =>
      intro levels hgap hpres
      obtain ⟨u, hu₁, hu₂, hu₃⟩ := ih levels
        (fun i hi => hgap i (Nat.lt_succ_of_lt hi))
        (fun i hi => hpres i (Nat.le_succ_of_le hi))
      have hupk : UpcrossAt D₀ pushes (u k) := (hu₁ k le_rfl).1
      have hukk : u k < levels k := (hu₁ k le_rfl).2
      obtain ⟨jj, hjj1, hjjℓ, hjjnp⟩ := hexc (u k) hupk
      have hmstar_le : u k + 1 + jj ≤ levels (k + 1) := by
        have := hgap k (Nat.lt_succ_self k)
        omega
      obtain ⟨m₁, hm₁ge, hm₁lt, hm₁np, hm₁pos⟩ :=
        exists_last_nonpos_between hmstar_le hjjnp (hpres (k + 1) le_rfl)
      refine ⟨fun i => if i ≤ k then u i else m₁, ?_, ?_, ?_⟩
      · intro i hi
        dsimp only
        by_cases hik : i ≤ k
        · rw [if_pos hik]
          exact hu₁ i hik
        · have hieq : i = k + 1 := by omega
          subst hieq
          rw [if_neg hik]
          exact ⟨⟨hm₁np, hm₁pos (m₁ + 1) (Nat.lt_succ_self m₁)
            (Nat.succ_le_of_lt hm₁lt)⟩, hm₁lt⟩
      · intro i j hij hj
        dsimp only
        by_cases hjk : j ≤ k
        · rw [if_pos (le_trans (le_of_lt hij) hjk), if_pos hjk]
          exact hu₂ i j hij hjk
        · have hjeq : j = k + 1 := by omega
          subst hjeq
          have hik : i ≤ k := by omega
          rw [if_pos hik, if_neg hjk]
          have hik' : u i ≤ u k := by
            rcases eq_or_lt_of_le hik with h | h
            · rw [h]
            · exact le_of_lt (hu₂ i k h le_rfl)
          omega
      · intro m hm hm'
        dsimp only at hm
        rw [if_neg (by omega : ¬ (k + 1 ≤ k))] at hm
        exact hm₁pos m hm hm'

/-- **Counting form**: presence at `k+1` levels with gaps ≥ ℓ puts at least
`k+1` upcrossings strictly below the top level. -/
theorem card_upcross_ge_of_spread {D₀ : ℝ} {pushes : List ℝ} {ℓ k : ℕ}
    {levels : ℕ → ℕ} [DecidablePred (UpcrossAt D₀ pushes)]
    (hD₀ : D₀ ≤ 0) (hexc : ExcursionBound D₀ pushes ℓ)
    (hgap : ∀ i, i < k → levels i + ℓ ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k → 0 < signedDepth D₀ pushes (levels i)) :
    k + 1 ≤ ((Finset.range (levels k)).filter (UpcrossAt D₀ pushes)).card := by
  obtain ⟨u, hu₁, hu₂, -⟩ := exists_upcross_chain hD₀ hexc k levels hgap hpres
  have hstep : ∀ i, i < k → levels i ≤ levels (i + 1) := fun i hi =>
    le_trans (Nat.le_add_right _ _) (hgap i hi)
  have hlev : ∀ d i, i + d ≤ k → levels i ≤ levels (i + d) := by
    intro d
    induction d with
    | zero => intro i _; exact le_rfl
    | succ d ihd =>
        intro i hik
        have h1 : levels i ≤ levels (i + d) := ihd i (by omega)
        have h2 : levels (i + d) ≤ levels (i + d + 1) := hstep _ (by omega)
        exact le_trans h1 h2
  have hlev' : ∀ i, i ≤ k → levels i ≤ levels k := by
    intro i hi
    have := hlev (k - i) i (by omega)
    rwa [Nat.add_sub_cancel' hi] at this
  have hmem : ∀ i : Fin (k + 1),
      u ↑i ∈ (Finset.range (levels k)).filter (UpcrossAt D₀ pushes) := by
    intro i
    have hik : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
    have h₁ := hu₁ i hik
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_lt_of_le h₁.2 (hlev' i hik)), h₁.1⟩
  have hinj : Function.Injective (fun i : Fin (k + 1) => u ↑i) := by
    intro a b hab
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with h | h | h
    · exact absurd hab (ne_of_lt (hu₂ a b h (Nat.lt_succ_iff.mp b.isLt)))
    · exact Fin.ext h
    · exact absurd hab.symm (ne_of_lt (hu₂ b a h (Nat.lt_succ_iff.mp a.isLt)))
  calc k + 1 = (Finset.univ : Finset (Fin (k + 1))).card := (Finset.card_fin _).symm
    _ = (Finset.univ.image fun i : Fin (k + 1) => u ↑i).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (levels k)).filter (UpcrossAt D₀ pushes)).card := by
        refine Finset.card_le_card ?_
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact hmem i

/-- **The budget form (the marginal-regime contradiction shape)**: an
upcrossing budget `R` below height `M` forbids presence at `R+1` levels with
gaps ≥ ℓ below `M` — the formal consumption point for a creation budget times
(XLD) sub-criticality. -/
theorem spread_lt_of_upcross_budget {D₀ : ℝ} {pushes : List ℝ} {ℓ k M R : ℕ}
    {levels : ℕ → ℕ} [DecidablePred (UpcrossAt D₀ pushes)]
    (hD₀ : D₀ ≤ 0) (hexc : ExcursionBound D₀ pushes ℓ)
    (hgap : ∀ i, i < k → levels i + ℓ ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k → 0 < signedDepth D₀ pushes (levels i))
    (hM : levels k ≤ M)
    (hbud : ((Finset.range M).filter (UpcrossAt D₀ pushes)).card ≤ R) :
    k < R := by
  have h1 := card_upcross_ge_of_spread hD₀ hexc hgap hpres
  have h2 : ((Finset.range (levels k)).filter (UpcrossAt D₀ pushes)).card
      ≤ ((Finset.range M).filter (UpcrossAt D₀ pushes)).card :=
    Finset.card_le_card
      (Finset.filter_subset_filter _ (by
        intro x hx
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hM)))
  omega

/-- The old one-way ledger is the special case "off-line at every prefix":
`SurvivesFrom` is equivalent to positivity of every signed prefix depth. -/
theorem survivesFrom_iff_forall_signedDepth_pos {D₀ : ℝ} {pushes : List ℝ}
    (hD₀ : 0 < D₀) :
    SurvivesFrom D₀ pushes ↔ ∀ m, 0 < signedDepth D₀ pushes m := by
  induction pushes generalizing D₀ with
  | nil =>
      constructor
      · intro _ m
        simpa [signedDepth, depthAfter] using hD₀
      · intro _
        simpa [SurvivesFrom] using hD₀
  | cons q qs ih =>
      constructor
      · rintro ⟨h1, h2⟩ m
        cases m with
        | zero => simpa using hD₀
        | succ m =>
            rw [signedDepth_cons_succ]
            exact (ih h1).mp h2 m
      · intro h
        have h1 : 0 < D₀ + q := by
          have := h 1
          rwa [signedDepth_cons_succ, signedDepth_zero] at this
        refine ⟨h1, (ih h1).mpr ?_⟩
        intro m
        have := h (m + 1)
        rwa [signedDepth_cons_succ] at this

end RHTower
