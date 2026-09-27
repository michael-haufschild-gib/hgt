import GaloisForLFunctions.RHTower.LensIsolatedSimpleZeros
import GaloisForLFunctions.RHTower.ClusteredBlockPacket

/-!
# Most zeta zeros are simple, critical and separated from every other zero

For `0 < r ≤ 1`, a zero `ρ` is *`r`-separated at scale `L`* if no other zero lies within distance
`r/L`.  The main theorem `separated_simple_critical` states: for every `ε > 0` and all large `T`, at
least `(HD(1) − r² − ε)·N(T,2T)` zeros `ρ` with `T < Im ρ ≤ 2T` are simple, lie on the critical
line, and have no other zero within distance `r/log(T/2π)`.  Here `HD(1) = 0.67250…`; for example
`r = 1/10` gives `0.6625`.

Proof.  Non-simple and off-line zeros near `ρ` lie in its lens and are absorbed at no cost
(`LensIsolatedSimpleZeros`).  Simple critical zeros closer than `r/L` to each other are grouped: a
half-size dominating set `Q` of them is moved into the absorbing range (`exists_dominating_half`),
each representative costs `2`, and each other clustered zero, being within `r/L` of a
representative, earns `2cos(Δ L) ≥ 2 − r²` in the trace form of the Lamzouri inequality
(`clustered_block_count`, `blockOverlap_ge`).  Since there are at least as many absorbed zeros as
representatives, the loss is at most `r²` per clustered zero.
-/

open Complex Finset
open scoped RealInnerProductSpace
open Zeta23 Zeta23.ZeroSide

namespace RHTower

noncomputable section

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- A zero is `r`-separated at scale `L` if no other zero lies within distance `r/L`. -/
def Separated (Z : ZeroConfig) (r L : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' ∈ Z.carrier, ρ' ≠ ρ → ‖ρ' - ρ‖ * L ≤ r → False

/-- Simple critical-line zeros with ordinate in `(T₁, T₂]` that are `r`-separated at scale `L`. -/
def NisoSep (Z : ZeroConfig) (r L T₁ T₂ : ℝ) : ℕ :=
  (Z.window T₁ T₂ ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | Separated Z r L ρ}).ncard

/-- Two distinct points of `I′` whose ordinates differ by at most `r/L`. -/
def CloseAt (r L : ℝ) (x s : ZI Z T) : Prop := x ≠ s ∧ |(x : ℂ).im - (s : ℂ).im| * L ≤ r

instance CloseAt.decidableRel (r L : ℝ) : DecidableRel (CloseAt (Z := Z) (T := T) r L) :=
  fun x s => by unfold CloseAt; infer_instance

theorem CloseAt.symm {r L : ℝ} {x s : ZI Z T} (h : CloseAt r L x s) : CloseAt r L s x :=
  ⟨Ne.symm h.1, by rw [abs_sub_comm]; exact h.2⟩

/-- Simple on-line points of `I′` with another simple on-line point within ordinate distance `r/L`. -/
def clustered (Z : ZeroConfig) (hconj : PhiHatConj T P) (r L : ℝ) : Finset (ZI Z T) :=
  (blockData Z T P hconj).S₁.filter fun x => ∃ s ∈ (blockData Z T P hconj).S₁, CloseAt r L x s

theorem clustered_subset (hconj : PhiHatConj T P) (r L : ℝ) :
    clustered Z hconj r L ⊆ (blockData Z T P hconj).S₁ := Finset.filter_subset _ _

theorem exists_clusterReps (hconj : PhiHatConj T P) (r L : ℝ) :
    ∃ Q ⊆ clustered Z hconj r L, 2 * Q.card ≤ (clustered Z hconj r L).card ∧
      ∀ v ∈ clustered Z hconj r L \ Q, ∃ q ∈ Q, CloseAt r L v q := by
  refine exists_dominating_half _ (CloseAt r L) (fun a b h => h.symm) (fun a h => h.1 rfl) ?_
  intro v hv
  obtain ⟨hvS, s, hsS, hvs⟩ := Finset.mem_filter.mp hv
  exact ⟨s, Finset.mem_filter.mpr ⟨hsS, v, hvS, hvs.symm⟩, hvs⟩

/-- A half-size set of representatives of the clustered points. -/
def clusterReps (Z : ZeroConfig) (hconj : PhiHatConj T P) (r L : ℝ) : Finset (ZI Z T) :=
  (exists_clusterReps (Z := Z) hconj r L).choose

theorem clusterReps_subset (hconj : PhiHatConj T P) (r L : ℝ) :
    clusterReps Z hconj r L ⊆ clustered Z hconj r L :=
  (exists_clusterReps (Z := Z) hconj r L).choose_spec.1

theorem two_mul_card_clusterReps_le (hconj : PhiHatConj T P) (r L : ℝ) :
    2 * (clusterReps Z hconj r L).card ≤ (clustered Z hconj r L).card :=
  (exists_clusterReps (Z := Z) hconj r L).choose_spec.2.1

theorem clusterReps_dominate (hconj : PhiHatConj T P) (r L : ℝ) {v : ZI Z T}
    (hv : v ∈ clustered Z hconj r L) (hvQ : v ∉ clusterReps Z hconj r L) :
    ∃ q ∈ clusterReps Z hconj r L, CloseAt r L v q :=
  (exists_clusterReps (Z := Z) hconj r L).choose_spec.2.2 v (Finset.mem_sdiff.mpr ⟨hv, hvQ⟩)

/-- The absorbed points: lens-mixed or clustered, but not representatives. -/
def sepMixed (Z : ZeroConfig) (hconj : PhiHatConj T P) (r L : ℝ) : Finset (ZI Z T) :=
  (lensMixed Z hconj L ∪ clustered Z hconj r L) \ clusterReps Z hconj r L

theorem mem_sepMixed_iff (hconj : PhiHatConj T P) (r L : ℝ) {x : ZI Z T} :
    x ∈ sepMixed Z hconj r L ↔ (x ∈ lensMixed Z hconj L ∨ x ∈ clustered Z hconj r L) ∧
      x ∉ clusterReps Z hconj r L := by
  unfold sepMixed; rw [Finset.mem_sdiff, Finset.mem_union]

open scoped Classical in
/-- The absorber of a point: a nearby representative when there is one, otherwise a lens absorber. -/
def sepAbsorber (Z : ZeroConfig) (hconj : PhiHatConj T P) (r L : ℝ) (x : ZI Z T) : ZI Z T :=
  if h : ∃ q ∈ clusterReps Z hconj r L, CloseAt r L x q then h.choose
  else if h' : ∃ z : ZI Z T, (z ∈ (blockData Z T P hconj).S₂ ∨
      z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R) ∧
      InLens L (x : ℂ).im (z : ℂ) then h'.choose else x

/-- The guaranteed gain of an absorbed point. -/
def sepGain (Z : ZeroConfig) (hconj : PhiHatConj T P) (r L : ℝ) (x : ZI Z T) : ℝ :=
  if ∃ q ∈ clusterReps Z hconj r L, CloseAt r L x q then 1 - r ^ 2 / 2 else 0

theorem card_S₁_le_Ncount (hconj : PhiHatConj T P) :
    ((blockData Z T P hconj).S₁.card : ℝ) ≤ ((blockData Z T P hconj).Ncount : ℝ) := by
  set D := blockData Z T P hconj
  have hN : (D.Ncount : ℝ) = ∑ z ∈ D.onLine, (D.m z : ℝ)
      + ∑ z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R,
          ((D.m z : ℝ) + D.m (D.σ z)) := by
    unfold Zeta23.ZeroSide.ZeroBlockData.Ncount
    push_cast
    exact D.sum_split _ (fun z => (D.m z : ℝ))
  have h1 : 0 ≤ ∑ z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R,
      ((D.m z : ℝ) + D.m (D.σ z)) := Finset.sum_nonneg fun z _ => by positivity
  have h2 : ∑ z ∈ D.S₁, (D.m z : ℝ) ≤ ∑ z ∈ D.onLine, (D.m z : ℝ) := by
    rw [D.onLine_eq_S₁_union_S₂, Finset.sum_union D.disjoint_S₁_S₂]
    have : 0 ≤ ∑ z ∈ D.S₂, (D.m z : ℝ) := Finset.sum_nonneg fun z _ => by positivity
    linarith
  have h3 : ∑ z ∈ D.S₁, (D.m z : ℝ) = D.S₁.card := by
    rw [Finset.sum_congr rfl fun z hz => m_eq_one_of_mem_S₁ D hz]
    simp
  linarith

/-- **Separated zero-side count.**  For `0 < r ≤ 1`,
`4 tr Â − ‖Â‖² − 2N(I′) ≤ #(S₁ ∖ (lensMixed ∪ clustered)) + r²·N(I′)`. -/
theorem hatAz_sep (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (ha : 0 < P.a T) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    4 * RHLinalg.rtrace (P.hat T (Z.Az P T)) - RHLinalg.frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ)
      ≤ (((blockData Z T P hconj).S₁ \ (lensMixed Z hconj (P.L T) ∪
          clustered Z hconj r (P.L T))).card : ℝ) + r ^ 2 * (Z.NIprime T : ℝ) := by
  set L := P.L T with hLdef
  set D := blockData Z T P hconj
  set Q := clusterReps Z hconj r L
  set Cl := clustered Z hconj r L
  set M := sepMixed Z hconj r L
  have hQCl : Q ⊆ Cl := clusterReps_subset hconj r L
  have hQcard : 2 * Q.card ≤ Cl.card := two_mul_card_clusterReps_le hconj r L
  have hQdom : ∀ v, v ∈ Cl → v ∉ Q → ∃ q ∈ Q, CloseAt r L v q := fun v hv hvQ =>
    clusterReps_dominate hconj r L hv hvQ
  have hc0 : 0 < P.a T * L ^ 2 := by positivity
  have hClS : Cl ⊆ D.S₁ := clustered_subset hconj r L
  have hQS : Q ⊆ D.S₁ := hQCl.trans hClS
  have hMS : M ⊆ D.S₁ := by
    intro x hx
    rcases ((mem_sepMixed_iff hconj r L).mp hx).1 with h | h
    · exact lensMixed_subset hconj _ h
    · exact hClS h
  have hMQ : Disjoint M Q := Finset.disjoint_left.mpr fun x hx hxQ =>
    ((mem_sepMixed_iff hconj r L).mp hx).2 hxQ
  have hon : ∀ x ∈ D.S₁, ((x : ZI Z T) : ℂ).re = 1 / 2 := fun x hx =>
    (mkData_σ_eq_iff Z T _ _ _).mp (Finset.mem_filter.mp hx).2.1
  have hr2 : 0 ≤ 1 - r ^ 2 / 2 := by nlinarith
  -- the absorber of each point of `M`
  have hσ : ∀ x : {z // z ∈ M}, sepAbsorber Z hconj r L x ∈ D.S₂ ∪ Q ∨
      sepAbsorber Z hconj r L x ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R := by
    intro x
    unfold sepAbsorber
    split_ifs with h h'
    · exact Or.inl (Finset.mem_union_right _ h.choose_spec.1)
    · rcases h'.choose_spec.1 with h1 | h1
      · exact Or.inl (Finset.mem_union_left _ h1)
      · exact Or.inr h1
    · exfalso
      have hx := (mem_sepMixed_iff hconj r L).mp x.2
      rcases hx.1 with hl | hcl
      · have hspec := mem_lensMixed_spec hconj
          (⟨(x : ZI Z T), hl⟩ : {z // z ∈ lensMixed Z hconj L})
        exact h' hspec
      · exact h (hQdom x hcl hx.2)
  have hcost : ∀ x : {z // z ∈ M}, sepGain Z hconj r L x ≤
      1 + 2 * ⟪blockReVec D (P.a T * L ^ 2) x, blockReVec D (P.a T * L ^ 2)
          (sepAbsorber Z hconj r L x)⟫ ^ 2
        / ‖blockReVec D (P.a T * L ^ 2) (sepAbsorber Z hconj r L x)‖ ^ 2
        - 2 * ‖blockReVec D (P.a T * L ^ 2) x‖ ^ 2 := by
    intro x
    have hxon : ((x : ZI Z T) : ℂ).re = 1 / 2 := hon x (hMS x.2)
    unfold sepGain sepAbsorber
    split_ifs with h h'
    · -- a nearby representative
      obtain ⟨hqQ, hclose⟩ := h.choose_spec
      set q := h.choose
      have hqon : ((q : ZI Z T) : ℂ).re = 1 / 2 := hon q (hQS hqQ)
      have hΔ : |((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im| * L ≤ r := by
        rw [abs_sub_comm]; exact hclose.2
      have hΔ2 : |((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im| * (L / 2) ≤ Real.pi / 2 := by
        nlinarith [Real.pi_gt_three]
      have habs : |(((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im) * (L / 2)| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]; nlinarith
      have hpos : 0 < Real.cos ((((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im) * (L / 2)) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2, Real.pi_gt_three]
      have hb := blockOverlap_ge hconj hreal hL hc hsupp ha hxon hΔ2 hpos
      rw [hqon, sub_self, zero_mul, Real.cosh_zero, div_one] at hb
      set θ := (((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im) * (L / 2)
      have hcos2 : 2 * Real.cos θ ^ 2 - 1 = Real.cos (2 * θ) := by rw [Real.cos_two_mul]
      have hlow := Real.one_sub_sq_div_two_le_cos (x := 2 * θ)
      have hθ : (2 * θ) ^ 2 ≤ r ^ 2 := by
        have : |2 * θ| ≤ r := by
          rw [show 2 * θ = (((q : ZI Z T) : ℂ).im - ((x : ZI Z T) : ℂ).im) * L by
            simp only [θ]; ring, abs_mul, abs_of_pos hL]
          exact hΔ
        have := sq_abs (2 * θ)
        nlinarith [abs_nonneg (2 * θ)]
      linarith
    · -- a lens absorber
      exact blockOverlap_lens hconj hreal hL hc hsupp ha hxon h'.choose_spec.2
    · -- impossible for points of `M`
      exfalso
      have hx := (mem_sepMixed_iff hconj r L).mp x.2
      rcases hx.1 with hl | hcl
      · have hspec := mem_lensMixed_spec hconj
          (⟨(x : ZI Z T), hl⟩ : {z // z ∈ lensMixed Z hconj L})
        exact h' hspec
      · exact h (hQdom x hcl hx.2)
  have hcount := clustered_block_count D
    (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)) (P.a T * L ^ 2) Q M hc0 hQS hMS hMQ
    (fun z hz => sum_normSq_v_le Z T P hconj hreal hPois z hz)
    (fun x => sepAbsorber Z hconj r L x) hσ (fun x => sepGain Z hconj r L x) hcost
  -- the gains cover the representatives
  have hgain : (1 - r ^ 2 / 2) * ((Cl \ Q).card : ℝ) ≤ ∑ x : {z // z ∈ M}, sepGain Z hconj r L x := by
    rw [Finset.sum_coe_sort M (fun x => sepGain Z hconj r L x)]
    have hsub : Cl \ Q ⊆ M := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      exact (mem_sepMixed_iff hconj r L).mpr ⟨Or.inr hx.1, hx.2⟩
    have hnn : ∀ x ∈ M, 0 ≤ sepGain Z hconj r L x := fun x _ => by
      unfold sepGain; split_ifs <;> linarith
    calc (1 - r ^ 2 / 2) * ((Cl \ Q).card : ℝ) = ∑ x ∈ Cl \ Q, (1 - r ^ 2 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ x ∈ Cl \ Q, sepGain Z hconj r L x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          unfold sepGain
          rw [Finset.mem_sdiff] at hx
          rw [if_pos (hQdom x hx.1 hx.2)]
      _ ≤ ∑ x ∈ M, sepGain Z hconj r L x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hnn x hx
  have hunion : M ∪ Q = lensMixed Z hconj L ∪ Cl := by
    ext x
    rw [Finset.mem_union, Finset.mem_union, mem_sepMixed_iff hconj r L]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact Or.inr (hQCl h)
    · intro h
      by_cases hq : x ∈ Q
      · exact Or.inr hq
      · exact Or.inl ⟨h, hq⟩
  rw [hunion] at hcount
  have hCl : ((Cl \ Q).card : ℝ) = Cl.card - Q.card := by
    rw [Finset.card_sdiff_of_subset hQCl]; push_cast [Finset.card_le_card hQCl]; ring
  have hQc : 2 * (Q.card : ℝ) ≤ Cl.card := by exact_mod_cast hQcard
  have hClN : (Cl.card : ℝ) ≤ (D.Ncount : ℝ) :=
    le_trans (by exact_mod_cast Finset.card_le_card hClS) (card_S₁_le_Ncount hconj)
  have hQnn : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  have key : 2 * (Q.card : ℝ) - 2 * ((1 - r ^ 2 / 2) * ((Cl \ Q).card : ℝ)) ≤ r ^ 2 * D.Ncount := by
    rw [hCl]
    have hr2' : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  have hgoal : 4 * RHLinalg.rtrace (D.blockP (P.a T * L ^ 2) + D.blockQ (P.a T * L ^ 2))
      - RHLinalg.frobSq (D.blockP (P.a T * L ^ 2) + D.blockQ (P.a T * L ^ 2)) - 2 * (D.Ncount : ℝ)
      ≤ ((D.S₁ \ (lensMixed Z hconj L ∪ Cl)).card : ℝ) + r ^ 2 * (D.Ncount : ℝ) := by
    linarith
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  exact hgoal

/-- **From `I′` to `(T, 2T]`.**  The simple on-line points of `I′` outside `lensMixed` and
`clustered`, with ordinate in `(T, 2T]`, are `r`-separated. -/
theorem card_S₁_sdiff_sep_le (hconj : PhiHatConj T P) {L r : ℝ} (hL : 0 < L)
    (hr1 : r ≤ 1) (hwin : Real.pi / L ≤ D0 T) :
    ((blockData Z T P hconj).S₁ \ (lensMixed Z hconj L ∪ clustered Z hconj r L)).card
      ≤ NisoSep Z r L T (2 * T) + Assembly.NII Z T := by
  classical
  set A : Finset ℂ := ((blockData Z T P hconj).S₁ \ (lensMixed Z hconj L ∪
    clustered Z hconj r L)).map (Function.Embedding.subtype _)
  have hcardA : A.card = ((blockData Z T P hconj).S₁ \ (lensMixed Z hconj L ∪
      clustered Z hconj r L)).card := Finset.card_map _
  set S := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | Separated Z r L ρ}
  set W₁ := Z.window (T - D0 T) T
  set W₂ := Z.window (2 * T) (2 * T + D0 T)
  have hsub : (A : Set ℂ) ⊆ S ∪ W₁ ∪ W₂ := by
    intro ρ hρ
    simp only [A, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hρ
    obtain ⟨x, hx, rfl⟩ := hρ
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hx
    obtain ⟨hxS1, hxl, hxc⟩ := hx
    have hxZI := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp x.2)
    have hxon : (x : ℂ).re = 1 / 2 :=
      (mkData_σ_eq_iff Z T _ _ _).mp (Finset.mem_filter.mp hxS1).2.1
    have hxm : Z.mult (x : ℂ) = 1 := (Finset.mem_filter.mp hxS1).2.2
    by_cases h1 : (x : ℂ).im ≤ T
    · exact Or.inl (Or.inr ⟨hxZI.1, hxZI.2.1, h1⟩)
    by_cases h2 : 2 * T < (x : ℂ).im
    · exact Or.inr ⟨hxZI.1, h2, hxZI.2.2⟩
    replace h1 : T < (x : ℂ).im := lt_of_not_ge h1
    replace h2 : (x : ℂ).im ≤ 2 * T := le_of_not_gt h2
    have hlens := lensIsolated_of_not_mem_lensMixed hconj hL hwin hxS1 hxl h1 h2
    refine Or.inl (Or.inl ⟨⟨⟨⟨hxZI.1, h1, h2⟩, hxon⟩, hxm⟩, ?_⟩)
    intro ρ' hρ' hne hd
    have hdim : |ρ'.im - (x : ℂ).im| * L ≤ r := by
      have := Complex.abs_im_le_norm (ρ' - (x : ℂ))
      rw [Complex.sub_im] at this
      nlinarith
    have hdre : |ρ'.re - 1 / 2| * L ≤ r := by
      have := Complex.abs_re_le_norm (ρ' - (x : ℂ))
      rw [Complex.sub_re, hxon] at this
      nlinarith
    have hin : InLens L (x : ℂ).im ρ' := inLens_of_rect hL (by linarith) (by linarith)
    obtain ⟨hρ'on, hρ'm⟩ := hlens ρ' hρ' hne hin
    -- a simple critical zero this close makes `x` clustered
    apply hxc
    have hdist : |ρ'.im - (x : ℂ).im| ≤ D0 T := by
      have hπ : r / L ≤ Real.pi / L := div_le_div_of_nonneg_right (by linarith [Real.pi_gt_three]) hL.le
      have : |ρ'.im - (x : ℂ).im| ≤ r / L := by rw [le_div_iff₀ hL]; exact hdim
      linarith
    have hρ'ZI : ρ' ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      refine ⟨hρ', ?_, ?_⟩
      · have := (abs_le.mp hdist).1; linarith
      · have := (abs_le.mp hdist).2; linarith
    have hsS1 : (⟨ρ', hρ'ZI⟩ : ZI Z T) ∈ (blockData Z T P hconj).S₁ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mkData_σ_eq_iff Z T _ _ _).mpr hρ'on, hρ'm⟩
    refine Finset.mem_filter.mpr ⟨hxS1, ⟨ρ', hρ'ZI⟩, hsS1, ?_, ?_⟩
    · intro h; apply hne; rw [h]
    · rw [abs_sub_comm]; exact hdim
  have hfin : ∀ {T₁ T₂ : ℝ}, (Z.window T₁ T₂).Finite := fun {T₁ T₂} => Z.window_finite T₁ T₂
  have hSfin : S.Finite := hfin.subset (fun ρ h => h.1.1.1)
  calc ((blockData Z T P hconj).S₁ \ (lensMixed Z hconj L ∪ clustered Z hconj r L)).card
        = (A : Set ℂ).ncard := by rw [Set.ncard_coe_finset, hcardA]
    _ ≤ (S ∪ W₁ ∪ W₂).ncard := Set.ncard_le_ncard hsub ((hSfin.union hfin).union hfin)
    _ ≤ (S ∪ W₁).ncard + W₂.ncard := Set.ncard_union_le _ _
    _ ≤ S.ncard + W₁.ncard + W₂.ncard := by gcongr; exact Set.ncard_union_le _ _
    _ ≤ NisoSep Z r L T (2 * T) + Assembly.NII Z T := by
        have e1 : S.ncard = NisoSep Z r L T (2 * T) := rfl
        have e2 : W₁.ncard ≤ Z.N (T - D0 T) T := Z.Nd_le_N _ _
        have e3 : W₂.ncard ≤ Z.N (2 * T) (2 * T + D0 T) := Z.Nd_le_N _ _
        unfold Assembly.NII
        omega

/-- **Seam, separated count.** -/
theorem seam_sep (hT : 0 ≤ T) (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀) (ha : 0 < P.a T)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (hwin : Real.pi / P.L T ≤ D0 T) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ NisoSep Z r (P.L T) T (2 * T)
        + r ^ 2 * ((Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ)) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_sep (Z := Z) hconj hreal hPois hL hc hsupp ha hr0 hr1
  have hpert := Assembly.ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : ((((blockData Z T P hconj).S₁ \ (lensMixed Z hconj (P.L T) ∪
        clustered Z hconj r (P.L T))).card : ℕ) : ℝ)
      ≤ (NisoSep Z r (P.L T) T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast card_S₁_sdiff_sep_le hconj hL hr1 hwin
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end

section ThmD

open Filter Asymptotics Topology Real RHLinalg Zeta23.ThmD Zeta23.Assembly

/-- **Theorem D for separated simple zeros, abstract.** -/
theorem thmD_sep_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ - r ^ 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoSep Z r (P.L T) T (2 * T) := by
  have hmain := thmD_count_of_seam Z H P hP hlam aT bT JT trG trG2 hTr hc0 hc ha θ₀ hTail hθ₀
    hNII hGzGp hId hcalE
    (fun T => (NisoSep Z r (P.L T) T (2 * T) : ℝ)
      + r ^ 2 * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ))) ?_
  · -- `N(I′ ∖ I) = o(N)`
    obtain ⟨CII, hII⟩ := hNII
    have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
      have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
        refine IsBigO.of_bound CII ?_
        filter_upwards [hII, eventually_l_pos] with T h hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (by positivity)]
        simpa [mul_assoc] using h
      exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := hmain (ε / 2) (by linarith)
    have hsmall := o3.def (show (0 : ℝ) < ε / 2 by linarith)
    obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp hsmall
    refine ⟨max T₁ T₂, fun T hT => ?_⟩
    have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
    have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _)] at h2
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hNII0 : (0 : ℝ) ≤ NII Z T := Nat.cast_nonneg _
    have : r ^ 2 * (NII Z T : ℝ) ≤ ε / 2 * (Z.N T (2 * T) : ℝ) := by nlinarith
    nlinarith
  · have hlam0 := hP.lam_pos
    have hLtop := Assembly.tendsto_L_atTop P hlam0
    filter_upwards [hTail, hId, ha, eventually_ge_atTop (1:ℝ), eventually_l_pos, eventually_w8 hP,
      hLtop.eventually (eventually_ge_atTop Real.pi)]
      with T hTl hid ha2 hT1 hl h8 hLpi
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hW := admWindow_params hP h8
    have hcD : Continuous ((P.atD T).phi T) := by
      rw [Params.atD_phi_valid T hP]; exact hW.contDiff.continuous
    have hsuppD : ∀ u, (P.atD T).L T / 2 ≤ |u| → (P.atD T).phi T u = 0 := by
      intro u hu; rw [Params.atD_phi_valid T hP]; exact hW.support u hu
    have hwin : Real.pi / (P.atD T).L T ≤ D0 T := by
      rw [Params.atD_L, div_le_iff₀ hLpos]
      have hsq : 1 ≤ D0 T := by
        unfold D0; rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT1
      nlinarith [Real.pi_pos]
    have h := seam_sep (Z := Z) hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD
      (by rw [Params.atD_L]; exact hLpos) hcD hsuppD hwin hr0 hr1
    rw [Params.atD_L] at h
    exact h

/-- Fixed `λ ∈ (0,1)`, abstract zero configuration with the paper's inputs. -/
theorem thmD_sep_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - r ^ 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoSep Z r (P.L T) T (2 * T) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_sep_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE hr0 hr1
  simpa only [HD, one_div] using h

end ThmD

noncomputable section Zeta

open Filter Zeta23.ThmD

/-- A nontrivial zero `ρ` of `ζ` is `r`-separated at scale `L` if no other nontrivial zero lies
within distance `r/L`. -/
def ZetaSeparated (r L : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ' ≠ ρ → ‖ρ' - ρ‖ * L ≤ r → False

/-- Simple critical-line zeros of `ζ` with `T₁ < γ ≤ T₂` that are `r`-separated at scale `L`. -/
def N0simpleSeparated (r L T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩ {ρ | ZetaSeparated r L ρ}).ncard

theorem NisoSep_zetaZeroConfig (r L T₁ T₂ : ℝ) :
    NisoSep zetaZeroConfig r L T₁ T₂ = N0simpleSeparated r L T₁ T₂ := rfl

/-- A smaller scale is a stronger separation condition. -/
theorem N0simpleSeparated_mono {r L L' : ℝ} (hLL : L' ≤ L) (T₁ T₂ : ℝ) :
    N0simpleSeparated r L' T₁ T₂ ≤ N0simpleSeparated r L T₁ T₂ := by
  apply Set.ncard_le_ncard
  · rintro ρ ⟨hρ, hsep⟩
    refine ⟨hρ, fun ρ' h1 h2 h3 => hsep ρ' h1 h2 (le_trans ?_ h3)⟩
    exact mul_le_mul_of_nonneg_left hLL (norm_nonneg _)
  · exact (zetaZeroConfig.window_finite T₁ T₂).subset fun ρ hρ => hρ.1.1.1

/-- `ζ` at fixed `λ ∈ (0,1)`. -/
theorem separated_simple_critical_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - r ^ 2 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simpleSeparated r (lam * l T) T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have h := thmD_sep_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    hr0 hr1
  simpa [paramsOf, Params.L, NisoSep_zetaZeroConfig] using h

/-- **Separated simple zeros of ζ.**  For `0 < r ≤ 1`, every `ε > 0` and all large `T`, at least
`(HD(1) − r² − ε)·N(T,2T)` zeros `ρ` with `T < Im ρ ≤ 2T` are simple, lie on the critical line, and
no other nontrivial zero lies within distance `r/log(T/2π)` of `ρ`.  Here
`HD(1) = 2 − 1/c₁* = 0.67250…`. -/
theorem separated_simple_critical {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - r ^ 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleSeparated r (l T) T (2 * T) := by
  have h := eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simpleSeparated r (l T) T (2 * T) : ℝ) + r ^ 2 * (Ncount T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) ?_
  · intro ε hε
    obtain ⟨T₀, hT₀⟩ := h ε hε
    exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩
  intro lam hl1 hl2 ε hε
  obtain ⟨T₀, hT₀⟩ := separated_simple_critical_lam (by linarith) hl2 hr0 hr1 ε hε
  refine ⟨max T₀ (2 * Real.pi * Real.exp 1), fun T hT => ?_⟩
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTbig : 2 * Real.pi * Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTbig
  have hl : 1 ≤ l T := by
    unfold l
    rw [Real.le_log_iff_exp_le (div_pos hTpos (by positivity))]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlam0 : 0 < lam := by linarith
  have hscale : lam * l T ≤ l T := by nlinarith
  have := hT₀ T hTT₀
  have hmono := N0simpleSeparated_mono (r := r) hscale T (2 * T)
  have hmono' : (N0simpleSeparated r (lam * l T) T (2 * T) : ℝ)
      ≤ N0simpleSeparated r (l T) T (2 * T) := by exact_mod_cast hmono
  nlinarith

end Zeta

end RHTower
