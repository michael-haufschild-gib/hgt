import GaloisForLFunctions.CountingHolography.Sections.MidpointProductsOfSmallSections

/-!
# Subquadratic fibres and translation rigidity of midpoint section maps

Allowing non-injective midpoint section maps whose largest fibre grows
subquadratically in logarithm preserves the signed Tate degree comparison and
still characterizes the Riemann hypothesis over a single two-atom background.
Conversely, intersecting two translations at a shared midpoint shows that no
single coordinate map on `ℤ × ℤ` can serve distinct scales with subquadratic
fibre loss whenever the displacement pairs nontrivially with the background.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography

/-- Largest fibre cardinality of a map between finite types. -/
def maxFibre {α β : Type*} [Fintype α] [Fintype β] (f : α → β) : ℕ := by
  classical
  exact Finset.univ.sup fun y : β => (Finset.univ.filter fun x : α => f x = y).card

theorem card_le_maxFibre_of_forall_eq {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) {S : Finset α} (y : β) (hS : ∀ x ∈ S, f x = y) :
    S.card ≤ maxFibre f := by
  classical
  unfold maxFibre
  refine (Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hx⟩).trans ?_
  exact Finset.le_sup (f := fun z : β => (Finset.univ.filter fun x : α => f x = z).card)
    (Finset.mem_univ y)

theorem maxFibre_le_iff {α β : Type*} [Fintype α] [Fintype β] {f : α → β} {B : ℕ} :
    maxFibre f ≤ B ↔ ∀ (y : β) (S : Finset α), (∀ x ∈ S, f x = y) → S.card ≤ B := by
  classical
  unfold maxFibre
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h y S hS
    exact (Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hx⟩).trans (h y)
  · intro h y
    exact h y _ fun x hx => (Finset.mem_filter.mp hx).2

theorem card_le_maxFibre_mul_card {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    Fintype.card α ≤ maxFibre f * Fintype.card β := by
  classical
  unfold maxFibre
  have hpart : Fintype.card α = ∑ y : β, (Finset.univ.filter fun x : α => f x = y).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) fun _ _ => Finset.mem_univ _
  calc Fintype.card α = ∑ y : β, (Finset.univ.filter fun x : α => f x = y).card := hpart
    _ ≤ ∑ _ : β, Finset.univ.sup (fun z : β => (Finset.univ.filter fun x : α => f x = z).card) :=
        Finset.sum_le_sum fun y _ =>
          Finset.le_sup (f := fun z : β => (Finset.univ.filter fun x : α => f x = z).card) (Finset.mem_univ y)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

theorem maxFibre_pos {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] (f : α → β) :
    0 < maxFibre f := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have h1 : 1 ≤ maxFibre f := by
    simpa only [Finset.card_singleton] using
      card_le_maxFibre_of_forall_eq f (f x) (S := {x}) fun z hz => by
        rw [Finset.mem_singleton.mp hz]
  omega

theorem maxFibre_le_one_iff_injective {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    maxFibre f ≤ 1 ↔ Function.Injective f := by
  classical
  unfold maxFibre
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_true_left, Finset.card_le_one,
    Finset.mem_filter, true_and]
  constructor
  · exact fun h x₁ x₂ he => h (f x₁) x₁ rfl x₂ he.symm
  · exact fun hf y x₁ hx₁ x₂ hx₂ => hf (hx₁.trans hx₂.symm)

/-- Arbitrary two-output maps from the midpoint section square to the outer section product. -/
abbrev midpointSectionMap {N : ℕ} (b a : Fin N → ℤ) (m : ℕ) :=
  (↥(divisorSections (m • b)) × ↥(divisorSections (m • b))) →
    (↥(divisorSections (m • (b + a))) × ↥(divisorSections (m • (b - a))))

private theorem divisorSections_nonempty {N : ℕ} (a : Fin N → ℤ) :
    Nonempty ↥(divisorSections a) := by
  have hc : 0 < (divisorSections a).card := by
    rw [divisorSections, card_smallSections]
    omega
  exact Finset.Nonempty.to_subtype (Finset.card_pos.mp hc)

theorem maxFibre_midpointSectionMap_pos {N : ℕ} {b a : Fin N → ℤ} {m : ℕ}
    (f : midpointSectionMap b a m) : 0 < maxFibre f := by
  haveI := divisorSections_nonempty (m • b)
  exact maxFibre_pos f

/-- The normalized logarithmic midpoint excess is bounded below by minus the
normalized logarithmic collision size across both outputs. -/
theorem neg_log_maxFibre_le_midpointExcess {N : ℕ} {b a : Fin N → ℤ} {m : ℕ} (hm : 0 < m)
    (f : midpointSectionMap b a m) :
    -(Real.log (maxFibre f) / (m : ℝ)^2) ≤ midpointExcess b a m := by
  have hcard := card_le_maxFibre_mul_card f
  simp only [Fintype.card_prod, Fintype.card_coe] at hcard
  have hx : 0 < ((divisorSections (m • b)).card : ℝ) := by
    have : 0 < (divisorSections (m • b)).card := by rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hy : 0 < ((divisorSections (m • (b + a))).card : ℝ) := by
    have : 0 < (divisorSections (m • (b + a))).card := by rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hz : 0 < ((divisorSections (m • (b - a))).card : ℝ) := by
    have : 0 < (divisorSections (m • (b - a))).card := by rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hf : 0 < (maxFibre f : ℝ) := Nat.cast_pos.mpr (maxFibre_midpointSectionMap_pos f)
  have hreal : ((divisorSections (m • b)).card : ℝ) * (divisorSections (m • b)).card ≤
      maxFibre f * ((divisorSections (m • (b + a))).card * (divisorSections (m • (b - a))).card) := by
    exact_mod_cast hcard
  have hlog := Real.log_le_log (mul_pos hx hx) hreal
  rw [Real.log_mul hx.ne' hx.ne', Real.log_mul hf.ne' (mul_pos hy hz).ne',
    Real.log_mul hy.ne' hz.ne'] at hlog
  rw [midpointExcess, logCard, logCard, logCard, ← neg_div,
    div_le_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2)]
  linarith only [hlog]

/-- Cofinal midpoint section maps with subquadratic logarithmic fibre growth. -/
def hasSubquadraticMidpointFibres {N : ℕ} (b a : Fin N → ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ᶠ m : ℕ in atTop, ∃ f : midpointSectionMap b a m,
    Real.log (maxFibre f) ≤ ε * (m : ℝ)^2

/-- Any sequence of midpoint maps with `log(maxFibre f_m) = o(m²)` satisfies
the cofinal subquadratic fibre condition. -/
theorem hasSubquadraticMidpointFibres_of_tendsto_zero {N : ℕ} {b a : Fin N → ℤ}
    (f : ∀ m : ℕ, midpointSectionMap b a m)
    (hf : Tendsto (fun m : ℕ => Real.log (maxFibre (f m)) / (m : ℝ)^2) atTop (𝓝 0)) :
    hasSubquadraticMidpointFibres b a := by
  intro ε hε
  refine ((hf.eventually_lt_const hε).and (eventually_ge_atTop 1)).frequently.mono ?_
  rintro m ⟨hm, hm1⟩
  exact ⟨f m, ((div_lt_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm).le⟩

theorem hasSubquadraticMidpointFibres_of_frequently_embeds {N : ℕ} {b a : Fin N → ℤ}
    (h : ∃ᶠ m : ℕ in atTop, midpointEmbeds b a m) :
    hasSubquadraticMidpointFibres b a := by
  intro ε hε
  refine h.mono fun m ⟨e⟩ => ⟨e, ?_⟩
  have hle : maxFibre (e : midpointSectionMap b a m) ≤ 1 :=
    (maxFibre_le_one_iff_injective _).mpr e.injective
  have hle' : (maxFibre (e : midpointSectionMap b a m) : ℝ) ≤ 1 := by exact_mod_cast hle
  have hpos : 0 < (maxFibre (e : midpointSectionMap b a m) : ℝ) :=
    Nat.cast_pos.mpr (maxFibre_midpointSectionMap_pos e)
  have hlog : Real.log (maxFibre (e : midpointSectionMap b a m)) ≤ 0 := by
    simpa only [Real.log_one] using Real.log_le_log hpos hle'
  exact hlog.trans (mul_nonneg hε.le (sq_nonneg _))

/-- Subquadratic logarithmic fibre growth along cofinal translations of a
positive background implies nonnegativity of the signed Weil degree. -/
theorem integerProbe_nonneg_of_subquadraticMidpointFibres {N : ℕ} (b a : Fin N → ℤ)
    (hb : 0 < integerProbe N b)
    (h : ∃ᶠ k : ℕ in atTop, hasSubquadraticMidpointFibres (k • b) a) :
    0 ≤ integerProbe N a := by
  by_contra! hneg
  obtain ⟨k, hk, hlim⟩ := (h.and_eventually (eventually_midpointExcess_tateLimit b a hb)).exists
  let ε : ℝ := -(integerProbe N a)
  have hε : 0 < ε := neg_pos.mpr hneg
  have hlt : 2 * integerProbe N a < -ε := by dsimp [ε]; linarith only [hneg]
  obtain ⟨m, ⟨f, hf⟩, hm_lt, hm1⟩ :=
    ((hk ε hε).and_eventually ((hlim.eventually_lt_const hlt).and (eventually_ge_atTop 1))).exists
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hdiv : Real.log (maxFibre f) / (m : ℝ)^2 ≤ ε := (div_le_iff₀ hm2).mpr hf
  have hlow := neg_log_maxFibre_le_midpointExcess hm1 f
  linarith only [hdiv, hlow, hm_lt]

/-- Global midpoint test allowing subquadratic logarithmic fibre collisions at
every displacement and all sufficiently high background translations. -/
def subquadraticMidpointTest {P : ℕ} (b : Fin P → ℤ) : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ k : ℕ in atTop,
    hasSubquadraticMidpointFibres (k • padDivisor (le_max_left P N) b)
      (padDivisor (le_max_right P N) a)

/-- Relaxing midpoint injections to arbitrary maps with `exp(o(m²))` fibres
yields an exact characterization of the Riemann hypothesis. -/
theorem riemannHypothesis_iff_subquadraticMidpointTest {P : ℕ} (b : Fin P → ℤ)
    (hb : 0 < integerProbe P b) :
    RiemannHypothesis ↔ subquadraticMidpointTest b := by
  constructor
  · intro hRH N a
    filter_upwards [(riemannHypothesis_iff_midpointTest b hb).mp hRH N a] with k hk
    exact hasSubquadraticMidpointFibres_of_frequently_embeds hk
  · intro h
    apply riemannHypothesis_iff_integerProbes.mpr
    intro N a
    let B := padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    have hb' : 0 < integerProbe (max P N) B := by simpa only [B, integerProbe_pad] using hb
    have hA := integerProbe_nonneg_of_subquadraticMidpointFibres B A hb' (h N a).frequently
    simpa only [A, integerProbe_pad] using hA

/-- One unconditional two-atom prime background characterizes RH via midpoint
section maps of subquadratic logarithmic fibre cost. -/
theorem exists_prime_background_subquadraticMidpointTest :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧ (RiemannHypothesis ↔ subquadraticMidpointTest b) := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, _⟩ := exists_prime_background_midpointTest
  exact ⟨p, b, hp, hb_eq, hb_pos, riemannHypothesis_iff_subquadraticMidpointTest b hb_pos⟩

/-! ### Translation rigidity of fixed integer-coordinate section maps -/

/-- An integer-coordinate operation `Ψ : ℤ × ℤ → ℤ × ℤ` sends pairs of sections
of `v₀` into `divisorSections v₁ × divisorSections v₂`. -/
def mapsDivisorSections {N : ℕ} (Ψ : ℤ × ℤ → ℤ × ℤ) (v₀ v₁ v₂ : Fin N → ℤ) : Prop :=
  ∀ x ∈ divisorSections v₀, ∀ y ∈ divisorSections v₀,
    (Ψ (x, y)).1 ∈ divisorSections v₁ ∧ (Ψ (x, y)).2 ∈ divisorSections v₂

/-- Restriction of a global integer map `Ψ` to finite section intervals. -/
def restrictSectionMap {N : ℕ} (Ψ : ℤ × ℤ → ℤ × ℤ) {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsDivisorSections Ψ v₀ v₁ v₂) :
    (↥(divisorSections v₀) × ↥(divisorSections v₀)) →
      (↥(divisorSections v₁) × ↥(divisorSections v₂)) :=
  fun p => (⟨(Ψ (p.1.val, p.2.val)).1, (h p.1.val p.1.property p.2.val p.2.property).1⟩,
            ⟨(Ψ (p.1.val, p.2.val)).2, (h p.1.val p.1.property p.2.val p.2.property).2⟩)

/-- The largest fibre cardinality of `restrictSectionMap Ψ h` depends only on the
domain `divisorSections v₀` and `Ψ`, not on the ambient target intervals. -/
theorem maxFibre_restrictSectionMap_eq {N : ℕ} (Ψ : ℤ × ℤ → ℤ × ℤ)
    {v₀ v₁ v₂ w₁ w₂ : Fin N → ℤ}
    (h₁ : mapsDivisorSections Ψ v₀ v₁ v₂) (h₂ : mapsDivisorSections Ψ v₀ w₁ w₂) :
    maxFibre (restrictSectionMap Ψ h₁) = maxFibre (restrictSectionMap Ψ h₂) := by
  have hle : ∀ {a₁ a₂ b₁ b₂ : Fin N → ℤ}
      (u₁ : mapsDivisorSections Ψ v₀ a₁ a₂) (u₂ : mapsDivisorSections Ψ v₀ b₁ b₂),
      maxFibre (restrictSectionMap Ψ u₁) ≤ maxFibre (restrictSectionMap Ψ u₂) := by
    intro a₁ a₂ b₁ b₂ u₁ u₂
    rw [maxFibre_le_iff]
    intro y S hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · simp
    · refine card_le_maxFibre_of_forall_eq (restrictSectionMap Ψ u₂) (restrictSectionMap Ψ u₂ p)
        fun q hq => ?_
      have heq : restrictSectionMap Ψ u₁ q = restrictSectionMap Ψ u₁ p :=
        (hS q hq).trans (hS p hp).symm
      simp only [restrictSectionMap, Prod.ext_iff, Subtype.ext_iff] at heq ⊢
      exact heq
  exact le_antisymm (hle h₁ h₂) (hle h₂ h₁)

private theorem card_sq_le_of_two_targets {N : ℕ} (Ψ : ℤ × ℤ → ℤ × ℤ)
    {v₀ v₁ v₂ w₁ w₂ : Fin N → ℤ}
    (h₁ : mapsDivisorSections Ψ v₀ v₁ v₂) (h₂ : mapsDivisorSections Ψ v₀ w₁ w₂) :
    (divisorSections v₀).card ^ 2 ≤
      maxFibre (restrictSectionMap Ψ h₁) * ((divisorSections w₁).card * (divisorSections v₂).card) := by
  have hint : mapsDivisorSections Ψ v₀ w₁ v₂ := fun x hx y hy =>
    ⟨(h₂ x hx y hy).1, (h₁ x hx y hy).2⟩
  rw [maxFibre_restrictSectionMap_eq Ψ h₁ hint]
  have hc := card_le_maxFibre_mul_card (restrictSectionMap Ψ hint)
  simpa only [Fintype.card_prod, Fintype.card_coe, sq] using hc

private theorem integerProbe_shift_diff {N : ℕ} (r s : ℕ) (b c : Fin N → ℤ) :
    integerProbe N (r • b + s • c) - integerProbe N (r • b - s • c) =
      (r : ℝ) * (s : ℝ) * (integerProbe N (b + c) - integerProbe N (b - c)) := by
  have hsmul {m : ℕ} (v : Fin N → ℤ) (i : Fin N) : ((m • v) i : ℝ) = (m : ℝ) * (v i : ℝ) := by
    change ((m • v i : ℤ) : ℝ) = _
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  simp only [integerProbe_eq_sum, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub, hsmul]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Any single integer-coordinate map serving both translations `k ≥ 2` and `2k`
on a positive ray `b` suffers quadratic logarithmic fibre loss of rate at least
`((4k - 5) / 4) * Q(b)` at multiplicity `2m`. -/
theorem eventually_doubling_translation_fibre_cost {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : δ < ((4 * (k : ℝ) - 5) / 4) * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (Ψ : ℤ × ℤ → ℤ × ℤ)
      (h₁ : mapsDivisorSections Ψ ((2 * m) • (k • b))
        ((2 * m) • (k • b + b)) ((2 * m) • (k • b - b))),
      mapsDivisorSections Ψ (m • ((2 * k) • b))
        (m • ((2 * k) • b + b)) (m • ((2 * k) • b - b)) →
      δ * ((2 * m : ℕ) : ℝ)^2 < Real.log (maxFibre (restrictSectionMap Ψ h₁)) := by
  let d := integerProbe N b
  have hmid : Tendsto (fun m : ℕ => logCard (m • ((2 * k) • b)) / (m : ℝ)^2) atTop
      (𝓝 ((2 * (k : ℝ))^2 * d)) := by
    have h := logCard_tateLimit ((2 * k) • b)
    rw [integerProbe_smul, Nat.cast_mul, Nat.cast_ofNat,
      max_eq_left (mul_nonneg (sq_nonneg _) hb.le)] at h
    exact h
  have hout₁ : Tendsto (fun m : ℕ => logCard (m • ((2 * k + 1) • b)) / (m : ℝ)^2) atTop
      (𝓝 ((2 * (k : ℝ) + 1)^2 * d)) := by
    have h := logCard_tateLimit ((2 * k + 1) • b)
    rw [integerProbe_smul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      max_eq_left (mul_nonneg (sq_nonneg _) hb.le)] at h
    exact h
  have hout₂ : Tendsto (fun m : ℕ => logCard (m • ((2 * (k - 1)) • b)) / (m : ℝ)^2) atTop
      (𝓝 ((2 * ((k : ℝ) - 1))^2 * d)) := by
    have h := logCard_tateLimit ((2 * (k - 1)) • b)
    rw [integerProbe_smul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_one, max_eq_left (mul_nonneg (sq_nonneg _) hb.le)] at h
    exact h
  have hlim := ((hmid.const_mul 2).sub hout₁).sub hout₂
  have hgap : 4 * δ < 2 * ((2 * (k : ℝ))^2 * d) - (2 * (k : ℝ) + 1)^2 * d -
      (2 * ((k : ℝ) - 1))^2 * d := by
    dsimp [d]; nlinarith only [hδ]
  filter_upwards [hlim.eventually_const_lt hgap, eventually_ge_atTop 1] with m hm hm1
  intro Ψ h₁ h₂
  have he₀ : (2 * m) • (k • b) = m • ((2 * k) • b) := by
    rw [smul_smul, smul_smul, show 2 * m * k = m * (2 * k) by ring]
  have he₁ : m • ((2 * k) • b + b) = m • ((2 * k + 1) • b) := by
    ext i
    change m • (((2 * k) • b i) + b i) = m • ((2 * k + 1) • b i)
    simp only [nsmul_eq_mul]; push_cast; ring
  have he₂ : (2 * m) • (k • b - b) = m • ((2 * (k - 1)) • b) := by
    ext i
    change (2 * m) • ((k • b i) - b i) = m • ((2 * (k - 1)) • b i)
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (R := ℤ) (by omega : 1 ≤ k), Nat.cast_one]
    ring
  have h₂' : mapsDivisorSections Ψ ((2 * m) • (k • b))
      (m • ((2 * k + 1) • b)) (m • ((2 * k) • b - b)) := by
    rwa [he₀, ← he₁]
  have hcard := card_sq_le_of_two_targets Ψ h₁ h₂'
  have hc0_eq : (divisorSections ((2 * m) • (k • b))).card =
      (divisorSections (m • ((2 * k) • b))).card :=
    congrArg (fun v => (divisorSections v).card) he₀
  have hc2_eq : (divisorSections ((2 * m) • (k • b - b))).card =
      (divisorSections (m • ((2 * (k - 1)) • b))).card :=
    congrArg (fun v => (divisorSections v).card) he₂
  rw [hc0_eq, hc2_eq] at hcard
  have hc₀ : 0 < ((divisorSections (m • ((2 * k) • b))).card : ℝ) := by
    have : 0 < (divisorSections (m • ((2 * k) • b))).card := by
      rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hc₁ : 0 < ((divisorSections (m • ((2 * k + 1) • b))).card : ℝ) := by
    have : 0 < (divisorSections (m • ((2 * k + 1) • b))).card := by
      rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hc₂ : 0 < ((divisorSections (m • ((2 * (k - 1)) • b))).card : ℝ) := by
    have : 0 < (divisorSections (m • ((2 * (k - 1)) • b))).card := by
      rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  haveI := divisorSections_nonempty ((2 * m) • (k • b))
  have hfpos : 0 < (maxFibre (restrictSectionMap Ψ h₁) : ℝ) :=
    Nat.cast_pos.mpr (maxFibre_pos _)
  have hreal : ((divisorSections (m • ((2 * k) • b))).card : ℝ)^2 ≤
      maxFibre (restrictSectionMap Ψ h₁) *
        ((divisorSections (m • ((2 * k + 1) • b))).card *
          (divisorSections (m • ((2 * (k - 1)) • b))).card) := by
    exact_mod_cast hcard
  have hlog := Real.log_le_log (sq_pos_of_pos hc₀) hreal
  rw [Real.log_pow, Real.log_mul hfpos.ne' (mul_pos hc₁ hc₂).ne',
    Real.log_mul hc₁.ne' hc₂.ne'] at hlog
  change 4 * δ < 2 * (logCard (m • ((2 * k) • b)) / (m : ℝ)^2) -
    logCard (m • ((2 * k + 1) • b)) / (m : ℝ)^2 -
    logCard (m • ((2 * (k - 1)) • b)) / (m : ℝ)^2 at hm
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hm' : 4 * δ * (m : ℝ)^2 < 2 * logCard (m • ((2 * k) • b)) -
      logCard (m • ((2 * k + 1) • b)) - logCard (m • ((2 * (k - 1)) • b)) := by
    have hdiv : 4 * δ < (2 * logCard (m • ((2 * k) • b)) -
        logCard (m • ((2 * k + 1) • b)) - logCard (m • ((2 * (k - 1)) • b))) / (m : ℝ)^2 := by
      convert hm using 1; ring
    exact (lt_div_iff₀ hm2).mp hdiv
  have h2m : ((2 * m : ℕ) : ℝ)^2 = 4 * (m : ℝ)^2 := by push_cast; ring
  rw [h2m]
  unfold logCard at hm'
  push_cast at hlog
  linarith only [hm', hlog]

/-- For any displacement `a` whose mixed Weil pairing with `b` is nonzero
(`Q(b + a) ≠ Q(b - a)`), no single coordinate operation `Ψ : ℤ × ℤ → ℤ × ℤ`
can realize midpoint section maps with subquadratic logarithmic fibre cost across
all sufficiently high background translations. -/
theorem not_exists_translation_uniform_subquadratic_midpointMap {N : ℕ} {b a : Fin N → ℤ}
    (hb : 0 < integerProbe N b) (hmix : integerProbe N (b + a) ≠ integerProbe N (b - a)) :
    ¬ ∃ Ψ : ℤ × ℤ → ℤ × ℤ, ∀ᶠ k : ℕ in atTop,
      (∀ᶠ m : ℕ in atTop, mapsDivisorSections Ψ (m • (k • b)) (m • (k • b + a)) (m • (k • b - a))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ᶠ m : ℕ in atTop, ∃ h : mapsDivisorSections Ψ (m • (k • b))
        (m • (k • b + a)) (m • (k • b - a)),
        Real.log (maxFibre (restrictSectionMap Ψ h)) ≤ ε * (m : ℝ)^2 := by
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    ((hΨ.and (eventually_positive_shift b a hb)).and
      ((eventually_positive_shift b (-a) hb).and
        ((eventually_positive_shift b (2 • a) hb).and (eventually_positive_shift b (-(2 • a)) hb))))
  let Δ := |integerProbe N (b + a) - integerProbe N (b - a)|
  have hΔ : 0 < Δ := abs_pos.mpr (sub_ne_zero.mpr hmix)
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt ((5 * |integerProbe N a| + 4) / Δ)
  let k := max (max K₀ 1) K₁
  have hk0 : K₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have h2k0 : K₀ ≤ 2 * k := by omega
  have hgap_k : 5 * integerProbe N a + 4 < (k : ℝ) * Δ := by
    have hkK₁ : (K₁ : ℝ) ≤ k := by exact_mod_cast le_max_right (max K₀ 1) K₁
    have hgt := (div_lt_iff₀ hΔ).mp (hK₁.trans_le hkK₁)
    linarith only [hgt, le_abs_self (integerProbe N a)]
  obtain ⟨⟨⟨hm_k, _⟩, _⟩, _, _⟩ := hK₀ k hk0
  obtain ⟨⟨⟨_, hfib_2k⟩, hp_2k_a⟩, hn_2k_a, hp_2k_2a, hn_2k_2a⟩ := hK₀ (2 * k) h2k0
  rw [← sub_eq_add_neg] at hn_2k_a hn_2k_2a
  have hmid_pos : 0 ≤ integerProbe N ((2 * k) • b) := by
    rw [integerProbe_smul]; exact mul_nonneg (sq_nonneg _) hb.le
  have hp1 := integerProbe_parallelogram N ((2 * k) • b) a
  have hp2 := integerProbe_parallelogram N ((2 * k) • b) (2 • a)
  rw [integerProbe_smul N 2 a] at hp2
  have hp3 := integerProbe_shift_diff (2 * k) 1 b a
  simp only [one_smul, Nat.cast_one, mul_one, Nat.cast_mul, Nat.cast_ofNat] at hp3
  have hp4 := integerProbe_shift_diff (2 * k) 2 b a
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp4
  push_cast at hp2
  have h2m_map : ∀ᶠ m : ℕ in atTop,
      mapsDivisorSections Ψ ((2 * m) • (k • b)) ((2 * m) • (k • b + a)) ((2 * m) • (k • b - a)) := by
    have ht : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_atTop_mono (f := id) (fun m => by dsimp; omega) tendsto_id
    exact ht.eventually hm_k
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hmix) with hneg_mix | hpos_mix
  · -- Negative mixed pairing: intersect `(k, 2m)` first output with `(2k, m)` second output.
    have hΔ_eq : Δ = -(integerProbe N (b + a) - integerProbe N (b - a)) := abs_of_neg hneg_mix
    have hdef : 4 < 2 * integerProbe N ((2 * k) • b) -
        integerProbe N ((2 * k) • b + 2 • a) - integerProbe N ((2 * k) • b - a) := by
      rw [hΔ_eq] at hgap_k
      linarith only [hp1, hp2, hp3, hp4, hgap_k]
    have hl₀ := logCard_tateLimit ((2 * k) • b)
    rw [max_eq_left hmid_pos] at hl₀
    have hl₁ := logCard_tateLimit ((2 * k) • b + 2 • a)
    rw [max_eq_left hp_2k_2a.le] at hl₁
    have hl₂ := logCard_tateLimit ((2 * k) • b - a)
    rw [max_eq_left hn_2k_a.le] at hl₂
    have hlim := ((hl₀.const_mul 2).sub hl₁).sub hl₂
    obtain ⟨m, ⟨h_2k, hsmall⟩, h_k2m, h_rate, hm1⟩ :=
      ((hfib_2k 1 one_pos).and_eventually
        (h2m_map.and ((hlim.eventually_const_lt hdef).and (eventually_ge_atTop 1)))).exists
    have he₀ : (2 * m) • (k • b) = m • ((2 * k) • b) := by
      rw [smul_smul, smul_smul, show 2 * m * k = m * (2 * k) by ring]
    have he₁ : (2 * m) • (k • b + a) = m • ((2 * k) • b + 2 • a) := by
      ext i
      change (2 * m) • ((k • b i) + a i) = m • (((2 * k) • b i) + (2 • a i))
      simp only [nsmul_eq_mul]; push_cast; ring
    have h_k2m' : mapsDivisorSections Ψ (m • ((2 * k) • b))
        (m • ((2 * k) • b + 2 • a)) ((2 * m) • (k • b - a)) := by
      rwa [← he₀, ← he₁]
    have hcard := card_sq_le_of_two_targets Ψ h_2k h_k2m'
    have hc₀ : 0 < ((divisorSections (m • ((2 * k) • b))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    have hc₁ : 0 < ((divisorSections (m • ((2 * k) • b + 2 • a))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b + 2 • a))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    have hc₂ : 0 < ((divisorSections (m • ((2 * k) • b - a))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b - a))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    haveI := divisorSections_nonempty (m • ((2 * k) • b))
    have hfpos : 0 < (maxFibre (restrictSectionMap Ψ h_2k) : ℝ) := Nat.cast_pos.mpr (maxFibre_pos _)
    have hreal : ((divisorSections (m • ((2 * k) • b))).card : ℝ)^2 ≤
        maxFibre (restrictSectionMap Ψ h_2k) *
          ((divisorSections (m • ((2 * k) • b + 2 • a))).card *
            (divisorSections (m • ((2 * k) • b - a))).card) := by exact_mod_cast hcard
    have hlog := Real.log_le_log (sq_pos_of_pos hc₀) hreal
    rw [Real.log_pow, Real.log_mul hfpos.ne' (mul_pos hc₁ hc₂).ne',
      Real.log_mul hc₁.ne' hc₂.ne'] at hlog
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hrate' : 4 * (m : ℝ)^2 < 2 * logCard (m • ((2 * k) • b)) -
        logCard (m • ((2 * k) • b + 2 • a)) - logCard (m • ((2 * k) • b - a)) := by
      have hd : 4 < (2 * logCard (m • ((2 * k) • b)) -
          logCard (m • ((2 * k) • b + 2 • a)) - logCard (m • ((2 * k) • b - a))) / (m : ℝ)^2 := by
        simpa only [sub_div, mul_div_assoc] using h_rate
      exact (lt_div_iff₀ hm2).mp hd
    unfold logCard at hrate'
    push_cast at hlog
    linarith only [hsmall, hlog, hrate', hm2]
  · -- Positive mixed pairing: intersect `(2k, m)` first output with `(k, 2m)` second output.
    have hΔ_eq : Δ = integerProbe N (b + a) - integerProbe N (b - a) := abs_of_pos hpos_mix
    have hdef : 4 < 2 * integerProbe N ((2 * k) • b) -
        integerProbe N ((2 * k) • b + a) - integerProbe N ((2 * k) • b - 2 • a) := by
      rw [hΔ_eq] at hgap_k
      linarith only [hp1, hp2, hp3, hp4, hgap_k]
    have hl₀ := logCard_tateLimit ((2 * k) • b)
    rw [max_eq_left hmid_pos] at hl₀
    have hl₁ := logCard_tateLimit ((2 * k) • b + a)
    rw [max_eq_left hp_2k_a.le] at hl₁
    have hl₂ := logCard_tateLimit ((2 * k) • b - 2 • a)
    rw [max_eq_left hn_2k_2a.le] at hl₂
    have hlim := ((hl₀.const_mul 2).sub hl₁).sub hl₂
    obtain ⟨m, ⟨h_2k, hsmall⟩, h_k2m, h_rate, hm1⟩ :=
      ((hfib_2k 1 one_pos).and_eventually
        (h2m_map.and ((hlim.eventually_const_lt hdef).and (eventually_ge_atTop 1)))).exists
    have he₀ : (2 * m) • (k • b) = m • ((2 * k) • b) := by
      rw [smul_smul, smul_smul, show 2 * m * k = m * (2 * k) by ring]
    have he₂ : (2 * m) • (k • b - a) = m • ((2 * k) • b - 2 • a) := by
      ext i
      change (2 * m) • ((k • b i) - a i) = m • (((2 * k) • b i) - (2 • a i))
      simp only [nsmul_eq_mul]; push_cast; ring
    have h_k2m' : mapsDivisorSections Ψ (m • ((2 * k) • b))
        ((2 * m) • (k • b + a)) (m • ((2 * k) • b - 2 • a)) := by
      rwa [← he₀, ← he₂]
    have hcard := card_sq_le_of_two_targets Ψ h_k2m' h_2k
    rw [← maxFibre_restrictSectionMap_eq Ψ h_2k h_k2m'] at hcard
    have hc₀ : 0 < ((divisorSections (m • ((2 * k) • b))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    have hc₁ : 0 < ((divisorSections (m • ((2 * k) • b + a))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b + a))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    have hc₂ : 0 < ((divisorSections (m • ((2 * k) • b - 2 • a))).card : ℝ) := by
      have : 0 < (divisorSections (m • ((2 * k) • b - 2 • a))).card := by
        rw [divisorSections, card_smallSections]; omega
      exact_mod_cast this
    haveI := divisorSections_nonempty (m • ((2 * k) • b))
    have hfpos : 0 < (maxFibre (restrictSectionMap Ψ h_2k) : ℝ) := Nat.cast_pos.mpr (maxFibre_pos _)
    have hreal : ((divisorSections (m • ((2 * k) • b))).card : ℝ)^2 ≤
        maxFibre (restrictSectionMap Ψ h_2k) *
          ((divisorSections (m • ((2 * k) • b + a))).card *
            (divisorSections (m • ((2 * k) • b - 2 • a))).card) := by exact_mod_cast hcard
    have hlog := Real.log_le_log (sq_pos_of_pos hc₀) hreal
    rw [Real.log_pow, Real.log_mul hfpos.ne' (mul_pos hc₁ hc₂).ne',
      Real.log_mul hc₁.ne' hc₂.ne'] at hlog
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hrate' : 4 * (m : ℝ)^2 < 2 * logCard (m • ((2 * k) • b)) -
        logCard (m • ((2 * k) • b + a)) - logCard (m • ((2 * k) • b - 2 • a)) := by
      have hd : 4 < (2 * logCard (m • ((2 * k) • b)) -
          logCard (m • ((2 * k) • b + a)) - logCard (m • ((2 * k) • b - 2 • a))) / (m : ℝ)^2 := by
        simpa only [sub_div, mul_div_assoc] using h_rate
      exact (lt_div_iff₀ hm2).mp hd
    unfold logCard at hrate'
    push_cast at hlog
    linarith only [hsmall, hlog, hrate', hm2]

/-- Unconditional two-atom prime ray witnessing quadratic fibre loss for any
single coordinate operation across translations `k ≥ 2` and `2k`. -/
theorem exists_prime_ray_doubling_translation_obstruction :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧
      ∀ {k : ℕ}, 2 ≤ k → ∀ {δ : ℝ}, δ < ((4 * (k : ℝ) - 5) / 4) * integerProbe (p + 1) b →
        ∀ᶠ m : ℕ in atTop, ∀ (Ψ : ℤ × ℤ → ℤ × ℤ)
          (h₁ : mapsDivisorSections Ψ ((2 * m) • (k • b))
            ((2 * m) • (k • b + b)) ((2 * m) • (k • b - b))),
          mapsDivisorSections Ψ (m • ((2 * k) • b))
            (m • ((2 * k) • b + b)) (m • ((2 * k) • b - b)) →
          δ * ((2 * m : ℕ) : ℝ)^2 < Real.log (maxFibre (restrictSectionMap Ψ h₁)) := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, _⟩ := exists_prime_background_midpointTest
  refine ⟨p, b, hp, hb_eq, hb_pos, ?_⟩
  intro k hk δ hδ
  exact eventually_doubling_translation_fibre_cost hb_pos hk hδ

#print axioms riemannHypothesis_iff_subquadraticMidpointTest
#print axioms exists_prime_background_subquadraticMidpointTest
#print axioms eventually_doubling_translation_fibre_cost
#print axioms not_exists_translation_uniform_subquadratic_midpointMap
#print axioms exists_prime_ray_doubling_translation_obstruction

end GaloisForLFunctions.CountingHolography.Sections
